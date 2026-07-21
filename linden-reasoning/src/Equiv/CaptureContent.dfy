// The typed-capture content theory (digit-capture README, promotion items 1+2):
// examples/digit-capture/DigitContent.dfy generalized from ASCII digits to an
// arbitrary character predicate P — "a capture whose body only matches
// P-characters records a P-only span", proven once from the tree semantics.
// The digit theory becomes the instantiation P := c => '0' <= c <= '9'.
//
// The structure (and every induction skeleton, termination measure, and case
// body) is DigitContent's; only the digit-specific facts are abstracted:
//   * DigitOnly(r)                  ->  POnly(rer, r, P)   (body reads only P-chars)
//   * cd == digitCd                 ->  CdOnly(rer, cd, P) (descriptor implies P)
//   * DigitCharMatch                ->  CdOnly, definitionally
//   * '0' <= c <= '9' conclusions   ->  P(c)
// GidContainer is also refactored to be PURELY STRUCTURAL (the content
// condition on the body is a separate POnly precondition where needed), so
// bounds-only clients can use it with P := c => true.
//
// ENGINE-INDEPENDENT: this file imports only linden-semantics modules — every
// theorem here is about Linden's ECMAScript tree semantics itself, so it
// applies to ANY conforming engine (a production JavaScript engine included),
// not just the verified RegElk engine. It also verifies in the cheap CI
// partition. Engine-facing plumbing lives in Transfer.dfy/ApiReasoning.dfy.
include "LindenImports.dfy"

/** Proves, from `IsTree`/`TreeRes`, that a regex which only reads characters
    satisfying `P` consumes only `P`-characters — and that a capture group with
    such a body records a `P`-only span, wherever it sits in a (simple-fragment)
    pattern. The reusable content theory behind "typed captures". */
module CaptureContent {
  import opened Std.Wrappers
  import L = Regex
  import LT = Tree
  import LS = Semantics
  import LC = Chars
  import LG = Groups
  import LW = WarblreRegExpRecord
  import WP = WarblrePrimitives
  import LN = WarblreNumeric
  import SS = StrictSuffix

  // ===========================================================================
  // The parameterization: what "only matches P-characters" means
  // ===========================================================================

  /** Every character the descriptor `cd` matches satisfies `P`. */
  ghost predicate CdOnly(rer: LW.RegExpRecord, cd: LC.CharDescr, P: char -> bool) {
    forall c: char :: LC.CharMatch(rer, c, cd) ==> P(c)
  }

  /** The `P`-only fragment: `r` is built from Epsilon/Character/Sequence/
      Quantified and every character node it reads implies `P`. */
  ghost predicate POnly(rer: LW.RegExpRecord, r: L.Regex, P: char -> bool)
    decreases r
  {
    match r
    case Epsilon => true
    case Character(cd) => CdOnly(rer, cd, P)
    case Sequence(r1, r2) => POnly(rer, r1, P) && POnly(rer, r2, P)
    case Quantified(_, _, _, r1) => POnly(rer, r1, P)
    case _ => false
  }

  /** A `P`-only regex defines no groups. */
  lemma POnlyNoGroups(rer: LW.RegExpRecord, r: L.Regex, P: char -> bool)
    requires POnly(rer, r, P)
    ensures L.DefGroups(r) == []
    decreases r
  {
    match r
    case Sequence(r1, r2) => POnlyNoGroups(rer, r1, P); POnlyNoGroups(rer, r2, P);
    case Quantified(_, _, _, r1) => POnlyNoGroups(rer, r1, P);
    case _ =>
  }

  ghost predicate PAction(rer: LW.RegExpRecord, a: LS.Action, P: char -> bool) {
    match a case Areg(r) => POnly(rer, r, P) case Acheck(_) => true case Aclose(_) => false
  }
  ghost predicate PActions(rer: LW.RegExpRecord, acts: LS.Actions, P: char -> bool) {
    forall i :: 0 <= i < |acts| ==> PAction(rer, acts[i], P)
  }

  // A P-only action stack has no group-resetting to do.
  lemma GMResetEmpty(gm: LG.GroupMap)
    ensures LG.GMReset([], gm) == gm
  {
    var empty: LG.GroupSet := [];
    assert (set g | g in empty) == {};
  }

  // ---- Input threading facts (forward reads) -------------------------------

  /** Basic length/head facts about `LC.Reverse` (also proven in the Equiv
      layer's Translate.dfy; duplicated here to keep this file Linden-only). */
  lemma ReverseProps(s: LC.String)
    ensures |LC.Reverse(s)| == |s|
    ensures |s| > 0 ==> LC.Reverse(s)[0] == s[|s|-1]
  {
    if |s| == 0 {
    } else {
      ReverseProps(s[1..]);
    }
  }

  lemma InputStrIdx(inp: LC.Input)
    requires |inp.next| > 0
    ensures LC.Idx(inp) < |LC.InputStr(inp)|
    ensures LC.InputStr(inp)[LC.Idx(inp)] == inp.next[0]
  {
    ReverseProps(inp.pref);
  }

  lemma AdvancePreservesStr(inp: LC.Input)
    requires |inp.next| > 0
    ensures LC.InputStr(LC.AdvanceInputP(inp, WP.Forward)) == LC.InputStr(inp)
    ensures LC.Idx(LC.AdvanceInputP(inp, WP.Forward)) == LC.Idx(inp) + 1
  {
    var inp' := LC.AdvanceInputP(inp, WP.Forward);
    assert inp' == LC.Input(inp.next[1..], [inp.next[0]] + inp.pref);
    ReverseProps(inp.pref);
    ReverseProps([inp.next[0]] + inp.pref);
    assert [inp.next[0]] + inp.next[1..] == inp.next;
  }

  // ==========================================================================
  // THE CORE LEMMA. On the highest-priority (TreeRes) path, an action stack
  // that only ever reads P-characters consumes exactly P-characters, advances
  // the position monotonically, and leaves the group map untouched.
  // ==========================================================================
  lemma PConsume(rer: LW.RegExpRecord, P: char -> bool, acts: LS.Actions, inp: LC.Input,
                 gm: LG.GroupMap, t: LT.Tree, inpF: LC.Input, gmF: LG.GroupMap)
    requires !rer.ignoreCase
    requires PActions(rer, acts, P)
    requires LS.IsTree(rer, acts, inp, gm, WP.Forward, t)
    requires LT.TreeRes(t, gm, inp, WP.Forward) == Some((inpF, gmF))
    ensures LC.InputStr(inpF) == LC.InputStr(inp)
    ensures LC.Idx(inp) <= LC.Idx(inpF) <= |LC.InputStr(inp)|
    ensures gmF == gm
    ensures forall k :: LC.Idx(inp) <= k < LC.Idx(inpF) ==> P(LC.InputStr(inp)[k])
    decreases LS.TreeSize(t), LS.ActionsRegexSize(acts)
  {
    if |acts| == 0 {
      // t == Match; TreeRes freezes (inp, gm), so inpF == inp and gmF == gm.
      assert t == LT.Match;
      assert LT.TreeRes(t, gm, inp, WP.Forward) == Some((inp, gm));
      assert inpF == inp && gmF == gm;
      ReverseProps(inp.pref);   // |InputStr(inp)| == |inp.pref| + |inp.next| >= Idx(inp)
      return;
    }
    var cont := acts[1..];
    assert PActions(rer, cont, P);
    match acts[0]
    case Aclose(gid) =>
      assert PAction(rer, acts[0], P);   // false: contradiction
    case Acheck(sc) =>
      if SS.StrictSuffix(inp, sc, WP.Forward) {
        match t
        case Progress(tc) =>
          PConsume(rer, P, cont, inp, gm, tc, inpF, gmF);
        case _ =>
      }
    case Areg(r) => {
      match r {
        case Epsilon => {
          PConsume(rer, P, cont, inp, gm, t, inpF, gmF);
        }
        case Character(cd) => {
          match LC.ReadChar(rer, cd, inp, WP.Forward) {
            case Some(pair) => {
              match t {
                case Read(c, tc) => {
                  assert |inp.next| > 0 && LC.CharMatch(rer, inp.next[0], cd);
                  InputStrIdx(inp);
                  AdvancePreservesStr(inp);
                  assert P(inp.next[0]);   // CdOnly(rer, cd, P) + the CharMatch fact
                  PConsume(rer, P, cont, pair.1, gm, tc, inpF, gmF);
                }
                case _ => {}
              }
            }
            case None => {}
          }
        }
        case Sequence(r1, r2) => {
          var acts2 := [LS.Areg(r1), LS.Areg(r2)] + cont;
          assert PActions(rer, acts2, P);
          assert acts == [LS.Areg(L.Sequence(r1, r2))] + cont;
          assert LS.IsTree(rer, acts2, inp, gm, WP.Forward, t);   // tree_sequence, Forward
          SeqSizeTwo(r1, r2, cont);
          PConsume(rer, P, acts2, inp, gm, t, inpF, gmF);
        }
        case Quantified(greedy, min, delta, r1) => {
          var gidl := L.DefGroups(r1);
          POnlyNoGroups(rer, r1, P);
          assert gidl == [];
          GMResetEmpty(gm);
          if min > 0 {
            match t {
              case GroupActionT(g, tc) => {
                var acts2 := [LS.Areg(r1), LS.Areg(L.Quantified(greedy, min - 1, delta, r1))] + cont;
                assert PActions(rer, acts2, P);
                PConsume(rer, P, acts2, inp, gm, tc, inpF, gmF);
              }
              case _ => {}
            }
          } else if delta == LN.NN(0) {
            PConsume(rer, P, cont, inp, gm, t, inpF, gmF);
          } else {
            var plus := LN.NoISub(delta, 1);
            var iterActs := [LS.Areg(r1), LS.Acheck(inp), LS.Areg(L.Quantified(greedy, 0, plus, r1))] + cont;
            assert PActions(rer, iterActs, P);
            match t {
              case Choice(ta, tb) => {
                var itert := if greedy then ta else tb;
                var skipt := if greedy then tb else ta;
                // Matching itert as GroupActionT unfolds IsTree (tree_quant_free):
                //   g == Reset(gidl), IsTree(iterActs, inp, GMReset(gidl,gm), ti),
                //   IsTree(cont, inp, gm, skipt).  gidl == [] so GMReset(gidl,gm) == gm.
                match itert {
                  case GroupActionT(g, ti) => {
                    assert LG.GMReset(gidl, gm) == gm;   // gidl == [] (proven above) + GMResetEmpty
                    // TreeRes(itert) = TreeRes(ti, GMUpdate(Reset([]),Idx,gm) = gm, inp).
                    assert LT.TreeRes(itert, gm, inp, WP.Forward)
                        == LT.TreeRes(ti, gm, inp, WP.Forward);
                    assert LS.TreeSize(ti) < LS.TreeSize(t);
                    assert LS.TreeSize(skipt) < LS.TreeSize(t);
                    // TreeRes(t) = Seqop(TreeRes(ta), TreeRes(tb)): the LEFT branch wins.
                    if LT.TreeRes(ta, gm, inp, WP.Forward).Some? {
                      // TreeRes(t) == TreeRes(ta)
                      if greedy {
                        PConsume(rer, P, iterActs, inp, gm, ti, inpF, gmF);
                      } else {
                        PConsume(rer, P, cont, inp, gm, skipt, inpF, gmF);
                      }
                    } else {
                      // TreeRes(t) == TreeRes(tb)
                      if greedy {
                        PConsume(rer, P, cont, inp, gm, skipt, inpF, gmF);
                      } else {
                        PConsume(rer, P, iterActs, inp, gm, ti, inpF, gmF);
                      }
                    }
                  }
                  case _ => {}
                }
              }
              case _ => {}
            }
          }
        }
        case _ => {}
      }
    }
  }

  // ==========================================================================
  // The PREFIX factoring. A P-only PREFIX `pre` of a stack `pre + cont` (with
  // `cont` arbitrary, NOT P-only) consumes only P-characters, leaves the group
  // map untouched, and factors the highest-priority path through a checkpoint
  // (inp1, tc): from (inp1, gm), `cont` alone finishes with the same leaf
  // (inpF, gmF). This is what lets us reason about a typed group embedded in a
  // larger pattern.
  // ==========================================================================
  lemma PPrefixFactors(rer: LW.RegExpRecord, P: char -> bool, pre: LS.Actions, cont: LS.Actions,
                       inp: LC.Input, gm: LG.GroupMap, t: LT.Tree,
                       inpF: LC.Input, gmF: LG.GroupMap)
      returns (inp1: LC.Input, tc: LT.Tree)
    requires !rer.ignoreCase
    requires PActions(rer, pre, P)
    requires LS.IsTree(rer, pre + cont, inp, gm, WP.Forward, t)
    requires LT.TreeRes(t, gm, inp, WP.Forward) == Some((inpF, gmF))
    ensures LS.IsTree(rer, cont, inp1, gm, WP.Forward, tc)
    ensures LT.TreeRes(tc, gm, inp1, WP.Forward) == Some((inpF, gmF))
    ensures LC.InputStr(inp1) == LC.InputStr(inp)
    ensures LC.Idx(inp) <= LC.Idx(inp1) <= |LC.InputStr(inp)|
    ensures forall k :: LC.Idx(inp) <= k < LC.Idx(inp1) ==> P(LC.InputStr(inp)[k])
    decreases LS.TreeSize(t), LS.ActionsRegexSize(pre)
  {
    if |pre| == 0 {
      assert pre + cont == cont;              // stack is exactly the boundary
      ReverseProps(inp.pref);
      inp1 := inp;
      tc := t;
      return;
    }
    var cont0 := pre[1..];                    // the remaining P-only prefix
    assert PActions(rer, cont0, P);
    assert (pre + cont)[0] == pre[0];
    assert (pre + cont)[1..] == cont0 + cont;
    match pre[0]
    case Acheck(sc) => {
      if SS.StrictSuffix(inp, sc, WP.Forward) {
        match t {
          case Progress(tcp) => {
            inp1, tc := PPrefixFactors(rer, P, cont0, cont, inp, gm, tcp, inpF, gmF);
          }
          case _ => {}
        }
      } else {
        assert t == LT.Mismatch;              // TreeRes(Mismatch) == None: contradiction
      }
    }
    case Aclose(gid) => {
      assert PAction(rer, pre[0], P);         // false: contradiction
    }
    case Areg(r) => {
      match r {
        case Epsilon => {
          inp1, tc := PPrefixFactors(rer, P, cont0, cont, inp, gm, t, inpF, gmF);
        }
        case Character(cd) => {
          match LC.ReadChar(rer, cd, inp, WP.Forward) {
            case Some(pair) => {
              match t {
                case Read(c, tcr) => {
                  assert |inp.next| > 0 && LC.CharMatch(rer, inp.next[0], cd);
                  InputStrIdx(inp);
                  AdvancePreservesStr(inp);
                  assert P(inp.next[0]);       // CdOnly(rer, cd, P) + the CharMatch fact
                  inp1, tc := PPrefixFactors(rer, P, cont0, cont, pair.1, gm, tcr, inpF, gmF);
                }
                case _ => {}
              }
            }
            case None => {
              assert t == LT.Mismatch;         // contradiction
            }
          }
        }
        case Sequence(r1, r2) => {
          var pre2 := [LS.Areg(r1), LS.Areg(r2)] + cont0;
          assert PActions(rer, pre2, P);
          assert pre + cont == [LS.Areg(L.Sequence(r1, r2))] + (cont0 + cont);
          assert pre2 + cont == [LS.Areg(r1), LS.Areg(r2)] + (cont0 + cont);
          assert LS.IsTree(rer, pre2 + cont, inp, gm, WP.Forward, t);   // tree_sequence, Forward
          SeqSizeTwo(r1, r2, cont0);
          inp1, tc := PPrefixFactors(rer, P, pre2, cont, inp, gm, t, inpF, gmF);
        }
        case Quantified(greedy, min, delta, r1) => {
          var gidl := L.DefGroups(r1);
          POnlyNoGroups(rer, r1, P);
          assert gidl == [];
          GMResetEmpty(gm);
          assert LG.GMReset(gidl, gm) == gm;
          if min > 0 {
            match t {
              case GroupActionT(g, tcq) => {
                var pre2 := [LS.Areg(r1), LS.Areg(L.Quantified(greedy, min - 1, delta, r1))] + cont0;
                assert PActions(rer, pre2, P);
                assert pre + cont
                    == [LS.Areg(L.Quantified(greedy, min, delta, r1))] + (cont0 + cont);
                assert pre2 + cont
                    == [LS.Areg(r1), LS.Areg(L.Quantified(greedy, min - 1, delta, r1))] + (cont0 + cont);
                assert LS.IsTree(rer, pre2 + cont, inp, gm, WP.Forward, tcq);  // GMReset(gidl,gm)==gm
                inp1, tc := PPrefixFactors(rer, P, pre2, cont, inp, gm, tcq, inpF, gmF);
              }
              case _ => {}
            }
          } else if delta == LN.NN(0) {
            inp1, tc := PPrefixFactors(rer, P, cont0, cont, inp, gm, t, inpF, gmF);
          } else {
            var plus := LN.NoISub(delta, 1);
            var iterPre := [LS.Areg(r1), LS.Acheck(inp), LS.Areg(L.Quantified(greedy, 0, plus, r1))] + cont0;
            assert PActions(rer, iterPre, P);
            match t {
              case Choice(ta, tb) => {
                var itert := if greedy then ta else tb;
                var skipt := if greedy then tb else ta;
                match itert {
                  case GroupActionT(g, ti) => {
                    assert LT.TreeRes(itert, gm, inp, WP.Forward)
                        == LT.TreeRes(ti, gm, inp, WP.Forward);
                    assert LS.TreeSize(ti) < LS.TreeSize(t);
                    assert LS.TreeSize(skipt) < LS.TreeSize(t);
                    assert iterPre + cont
                        == [LS.Areg(r1), LS.Acheck(inp), LS.Areg(L.Quantified(greedy, 0, plus, r1))]
                           + (cont0 + cont);
                    assert LS.IsTree(rer, iterPre + cont, inp, gm, WP.Forward, ti);   // GMReset(gidl,gm)==gm
                    if LT.TreeRes(ta, gm, inp, WP.Forward).Some? {
                      if greedy {
                        inp1, tc := PPrefixFactors(rer, P, iterPre, cont, inp, gm, ti, inpF, gmF);
                      } else {
                        inp1, tc := PPrefixFactors(rer, P, cont0, cont, inp, gm, skipt, inpF, gmF);
                      }
                    } else {
                      if greedy {
                        inp1, tc := PPrefixFactors(rer, P, cont0, cont, inp, gm, skipt, inpF, gmF);
                      } else {
                        inp1, tc := PPrefixFactors(rer, P, iterPre, cont, inp, gm, ti, inpF, gmF);
                      }
                    }
                  }
                  case _ => {}
                }
              }
              case _ => {}
            }
          }
        }
        case _ => {}
      }
    }
  }

  // ActionsRegexSize([Areg(r1), Areg(r2)] + cont) < ActionsRegexSize([Areg(Sequence(r1,r2))] + cont)
  lemma SeqSizeTwo(r1: L.Regex, r2: L.Regex, cont: LS.Actions)
    ensures LS.ActionsRegexSize([LS.Areg(r1), LS.Areg(r2)] + cont)
          < LS.ActionsRegexSize([LS.Areg(L.Sequence(r1, r2))] + cont)
  {
    assert ([LS.Areg(r1), LS.Areg(r2)] + cont)[1..] == [LS.Areg(r2)] + cont;
    assert ([LS.Areg(r2)] + cont)[1..] == cont;
    assert ([LS.Areg(L.Sequence(r1, r2))] + cont)[1..] == cont;
  }

  // ==========================================================================
  // The GROUP read-off. A capture group whose body is P-only, taken as the
  // WHOLE regex, records a P-only span: on the winning path group `gid` ends
  // up mapped to [Idx(inp), Idx(inpF)] and every character there satisfies P.
  // ==========================================================================
  lemma GroupContentP(rer: LW.RegExpRecord, P: char -> bool, gid: LG.GroupId, r1: L.Regex,
                      inp: LC.Input, gm: LG.GroupMap, t: LT.Tree,
                      inpF: LC.Input, gmF: LG.GroupMap)
    requires !rer.ignoreCase
    requires POnly(rer, r1, P)
    requires LS.IsTree(rer, [LS.Areg(L.Group(gid, r1))], inp, gm, WP.Forward, t)
    requires LT.TreeRes(t, gm, inp, WP.Forward) == Some((inpF, gmF))
    ensures LC.InputStr(inpF) == LC.InputStr(inp)
    ensures LC.Idx(inp) <= LC.Idx(inpF) <= |LC.InputStr(inp)|
    ensures LG.Find(gid, gmF) == Some(LG.Range(LC.Idx(inp), Some(LC.Idx(inpF))))
    ensures forall k :: LC.Idx(inp) <= k < LC.Idx(inpF) ==> P(LC.InputStr(inp)[k])
  {
    // tree_group: t == GroupActionT(Open(gid), tc); the body stack is
    // [Areg(r1), Aclose(gid)] with gid opened at Idx(inp).
    match t {
      case GroupActionT(g, tc) => {
        assert g == LG.Open(gid);
        var gmO := LG.GMOpen(LC.Idx(inp), gid, gm);
        assert [LS.Areg(L.Group(gid, r1))][1..] == [];               // cont == []
        assert [LS.Areg(r1), LS.Aclose(gid)] + [] == [LS.Areg(r1)] + [LS.Aclose(gid)];
        assert LS.IsTree(rer, [LS.Areg(r1)] + [LS.Aclose(gid)], inp, gmO, WP.Forward, tc);
        assert LT.TreeRes(t, gm, inp, WP.Forward) == LT.TreeRes(tc, gmO, inp, WP.Forward);
        // Factor the P-only body; checkpoint inp1 is where the P-chars end.
        var inp1, tc1 := PPrefixFactors(rer, P, [LS.Areg(r1)], [LS.Aclose(gid)],
                                        inp, gmO, tc, inpF, gmF);
        // tree_close: tc1 == GroupActionT(Close(gid), Match); closing records
        // gid |-> [Idx(inp), Idx(inp1)] (startIdx <= currIdx since reads only advance).
        match tc1 {
          case GroupActionT(g2, tc2) => {
            assert g2 == LG.Close(gid);
            assert [LS.Aclose(gid)][1..] == [];
            assert tc2 == LT.Match;
            var gmC := LG.GMClose(LC.Idx(inp1), gid, gmO);
            assert LG.Find(gid, gmO) == Some(LG.Range(LC.Idx(inp), None));
            assert LT.TreeRes(tc1, gmO, inp1, WP.Forward) == Some((inp1, gmC));
            assert inpF == inp1 && gmF == gmC;
            assert LG.Find(gid, gmF) == Some(LG.Range(LC.Idx(inp), Some(LC.Idx(inpF))));
          }
          case _ => {}
        }
      }
      case _ => {}
    }
  }

  // ==========================================================================
  // GROUP-MAP PRESERVATION. If no node of a tree touches group `gid`, the
  // winning leaf's map agrees with the starting map on `gid`.
  // ==========================================================================
  predicate GidUntouched(a: LG.GroupAction, gid: LG.GroupId) {
    match a
    case Open(g) => g != gid
    case Close(g) => g != gid
    case Reset(gs) => gid !in gs
  }

  predicate NoGidAction(t: LT.Tree, gid: LG.GroupId)
    decreases t
  {
    match t
    case Mismatch => true
    case Match => true
    case Choice(t1, t2) => NoGidAction(t1, gid) && NoGidAction(t2, gid)
    case Read(_, t1) => NoGidAction(t1, gid)
    case ReadBackRef(_, t1) => NoGidAction(t1, gid)
    case Progress(t1) => NoGidAction(t1, gid)
    case AnchorPass(_, t1) => NoGidAction(t1, gid)
    case GroupActionT(a, t1) => GidUntouched(a, gid) && NoGidAction(t1, gid)
    case LK(_, tlk, t1) => NoGidAction(tlk, gid) && NoGidAction(t1, gid)
    case LKFail(_, tlk) => NoGidAction(tlk, gid)
  }

  lemma GMUpdatePreservesGid(a: LG.GroupAction, idx: nat, gm: LG.GroupMap, gid: LG.GroupId)
    requires GidUntouched(a, gid)
    ensures LG.Find(gid, LG.GMUpdate(a, idx, gm)) == LG.Find(gid, gm)
  {
    match a
    case Reset(gs) => {
      assert gid !in (set g | g in gs);   // GMReset removes exactly this set
    }
    case _ =>
  }

  lemma TreeResPreservesGid(t: LT.Tree, gm: LG.GroupMap, inp: LC.Input, dir: WP.Direction, gid: LG.GroupId)
    requires NoGidAction(t, gid)
    requires LT.TreeRes(t, gm, inp, dir).Some?
    ensures LG.Find(gid, LT.TreeRes(t, gm, inp, dir).value.1) == LG.Find(gid, gm)
    decreases t
  {
    match t
    case Match =>
    case Choice(t1, t2) => {
      if LT.TreeRes(t1, gm, inp, dir).Some? {
        TreeResPreservesGid(t1, gm, inp, dir, gid);
      } else {
        TreeResPreservesGid(t2, gm, inp, dir, gid);
      }
    }
    case Read(_, t1) => TreeResPreservesGid(t1, gm, LC.AdvanceInputP(inp, dir), dir, gid);
    case ReadBackRef(brStr, t1) =>
      TreeResPreservesGid(t1, gm, LC.AdvanceInputN(inp, |brStr|, dir), dir, gid);
    case Progress(t1) => TreeResPreservesGid(t1, gm, inp, dir, gid);
    case AnchorPass(_, t1) => TreeResPreservesGid(t1, gm, inp, dir, gid);
    case GroupActionT(a, t1) => {
      GMUpdatePreservesGid(a, LC.Idx(inp), gm, gid);
      TreeResPreservesGid(t1, LG.GMUpdate(a, LC.Idx(inp), gm), inp, dir, gid);
    }
    case LK(lk, tlk, t1) => {
      if L.Positivity(lk) {
        match LT.TreeRes(tlk, gm, inp, L.LkDir(lk)) {
          case Some(pair) => {
            TreeResPreservesGid(tlk, gm, inp, L.LkDir(lk), gid);      // Find(gid,pair.1)==Find(gid,gm)
            TreeResPreservesGid(t1, pair.1, inp, dir, gid);           // then t1 preserves it
          }
          case None => {}   // overall None: contradicts .Some?
        }
      } else {
        match LT.TreeRes(tlk, gm, inp, L.LkDir(lk)) {
          case None => TreeResPreservesGid(t1, gm, inp, dir, gid);
          case Some(_) => {}   // overall None: contradicts .Some?
        }
      }
    }
    case Mismatch =>     // TreeRes == None: contradicts .Some?
    case LKFail(_, _) =>  // TreeRes == None: contradicts .Some?
  }

  // ---- keystone: a stack that never mentions gid yields a gid-free tree -----
  predicate GidFreeAction(a: LS.Action, gid: LG.GroupId) {
    match a
    case Areg(r) => gid !in L.DefGroups(r)
    case Acheck(_) => true
    case Aclose(g) => g != gid
  }
  predicate GidFreeActions(acts: LS.Actions, gid: LG.GroupId) {
    forall i :: 0 <= i < |acts| ==> GidFreeAction(acts[i], gid)
  }

  lemma TreeFromGidFreeStack(rer: LW.RegExpRecord, acts: LS.Actions, inp: LC.Input,
                             gm: LG.GroupMap, dir: WP.Direction, t: LT.Tree, gid: LG.GroupId)
    requires LS.IsTree(rer, acts, inp, gm, dir, t)
    requires GidFreeActions(acts, gid)
    ensures NoGidAction(t, gid)
    decreases LS.TreeSize(t), LS.ActionsRegexSize(acts)
  {
    if |acts| == 0 {
      assert t == LT.Match;
      return;
    }
    var cont := acts[1..];
    assert GidFreeActions(cont, gid);
    match acts[0]
    case Acheck(sc) => {
      if SS.StrictSuffix(inp, sc, dir) {
        match t { case Progress(tc) => TreeFromGidFreeStack(rer, cont, inp, gm, dir, tc, gid); case _ => }
      } else {
        assert t == LT.Mismatch;
      }
    }
    case Aclose(g) => {
      assert g != gid;                              // GidFreeAction
      match t {
        case GroupActionT(a, tc) =>
          TreeFromGidFreeStack(rer, cont, inp, LG.GMClose(LC.Idx(inp), g, gm), dir, tc, gid);
        case _ =>
      }
    }
    case Areg(r) => {
      assert gid !in L.DefGroups(r);                // GidFreeAction
      match r {
        case Epsilon => TreeFromGidFreeStack(rer, cont, inp, gm, dir, t, gid);
        case Character(cd) => {
          match LC.ReadChar(rer, cd, inp, dir) {
            case Some(pair) =>
              match t { case Read(c, tc) => TreeFromGidFreeStack(rer, cont, pair.1, gm, dir, tc, gid); case _ => }
            case None => assert t == LT.Mismatch;
          }
        }
        case Disjunction(r1, r2) => {
          match t {
            case Choice(ta, tb) => {
              TreeFromGidFreeStack(rer, [LS.Areg(r1)] + cont, inp, gm, dir, ta, gid);
              TreeFromGidFreeStack(rer, [LS.Areg(r2)] + cont, inp, gm, dir, tb, gid);
            }
            case _ =>
          }
        }
        case Sequence(r1, r2) => {
          assert acts == [LS.Areg(L.Sequence(r1, r2))] + cont;
          match dir {
            case Forward => {
              SeqSizeTwo(r1, r2, cont);
              TreeFromGidFreeStack(rer, [LS.Areg(r1), LS.Areg(r2)] + cont, inp, gm, dir, t, gid);
            }
            case Backward => {
              assert ([LS.Areg(r2), LS.Areg(r1)] + cont)[1..] == [LS.Areg(r1)] + cont;
              assert ([LS.Areg(r1)] + cont)[1..] == cont;
              assert LS.ActionsRegexSize([LS.Areg(r2), LS.Areg(r1)] + cont)
                  == LS.RegexSize(r2) + LS.RegexSize(r1) + LS.ActionsRegexSize(cont);
              assert LS.ActionsRegexSize(acts)
                  == LS.RegexSize(L.Sequence(r1, r2)) + LS.ActionsRegexSize(cont);
              TreeFromGidFreeStack(rer, [LS.Areg(r2), LS.Areg(r1)] + cont, inp, gm, dir, t, gid);
            }
          }
        }
        case Quantified(greedy, min, delta, r1) => {
          var gidl := L.DefGroups(r1);
          if min > 0 {
            match t {
              case GroupActionT(a, tc) =>
                TreeFromGidFreeStack(rer, [LS.Areg(r1), LS.Areg(L.Quantified(greedy, min - 1, delta, r1))] + cont,
                                     inp, LG.GMReset(gidl, gm), dir, tc, gid);
              case _ =>
            }
          } else if delta == LN.NN(0) {
            TreeFromGidFreeStack(rer, cont, inp, gm, dir, t, gid);
          } else {
            var plus := LN.NoISub(delta, 1);
            var iterActs := [LS.Areg(r1), LS.Acheck(inp), LS.Areg(L.Quantified(greedy, 0, plus, r1))] + cont;
            match t {
              case Choice(ta, tb) => {
                var itert := if greedy then ta else tb;
                var skipt := if greedy then tb else ta;
                match itert {
                  case GroupActionT(a, ti) => {
                    assert LS.TreeSize(ti) < LS.TreeSize(t);
                    assert LS.TreeSize(skipt) < LS.TreeSize(t);
                    TreeFromGidFreeStack(rer, iterActs, inp, LG.GMReset(gidl, gm), dir, ti, gid);
                    TreeFromGidFreeStack(rer, cont, inp, gm, dir, skipt, gid);
                  }
                  case _ =>
                }
              }
              case _ =>
            }
          }
        }
        case Group(g, r1) => {
          assert g != gid;                          // gid !in [g] + DefGroups(r1)
          match t {
            case GroupActionT(a, tc) =>
              TreeFromGidFreeStack(rer, [LS.Areg(r1), LS.Aclose(g)] + cont,
                                   inp, LG.GMOpen(LC.Idx(inp), g, gm), dir, tc, gid);
            case _ =>
          }
        }
        case LookaroundR(lk, r1) => {
          match t {
            case LK(lk2, tlk, tc) => {
              TreeFromGidFreeStack(rer, [LS.Areg(r1)], inp, gm, L.LkDir(lk), tlk, gid);
              var lr := LS.LkResult(lk, tlk, gm, inp);
              if lr.Some? {
                TreeFromGidFreeStack(rer, cont, inp, lr.value, dir, tc, gid);
              }
            }
            case LKFail(lk2, tlk) => {
              TreeFromGidFreeStack(rer, [LS.Areg(r1)], inp, gm, L.LkDir(lk), tlk, gid);
            }
            case _ =>
          }
        }
        case AnchorR(a) => {
          match t {
            case AnchorPass(a2, tc) => TreeFromGidFreeStack(rer, cont, inp, gm, dir, tc, gid);
            case _ =>   // Mismatch
          }
        }
        case Backreference(g) => {
          match LS.ReadBackref(rer, gm, g, inp, dir) {
            case Some(pair) =>
              match t {
                case ReadBackRef(s, tc) => TreeFromGidFreeStack(rer, cont, pair.1, gm, dir, tc, gid);
                case _ =>
              }
            case None => assert t == LT.Mismatch;
          }
        }
      }
    }
  }

  // ==========================================================================
  // The EMBEDDED typed group. A capture Group(gid, r1) with P-only body at the
  // head of a stack whose continuation never mentions gid records a P-only
  // span in the FINAL leaf.
  // ==========================================================================
  lemma GroupContentPCont(rer: LW.RegExpRecord, P: char -> bool, gid: LG.GroupId, r1: L.Regex,
                          cont: LS.Actions, inp: LC.Input, gm: LG.GroupMap,
                          t: LT.Tree, inpF: LC.Input, gmF: LG.GroupMap)
    requires !rer.ignoreCase
    requires POnly(rer, r1, P)
    requires GidFreeActions(cont, gid)
    requires LS.IsTree(rer, [LS.Areg(L.Group(gid, r1))] + cont, inp, gm, WP.Forward, t)
    requires LT.TreeRes(t, gm, inp, WP.Forward) == Some((inpF, gmF))
    ensures exists e: nat ::
              (LG.Find(gid, gmF) == Some(LG.Range(LC.Idx(inp), Some(e)))
               && LC.Idx(inp) <= e <= |LC.InputStr(inp)|
               && (forall k :: LC.Idx(inp) <= k < e ==> P(LC.InputStr(inp)[k])))
  {
    match t {
      case GroupActionT(g, tc) => {
        assert g == LG.Open(gid);
        var gmO := LG.GMOpen(LC.Idx(inp), gid, gm);
        assert ([LS.Areg(L.Group(gid, r1))] + cont)[1..] == cont;
        assert [LS.Areg(r1), LS.Aclose(gid)] + cont == [LS.Areg(r1)] + ([LS.Aclose(gid)] + cont);
        assert LS.IsTree(rer, [LS.Areg(r1)] + ([LS.Aclose(gid)] + cont), inp, gmO, WP.Forward, tc);
        assert LT.TreeRes(t, gm, inp, WP.Forward) == LT.TreeRes(tc, gmO, inp, WP.Forward);
        // P-only body runs to checkpoint inp1 (map still gmO)
        var inp1, tc1 := PPrefixFactors(rer, P, [LS.Areg(r1)], [LS.Aclose(gid)] + cont,
                                        inp, gmO, tc, inpF, gmF);
        // tree_close then the continuation
        match tc1 {
          case GroupActionT(g2, tc2) => {
            assert g2 == LG.Close(gid);
            assert ([LS.Aclose(gid)] + cont)[1..] == cont;
            var gmC := LG.GMClose(LC.Idx(inp1), gid, gmO);
            assert LG.Find(gid, gmO) == Some(LG.Range(LC.Idx(inp), None));
            assert LC.Idx(inp) <= LC.Idx(inp1);
            assert LG.Find(gid, gmC) == Some(LG.Range(LC.Idx(inp), Some(LC.Idx(inp1))));
            // TreeRes(tc1) = TreeRes(tc2 with gmC); and IsTree(cont, inp1, gmC, tc2)
            assert LS.IsTree(rer, cont, inp1, gmC, WP.Forward, tc2);
            assert LT.TreeRes(tc2, gmC, inp1, WP.Forward) == Some((inpF, gmF));
            // continuation never mentions gid => it leaves gid's range intact
            TreeFromGidFreeStack(rer, cont, inp1, gmC, WP.Forward, tc2, gid);
            TreeResPreservesGid(tc2, gmC, inp1, WP.Forward, gid);
            assert LG.Find(gid, gmF) == LG.Find(gid, gmC);
            assert LC.Idx(inp1) <= |LC.InputStr(inp)|;
            assert LG.Find(gid, gmF) == Some(LG.Range(LC.Idx(inp), Some(LC.Idx(inp1))));
          }
          case _ => {}
        }
      }
      case _ => {}
    }
  }

  // ==========================================================================
  // Winning-path navigation to SURFACE the typed group. The "simple fragment"
  // (Sequence/Quantified/Group/Character/Epsilon), plus: `rc` holds gid as
  // exactly one Group(gid, r1), never under a quantifier (whose per-iteration
  // Reset would clear the group — see the digit-capture README).
  // ==========================================================================
  predicate SimpleFragRe(r: L.Regex)
    decreases r
  {
    match r
    case Epsilon => true
    case Character(_) => true
    case Sequence(a, b) => SimpleFragRe(a) && SimpleFragRe(b)
    case Quantified(_, _, _, body) => SimpleFragRe(body)
    case Group(_, body) => SimpleFragRe(body)
    case _ => false      // Disjunction / LookaroundR / AnchorR / Backreference
  }
  predicate SimpleFragAction(a: LS.Action) {
    match a case Areg(r) => SimpleFragRe(r) case Acheck(_) => true case Aclose(_) => true
  }
  predicate SimpleFragActions(acts: LS.Actions) {
    forall i :: 0 <= i < |acts| ==> SimpleFragAction(acts[i])
  }

  // rc holds gid as exactly one Group(gid, r1), never under a quantifier.
  // PURELY STRUCTURAL (unlike the digit-capture original, the body's content
  // condition is NOT baked in — pass POnly separately where needed, or don't,
  // for bounds-only conclusions).
  predicate GidContainer(r: L.Regex, gid: LG.GroupId, r1: L.Regex)
    requires SimpleFragRe(r)
    decreases r
  {
    match r
    case Group(g, body) =>
      if g == gid then body == r1 && gid !in L.DefGroups(r1)
      else gid in L.DefGroups(body) && GidContainer(body, gid, r1)
    case Sequence(a, b) =>
      if gid in L.DefGroups(a) then GidContainer(a, gid, r1) && gid !in L.DefGroups(b)
      else gid in L.DefGroups(b) && GidContainer(b, gid, r1)
    case _ => false      // Quantified (forbidden), Character/Epsilon (no groups)
  }

  lemma RunToGroup(rer: LW.RegExpRecord, P: char -> bool, str: string, pre: LS.Actions,
                   rc: L.Regex, suf: LS.Actions, gid: LG.GroupId, r1: L.Regex, inp: LC.Input,
                   gm: LG.GroupMap, t: LT.Tree, inpF: LC.Input, gmF: LG.GroupMap)
    requires !rer.ignoreCase && POnly(rer, r1, P)
    requires SimpleFragActions(pre) && SimpleFragRe(rc) && SimpleFragActions(suf)
    requires GidContainer(rc, gid, r1)
    requires GidFreeActions(pre, gid) && GidFreeActions(suf, gid)
    requires LG.Find(gid, gm).None?
    requires LC.InputStr(inp) == str
    requires LS.IsTree(rer, pre + [LS.Areg(rc)] + suf, inp, gm, WP.Forward, t)
    requires LT.TreeRes(t, gm, inp, WP.Forward) == Some((inpF, gmF))
    ensures exists s: nat, e: nat ::
              (LG.Find(gid, gmF) == Some(LG.Range(s, Some(e)))
               && s <= e <= |str|
               && (forall k :: s <= k < e ==> P(str[k])))
    decreases LS.TreeSize(t), LS.ActionsRegexSize(pre + [LS.Areg(rc)] + suf)
  {
    if |pre| == 0 {
      assert pre + [LS.Areg(rc)] + suf == [LS.Areg(rc)] + suf;
      match rc {
        case Group(g, body) => {
          if g == gid {
            // the target group: content satisfies P, continuation is gid-free
            GroupContentPCont(rer, P, gid, r1, suf, inp, gm, t, inpF, gmF);
          } else {
            // a different group opens; recurse with the target now inside body
            match t {
              case GroupActionT(ga, tc) => {
                var gmO := LG.GMOpen(LC.Idx(inp), g, gm);
                GMUpdatePreservesGid(LG.Open(g), LC.Idx(inp), gm, gid);
                assert ([LS.Areg(rc)] + suf)[1..] == suf;
                assert [LS.Areg(body), LS.Aclose(g)] + suf == [] + [LS.Areg(body)] + ([LS.Aclose(g)] + suf);
                RunToGroup(rer, P, str, [], body, [LS.Aclose(g)] + suf, gid, r1, inp, gmO, tc, inpF, gmF);
              }
              case _ =>
            }
          }
        }
        case Sequence(a, b) => {
          SeqSizeTwo(a, b, suf);
          assert [LS.Areg(a), LS.Areg(b)] + suf == [] + [LS.Areg(a)] + ([LS.Areg(b)] + suf);
          if gid in L.DefGroups(a) {
            RunToGroup(rer, P, str, [], a, [LS.Areg(b)] + suf, gid, r1, inp, gm, t, inpF, gmF);
          } else {
            assert [LS.Areg(a)] + [LS.Areg(b)] + suf == [LS.Areg(a), LS.Areg(b)] + suf;
            RunToGroup(rer, P, str, [LS.Areg(a)], b, suf, gid, r1, inp, gm, t, inpF, gmF);
          }
        }
        case _ =>   // Quantified/Character/Epsilon: GidContainer(rc) is false -> vacuous
      }
    } else {
      var rest := pre[1..] + [LS.Areg(rc)] + suf;
      assert pre + [LS.Areg(rc)] + suf == [pre[0]] + rest;
      assert GidFreeActions(pre[1..], gid) && SimpleFragActions(pre[1..]);
      match pre[0] {
        case Acheck(sc) => {
          if SS.StrictSuffix(inp, sc, WP.Forward) {
            match t { case Progress(tc) => RunToGroup(rer, P, str, pre[1..], rc, suf, gid, r1, inp, gm, tc, inpF, gmF); case _ => }
          } else { assert t == LT.Mismatch; }
        }
        case Aclose(g) => {
          assert g != gid;
          match t {
            case GroupActionT(ga, tc) => {
              var gmC := LG.GMClose(LC.Idx(inp), g, gm);
              GMUpdatePreservesGid(LG.Close(g), LC.Idx(inp), gm, gid);
              RunToGroup(rer, P, str, pre[1..], rc, suf, gid, r1, inp, gmC, tc, inpF, gmF);
            }
            case _ =>
          }
        }
        case Areg(r) => {
          assert gid !in L.DefGroups(r);
          match r {
            case Epsilon => RunToGroup(rer, P, str, pre[1..], rc, suf, gid, r1, inp, gm, t, inpF, gmF);
            case Character(cd) => {
              match LC.ReadChar(rer, cd, inp, WP.Forward) {
                case Some(pair) => {
                  match t {
                    case Read(c, tc) => {
                      AdvancePreservesStr(inp);
                      RunToGroup(rer, P, str, pre[1..], rc, suf, gid, r1, pair.1, gm, tc, inpF, gmF);
                    }
                    case _ =>
                  }
                }
                case None => assert t == LT.Mismatch;
              }
            }
            case Sequence(a, b) => {
              var pre2 := [LS.Areg(a), LS.Areg(b)] + pre[1..];
              assert pre2 + [LS.Areg(rc)] + suf == [LS.Areg(a), LS.Areg(b)] + rest;
              SeqSizeTwo(a, b, rest);
              RunToGroup(rer, P, str, pre2, rc, suf, gid, r1, inp, gm, t, inpF, gmF);
            }
            case Group(g, body) => {
              assert g != gid;
              match t {
                case GroupActionT(ga, tc) => {
                  var gmO := LG.GMOpen(LC.Idx(inp), g, gm);
                  GMUpdatePreservesGid(LG.Open(g), LC.Idx(inp), gm, gid);
                  var pre2 := [LS.Areg(body), LS.Aclose(g)] + pre[1..];
                  assert pre2 + [LS.Areg(rc)] + suf == [LS.Areg(body), LS.Aclose(g)] + rest;
                  RunToGroup(rer, P, str, pre2, rc, suf, gid, r1, inp, gmO, tc, inpF, gmF);
                }
                case _ =>
              }
            }
            case Quantified(greedy, min, delta, body) => {
              var gidl := L.DefGroups(body);
              GMUpdatePreservesGid(LG.Reset(gidl), LC.Idx(inp), gm, gid);
              var gmR := LG.GMReset(gidl, gm);
              if min > 0 {
                match t {
                  case GroupActionT(ga, tc) => {
                    var pre2 := [LS.Areg(body), LS.Areg(L.Quantified(greedy, min - 1, delta, body))] + pre[1..];
                    assert pre2 + [LS.Areg(rc)] + suf
                        == [LS.Areg(body), LS.Areg(L.Quantified(greedy, min - 1, delta, body))] + rest;
                    assert LS.IsTree(rer, pre2 + [LS.Areg(rc)] + suf, inp, gmR, WP.Forward, tc);
                    RunToGroup(rer, P, str, pre2, rc, suf, gid, r1, inp, gmR, tc, inpF, gmF);
                  }
                  case _ =>
                }
              } else if delta == LN.NN(0) {
                RunToGroup(rer, P, str, pre[1..], rc, suf, gid, r1, inp, gm, t, inpF, gmF);
              } else {
                var plus := LN.NoISub(delta, 1);
                var iterPre := [LS.Areg(body), LS.Acheck(inp), LS.Areg(L.Quantified(greedy, 0, plus, body))] + pre[1..];
                match t {
                  case Choice(ta, tb) => {
                    var itert := if greedy then ta else tb;
                    var skipt := if greedy then tb else ta;
                    match itert {
                      case GroupActionT(ga, ti) => {
                        assert LS.TreeSize(ti) < LS.TreeSize(t);
                        assert LS.TreeSize(skipt) < LS.TreeSize(t);
                        assert iterPre + [LS.Areg(rc)] + suf
                            == [LS.Areg(body), LS.Acheck(inp), LS.Areg(L.Quantified(greedy, 0, plus, body))] + rest;
                        assert LS.IsTree(rer, iterPre + [LS.Areg(rc)] + suf, inp, gmR, WP.Forward, ti);
                        if LT.TreeRes(ta, gm, inp, WP.Forward).Some? {
                          if greedy { RunToGroup(rer, P, str, iterPre, rc, suf, gid, r1, inp, gmR, ti, inpF, gmF); }
                          else { RunToGroup(rer, P, str, pre[1..], rc, suf, gid, r1, inp, gm, skipt, inpF, gmF); }
                        } else {
                          if greedy { RunToGroup(rer, P, str, pre[1..], rc, suf, gid, r1, inp, gm, skipt, inpF, gmF); }
                          else { RunToGroup(rer, P, str, iterPre, rc, suf, gid, r1, inp, gmR, ti, inpF, gmF); }
                        }
                      }
                      case _ =>
                    }
                  }
                  case _ =>
                }
              }
            }
            case _ =>   // out of the simple fragment: SimpleFragRe(r) is false -> vacuous
          }
        }
      }
    }
  }

  // ==========================================================================
  // THE ALTERNATION LIFT. The simple fragment extended with Disjunction, and
  // the navigation lemma over it. The price of `|`: an untaken alternative
  // leaves the group UNSET, so the conclusion weakens to "unset, or set with
  // P-only in-range content". (A group under a quantifier stays out of scope:
  // per-iteration Reset needs a was-reset invariant — see the GUIDE.)
  // ==========================================================================
  predicate AltFragRe(r: L.Regex)
    decreases r
  {
    match r
    case Epsilon => true
    case Character(_) => true
    case Disjunction(a, b) => AltFragRe(a) && AltFragRe(b)
    case Sequence(a, b) => AltFragRe(a) && AltFragRe(b)
    case Quantified(_, _, _, body) => AltFragRe(body)
    case Group(_, body) => AltFragRe(body)
    case AnchorR(_) => true      // anchors: zero-width, no groups — free here
    case _ => false      // LookaroundR / Backreference
  }
  predicate AltFragAction(a: LS.Action) {
    match a case Areg(r) => AltFragRe(r) case Acheck(_) => true case Aclose(_) => true
  }
  predicate AltFragActions(acts: LS.Actions) {
    forall i :: 0 <= i < |acts| ==> AltFragAction(acts[i])
  }

  /** The simple fragment embeds in the alternation fragment. */
  lemma SimpleFragIsAltFrag(r: L.Regex)
    requires SimpleFragRe(r)
    ensures AltFragRe(r)
    decreases r
  {
    match r
    case Sequence(a, b) => SimpleFragIsAltFrag(a); SimpleFragIsAltFrag(b);
    case Quantified(_, _, _, body) => SimpleFragIsAltFrag(body);
    case Group(_, body) => SimpleFragIsAltFrag(body);
    case _ =>
  }

  /** The P-only fragment embeds in the simple fragment... */
  lemma POnlyIsSimpleFrag(rer: LW.RegExpRecord, r: L.Regex, P: char -> bool)
    requires POnly(rer, r, P)
    ensures SimpleFragRe(r)
    decreases r
  {
    match r
    case Sequence(a, b) => POnlyIsSimpleFrag(rer, a, P); POnlyIsSimpleFrag(rer, b, P);
    case Quantified(_, _, _, body) => POnlyIsSimpleFrag(rer, body, P);
    case _ =>
  }

  /** ... and hence in the alternation fragment too. */
  lemma POnlyIsAltFrag(rer: LW.RegExpRecord, r: L.Regex, P: char -> bool)
    requires POnly(rer, r, P)
    ensures AltFragRe(r)
  {
    POnlyIsSimpleFrag(rer, r, P);
    SimpleFragIsAltFrag(r);
  }

  // rc holds gid as exactly one Group(gid, r1), never under a quantifier —
  // but now possibly inside ONE arm of a Disjunction.
  predicate GidContainerAlt(r: L.Regex, gid: LG.GroupId, r1: L.Regex)
    requires AltFragRe(r)
    decreases r
  {
    match r
    case Group(g, body) =>
      if g == gid then body == r1 && gid !in L.DefGroups(r1)
      else gid in L.DefGroups(body) && GidContainerAlt(body, gid, r1)
    case Sequence(a, b) =>
      if gid in L.DefGroups(a) then GidContainerAlt(a, gid, r1) && gid !in L.DefGroups(b)
      else gid in L.DefGroups(b) && GidContainerAlt(b, gid, r1)
    case Disjunction(a, b) =>
      if gid in L.DefGroups(a) then GidContainerAlt(a, gid, r1) && gid !in L.DefGroups(b)
      else gid in L.DefGroups(b) && GidContainerAlt(b, gid, r1)
    case _ => false      // Quantified (forbidden), Character/Epsilon (no groups)
  }

  lemma RunToGroupAlt(rer: LW.RegExpRecord, P: char -> bool, str: string, pre: LS.Actions,
                      rc: L.Regex, suf: LS.Actions, gid: LG.GroupId, r1: L.Regex, inp: LC.Input,
                      gm: LG.GroupMap, t: LT.Tree, inpF: LC.Input, gmF: LG.GroupMap)
    requires !rer.ignoreCase && POnly(rer, r1, P)
    requires AltFragActions(pre) && AltFragRe(rc) && AltFragActions(suf)
    requires GidContainerAlt(rc, gid, r1)
    requires GidFreeActions(pre, gid) && GidFreeActions(suf, gid)
    requires LG.Find(gid, gm).None?
    requires LC.InputStr(inp) == str
    requires LS.IsTree(rer, pre + [LS.Areg(rc)] + suf, inp, gm, WP.Forward, t)
    requires LT.TreeRes(t, gm, inp, WP.Forward) == Some((inpF, gmF))
    ensures LG.Find(gid, gmF).None?
         || exists s: nat, e: nat ::
              (LG.Find(gid, gmF) == Some(LG.Range(s, Some(e)))
               && s <= e <= |str|
               && (forall k :: s <= k < e ==> P(str[k])))
    decreases LS.TreeSize(t), LS.ActionsRegexSize(pre + [LS.Areg(rc)] + suf)
  {
    if |pre| == 0 {
      assert pre + [LS.Areg(rc)] + suf == [LS.Areg(rc)] + suf;
      match rc {
        case Group(g, body) => {
          if g == gid {
            GroupContentPCont(rer, P, gid, r1, suf, inp, gm, t, inpF, gmF);
          } else {
            match t {
              case GroupActionT(ga, tc) => {
                var gmO := LG.GMOpen(LC.Idx(inp), g, gm);
                GMUpdatePreservesGid(LG.Open(g), LC.Idx(inp), gm, gid);
                assert ([LS.Areg(rc)] + suf)[1..] == suf;
                assert [LS.Areg(body), LS.Aclose(g)] + suf == [] + [LS.Areg(body)] + ([LS.Aclose(g)] + suf);
                RunToGroupAlt(rer, P, str, [], body, [LS.Aclose(g)] + suf, gid, r1, inp, gmO, tc, inpF, gmF);
              }
              case _ =>
            }
          }
        }
        case Sequence(a, b) => {
          SeqSizeTwo(a, b, suf);
          assert [LS.Areg(a), LS.Areg(b)] + suf == [] + [LS.Areg(a)] + ([LS.Areg(b)] + suf);
          if gid in L.DefGroups(a) {
            RunToGroupAlt(rer, P, str, [], a, [LS.Areg(b)] + suf, gid, r1, inp, gm, t, inpF, gmF);
          } else {
            assert [LS.Areg(a)] + [LS.Areg(b)] + suf == [LS.Areg(a), LS.Areg(b)] + suf;
            RunToGroupAlt(rer, P, str, [LS.Areg(a)], b, suf, gid, r1, inp, gm, t, inpF, gmF);
          }
        }
        case Disjunction(a, b) => {
          match t {
            case Choice(ta, tb) => {
              // tree_disj: IsTree([Areg(a)]+suf, ta) and IsTree([Areg(b)]+suf, tb);
              // TreeRes takes the left branch if it has a result.
              assert [] + [LS.Areg(a)] + suf == [LS.Areg(a)] + suf;
              assert [] + [LS.Areg(b)] + suf == [LS.Areg(b)] + suf;
              if LT.TreeRes(ta, gm, inp, WP.Forward).Some? {
                if gid in L.DefGroups(a) {
                  RunToGroupAlt(rer, P, str, [], a, suf, gid, r1, inp, gm, ta, inpF, gmF);
                } else {
                  // the winning arm never mentions gid: it stays unset
                  assert GidFreeActions([LS.Areg(a)] + suf, gid);
                  TreeFromGidFreeStack(rer, [LS.Areg(a)] + suf, inp, gm, WP.Forward, ta, gid);
                  TreeResPreservesGid(ta, gm, inp, WP.Forward, gid);
                }
              } else {
                if gid !in L.DefGroups(a) {
                  RunToGroupAlt(rer, P, str, [], b, suf, gid, r1, inp, gm, tb, inpF, gmF);
                } else {
                  assert GidFreeActions([LS.Areg(b)] + suf, gid);
                  TreeFromGidFreeStack(rer, [LS.Areg(b)] + suf, inp, gm, WP.Forward, tb, gid);
                  TreeResPreservesGid(tb, gm, inp, WP.Forward, gid);
                }
              }
            }
            case _ =>
          }
        }
        case _ =>   // Quantified/Character/Epsilon: GidContainerAlt(rc) is false -> vacuous
      }
    } else {
      var rest := pre[1..] + [LS.Areg(rc)] + suf;
      assert pre + [LS.Areg(rc)] + suf == [pre[0]] + rest;
      assert GidFreeActions(pre[1..], gid) && AltFragActions(pre[1..]);
      match pre[0] {
        case Acheck(sc) => {
          if SS.StrictSuffix(inp, sc, WP.Forward) {
            match t { case Progress(tc) => RunToGroupAlt(rer, P, str, pre[1..], rc, suf, gid, r1, inp, gm, tc, inpF, gmF); case _ => }
          } else { assert t == LT.Mismatch; }
        }
        case Aclose(g) => {
          assert g != gid;
          match t {
            case GroupActionT(ga, tc) => {
              var gmC := LG.GMClose(LC.Idx(inp), g, gm);
              GMUpdatePreservesGid(LG.Close(g), LC.Idx(inp), gm, gid);
              RunToGroupAlt(rer, P, str, pre[1..], rc, suf, gid, r1, inp, gmC, tc, inpF, gmF);
            }
            case _ =>
          }
        }
        case Areg(r) => {
          assert gid !in L.DefGroups(r);
          match r {
            case Epsilon => RunToGroupAlt(rer, P, str, pre[1..], rc, suf, gid, r1, inp, gm, t, inpF, gmF);
            case Character(cd) => {
              match LC.ReadChar(rer, cd, inp, WP.Forward) {
                case Some(pair) => {
                  match t {
                    case Read(c, tc) => {
                      AdvancePreservesStr(inp);
                      RunToGroupAlt(rer, P, str, pre[1..], rc, suf, gid, r1, pair.1, gm, tc, inpF, gmF);
                    }
                    case _ =>
                  }
                }
                case None => assert t == LT.Mismatch;
              }
            }
            case Sequence(a, b) => {
              var pre2 := [LS.Areg(a), LS.Areg(b)] + pre[1..];
              assert pre2 + [LS.Areg(rc)] + suf == [LS.Areg(a), LS.Areg(b)] + rest;
              SeqSizeTwo(a, b, rest);
              RunToGroupAlt(rer, P, str, pre2, rc, suf, gid, r1, inp, gm, t, inpF, gmF);
            }
            case Disjunction(a, b) => {
              match t {
                case Choice(ta, tb) => {
                  var pre2a := [LS.Areg(a)] + pre[1..];
                  var pre2b := [LS.Areg(b)] + pre[1..];
                  assert pre2a + [LS.Areg(rc)] + suf == [LS.Areg(a)] + rest;
                  assert pre2b + [LS.Areg(rc)] + suf == [LS.Areg(b)] + rest;
                  if LT.TreeRes(ta, gm, inp, WP.Forward).Some? {
                    RunToGroupAlt(rer, P, str, pre2a, rc, suf, gid, r1, inp, gm, ta, inpF, gmF);
                  } else {
                    RunToGroupAlt(rer, P, str, pre2b, rc, suf, gid, r1, inp, gm, tb, inpF, gmF);
                  }
                }
                case _ =>
              }
            }
            case Group(g, body) => {
              assert g != gid;
              match t {
                case GroupActionT(ga, tc) => {
                  var gmO := LG.GMOpen(LC.Idx(inp), g, gm);
                  GMUpdatePreservesGid(LG.Open(g), LC.Idx(inp), gm, gid);
                  var pre2 := [LS.Areg(body), LS.Aclose(g)] + pre[1..];
                  assert pre2 + [LS.Areg(rc)] + suf == [LS.Areg(body), LS.Aclose(g)] + rest;
                  RunToGroupAlt(rer, P, str, pre2, rc, suf, gid, r1, inp, gmO, tc, inpF, gmF);
                }
                case _ =>
              }
            }
            case Quantified(greedy, min, delta, body) => {
              var gidl := L.DefGroups(body);
              GMUpdatePreservesGid(LG.Reset(gidl), LC.Idx(inp), gm, gid);
              var gmR := LG.GMReset(gidl, gm);
              if min > 0 {
                match t {
                  case GroupActionT(ga, tc) => {
                    var pre2 := [LS.Areg(body), LS.Areg(L.Quantified(greedy, min - 1, delta, body))] + pre[1..];
                    assert pre2 + [LS.Areg(rc)] + suf
                        == [LS.Areg(body), LS.Areg(L.Quantified(greedy, min - 1, delta, body))] + rest;
                    assert LS.IsTree(rer, pre2 + [LS.Areg(rc)] + suf, inp, gmR, WP.Forward, tc);
                    RunToGroupAlt(rer, P, str, pre2, rc, suf, gid, r1, inp, gmR, tc, inpF, gmF);
                  }
                  case _ =>
                }
              } else if delta == LN.NN(0) {
                RunToGroupAlt(rer, P, str, pre[1..], rc, suf, gid, r1, inp, gm, t, inpF, gmF);
              } else {
                var plus := LN.NoISub(delta, 1);
                var iterPre := [LS.Areg(body), LS.Acheck(inp), LS.Areg(L.Quantified(greedy, 0, plus, body))] + pre[1..];
                match t {
                  case Choice(ta, tb) => {
                    var itert := if greedy then ta else tb;
                    var skipt := if greedy then tb else ta;
                    match itert {
                      case GroupActionT(ga, ti) => {
                        assert LS.TreeSize(ti) < LS.TreeSize(t);
                        assert LS.TreeSize(skipt) < LS.TreeSize(t);
                        assert iterPre + [LS.Areg(rc)] + suf
                            == [LS.Areg(body), LS.Acheck(inp), LS.Areg(L.Quantified(greedy, 0, plus, body))] + rest;
                        assert LS.IsTree(rer, iterPre + [LS.Areg(rc)] + suf, inp, gmR, WP.Forward, ti);
                        if LT.TreeRes(ta, gm, inp, WP.Forward).Some? {
                          if greedy { RunToGroupAlt(rer, P, str, iterPre, rc, suf, gid, r1, inp, gmR, ti, inpF, gmF); }
                          else { RunToGroupAlt(rer, P, str, pre[1..], rc, suf, gid, r1, inp, gm, skipt, inpF, gmF); }
                        } else {
                          if greedy { RunToGroupAlt(rer, P, str, pre[1..], rc, suf, gid, r1, inp, gm, skipt, inpF, gmF); }
                          else { RunToGroupAlt(rer, P, str, iterPre, rc, suf, gid, r1, inp, gmR, ti, inpF, gmF); }
                        }
                      }
                      case _ =>
                    }
                  }
                  case _ =>
                }
              }
            }
            case AnchorR(a) => {
              // zero-width: passes (same input, same map) or mismatches
              match t {
                case AnchorPass(a2, tc) =>
                  RunToGroupAlt(rer, P, str, pre[1..], rc, suf, gid, r1, inp, gm, tc, inpF, gmF);
                case _ =>   // Mismatch: TreeRes None, contradiction
              }
            }
            case _ =>   // out of the alternation fragment: AltFragRe(r) is false -> vacuous
          }
        }
      }
    }
  }

  // ==========================================================================
  // CdOnly discharge helpers — how a client (or Patterns.dfy) establishes
  // that a concrete descriptor only matches P-characters.
  // ==========================================================================

  /** A single-character descriptor only matches that character. */
  lemma CdSingleOnly(rer: LW.RegExpRecord, ch: char, P: char -> bool)
    requires !rer.ignoreCase && P(ch)
    ensures CdOnly(rer, LC.CdSingle(ch), P)
  {
    forall c: char | LC.CharMatch(rer, c, LC.CdSingle(ch))
      ensures P(c)
    {
      WP.CanonicalizeCaseSensitive(rer, c);
      WP.CanonicalizeCaseSensitive(rer, ch);
    }
  }

  /** The shape-only fragment `POnly` ranges over — with `P := c => true`,
      membership here is ALL it takes (used for bounds-only conclusions). */
  ghost predicate ContentFragRe(r: L.Regex)
    decreases r
  {
    match r
    case Epsilon => true
    case Character(_) => true
    case Sequence(r1, r2) => ContentFragRe(r1) && ContentFragRe(r2)
    case Quantified(_, _, _, r1) => ContentFragRe(r1)
    case _ => false
  }

  /** Everything in the content fragment is trivially `(c => true)`-only —
      the instantiation that turns the content theory into pure bounds facts. */
  lemma POnlyTrue(rer: LW.RegExpRecord, r: L.Regex)
    requires ContentFragRe(r)
    ensures POnly(rer, r, c => true)
    decreases r
  {
    match r
    case Sequence(r1, r2) => POnlyTrue(rer, r1); POnlyTrue(rer, r2);
    case Quantified(_, _, _, r1) => POnlyTrue(rer, r1);
    case _ =>
  }
}
