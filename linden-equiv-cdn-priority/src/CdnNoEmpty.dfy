// G5a-1 row A2 (G5a1-statements.md §18): SEMANTIC check insertion, the iteration tree of a guarded plus whose
// guard fails. PROBE SOURCE: written by reading against 543ed77 + P1, never resolved or verified.
//
// HOW TO RUN
//   * Put it in the new leaf package as `linden-equiv-cdn-priority/src/CdnNoEmpty.dfy` (after
//     `G5a1-P1a-cdn-priority.py.txt --apply`); the package's dependency list already covers every import here
//     (reasoning, semantics-core, warblre, entry-lk, check-erase, look-leaves, nulled-plus).
//   * `dafny resolve`, then per symbol: NoAcheckTail, NoAcheckPrepend, BoolCheckInsertNoEmpty, IterTreeOfNoEmpty.
//   * It uses the head-atom lemmas of 3-L0c (`EL.CinHeadMono`, `EL.CinHeadIntro`), so it needs the g5a1-s2 `.doo`s.
//
// WHAT IT IS
//   `CE.BoolCheckInsertK` inserts `Acheck(chk)` after `pre` when a NonNullable element of `pre`, an earlier check,
//   or the flag guarantees the check is reached at `CanExit`: a SYNTACTIC guarantee. A CDN body is nullable; that
//   it consumes at this `inp` is the semantic fact `NP.FirstEmptyPathA(rer, pre, inp).None?`. This lemma is
//   `BoolCheckInsertK`'s case structure [read: its body, `CheckErase.dfy:876-1168`] with that premise, and with
//   TWO flags: the given tree walks at `b`, the produced one at `b2`. The flag is read only at an `Acheck`, `pre`
//   has none, and the first `Read` sets both to `CanExit`, so along the Read-free prefix the two trees coincide.
//   It closes early in three places, where the syntactic lemma applies as it stands:
//     - a `Character` head: after the `Read` both sides are at `CanExit`;
//     - a star / bounded-layer head: the ITERATION list holds its own `Acheck(inp)` and runs at `CannotExit` on
//       both sides (`BoolCheckInsertK`'s `AcheckIn` disjunct);
//     - the look bridge is definitional: `EL.LkGateOk(rer, lk, r1, inp, tlk, true)` unfolds to
//       `tlk == FU.ComputeTr(…) && LS.LkResult(lk, tlk, LG.Empty, inp).Some?`, which is `NP.LkVerdictL` verbatim
//       (`EntryLk.dfy:1141`, `NulledPlus.dfy:165`). No TODO lemma was needed.
//   Every other arm unfolds one step and takes `None` for the unfolded list from `FirstEmptyPathA`'s own
//   equation (`NulledPlus.dfy:169-245` [read]).
//
// EXPECTED FIRST SOLVER FAILURES (guesses, most likely first)
//   1. The `None` premise of a recursive call. `FirstEmptyPathA` is a fuel-limited recursive ghost function with
//      asserts in its body; one unfolding at `pre` must expose the callee's term syntactically
//      (`[LS.Areg(r1), LS.Areg(r2)] + pre[1..]` etc.). Each arm asserts the equation it needs
//      (`assert NP.FirstEmptyPathA(rer, pn, inp).None?`); if one fails, the list in the function's body and `pn`
//      differ by a sequence identity: assert `pre == [pre[0]] + pre[1..]` and `pn == […] + pre[1..]` first.
//   2. The lookaround arm: `assert NP.LkVerdictL(rer, lk, r1, inp)` from `EL.LkGateOk(…, true)`. Definitional,
//      but `FU.ComputeTr` appears on both sides and must not be unfolded: if it loops, `hide FU.ComputeTr`.
//   3. The star arm's two conclusions (`PSize`, `ProgErase`) for `Choice(GroupActionT(g, si), ss)`: the template
//      gets them unaided; here `si` comes from another lemma (`CE.BoolCheckInsertK`), same shape.
//   4. The whole lemma as one batch: the template verifies as one; this one has one more premise per arm. If it
//      is heavy, put `assert {:split_here} true;` at the top of each `case` (they are independent).
module LindenElkCdnNoEmpty {
  import opened Std.Wrappers
  import LW = WarblreRegExpRecord
  import WP = WarblrePrimitives
  import LC = Chars
  import LG = Groups
  import L = Regex
  import LN = WarblreNumeric
  import LS = Semantics
  import LT = Tree
  import BS = BooleanSemantics
  import FS = FunctionalSemantics
  import EL = LindenElkEntryLk
  import CE = LindenElkCheckErase
  import NP = LindenElkNulledPlus

  /** No check in `pre`, none in its tail. */
  lemma NoAcheckTail(pre: LS.Actions)
    requires |pre| > 0 && !CE.AcheckIn(pre)
    ensures !CE.AcheckIn(pre[1..])
  {
    if CE.AcheckIn(pre[1..]) {
      var i :| 0 <= i < |pre[1..]| && pre[1..][i].Acheck?;
      assert pre[i + 1] == pre[1..][i];
      assert CE.AcheckIn(pre);
    }
  }

  /** Replacing the head of a check-free list by check-free actions keeps it check-free. */
  lemma NoAcheckPrepend(xs: LS.Actions, pre: LS.Actions)
    requires |pre| > 0 && !CE.AcheckIn(pre)
    requires forall i :: 0 <= i < |xs| ==> !xs[i].Acheck?
    ensures !CE.AcheckIn(xs + pre[1..])
  {
    var pn := xs + pre[1..];
    if CE.AcheckIn(pn) {
      var i :| 0 <= i < |pn| && pn[i].Acheck?;
      assert i >= |xs|;
      assert pn[i] == pre[i - |xs| + 1];
      assert CE.AcheckIn(pre);
    }
  }

  /** SEMANTIC check insertion: if no zero-width path crosses the check-free list `pre` at `inp`, a check
      inserted after `pre` is only ever reached with the flag set, whatever flag either walk starts with. */
  lemma BoolCheckInsertNoEmpty(rer: LW.RegExpRecord, pre: LS.Actions, chk: LC.Input, rest: LS.Actions,
                               inp: LC.Input, b: BS.LoopBool, b2: BS.LoopBool, t: LT.Tree) returns (tstar: LT.Tree)
    requires EL.PikeLkActionsRec(pre)
    requires !CE.AcheckIn(pre)
    requires NP.FirstEmptyPathA(rer, pre, inp).None?
    requires EL.BoolTreeLk(rer, pre + rest, inp, b, t)
    ensures EL.BoolTreeLk(rer, pre + [LS.Acheck(chk)] + rest, inp, b2, tstar)
    ensures CE.PSize(tstar) == CE.PSize(t)
    ensures CE.ProgErase(tstar) == CE.ProgErase(t)
    ensures forall SS: set<LG.GroupId> :: CE.LkConfinedTreeK(t, SS) ==> CE.LkConfinedTreeK(tstar, SS)
    decreases LS.TreeSize(t), LS.ActionsRegexSize(pre)
  {
    if |pre| == 0 {
      assert NP.FirstEmptyPathA(rer, pre, inp) == Some([]);
      assert false;
    }
    var cont := pre[1..];
    assert pre == [pre[0]] + cont;
    assert (pre + rest)[0] == pre[0] && (pre + rest)[1..] == cont + rest;
    assert (pre + [LS.Acheck(chk)] + rest)[0] == pre[0]
        && (pre + [LS.Acheck(chk)] + rest)[1..] == cont + [LS.Acheck(chk)] + rest;
    assert EL.PikeLkActionRec(pre[0]);
    assert EL.PikeLkActionsRec(cont) by {
      forall i | 0 <= i < |cont| ensures EL.PikeLkActionRec(cont[i]) {
        assert cont[i] == pre[i + 1];
      }
    }
    NoAcheckTail(pre);
    match pre[0]
    case Acheck(c2) =>
      assert pre[0].Acheck?;
      assert CE.AcheckIn(pre);
      assert false;
    case Aclose(gid) =>
      assert NP.FirstEmptyPathA(rer, cont, inp).None?;
      match t {
        case GroupActionT(g, tc) =>
          var sub := BoolCheckInsertNoEmpty(rer, cont, chk, rest, inp, b, b2, tc);
          tstar := LT.GroupActionT(g, sub);
          forall SSp: set<LG.GroupId> | CE.LkConfinedTreeK(t, SSp) ensures CE.LkConfinedTreeK(tstar, SSp) {}
        case _ =>
      }
    case Areg(r) =>
      assert EL.PikeLkRegexRec(r);
      match r
      case Epsilon =>
        assert NP.FirstEmptyPathA(rer, cont, inp).None?;
        tstar := BoolCheckInsertNoEmpty(rer, cont, chk, rest, inp, b, b2, t);
      case Character(cd) =>
        // the Read sets the flag on both sides: the syntactic lemma finishes
        match LC.ReadChar(rer, cd, inp, WP.Forward) {
          case Some(pair) =>
            match t {
              case Read(c, tc) =>
                var sub := CE.BoolCheckInsertK(rer, cont, chk, rest, pair.1, BS.CanExit, tc);
                tstar := LT.Read(c, sub);
                forall SSp: set<LG.GroupId> | CE.LkConfinedTreeK(t, SSp) ensures CE.LkConfinedTreeK(tstar, SSp) {}
              case _ =>
            }
          case None =>
            tstar := LT.Mismatch;
        }
      case Disjunction(r1, r2) =>
        match t {
          case Choice(ta, tb) =>
            var pa := [LS.Areg(r1)] + cont;
            var pb := [LS.Areg(r2)] + cont;
            assert pa + rest == [LS.Areg(r1)] + (cont + rest);
            assert pb + rest == [LS.Areg(r2)] + (cont + rest);
            assert pa + [LS.Acheck(chk)] + rest == [LS.Areg(r1)] + (cont + [LS.Acheck(chk)] + rest);
            assert pb + [LS.Acheck(chk)] + rest == [LS.Areg(r2)] + (cont + [LS.Acheck(chk)] + rest);
            assert EL.PikeLkActionsRec(pa) by {
              forall i | 0 <= i < |pa| ensures EL.PikeLkActionRec(pa[i]) { if i > 0 { assert pa[i] == pre[i]; } }
            }
            assert EL.PikeLkActionsRec(pb) by {
              forall i | 0 <= i < |pb| ensures EL.PikeLkActionRec(pb[i]) { if i > 0 { assert pb[i] == pre[i]; } }
            }
            NoAcheckPrepend([LS.Areg(r1)], pre);
            NoAcheckPrepend([LS.Areg(r2)], pre);
            // no empty path through the disjunction: none through either branch
            assert NP.FirstEmptyPathA(rer, pa, inp).None? && NP.FirstEmptyPathA(rer, pb, inp).None?;
            var sa := BoolCheckInsertNoEmpty(rer, pa, chk, rest, inp, b, b2, ta);
            var sb := BoolCheckInsertNoEmpty(rer, pb, chk, rest, inp, b, b2, tb);
            tstar := LT.Choice(sa, sb);
            forall SSp: set<LG.GroupId> | CE.LkConfinedTreeK(t, SSp) ensures CE.LkConfinedTreeK(tstar, SSp) {}
          case _ =>
        }
      case Sequence(r1, r2) =>
        var pn := [LS.Areg(r1), LS.Areg(r2)] + cont;
        assert pn + rest == [LS.Areg(r1), LS.Areg(r2)] + (cont + rest);
        assert pn + [LS.Acheck(chk)] + rest == [LS.Areg(r1), LS.Areg(r2)] + (cont + [LS.Acheck(chk)] + rest);
        assert EL.PikeLkActionsRec(pn) by {
          forall i | 0 <= i < |pn| ensures EL.PikeLkActionRec(pn[i]) {
            if i >= 2 { assert pn[i] == pre[i - 1]; }
          }
        }
        NoAcheckPrepend([LS.Areg(r1), LS.Areg(r2)], pre);
        assert NP.FirstEmptyPathA(rer, pn, inp).None?;
        assert LS.ActionsRegexSize(pn) < LS.ActionsRegexSize(pre);
        tstar := BoolCheckInsertNoEmpty(rer, pn, chk, rest, inp, b, b2, t);
      case Quantified(greedy, min, delta, r1) =>
        var gidl := L.DefGroups(r1);
        if min > 0 {
          match t {
            case GroupActionT(g, tc) =>
              var q1 := L.Quantified(greedy, min - 1, delta, r1);
              if EL.CinHeadL(greedy, min, delta, r1) { EL.CinHeadMono(greedy, min, delta, r1, min - 1, delta); }
              var pn := [LS.Areg(r1), LS.Areg(q1)] + cont;
              assert pn + rest == [LS.Areg(r1), LS.Areg(q1)] + (cont + rest);
              assert pn + [LS.Acheck(chk)] + rest == [LS.Areg(r1), LS.Areg(q1)] + (cont + [LS.Acheck(chk)] + rest);
              assert EL.PikeLkActionsRec(pn) by {
                forall i | 0 <= i < |pn| ensures EL.PikeLkActionRec(pn[i]) {
                  if i >= 2 { assert pn[i] == pre[i - 1]; }
                }
              }
              NoAcheckPrepend([LS.Areg(r1), LS.Areg(q1)], pre);
              assert NP.FirstEmptyPathA(rer, pn, inp).None?;
              var sub := BoolCheckInsertNoEmpty(rer, pn, chk, rest, inp, b, b2, tc);
              tstar := LT.GroupActionT(g, sub);
              forall SSp: set<LG.GroupId> | CE.LkConfinedTreeK(t, SSp) ensures CE.LkConfinedTreeK(tstar, SSp) {}
            case _ =>
          }
        } else if delta == LN.NN(0) {
          assert NP.FirstEmptyPathA(rer, cont, inp).None?;
          tstar := BoolCheckInsertNoEmpty(rer, cont, chk, rest, inp, b, b2, t);
        } else {
          match t {
            case Choice(ta, tb) =>
              var itert := if greedy then ta else tb;
              var skipt := if greedy then tb else ta;
              match itert {
                case GroupActionT(g, ti) =>
                  var q0 := L.Quantified(greedy, 0, FS.NoiPred(delta), r1);
                  EL.CinHeadIntro(greedy, 0, FS.NoiPred(delta), r1);
                  // the iteration: its own `Acheck(inp)` shields the inserted one, at `CannotExit` on both sides
                  var pi := [LS.Areg(r1), LS.Acheck(inp), LS.Areg(q0)] + cont;
                  assert pi + rest == [LS.Areg(r1), LS.Acheck(inp), LS.Areg(q0)] + (cont + rest);
                  assert pi + [LS.Acheck(chk)] + rest == [LS.Areg(r1), LS.Acheck(inp), LS.Areg(q0)] + (cont + [LS.Acheck(chk)] + rest);
                  assert EL.PikeLkActionsRec(pi) by {
                    forall i | 0 <= i < |pi| ensures EL.PikeLkActionRec(pi[i]) {
                      if i >= 3 { assert pi[i] == pre[i - 2]; }
                    }
                  }
                  assert CE.AcheckIn(pi) by { assert pi[1].Acheck?; }
                  var si := CE.BoolCheckInsertK(rer, pi, chk, rest, inp, BS.CannotExit, ti);
                  // the skip: the star contributes no zero-width path of its own, so `cont` has none either
                  assert NP.FirstEmptyPathA(rer, cont, inp).None?;
                  assert LS.TreeSize(skipt) < LS.TreeSize(t);
                  var ss := BoolCheckInsertNoEmpty(rer, cont, chk, rest, inp, b, b2, skipt);
                  var istar := LT.GroupActionT(g, si);
                  if greedy {
                    tstar := LT.Choice(istar, ss);
                  } else {
                    tstar := LT.Choice(ss, istar);
                  }
                  forall SSp: set<LG.GroupId> | CE.LkConfinedTreeK(t, SSp) ensures CE.LkConfinedTreeK(tstar, SSp) {
                    assert CE.LkConfinedTreeK(itert, SSp) && CE.LkConfinedTreeK(skipt, SSp);
                    assert CE.LkConfinedTreeK(ti, SSp);
                  }
                case _ =>
              }
            case _ =>
          }
        }
      case Group(gid, r1) =>
        match t {
          case GroupActionT(g, tc) =>
            var pn := [LS.Areg(r1), LS.Aclose(gid)] + cont;
            assert pn + rest == [LS.Areg(r1), LS.Aclose(gid)] + (cont + rest);
            assert pn + [LS.Acheck(chk)] + rest == [LS.Areg(r1), LS.Aclose(gid)] + (cont + [LS.Acheck(chk)] + rest);
            assert EL.PikeLkActionsRec(pn) by {
              forall i | 0 <= i < |pn| ensures EL.PikeLkActionRec(pn[i]) {
                if i >= 2 { assert pn[i] == pre[i - 1]; }
              }
            }
            NoAcheckPrepend([LS.Areg(r1), LS.Aclose(gid)], pre);
            assert NP.FirstEmptyPathA(rer, pn, inp).None?;
            var sub := BoolCheckInsertNoEmpty(rer, pn, chk, rest, inp, b, b2, tc);
            tstar := LT.GroupActionT(g, sub);
            forall SSp: set<LG.GroupId> | CE.LkConfinedTreeK(t, SSp) ensures CE.LkConfinedTreeK(tstar, SSp) {}
          case _ =>
        }
      case AnchorR(a) =>
        if LS.AnchorSatisfied(rer, a, inp) {
          assert NP.FirstEmptyPathA(rer, cont, inp).None?;
          match t {
            case AnchorPass(a2, tc) =>
              var sub := BoolCheckInsertNoEmpty(rer, cont, chk, rest, inp, b, b2, tc);
              tstar := LT.AnchorPass(a2, sub);
              forall SSp: set<LG.GroupId> | CE.LkConfinedTreeK(t, SSp) ensures CE.LkConfinedTreeK(tstar, SSp) {}
            case _ =>
          }
        } else {
          tstar := LT.Mismatch;
        }
      case LookaroundR(lk, r1) =>
        match t {
          case LK(lk2, tlk, tc) =>
            // THE BRIDGE: the gate passed, so the spec-level verdict holds (both are
            // `LS.LkResult(lk, FU.ComputeTr(rer, [Areg(r1)], inp, LG.Empty, L.LkDir(lk)), LG.Empty, inp).Some?`),
            // and then no zero-width path crosses the rest
            assert EL.LkGateOk(rer, lk, r1, inp, tlk, true);
            assert NP.LkVerdictL(rer, lk, r1, inp);
            assert NP.FirstEmptyPathA(rer, cont, inp).None?;
            var sub := BoolCheckInsertNoEmpty(rer, cont, chk, rest, inp, b, b2, tc);
            tstar := LT.LK(lk2, tlk, sub);
            forall SSp: set<LG.GroupId> | CE.LkConfinedTreeK(t, SSp) ensures CE.LkConfinedTreeK(tstar, SSp) {}
          case LKFail(lk2, tlk) =>
            tstar := t;
          case _ =>
        }
      case Backreference(_) =>
        assert false;   // not pike
  }

  /** THE USE: the engine's iteration tree of a guarded greedy plus whose guard fails at `inp`, read off the
      spec tree's forced copy. `tc` is the tree of `[r1] + rest` at the ambient flag (the child of the spec
      tree's `Reset`), `rest == [Areg(Quantified(true, 0, Inf, r1))] + cont` at the call sites; the result walks
      at `CannotExit`, is no bigger in `PSize` (the recursions' measure), and erases to the same program. */
  lemma IterTreeOfNoEmpty(rer: LW.RegExpRecord, r1: L.Regex, rest: LS.Actions, inp: LC.Input,
                          b: BS.LoopBool, tc: LT.Tree) returns (ti: LT.Tree)
    requires EL.PikeLkRegexRec(r1)
    requires NP.FirstEmptyPathL(rer, r1, inp).None?
    requires EL.BoolTreeLk(rer, [LS.Areg(r1)] + rest, inp, b, tc)
    ensures EL.BoolTreeLk(rer, [LS.Areg(r1), LS.Acheck(inp)] + rest, inp, BS.CannotExit, ti)
    ensures CE.PSize(ti) == CE.PSize(tc)
    ensures CE.ProgErase(ti) == CE.ProgErase(tc)
    ensures forall SS: set<LG.GroupId> :: CE.LkConfinedTreeK(tc, SS) ==> CE.LkConfinedTreeK(ti, SS)
  {
    var pre := [LS.Areg(r1)];
    assert EL.PikeLkActionsRec(pre) by {
      forall i | 0 <= i < |pre| ensures EL.PikeLkActionRec(pre[i]) { assert pre[i] == LS.Areg(r1); }
    }
    assert !CE.AcheckIn(pre) by {
      if CE.AcheckIn(pre) { var i :| 0 <= i < |pre| && pre[i].Acheck?; assert pre[i] == LS.Areg(r1); }
    }
    assert pre + [LS.Acheck(inp)] + rest == [LS.Areg(r1), LS.Acheck(inp)] + rest;
    ti := BoolCheckInsertNoEmpty(rer, pre, inp, rest, inp, b, BS.CannotExit, tc);
  }
}
