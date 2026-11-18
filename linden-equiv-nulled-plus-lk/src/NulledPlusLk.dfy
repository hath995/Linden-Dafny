// (G4b) The Lk-carrying first empty path of a CI-nullable plus body (W15 spec, re-checked by W20 on 2026-11-17).
//
//   * `FirstEmptyPathLkA` = `NP.FirstEmptyPathA` with a `LkS(lk, b)` step emitted at
//     every passed look (same gate: `NP.LkVerdictL`). `ProjPath`: dropping the look
//     steps gives `NP.FirstEmptyPathA` back, so no gate decision changes.
//   * `ApplyPathLk` folds a step at a look as the spec does: `LkResult` of the body
//     tree from the CURRENT map.
//   * `EmptyLeavesLk`: the first leaf at `inp` of the spec tree IS `ApplyPathLk`
//     (exact; `NP.EmptyLeavesA` only had "outside S").
//   * `NulledLooks` / `NulledIterationLeaf`: at a map where the regex's groups are unset (the plus's Reset),
//     a crossed positive look's groups carry the body's leaf from `Empty` at `inp`,
//     an uncrossed look's groups are unset, and outside the look groups the
//     result is `NP.ApplyPath` of the projected path.
//   * `CinPlusPriorityLk`: rung A, exact (no `S`), on the look-carrying chain; (G4b-1)
//     `CinPlusPriorityGroupFreeCrossed`: exact on TODAY's bare chain when every crossed look is group-free.
module LindenElkNulledPlusLk {
  import opened Std.Wrappers
  import LW = WarblreRegExpRecord
  import WP = WarblrePrimitives
  import LC = Chars
  import LG = Groups
  import L = Regex
  import LN = WarblreNumeric
  import LS = Semantics
  import LT = Tree
  import FS = FunctionalSemantics
  import FU = FunctionalUtils
  import SS = StrictSuffix
  import NUL = LindenElkNullable
  import EL = LindenElkEntryLk
  import CE = LindenElkCheckErase
  import LL = LindenElkLookLeaves
  import NP = LindenElkNulledPlus
  import NT = LindenElkNulledPlusTie
  import NB = LindenElkNulledPlusBool
  import CDP = LindenElkCdnPriority
  import BS = BooleanSemantics
  import EQ = Equivalence
  import FM = FlatMap

  // ===========================================================================
  // 1. The Lk-carrying first empty path
  // ===========================================================================

  datatype Step = GA(a: LG.GroupAction) | LkS(lk: L.Lookaround, b: L.Regex)

  ghost function FirstEmptyPathLkA(rer: LW.RegExpRecord, acts: LS.Actions, inp: LC.Input): Option<seq<Step>>
    decreases FS.ActionsFuel(acts, inp, WP.Forward)
  {
    if |acts| == 0 then Some([])
    else
      var cont := acts[1..];
      match acts[0]
      case Acheck(strcheck) =>
        if SS.IsStrictSuffix(inp, strcheck, WP.Forward) then
          assert FS.ActionsFuel(cont, inp, WP.Forward) < FS.ActionsFuel(acts, inp, WP.Forward) by {
            SS.IsStrictSuffixCorrect(inp, strcheck, WP.Forward);
            assert acts == [LS.Acheck(strcheck)] + cont;
            FS.CheckTermination(cont, inp, strcheck, WP.Forward);
          }
          FirstEmptyPathLkA(rer, cont, inp)
        else None
      case Aclose(gid) =>
        assert FS.ActionsFuel(cont, inp, WP.Forward) < FS.ActionsFuel(acts, inp, WP.Forward) by {
          assert acts == [LS.Aclose(gid)] + cont;
          FS.CloseTermination(cont, inp, WP.Forward, gid);
        }
        (match FirstEmptyPathLkA(rer, cont, inp)
         case Some(p) => Some([GA(LG.Close(gid))] + p)
         case None => None)
      case Areg(r) =>
        match r
        case Epsilon =>
          assert FS.ActionsFuel(cont, inp, WP.Forward) < FS.ActionsFuel(acts, inp, WP.Forward) by {
            assert acts == [LS.Areg(L.Epsilon)] + cont;
            FS.EpsilonTermination(cont, inp, WP.Forward);
          }
          FirstEmptyPathLkA(rer, cont, inp)
        case Character(_) => None
        case Disjunction(r1, r2) =>
          assert FS.ActionsFuel([LS.Areg(r1)] + cont, inp, WP.Forward) < FS.ActionsFuel(acts, inp, WP.Forward)
              && FS.ActionsFuel([LS.Areg(r2)] + cont, inp, WP.Forward) < FS.ActionsFuel(acts, inp, WP.Forward) by {
            assert acts == [LS.Areg(L.Disjunction(r1, r2))] + cont;
            FS.DisjunctionLeftTermination(cont, inp, WP.Forward, r1, r2);
            FS.DisjunctionRightTermination(cont, inp, WP.Forward, r1, r2);
          }
          (match FirstEmptyPathLkA(rer, [LS.Areg(r1)] + cont, inp)
           case Some(p) => Some(p)
           case None => FirstEmptyPathLkA(rer, [LS.Areg(r2)] + cont, inp))
        case Sequence(r1, r2) =>
          assert FS.ActionsFuel([LS.Areg(r1), LS.Areg(r2)] + cont, inp, WP.Forward) < FS.ActionsFuel(acts, inp, WP.Forward) by {
            assert acts == [LS.Areg(L.Sequence(r1, r2))] + cont;
            FS.SequenceTermination(cont, inp, WP.Forward, r1, r2);
            assert LS.SeqList(r1, r2, WP.Forward) == [LS.Areg(r1), LS.Areg(r2)];
          }
          FirstEmptyPathLkA(rer, [LS.Areg(r1), LS.Areg(r2)] + cont, inp)
        case Quantified(greedy, min, delta, r1) =>
          var gidl := L.DefGroups(r1);
          if min > 0 then
            assert FS.ActionsFuel([LS.Areg(r1), LS.Areg(L.Quantified(greedy, min - 1, delta, r1))] + cont, inp, WP.Forward)
                 < FS.ActionsFuel(acts, inp, WP.Forward) by {
              assert acts == [LS.Areg(L.Quantified(greedy, min, delta, r1))] + cont;
              FS.QuantForcedTermination(cont, inp, WP.Forward, r1, min - 1, delta, greedy);
            }
            (match FirstEmptyPathLkA(rer, [LS.Areg(r1), LS.Areg(L.Quantified(greedy, min - 1, delta, r1))] + cont, inp)
             case Some(p) => Some([GA(LG.Reset(gidl))] + p)
             case None => None)
          else
            assert FS.ActionsFuel(cont, inp, WP.Forward) < FS.ActionsFuel(acts, inp, WP.Forward) by {
              assert acts == [LS.Areg(L.Quantified(greedy, 0, delta, r1))] + cont;
              FS.QuantFreeSkipTermination(cont, inp, WP.Forward, r1, greedy, delta);
            }
            FirstEmptyPathLkA(rer, cont, inp)
        case Group(gid, r1) =>
          assert FS.ActionsFuel([LS.Areg(r1), LS.Aclose(gid)] + cont, inp, WP.Forward) < FS.ActionsFuel(acts, inp, WP.Forward) by {
            assert acts == [LS.Areg(L.Group(gid, r1))] + cont;
            FS.GroupTermination(cont, inp, WP.Forward, r1, gid);
          }
          (match FirstEmptyPathLkA(rer, [LS.Areg(r1), LS.Aclose(gid)] + cont, inp)
           case Some(p) => Some([GA(LG.Open(gid))] + p)
           case None => None)
        case AnchorR(a) =>
          if LS.AnchorSatisfied(rer, a, inp) then
            assert FS.ActionsFuel(cont, inp, WP.Forward) < FS.ActionsFuel(acts, inp, WP.Forward) by {
              assert acts == [LS.Areg(L.AnchorR(a))] + cont;
              FS.AnchorTermination(cont, inp, WP.Forward, a);
            }
            FirstEmptyPathLkA(rer, cont, inp)
          else None
        case LookaroundR(lk, r1) =>
          if NP.LkVerdictL(rer, lk, r1, inp) then
            assert FS.ActionsFuel(cont, inp, WP.Forward) < FS.ActionsFuel(acts, inp, WP.Forward) by {
              assert acts == [LS.Areg(L.LookaroundR(lk, r1))] + cont;
              FS.LkAfterTermination(cont, inp, WP.Forward, lk, r1);
            }
            (match FirstEmptyPathLkA(rer, cont, inp)
             case Some(p) => Some([LkS(lk, r1)] + p)
             case None => None)
          else None
        case Backreference(_) => None
  }

  ghost function FirstEmptyPathLkL(rer: LW.RegExpRecord, r: L.Regex, inp: LC.Input): Option<seq<Step>> {
    FirstEmptyPathLkA(rer, [LS.Areg(r)], inp)
  }

  /** Dropping the look steps. */
  function Proj(s: seq<Step>): seq<LG.GroupAction>
    decreases |s|
  {
    if |s| == 0 then [] else (if s[0].GA? then [s[0].a] else []) + Proj(s[1..])
  }

  function ProjO(o: Option<seq<Step>>): Option<seq<LG.GroupAction>> {
    match o case None => None case Some(s) => Some(Proj(s))
  }

  lemma ProjCons(x: Step, s: seq<Step>)
    ensures Proj([x] + s) == (if x.GA? then [x.a] else []) + Proj(s)
  {
    assert ([x] + s)[0] == x && ([x] + s)[1..] == s;
  }

  lemma ProjApp(a: seq<Step>, b: seq<Step>)
    ensures Proj(a + b) == Proj(a) + Proj(b)
    decreases |a|
  {
    if |a| == 0 {
      assert a + b == b;
    } else {
      assert (a + b)[0] == a[0] && (a + b)[1..] == a[1..] + b;
      ProjApp(a[1..], b);
    }
  }

  /** NO GATE DECISION CHANGES: the Lk-carrying path projects to `NP.FirstEmptyPathA`. */
  lemma ProjPath(rer: LW.RegExpRecord, acts: LS.Actions, inp: LC.Input)
    ensures ProjO(FirstEmptyPathLkA(rer, acts, inp)) == NP.FirstEmptyPathA(rer, acts, inp)
    decreases FS.ActionsFuel(acts, inp, WP.Forward)
  {
    if |acts| == 0 { return; }
    var cont := acts[1..];
    assert acts == [acts[0]] + cont;
    match acts[0]
    case Acheck(strcheck) =>
      SS.IsStrictSuffixCorrect(inp, strcheck, WP.Forward);
      if SS.IsStrictSuffix(inp, strcheck, WP.Forward) {
        FS.CheckTermination(cont, inp, strcheck, WP.Forward);
        ProjPath(rer, cont, inp);
      }
    case Aclose(gid) =>
      FS.CloseTermination(cont, inp, WP.Forward, gid);
      ProjPath(rer, cont, inp);
      var o := FirstEmptyPathLkA(rer, cont, inp);
      if o.Some? { ProjCons(GA(LG.Close(gid)), o.value); }
    case Areg(r) =>
      match r
      case Epsilon =>
        FS.EpsilonTermination(cont, inp, WP.Forward);
        ProjPath(rer, cont, inp);
      case Character(_) =>
      case Disjunction(r1, r2) =>
        FS.DisjunctionLeftTermination(cont, inp, WP.Forward, r1, r2);
        FS.DisjunctionRightTermination(cont, inp, WP.Forward, r1, r2);
        ProjPath(rer, [LS.Areg(r1)] + cont, inp);
        ProjPath(rer, [LS.Areg(r2)] + cont, inp);
      case Sequence(r1, r2) =>
        FS.SequenceTermination(cont, inp, WP.Forward, r1, r2);
        assert LS.SeqList(r1, r2, WP.Forward) == [LS.Areg(r1), LS.Areg(r2)];
        ProjPath(rer, [LS.Areg(r1), LS.Areg(r2)] + cont, inp);
      case Quantified(greedy, min, delta, r1) =>
        var gidl := L.DefGroups(r1);
        if min > 0 {
          FS.QuantForcedTermination(cont, inp, WP.Forward, r1, min - 1, delta, greedy);
          var ia := [LS.Areg(r1), LS.Areg(L.Quantified(greedy, min - 1, delta, r1))] + cont;
          ProjPath(rer, ia, inp);
          var o := FirstEmptyPathLkA(rer, ia, inp);
          if o.Some? { ProjCons(GA(LG.Reset(gidl)), o.value); }
        } else {
          FS.QuantFreeSkipTermination(cont, inp, WP.Forward, r1, greedy, delta);
          ProjPath(rer, cont, inp);
        }
      case Group(gid, r1) =>
        FS.GroupTermination(cont, inp, WP.Forward, r1, gid);
        var ia := [LS.Areg(r1), LS.Aclose(gid)] + cont;
        ProjPath(rer, ia, inp);
        var o := FirstEmptyPathLkA(rer, ia, inp);
        if o.Some? { ProjCons(GA(LG.Open(gid)), o.value); }
      case AnchorR(a) =>
        if LS.AnchorSatisfied(rer, a, inp) {
          FS.AnchorTermination(cont, inp, WP.Forward, a);
          ProjPath(rer, cont, inp);
        }
      case LookaroundR(lk, r1) =>
        if NP.LkVerdictL(rer, lk, r1, inp) {
          FS.LkAfterTermination(cont, inp, WP.Forward, lk, r1);
          ProjPath(rer, cont, inp);
          var o := FirstEmptyPathLkA(rer, cont, inp);
          if o.Some? {
            ProjCons(LkS(lk, r1), o.value);
            assert Proj([LkS(lk, r1)] + o.value) == [] + Proj(o.value) == Proj(o.value);
            assert NP.FirstEmptyPathA(rer, acts, inp) == NP.FirstEmptyPathA(rer, cont, inp);
          } else {
            assert NP.FirstEmptyPathA(rer, acts, inp) == NP.FirstEmptyPathA(rer, cont, inp);
          }
        }
      case Backreference(_) =>
  }

  // ===========================================================================
  // 2. The Lk-aware fold and the EXACT first empty leaf
  // ===========================================================================

  /** A look step as the spec folds it: `LkResult` of the body tree from the current map. */
  ghost function LkGm(rer: LW.RegExpRecord, lk: L.Lookaround, b: L.Regex, inp: LC.Input, gm: LG.GroupMap): LG.GroupMap {
    match LS.LkResult(lk, FU.ComputeTr(rer, [LS.Areg(b)], inp, gm, L.LkDir(lk)), gm, inp)
    case Some(g) => g
    case None => gm
  }

  ghost function StepGm(rer: LW.RegExpRecord, x: Step, inp: LC.Input, gm: LG.GroupMap): LG.GroupMap {
    match x
    case GA(a) => LG.GMUpdate(a, LC.Idx(inp), gm)
    case LkS(lk, b) => LkGm(rer, lk, b, inp, gm)
  }

  ghost function ApplyPathLk(rer: LW.RegExpRecord, s: seq<Step>, inp: LC.Input, gm: LG.GroupMap): LG.GroupMap
    decreases |s|
  {
    if |s| == 0 then gm else ApplyPathLk(rer, s[1..], inp, StepGm(rer, s[0], inp, gm))
  }

  lemma ApplyPathLkCons(rer: LW.RegExpRecord, x: Step, s: seq<Step>, inp: LC.Input, gm: LG.GroupMap)
    ensures ApplyPathLk(rer, [x] + s, inp, gm) == ApplyPathLk(rer, s, inp, StepGm(rer, x, inp, gm))
  {
    assert ([x] + s)[0] == x && ([x] + s)[1..] == s;
  }

  lemma ApplyPathLkApp(rer: LW.RegExpRecord, a: seq<Step>, b: seq<Step>, inp: LC.Input, gm: LG.GroupMap)
    ensures ApplyPathLk(rer, a + b, inp, gm) == ApplyPathLk(rer, b, inp, ApplyPathLk(rer, a, inp, gm))
    decreases |a|
  {
    if |a| == 0 {
      assert a + b == b;
    } else {
      assert (a + b)[0] == a[0] && (a + b)[1..] == a[1..] + b;
      ApplyPathLkApp(rer, a[1..], b, inp, StepGm(rer, a[0], inp, gm));
    }
  }

  /** THE EXACT LEAF: the first leaf at `inp` of the spec tree of a fragment stack is
      the Lk-aware fold of the Lk-carrying path (no `S`). */
  lemma EmptyLeavesLk(rer: LW.RegExpRecord, acts: LS.Actions, inp: LC.Input, gm: LG.GroupMap, t: LT.Tree)
    requires EL.PikeLkActionsRec(acts)
    requires LS.IsTree(rer, acts, inp, gm, WP.Forward, t)
    ensures var ls := LT.TreeLeaves(t, gm, inp, WP.Forward);
            var p := FirstEmptyPathLkA(rer, acts, inp);
            (forall i :: 0 <= i < |ls| ==> ls[i].0 == inp || SS.StrictSuffix(ls[i].0, inp, WP.Forward))
            && (NP.FirstAt(ls, inp).Some? <==> p.Some?)
            && (p.Some? ==> NP.FirstAt(ls, inp).Some? && NP.FirstAt(ls, inp).value < |ls|
                            && ls[NP.FirstAt(ls, inp).value].1 == ApplyPathLk(rer, p.value, inp, gm))
    decreases FS.ActionsFuel(acts, inp, WP.Forward)
  {
    var ls := LT.TreeLeaves(t, gm, inp, WP.Forward);
    var p := FirstEmptyPathLkA(rer, acts, inp);
    var idx := LC.Idx(inp);
    NP.FirstAtSpec(ls, inp);
    if |acts| == 0 {
      assert t == LT.Match;
      assert ls == [(inp, gm)];
      assert NP.FirstAt(ls, inp) == Some(0);
      return;
    }
    var cont := acts[1..];
    assert acts == [acts[0]] + cont;
    EL.PikeLkActionsRecTail(acts);
    match acts[0] {
      case Acheck(strcheck) =>
        SS.IsStrictSuffixCorrect(inp, strcheck, WP.Forward);
        if SS.IsStrictSuffix(inp, strcheck, WP.Forward) {
          FS.CheckTermination(cont, inp, strcheck, WP.Forward);
          var tc := t.t;
          assert LS.IsTree(rer, cont, inp, gm, WP.Forward, tc);
          EmptyLeavesLk(rer, cont, inp, gm, tc);
          assert ls == LT.TreeLeaves(tc, gm, inp, WP.Forward);
        } else {
          assert t == LT.Mismatch;
        }
      case Aclose(gid) =>
        FS.CloseTermination(cont, inp, WP.Forward, gid);
        var tc := t.t;
        var gm2 := LG.GMClose(idx, gid, gm);
        assert gm2 == LG.GMUpdate(LG.Close(gid), idx, gm);
        assert LS.IsTree(rer, cont, inp, gm2, WP.Forward, tc);
        EmptyLeavesLk(rer, cont, inp, gm2, tc);
        assert ls == LT.TreeLeaves(tc, gm2, inp, WP.Forward);
        if p.Some? {
          var p' := FirstEmptyPathLkA(rer, cont, inp).value;
          assert p.value == [GA(LG.Close(gid))] + p';
          ApplyPathLkCons(rer, GA(LG.Close(gid)), p', inp, gm);
        }
      case Areg(r) =>
        EL.PikeLkActionsRecConsIff(LS.Areg(r), cont);
        assert EL.PikeLkRegexRec(r);
        match r {
          case Epsilon =>
            FS.EpsilonTermination(cont, inp, WP.Forward);
            EmptyLeavesLk(rer, cont, inp, gm, t);
          case Character(cd) =>
            match LC.ReadChar(rer, cd, inp, WP.Forward) {
              case None =>
                assert t == LT.Mismatch;
              case Some(pair) =>
                var tc := t.t;
                var nexti := pair.1;
                assert nexti == LC.Input(inp.next[1..], [inp.next[0]] + inp.pref);
                assert nexti == LC.AdvanceInputP(inp, WP.Forward);
                SS.ReadCharSuffix(inp, WP.Forward, nexti, cd, pair.0, rer);
                FS.CharacterTermination(rer, cont, inp, WP.Forward, cd, pair.0, nexti);
                assert LS.IsTree(rer, cont, nexti, gm, WP.Forward, tc);
                EmptyLeavesLk(rer, cont, nexti, gm, tc);
                assert ls == LT.TreeLeaves(tc, gm, nexti, WP.Forward);
                forall i | 0 <= i < |ls| ensures SS.StrictSuffix(ls[i].0, inp, WP.Forward) && ls[i].0 != inp {
                  if ls[i].0 != nexti { SS.StrictSuffixTrans(ls[i].0, nexti, inp, WP.Forward); }
                  SS.SSNeq(ls[i].0, inp, WP.Forward);
                }
                assert NP.FirstAt(ls, inp).None?;
            }
          case Disjunction(r1, r2) =>
            FS.DisjunctionLeftTermination(cont, inp, WP.Forward, r1, r2);
            FS.DisjunctionRightTermination(cont, inp, WP.Forward, r1, r2);
            var ta := t.t1;
            var tb := t.t2;
            EL.PikeLkActionsRecConsIff(LS.Areg(r1), cont);
            EL.PikeLkActionsRecConsIff(LS.Areg(r2), cont);
            EmptyLeavesLk(rer, [LS.Areg(r1)] + cont, inp, gm, ta);
            EmptyLeavesLk(rer, [LS.Areg(r2)] + cont, inp, gm, tb);
            var la := LT.TreeLeaves(ta, gm, inp, WP.Forward);
            var lb := LT.TreeLeaves(tb, gm, inp, WP.Forward);
            assert ls == la + lb;
            NP.FirstAtApp(la, lb, inp);
            var pa := FirstEmptyPathLkA(rer, [LS.Areg(r1)] + cont, inp);
            var pb := FirstEmptyPathLkA(rer, [LS.Areg(r2)] + cont, inp);
            forall i | 0 <= i < |ls|
              ensures ls[i].0 == inp || SS.StrictSuffix(ls[i].0, inp, WP.Forward)
            { if i < |la| { assert ls[i] == la[i]; } else { assert ls[i] == lb[i - |la|]; } }
            if pa.Some? {
              assert p == pa;
              var k := NP.FirstAt(la, inp).value;
              assert NP.FirstAt(ls, inp) == Some(k);
              assert ls[k] == la[k];
            } else {
              assert p == pb;
              assert NP.FirstAt(la, inp).None?;
              if pb.Some? {
                var k := NP.FirstAt(lb, inp).value;
                assert NP.FirstAt(ls, inp) == Some(k + |la|);
                assert ls[k + |la|] == lb[k];
              }
            }
          case Sequence(r1, r2) =>
            FS.SequenceTermination(cont, inp, WP.Forward, r1, r2);
            assert LS.SeqList(r1, r2, WP.Forward) == [LS.Areg(r1), LS.Areg(r2)];
            NP.PikeRecCons2(LS.Areg(r1), LS.Areg(r2), cont);
            assert LS.IsTree(rer, [LS.Areg(r1), LS.Areg(r2)] + cont, inp, gm, WP.Forward, t);
            EmptyLeavesLk(rer, [LS.Areg(r1), LS.Areg(r2)] + cont, inp, gm, t);
          case Quantified(greedy, min, delta, r1) =>
            var gidl := L.DefGroups(r1);
            if min > 0 {
              FS.QuantForcedTermination(cont, inp, WP.Forward, r1, min - 1, delta, greedy);
              var q := L.Quantified(greedy, min - 1, delta, r1);
              if EL.CinHeadL(greedy, min, delta, r1) { EL.CinHeadMono(greedy, min, delta, r1, min - 1, delta); }   // (W20) G5a atom
              var tc := t.t;
              var gm2 := LG.GMReset(gidl, gm);
              assert gm2 == LG.GMUpdate(LG.Reset(gidl), idx, gm);
              NP.PikeRecCons2(LS.Areg(r1), LS.Areg(q), cont);
              assert LS.IsTree(rer, [LS.Areg(r1), LS.Areg(q)] + cont, inp, gm2, WP.Forward, tc);
              EmptyLeavesLk(rer, [LS.Areg(r1), LS.Areg(q)] + cont, inp, gm2, tc);
              assert ls == LT.TreeLeaves(tc, gm2, inp, WP.Forward);
              if p.Some? {
                var p' := FirstEmptyPathLkA(rer, [LS.Areg(r1), LS.Areg(q)] + cont, inp).value;
                assert p.value == [GA(LG.Reset(gidl))] + p';
                ApplyPathLkCons(rer, GA(LG.Reset(gidl)), p', inp, gm);
              }
            } else if delta == LN.NN(0) {
              FS.QuantDoneTermination(cont, inp, WP.Forward, r1, greedy);
              EmptyLeavesLk(rer, cont, inp, gm, t);
            } else {
              FS.QuantFreeSkipTermination(cont, inp, WP.Forward, r1, greedy, delta);
              FS.QuantFreeIterTermination(cont, inp, WP.Forward, r1, greedy, delta);
              var plus := LN.NoISub(delta, 1);
              assert plus == FS.NoiPred(delta);
              var q := L.Quantified(greedy, 0, plus, r1);
              EL.CinHeadIntro(greedy, 0, plus, r1);   // (W20) G5a atom
              var iterActs := [LS.Areg(r1), LS.Acheck(inp), LS.Areg(q)] + cont;
              var itert := if greedy then t.t1 else t.t2;
              var skipt := if greedy then t.t2 else t.t1;
              var ti := itert.t;
              var gm2 := LG.GMReset(gidl, gm);
              assert LS.IsTree(rer, iterActs, inp, gm2, WP.Forward, ti);
              assert LS.IsTree(rer, cont, inp, gm, WP.Forward, skipt);
              // the iteration arm has no zero-width leaf (via the plain path)
              var rest := [LS.Acheck(inp), LS.Areg(q)] + cont;
              assert iterActs == [LS.Areg(r1)] + rest;
              NP.NotStrictSuffixSelf(inp);
              assert rest[0] == LS.Acheck(inp);
              assert NP.FirstEmptyPathA(rer, rest, inp).None?;
              if NP.FirstEmptyPathA(rer, iterActs, inp).Some? { NP.EmptyPathNeedsCont(rer, r1, rest, inp); }
              ProjPath(rer, iterActs, inp);
              assert FirstEmptyPathLkA(rer, iterActs, inp).None?;
              EL.PikeLkActionsRecConsIff(LS.Areg(q), cont);
              EL.PikeLkActionsRecConsIff(LS.Acheck(inp), [LS.Areg(q)] + cont);
              EL.PikeLkActionsRecConsIff(LS.Areg(r1), [LS.Acheck(inp)] + ([LS.Areg(q)] + cont));
              assert iterActs == [LS.Areg(r1)] + ([LS.Acheck(inp)] + ([LS.Areg(q)] + cont));
              EmptyLeavesLk(rer, iterActs, inp, gm2, ti);
              EmptyLeavesLk(rer, cont, inp, gm, skipt);
              var li := LT.TreeLeaves(ti, gm2, inp, WP.Forward);
              var lsk := LT.TreeLeaves(skipt, gm, inp, WP.Forward);
              assert LT.TreeLeaves(itert, gm, inp, WP.Forward) == li;
              assert NP.FirstAt(li, inp).None?;
              if greedy {
                assert ls == li + lsk;
                NP.FirstAtApp(li, lsk, inp);
                forall i | 0 <= i < |ls|
                  ensures ls[i].0 == inp || SS.StrictSuffix(ls[i].0, inp, WP.Forward)
                { if i < |li| { assert ls[i] == li[i]; } else { assert ls[i] == lsk[i - |li|]; } }
                if p.Some? {
                  var k := NP.FirstAt(lsk, inp).value;
                  assert NP.FirstAt(ls, inp) == Some(k + |li|);
                  assert ls[k + |li|] == lsk[k];
                }
              } else {
                assert ls == lsk + li;
                NP.FirstAtApp(lsk, li, inp);
                forall i | 0 <= i < |ls|
                  ensures ls[i].0 == inp || SS.StrictSuffix(ls[i].0, inp, WP.Forward)
                { if i < |lsk| { assert ls[i] == lsk[i]; } else { assert ls[i] == li[i - |lsk|]; } }
                if p.Some? {
                  var k := NP.FirstAt(lsk, inp).value;
                  assert NP.FirstAt(ls, inp) == Some(k);
                  assert ls[k] == lsk[k];
                }
              }
            }
          case Group(gid, r1) =>
            FS.GroupTermination(cont, inp, WP.Forward, r1, gid);
            var tc := t.t;
            var gm2 := LG.GMOpen(idx, gid, gm);
            assert gm2 == LG.GMUpdate(LG.Open(gid), idx, gm);
            NP.PikeRecCons2(LS.Areg(r1), LS.Aclose(gid), cont);
            assert LS.IsTree(rer, [LS.Areg(r1), LS.Aclose(gid)] + cont, inp, gm2, WP.Forward, tc);
            EmptyLeavesLk(rer, [LS.Areg(r1), LS.Aclose(gid)] + cont, inp, gm2, tc);
            assert ls == LT.TreeLeaves(tc, gm2, inp, WP.Forward);
            if p.Some? {
              var p' := FirstEmptyPathLkA(rer, [LS.Areg(r1), LS.Aclose(gid)] + cont, inp).value;
              assert p.value == [GA(LG.Open(gid))] + p';
              ApplyPathLkCons(rer, GA(LG.Open(gid)), p', inp, gm);
            }
          case AnchorR(a) =>
            if LS.AnchorSatisfied(rer, a, inp) {
              FS.AnchorTermination(cont, inp, WP.Forward, a);
              var tc := t.t;
              assert LS.IsTree(rer, cont, inp, gm, WP.Forward, tc);
              EmptyLeavesLk(rer, cont, inp, gm, tc);
              assert ls == LT.TreeLeaves(tc, gm, inp, WP.Forward);
            } else {
              assert t == LT.Mismatch;
            }
          case LookaroundR(lk, r1) =>
            FS.LkAfterTermination(cont, inp, WP.Forward, lk, r1);
            var ldir := L.LkDir(lk);
            EL.ComputeTrGmIndepLkRec(rer, r1, inp, gm, ldir);
            match t {
              case LK(lk2, tlk, tc) =>
                assert lk2 == lk;
                assert LS.IsTree(rer, [LS.Areg(r1)], inp, gm, ldir, tlk);
                FU.IsTreeEqComputeTr(rer, [LS.Areg(r1)], inp, gm, ldir, tlk);
                assert tlk == FU.ComputeTr(rer, [LS.Areg(r1)], inp, gm, ldir);
                assert LS.LkResult(lk, tlk, gm, inp).Some?;
                EL.LkResultGmIndep(lk, tlk, gm, inp);
                assert NP.LkVerdictL(rer, lk, r1, inp);
                var gmlk := LS.LkResult(lk, tlk, gm, inp).value;
                assert gmlk == LkGm(rer, lk, r1, inp, gm);
                assert LS.IsTree(rer, cont, inp, gmlk, WP.Forward, tc);
                LT.FirstTreeLeaf(tlk, gm, inp, ldir);
                var sub := LT.TreeLeaves(tlk, gm, inp, ldir);
                if L.Positivity(lk) {
                  assert |sub| > 0 && gmlk == sub[0].1;
                } else {
                  assert |sub| == 0 && gmlk == gm;
                }
                assert ls == LT.TreeLeaves(tc, gmlk, inp, WP.Forward);
                EmptyLeavesLk(rer, cont, inp, gmlk, tc);
                if p.Some? {
                  var p' := FirstEmptyPathLkA(rer, cont, inp).value;
                  assert p.value == [LkS(lk, r1)] + p';
                  ApplyPathLkCons(rer, LkS(lk, r1), p', inp, gm);
                }
              case LKFail(lk2, tlk) =>
                assert lk2 == lk;
                assert LS.IsTree(rer, [LS.Areg(r1)], inp, gm, ldir, tlk);
                FU.IsTreeEqComputeTr(rer, [LS.Areg(r1)], inp, gm, ldir, tlk);
                assert LS.LkResult(lk, tlk, gm, inp).None?;
                EL.LkResultGmIndep(lk, tlk, gm, inp);
                assert !NP.LkVerdictL(rer, lk, r1, inp);
                assert ls == [];
              case _ =>
                assert false;
            }
          case Backreference(_) =>
            assert false;
        }
    }
  }

  // ===========================================================================
  // 3. Composition (the Lk twin of `NT.FirstEmptyPathAComp`)
  // ===========================================================================

  ghost function CompPathLk(a: Option<seq<Step>>, b: Option<seq<Step>>): Option<seq<Step>> {
    match a
    case None => None
    case Some(p) => (match b case None => None case Some(q) => Some(p + q))
  }

  lemma CompPathLkAssoc(a: Option<seq<Step>>, b: Option<seq<Step>>, c: Option<seq<Step>>)
    ensures CompPathLk(CompPathLk(a, b), c) == CompPathLk(a, CompPathLk(b, c))
  {
    if a.Some? && b.Some? && c.Some? {
      assert (a.value + b.value) + c.value == a.value + (b.value + c.value);
    }
  }

  ghost function PrePathLk(x: Step, a: Option<seq<Step>>): Option<seq<Step>> {
    match a case None => None case Some(p) => Some([x] + p)
  }

  lemma PrePathLkComp(x: Step, a: Option<seq<Step>>, b: Option<seq<Step>>)
    ensures CompPathLk(PrePathLk(x, a), b) == PrePathLk(x, CompPathLk(a, b))
  {
    if a.Some? && b.Some? {
      assert ([x] + a.value) + b.value == [x] + (a.value + b.value);
    }
  }

  lemma FirstEmptyPathLkAComp(rer: LW.RegExpRecord, r: L.Regex, cont: LS.Actions, inp: LC.Input)
    ensures FirstEmptyPathLkA(rer, [LS.Areg(r)] + cont, inp)
         == CompPathLk(FirstEmptyPathLkL(rer, r, inp), FirstEmptyPathLkA(rer, cont, inp))
    decreases NT.RSizeL(r), NT.MinOfL(r)
  {
    var acts := [LS.Areg(r)] + cont;
    assert acts[0] == LS.Areg(r) && acts[1..] == cont;
    var solo := [LS.Areg(r)];
    assert solo[0] == LS.Areg(r) && solo[1..] == [];
    assert FirstEmptyPathLkA(rer, [], inp) == Some([]);
    var q := FirstEmptyPathLkA(rer, cont, inp);
    match r
    case Epsilon =>
      assert FirstEmptyPathLkL(rer, r, inp) == Some([]);
      assert FirstEmptyPathLkA(rer, acts, inp) == q;
      if q.Some? { assert [] + q.value == q.value; }
    case Character(_) =>
    case Disjunction(r1, r2) =>
      assert [LS.Areg(r1)] + [] == [LS.Areg(r1)] && [LS.Areg(r2)] + [] == [LS.Areg(r2)];
      FirstEmptyPathLkAComp(rer, r1, cont, inp);
      FirstEmptyPathLkAComp(rer, r2, cont, inp);
      var p1 := FirstEmptyPathLkL(rer, r1, inp);
      var p2 := FirstEmptyPathLkL(rer, r2, inp);
      assert FirstEmptyPathLkL(rer, r, inp) == (match p1 case Some(p) => Some(p) case None => p2);
      assert FirstEmptyPathLkA(rer, acts, inp)
          == (match FirstEmptyPathLkA(rer, [LS.Areg(r1)] + cont, inp)
              case Some(p) => Some(p)
              case None => FirstEmptyPathLkA(rer, [LS.Areg(r2)] + cont, inp));
    case Sequence(r1, r2) =>
      assert [LS.Areg(r1), LS.Areg(r2)] + cont == [LS.Areg(r1)] + ([LS.Areg(r2)] + cont);
      assert [LS.Areg(r1), LS.Areg(r2)] + [] == [LS.Areg(r1)] + [LS.Areg(r2)];
      assert [LS.Areg(r2)] + [] == [LS.Areg(r2)];
      FirstEmptyPathLkAComp(rer, r1, [LS.Areg(r2)] + cont, inp);
      FirstEmptyPathLkAComp(rer, r2, cont, inp);
      FirstEmptyPathLkAComp(rer, r1, [LS.Areg(r2)], inp);
      var p1 := FirstEmptyPathLkL(rer, r1, inp);
      var p2 := FirstEmptyPathLkL(rer, r2, inp);
      assert FirstEmptyPathLkA(rer, acts, inp) == FirstEmptyPathLkA(rer, [LS.Areg(r1)] + ([LS.Areg(r2)] + cont), inp);
      assert FirstEmptyPathLkA(rer, acts, inp) == CompPathLk(p1, CompPathLk(p2, q));
      assert FirstEmptyPathLkL(rer, r, inp) == FirstEmptyPathLkA(rer, solo, inp);
      assert FirstEmptyPathLkA(rer, solo, inp) == FirstEmptyPathLkA(rer, [LS.Areg(r1), LS.Areg(r2)] + [], inp);
      assert FirstEmptyPathLkL(rer, r, inp) == FirstEmptyPathLkA(rer, [LS.Areg(r1)] + [LS.Areg(r2)], inp);
      assert FirstEmptyPathLkA(rer, [LS.Areg(r2)], inp) == p2;
      assert FirstEmptyPathLkL(rer, r, inp) == CompPathLk(p1, p2);
      CompPathLkAssoc(p1, p2, q);
    case Quantified(greedy, min, delta, r1) =>
      var gidl := L.DefGroups(r1);
      if min > 0 {
        var qn := L.Quantified(greedy, min - 1, delta, r1);
        if EL.CinHeadL(greedy, min, delta, r1) { EL.CinHeadMono(greedy, min, delta, r1, min - 1, delta); }   // (W20) G5a atom
        assert NT.RSizeL(qn) == NT.RSizeL(r) && NT.MinOfL(qn) < NT.MinOfL(r);
        assert [LS.Areg(r1), LS.Areg(qn)] + cont == [LS.Areg(r1)] + ([LS.Areg(qn)] + cont);
        assert [LS.Areg(r1), LS.Areg(qn)] + [] == [LS.Areg(r1)] + [LS.Areg(qn)];
        assert [LS.Areg(qn)] + [] == [LS.Areg(qn)];
        FirstEmptyPathLkAComp(rer, r1, [LS.Areg(qn)] + cont, inp);
        FirstEmptyPathLkAComp(rer, qn, cont, inp);
        FirstEmptyPathLkAComp(rer, r1, [LS.Areg(qn)], inp);
        var p1 := FirstEmptyPathLkL(rer, r1, inp);
        var pn := FirstEmptyPathLkL(rer, qn, inp);
        assert FirstEmptyPathLkA(rer, acts, inp) == PrePathLk(GA(LG.Reset(gidl)), CompPathLk(p1, CompPathLk(pn, q)));
        assert FirstEmptyPathLkL(rer, r, inp) == PrePathLk(GA(LG.Reset(gidl)), CompPathLk(p1, pn));
        CompPathLkAssoc(p1, pn, q);
        PrePathLkComp(GA(LG.Reset(gidl)), CompPathLk(p1, pn), q);
      } else {
        assert FirstEmptyPathLkL(rer, r, inp) == Some([]);
        assert FirstEmptyPathLkA(rer, acts, inp) == q;
        if q.Some? { assert [] + q.value == q.value; }
      }
    case Group(gid, r1) =>
      assert [LS.Areg(r1), LS.Aclose(gid)] + cont == [LS.Areg(r1)] + ([LS.Aclose(gid)] + cont);
      assert [LS.Areg(r1), LS.Aclose(gid)] + [] == [LS.Areg(r1)] + [LS.Aclose(gid)];
      assert ([LS.Aclose(gid)] + cont)[0] == LS.Aclose(gid) && ([LS.Aclose(gid)] + cont)[1..] == cont;
      assert [LS.Aclose(gid)][0] == LS.Aclose(gid) && [LS.Aclose(gid)][1..] == [];
      assert FirstEmptyPathLkA(rer, [LS.Aclose(gid)] + cont, inp) == PrePathLk(GA(LG.Close(gid)), q);
      assert [GA(LG.Close(gid))] + [] == [GA(LG.Close(gid))];
      assert FirstEmptyPathLkA(rer, [LS.Aclose(gid)], inp) == Some([GA(LG.Close(gid))]);
      FirstEmptyPathLkAComp(rer, r1, [LS.Aclose(gid)] + cont, inp);
      FirstEmptyPathLkAComp(rer, r1, [LS.Aclose(gid)], inp);
      var p1 := FirstEmptyPathLkL(rer, r1, inp);
      assert FirstEmptyPathLkA(rer, acts, inp) == PrePathLk(GA(LG.Open(gid)), CompPathLk(p1, PrePathLk(GA(LG.Close(gid)), q)));
      assert FirstEmptyPathLkL(rer, r, inp) == PrePathLk(GA(LG.Open(gid)), CompPathLk(p1, Some([GA(LG.Close(gid))])));
      assert CompPathLk(Some([GA(LG.Close(gid))]), q) == PrePathLk(GA(LG.Close(gid)), q);
      CompPathLkAssoc(p1, Some([GA(LG.Close(gid))]), q);
      PrePathLkComp(GA(LG.Open(gid)), CompPathLk(p1, Some([GA(LG.Close(gid))])), q);
    case AnchorR(a) =>
      if LS.AnchorSatisfied(rer, a, inp) {
        assert FirstEmptyPathLkL(rer, r, inp) == Some([]);
        assert FirstEmptyPathLkA(rer, acts, inp) == q;
        if q.Some? { assert [] + q.value == q.value; }
      }
    case LookaroundR(lk, r1) =>
      if NP.LkVerdictL(rer, lk, r1, inp) {
        assert [LkS(lk, r1)] + [] == [LkS(lk, r1)];
        assert FirstEmptyPathLkL(rer, r, inp) == Some([LkS(lk, r1)]);
        assert FirstEmptyPathLkA(rer, acts, inp) == PrePathLk(LkS(lk, r1), q);
      }
    case Backreference(_) =>
  }

  // ===========================================================================
  // 4. Group bookkeeping
  // ===========================================================================

  ghost function DG(r: L.Regex): set<LG.GroupId> { set g | g in L.DefGroups(r) }

  /** Linden-level capture uniqueness (the translation of `PIV.CapUnique`): sibling
      subterms define disjoint groups, a group's id is not reused in its body. */
  ghost predicate GUniq(r: L.Regex)
    decreases r
  {
    match r
    case Disjunction(r1, r2) => GUniq(r1) && GUniq(r2) && DG(r1) !! DG(r2)
    case Sequence(r1, r2) => GUniq(r1) && GUniq(r2) && DG(r1) !! DG(r2)
    case Quantified(_, _, _, r1) => GUniq(r1)
    case Group(id, r1) => id !in DG(r1) && GUniq(r1)
    case LookaroundR(_, r1) => GUniq(r1)
    case _ => true
  }

  lemma LkBodyGroupsSubDG(r: L.Regex)
    ensures LL.LkBodyGroups(r) <= DG(r)
    decreases r
  {
    match r
    case Disjunction(r1, r2) => LkBodyGroupsSubDG(r1); LkBodyGroupsSubDG(r2);
    case Sequence(r1, r2) => LkBodyGroupsSubDG(r1); LkBodyGroupsSubDG(r2);
    case Quantified(_, _, _, r1) => LkBodyGroupsSubDG(r1);
    case Group(_, r1) => LkBodyGroupsSubDG(r1);
    case LookaroundR(_, r1) => LkBodyGroupsSubDG(r1);
    case _ =>
  }

  /** The body's leaf map at `inp`, from the empty map: what the engine's row replay
      from `start_cp` reads (`LkGm` at `Empty`). */
  ghost function BodyLeafE(rer: LW.RegExpRecord, lk: L.Lookaround, b: L.Regex, inp: LC.Input): LG.GroupMap {
    LkGm(rer, lk, b, inp, LG.Empty)
  }

  /** `g` lies in a POSITIVE look the path crosses. */
  ghost predicate Crossed(s: seq<Step>, g: LG.GroupId) {
    exists i :: 0 <= i < |s| && s[i].LkS? && L.Positivity(s[i].lk) && g in L.DefGroups(s[i].b)
  }

  lemma CrossedApp(a: seq<Step>, b: seq<Step>, g: LG.GroupId)
    ensures Crossed(a + b, g) <==> Crossed(a, g) || Crossed(b, g)
  {
    if Crossed(a, g) {
      var i :| 0 <= i < |a| && a[i].LkS? && L.Positivity(a[i].lk) && g in L.DefGroups(a[i].b);
      assert (a + b)[i] == a[i];
    }
    if Crossed(b, g) {
      var i :| 0 <= i < |b| && b[i].LkS? && L.Positivity(b[i].lk) && g in L.DefGroups(b[i].b);
      assert (a + b)[|a| + i] == b[i];
    }
    if Crossed(a + b, g) {
      var i :| 0 <= i < |a + b| && (a + b)[i].LkS? && L.Positivity((a + b)[i].lk) && g in L.DefGroups((a + b)[i].b);
      if i < |a| { assert (a + b)[i] == a[i]; } else { assert (a + b)[i] == b[i - |a|]; }
    }
  }

  /** Every look step of `s`: its body is in the fragment and its groups are in `X`. */
  ghost predicate LkStepsIn(s: seq<Step>, X: set<LG.GroupId>) {
    forall i :: 0 <= i < |s| && s[i].LkS? ==> DG(s[i].b) <= X && EL.PikeLkRegexRec(s[i].b)
  }

  /** A crossed positive look's groups carry its body's leaf (from `Empty`, at `inp`). */
  ghost predicate LkLeafOk(rer: LW.RegExpRecord, s: seq<Step>, inp: LC.Input, gme: LG.GroupMap) {
    forall i :: 0 <= i < |s| && s[i].LkS? && L.Positivity(s[i].lk) ==>
      LL.GmAgreeInside(gme, BodyLeafE(rer, s[i].lk, s[i].b, inp), DG(s[i].b))
  }

  // ===========================================================================
  // 5. One look step
  // ===========================================================================

  /** A look step writes only its body's groups. */
  lemma LkGmOutside(rer: LW.RegExpRecord, lk: L.Lookaround, b: L.Regex, inp: LC.Input, gm: LG.GroupMap)
    requires EL.PikeLkRegexRec(b)
    ensures LL.GmAgreeOutside(LkGm(rer, lk, b, inp, gm), gm, DG(b))
  {
    var ldir := L.LkDir(lk);
    var tlk := FU.ComputeTr(rer, [LS.Areg(b)], inp, gm, ldir);
    if L.Positivity(lk) && LT.TreeRes(tlk, gm, inp, ldir).Some? {
      assert LL.DefGroupsIn(b, DG(b));
      LL.ComputeTrConfinedRec(rer, b, inp, gm, ldir, DG(b));
      LL.GmConfinedLeavesRec(tlk, gm, inp, ldir, DG(b));
      LT.FirstTreeLeaf(tlk, gm, inp, ldir);
      var sub := LT.TreeLeaves(tlk, gm, inp, ldir);
      assert LkGm(rer, lk, b, inp, gm) == sub[0].1;
    } else {
      assert LkGm(rer, lk, b, inp, gm) == gm;
      LL.GmAgreeOutsideRefl(gm, DG(b));
    }
  }

  /** A look step from a map where the body's groups are unset reproduces, on those
      groups, the body's leaf from `Empty`. */
  lemma LkGmInside(rer: LW.RegExpRecord, lk: L.Lookaround, b: L.Regex, inp: LC.Input, gm: LG.GroupMap)
    requires EL.PikeLkRegexRec(b)
    requires forall g :: g in L.DefGroups(b) ==> g !in gm
    ensures LL.GmAgreeInside(LkGm(rer, lk, b, inp, gm), BodyLeafE(rer, lk, b, inp), DG(b))
  {
    var ldir := L.LkDir(lk);
    EL.ComputeTrGmIndepLkRec(rer, b, inp, gm, ldir);
    var tlk := FU.ComputeTr(rer, [LS.Areg(b)], inp, LG.Empty, ldir);
    assert FU.ComputeTr(rer, [LS.Areg(b)], inp, gm, ldir) == tlk;
    assert LL.GmAgreeInside(gm, LG.Empty, DG(b));
    LL.TreeLeavesFrameInside(tlk, gm, LG.Empty, inp, ldir, DG(b));
    LT.FirstTreeLeaf(tlk, gm, inp, ldir);
    LT.FirstTreeLeaf(tlk, LG.Empty, inp, ldir);
    var s1 := LT.TreeLeaves(tlk, gm, inp, ldir);
    var s2 := LT.TreeLeaves(tlk, LG.Empty, inp, ldir);
    assert |s1| == |s2|;
    if L.Positivity(lk) && |s1| > 0 {
      assert LkGm(rer, lk, b, inp, gm) == s1[0].1;
      assert BodyLeafE(rer, lk, b, inp) == s2[0].1;
    } else {
      assert LkGm(rer, lk, b, inp, gm) == gm;
      assert BodyLeafE(rer, lk, b, inp) == LG.Empty;
    }
  }

  // ===========================================================================
  // 6. THE DECOMPOSITION (regex level). At a map where `r`'s groups are unset —
  //    the CIN plus's `Reset(DefGroups(r1))` provides this — the Lk-aware fold of
  //    `r`'s first empty path:
  //    (A) writes only `r`'s groups;
  //    (E) crosses only fragment looks whose groups are look groups of `r`;
  //    (B) leaves every crossed positive look's groups equal to its body's leaf
  //        from `Empty` at `inp`;
  //    (C) leaves every look group of `r` that no crossed positive look owns unset.
  // ===========================================================================

  lemma NulledLooks(rer: LW.RegExpRecord, r: L.Regex, inp: LC.Input, gm: LG.GroupMap)
    requires EL.PikeLkRegexRec(r) && GUniq(r)
    requires forall g :: g in L.DefGroups(r) ==> g !in gm
    requires FirstEmptyPathLkL(rer, r, inp).Some?
    ensures var s := FirstEmptyPathLkL(rer, r, inp).value;
            var gme := ApplyPathLk(rer, s, inp, gm);
            LL.GmAgreeOutside(gme, gm, DG(r))
            && LkStepsIn(s, LL.LkBodyGroups(r))
            && LkLeafOk(rer, s, inp, gme)
            && (forall g :: g in LL.LkBodyGroups(r) && !Crossed(s, g) ==> g !in gme)
    decreases NT.RSizeL(r), NT.MinOfL(r)
  {
    var s := FirstEmptyPathLkL(rer, r, inp).value;
    var gme := ApplyPathLk(rer, s, inp, gm);
    var solo := [LS.Areg(r)];
    assert solo[0] == LS.Areg(r) && solo[1..] == [];
    assert FirstEmptyPathLkA(rer, [], inp) == Some([]);
    LkBodyGroupsSubDG(r);
    match r
    case Epsilon =>
      assert s == [];
    case Character(_) =>
      assert false;
    case Backreference(_) =>
      assert false;
    case AnchorR(a) =>
      assert s == [];
    case LookaroundR(lk, b) =>
      assert NP.LkVerdictL(rer, lk, b, inp);
      assert [LkS(lk, b)] + [] == [LkS(lk, b)];
      assert s == [LkS(lk, b)];
      ApplyPathLkCons(rer, LkS(lk, b), [], inp, gm);
      assert gme == LkGm(rer, lk, b, inp, gm);
      assert EL.PikeLkRegexRec(b);
      LkGmOutside(rer, lk, b, inp, gm);
      LkGmInside(rer, lk, b, inp, gm);
      LkBodyGroupsSubDG(b);
      assert DG(r) == DG(b);
      if L.Positivity(lk) {
        forall g | g in LL.LkBodyGroups(r) ensures Crossed(s, g) { assert s[0].LkS? && g in L.DefGroups(s[0].b); }
      } else {
        // (W20) `EL.NegBodyNoDefs` is gone (G2 gate C: a negative body may capture); its groups stay unset
        assert gme == gm by { reveal LkGm(); }
      }
    case Disjunction(r1, r2) =>
      assert [LS.Areg(r1)] + [] == [LS.Areg(r1)] && [LS.Areg(r2)] + [] == [LS.Areg(r2)];
      var p1 := FirstEmptyPathLkL(rer, r1, inp);
      var p2 := FirstEmptyPathLkL(rer, r2, inp);
      assert FirstEmptyPathLkL(rer, r, inp) == (match p1 case Some(p) => Some(p) case None => p2);
      LkBodyGroupsSubDG(r1);
      LkBodyGroupsSubDG(r2);
      if p1.Some? {
        assert s == p1.value;
        NulledLooks(rer, r1, inp, gm);
        forall g | g in LL.LkBodyGroups(r) && !Crossed(s, g) ensures g !in gme {
          if g !in LL.LkBodyGroups(r1) {
            assert g in DG(r2) && g !in DG(r1);
          }
        }
      } else {
        assert s == p2.value;
        NulledLooks(rer, r2, inp, gm);
        forall g | g in LL.LkBodyGroups(r) && !Crossed(s, g) ensures g !in gme {
          if g !in LL.LkBodyGroups(r2) {
            assert g in DG(r1) && g !in DG(r2);
          }
        }
      }
    case Sequence(r1, r2) =>
      assert [LS.Areg(r1), LS.Areg(r2)] + [] == [LS.Areg(r1)] + [LS.Areg(r2)];
      assert [LS.Areg(r2)] + [] == [LS.Areg(r2)];
      FirstEmptyPathLkAComp(rer, r1, [LS.Areg(r2)], inp);
      assert FirstEmptyPathLkL(rer, r, inp) == FirstEmptyPathLkA(rer, [LS.Areg(r1), LS.Areg(r2)] + [], inp);
      var p1 := FirstEmptyPathLkL(rer, r1, inp);
      var p2 := FirstEmptyPathLkL(rer, r2, inp);
      assert FirstEmptyPathLkA(rer, [LS.Areg(r2)], inp) == p2;
      assert FirstEmptyPathLkL(rer, r, inp) == CompPathLk(p1, p2);
      var s1 := p1.value;
      var s2 := p2.value;
      assert s == s1 + s2;
      LkBodyGroupsSubDG(r1);
      LkBodyGroupsSubDG(r2);
      NulledLooks(rer, r1, inp, gm);
      var gm1 := ApplyPathLk(rer, s1, inp, gm);
      assert forall g :: g in L.DefGroups(r2) ==> g !in gm1 by {
        forall g | g in L.DefGroups(r2) ensures g !in gm1 { assert g in DG(r2) && g !in DG(r1); }
      }
      NulledLooks(rer, r2, inp, gm1);
      ApplyPathLkApp(rer, s1, s2, inp, gm);
      assert gme == ApplyPathLk(rer, s2, inp, gm1);
      assert {:split_here} true;
      // (A)
      assert LL.GmAgreeOutside(gme, gm, DG(r)) by {
        forall g | g !in DG(r) ensures (g in gme <==> g in gm) && (g in gme ==> gme[g] == gm[g]) {
          assert g !in DG(r1) && g !in DG(r2);
        }
      }
      // (E)
      assert LkStepsIn(s, LL.LkBodyGroups(r)) by {
        forall i | 0 <= i < |s| && s[i].LkS? ensures DG(s[i].b) <= LL.LkBodyGroups(r) && EL.PikeLkRegexRec(s[i].b) {
          if i < |s1| { assert s[i] == s1[i]; } else { assert s[i] == s2[i - |s1|]; }
        }
      }
      assert {:split_here} true;
      // (B)
      assert LkLeafOk(rer, s, inp, gme) by {
        forall i | 0 <= i < |s| && s[i].LkS? && L.Positivity(s[i].lk)
          ensures LL.GmAgreeInside(gme, BodyLeafE(rer, s[i].lk, s[i].b, inp), DG(s[i].b))
        {
          if i < |s1| {
            assert s[i] == s1[i];
            var BL := BodyLeafE(rer, s1[i].lk, s1[i].b, inp);
            assert LL.GmAgreeInside(gm1, BL, DG(s1[i].b));
            assert DG(s1[i].b) <= DG(r1);
            forall g | g in DG(s1[i].b) ensures (g in gme <==> g in BL) && (g in gme ==> gme[g] == BL[g]) {
              assert g !in DG(r2);
            }
          } else {
            assert s[i] == s2[i - |s1|];
          }
        }
      }
      assert {:split_here} true;
      // (C)
      forall g | g in LL.LkBodyGroups(r) && !Crossed(s, g) ensures g !in gme {
        CrossedApp(s1, s2, g);
        if g in LL.LkBodyGroups(r1) {
          assert g !in gm1;
          assert g in DG(r1) && g !in DG(r2);
        }
      }
    case Group(gid, r1) =>
      assert [LS.Areg(r1), LS.Aclose(gid)] + [] == [LS.Areg(r1)] + [LS.Aclose(gid)];
      assert [LS.Aclose(gid)][0] == LS.Aclose(gid) && [LS.Aclose(gid)][1..] == [];
      assert [GA(LG.Close(gid))] + [] == [GA(LG.Close(gid))];
      assert FirstEmptyPathLkA(rer, [LS.Aclose(gid)], inp) == Some([GA(LG.Close(gid))]);
      FirstEmptyPathLkAComp(rer, r1, [LS.Aclose(gid)], inp);
      var p1 := FirstEmptyPathLkL(rer, r1, inp);
      assert FirstEmptyPathLkL(rer, r, inp) == PrePathLk(GA(LG.Open(gid)), CompPathLk(p1, Some([GA(LG.Close(gid))])));
      var s1 := p1.value;
      assert s == [GA(LG.Open(gid))] + (s1 + [GA(LG.Close(gid))]);
      var idx := LC.Idx(inp);
      var gm0 := LG.GMOpen(idx, gid, gm);
      LkBodyGroupsSubDG(r1);
      NulledLooks(rer, r1, inp, gm0);
      var gm1 := ApplyPathLk(rer, s1, inp, gm0);
      ApplyPathLkCons(rer, GA(LG.Open(gid)), s1 + [GA(LG.Close(gid))], inp, gm);
      ApplyPathLkApp(rer, s1, [GA(LG.Close(gid))], inp, gm0);
      ApplyPathLkCons(rer, GA(LG.Close(gid)), [], inp, gm1);
      assert gme == LG.GMClose(idx, gid, gm1);
      assert {:split_here} true;
      assert LL.GmAgreeOutside(gme, gm, DG(r)) by {
        forall g | g !in DG(r) ensures (g in gme <==> g in gm) && (g in gme ==> gme[g] == gm[g]) {
          assert g != gid && g !in DG(r1);
        }
      }
      assert LkStepsIn(s, LL.LkBodyGroups(r)) by {
        forall i | 0 <= i < |s| && s[i].LkS? ensures DG(s[i].b) <= LL.LkBodyGroups(r) && EL.PikeLkRegexRec(s[i].b) {
          if 1 <= i < 1 + |s1| { assert s[i] == s1[i - 1]; }
          else if i == 0 { assert s[i] == GA(LG.Open(gid)); }
          else { assert s[i] == GA(LG.Close(gid)); }
        }
      }
      assert {:split_here} true;
      assert LkLeafOk(rer, s, inp, gme) by {
        forall i | 0 <= i < |s| && s[i].LkS? && L.Positivity(s[i].lk)
          ensures LL.GmAgreeInside(gme, BodyLeafE(rer, s[i].lk, s[i].b, inp), DG(s[i].b))
        {
          if 1 <= i < 1 + |s1| {
            assert s[i] == s1[i - 1];
            var BL := BodyLeafE(rer, s1[i - 1].lk, s1[i - 1].b, inp);
            assert LL.GmAgreeInside(gm1, BL, DG(s1[i - 1].b));
            assert DG(s1[i - 1].b) <= DG(r1);
          } else if i == 0 { assert s[i] == GA(LG.Open(gid)); }
          else { assert s[i] == GA(LG.Close(gid)); }
        }
      }
      forall g | g in LL.LkBodyGroups(r) && !Crossed(s, g) ensures g !in gme {
        CrossedApp([GA(LG.Open(gid))], s1 + [GA(LG.Close(gid))], g);
        CrossedApp(s1, [GA(LG.Close(gid))], g);
        assert !Crossed(s1, g);
        assert g !in gm1 && g != gid;
      }
    case Quantified(greedy, min, delta, r1) =>
      var gidl := L.DefGroups(r1);
      LkBodyGroupsSubDG(r1);
      if min == 0 {
        assert FirstEmptyPathLkL(rer, r, inp) == Some([]);
        assert s == [];
      } else {
        var qn := L.Quantified(greedy, min - 1, delta, r1);
        if EL.CinHeadL(greedy, min, delta, r1) { EL.CinHeadMono(greedy, min, delta, r1, min - 1, delta); }   // (W20) G5a atom
        assert NT.RSizeL(qn) == NT.RSizeL(r) && NT.MinOfL(qn) < NT.MinOfL(r);
        assert [LS.Areg(r1), LS.Areg(qn)] + [] == [LS.Areg(r1)] + [LS.Areg(qn)];
        assert [LS.Areg(qn)] + [] == [LS.Areg(qn)];
        FirstEmptyPathLkAComp(rer, r1, [LS.Areg(qn)], inp);
        var p1 := FirstEmptyPathLkL(rer, r1, inp);
        var pn := FirstEmptyPathLkL(rer, qn, inp);
        assert FirstEmptyPathLkA(rer, [LS.Areg(qn)], inp) == pn;
        assert FirstEmptyPathLkL(rer, r, inp) == PrePathLk(GA(LG.Reset(gidl)), CompPathLk(p1, pn));
        var s1 := p1.value;
        var sn := pn.value;
        assert s == [GA(LG.Reset(gidl))] + (s1 + sn);
        var idx := LC.Idx(inp);
        var gm0 := LG.GMReset(gidl, gm);
        NulledLooks(rer, r1, inp, gm0);
        var gm1 := ApplyPathLk(rer, s1, inp, gm0);
        ApplyPathLkCons(rer, GA(LG.Reset(gidl)), s1 + sn, inp, gm);
        ApplyPathLkApp(rer, s1, sn, inp, gm0);
        assert gme == ApplyPathLk(rer, sn, inp, gm1);
        assert {:split_here} true;
        if min - 1 == 0 {
          assert FirstEmptyPathLkL(rer, qn, inp) == Some([]);
          assert sn == [] && gme == gm1;
          assert s == [GA(LG.Reset(gidl))] + s1;
          assert LL.GmAgreeOutside(gme, gm, DG(r));
          assert LkStepsIn(s, LL.LkBodyGroups(r)) by {
            forall i | 0 <= i < |s| && s[i].LkS? ensures DG(s[i].b) <= LL.LkBodyGroups(r) && EL.PikeLkRegexRec(s[i].b) {
              if i > 0 { assert s[i] == s1[i - 1]; }
            }
          }
          assert LkLeafOk(rer, s, inp, gme) by {
            forall i | 0 <= i < |s| && s[i].LkS? && L.Positivity(s[i].lk)
              ensures LL.GmAgreeInside(gme, BodyLeafE(rer, s[i].lk, s[i].b, inp), DG(s[i].b))
            { if i > 0 { assert s[i] == s1[i - 1]; } }
          }
          forall g | g in LL.LkBodyGroups(r) && !Crossed(s, g) ensures g !in gme {
            CrossedApp([GA(LG.Reset(gidl))], s1, g);
          }
        } else {
          // the next forced copy restarts from a Reset: fold it from the reset map
          var qn2 := L.Quantified(greedy, min - 2, delta, r1);
          assert [LS.Areg(r1), LS.Areg(qn2)] + [] == [LS.Areg(r1)] + [LS.Areg(qn2)];
          assert [LS.Areg(qn2)] + [] == [LS.Areg(qn2)];
          var soloN := [LS.Areg(qn)];
          assert soloN[0] == LS.Areg(qn) && soloN[1..] == [];
          FirstEmptyPathLkAComp(rer, r1, [LS.Areg(qn2)], inp);
          var pn2 := FirstEmptyPathLkL(rer, qn2, inp);
          assert FirstEmptyPathLkA(rer, [LS.Areg(qn2)], inp) == pn2;
          assert pn == PrePathLk(GA(LG.Reset(gidl)), CompPathLk(p1, pn2));
          var sn2 := pn2.value;
          assert sn == [GA(LG.Reset(gidl))] + (s1 + sn2);
          var gm1r := LG.GMReset(gidl, gm1);
          assert LG.GMReset(gidl, gm1r) == gm1r;
          ApplyPathLkCons(rer, GA(LG.Reset(gidl)), s1 + sn2, inp, gm1);
          ApplyPathLkCons(rer, GA(LG.Reset(gidl)), s1 + sn2, inp, gm1r);
          assert gme == ApplyPathLk(rer, sn, inp, gm1r);
          NulledLooks(rer, qn, inp, gm1r);
          assert L.DefGroups(qn) == gidl && LL.LkBodyGroups(qn) == LL.LkBodyGroups(r1);
          assert {:split_here} true;
          assert LL.GmAgreeOutside(gme, gm, DG(r)) by {
            forall g | g !in DG(r) ensures (g in gme <==> g in gm) && (g in gme ==> gme[g] == gm[g]) {
              assert g !in DG(r1) && g !in gidl;
            }
          }
          assert LkStepsIn(s, LL.LkBodyGroups(r)) by {
            forall i | 0 <= i < |s| && s[i].LkS? ensures DG(s[i].b) <= LL.LkBodyGroups(r) && EL.PikeLkRegexRec(s[i].b) {
              if 1 <= i < 1 + |s1| { assert s[i] == s1[i - 1]; }
              else if i >= 1 + |s1| { assert s[i] == sn[i - 1 - |s1|]; }
            }
          }
          assert {:split_here} true;
          // every look step of the first copy recurs in the next copy (same choices)
          assert LkLeafOk(rer, s, inp, gme) by {
            forall i | 0 <= i < |s| && s[i].LkS? && L.Positivity(s[i].lk)
              ensures LL.GmAgreeInside(gme, BodyLeafE(rer, s[i].lk, s[i].b, inp), DG(s[i].b))
            {
              if 1 <= i < 1 + |s1| {
                assert s[i] == s1[i - 1];
                assert sn[i] == s1[i - 1];
              } else if i >= 1 + |s1| {
                assert s[i] == sn[i - 1 - |s1|];
              }
            }
          }
          assert {:split_here} true;
          forall g | g in LL.LkBodyGroups(r) && !Crossed(s, g) ensures g !in gme {
            CrossedApp([GA(LG.Reset(gidl))], s1 + sn, g);
            CrossedApp(s1, sn, g);
            assert !Crossed(sn, g);
          }
        }
      }
  }

  // ===========================================================================
  // 7. Step validity without uniqueness, and the generic frames
  // ===========================================================================

  /** Every look step: fragment body, groups in `X`, gate passes at `inp`. */
  ghost predicate LkStepsOk(rer: LW.RegExpRecord, s: seq<Step>, inp: LC.Input, X: set<LG.GroupId>) {
    forall i :: 0 <= i < |s| && s[i].LkS? ==>
      DG(s[i].b) <= X && EL.PikeLkRegexRec(s[i].b) && NP.LkVerdictL(rer, s[i].lk, s[i].b, inp)
  }

  lemma LkStepsOkCat(rer: LW.RegExpRecord, a: seq<Step>, b: seq<Step>, inp: LC.Input, X: set<LG.GroupId>)
    requires LkStepsOk(rer, a, inp, X) && LkStepsOk(rer, b, inp, X)
    ensures LkStepsOk(rer, a + b, inp, X)
  {
    forall i | 0 <= i < |a + b| && (a + b)[i].LkS?
      ensures DG((a + b)[i].b) <= X && EL.PikeLkRegexRec((a + b)[i].b) && NP.LkVerdictL(rer, (a + b)[i].lk, (a + b)[i].b, inp)
    { if i < |a| { assert (a + b)[i] == a[i]; } else { assert (a + b)[i] == b[i - |a|]; } }
  }

  lemma StepsOkL(rer: LW.RegExpRecord, r: L.Regex, inp: LC.Input)
    requires EL.PikeLkRegexRec(r)
    requires FirstEmptyPathLkL(rer, r, inp).Some?
    ensures LkStepsOk(rer, FirstEmptyPathLkL(rer, r, inp).value, inp, LL.LkBodyGroups(r))
    decreases NT.RSizeL(r), NT.MinOfL(r)
  {
    var s := FirstEmptyPathLkL(rer, r, inp).value;
    var solo := [LS.Areg(r)];
    assert solo[0] == LS.Areg(r) && solo[1..] == [];
    assert FirstEmptyPathLkA(rer, [], inp) == Some([]);
    match r
    case Epsilon => assert s == [];
    case Character(_) =>
    case Backreference(_) =>
    case AnchorR(a) => assert s == [];
    case LookaroundR(lk, b) =>
      assert [LkS(lk, b)] + [] == [LkS(lk, b)];
      assert s == [LkS(lk, b)];
    case Disjunction(r1, r2) =>
      assert [LS.Areg(r1)] + [] == [LS.Areg(r1)] && [LS.Areg(r2)] + [] == [LS.Areg(r2)];
      var p1 := FirstEmptyPathLkL(rer, r1, inp);
      assert FirstEmptyPathLkL(rer, r, inp) == (match p1 case Some(p) => Some(p) case None => FirstEmptyPathLkL(rer, r2, inp));
      if p1.Some? { StepsOkL(rer, r1, inp); } else { StepsOkL(rer, r2, inp); }
    case Sequence(r1, r2) =>
      assert [LS.Areg(r1), LS.Areg(r2)] + [] == [LS.Areg(r1)] + [LS.Areg(r2)];
      assert [LS.Areg(r2)] + [] == [LS.Areg(r2)];
      FirstEmptyPathLkAComp(rer, r1, [LS.Areg(r2)], inp);
      assert FirstEmptyPathLkL(rer, r, inp) == FirstEmptyPathLkA(rer, [LS.Areg(r1), LS.Areg(r2)] + [], inp);
      assert FirstEmptyPathLkA(rer, [LS.Areg(r2)], inp) == FirstEmptyPathLkL(rer, r2, inp);
      StepsOkL(rer, r1, inp);
      StepsOkL(rer, r2, inp);
      LkStepsOkCat(rer, FirstEmptyPathLkL(rer, r1, inp).value, FirstEmptyPathLkL(rer, r2, inp).value, inp, LL.LkBodyGroups(r));
    case Group(gid, r1) =>
      assert [LS.Areg(r1), LS.Aclose(gid)] + [] == [LS.Areg(r1)] + [LS.Aclose(gid)];
      assert [LS.Aclose(gid)][0] == LS.Aclose(gid) && [LS.Aclose(gid)][1..] == [];
      assert [GA(LG.Close(gid))] + [] == [GA(LG.Close(gid))];
      assert FirstEmptyPathLkA(rer, [LS.Aclose(gid)], inp) == Some([GA(LG.Close(gid))]);
      FirstEmptyPathLkAComp(rer, r1, [LS.Aclose(gid)], inp);
      var s1 := FirstEmptyPathLkL(rer, r1, inp).value;
      assert s == [GA(LG.Open(gid))] + (s1 + [GA(LG.Close(gid))]);
      StepsOkL(rer, r1, inp);
      LkStepsOkCat(rer, s1, [GA(LG.Close(gid))], inp, LL.LkBodyGroups(r));
      LkStepsOkCat(rer, [GA(LG.Open(gid))], s1 + [GA(LG.Close(gid))], inp, LL.LkBodyGroups(r));
    case Quantified(greedy, min, delta, r1) =>
      if min == 0 {
        assert s == [];
      } else {
        var gidl := L.DefGroups(r1);
        var qn := L.Quantified(greedy, min - 1, delta, r1);
        if EL.CinHeadL(greedy, min, delta, r1) { EL.CinHeadMono(greedy, min, delta, r1, min - 1, delta); }   // (W20) G5a atom
        assert NT.RSizeL(qn) == NT.RSizeL(r) && NT.MinOfL(qn) < NT.MinOfL(r);
        assert [LS.Areg(r1), LS.Areg(qn)] + [] == [LS.Areg(r1)] + [LS.Areg(qn)];
        assert [LS.Areg(qn)] + [] == [LS.Areg(qn)];
        FirstEmptyPathLkAComp(rer, r1, [LS.Areg(qn)], inp);
        assert FirstEmptyPathLkA(rer, [LS.Areg(qn)], inp) == FirstEmptyPathLkL(rer, qn, inp);
        var s1 := FirstEmptyPathLkL(rer, r1, inp).value;
        var sn := FirstEmptyPathLkL(rer, qn, inp).value;
        assert s == [GA(LG.Reset(gidl))] + (s1 + sn);
        StepsOkL(rer, r1, inp);
        StepsOkL(rer, qn, inp);
        LkStepsOkCat(rer, s1, sn, inp, LL.LkBodyGroups(r));
        LkStepsOkCat(rer, [GA(LG.Reset(gidl))], s1 + sn, inp, LL.LkBodyGroups(r));
      }
  }

  /** A path whose group actions and look bodies stay in `G` leaves the map unchanged outside `G`. */
  lemma ApplyPathLkOutside(rer: LW.RegExpRecord, s: seq<Step>, inp: LC.Input, gm: LG.GroupMap, G: set<LG.GroupId>)
    requires NP.PathIn(Proj(s), G)
    requires forall i :: 0 <= i < |s| && s[i].LkS? ==> DG(s[i].b) <= G && EL.PikeLkRegexRec(s[i].b)
    ensures LL.GmAgreeOutside(ApplyPathLk(rer, s, inp, gm), gm, G)
    decreases |s|
  {
    if |s| == 0 { LL.GmAgreeOutsideRefl(gm, G); return; }
    assert s == [s[0]] + s[1..];
    ProjCons(s[0], s[1..]);
    var gm1 := StepGm(rer, s[0], inp, gm);
    match s[0]
    case GA(a) =>
      assert Proj(s) == [a] + Proj(s[1..]);
      assert Proj(s)[0] == a;
      assert CE.GmActionIn(a, G);
      assert LL.GmAgreeOutside(gm1, gm, G) by {
        match a
        case Open(g) =>
        case Close(g) =>
        case Reset(gs) =>
      }
      forall i | 0 <= i < |Proj(s[1..])| ensures CE.GmActionIn(Proj(s[1..])[i], G) { assert Proj(s[1..])[i] == Proj(s)[i + 1]; }
    case LkS(lk, b) =>
      assert Proj(s) == Proj(s[1..]);
      LkGmOutside(rer, lk, b, inp, gm);
  }

  /** (D) outside `X` ⊇ every crossed body's groups, the Lk-aware fold IS the bare-gate fold. */
  lemma ApplyPathLkVsPlain(rer: LW.RegExpRecord, s: seq<Step>, inp: LC.Input, gm1: LG.GroupMap, gm2: LG.GroupMap,
                           X: set<LG.GroupId>)
    requires LL.GmAgreeOutside(gm1, gm2, X)
    requires forall i :: 0 <= i < |s| && s[i].LkS? ==> DG(s[i].b) <= X && EL.PikeLkRegexRec(s[i].b)
    ensures LL.GmAgreeOutside(ApplyPathLk(rer, s, inp, gm1), NP.ApplyPath(Proj(s), LC.Idx(inp), gm2), X)
    decreases |s|
  {
    if |s| == 0 { return; }
    assert s == [s[0]] + s[1..];
    ProjCons(s[0], s[1..]);
    match s[0]
    case GA(a) =>
      var P := Proj(s);
      assert P == [a] + Proj(s[1..]);
      assert P[0] == a && P[1..] == Proj(s[1..]);
      LL.GMUpdateAgreeOutside(a, LC.Idx(inp), gm1, gm2, X);
      ApplyPathLkVsPlain(rer, s[1..], inp, LG.GMUpdate(a, LC.Idx(inp), gm1), LG.GMUpdate(a, LC.Idx(inp), gm2), X);
    case LkS(lk, b) =>
      assert Proj(s) == Proj(s[1..]);
      LkGmOutside(rer, lk, b, inp, gm1);
      var g1 := LkGm(rer, lk, b, inp, gm1);
      assert LL.GmAgreeOutside(g1, gm2, X) by {
        forall g | g !in X ensures (g in g1 <==> g in gm2) && (g in g1 ==> g1[g] == gm2[g]) { assert g !in DG(b); }
      }
      ApplyPathLkVsPlain(rer, s[1..], inp, g1, gm2, X);
  }

  // ===========================================================================
  // 8. The Lk chain (the engine's skip arm with the crossed looks as LK nodes)
  // ===========================================================================

  ghost function ChainLk(rer: LW.RegExpRecord, s: seq<Step>, inp: LC.Input, t: LT.Tree): LT.Tree
    decreases |s|
  {
    if |s| == 0 then t
    else match s[0]
      case GA(a) => LT.GroupActionT(a, ChainLk(rer, s[1..], inp, t))
      case LkS(lk, b) => LT.LK(lk, FU.ComputeTr(rer, [LS.Areg(b)], inp, LG.Empty, L.LkDir(lk)), ChainLk(rer, s[1..], inp, t))
  }

  /** One LK node of the chain: a passing gate continues from the look step's map. */
  lemma LkNodeLeaves(rer: LW.RegExpRecord, lk: L.Lookaround, b: L.Regex, tlk: LT.Tree, c: LT.Tree,
                     gm: LG.GroupMap, inp: LC.Input)
    requires EL.PikeLkRegexRec(b) && NP.LkVerdictL(rer, lk, b, inp)
    requires tlk == FU.ComputeTr(rer, [LS.Areg(b)], inp, LG.Empty, L.LkDir(lk))
    ensures LT.TreeLeaves(LT.LK(lk, tlk, c), gm, inp, WP.Forward)
         == LT.TreeLeaves(c, LkGm(rer, lk, b, inp, gm), inp, WP.Forward)
  {
    var ldir := L.LkDir(lk);
    EL.ComputeTrGmIndepLkRec(rer, b, inp, gm, ldir);
    assert FU.ComputeTr(rer, [LS.Areg(b)], inp, gm, ldir) == tlk;
    assert LkGm(rer, lk, b, inp, gm) == (match LS.LkResult(lk, tlk, gm, inp) case Some(g) => g case None => gm);
    hide FU.ComputeTr;
    assert LS.LkResult(lk, tlk, LG.Empty, inp).Some?;
    EL.LkResultGmIndep(lk, tlk, gm, inp);
    assert LS.LkResult(lk, tlk, gm, inp).Some?;
    LT.FirstTreeLeaf(tlk, gm, inp, ldir);
    var sub := LT.TreeLeaves(tlk, gm, inp, ldir);
    if L.Positivity(lk) {
      assert |sub| > 0;
      assert LS.LkResult(lk, tlk, gm, inp).value == sub[0].1;
      assert LT.TreeLeaves(LT.LK(lk, tlk, c), gm, inp, WP.Forward) == LT.TreeLeaves(c, sub[0].1, inp, WP.Forward);
    } else {
      assert |sub| == 0;
      assert LS.LkResult(lk, tlk, gm, inp).value == gm;
      assert LT.TreeLeaves(LT.LK(lk, tlk, c), gm, inp, WP.Forward) == LT.TreeLeaves(c, gm, inp, WP.Forward);
    }
  }

  lemma ChainLkLeaves(rer: LW.RegExpRecord, s: seq<Step>, t: LT.Tree, gm: LG.GroupMap, inp: LC.Input)
    requires forall i :: 0 <= i < |s| && s[i].LkS? ==> EL.PikeLkRegexRec(s[i].b) && NP.LkVerdictL(rer, s[i].lk, s[i].b, inp)
    ensures LT.TreeLeaves(ChainLk(rer, s, inp, t), gm, inp, WP.Forward)
         == LT.TreeLeaves(t, ApplyPathLk(rer, s, inp, gm), inp, WP.Forward)
    decreases |s|
  {
    if |s| == 0 { return; }
    var gm1 := StepGm(rer, s[0], inp, gm);
    forall i | 0 <= i < |s[1..]| && s[1..][i].LkS?
      ensures EL.PikeLkRegexRec(s[1..][i].b) && NP.LkVerdictL(rer, s[1..][i].lk, s[1..][i].b, inp)
    { assert s[1..][i] == s[i + 1]; }
    ChainLkLeaves(rer, s[1..], t, gm1, inp);
    var c := ChainLk(rer, s[1..], inp, t);
    assert ApplyPathLk(rer, s, inp, gm) == ApplyPathLk(rer, s[1..], inp, gm1);
    match s[0]
    case GA(a) =>
      assert ChainLk(rer, s, inp, t) == LT.GroupActionT(a, c);
    case LkS(lk, b) =>
      var tlk := FU.ComputeTr(rer, [LS.Areg(b)], inp, LG.Empty, L.LkDir(lk));
      assert ChainLk(rer, s, inp, t) == LT.LK(lk, tlk, c);
      LkNodeLeaves(rer, lk, b, tlk, c, gm, inp);
  }

  // ===========================================================================
  // 9. RUNG A, EXACT: no `S`, no `LkBodiesInS` premise. The engine's CIN shape
  //    with the crossed looks kept as LK nodes on the skip arm has the SAME first
  //    result as the spec's forced-iteration tree, at every incoming map.
  // ===========================================================================

  lemma CinPlusPriorityLk(rer: LW.RegExpRecord, r1: L.Regex, cont: LS.Actions, inp: LC.Input, gm: LG.GroupMap,
                          tplus: LT.Tree, titer: LT.Tree, tcont: LT.Tree)
    requires EL.PikeLkRegexRec(r1) && EL.PikeLkActionsRec(cont)
    requires NUL.CINullableL(r1)
    requires LS.IsTree(rer, [LS.Areg(L.Quantified(true, 1, LN.Inf, r1))] + cont, inp, gm, WP.Forward, tplus)
    requires LS.IsTree(rer, [LS.Areg(r1), LS.Acheck(inp), LS.Areg(L.Quantified(true, 0, LN.Inf, r1))] + cont,
                       inp, LG.GMReset(L.DefGroups(r1), gm), WP.Forward, titer)
    requires LS.IsTree(rer, cont, inp, gm, WP.Forward, tcont)
    ensures FirstEmptyPathLkL(rer, r1, inp).Some?
    ensures ProjO(FirstEmptyPathLkL(rer, r1, inp)) == NP.FirstEmptyPathL(rer, r1, inp)
    ensures var gidl := L.DefGroups(r1);
            var s := FirstEmptyPathLkL(rer, r1, inp).value;
            var tcin := LT.Choice(LT.GroupActionT(LG.Reset(gidl), titer),
                                  LT.GroupActionT(LG.Reset(gidl), ChainLk(rer, s, inp, tcont)));
            LT.TreeRes(tcin, gm, inp, WP.Forward) == LT.TreeRes(tplus, gm, inp, WP.Forward)
  {
    var gidl := L.DefGroups(r1);
    var Gset := set g | g in gidl;
    var gm' := LG.GMReset(gidl, gm);
    var idx := LC.Idx(inp);
    var Q1 := L.Quantified(true, 1, LN.Inf, r1);
    var Q0 := L.Quantified(true, 0, LN.Inf, r1);
    EL.CinHeadIntro(true, 0, LN.Inf, r1);   // (W20) G5a atom
    var A := [LS.Areg(r1)];
    var rest := [LS.Areg(Q0)] + cont;
    var chk := [LS.Acheck(inp)] + rest;
    var iterActs := [LS.Areg(r1), LS.Acheck(inp), LS.Areg(Q0)] + cont;
    assert iterActs == A + chk;
    var plusActs := [LS.Areg(Q1)] + cont;
    assert plusActs[0] == LS.Areg(Q1) && plusActs[1..] == cont;

    // ---- the spec tree: Reset; tc with tc the tree of A + rest at gm' ----
    assert tplus.GroupActionT? && tplus.g == LG.Reset(gidl);
    var tc := tplus.t;
    assert LS.IsTree(rer, [LS.Areg(r1), LS.Areg(L.Quantified(true, 0, LN.Inf, r1))] + cont, inp, gm', WP.Forward, tc);
    assert [LS.Areg(r1), LS.Areg(Q0)] + cont == A + rest;
    var Lplus := LT.TreeLeaves(tc, gm', inp, WP.Forward);
    assert LT.TreeLeaves(tplus, gm, inp, WP.Forward) == Lplus;

    assert {:split_here} true;
    EL.PikeLkActionsRecConsIff(LS.Areg(r1), []);
    assert EL.PikeLkActionsRec(A);
    EL.PikeLkActionsRecConsIff(LS.Areg(Q0), cont);
    assert EL.PikeLkActionsRec(rest);

    // ---- the Lk-carrying first empty path of r1, and its fold ----
    assert A == [LS.Areg(r1)] + [];
    NP.CINullableEmptyPathA(rer, r1, [], inp);
    ProjPath(rer, A, inp);
    var s := FirstEmptyPathLkL(rer, r1, inp).value;
    var gmE := ApplyPathLk(rer, s, inp, gm');
    assert NP.ActsGroupsIn(A, Gset) by {
      forall i | 0 <= i < |A| ensures (A[i].Areg? ==> forall g :: g in L.DefGroups(A[i].r) ==> g in Gset) && (A[i].Aclose? ==> A[i].gid in Gset) {}
    }
    NP.PathActionsIn(rer, A, inp, Gset);
    assert Proj(s) == NP.FirstEmptyPathA(rer, A, inp).value;
    StepsOkL(rer, r1, inp);
    LkBodyGroupsSubDG(r1);
    assert DG(r1) == Gset;
    ApplyPathLkOutside(rer, s, inp, gm', Gset);
    NP.GMResetAgree(gidl, gmE, gm');
    assert LG.GMReset(gidl, gm') == gm';
    assert LG.GMReset(gidl, gmE) == gm';

    assert {:split_here} true;
    // ---- r1's own tree: its first empty leaf IS gmE ----
    var tr1 := FU.ComputeTr(rer, A, inp, gm', WP.Forward);
    FU.ComputeTrIsTree(rer, A, inp, gm', WP.Forward);
    var ls := LT.TreeLeaves(tr1, gm', inp, WP.Forward);
    EmptyLeavesLk(rer, A, inp, gm', tr1);
    NP.FirstAtSpec(ls, inp);
    var e := NP.FirstAt(ls, inp).value;
    var gme := ls[e].1;
    assert gme == gmE;

    assert {:split_here} true;
    // ---- the two flat-maps over r1's leaves ----
    var frest := EQ.ActFromLeafFn(rer, rest, WP.Forward);
    var fchk := EQ.ActFromLeafFn(rer, chk, WP.Forward);
    EQ.ActFromLeafDeterm(rer, WP.Forward, rest);
    EQ.ActFromLeafDeterm(rer, WP.Forward, chk);
    EQ.LeavesConcat(rer, inp, gm', WP.Forward, A, rest, tc, tr1);
    assert FM.FlatMapRel(ls, frest, Lplus);
    var I := LT.TreeLeaves(titer, gm', inp, WP.Forward);
    EQ.LeavesConcat(rer, inp, gm', WP.Forward, A, chk, titer, tr1);
    assert FM.FlatMapRel(ls, fchk, I);

    assert {:split_here} true;
    var pre := ls[..e];
    var post := ls[e + 1..];
    assert ls == pre + ([ls[e]] + post);
    NP.FlatMapSplit(pre, [ls[e]] + post, frest, Lplus);
    var R1: seq<LT.Leaf>, R23: seq<LT.Leaf> :| FM.FlatMapRel(pre, frest, R1) && FM.FlatMapRel([ls[e]] + post, frest, R23) && Lplus == R1 + R23;
    NP.FlatMapSplit([ls[e]], post, frest, R23);
    var R2: seq<LT.Leaf>, R3: seq<LT.Leaf> :| FM.FlatMapRel([ls[e]], frest, R2) && FM.FlatMapRel(post, frest, R3) && R23 == R2 + R3;
    NP.FlatMapSplit(pre, [ls[e]] + post, fchk, I);
    var I1: seq<LT.Leaf>, I23: seq<LT.Leaf> :| FM.FlatMapRel(pre, fchk, I1) && FM.FlatMapRel([ls[e]] + post, fchk, I23) && I == I1 + I23;
    NP.FlatMapSplit([ls[e]], post, fchk, I23);
    var I2: seq<LT.Leaf>, I3: seq<LT.Leaf> :| FM.FlatMapRel([ls[e]], fchk, I2) && FM.FlatMapRel(post, fchk, I3) && I23 == I2 + I3;
    assert frest(ls[e], R2) by {
      var ly, rst :| frest(([ls[e]])[0], ly) && FM.FlatMapRel(([ls[e]])[1..], frest, rst) && R2 == ly + rst;
      assert rst == [];
    }
    assert fchk(ls[e], I2) by {
      var ly, rst :| fchk(([ls[e]])[0], ly) && FM.FlatMapRel(([ls[e]])[1..], fchk, rst) && I2 == ly + rst;
      assert rst == [];
    }

    assert {:split_here} true;
    forall i, y | 0 <= i < |pre| && fchk(pre[i], y) ensures frest(pre[i], y) {
      assert pre[i] == ls[i] && ls[i].0 != inp;
      NP.ChkChunk(rer, rest, inp, ls[i], y);
    }
    NP.FlatMapEqOn(pre, frest, fchk, R1, I1);
    assert R1 == I1;
    NP.ChkChunk(rer, rest, inp, ls[e], I2);
    assert I2 == [];
    assert I2 + I3 == I3;
    assert I == I1 + I3;

    assert {:split_here} true;
    // ---- the empty leaf's rest chunk: EXACTLY I then the continuation from gmE ----
    NP.EmptyLeafChunk(rer, r1, cont, inp, ls[e], R2, titer, tcont, gm', gm);
    var C := LT.TreeLeaves(tcont, gmE, inp, WP.Forward);
    assert R2 == I + C;

    assert {:split_here} true;
    // ---- the engine shape's leaves ----
    var tcin := LT.Choice(LT.GroupActionT(LG.Reset(gidl), titer), LT.GroupActionT(LG.Reset(gidl), ChainLk(rer, s, inp, tcont)));
    var Lcin := LT.TreeLeaves(tcin, gm, inp, WP.Forward);
    assert Lcin == I + C by {
      assert LkStepsOk(rer, s, inp, LL.LkBodyGroups(r1));
      assert forall i :: 0 <= i < |s| && s[i].LkS? ==> EL.PikeLkRegexRec(s[i].b) && NP.LkVerdictL(rer, s[i].lk, s[i].b, inp);
      ChainLkLeaves(rer, s, tcont, gm', inp);
      assert LG.GMUpdate(LG.Reset(gidl), idx, gm) == gm';
      assert LT.TreeLeaves(LT.GroupActionT(LG.Reset(gidl), titer), gm, inp, WP.Forward) == I;
      assert LT.TreeLeaves(LT.GroupActionT(LG.Reset(gidl), ChainLk(rer, s, inp, tcont)), gm, inp, WP.Forward)
          == LT.TreeLeaves(ChainLk(rer, s, inp, tcont), gm', inp, WP.Forward);
      assert LT.TreeLeaves(ChainLk(rer, s, inp, tcont), gm', inp, WP.Forward) == C;
    }

    assert {:split_here} true;
    var rc := LT.TreeRes(tcin, gm, inp, WP.Forward);
    var rp := LT.TreeRes(tplus, gm, inp, WP.Forward);
    assert rc == LT.HdError(Lcin) && rp == LT.HdError(Lplus) by {
      LT.FirstTreeLeaf(tcin, gm, inp, WP.Forward);
      LT.FirstTreeLeaf(tplus, gm, inp, WP.Forward);
    }
    assert Lplus == I1 + ((I + C) + R3);
    if |I1| > 0 {
      assert Lplus[0] == I1[0] && Lcin[0] == I[0] == I1[0];
    } else {
      assert I == I3;
      assert Lplus == (I + C) + R3;
      if |I + C| > 0 {
        assert Lplus[0] == (I + C)[0];
      } else {
        assert |I3| == 0 && |C| == 0;
        assert {:split_here} true;
        NP.FlatMapEmptyChunks(post, fchk);
        forall i, y | 0 <= i < |post| && frest(post[i], y) ensures y == [] {
          var l := post[i];
          assert l == ls[e + 1 + i];
          if l.0 != inp {
            NP.ChkChunk(rer, rest, inp, l, y);
            assert fchk(l, y);
          } else {
            NP.EmptyLeafChunk(rer, r1, cont, inp, l, y, titer, tcont, gm', gm);
            NP.TreeLeavesLenIndep(titer, LG.GMReset(gidl, l.1), gm', inp);
            NP.TreeLeavesLenIndep(tcont, l.1, gmE, inp);
          }
        }
        NP.FlatMapAllEmpty(post, frest, R3);
        assert Lplus == [] && Lcin == [];
      }
    }
  }

  // ===========================================================================
  // 10. THE G4b SPEC LEMMA (assembled, at the nulled iteration of a CIN plus).
  //     `gm'` is the plus's reset map. The first leaf at `inp` of the body's tree
  //     (the leaf the spec's skip-to-continuation reads) is exactly the Lk-aware
  //     fold; outside the look groups it is the bare-gate fold (`NP.ApplyPath` of
  //     `NP.FirstEmptyPathL`); a crossed positive look's groups are its body's leaf
  //     at `inp` from `Empty`; every other look group is unset.
  // ===========================================================================

  lemma NulledIterationLeaf(rer: LW.RegExpRecord, r1: L.Regex, inp: LC.Input, gm: LG.GroupMap, t: LT.Tree)
    requires EL.PikeLkRegexRec(r1) && GUniq(r1)
    requires NP.FirstEmptyPathL(rer, r1, inp).Some?   // (G4b-2) CIN or CDN: the CIN premise weakened to its only use
    requires LS.IsTree(rer, [LS.Areg(r1)], inp, LG.GMReset(L.DefGroups(r1), gm), WP.Forward, t)
    ensures FirstEmptyPathLkL(rer, r1, inp).Some?
    ensures ProjO(FirstEmptyPathLkL(rer, r1, inp)) == NP.FirstEmptyPathL(rer, r1, inp)
    ensures var gm' := LG.GMReset(L.DefGroups(r1), gm);
            var s := FirstEmptyPathLkL(rer, r1, inp).value;
            var ls := LT.TreeLeaves(t, gm', inp, WP.Forward);
            NP.FirstAt(ls, inp).Some? && NP.FirstAt(ls, inp).value < |ls|
            && var gme := ls[NP.FirstAt(ls, inp).value].1;
               gme == ApplyPathLk(rer, s, inp, gm')
               && LL.GmAgreeOutside(gme, NP.ApplyPath(NP.FirstEmptyPathL(rer, r1, inp).value, LC.Idx(inp), gm'),
                                    LL.LkBodyGroups(r1))
               && LkLeafOk(rer, s, inp, gme)
               && (forall g :: g in LL.LkBodyGroups(r1) && !Crossed(s, g) ==> g !in gme)
  {
    var gidl := L.DefGroups(r1);
    var gm' := LG.GMReset(gidl, gm);
    var A := [LS.Areg(r1)];
    assert A == [LS.Areg(r1)] + [];
    assert NP.FirstEmptyPathA(rer, [], inp) == Some([]);
    assert NP.FirstEmptyPathA(rer, A, inp).Some?;
    ProjPath(rer, A, inp);
    EL.PikeLkActionsRecConsIff(LS.Areg(r1), []);
    EmptyLeavesLk(rer, A, inp, gm', t);
    var s := FirstEmptyPathLkL(rer, r1, inp).value;
    NulledLooks(rer, r1, inp, gm');
    StepsOkL(rer, r1, inp);
    LL.GmAgreeOutsideRefl(gm', LL.LkBodyGroups(r1));
    ApplyPathLkVsPlain(rer, s, inp, gm', gm', LL.LkBodyGroups(r1));
  }

  // ===========================================================================
  // 11. Machine B's walk glue needs no look-free premise: `CinWalkHead`'s step (3)
  //     runs rung A at `S = DefGroups(r1)` instead of `{}` and widens to `G`.
  // ===========================================================================

  lemma CinHeadStep3NoLookFree(rer: LW.RegExpRecord, r1: L.Regex, cont: LS.Actions, inp: LC.Input, b: BS.LoopBool,
                               t: LT.Tree, ti: LT.Tree, tcont: LT.Tree, G: set<LG.GroupId>)
    requires EL.PikeLkRegexRec(r1) && EL.PikeLkActionsRec(cont)
    requires NUL.CINullableL(r1)
    requires NB.EncOk(cont, inp, b)
    requires EL.BoolTreeLk(rer, [LS.Areg(L.Quantified(true, 1, LN.Inf, r1))] + cont, inp, b, t)
    requires EL.BoolTreeLk(rer, [LS.Areg(r1), LS.Acheck(inp), LS.Areg(L.Quantified(true, 0, LN.Inf, r1))] + cont, inp, BS.CannotExit, ti)
    requires EL.BoolTreeLk(rer, cont, inp, b, tcont)
    requires forall g :: g in L.DefGroups(r1) ==> g in G
    ensures NP.FirstEmptyPathL(rer, r1, inp).Some?
    ensures var gidl := L.DefGroups(r1);
            var p := NP.FirstEmptyPathL(rer, r1, inp).value;
            NP.ResAgreeAtOutside(LT.Choice(LT.GroupActionT(LG.Reset(gidl), ti),
                                           LT.GroupActionT(LG.Reset(gidl), NP.Chain(p, tcont))), t, inp, G)
  {
    LkBodyGroupsSubDG(r1);
    LL.LkBodyGroupsConfines(r1, DG(r1));
    NB.CinPlusPriorityBool(rer, r1, cont, inp, b, DG(r1), t, ti, tcont);
    var gidl := L.DefGroups(r1);
    var p := NP.FirstEmptyPathL(rer, r1, inp).value;
    RAMonoOutside(LT.Choice(LT.GroupActionT(LG.Reset(gidl), ti), LT.GroupActionT(LG.Reset(gidl), NP.Chain(p, tcont))),
                     t, inp, DG(r1), G);
  }

  // ===========================================================================
  // 12. WITNESS: `((?=(1:))|)`, i.e. r1 = (?=()) | ε. The bare-gate path is []
  //     (group 1 untouched), the spec's empty leaf DEFINES group 1 = [i, i].
  // ===========================================================================

  /** `ResAgreeAtOutside` is monotone in the set (moved down from `CW.RAMonoOutside`). */
  lemma RAMonoOutside(t1: LT.Tree, t2: LT.Tree, inp: LC.Input, S: set<LG.GroupId>, G: set<LG.GroupId>)
    requires S <= G
    requires NP.ResAgreeAtOutside(t1, t2, inp, S)
    ensures NP.ResAgreeAtOutside(t1, t2, inp, G)
  {
    forall gm: LG.GroupMap
      ensures var r1 := LT.TreeRes(t1, gm, inp, WP.Forward);
              var r2 := LT.TreeRes(t2, gm, inp, WP.Forward);
              (r1.Some? <==> r2.Some?)
              && (r1.Some? ==> r1.value.0 == r2.value.0 && LL.GmAgreeOutside(r1.value.1, r2.value.1, G))
    {
      var r1 := LT.TreeRes(t1, gm, inp, WP.Forward);
      var r2 := LT.TreeRes(t2, gm, inp, WP.Forward);
      if r1.Some? {
        assert LL.GmAgreeOutside(r1.value.1, r2.value.1, S);
      }
    }
  }

  // ===========================================================================
  // 12. (G4b-1, W20) Rung A on TODAY's bare chain: when every look the nulled iteration crosses has a
  //     group-free body, the look-carrying chain and the bare chain have the same leaves, so W15's exact
  //     rung A holds with `Reset(gidl); Chain(p, tcont)` and EQUALITY of first results.
  // ===========================================================================
  /** Every crossed look step has a group-free body. */
  ghost predicate CrossedGroupFree(s: seq<Step>) {
    forall i :: 0 <= i < |s| && s[i].LkS? ==> DG(s[i].b) == {}
  }

  lemma AgreeEmptyEq(a: LG.GroupMap, b: LG.GroupMap)
    requires LL.GmAgreeOutside(a, b, {})
    ensures a == b
  {
    assert a.Keys == b.Keys;
    forall g | g in a ensures a[g] == b[g] {}
  }

  /** The look-carrying chain and the bare chain have the same leaves when the crossed bodies capture nothing. */
  lemma ChainLkGroupFreeLeaves(rer: LW.RegExpRecord, s: seq<Step>, t: LT.Tree, gm: LG.GroupMap, inp: LC.Input)
    requires forall i :: 0 <= i < |s| && s[i].LkS? ==> EL.PikeLkRegexRec(s[i].b) && NP.LkVerdictL(rer, s[i].lk, s[i].b, inp)
    requires CrossedGroupFree(s)
    ensures LT.TreeLeaves(ChainLk(rer, s, inp, t), gm, inp, WP.Forward)
         == LT.TreeLeaves(NP.Chain(Proj(s), t), gm, inp, WP.Forward)
  {
    ChainLkLeaves(rer, s, t, gm, inp);
    NP.ChainLeaves(Proj(s), t, gm, inp);
    LL.GmAgreeOutsideRefl(gm, {});
    ApplyPathLkVsPlain(rer, s, inp, gm, gm, {});
    AgreeEmptyEq(ApplyPathLk(rer, s, inp, gm), NP.ApplyPath(Proj(s), LC.Idx(inp), gm));
  }

  /** G4b-1's rung A: exact, with the bare chain. */
  lemma CinPlusPriorityGroupFreeCrossed(rer: LW.RegExpRecord, r1: L.Regex, cont: LS.Actions, inp: LC.Input,
                                        gm: LG.GroupMap, tplus: LT.Tree, titer: LT.Tree, tcont: LT.Tree)
    requires EL.PikeLkRegexRec(r1) && EL.PikeLkActionsRec(cont)
    requires NUL.CINullableL(r1)
    requires LS.IsTree(rer, [LS.Areg(L.Quantified(true, 1, LN.Inf, r1))] + cont, inp, gm, WP.Forward, tplus)
    requires LS.IsTree(rer, [LS.Areg(r1), LS.Acheck(inp), LS.Areg(L.Quantified(true, 0, LN.Inf, r1))] + cont,
                       inp, LG.GMReset(L.DefGroups(r1), gm), WP.Forward, titer)
    requires LS.IsTree(rer, cont, inp, gm, WP.Forward, tcont)
    requires FirstEmptyPathLkL(rer, r1, inp).Some? ==> CrossedGroupFree(FirstEmptyPathLkL(rer, r1, inp).value)
    ensures NP.FirstEmptyPathL(rer, r1, inp).Some?
    ensures var gidl := L.DefGroups(r1);
            var p := NP.FirstEmptyPathL(rer, r1, inp).value;
            var tcin := LT.Choice(LT.GroupActionT(LG.Reset(gidl), titer),
                                  LT.GroupActionT(LG.Reset(gidl), NP.Chain(p, tcont)));
            LT.TreeRes(tcin, gm, inp, WP.Forward) == LT.TreeRes(tplus, gm, inp, WP.Forward)
  {
    var gidl := L.DefGroups(r1);
    var gm' := LG.GMReset(gidl, gm);
    CinPlusPriorityLk(rer, r1, cont, inp, gm, tplus, titer, tcont);
    var s := FirstEmptyPathLkL(rer, r1, inp).value;
    ProjPath(rer, [LS.Areg(r1)], inp);
    assert Proj(s) == NP.FirstEmptyPathL(rer, r1, inp).value;
    StepsOkL(rer, r1, inp);
    assert forall i :: 0 <= i < |s| && s[i].LkS? ==> EL.PikeLkRegexRec(s[i].b) && NP.LkVerdictL(rer, s[i].lk, s[i].b, inp);
    ChainLkGroupFreeLeaves(rer, s, tcont, gm', inp);
    var tlk := LT.Choice(LT.GroupActionT(LG.Reset(gidl), titer), LT.GroupActionT(LG.Reset(gidl), ChainLk(rer, s, inp, tcont)));
    var tcin := LT.Choice(LT.GroupActionT(LG.Reset(gidl), titer), LT.GroupActionT(LG.Reset(gidl), NP.Chain(Proj(s), tcont)));
    assert LT.TreeLeaves(tlk, gm, inp, WP.Forward) == LT.TreeLeaves(tcin, gm, inp, WP.Forward);
    LT.FirstTreeLeaf(tlk, gm, inp, WP.Forward);
    LT.FirstTreeLeaf(tcin, gm, inp, WP.Forward);
  }

  // ===========================================================================
  // 13. (G4b-1) The static scope: every lookaround that an empty path of a body can cross has a
  //     group-free body. Context-free: a sequence's half lies on an empty path only when the other half
  //     is not `NonNullableL`; a `{0,…}` quantifier is skipped; a look's own body is read as a whole.
  // ===========================================================================

  ghost predicate EmptyLooksGroupFreeL(r: L.Regex)
    decreases r
  {
    match r
    case Disjunction(r1, r2) => EmptyLooksGroupFreeL(r1) && EmptyLooksGroupFreeL(r2)
    case Sequence(r1, r2) =>
      (!NUL.NonNullableL(r2) ==> EmptyLooksGroupFreeL(r1)) && (!NUL.NonNullableL(r1) ==> EmptyLooksGroupFreeL(r2))
    case Quantified(_, min, _, r1) => min == 0 || EmptyLooksGroupFreeL(r1)
    case Group(_, r1) => EmptyLooksGroupFreeL(r1)
    case LookaroundR(_, b) => DG(b) == {}
    case _ => true
  }

  /** A regex with an empty path is not `NonNullableL`. */
  lemma EmptyPathNotNonNullable(rer: LW.RegExpRecord, r: L.Regex, inp: LC.Input)
    requires FirstEmptyPathLkL(rer, r, inp).Some?
    ensures !NUL.NonNullableL(r)
    decreases NT.RSizeL(r), NT.MinOfL(r)
  {
    var solo := [LS.Areg(r)];
    assert solo[0] == LS.Areg(r) && solo[1..] == [];
    assert FirstEmptyPathLkA(rer, [], inp) == Some([]);
    match r
    case Character(_) => assert FirstEmptyPathLkL(rer, r, inp) == None;
    case Disjunction(r1, r2) =>
      assert [LS.Areg(r1)] + [] == [LS.Areg(r1)] && [LS.Areg(r2)] + [] == [LS.Areg(r2)];
      var p1 := FirstEmptyPathLkL(rer, r1, inp);
      assert FirstEmptyPathLkL(rer, r, inp) == (match p1 case Some(p) => Some(p) case None => FirstEmptyPathLkL(rer, r2, inp));
      if p1.Some? { EmptyPathNotNonNullable(rer, r1, inp); } else { EmptyPathNotNonNullable(rer, r2, inp); }
    case Sequence(r1, r2) =>
      assert [LS.Areg(r1), LS.Areg(r2)] + [] == [LS.Areg(r1)] + [LS.Areg(r2)];
      assert [LS.Areg(r2)] + [] == [LS.Areg(r2)];
      FirstEmptyPathLkAComp(rer, r1, [LS.Areg(r2)], inp);
      assert FirstEmptyPathLkL(rer, r, inp) == FirstEmptyPathLkA(rer, [LS.Areg(r1), LS.Areg(r2)] + [], inp);
      assert FirstEmptyPathLkA(rer, [LS.Areg(r2)], inp) == FirstEmptyPathLkL(rer, r2, inp);
      EmptyPathNotNonNullable(rer, r1, inp);
      EmptyPathNotNonNullable(rer, r2, inp);
    case Group(gid, r1) =>
      assert [LS.Areg(r1), LS.Aclose(gid)] + [] == [LS.Areg(r1)] + [LS.Aclose(gid)];
      FirstEmptyPathLkAComp(rer, r1, [LS.Aclose(gid)], inp);
      EmptyPathNotNonNullable(rer, r1, inp);
    case Quantified(greedy, min, delta, r1) =>
      if min > 0 {
        var qn := L.Quantified(greedy, min - 1, delta, r1);
        if EL.CinHeadL(greedy, min, delta, r1) { EL.CinHeadMono(greedy, min, delta, r1, min - 1, delta); }
        assert NT.RSizeL(qn) == NT.RSizeL(r) && NT.MinOfL(qn) < NT.MinOfL(r);
        assert [LS.Areg(r1), LS.Areg(qn)] + [] == [LS.Areg(r1)] + [LS.Areg(qn)];
        FirstEmptyPathLkAComp(rer, r1, [LS.Areg(qn)], inp);
        EmptyPathNotNonNullable(rer, r1, inp);
      }
    case _ =>
  }

  /** (G4b-1) Under the static scope, every look the first empty path crosses has a group-free body. */
  lemma CrossedGroupFreeOfScope(rer: LW.RegExpRecord, r: L.Regex, inp: LC.Input)
    requires EmptyLooksGroupFreeL(r)
    requires FirstEmptyPathLkL(rer, r, inp).Some?
    ensures CrossedGroupFree(FirstEmptyPathLkL(rer, r, inp).value)
    decreases NT.RSizeL(r), NT.MinOfL(r)
  {
    var s := FirstEmptyPathLkL(rer, r, inp).value;
    var solo := [LS.Areg(r)];
    assert solo[0] == LS.Areg(r) && solo[1..] == [];
    assert FirstEmptyPathLkA(rer, [], inp) == Some([]);
    match r
    case Epsilon => assert s == [];
    case Character(_) =>
    case Backreference(_) =>
    case AnchorR(a) => assert s == [];
    case LookaroundR(lk, b) =>
      assert [LkS(lk, b)] + [] == [LkS(lk, b)];
      assert s == [LkS(lk, b)];
    case Disjunction(r1, r2) =>
      assert [LS.Areg(r1)] + [] == [LS.Areg(r1)] && [LS.Areg(r2)] + [] == [LS.Areg(r2)];
      var p1 := FirstEmptyPathLkL(rer, r1, inp);
      assert FirstEmptyPathLkL(rer, r, inp) == (match p1 case Some(p) => Some(p) case None => FirstEmptyPathLkL(rer, r2, inp));
      if p1.Some? { CrossedGroupFreeOfScope(rer, r1, inp); } else { CrossedGroupFreeOfScope(rer, r2, inp); }
    case Sequence(r1, r2) =>
      assert [LS.Areg(r1), LS.Areg(r2)] + [] == [LS.Areg(r1)] + [LS.Areg(r2)];
      assert [LS.Areg(r2)] + [] == [LS.Areg(r2)];
      FirstEmptyPathLkAComp(rer, r1, [LS.Areg(r2)], inp);
      assert FirstEmptyPathLkL(rer, r, inp) == FirstEmptyPathLkA(rer, [LS.Areg(r1), LS.Areg(r2)] + [], inp);
      assert FirstEmptyPathLkA(rer, [LS.Areg(r2)], inp) == FirstEmptyPathLkL(rer, r2, inp);
      EmptyPathNotNonNullable(rer, r1, inp);
      EmptyPathNotNonNullable(rer, r2, inp);
      CrossedGroupFreeOfScope(rer, r1, inp);
      CrossedGroupFreeOfScope(rer, r2, inp);
      var s1 := FirstEmptyPathLkL(rer, r1, inp).value;
      var s2 := FirstEmptyPathLkL(rer, r2, inp).value;
      assert s == s1 + s2;
      forall i | 0 <= i < |s| && s[i].LkS? ensures DG(s[i].b) == {} {
        if i < |s1| { assert s[i] == s1[i]; } else { assert s[i] == s2[i - |s1|]; }
      }
    case Group(gid, r1) =>
      assert [LS.Areg(r1), LS.Aclose(gid)] + [] == [LS.Areg(r1)] + [LS.Aclose(gid)];
      assert [LS.Aclose(gid)][0] == LS.Aclose(gid) && [LS.Aclose(gid)][1..] == [];
      assert [GA(LG.Close(gid))] + [] == [GA(LG.Close(gid))];
      assert FirstEmptyPathLkA(rer, [LS.Aclose(gid)], inp) == Some([GA(LG.Close(gid))]);
      FirstEmptyPathLkAComp(rer, r1, [LS.Aclose(gid)], inp);
      var s1 := FirstEmptyPathLkL(rer, r1, inp).value;
      assert s == [GA(LG.Open(gid))] + (s1 + [GA(LG.Close(gid))]);
      CrossedGroupFreeOfScope(rer, r1, inp);
      forall i | 0 <= i < |s| && s[i].LkS? ensures DG(s[i].b) == {} {
        assert 1 <= i <= |s1|;
        assert s[i] == s1[i - 1];
      }
    case Quantified(greedy, min, delta, r1) =>
      if min == 0 {
        assert s == [];
      } else {
        var gidl := L.DefGroups(r1);
        var qn := L.Quantified(greedy, min - 1, delta, r1);
        if EL.CinHeadL(greedy, min, delta, r1) { EL.CinHeadMono(greedy, min, delta, r1, min - 1, delta); }
        assert NT.RSizeL(qn) == NT.RSizeL(r) && NT.MinOfL(qn) < NT.MinOfL(r);
        assert [LS.Areg(r1), LS.Areg(qn)] + [] == [LS.Areg(r1)] + [LS.Areg(qn)];
        assert [LS.Areg(qn)] + [] == [LS.Areg(qn)];
        FirstEmptyPathLkAComp(rer, r1, [LS.Areg(qn)], inp);
        assert FirstEmptyPathLkA(rer, [LS.Areg(qn)], inp) == FirstEmptyPathLkL(rer, qn, inp);
        var s1 := FirstEmptyPathLkL(rer, r1, inp).value;
        var sn := FirstEmptyPathLkL(rer, qn, inp).value;
        assert s == [GA(LG.Reset(gidl))] + (s1 + sn);
        CrossedGroupFreeOfScope(rer, r1, inp);
        CrossedGroupFreeOfScope(rer, qn, inp);
        forall i | 0 <= i < |s| && s[i].LkS? ensures DG(s[i].b) == {} {
          assert 1 <= i;
          if i - 1 < |s1| { assert s[i] == s1[i - 1]; } else { assert s[i] == sn[i - 1 - |s1|]; }
        }
      }
  }

  // ===========================================================================
  // 14. (G4b-1) The CDN twins and machine B's Bool-tree rung A without `LkBodiesInS(r1, {})`
  // ===========================================================================

  lemma CdnPlusPriorityLkSome(rer: LW.RegExpRecord, r1: L.Regex, cont: LS.Actions, inp: LC.Input, gm: LG.GroupMap,
                          tplus: LT.Tree, titer: LT.Tree, tcont: LT.Tree)
    requires EL.PikeLkRegexRec(r1) && EL.PikeLkActionsRec(cont)
    requires NP.FirstEmptyPathL(rer, r1, inp).Some?   // (G4b-1) the CIN premise weakened to its only use
    requires LS.IsTree(rer, [LS.Areg(L.Quantified(true, 1, LN.Inf, r1))] + cont, inp, gm, WP.Forward, tplus)
    requires LS.IsTree(rer, [LS.Areg(r1), LS.Acheck(inp), LS.Areg(L.Quantified(true, 0, LN.Inf, r1))] + cont,
                       inp, LG.GMReset(L.DefGroups(r1), gm), WP.Forward, titer)
    requires LS.IsTree(rer, cont, inp, gm, WP.Forward, tcont)
    ensures FirstEmptyPathLkL(rer, r1, inp).Some?
    ensures ProjO(FirstEmptyPathLkL(rer, r1, inp)) == NP.FirstEmptyPathL(rer, r1, inp)
    ensures var gidl := L.DefGroups(r1);
            var s := FirstEmptyPathLkL(rer, r1, inp).value;
            var tcin := LT.Choice(LT.GroupActionT(LG.Reset(gidl), titer),
                                  LT.GroupActionT(LG.Reset(gidl), ChainLk(rer, s, inp, tcont)));
            LT.TreeRes(tcin, gm, inp, WP.Forward) == LT.TreeRes(tplus, gm, inp, WP.Forward)
  {
    var gidl := L.DefGroups(r1);
    var Gset := set g | g in gidl;
    var gm' := LG.GMReset(gidl, gm);
    var idx := LC.Idx(inp);
    var Q1 := L.Quantified(true, 1, LN.Inf, r1);
    var Q0 := L.Quantified(true, 0, LN.Inf, r1);
    EL.CinHeadIntro(true, 0, LN.Inf, r1);   // (W20) G5a atom
    var A := [LS.Areg(r1)];
    var rest := [LS.Areg(Q0)] + cont;
    var chk := [LS.Acheck(inp)] + rest;
    var iterActs := [LS.Areg(r1), LS.Acheck(inp), LS.Areg(Q0)] + cont;
    assert iterActs == A + chk;
    var plusActs := [LS.Areg(Q1)] + cont;
    assert plusActs[0] == LS.Areg(Q1) && plusActs[1..] == cont;

    // ---- the spec tree: Reset; tc with tc the tree of A + rest at gm' ----
    assert tplus.GroupActionT? && tplus.g == LG.Reset(gidl);
    var tc := tplus.t;
    assert LS.IsTree(rer, [LS.Areg(r1), LS.Areg(L.Quantified(true, 0, LN.Inf, r1))] + cont, inp, gm', WP.Forward, tc);
    assert [LS.Areg(r1), LS.Areg(Q0)] + cont == A + rest;
    var Lplus := LT.TreeLeaves(tc, gm', inp, WP.Forward);
    assert LT.TreeLeaves(tplus, gm, inp, WP.Forward) == Lplus;

    assert {:split_here} true;
    EL.PikeLkActionsRecConsIff(LS.Areg(r1), []);
    assert EL.PikeLkActionsRec(A);
    EL.PikeLkActionsRecConsIff(LS.Areg(Q0), cont);
    assert EL.PikeLkActionsRec(rest);

    // ---- the Lk-carrying first empty path of r1, and its fold ----
    assert A == [LS.Areg(r1)] + [];
    assert NP.FirstEmptyPathA(rer, A, inp).Some?;
    ProjPath(rer, A, inp);
    var s := FirstEmptyPathLkL(rer, r1, inp).value;
    var gmE := ApplyPathLk(rer, s, inp, gm');
    assert NP.ActsGroupsIn(A, Gset) by {
      forall i | 0 <= i < |A| ensures (A[i].Areg? ==> forall g :: g in L.DefGroups(A[i].r) ==> g in Gset) && (A[i].Aclose? ==> A[i].gid in Gset) {}
    }
    NP.PathActionsIn(rer, A, inp, Gset);
    assert Proj(s) == NP.FirstEmptyPathA(rer, A, inp).value;
    StepsOkL(rer, r1, inp);
    LkBodyGroupsSubDG(r1);
    assert DG(r1) == Gset;
    ApplyPathLkOutside(rer, s, inp, gm', Gset);
    NP.GMResetAgree(gidl, gmE, gm');
    assert LG.GMReset(gidl, gm') == gm';
    assert LG.GMReset(gidl, gmE) == gm';

    assert {:split_here} true;
    // ---- r1's own tree: its first empty leaf IS gmE ----
    var tr1 := FU.ComputeTr(rer, A, inp, gm', WP.Forward);
    FU.ComputeTrIsTree(rer, A, inp, gm', WP.Forward);
    var ls := LT.TreeLeaves(tr1, gm', inp, WP.Forward);
    EmptyLeavesLk(rer, A, inp, gm', tr1);
    NP.FirstAtSpec(ls, inp);
    var e := NP.FirstAt(ls, inp).value;
    var gme := ls[e].1;
    assert gme == gmE;

    assert {:split_here} true;
    // ---- the two flat-maps over r1's leaves ----
    var frest := EQ.ActFromLeafFn(rer, rest, WP.Forward);
    var fchk := EQ.ActFromLeafFn(rer, chk, WP.Forward);
    EQ.ActFromLeafDeterm(rer, WP.Forward, rest);
    EQ.ActFromLeafDeterm(rer, WP.Forward, chk);
    EQ.LeavesConcat(rer, inp, gm', WP.Forward, A, rest, tc, tr1);
    assert FM.FlatMapRel(ls, frest, Lplus);
    var I := LT.TreeLeaves(titer, gm', inp, WP.Forward);
    EQ.LeavesConcat(rer, inp, gm', WP.Forward, A, chk, titer, tr1);
    assert FM.FlatMapRel(ls, fchk, I);

    assert {:split_here} true;
    var pre := ls[..e];
    var post := ls[e + 1..];
    assert ls == pre + ([ls[e]] + post);
    NP.FlatMapSplit(pre, [ls[e]] + post, frest, Lplus);
    var R1: seq<LT.Leaf>, R23: seq<LT.Leaf> :| FM.FlatMapRel(pre, frest, R1) && FM.FlatMapRel([ls[e]] + post, frest, R23) && Lplus == R1 + R23;
    NP.FlatMapSplit([ls[e]], post, frest, R23);
    var R2: seq<LT.Leaf>, R3: seq<LT.Leaf> :| FM.FlatMapRel([ls[e]], frest, R2) && FM.FlatMapRel(post, frest, R3) && R23 == R2 + R3;
    NP.FlatMapSplit(pre, [ls[e]] + post, fchk, I);
    var I1: seq<LT.Leaf>, I23: seq<LT.Leaf> :| FM.FlatMapRel(pre, fchk, I1) && FM.FlatMapRel([ls[e]] + post, fchk, I23) && I == I1 + I23;
    NP.FlatMapSplit([ls[e]], post, fchk, I23);
    var I2: seq<LT.Leaf>, I3: seq<LT.Leaf> :| FM.FlatMapRel([ls[e]], fchk, I2) && FM.FlatMapRel(post, fchk, I3) && I23 == I2 + I3;
    assert frest(ls[e], R2) by {
      var ly, rst :| frest(([ls[e]])[0], ly) && FM.FlatMapRel(([ls[e]])[1..], frest, rst) && R2 == ly + rst;
      assert rst == [];
    }
    assert fchk(ls[e], I2) by {
      var ly, rst :| fchk(([ls[e]])[0], ly) && FM.FlatMapRel(([ls[e]])[1..], fchk, rst) && I2 == ly + rst;
      assert rst == [];
    }

    assert {:split_here} true;
    forall i, y | 0 <= i < |pre| && fchk(pre[i], y) ensures frest(pre[i], y) {
      assert pre[i] == ls[i] && ls[i].0 != inp;
      NP.ChkChunk(rer, rest, inp, ls[i], y);
    }
    NP.FlatMapEqOn(pre, frest, fchk, R1, I1);
    assert R1 == I1;
    NP.ChkChunk(rer, rest, inp, ls[e], I2);
    assert I2 == [];
    assert I2 + I3 == I3;
    assert I == I1 + I3;

    assert {:split_here} true;
    // ---- the empty leaf's rest chunk: EXACTLY I then the continuation from gmE ----
    NP.EmptyLeafChunk(rer, r1, cont, inp, ls[e], R2, titer, tcont, gm', gm);
    var C := LT.TreeLeaves(tcont, gmE, inp, WP.Forward);
    assert R2 == I + C;

    assert {:split_here} true;
    // ---- the engine shape's leaves ----
    var tcin := LT.Choice(LT.GroupActionT(LG.Reset(gidl), titer), LT.GroupActionT(LG.Reset(gidl), ChainLk(rer, s, inp, tcont)));
    var Lcin := LT.TreeLeaves(tcin, gm, inp, WP.Forward);
    assert Lcin == I + C by {
      assert LkStepsOk(rer, s, inp, LL.LkBodyGroups(r1));
      assert forall i :: 0 <= i < |s| && s[i].LkS? ==> EL.PikeLkRegexRec(s[i].b) && NP.LkVerdictL(rer, s[i].lk, s[i].b, inp);
      ChainLkLeaves(rer, s, tcont, gm', inp);
      assert LG.GMUpdate(LG.Reset(gidl), idx, gm) == gm';
      assert LT.TreeLeaves(LT.GroupActionT(LG.Reset(gidl), titer), gm, inp, WP.Forward) == I;
      assert LT.TreeLeaves(LT.GroupActionT(LG.Reset(gidl), ChainLk(rer, s, inp, tcont)), gm, inp, WP.Forward)
          == LT.TreeLeaves(ChainLk(rer, s, inp, tcont), gm', inp, WP.Forward);
      assert LT.TreeLeaves(ChainLk(rer, s, inp, tcont), gm', inp, WP.Forward) == C;
    }

    assert {:split_here} true;
    var rc := LT.TreeRes(tcin, gm, inp, WP.Forward);
    var rp := LT.TreeRes(tplus, gm, inp, WP.Forward);
    assert rc == LT.HdError(Lcin) && rp == LT.HdError(Lplus) by {
      LT.FirstTreeLeaf(tcin, gm, inp, WP.Forward);
      LT.FirstTreeLeaf(tplus, gm, inp, WP.Forward);
    }
    assert Lplus == I1 + ((I + C) + R3);
    if |I1| > 0 {
      assert Lplus[0] == I1[0] && Lcin[0] == I[0] == I1[0];
    } else {
      assert I == I3;
      assert Lplus == (I + C) + R3;
      if |I + C| > 0 {
        assert Lplus[0] == (I + C)[0];
      } else {
        assert |I3| == 0 && |C| == 0;
        assert {:split_here} true;
        NP.FlatMapEmptyChunks(post, fchk);
        forall i, y | 0 <= i < |post| && frest(post[i], y) ensures y == [] {
          var l := post[i];
          assert l == ls[e + 1 + i];
          if l.0 != inp {
            NP.ChkChunk(rer, rest, inp, l, y);
            assert fchk(l, y);
          } else {
            NP.EmptyLeafChunk(rer, r1, cont, inp, l, y, titer, tcont, gm', gm);
            NP.TreeLeavesLenIndep(titer, LG.GMReset(gidl, l.1), gm', inp);
            NP.TreeLeavesLenIndep(tcont, l.1, gmE, inp);
          }
        }
        NP.FlatMapAllEmpty(post, frest, R3);
        assert Lplus == [] && Lcin == [];
      }
    }
  }

  /** (G4b-1) The CDN twin: a guarded plus whose guard passes at `inp`. */
  lemma CdnPlusPriorityGroupFreeCrossed(rer: LW.RegExpRecord, r1: L.Regex, cont: LS.Actions, inp: LC.Input,
                                        gm: LG.GroupMap, tplus: LT.Tree, titer: LT.Tree, tcont: LT.Tree)
    requires EL.PikeLkRegexRec(r1) && EL.PikeLkActionsRec(cont)
    requires NP.FirstEmptyPathL(rer, r1, inp).Some?
    requires LS.IsTree(rer, [LS.Areg(L.Quantified(true, 1, LN.Inf, r1))] + cont, inp, gm, WP.Forward, tplus)
    requires LS.IsTree(rer, [LS.Areg(r1), LS.Acheck(inp), LS.Areg(L.Quantified(true, 0, LN.Inf, r1))] + cont,
                       inp, LG.GMReset(L.DefGroups(r1), gm), WP.Forward, titer)
    requires LS.IsTree(rer, cont, inp, gm, WP.Forward, tcont)
    requires FirstEmptyPathLkL(rer, r1, inp).Some? ==> CrossedGroupFree(FirstEmptyPathLkL(rer, r1, inp).value)
    ensures NP.FirstEmptyPathL(rer, r1, inp).Some?
    ensures var gidl := L.DefGroups(r1);
            var p := NP.FirstEmptyPathL(rer, r1, inp).value;
            var tcin := LT.Choice(LT.GroupActionT(LG.Reset(gidl), titer),
                                  LT.GroupActionT(LG.Reset(gidl), NP.Chain(p, tcont)));
            LT.TreeRes(tcin, gm, inp, WP.Forward) == LT.TreeRes(tplus, gm, inp, WP.Forward)
  {
    var gidl := L.DefGroups(r1);
    var gm' := LG.GMReset(gidl, gm);
    CdnPlusPriorityLkSome(rer, r1, cont, inp, gm, tplus, titer, tcont);
    var s := FirstEmptyPathLkL(rer, r1, inp).value;
    ProjPath(rer, [LS.Areg(r1)], inp);
    assert Proj(s) == NP.FirstEmptyPathL(rer, r1, inp).value;
    StepsOkL(rer, r1, inp);
    assert forall i :: 0 <= i < |s| && s[i].LkS? ==> EL.PikeLkRegexRec(s[i].b) && NP.LkVerdictL(rer, s[i].lk, s[i].b, inp);
    ChainLkGroupFreeLeaves(rer, s, tcont, gm', inp);
    var tlk := LT.Choice(LT.GroupActionT(LG.Reset(gidl), titer), LT.GroupActionT(LG.Reset(gidl), ChainLk(rer, s, inp, tcont)));
    var tcin := LT.Choice(LT.GroupActionT(LG.Reset(gidl), titer), LT.GroupActionT(LG.Reset(gidl), NP.Chain(Proj(s), tcont)));
    assert LT.TreeLeaves(tlk, gm, inp, WP.Forward) == LT.TreeLeaves(tcin, gm, inp, WP.Forward);
    LT.FirstTreeLeaf(tlk, gm, inp, WP.Forward);
    LT.FirstTreeLeaf(tcin, gm, inp, WP.Forward);
  }

  /** (G4b-1) `CDP.CdnPlusPriorityBool` at `S = {}` WITHOUT `LkBodiesInS(r1, {})`: under the static scope the
      looks the guard's empty path crosses are group-free, so rung A is exact on the engine's chained shape. */
  lemma CdnPlusPriorityBoolGF(rer: LW.RegExpRecord, r1: L.Regex, cont: LS.Actions, inp: LC.Input, b: BS.LoopBool,
                              t: LT.Tree, ti: LT.Tree, tcont: LT.Tree)
    requires EL.PikeLkRegexRec(r1) && EL.PikeLkActionsRec(cont)
    requires EL.CinHeadL(true, 1, LN.Inf, r1)
    requires EmptyLooksGroupFreeL(r1)
    requires NP.FirstEmptyPathL(rer, r1, inp).Some?
    requires NB.EncOk(cont, inp, b)
    requires EL.BoolTreeLk(rer, [LS.Areg(L.Quantified(true, 1, LN.Inf, r1))] + cont, inp, b, t)
    requires EL.BoolTreeLk(rer, [LS.Areg(r1), LS.Acheck(inp), LS.Areg(L.Quantified(true, 0, LN.Inf, r1))] + cont, inp, BS.CannotExit, ti)
    requires EL.BoolTreeLk(rer, cont, inp, b, tcont)
    ensures NP.ResAgreeAtOutside(CDP.CdnTree(rer, r1, inp, ti, tcont), t, inp, {})
  {
    var gidl := L.DefGroups(r1);
    var plus := L.Quantified(true, 1, LN.Inf, r1);
    var star := L.Quantified(true, 0, LN.Inf, r1);
    EL.PikeLkRecQuantZero(true, LN.Inf, r1);
    var pacts := [LS.Areg(plus)] + cont;
    var ia := [LS.Areg(r1), LS.Acheck(inp), LS.Areg(star)] + cont;
    assert EL.PikeLkRegexRec(plus) && EL.PikeLkRegexRec(star);
    assert EL.PikeLkActionRec(LS.Areg(plus)) && EL.PikeLkActionRec(LS.Areg(star))
        && EL.PikeLkActionRec(LS.Areg(r1)) && EL.PikeLkActionRec(LS.Acheck(inp));
    EL.PikeLkActionsRecConsIff(LS.Areg(plus), cont);
    EL.PikeLkActionsRecConsIff(LS.Areg(star), cont);
    EL.PikeLkActionsRecConsIff(LS.Acheck(inp), [LS.Areg(star)] + cont);
    EL.PikeLkActionsRecConsIff(LS.Areg(r1), [LS.Acheck(inp)] + ([LS.Areg(star)] + cont));
    assert ia == [LS.Areg(r1)] + ([LS.Acheck(inp)] + ([LS.Areg(star)] + cont));
    assert EL.PikeLkActionsRec(pacts) && EL.PikeLkActionsRec(ia);
    NB.EncOkConsPlus(plus, cont, inp, b);
    NB.EncOkEncodable(cont, inp, b);
    NB.EncOkIter(r1, star, cont, inp);
    ProjPath(rer, [LS.Areg(r1)], inp);
    CrossedGroupFreeOfScope(rer, r1, inp);
    assert {:split_here} true;
    var tcdn := CDP.CdnTree(rer, r1, inp, ti, tcont);
    assert tcdn == LT.Choice(LT.GroupActionT(LG.Reset(gidl), ti),
                             LT.GroupActionT(LG.Reset(gidl), NP.Chain(NP.FirstEmptyPathL(rer, r1, inp).value, tcont)));
    forall gm: LG.GroupMap
      ensures var rc := LT.TreeRes(tcdn, gm, inp, WP.Forward);
              var rp := LT.TreeRes(t, gm, inp, WP.Forward);
              (rc.Some? <==> rp.Some?)
              && (rc.Some? ==> rc.value.0 == rp.value.0 && LL.GmAgreeOutside(rc.value.1, rp.value.1, {}))
    {
      NB.EncTreeIsTree(rer, pacts, inp, b, t, gm);
      NB.EncTreeIsTree(rer, ia, inp, BS.CannotExit, ti, LG.GMReset(gidl, gm));
      NB.EncTreeIsTree(rer, cont, inp, b, tcont, gm);
      CdnPlusPriorityGroupFreeCrossed(rer, r1, cont, inp, gm, t, ti, tcont);
      var rp := LT.TreeRes(t, gm, inp, WP.Forward);
      if rp.Some? { LL.GmAgreeOutsideRefl(rp.value.1, {}); }
    }
  }

  /** (G4b-1) `CDP.CdnPlusPriorityBoolNone` at `S = {}` WITHOUT `LkBodiesInS(r1, {})`: the None case is exact, so
      it runs at `S = DG(r1)` (which every regex satisfies) and is read off with no slack. */
  lemma CdnPlusPriorityBoolNoneExact(rer: LW.RegExpRecord, r1: L.Regex, cont: LS.Actions, inp: LC.Input, b: BS.LoopBool,
                                     t: LT.Tree, ti: LT.Tree)
    requires EL.PikeLkRegexRec(r1) && EL.PikeLkActionsRec(cont)
    requires EL.CinHeadL(true, 1, LN.Inf, r1)
    requires NB.EncOk(cont, inp, b)
    requires NP.FirstEmptyPathL(rer, r1, inp).None?
    requires EL.BoolTreeLk(rer, [LS.Areg(L.Quantified(true, 1, LN.Inf, r1))] + cont, inp, b, t)
    requires EL.BoolTreeLk(rer, [LS.Areg(r1), LS.Acheck(inp), LS.Areg(L.Quantified(true, 0, LN.Inf, r1))] + cont, inp, BS.CannotExit, ti)
    ensures NP.ResAgreeAtOutside(CDP.CdnDeadTree(L.DefGroups(r1), ti), t, inp, {})
  {
    var gidl := L.DefGroups(r1);
    var plus := L.Quantified(true, 1, LN.Inf, r1);
    var star := L.Quantified(true, 0, LN.Inf, r1);
    EL.PikeLkRecQuantZero(true, LN.Inf, r1);
    var pacts := [LS.Areg(plus)] + cont;
    var ia := [LS.Areg(r1), LS.Acheck(inp), LS.Areg(star)] + cont;
    assert EL.PikeLkRegexRec(plus) && EL.PikeLkRegexRec(star);
    assert EL.PikeLkActionRec(LS.Areg(plus)) && EL.PikeLkActionRec(LS.Areg(star))
        && EL.PikeLkActionRec(LS.Areg(r1)) && EL.PikeLkActionRec(LS.Acheck(inp));
    EL.PikeLkActionsRecConsIff(LS.Areg(plus), cont);
    EL.PikeLkActionsRecConsIff(LS.Areg(star), cont);
    EL.PikeLkActionsRecConsIff(LS.Acheck(inp), [LS.Areg(star)] + cont);
    EL.PikeLkActionsRecConsIff(LS.Areg(r1), [LS.Acheck(inp)] + ([LS.Areg(star)] + cont));
    assert ia == [LS.Areg(r1)] + ([LS.Acheck(inp)] + ([LS.Areg(star)] + cont));
    assert EL.PikeLkActionsRec(pacts) && EL.PikeLkActionsRec(ia);
    NB.EncOkConsPlus(plus, cont, inp, b);
    NB.EncOkEncodable(cont, inp, b);
    NB.EncOkIter(r1, star, cont, inp);
    LkBodyGroupsSubDG(r1);
    LL.LkBodyGroupsConfines(r1, DG(r1));
    assert {:split_here} true;
    var tdead := CDP.CdnDeadTree(gidl, ti);
    forall gm: LG.GroupMap
      ensures var rc := LT.TreeRes(tdead, gm, inp, WP.Forward);
              var rp := LT.TreeRes(t, gm, inp, WP.Forward);
              (rc.Some? <==> rp.Some?)
              && (rc.Some? ==> rc.value.0 == rp.value.0 && LL.GmAgreeOutside(rc.value.1, rp.value.1, {}))
    {
      NB.EncTreeIsTree(rer, pacts, inp, b, t, gm);
      NB.EncTreeIsTree(rer, ia, inp, BS.CannotExit, ti, LG.GMReset(gidl, gm));
      CDP.CdnPlusPriorityNone(rer, r1, cont, inp, gm, DG(r1), t, ti);
      var rp := LT.TreeRes(t, gm, inp, WP.Forward);
      if rp.Some? { LL.GmAgreeOutsideRefl(rp.value.1, {}); }
    }
  }

  // ===========================================================================
  // 15. (G4b-1) The chain of the first empty path is invisible outside `G ⊇ OutLk(r1)` once the plus's
  //     `Reset(DefGroups(r1))` has cleared the look groups: its Open/Close steps are `OutLk(r1)` groups
  //     (`OCStepsL`, W15), and its Resets only clear groups of `r1`, which stay unset outside `G`.
  // ===========================================================================

  /** r's groups that are not inside a lookaround. */
  ghost function OutLk(r: L.Regex): set<LG.GroupId>
    decreases r
  {
    match r
    case Disjunction(r1, r2) => OutLk(r1) + OutLk(r2)
    case Sequence(r1, r2) => OutLk(r1) + OutLk(r2)
    case Quantified(_, _, _, r1) => OutLk(r1)
    case Group(id, r1) => {id} + OutLk(r1)
    case _ => {}
  }

  ghost predicate OCIn(s: seq<Step>, G: set<LG.GroupId>) {
    forall i :: 0 <= i < |s| && s[i].GA? && !s[i].a.Reset? ==> s[i].a.g in G
  }

  lemma OCInCat(a: seq<Step>, b: seq<Step>, G: set<LG.GroupId>)
    requires OCIn(a, G) && OCIn(b, G)
    ensures OCIn(a + b, G)
  {
    forall i | 0 <= i < |a + b| && (a + b)[i].GA? && !(a + b)[i].a.Reset? ensures (a + b)[i].a.g in G {
      if i < |a| { assert (a + b)[i] == a[i]; } else { assert (a + b)[i] == b[i - |a|]; }
    }
  }

  /** The path's Open/Close steps are r's out-of-look groups. */
  lemma OCStepsL(rer: LW.RegExpRecord, r: L.Regex, inp: LC.Input)
    requires FirstEmptyPathLkL(rer, r, inp).Some?
    ensures OCIn(FirstEmptyPathLkL(rer, r, inp).value, OutLk(r))
    decreases NT.RSizeL(r), NT.MinOfL(r)
  {
    var s := FirstEmptyPathLkL(rer, r, inp).value;
    var solo := [LS.Areg(r)];
    assert solo[0] == LS.Areg(r) && solo[1..] == [];
    assert FirstEmptyPathLkA(rer, [], inp) == Some([]);
    match r
    case Epsilon => assert s == [];
    case Character(_) =>
    case Backreference(_) =>
    case AnchorR(a) => assert s == [];
    case LookaroundR(lk, b) =>
      assert [LkS(lk, b)] + [] == [LkS(lk, b)];
      assert s == [LkS(lk, b)];
    case Disjunction(r1, r2) =>
      assert [LS.Areg(r1)] + [] == [LS.Areg(r1)] && [LS.Areg(r2)] + [] == [LS.Areg(r2)];
      var p1 := FirstEmptyPathLkL(rer, r1, inp);
      assert FirstEmptyPathLkL(rer, r, inp) == (match p1 case Some(p) => Some(p) case None => FirstEmptyPathLkL(rer, r2, inp));
      if p1.Some? { OCStepsL(rer, r1, inp); } else { OCStepsL(rer, r2, inp); }
    case Sequence(r1, r2) =>
      assert [LS.Areg(r1), LS.Areg(r2)] + [] == [LS.Areg(r1)] + [LS.Areg(r2)];
      assert [LS.Areg(r2)] + [] == [LS.Areg(r2)];
      FirstEmptyPathLkAComp(rer, r1, [LS.Areg(r2)], inp);
      assert FirstEmptyPathLkL(rer, r, inp) == FirstEmptyPathLkA(rer, [LS.Areg(r1), LS.Areg(r2)] + [], inp);
      assert FirstEmptyPathLkA(rer, [LS.Areg(r2)], inp) == FirstEmptyPathLkL(rer, r2, inp);
      OCStepsL(rer, r1, inp);
      OCStepsL(rer, r2, inp);
      OCInCat(FirstEmptyPathLkL(rer, r1, inp).value, FirstEmptyPathLkL(rer, r2, inp).value, OutLk(r));
    case Group(gid, r1) =>
      assert [LS.Areg(r1), LS.Aclose(gid)] + [] == [LS.Areg(r1)] + [LS.Aclose(gid)];
      assert [LS.Aclose(gid)][0] == LS.Aclose(gid) && [LS.Aclose(gid)][1..] == [];
      assert [GA(LG.Close(gid))] + [] == [GA(LG.Close(gid))];
      assert FirstEmptyPathLkA(rer, [LS.Aclose(gid)], inp) == Some([GA(LG.Close(gid))]);
      FirstEmptyPathLkAComp(rer, r1, [LS.Aclose(gid)], inp);
      var s1 := FirstEmptyPathLkL(rer, r1, inp).value;
      assert s == [GA(LG.Open(gid))] + (s1 + [GA(LG.Close(gid))]);
      OCStepsL(rer, r1, inp);
      OCInCat(s1, [GA(LG.Close(gid))], OutLk(r));
      OCInCat([GA(LG.Open(gid))], s1 + [GA(LG.Close(gid))], OutLk(r));
    case Quantified(greedy, min, delta, r1) =>
      if min == 0 {
        assert s == [];
      } else {
        var gidl := L.DefGroups(r1);
        var qn := L.Quantified(greedy, min - 1, delta, r1);
        assert NT.RSizeL(qn) == NT.RSizeL(r) && NT.MinOfL(qn) < NT.MinOfL(r);
        assert [LS.Areg(r1), LS.Areg(qn)] + [] == [LS.Areg(r1)] + [LS.Areg(qn)];
        assert [LS.Areg(qn)] + [] == [LS.Areg(qn)];
        FirstEmptyPathLkAComp(rer, r1, [LS.Areg(qn)], inp);
        assert FirstEmptyPathLkA(rer, [LS.Areg(qn)], inp) == FirstEmptyPathLkL(rer, qn, inp);
        var s1 := FirstEmptyPathLkL(rer, r1, inp).value;
        var sn := FirstEmptyPathLkL(rer, qn, inp).value;
        assert s == [GA(LG.Reset(gidl))] + (s1 + sn);
        OCStepsL(rer, r1, inp);
        OCStepsL(rer, qn, inp);
        OCInCat(s1, sn, OutLk(r));
        OCInCat([GA(LG.Reset(gidl))], s1 + sn, OutLk(r));
      }
  }

  /** Open/Close actions of a bare path lie in `G`. */
  ghost predicate OCInP(p: seq<LG.GroupAction>, G: set<LG.GroupId>) {
    forall i :: 0 <= i < |p| && !p[i].Reset? ==> p[i].g in G
  }

  lemma OCInProj(s: seq<Step>, G: set<LG.GroupId>)
    requires OCIn(s, G)
    ensures OCInP(Proj(s), G)
    decreases |s|
  {
    if |s| > 0 {
      assert s == [s[0]] + s[1..];
      ProjCons(s[0], s[1..]);
      assert OCIn(s[1..], G) by {
        forall i | 0 <= i < |s[1..]| && s[1..][i].GA? && !s[1..][i].a.Reset? ensures s[1..][i].a.g in G { assert s[1..][i] == s[i + 1]; }
      }
      OCInProj(s[1..], G);
      var h := if s[0].GA? then [s[0].a] else [];
      assert Proj(s) == h + Proj(s[1..]);
      forall i | 0 <= i < |Proj(s)| && !Proj(s)[i].Reset? ensures Proj(s)[i].g in G {
        if i < |h| { assert Proj(s)[i] == s[0].a; } else { assert Proj(s)[i] == Proj(s[1..])[i - |h|]; }
      }
    }
  }

  /** A bare path whose Open/Close steps lie in `G` and whose actions stay in `D`, run from a map where `D`'s
      groups outside `G` are unset, changes nothing outside `G`. */
  lemma ApplyPathOCOutside(p: seq<LG.GroupAction>, idx: nat, gm: LG.GroupMap, G: set<LG.GroupId>, D: set<LG.GroupId>)
    requires OCInP(p, G) && NP.PathIn(p, D)
    requires forall g :: g in D && g !in G ==> g !in gm
    ensures LL.GmAgreeOutside(NP.ApplyPath(p, idx, gm), gm, G)
    decreases |p|
  {
    if |p| == 0 { LL.GmAgreeOutsideRefl(gm, G); return; }
    var gm1 := LG.GMUpdate(p[0], idx, gm);
    assert CE.GmActionIn(p[0], D);
    assert LL.GmAgreeOutside(gm1, gm, G) && (forall g :: g in D && g !in G ==> g !in gm1) by {
      match p[0]
      case Open(g) =>
      case Close(g) =>
      case Reset(gs) =>
    }
    assert OCInP(p[1..], G) by { forall i | 0 <= i < |p[1..]| && !p[1..][i].Reset? ensures p[1..][i].g in G { assert p[1..][i] == p[i + 1]; } }
    assert NP.PathIn(p[1..], D) by { forall i | 0 <= i < |p[1..]| ensures CE.GmActionIn(p[1..][i], D) { assert p[1..][i] == p[i + 1]; } }
    ApplyPathOCOutside(p[1..], idx, gm1, G, D);
    LL.GmAgreeOutsideTrans(NP.ApplyPath(p, idx, gm), gm1, gm, G);
  }

  /** The first empty path's Open/Close steps are `OutLk(r)` groups and all its actions are `r`'s groups. */
  lemma FirstEmptyPathOC(rer: LW.RegExpRecord, r: L.Regex, inp: LC.Input)
    requires NP.FirstEmptyPathL(rer, r, inp).Some?
    ensures OCInP(NP.FirstEmptyPathL(rer, r, inp).value, OutLk(r))
    ensures NP.PathIn(NP.FirstEmptyPathL(rer, r, inp).value, DG(r))
  {
    ProjPath(rer, [LS.Areg(r)], inp);
    OCStepsL(rer, r, inp);
    OCInProj(FirstEmptyPathLkL(rer, r, inp).value, OutLk(r));
    assert NP.ActsGroupsIn([LS.Areg(r)], DG(r)) by {
      forall i | 0 <= i < |[LS.Areg(r)]|
        ensures ([LS.Areg(r)][i].Areg? ==> forall g :: g in L.DefGroups([LS.Areg(r)][i].r) ==> g in DG(r))
             && ([LS.Areg(r)][i].Aclose? ==> [LS.Areg(r)][i].gid in DG(r))
      {}
    }
    NP.PathActionsIn(rer, [LS.Areg(r)], inp, DG(r));
  }

  /** Bridges for the callers of the old `CinOk` arm: group-free look bodies satisfy the static scope, and
      `OutLk` is part of `DG`. */
  lemma LkBodiesInSEmptyGF(r: L.Regex)
    requires LL.LkBodiesInS(r, {})
    ensures EmptyLooksGroupFreeL(r)
    decreases r
  {
    match r
    case Disjunction(r1, r2) => LkBodiesInSEmptyGF(r1); LkBodiesInSEmptyGF(r2);
    case Sequence(r1, r2) => LkBodiesInSEmptyGF(r1); LkBodiesInSEmptyGF(r2);
    case Quantified(_, _, _, r1) => LkBodiesInSEmptyGF(r1);
    case Group(_, r1) => LkBodiesInSEmptyGF(r1);
    case LookaroundR(_, b) =>
      reveal LL.LookBodyInS();
      assert LL.DefGroupsIn(b, {});
      assert DG(b) == {};
    case _ =>
  }

  lemma OutLkSubDG(r: L.Regex)
    ensures OutLk(r) <= DG(r)
    decreases r
  {
    match r
    case Disjunction(r1, r2) => OutLkSubDG(r1); OutLkSubDG(r2);
    case Sequence(r1, r2) => OutLkSubDG(r1); OutLkSubDG(r2);
    case Quantified(_, _, _, r1) => OutLkSubDG(r1);
    case Group(_, r1) => OutLkSubDG(r1);
    case _ =>
  }

  // ===========================================================================
  // 16. (G4b-2) The synthetic stamp node, spec side (ported from the W20 §7 probe, `work/g4b2/`): machine B's
  //     node at a nulled-exit stamp is ONE lookahead gate whose body tree is `Reset(DefGroups r1); ChainLk(DropOC s)`
  //     with `s` the body's Lk-carrying first empty path; its fold is `NulledIterationLeaf`'s leaf.
  // ===========================================================================

  function DropOC(s: seq<Step>): seq<Step>
    decreases |s|
  {
    if |s| == 0 then [] else (if s[0].GA? && !s[0].a.Reset? then [] else [s[0]]) + DropOC(s[1..])
  }

  lemma DropOCSteps(rer: LW.RegExpRecord, s: seq<Step>, inp: LC.Input, X: set<LG.GroupId>)
    requires LkStepsOk(rer, s, inp, X)
    ensures LkStepsOk(rer, DropOC(s), inp, X)
    decreases |s|
  {
    if |s| > 0 {
      assert LkStepsOk(rer, s[1..], inp, X) by {
        forall i | 0 <= i < |s[1..]| && s[1..][i].LkS?
          ensures DG(s[1..][i].b) <= X && EL.PikeLkRegexRec(s[1..][i].b)
                  && NP.LkVerdictL(rer, s[1..][i].lk, s[1..][i].b, inp)
        { assert s[1..][i] == s[i + 1]; }
      }
      DropOCSteps(rer, s[1..], inp, X);
      var h := if s[0].GA? && !s[0].a.Reset? then [] else [s[0]];
      assert DropOC(s) == h + DropOC(s[1..]);
      assert LkStepsOk(rer, h, inp, X);
      LkStepsOkCat(rer, h, DropOC(s[1..]), inp, X);
    }
  }

  /** A look step is a frame outside any `G` (W15 G4bWalkB). */
  lemma LkGmFrameOutside(rer: LW.RegExpRecord, lk: L.Lookaround, b: L.Regex, inp: LC.Input,
                         gm1: LG.GroupMap, gm2: LG.GroupMap, G: set<LG.GroupId>)
    requires EL.PikeLkRegexRec(b)
    requires LL.GmAgreeOutside(gm1, gm2, G)
    ensures LL.GmAgreeOutside(LkGm(rer, lk, b, inp, gm1), LkGm(rer, lk, b, inp, gm2), G)
  {
    var ldir := L.LkDir(lk);
    EL.ComputeTrGmIndepLkRec(rer, b, inp, gm1, ldir);
    EL.ComputeTrGmIndepLkRec(rer, b, inp, gm2, ldir);
    var tlk := FU.ComputeTr(rer, [LS.Areg(b)], inp, LG.Empty, ldir);
    assert LkGm(rer, lk, b, inp, gm1) == (match LS.LkResult(lk, tlk, gm1, inp) case Some(g) => g case None => gm1);
    assert LkGm(rer, lk, b, inp, gm2) == (match LS.LkResult(lk, tlk, gm2, inp) case Some(g) => g case None => gm2);
    hide FU.ComputeTr;
    LL.TreeLeavesFrameOutside(tlk, gm1, gm2, inp, ldir, G);
    LT.FirstTreeLeaf(tlk, gm1, inp, ldir);
    LT.FirstTreeLeaf(tlk, gm2, inp, ldir);
    var s1 := LT.TreeLeaves(tlk, gm1, inp, ldir);
    var s2 := LT.TreeLeaves(tlk, gm2, inp, ldir);
    if L.Positivity(lk) && |s1| > 0 {
      assert LS.LkResult(lk, tlk, gm1, inp) == Some(s1[0].1);
      assert LS.LkResult(lk, tlk, gm2, inp) == Some(s2[0].1);
    }
  }

  /** Dropping Open/Close in `G` is a frame outside `G` (W15 G4bWalkB). */
  lemma DropOCFrame(rer: LW.RegExpRecord, s: seq<Step>, inp: LC.Input, gm1: LG.GroupMap, gm2: LG.GroupMap,
                    G: set<LG.GroupId>)
    requires LL.GmAgreeOutside(gm1, gm2, G)
    requires OCIn(s, G)
    requires forall i :: 0 <= i < |s| && s[i].LkS? ==> EL.PikeLkRegexRec(s[i].b)
    ensures LL.GmAgreeOutside(ApplyPathLk(rer, DropOC(s), inp, gm1), ApplyPathLk(rer, s, inp, gm2), G)
    decreases |s|
  {
    if |s| == 0 { return; }
    var t := s[1..];
    assert OCIn(t, G) by {
      forall i | 0 <= i < |t| && t[i].GA? && !t[i].a.Reset? ensures t[i].a.g in G { assert t[i] == s[i + 1]; }
    }
    assert forall i :: 0 <= i < |t| && t[i].LkS? ==> EL.PikeLkRegexRec(t[i].b) by {
      forall i | 0 <= i < |t| && t[i].LkS? ensures EL.PikeLkRegexRec(t[i].b) { assert t[i] == s[i + 1]; }
    }
    var x := s[0];
    var gm2' := StepGm(rer, x, inp, gm2);
    assert ApplyPathLk(rer, s, inp, gm2) == ApplyPathLk(rer, t, inp, gm2');
    if x.GA? && !x.a.Reset? {
      assert DropOC(s) == DropOC(t);
      assert x.a.g in G;
      assert LL.GmAgreeOutside(gm2', gm2, G) by {
        match x.a
        case Open(g) =>
        case Close(g) =>
      }
      LL.GmAgreeOutsideSym(gm2', gm2, G);
      LL.GmAgreeOutsideTrans(gm1, gm2, gm2', G);
      DropOCFrame(rer, t, inp, gm1, gm2', G);
    } else {
      assert DropOC(s) == [x] + DropOC(t);
      ApplyPathLkCons(rer, x, DropOC(t), inp, gm1);
      var gm1' := StepGm(rer, x, inp, gm1);
      match x {
        case GA(a) => LL.GMUpdateAgreeOutside(a, LC.Idx(inp), gm1, gm2, G);
        case LkS(lk, b) => LkGmFrameOutside(rer, lk, b, inp, gm1, gm2, G);
      }
      DropOCFrame(rer, t, inp, gm1', gm2', G);
    }
  }

  /** Resets and looks only: from a map where `D \ X` is unset, the fold is the identity outside `X`
      (`X` holds every crossed look body's groups, `D` every action's groups). */
  lemma DropOCPlain(rer: LW.RegExpRecord, s: seq<Step>, inp: LC.Input, gm: LG.GroupMap,
                    X: set<LG.GroupId>, D: set<LG.GroupId>)
    requires NP.PathIn(Proj(s), D)
    requires forall i :: 0 <= i < |s| && s[i].LkS? ==> DG(s[i].b) <= X && EL.PikeLkRegexRec(s[i].b)
    requires forall g :: g in D && g !in X ==> g !in gm
    ensures LL.GmAgreeOutside(ApplyPathLk(rer, DropOC(s), inp, gm), gm, X)
    decreases |s|
  {
    if |s| == 0 { return; }
    var t := s[1..];
    var x := s[0];
    assert s == [x] + t;
    ProjCons(x, t);
    var h := if x.GA? then [x.a] else [];
    assert Proj(s) == h + Proj(t);
    assert forall i :: 0 <= i < |t| && t[i].LkS? ==> DG(t[i].b) <= X && EL.PikeLkRegexRec(t[i].b) by {
      forall i | 0 <= i < |t| && t[i].LkS? ensures DG(t[i].b) <= X && EL.PikeLkRegexRec(t[i].b) { assert t[i] == s[i + 1]; }
    }
    assert NP.PathIn(Proj(t), D) by {
      forall i | 0 <= i < |Proj(t)| ensures CE.GmActionIn(Proj(t)[i], D) {
        assert Proj(t)[i] == Proj(s)[|h| + i];
      }
    }
    if x.GA? && !x.a.Reset? {
      assert DropOC(s) == DropOC(t);
      DropOCPlain(rer, t, inp, gm, X, D);
    } else {
      assert DropOC(s) == [x] + DropOC(t);
      ApplyPathLkCons(rer, x, DropOC(t), inp, gm);
      var gm1 := StepGm(rer, x, inp, gm);
      assert LL.GmAgreeOutside(gm1, gm, X) && (forall g :: g in D && g !in X ==> g !in gm1) by {
        match x {
          case GA(a) =>
            assert Proj(s)[0] == a;
            assert CE.GmActionIn(a, D);
          case LkS(lk, b) =>
            assert s[0].LkS?;
            LkGmOutside(rer, lk, b, inp, gm);
        }
      }
      DropOCPlain(rer, t, inp, gm1, X, D);
    }
  }

  /** Under group uniqueness, a group outside every look is in no look body. */
  lemma OutLkLkBodyDisjoint(r: L.Regex)
    requires GUniq(r)
    ensures OutLk(r) !! LL.LkBodyGroups(r)
    decreases r
  {
    match r
    case Disjunction(r1, r2) =>
      OutLkLkBodyDisjoint(r1); OutLkLkBodyDisjoint(r2);
      OutLkSubDG(r1); OutLkSubDG(r2); LkBodyGroupsSubDG(r1); LkBodyGroupsSubDG(r2);
    case Sequence(r1, r2) =>
      OutLkLkBodyDisjoint(r1); OutLkLkBodyDisjoint(r2);
      OutLkSubDG(r1); OutLkSubDG(r2); LkBodyGroupsSubDG(r1); LkBodyGroupsSubDG(r2);
    case Quantified(_, _, _, r1) => OutLkLkBodyDisjoint(r1);
    case Group(id, r1) => OutLkLkBodyDisjoint(r1); LkBodyGroupsSubDG(r1);
    case _ =>
  }

  /** The stamp gate's path: the body's Lk-carrying first empty path with Open/Close dropped. */
  ghost function StampPath(rer: LW.RegExpRecord, r1: L.Regex, inp: LC.Input): seq<Step> {
    var p := FirstEmptyPathLkL(rer, r1, inp);
    if p.Some? then DropOC(p.value) else []
  }

  /** THE SYNTHETIC NODE'S BODY (W20 §4): `Reset(gidl); ChainLk(DropOC(s), Match)`. */
  ghost function StampTreeLk(rer: LW.RegExpRecord, r1: L.Regex, inp: LC.Input): LT.Tree {
    LT.GroupActionT(LG.Reset(L.DefGroups(r1)), ChainLk(rer, StampPath(rer, r1, inp), inp, LT.Match))
  }

  /** `gm' = fold`: what machine B's map becomes across the synthetic node. */
  ghost function StampFold(rer: LW.RegExpRecord, r1: L.Regex, inp: LC.Input, gm: LG.GroupMap): LG.GroupMap {
    ApplyPathLk(rer, StampPath(rer, r1, inp), inp, LG.GMReset(L.DefGroups(r1), gm))
  }

  /** `SynthGateRes`: ONE `LK(LookAhead, StampTreeLk, t')` node is one machine-B step whose effect is the fold. */

  ghost predicate FrozenAt(rer: LW.RegExpRecord, r1: L.Regex, inp: LC.Input, gmt: LG.GroupMap) {
    var p := FirstEmptyPathLkL(rer, r1, inp);
    p.Some?
    && LkStepsIn(p.value, LL.LkBodyGroups(r1))
    && LkLeafOk(rer, p.value, inp, gmt)
    && (forall g :: g in LL.LkBodyGroups(r1) && !Crossed(p.value, g) ==> g !in gmt)
  }

  /** `FrozenAt` reads `gmt` only on the body's look groups. */
  lemma FrozenAtFrame(rer: LW.RegExpRecord, r1: L.Regex, inp: LC.Input, gmt: LG.GroupMap, gmt': LG.GroupMap)
    requires FrozenAt(rer, r1, inp, gmt)
    requires LL.GmAgreeInside(gmt', gmt, LL.LkBodyGroups(r1))
    ensures FrozenAt(rer, r1, inp, gmt')
  {
    var s := FirstEmptyPathLkL(rer, r1, inp).value;
    forall i | 0 <= i < |s| && s[i].LkS? && L.Positivity(s[i].lk)
      ensures LL.GmAgreeInside(gmt', BodyLeafE(rer, s[i].lk, s[i].b, inp), DG(s[i].b))
    {
      assert DG(s[i].b) <= LL.LkBodyGroups(r1);
      assert LL.GmAgreeInside(gmt, BodyLeafE(rer, s[i].lk, s[i].b, inp), DG(s[i].b));
    }
  }

  /** THE FOLD'S VALUE (uses `NulledIterationLeaf`): outside the body's look groups it is the plain Reset
      (so machine A's tie and every off-body carrier see today's step), and on them it is frozen. */
  lemma StampFoldFacts(rer: LW.RegExpRecord, r1: L.Regex, inp: LC.Input, gm: LG.GroupMap)
    requires EL.PikeLkRegexRec(r1) && GUniq(r1) && NP.FirstEmptyPathL(rer, r1, inp).Some?
    ensures LL.GmAgreeOutside(StampFold(rer, r1, inp, gm), LG.GMReset(L.DefGroups(r1), gm), LL.LkBodyGroups(r1))
    ensures FrozenAt(rer, r1, inp, StampFold(rer, r1, inp, gm))
  {
    var gidl := L.DefGroups(r1);
    var gm0 := LG.GMReset(gidl, gm);
    var t := FU.ComputeTr(rer, [LS.Areg(r1)], inp, gm0, WP.Forward);
    FU.ComputeTrIsTree(rer, [LS.Areg(r1)], inp, gm0, WP.Forward);
    NulledIterationLeaf(rer, r1, inp, gm, t);
    var s := FirstEmptyPathLkL(rer, r1, inp).value;
    var gme := ApplyPathLk(rer, s, inp, gm0);
    var mB := ApplyPathLk(rer, DropOC(s), inp, gm0);
    assert mB == StampFold(rer, r1, inp, gm);
    assert LkLeafOk(rer, s, inp, gme);
    assert forall g :: g in LL.LkBodyGroups(r1) && !Crossed(s, g) ==> g !in gme;
    StepsOkL(rer, r1, inp);
    assert LkStepsIn(s, LL.LkBodyGroups(r1));
    OCStepsL(rer, r1, inp);
    LL.GmAgreeOutsideRefl(gm0, OutLk(r1));
    DropOCFrame(rer, s, inp, gm0, gm0, OutLk(r1));
    OutLkLkBodyDisjoint(r1);
    assert LL.GmAgreeInside(mB, gme, LL.LkBodyGroups(r1));
    assert FrozenAt(rer, r1, inp, gme);
    FrozenAtFrame(rer, r1, inp, gme, mB);
    // the plain half
    assert NP.FirstEmptyPathL(rer, r1, inp) == Some(Proj(s));
    FirstEmptyPathOC(rer, r1, inp);
    LkBodyGroupsSubDG(r1);
    DropOCPlain(rer, s, inp, gm0, LL.LkBodyGroups(r1), DG(r1));
  }

  // ===========================================================================
  // 17. (G4b-2) Machine B's plus head with the SYNTHETIC skip arm (W15 `CinHeadB`, CIN or CDN): the skip arm is
  //     ONE lookahead gate `LK(LookAhead, StampTreeLk, tcont)` (W20 §4: the 1:1 VM lockstep), whose result is the
  //     inline arm's `Reset; ChainLk(DropOC s, tcont)`; it agrees with the spec's forced iteration outside any `G`
  //     holding the body's out-of-look groups, hence EXACTLY on every look group.
  // ===========================================================================

  /** `TreeRes` is a frame (the cin-walk lemma, copied: cin-walk sits above this member). */
  lemma TreeResFrameOutsideL(t: LT.Tree, gm1: LG.GroupMap, gm2: LG.GroupMap, inp: LC.Input,
                             dir: WP.Direction, G: set<LG.GroupId>)
    requires LL.GmAgreeOutside(gm1, gm2, G)
    ensures var r1 := LT.TreeRes(t, gm1, inp, dir);
            var r2 := LT.TreeRes(t, gm2, inp, dir);
            (r1.Some? <==> r2.Some?)
            && (r1.Some? ==> r1.value.0 == r2.value.0 && LL.GmAgreeOutside(r1.value.1, r2.value.1, G))
  {
    LL.TreeLeavesFrameOutside(t, gm1, gm2, inp, dir, G);
    LT.FirstTreeLeaf(t, gm1, inp, dir);
    LT.FirstTreeLeaf(t, gm2, inp, dir);
    var l1 := LT.TreeLeaves(t, gm1, inp, dir);
    var l2 := LT.TreeLeaves(t, gm2, inp, dir);
    if |l1| > 0 {
      assert l1[0].0 == l2[0].0 && LL.GmAgreeOutside(l1[0].1, l2[0].1, G);
    }
  }

  /** The synthetic gate's body passes, ending at `inp` with the fold. */
  lemma StampGateRes(rer: LW.RegExpRecord, r1: L.Regex, inp: LC.Input, gm: LG.GroupMap)
    requires EL.PikeLkRegexRec(r1)
    ensures LT.TreeRes(StampTreeLk(rer, r1, inp), gm, inp, WP.Forward) == Some((inp, StampFold(rer, r1, inp, gm)))
  {
    var gm0 := LG.GMReset(L.DefGroups(r1), gm);
    var sB := StampPath(rer, r1, inp);
    var p := FirstEmptyPathLkL(rer, r1, inp);
    assert LkStepsOk(rer, sB, inp, LL.LkBodyGroups(r1)) by {
      if p.Some? {
        StepsOkL(rer, r1, inp);
        DropOCSteps(rer, p.value, inp, LL.LkBodyGroups(r1));
      }
    }
    ChainLkLeaves(rer, sB, LT.Match, gm0, inp);
    var c := ChainLk(rer, sB, inp, LT.Match);
    var mB := ApplyPathLk(rer, sB, inp, gm0);
    LT.FirstTreeLeaf(c, gm0, inp, WP.Forward);
    assert LT.TreeLeaves(LT.Match, mB, inp, WP.Forward) == [(inp, mB)];
    assert LT.TreeRes(c, gm0, inp, WP.Forward) == Some((inp, mB));
    assert LG.GMUpdate(LG.Reset(L.DefGroups(r1)), LC.Idx(inp), gm) == gm0;
  }

  /** The synthetic gate's tree result is the continuation's at the fold. */
  lemma SynthTreeRes(rer: LW.RegExpRecord, r1: L.Regex, inp: LC.Input, gm: LG.GroupMap, tc: LT.Tree)
    requires EL.PikeLkRegexRec(r1)
    ensures LT.TreeRes(LT.LK(L.LookAhead, StampTreeLk(rer, r1, inp), tc), gm, inp, WP.Forward)
         == LT.TreeRes(tc, StampFold(rer, r1, inp, gm), inp, WP.Forward)
  {
    StampGateRes(rer, r1, inp, gm);
    assert L.Positivity(L.LookAhead) && L.LkDir(L.LookAhead) == WP.Forward;
  }

  /** THE HEAD: machine B's synthetic skip arm against the spec's forced-iteration tree. */
  lemma CinHeadSynth(rer: LW.RegExpRecord, r1: L.Regex, cont: LS.Actions, inp: LC.Input, gm: LG.GroupMap,
                     tplus: LT.Tree, titer: LT.Tree, tcont: LT.Tree, G: set<LG.GroupId>)
    requires EL.PikeLkRegexRec(r1) && EL.PikeLkActionsRec(cont)
    requires NP.FirstEmptyPathL(rer, r1, inp).Some?   // CIN, or CDN with the guard passing
    requires LS.IsTree(rer, [LS.Areg(L.Quantified(true, 1, LN.Inf, r1))] + cont, inp, gm, WP.Forward, tplus)
    requires LS.IsTree(rer, [LS.Areg(r1), LS.Acheck(inp), LS.Areg(L.Quantified(true, 0, LN.Inf, r1))] + cont,
                       inp, LG.GMReset(L.DefGroups(r1), gm), WP.Forward, titer)
    requires LS.IsTree(rer, cont, inp, gm, WP.Forward, tcont)
    requires OutLk(r1) <= G
    ensures var gidl := L.DefGroups(r1);
            var tB := LT.Choice(LT.GroupActionT(LG.Reset(gidl), titer),
                                LT.LK(L.LookAhead, StampTreeLk(rer, r1, inp), tcont));
            var rb := LT.TreeRes(tB, gm, inp, WP.Forward);
            var rp := LT.TreeRes(tplus, gm, inp, WP.Forward);
            (rb.Some? <==> rp.Some?)
            && (rb.Some? ==> rb.value.0 == rp.value.0 && LL.GmAgreeOutside(rb.value.1, rp.value.1, G))
  {
    var gidl := L.DefGroups(r1);
    var gm' := LG.GMReset(gidl, gm);
    CdnPlusPriorityLkSome(rer, r1, cont, inp, gm, tplus, titer, tcont);
    var s := FirstEmptyPathLkL(rer, r1, inp).value;
    var sB := DropOC(s);
    assert StampPath(rer, r1, inp) == sB;
    StepsOkL(rer, r1, inp);
    DropOCSteps(rer, s, inp, LL.LkBodyGroups(r1));
    OCStepsL(rer, r1, inp);
    assert OCIn(s, G) by {
      forall i | 0 <= i < |s| && s[i].GA? && !s[i].a.Reset? ensures s[i].a.g in G {
        assert s[i].a.g in OutLk(r1);
      }
    }
    var tF := ChainLk(rer, s, inp, tcont);
    ChainLkLeaves(rer, s, tcont, gm', inp);
    var mF := ApplyPathLk(rer, s, inp, gm');
    var mB := ApplyPathLk(rer, sB, inp, gm');
    assert mB == StampFold(rer, r1, inp, gm);
    LL.GmAgreeOutsideRefl(gm', G);
    DropOCFrame(rer, s, inp, gm', gm', G);
    TreeResFrameOutsideL(tcont, mB, mF, inp, WP.Forward, G);
    LT.FirstTreeLeaf(tF, gm', inp, WP.Forward);
    LT.FirstTreeLeaf(tcont, mF, inp, WP.Forward);
    assert LT.TreeRes(tF, gm', inp, WP.Forward) == LT.TreeRes(tcont, mF, inp, WP.Forward);
    SynthTreeRes(rer, r1, inp, gm, tcont);
    var tL := LT.GroupActionT(LG.Reset(gidl), titer);
    var tcin := LT.Choice(tL, LT.GroupActionT(LG.Reset(gidl), tF));
    var tB := LT.Choice(tL, LT.LK(L.LookAhead, StampTreeLk(rer, r1, inp), tcont));
    assert LT.TreeRes(tcin, gm, inp, WP.Forward) == LT.Seqop(LT.TreeRes(tL, gm, inp, WP.Forward), LT.TreeRes(tF, gm', inp, WP.Forward));
    assert LT.TreeRes(tB, gm, inp, WP.Forward) == LT.Seqop(LT.TreeRes(tL, gm, inp, WP.Forward), LT.TreeRes(tcont, mB, inp, WP.Forward));
    var rL := LT.TreeRes(tL, gm, inp, WP.Forward);
    if rL.Some? {
      LL.GmAgreeOutsideRefl(rL.value.1, G);
    }
  }

  /** A positive forward gate is a congruence: equal bodies, continuations agreeing outside `G`. */
  lemma RACongLkPosOutside(lk: L.Lookaround, tlk: LT.Tree, x: LT.Tree, y: LT.Tree, inp: LC.Input, G: set<LG.GroupId>)
    requires L.Positivity(lk)
    requires NP.ResAgreeAtOutside(x, y, inp, G)
    ensures NP.ResAgreeAtOutside(LT.LK(lk, tlk, x), LT.LK(lk, tlk, y), inp, G)
  {
    forall gm: LG.GroupMap
      ensures var r1 := LT.TreeRes(LT.LK(lk, tlk, x), gm, inp, WP.Forward);
              var r2 := LT.TreeRes(LT.LK(lk, tlk, y), gm, inp, WP.Forward);
              (r1.Some? <==> r2.Some?)
              && (r1.Some? ==> r1.value.0 == r2.value.0 && LL.GmAgreeOutside(r1.value.1, r2.value.1, G))
    {
      var rl := LT.TreeRes(tlk, gm, inp, L.LkDir(lk));
      if rl.Some? {
        var gm1 := rl.value.1;
        assert LT.TreeRes(LT.LK(lk, tlk, x), gm, inp, WP.Forward) == LT.TreeRes(x, gm1, inp, WP.Forward);
        assert LT.TreeRes(LT.LK(lk, tlk, y), gm, inp, WP.Forward) == LT.TreeRes(y, gm1, inp, WP.Forward);
      }
    }
  }

  /** `CinHeadSynth` on the Bool trees (machine B's walk lives there): the synthetic head against the spec's. */
  lemma CinHeadSynthBool(rer: LW.RegExpRecord, r1: L.Regex, cont: LS.Actions, inp: LC.Input, b: BS.LoopBool,
                         t: LT.Tree, ti: LT.Tree, tcont: LT.Tree, G: set<LG.GroupId>)
    requires EL.PikeLkRegexRec(r1) && EL.PikeLkActionsRec(cont)
    requires EL.CinHeadL(true, 1, LN.Inf, r1)
    requires NP.FirstEmptyPathL(rer, r1, inp).Some?
    requires NB.EncOk(cont, inp, b)
    requires EL.BoolTreeLk(rer, [LS.Areg(L.Quantified(true, 1, LN.Inf, r1))] + cont, inp, b, t)
    requires EL.BoolTreeLk(rer, [LS.Areg(r1), LS.Acheck(inp), LS.Areg(L.Quantified(true, 0, LN.Inf, r1))] + cont, inp, BS.CannotExit, ti)
    requires EL.BoolTreeLk(rer, cont, inp, b, tcont)
    requires OutLk(r1) <= G
    ensures NP.ResAgreeAtOutside(LT.Choice(LT.GroupActionT(LG.Reset(L.DefGroups(r1)), ti),
                                           LT.LK(L.LookAhead, StampTreeLk(rer, r1, inp), tcont)), t, inp, G)
  {
    var gidl := L.DefGroups(r1);
    var plus := L.Quantified(true, 1, LN.Inf, r1);
    var star := L.Quantified(true, 0, LN.Inf, r1);
    EL.PikeLkRecQuantZero(true, LN.Inf, r1);
    var pacts := [LS.Areg(plus)] + cont;
    var ia := [LS.Areg(r1), LS.Acheck(inp), LS.Areg(star)] + cont;
    assert EL.PikeLkRegexRec(plus) && EL.PikeLkRegexRec(star);
    assert EL.PikeLkActionRec(LS.Areg(plus)) && EL.PikeLkActionRec(LS.Areg(star))
        && EL.PikeLkActionRec(LS.Areg(r1)) && EL.PikeLkActionRec(LS.Acheck(inp));
    EL.PikeLkActionsRecConsIff(LS.Areg(plus), cont);
    EL.PikeLkActionsRecConsIff(LS.Areg(star), cont);
    EL.PikeLkActionsRecConsIff(LS.Acheck(inp), [LS.Areg(star)] + cont);
    EL.PikeLkActionsRecConsIff(LS.Areg(r1), [LS.Acheck(inp)] + ([LS.Areg(star)] + cont));
    assert ia == [LS.Areg(r1)] + ([LS.Acheck(inp)] + ([LS.Areg(star)] + cont));
    assert EL.PikeLkActionsRec(pacts) && EL.PikeLkActionsRec(ia);
    NB.EncOkConsPlus(plus, cont, inp, b);
    NB.EncOkEncodable(cont, inp, b);
    NB.EncOkIter(r1, star, cont, inp);
    assert {:split_here} true;
    var tB := LT.Choice(LT.GroupActionT(LG.Reset(gidl), ti), LT.LK(L.LookAhead, StampTreeLk(rer, r1, inp), tcont));
    forall gm: LG.GroupMap
      ensures var rb := LT.TreeRes(tB, gm, inp, WP.Forward);
              var rp := LT.TreeRes(t, gm, inp, WP.Forward);
              (rb.Some? <==> rp.Some?)
              && (rb.Some? ==> rb.value.0 == rp.value.0 && LL.GmAgreeOutside(rb.value.1, rp.value.1, G))
    {
      NB.EncTreeIsTree(rer, pacts, inp, b, t, gm);
      NB.EncTreeIsTree(rer, ia, inp, BS.CannotExit, ti, LG.GMReset(gidl, gm));
      NB.EncTreeIsTree(rer, cont, inp, b, tcont, gm);
      CinHeadSynth(rer, r1, cont, inp, gm, t, ti, tcont, G);
    }
  }
}
