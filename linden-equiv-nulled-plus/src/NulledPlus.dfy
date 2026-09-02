// §2.5b stage 2, rung A: the Hd-level (first-result) agreement relation the
// CIN-greedy plus needs, its congruence toolkit, and the spec-level priority
// theorem (engine shape `T_cin` vs the spec's forced-iteration tree).
module LindenElkNulledPlus {
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
  import EQ = Equivalence
  import FM = FlatMap
  import EL = LindenElkEntryLk
  import CE = LindenElkCheckErase
  import LL = LindenElkLookLeaves

  /** First-result agreement outside `S`: at every incoming map both trees
      have a result or neither does, and when both do the positions coincide
      and the maps agree outside `S`. The Hd-level weakening of
      `LL.LeavesAgreeAtOutside` — the relation a CIN-greedy `+` preserves
      (its LEAF LISTS differ: the spec re-emits the consuming blocks under
      every empty mandatory iteration). */
  ghost predicate ResAgreeAtOutside(t1: LT.Tree, t2: LT.Tree, inp: LC.Input, S: set<LG.GroupId>) {
    forall gm: LG.GroupMap ::
      var r1 := LT.TreeRes(t1, gm, inp, WP.Forward);
      var r2 := LT.TreeRes(t2, gm, inp, WP.Forward);
      (r1.Some? <==> r2.Some?)
      && (r1.Some? ==> r1.value.0 == r2.value.0 && LL.GmAgreeOutside(r1.value.1, r2.value.1, S))
  }

  /** Leaf-list agreement implies first-result agreement (`TreeRes` is the
      head of `TreeLeaves`). */
  lemma ResFromLeavesOutside(t1: LT.Tree, t2: LT.Tree, inp: LC.Input, S: set<LG.GroupId>)
    requires LL.LeavesAgreeAtOutside(t1, t2, inp, S)
    ensures ResAgreeAtOutside(t1, t2, inp, S)
  {
    forall gm: LG.GroupMap
      ensures var r1 := LT.TreeRes(t1, gm, inp, WP.Forward);
              var r2 := LT.TreeRes(t2, gm, inp, WP.Forward);
              (r1.Some? <==> r2.Some?)
              && (r1.Some? ==> r1.value.0 == r2.value.0 && LL.GmAgreeOutside(r1.value.1, r2.value.1, S))
    {
      LT.FirstTreeLeaf(t1, gm, inp, WP.Forward);
      LT.FirstTreeLeaf(t2, gm, inp, WP.Forward);
      var l1 := LT.TreeLeaves(t1, gm, inp, WP.Forward);
      var l2 := LT.TreeLeaves(t2, gm, inp, WP.Forward);
      assert |l1| == |l2|;
      if |l1| > 0 {
        assert l1[0].0 == l2[0].0 && LL.GmAgreeOutside(l1[0].1, l2[0].1, S);
      }
    }
  }

  // --- congruence toolkit (mirrors LookLeaves' LAAt*Outside family) ---

  lemma RAReflOutside(t: LT.Tree, inp: LC.Input, S: set<LG.GroupId>)
    ensures ResAgreeAtOutside(t, t, inp, S)
  {
    forall gm: LG.GroupMap
      ensures var r := LT.TreeRes(t, gm, inp, WP.Forward);
              r.Some? ==> LL.GmAgreeOutside(r.value.1, r.value.1, S)
    {
      var r := LT.TreeRes(t, gm, inp, WP.Forward);
      if r.Some? { LL.GmAgreeOutsideRefl(r.value.1, S); }
    }
  }

  lemma RASymOutside(t1: LT.Tree, t2: LT.Tree, inp: LC.Input, S: set<LG.GroupId>)
    requires ResAgreeAtOutside(t1, t2, inp, S)
    ensures ResAgreeAtOutside(t2, t1, inp, S)
  {
    forall gm: LG.GroupMap
      ensures var r2 := LT.TreeRes(t2, gm, inp, WP.Forward);
              var r1 := LT.TreeRes(t1, gm, inp, WP.Forward);
              (r2.Some? <==> r1.Some?)
              && (r2.Some? ==> r2.value.0 == r1.value.0 && LL.GmAgreeOutside(r2.value.1, r1.value.1, S))
    {
      var r1 := LT.TreeRes(t1, gm, inp, WP.Forward);
      var r2 := LT.TreeRes(t2, gm, inp, WP.Forward);
      if r1.Some? { LL.GmAgreeOutsideSym(r1.value.1, r2.value.1, S); }
    }
  }

  lemma RATransOutside(a: LT.Tree, b: LT.Tree, c: LT.Tree, inp: LC.Input, S: set<LG.GroupId>)
    requires ResAgreeAtOutside(a, b, inp, S) && ResAgreeAtOutside(b, c, inp, S)
    ensures ResAgreeAtOutside(a, c, inp, S)
  {
    forall gm: LG.GroupMap
      ensures var ra := LT.TreeRes(a, gm, inp, WP.Forward);
              var rc := LT.TreeRes(c, gm, inp, WP.Forward);
              (ra.Some? <==> rc.Some?)
              && (ra.Some? ==> ra.value.0 == rc.value.0 && LL.GmAgreeOutside(ra.value.1, rc.value.1, S))
    {
      var ra := LT.TreeRes(a, gm, inp, WP.Forward);
      var rb := LT.TreeRes(b, gm, inp, WP.Forward);
      var rc := LT.TreeRes(c, gm, inp, WP.Forward);
      if ra.Some? { LL.GmAgreeOutsideTrans(ra.value.1, rb.value.1, rc.value.1, S); }
    }
  }

  lemma RAProgressPassOutside(t: LT.Tree, inp: LC.Input, S: set<LG.GroupId>)
    ensures ResAgreeAtOutside(LT.Progress(t), t, inp, S)
  { RAReflOutside(t, inp, S); }

  lemma RACongProgressOutside(a: LT.Tree, b: LT.Tree, inp: LC.Input, S: set<LG.GroupId>)
    requires ResAgreeAtOutside(a, b, inp, S)
    ensures ResAgreeAtOutside(LT.Progress(a), LT.Progress(b), inp, S)
  {}

  lemma RACongReadOutside(c: char, a: LT.Tree, b: LT.Tree, inp: LC.Input, S: set<LG.GroupId>)
    requires ResAgreeAtOutside(a, b, LC.AdvanceInputP(inp, WP.Forward), S)
    ensures ResAgreeAtOutside(LT.Read(c, a), LT.Read(c, b), inp, S)
  {}

  lemma RACongGroupOutside(g: LG.GroupAction, a: LT.Tree, b: LT.Tree, inp: LC.Input, S: set<LG.GroupId>)
    requires ResAgreeAtOutside(a, b, inp, S)
    ensures ResAgreeAtOutside(LT.GroupActionT(g, a), LT.GroupActionT(g, b), inp, S)
  {}

  lemma RACongAnchorOutside(an: L.Anchor, a: LT.Tree, b: LT.Tree, inp: LC.Input, S: set<LG.GroupId>)
    requires ResAgreeAtOutside(a, b, inp, S)
    ensures ResAgreeAtOutside(LT.AnchorPass(an, a), LT.AnchorPass(an, b), inp, S)
  {}

  lemma RACongChoiceOutside(a1: LT.Tree, b1: LT.Tree, a2: LT.Tree, b2: LT.Tree, inp: LC.Input, S: set<LG.GroupId>)
    requires ResAgreeAtOutside(a1, b1, inp, S) && ResAgreeAtOutside(a2, b2, inp, S)
    ensures ResAgreeAtOutside(LT.Choice(a1, a2), LT.Choice(b1, b2), inp, S)
  {
    forall gm: LG.GroupMap
      ensures var r1 := LT.TreeRes(LT.Choice(a1, a2), gm, inp, WP.Forward);
              var r2 := LT.TreeRes(LT.Choice(b1, b2), gm, inp, WP.Forward);
              (r1.Some? <==> r2.Some?)
              && (r1.Some? ==> r1.value.0 == r2.value.0 && LL.GmAgreeOutside(r1.value.1, r2.value.1, S))
    {
      var x1 := LT.TreeRes(a1, gm, inp, WP.Forward);
      var y1 := LT.TreeRes(a2, gm, inp, WP.Forward);
      var x2 := LT.TreeRes(b1, gm, inp, WP.Forward);
      var y2 := LT.TreeRes(b2, gm, inp, WP.Forward);
      assert LT.TreeRes(LT.Choice(a1, a2), gm, inp, WP.Forward) == LT.Seqop(x1, y1);
      assert LT.TreeRes(LT.Choice(b1, b2), gm, inp, WP.Forward) == LT.Seqop(x2, y2);
      if x1.Some? {
        assert x2.Some?;
      } else {
        assert x2.None?;
      }
    }
  }

  // ===========================================================================
  // The first empty path of an action stack at `inp` (Forward): the group
  // actions along the highest-priority zero-width path to a leaf, or None
  // when no zero-width path reaches a leaf. Mirrors `FS.ComputeTree`'s case
  // structure; termination by the same `ActionsFuel` potential.
  // ===========================================================================

  /** Spec-level lookaround verdict at `inp` (the `LkGateOk` verdict): the
      body's tree from the empty map, judged by `LkResult`. */
  ghost predicate LkVerdictL(rer: LW.RegExpRecord, lk: L.Lookaround, r1: L.Regex, inp: LC.Input) {
    LS.LkResult(lk, FU.ComputeTr(rer, [LS.Areg(r1)], inp, LG.Empty, L.LkDir(lk)), LG.Empty, inp).Some?
  }

  ghost function FirstEmptyPathA(rer: LW.RegExpRecord, acts: LS.Actions, inp: LC.Input): Option<seq<LG.GroupAction>>
    decreases FS.ActionsFuel(acts, inp, WP.Forward)
  {
    if |acts| == 0 then Some([])
    else
      var cont := acts[1..];
      match acts[0]
      case Acheck(strcheck) =>
        // a zero-width path from `inp` passes the check iff `inp` is already
        // strictly past `strcheck`
        if SS.IsStrictSuffix(inp, strcheck, WP.Forward) then
          assert FS.ActionsFuel(cont, inp, WP.Forward) < FS.ActionsFuel(acts, inp, WP.Forward) by {
            SS.IsStrictSuffixCorrect(inp, strcheck, WP.Forward);
            assert acts == [LS.Acheck(strcheck)] + cont;
            FS.CheckTermination(cont, inp, strcheck, WP.Forward);
          }
          FirstEmptyPathA(rer, cont, inp)
        else None
      case Aclose(gid) =>
        assert FS.ActionsFuel(cont, inp, WP.Forward) < FS.ActionsFuel(acts, inp, WP.Forward) by {
          assert acts == [LS.Aclose(gid)] + cont;
          FS.CloseTermination(cont, inp, WP.Forward, gid);
        }
        (match FirstEmptyPathA(rer, cont, inp)
         case Some(p) => Some([LG.Close(gid)] + p)
         case None => None)
      case Areg(r) =>
        match r
        case Epsilon =>
          assert FS.ActionsFuel(cont, inp, WP.Forward) < FS.ActionsFuel(acts, inp, WP.Forward) by {
            assert acts == [LS.Areg(L.Epsilon)] + cont;
            FS.EpsilonTermination(cont, inp, WP.Forward);
          }
          FirstEmptyPathA(rer, cont, inp)
        case Character(_) => None
        case Disjunction(r1, r2) =>
          assert FS.ActionsFuel([LS.Areg(r1)] + cont, inp, WP.Forward) < FS.ActionsFuel(acts, inp, WP.Forward)
              && FS.ActionsFuel([LS.Areg(r2)] + cont, inp, WP.Forward) < FS.ActionsFuel(acts, inp, WP.Forward) by {
            assert acts == [LS.Areg(L.Disjunction(r1, r2))] + cont;
            FS.DisjunctionLeftTermination(cont, inp, WP.Forward, r1, r2);
            FS.DisjunctionRightTermination(cont, inp, WP.Forward, r1, r2);
          }
          (match FirstEmptyPathA(rer, [LS.Areg(r1)] + cont, inp)
           case Some(p) => Some(p)
           case None => FirstEmptyPathA(rer, [LS.Areg(r2)] + cont, inp))
        case Sequence(r1, r2) =>
          assert FS.ActionsFuel([LS.Areg(r1), LS.Areg(r2)] + cont, inp, WP.Forward) < FS.ActionsFuel(acts, inp, WP.Forward) by {
            assert acts == [LS.Areg(L.Sequence(r1, r2))] + cont;
            FS.SequenceTermination(cont, inp, WP.Forward, r1, r2);
            assert LS.SeqList(r1, r2, WP.Forward) == [LS.Areg(r1), LS.Areg(r2)];
          }
          FirstEmptyPathA(rer, [LS.Areg(r1), LS.Areg(r2)] + cont, inp)
        case Quantified(greedy, min, delta, r1) =>
          var gidl := L.DefGroups(r1);
          if min > 0 then
            assert FS.ActionsFuel([LS.Areg(r1), LS.Areg(L.Quantified(greedy, min - 1, delta, r1))] + cont, inp, WP.Forward)
                 < FS.ActionsFuel(acts, inp, WP.Forward) by {
              assert acts == [LS.Areg(L.Quantified(greedy, min, delta, r1))] + cont;
              FS.QuantForcedTermination(cont, inp, WP.Forward, r1, min - 1, delta, greedy);
            }
            (match FirstEmptyPathA(rer, [LS.Areg(r1), LS.Areg(L.Quantified(greedy, min - 1, delta, r1))] + cont, inp)
             case Some(p) => Some([LG.Reset(gidl)] + p)
             case None => None)
          else
            // min == 0: `tree_quant_done` continues; `tree_quant_free`'s
            // iteration arm has NO zero-width leaf (its `Acheck(inp)` kills
            // every empty iteration), so the skip arm is the first empty path
            // for greedy and lazy alike.
            assert FS.ActionsFuel(cont, inp, WP.Forward) < FS.ActionsFuel(acts, inp, WP.Forward) by {
              assert acts == [LS.Areg(L.Quantified(greedy, 0, delta, r1))] + cont;
              FS.QuantFreeSkipTermination(cont, inp, WP.Forward, r1, greedy, delta);
            }
            FirstEmptyPathA(rer, cont, inp)
        case Group(gid, r1) =>
          assert FS.ActionsFuel([LS.Areg(r1), LS.Aclose(gid)] + cont, inp, WP.Forward) < FS.ActionsFuel(acts, inp, WP.Forward) by {
            assert acts == [LS.Areg(L.Group(gid, r1))] + cont;
            FS.GroupTermination(cont, inp, WP.Forward, r1, gid);
          }
          (match FirstEmptyPathA(rer, [LS.Areg(r1), LS.Aclose(gid)] + cont, inp)
           case Some(p) => Some([LG.Open(gid)] + p)
           case None => None)
        case AnchorR(a) =>
          if LS.AnchorSatisfied(rer, a, inp) then
            assert FS.ActionsFuel(cont, inp, WP.Forward) < FS.ActionsFuel(acts, inp, WP.Forward) by {
              assert acts == [LS.Areg(L.AnchorR(a))] + cont;
              FS.AnchorTermination(cont, inp, WP.Forward, a);
            }
            FirstEmptyPathA(rer, cont, inp)
          else None
        case LookaroundR(lk, r1) =>
          if LkVerdictL(rer, lk, r1, inp) then
            assert FS.ActionsFuel(cont, inp, WP.Forward) < FS.ActionsFuel(acts, inp, WP.Forward) by {
              assert acts == [LS.Areg(L.LookaroundR(lk, r1))] + cont;
              FS.LkAfterTermination(cont, inp, WP.Forward, lk, r1);
            }
            FirstEmptyPathA(rer, cont, inp)
          else None
        case Backreference(_) => None
  }

  /** The first empty path of a regex alone. */
  ghost function FirstEmptyPathL(rer: LW.RegExpRecord, r: L.Regex, inp: LC.Input): Option<seq<LG.GroupAction>> {
    FirstEmptyPathA(rer, [LS.Areg(r)], inp)
  }

  /** Applying a path's actions at one index. */
  ghost function ApplyPath(p: seq<LG.GroupAction>, idx: nat, gm: LG.GroupMap): LG.GroupMap
    decreases |p|
  {
    if |p| == 0 then gm else ApplyPath(p[1..], idx, LG.GMUpdate(p[0], idx, gm))
  }

  /** A CI-nullable regex has an empty path at every position, whatever the
      continuation contributes (the continuation must itself have one). */
  lemma CINullableEmptyPathA(rer: LW.RegExpRecord, r: L.Regex, cont: LS.Actions, inp: LC.Input)
    requires NUL.CINullableL(r)
    requires FirstEmptyPathA(rer, cont, inp).Some?
    ensures FirstEmptyPathA(rer, [LS.Areg(r)] + cont, inp).Some?
    decreases FS.ActionsFuel([LS.Areg(r)] + cont, inp, WP.Forward)
  {
    var acts := [LS.Areg(r)] + cont;
    assert acts[0] == LS.Areg(r) && acts[1..] == cont;
    match r
    case Epsilon =>
    case Character(_) =>
    case Disjunction(r1, r2) =>
      FS.DisjunctionLeftTermination(cont, inp, WP.Forward, r1, r2);
      FS.DisjunctionRightTermination(cont, inp, WP.Forward, r1, r2);
      if NUL.CINullableL(r1) {
        CINullableEmptyPathA(rer, r1, cont, inp);
      } else {
        CINullableEmptyPathA(rer, r2, cont, inp);
      }
    case Sequence(r1, r2) =>
      FS.SequenceTermination(cont, inp, WP.Forward, r1, r2);
      assert LS.SeqList(r1, r2, WP.Forward) == [LS.Areg(r1), LS.Areg(r2)];
      FS.ActionsFuelConsAreg(r1, [LS.Areg(r2)] + cont, inp, WP.Forward);
      CINullableEmptyPathA(rer, r2, cont, inp);
      assert [LS.Areg(r1), LS.Areg(r2)] + cont == [LS.Areg(r1)] + ([LS.Areg(r2)] + cont);
      CINullableEmptyPathA(rer, r1, [LS.Areg(r2)] + cont, inp);
    case Quantified(greedy, min, delta, r1) =>
      if min > 0 {
        FS.QuantForcedTermination(cont, inp, WP.Forward, r1, min - 1, delta, greedy);
        var q := L.Quantified(greedy, min - 1, delta, r1);
        FS.ActionsFuelConsAreg(r1, [LS.Areg(q)] + cont, inp, WP.Forward);
        assert NUL.CINullableL(q);
        CINullableEmptyPathA(rer, q, cont, inp);
        assert [LS.Areg(r1), LS.Areg(q)] + cont == [LS.Areg(r1)] + ([LS.Areg(q)] + cont);
        CINullableEmptyPathA(rer, r1, [LS.Areg(q)] + cont, inp);
      }
    case Group(gid, r1) =>
      FS.GroupTermination(cont, inp, WP.Forward, r1, gid);
      FS.ActionsFuelConsAreg(r1, [LS.Aclose(gid)] + cont, inp, WP.Forward);
      FS.CloseTermination(cont, inp, WP.Forward, gid);
      assert [LS.Areg(r1), LS.Aclose(gid)] + cont == [LS.Areg(r1)] + ([LS.Aclose(gid)] + cont);
      assert FirstEmptyPathA(rer, [LS.Aclose(gid)] + cont, inp).Some?;
      CINullableEmptyPathA(rer, r1, [LS.Aclose(gid)] + cont, inp);
    case AnchorR(_) =>
    case LookaroundR(_, _) =>
    case Backreference(_) =>
  }

  // ===========================================================================
  // The first leaf at position `inp` of an IsTree tree is the path's fold.
  // ===========================================================================

  /** Index of the first leaf sitting at `inp`. */
  ghost function FirstAt(ls: seq<LT.Leaf>, inp: LC.Input): Option<nat>
    decreases |ls|
  {
    if |ls| == 0 then None
    else if ls[0].0 == inp then Some(0)
    else match FirstAt(ls[1..], inp) case None => None case Some(k) => Some(k + 1)
  }

  lemma FirstAtSpec(ls: seq<LT.Leaf>, inp: LC.Input)
    ensures FirstAt(ls, inp).Some? ==>
              var k := FirstAt(ls, inp).value;
              k < |ls| && ls[k].0 == inp && (forall j :: 0 <= j < k ==> ls[j].0 != inp)
    ensures FirstAt(ls, inp).None? <==> (forall i :: 0 <= i < |ls| ==> ls[i].0 != inp)
    decreases |ls|
  {
    if |ls| > 0 && ls[0].0 != inp {
      FirstAtSpec(ls[1..], inp);
      if FirstAt(ls[1..], inp).Some? {
        var k := FirstAt(ls[1..], inp).value;
        assert ls[k + 1] == ls[1..][k];
        forall j | 0 <= j < k + 1 ensures ls[j].0 != inp {
          if j > 0 { assert ls[j] == ls[1..][j - 1]; }
        }
      } else {
        forall i | 0 <= i < |ls| ensures ls[i].0 != inp {
          if i > 0 { assert ls[i] == ls[1..][i - 1]; }
        }
      }
    }
  }

  lemma FirstAtApp(a: seq<LT.Leaf>, b: seq<LT.Leaf>, inp: LC.Input)
    ensures FirstAt(a + b, inp)
         == (match FirstAt(a, inp)
             case Some(k) => Some(k)
             case None => (match FirstAt(b, inp) case None => None case Some(k) => Some(k + |a|)))
    decreases |a|
  {
    if |a| == 0 {
      assert a + b == b;
    } else {
      assert (a + b)[0] == a[0];
      assert (a + b)[1..] == a[1..] + b;
      FirstAtApp(a[1..], b, inp);
    }
  }

  /** `ApplyPath` respects outside-`S` agreement. */
  lemma ApplyPathFrame(p: seq<LG.GroupAction>, idx: nat, gm1: LG.GroupMap, gm2: LG.GroupMap, S: set<LG.GroupId>)
    requires LL.GmAgreeOutside(gm1, gm2, S)
    ensures LL.GmAgreeOutside(ApplyPath(p, idx, gm1), ApplyPath(p, idx, gm2), S)
    decreases |p|
  {
    if |p| > 0 {
      LL.GMUpdateAgreeOutside(p[0], idx, gm1, gm2, S);
      ApplyPathFrame(p[1..], idx, LG.GMUpdate(p[0], idx, gm1), LG.GMUpdate(p[0], idx, gm2), S);
    }
  }

  lemma LkActsInSTail(acts: LS.Actions, S: set<LG.GroupId>)
    requires |acts| > 0 && LL.LkActsInS(acts, S)
    ensures LL.LkActsInS(acts[1..], S)
  {
    forall i | 0 <= i < |acts[1..]| ensures acts[1..][i].Areg? ==> LL.LkBodiesInS(acts[1..][i].r, S)
    { assert acts[1..][i] == acts[i + 1]; }
  }

  lemma LkActsInSCons2(x: LS.Action, y: LS.Action, cont: LS.Actions, S: set<LG.GroupId>)
    requires (x.Areg? ==> LL.LkBodiesInS(x.r, S)) && (y.Areg? ==> LL.LkBodiesInS(y.r, S)) && LL.LkActsInS(cont, S)
    ensures LL.LkActsInS([x, y] + cont, S)
  {
    LL.LkActsInSCons(y, cont, S);
    LL.LkActsInSCons(x, [y] + cont, S);
    assert [x, y] + cont == [x] + ([y] + cont);
  }

  lemma PikeRecCons2(x: LS.Action, y: LS.Action, cont: LS.Actions)
    requires EL.PikeLkActionRec(x) && EL.PikeLkActionRec(y) && EL.PikeLkActionsRec(cont)
    ensures EL.PikeLkActionsRec([x, y] + cont)
  {
    EL.PikeLkActionsRecConsIff(y, cont);
    EL.PikeLkActionsRecConsIff(x, [y] + cont);
    assert [x, y] + cont == [x] + ([y] + cont);
  }

  /** A forward strict suffix has a strictly longer consumed prefix, so an input is
      never a strict suffix of itself. */
  lemma StrictSuffixFwdLen(inp: LC.Input, next: seq<char>, pref: seq<char>)
    requires |pref| >= |inp.pref|
    ensures !SS.StrictSuffixForward(inp, next, pref)
    decreases |next|
  {
    if |next| > 0 {
      StrictSuffixFwdLen(inp, next[1..], [next[0]] + pref);
    }
  }

  lemma NotStrictSuffixSelf(inp: LC.Input)
    ensures !SS.IsStrictSuffix(inp, inp, WP.Forward)
    ensures !SS.StrictSuffix(inp, inp, WP.Forward)
  {
    StrictSuffixFwdLen(inp, inp.next, inp.pref);
    SS.IsStrictSuffixCorrect(inp, inp, WP.Forward);
  }

  /** An empty path through `[Areg(r)] + cont` needs an empty path through `cont`. */
  lemma EmptyPathNeedsCont(rer: LW.RegExpRecord, r: L.Regex, cont: LS.Actions, inp: LC.Input)
    requires FirstEmptyPathA(rer, [LS.Areg(r)] + cont, inp).Some?
    ensures FirstEmptyPathA(rer, cont, inp).Some?
    decreases FS.ActionsFuel([LS.Areg(r)] + cont, inp, WP.Forward)
  {
    var acts := [LS.Areg(r)] + cont;
    assert acts[0] == LS.Areg(r) && acts[1..] == cont;
    match r
    case Epsilon =>
    case Character(_) =>
    case Disjunction(r1, r2) =>
      FS.DisjunctionLeftTermination(cont, inp, WP.Forward, r1, r2);
      FS.DisjunctionRightTermination(cont, inp, WP.Forward, r1, r2);
      if FirstEmptyPathA(rer, [LS.Areg(r1)] + cont, inp).Some? {
        EmptyPathNeedsCont(rer, r1, cont, inp);
      } else {
        EmptyPathNeedsCont(rer, r2, cont, inp);
      }
    case Sequence(r1, r2) =>
      FS.SequenceTermination(cont, inp, WP.Forward, r1, r2);
      assert LS.SeqList(r1, r2, WP.Forward) == [LS.Areg(r1), LS.Areg(r2)];
      FS.ActionsFuelConsAreg(r1, [LS.Areg(r2)] + cont, inp, WP.Forward);
      assert [LS.Areg(r1), LS.Areg(r2)] + cont == [LS.Areg(r1)] + ([LS.Areg(r2)] + cont);
      EmptyPathNeedsCont(rer, r1, [LS.Areg(r2)] + cont, inp);
      EmptyPathNeedsCont(rer, r2, cont, inp);
    case Quantified(greedy, min, delta, r1) =>
      if min > 0 {
        FS.QuantForcedTermination(cont, inp, WP.Forward, r1, min - 1, delta, greedy);
        var q := L.Quantified(greedy, min - 1, delta, r1);
        FS.ActionsFuelConsAreg(r1, [LS.Areg(q)] + cont, inp, WP.Forward);
        assert [LS.Areg(r1), LS.Areg(q)] + cont == [LS.Areg(r1)] + ([LS.Areg(q)] + cont);
        EmptyPathNeedsCont(rer, r1, [LS.Areg(q)] + cont, inp);
        EmptyPathNeedsCont(rer, q, cont, inp);
      }
    case Group(gid, r1) =>
      FS.GroupTermination(cont, inp, WP.Forward, r1, gid);
      FS.ActionsFuelConsAreg(r1, [LS.Aclose(gid)] + cont, inp, WP.Forward);
      assert [LS.Areg(r1), LS.Aclose(gid)] + cont == [LS.Areg(r1)] + ([LS.Aclose(gid)] + cont);
      EmptyPathNeedsCont(rer, r1, [LS.Aclose(gid)] + cont, inp);
      assert ([LS.Aclose(gid)] + cont)[1..] == cont;
    case AnchorR(_) =>
    case LookaroundR(_, _) =>
    case Backreference(_) =>
  }

  /** THE leaf characterization. For an `IsTree` tree of a fragment action stack at
      `(inp, gm)` (forward): every leaf sits at or after `inp`, a leaf at `inp`'s index
      IS `inp`; there is a leaf at `inp` iff the stack has an empty path; and the FIRST
      such leaf's map is the path's fold — outside the look-confined groups `S`. */
  lemma EmptyLeavesA(rer: LW.RegExpRecord, acts: LS.Actions, inp: LC.Input, gm: LG.GroupMap,
                     S: set<LG.GroupId>, t: LT.Tree)
    requires EL.PikeLkActionsRec(acts)
    requires LL.LkActsInS(acts, S)
    requires LS.IsTree(rer, acts, inp, gm, WP.Forward, t)
    ensures var ls := LT.TreeLeaves(t, gm, inp, WP.Forward);
            var p := FirstEmptyPathA(rer, acts, inp);
            (forall i :: 0 <= i < |ls| ==> ls[i].0 == inp || SS.StrictSuffix(ls[i].0, inp, WP.Forward))
            && (FirstAt(ls, inp).Some? <==> p.Some?)
            && (p.Some? ==> FirstAt(ls, inp).Some? && FirstAt(ls, inp).value < |ls|
                            && LL.GmAgreeOutside(ls[FirstAt(ls, inp).value].1, ApplyPath(p.value, LC.Idx(inp), gm), S))
    decreases FS.ActionsFuel(acts, inp, WP.Forward)
  {
    var ls := LT.TreeLeaves(t, gm, inp, WP.Forward);
    var p := FirstEmptyPathA(rer, acts, inp);
    var idx := LC.Idx(inp);
    FirstAtSpec(ls, inp);
    if |acts| == 0 {
      assert t == LT.Match;
      assert ls == [(inp, gm)];
      assert FirstAt(ls, inp) == Some(0);
      LL.GmAgreeOutsideRefl(gm, S);
      return;
    }
    var cont := acts[1..];
    assert acts == [acts[0]] + cont;
    EL.PikeLkActionsRecTail(acts);
    LkActsInSTail(acts, S);
    match acts[0] {
      case Acheck(strcheck) =>
        SS.IsStrictSuffixCorrect(inp, strcheck, WP.Forward);
        if SS.IsStrictSuffix(inp, strcheck, WP.Forward) {
          FS.CheckTermination(cont, inp, strcheck, WP.Forward);
          var tc := t.t;
          assert LS.IsTree(rer, cont, inp, gm, WP.Forward, tc);
          EmptyLeavesA(rer, cont, inp, gm, S, tc);
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
        EmptyLeavesA(rer, cont, inp, gm2, S, tc);
        assert ls == LT.TreeLeaves(tc, gm2, inp, WP.Forward);
        if p.Some? {
          var p' := FirstEmptyPathA(rer, cont, inp).value;
          assert p.value == [LG.Close(gid)] + p';
          assert ApplyPath(p.value, idx, gm) == ApplyPath(p', idx, gm2);
        }
      case Areg(r) =>
        EL.PikeLkActionsRecConsIff(LS.Areg(r), cont);
        assert EL.PikeLkRegexRec(r);
        assert LL.LkBodiesInS(r, S);
        match r {
          case Epsilon =>
            FS.EpsilonTermination(cont, inp, WP.Forward);
            EmptyLeavesA(rer, cont, inp, gm, S, t);
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
                EmptyLeavesA(rer, cont, nexti, gm, S, tc);
                assert ls == LT.TreeLeaves(tc, gm, nexti, WP.Forward);
                forall i | 0 <= i < |ls| ensures SS.StrictSuffix(ls[i].0, inp, WP.Forward) && ls[i].0 != inp {
                  if ls[i].0 != nexti { SS.StrictSuffixTrans(ls[i].0, nexti, inp, WP.Forward); }
                  SS.SSNeq(ls[i].0, inp, WP.Forward);
                }
                assert FirstAt(ls, inp).None?;
            }
          case Disjunction(r1, r2) =>
            FS.DisjunctionLeftTermination(cont, inp, WP.Forward, r1, r2);
            FS.DisjunctionRightTermination(cont, inp, WP.Forward, r1, r2);
            var ta := t.t1;
            var tb := t.t2;
            EL.PikeLkActionsRecConsIff(LS.Areg(r1), cont);
            EL.PikeLkActionsRecConsIff(LS.Areg(r2), cont);
            LL.LkActsInSCons(LS.Areg(r1), cont, S);
            LL.LkActsInSCons(LS.Areg(r2), cont, S);
            EmptyLeavesA(rer, [LS.Areg(r1)] + cont, inp, gm, S, ta);
            EmptyLeavesA(rer, [LS.Areg(r2)] + cont, inp, gm, S, tb);
            var la := LT.TreeLeaves(ta, gm, inp, WP.Forward);
            var lb := LT.TreeLeaves(tb, gm, inp, WP.Forward);
            assert ls == la + lb;
            FirstAtApp(la, lb, inp);
            var pa := FirstEmptyPathA(rer, [LS.Areg(r1)] + cont, inp);
            var pb := FirstEmptyPathA(rer, [LS.Areg(r2)] + cont, inp);
            forall i | 0 <= i < |ls|
              ensures ls[i].0 == inp || SS.StrictSuffix(ls[i].0, inp, WP.Forward)
            { if i < |la| { assert ls[i] == la[i]; } else { assert ls[i] == lb[i - |la|]; } }
            if pa.Some? {
              assert p == pa;
              var k := FirstAt(la, inp).value;
              assert FirstAt(ls, inp) == Some(k);
              assert ls[k] == la[k];
            } else {
              assert p == pb;
              assert FirstAt(la, inp).None?;
              if pb.Some? {
                var k := FirstAt(lb, inp).value;
                assert FirstAt(ls, inp) == Some(k + |la|);
                assert ls[k + |la|] == lb[k];
              }
            }
          case Sequence(r1, r2) =>
            FS.SequenceTermination(cont, inp, WP.Forward, r1, r2);
            assert LS.SeqList(r1, r2, WP.Forward) == [LS.Areg(r1), LS.Areg(r2)];
            PikeRecCons2(LS.Areg(r1), LS.Areg(r2), cont);
            LkActsInSCons2(LS.Areg(r1), LS.Areg(r2), cont, S);
            assert LS.IsTree(rer, [LS.Areg(r1), LS.Areg(r2)] + cont, inp, gm, WP.Forward, t);
            EmptyLeavesA(rer, [LS.Areg(r1), LS.Areg(r2)] + cont, inp, gm, S, t);
          case Quantified(greedy, min, delta, r1) =>
            var gidl := L.DefGroups(r1);
            if min > 0 {
              FS.QuantForcedTermination(cont, inp, WP.Forward, r1, min - 1, delta, greedy);
              var q := L.Quantified(greedy, min - 1, delta, r1);
              var tc := t.t;
              var gm2 := LG.GMReset(gidl, gm);
              assert gm2 == LG.GMUpdate(LG.Reset(gidl), idx, gm);
              PikeRecCons2(LS.Areg(r1), LS.Areg(q), cont);
              LkActsInSCons2(LS.Areg(r1), LS.Areg(q), cont, S);
              assert LS.IsTree(rer, [LS.Areg(r1), LS.Areg(q)] + cont, inp, gm2, WP.Forward, tc);
              EmptyLeavesA(rer, [LS.Areg(r1), LS.Areg(q)] + cont, inp, gm2, S, tc);
              assert ls == LT.TreeLeaves(tc, gm2, inp, WP.Forward);
              if p.Some? {
                var p' := FirstEmptyPathA(rer, [LS.Areg(r1), LS.Areg(q)] + cont, inp).value;
                assert p.value == [LG.Reset(gidl)] + p';
                assert ApplyPath(p.value, idx, gm) == ApplyPath(p', idx, gm2);
              }
            } else if delta == LN.NN(0) {
              FS.QuantDoneTermination(cont, inp, WP.Forward, r1, greedy);
              EmptyLeavesA(rer, cont, inp, gm, S, t);
            } else {
              FS.QuantFreeSkipTermination(cont, inp, WP.Forward, r1, greedy, delta);
              FS.QuantFreeIterTermination(cont, inp, WP.Forward, r1, greedy, delta);
              var plus := LN.NoISub(delta, 1);
              assert plus == FS.NoiPred(delta);
              var q := L.Quantified(greedy, 0, plus, r1);
              var iterActs := [LS.Areg(r1), LS.Acheck(inp), LS.Areg(q)] + cont;
              var itert := if greedy then t.t1 else t.t2;
              var skipt := if greedy then t.t2 else t.t1;
              var ti := itert.t;
              var gm2 := LG.GMReset(gidl, gm);
              assert LS.IsTree(rer, iterActs, inp, gm2, WP.Forward, ti);
              assert LS.IsTree(rer, cont, inp, gm, WP.Forward, skipt);
              // the iteration arm has no zero-width leaf
              var rest := [LS.Acheck(inp), LS.Areg(q)] + cont;
              assert iterActs == [LS.Areg(r1)] + rest;
              NotStrictSuffixSelf(inp);
              assert rest[0] == LS.Acheck(inp);
              assert FirstEmptyPathA(rer, rest, inp).None?;
              if FirstEmptyPathA(rer, iterActs, inp).Some? { EmptyPathNeedsCont(rer, r1, rest, inp); }
              assert FirstEmptyPathA(rer, iterActs, inp).None?;
              EL.PikeLkActionsRecConsIff(LS.Areg(q), cont);
              EL.PikeLkActionsRecConsIff(LS.Acheck(inp), [LS.Areg(q)] + cont);
              EL.PikeLkActionsRecConsIff(LS.Areg(r1), [LS.Acheck(inp)] + ([LS.Areg(q)] + cont));
              assert iterActs == [LS.Areg(r1)] + ([LS.Acheck(inp)] + ([LS.Areg(q)] + cont));
              LL.LkActsInSCons(LS.Areg(q), cont, S);
              LL.LkActsInSCons(LS.Acheck(inp), [LS.Areg(q)] + cont, S);
              LL.LkActsInSCons(LS.Areg(r1), [LS.Acheck(inp)] + ([LS.Areg(q)] + cont), S);
              EmptyLeavesA(rer, iterActs, inp, gm2, S, ti);
              EmptyLeavesA(rer, cont, inp, gm, S, skipt);
              var li := LT.TreeLeaves(ti, gm2, inp, WP.Forward);
              var lsk := LT.TreeLeaves(skipt, gm, inp, WP.Forward);
              assert LT.TreeLeaves(itert, gm, inp, WP.Forward) == li;
              assert FirstAt(li, inp).None?;
              if greedy {
                assert ls == li + lsk;
                FirstAtApp(li, lsk, inp);
                forall i | 0 <= i < |ls|
                  ensures ls[i].0 == inp || SS.StrictSuffix(ls[i].0, inp, WP.Forward)
                { if i < |li| { assert ls[i] == li[i]; } else { assert ls[i] == lsk[i - |li|]; } }
                if p.Some? {
                  var k := FirstAt(lsk, inp).value;
                  assert FirstAt(ls, inp) == Some(k + |li|);
                  assert ls[k + |li|] == lsk[k];
                }
              } else {
                assert ls == lsk + li;
                FirstAtApp(lsk, li, inp);
                forall i | 0 <= i < |ls|
                  ensures ls[i].0 == inp || SS.StrictSuffix(ls[i].0, inp, WP.Forward)
                { if i < |lsk| { assert ls[i] == lsk[i]; } else { assert ls[i] == li[i - |lsk|]; } }
                if p.Some? {
                  var k := FirstAt(lsk, inp).value;
                  assert FirstAt(ls, inp) == Some(k);
                  assert ls[k] == lsk[k];
                }
              }
            }
          case Group(gid, r1) =>
            FS.GroupTermination(cont, inp, WP.Forward, r1, gid);
            var tc := t.t;
            var gm2 := LG.GMOpen(idx, gid, gm);
            assert gm2 == LG.GMUpdate(LG.Open(gid), idx, gm);
            PikeRecCons2(LS.Areg(r1), LS.Aclose(gid), cont);
            LkActsInSCons2(LS.Areg(r1), LS.Aclose(gid), cont, S);
            assert LS.IsTree(rer, [LS.Areg(r1), LS.Aclose(gid)] + cont, inp, gm2, WP.Forward, tc);
            EmptyLeavesA(rer, [LS.Areg(r1), LS.Aclose(gid)] + cont, inp, gm2, S, tc);
            assert ls == LT.TreeLeaves(tc, gm2, inp, WP.Forward);
            if p.Some? {
              var p' := FirstEmptyPathA(rer, [LS.Areg(r1), LS.Aclose(gid)] + cont, inp).value;
              assert p.value == [LG.Open(gid)] + p';
              assert ApplyPath(p.value, idx, gm) == ApplyPath(p', idx, gm2);
            }
          case AnchorR(a) =>
            if LS.AnchorSatisfied(rer, a, inp) {
              FS.AnchorTermination(cont, inp, WP.Forward, a);
              var tc := t.t;
              assert LS.IsTree(rer, cont, inp, gm, WP.Forward, tc);
              EmptyLeavesA(rer, cont, inp, gm, S, tc);
              assert ls == LT.TreeLeaves(tc, gm, inp, WP.Forward);
            } else {
              assert t == LT.Mismatch;
            }
          case LookaroundR(lk, r1) =>
            FS.LkAfterTermination(cont, inp, WP.Forward, lk, r1);
            var ldir := L.LkDir(lk);
            // the body's tree is the same from any map (positive: fragment body;
            // negative: group-free body), so the gate's verdict is `LkVerdictL`
            if !L.Positivity(lk) {
              EL.GroupFreeLNoLkBr(r1);
              EL.NoLkBrLIsPikeLkRegexRec(r1);
            }
            assert EL.PikeLkRegexRec(r1);
            EL.ComputeTrGmIndepLkRec(rer, r1, inp, gm, ldir);
            var tlkE := FU.ComputeTr(rer, [LS.Areg(r1)], inp, LG.Empty, ldir);
            match t {
              case LK(lk2, tlk, tc) =>
                assert lk2 == lk;
                assert LS.IsTree(rer, [LS.Areg(r1)], inp, gm, ldir, tlk);
                FU.IsTreeEqComputeTr(rer, [LS.Areg(r1)], inp, gm, ldir, tlk);
                assert tlk == tlkE;
                assert LS.LkResult(lk, tlk, gm, inp).Some?;
                EL.LkResultGmIndep(lk, tlk, gm, inp);
                assert LkVerdictL(rer, lk, r1, inp);
                var gmlk := LS.LkResult(lk, tlk, gm, inp).value;
                assert LS.IsTree(rer, cont, inp, gmlk, WP.Forward, tc);
                // leaves of the gate node = leaves of the continuation from gmlk
                LT.FirstTreeLeaf(tlk, gm, inp, ldir);
                var sub := LT.TreeLeaves(tlk, gm, inp, ldir);
                if L.Positivity(lk) {
                  assert |sub| > 0 && gmlk == sub[0].1;
                  assert ls == LT.TreeLeaves(tc, gmlk, inp, WP.Forward);
                  // the body only writes `S` (its groups are in `S`)
                  assert LL.DefGroupsIn(r1, S);
                  LL.ComputeTrConfinedRec(rer, r1, inp, gm, ldir, S);
                  assert CE.LkConfinedTreeRec(tlk, S);
                  LL.GmConfinedLeavesRec(tlk, gm, inp, ldir, S);
                  assert LL.GmAgreeOutside(gmlk, gm, S);
                } else {
                  assert |sub| == 0 && gmlk == gm;
                  assert ls == LT.TreeLeaves(tc, gmlk, inp, WP.Forward);
                  LL.GmAgreeOutsideRefl(gm, S);
                }
                EmptyLeavesA(rer, cont, inp, gmlk, S, tc);
                if p.Some? {
                  assert p == FirstEmptyPathA(rer, cont, inp);
                  ApplyPathFrame(p.value, idx, gmlk, gm, S);
                  LL.GmAgreeOutsideTrans(ls[FirstAt(ls, inp).value].1, ApplyPath(p.value, idx, gmlk), ApplyPath(p.value, idx, gm), S);
                }
              case LKFail(lk2, tlk) =>
                assert lk2 == lk;
                assert LS.IsTree(rer, [LS.Areg(r1)], inp, gm, ldir, tlk);
                FU.IsTreeEqComputeTr(rer, [LS.Areg(r1)], inp, gm, ldir, tlk);
                assert tlk == tlkE;
                assert LS.LkResult(lk, tlk, gm, inp).None?;
                EL.LkResultGmIndep(lk, tlk, gm, inp);
                assert !LkVerdictL(rer, lk, r1, inp);
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
  // Helpers for the priority theorem: flat-map algebra, the virtual chain,
  // path/group containment, gm-independence of fragment trees.
  // ===========================================================================

  /** Converse of `FM.FlatMapApp`: a flat-map over a concatenation splits. */
  lemma FlatMapSplit(l1: seq<LT.Leaf>, l2: seq<LT.Leaf>, f: (LT.Leaf, seq<LT.Leaf>) -> bool, R: seq<LT.Leaf>)
    requires FM.FlatMapRel(l1 + l2, f, R)
    ensures exists R1, R2 :: FM.FlatMapRel(l1, f, R1) && FM.FlatMapRel(l2, f, R2) && R == R1 + R2
    decreases |l1|
  {
    if |l1| == 0 {
      assert l1 + l2 == l2;
      assert FM.FlatMapRel(l1, f, []);
      assert R == [] + R;
    } else {
      var l := l1 + l2;
      assert l[0] == l1[0] && l[1..] == l1[1..] + l2;
      var ly, rest :| f(l[0], ly) && FM.FlatMapRel(l[1..], f, rest) && R == ly + rest;
      FlatMapSplit(l1[1..], l2, f, rest);
      var R1', R2 :| FM.FlatMapRel(l1[1..], f, R1') && FM.FlatMapRel(l2, f, R2) && rest == R1' + R2;
      assert FM.FlatMapRel(l1, f, ly + R1');
      assert R == (ly + R1') + R2;
    }
  }

  /** A deterministic flat-map has a unique image. */
  lemma FlatMapDetermRel(l: seq<LT.Leaf>, f: (LT.Leaf, seq<LT.Leaf>) -> bool, R1: seq<LT.Leaf>, R2: seq<LT.Leaf>)
    requires FM.Determ(f)
    requires FM.FlatMapRel(l, f, R1) && FM.FlatMapRel(l, f, R2)
    ensures R1 == R2
    decreases |l|
  {
    if |l| > 0 {
      var y1, r1 :| f(l[0], y1) && FM.FlatMapRel(l[1..], f, r1) && R1 == y1 + r1;
      var y2, r2 :| f(l[0], y2) && FM.FlatMapRel(l[1..], f, r2) && R2 == y2 + r2;
      assert y1 == y2;
      FlatMapDetermRel(l[1..], f, r1, r2);
    }
  }

  /** Two flat-maps whose functions agree on every element of the base have equal images. */
  lemma FlatMapEqOn(l: seq<LT.Leaf>, f: (LT.Leaf, seq<LT.Leaf>) -> bool, g: (LT.Leaf, seq<LT.Leaf>) -> bool,
                    Rf: seq<LT.Leaf>, Rg: seq<LT.Leaf>)
    requires FM.Determ(f)
    requires forall i, y :: 0 <= i < |l| && g(l[i], y) ==> f(l[i], y)
    requires FM.FlatMapRel(l, f, Rf) && FM.FlatMapRel(l, g, Rg)
    ensures Rf == Rg
    decreases |l|
  {
    if |l| > 0 {
      var yf, rf :| f(l[0], yf) && FM.FlatMapRel(l[1..], f, rf) && Rf == yf + rf;
      var yg, rg :| g(l[0], yg) && FM.FlatMapRel(l[1..], g, rg) && Rg == yg + rg;
      assert f(l[0], yg);
      assert yf == yg;
      forall i, y | 0 <= i < |l[1..]| && g(l[1..][i], y) ensures f(l[1..][i], y) { assert l[1..][i] == l[i + 1]; }
      FlatMapEqOn(l[1..], f, g, rf, rg);
    }
  }

  /** A flat-map whose every chunk is empty is empty. */
  lemma FlatMapAllEmpty(l: seq<LT.Leaf>, f: (LT.Leaf, seq<LT.Leaf>) -> bool, R: seq<LT.Leaf>)
    requires forall i, y :: 0 <= i < |l| && f(l[i], y) ==> y == []
    requires FM.FlatMapRel(l, f, R)
    ensures R == []
    decreases |l|
  {
    if |l| > 0 {
      var y, rest :| f(l[0], y) && FM.FlatMapRel(l[1..], f, rest) && R == y + rest;
      forall i, y' | 0 <= i < |l[1..]| && f(l[1..][i], y') ensures y' == [] { assert l[1..][i] == l[i + 1]; }
      FlatMapAllEmpty(l[1..], f, rest);
    }
  }

  /** The virtual chain: a path's group actions as nested `GroupActionT` nodes. */
  ghost function Chain(p: seq<LG.GroupAction>, t: LT.Tree): LT.Tree
    decreases |p|
  {
    if |p| == 0 then t else LT.GroupActionT(p[0], Chain(p[1..], t))
  }

  lemma ChainLeaves(p: seq<LG.GroupAction>, t: LT.Tree, gm: LG.GroupMap, inp: LC.Input)
    ensures LT.TreeLeaves(Chain(p, t), gm, inp, WP.Forward) == LT.TreeLeaves(t, ApplyPath(p, LC.Idx(inp), gm), inp, WP.Forward)
    decreases |p|
  {
    if |p| > 0 { ChainLeaves(p[1..], t, LG.GMUpdate(p[0], LC.Idx(inp), gm), inp); }
  }

  /** Every group an action stack can touch. */
  ghost predicate ActsGroupsIn(acts: LS.Actions, G: set<LG.GroupId>) {
    forall i :: 0 <= i < |acts| ==>
      (acts[i].Areg? ==> forall g :: g in L.DefGroups(acts[i].r) ==> g in G)
      && (acts[i].Aclose? ==> acts[i].gid in G)
  }

  lemma ActsGroupsInTail(acts: LS.Actions, G: set<LG.GroupId>)
    requires |acts| > 0 && ActsGroupsIn(acts, G)
    ensures ActsGroupsIn(acts[1..], G)
  {
    forall i | 0 <= i < |acts[1..]| ensures (acts[1..][i].Areg? ==> forall g :: g in L.DefGroups(acts[1..][i].r) ==> g in G)
                                          && (acts[1..][i].Aclose? ==> acts[1..][i].gid in G)
    { assert acts[1..][i] == acts[i + 1]; }
  }

  lemma ActsGroupsInCons(x: LS.Action, cont: LS.Actions, G: set<LG.GroupId>)
    requires (x.Areg? ==> forall g :: g in L.DefGroups(x.r) ==> g in G) && (x.Aclose? ==> x.gid in G)
    requires ActsGroupsIn(cont, G)
    ensures ActsGroupsIn([x] + cont, G)
  {
    forall i | 0 <= i < |[x] + cont|
      ensures (([x] + cont)[i].Areg? ==> forall g :: g in L.DefGroups(([x] + cont)[i].r) ==> g in G)
              && (([x] + cont)[i].Aclose? ==> ([x] + cont)[i].gid in G)
    { if i > 0 { assert ([x] + cont)[i] == cont[i - 1]; } }
  }

  ghost predicate PathIn(p: seq<LG.GroupAction>, G: set<LG.GroupId>) {
    forall i :: 0 <= i < |p| ==> CE.GmActionIn(p[i], G)
  }

  /** The first empty path only touches the stack's groups. */
  lemma PathActionsIn(rer: LW.RegExpRecord, acts: LS.Actions, inp: LC.Input, G: set<LG.GroupId>)
    requires ActsGroupsIn(acts, G)
    requires FirstEmptyPathA(rer, acts, inp).Some?
    ensures PathIn(FirstEmptyPathA(rer, acts, inp).value, G)
    decreases FS.ActionsFuel(acts, inp, WP.Forward)
  {
    if |acts| == 0 { return; }
    var cont := acts[1..];
    assert acts == [acts[0]] + cont;
    ActsGroupsInTail(acts, G);
    match acts[0] {
      case Acheck(strcheck) =>
        SS.IsStrictSuffixCorrect(inp, strcheck, WP.Forward);
        FS.CheckTermination(cont, inp, strcheck, WP.Forward);
        PathActionsIn(rer, cont, inp, G);
      case Aclose(gid) =>
        FS.CloseTermination(cont, inp, WP.Forward, gid);
        PathActionsIn(rer, cont, inp, G);
        var p' := FirstEmptyPathA(rer, cont, inp).value;
        forall i | 0 <= i < |[LG.Close(gid)] + p'| ensures CE.GmActionIn(([LG.Close(gid)] + p')[i], G)
        { if i > 0 { assert ([LG.Close(gid)] + p')[i] == p'[i - 1]; } }
      case Areg(r) =>
        assert forall g :: g in L.DefGroups(r) ==> g in G;
        match r {
          case Epsilon =>
            FS.EpsilonTermination(cont, inp, WP.Forward);
            PathActionsIn(rer, cont, inp, G);
          case Character(_) =>
          case Disjunction(r1, r2) =>
            FS.DisjunctionLeftTermination(cont, inp, WP.Forward, r1, r2);
            FS.DisjunctionRightTermination(cont, inp, WP.Forward, r1, r2);
            ActsGroupsInCons(LS.Areg(r1), cont, G);
            ActsGroupsInCons(LS.Areg(r2), cont, G);
            if FirstEmptyPathA(rer, [LS.Areg(r1)] + cont, inp).Some? {
              PathActionsIn(rer, [LS.Areg(r1)] + cont, inp, G);
            } else {
              PathActionsIn(rer, [LS.Areg(r2)] + cont, inp, G);
            }
          case Sequence(r1, r2) =>
            FS.SequenceTermination(cont, inp, WP.Forward, r1, r2);
            assert LS.SeqList(r1, r2, WP.Forward) == [LS.Areg(r1), LS.Areg(r2)];
            ActsGroupsInCons(LS.Areg(r2), cont, G);
            ActsGroupsInCons(LS.Areg(r1), [LS.Areg(r2)] + cont, G);
            assert [LS.Areg(r1), LS.Areg(r2)] + cont == [LS.Areg(r1)] + ([LS.Areg(r2)] + cont);
            PathActionsIn(rer, [LS.Areg(r1), LS.Areg(r2)] + cont, inp, G);
          case Quantified(greedy, min, delta, r1) =>
            var gidl := L.DefGroups(r1);
            if min > 0 {
              FS.QuantForcedTermination(cont, inp, WP.Forward, r1, min - 1, delta, greedy);
              var q := L.Quantified(greedy, min - 1, delta, r1);
              ActsGroupsInCons(LS.Areg(q), cont, G);
              ActsGroupsInCons(LS.Areg(r1), [LS.Areg(q)] + cont, G);
              assert [LS.Areg(r1), LS.Areg(q)] + cont == [LS.Areg(r1)] + ([LS.Areg(q)] + cont);
              PathActionsIn(rer, [LS.Areg(r1), LS.Areg(q)] + cont, inp, G);
              var p' := FirstEmptyPathA(rer, [LS.Areg(r1), LS.Areg(q)] + cont, inp).value;
              assert CE.GmActionIn(LG.Reset(gidl), G);
              forall i | 0 <= i < |[LG.Reset(gidl)] + p'| ensures CE.GmActionIn(([LG.Reset(gidl)] + p')[i], G)
              { if i > 0 { assert ([LG.Reset(gidl)] + p')[i] == p'[i - 1]; } }
            } else {
              FS.QuantFreeSkipTermination(cont, inp, WP.Forward, r1, greedy, delta);
              PathActionsIn(rer, cont, inp, G);
            }
          case Group(gid, r1) =>
            FS.GroupTermination(cont, inp, WP.Forward, r1, gid);
            ActsGroupsInCons(LS.Aclose(gid), cont, G);
            ActsGroupsInCons(LS.Areg(r1), [LS.Aclose(gid)] + cont, G);
            assert [LS.Areg(r1), LS.Aclose(gid)] + cont == [LS.Areg(r1)] + ([LS.Aclose(gid)] + cont);
            PathActionsIn(rer, [LS.Areg(r1), LS.Aclose(gid)] + cont, inp, G);
            var p' := FirstEmptyPathA(rer, [LS.Areg(r1), LS.Aclose(gid)] + cont, inp).value;
            forall i | 0 <= i < |[LG.Open(gid)] + p'| ensures CE.GmActionIn(([LG.Open(gid)] + p')[i], G)
            { if i > 0 { assert ([LG.Open(gid)] + p')[i] == p'[i - 1]; } }
          case AnchorR(a) =>
            FS.AnchorTermination(cont, inp, WP.Forward, a);
            PathActionsIn(rer, cont, inp, G);
          case LookaroundR(lk, r1) =>
            FS.LkAfterTermination(cont, inp, WP.Forward, lk, r1);
            PathActionsIn(rer, cont, inp, G);
          case Backreference(_) =>
        }
    }
  }

  /** Actions inside `G` leave the map unchanged outside `G`. */
  lemma ApplyPathOutside(p: seq<LG.GroupAction>, idx: nat, gm: LG.GroupMap, G: set<LG.GroupId>)
    requires PathIn(p, G)
    ensures LL.GmAgreeOutside(ApplyPath(p, idx, gm), gm, G)
    decreases |p|
  {
    if |p| > 0 {
      var gm1 := LG.GMUpdate(p[0], idx, gm);
      assert LL.GmAgreeOutside(gm1, gm, G) by {
        match p[0]
        case Open(g) =>
        case Close(g) =>
        case Reset(gs) =>
      }
      forall i | 0 <= i < |p[1..]| ensures CE.GmActionIn(p[1..][i], G) { assert p[1..][i] == p[i + 1]; }
      ApplyPathOutside(p[1..], idx, gm1, G);
      LL.GmAgreeOutsideTrans(ApplyPath(p, idx, gm), gm1, gm, G);
    }
  }

  /** Fragment trees do not depend on the incoming map. */
  lemma IsTreeGmIndep(rer: LW.RegExpRecord, acts: LS.Actions, inp: LC.Input, gm1: LG.GroupMap, gm2: LG.GroupMap,
                      t1: LT.Tree, t2: LT.Tree)
    requires EL.PikeLkActionsRec(acts)
    requires LS.IsTree(rer, acts, inp, gm1, WP.Forward, t1)
    requires LS.IsTree(rer, acts, inp, gm2, WP.Forward, t2)
    ensures t1 == t2
  {
    var fuel := FS.ActionsFuel(acts, inp, WP.Forward) + 1;
    FU.IsTreeEqComputeTr(rer, acts, inp, gm1, WP.Forward, t1);
    FU.IsTreeEqComputeTr(rer, acts, inp, gm2, WP.Forward, t2);
    EL.ComputeTreeGmIndepLkRec(rer, acts, inp, gm1, gm2, WP.Forward, fuel);
  }

  // ===========================================================================
  // THE PRIORITY THEOREM (spec-level): the engine's CIN-greedy shape
  //   T_cin = Choice(Reset(gidl); T_iter, Reset(gidl); Chain(first empty path); T_cont)
  // has the same first result as the spec's forced-iteration tree of `r1+`,
  // outside the look-confined groups S.
  // ===========================================================================

  /** Leaf-list length does not depend on the incoming map. */
  lemma TreeLeavesLenIndep(t: LT.Tree, gm1: LG.GroupMap, gm2: LG.GroupMap, inp: LC.Input)
    ensures |LT.TreeLeaves(t, gm1, inp, WP.Forward)| == |LT.TreeLeaves(t, gm2, inp, WP.Forward)|
  {
    var S := gm1.Keys + gm2.Keys;
    assert LL.GmAgreeOutside(gm1, gm2, S);
    LL.TreeLeavesFrameOutside(t, gm1, gm2, inp, WP.Forward, S);
  }

  /** A deterministic flat-map with an empty image has only empty chunks. */
  lemma FlatMapEmptyChunks(l: seq<LT.Leaf>, f: (LT.Leaf, seq<LT.Leaf>) -> bool)
    requires FM.Determ(f)
    requires FM.FlatMapRel(l, f, [])
    ensures forall i, y :: 0 <= i < |l| && f(l[i], y) ==> y == []
    decreases |l|
  {
    if |l| > 0 {
      var y0, rest :| f(l[0], y0) && FM.FlatMapRel(l[1..], f, rest) && [] == y0 + rest;
      assert y0 == [] && rest == [];
      FlatMapEmptyChunks(l[1..], f);
      forall i, y | 0 <= i < |l| && f(l[i], y) ensures y == [] {
        if i == 0 { assert y == y0; } else { assert l[i] == l[1..][i - 1]; }
      }
    }
  }

  /** Maps agreeing outside a group list reset to the same map. */
  lemma GMResetAgree(gidl: seq<LG.GroupId>, a: LG.GroupMap, b: LG.GroupMap)
    requires LL.GmAgreeOutside(a, b, set g | g in gidl)
    ensures LG.GMReset(gidl, a) == LG.GMReset(gidl, b)
  {
    var ra := LG.GMReset(gidl, a);
    var rb := LG.GMReset(gidl, b);
    forall g ensures g in ra <==> g in rb { }
    forall g | g in ra ensures ra[g] == rb[g] { }
    assert ra == rb;
  }

  /** The check chunk: past `inp` the `Acheck(inp)` is a pass-through; at `inp` it kills. */
  lemma ChkChunk(rer: LW.RegExpRecord, rest: LS.Actions, inp: LC.Input, l: LT.Leaf, y: seq<LT.Leaf>)
    ensures SS.StrictSuffix(l.0, inp, WP.Forward) ==>
              (EQ.ActFromLeafFn(rer, [LS.Acheck(inp)] + rest, WP.Forward)(l, y)
               <==> EQ.ActFromLeafFn(rer, rest, WP.Forward)(l, y))
    ensures l.0 == inp && EQ.ActFromLeafFn(rer, [LS.Acheck(inp)] + rest, WP.Forward)(l, y) ==> y == []
  {
    var chk := [LS.Acheck(inp)] + rest;
    assert chk[0] == LS.Acheck(inp) && chk[1..] == rest;
    if SS.StrictSuffix(l.0, inp, WP.Forward) {
      if EQ.ActFromLeafFn(rer, chk, WP.Forward)(l, y) {
        var t' :| LS.IsTree(rer, chk, l.0, l.1, WP.Forward, t') && y == LT.TreeLeaves(t', l.1, l.0, WP.Forward);
        assert t'.Progress?;
        var t'' := t'.t;
        assert LS.IsTree(rer, rest, l.0, l.1, WP.Forward, t'');
        assert y == LT.TreeLeaves(t'', l.1, l.0, WP.Forward);
        assert EQ.ActFromLeaf(rer, rest, WP.Forward, l, y);
      }
      if EQ.ActFromLeafFn(rer, rest, WP.Forward)(l, y) {
        var t'' :| LS.IsTree(rer, rest, l.0, l.1, WP.Forward, t'') && y == LT.TreeLeaves(t'', l.1, l.0, WP.Forward);
        assert LS.IsTree(rer, chk, l.0, l.1, WP.Forward, LT.Progress(t''));
        assert EQ.ActFromLeaf(rer, chk, WP.Forward, l, y);
      }
    }
    if l.0 == inp && EQ.ActFromLeafFn(rer, chk, WP.Forward)(l, y) {
      var t' :| LS.IsTree(rer, chk, l.0, l.1, WP.Forward, t') && y == LT.TreeLeaves(t', l.1, l.0, WP.Forward);
      NotStrictSuffixSelf(inp);
      assert t' == LT.Mismatch;
    }
  }

  /** The chunk of the star continuation at an EMPTY leaf: the (map-independent)
      iteration tree from the reset map, then the (map-independent) continuation. */
  lemma EmptyLeafChunk(rer: LW.RegExpRecord, r1: L.Regex, cont: LS.Actions, inp: LC.Input,
                       l: LT.Leaf, y: seq<LT.Leaf>, titer: LT.Tree, tcont: LT.Tree, gmI: LG.GroupMap, gmC: LG.GroupMap)
    requires EL.PikeLkRegexRec(r1) && EL.PikeLkActionsRec(cont)
    requires l.0 == inp
    requires LS.IsTree(rer, [LS.Areg(r1), LS.Acheck(inp), LS.Areg(L.Quantified(true, 0, LN.Inf, r1))] + cont, inp, gmI, WP.Forward, titer)
    requires LS.IsTree(rer, cont, inp, gmC, WP.Forward, tcont)
    requires EQ.ActFromLeafFn(rer, [LS.Areg(L.Quantified(true, 0, LN.Inf, r1))] + cont, WP.Forward)(l, y)
    ensures y == LT.TreeLeaves(titer, LG.GMReset(L.DefGroups(r1), l.1), inp, WP.Forward)
              + LT.TreeLeaves(tcont, l.1, inp, WP.Forward)
  {
    var gidl := L.DefGroups(r1);
    var Q0 := L.Quantified(true, 0, LN.Inf, r1);
    var rest := [LS.Areg(Q0)] + cont;
    var iterActs := [LS.Areg(r1), LS.Acheck(inp), LS.Areg(Q0)] + cont;
    assert rest[0] == LS.Areg(Q0) && rest[1..] == cont;
    var te :| LS.IsTree(rer, rest, inp, l.1, WP.Forward, te) && y == LT.TreeLeaves(te, l.1, inp, WP.Forward);
    // tree_quant_free, greedy
    assert LN.NoISub(LN.Inf, 1) == LN.Inf;
    assert te.Choice?;
    var itert := te.t1;
    var skipt := te.t2;
    assert itert.GroupActionT? && itert.g == LG.Reset(gidl);
    var tie := itert.t;
    assert LS.IsTree(rer, iterActs, inp, LG.GMReset(gidl, l.1), WP.Forward, tie);
    assert LS.IsTree(rer, cont, inp, l.1, WP.Forward, skipt);
    // fragment facts
    EL.PikeLkActionsRecConsIff(LS.Areg(Q0), cont);
    EL.PikeLkActionsRecConsIff(LS.Acheck(inp), [LS.Areg(Q0)] + cont);
    EL.PikeLkActionsRecConsIff(LS.Areg(r1), [LS.Acheck(inp)] + ([LS.Areg(Q0)] + cont));
    assert iterActs == [LS.Areg(r1)] + ([LS.Acheck(inp)] + ([LS.Areg(Q0)] + cont));
    assert EL.PikeLkActionsRec(iterActs);
    IsTreeGmIndep(rer, iterActs, inp, LG.GMReset(gidl, l.1), gmI, tie, titer);
    IsTreeGmIndep(rer, cont, inp, l.1, gmC, skipt, tcont);
    assert LT.TreeLeaves(te, l.1, inp, WP.Forward)
        == LT.TreeLeaves(itert, l.1, inp, WP.Forward) + LT.TreeLeaves(skipt, l.1, inp, WP.Forward);
    assert LT.TreeLeaves(itert, l.1, inp, WP.Forward) == LT.TreeLeaves(tie, LG.GMReset(gidl, l.1), inp, WP.Forward);
  }

  lemma SetOfSeqMem(gidl: seq<LG.GroupId>, g: LG.GroupId)
    ensures g in (set x | x in gidl) <==> g in gidl
  {}

  /** THE PRIORITY THEOREM. */
  lemma CinPlusPriority(rer: LW.RegExpRecord, r1: L.Regex, cont: LS.Actions, inp: LC.Input, gm: LG.GroupMap,
                        S: set<LG.GroupId>, tplus: LT.Tree, titer: LT.Tree, tcont: LT.Tree)
    requires EL.PikeLkRegexRec(r1) && EL.PikeLkActionsRec(cont)
    requires LL.LkBodiesInS(r1, S) && LL.LkActsInS(cont, S)
    requires NUL.CINullableL(r1)
    requires LS.IsTree(rer, [LS.Areg(L.Quantified(true, 1, LN.Inf, r1))] + cont, inp, gm, WP.Forward, tplus)
    requires LS.IsTree(rer, [LS.Areg(r1), LS.Acheck(inp), LS.Areg(L.Quantified(true, 0, LN.Inf, r1))] + cont,
                       inp, LG.GMReset(L.DefGroups(r1), gm), WP.Forward, titer)
    requires LS.IsTree(rer, cont, inp, gm, WP.Forward, tcont)
    ensures FirstEmptyPathL(rer, r1, inp).Some?
    ensures var gidl := L.DefGroups(r1);
            var p := FirstEmptyPathL(rer, r1, inp).value;
            var tcin := LT.Choice(LT.GroupActionT(LG.Reset(gidl), titer),
                                  LT.GroupActionT(LG.Reset(gidl), Chain(p, tcont)));
            var rc := LT.TreeRes(tcin, gm, inp, WP.Forward);
            var rp := LT.TreeRes(tplus, gm, inp, WP.Forward);
            (rc.Some? <==> rp.Some?)
            && (rc.Some? ==> rc.value.0 == rp.value.0 && LL.GmAgreeOutside(rc.value.1, rp.value.1, S))
  {
    var gidl := L.DefGroups(r1);
    var Gset := set g | g in gidl;
    var gm' := LG.GMReset(gidl, gm);
    var idx := LC.Idx(inp);
    var Q1 := L.Quantified(true, 1, LN.Inf, r1);
    var Q0 := L.Quantified(true, 0, LN.Inf, r1);
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
    // ---- fragment facts for the sub-stacks ----
    EL.PikeLkActionsRecConsIff(LS.Areg(r1), []);
    assert EL.PikeLkActionsRec(A);
    EL.PikeLkActionsRecConsIff(LS.Areg(Q0), cont);
    assert EL.PikeLkActionsRec(rest);
    LL.LkActsInSCons(LS.Areg(r1), [], S);
    assert LL.LkActsInS(A, S);

    // ---- the first empty path of r1 ----
    assert A == [LS.Areg(r1)] + [];
    CINullableEmptyPathA(rer, r1, [], inp);
    var p := FirstEmptyPathL(rer, r1, inp).value;
    var gmP := ApplyPath(p, idx, gm');
    assert ActsGroupsIn(A, Gset) by {
      forall i | 0 <= i < |A| ensures (A[i].Areg? ==> forall g :: g in L.DefGroups(A[i].r) ==> g in Gset) && (A[i].Aclose? ==> A[i].gid in Gset) {}
    }
    PathActionsIn(rer, A, inp, Gset);
    ApplyPathOutside(p, idx, gm', Gset);
    GMResetAgree(gidl, gmP, gm');
    assert LG.GMReset(gidl, gm') == gm';
    assert LG.GMReset(gidl, gmP) == gm';

    assert {:split_here} true;
    // ---- r1's own tree and its leaves at gm' ----
    var tr1 := FU.ComputeTr(rer, A, inp, gm', WP.Forward);
    FU.ComputeTrIsTree(rer, A, inp, gm', WP.Forward);
    var ls := LT.TreeLeaves(tr1, gm', inp, WP.Forward);
    EmptyLeavesA(rer, A, inp, gm', S, tr1);
    FirstAtSpec(ls, inp);
    var e := FirstAt(ls, inp).value;
    var gme := ls[e].1;
    assert LL.GmAgreeOutside(gme, gmP, S);

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
    // ---- split both at the first empty leaf ----
    var pre := ls[..e];
    var post := ls[e + 1..];
    assert ls == pre + ([ls[e]] + post);
    FlatMapSplit(pre, [ls[e]] + post, frest, Lplus);
    var R1: seq<LT.Leaf>, R23: seq<LT.Leaf> :| FM.FlatMapRel(pre, frest, R1) && FM.FlatMapRel([ls[e]] + post, frest, R23) && Lplus == R1 + R23;
    FlatMapSplit([ls[e]], post, frest, R23);
    var R2: seq<LT.Leaf>, R3: seq<LT.Leaf> :| FM.FlatMapRel([ls[e]], frest, R2) && FM.FlatMapRel(post, frest, R3) && R23 == R2 + R3;
    FlatMapSplit(pre, [ls[e]] + post, fchk, I);
    var I1: seq<LT.Leaf>, I23: seq<LT.Leaf> :| FM.FlatMapRel(pre, fchk, I1) && FM.FlatMapRel([ls[e]] + post, fchk, I23) && I == I1 + I23;
    FlatMapSplit([ls[e]], post, fchk, I23);
    var I2: seq<LT.Leaf>, I3: seq<LT.Leaf> :| FM.FlatMapRel([ls[e]], fchk, I2) && FM.FlatMapRel(post, fchk, I3) && I23 == I2 + I3;
    // singleton flat-maps are single chunks
    assert frest(ls[e], R2) by {
      var ly, rst :| frest(([ls[e]])[0], ly) && FM.FlatMapRel(([ls[e]])[1..], frest, rst) && R2 == ly + rst;
      assert rst == [];
    }
    assert fchk(ls[e], I2) by {
      var ly, rst :| fchk(([ls[e]])[0], ly) && FM.FlatMapRel(([ls[e]])[1..], fchk, rst) && I2 == ly + rst;
      assert rst == [];
    }

    assert {:split_here} true;
    // ---- the consuming prefix agrees chunk by chunk ----
    forall i, y | 0 <= i < |pre| && fchk(pre[i], y) ensures frest(pre[i], y) {
      assert pre[i] == ls[i] && ls[i].0 != inp;
      ChkChunk(rer, rest, inp, ls[i], y);
    }
    FlatMapEqOn(pre, frest, fchk, R1, I1);
    assert R1 == I1;
    // ---- the empty leaf's check chunk is empty ----
    ChkChunk(rer, rest, inp, ls[e], I2);
    assert I2 == [];
    assert I2 + I3 == I3;
    assert I23 == I3;
    assert I == I1 + I3;
    assert {:split_here} true;
    // ---- the empty leaf's rest chunk: I (up to S) then the continuation ----
    EmptyLeafChunk(rer, r1, cont, inp, ls[e], R2, titer, tcont, gm', gm);
    var IE := LT.TreeLeaves(titer, LG.GMReset(gidl, gme), inp, WP.Forward);
    var CE' := LT.TreeLeaves(tcont, gme, inp, WP.Forward);
    assert R2 == IE + CE';
    var C := LT.TreeLeaves(tcont, gmP, inp, WP.Forward);
    // the frame facts, stated as the instances the head comparison needs
    assert |IE| == |I| && |CE'| == |C| by {
      LL.GMUpdateAgreeOutside(LG.Reset(gidl), idx, gme, gmP, S);
      LL.TreeLeavesFrameOutside(titer, LG.GMReset(gidl, gme), gm', inp, WP.Forward, S);
      LL.TreeLeavesFrameOutside(tcont, gme, gmP, inp, WP.Forward, S);
    }
    assert |IE| > 0 ==> IE[0].0 == I[0].0 && LL.GmAgreeOutside(IE[0].1, I[0].1, S) by {
      LL.GMUpdateAgreeOutside(LG.Reset(gidl), idx, gme, gmP, S);
      LL.TreeLeavesFrameOutside(titer, LG.GMReset(gidl, gme), gm', inp, WP.Forward, S);
    }
    assert |CE'| > 0 ==> CE'[0].0 == C[0].0 && LL.GmAgreeOutside(CE'[0].1, C[0].1, S) by {
      LL.TreeLeavesFrameOutside(tcont, gme, gmP, inp, WP.Forward, S);
    }

    assert {:split_here} true;
    // ---- the engine shape's leaves ----
    var tcin := LT.Choice(LT.GroupActionT(LG.Reset(gidl), titer), LT.GroupActionT(LG.Reset(gidl), Chain(p, tcont)));
    var Lcin := LT.TreeLeaves(tcin, gm, inp, WP.Forward);
    assert Lcin == I + C by {
      ChainLeaves(p, tcont, gm', inp);
      assert LG.GMUpdate(LG.Reset(gidl), idx, gm) == gm';
      assert LT.TreeLeaves(LT.GroupActionT(LG.Reset(gidl), titer), gm, inp, WP.Forward) == I;
      assert LT.TreeLeaves(LT.GroupActionT(LG.Reset(gidl), Chain(p, tcont)), gm, inp, WP.Forward)
          == LT.TreeLeaves(Chain(p, tcont), gm', inp, WP.Forward);
      assert LT.TreeLeaves(Chain(p, tcont), gm', inp, WP.Forward) == C;
    }

    assert {:split_here} true;
    // ---- heads ----
    var rc := LT.TreeRes(tcin, gm, inp, WP.Forward);
    var rp := LT.TreeRes(tplus, gm, inp, WP.Forward);
    assert rc == LT.HdError(Lcin) && rp == LT.HdError(Lplus) by {
      LT.FirstTreeLeaf(tcin, gm, inp, WP.Forward);
      LT.FirstTreeLeaf(tplus, gm, inp, WP.Forward);
    }
    assert R23 == R2 + R3 && R1 == I1;
    assert Lplus == I1 + (R2 + R3);
    assert (I1 + I3) + C == I1 + (I3 + C);
    assert Lcin == I1 + (I3 + C);
    assert {:split_here} true;
    if |I1| > 0 {
      assert Lplus[0] == I1[0] && Lcin[0] == I1[0];
      LL.GmAgreeOutsideRefl(I1[0].1, S);
    } else {
      assert Lplus == R2 + R3;
      assert Lcin == I3 + C;
      assert I == I3;
      assert |R2| == |I3 + C|;
      assert {:split_here} true;
      if |R2| > 0 {
        assert Lplus[0] == R2[0];
        assert Lcin[0] == (I3 + C)[0];
        if |IE| > 0 {
          assert R2[0] == IE[0] && (I3 + C)[0] == I3[0] && I3[0] == I[0];
        } else {
          assert R2[0] == CE'[0] && (I3 + C)[0] == C[0];
        }
      } else {
        assert |I3| == 0 && |C| == 0 && |IE| == 0 && |CE'| == 0;
        assert Lcin == [];
        assert {:split_here} true;
        // every remaining chunk is empty
        FlatMapEmptyChunks(post, fchk);
        forall i, y | 0 <= i < |post| && frest(post[i], y) ensures y == [] {
          var l := post[i];
          assert l == ls[e + 1 + i];
          if l.0 != inp {
            ChkChunk(rer, rest, inp, l, y);
            assert fchk(l, y);
          } else {
            EmptyLeafChunk(rer, r1, cont, inp, l, y, titer, tcont, gm', gm);
            TreeLeavesLenIndep(titer, LG.GMReset(gidl, l.1), gm', inp);
            TreeLeavesLenIndep(tcont, l.1, gmP, inp);
          }
        }
        FlatMapAllEmpty(post, frest, R3);
        assert Lplus == [];
      }
    }
  }
}
