// L5 CAPTURES — BRICK F1 (part 3) + F2: discipline ESTABLISHMENT + the tie.
//
// FlipMirror.dfy proves the flip tree mirror (builder `ComputeTrReverseF`,
// value fold `TreeResMirrorF`) under the FULL-tree close discipline
// `CloseDiscF`. This file ESTABLISHES that discipline for real `ComputeTr`
// trees — reusing TreeMirrorLk.dfy's sound `StackInvLk` machinery (the
// salvaged, mirror-independent half of that file) — and composes everything
// into F2:
//
//   `BackBodyGmTieFlip` — for a `GroupOkLB` body `tr`, the backward spec tree
//   over `inp` and the forward spec tree of `FlipRevL(tr)` over the swapped
//   window fold (at Empty) to corresponding leaves: None iff None, inputs
//   swap, and the leaf group maps are EXACT `MirrorGm` images — INNER-LOOK
//   CAPTURES INCLUDED.
//
// New establishments here:
//  - `ComputeTreeGActsIn` — a computed tree's group actions stay within the
//    stack's gid universe (feeds `AvoidsCR` at look nodes via disjointness).
//  - `ComputeTreeCloseDiscF` — the `CloseDiscF` establishment: TreeMirrorLk's
//    `ComputeTreeCloseDiscLk` case-for-case, with the `LookaroundR` case
//    EXTENDED to discharge the sub-tree obligations (fresh sub-establishment
//    at `{}`, widened by `CloseDiscFWiden` through the gid-disjointness the
//    stack invariant provides).
/** F1 (part 3) + F2: `CloseDiscF` for real spec trees, and the flip tie. */
module LindenElkFlipDisc {
  import opened Std.Wrappers
  import LW = WarblreRegExpRecord
  import WP = WarblrePrimitives
  import LC = Chars
  import LG = Groups
  import L = Regex
  import LN = WarblreNumeric
  import LS = Semantics
  import LT = Tree
  import FU = FunctionalUtils
  import FS = FunctionalSemantics
  import CI = ComputeIsTree
  import SSx = StrictSuffix
  import SD = LindenSpanDuality
  import TRM = LindenTreeResMirror
  import CD = LindenCloseDisc
  import EL = LindenElkEntryLk
  import FM = LindenElkFlipMirror
  import TML = LindenElkTreeMirrorLk

  // ===========================================================================
  // Group-action confinement for computed trees
  // ===========================================================================

  /** Every `Areg`'s defined gids and every `Aclose` gid of the stack lie in
      `S` — the invariant under which the computed tree's actions stay in `S`. */
  ghost predicate ActsGidsIn(acts: LS.Actions, S: set<LG.GroupId>) {
    forall i :: 0 <= i < |acts| ==>
      && (acts[i].Areg? ==> forall g :: g in L.DefGroups(acts[i].r) ==> g in S)
      && (acts[i].Aclose? ==> acts[i].gid in S)
  }

  lemma ActsGidsInTail(acts: LS.Actions, S: set<LG.GroupId>)
    requires |acts| > 0 && ActsGidsIn(acts, S)
    ensures ActsGidsIn(acts[1..], S)
  {
    forall i | 0 <= i < |acts[1..]|
      ensures (acts[1..][i].Areg? ==> forall g :: g in L.DefGroups(acts[1..][i].r) ==> g in S)
           && (acts[1..][i].Aclose? ==> acts[1..][i].gid in S)
    { assert acts[1..][i] == acts[i + 1]; }
  }

  lemma ActsGidsInCons(a: LS.Action, acts: LS.Actions, S: set<LG.GroupId>)
    requires ActsGidsIn(acts, S)
    requires a.Acheck? || (a.Aclose? && a.gid in S)
          || (a.Areg? && forall g :: g in L.DefGroups(a.r) ==> g in S)
    ensures ActsGidsIn([a] + acts, S)
  {
    forall i | 0 <= i < |[a] + acts|
      ensures (([a] + acts)[i].Areg? ==> forall g :: g in L.DefGroups(([a] + acts)[i].r) ==> g in S)
           && (([a] + acts)[i].Aclose? ==> ([a] + acts)[i].gid in S)
    { if i > 0 { assert ([a] + acts)[i] == acts[i - 1]; } }
  }

  /** A computed tree only ever acts on gids of the stack's universe `S` —
      inner look sub-trees included. */
  lemma ComputeTreeGActsIn(rer: LW.RegExpRecord, acts: LS.Actions, inp: LC.Input,
                           gm: LG.GroupMap, dir: WP.Direction, fuel: nat, S: set<LG.GroupId>)
    requires ActsGidsIn(acts, S)
    ensures var o := FS.ComputeTree(rer, acts, inp, gm, dir, fuel);
            o.Some? ==> FM.GActsIn(o.value, S)
    decreases fuel
  {
    if fuel == 0 { return; }
    var f := fuel - 1;
    if |acts| == 0 { return; }
    var cont := acts[1..];
    ActsGidsInTail(acts, S);
    match acts[0]
    case Acheck(strcheck) =>
      if SSx.IsStrictSuffix(inp, strcheck, dir) {
        ComputeTreeGActsIn(rer, cont, inp, gm, dir, f, S);
      }
    case Aclose(gid) =>
      assert gid in S;
      ComputeTreeGActsIn(rer, cont, inp, LG.GMClose(LC.Idx(inp), gid, gm), dir, f, S);
    case Areg(r) =>
      assert forall g :: g in L.DefGroups(r) ==> g in S;
      match r
      case Epsilon => ComputeTreeGActsIn(rer, cont, inp, gm, dir, f, S);
      case Character(cd) =>
        match LC.ReadChar(rer, cd, inp, dir) {
          case Some(pair) => ComputeTreeGActsIn(rer, cont, pair.1, gm, dir, f, S);
          case None =>
        }
      case Disjunction(r1, r2) =>
        assert L.DefGroups(r) == L.DefGroups(r1) + L.DefGroups(r2);
        SD.SetOfConcat(L.DefGroups(r1), L.DefGroups(r2));
        ActsGidsInCons(LS.Areg(r1), cont, S);
        ActsGidsInCons(LS.Areg(r2), cont, S);
        ComputeTreeGActsIn(rer, [LS.Areg(r1)] + cont, inp, gm, dir, f, S);
        ComputeTreeGActsIn(rer, [LS.Areg(r2)] + cont, inp, gm, dir, f, S);
      case Sequence(r1, r2) =>
        assert L.DefGroups(r) == L.DefGroups(r1) + L.DefGroups(r2);
        SD.SetOfConcat(L.DefGroups(r1), L.DefGroups(r2));
        match dir {
          case Forward =>
            ActsGidsInCons(LS.Areg(r2), cont, S);
            ActsGidsInCons(LS.Areg(r1), [LS.Areg(r2)] + cont, S);
            assert LS.SeqList(r1, r2, dir) + cont == [LS.Areg(r1)] + ([LS.Areg(r2)] + cont);
          case Backward =>
            ActsGidsInCons(LS.Areg(r1), cont, S);
            ActsGidsInCons(LS.Areg(r2), [LS.Areg(r1)] + cont, S);
            assert LS.SeqList(r1, r2, dir) + cont == [LS.Areg(r2)] + ([LS.Areg(r1)] + cont);
        }
        ComputeTreeGActsIn(rer, LS.SeqList(r1, r2, dir) + cont, inp, gm, dir, f, S);
      case Quantified(greedy, min, delta, r1) =>
        var gidl := L.DefGroups(r1);
        assert L.DefGroups(r) == gidl;
        if min > 0 {
          var q1 := L.Quantified(greedy, min - 1, delta, r1);
          assert L.DefGroups(q1) == gidl;
          ActsGidsInCons(LS.Areg(q1), cont, S);
          ActsGidsInCons(LS.Areg(r1), [LS.Areg(q1)] + cont, S);
          assert [LS.Areg(r1), LS.Areg(q1)] + cont == [LS.Areg(r1)] + ([LS.Areg(q1)] + cont);
          ComputeTreeGActsIn(rer, [LS.Areg(r1), LS.Areg(q1)] + cont, inp,
                             LG.GMReset(gidl, gm), dir, f, S);
        } else if delta == LN.NN(0) {
          ComputeTreeGActsIn(rer, cont, inp, gm, dir, f, S);
        } else {
          var q0 := L.Quantified(greedy, 0, FS.NoiPred(delta), r1);
          assert L.DefGroups(q0) == gidl;
          ActsGidsInCons(LS.Areg(q0), cont, S);
          ActsGidsInCons(LS.Acheck(inp), [LS.Areg(q0)] + cont, S);
          ActsGidsInCons(LS.Areg(r1), [LS.Acheck(inp)] + ([LS.Areg(q0)] + cont), S);
          assert [LS.Areg(r1), LS.Acheck(inp), LS.Areg(q0)] + cont
              == [LS.Areg(r1)] + ([LS.Acheck(inp)] + ([LS.Areg(q0)] + cont));
          ComputeTreeGActsIn(rer, [LS.Areg(r1), LS.Acheck(inp), LS.Areg(q0)] + cont, inp,
                             LG.GMReset(gidl, gm), dir, f, S);
          ComputeTreeGActsIn(rer, cont, inp, gm, dir, f, S);
        }
      case Group(gid, r1) =>
        assert L.DefGroups(r) == [gid] + L.DefGroups(r1);
        SD.SetOfConcat([gid], L.DefGroups(r1));
        assert gid in S;
        ActsGidsInCons(LS.Aclose(gid), cont, S);
        ActsGidsInCons(LS.Areg(r1), [LS.Aclose(gid)] + cont, S);
        assert [LS.Areg(r1), LS.Aclose(gid)] + cont
            == [LS.Areg(r1)] + ([LS.Aclose(gid)] + cont);
        ComputeTreeGActsIn(rer, [LS.Areg(r1), LS.Aclose(gid)] + cont, inp,
                           LG.GMOpen(LC.Idx(inp), gid, gm), dir, f, S);
      case LookaroundR(lk, r1) =>
        assert L.DefGroups(r) == L.DefGroups(r1);
        ActsGidsInCons(LS.Areg(r1), [], S);
        assert [LS.Areg(r1)] + [] == [LS.Areg(r1)];
        ComputeTreeGActsIn(rer, [LS.Areg(r1)], inp, gm, L.LkDir(lk), f, S);
        var treelk := FS.ComputeTree(rer, [LS.Areg(r1)], inp, gm, L.LkDir(lk), f);
        if treelk.Some? {
          match LS.LkResult(lk, treelk.value, gm, inp) {
            case Some(gmlk) => ComputeTreeGActsIn(rer, cont, inp, gmlk, dir, f, S);
            case None =>
          }
        }
      case AnchorR(a) =>
        if LS.AnchorSatisfied(rer, a, inp) {
          ComputeTreeGActsIn(rer, cont, inp, gm, dir, f, S);
        }
      case Backreference(gid) =>
        match LS.ReadBackref(rer, gm, gid, inp, dir) {
          case Some(pair) => ComputeTreeGActsIn(rer, cont, pair.1, gm, dir, f, S);
          case None =>
        }
  }

  // ===========================================================================
  // THE CloseDiscF ESTABLISHMENT
  // ===========================================================================

  /** A computed tree of a `StackInvLk` stack satisfies the FULL-tree close
      discipline at the stack's pending closes. `TML.ComputeTreeCloseDiscLk`
      case-for-case; the `LookaroundR` case additionally establishes the inner
      sub-tree's own discipline (fresh at `{}`, widened by the pending closes
      it provably avoids). */
  lemma ComputeTreeCloseDiscF(rer: LW.RegExpRecord, acts: LS.Actions, inp: LC.Input,
                              gm: LG.GroupMap, dir: WP.Direction, fuel: nat)
    requires TML.StackInvLk(acts)
    ensures var o := FS.ComputeTree(rer, acts, inp, gm, dir, fuel);
            o.Some? ==> FM.CloseDiscF(o.value, CD.ClosesSet(acts))
    decreases fuel
  {
    if fuel == 0 { return; }
    var f := fuel - 1;
    if |acts| == 0 { return; }
    var cont := acts[1..];
    var O := CD.ClosesSet(acts);
    match acts[0]
    case Acheck(strcheck) =>
      CD.ClosesActsConsNonClose(acts[0], cont);
      assert acts == [acts[0]] + cont;
      if SSx.IsStrictSuffix(inp, strcheck, dir) {
        TML.StackInvLkTail(acts);
        ComputeTreeCloseDiscF(rer, cont, inp, gm, dir, f);
      }
    case Aclose(gid) =>
      CD.ClosesActsConsClose(gid, cont);
      assert acts == [LS.Aclose(gid)] + cont;
      CD.NoDupGTail(gid, CD.ClosesActs(cont));
      TML.StackInvLkTail(acts);
      ComputeTreeCloseDiscF(rer, cont, inp, LG.GMClose(LC.Idx(inp), gid, gm), dir, f);
      var sub := FS.ComputeTree(rer, cont, inp, LG.GMClose(LC.Idx(inp), gid, gm), dir, f);
      if sub.Some? { assert gid in O; assert O - {gid} == CD.ClosesSet(cont); }
    case Areg(r) =>
      assert acts == [LS.Areg(r)] + cont;
      CD.ClosesActsConsNonClose(acts[0], cont);
      assert CD.ClosesSet(acts) == CD.ClosesSet(cont);
      assert EL.PikeLkRegexRec(r);
      assert CD.NoDupG(L.DefGroups(r));
      assert forall g :: g in L.DefGroups(r) ==> g !in CD.ClosesActs(cont);
      match r
      case Epsilon => TML.StackInvLkTail(acts); ComputeTreeCloseDiscF(rer, cont, inp, gm, dir, f);
      case Character(cd) =>
        match LC.ReadChar(rer, cd, inp, dir) {
          case Some(pair) => TML.StackInvLkTail(acts); ComputeTreeCloseDiscF(rer, cont, pair.1, gm, dir, f);
          case None =>
        }
      case Disjunction(r1, r2) =>
        assert L.DefGroups(r) == L.DefGroups(r1) + L.DefGroups(r2);
        CD.DefGroupsConcatAvoid(r1, r2, cont);
        TML.DefGroupsConcatAvoidSym(r1, r2, cont);
        CD.DefGroupsConcatNoDup(r1, r2);
        TML.NoDupGSuffix(L.DefGroups(r1), L.DefGroups(r2));
        TML.StackInvLkTail(acts);
        TML.StackInvLkConsRegAvoid(r1, cont);
        TML.StackInvLkConsRegAvoid(r2, cont);
        ComputeTreeCloseDiscF(rer, [LS.Areg(r1)] + cont, inp, gm, dir, f);
        ComputeTreeCloseDiscF(rer, [LS.Areg(r2)] + cont, inp, gm, dir, f);
        assert CD.ClosesSet([LS.Areg(r1)] + cont) == CD.ClosesSet(cont) by { CD.ClosesActsConsNonClose(LS.Areg(r1), cont); }
        assert CD.ClosesSet([LS.Areg(r2)] + cont) == CD.ClosesSet(cont) by { CD.ClosesActsConsNonClose(LS.Areg(r2), cont); }
      case Sequence(r1, r2) =>
        assert L.DefGroups(r) == L.DefGroups(r1) + L.DefGroups(r2);
        TML.StackInvLkTail(acts);
        TML.SeqListStackInvLk(r1, r2, dir, cont);
        ComputeTreeCloseDiscF(rer, LS.SeqList(r1, r2, dir) + cont, inp, gm, dir, f);
        assert CD.ClosesSet(LS.SeqList(r1, r2, dir) + cont) == O by { TML.SeqListClosesSetLk(r1, r2, dir, cont); }
      case Quantified(greedy, min, delta, r1) =>
        var gidl := L.DefGroups(r1);
        assert L.DefGroups(r) == gidl;
        TML.StackInvLkTail(acts);
        assert (set g | g in gidl) * O == {} by {
          forall g | g in gidl && g in O ensures false { assert g !in CD.ClosesActs(cont); }
        }
        assert O - (set g | g in gidl) == O;
        if min > 0 {
          var q1 := L.Quantified(greedy, min - 1, delta, r1);
          TML.QuantStackInvLk(greedy, min, delta, r1, cont);
          ComputeTreeCloseDiscF(rer, [LS.Areg(r1), LS.Areg(q1)] + cont, inp, LG.GMReset(gidl, gm), dir, f);
          var titer := FS.ComputeTree(rer, [LS.Areg(r1), LS.Areg(q1)] + cont, inp, LG.GMReset(gidl, gm), dir, f);
          if titer.Some? {
            assert CD.ClosesSet([LS.Areg(r1), LS.Areg(q1)] + cont) == O by { CD.QuantClosesSet(r1, q1, cont); }
            assert FM.CloseDiscF(LT.GroupActionT(LG.Reset(gidl), titer.value), O);
          }
        } else if delta == LN.NN(0) {
          ComputeTreeCloseDiscF(rer, cont, inp, gm, dir, f);
        } else {
          var q0 := L.Quantified(greedy, 0, FS.NoiPred(delta), r1);
          TML.QuantFreeStackInvLk(greedy, delta, r1, inp, cont);
          ComputeTreeCloseDiscF(rer, [LS.Areg(r1), LS.Acheck(inp), LS.Areg(q0)] + cont, inp, LG.GMReset(gidl, gm), dir, f);
          ComputeTreeCloseDiscF(rer, cont, inp, gm, dir, f);
          var titer := FS.ComputeTree(rer, [LS.Areg(r1), LS.Acheck(inp), LS.Areg(q0)] + cont, inp, LG.GMReset(gidl, gm), dir, f);
          var tskip := FS.ComputeTree(rer, cont, inp, gm, dir, f);
          if titer.Some? && tskip.Some? {
            assert CD.ClosesSet([LS.Areg(r1), LS.Acheck(inp), LS.Areg(q0)] + cont) == O by { CD.QuantFreeClosesSet(r1, q0, inp, cont); }
            assert FM.CloseDiscF(LT.GroupActionT(LG.Reset(gidl), titer.value), O);
            assert FM.CloseDiscF(tskip.value, O);
            assert FM.CloseDiscF(LT.GreedyChoice(greedy, LT.GroupActionT(LG.Reset(gidl), titer.value), tskip.value), O);
          }
        }
      case Group(gid, r1) =>
        TML.StackInvLkGroup(gid, r1, cont);
        ComputeTreeCloseDiscF(rer, [LS.Areg(r1), LS.Aclose(gid)] + cont, inp, LG.GMOpen(LC.Idx(inp), gid, gm), dir, f);
        var sub := FS.ComputeTree(rer, [LS.Areg(r1), LS.Aclose(gid)] + cont, inp, LG.GMOpen(LC.Idx(inp), gid, gm), dir, f);
        if sub.Some? {
          assert CD.ClosesSet([LS.Areg(r1), LS.Aclose(gid)] + cont) == O + {gid} by { CD.GroupClosesSet(r1, gid, cont); }
        }
      case AnchorR(a) =>
        if LS.AnchorSatisfied(rer, a, inp) { TML.StackInvLkTail(acts); ComputeTreeCloseDiscF(rer, cont, inp, gm, dir, f); }
      case LookaroundR(lk, r1) =>
        // THE EXTENDED CASE: the inner sub-tree's discipline is established too.
        assert L.DefGroups(r) == L.DefGroups(r1);
        assert EL.PikeLkRegexRec(r1) by {
          if L.Positivity(lk) {} else { TML.GroupFreeLIsPikeLkRec(r1); }
        }
        // StackInvLk of the fresh sub-stack [Areg(r1)]
        EL.PikeLkActionsRecConsIff(LS.Areg(r1), []);
        CD.ClosesActsConsNonClose(LS.Areg(r1), []);
        assert [LS.Areg(r1)] + [] == [LS.Areg(r1)];
        assert [LS.Areg(r1)][1..] == [];
        assert CD.ClosesActs([LS.Areg(r1)]) == [];
        assert CD.HeadsFreshOfCloses([LS.Areg(r1)]);
        assert CD.HeadsNoDupDefs([LS.Areg(r1)]);
        assert EL.PikeLkActionsRec([LS.Areg(r1)]);
        assert TML.StackInvLk([LS.Areg(r1)]);
        assert CD.ClosesSet([LS.Areg(r1)]) == {};
        ComputeTreeCloseDiscF(rer, [LS.Areg(r1)], inp, gm, L.LkDir(lk), f);
        var treelk := FS.ComputeTree(rer, [LS.Areg(r1)], inp, gm, L.LkDir(lk), f);
        if treelk.Some? {
          assert FM.CloseDiscF(treelk.value, {});
          // avoidance: the sub-tree acts only on the body's gids, disjoint
          // from the pending outer closes
          var S1 := set g | g in L.DefGroups(r1);
          ActsGidsInCons(LS.Areg(r1), [], S1);
          assert [LS.Areg(r1)] + [] == [LS.Areg(r1)];
          ComputeTreeGActsIn(rer, [LS.Areg(r1)], inp, gm, L.LkDir(lk), f, S1);
          assert FM.GActsIn(treelk.value, S1);
          assert S1 !! O by {
            forall g | g in S1 && g in O ensures false {
              assert g in L.DefGroups(r);
              assert g !in CD.ClosesActs(cont);
            }
          }
          FM.GActsInAvoids(treelk.value, S1, O);
          FM.CloseDiscFWiden(treelk.value, {}, O);
          assert {} + O == O;
          assert FM.CloseDiscF(treelk.value, O);
          match LS.LkResult(lk, treelk.value, gm, inp) {
            case Some(gmlk) =>
              var tc := FS.ComputeTree(rer, cont, inp, gmlk, dir, f);
              if tc.Some? {
                TML.StackInvLkTail(acts);
                ComputeTreeCloseDiscF(rer, cont, inp, gmlk, dir, f);
                assert FM.CloseDiscF(LT.LK(lk, treelk.value, tc.value), O);
              }
            case None =>
              assert FM.CloseDiscF(LT.LKFail(lk, treelk.value), O);
          }
        }
      case Backreference(gid) => assert EL.PikeLkRegexRec(r); assert false;
  }

  /** Fuel-free: the spec tree of a fragment regex with dup-free defs has the
      FULL-tree close discipline at the empty pending set. */
  lemma ComputeTrCloseDiscF(rer: LW.RegExpRecord, tr: L.Regex, inp: LC.Input,
                            gm: LG.GroupMap, dir: WP.Direction)
    requires EL.PikeLkRegexRec(tr) && CD.NoDupG(L.DefGroups(tr))
    ensures FM.CloseDiscF(FU.ComputeTr(rer, [LS.Areg(tr)], inp, gm, dir), {})
  {
    var acts := [LS.Areg(tr)];
    EL.PikeLkActionsRecConsIff(LS.Areg(tr), []);
    CD.ClosesActsConsNonClose(LS.Areg(tr), []);
    assert CD.ClosesActs(acts) == [];
    assert CD.HeadsFreshOfCloses(acts);
    assert CD.HeadsNoDupDefs(acts);
    assert TML.StackInvLk(acts);
    assert CD.ClosesSet(acts) == {};
    var fuel := FS.ActionsFuel(acts, inp, dir) + 1;
    FS.FunctionalTerminates(rer, acts, inp, gm, dir, fuel);
    var b := FS.ComputeTree(rer, acts, inp, gm, dir, fuel);
    ComputeTreeCloseDiscF(rer, acts, inp, gm, dir, fuel);
  }

  // ===========================================================================
  // F2: THE SPEC-SIDE TIE — backward body leaf == MirrorGm of the flip leaf
  // ===========================================================================

  /** `GroupOkLB` implies the `PikeLkRegexRec` fragment (positive looks
      recurse; negative-lookbehind bodies must be group-free — supplied). */
  lemma GroupOkLBNegFreePikeLk(tr: L.Regex)
    requires SD.GroupOkLB(tr)
    requires NegBodiesGroupFree(tr)
    ensures EL.PikeLkRegexRec(tr)
    decreases tr
  {
    match tr
    case Disjunction(r1, r2) => GroupOkLBNegFreePikeLk(r1); GroupOkLBNegFreePikeLk(r2);
    case Sequence(r1, r2) => GroupOkLBNegFreePikeLk(r1); GroupOkLBNegFreePikeLk(r2);
    case Quantified(_, _, _, r1) => GroupOkLBNegFreePikeLk(r1);
    case Group(_, r1) => GroupOkLBNegFreePikeLk(r1);
    case LookaroundR(lk, r1) =>
      if L.Positivity(lk) { GroupOkLBNegFreePikeLk(r1); }
    case _ =>
  }

  /** Negative looks' bodies are group-free (the fragment's negative arm —
      `NestedFragmentRE` forces negative bodies capture-free). */
  ghost predicate NegBodiesGroupFree(r: L.Regex)
    decreases r
  {
    match r
    case Disjunction(r1, r2) => NegBodiesGroupFree(r1) && NegBodiesGroupFree(r2)
    case Sequence(r1, r2) => NegBodiesGroupFree(r1) && NegBodiesGroupFree(r2)
    case Quantified(_, _, _, r1) => NegBodiesGroupFree(r1)
    case Group(_, r1) => NegBodiesGroupFree(r1)
    case LookaroundR(lk, r1) =>
      if L.Positivity(lk) then NegBodiesGroupFree(r1) else SD.GroupFreeL(r1)
    case _ => true
  }

  /** F2 — the flip-route SPEC tie (the sound replacement for the vacuous
      `BackBodyGmTieNested`): the backward spec tree of a `GroupOkLB` body and
      the forward spec tree of its FLIP reversal over the swapped window fold
      to corresponding leaves — None iff None, inputs swap, and the leaf group
      maps are EXACT `MirrorGm` images, inner-look captures included. */
  lemma BackBodyGmTieFlip(rer: LW.RegExpRecord, tr: L.Regex, inp: LC.Input, n: nat)
    requires SD.GroupOkLB(tr)
    requires NegBodiesGroupFree(tr)
    requires CD.NoDupG(L.DefGroups(tr))
    requires n == |inp.pref| + |inp.next|
    ensures var tB := FU.ComputeTr(rer, [LS.Areg(tr)], inp, LG.Empty, WP.Backward);
            var tF := FU.ComputeTr(rer, [LS.Areg(FM.FlipRevL(tr))], SD.SwapInput(inp),
                                   LG.Empty, WP.Forward);
            var rb := LT.TreeRes(tB, LG.Empty, inp, WP.Backward);
            var rf := LT.TreeRes(tF, LG.Empty, SD.SwapInput(inp), WP.Forward);
            && (rb.None? <==> rf.None?)
            && (rb.Some? ==>
                  && rf.Some?
                  && rf.value.0 == SD.SwapInput(rb.value.0)
                  && TRM.GmInBounds(rb.value.1, n)
                  && rf.value.1 == TRM.MirrorGm(rb.value.1, n))
  {
    var tB := FU.ComputeTr(rer, [LS.Areg(tr)], inp, LG.Empty, WP.Backward);
    var tF := FU.ComputeTr(rer, [LS.Areg(FM.FlipRevL(tr))], SD.SwapInput(inp),
                           LG.Empty, WP.Forward);
    // builder: the two trees are relation-related
    assert FM.GroupOkLBActs([LS.Areg(tr)]);
    FM.ComputeTrReverseF(rer, [LS.Areg(tr)], inp, LG.Empty, LG.Empty);
    assert FM.FlipRevActs([LS.Areg(tr)]) == [LS.Areg(FM.FlipRevL(tr))];
    assert FM.TreeMirrorRelF(tB, tF);
    // discipline: real trees satisfy CloseDiscF at {}
    GroupOkLBNegFreePikeLk(tr);
    ComputeTrCloseDiscF(rer, tr, inp, LG.Empty, WP.Backward);
    // fold at Empty (MirrorGm(Empty) == Empty)
    assert TRM.GmInBounds(LG.Empty, n);
    assert TRM.OpenSubset(LG.Empty, {});
    assert TRM.MirrorGm(LG.Empty, n) == LG.Empty;
    FM.TreeResMirrorF(tB, tF, LG.Empty, inp, n, {});
  }
}
