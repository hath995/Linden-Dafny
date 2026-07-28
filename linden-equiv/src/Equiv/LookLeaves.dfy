// Lookaround campaign (L1), §6.6: dissolving the gate at the LEAF level.
//
// The checked tree the simulation runs on drops the `LK` wrapper entirely (see
// TreeRepRE's gate rule): a passing gate carries the SAME tree onward, a
// failing one is `Mismatch`. The entry construction has to justify that against
// the spec tree, which does carry `LK`/`LKFail` nodes — i.e. it has to show the
// two denote the same leaves.
//
// THE CATCH: `CE.LeavesAgree` quantifies over EVERY group map, input, and
// direction, and at that strength the gate is NOT transparent — at some other
// input the body's subtree may have no leaves, killing the `LK` side while the
// dissolved side happily produces leaves. What IS true is agreement at the
// input the walk actually reached, for every group map, which is all the entry
// needs (`LAFirstLeaf` reads the first leaf at exactly one input). Hence
// `LeavesAgreeAt`, its congruences, and the two gate lemmas below.
//
// Group maps still have to be quantified, because the construction is
// group-map-free. Two facts make that work at a gate:
//   * whether the body's subtree has leaves does not depend on the group map
//     (`ResGroupMapIndep`), so the gate's verdict is the same for all of them;
//   * a group-free body's tree is GROUP-MAP NEUTRAL — every leaf it produces
//     carries the map it was given (its only group actions are `Reset([])`, and
//     resetting nothing is the identity) — so the continuation of a passing
//     positive gate resumes at the very map the `LK` node was entered with.
include "EntryLk.dfy"
include "CheckErase.dfy"
include "TreeRepRE.dfy"

/** §6.6: `LeavesAgreeAt` (leaf agreement at one input, for every group map),
    its congruences, group-map neutrality of group-free walks, and the two
    lemmas that dissolve a lookaround gate. */
module LindenElkLookLeaves {
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
  import SD = LindenSpanDuality
  import CE = LindenElkCheckErase
  import SSx = StrictSuffix
  import EL = LindenElkEntryLk
  import AR = LindenElkActionsRep
  import TR = LindenElkTreeRep
  import LOr = Oracle

  // ===========================================================================
  // Leaf agreement at a fixed input
  // ===========================================================================

  /** `t1` and `t2` denote the same leaves at input `inp` (scanning forward),
      under every group map — the weakening of `CE.LeavesAgree` that survives
      the gate. */
  ghost predicate LeavesAgreeAt(t1: LT.Tree, t2: LT.Tree, inp: LC.Input) {
    forall gm: LG.GroupMap :: LT.TreeLeaves(t1, gm, inp, WP.Forward)
                           == LT.TreeLeaves(t2, gm, inp, WP.Forward)
  }

  /** Agreement everywhere implies agreement here. */
  lemma LAWeaken(t1: LT.Tree, t2: LT.Tree, inp: LC.Input)
    requires CE.LeavesAgree(t1, t2)
    ensures LeavesAgreeAt(t1, t2, inp)
  {}

  /** What the entry actually reads off. */
  lemma LAAtFirstLeaf(t1: LT.Tree, t2: LT.Tree, inp: LC.Input)
    requires LeavesAgreeAt(t1, t2, inp)
    ensures LT.FirstLeaf(t1, inp) == LT.FirstLeaf(t2, inp)
  {
    LT.FirstTreeLeaf(t1, LG.Empty, inp, WP.Forward);
    LT.FirstTreeLeaf(t2, LG.Empty, inp, WP.Forward);
  }

  lemma LAAtProgressPass(t: LT.Tree, inp: LC.Input)
    ensures LeavesAgreeAt(LT.Progress(t), t, inp)
  {}

  lemma LAAtCongProgress(a: LT.Tree, b: LT.Tree, inp: LC.Input)
    requires LeavesAgreeAt(a, b, inp)
    ensures LeavesAgreeAt(LT.Progress(a), LT.Progress(b), inp)
  {}

  lemma LAAtCongRead(c: char, a: LT.Tree, b: LT.Tree, inp: LC.Input)
    requires LeavesAgreeAt(a, b, LC.AdvanceInputP(inp, WP.Forward))
    ensures LeavesAgreeAt(LT.Read(c, a), LT.Read(c, b), inp)
  {}

  lemma LAAtCongGroup(g: LG.GroupAction, a: LT.Tree, b: LT.Tree, inp: LC.Input)
    requires LeavesAgreeAt(a, b, inp)
    ensures LeavesAgreeAt(LT.GroupActionT(g, a), LT.GroupActionT(g, b), inp)
  {}

  lemma LAAtCongAnchor(an: L.Anchor, a: LT.Tree, b: LT.Tree, inp: LC.Input)
    requires LeavesAgreeAt(a, b, inp)
    ensures LeavesAgreeAt(LT.AnchorPass(an, a), LT.AnchorPass(an, b), inp)
  {}

  lemma LAAtCongChoice(a1: LT.Tree, b1: LT.Tree, a2: LT.Tree, b2: LT.Tree, inp: LC.Input)
    requires LeavesAgreeAt(a1, b1, inp) && LeavesAgreeAt(a2, b2, inp)
    ensures LeavesAgreeAt(LT.Choice(a1, a2), LT.Choice(b1, b2), inp)
  {}

  lemma LAAtRefl(t: LT.Tree, inp: LC.Input)
    ensures LeavesAgreeAt(t, t, inp)
  {}

  lemma LAAtTrans(a: LT.Tree, b: LT.Tree, c: LT.Tree, inp: LC.Input)
    requires LeavesAgreeAt(a, b, inp) && LeavesAgreeAt(b, c, inp)
    ensures LeavesAgreeAt(a, c, inp)
  {}

  // ===========================================================================
  // Group-map neutral trees
  // ===========================================================================

  /** A tree that passes its group map through untouched: its only group
      actions are `Reset([])` (what a group-free quantifier emits), and it
      contains no gate or backreference node. Every leaf it produces therefore
      carries the map the tree was entered with. */
  ghost predicate GmNeutralTree(t: LT.Tree)
    decreases t
  {
    match t
    case Mismatch => true
    case Match => true
    case Choice(t1, t2) => GmNeutralTree(t1) && GmNeutralTree(t2)
    case Read(_, t1) => GmNeutralTree(t1)
    case Progress(t1) => GmNeutralTree(t1)
    case GroupActionT(a, t1) => a.Reset? && a.gl == [] && GmNeutralTree(t1)
    case AnchorPass(_, t1) => GmNeutralTree(t1)
    case LK(_, _, _) => false
    case LKFail(_, _) => false
    case ReadBackRef(_, _) => false
  }

  /** Every leaf of a group-map-neutral tree carries the map it was entered
      with. */
  lemma GmNeutralLeaves(t: LT.Tree, gm: LG.GroupMap, inp: LC.Input, dir: WP.Direction)
    requires GmNeutralTree(t)
    ensures forall i :: 0 <= i < |LT.TreeLeaves(t, gm, inp, dir)|
                        ==> LT.TreeLeaves(t, gm, inp, dir)[i].1 == gm
    decreases t
  {
    match t
    case Choice(t1, t2) =>
      GmNeutralLeaves(t1, gm, inp, dir);
      GmNeutralLeaves(t2, gm, inp, dir);
      var l1 := LT.TreeLeaves(t1, gm, inp, dir);
      var l2 := LT.TreeLeaves(t2, gm, inp, dir);
      var both: seq<LT.Leaf> := l1 + l2;
      assert LT.TreeLeaves(t, gm, inp, dir) == both;
      forall i: nat | 0 <= i < |both| ensures both[i].1 == gm {
        if i < |l1| { assert both[i] == l1[i]; } else { assert both[i] == l2[i - |l1|]; }
      }
    case Read(_, t1) => GmNeutralLeaves(t1, gm, LC.AdvanceInputP(inp, dir), dir);
    case Progress(t1) => GmNeutralLeaves(t1, gm, inp, dir);
    case GroupActionT(a, t1) =>
      SD.GMResetNil(gm);
      assert LG.GMUpdate(a, LC.Idx(inp), gm) == gm;
      GmNeutralLeaves(t1, gm, inp, dir);
    case AnchorPass(_, t1) => GmNeutralLeaves(t1, gm, inp, dir);
    case _ =>
  }

  /** A group-free walk computes a group-map-neutral tree. */
  lemma ComputeTreeGmNeutral(rer: LW.RegExpRecord, act: LS.Actions, inp: LC.Input,
                             gm: LG.GroupMap, dir: WP.Direction, fuel: nat, t: LT.Tree)
    requires EL.GroupFreeActs(act)
    requires FS.ComputeTree(rer, act, inp, gm, dir, fuel) == Some(t)
    ensures GmNeutralTree(t)
    decreases fuel
  {
    var f := fuel - 1;
    if |act| == 0 { return; }
    var cont := act[1..];
    EL.GroupFreeActsTail(act);
    match act[0]
    case Acheck(strcheck) =>
      if SSx.IsStrictSuffix(inp, strcheck, dir) {
        var sub := FS.ComputeTree(rer, cont, inp, gm, dir, f);
        ComputeTreeGmNeutral(rer, cont, inp, gm, dir, f, sub.value);
      }
    case Aclose(gid) =>          // excluded by GroupFreeActs
    case Areg(r) =>
      match r
      case Epsilon => ComputeTreeGmNeutral(rer, cont, inp, gm, dir, f, t);
      case Character(cd) =>
        match LC.ReadChar(rer, cd, inp, dir) {
          case None =>
          case Some(pair) =>
            var sub := FS.ComputeTree(rer, cont, pair.1, gm, dir, f);
            ComputeTreeGmNeutral(rer, cont, pair.1, gm, dir, f, sub.value);
        }
      case Disjunction(r1, r2) =>
        EL.GroupFreeActsCons(LS.Areg(r1), cont);
        EL.GroupFreeActsCons(LS.Areg(r2), cont);
        var s1 := FS.ComputeTree(rer, [LS.Areg(r1)] + cont, inp, gm, dir, f);
        var s2 := FS.ComputeTree(rer, [LS.Areg(r2)] + cont, inp, gm, dir, f);
        ComputeTreeGmNeutral(rer, [LS.Areg(r1)] + cont, inp, gm, dir, f, s1.value);
        ComputeTreeGmNeutral(rer, [LS.Areg(r2)] + cont, inp, gm, dir, f, s2.value);
      case Sequence(r1, r2) =>
        var na := LS.SeqList(r1, r2, dir) + cont;
        assert EL.GroupFreeActs(na) by {
          if dir.Forward? {
            assert na == [LS.Areg(r1)] + ([LS.Areg(r2)] + cont);
            EL.GroupFreeActsCons(LS.Areg(r2), cont);
            EL.GroupFreeActsCons(LS.Areg(r1), [LS.Areg(r2)] + cont);
          } else {
            assert na == [LS.Areg(r2)] + ([LS.Areg(r1)] + cont);
            EL.GroupFreeActsCons(LS.Areg(r1), cont);
            EL.GroupFreeActsCons(LS.Areg(r2), [LS.Areg(r1)] + cont);
          }
        }
        var sub := FS.ComputeTree(rer, na, inp, gm, dir, f);
        ComputeTreeGmNeutral(rer, na, inp, gm, dir, f, sub.value);
      case Quantified(greedy, min, delta, r1) =>
        SD.GroupFreeDefGroups(r1);
        assert L.DefGroups(r1) == [];
        var gm' := LG.GMReset(L.DefGroups(r1), gm);
        if min > 0 {
          var quant := L.Quantified(greedy, min - 1, delta, r1);
          var na := [LS.Areg(r1), LS.Areg(quant)] + cont;
          assert EL.GroupFreeActs(na) by {
            assert na == [LS.Areg(r1)] + ([LS.Areg(quant)] + cont);
            EL.GroupFreeActsCons(LS.Areg(quant), cont);
            EL.GroupFreeActsCons(LS.Areg(r1), [LS.Areg(quant)] + cont);
          }
          var sub := FS.ComputeTree(rer, na, inp, gm', dir, f);
          ComputeTreeGmNeutral(rer, na, inp, gm', dir, f, sub.value);
        } else if delta == LN.NN(0) {
          ComputeTreeGmNeutral(rer, cont, inp, gm, dir, f, t);
        } else {
          var quant := L.Quantified(greedy, 0, FS.NoiPred(delta), r1);
          var na := [LS.Areg(r1), LS.Acheck(inp), LS.Areg(quant)] + cont;
          assert EL.GroupFreeActs(na) by {
            assert na == [LS.Areg(r1)] + ([LS.Acheck(inp)] + ([LS.Areg(quant)] + cont));
            EL.GroupFreeActsCons(LS.Areg(quant), cont);
            EL.GroupFreeActsCons(LS.Acheck(inp), [LS.Areg(quant)] + cont);
            EL.GroupFreeActsCons(LS.Areg(r1), [LS.Acheck(inp)] + ([LS.Areg(quant)] + cont));
          }
          var siter := FS.ComputeTree(rer, na, inp, gm', dir, f);
          var sskip := FS.ComputeTree(rer, cont, inp, gm, dir, f);
          ComputeTreeGmNeutral(rer, na, inp, gm', dir, f, siter.value);
          ComputeTreeGmNeutral(rer, cont, inp, gm, dir, f, sskip.value);
        }
      case Group(gid, r1) =>       // excluded by GroupFreeL
      case LookaroundR(lk, r1) =>  // excluded by GroupFreeL
      case AnchorR(a) =>
        if LS.AnchorSatisfied(rer, a, inp) {
          var sub := FS.ComputeTree(rer, cont, inp, gm, dir, f);
          ComputeTreeGmNeutral(rer, cont, inp, gm, dir, f, sub.value);
        }
      case Backreference(gid) =>   // excluded by GroupFreeL
  }

  /** `ComputeTreeGmNeutral` in `ComputeTr` form — the shape the gate rule's
      body tree comes in. */
  lemma ComputeTrGmNeutral(rer: LW.RegExpRecord, r: L.Regex, inp: LC.Input, gm: LG.GroupMap,
                           dir: WP.Direction)
    requires SD.GroupFreeL(r)
    ensures GmNeutralTree(FU.ComputeTr(rer, [LS.Areg(r)], inp, gm, dir))
  {
    var acts := [LS.Areg(r)];
    assert EL.GroupFreeActs(acts);
    var fuel := FS.ActionsFuel(acts, inp, dir) + 1;
    FS.FunctionalTerminates(rer, acts, inp, gm, dir, fuel);
    var opt := FS.ComputeTree(rer, acts, inp, gm, dir, fuel);
    ComputeTreeGmNeutral(rer, acts, inp, gm, dir, fuel, opt.value);
  }

  // ===========================================================================
  // Dissolving the gate
  // ===========================================================================

  /** A PASSING gate is leaf-transparent at the input it was taken: the `LK`
      node denotes exactly its continuation's leaves. Positive gates need the
      body tree to be group-map neutral (so the continuation resumes at the
      same map); negative gates hand the map straight through. */
  // ===========================================================================
  // L3a: the CAPTURING analogue of the gm-neutral gate machinery. A captured
  // lookAHEAD's body touches only its own groups `S`, so at the gate it folds
  // captures into the continuation's map WITHIN `S`. Everything is stated
  // "outside `S`": the gate node's leaves agree with the continuation's OUTSIDE
  // `S`. Threading this weaker relation replaces `LeavesAgreeAt` in the L3a
  // checked-tree correspondence.
  // ===========================================================================

  /** Two group maps agree on membership and value at every group NOT in `S`. */
  ghost predicate GmAgreeOutside(gm1: LG.GroupMap, gm2: LG.GroupMap, S: set<LG.GroupId>) {
    forall g :: g !in S ==> (g in gm1 <==> g in gm2) && (g in gm1 ==> gm1[g] == gm2[g])
  }

  /** The SAME group action preserves outside-`S` agreement. */
  lemma GMUpdateAgreeOutside(op: LG.GroupAction, idx: nat, gm1: LG.GroupMap, gm2: LG.GroupMap, S: set<LG.GroupId>)
    requires GmAgreeOutside(gm1, gm2, S)
    ensures GmAgreeOutside(LG.GMUpdate(op, idx, gm1), LG.GMUpdate(op, idx, gm2), S)
  {
    match op
    case Open(g) =>
    case Close(g) =>
      forall g' | g' !in S
        ensures (g' in LG.GMClose(idx, g, gm1) <==> g' in LG.GMClose(idx, g, gm2))
             && (g' in LG.GMClose(idx, g, gm1) ==> LG.GMClose(idx, g, gm1)[g'] == LG.GMClose(idx, g, gm2)[g'])
      { if g' == g { assert LG.Find(g, gm1) == LG.Find(g, gm2); } }
    case Reset(gs) =>
  }

  /** THE general frame: `TreeLeaves` from two maps that agree OUTSIDE `S` yields
      leaf lists of equal length, equal positions, and per-leaf maps that still
      agree outside `S`. Holds for ANY tree (nested `LK` verdicts are group-map
      independent, so the recursion carries through). */
  lemma TreeLeavesFrameOutside(t: LT.Tree, gm1: LG.GroupMap, gm2: LG.GroupMap, inp: LC.Input,
                               dir: WP.Direction, S: set<LG.GroupId>)
    requires GmAgreeOutside(gm1, gm2, S)
    ensures |LT.TreeLeaves(t, gm1, inp, dir)| == |LT.TreeLeaves(t, gm2, inp, dir)|
    ensures forall i :: 0 <= i < |LT.TreeLeaves(t, gm1, inp, dir)| ==>
              LT.TreeLeaves(t, gm1, inp, dir)[i].0 == LT.TreeLeaves(t, gm2, inp, dir)[i].0
              && GmAgreeOutside(LT.TreeLeaves(t, gm1, inp, dir)[i].1, LT.TreeLeaves(t, gm2, inp, dir)[i].1, S)
    decreases t
  {
    match t
    case Mismatch =>
    case Match =>
    case Choice(t1, t2) =>
      TreeLeavesFrameOutside(t1, gm1, gm2, inp, dir, S);
      TreeLeavesFrameOutside(t2, gm1, gm2, inp, dir, S);
      var a1: seq<LT.Leaf> := LT.TreeLeaves(t1, gm1, inp, dir);
      var a2: seq<LT.Leaf> := LT.TreeLeaves(t1, gm2, inp, dir);
      var b1: seq<LT.Leaf> := LT.TreeLeaves(t2, gm1, inp, dir);
      var b2: seq<LT.Leaf> := LT.TreeLeaves(t2, gm2, inp, dir);
      var L1: seq<LT.Leaf> := LT.TreeLeaves(t, gm1, inp, dir);
      var L2: seq<LT.Leaf> := LT.TreeLeaves(t, gm2, inp, dir);
      assert L1 == a1 + b1 && L2 == a2 + b2;
      forall i | 0 <= i < |L1|
        ensures L1[i].0 == L2[i].0 && GmAgreeOutside(L1[i].1, L2[i].1, S)
      {
        if i < |a1| { assert L1[i] == a1[i] && L2[i] == a2[i]; }
        else { assert L1[i] == b1[i - |a1|] && L2[i] == b2[i - |a1|]; }
      }
    case Read(c, t1) => TreeLeavesFrameOutside(t1, gm1, gm2, LC.AdvanceInputP(inp, dir), dir, S);
    case Progress(t1) => TreeLeavesFrameOutside(t1, gm1, gm2, inp, dir, S);
    case GroupActionT(a, t1) =>
      GMUpdateAgreeOutside(a, LC.Idx(inp), gm1, gm2, S);
      TreeLeavesFrameOutside(t1, LG.GMUpdate(a, LC.Idx(inp), gm1), LG.GMUpdate(a, LC.Idx(inp), gm2), inp, dir, S);
    case AnchorPass(_, t0) => TreeLeavesFrameOutside(t0, gm1, gm2, inp, dir, S);
    case ReadBackRef(brStr, t0) => TreeLeavesFrameOutside(t0, gm1, gm2, LC.AdvanceInputN(inp, |brStr|, dir), dir, S);
    case LK(lk, tlk, t1) =>
      TreeLeavesFrameOutside(tlk, gm1, gm2, inp, L.LkDir(lk), S);
      var sub1 := LT.TreeLeaves(tlk, gm1, inp, L.LkDir(lk));
      var sub2 := LT.TreeLeaves(tlk, gm2, inp, L.LkDir(lk));
      if L.Positivity(lk) {
        if |sub1| > 0 { TreeLeavesFrameOutside(t1, sub1[0].1, sub2[0].1, inp, dir, S); }
      } else {
        if |sub1| == 0 { TreeLeavesFrameOutside(t1, gm1, gm2, inp, dir, S); }
      }
    case LKFail(_, _) =>
  }

  /** `GmAgreeOutside` is reflexive and transitive. */
  lemma GmAgreeOutsideRefl(gm: LG.GroupMap, S: set<LG.GroupId>)
    ensures GmAgreeOutside(gm, gm, S)
  {}
  lemma GmAgreeOutsideTrans(a: LG.GroupMap, b: LG.GroupMap, c: LG.GroupMap, S: set<LG.GroupId>)
    requires GmAgreeOutside(a, b, S) && GmAgreeOutside(b, c, S)
    ensures GmAgreeOutside(a, c, S)
  {}

  /** A group action touches only groups in `S`. */
  ghost predicate GmActionIn(a: LG.GroupAction, S: set<LG.GroupId>) {
    match a
    case Open(g) => g in S
    case Close(g) => g in S
    case Reset(gs) => forall g :: g in gs ==> g in S
  }

  /** A tree whose group actions all touch only `S` (and no `LK`/`LKFail`) --
      the tree of a look-free body that captures only its own groups `S`. */
  ghost predicate GmConfinedTree(t: LT.Tree, S: set<LG.GroupId>) {
    match t
    case Mismatch => true
    case Match => true
    case Choice(t1, t2) => GmConfinedTree(t1, S) && GmConfinedTree(t2, S)
    case Read(_, t1) => GmConfinedTree(t1, S)
    case Progress(t1) => GmConfinedTree(t1, S)
    case GroupActionT(a, t1) => GmActionIn(a, S) && GmConfinedTree(t1, S)
    case AnchorPass(_, t1) => GmConfinedTree(t1, S)
    case ReadBackRef(_, t1) => GmConfinedTree(t1, S)
    case LK(_, _, _) => false
    case LKFail(_, _) => false
  }

  /** A confined action leaves the map unchanged outside `S`. */
  lemma GmUpdateConfined(a: LG.GroupAction, idx: nat, gm: LG.GroupMap, S: set<LG.GroupId>)
    requires GmActionIn(a, S)
    ensures GmAgreeOutside(LG.GMUpdate(a, idx, gm), gm, S)
  {
    match a
    case Open(g) =>
    case Close(g) =>
      forall g' | g' !in S
        ensures (g' in LG.GMClose(idx, g, gm) <==> g' in gm)
             && (g' in LG.GMClose(idx, g, gm) ==> LG.GMClose(idx, g, gm)[g'] == gm[g'])
      {}
    case Reset(gs) =>
  }

  /** A confined tree's every leaf agrees with the incoming map OUTSIDE `S`. */
  lemma GmConfinedLeaves(t: LT.Tree, gm: LG.GroupMap, inp: LC.Input, dir: WP.Direction, S: set<LG.GroupId>)
    requires GmConfinedTree(t, S)
    ensures forall i :: 0 <= i < |LT.TreeLeaves(t, gm, inp, dir)|
                        ==> GmAgreeOutside(LT.TreeLeaves(t, gm, inp, dir)[i].1, gm, S)
    decreases t
  {
    match t
    case Mismatch =>
    case Match => GmAgreeOutsideRefl(gm, S);
    case Choice(t1, t2) =>
      GmConfinedLeaves(t1, gm, inp, dir, S);
      GmConfinedLeaves(t2, gm, inp, dir, S);
      var a1: seq<LT.Leaf> := LT.TreeLeaves(t1, gm, inp, dir);
      var b1: seq<LT.Leaf> := LT.TreeLeaves(t2, gm, inp, dir);
      var L1: seq<LT.Leaf> := LT.TreeLeaves(t, gm, inp, dir);
      assert L1 == a1 + b1;
      forall i | 0 <= i < |L1| ensures GmAgreeOutside(L1[i].1, gm, S) {
        if i < |a1| { assert L1[i] == a1[i]; } else { assert L1[i] == b1[i - |a1|]; }
      }
    case Read(c, t1) => GmConfinedLeaves(t1, gm, LC.AdvanceInputP(inp, dir), dir, S);
    case Progress(t1) => GmConfinedLeaves(t1, gm, inp, dir, S);
    case GroupActionT(a, t1) =>
      var gm' := LG.GMUpdate(a, LC.Idx(inp), gm);
      GmUpdateConfined(a, LC.Idx(inp), gm, S);           // gm' agrees gm outside S
      GmConfinedLeaves(t1, gm', inp, dir, S);            // leaves agree gm' outside S
      forall i | 0 <= i < |LT.TreeLeaves(t1, gm', inp, dir)|
        ensures GmAgreeOutside(LT.TreeLeaves(t1, gm', inp, dir)[i].1, gm, S)
      { GmAgreeOutsideTrans(LT.TreeLeaves(t1, gm', inp, dir)[i].1, gm', gm, S); }
    case AnchorPass(_, t0) => GmConfinedLeaves(t0, gm, inp, dir, S);
    case ReadBackRef(brStr, t0) => GmConfinedLeaves(t0, gm, LC.AdvanceInputN(inp, |brStr|, dir), dir, S);
  }

  /** Leaf lists agree (length, positions, maps OUTSIDE `S`) at every incoming map. */
  ghost predicate LeavesAgreeAtOutside(t1: LT.Tree, t2: LT.Tree, inp: LC.Input, S: set<LG.GroupId>) {
    forall gm: LG.GroupMap ::
      |LT.TreeLeaves(t1, gm, inp, WP.Forward)| == |LT.TreeLeaves(t2, gm, inp, WP.Forward)|
      && (forall i :: 0 <= i < |LT.TreeLeaves(t1, gm, inp, WP.Forward)| ==>
            LT.TreeLeaves(t1, gm, inp, WP.Forward)[i].0 == LT.TreeLeaves(t2, gm, inp, WP.Forward)[i].0
            && GmAgreeOutside(LT.TreeLeaves(t1, gm, inp, WP.Forward)[i].1,
                              LT.TreeLeaves(t2, gm, inp, WP.Forward)[i].1, S))
  }

  /** L3a gate-pass: a POSITIVE lookAHEAD whose confined (captures only `S`) body
      matches folds captures within `S`, so the gate node's leaves agree with the
      continuation's OUTSIDE `S`. The capturing analogue of `LAAtGatePass`. */
  lemma LAAtGatePassL3a(lk: L.Lookaround, tlk: LT.Tree, tc: LT.Tree, inp: LC.Input, S: set<LG.GroupId>)
    requires L.Positivity(lk) && L.LkDir(lk) == WP.Forward
    requires GmConfinedTree(tlk, S)
    requires |LT.TreeLeaves(tlk, LG.Empty, inp, L.LkDir(lk))| > 0
    ensures LeavesAgreeAtOutside(LT.LK(lk, tlk, tc), tc, inp, S)
  {
    forall gm: LG.GroupMap
      ensures |LT.TreeLeaves(LT.LK(lk, tlk, tc), gm, inp, WP.Forward)| == |LT.TreeLeaves(tc, gm, inp, WP.Forward)|
      ensures forall i :: 0 <= i < |LT.TreeLeaves(LT.LK(lk, tlk, tc), gm, inp, WP.Forward)| ==>
                LT.TreeLeaves(LT.LK(lk, tlk, tc), gm, inp, WP.Forward)[i].0 == LT.TreeLeaves(tc, gm, inp, WP.Forward)[i].0
                && GmAgreeOutside(LT.TreeLeaves(LT.LK(lk, tlk, tc), gm, inp, WP.Forward)[i].1,
                                  LT.TreeLeaves(tc, gm, inp, WP.Forward)[i].1, S)
    {
      var sub: seq<LT.Leaf> := LT.TreeLeaves(tlk, gm, inp, L.LkDir(lk));
      // the body still matches at gm (verdict is group-map independent)
      LT.FirstTreeLeaf(tlk, gm, inp, L.LkDir(lk));
      LT.FirstTreeLeaf(tlk, LG.Empty, inp, L.LkDir(lk));
      if |sub| == 0 {
        LT.HdErrorNoneNil(sub);
        LT.ResGroupMapIndep(tlk, gm, LG.Empty, inp, inp, L.LkDir(lk), L.LkDir(lk));
        LT.HdErrorNoneNil(LT.TreeLeaves(tlk, LG.Empty, inp, L.LkDir(lk)));
        assert false;
      }
      // TreeLeaves(LK, gm) == TreeLeaves(tc, sub[0].1); sub[0].1 agrees gm outside S.
      GmConfinedLeaves(tlk, gm, inp, L.LkDir(lk), S);       // sub[0].1 agrees gm outside S
      assert GmAgreeOutside(sub[0].1, gm, S);
      TreeLeavesFrameOutside(tc, sub[0].1, gm, inp, WP.Forward, S);
    }
  }

  /** Full agreement is agreement outside any `S` (the L1 gate cases feed the
      L3a chain unchanged). */
  lemma LeavesAgreeAtWeaken(t1: LT.Tree, t2: LT.Tree, inp: LC.Input, S: set<LG.GroupId>)
    requires LeavesAgreeAt(t1, t2, inp)
    ensures LeavesAgreeAtOutside(t1, t2, inp, S)
  {
    forall gm: LG.GroupMap
      ensures |LT.TreeLeaves(t1, gm, inp, WP.Forward)| == |LT.TreeLeaves(t2, gm, inp, WP.Forward)|
      ensures forall i :: 0 <= i < |LT.TreeLeaves(t1, gm, inp, WP.Forward)| ==>
                LT.TreeLeaves(t1, gm, inp, WP.Forward)[i].0 == LT.TreeLeaves(t2, gm, inp, WP.Forward)[i].0
                && GmAgreeOutside(LT.TreeLeaves(t1, gm, inp, WP.Forward)[i].1,
                                  LT.TreeLeaves(t2, gm, inp, WP.Forward)[i].1, S)
    {
      forall i | 0 <= i < |LT.TreeLeaves(t1, gm, inp, WP.Forward)|
        ensures GmAgreeOutside(LT.TreeLeaves(t1, gm, inp, WP.Forward)[i].1,
                               LT.TreeLeaves(t2, gm, inp, WP.Forward)[i].1, S)
      { GmAgreeOutsideRefl(LT.TreeLeaves(t1, gm, inp, WP.Forward)[i].1, S); }
    }
  }

  /** `LeavesAgreeAtOutside` transfers to the FIRST leaf (`TreeRes`/`FirstLeaf`):
      same success, same position, maps agreeing outside `S`. */
  lemma FirstLeafAgreeOutside(t1: LT.Tree, t2: LT.Tree, inp: LC.Input, S: set<LG.GroupId>)
    requires LeavesAgreeAtOutside(t1, t2, inp, S)
    ensures (LT.FirstLeaf(t1, inp).None? <==> LT.FirstLeaf(t2, inp).None?)
    ensures LT.FirstLeaf(t1, inp).Some? ==>
              LT.FirstLeaf(t1, inp).value.0 == LT.FirstLeaf(t2, inp).value.0
              && GmAgreeOutside(LT.FirstLeaf(t1, inp).value.1, LT.FirstLeaf(t2, inp).value.1, S)
  {
    LT.FirstTreeLeaf(t1, LG.Empty, inp, WP.Forward);
    LT.FirstTreeLeaf(t2, LG.Empty, inp, WP.Forward);
    var l1: seq<LT.Leaf> := LT.TreeLeaves(t1, LG.Empty, inp, WP.Forward);
    var l2: seq<LT.Leaf> := LT.TreeLeaves(t2, LG.Empty, inp, WP.Forward);
    LT.HdErrorNoneNil(l1);
    LT.HdErrorNoneNil(l2);
    // FirstLeaf == HdError(TreeLeaves(_, Empty, inp, Forward)); lists agree outside S.
  }

  /** Agreement outside the EMPTY set is full agreement -- lets a caller that
      passes `S == {}` recover `LeavesAgreeAt` (the capture-free path). */
  lemma LeavesAgreeAtOutsideEmpty(t1: LT.Tree, t2: LT.Tree, inp: LC.Input)
    requires LeavesAgreeAtOutside(t1, t2, inp, {})
    ensures LeavesAgreeAt(t1, t2, inp)
  {
    forall gm: LG.GroupMap
      ensures LT.TreeLeaves(t1, gm, inp, WP.Forward) == LT.TreeLeaves(t2, gm, inp, WP.Forward)
    {
      var emptyS: set<LG.GroupId> := {};
      var l1: seq<LT.Leaf> := LT.TreeLeaves(t1, gm, inp, WP.Forward);
      var l2: seq<LT.Leaf> := LT.TreeLeaves(t2, gm, inp, WP.Forward);
      assert |l1| == |l2|;
      forall i | 0 <= i < |l1| ensures l1[i] == l2[i] {
        assert l1[i].0 == l2[i].0 && GmAgreeOutside(l1[i].1, l2[i].1, emptyS);
        assert l1[i].1 == l2[i].1 by {
          forall g ensures (g in l1[i].1 <==> g in l2[i].1) && (g in l1[i].1 ==> l1[i].1[g] == l2[i].1[g])
          { assert g !in emptyS; }
        }
      }
    }
  }

  // --- the "outside S" congruence toolkit (mirrors the LeavesAgreeAt LAAt*
  // family) -- what the L3a checked-tree correspondence assembles with. ---

  lemma LAAtReflOutside(t: LT.Tree, inp: LC.Input, S: set<LG.GroupId>)
    ensures LeavesAgreeAtOutside(t, t, inp, S)
  {
    forall gm: LG.GroupMap
      ensures forall i :: 0 <= i < |LT.TreeLeaves(t, gm, inp, WP.Forward)| ==>
                GmAgreeOutside(LT.TreeLeaves(t, gm, inp, WP.Forward)[i].1, LT.TreeLeaves(t, gm, inp, WP.Forward)[i].1, S)
    { forall i | 0 <= i < |LT.TreeLeaves(t, gm, inp, WP.Forward)|
        ensures GmAgreeOutside(LT.TreeLeaves(t, gm, inp, WP.Forward)[i].1, LT.TreeLeaves(t, gm, inp, WP.Forward)[i].1, S)
      { GmAgreeOutsideRefl(LT.TreeLeaves(t, gm, inp, WP.Forward)[i].1, S); } }
  }

  lemma LAAtTransOutside(a: LT.Tree, b: LT.Tree, c: LT.Tree, inp: LC.Input, S: set<LG.GroupId>)
    requires LeavesAgreeAtOutside(a, b, inp, S) && LeavesAgreeAtOutside(b, c, inp, S)
    ensures LeavesAgreeAtOutside(a, c, inp, S)
  {
    forall gm: LG.GroupMap
      ensures |LT.TreeLeaves(a, gm, inp, WP.Forward)| == |LT.TreeLeaves(c, gm, inp, WP.Forward)|
      ensures forall i :: 0 <= i < |LT.TreeLeaves(a, gm, inp, WP.Forward)| ==>
                LT.TreeLeaves(a, gm, inp, WP.Forward)[i].0 == LT.TreeLeaves(c, gm, inp, WP.Forward)[i].0
                && GmAgreeOutside(LT.TreeLeaves(a, gm, inp, WP.Forward)[i].1, LT.TreeLeaves(c, gm, inp, WP.Forward)[i].1, S)
    { forall i | 0 <= i < |LT.TreeLeaves(a, gm, inp, WP.Forward)|
        ensures LT.TreeLeaves(a, gm, inp, WP.Forward)[i].0 == LT.TreeLeaves(c, gm, inp, WP.Forward)[i].0
             && GmAgreeOutside(LT.TreeLeaves(a, gm, inp, WP.Forward)[i].1, LT.TreeLeaves(c, gm, inp, WP.Forward)[i].1, S)
      { GmAgreeOutsideTrans(LT.TreeLeaves(a, gm, inp, WP.Forward)[i].1,
                            LT.TreeLeaves(b, gm, inp, WP.Forward)[i].1,
                            LT.TreeLeaves(c, gm, inp, WP.Forward)[i].1, S); } }
  }

  lemma LAAtProgressPassOutside(t: LT.Tree, inp: LC.Input, S: set<LG.GroupId>)
    ensures LeavesAgreeAtOutside(LT.Progress(t), t, inp, S)
  { LAAtReflOutside(t, inp, S); }

  lemma LAAtCongProgressOutside(a: LT.Tree, b: LT.Tree, inp: LC.Input, S: set<LG.GroupId>)
    requires LeavesAgreeAtOutside(a, b, inp, S)
    ensures LeavesAgreeAtOutside(LT.Progress(a), LT.Progress(b), inp, S)
  {}

  lemma LAAtCongReadOutside(c: char, a: LT.Tree, b: LT.Tree, inp: LC.Input, S: set<LG.GroupId>)
    requires LeavesAgreeAtOutside(a, b, LC.AdvanceInputP(inp, WP.Forward), S)
    ensures LeavesAgreeAtOutside(LT.Read(c, a), LT.Read(c, b), inp, S)
  {}

  lemma LAAtCongGroupOutside(g: LG.GroupAction, a: LT.Tree, b: LT.Tree, inp: LC.Input, S: set<LG.GroupId>)
    requires LeavesAgreeAtOutside(a, b, inp, S)
    ensures LeavesAgreeAtOutside(LT.GroupActionT(g, a), LT.GroupActionT(g, b), inp, S)
  {}

  lemma LAAtCongAnchorOutside(an: L.Anchor, a: LT.Tree, b: LT.Tree, inp: LC.Input, S: set<LG.GroupId>)
    requires LeavesAgreeAtOutside(a, b, inp, S)
    ensures LeavesAgreeAtOutside(LT.AnchorPass(an, a), LT.AnchorPass(an, b), inp, S)
  {}

  lemma LAAtCongChoiceOutside(a1: LT.Tree, b1: LT.Tree, a2: LT.Tree, b2: LT.Tree, inp: LC.Input, S: set<LG.GroupId>)
    requires LeavesAgreeAtOutside(a1, b1, inp, S) && LeavesAgreeAtOutside(a2, b2, inp, S)
    ensures LeavesAgreeAtOutside(LT.Choice(a1, a2), LT.Choice(b1, b2), inp, S)
  {
    forall gm: LG.GroupMap
      ensures |LT.TreeLeaves(LT.Choice(a1, a2), gm, inp, WP.Forward)| == |LT.TreeLeaves(LT.Choice(b1, b2), gm, inp, WP.Forward)|
      ensures forall i :: 0 <= i < |LT.TreeLeaves(LT.Choice(a1, a2), gm, inp, WP.Forward)| ==>
                LT.TreeLeaves(LT.Choice(a1, a2), gm, inp, WP.Forward)[i].0 == LT.TreeLeaves(LT.Choice(b1, b2), gm, inp, WP.Forward)[i].0
                && GmAgreeOutside(LT.TreeLeaves(LT.Choice(a1, a2), gm, inp, WP.Forward)[i].1,
                                  LT.TreeLeaves(LT.Choice(b1, b2), gm, inp, WP.Forward)[i].1, S)
    {
      var x1: seq<LT.Leaf> := LT.TreeLeaves(a1, gm, inp, WP.Forward);
      var y1: seq<LT.Leaf> := LT.TreeLeaves(a2, gm, inp, WP.Forward);
      var x2: seq<LT.Leaf> := LT.TreeLeaves(b1, gm, inp, WP.Forward);
      var y2: seq<LT.Leaf> := LT.TreeLeaves(b2, gm, inp, WP.Forward);
      var L1: seq<LT.Leaf> := LT.TreeLeaves(LT.Choice(a1, a2), gm, inp, WP.Forward);
      var L2: seq<LT.Leaf> := LT.TreeLeaves(LT.Choice(b1, b2), gm, inp, WP.Forward);
      assert L1 == x1 + y1 && L2 == x2 + y2;
      forall i | 0 <= i < |L1|
        ensures L1[i].0 == L2[i].0 && GmAgreeOutside(L1[i].1, L2[i].1, S)
      { if i < |x1| { assert L1[i] == x1[i] && L2[i] == x2[i]; }
        else { assert L1[i] == y1[i - |x1|] && L2[i] == y2[i - |x1|]; } }
    }
  }

  lemma LAAtGatePass(lk: L.Lookaround, tlk: LT.Tree, tc: LT.Tree, inp: LC.Input)
    requires GmNeutralTree(tlk)
    requires L.Positivity(lk) ==> |LT.TreeLeaves(tlk, LG.Empty, inp, L.LkDir(lk))| > 0
    requires !L.Positivity(lk) ==> |LT.TreeLeaves(tlk, LG.Empty, inp, L.LkDir(lk))| == 0
    ensures LeavesAgreeAt(LT.LK(lk, tlk, tc), tc, inp)
  {
    forall gm: LG.GroupMap
      ensures LT.TreeLeaves(LT.LK(lk, tlk, tc), gm, inp, WP.Forward)
           == LT.TreeLeaves(tc, gm, inp, WP.Forward)
    {
      var sub := LT.TreeLeaves(tlk, gm, inp, L.LkDir(lk));
      // the verdict does not depend on the group map
      LT.FirstTreeLeaf(tlk, gm, inp, L.LkDir(lk));
      LT.FirstTreeLeaf(tlk, LG.Empty, inp, L.LkDir(lk));
      if |sub| == 0 {
        LT.HdErrorNoneNil(sub);
        LT.ResGroupMapIndep(tlk, gm, LG.Empty, inp, inp, L.LkDir(lk), L.LkDir(lk));
        assert LT.TreeRes(tlk, LG.Empty, inp, L.LkDir(lk)) == None;
        LT.HdErrorNoneNil(LT.TreeLeaves(tlk, LG.Empty, inp, L.LkDir(lk)));
      } else {
        assert LT.TreeRes(tlk, gm, inp, L.LkDir(lk)).Some?;
        if LT.TreeRes(tlk, LG.Empty, inp, L.LkDir(lk)) == None {
          LT.ResGroupMapIndep(tlk, LG.Empty, gm, inp, inp, L.LkDir(lk), L.LkDir(lk));
        }
        LT.HdErrorNoneNil(LT.TreeLeaves(tlk, LG.Empty, inp, L.LkDir(lk)));
        GmNeutralLeaves(tlk, gm, inp, L.LkDir(lk));
        assert sub[0].1 == gm;
      }
    }
  }

  /** A FAILING gate denotes nothing — just like the `Mismatch` the checked
      tree puts in its place. */
  lemma LAAtGateFail(lk: L.Lookaround, tlk: LT.Tree, inp: LC.Input)
    ensures LeavesAgreeAt(LT.LKFail(lk, tlk), LT.Mismatch, inp)
  {}

  // ===========================================================================
  // What the construction must know about the oracle
  // ===========================================================================

  /** The oracle column at `inp`'s position tells the truth about every
      lookaround the table knows: the bit is set exactly when the body's walk
      (in the lookaround's own direction) succeeds there. Stated over `Input`
      rather than a string+cp pair because the construction is string-free —
      `TR.CpOf(inp)` is the column. */
  ghost predicate OracleOkAt(rer: LW.RegExpRecord, qm: AR.QMap, inp: LC.Input) {
    forall lid: int, lk: L.Lookaround, r1: L.Regex ::
      lid in qm.looks && qm.looks[lid] == (lk, r1) ==>
        (LOr.view_get_oracle(qm.ov, TR.CpOf(inp), lid)
         <==> LT.TreeRes(FU.ComputeTr(rer, [LS.Areg(r1)], inp, LG.Empty, L.LkDir(lk)),
                         LG.Empty, inp, L.LkDir(lk)).Some?)
  }

  /** `OracleOkAt` here and at every position the walk can still reach — the
      form the construction carries, since it recurses into suffixes. */
  ghost predicate OracleOkSuffix(rer: LW.RegExpRecord, qm: AR.QMap, inp0: LC.Input) {
    forall inp: LC.Input :: (inp == inp0 || SSx.IsStrictSuffix(inp, inp0, WP.Forward))
                            ==> OracleOkAt(rer, qm, inp)
  }

  /** The hypothesis survives a read. */
  lemma OracleOkSuffixStep(rer: LW.RegExpRecord, qm: AR.QMap, inp0: LC.Input, inp1: LC.Input)
    requires OracleOkSuffix(rer, qm, inp0)
    requires inp1 == inp0 || SSx.IsStrictSuffix(inp1, inp0, WP.Forward)
    ensures OracleOkSuffix(rer, qm, inp1)
  {
    forall inp: LC.Input | inp == inp1 || SSx.IsStrictSuffix(inp, inp1, WP.Forward)
      ensures OracleOkAt(rer, qm, inp)
    {
      if inp != inp0 && !SSx.IsStrictSuffix(inp, inp0, WP.Forward) {
        assert inp != inp1;
        assert SSx.IsStrictSuffix(inp, inp1, WP.Forward);
        assert inp1 != inp0;
        assert SSx.IsStrictSuffix(inp1, inp0, WP.Forward);
        SSx.StrictSuffixTrans(inp, inp1, inp0, WP.Forward);
        assert false;
      }
    }
  }
}
