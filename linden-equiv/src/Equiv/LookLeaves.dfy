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
}
