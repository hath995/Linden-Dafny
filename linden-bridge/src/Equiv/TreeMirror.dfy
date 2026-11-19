// L3b (linden-equiv LOOKAROUND_CAMPAIGN.md §4.5.1 item 4, the spec half):
// the PRIORITY-AWARE tree-level reversal — the assembly SpanDuality's
// "(4) CONCATENATION ORDER" note showed was tractable and left open.
//
// SuccActsReverse (SpanDuality) relates the two scan directions
// EXISTENTIALLY: the backward walk succeeds iff the forward walk of the
// reversed stack succeeds. Capturing lookbehinds need more: the engine's
// backward capture replay is priority-correct (first leaf), so the SPEC
// correspondence must relate the WHOLE backtracking trees, preserving
// Choice order — from which first-leaf correspondence follows.
//
// The statement (ComputeTreeReverse): for group-OK stacks (no lookarounds,
// no backreferences — Groups allowed; the L3b lookbehind-body fragment),
//
//   ComputeTree(acts, inp, gm1, Backward, fuel)
//     ~TreeMirrorRel~
//   ComputeTree(RevActs(acts), SwapInput(inp), gm2, Forward, fuel)
//
// where TreeMirrorRel is structural EQUALITY except: anchors swap
// (AnchorPass payloads related by SwapAnchorL) and Reset payloads agree as
// SETS (RevL permutes DefGroups) — exactly the equivalence the SpanDuality
// note predicted. Group maps on the two sides are UNRELATED (arbitrary):
// under GroupOk the tree never reads the map (ComputeTreeGroupOkGmIndep's
// argument), so no map correspondence is needed to BUILD the trees. The
// map correspondence enters only when FOLDING leaves (TreeRes) — that is
// the follow-up lemma, which consumes this one.
//
// The induction is fuel-parallel: both sides consume fuel identically,
// case for case, because RevActs maps each head action to exactly the
// head action the mirrored computation dispatches on (SeqListReverse is
// the load-bearing alignment: the spec ALREADY swaps concatenation order
// when scanning backward).

include "SpanDuality.dfy"

/** The tree-level reversal: backward backtracking trees mirror forward
    trees of the reversed stack, priorities preserved. */
module LindenTreeMirror {
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
  import SSx = StrictSuffix
  import SD = LindenSpanDuality

  // ===========================================================================
  // The relation: equal trees up to the anchor swap and Reset-payload
  // permutation
  // ===========================================================================

  /** Two group actions mirror: identical, except `Reset` payloads need only
      agree as sets (`RevL` permutes `DefGroups`). */
  ghost predicate GroupActionMirror(ga: LG.GroupAction, gam: LG.GroupAction) {
    match (ga, gam)
    case (Open(g), Open(g2)) => g == g2
    case (Close(g), Close(g2)) => g == g2
    case (Reset(gl), Reset(gl2)) => forall g: LG.GroupId :: g in gl <==> g in gl2
    case _ => false
  }

  /** Backward tree `t` and forward tree `tm` correspond: same shape, same
      Choice order (priority!), same characters read, group actions mirrored,
      anchors swapped. No `LK`/`LKFail`/`ReadBackRef` cases — the group-OK
      fragment produces none. */
  ghost predicate TreeMirrorRel(t: LT.Tree, tm: LT.Tree) {
    match (t, tm)
    case (Mismatch, Mismatch) => true
    case (Match, Match) => true
    case (Choice(a, b), Choice(am, bm)) => TreeMirrorRel(a, am) && TreeMirrorRel(b, bm)
    case (Read(c, a), Read(cm, am)) => c == cm && TreeMirrorRel(a, am)
    case (Progress(a), Progress(am)) => TreeMirrorRel(a, am)
    case (AnchorPass(x, a), AnchorPass(xm, am)) =>
      xm == SD.SwapAnchorL(x) && TreeMirrorRel(a, am)
    case (GroupActionT(ga, a), GroupActionT(gam, am)) =>
      GroupActionMirror(ga, gam) && TreeMirrorRel(a, am)
    case _ => false
  }

  // ===========================================================================
  // Small stack plumbing
  // ===========================================================================

  /** `RevActs` distributes over concatenation (it is a pointwise map). */
  lemma RevActsAppend(xs: LS.Actions, ys: LS.Actions)
    ensures SD.RevActs(xs + ys) == SD.RevActs(xs) + SD.RevActs(ys)
  {
    var lhs := SD.RevActs(xs + ys);
    var rhs := SD.RevActs(xs) + SD.RevActs(ys);
    assert |lhs| == |rhs|;
    forall i | 0 <= i < |lhs| ensures lhs[i] == rhs[i] {
      if i < |xs| { assert (xs + ys)[i] == xs[i]; } else { assert (xs + ys)[i] == ys[i - |xs|]; }
    }
  }

  /** The reversal keeps a stack group-OK. */
  lemma RevActsGroupOk(acts: LS.Actions)
    requires SD.GroupOkActs(acts)
    ensures SD.GroupOkActs(SD.RevActs(acts))
  {
    forall i | 0 <= i < |SD.RevActs(acts)| && SD.RevActs(acts)[i].Areg?
      ensures SD.GroupOkL(SD.RevActs(acts)[i].r)
    {
      assert acts[i].Areg?;
      SD.RevLGroupOk(acts[i].r);
    }
  }

  // ===========================================================================
  // THE TREE CORRESPONDENCE
  // ===========================================================================

  /** A backward `ComputeTree` and the forward `ComputeTree` of the reversed
      stack over the swapped input run out of fuel together, and — when they
      complete — produce `TreeMirrorRel` trees. The group maps are arbitrary
      and UNRELATED: a group-OK stack's tree never reads the map. */
  lemma ComputeTreeReverse(rer: LW.RegExpRecord, acts: LS.Actions, inp: LC.Input,
                           gm1: LG.GroupMap, gm2: LG.GroupMap, fuel: nat)
    requires SD.GroupOkActs(acts)
    ensures var b := FS.ComputeTree(rer, acts, inp, gm1, WP.Backward, fuel);
            var fw := FS.ComputeTree(rer, SD.RevActs(acts), SD.SwapInput(inp), gm2,
                                     WP.Forward, fuel);
            (b.None? <==> fw.None?)
            && (b.Some? && fw.Some? ==> TreeMirrorRel(b.value, fw.value))
    decreases fuel
  {
    var racts := SD.RevActs(acts);
    var sinp := SD.SwapInput(inp);
    if fuel == 0 { return; }
    var f := fuel - 1;
    if |acts| == 0 {
      assert racts == [];
      return;
    }
    var cont := acts[1..];
    SD.GroupOkActsTail(acts);
    SD.RevActsTail(acts);
    assert racts[1..] == SD.RevActs(cont);
    match acts[0]
    case Acheck(strcheck) =>
      assert racts[0] == LS.Acheck(SD.SwapInput(strcheck));
      SD.IsStrictSuffixSwap(inp, strcheck);
      if SSx.IsStrictSuffix(inp, strcheck, WP.Backward) {
        ComputeTreeReverse(rer, cont, inp, gm1, gm2, f);
      }
    case Aclose(gid) =>
      assert racts[0] == LS.Aclose(gid);
      ComputeTreeReverse(rer, cont, inp, LG.GMClose(LC.Idx(inp), gid, gm1),
                         LG.GMClose(LC.Idx(sinp), gid, gm2), f);
    case Areg(r) =>
      assert racts[0] == LS.Areg(SD.RevL(r));
      match r
      case Epsilon =>
        ComputeTreeReverse(rer, cont, inp, gm1, gm2, f);
      case Character(cd) =>
        SD.ReadCharSwap(rer, cd, inp);
        match LC.ReadChar(rer, cd, inp, WP.Backward) {
          case Some(pair) =>
            ComputeTreeReverse(rer, cont, pair.1, gm1, gm2, f);
          case None =>
        }
      case Disjunction(r1, r2) =>
        assert SD.RevL(r) == L.Disjunction(SD.RevL(r1), SD.RevL(r2));
        SD.GroupOkActsCons(LS.Areg(r1), cont);
        SD.GroupOkActsCons(LS.Areg(r2), cont);
        SD.RevActsCons(LS.Areg(r1), cont);
        SD.RevActsCons(LS.Areg(r2), cont);
        ComputeTreeReverse(rer, [LS.Areg(r1)] + cont, inp, gm1, gm2, f);
        ComputeTreeReverse(rer, [LS.Areg(r2)] + cont, inp, gm1, gm2, f);
      case Sequence(r1, r2) =>
        assert SD.RevL(r) == L.Sequence(SD.RevL(r2), SD.RevL(r1));
        assert LS.SeqList(r1, r2, WP.Backward) == [LS.Areg(r2), LS.Areg(r1)];
        assert LS.SeqList(SD.RevL(r2), SD.RevL(r1), WP.Forward)
            == [LS.Areg(SD.RevL(r2)), LS.Areg(SD.RevL(r1))];
        SD.SeqListReverse(r1, r2);
        RevActsAppend([LS.Areg(r2), LS.Areg(r1)], cont);
        SD.GroupOkActsCons(LS.Areg(r1), cont);
        SD.GroupOkActsCons(LS.Areg(r2), [LS.Areg(r1)] + cont);
        assert [LS.Areg(r2), LS.Areg(r1)] + cont == [LS.Areg(r2)] + ([LS.Areg(r1)] + cont);
        ComputeTreeReverse(rer, [LS.Areg(r2), LS.Areg(r1)] + cont, inp, gm1, gm2, f);
      case Quantified(greedy, min, delta, r1) =>
        assert SD.RevL(r) == L.Quantified(greedy, min, delta, SD.RevL(r1));
        var gidl := L.DefGroups(r1);
        var gidlm := L.DefGroups(SD.RevL(r1));
        SD.RevLDefGroupsSet(r1);
        if min > 0 {
          var q1 := L.Quantified(greedy, min - 1, delta, r1);
          assert SD.RevL(q1) == L.Quantified(greedy, min - 1, delta, SD.RevL(r1));
          SD.GroupOkActsCons(LS.Areg(q1), cont);
          SD.GroupOkActsCons(LS.Areg(r1), [LS.Areg(q1)] + cont);
          RevActsAppend([LS.Areg(r1), LS.Areg(q1)], cont);
          assert SD.RevActs([LS.Areg(r1), LS.Areg(q1)])
              == [LS.Areg(SD.RevL(r1)), LS.Areg(SD.RevL(q1))];
          assert [LS.Areg(r1), LS.Areg(q1)] + cont == [LS.Areg(r1)] + ([LS.Areg(q1)] + cont);
          ComputeTreeReverse(rer, [LS.Areg(r1), LS.Areg(q1)] + cont, inp,
                             LG.GMReset(gidl, gm1), LG.GMReset(gidlm, gm2), f);
          var bi := FS.ComputeTree(rer, [LS.Areg(r1), LS.Areg(q1)] + cont, inp,
                                   LG.GMReset(gidl, gm1), WP.Backward, f);
          var fi := FS.ComputeTree(rer, SD.RevActs([LS.Areg(r1), LS.Areg(q1)] + cont), sinp,
                                   LG.GMReset(gidlm, gm2), WP.Forward, f);
          if bi.Some? && fi.Some? {
            assert GroupActionMirror(LG.Reset(gidl), LG.Reset(gidlm));
            assert TreeMirrorRel(LT.GroupActionT(LG.Reset(gidl), bi.value),
                                 LT.GroupActionT(LG.Reset(gidlm), fi.value));
          }
        } else if delta == LN.NN(0) {
          ComputeTreeReverse(rer, cont, inp, gm1, gm2, f);
        } else {
          var q0 := L.Quantified(greedy, 0, FS.NoiPred(delta), r1);
          assert SD.RevL(q0) == L.Quantified(greedy, 0, FS.NoiPred(delta), SD.RevL(r1));
          SD.GroupOkActsCons(LS.Areg(q0), cont);
          SD.GroupOkActsCons(LS.Acheck(inp), [LS.Areg(q0)] + cont);
          SD.GroupOkActsCons(LS.Areg(r1), [LS.Acheck(inp)] + ([LS.Areg(q0)] + cont));
          RevActsAppend([LS.Areg(r1), LS.Acheck(inp), LS.Areg(q0)], cont);
          assert SD.RevActs([LS.Areg(r1), LS.Acheck(inp), LS.Areg(q0)])
              == [LS.Areg(SD.RevL(r1)), LS.Acheck(sinp), LS.Areg(SD.RevL(q0))];
          assert [LS.Areg(r1), LS.Acheck(inp), LS.Areg(q0)] + cont
              == [LS.Areg(r1)] + ([LS.Acheck(inp)] + ([LS.Areg(q0)] + cont));
          ComputeTreeReverse(rer, [LS.Areg(r1), LS.Acheck(inp), LS.Areg(q0)] + cont, inp,
                             LG.GMReset(gidl, gm1), LG.GMReset(gidlm, gm2), f);
          ComputeTreeReverse(rer, cont, inp, gm1, gm2, f);
          // assemble the GreedyChoice arms explicitly: the reset-wrapped
          // iteration trees mirror (Reset payloads agree as sets), and the
          // skip trees mirror; Choice order is the same on both sides.
          var bi := FS.ComputeTree(rer, [LS.Areg(r1), LS.Acheck(inp), LS.Areg(q0)] + cont,
                                   inp, LG.GMReset(gidl, gm1), WP.Backward, f);
          var fi := FS.ComputeTree(rer, SD.RevActs([LS.Areg(r1), LS.Acheck(inp), LS.Areg(q0)] + cont),
                                   sinp, LG.GMReset(gidlm, gm2), WP.Forward, f);
          var bs := FS.ComputeTree(rer, cont, inp, gm1, WP.Backward, f);
          var fs := FS.ComputeTree(rer, SD.RevActs(cont), sinp, gm2, WP.Forward, f);
          if bi.Some? && bs.Some? && fi.Some? && fs.Some? {
            assert GroupActionMirror(LG.Reset(gidl), LG.Reset(gidlm));
            assert TreeMirrorRel(LT.GroupActionT(LG.Reset(gidl), bi.value),
                                 LT.GroupActionT(LG.Reset(gidlm), fi.value));
            assert TreeMirrorRel(bs.value, fs.value);
          }
        }
      case Group(gid, r1) =>
        assert SD.RevL(r) == L.Group(gid, SD.RevL(r1));
        SD.GroupOkActsCons(LS.Aclose(gid), cont);
        SD.GroupOkActsCons(LS.Areg(r1), [LS.Aclose(gid)] + cont);
        RevActsAppend([LS.Areg(r1), LS.Aclose(gid)], cont);
        assert SD.RevActs([LS.Areg(r1), LS.Aclose(gid)])
            == [LS.Areg(SD.RevL(r1)), LS.Aclose(gid)];
        assert [LS.Areg(r1), LS.Aclose(gid)] + cont
            == [LS.Areg(r1)] + ([LS.Aclose(gid)] + cont);
        ComputeTreeReverse(rer, [LS.Areg(r1), LS.Aclose(gid)] + cont, inp,
                           LG.GMOpen(LC.Idx(inp), gid, gm1),
                           LG.GMOpen(LC.Idx(sinp), gid, gm2), f);
      case LookaroundR(lk, r1) =>
        assert SD.GroupOkL(r);
        assert false;
      case AnchorR(a) =>
        assert SD.RevL(r) == L.AnchorR(SD.SwapAnchorL(a));
        SD.AnchorSatisfiedSwap(rer, a, inp);
        if LS.AnchorSatisfied(rer, a, inp) {
          ComputeTreeReverse(rer, cont, inp, gm1, gm2, f);
        }
      case Backreference(gid) =>
        assert SD.GroupOkL(r);
        assert false;
  }

  // ===========================================================================
  // The fuel-free corollary
  // ===========================================================================

  /** `ComputeTr`-level form: the backward tree of a group-OK stack mirrors
      the forward tree of the reversed stack over the swapped input, at ANY
      pair of group maps. */
  lemma ComputeTrReverse(rer: LW.RegExpRecord, acts: LS.Actions, inp: LC.Input,
                         gm1: LG.GroupMap, gm2: LG.GroupMap)
    requires SD.GroupOkActs(acts)
    ensures TreeMirrorRel(FU.ComputeTr(rer, acts, inp, gm1, WP.Backward),
                          FU.ComputeTr(rer, SD.RevActs(acts), SD.SwapInput(inp), gm2,
                                       WP.Forward))
  {
    var fb := FS.ActionsFuel(acts, inp, WP.Backward) + 1;
    var ff := FS.ActionsFuel(SD.RevActs(acts), SD.SwapInput(inp), WP.Forward) + 1;
    SD.ActionsFuelReverse(acts, inp);
    assert fb == ff;
    FS.FunctionalTerminates(rer, acts, inp, gm1, WP.Backward, fb);
    RevActsGroupOk(acts);
    FS.FunctionalTerminates(rer, SD.RevActs(acts), SD.SwapInput(inp), gm2, WP.Forward, ff);
    ComputeTreeReverse(rer, acts, inp, gm1, gm2, fb);
  }
}
