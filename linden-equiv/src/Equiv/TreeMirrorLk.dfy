// L5 (nested capturing lookBEHIND) — the CAPTURES value tie.
//
// The depth-1 lookbehind keystone (`LkReplayMatchesSpecLB`) routes the body's
// captures through the SPEC mirror `BackBodyGmTie`:
//   ComputeTr(tr, Backward)  ~TreeMirrorRel~  ComputeTr(RevL(tr), Forward)
// which folds to `TreeResMirror` (leaves mirror under `MirrorGm`). That mirror
// is `GroupOkL`-gated (LOOK-FREE bodies): its `TreeMirrorRel` has no LK case.
//
// For a NESTED body the raw spec mirror DIES: a nested inner look is re-walked
// on both sides, and `RevL` keeps its direction (no flip), so the backward
// original reads chars BEFORE the point while the forward-RevL side reads chars
// AFTER it — the inner gate (and its captures) disagree. This is a proven
// dead-end for the RE-WALK tree.
//
// THE FIX (this file): the SURFACE captures still mirror, provided the inner
// look GATES agree. They DO agree — but only through the ORACLE, which is
// position-consistent across `MirrorView` (`MirrorView(ov,n)[n-i] == ov[i]`, no
// direction flip) and tied to each side's LkDir-walk by the direction-generic
// `LL.OracleOkAt`. So we extend the mirror relation with LK/LKFail cases that
// (a) require the two looks to have the SAME kind and their surface
// CONTINUATIONS to mirror, and (b) EXCLUDE the inner sub-trees (they can't
// tree-mirror). The mixed `(LK, LKFail)` pairing is disallowed, so the relation
// STRUCTURALLY encodes gate agreement; the builder `ComputeTrReverseLk`
// discharges it via the oracle. The leaves then mirror OUTSIDE the inner-look
// groups `Sin = LkBodyGroups(tr)` — exactly the split the L4 forward keystone
// (`LkReplayMatchesSpecNested`) already uses (surface internal, inner via the
// oracle reconstruction).

include "LookBehindValue.dfy"
include "CheckErase.dfy"

module LindenElkTreeMirrorLk {
  import opened Std.Wrappers
  import LW = WarblreRegExpRecord
  import WP = WarblrePrimitives
  import LC = Chars
  import LG = Groups
  import L = Regex
  import LS = Semantics
  import LT = Tree
  import FU = FunctionalUtils
  import SD = LindenSpanDuality
  import TM = LindenTreeMirror
  import TRM = LindenTreeResMirror
  import CE = LindenElkCheckErase

  // ===========================================================================
  // BRICK 1: the LK-extended mirror relation
  // ===========================================================================

  /** Backward tree `t` and forward tree `tm` correspond on the SURFACE (groups
      outside the inner-look set `Sin`): same shape/priority/reads/anchors/group
      actions as `TreeMirrorRel`, PLUS an LK/LKFail rule. At a nested inner look
      the two looks share their kind `lk` and their surface CONTINUATIONS mirror;
      the inner sub-trees `tlk`/`tlkm` are UNRELATED (they provably can't
      tree-mirror — see the file header). The mixed `(LK, LKFail)` pairing is
      disallowed (default `false`), so the relation ENCODES gate agreement: `t`
      has `LK` iff `tm` has `LK` (both looks passed) and `LKFail` iff `LKFail`
      (both failed). */
  ghost predicate TreeMirrorRelLk(t: LT.Tree, tm: LT.Tree, Sin: set<LG.GroupId>)
    decreases t
  {
    match (t, tm)
    case (Mismatch, Mismatch) => true
    case (Match, Match) => true
    case (Choice(a, b), Choice(am, bm)) =>
      TreeMirrorRelLk(a, am, Sin) && TreeMirrorRelLk(b, bm, Sin)
    case (Read(c, a), Read(cm, am)) => c == cm && TreeMirrorRelLk(a, am, Sin)
    case (Progress(a), Progress(am)) => TreeMirrorRelLk(a, am, Sin)
    case (AnchorPass(x, a), AnchorPass(xm, am)) =>
      xm == SD.SwapAnchorL(x) && TreeMirrorRelLk(a, am, Sin)
    case (GroupActionT(ga, a), GroupActionT(gam, am)) =>
      TM.GroupActionMirror(ga, gam) && TreeMirrorRelLk(a, am, Sin)
    case (LK(lk, tlk, tc), LK(lk2, tlkm, tcm)) =>
      lk == lk2 && TreeMirrorRelLk(tc, tcm, Sin)
    case (LKFail(lk, tlk), LKFail(lk2, tlkm)) =>
      lk == lk2
    case _ => false
  }

  /** The look-free mirror `TreeMirrorRel` is the LK-free special case: it never
      produces LK/LKFail (its own `case _ => false`), so it implies the extended
      relation at any `Sin`. This lets the nested machinery subsume the depth-1
      surface segments unchanged. */
  lemma TreeMirrorRelLkFromRel(t: LT.Tree, tm: LT.Tree, Sin: set<LG.GroupId>)
    requires TM.TreeMirrorRel(t, tm)
    ensures TreeMirrorRelLk(t, tm, Sin)
    decreases t
  {
    match (t, tm)
    case (Choice(a, b), Choice(am, bm)) =>
      TreeMirrorRelLkFromRel(a, am, Sin);
      TreeMirrorRelLkFromRel(b, bm, Sin);
    case (Read(c, a), Read(cm, am)) => TreeMirrorRelLkFromRel(a, am, Sin);
    case (Progress(a), Progress(am)) => TreeMirrorRelLkFromRel(a, am, Sin);
    case (AnchorPass(x, a), AnchorPass(xm, am)) => TreeMirrorRelLkFromRel(a, am, Sin);
    case (GroupActionT(ga, a), GroupActionT(gam, am)) => TreeMirrorRelLkFromRel(a, am, Sin);
    case _ =>
  }
}
