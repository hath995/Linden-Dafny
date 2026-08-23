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
include "LookLeaves.dfy"

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
  import CC = CaptureContent
  import LL = LindenElkLookLeaves

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

  // ===========================================================================
  // BRICK 2 helpers: bounds, confinement bridges, mirror-agree
  // ===========================================================================

  /** One group action keeps a bounded map bounded (all endpoints stay `<= n`
      because `currIdx <= n` and existing endpoints are `<= n`). */
  lemma GMUpdateInBounds(op: LG.GroupAction, idx: nat, gm: LG.GroupMap, n: nat)
    requires idx <= n
    requires TRM.GmInBounds(gm, n)
    ensures TRM.GmInBounds(LG.GMUpdate(op, idx, gm), n)
  {
    match op
    case Open(g) =>
    case Close(g) => { match LG.Find(g, gm) { case Some(rg) => case None => } }
    case Reset(gs) =>
  }

  /** A tree's `TreeRes` leaf stays within `[0, n]` when the starting map is
      bounded and the input length is `n` (every captured endpoint is some
      `Idx(inp') <= n`). Direction-generic; recurses through look bodies. */
  lemma TreeResGmInBounds(t: LT.Tree, gm: LG.GroupMap, inp: LC.Input, dir: WP.Direction, n: nat)
    requires n == |inp.pref| + |inp.next|
    requires TRM.GmInBounds(gm, n)
    requires LT.TreeRes(t, gm, inp, dir).Some?
    ensures TRM.GmInBounds(LT.TreeRes(t, gm, inp, dir).value.1, n)
    decreases t
  {
    match t
    case Match =>
    case Choice(t1, t2) =>
      if LT.TreeRes(t1, gm, inp, dir).Some? { TreeResGmInBounds(t1, gm, inp, dir, n); }
      else { TreeResGmInBounds(t2, gm, inp, dir, n); }
    case Read(_, t1) =>
      var inp' := LC.AdvanceInputP(inp, dir);
      assert n == |inp'.pref| + |inp'.next|;
      TreeResGmInBounds(t1, gm, inp', dir, n);
    case ReadBackRef(brStr, t1) =>
      var inp' := LC.AdvanceInputN(inp, |brStr|, dir);
      AdvanceInputNLen(inp, |brStr|, dir);
      TreeResGmInBounds(t1, gm, inp', dir, n);
    case Progress(t1) => TreeResGmInBounds(t1, gm, inp, dir, n);
    case AnchorPass(_, t1) => TreeResGmInBounds(t1, gm, inp, dir, n);
    case GroupActionT(a, t1) =>
      assert LC.Idx(inp) <= n;
      GMUpdateInBounds(a, LC.Idx(inp), gm, n);
      TreeResGmInBounds(t1, LG.GMUpdate(a, LC.Idx(inp), gm), inp, dir, n);
    case LK(lk, tlk, t1) =>
      if L.Positivity(lk) {
        match LT.TreeRes(tlk, gm, inp, L.LkDir(lk)) {
          case Some(pair) =>
            TreeResGmInBounds(tlk, gm, inp, L.LkDir(lk), n);
            TreeResGmInBounds(t1, pair.1, inp, dir, n);
          case None =>
        }
      } else {
        match LT.TreeRes(tlk, gm, inp, L.LkDir(lk)) {
          case None => TreeResGmInBounds(t1, gm, inp, dir, n);
          case Some(_) =>
        }
      }
    case Mismatch =>
    case LKFail(_, _) =>
  }

  /** `AdvanceInputN` keeps the total length. */
  lemma AdvanceInputNLen(inp: LC.Input, k: nat, dir: WP.Direction)
    ensures |LC.AdvanceInputN(inp, k, dir).pref| + |LC.AdvanceInputN(inp, k, dir).next|
         == |inp.pref| + |inp.next|
  {
    match dir
    case Forward => LS.ReverseLength(LC.Take(inp.next, k));
    case Backward => LS.ReverseLength(LC.Take(inp.pref, k));
  }

  /** A tree confined to `S` never touches a group outside `S` (bridge from
      `CE.LkConfinedTreeRec` to `CC.NoGidAction`). */
  lemma ConfinedNoGid(t: LT.Tree, S: set<LG.GroupId>, g: LG.GroupId)
    requires CE.LkConfinedTreeRec(t, S)
    requires g !in S
    ensures CC.NoGidAction(t, g)
    decreases t
  {
    match t
    case Mismatch =>
    case Match =>
    case Choice(t1, t2) => ConfinedNoGid(t1, S, g); ConfinedNoGid(t2, S, g);
    case Read(_, t1) => ConfinedNoGid(t1, S, g);
    case ReadBackRef(_, t1) => ConfinedNoGid(t1, S, g);
    case Progress(t1) => ConfinedNoGid(t1, S, g);
    case AnchorPass(_, t1) => ConfinedNoGid(t1, S, g);
    case GroupActionT(a, t1) =>
      assert CC.GidUntouched(a, g) by { match a case Open(x) => case Close(x) => case Reset(gs) => assert g !in gs; }
      ConfinedNoGid(t1, S, g);
    case LK(_, tlk, t1) => ConfinedNoGid(tlk, S, g); ConfinedNoGid(t1, S, g);
    case LKFail(_, tlk) => ConfinedNoGid(tlk, S, g);
  }

  /** A confined tree's `TreeRes` leaf agrees with its starting map OUTSIDE `S`
      (it only writes groups inside `S`). */
  lemma ConfinedLeafAgree(t: LT.Tree, gm: LG.GroupMap, inp: LC.Input, dir: WP.Direction,
                          S: set<LG.GroupId>)
    requires CE.LkConfinedTreeRec(t, S)
    requires LT.TreeRes(t, gm, inp, dir).Some?
    ensures LL.GmAgreeOutside(LT.TreeRes(t, gm, inp, dir).value.1, gm, S)
  {
    var leaf := LT.TreeRes(t, gm, inp, dir).value.1;
    forall g | g !in S ensures (g in leaf <==> g in gm) && (g in leaf ==> leaf[g] == gm[g]) {
      ConfinedNoGid(t, S, g);
      CC.TreeResPreservesGid(t, gm, inp, dir, g);
      assert LG.Find(g, leaf) == LG.Find(g, gm);
    }
  }

  /** `MirrorGm` preserves outside-`S` agreement (it maps each range pointwise,
      so groups the two maps agree on are mapped identically). */
  lemma MirrorGmAgreeOutside(a: LG.GroupMap, b: LG.GroupMap, n: nat, S: set<LG.GroupId>)
    requires TRM.GmInBounds(a, n) && TRM.GmInBounds(b, n)
    requires LL.GmAgreeOutside(a, b, S)
    ensures LL.GmAgreeOutside(TRM.MirrorGm(a, n), TRM.MirrorGm(b, n), S)
  {
    forall g | g !in S
      ensures (g in TRM.MirrorGm(a, n) <==> g in TRM.MirrorGm(b, n))
           && (g in TRM.MirrorGm(a, n) ==> TRM.MirrorGm(a, n)[g] == TRM.MirrorGm(b, n)[g])
    {
      TRM.MirrorGmAt(a, n);
      TRM.MirrorGmAt(b, n);
    }
  }
}
