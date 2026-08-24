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
  import TR = LindenElkTreeRep
  import MIR = LindenElkMirror
  import AR = LindenElkActionsRep
  import LOr = Oracle
  import PIV = LindenElkPikeInv
  import EL = LindenElkEntryLk
  import FS = FunctionalSemantics
  import CI = ComputeIsTree
  import LN = WarblreNumeric
  import SSx = StrictSuffix

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

  // ===========================================================================
  // BRICK 2: the surface leaf fold
  // ===========================================================================

  /** Close discipline for LK-bearing trees: like `TRM.CloseDisc` on the surface,
      but an `LK` node's Close discipline is just its CONTINUATION's (the inner
      sub-tree is a self-contained confined walk), and `LKFail` has no leaves. */
  ghost predicate CloseDiscLk(t: LT.Tree, O: set<LG.GroupId>)
    decreases t
  {
    match t
    case Mismatch => true
    case Match => true
    case Choice(a, b) => CloseDiscLk(a, O) && CloseDiscLk(b, O)
    case Read(_, a) => CloseDiscLk(a, O)
    case ReadBackRef(_, a) => CloseDiscLk(a, O)
    case Progress(a) => CloseDiscLk(a, O)
    case AnchorPass(_, a) => CloseDiscLk(a, O)
    case GroupActionT(ga, a) =>
      match ga {
        case Open(g) => CloseDiscLk(a, O + {g})
        case Close(g) => g in O && CloseDiscLk(a, O - {g})
        case Reset(gl) => CloseDiscLk(a, O - (set g | g in gl))
      }
    case LK(_, _, tc) => CloseDiscLk(tc, O)
    case LKFail(_, _) => true
  }

  /** One group action's groups are disjoint from `Sin`. */
  ghost predicate GADisjoint(ga: LG.GroupAction, Sin: set<LG.GroupId>) {
    match ga
    case Open(g) => g !in Sin
    case Close(g) => g !in Sin
    case Reset(gl) => forall g :: g in gl ==> g !in Sin
  }

  /** Every SURFACE group action (outside inner looks) acts on groups disjoint
      from `Sin`. True for a spec tree of a nested body: surface groups are
      `DefGroups(tr) \ LkBodyGroups(tr)`, disjoint from `Sin = LkBodyGroups`. */
  ghost predicate GActsOutsideSin(t: LT.Tree, Sin: set<LG.GroupId>)
    decreases t
  {
    match t
    case Mismatch => true
    case Match => true
    case Choice(a, b) => GActsOutsideSin(a, Sin) && GActsOutsideSin(b, Sin)
    case Read(_, a) => GActsOutsideSin(a, Sin)
    case ReadBackRef(_, a) => GActsOutsideSin(a, Sin)
    case Progress(a) => GActsOutsideSin(a, Sin)
    case AnchorPass(_, a) => GActsOutsideSin(a, Sin)
    case GroupActionT(ga, a) => GADisjoint(ga, Sin) && GActsOutsideSin(a, Sin)
    case LK(_, _, tc) => GActsOutsideSin(tc, Sin)
    case LKFail(_, _) => true
  }

  /** Gate stability: at every reachable LK node the gate re-evaluates the same
      way for ANY group map (positive => always Some, negative => always None),
      so the STRUCTURAL node type (LK vs LKFail) matches the folded gate. Holds
      for spec trees of the fragment by `EL.ComputeTrGmIndepLkRec`. */
  ghost predicate GateStableLk(t: LT.Tree, inp: LC.Input, dir: WP.Direction)
    decreases t
  {
    match t
    case Mismatch => true
    case Match => true
    case Choice(a, b) => GateStableLk(a, inp, dir) && GateStableLk(b, inp, dir)
    case Read(_, a) => GateStableLk(a, LC.AdvanceInputP(inp, dir), dir)
    case ReadBackRef(brStr, a) => GateStableLk(a, LC.AdvanceInputN(inp, |brStr|, dir), dir)
    case Progress(a) => GateStableLk(a, inp, dir)
    case AnchorPass(_, a) => GateStableLk(a, inp, dir)
    case GroupActionT(_, a) => GateStableLk(a, inp, dir)
    case LK(lk, tlk, tc) =>
      (if L.Positivity(lk) then (forall gm :: LT.TreeRes(tlk, gm, inp, L.LkDir(lk)).Some?)
                           else (forall gm :: LT.TreeRes(tlk, gm, inp, L.LkDir(lk)).None?))
      && GateStableLk(tc, inp, dir)
    case LKFail(_, _) => true
  }

  /** THE SURFACE FOLD. Two `TreeMirrorRelLk`-related trees fold to leaves that
      mirror OUTSIDE the inner-look groups `Sin`: `None` iff `None`, and on a
      match the winning-leaf inputs swap and the group maps agree outside `Sin`
      under `MirrorGm`. The forward map `gm2` need only agree with `MirrorGm(gm1)`
      OUTSIDE `Sin` (the inner captures, which don't mirror, are free). */
  lemma TreeResMirrorLk(t: LT.Tree, tm: LT.Tree, gm1: LG.GroupMap, gm2: LG.GroupMap,
                        inp: LC.Input, n: nat, O: set<LG.GroupId>, Sin: set<LG.GroupId>)
    requires TreeMirrorRelLk(t, tm, Sin)
    requires n == |inp.pref| + |inp.next|
    requires TRM.GmInBounds(gm1, n)
    requires CloseDiscLk(t, O)
    requires TRM.OpenSubset(gm1, O)
    requires O !! Sin
    requires GActsOutsideSin(t, Sin)
    requires LL.GmAgreeOutside(gm2, TRM.MirrorGm(gm1, n), Sin)
    requires CE.LkConfinedTreeK(t, Sin)
    requires CE.LkConfinedTreeK(tm, Sin)
    requires GateStableLk(t, inp, WP.Backward)
    requires GateStableLk(tm, SD.SwapInput(inp), WP.Forward)
    ensures var rb := LT.TreeRes(t, gm1, inp, WP.Backward);
            var rf := LT.TreeRes(tm, gm2, SD.SwapInput(inp), WP.Forward);
            && (rb.None? <==> rf.None?)
            && (rb.Some? ==>
                  && rf.Some?
                  && rf.value.0 == SD.SwapInput(rb.value.0)
                  && TRM.GmInBounds(rb.value.1, n)
                  && LL.GmAgreeOutside(rf.value.1, TRM.MirrorGm(rb.value.1, n), Sin))
    decreases t
  {
    var sinp := SD.SwapInput(inp);
    assert LC.Idx(sinp) == n - LC.Idx(inp);
    match t
    case Mismatch =>
    case Match =>
    case Choice(a, b) =>
      match tm {
        case Choice(am, bm) =>
          TreeResMirrorLk(a, am, gm1, gm2, inp, n, O, Sin);
          TreeResMirrorLk(b, bm, gm1, gm2, inp, n, O, Sin);
        case _ =>
      }
    case Read(c, a) =>
      match tm {
        case Read(cm, am) =>
          var inp' := LC.AdvanceInputP(inp, WP.Backward);
          TRM.AdvanceInputPSwap(inp);
          TRM.AdvanceInputPLen(inp, WP.Backward);
          assert LC.AdvanceInputP(sinp, WP.Forward) == SD.SwapInput(inp');
          TreeResMirrorLk(a, am, gm1, gm2, inp', n, O, Sin);
        case _ =>
      }
    case Progress(a) =>
      match tm {
        case Progress(am) => TreeResMirrorLk(a, am, gm1, gm2, inp, n, O, Sin);
        case _ =>
      }
    case AnchorPass(x, a) =>
      match tm {
        case AnchorPass(xm, am) => TreeResMirrorLk(a, am, gm1, gm2, inp, n, O, Sin);
        case _ =>
      }
    case GroupActionT(ga, a) =>
      match tm {
        case GroupActionT(gam, am) =>
        var gm2' := LG.GMUpdate(gam, LC.Idx(sinp), gm2);
        var gm1' := LG.GMUpdate(ga, LC.Idx(inp), gm1);
        GMUpdateInBounds(ga, LC.Idx(inp), gm1, n);
        // MirrorGm(gm1') == GMUpdate(gam, Idx(sinp), MirrorGm(gm1))
        match ga {
          case Open(g) =>
            assert gam == LG.Open(g);
            TRM.GMOpenMirror(gm1, g, LC.Idx(inp), n);
          case Close(g) =>
            assert gam == LG.Close(g);
            assert g in O by { assert CloseDiscLk(t, O); }
            assert g in gm1 && gm1[g].endIdx.None?;
            TRM.GMCloseMirror(gm1, g, LC.Idx(inp), n);
          case Reset(gl) =>
            assert gam.Reset?;
            TRM.GMResetMirror(gm1, gl, gam.gl, n);
        }
        // per-case GM*Mirror above gives: MirrorGm(gm1') == GMUpdate(gam, Idx(sinp), MirrorGm(gm1))
        assert TRM.MirrorGm(gm1', n) == LG.GMUpdate(gam, LC.Idx(sinp), TRM.MirrorGm(gm1, n));
        LL.GMUpdateAgreeOutside(gam, LC.Idx(sinp), gm2, TRM.MirrorGm(gm1, n), Sin);
        // GMUpdateAgreeOutside: GmAgreeOutside(gm2', GMUpdate(gam,Idx(sinp),MirrorGm(gm1)), Sin)
        //                     == GmAgreeOutside(gm2', MirrorGm(gm1'), Sin)
        var O' := match ga case Open(g) => O + {g} case Close(g) => O - {g} case Reset(gl) => O - (set g | g in gl);
        assert TRM.OpenSubset(gm1', O') by {
          forall h | h in O' ensures h in gm1' && gm1'[h].endIdx.None? {}
        }
        assert O' !! Sin;
        TreeResMirrorLk(a, am, gm1', gm2', inp, n, O', Sin);
        case _ =>
      }
    case LK(lk, tlk, tc) =>
      match tm {
        case LK(lk2, tlkm, tcm) =>
        assert lk2 == lk;
        if L.Positivity(lk) {
          assert LT.TreeRes(tlk, gm1, inp, L.LkDir(lk)).Some?;
          assert LT.TreeRes(tlkm, gm2, sinp, L.LkDir(lk)).Some?;
          var pairB := LT.TreeRes(tlk, gm1, inp, L.LkDir(lk)).value;
          var pairF := LT.TreeRes(tlkm, gm2, sinp, L.LkDir(lk)).value;
          ConfinedLeafAgree(tlk, gm1, inp, L.LkDir(lk), Sin);
          ConfinedLeafAgree(tlkm, gm2, sinp, L.LkDir(lk), Sin);
          TreeResGmInBounds(tlk, gm1, inp, L.LkDir(lk), n);
          // pairF.1 agrees with MirrorGm(pairB.1) outside Sin
          MirrorGmAgreeOutside(pairB.1, gm1, n, Sin);
          LL.GmAgreeOutsideSym(pairB.1, gm1, Sin);
          LL.GmAgreeOutsideTrans(pairF.1, gm2, TRM.MirrorGm(gm1, n), Sin);
          LL.GmAgreeOutsideTrans(pairF.1, TRM.MirrorGm(gm1, n), TRM.MirrorGm(pairB.1, n), Sin);
          assert LL.GmAgreeOutside(pairF.1, TRM.MirrorGm(pairB.1, n), Sin);
          assert TRM.OpenSubset(pairB.1, O) by {
            forall h | h in O ensures h in pairB.1 && pairB.1[h].endIdx.None? {
              assert h !in Sin;
            }
          }
          TreeResMirrorLk(tc, tcm, pairB.1, pairF.1, inp, n, O, Sin);
        } else {
          assert LT.TreeRes(tlk, gm1, inp, L.LkDir(lk)).None?;
          assert LT.TreeRes(tlkm, gm2, sinp, L.LkDir(lk)).None?;
          TreeResMirrorLk(tc, tcm, gm1, gm2, inp, n, O, Sin);
        }
        case _ =>
      }
    case LKFail(lk, tlk) =>
      match tm {
        case LKFail(lk2, tlkm) =>
        case _ =>
      }
  }

  // ===========================================================================
  // BRICK 3a: the inner-look GATE AGREEMENT via the oracle (the crux)
  // ===========================================================================

  /** The core of the nested tree mirror: a nested inner look's BACKWARD gate at
      `cp` (original string) agrees with its RevL forward-of-mirror gate at
      `n-cp` (reversed string). This is the fact the raw span/tree mirror CANNOT
      give (a nested lookbehind is walked in its intrinsic direction on both
      sides, reading opposite sides of the point). It holds because BOTH gates
      equal the SAME oracle bit: `OracleOkAt` (direction-generic) ties each
      side's re-walk gate to its oracle, and `MirrorViewGet` (position-consistent,
      no direction flip) ties the two oracle bits. `qm` is the original static
      package, `qm'` its mirror (oracle `MirrorView`, look bodies `RevL`). */
  lemma InnerGateAgree(rer: LW.RegExpRecord, qm: AR.QMap, qm': AR.QMap, str: string, rstr: string,
                       n: nat, cp: nat, lid: int, lk: L.Lookaround, r1: L.Regex)
    requires n == |str| && cp <= n && |qm.ov| == n + 1
    requires rstr == LC.Reverse(str) && |rstr| == n
    requires qm'.ov == MIR.MirrorView(qm.ov, n)
    requires LL.OracleOkAt(rer, qm, PIV.InpOfCp(str, cp))
    requires LL.OracleOkAt(rer, qm', PIV.InpOfCp(rstr, n - cp))
    requires lid in qm.looks && qm.looks[lid] == (lk, r1)
    requires lid in qm'.looks && qm'.looks[lid] == (lk, SD.RevL(r1))
    ensures
      var inpB := PIV.InpOfCp(str, cp);
      var inpF := PIV.InpOfCp(rstr, n - cp);
      LT.TreeRes(FU.ComputeTr(rer, [LS.Areg(r1)], inpB, LG.Empty, L.LkDir(lk)),
                 LG.Empty, inpB, L.LkDir(lk)).Some?
      == LT.TreeRes(FU.ComputeTr(rer, [LS.Areg(SD.RevL(r1))], inpF, LG.Empty, L.LkDir(lk)),
                    LG.Empty, inpF, L.LkDir(lk)).Some?
  {
    var inpB := PIV.InpOfCp(str, cp);
    var inpF := PIV.InpOfCp(rstr, n - cp);
    PIV.IdxInpOfCp(str, cp);
    PIV.IdxInpOfCp(rstr, n - cp);
    assert TR.CpOf(inpB) == cp;
    assert TR.CpOf(inpF) == n - cp;
    LL.OracleOkAtGet(rer, qm, inpB, lid, lk, r1);
    LL.OracleOkAtGet(rer, qm', inpF, lid, lk, SD.RevL(r1));
    // MirrorViewGet: view(MirrorView(ov,n), n-cp, lid) == view(ov, cp, lid)
    MIR.MirrorViewGet(qm.ov, n, cp, lid);
    assert MIR.Mirror(cp, n) == n - cp;
  }

  // ===========================================================================
  // BRICK 3b: the tree-building mirror (ComputeTrReverseLk)
  // ===========================================================================

  /** LOOK-FREE base: for a look-free body the extended mirror is just the
      existing `TM.ComputeTrReverse` lifted through `TreeMirrorRelLkFromRel`.
      This is the depth-0 base of the nested builder's look-nesting
      stratification (and directly serves a look-free surface segment). */
  lemma ComputeTrReverseLkLookFree(rer: LW.RegExpRecord, tr: L.Regex, inpB: LC.Input,
                                   Sin: set<LG.GroupId>)
    requires SD.GroupOkL(tr)
    ensures TreeMirrorRelLk(
      FU.ComputeTr(rer, [LS.Areg(tr)], inpB, LG.Empty, WP.Backward),
      FU.ComputeTr(rer, [LS.Areg(SD.RevL(tr))], SD.SwapInput(inpB), LG.Empty, WP.Forward),
      Sin)
  {
    var acts := [LS.Areg(tr)];
    assert SD.GroupOkActs(acts) by { SD.GroupOkActsCons(LS.Areg(tr), []); }
    TM.ComputeTrReverse(rer, acts, inpB, LG.Empty, LG.Empty);
    assert SD.RevActs(acts) == [LS.Areg(SD.RevL(tr))] by { SD.RevActsCons(LS.Areg(tr), []); }
    var tB := FU.ComputeTr(rer, acts, inpB, LG.Empty, WP.Backward);
    var tF := FU.ComputeTr(rer, [LS.Areg(SD.RevL(tr))], SD.SwapInput(inpB), LG.Empty, WP.Forward);
    assert TM.TreeMirrorRel(tB, tF);
    TreeMirrorRelLkFromRel(tB, tF, Sin);
  }

  // ===========================================================================
  // BRICK 3b scaffolding: the abstract gate-mirror hypothesis + acts plumbing
  // ===========================================================================

  /** The gate-agreement fact the builder needs at ONE inner look, ONE input:
      the body's LkDir walk succeeds iff its RevL image's LkDir walk over the
      swapped input succeeds. Discharged (over all inputs) by `InnerGateAgree`
      through the oracle; stated abstractly here so the builder recursion stays
      oracle-free. */
  ghost predicate GateAgree(rer: LW.RegExpRecord, lk: L.Lookaround, r1: L.Regex, inp2: LC.Input) {
    LT.TreeRes(FU.ComputeTr(rer, [LS.Areg(r1)], inp2, LG.Empty, L.LkDir(lk)),
               LG.Empty, inp2, L.LkDir(lk)).Some?
    == LT.TreeRes(FU.ComputeTr(rer, [LS.Areg(SD.RevL(r1))], SD.SwapInput(inp2), LG.Empty, L.LkDir(lk)),
                  LG.Empty, SD.SwapInput(inp2), L.LkDir(lk)).Some?
  }

  /** Every inner look in `r` has its gate mirror (at every input). Structural
      over `r`, so a subterm inherits it directly. */
  ghost predicate RegLookGatesMirror(r: L.Regex, rer: LW.RegExpRecord)
    decreases r
  {
    match r
    case LookaroundR(lk, r1) =>
      (forall inp2: LC.Input :: GateAgree(rer, lk, r1, inp2)) && RegLookGatesMirror(r1, rer)
    case Disjunction(a, b) => RegLookGatesMirror(a, rer) && RegLookGatesMirror(b, rer)
    case Sequence(a, b) => RegLookGatesMirror(a, rer) && RegLookGatesMirror(b, rer)
    case Quantified(_, _, _, r1) => RegLookGatesMirror(r1, rer)
    case Group(_, r1) => RegLookGatesMirror(r1, rer)
    case _ => true
  }

  /** Lifted to an action stack. */
  ghost predicate ActsLookGatesMirror(acts: LS.Actions, rer: LW.RegExpRecord) {
    forall i :: 0 <= i < |acts| && acts[i].Areg? ==> RegLookGatesMirror(acts[i].r, rer)
  }

  /** Per-`Areg` `GroupOkLB` (allows nested lookbehinds; bans backrefs and
      lookaheads on the surface). The builder's fragment invariant. */
  ghost predicate GroupOkLBActs(acts: LS.Actions) {
    forall i :: 0 <= i < |acts| && acts[i].Areg? ==> SD.GroupOkLB(acts[i].r)
  }

  lemma GroupOkLBActsTail(acts: LS.Actions)
    requires |acts| > 0 && GroupOkLBActs(acts)
    ensures GroupOkLBActs(acts[1..])
  {
    forall i | 0 <= i < |acts[1..]| && acts[1..][i].Areg? ensures SD.GroupOkLB(acts[1..][i].r) {
      assert acts[1..][i] == acts[i + 1];
    }
  }

  lemma GroupOkLBActsCons(a: LS.Action, acts: LS.Actions)
    requires GroupOkLBActs(acts) && (a.Areg? ==> SD.GroupOkLB(a.r))
    ensures GroupOkLBActs([a] + acts)
  {
    forall i | 0 <= i < |[a] + acts| && ([a] + acts)[i].Areg? ensures SD.GroupOkLB(([a] + acts)[i].r) {
      if i == 0 {} else { assert ([a] + acts)[i] == acts[i - 1]; }
    }
  }

  lemma ActsLookGatesMirrorTail(acts: LS.Actions, rer: LW.RegExpRecord)
    requires |acts| > 0 && ActsLookGatesMirror(acts, rer)
    ensures ActsLookGatesMirror(acts[1..], rer)
  {
    forall i | 0 <= i < |acts[1..]| && acts[1..][i].Areg? ensures RegLookGatesMirror(acts[1..][i].r, rer) {
      assert acts[1..][i] == acts[i + 1];
    }
  }

  lemma ActsLookGatesMirrorCons(a: LS.Action, acts: LS.Actions, rer: LW.RegExpRecord)
    requires ActsLookGatesMirror(acts, rer) && (a.Areg? ==> RegLookGatesMirror(a.r, rer))
    ensures ActsLookGatesMirror([a] + acts, rer)
  {
    forall i | 0 <= i < |[a] + acts| && ([a] + acts)[i].Areg? ensures RegLookGatesMirror(([a] + acts)[i].r, rer) {
      if i == 0 {} else { assert ([a] + acts)[i] == acts[i - 1]; }
    }
  }

  // ===========================================================================
  // BRICK 3b: the LK-case gate plumbing (de-risking the builder's hard case)
  // ===========================================================================

  /** `RevL` preserves the recursive fragment (kinds unchanged; positive bodies
      recurse, negative bodies stay group-free via `SD.RevLGroupFree`). Needed to
      apply `ComputeTrGmIndepLkRec` on the RevL side. */
  lemma RevLPreservesPikeLkRec(r: L.Regex)
    requires EL.PikeLkRegexRec(r)
    ensures EL.PikeLkRegexRec(SD.RevL(r))
    decreases r
  {
    match r
    case Disjunction(a, b) => RevLPreservesPikeLkRec(a); RevLPreservesPikeLkRec(b);
    case Sequence(a, b) => RevLPreservesPikeLkRec(a); RevLPreservesPikeLkRec(b);
    case Quantified(_, _, _, r1) => RevLPreservesPikeLkRec(r1);
    case Group(_, r1) => RevLPreservesPikeLkRec(r1);
    case LookaroundR(lk, r1) =>
      if L.Positivity(lk) { RevLPreservesPikeLkRec(r1); }
      else { SD.RevLGroupFree(r1); }
    case _ =>
  }

  /** THE LK-case gate plumbing. Given the abstract gate mirror (`GateAgree`) and
      the two fuel-computed body trees, the two `LkResult` gate verdicts agree
      (both Some ⇒ both trees are `LK`; both None ⇒ both `LKFail`). Composes
      determinism (`ComputeTree` Some ⇒ `ComputeTr`), tree gm-independence
      (`ComputeTrGmIndepLkRec`), and gate gm-independence (`LkResultGmIndep`). */
  lemma LookGateAgree(rer: LW.RegExpRecord, lk: L.Lookaround, r1: L.Regex, inp: LC.Input,
                      gm1: LG.GroupMap, gm2: LG.GroupMap, sinp: LC.Input,
                      treelk_B: LT.Tree, treelk_F: LT.Tree, fB: nat, fF: nat)
    requires EL.PikeLkRegexRec(r1)
    requires sinp == SD.SwapInput(inp)
    requires GateAgree(rer, lk, r1, inp)
    requires FS.ComputeTree(rer, [LS.Areg(r1)], inp, gm1, L.LkDir(lk), fB) == Some(treelk_B)
    requires FS.ComputeTree(rer, [LS.Areg(SD.RevL(r1))], sinp, gm2, L.LkDir(lk), fF) == Some(treelk_F)
    ensures LS.LkResult(lk, treelk_B, gm1, inp).Some? == LS.LkResult(lk, treelk_F, gm2, sinp).Some?
  {
    // treelk_B == ComputeTr([Areg(r1)], inp, Empty, LkDir)
    CI.ComputeIsTreeThm(rer, [LS.Areg(r1)], inp, gm1, L.LkDir(lk), fB, treelk_B);
    FU.IsTreeEqComputeTr(rer, [LS.Areg(r1)], inp, gm1, L.LkDir(lk), treelk_B);
    EL.ComputeTrGmIndepLkRec(rer, r1, inp, gm1, L.LkDir(lk));
    assert treelk_B == FU.ComputeTr(rer, [LS.Areg(r1)], inp, LG.Empty, L.LkDir(lk));
    // treelk_F == ComputeTr([Areg(RevL(r1))], sinp, Empty, LkDir)
    RevLPreservesPikeLkRec(r1);
    CI.ComputeIsTreeThm(rer, [LS.Areg(SD.RevL(r1))], sinp, gm2, L.LkDir(lk), fF, treelk_F);
    FU.IsTreeEqComputeTr(rer, [LS.Areg(SD.RevL(r1))], sinp, gm2, L.LkDir(lk), treelk_F);
    EL.ComputeTrGmIndepLkRec(rer, SD.RevL(r1), sinp, gm2, L.LkDir(lk));
    assert treelk_F == FU.ComputeTr(rer, [LS.Areg(SD.RevL(r1))], sinp, LG.Empty, L.LkDir(lk));
    // gate gm-independence (unconditional)
    EL.LkResultGmIndep(lk, treelk_B, gm1, inp);
    EL.LkResultGmIndep(lk, treelk_F, gm2, sinp);
    // Empty-gates: LkResult.Some? is a function (identity or negation, per Positivity)
    // of TreeRes(t, Empty, ., LkDir).Some?, which GateAgree equates across sides.
    assert LT.TreeRes(treelk_B, LG.Empty, inp, L.LkDir(lk)).Some?
        == LT.TreeRes(treelk_F, LG.Empty, sinp, L.LkDir(lk)).Some?;   // == GateAgree
  }

  // ===========================================================================
  // BRICK 3b-main: the tree-building mirror (fuel helper + fuel-free wrapper)
  // ===========================================================================

  /** `GroupFreeL` bodies are in the recursive fragment (group-free ⇒ no
      lookarounds/backrefs ⇒ `PikeLkRegexRec`). */
  lemma GroupFreeLIsPikeLkRec(r: L.Regex)
    requires SD.GroupFreeL(r)
    ensures EL.PikeLkRegexRec(r)
  {
    EL.GroupFreeLNoLkBr(r);
    EL.NoLkBrLIsPikeLkRegexRec(r);
  }

  /** THE BUILDER (fuel helper). A backward `ComputeTree` and the forward
      `ComputeTree` of the reversed stack over the swapped input, when both
      terminate, are `TreeMirrorRelLk`-related. Look-free cases mirror
      `TM.ComputeTreeReverse`; the `LookaroundR` case uses `LookGateAgree` for the
      gate verdict and the IH for the continuation (inner body trees excluded).
      Guarded ensures only (no None-iff) — the wrapper runs at adequate fuel. */
  lemma ComputeTreeReverseLk(rer: LW.RegExpRecord, acts: LS.Actions, inp: LC.Input,
                             gm1: LG.GroupMap, gm2: LG.GroupMap, fuel: nat, Sin: set<LG.GroupId>)
    requires EL.PikeLkActionsRec(acts)
    requires ActsLookGatesMirror(acts, rer)
    ensures var b := FS.ComputeTree(rer, acts, inp, gm1, WP.Backward, fuel);
            var fw := FS.ComputeTree(rer, SD.RevActs(acts), SD.SwapInput(inp), gm2, WP.Forward, fuel);
            b.Some? && fw.Some? ==> TreeMirrorRelLk(b.value, fw.value, Sin)
    decreases fuel
  {
    var racts := SD.RevActs(acts);
    var sinp := SD.SwapInput(inp);
    if fuel == 0 { return; }
    var f := fuel - 1;
    if |acts| == 0 { assert racts == []; return; }
    var cont := acts[1..];
    SD.RevActsTail(acts);
    assert racts[1..] == SD.RevActs(cont);
    EL.PikeLkActionsRecConsIff(acts[0], cont);       // PikeLkActionRec(acts[0]) && PikeLkActionsRec(cont)
    ActsLookGatesMirrorTail(acts, rer);              // ActsLookGatesMirror(cont)
    match acts[0]
    case Acheck(strcheck) =>
      assert racts[0] == LS.Acheck(SD.SwapInput(strcheck));
      SD.IsStrictSuffixSwap(inp, strcheck);
      if SSx.IsStrictSuffix(inp, strcheck, WP.Backward) {
        ComputeTreeReverseLk(rer, cont, inp, gm1, gm2, f, Sin);
      }
    case Aclose(gid) =>
      assert racts[0] == LS.Aclose(gid);
      ComputeTreeReverseLk(rer, cont, inp, LG.GMClose(LC.Idx(inp), gid, gm1),
                           LG.GMClose(LC.Idx(sinp), gid, gm2), f, Sin);
    case Areg(r) =>
      assert racts[0] == LS.Areg(SD.RevL(r));
      assert EL.PikeLkRegexRec(r);
      match r
      case Epsilon =>
        ComputeTreeReverseLk(rer, cont, inp, gm1, gm2, f, Sin);
      case Character(cd) =>
        SD.ReadCharSwap(rer, cd, inp);
        match LC.ReadChar(rer, cd, inp, WP.Backward) {
          case Some(pair) => ComputeTreeReverseLk(rer, cont, pair.1, gm1, gm2, f, Sin);
          case None =>
        }
      case Disjunction(r1, r2) =>
        assert SD.RevL(r) == L.Disjunction(SD.RevL(r1), SD.RevL(r2));
        LkActsRegHelper(acts, r, r1, r2, cont, rer);
        SD.RevActsCons(LS.Areg(r1), cont);
        SD.RevActsCons(LS.Areg(r2), cont);
        ComputeTreeReverseLk(rer, [LS.Areg(r1)] + cont, inp, gm1, gm2, f, Sin);
        ComputeTreeReverseLk(rer, [LS.Areg(r2)] + cont, inp, gm1, gm2, f, Sin);
      case Sequence(r1, r2) =>
        assert SD.RevL(r) == L.Sequence(SD.RevL(r2), SD.RevL(r1));
        assert LS.SeqList(r1, r2, WP.Backward) == [LS.Areg(r2), LS.Areg(r1)];
        SD.SeqListReverse(r1, r2);
        TM.RevActsAppend([LS.Areg(r2), LS.Areg(r1)], cont);
        assert [LS.Areg(r2), LS.Areg(r1)] + cont == [LS.Areg(r2)] + ([LS.Areg(r1)] + cont);
        SeqFragHelper(acts, r, r1, r2, cont, rer);
        ComputeTreeReverseLk(rer, [LS.Areg(r2), LS.Areg(r1)] + cont, inp, gm1, gm2, f, Sin);
      case Quantified(greedy, min, delta, r1) =>
        assert SD.RevL(r) == L.Quantified(greedy, min, delta, SD.RevL(r1));
        var gidl := L.DefGroups(r1);
        var gidlm := L.DefGroups(SD.RevL(r1));
        SD.RevLDefGroupsSet(r1);
        QuantFragHelper(acts, r, r1, cont, rer, greedy, min, delta);
        if min > 0 {
          var q1 := L.Quantified(greedy, min - 1, delta, r1);
          assert SD.RevL(q1) == L.Quantified(greedy, min - 1, delta, SD.RevL(r1));
          TM.RevActsAppend([LS.Areg(r1), LS.Areg(q1)], cont);
          assert SD.RevActs([LS.Areg(r1), LS.Areg(q1)]) == [LS.Areg(SD.RevL(r1)), LS.Areg(SD.RevL(q1))]
            by { SD.RevActsCons(LS.Areg(r1), [LS.Areg(q1)]); SD.RevActsCons(LS.Areg(q1), []); }
          assert [LS.Areg(r1), LS.Areg(q1)] + cont == [LS.Areg(r1)] + ([LS.Areg(q1)] + cont);
          QuantMinHelper(r1, q1, cont, rer, greedy, min, delta);
          ComputeTreeReverseLk(rer, [LS.Areg(r1), LS.Areg(q1)] + cont, inp,
                               LG.GMReset(gidl, gm1), LG.GMReset(gidlm, gm2), f, Sin);
          var bi := FS.ComputeTree(rer, [LS.Areg(r1), LS.Areg(q1)] + cont, inp,
                                   LG.GMReset(gidl, gm1), WP.Backward, f);
          var fi := FS.ComputeTree(rer, SD.RevActs([LS.Areg(r1), LS.Areg(q1)] + cont), sinp,
                                   LG.GMReset(gidlm, gm2), WP.Forward, f);
          if bi.Some? && fi.Some? {
            assert TM.GroupActionMirror(LG.Reset(gidl), LG.Reset(gidlm));
            assert TreeMirrorRelLk(LT.GroupActionT(LG.Reset(gidl), bi.value),
                                   LT.GroupActionT(LG.Reset(gidlm), fi.value), Sin);
          }
        } else if delta == LN.NN(0) {
          ComputeTreeReverseLk(rer, cont, inp, gm1, gm2, f, Sin);
        } else {
          var q0 := L.Quantified(greedy, 0, FS.NoiPred(delta), r1);
          assert SD.RevL(q0) == L.Quantified(greedy, 0, FS.NoiPred(delta), SD.RevL(r1));
          TM.RevActsAppend([LS.Areg(r1), LS.Acheck(inp), LS.Areg(q0)], cont);
          assert SD.RevActs([LS.Areg(r1), LS.Acheck(inp), LS.Areg(q0)])
              == [LS.Areg(SD.RevL(r1)), LS.Acheck(sinp), LS.Areg(SD.RevL(q0))]
            by { SD.RevActsCons(LS.Areg(r1), [LS.Acheck(inp), LS.Areg(q0)]);
                 SD.RevActsCons(LS.Acheck(inp), [LS.Areg(q0)]); SD.RevActsCons(LS.Areg(q0), []); }
          assert [LS.Areg(r1), LS.Acheck(inp), LS.Areg(q0)] + cont
              == [LS.Areg(r1)] + ([LS.Acheck(inp)] + ([LS.Areg(q0)] + cont));
          QuantFreeHelper(r1, q0, cont, rer, greedy, delta, inp);
          ComputeTreeReverseLk(rer, [LS.Areg(r1), LS.Acheck(inp), LS.Areg(q0)] + cont, inp,
                               LG.GMReset(gidl, gm1), LG.GMReset(gidlm, gm2), f, Sin);
          ComputeTreeReverseLk(rer, cont, inp, gm1, gm2, f, Sin);
          var bi := FS.ComputeTree(rer, [LS.Areg(r1), LS.Acheck(inp), LS.Areg(q0)] + cont,
                                   inp, LG.GMReset(gidl, gm1), WP.Backward, f);
          var fi := FS.ComputeTree(rer, SD.RevActs([LS.Areg(r1), LS.Acheck(inp), LS.Areg(q0)] + cont),
                                   sinp, LG.GMReset(gidlm, gm2), WP.Forward, f);
          var bs := FS.ComputeTree(rer, cont, inp, gm1, WP.Backward, f);
          var fs := FS.ComputeTree(rer, SD.RevActs(cont), sinp, gm2, WP.Forward, f);
          if bi.Some? && bs.Some? && fi.Some? && fs.Some? {
            assert TM.GroupActionMirror(LG.Reset(gidl), LG.Reset(gidlm));
            assert TreeMirrorRelLk(LT.GroupActionT(LG.Reset(gidl), bi.value),
                                   LT.GroupActionT(LG.Reset(gidlm), fi.value), Sin);
            assert TreeMirrorRelLk(bs.value, fs.value, Sin);
          }
        }
      case Group(gid, r1) =>
        assert SD.RevL(r) == L.Group(gid, SD.RevL(r1));
        TM.RevActsAppend([LS.Areg(r1), LS.Aclose(gid)], cont);
        assert SD.RevActs([LS.Areg(r1), LS.Aclose(gid)]) == [LS.Areg(SD.RevL(r1)), LS.Aclose(gid)]
          by { SD.RevActsCons(LS.Areg(r1), [LS.Aclose(gid)]); SD.RevActsCons(LS.Aclose(gid), []); }
        assert [LS.Areg(r1), LS.Aclose(gid)] + cont == [LS.Areg(r1)] + ([LS.Aclose(gid)] + cont);
        GroupFragHelper(r1, gid, cont, rer);
        ComputeTreeReverseLk(rer, [LS.Areg(r1), LS.Aclose(gid)] + cont, inp,
                             LG.GMOpen(LC.Idx(inp), gid, gm1),
                             LG.GMOpen(LC.Idx(sinp), gid, gm2), f, Sin);
      case LookaroundR(lk, r1) =>
        assert EL.PikeLkRegexRec(r1) by {
          if L.Positivity(lk) {} else { GroupFreeLIsPikeLkRec(r1); }
        }
        assert RegLookGatesMirror(r, rer);
        assert GateAgree(rer, lk, r1, inp);
        assert SD.RevL(r) == L.LookaroundR(lk, SD.RevL(r1));
        var tB := FS.ComputeTree(rer, [LS.Areg(r1)], inp, gm1, L.LkDir(lk), f);
        var tF := FS.ComputeTree(rer, [LS.Areg(SD.RevL(r1))], sinp, gm2, L.LkDir(lk), f);
        EL.PikeLkActionsRecConsIff(LS.Areg(r1), []);
        if tB.Some? && tF.Some? {
          LookGateAgree(rer, lk, r1, inp, gm1, gm2, sinp, tB.value, tF.value, f, f);
          if LS.LkResult(lk, tB.value, gm1, inp).Some? {
            var gmlkB := LS.LkResult(lk, tB.value, gm1, inp).value;
            var gmlkF := LS.LkResult(lk, tF.value, gm2, sinp).value;
            ComputeTreeReverseLk(rer, cont, inp, gmlkB, gmlkF, f, Sin);
          }
        }
      case AnchorR(a) =>
        assert SD.RevL(r) == L.AnchorR(SD.SwapAnchorL(a));
        SD.AnchorSatisfiedSwap(rer, a, inp);
        if LS.AnchorSatisfied(rer, a, inp) {
          ComputeTreeReverseLk(rer, cont, inp, gm1, gm2, f, Sin);
        }
      case Backreference(gid) =>
        assert EL.PikeLkRegexRec(r);
        assert false;
  }

  // --- fragment/gate-hypothesis threading helpers for the builder recursion ---

  lemma LkActsRegHelper(acts: LS.Actions, r: L.Regex, r1: L.Regex, r2: L.Regex, cont: LS.Actions, rer: LW.RegExpRecord)
    requires |acts| > 0 && acts[0] == LS.Areg(r) && cont == acts[1..]
    requires r == L.Disjunction(r1, r2)
    requires EL.PikeLkActionsRec(acts) && ActsLookGatesMirror(acts, rer)
    ensures EL.PikeLkActionsRec([LS.Areg(r1)] + cont) && ActsLookGatesMirror([LS.Areg(r1)] + cont, rer)
    ensures EL.PikeLkActionsRec([LS.Areg(r2)] + cont) && ActsLookGatesMirror([LS.Areg(r2)] + cont, rer)
  {
    EL.PikeLkActionsRecConsIff(acts[0], cont);
    ActsLookGatesMirrorTail(acts, rer);
    assert EL.PikeLkRegexRec(r) && RegLookGatesMirror(r, rer);
    EL.PikeLkActionsRecConsIff(LS.Areg(r1), cont);
    EL.PikeLkActionsRecConsIff(LS.Areg(r2), cont);
    ActsLookGatesMirrorCons(LS.Areg(r1), cont, rer);
    ActsLookGatesMirrorCons(LS.Areg(r2), cont, rer);
  }

  lemma SeqFragHelper(acts: LS.Actions, r: L.Regex, r1: L.Regex, r2: L.Regex, cont: LS.Actions, rer: LW.RegExpRecord)
    requires |acts| > 0 && acts[0] == LS.Areg(r) && cont == acts[1..]
    requires r == L.Sequence(r1, r2)
    requires EL.PikeLkActionsRec(acts) && ActsLookGatesMirror(acts, rer)
    ensures EL.PikeLkActionsRec([LS.Areg(r2), LS.Areg(r1)] + cont)
    ensures ActsLookGatesMirror([LS.Areg(r2), LS.Areg(r1)] + cont, rer)
  {
    EL.PikeLkActionsRecConsIff(acts[0], cont);
    ActsLookGatesMirrorTail(acts, rer);
    assert [LS.Areg(r2), LS.Areg(r1)] + cont == [LS.Areg(r2)] + ([LS.Areg(r1)] + cont);
    EL.PikeLkActionsRecConsIff(LS.Areg(r1), cont);
    EL.PikeLkActionsRecConsIff(LS.Areg(r2), [LS.Areg(r1)] + cont);
    ActsLookGatesMirrorCons(LS.Areg(r1), cont, rer);
    ActsLookGatesMirrorCons(LS.Areg(r2), [LS.Areg(r1)] + cont, rer);
  }

  lemma QuantFragHelper(acts: LS.Actions, r: L.Regex, r1: L.Regex, cont: LS.Actions, rer: LW.RegExpRecord,
                        greedy: bool, min: nat, delta: LN.NoI)
    requires |acts| > 0 && acts[0] == LS.Areg(r) && cont == acts[1..]
    requires r == L.Quantified(greedy, min, delta, r1)
    requires EL.PikeLkActionsRec(acts) && ActsLookGatesMirror(acts, rer)
    ensures EL.PikeLkRegexRec(r1) && RegLookGatesMirror(r1, rer)
    ensures EL.PikeLkActionsRec(cont) && ActsLookGatesMirror(cont, rer)
  {
    EL.PikeLkActionsRecConsIff(acts[0], cont);
    ActsLookGatesMirrorTail(acts, rer);
  }

  lemma QuantMinHelper(r1: L.Regex, q1: L.Regex, cont: LS.Actions, rer: LW.RegExpRecord,
                       greedy: bool, min: nat, delta: LN.NoI)
    requires min > 0 && q1 == L.Quantified(greedy, min - 1, delta, r1)
    requires EL.PikeLkRegexRec(r1) && RegLookGatesMirror(r1, rer)
    requires EL.PikeLkActionsRec(cont) && ActsLookGatesMirror(cont, rer)
    ensures EL.PikeLkActionsRec([LS.Areg(r1), LS.Areg(q1)] + cont)
    ensures ActsLookGatesMirror([LS.Areg(r1), LS.Areg(q1)] + cont, rer)
  {
    assert EL.PikeLkRegexRec(q1) && RegLookGatesMirror(q1, rer);
    assert [LS.Areg(r1), LS.Areg(q1)] + cont == [LS.Areg(r1)] + ([LS.Areg(q1)] + cont);
    EL.PikeLkActionsRecConsIff(LS.Areg(q1), cont);
    EL.PikeLkActionsRecConsIff(LS.Areg(r1), [LS.Areg(q1)] + cont);
    ActsLookGatesMirrorCons(LS.Areg(q1), cont, rer);
    ActsLookGatesMirrorCons(LS.Areg(r1), [LS.Areg(q1)] + cont, rer);
  }

  lemma QuantFreeHelper(r1: L.Regex, q0: L.Regex, cont: LS.Actions, rer: LW.RegExpRecord,
                        greedy: bool, delta: LN.NoI, inp: LC.Input)
    requires q0 == L.Quantified(greedy, 0, FS.NoiPred(delta), r1)
    requires EL.PikeLkRegexRec(r1) && RegLookGatesMirror(r1, rer)
    requires EL.PikeLkActionsRec(cont) && ActsLookGatesMirror(cont, rer)
    ensures EL.PikeLkActionsRec([LS.Areg(r1), LS.Acheck(inp), LS.Areg(q0)] + cont)
    ensures ActsLookGatesMirror([LS.Areg(r1), LS.Acheck(inp), LS.Areg(q0)] + cont, rer)
  {
    assert EL.PikeLkRegexRec(q0) && RegLookGatesMirror(q0, rer);
    assert [LS.Areg(r1), LS.Acheck(inp), LS.Areg(q0)] + cont
        == [LS.Areg(r1)] + ([LS.Acheck(inp)] + ([LS.Areg(q0)] + cont));
    EL.PikeLkActionsRecConsIff(LS.Areg(q0), cont);
    EL.PikeLkActionsRecConsIff(LS.Acheck(inp), [LS.Areg(q0)] + cont);
    EL.PikeLkActionsRecConsIff(LS.Areg(r1), [LS.Acheck(inp)] + ([LS.Areg(q0)] + cont));
    ActsLookGatesMirrorCons(LS.Areg(q0), cont, rer);
    ActsLookGatesMirrorCons(LS.Acheck(inp), [LS.Areg(q0)] + cont, rer);
    ActsLookGatesMirrorCons(LS.Areg(r1), [LS.Acheck(inp)] + ([LS.Areg(q0)] + cont), rer);
  }

  lemma GroupFragHelper(r1: L.Regex, gid: nat, cont: LS.Actions, rer: LW.RegExpRecord)
    requires EL.PikeLkRegexRec(r1) && RegLookGatesMirror(r1, rer)
    requires EL.PikeLkActionsRec(cont) && ActsLookGatesMirror(cont, rer)
    ensures EL.PikeLkActionsRec([LS.Areg(r1), LS.Aclose(gid)] + cont)
    ensures ActsLookGatesMirror([LS.Areg(r1), LS.Aclose(gid)] + cont, rer)
  {
    assert [LS.Areg(r1), LS.Aclose(gid)] + cont == [LS.Areg(r1)] + ([LS.Aclose(gid)] + cont);
    EL.PikeLkActionsRecConsIff(LS.Aclose(gid), cont);
    EL.PikeLkActionsRecConsIff(LS.Areg(r1), [LS.Aclose(gid)] + cont);
    ActsLookGatesMirrorCons(LS.Aclose(gid), cont, rer);
    ActsLookGatesMirrorCons(LS.Areg(r1), [LS.Aclose(gid)] + cont, rer);
  }

  /** Fuel-free wrapper: `ComputeTr` backward mirrors `ComputeTr` of the reversed
      stack over the swapped input (`TreeMirrorRelLk`). */
  lemma ComputeTrReverseLk(rer: LW.RegExpRecord, acts: LS.Actions, inp: LC.Input,
                           gm1: LG.GroupMap, gm2: LG.GroupMap, Sin: set<LG.GroupId>)
    requires EL.PikeLkActionsRec(acts)
    requires ActsLookGatesMirror(acts, rer)
    ensures TreeMirrorRelLk(FU.ComputeTr(rer, acts, inp, gm1, WP.Backward),
                            FU.ComputeTr(rer, SD.RevActs(acts), SD.SwapInput(inp), gm2, WP.Forward), Sin)
  {
    var sinp := SD.SwapInput(inp);
    var racts := SD.RevActs(acts);
    var fb := FS.ActionsFuel(acts, inp, WP.Backward) + 1;
    var ff := FS.ActionsFuel(racts, sinp, WP.Forward) + 1;
    var fuel := if fb >= ff then fb else ff;
    FS.FunctionalTerminates(rer, acts, inp, gm1, WP.Backward, fuel);
    FS.FunctionalTerminates(rer, racts, sinp, gm2, WP.Forward, fuel);
    var b := FS.ComputeTree(rer, acts, inp, gm1, WP.Backward, fuel);
    var fw := FS.ComputeTree(rer, racts, sinp, gm2, WP.Forward, fuel);
    ComputeTreeReverseLk(rer, acts, inp, gm1, gm2, fuel, Sin);
    // pin both computed trees to ComputeTr (determinism, any adequate fuel)
    CI.ComputeIsTreeThm(rer, acts, inp, gm1, WP.Backward, fuel, b.value);
    FU.IsTreeEqComputeTr(rer, acts, inp, gm1, WP.Backward, b.value);
    CI.ComputeIsTreeThm(rer, racts, sinp, gm2, WP.Forward, fuel, fw.value);
    FU.IsTreeEqComputeTr(rer, racts, sinp, gm2, WP.Forward, fw.value);
  }
}
