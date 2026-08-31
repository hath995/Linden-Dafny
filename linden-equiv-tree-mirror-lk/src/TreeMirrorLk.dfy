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
  import NUL = LindenElkNullable
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
  import CD = LindenCloseDisc
  import EL = LindenElkEntryLk
  import FS = FunctionalSemantics
  import CI = ComputeIsTree
  import T = LindenElkTranslate
  import R = RegElkRegex
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
    case Close(g) => true   // O!!Sin gives g∉Sin from g∈O; a Close needn't be constrained
    case Reset(gl) => true   // a quantifier over a nested-look body resets inner gids ∈ Sin — harmless
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

  /** REGEX-SCOPED oracle correctness: at every position, the oracle bit of each
      look IN `re` characterizes that look body's LkDir walk. Unlike `LL.OracleOkAt`
      (a forall over ALL of `qm.looks`), this is scoped to `re`'s own looks, so it
      inherits to sub-regexes and supports the mirror-oracle depth induction. */
  ghost predicate OracleColsOkRE(rer: LW.RegExpRecord, qm: AR.QMap, str: string, re: R.regex)
    requires T.TransWf(re)
    decreases re
  {
    match re
    case Re_alt(r1, r2) => OracleColsOkRE(rer, qm, str, r1) && OracleColsOkRE(rer, qm, str, r2)
    case Re_con(r1, r2) => OracleColsOkRE(rer, qm, str, r1) && OracleColsOkRE(rer, qm, str, r2)
    case Re_quant(_, _, _, r1) => OracleColsOkRE(rer, qm, str, r1)
    case Re_capture(_, r1) => OracleColsOkRE(rer, qm, str, r1)
    case Re_lookaround(lid, la, r1) =>
      (forall k: nat :: k <= |str| ==>
         (LOr.view_get_oracle(qm.ov, k, lid)
          <==> LT.TreeRes(FU.ComputeTr(rer, [LS.Areg(T.Translate(r1))], PIV.InpOfCp(str, k),
                                       LG.Empty, L.LkDir(T.TrLookaround(la))),
                          LG.Empty, PIV.InpOfCp(str, k), L.LkDir(T.TrLookaround(la))).Some?))
      && OracleColsOkRE(rer, qm, str, r1)
    case _ => true
  }

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
    // the two per-lid oracle bits (regex-scoped: the caller supplies only THIS look's bits)
    requires LOr.view_get_oracle(qm.ov, cp, lid)
        <==> LT.TreeRes(FU.ComputeTr(rer, [LS.Areg(r1)], PIV.InpOfCp(str, cp), LG.Empty, L.LkDir(lk)),
                        LG.Empty, PIV.InpOfCp(str, cp), L.LkDir(lk)).Some?
    requires LOr.view_get_oracle(qm'.ov, n - cp, lid)
        <==> LT.TreeRes(FU.ComputeTr(rer, [LS.Areg(SD.RevL(r1))], PIV.InpOfCp(rstr, n - cp), LG.Empty, L.LkDir(lk)),
                        LG.Empty, PIV.InpOfCp(rstr, n - cp), L.LkDir(lk)).Some?
    ensures
      var inpB := PIV.InpOfCp(str, cp);
      var inpF := PIV.InpOfCp(rstr, n - cp);
      LT.TreeRes(FU.ComputeTr(rer, [LS.Areg(r1)], inpB, LG.Empty, L.LkDir(lk)),
                 LG.Empty, inpB, L.LkDir(lk)).Some?
      == LT.TreeRes(FU.ComputeTr(rer, [LS.Areg(SD.RevL(r1))], inpF, LG.Empty, L.LkDir(lk)),
                    LG.Empty, inpF, L.LkDir(lk)).Some?
  {
    // MirrorViewGet: view(MirrorView(ov,n), n-cp, lid) == view(ov, cp, lid); the two bits chain.
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

  /** !!! DEAD-END WITNESS: `GateAgree` is UNSATISFIABLE for nested inner looks !!!
      `SD.SwapInput` merely swaps pref<->next, so the RevL-side backward walk reads
      the char AFTER the point while the original reads the char BEFORE — opposite
      sides. Hence `GateAgree`, `RegLookGatesMirror`/`ActsLookGatesMirror`, and every
      lemma gated on them (`ComputeTrReverseLk`, `RegLookGatesMirrorDischarge`,
      `BackBodyGmTieNested`) are VACUOUS for a nested capturing lookbehind: the
      ComputeTr RE-WALK tree does NOT mirror for nested looks (the documented
      dead-end). The tree-property establishments (GateStableLk/GActsOutsideSin/
      CloseDiscLk) and confinement ARE sound (independent of the mirror). The correct
      captures route is the ORACLE-GATED / backward-simulation stack, not this. */
  lemma GateAgreeIsFalse(rer: LW.RegExpRecord, cd: LC.CharDescr)
    requires LC.CharMatch(rer, 'a', cd) && !LC.CharMatch(rer, 'b', cd)
    ensures !GateAgree(rer, L.LookBehind, L.Character(cd), LC.Input(['b'], ['a']))
  {
    var r1 := L.Character(cd);
    var inp2 := LC.Input(['b'], ['a']);
    var sinp := SD.SwapInput(inp2);
    assert L.LkDir(L.LookBehind) == WP.Backward;
    assert SD.RevL(r1) == r1;
    FU.ComputeTrRw(rer, [LS.Areg(r1)], inp2, LG.Empty, WP.Backward);
    FU.ComputeTrRw(rer, [LS.Areg(r1)], sinp, LG.Empty, WP.Backward);
    assert inp2.pref == ['a'] && inp2.pref[0] == 'a';
    assert LC.ReadChar(rer, cd, inp2, WP.Backward).Some?;
    assert sinp == LC.Input(['a'], ['b']);
    assert LC.ReadChar(rer, cd, sinp, WP.Backward).None?;
  }

  /** Every inner look in `r` has its gate mirror at every POSITION of `str`.
      String-relative (not input-generic): a nested inner look's re-walks only
      agree at views of the fixed `str`, via the oracle (`InnerGateAgree`).
      Structural over `r`, so a subterm inherits it directly. */
  ghost predicate RegLookGatesMirror(r: L.Regex, rer: LW.RegExpRecord, str: string)
    decreases r
  {
    match r
    case LookaroundR(lk, r1) =>
      (forall cp': nat :: cp' <= |str| ==> GateAgree(rer, lk, r1, PIV.InpOfCp(str, cp')))
      && RegLookGatesMirror(r1, rer, str)
    case Disjunction(a, b) => RegLookGatesMirror(a, rer, str) && RegLookGatesMirror(b, rer, str)
    case Sequence(a, b) => RegLookGatesMirror(a, rer, str) && RegLookGatesMirror(b, rer, str)
    case Quantified(_, _, _, r1) => RegLookGatesMirror(r1, rer, str)
    case Group(_, r1) => RegLookGatesMirror(r1, rer, str)
    case _ => true
  }

  /** Lifted to an action stack. */
  ghost predicate ActsLookGatesMirror(acts: LS.Actions, rer: LW.RegExpRecord, str: string) {
    forall i :: 0 <= i < |acts| && acts[i].Areg? ==> RegLookGatesMirror(acts[i].r, rer, str)
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

  lemma ActsLookGatesMirrorTail(acts: LS.Actions, rer: LW.RegExpRecord, str: string)
    requires |acts| > 0 && ActsLookGatesMirror(acts, rer, str)
    ensures ActsLookGatesMirror(acts[1..], rer, str)
  {
    forall i | 0 <= i < |acts[1..]| && acts[1..][i].Areg? ensures RegLookGatesMirror(acts[1..][i].r, rer, str) {
      assert acts[1..][i] == acts[i + 1];
    }
  }

  lemma ActsLookGatesMirrorCons(a: LS.Action, acts: LS.Actions, rer: LW.RegExpRecord, str: string)
    requires ActsLookGatesMirror(acts, rer, str) && (a.Areg? ==> RegLookGatesMirror(a.r, rer, str))
    ensures ActsLookGatesMirror([a] + acts, rer, str)
  {
    forall i | 0 <= i < |[a] + acts| && ([a] + acts)[i].Areg? ensures RegLookGatesMirror(([a] + acts)[i].r, rer, str) {
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
    case Quantified(_, _, _, r1) =>
      RevLPreservesPikeLkRec(r1);
      SD.RevLNonNullable(r1);        // §2.5b interim conjunct transfers
    case Group(_, r1) => RevLPreservesPikeLkRec(r1);
    case LookaroundR(lk, r1) =>
      if L.Positivity(lk) { RevLPreservesPikeLkRec(r1); }
      else { SD.RevLGroupFree(r1); SD.RevLNoNulledPlus(r1); }
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
    requires NUL.NoNulledPlusL(r)   // §2.5b interim
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
  /** THE BUILDER (fuel helper). A backward `ComputeTree` and the forward
      `ComputeTree` of the reversed stack over the swapped input, when both
      terminate, are `TreeMirrorRelLk`-related. Look-free cases mirror
      `TM.ComputeTreeReverse`; the `LookaroundR` case uses `LookGateAgree` for the
      gate verdict and the IH for the continuation (inner body trees excluded).
      Guarded ensures only (no None-iff) — the wrapper runs at adequate fuel.
      `inp` is pinned to `InpOfCp(str, cp0)` so the string-relative gate
      hypothesis instantiates at the current position. */
  lemma ComputeTreeReverseLk(rer: LW.RegExpRecord, acts: LS.Actions, inp: LC.Input,
                             gm1: LG.GroupMap, gm2: LG.GroupMap, fuel: nat,
                             str: string, cp0: nat, Sin: set<LG.GroupId>)
    requires EL.PikeLkActionsRec(acts)
    requires ActsLookGatesMirror(acts, rer, str)
    requires cp0 <= |str| && inp == PIV.InpOfCp(str, cp0)
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
    EL.PikeLkActionsRecConsIff(acts[0], cont);
    ActsLookGatesMirrorTail(acts, rer, str);
    match acts[0]
    case Acheck(strcheck) =>
      assert racts[0] == LS.Acheck(SD.SwapInput(strcheck));
      SD.IsStrictSuffixSwap(inp, strcheck);
      if SSx.IsStrictSuffix(inp, strcheck, WP.Backward) {
        ComputeTreeReverseLk(rer, cont, inp, gm1, gm2, f, str, cp0, Sin);
      }
    case Aclose(gid) =>
      assert racts[0] == LS.Aclose(gid);
      ComputeTreeReverseLk(rer, cont, inp, LG.GMClose(LC.Idx(inp), gid, gm1),
                           LG.GMClose(LC.Idx(sinp), gid, gm2), f, str, cp0, Sin);
    case Areg(r) =>
      assert racts[0] == LS.Areg(SD.RevL(r));
      assert EL.PikeLkRegexRec(r);
      match r
      case Epsilon =>
        ComputeTreeReverseLk(rer, cont, inp, gm1, gm2, f, str, cp0, Sin);
      case Character(cd) =>
        SD.ReadCharSwap(rer, cd, inp);
        match LC.ReadChar(rer, cd, inp, WP.Backward) {
          case Some(pair) =>
            assert cp0 > 0 by { assert |inp.pref| > 0; PIV.IdxInpOfCp(str, cp0); }
            assert inp == T.InputAt(str, cp0) by { LS.ReverseLength(str[..cp0]); }
            SD.AdvanceInputPBackAt(str, cp0);
            assert pair.1 == LC.AdvanceInputP(inp, WP.Backward);
            assert pair.1 == T.InputAt(str, cp0 - 1);
            assert pair.1 == PIV.InpOfCp(str, cp0 - 1) by { LS.ReverseLength(str[..cp0 - 1]); }
            ComputeTreeReverseLk(rer, cont, pair.1, gm1, gm2, f, str, cp0 - 1, Sin);
          case None =>
        }
      case Disjunction(r1, r2) =>
        assert SD.RevL(r) == L.Disjunction(SD.RevL(r1), SD.RevL(r2));
        LkActsRegHelper(acts, r, r1, r2, cont, rer, str);
        SD.RevActsCons(LS.Areg(r1), cont);
        SD.RevActsCons(LS.Areg(r2), cont);
        ComputeTreeReverseLk(rer, [LS.Areg(r1)] + cont, inp, gm1, gm2, f, str, cp0, Sin);
        ComputeTreeReverseLk(rer, [LS.Areg(r2)] + cont, inp, gm1, gm2, f, str, cp0, Sin);
      case Sequence(r1, r2) =>
        assert SD.RevL(r) == L.Sequence(SD.RevL(r2), SD.RevL(r1));
        assert LS.SeqList(r1, r2, WP.Backward) == [LS.Areg(r2), LS.Areg(r1)];
        SD.SeqListReverse(r1, r2);
        TM.RevActsAppend([LS.Areg(r2), LS.Areg(r1)], cont);
        assert [LS.Areg(r2), LS.Areg(r1)] + cont == [LS.Areg(r2)] + ([LS.Areg(r1)] + cont);
        SeqFragHelper(acts, r, r1, r2, cont, rer, str);
        ComputeTreeReverseLk(rer, [LS.Areg(r2), LS.Areg(r1)] + cont, inp, gm1, gm2, f, str, cp0, Sin);
      case Quantified(greedy, min, delta, r1) =>
        assert SD.RevL(r) == L.Quantified(greedy, min, delta, SD.RevL(r1));
        var gidl := L.DefGroups(r1);
        var gidlm := L.DefGroups(SD.RevL(r1));
        SD.RevLDefGroupsSet(r1);
        QuantFragHelper(acts, r, r1, cont, rer, str, greedy, min, delta);
        if min > 0 {
          var q1 := L.Quantified(greedy, min - 1, delta, r1);
          assert SD.RevL(q1) == L.Quantified(greedy, min - 1, delta, SD.RevL(r1));
          TM.RevActsAppend([LS.Areg(r1), LS.Areg(q1)], cont);
          assert SD.RevActs([LS.Areg(r1), LS.Areg(q1)]) == [LS.Areg(SD.RevL(r1)), LS.Areg(SD.RevL(q1))]
            by { SD.RevActsCons(LS.Areg(r1), [LS.Areg(q1)]); SD.RevActsCons(LS.Areg(q1), []); }
          assert [LS.Areg(r1), LS.Areg(q1)] + cont == [LS.Areg(r1)] + ([LS.Areg(q1)] + cont);
          QuantMinHelper(r1, q1, cont, rer, str, greedy, min, delta);
          ComputeTreeReverseLk(rer, [LS.Areg(r1), LS.Areg(q1)] + cont, inp,
                               LG.GMReset(gidl, gm1), LG.GMReset(gidlm, gm2), f, str, cp0, Sin);
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
          ComputeTreeReverseLk(rer, cont, inp, gm1, gm2, f, str, cp0, Sin);
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
          QuantFreeHelper(r1, q0, cont, rer, str, greedy, delta, inp);
          ComputeTreeReverseLk(rer, [LS.Areg(r1), LS.Acheck(inp), LS.Areg(q0)] + cont, inp,
                               LG.GMReset(gidl, gm1), LG.GMReset(gidlm, gm2), f, str, cp0, Sin);
          ComputeTreeReverseLk(rer, cont, inp, gm1, gm2, f, str, cp0, Sin);
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
        GroupFragHelper(r1, gid, cont, rer, str);
        ComputeTreeReverseLk(rer, [LS.Areg(r1), LS.Aclose(gid)] + cont, inp,
                             LG.GMOpen(LC.Idx(inp), gid, gm1),
                             LG.GMOpen(LC.Idx(sinp), gid, gm2), f, str, cp0, Sin);
      case LookaroundR(lk, r1) =>
        assert EL.PikeLkRegexRec(r1) by {
          if L.Positivity(lk) {} else { GroupFreeLIsPikeLkRec(r1); }
        }
        assert RegLookGatesMirror(r, rer, str);
        assert GateAgree(rer, lk, r1, inp) by {
          assert cp0 <= |str| && inp == PIV.InpOfCp(str, cp0);
        }
        assert SD.RevL(r) == L.LookaroundR(lk, SD.RevL(r1));
        var tB := FS.ComputeTree(rer, [LS.Areg(r1)], inp, gm1, L.LkDir(lk), f);
        var tF := FS.ComputeTree(rer, [LS.Areg(SD.RevL(r1))], sinp, gm2, L.LkDir(lk), f);
        EL.PikeLkActionsRecConsIff(LS.Areg(r1), []);
        if tB.Some? && tF.Some? {
          LookGateAgree(rer, lk, r1, inp, gm1, gm2, sinp, tB.value, tF.value, f, f);
          if LS.LkResult(lk, tB.value, gm1, inp).Some? {
            var gmlkB := LS.LkResult(lk, tB.value, gm1, inp).value;
            var gmlkF := LS.LkResult(lk, tF.value, gm2, sinp).value;
            ComputeTreeReverseLk(rer, cont, inp, gmlkB, gmlkF, f, str, cp0, Sin);
          }
        }
      case AnchorR(a) =>
        assert SD.RevL(r) == L.AnchorR(SD.SwapAnchorL(a));
        SD.AnchorSatisfiedSwap(rer, a, inp);
        if LS.AnchorSatisfied(rer, a, inp) {
          ComputeTreeReverseLk(rer, cont, inp, gm1, gm2, f, str, cp0, Sin);
        }
      case Backreference(gid) =>
        assert EL.PikeLkRegexRec(r);
        assert false;
  }

  // --- fragment/gate-hypothesis threading helpers for the builder recursion ---

  lemma LkActsRegHelper(acts: LS.Actions, r: L.Regex, r1: L.Regex, r2: L.Regex, cont: LS.Actions, rer: LW.RegExpRecord, str: string)
    requires |acts| > 0 && acts[0] == LS.Areg(r) && cont == acts[1..]
    requires r == L.Disjunction(r1, r2)
    requires EL.PikeLkActionsRec(acts) && ActsLookGatesMirror(acts, rer, str)
    ensures EL.PikeLkActionsRec([LS.Areg(r1)] + cont) && ActsLookGatesMirror([LS.Areg(r1)] + cont, rer, str)
    ensures EL.PikeLkActionsRec([LS.Areg(r2)] + cont) && ActsLookGatesMirror([LS.Areg(r2)] + cont, rer, str)
  {
    EL.PikeLkActionsRecConsIff(acts[0], cont);
    ActsLookGatesMirrorTail(acts, rer, str);
    assert EL.PikeLkRegexRec(r) && RegLookGatesMirror(r, rer, str);
    EL.PikeLkActionsRecConsIff(LS.Areg(r1), cont);
    EL.PikeLkActionsRecConsIff(LS.Areg(r2), cont);
    ActsLookGatesMirrorCons(LS.Areg(r1), cont, rer, str);
    ActsLookGatesMirrorCons(LS.Areg(r2), cont, rer, str);
  }

  lemma SeqFragHelper(acts: LS.Actions, r: L.Regex, r1: L.Regex, r2: L.Regex, cont: LS.Actions, rer: LW.RegExpRecord, str: string)
    requires |acts| > 0 && acts[0] == LS.Areg(r) && cont == acts[1..]
    requires r == L.Sequence(r1, r2)
    requires EL.PikeLkActionsRec(acts) && ActsLookGatesMirror(acts, rer, str)
    ensures EL.PikeLkActionsRec([LS.Areg(r2), LS.Areg(r1)] + cont)
    ensures ActsLookGatesMirror([LS.Areg(r2), LS.Areg(r1)] + cont, rer, str)
  {
    EL.PikeLkActionsRecConsIff(acts[0], cont);
    ActsLookGatesMirrorTail(acts, rer, str);
    assert [LS.Areg(r2), LS.Areg(r1)] + cont == [LS.Areg(r2)] + ([LS.Areg(r1)] + cont);
    EL.PikeLkActionsRecConsIff(LS.Areg(r1), cont);
    EL.PikeLkActionsRecConsIff(LS.Areg(r2), [LS.Areg(r1)] + cont);
    ActsLookGatesMirrorCons(LS.Areg(r1), cont, rer, str);
    ActsLookGatesMirrorCons(LS.Areg(r2), [LS.Areg(r1)] + cont, rer, str);
  }

  lemma QuantFragHelper(acts: LS.Actions, r: L.Regex, r1: L.Regex, cont: LS.Actions, rer: LW.RegExpRecord, str: string,
                        greedy: bool, min: nat, delta: LN.NoI)
    requires |acts| > 0 && acts[0] == LS.Areg(r) && cont == acts[1..]
    requires r == L.Quantified(greedy, min, delta, r1)
    requires EL.PikeLkActionsRec(acts) && ActsLookGatesMirror(acts, rer, str)
    ensures EL.PikeLkRegexRec(r1) && RegLookGatesMirror(r1, rer, str)
    ensures EL.PikeLkActionsRec(cont) && ActsLookGatesMirror(cont, rer, str)
  {
    EL.PikeLkActionsRecConsIff(acts[0], cont);
    ActsLookGatesMirrorTail(acts, rer, str);
  }

  lemma QuantMinHelper(r1: L.Regex, q1: L.Regex, cont: LS.Actions, rer: LW.RegExpRecord, str: string,
                       greedy: bool, min: nat, delta: LN.NoI)
    requires min > 0 && q1 == L.Quantified(greedy, min - 1, delta, r1)
    requires min > 1 && delta.Inf? && greedy ==> NUL.NonNullableL(r1)   // §2.5b interim
    requires EL.PikeLkRegexRec(r1) && RegLookGatesMirror(r1, rer, str)
    requires EL.PikeLkActionsRec(cont) && ActsLookGatesMirror(cont, rer, str)
    ensures EL.PikeLkActionsRec([LS.Areg(r1), LS.Areg(q1)] + cont)
    ensures ActsLookGatesMirror([LS.Areg(r1), LS.Areg(q1)] + cont, rer, str)
  {
    assert EL.PikeLkRegexRec(q1) && RegLookGatesMirror(q1, rer, str);
    assert [LS.Areg(r1), LS.Areg(q1)] + cont == [LS.Areg(r1)] + ([LS.Areg(q1)] + cont);
    EL.PikeLkActionsRecConsIff(LS.Areg(q1), cont);
    EL.PikeLkActionsRecConsIff(LS.Areg(r1), [LS.Areg(q1)] + cont);
    ActsLookGatesMirrorCons(LS.Areg(q1), cont, rer, str);
    ActsLookGatesMirrorCons(LS.Areg(r1), [LS.Areg(q1)] + cont, rer, str);
  }

  lemma QuantFreeHelper(r1: L.Regex, q0: L.Regex, cont: LS.Actions, rer: LW.RegExpRecord, str: string,
                        greedy: bool, delta: LN.NoI, inp: LC.Input)
    requires q0 == L.Quantified(greedy, 0, FS.NoiPred(delta), r1)
    requires EL.PikeLkRegexRec(r1) && RegLookGatesMirror(r1, rer, str)
    requires EL.PikeLkActionsRec(cont) && ActsLookGatesMirror(cont, rer, str)
    ensures EL.PikeLkActionsRec([LS.Areg(r1), LS.Acheck(inp), LS.Areg(q0)] + cont)
    ensures ActsLookGatesMirror([LS.Areg(r1), LS.Acheck(inp), LS.Areg(q0)] + cont, rer, str)
  {
    assert EL.PikeLkRegexRec(q0) && RegLookGatesMirror(q0, rer, str);
    assert [LS.Areg(r1), LS.Acheck(inp), LS.Areg(q0)] + cont
        == [LS.Areg(r1)] + ([LS.Acheck(inp)] + ([LS.Areg(q0)] + cont));
    EL.PikeLkActionsRecConsIff(LS.Areg(q0), cont);
    EL.PikeLkActionsRecConsIff(LS.Acheck(inp), [LS.Areg(q0)] + cont);
    EL.PikeLkActionsRecConsIff(LS.Areg(r1), [LS.Acheck(inp)] + ([LS.Areg(q0)] + cont));
    ActsLookGatesMirrorCons(LS.Areg(q0), cont, rer, str);
    ActsLookGatesMirrorCons(LS.Acheck(inp), [LS.Areg(q0)] + cont, rer, str);
    ActsLookGatesMirrorCons(LS.Areg(r1), [LS.Acheck(inp)] + ([LS.Areg(q0)] + cont), rer, str);
  }

  lemma GroupFragHelper(r1: L.Regex, gid: nat, cont: LS.Actions, rer: LW.RegExpRecord, str: string)
    requires EL.PikeLkRegexRec(r1) && RegLookGatesMirror(r1, rer, str)
    requires EL.PikeLkActionsRec(cont) && ActsLookGatesMirror(cont, rer, str)
    ensures EL.PikeLkActionsRec([LS.Areg(r1), LS.Aclose(gid)] + cont)
    ensures ActsLookGatesMirror([LS.Areg(r1), LS.Aclose(gid)] + cont, rer, str)
  {
    assert [LS.Areg(r1), LS.Aclose(gid)] + cont == [LS.Areg(r1)] + ([LS.Aclose(gid)] + cont);
    EL.PikeLkActionsRecConsIff(LS.Aclose(gid), cont);
    EL.PikeLkActionsRecConsIff(LS.Areg(r1), [LS.Aclose(gid)] + cont);
    ActsLookGatesMirrorCons(LS.Aclose(gid), cont, rer, str);
    ActsLookGatesMirrorCons(LS.Areg(r1), [LS.Aclose(gid)] + cont, rer, str);
  }

  /** Fuel-free wrapper: `ComputeTr` backward mirrors `ComputeTr` of the reversed
      stack over the swapped input (`TreeMirrorRelLk`). */
  lemma ComputeTrReverseLk(rer: LW.RegExpRecord, acts: LS.Actions, inp: LC.Input,
                           gm1: LG.GroupMap, gm2: LG.GroupMap, str: string, cp0: nat, Sin: set<LG.GroupId>)
    requires EL.PikeLkActionsRec(acts)
    requires ActsLookGatesMirror(acts, rer, str)
    requires cp0 <= |str| && inp == PIV.InpOfCp(str, cp0)
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
    ComputeTreeReverseLk(rer, acts, inp, gm1, gm2, fuel, str, cp0, Sin);
    CI.ComputeIsTreeThm(rer, acts, inp, gm1, WP.Backward, fuel, b.value);
    FU.IsTreeEqComputeTr(rer, acts, inp, gm1, WP.Backward, b.value);
    CI.ComputeIsTreeThm(rer, racts, sinp, gm2, WP.Forward, fuel, fw.value);
    FU.IsTreeEqComputeTr(rer, racts, sinp, gm2, WP.Forward, fw.value);
  }

  // ===========================================================================
  // BRICK 2: discharge the builder's gate hypothesis from the oracle
  // ===========================================================================

  /** One inner look, one position: `GateAgree` from the oracle. Instantiates
      `InnerGateAgree` with the look's lid (via `AR.LmapOk` on the original and
      the RevRE-mirrored regex) and the oracle bit at `cp`/`n-cp`; the endpoint
      swap `InpOfCp(rstr, n-cp) == SwapInput(InpOfCp(str, cp))` (`SD.InputAtSwap`)
      reconciles `InnerGateAgree`'s conclusion with `GateAgree`. */
  lemma LookGateDischargeOne(rer: LW.RegExpRecord, re: R.regex, r1: R.regex, qm: AR.QMap, qm': AR.QMap,
                             str: string, rstr: string, n: nat, cp: nat, lid: int, la: R.lookaround)
    requires re == R.Re_lookaround(lid, la, r1) && T.TransWf(re)
    requires n == |str| && rstr == LC.Reverse(str) && |rstr| == n && |qm.ov| == n + 1 && cp <= n
    requires T.TransWf(SD.RevRE(re))
    requires qm'.ov == MIR.MirrorView(qm.ov, n)
    requires OracleColsOkRE(rer, qm, str, re)
    requires OracleColsOkRE(rer, qm', rstr, SD.RevRE(re))
    ensures GateAgree(rer, T.TrLookaround(la), T.Translate(r1), PIV.InpOfCp(str, cp))
  {
    var lk := T.TrLookaround(la);
    var r1L := T.Translate(r1);
    // backward bit from OracleColsOkRE(qm, str, re) at k = cp
    assert LOr.view_get_oracle(qm.ov, cp, lid)
        <==> LT.TreeRes(FU.ComputeTr(rer, [LS.Areg(r1L)], PIV.InpOfCp(str, cp), LG.Empty, L.LkDir(lk)),
                        LG.Empty, PIV.InpOfCp(str, cp), L.LkDir(lk)).Some?;
    // mirror bit from OracleColsOkRE(qm', rstr, RevRE(re)) at k = n-cp; Translate(RevRE(r1)) == RevL(r1L)
    assert SD.RevRE(re) == R.Re_lookaround(lid, la, SD.RevRE(r1));
    SD.TranslateRevRE(r1);
    assert T.Translate(SD.RevRE(r1)) == SD.RevL(r1L);
    assert LOr.view_get_oracle(qm'.ov, n - cp, lid)
        <==> LT.TreeRes(FU.ComputeTr(rer, [LS.Areg(SD.RevL(r1L))], PIV.InpOfCp(rstr, n - cp), LG.Empty, L.LkDir(lk)),
                        LG.Empty, PIV.InpOfCp(rstr, n - cp), L.LkDir(lk)).Some?;
    InnerGateAgree(rer, qm, qm', str, rstr, n, cp, lid, lk, r1L);
    // endpoint swap: InpOfCp(rstr, n-cp) == SwapInput(InpOfCp(str, cp))
    SD.InputAtSwap(str, cp);
    assert PIV.InpOfCp(str, cp) == T.InputAt(str, cp) by { LS.ReverseLength(str[..cp]); }
    assert PIV.InpOfCp(rstr, n - cp) == T.InputAt(rstr, n - cp) by { LS.ReverseLength(rstr[..n - cp]); }
  }

  /** THE DISCHARGE: the builder's string-relative gate hypothesis
      `RegLookGatesMirror(Translate(re), rer, str)` holds when the oracle is
      correct on `str` (for `qm`) and on `rstr = Reverse(str)` (for the mirror
      `qm'`, whose look bodies are `RevRE` of `re`'s and whose view is
      `MirrorView`). Recurses over the RegElk `re` (lids live there); each look
      is discharged by `LookGateDischargeOne`. */
  lemma RegLookGatesMirrorDischarge(rer: LW.RegExpRecord, re: R.regex, qm: AR.QMap, qm': AR.QMap,
                                    str: string, rstr: string, n: nat)
    requires T.TransWf(re)
    requires n == |str| && rstr == LC.Reverse(str) && |rstr| == n && |qm.ov| == n + 1
    requires T.TransWf(SD.RevRE(re))
    requires qm'.ov == MIR.MirrorView(qm.ov, n)
    requires OracleColsOkRE(rer, qm, str, re)
    requires OracleColsOkRE(rer, qm', rstr, SD.RevRE(re))
    ensures RegLookGatesMirror(T.Translate(re), rer, str)
    decreases re
  {
    match re
    case Re_empty =>
    case Re_character(_) =>
    case Re_anchor(_) =>
    case Re_alt(r1, r2) =>
      assert SD.RevRE(re) == R.Re_alt(SD.RevRE(r1), SD.RevRE(r2));
      SD.RevRETransWf(r1); SD.RevRETransWf(r2);
      RegLookGatesMirrorDischarge(rer, r1, qm, qm', str, rstr, n);
      RegLookGatesMirrorDischarge(rer, r2, qm, qm', str, rstr, n);
    case Re_con(r1, r2) =>
      assert SD.RevRE(re) == R.Re_con(SD.RevRE(r2), SD.RevRE(r1));
      SD.RevRETransWf(r1); SD.RevRETransWf(r2);
      RegLookGatesMirrorDischarge(rer, r1, qm, qm', str, rstr, n);
      RegLookGatesMirrorDischarge(rer, r2, qm, qm', str, rstr, n);
    case Re_quant(qn, qq, qt, r1) =>
      assert SD.RevRE(re) == R.Re_quant(qn, qq, qt, SD.RevRE(r1));
      SD.RevRETransWf(r1);
      RegLookGatesMirrorDischarge(rer, r1, qm, qm', str, rstr, n);
    case Re_capture(cid, r1) =>
      assert SD.RevRE(re) == R.Re_capture(cid, SD.RevRE(r1));
      SD.RevRETransWf(r1);
      RegLookGatesMirrorDischarge(rer, r1, qm, qm', str, rstr, n);
    case Re_lookaround(lid, la, r1) =>
      var lk := T.TrLookaround(la);
      var r1L := T.Translate(r1);
      assert T.Translate(re) == L.LookaroundR(lk, r1L);
      forall cp': nat | cp' <= n ensures GateAgree(rer, lk, r1L, PIV.InpOfCp(str, cp')) {
        LookGateDischargeOne(rer, re, r1, qm, qm', str, rstr, n, cp', lid, la);
      }
      assert SD.RevRE(re) == R.Re_lookaround(lid, la, SD.RevRE(r1));
      SD.RevRETransWf(r1);
      RegLookGatesMirrorDischarge(rer, r1, qm, qm', str, rstr, n);
  }

  // ===========================================================================
  // BRICK 4 establishment (1/3): GateStableLk for ComputeTr trees
  // ===========================================================================

  /** An LK node's gate is gm-CONSTANT: since the node exists (`LkResult` at the
      build map is `Some`), the gate re-evaluates the same way for ANY map — Some
      for positive, None for negative. Pure `LkResultGmIndep` (unconditional). */
  lemma LookGateStableAt(lk: L.Lookaround, tlk: LT.Tree, inp: LC.Input, gm: LG.GroupMap)
    requires LS.LkResult(lk, tlk, gm, inp).Some?
    ensures L.Positivity(lk) ==> (forall gm2: LG.GroupMap :: LT.TreeRes(tlk, gm2, inp, L.LkDir(lk)).Some?)
    ensures !L.Positivity(lk) ==> (forall gm2: LG.GroupMap :: LT.TreeRes(tlk, gm2, inp, L.LkDir(lk)).None?)
  {
    EL.LkResultGmIndep(lk, tlk, gm, inp);
    forall gm2: LG.GroupMap
      ensures L.Positivity(lk) ==> LT.TreeRes(tlk, gm2, inp, L.LkDir(lk)).Some?
      ensures !L.Positivity(lk) ==> LT.TreeRes(tlk, gm2, inp, L.LkDir(lk)).None?
    {
      EL.LkResultGmIndep(lk, tlk, gm2, inp);
    }
  }

  /** Fuel helper: every LK node in a `ComputeTree`-built tree of a recursive-
      fragment stack has a gm-constant gate (`GateStableLk`). Mirrors
      `ComputeTree`'s construction case-for-case. */
  lemma ComputeTreeGateStable(rer: LW.RegExpRecord, acts: LS.Actions, inp: LC.Input,
                              gm: LG.GroupMap, dir: WP.Direction, fuel: nat)
    requires EL.PikeLkActionsRec(acts)
    ensures FS.ComputeTree(rer, acts, inp, gm, dir, fuel).Some? ==>
            GateStableLk(FS.ComputeTree(rer, acts, inp, gm, dir, fuel).value, inp, dir)
    decreases fuel
  {
    if fuel == 0 { return; }
    var f := fuel - 1;
    if |acts| == 0 { return; }
    var cont := acts[1..];
    EL.PikeLkActionsRecConsIff(acts[0], cont);
    match acts[0]
    case Acheck(strcheck) =>
      if SSx.IsStrictSuffix(inp, strcheck, dir) {
        ComputeTreeGateStable(rer, cont, inp, gm, dir, f);
      }
    case Aclose(gid) =>
      ComputeTreeGateStable(rer, cont, inp, LG.GMClose(LC.Idx(inp), gid, gm), dir, f);
    case Areg(r) =>
      match r
      case Epsilon => ComputeTreeGateStable(rer, cont, inp, gm, dir, f);
      case Character(cd) =>
        match LC.ReadChar(rer, cd, inp, dir) {
          case Some(pair) => ComputeTreeGateStable(rer, cont, pair.1, gm, dir, f);
          case None =>
        }
      case Disjunction(r1, r2) =>
        EL.PikeLkActionsRecConsIff(LS.Areg(r1), cont);
        EL.PikeLkActionsRecConsIff(LS.Areg(r2), cont);
        ComputeTreeGateStable(rer, [LS.Areg(r1)] + cont, inp, gm, dir, f);
        ComputeTreeGateStable(rer, [LS.Areg(r2)] + cont, inp, gm, dir, f);
      case Sequence(r1, r2) =>
        assert EL.PikeLkActionsRec(LS.SeqList(r1, r2, dir) + cont) by {
          SeqListFrag(r1, r2, dir, cont);
        }
        ComputeTreeGateStable(rer, LS.SeqList(r1, r2, dir) + cont, inp, gm, dir, f);
      case Quantified(greedy, min, delta, r1) =>
        var gidl := L.DefGroups(r1);
        if min > 0 {
          var q1 := L.Quantified(greedy, min - 1, delta, r1);
          assert EL.PikeLkActionsRec([LS.Areg(r1), LS.Areg(q1)] + cont) by {
            assert [LS.Areg(r1), LS.Areg(q1)] + cont == [LS.Areg(r1)] + ([LS.Areg(q1)] + cont);
            EL.PikeLkActionsRecConsIff(LS.Areg(q1), cont);
            EL.PikeLkActionsRecConsIff(LS.Areg(r1), [LS.Areg(q1)] + cont);
          }
          ComputeTreeGateStable(rer, [LS.Areg(r1), LS.Areg(q1)] + cont, inp, LG.GMReset(gidl, gm), dir, f);
        } else if delta == LN.NN(0) {
          ComputeTreeGateStable(rer, cont, inp, gm, dir, f);
        } else {
          var q0 := L.Quantified(greedy, 0, FS.NoiPred(delta), r1);
          assert EL.PikeLkActionsRec([LS.Areg(r1), LS.Acheck(inp), LS.Areg(q0)] + cont) by {
            assert [LS.Areg(r1), LS.Acheck(inp), LS.Areg(q0)] + cont
                == [LS.Areg(r1)] + ([LS.Acheck(inp)] + ([LS.Areg(q0)] + cont));
            EL.PikeLkActionsRecConsIff(LS.Areg(q0), cont);
            EL.PikeLkActionsRecConsIff(LS.Acheck(inp), [LS.Areg(q0)] + cont);
            EL.PikeLkActionsRecConsIff(LS.Areg(r1), [LS.Acheck(inp)] + ([LS.Areg(q0)] + cont));
          }
          ComputeTreeGateStable(rer, [LS.Areg(r1), LS.Acheck(inp), LS.Areg(q0)] + cont, inp,
                                LG.GMReset(gidl, gm), dir, f);
          ComputeTreeGateStable(rer, cont, inp, gm, dir, f);
        }
      case Group(gid, r1) =>
        assert EL.PikeLkActionsRec([LS.Areg(r1), LS.Aclose(gid)] + cont) by {
          assert [LS.Areg(r1), LS.Aclose(gid)] + cont == [LS.Areg(r1)] + ([LS.Aclose(gid)] + cont);
          EL.PikeLkActionsRecConsIff(LS.Aclose(gid), cont);
          EL.PikeLkActionsRecConsIff(LS.Areg(r1), [LS.Aclose(gid)] + cont);
        }
        ComputeTreeGateStable(rer, [LS.Areg(r1), LS.Aclose(gid)] + cont, inp,
                              LG.GMOpen(LC.Idx(inp), gid, gm), dir, f);
      case LookaroundR(lk, r1) =>
        var treelk := FS.ComputeTree(rer, [LS.Areg(r1)], inp, gm, L.LkDir(lk), f);
        if treelk.Some? {
          match LS.LkResult(lk, treelk.value, gm, inp) {
            case Some(gmlk) =>
              var tc := FS.ComputeTree(rer, cont, inp, gmlk, dir, f);
              if tc.Some? {
                ComputeTreeGateStable(rer, cont, inp, gmlk, dir, f);
                LookGateStableAt(lk, treelk.value, inp, gm);
              }
            case None =>
          }
        }
      case AnchorR(a) =>
        if LS.AnchorSatisfied(rer, a, inp) {
          ComputeTreeGateStable(rer, cont, inp, gm, dir, f);
        }
      case Backreference(gid) =>
        assert EL.PikeLkRegexRec(r);
        assert false;
  }

  /** `SeqList` of fragment regexes is a fragment stack. */
  lemma SeqListFrag(r1: L.Regex, r2: L.Regex, dir: WP.Direction, cont: LS.Actions)
    requires EL.PikeLkRegexRec(r1) && EL.PikeLkRegexRec(r2) && EL.PikeLkActionsRec(cont)
    ensures EL.PikeLkActionsRec(LS.SeqList(r1, r2, dir) + cont)
  {
    match dir
    case Forward =>
      assert LS.SeqList(r1, r2, dir) + cont == [LS.Areg(r1)] + ([LS.Areg(r2)] + cont);
      EL.PikeLkActionsRecConsIff(LS.Areg(r2), cont);
      EL.PikeLkActionsRecConsIff(LS.Areg(r1), [LS.Areg(r2)] + cont);
    case Backward =>
      assert LS.SeqList(r1, r2, dir) + cont == [LS.Areg(r2)] + ([LS.Areg(r1)] + cont);
      EL.PikeLkActionsRecConsIff(LS.Areg(r1), cont);
      EL.PikeLkActionsRecConsIff(LS.Areg(r2), [LS.Areg(r1)] + cont);
  }

  /** Fuel-free: the spec tree of a recursive-fragment regex is `GateStableLk`. */
  lemma ComputeTrGateStable(rer: LW.RegExpRecord, tr: L.Regex, inp: LC.Input, gm: LG.GroupMap, dir: WP.Direction)
    requires EL.PikeLkRegexRec(tr)
    ensures GateStableLk(FU.ComputeTr(rer, [LS.Areg(tr)], inp, gm, dir), inp, dir)
  {
    var acts := [LS.Areg(tr)];
    EL.PikeLkActionsRecConsIff(LS.Areg(tr), []);
    var fuel := FS.ActionsFuel(acts, inp, dir) + 1;
    FS.FunctionalTerminates(rer, acts, inp, gm, dir, fuel);
    var b := FS.ComputeTree(rer, acts, inp, gm, dir, fuel);
    ComputeTreeGateStable(rer, acts, inp, gm, dir, fuel);
    CI.ComputeIsTreeThm(rer, acts, inp, gm, dir, fuel, b.value);
    FU.IsTreeEqComputeTr(rer, acts, inp, gm, dir, b.value);
  }

  // ===========================================================================
  // BRICK 4 establishment (2/3): GActsOutsideSin for ComputeTr trees
  // ===========================================================================

  /** Every SURFACE `Group` (Open) gid in `r` is outside `Sin` (looks excluded —
      inner gids live in Sin). Only Opens matter (Close/Reset are unconstrained
      in `GADisjoint`). */
  ghost predicate RegOpensOutside(r: L.Regex, Sin: set<LG.GroupId>)
    decreases r
  {
    match r
    case Group(gid, r1) => gid !in Sin && RegOpensOutside(r1, Sin)
    case Disjunction(a, b) => RegOpensOutside(a, Sin) && RegOpensOutside(b, Sin)
    case Sequence(a, b) => RegOpensOutside(a, Sin) && RegOpensOutside(b, Sin)
    case Quantified(_, _, _, r1) => RegOpensOutside(r1, Sin)
    case LookaroundR(_, _) => true
    case _ => true
  }

  ghost predicate ActsOpensOutside(acts: LS.Actions, Sin: set<LG.GroupId>) {
    forall i :: 0 <= i < |acts| && acts[i].Areg? ==> RegOpensOutside(acts[i].r, Sin)
  }

  lemma ActsOpensOutsideTail(acts: LS.Actions, Sin: set<LG.GroupId>)
    requires |acts| > 0 && ActsOpensOutside(acts, Sin)
    ensures ActsOpensOutside(acts[1..], Sin)
  { forall i | 0 <= i < |acts[1..]| && acts[1..][i].Areg? ensures RegOpensOutside(acts[1..][i].r, Sin) { assert acts[1..][i] == acts[i + 1]; } }

  lemma ActsOpensOutsideCons(a: LS.Action, acts: LS.Actions, Sin: set<LG.GroupId>)
    requires ActsOpensOutside(acts, Sin) && (a.Areg? ==> RegOpensOutside(a.r, Sin))
    ensures ActsOpensOutside([a] + acts, Sin)
  { forall i | 0 <= i < |[a] + acts| && ([a] + acts)[i].Areg? ensures RegOpensOutside(([a] + acts)[i].r, Sin) { if i == 0 {} else { assert ([a] + acts)[i] == acts[i - 1]; } } }

  /** Fuel helper: a `ComputeTree`-built tree of an `ActsOpensOutside` stack has
      all its SURFACE Open actions outside `Sin` (`GActsOutsideSin`). */
  lemma ComputeTreeGActsOutside(rer: LW.RegExpRecord, acts: LS.Actions, inp: LC.Input,
                                gm: LG.GroupMap, dir: WP.Direction, fuel: nat, Sin: set<LG.GroupId>)
    requires EL.PikeLkActionsRec(acts) && ActsOpensOutside(acts, Sin)
    ensures FS.ComputeTree(rer, acts, inp, gm, dir, fuel).Some? ==>
            GActsOutsideSin(FS.ComputeTree(rer, acts, inp, gm, dir, fuel).value, Sin)
    decreases fuel
  {
    if fuel == 0 { return; }
    var f := fuel - 1;
    if |acts| == 0 { return; }
    var cont := acts[1..];
    EL.PikeLkActionsRecConsIff(acts[0], cont);
    ActsOpensOutsideTail(acts, Sin);
    match acts[0]
    case Acheck(strcheck) =>
      if SSx.IsStrictSuffix(inp, strcheck, dir) { ComputeTreeGActsOutside(rer, cont, inp, gm, dir, f, Sin); }
    case Aclose(gid) =>
      ComputeTreeGActsOutside(rer, cont, inp, LG.GMClose(LC.Idx(inp), gid, gm), dir, f, Sin);
    case Areg(r) =>
      match r
      case Epsilon => ComputeTreeGActsOutside(rer, cont, inp, gm, dir, f, Sin);
      case Character(cd) =>
        match LC.ReadChar(rer, cd, inp, dir) {
          case Some(pair) => ComputeTreeGActsOutside(rer, cont, pair.1, gm, dir, f, Sin);
          case None =>
        }
      case Disjunction(r1, r2) =>
        RegActsHelper2(acts[0], r, r1, r2, cont, Sin);
        ComputeTreeGActsOutside(rer, [LS.Areg(r1)] + cont, inp, gm, dir, f, Sin);
        ComputeTreeGActsOutside(rer, [LS.Areg(r2)] + cont, inp, gm, dir, f, Sin);
      case Sequence(r1, r2) =>
        assert EL.PikeLkActionsRec(LS.SeqList(r1, r2, dir) + cont) by { SeqListFrag(r1, r2, dir, cont); }
        assert ActsOpensOutside(LS.SeqList(r1, r2, dir) + cont, Sin) by { SeqListOpens(r1, r2, dir, cont, Sin); }
        ComputeTreeGActsOutside(rer, LS.SeqList(r1, r2, dir) + cont, inp, gm, dir, f, Sin);
      case Quantified(greedy, min, delta, r1) =>
        var gidl := L.DefGroups(r1);
        if min > 0 {
          var q1 := L.Quantified(greedy, min - 1, delta, r1);
          QuantOpensHelper(r1, q1, cont, Sin, greedy, min, delta);
          assert EL.PikeLkActionsRec([LS.Areg(r1), LS.Areg(q1)] + cont) by {
            assert [LS.Areg(r1), LS.Areg(q1)] + cont == [LS.Areg(r1)] + ([LS.Areg(q1)] + cont);
            EL.PikeLkActionsRecConsIff(LS.Areg(q1), cont);
            EL.PikeLkActionsRecConsIff(LS.Areg(r1), [LS.Areg(q1)] + cont);
          }
          ComputeTreeGActsOutside(rer, [LS.Areg(r1), LS.Areg(q1)] + cont, inp, LG.GMReset(gidl, gm), dir, f, Sin);
        } else if delta == LN.NN(0) {
          ComputeTreeGActsOutside(rer, cont, inp, gm, dir, f, Sin);
        } else {
          var q0 := L.Quantified(greedy, 0, FS.NoiPred(delta), r1);
          QuantFreeOpensHelper(r1, q0, cont, Sin, greedy, delta, inp);
          assert EL.PikeLkActionsRec([LS.Areg(r1), LS.Acheck(inp), LS.Areg(q0)] + cont) by {
            assert [LS.Areg(r1), LS.Acheck(inp), LS.Areg(q0)] + cont
                == [LS.Areg(r1)] + ([LS.Acheck(inp)] + ([LS.Areg(q0)] + cont));
            EL.PikeLkActionsRecConsIff(LS.Areg(q0), cont);
            EL.PikeLkActionsRecConsIff(LS.Acheck(inp), [LS.Areg(q0)] + cont);
            EL.PikeLkActionsRecConsIff(LS.Areg(r1), [LS.Acheck(inp)] + ([LS.Areg(q0)] + cont));
          }
          ComputeTreeGActsOutside(rer, [LS.Areg(r1), LS.Acheck(inp), LS.Areg(q0)] + cont, inp, LG.GMReset(gidl, gm), dir, f, Sin);
          ComputeTreeGActsOutside(rer, cont, inp, gm, dir, f, Sin);
        }
      case Group(gid, r1) =>
        assert gid !in Sin && RegOpensOutside(r1, Sin);   // from RegOpensOutside(Group)
        GroupOpensHelper(r1, gid, cont, Sin);
        assert EL.PikeLkActionsRec([LS.Areg(r1), LS.Aclose(gid)] + cont) by {
          assert [LS.Areg(r1), LS.Aclose(gid)] + cont == [LS.Areg(r1)] + ([LS.Aclose(gid)] + cont);
          EL.PikeLkActionsRecConsIff(LS.Aclose(gid), cont);
          EL.PikeLkActionsRecConsIff(LS.Areg(r1), [LS.Aclose(gid)] + cont);
        }
        ComputeTreeGActsOutside(rer, [LS.Areg(r1), LS.Aclose(gid)] + cont, inp, LG.GMOpen(LC.Idx(inp), gid, gm), dir, f, Sin);
      case LookaroundR(lk, r1) =>
        var treelk := FS.ComputeTree(rer, [LS.Areg(r1)], inp, gm, L.LkDir(lk), f);
        if treelk.Some? {
          match LS.LkResult(lk, treelk.value, gm, inp) {
            case Some(gmlk) =>
              var tc := FS.ComputeTree(rer, cont, inp, gmlk, dir, f);
              if tc.Some? { ComputeTreeGActsOutside(rer, cont, inp, gmlk, dir, f, Sin); }
            case None =>
          }
        }
      case AnchorR(a) =>
        if LS.AnchorSatisfied(rer, a, inp) { ComputeTreeGActsOutside(rer, cont, inp, gm, dir, f, Sin); }
      case Backreference(gid) => assert EL.PikeLkRegexRec(r); assert false;
  }

  // --- ActsOpensOutside threading helpers (mirror the fragment helpers) ---
  lemma RegActsHelper2(a0: LS.Action, r: L.Regex, r1: L.Regex, r2: L.Regex, cont: LS.Actions, Sin: set<LG.GroupId>)
    requires a0 == LS.Areg(r) && (r == L.Disjunction(r1, r2))
    requires EL.PikeLkActionsRec([a0] + cont) && ActsOpensOutside([a0] + cont, Sin)
    ensures EL.PikeLkActionsRec([LS.Areg(r1)] + cont) && ActsOpensOutside([LS.Areg(r1)] + cont, Sin)
    ensures EL.PikeLkActionsRec([LS.Areg(r2)] + cont) && ActsOpensOutside([LS.Areg(r2)] + cont, Sin)
  {
    assert ([a0] + cont)[0] == a0 && ([a0] + cont)[1..] == cont;
    EL.PikeLkActionsRecConsIff(a0, cont); ActsOpensOutsideTail([a0] + cont, Sin);
    assert RegOpensOutside(r, Sin);
    EL.PikeLkActionsRecConsIff(LS.Areg(r1), cont); EL.PikeLkActionsRecConsIff(LS.Areg(r2), cont);
    ActsOpensOutsideCons(LS.Areg(r1), cont, Sin); ActsOpensOutsideCons(LS.Areg(r2), cont, Sin);
  }
  lemma SeqListOpens(r1: L.Regex, r2: L.Regex, dir: WP.Direction, cont: LS.Actions, Sin: set<LG.GroupId>)
    requires RegOpensOutside(r1, Sin) && RegOpensOutside(r2, Sin) && ActsOpensOutside(cont, Sin)
    ensures ActsOpensOutside(LS.SeqList(r1, r2, dir) + cont, Sin)
  {
    match dir
    case Forward =>
      assert LS.SeqList(r1, r2, dir) + cont == [LS.Areg(r1)] + ([LS.Areg(r2)] + cont);
      ActsOpensOutsideCons(LS.Areg(r2), cont, Sin); ActsOpensOutsideCons(LS.Areg(r1), [LS.Areg(r2)] + cont, Sin);
    case Backward =>
      assert LS.SeqList(r1, r2, dir) + cont == [LS.Areg(r2)] + ([LS.Areg(r1)] + cont);
      ActsOpensOutsideCons(LS.Areg(r1), cont, Sin); ActsOpensOutsideCons(LS.Areg(r2), [LS.Areg(r1)] + cont, Sin);
  }
  lemma QuantOpensHelper(r1: L.Regex, q1: L.Regex, cont: LS.Actions, Sin: set<LG.GroupId>, greedy: bool, min: nat, delta: LN.NoI)
    requires min > 0 && q1 == L.Quantified(greedy, min - 1, delta, r1)
    requires RegOpensOutside(r1, Sin) && ActsOpensOutside(cont, Sin)
    ensures ActsOpensOutside([LS.Areg(r1), LS.Areg(q1)] + cont, Sin)
  {
    assert RegOpensOutside(q1, Sin);
    assert [LS.Areg(r1), LS.Areg(q1)] + cont == [LS.Areg(r1)] + ([LS.Areg(q1)] + cont);
    ActsOpensOutsideCons(LS.Areg(q1), cont, Sin); ActsOpensOutsideCons(LS.Areg(r1), [LS.Areg(q1)] + cont, Sin);
  }
  lemma QuantFreeOpensHelper(r1: L.Regex, q0: L.Regex, cont: LS.Actions, Sin: set<LG.GroupId>, greedy: bool, delta: LN.NoI, inp: LC.Input)
    requires q0 == L.Quantified(greedy, 0, FS.NoiPred(delta), r1)
    requires RegOpensOutside(r1, Sin) && ActsOpensOutside(cont, Sin)
    ensures ActsOpensOutside([LS.Areg(r1), LS.Acheck(inp), LS.Areg(q0)] + cont, Sin)
  {
    assert RegOpensOutside(q0, Sin);
    assert [LS.Areg(r1), LS.Acheck(inp), LS.Areg(q0)] + cont == [LS.Areg(r1)] + ([LS.Acheck(inp)] + ([LS.Areg(q0)] + cont));
    ActsOpensOutsideCons(LS.Areg(q0), cont, Sin); ActsOpensOutsideCons(LS.Acheck(inp), [LS.Areg(q0)] + cont, Sin);
    ActsOpensOutsideCons(LS.Areg(r1), [LS.Acheck(inp)] + ([LS.Areg(q0)] + cont), Sin);
  }
  lemma GroupOpensHelper(r1: L.Regex, gid: nat, cont: LS.Actions, Sin: set<LG.GroupId>)
    requires RegOpensOutside(r1, Sin) && ActsOpensOutside(cont, Sin)
    ensures ActsOpensOutside([LS.Areg(r1), LS.Aclose(gid)] + cont, Sin)
  {
    assert [LS.Areg(r1), LS.Aclose(gid)] + cont == [LS.Areg(r1)] + ([LS.Aclose(gid)] + cont);
    ActsOpensOutsideCons(LS.Aclose(gid), cont, Sin); ActsOpensOutsideCons(LS.Areg(r1), [LS.Aclose(gid)] + cont, Sin);
  }

  /** Fuel-free: the spec tree of a fragment regex whose surface Opens avoid
      `Sin` is `GActsOutsideSin`. */
  lemma ComputeTrGActsOutside(rer: LW.RegExpRecord, tr: L.Regex, inp: LC.Input, gm: LG.GroupMap,
                              dir: WP.Direction, Sin: set<LG.GroupId>)
    requires EL.PikeLkRegexRec(tr) && RegOpensOutside(tr, Sin)
    ensures GActsOutsideSin(FU.ComputeTr(rer, [LS.Areg(tr)], inp, gm, dir), Sin)
  {
    var acts := [LS.Areg(tr)];
    EL.PikeLkActionsRecConsIff(LS.Areg(tr), []);
    assert ActsOpensOutside(acts, Sin);
    var fuel := FS.ActionsFuel(acts, inp, dir) + 1;
    FS.FunctionalTerminates(rer, acts, inp, gm, dir, fuel);
    var b := FS.ComputeTree(rer, acts, inp, gm, dir, fuel);
    ComputeTreeGActsOutside(rer, acts, inp, gm, dir, fuel, Sin);
    CI.ComputeIsTreeThm(rer, acts, inp, gm, dir, fuel, b.value);
    FU.IsTreeEqComputeTr(rer, acts, inp, gm, dir, b.value);
  }

  // ===========================================================================
  // BRICK 4 establishment (3/3): CloseDiscLk for ComputeTr trees
  // ===========================================================================

  /** The nested analogue of `CD.StackInv`: the close-discipline invariant, but
      with `PikeLkActionsRec` (allows looks) instead of `GroupOkActs`. The
      look-agnostic components (`ClosesActs`/`HeadsFresh`/`HeadsNoDup`) are reused
      from `CD` unchanged. */
  ghost predicate StackInvLk(acts: LS.Actions) {
    && CD.NoDupG(CD.ClosesActs(acts))
    && CD.HeadsFreshOfCloses(acts)
    && CD.HeadsNoDupDefs(acts)
    && EL.PikeLkActionsRec(acts)
  }

  lemma StackInvLkTail(acts: LS.Actions)
    requires |acts| > 0 && StackInvLk(acts)
    ensures StackInvLk(acts[1..])
  {
    assert acts == [acts[0]] + acts[1..];
    if acts[0].Aclose? {
      CD.ClosesActsConsClose(acts[0].gid, acts[1..]);
      CD.NoDupGTail(acts[0].gid, CD.ClosesActs(acts[1..]));
    } else {
      CD.ClosesActsConsNonClose(acts[0], acts[1..]);
    }
    EL.PikeLkActionsRecConsIff(acts[0], acts[1..]);
  }

  /** Prepend a fragment `Areg`/`Acheck` whose defs avoid the current closes. */
  lemma StackInvLkConsFront(a: LS.Action, cont: LS.Actions)
    requires StackInvLk(cont)
    requires a.Acheck? || (a.Areg? && EL.PikeLkRegexRec(a.r)
                           && CD.NoDupG(L.DefGroups(a.r))
                           && (forall g :: g in L.DefGroups(a.r) ==> g !in CD.ClosesActs(cont)))
    ensures StackInvLk([a] + cont)
  {
    CD.ClosesActsConsNonClose(a, cont);
    assert ([a] + cont)[1..] == cont;
    EL.PikeLkActionsRecConsIff(a, cont);
  }

  lemma StackInvLkConsRegAvoid(r: L.Regex, cont: LS.Actions)
    requires StackInvLk(cont)
    requires EL.PikeLkRegexRec(r) && CD.NoDupG(L.DefGroups(r))
    requires forall g :: g in L.DefGroups(r) ==> g !in CD.ClosesActs(cont)
    ensures StackInvLk([LS.Areg(r)] + cont)
  {
    StackInvLkConsFront(LS.Areg(r), cont);
  }

  lemma StackInvLkGroup(gid: LG.GroupId, r1: L.Regex, cont: LS.Actions)
    requires StackInvLk([LS.Areg(L.Group(gid, r1))] + cont)
    ensures StackInvLk([LS.Areg(r1), LS.Aclose(gid)] + cont)
  {
    var acts := [LS.Areg(L.Group(gid, r1))] + cont;
    assert acts[0] == LS.Areg(L.Group(gid, r1)) && acts[1..] == cont;
    StackInvLkTail(acts);
    assert L.DefGroups(L.Group(gid, r1)) == [gid] + L.DefGroups(r1);
    assert CD.NoDupG([gid] + L.DefGroups(r1));
    CD.NoDupGTail(gid, L.DefGroups(r1));
    assert forall g :: g in [gid] + L.DefGroups(r1) ==> g !in CD.ClosesActs(cont);
    assert gid !in CD.ClosesActs(cont);
    assert EL.PikeLkRegexRec(L.Group(gid, r1));
    assert EL.PikeLkRegexRec(r1);
    var mid := [LS.Aclose(gid)] + cont;
    CD.ClosesActsConsClose(gid, cont);
    CD.NoDupGPrepend(gid, CD.ClosesActs(cont));
    assert mid[0] == LS.Aclose(gid) && mid[1..] == cont;
    assert CD.HeadsFreshOfCloses(mid);
    assert CD.HeadsNoDupDefs(mid);
    EL.PikeLkActionsRecConsIff(LS.Aclose(gid), cont);
    assert StackInvLk(mid);
    forall g | g in L.DefGroups(r1) ensures g !in CD.ClosesActs(mid) {
      assert g != gid;
      assert g !in CD.ClosesActs(cont);
    }
    StackInvLkConsFront(LS.Areg(r1), mid);
    assert [LS.Areg(r1)] + mid == [LS.Areg(r1), LS.Aclose(gid)] + cont;
  }

  lemma SeqListStackInvLk(r1: L.Regex, r2: L.Regex, dir: WP.Direction, cont: LS.Actions)
    requires StackInvLk(cont)
    requires EL.PikeLkRegexRec(r1) && EL.PikeLkRegexRec(r2)
    requires CD.NoDupG(L.DefGroups(r1) + L.DefGroups(r2))
    requires forall g :: g in L.DefGroups(r1) + L.DefGroups(r2) ==> g !in CD.ClosesActs(cont)
    ensures StackInvLk(LS.SeqList(r1, r2, dir) + cont)
  {
    CD.DefGroupsConcatNoDup(r1, r2);
    NoDupGSuffix(L.DefGroups(r1), L.DefGroups(r2));
    CD.DefGroupsConcatAvoid(r1, r2, cont);
    DefGroupsConcatAvoidSym(r1, r2, cont);
    match dir
    case Forward =>
      assert LS.SeqList(r1, r2, dir) + cont == [LS.Areg(r1)] + ([LS.Areg(r2)] + cont);
      StackInvLkConsRegAvoid(r2, cont);
      forall g | g in L.DefGroups(r1) ensures g !in CD.ClosesActs([LS.Areg(r2)] + cont) {
        CD.ClosesActsConsNonClose(LS.Areg(r2), cont);
      }
      StackInvLkConsRegAvoid(r1, [LS.Areg(r2)] + cont);
    case Backward =>
      assert LS.SeqList(r1, r2, dir) + cont == [LS.Areg(r2)] + ([LS.Areg(r1)] + cont);
      StackInvLkConsRegAvoid(r1, cont);
      forall g | g in L.DefGroups(r2) ensures g !in CD.ClosesActs([LS.Areg(r1)] + cont) {
        CD.ClosesActsConsNonClose(LS.Areg(r1), cont);
      }
      StackInvLkConsRegAvoid(r2, [LS.Areg(r1)] + cont);
  }

  lemma DefGroupsConcatAvoidSym(r1: L.Regex, r2: L.Regex, cont: LS.Actions)
    requires forall g :: g in L.DefGroups(r1) + L.DefGroups(r2) ==> g !in CD.ClosesActs(cont)
    ensures forall g :: g in L.DefGroups(r2) ==> g !in CD.ClosesActs(cont)
  {}

  /** `NoDupG` of a concatenation implies `NoDupG` of the suffix. */
  lemma NoDupGSuffix(a: seq<LG.GroupId>, b: seq<LG.GroupId>)
    requires CD.NoDupG(a + b)
    ensures CD.NoDupG(b)
  {
    forall i, j | 0 <= i < j < |b| ensures b[i] != b[j] {
      assert (a + b)[|a| + i] == b[i] && (a + b)[|a| + j] == b[j];
    }
  }

  /** `SeqList` prepends two non-Aclose heads, so it doesn't change the closes. */
  lemma SeqListClosesSetLk(r1: L.Regex, r2: L.Regex, dir: WP.Direction, cont: LS.Actions)
    ensures CD.ClosesSet(LS.SeqList(r1, r2, dir) + cont) == CD.ClosesSet(cont)
  {
    match dir
    case Forward =>
      assert LS.SeqList(r1, r2, dir) + cont == [LS.Areg(r1)] + ([LS.Areg(r2)] + cont);
      CD.ClosesActsConsNonClose(LS.Areg(r2), cont);
      CD.ClosesActsConsNonClose(LS.Areg(r1), [LS.Areg(r2)] + cont);
    case Backward =>
      assert LS.SeqList(r1, r2, dir) + cont == [LS.Areg(r2)] + ([LS.Areg(r1)] + cont);
      CD.ClosesActsConsNonClose(LS.Areg(r1), cont);
      CD.ClosesActsConsNonClose(LS.Areg(r2), [LS.Areg(r1)] + cont);
  }

  lemma QuantStackInvLk(greedy: bool, min: nat, delta: LN.NoI, r1: L.Regex, cont: LS.Actions)
    requires min > 0 && StackInvLk(cont)
    requires min > 1 && delta.Inf? && greedy ==> NUL.NonNullableL(r1)   // §2.5b interim
    requires EL.PikeLkRegexRec(r1) && CD.NoDupG(L.DefGroups(r1))
    requires forall g :: g in L.DefGroups(r1) ==> g !in CD.ClosesActs(cont)
    ensures StackInvLk([LS.Areg(r1), LS.Areg(L.Quantified(greedy, min - 1, delta, r1))] + cont)
  {
    var q1 := L.Quantified(greedy, min - 1, delta, r1);
    assert L.DefGroups(q1) == L.DefGroups(r1);
    assert EL.PikeLkRegexRec(q1);
    StackInvLkConsRegAvoid(q1, cont);
    forall g | g in L.DefGroups(r1) ensures g !in CD.ClosesActs([LS.Areg(q1)] + cont) {
      CD.ClosesActsConsNonClose(LS.Areg(q1), cont);
    }
    StackInvLkConsRegAvoid(r1, [LS.Areg(q1)] + cont);
    assert [LS.Areg(r1)] + ([LS.Areg(q1)] + cont) == [LS.Areg(r1), LS.Areg(q1)] + cont;
  }

  lemma QuantFreeStackInvLk(greedy: bool, delta: LN.NoI, r1: L.Regex, inpc: LC.Input, cont: LS.Actions)
    requires StackInvLk(cont)
    requires EL.PikeLkRegexRec(r1) && CD.NoDupG(L.DefGroups(r1))
    requires forall g :: g in L.DefGroups(r1) ==> g !in CD.ClosesActs(cont)
    ensures StackInvLk([LS.Areg(r1), LS.Acheck(inpc), LS.Areg(L.Quantified(greedy, 0, FS.NoiPred(delta), r1))] + cont)
  {
    var q0 := L.Quantified(greedy, 0, FS.NoiPred(delta), r1);
    assert L.DefGroups(q0) == L.DefGroups(r1);
    assert EL.PikeLkRegexRec(q0);
    StackInvLkConsRegAvoid(q0, cont);
    var m1 := [LS.Areg(q0)] + cont;
    forall g | g in L.DefGroups(r1) ensures g !in CD.ClosesActs(m1) { CD.ClosesActsConsNonClose(LS.Areg(q0), cont); }
    StackInvLkConsFront(LS.Acheck(inpc), m1);
    var m2 := [LS.Acheck(inpc)] + m1;
    forall g | g in L.DefGroups(r1) ensures g !in CD.ClosesActs(m2) { CD.ClosesActsConsNonClose(LS.Acheck(inpc), m1); }
    StackInvLkConsRegAvoid(r1, m2);
    assert [LS.Areg(r1)] + m2 == [LS.Areg(r1), LS.Acheck(inpc), LS.Areg(q0)] + cont;
  }

  /** Fuel helper: a `ComputeTree`-built tree of a `StackInvLk` stack satisfies
      `CloseDiscLk` at `ClosesSet(acts)`. Mirrors `CD.CloseDiscCT` case-for-case,
      + the `LookaroundR` case (LK/LKFail; inner body EXCLUDED). */
  lemma ComputeTreeCloseDiscLk(rer: LW.RegExpRecord, acts: LS.Actions, inp: LC.Input,
                               gm: LG.GroupMap, dir: WP.Direction, fuel: nat)
    requires StackInvLk(acts)
    ensures var o := FS.ComputeTree(rer, acts, inp, gm, dir, fuel);
            o.Some? ==> CloseDiscLk(o.value, CD.ClosesSet(acts))
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
        StackInvLkTail(acts);
        ComputeTreeCloseDiscLk(rer, cont, inp, gm, dir, f);
      }
    case Aclose(gid) =>
      CD.ClosesActsConsClose(gid, cont);
      assert acts == [LS.Aclose(gid)] + cont;
      CD.NoDupGTail(gid, CD.ClosesActs(cont));
      StackInvLkTail(acts);
      ComputeTreeCloseDiscLk(rer, cont, inp, LG.GMClose(LC.Idx(inp), gid, gm), dir, f);
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
      case Epsilon => StackInvLkTail(acts); ComputeTreeCloseDiscLk(rer, cont, inp, gm, dir, f);
      case Character(cd) =>
        match LC.ReadChar(rer, cd, inp, dir) {
          case Some(pair) => StackInvLkTail(acts); ComputeTreeCloseDiscLk(rer, cont, pair.1, gm, dir, f);
          case None =>
        }
      case Disjunction(r1, r2) =>
        assert L.DefGroups(r) == L.DefGroups(r1) + L.DefGroups(r2);
        CD.DefGroupsConcatAvoid(r1, r2, cont);
        DefGroupsConcatAvoidSym(r1, r2, cont);
        CD.DefGroupsConcatNoDup(r1, r2);
        NoDupGSuffix(L.DefGroups(r1), L.DefGroups(r2));
        StackInvLkTail(acts);
        StackInvLkConsRegAvoid(r1, cont);
        StackInvLkConsRegAvoid(r2, cont);
        ComputeTreeCloseDiscLk(rer, [LS.Areg(r1)] + cont, inp, gm, dir, f);
        ComputeTreeCloseDiscLk(rer, [LS.Areg(r2)] + cont, inp, gm, dir, f);
        assert CD.ClosesSet([LS.Areg(r1)] + cont) == CD.ClosesSet(cont) by { CD.ClosesActsConsNonClose(LS.Areg(r1), cont); }
        assert CD.ClosesSet([LS.Areg(r2)] + cont) == CD.ClosesSet(cont) by { CD.ClosesActsConsNonClose(LS.Areg(r2), cont); }
      case Sequence(r1, r2) =>
        assert L.DefGroups(r) == L.DefGroups(r1) + L.DefGroups(r2);
        StackInvLkTail(acts);
        SeqListStackInvLk(r1, r2, dir, cont);
        ComputeTreeCloseDiscLk(rer, LS.SeqList(r1, r2, dir) + cont, inp, gm, dir, f);
        assert CD.ClosesSet(LS.SeqList(r1, r2, dir) + cont) == O by { SeqListClosesSetLk(r1, r2, dir, cont); }
      case Quantified(greedy, min, delta, r1) =>
        var gidl := L.DefGroups(r1);
        assert L.DefGroups(r) == gidl;
        StackInvLkTail(acts);
        assert (set g | g in gidl) * O == {} by {
          forall g | g in gidl && g in O ensures false { assert g !in CD.ClosesActs(cont); }
        }
        assert O - (set g | g in gidl) == O;
        if min > 0 {
          var q1 := L.Quantified(greedy, min - 1, delta, r1);
          QuantStackInvLk(greedy, min, delta, r1, cont);
          ComputeTreeCloseDiscLk(rer, [LS.Areg(r1), LS.Areg(q1)] + cont, inp, LG.GMReset(gidl, gm), dir, f);
          var titer := FS.ComputeTree(rer, [LS.Areg(r1), LS.Areg(q1)] + cont, inp, LG.GMReset(gidl, gm), dir, f);
          if titer.Some? {
            assert CD.ClosesSet([LS.Areg(r1), LS.Areg(q1)] + cont) == O by { CD.QuantClosesSet(r1, q1, cont); }
            assert CloseDiscLk(LT.GroupActionT(LG.Reset(gidl), titer.value), O);
          }
        } else if delta == LN.NN(0) {
          ComputeTreeCloseDiscLk(rer, cont, inp, gm, dir, f);
        } else {
          var q0 := L.Quantified(greedy, 0, FS.NoiPred(delta), r1);
          QuantFreeStackInvLk(greedy, delta, r1, inp, cont);
          ComputeTreeCloseDiscLk(rer, [LS.Areg(r1), LS.Acheck(inp), LS.Areg(q0)] + cont, inp, LG.GMReset(gidl, gm), dir, f);
          ComputeTreeCloseDiscLk(rer, cont, inp, gm, dir, f);
          var titer := FS.ComputeTree(rer, [LS.Areg(r1), LS.Acheck(inp), LS.Areg(q0)] + cont, inp, LG.GMReset(gidl, gm), dir, f);
          var tskip := FS.ComputeTree(rer, cont, inp, gm, dir, f);
          if titer.Some? && tskip.Some? {
            assert CD.ClosesSet([LS.Areg(r1), LS.Acheck(inp), LS.Areg(q0)] + cont) == O by { CD.QuantFreeClosesSet(r1, q0, inp, cont); }
            assert CloseDiscLk(LT.GroupActionT(LG.Reset(gidl), titer.value), O);
            assert CloseDiscLk(tskip.value, O);
            assert CloseDiscLk(LT.GreedyChoice(greedy, LT.GroupActionT(LG.Reset(gidl), titer.value), tskip.value), O);
          }
        }
      case Group(gid, r1) =>
        StackInvLkGroup(gid, r1, cont);
        ComputeTreeCloseDiscLk(rer, [LS.Areg(r1), LS.Aclose(gid)] + cont, inp, LG.GMOpen(LC.Idx(inp), gid, gm), dir, f);
        var sub := FS.ComputeTree(rer, [LS.Areg(r1), LS.Aclose(gid)] + cont, inp, LG.GMOpen(LC.Idx(inp), gid, gm), dir, f);
        if sub.Some? {
          assert CD.ClosesSet([LS.Areg(r1), LS.Aclose(gid)] + cont) == O + {gid} by { CD.GroupClosesSet(r1, gid, cont); }
        }
      case AnchorR(a) =>
        if LS.AnchorSatisfied(rer, a, inp) { StackInvLkTail(acts); ComputeTreeCloseDiscLk(rer, cont, inp, gm, dir, f); }
      case LookaroundR(lk, r1) =>
        var treelk := FS.ComputeTree(rer, [LS.Areg(r1)], inp, gm, L.LkDir(lk), f);
        if treelk.Some? {
          match LS.LkResult(lk, treelk.value, gm, inp) {
            case Some(gmlk) =>
              var tc := FS.ComputeTree(rer, cont, inp, gmlk, dir, f);
              if tc.Some? {
                StackInvLkTail(acts);
                ComputeTreeCloseDiscLk(rer, cont, inp, gmlk, dir, f);
              }
            case None =>
          }
        }
      case Backreference(gid) => assert EL.PikeLkRegexRec(r); assert false;
  }

  /** Fuel-free: the spec tree of a fragment regex with dup-free defs has an
      LK-aware close discipline at the empty open set. */
  lemma ComputeTrCloseDiscLk(rer: LW.RegExpRecord, tr: L.Regex, inp: LC.Input, gm: LG.GroupMap, dir: WP.Direction)
    requires EL.PikeLkRegexRec(tr) && CD.NoDupG(L.DefGroups(tr))
    ensures CloseDiscLk(FU.ComputeTr(rer, [LS.Areg(tr)], inp, gm, dir), {})
  {
    var acts := [LS.Areg(tr)];
    EL.PikeLkActionsRecConsIff(LS.Areg(tr), []);
    CD.ClosesActsConsNonClose(LS.Areg(tr), []);
    assert CD.ClosesActs(acts) == [];
    assert CD.HeadsFreshOfCloses(acts);
    assert CD.HeadsNoDupDefs(acts);
    assert StackInvLk(acts);
    assert CD.ClosesSet(acts) == {};
    var fuel := FS.ActionsFuel(acts, inp, dir) + 1;
    FS.FunctionalTerminates(rer, acts, inp, gm, dir, fuel);
    var b := FS.ComputeTree(rer, acts, inp, gm, dir, fuel);
    ComputeTreeCloseDiscLk(rer, acts, inp, gm, dir, fuel);
    CI.ComputeIsTreeThm(rer, acts, inp, gm, dir, fuel, b.value);
    FU.IsTreeEqComputeTr(rer, acts, inp, gm, dir, b.value);
  }

  // ===========================================================================
  // BRICK 4 discharge: RegOpensOutside(tr, LkBodyGroups(tr)) from NoDupG
  // ===========================================================================

  /** Inner-look gids are among the defined gids. */
  lemma LkBodyGroupsSubDefsLocal(r: L.Regex)
    ensures LL.LkBodyGroups(r) <= (set g | g in L.DefGroups(r))
    decreases r
  {
    match r
    case Disjunction(r1, r2) => LkBodyGroupsSubDefsLocal(r1); LkBodyGroupsSubDefsLocal(r2);
      assert L.DefGroups(r) == L.DefGroups(r1) + L.DefGroups(r2);
    case Sequence(r1, r2) => LkBodyGroupsSubDefsLocal(r1); LkBodyGroupsSubDefsLocal(r2);
      assert L.DefGroups(r) == L.DefGroups(r1) + L.DefGroups(r2);
    case Quantified(_, _, _, r1) => LkBodyGroupsSubDefsLocal(r1);
    case Group(gid, r1) => LkBodyGroupsSubDefsLocal(r1); assert L.DefGroups(r) == [gid] + L.DefGroups(r1);
    case LookaroundR(lk, r1) => LkBodyGroupsSubDefsLocal(r1); assert L.DefGroups(r) == L.DefGroups(r1);
    case _ =>
  }

  /** `NoDupG(a+b)`: an element of `a` is not in `b`. */
  lemma NoDupGNotBoth(a: seq<LG.GroupId>, b: seq<LG.GroupId>, g: LG.GroupId)
    requires CD.NoDupG(a + b) && g in a
    ensures g !in b
  {
    if g in b {
      var i :| 0 <= i < |a| && a[i] == g;
      var j :| 0 <= j < |b| && b[j] == g;
      assert (a + b)[i] == g && (a + b)[|a| + j] == g && i < |a| + j;
    }
  }

  /** THE discharge: surface Opens of `r` avoid `S`, when `S` meets `DefGroups(r)`
      only inside looks and `r`'s defs are dup-free. At `S = LkBodyGroups(r)` the
      side condition is trivial (`g in LkBodyGroups ==> g in LkBodyGroups`). */
  lemma RegOpensOutsideFromNoDup(r: L.Regex, S: set<LG.GroupId>)
    requires CD.NoDupG(L.DefGroups(r))
    requires forall g: LG.GroupId :: g in L.DefGroups(r) && g in S ==> g in LL.LkBodyGroups(r)
    ensures RegOpensOutside(r, S)
    decreases r
  {
    match r
    case Disjunction(r1, r2) => DisjSeqOpensNoDup(r, r1, r2, S);
    case Sequence(r1, r2) => DisjSeqOpensNoDup(r, r1, r2, S);
    case Quantified(_, _, _, r1) =>
      assert L.DefGroups(r) == L.DefGroups(r1) && LL.LkBodyGroups(r) == LL.LkBodyGroups(r1);
      RegOpensOutsideFromNoDup(r1, S);
    case Group(gid, r1) =>
      assert L.DefGroups(r) == [gid] + L.DefGroups(r1);
      CD.NoDupGTail(gid, L.DefGroups(r1));
      assert LL.LkBodyGroups(r) == LL.LkBodyGroups(r1);
      LkBodyGroupsSubDefsLocal(r1);
      assert gid !in S by {
        if gid in S { assert gid in LL.LkBodyGroups(r); assert gid in L.DefGroups(r1); }
      }
      forall g: LG.GroupId | g in L.DefGroups(r1) && g in S ensures g in LL.LkBodyGroups(r1) {
        assert g in L.DefGroups(r);
      }
      RegOpensOutsideFromNoDup(r1, S);
    case LookaroundR(lk, r1) =>
    case _ =>
  }

  /** Disjunction/Sequence case of `RegOpensOutsideFromNoDup` (same shape). */
  lemma DisjSeqOpensNoDup(r: L.Regex, r1: L.Regex, r2: L.Regex, S: set<LG.GroupId>)
    requires r == L.Disjunction(r1, r2) || r == L.Sequence(r1, r2)
    requires CD.NoDupG(L.DefGroups(r))
    requires forall g: LG.GroupId :: g in L.DefGroups(r) && g in S ==> g in LL.LkBodyGroups(r)
    ensures RegOpensOutside(r1, S) && RegOpensOutside(r2, S)
    decreases r, 0
  {
    assert L.DefGroups(r) == L.DefGroups(r1) + L.DefGroups(r2);
    assert LL.LkBodyGroups(r) == LL.LkBodyGroups(r1) + LL.LkBodyGroups(r2);
    CD.DefGroupsConcatNoDup(r1, r2);
    NoDupGSuffix(L.DefGroups(r1), L.DefGroups(r2));
    LkBodyGroupsSubDefsLocal(r1); LkBodyGroupsSubDefsLocal(r2);
    forall g: LG.GroupId | g in L.DefGroups(r1) && g in S ensures g in LL.LkBodyGroups(r1) {
      assert g in L.DefGroups(r);          // DefGroups(r1) ⊆ DefGroups(r)
      assert g in LL.LkBodyGroups(r);      // hypothesis
      if g in LL.LkBodyGroups(r2) {
        assert g in L.DefGroups(r2);       // LkBodyGroupsSubDefsLocal(r2)
        NoDupGNotBoth(L.DefGroups(r1), L.DefGroups(r2), g);   // g in DefGroups(r1) => g !in DefGroups(r2)
        assert false;
      }
    }
    forall g: LG.GroupId | g in L.DefGroups(r2) && g in S ensures g in LL.LkBodyGroups(r2) {
      assert g in L.DefGroups(r);
      assert g in LL.LkBodyGroups(r);
      if g in LL.LkBodyGroups(r1) {
        assert g in L.DefGroups(r1);       // LkBodyGroupsSubDefsLocal(r1)
        NoDupGNotBoth(L.DefGroups(r1), L.DefGroups(r2), g);   // g in DefGroups(r1) => g !in DefGroups(r2)
        assert false;
      }
    }
    RegOpensOutsideFromNoDup(r1, S);
    RegOpensOutsideFromNoDup(r2, S);
  }

  /** At `S = LkBodyGroups(tr)` the discharge is unconditional beyond `NoDupG`. */
  lemma RegOpensOutsideLkBody(tr: L.Regex)
    requires CD.NoDupG(L.DefGroups(tr))
    ensures RegOpensOutside(tr, LL.LkBodyGroups(tr))
  {
    RegOpensOutsideFromNoDup(tr, LL.LkBodyGroups(tr));
  }

  // ===========================================================================
  // BRICK 3 (B4): BackBodyGmTieNested — compose builder + fold -> surface mirror
  // ===========================================================================

  /** `RevL` preserves the inner-look group set (it keeps gids, reverses
      structure). */
  lemma LkBodyGroupsRevL(r: L.Regex)
    ensures LL.LkBodyGroups(SD.RevL(r)) == LL.LkBodyGroups(r)
    decreases r
  {
    match r
    case Disjunction(r1, r2) => LkBodyGroupsRevL(r1); LkBodyGroupsRevL(r2);
    case Sequence(r1, r2) => LkBodyGroupsRevL(r1); LkBodyGroupsRevL(r2);
    case Quantified(_, _, _, r1) => LkBodyGroupsRevL(r1);
    case Group(_, r1) => LkBodyGroupsRevL(r1);
    case LookaroundR(lk, r1) =>
      LkBodyGroupsRevL(r1);
      SD.RevLDefGroupsSet(r1);
      assert (set g | g in L.DefGroups(SD.RevL(r1))) == (set g | g in L.DefGroups(r1));
    case _ =>
  }

  /** THE B4 CORE: for a nested body `tr` (recursive fragment, dup-free defs),
      the backward spec tree's first leaf and the forward RevL spec tree's first
      leaf mirror on the SURFACE (`GmAgreeOutside(_, MirrorGm(_), Sin)`), given
      the oracle-discharged gate hypothesis. The nested analogue of
      `LBV.BackBodyGmTie` — surface-only, since the inner-look captures come from
      the oracle, not the mirror. */
  lemma BackBodyGmTieNested(rer: LW.RegExpRecord, tr: L.Regex, str: string, cp: nat, n: nat,
                            Sin: set<LG.GroupId>)
    requires EL.PikeLkRegexRec(tr) && CD.NoDupG(L.DefGroups(tr))
    requires Sin == LL.LkBodyGroups(tr)
    requires n == |str| && cp <= n
    requires ActsLookGatesMirror([LS.Areg(tr)], rer, str)
    ensures
      var inpB := PIV.InpOfCp(str, cp);
      var tB := FU.ComputeTr(rer, [LS.Areg(tr)], inpB, LG.Empty, WP.Backward);
      var tF := FU.ComputeTr(rer, [LS.Areg(SD.RevL(tr))], SD.SwapInput(inpB), LG.Empty, WP.Forward);
      var rb := LT.TreeRes(tB, LG.Empty, inpB, WP.Backward);
      var rf := LT.TreeRes(tF, LG.Empty, SD.SwapInput(inpB), WP.Forward);
      && (rb.None? <==> rf.None?)
      && (rb.Some? ==>
            rf.Some?
            && rf.value.0 == SD.SwapInput(rb.value.0)
            && TRM.GmInBounds(rb.value.1, n)
            && LL.GmAgreeOutside(rf.value.1, TRM.MirrorGm(rb.value.1, n), Sin))
  {
    var inpB := PIV.InpOfCp(str, cp);
    var sinp := SD.SwapInput(inpB);
    var acts := [LS.Areg(tr)];
    var racts := [LS.Areg(SD.RevL(tr))];
    LS.ReverseLength(str[..cp]);
    assert n == |inpB.pref| + |inpB.next|;
    EL.PikeLkActionsRecConsIff(LS.Areg(tr), []);

    // ---- the two trees ----
    var tB := FU.ComputeTr(rer, acts, inpB, LG.Empty, WP.Backward);
    var tF := FU.ComputeTr(rer, racts, sinp, LG.Empty, WP.Forward);
    // builder: TreeMirrorRelLk(tB, tF, Sin). RevActs([Areg(tr)]) == [Areg(RevL(tr))].
    assert SD.RevActs(acts) == racts by { SD.RevActsCons(LS.Areg(tr), []); }
    ComputeTrReverseLk(rer, acts, inpB, LG.Empty, LG.Empty, str, cp, Sin);
    assert TreeMirrorRelLk(tB, tF, Sin);

    // ---- tree-property establishments ----
    ComputeTrGateStable(rer, tr, inpB, LG.Empty, WP.Backward);           // GateStableLk(tB, inpB, Backward)
    RevLPreservesPikeLkRec(tr);
    ComputeTrGateStable(rer, SD.RevL(tr), sinp, LG.Empty, WP.Forward);   // GateStableLk(tF, sinp, Forward)
    RegOpensOutsideLkBody(tr);                                           // RegOpensOutside(tr, Sin)
    ComputeTrGActsOutside(rer, tr, inpB, LG.Empty, WP.Backward, Sin);    // GActsOutsideSin(tB, Sin)
    ComputeTrCloseDiscLk(rer, tr, inpB, LG.Empty, WP.Backward);          // CloseDiscLk(tB, {})

    // ---- confinement (both trees) ----
    LL.BackwardBodyConfinedTree(rer, tr, inpB, Sin);                     // LkConfinedTreeK(tB, Sin)
    LkBodyGroupsRevL(tr);                                                // LkBodyGroups(RevL(tr)) == Sin
    EL.PikeLkActionsRecConsIff(LS.Areg(SD.RevL(tr)), []);
    LL.LkBodyGroupsConfines(SD.RevL(tr), Sin);
    LL.LkActsInSCons(LS.Areg(SD.RevL(tr)), [], Sin);
    LL.ComputeTrLkConfinedK(rer, racts, sinp, LG.Empty, WP.Forward, Sin); // LkConfinedTreeK(tF, Sin)

    // ---- the surface fold ----
    assert TRM.GmInBounds(LG.Empty, n);
    assert LL.GmAgreeOutside(LG.Empty, TRM.MirrorGm(LG.Empty, n), Sin) by { assert TRM.MirrorGm(LG.Empty, n) == LG.Empty; }
    assert TRM.OpenSubset(LG.Empty, {});
    TreeResMirrorLk(tB, tF, LG.Empty, LG.Empty, inpB, n, {}, Sin);
  }
}
