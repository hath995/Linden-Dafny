// §2.5b STAGE 2, RUNG E (readout side) — the reconstruction-aware GroupMap.
//
// `GmOfLiveR` is the simulation invariant's readout for a thread that carries
// nulled-exit stamps: `GmOfLive` (the clock-filtered readout) with, for every
// LIVE stamp, the stamped body's first-empty-path fold in place of its groups
// (`LiveStampsGm`). Liveness is decided by QUANT clocks only (the stamp beats
// every enclosing quantifier's clock); the thread invariants of rung D make it
// agree with `filter_capture`'s traversal.
//
// THE readout theorem (`ReconReadout`, end of file): `GmOfLive` of the
// registers `FNulledPlus` produces equals `GmOfLiveR` of the registers it
// started from. It composes `NullInterpNulled` (the null interpreter computes
// `NulledWrites`) with two structural readouts that meet on the set of groups
// the first empty path opens (`PathGroupsR`): the spec fold of `FirstEmptyPathR`
// on one side, `filter_capture` of the written registers on the other.
module LindenElkNulledReconReadout {
  import opened Std.Wrappers
  import R = RegElkRegex
  import RB = Bytecode
  import CP = Compiler
  import AI = ArrayInterp
  import AReg = Array_Regs
  import LOr = Oracle
  import RA = Anchors
  import LCdn = Cdn
  import T = LindenElkTranslate
  import NUL = LindenElkNullable
  import NR = LindenElkNfaRep
  import AR = LindenElkActionsRep
  import TR = LindenElkTreeRep
  import LC = Chars
  import LG = Groups
  import L = Regex
  import NP = LindenElkNulledPlus
  import PIV = LindenElkPikeInv
  import CE = LindenElkCheckErase
  import NRC = LindenElkNulledRecon
  import NRR = LindenElkNulledReconRegs

  // ===========================================================================
  // 1. Liveness of a stamp, and the readout.
  // ===========================================================================


  ghost function Minus(gm: LG.GroupMap, G: set<nat>): LG.GroupMap {
    gm - G
  }

  lemma ApplyPathApp(p1: seq<LG.GroupAction>, p2: seq<LG.GroupAction>, idx: nat, gm: LG.GroupMap)
    ensures NP.ApplyPath(p1 + p2, idx, gm) == NP.ApplyPath(p2, idx, NP.ApplyPath(p1, idx, gm))
    decreases |p1|
  {
    if |p1| == 0 {
      assert p1 + p2 == p2;
    } else {
      assert (p1 + p2)[0] == p1[0] && (p1 + p2)[1..] == p1[1..] + p2;
      ApplyPathApp(p1[1..], p2, idx, LG.GMUpdate(p1[0], idx, gm));
    }
  }

  // ===========================================================================
  // 2. The groups on the first empty path, and the spec-side readout (R1).
  // ===========================================================================

  // `PathGroupsR` / `ResetGroupsR` / `PathGroupsInCapIds` live in the register
  // module (`NRR`), shared with the engine-side readout.

  ghost function PathMap(G: set<nat>, cp: nat): LG.GroupMap {
    map g: nat | g in G :: LG.Range(cp, Some(cp))
  }

  /** `RepeatPath(n, Reset(G) :: p)` for `n >= 1` has the effect of one copy when
      `p` only touches `G` and its effect is `(· - G) + M`. */
  lemma RepeatPathEffect(n: nat, G: set<nat>, gl: LG.GroupSet, p: seq<LG.GroupAction>, cp: nat, M: LG.GroupMap, gm: LG.GroupMap)
    requires n >= 1
    requires forall g :: g in gl <==> g in G
    requires M.Keys <= G
    requires forall gm0: LG.GroupMap :: NP.ApplyPath(p, cp, LG.GMReset(gl, gm0)) == Minus(gm0, G) + M
    ensures NP.ApplyPath(TR.RepeatPath(n, [LG.Reset(gl)] + p), cp, gm) == Minus(gm, G) + M
    decreases n
  {
    var unit := [LG.Reset(gl)] + p;
    assert TR.RepeatPath(n, unit) == unit + TR.RepeatPath(n - 1, unit);
    ApplyPathApp(unit, TR.RepeatPath(n - 1, unit), cp, gm);
    assert NP.ApplyPath(unit, cp, gm) == NP.ApplyPath(p, cp, LG.GMUpdate(LG.Reset(gl), cp, gm)) by {
      assert unit[0] == LG.Reset(gl) && unit[1..] == p;
    }
    assert LG.GMUpdate(LG.Reset(gl), cp, gm) == LG.GMReset(gl, gm);
    var gm1 := Minus(gm, G) + M;
    assert NP.ApplyPath(unit, cp, gm) == gm1;
    if n == 1 {
      assert TR.RepeatPath(0, unit) == [];
    } else {
      RepeatPathEffect(n - 1, G, gl, p, cp, M, gm1);
      assert Minus(gm1, G) + M == Minus(gm, G) + M by {
        assert Minus(gm1, G) == Minus(gm, G);
      }
    }
  }

  /** (R1) The spec-side readout: the first empty path's fold resets the
      forced bodies' groups and captures the path's groups at `[cp, cp)`. */
  lemma PathFoldR(qm: AR.QMap, re: R.regex, inp: LC.Input, gm: LG.GroupMap)
    requires T.TransWf(re) && PIV.CapUnique(re)
    requires TR.FirstEmptyPathR(qm, re, inp).Some?
    ensures NP.ApplyPath(TR.FirstEmptyPathR(qm, re, inp).value, TR.CpOf(inp), gm)
         == Minus(gm, NRR.ResetGroupsR(qm, re, inp)) + PathMap(NRR.PathGroupsR(qm, re, inp), TR.CpOf(inp))
    decreases re
  {
    var cp := TR.CpOf(inp);
    var p := TR.FirstEmptyPathR(qm, re, inp).value;
    match re
    case Re_empty =>
      assert PathMap({}, cp) == map[];
      assert Minus(gm, {}) == gm;
    case Re_character(_) =>
    case Re_anchor(_) =>
      assert p == [];
      assert PathMap({}, cp) == map[];
      assert Minus(gm, {}) == gm;
    case Re_lookaround(_, _, _) =>
      assert p == [];
      assert PathMap({}, cp) == map[];
      assert Minus(gm, {}) == gm;
    case Re_alt(r1, r2) =>
      if TR.FirstEmptyPathR(qm, r1, inp).Some? {
        PathFoldR(qm, r1, inp, gm);
      } else {
        PathFoldR(qm, r2, inp, gm);
      }
    case Re_con(r1, r2) =>
      var p1 := TR.FirstEmptyPathR(qm, r1, inp).value;
      var p2 := TR.FirstEmptyPathR(qm, r2, inp).value;
      assert p == p1 + p2;
      ApplyPathApp(p1, p2, cp, gm);
      PathFoldR(qm, r1, inp, gm);
      var gm1 := Minus(gm, NRR.ResetGroupsR(qm, r1, inp)) + PathMap(NRR.PathGroupsR(qm, r1, inp), cp);
      PathFoldR(qm, r2, inp, gm1);
      var G1 := NRR.ResetGroupsR(qm, r1, inp);
      var G2 := NRR.ResetGroupsR(qm, r2, inp);
      var P1 := NRR.PathGroupsR(qm, r1, inp);
      var P2 := NRR.PathGroupsR(qm, r2, inp);
      // r2's reset never touches r1's path groups (disjoint capture ids) and
      // the two path maps agree on shared keys (none) — map algebra.
      NRR.PathGroupsInCapIds(qm, r1, inp);
      NRR.PathGroupsInCapIds(qm, r2, inp);
      assert Minus(gm1, G2) + PathMap(P2, cp) == Minus(gm, G1 + G2) + PathMap(P1 + P2, cp) by {
        assert PIV.CapIds(r1) * PIV.CapIds(r2) == {} by { CapUniqueDisjoint(re); }
        assert P1 * G2 == {};
        forall g: nat ensures (g in Minus(gm1, G2) + PathMap(P2, cp) <==> g in Minus(gm, G1 + G2) + PathMap(P1 + P2, cp))
                           && (g in Minus(gm1, G2) + PathMap(P2, cp) ==>
                                 (Minus(gm1, G2) + PathMap(P2, cp))[g] == (Minus(gm, G1 + G2) + PathMap(P1 + P2, cp))[g])
        {
        }
      }
    case Re_quant(nul, qid, q, r1) =>
      if q.min == 0 {
        assert p == [];
        assert PathMap({}, cp) == map[];
        assert Minus(gm, {}) == gm;
      } else {
        var p1 := TR.FirstEmptyPathR(qm, r1, inp).value;
        var gl := L.DefGroups(T.Translate(r1));
        var G := PIV.CapIds(r1);
        PIV.DefGroupsCapIds(r1);
        assert forall g :: g in gl <==> g in G;
        NRR.PathGroupsInCapIds(qm, r1, inp);
        var M := PathMap(NRR.PathGroupsR(qm, r1, inp), cp);
        assert forall gm0: LG.GroupMap :: NP.ApplyPath(p1, cp, LG.GMReset(gl, gm0)) == Minus(gm0, G) + M by {
          forall gm0: LG.GroupMap ensures NP.ApplyPath(p1, cp, LG.GMReset(gl, gm0)) == Minus(gm0, G) + M {
            PathFoldR(qm, r1, inp, LG.GMReset(gl, gm0));
            assert LG.GMReset(gl, gm0) == Minus(gm0, G);
            assert Minus(Minus(gm0, G), NRR.ResetGroupsR(qm, r1, inp)) == Minus(gm0, G);
          }
        }
        assert p == TR.RepeatPath(q.min as nat, [LG.Reset(gl)] + p1);
        RepeatPathEffect(q.min as nat, G, gl, p1, cp, M, gm);
      }
    case Re_capture(cid, r1) =>
      var p1 := TR.FirstEmptyPathR(qm, r1, inp).value;
      var g: nat := cid as nat;
      assert p == [LG.Open(g)] + p1 + [LG.Close(g)];
      var gmO := LG.GMOpen(cp, g, gm);
      assert NP.ApplyPath([LG.Open(g)], cp, gm) == gmO;
      ApplyPathApp([LG.Open(g)], p1, cp, gm);
      ApplyPathApp([LG.Open(g)] + p1, [LG.Close(g)], cp, gm);
      PathFoldR(qm, r1, inp, gmO);
      var gm1 := Minus(gmO, NRR.ResetGroupsR(qm, r1, inp)) + PathMap(NRR.PathGroupsR(qm, r1, inp), cp);
      assert NP.ApplyPath([LG.Close(g)], cp, gm1) == LG.GMClose(cp, g, gm1);
      NRR.PathGroupsInCapIds(qm, r1, inp);
      assert g !in PIV.CapIds(r1) by { CapUniqueNotIn(re); }
      assert g in gm1 && gm1[g] == LG.Range(cp, None);
      assert LG.GMClose(cp, g, gm1) == gm1[g := LG.Range(cp, Some(cp))];
      assert gm1[g := LG.Range(cp, Some(cp))]
          == Minus(gm, NRR.ResetGroupsR(qm, re, inp)) + PathMap(NRR.PathGroupsR(qm, re, inp), cp);
  }

  lemma CapUniqueDisjoint(re: R.regex)
    requires re.Re_alt? || re.Re_con?
    requires PIV.CapUnique(re)
    ensures PIV.CapIds(NRR.L1(re)) * PIV.CapIds(NRR.L2(re)) == {}
  {}

  lemma CapUniqueNotIn(re: R.regex)
    requires re.Re_capture? && re.cid >= 0
    requires PIV.CapUnique(re)
    ensures (re.cid as nat) !in PIV.CapIds(NRR.L1(re))
  {}

  /** A quant id of the second side is not one of the first (QuantUnique). */
  lemma QuantSideDisjoint(r: R.regex, q: nat)
    requires (r.Re_alt? || r.Re_con?) && PIV.QuantUnique(r)
    requires q in PIV.QuantIds(NRR.L2(r))
    ensures q !in PIV.QuantIds(NRR.L1(r))
  {
    if q in PIV.QuantIds(NRR.L1(r)) { assert q in PIV.QuantIds(NRR.L1(r)) * PIV.QuantIds(NRR.L2(r)); }
  }

  lemma CapSideDisjoint(r: R.regex, c: nat)
    requires (r.Re_alt? || r.Re_con?) && PIV.CapUnique(r)
    requires c in PIV.CapIds(NRR.L1(r))
    ensures c !in PIV.CapIds(NRR.L2(r))
  {
    if c in PIV.CapIds(NRR.L2(r)) { assert c in PIV.CapIds(NRR.L1(r)) * PIV.CapIds(NRR.L2(r)); }
  }

  // ===========================================================================
  // 3. One stamp's reconstruction (the `Some(start_cp)` branch of `FNulledPlus`):
  //    the body's groups read as the path's groups at `[cp, cp)`.
  // ===========================================================================

  type Regs3 = NRC.Regs3

  /** The `FNulledPlus` Some-branch at quantifier `qid` with body `r1`, as a triple. */
  ghost function PlusAt(qm: AR.QMap, re: R.regex, rg: Regs3, plus_bcv: seq<RB.code>, str: string, ov: LOr.OracleView): (Regs3, LOr.OracleView) {
    var (c, l, q, ov') := AI.FNulledPlus(re, rg.0, rg.1, rg.2, plus_bcv, str, ov, RA.Forward);
    ((c, l, q), ov')
  }

  /** `filter_capture` at the stamp's clock `K` over the reconstructed body: present
      iff on the path. (`EngineReadout` composed with the stamp's own recon run.) */
  lemma StampReadout(qm: AR.QMap, r: R.regex, rg: Regs3, plus_bcv: seq<RB.code>, str: string, ov: LOr.OracleView)
    requires r.Re_quant? && r.qid >= 0
    requires T.TransWf(r) && PIV.CapUnique(r) && PIV.QuantUnique(r) && NRR.LookUnique(r) && NRC.NoCdnPlusRE(r) && NRR.PlusTableOk(r, plus_bcv)
    requires ov == qm.ov
    requires NRR.QidCinPlus(r, r.qid as nat)
    requires NRR.WfRegs(rg) && NRR.CapValWf(rg) && NRR.Covers(r, rg)
    requires 0 <= AI.get_idx(rg.2.a_cp, r.qid) <= |str|
    requires var K := AI.get_idx(rg.2.a_clk, r.qid); NRR.RegsStale(NRR.L1(r), rg, K) && NRR.LookCapsAbsent(NRR.L1(r), rg) && K >= -1
    ensures var K := AI.get_idx(rg.2.a_clk, r.qid);
            var cp: nat := AI.get_idx(rg.2.a_cp, r.qid) as nat;
            var inp := T.InputAt(str, cp);
            var (rg2, ov2) := PlusAt(qm, r, rg, plus_bcv, str, ov);
            ov2 == ov && NRR.WfRegs(rg2) && NRR.Sized3(rg2, rg) && NRR.CapValWf(rg2)
            && NRR.AgreeOutside(rg2, rg, NRR.CapRegsOf(NRR.L1(r)), NRR.LookRegsOf(NRR.L1(r)), NRR.QuantRegsOf(NRR.L1(r)))
            && AI.get_idx(rg2.2.a_clk, r.qid) == K
            && TR.FirstEmptyPathR(qm, NRR.L1(r), inp).Some?
            && (forall c: nat :: c in PIV.CapIds(NRR.L1(r)) ==>
                  NRR.ReadsAs(NRR.Filt(NRR.L1(r), rg2, K), rg2, c, cp, c in NRR.PathGroupsR(qm, NRR.L1(r), inp)))
  {
    var qid := r.qid; var r1 := NRR.L1(r);
    var K := AI.get_idx(rg.2.a_clk, qid);
    var cp: nat := AI.get_idx(rg.2.a_cp, qid) as nat;
    var cpi := cp as int;
    var inp := T.InputAt(str, cp);
    // unfold FNulledPlus's Some branch
    assert AReg.get_cp(rg.2, qid) == Some(cpi);
    assert AI.opt_int(AReg.get_clock(rg.2, qid)) == K;
    var code := AI.get_code_v(plus_bcv, qid);
    assert (qid as nat) in PIV.QuantIds(r) && PIV.QidBody(r, qid as nat) == r1;
    assert code == CP.compile_reconstruct_nulled(r1);
    var ctx := AI.cp_context(cpi, str, RA.Forward);
    var subcdn := LCdn.compile_cdns(r1);
    var subtable := LCdn.build_cdn_v(subcdn, cpi, ov, ctx, RA.Forward);
    var inits := AI.FInitState(code, cpi, rg.0, rg.1, rg.2, K, ctx).(cdn := subtable);
    var (result, sF, ov1) := AI.FNullInterp(code, inits, ov, RA.Forward);
    NRR.CpOfInputAt(str, cp);
    assert inits == AI.FInitState(code, TR.CpOf(inp) as int, rg.0, rg.1, rg.2, K, TR.CtxOf(inp)).(cdn := inits.cdn);
    NRC.NullInterpNulled(qm, r1, inp, inits, ov, rg.0, rg.1, rg.2, K);
    NRR.CapUniqueChild(r);
    NUL.TransCINullable(r1);
    NRR.CINullablePath(qm, r1, inp);
    NRR.NulledWritesIffPath(qm, r1, inp);
    assert result.Some? && ov1 == ov;
    var w1 := NRC.NulledWrites(qm, r1, inp).value;
    var clks: seq<int> :| |clks| == |w1| && NRC.Incr(clks) && NRC.ClksIn(clks, K, sF.clock)
                          && NRC.RegsOf(result.value) == NRC.ApplyWrites(w1, cpi, clks, rg);
    var rgW := NRC.ApplyWrites(w1, cpi, clks, rg);
    var (rg2, ov2) := PlusAt(qm, r, rg, plus_bcv, str, ov);
    assert rg2 == NRR.FC(r1, subtable, cpi, rgW, plus_bcv, str, ov) && ov2 == NRR.FCov(r1, subtable, cpi, rgW, plus_bcv, str, ov);
    NRR.PlusTableOkChildren(r, plus_bcv);
    assert NRR.ReadoutCtx(qm, r1, plus_bcv, ov, str, cp);
    assert PIV.CapIds(r1) <= PIV.CapIds(r) && PIV.QuantIds(r1) <= PIV.QuantIds(r) && NRR.LookIds(r1) <= NRR.LookIds(r);
    assert NRR.Covers(r1, rg);
    assert NRR.RegsCtx(r1, rg, K);
    NRR.EngineReadout(qm, r1, subtable, cp, rg, K, clks, plus_bcv, str, ov);
    NRR.QuantRegsOfOwn(r);
    assert AI.get_idx(rg2.2.a_clk, qid) == K;
  }

  // ===========================================================================
  // 4. THE READOUT THEOREM.
  // ===========================================================================


  /** THE hypotheses of the readout theorem on a thread's registers. */
  ghost predicate StampsCtx(re: R.regex, qm: AR.QMap, str: string, rg: Regs3) {
    // every set stamp is a CIN-greedy plus, positioned inside the string, with a
    // fresh-chain stamp having stale insides and present capture ancestors
    forall q: nat :: q in PIV.QuantIds(re) && AI.get_idx(rg.2.a_cp, q) >= 0 ==>
      NRR.QidCinPlus(re, q)
      && 0 <= AI.get_idx(rg.2.a_cp, q) <= |str|
      && (q as int) in qm.bodies && qm.bodies[q as int] == PIV.QidBody(re, q)
      && (PIV.QChainFresh(re, rg.2.a_clk, -1, q) ==>
            PIV.PathPresentQ(re, rg.0.a_clk, rg.2.a_clk, -1, q)
            && NRR.RegsStale(PIV.QidBody(re, q), rg, AI.get_idx(rg.2.a_clk, q)))
  }

  // The theorem itself is proved by a generalised induction over subterms in
  // present mode (threshold `mx`); see `ReconReadoutSub` (TODO next session).

  // ===========================================================================
  // 5. THE READOUT THEOREM: `GmOfLive` after `FNulledPlus` is `GmOfLiveR` before.
  // ===========================================================================

  /** `FNulledPlus` as a triple, and its oracle view. */
  ghost function FP(r: R.regex, rg: Regs3, plus_bcv: seq<RB.code>, str: string, ov: LOr.OracleView): Regs3 {
    var (c, l, q, _) := AI.FNulledPlus(r, rg.0, rg.1, rg.2, plus_bcv, str, ov, RA.Forward);
    (c, l, q)
  }
  ghost function FPov(r: R.regex, rg: Regs3, plus_bcv: seq<RB.code>, str: string, ov: LOr.OracleView): LOr.OracleView {
    AI.FNulledPlus(r, rg.0, rg.1, rg.2, plus_bcv, str, ov, RA.Forward).3
  }

  /** The map `filter_capture` at `mx` reads off `r`'s groups from `rg`. */
  ghost function GmSub(r: R.regex, rg: Regs3, mx: int): LG.GroupMap {
    var f := NRR.Filt(r, rg, mx);
    map c: nat | c in PIV.CapIds(r) && AI.get_idx(f, CP.start_reg(c)) >= 0 :: PIV.LiveRange(f, rg.0.a_clk, c)
  }

  /** Every set stamp of `r` sits inside the string. */
  ghost predicate StampsInRange(r: R.regex, rg: Regs3, str: string) {
    forall q: nat :: q in PIV.QuantIds(r) && AI.get_idx(rg.2.a_cp, q) >= 0 ==> AI.get_idx(rg.2.a_cp, q) <= |str|
  }

  /** The frame of `FNulledPlus`: only registers strictly inside quantifier
      bodies of `r` move; the oracle view is kept. */
  lemma FNulledPlusFrame(qm: AR.QMap, r: R.regex, rg: Regs3, plus_bcv: seq<RB.code>, str: string, ov: LOr.OracleView)
    requires PIV.CapUnique(r) && PIV.QuantUnique(r) && NRC.NoCdnPlusRE(r) && NRR.PlusTableOk(r, plus_bcv)
    requires NRR.WfRegs(rg) && NRR.CapValWf(rg) && ov == qm.ov && StampsInRange(r, rg, str)
    ensures FPov(r, rg, plus_bcv, str, ov) == ov
    ensures var rg2 := FP(r, rg, plus_bcv, str, ov);
            NRR.WfRegs(rg2) && NRR.Sized3(rg2, rg) && NRR.CapValWf(rg2)
            && NRR.AgreeOutside(rg2, rg, NRR.InnerCapRegs(r), NRR.InnerLookRegs(r), NRR.InnerQuantRegs(r))
    decreases r
  {
    var rg2 := FP(r, rg, plus_bcv, str, ov);
    match r
    case Re_empty =>
    case Re_character(_) =>
    case Re_anchor(_) =>
    case Re_lookaround(_, _, _) =>
    case Re_capture(_, r1) =>
      NRR.PlusTableOkChildren(r, plus_bcv);
      FNulledPlusFrame(qm, r1, rg, plus_bcv, str, ov);
    case Re_alt(r1, r2) =>
      NRR.PlusTableOkChildren(r, plus_bcv);
      FNulledPlusFrame(qm, r1, rg, plus_bcv, str, ov);
      var rgA := FP(r1, rg, plus_bcv, str, ov);
      assert StampsInRange(r2, rgA, str) by {
        NRR.DisjointRegs(r); NRR.InnerSub(r1);
        StampsInRangeTransfer(r, r2, rg, rgA, str);
      }
      FNulledPlusFrame(qm, r2, rgA, plus_bcv, str, ov);
      assert rg2 == FP(r2, rgA, plus_bcv, str, ov);
      NRR.AgreeOutsideWeaken(rg2, rgA, NRR.InnerCapRegs(r2), NRR.InnerLookRegs(r2), NRR.InnerQuantRegs(r2), NRR.InnerCapRegs(r), NRR.InnerLookRegs(r), NRR.InnerQuantRegs(r));
      NRR.AgreeOutsideWeaken(rgA, rg, NRR.InnerCapRegs(r1), NRR.InnerLookRegs(r1), NRR.InnerQuantRegs(r1), NRR.InnerCapRegs(r), NRR.InnerLookRegs(r), NRR.InnerQuantRegs(r));
      NRR.AgreeOutsideTrans(rg2, rgA, rg, NRR.InnerCapRegs(r), NRR.InnerLookRegs(r), NRR.InnerQuantRegs(r));
    case Re_con(r1, r2) =>
      NRR.PlusTableOkChildren(r, plus_bcv);
      FNulledPlusFrame(qm, r1, rg, plus_bcv, str, ov);
      var rgA := FP(r1, rg, plus_bcv, str, ov);
      assert StampsInRange(r2, rgA, str) by {
        NRR.DisjointRegs(r); NRR.InnerSub(r1);
        StampsInRangeTransfer(r, r2, rg, rgA, str);
      }
      FNulledPlusFrame(qm, r2, rgA, plus_bcv, str, ov);
      assert rg2 == FP(r2, rgA, plus_bcv, str, ov);
      NRR.AgreeOutsideWeaken(rg2, rgA, NRR.InnerCapRegs(r2), NRR.InnerLookRegs(r2), NRR.InnerQuantRegs(r2), NRR.InnerCapRegs(r), NRR.InnerLookRegs(r), NRR.InnerQuantRegs(r));
      NRR.AgreeOutsideWeaken(rgA, rg, NRR.InnerCapRegs(r1), NRR.InnerLookRegs(r1), NRR.InnerQuantRegs(r1), NRR.InnerCapRegs(r), NRR.InnerLookRegs(r), NRR.InnerQuantRegs(r));
      NRR.AgreeOutsideTrans(rg2, rgA, rg, NRR.InnerCapRegs(r), NRR.InnerLookRegs(r), NRR.InnerQuantRegs(r));
    case Re_quant(nul, qid, q, body) =>
      NRR.PlusTableOkChildren(r, plus_bcv);
      NRR.InnerSub(body);
      match AReg.get_cp(rg.2, qid) {
        case None =>
          FNulledPlusFrame(qm, body, rg, plus_bcv, str, ov);
          NRR.AgreeOutsideWeaken(rg2, rg, NRR.InnerCapRegs(body), NRR.InnerLookRegs(body), NRR.InnerQuantRegs(body), NRR.CapRegsOf(body), NRR.LookRegsOf(body), NRR.QuantRegsOf(body));
        case Some(start_cp) =>
          assert qid >= 0 && (qid as nat) in PIV.QuantIds(r) && 0 <= start_cp <= |str|;
          var start_clock := AI.opt_int(AReg.get_clock(rg.2, qid));
          assert start_clock >= -1;
          var code := AI.get_code_v(plus_bcv, qid);
          var ctx := AI.cp_context(start_cp, str, RA.Forward);
          var subcdn := LCdn.compile_cdns(body);
          var subtable := LCdn.build_cdn_v(subcdn, start_cp, ov, ctx, RA.Forward);
          var (rgR, ovR) := NRR.ReconAt(code, body, subtable, start_cp, rg, start_clock, plus_bcv, str, ov);
          assert rg2 == rgR && FPov(r, rg, plus_bcv, str, ov) == ovR;
          NRR.ReconAtFrame(qm, r, body, qid, code, subtable, start_cp as nat, rg, start_clock, plus_bcv, str, ov);
      }
  }

  /** `FNulledPlus` keeps look-body captures absent. */
  lemma FNulledPlusLookCapsAbsent(qm: AR.QMap, r: R.regex, rg: Regs3, plus_bcv: seq<RB.code>, str: string, ov: LOr.OracleView)
    requires PIV.CapUnique(r) && PIV.QuantUnique(r) && NRC.NoCdnPlusRE(r) && NRR.PlusTableOk(r, plus_bcv)
    requires NRR.WfRegs(rg) && NRR.CapValWf(rg) && ov == qm.ov && StampsInRange(r, rg, str)
    requires NRR.LookCapsAbsent(r, rg)
    ensures NRR.LookCapsAbsent(r, FP(r, rg, plus_bcv, str, ov))
    decreases r
  {
    var rg2 := FP(r, rg, plus_bcv, str, ov);
    FNulledPlusFrame(qm, r, rg, plus_bcv, str, ov);
    match r
    case Re_empty =>
    case Re_character(_) =>
    case Re_anchor(_) =>
    case Re_lookaround(_, _, _) =>
    case Re_capture(_, r1) =>
      NRR.PlusTableOkChildren(r, plus_bcv);
      FNulledPlusLookCapsAbsent(qm, r1, rg, plus_bcv, str, ov);
    case Re_alt(r1, r2) =>
      NRR.PlusTableOkChildren(r, plus_bcv);
      FNulledPlusLookCapsAbsent(qm, r1, rg, plus_bcv, str, ov);
      var rgA := FP(r1, rg, plus_bcv, str, ov);
      FNulledPlusFrame(qm, r1, rg, plus_bcv, str, ov);
      NRR.SubAgree2(r, rg, rgA);
      NRR.CapIdsInLooksSub(r2); NRR.CapRegsOfChar(r2);
      assert NRR.LookCapsAbsent(r2, rgA) by {
        forall c: nat | c in PIV.CapIdsInLooks(r2) ensures AI.get_idx(rgA.0.a_cp, CP.start_reg(c)) < 0 { assert CP.start_reg(c) in NRR.CapRegsOf(r2); }
      }
      assert StampsInRange(r2, rgA, str) by { NRR.DisjointRegs(r); NRR.InnerSub(r1); StampsInRangeTransfer(r, r2, rg, rgA, str); }
      FNulledPlusLookCapsAbsent(qm, r2, rgA, plus_bcv, str, ov);
      FNulledPlusFrame(qm, r2, rgA, plus_bcv, str, ov);
      assert rg2 == FP(r2, rgA, plus_bcv, str, ov);
      NRR.SubAgree(r, rgA, rg2);
      NRR.CapIdsInLooksSub(r1); NRR.CapRegsOfChar(r1);
      forall c: nat | c in PIV.CapIdsInLooks(r) ensures AI.get_idx(rg2.0.a_cp, CP.start_reg(c)) < 0 {
        if c in PIV.CapIdsInLooks(r1) { assert CP.start_reg(c) in NRR.CapRegsOf(r1); }
      }
    case Re_con(r1, r2) =>
      NRR.PlusTableOkChildren(r, plus_bcv);
      FNulledPlusLookCapsAbsent(qm, r1, rg, plus_bcv, str, ov);
      var rgA := FP(r1, rg, plus_bcv, str, ov);
      FNulledPlusFrame(qm, r1, rg, plus_bcv, str, ov);
      NRR.SubAgree2(r, rg, rgA);
      NRR.CapIdsInLooksSub(r2); NRR.CapRegsOfChar(r2);
      assert NRR.LookCapsAbsent(r2, rgA) by {
        forall c: nat | c in PIV.CapIdsInLooks(r2) ensures AI.get_idx(rgA.0.a_cp, CP.start_reg(c)) < 0 { assert CP.start_reg(c) in NRR.CapRegsOf(r2); }
      }
      assert StampsInRange(r2, rgA, str) by { NRR.DisjointRegs(r); NRR.InnerSub(r1); StampsInRangeTransfer(r, r2, rg, rgA, str); }
      FNulledPlusLookCapsAbsent(qm, r2, rgA, plus_bcv, str, ov);
      FNulledPlusFrame(qm, r2, rgA, plus_bcv, str, ov);
      assert rg2 == FP(r2, rgA, plus_bcv, str, ov);
      NRR.SubAgree(r, rgA, rg2);
      NRR.CapIdsInLooksSub(r1); NRR.CapRegsOfChar(r1);
      forall c: nat | c in PIV.CapIdsInLooks(r) ensures AI.get_idx(rg2.0.a_cp, CP.start_reg(c)) < 0 {
        if c in PIV.CapIdsInLooks(r1) { assert CP.start_reg(c) in NRR.CapRegsOf(r1); }
      }
    case Re_quant(nul, qid, q, body) =>
      NRR.PlusTableOkChildren(r, plus_bcv);
      match AReg.get_cp(rg.2, qid) {
        case None => FNulledPlusLookCapsAbsent(qm, body, rg, plus_bcv, str, ov);
        case Some(start_cp) =>
          assert qid >= 0 && (qid as nat) in PIV.QuantIds(r) && 0 <= start_cp <= |str|;
          var start_clock := AI.opt_int(AReg.get_clock(rg.2, qid));
          var code := AI.get_code_v(plus_bcv, qid);
          var ctx := AI.cp_context(start_cp, str, RA.Forward);
          var subtable := LCdn.build_cdn_v(LCdn.compile_cdns(body), start_cp, ov, ctx, RA.Forward);
          assert rg2 == NRR.ReconAt(code, body, subtable, start_cp, rg, start_clock, plus_bcv, str, ov).0;
          NRR.ReconAtLookCapsAbsent(qm, r, body, qid, code, subtable, start_cp as nat, rg, start_clock, plus_bcv, str, ov);
      }
  }

  lemma StampsInRangeTransfer(r: R.regex, sub: R.regex, rg: Regs3, rg': Regs3, str: string)
    requires (r.Re_alt? || r.Re_con?) && (sub == NRR.L1(r) || sub == NRR.L2(r)) && PIV.QuantUnique(r)
    requires StampsInRange(r, rg, str)
    requires forall k: int :: k in NRR.QuantRegsOf(sub) ==> AI.get_idx(rg'.2.a_cp, k) == AI.get_idx(rg.2.a_cp, k)
    ensures StampsInRange(sub, rg', str)
  {
    NRR.QuantRegsOfChar(sub);
  }

  // ---- map algebra of `LiveStampsGm` and `GmSub` ----

  ghost function Restrict(gm: LG.GroupMap, S: set<nat>): LG.GroupMap {
    map g: nat | g in gm && g in S :: gm[g]
  }

  /** The QMap's bodies are the regex's own, for every SET stamp. */
  ghost predicate BodiesMatch(qm: AR.QMap, r: R.regex, qcp: seq<int>) {
    forall q: nat :: q in PIV.QuantIds(r) && AI.get_idx(qcp, q) >= 0 && (q as int) in qm.bodies ==> qm.bodies[q as int] == PIV.QidBody(r, q)
  }

  lemma BodiesMatchChild(qm: AR.QMap, r: R.regex, qcp: seq<int>)
    requires PIV.QuantUnique(r) && BodiesMatch(qm, r, qcp)
    ensures r.Re_alt? || r.Re_con? ==> BodiesMatch(qm, NRR.L1(r), qcp) && BodiesMatch(qm, NRR.L2(r), qcp)
    ensures r.Re_quant? || r.Re_capture? || r.Re_lookaround? ==> BodiesMatch(qm, NRR.L1(r), qcp)
  {
    match r
    case Re_alt(r1, r2) =>
      forall q: nat | q in PIV.QuantIds(r1) && AI.get_idx(qcp, q) >= 0 && (q as int) in qm.bodies ensures qm.bodies[q as int] == PIV.QidBody(r1, q) { assert q in PIV.QuantIds(r); }
      forall q: nat | q in PIV.QuantIds(r2) && AI.get_idx(qcp, q) >= 0 && (q as int) in qm.bodies ensures qm.bodies[q as int] == PIV.QidBody(r2, q) { QuantSideDisjoint(r, q); assert q in PIV.QuantIds(r); }
    case Re_con(r1, r2) =>
      forall q: nat | q in PIV.QuantIds(r1) && AI.get_idx(qcp, q) >= 0 && (q as int) in qm.bodies ensures qm.bodies[q as int] == PIV.QidBody(r1, q) { assert q in PIV.QuantIds(r); }
      forall q: nat | q in PIV.QuantIds(r2) && AI.get_idx(qcp, q) >= 0 && (q as int) in qm.bodies ensures qm.bodies[q as int] == PIV.QidBody(r2, q) { QuantSideDisjoint(r, q); assert q in PIV.QuantIds(r); }
    case Re_quant(_, qid, _, r1) =>
      forall q: nat | q in PIV.QuantIds(r1) && AI.get_idx(qcp, q) >= 0 && (q as int) in qm.bodies ensures qm.bodies[q as int] == PIV.QidBody(r1, q) { assert q in PIV.QuantIds(r) && q != qid as nat; }
    case Re_capture(_, r1) =>
      forall q: nat | q in PIV.QuantIds(r1) && AI.get_idx(qcp, q) >= 0 && (q as int) in qm.bodies ensures qm.bodies[q as int] == PIV.QidBody(r1, q) { assert q in PIV.QuantIds(r); }
    case Re_lookaround(_, _, r1) =>
      forall q: nat | q in PIV.QuantIds(r1) && AI.get_idx(qcp, q) >= 0 && (q as int) in qm.bodies ensures qm.bodies[q as int] == PIV.QidBody(r1, q) { assert q in PIV.QuantIds(r); }
    case _ =>
  }

  /** `LiveStampsGm` only rewrites `r`'s groups, and reads only them. */
  lemma LiveStampsGmFrame(r: R.regex, qm: AR.QMap, str: string, qc: seq<int>, qcp: seq<int>, mx: int, gm: LG.GroupMap, gm': LG.GroupMap)
    requires T.TransWf(r) && PIV.CapUnique(r) && PIV.QuantUnique(r) && BodiesMatch(qm, r, qcp)
    requires forall g: nat :: g in PIV.CapIds(r) ==> ((g in gm <==> g in gm') && (g in gm ==> gm[g] == gm'[g]))
    ensures var a := PIV.LiveStampsGm(r, qm, str, qc, qcp, mx, gm);
            var b := PIV.LiveStampsGm(r, qm, str, qc, qcp, mx, gm');
            (forall g: nat :: g in PIV.CapIds(r) ==> ((g in a <==> g in b) && (g in a ==> a[g] == b[g])))
            && (forall g: nat :: g !in PIV.CapIds(r) ==> ((g in a <==> g in gm) && (g in a ==> a[g] == gm[g])))
    decreases r
  {
    match r
    case Re_empty =>
    case Re_character(_) =>
    case Re_anchor(_) =>
    case Re_lookaround(_, _, _) =>
    case Re_capture(_, r1) => BodiesMatchChild(qm, r, qcp); LiveStampsGmFrame(r1, qm, str, qc, qcp, mx, gm, gm');
    case Re_alt(r1, r2) =>
      BodiesMatchChild(qm, r, qcp);
      LiveStampsGmFrame(r1, qm, str, qc, qcp, mx, gm, gm');
      var a1 := PIV.LiveStampsGm(r1, qm, str, qc, qcp, mx, gm);
      var b1 := PIV.LiveStampsGm(r1, qm, str, qc, qcp, mx, gm');
      LiveStampsGmFrame(r2, qm, str, qc, qcp, mx, a1, b1);
    case Re_con(r1, r2) =>
      BodiesMatchChild(qm, r, qcp);
      LiveStampsGmFrame(r1, qm, str, qc, qcp, mx, gm, gm');
      var a1 := PIV.LiveStampsGm(r1, qm, str, qc, qcp, mx, gm);
      var b1 := PIV.LiveStampsGm(r1, qm, str, qc, qcp, mx, gm');
      LiveStampsGmFrame(r2, qm, str, qc, qcp, mx, a1, b1);
    case Re_quant(nul, qid, q, r1) =>
      BodiesMatchChild(qm, r, qcp);
      var qv := AI.get_idx(qc, qid);
      if qv < mx {
      } else if qid >= 0 && AI.get_idx(qcp, qid) >= 0 {
        if PIV.StampReady(qm, str, qid as nat, qcp) {
          assert (qid as nat) in PIV.QuantIds(r) && PIV.QidBody(r, qid as nat) == r1;
          assert qm.bodies[qid as int] == r1;
          var cp := PIV.StampCp(qcp, qid as nat);
          var p := TR.FirstEmptyPathR(qm, r1, T.InputAt(str, cp));
          if p.Some? {
            var gl := L.DefGroups(T.Translate(r1));
            PIV.DefGroupsCapIds(r1);
            StampApplyPointwise(qm, str, qid as nat, qcp, r1, gm, gm');
          }
        }
      } else {
        LiveStampsGmFrame(r1, qm, str, qc, qcp, qv, gm, gm');
      }
  }

  /** `ApplyPath(p, cp, GMReset(gl, ·))` reads nothing inside `gl` and writes only inside `gl`. */
  lemma StampApplyPointwise(qm: AR.QMap, str: string, qid: nat, qcp: seq<int>, r1: R.regex, gm: LG.GroupMap, gm': LG.GroupMap)
    requires T.TransWf(r1) && PIV.StampReady(qm, str, qid, qcp) && qm.bodies[qid as int] == r1
    requires TR.FirstEmptyPathR(qm, r1, T.InputAt(str, PIV.StampCp(qcp, qid))).Some?
    ensures var a := PIV.StampApply(qm, str, qid, qcp, r1, gm);
            var b := PIV.StampApply(qm, str, qid, qcp, r1, gm');
            var gl := L.DefGroups(T.Translate(r1));
            (forall g: nat :: g in gl ==> ((g in a <==> g in b) && (g in a ==> a[g] == b[g])))
            && (forall g: nat :: g !in gl ==> ((g in a <==> g in gm) && (g in a ==> a[g] == gm[g])))
  {
    var cp := PIV.StampCp(qcp, qid);
    var inp := T.InputAt(str, cp);
    var body := qm.bodies[qid as int];
    var p := TR.FirstEmptyPathR(qm, body, inp).value;
    var gl := L.DefGroups(T.Translate(r1));
    var G := set g: nat | g in gl;
    PIV.DefGroupsCapIds(r1);
    PathInDefGroups(qm, body, inp, r1, gl);
    NP.ApplyPathOutside(p, cp, LG.GMReset(gl, gm), G);
    NP.ApplyPathOutside(p, cp, LG.GMReset(gl, gm'), G);
    // inside gl: both folds start from maps with nothing in gl
    ApplyPathInsideIndep(p, cp, LG.GMReset(gl, gm), LG.GMReset(gl, gm'), G);
  }

  /** The stamp's path lives inside the body's groups (`qm.bodies[qid]` IS the body). */
  lemma PathInDefGroups(qm: AR.QMap, body: R.regex, inp: LC.Input, r1: R.regex, gl: LG.GroupSet)
    requires T.TransWf(body) && T.TransWf(r1) && TR.FirstEmptyPathR(qm, body, inp).Some?
    requires gl == L.DefGroups(T.Translate(r1))
    requires forall g: nat :: g in PIV.CapIds(body) ==> g in gl
    ensures NP.PathIn(TR.FirstEmptyPathR(qm, body, inp).value, set g: nat | g in gl)
  {
    PathInCapIds(qm, body, inp);
    var p := TR.FirstEmptyPathR(qm, body, inp).value;
    forall i | 0 <= i < |p| ensures CE.GmActionIn(p[i], set g: nat | g in gl) {
      assert CE.GmActionIn(p[i], PIV.CapIds(body));
    }
  }

  lemma PathInCapIds(qm: AR.QMap, re: R.regex, inp: LC.Input)
    requires T.TransWf(re) && TR.FirstEmptyPathR(qm, re, inp).Some?
    ensures NP.PathIn(TR.FirstEmptyPathR(qm, re, inp).value, PIV.CapIds(re))
    decreases re
  {
    var p := TR.FirstEmptyPathR(qm, re, inp).value;
    match re
    case Re_empty =>
    case Re_character(_) =>
    case Re_anchor(_) =>
    case Re_lookaround(_, _, _) =>
    case Re_alt(r1, r2) =>
      if TR.FirstEmptyPathR(qm, r1, inp).Some? { PathInCapIds(qm, r1, inp); PathInWeaken(p, PIV.CapIds(r1), PIV.CapIds(re)); }
      else { PathInCapIds(qm, r2, inp); PathInWeaken(p, PIV.CapIds(r2), PIV.CapIds(re)); }
    case Re_con(r1, r2) =>
      PathInCapIds(qm, r1, inp); PathInCapIds(qm, r2, inp);
      var p1 := TR.FirstEmptyPathR(qm, r1, inp).value;
      var p2 := TR.FirstEmptyPathR(qm, r2, inp).value;
      PathInWeaken(p1, PIV.CapIds(r1), PIV.CapIds(re));
      PathInWeaken(p2, PIV.CapIds(r2), PIV.CapIds(re));
      PathInApp(p1, p2, PIV.CapIds(re));
    case Re_capture(cid, r1) =>
      PathInCapIds(qm, r1, inp);
      var p1 := TR.FirstEmptyPathR(qm, r1, inp).value;
      PathInWeaken(p1, PIV.CapIds(r1), PIV.CapIds(re));
      assert cid >= 0 ==> (cid as nat) in PIV.CapIds(re);
      PathInApp([LG.Open(cid as nat)], p1, PIV.CapIds(re));
      PathInApp([LG.Open(cid as nat)] + p1, [LG.Close(cid as nat)], PIV.CapIds(re));
    case Re_quant(nul, qid, q, r1) =>
      if q.min == 0 {
      } else {
        PathInCapIds(qm, r1, inp);
        var p1 := TR.FirstEmptyPathR(qm, r1, inp).value;
        var gl := L.DefGroups(T.Translate(r1));
        PIV.DefGroupsCapIds(r1);
        PathInWeaken(p1, PIV.CapIds(r1), PIV.CapIds(re));
        assert CE.GmActionIn(LG.Reset(gl), PIV.CapIds(re));
        PathInApp([LG.Reset(gl)], p1, PIV.CapIds(re));
        PathInRepeat(q.min as nat, [LG.Reset(gl)] + p1, PIV.CapIds(re));
      }
  }

  lemma PathInWeaken(p: seq<LG.GroupAction>, S: set<nat>, S': set<nat>)
    requires NP.PathIn(p, S) && S <= S'
    ensures NP.PathIn(p, S')
  {}

  lemma PathInApp(a: seq<LG.GroupAction>, b: seq<LG.GroupAction>, S: set<nat>)
    requires NP.PathIn(a, S) && NP.PathIn(b, S)
    ensures NP.PathIn(a + b, S)
  {
    forall i | 0 <= i < |a + b| ensures CE.GmActionIn((a + b)[i], S) {
      if i < |a| { assert (a + b)[i] == a[i]; } else { assert (a + b)[i] == b[i - |a|]; }
    }
  }

  lemma PathInRepeat(n: nat, p: seq<LG.GroupAction>, S: set<nat>)
    requires NP.PathIn(p, S)
    ensures NP.PathIn(TR.RepeatPath(n, p), S)
    decreases n
  {
    if n > 0 { PathInRepeat(n - 1, p, S); PathInApp(p, TR.RepeatPath(n - 1, p), S); }
  }

  /** Two folds of the same path from maps with NOTHING in `G` agree on `G`. */
  lemma ApplyPathInsideIndep(p: seq<LG.GroupAction>, cp: nat, gm1: LG.GroupMap, gm2: LG.GroupMap, G: set<nat>)
    requires forall g: nat :: g in G ==> ((g in gm1 <==> g in gm2) && (g in gm1 ==> gm1[g] == gm2[g]))
    ensures var a := NP.ApplyPath(p, cp, gm1); var b := NP.ApplyPath(p, cp, gm2);
            forall g: nat :: g in G ==> ((g in a <==> g in b) && (g in a ==> a[g] == b[g]))
    decreases |p|
  {
    if |p| > 0 {
      var h1 := LG.GMUpdate(p[0], cp, gm1);
      var h2 := LG.GMUpdate(p[0], cp, gm2);
      assert forall g: nat :: g in G ==> ((g in h1 <==> g in h2) && (g in h1 ==> h1[g] == h2[g])) by {
        match p[0]
        case Open(g0) =>
        case Close(g0) =>
        case Reset(gs) =>
      }
      ApplyPathInsideIndep(p[1..], cp, h1, h2, G);
    }
  }

  /** `GmSub` reads only `r`'s registers. */
  lemma GmSubDep(r: R.regex, a: Regs3, b: Regs3, mx: int)
    requires PIV.CapUnique(r) && PIV.QuantUnique(r)
    requires forall k: int :: k in NRR.CapRegsOf(r) ==> AI.get_idx(b.0.a_cp, k) == AI.get_idx(a.0.a_cp, k) && AI.get_idx(b.0.a_clk, k) == AI.get_idx(a.0.a_clk, k)
    requires forall k: int :: k in NRR.QuantRegsOf(r) ==> AI.get_idx(b.2.a_clk, k) == AI.get_idx(a.2.a_clk, k)
    requires NRR.LookCapsAbsent(r, a)
    ensures GmSub(r, a, mx) == GmSub(r, b, mx)
  {
    NRR.CapRegsOfChar(r);
    NRR.QuantRegsOfChar(r);
    assert forall c: nat :: c in PIV.CapIds(r) ==> CP.start_reg(c) in NRR.CapRegsOf(r) && CP.end_reg(c) in NRR.CapRegsOf(r);
    assert forall q: nat :: q in PIV.QuantIds(r) ==> (q as int) in NRR.QuantRegsOf(r);
    var fa := NRR.Filt(r, a, mx);
    var fb := NRR.Filt(r, b, mx);
    NRR.CapIdsInLooksSub(r);
    forall c: nat | c in PIV.CapIds(r)
      ensures (AI.get_idx(fa, CP.start_reg(c)) >= 0 <==> AI.get_idx(fb, CP.start_reg(c)) >= 0)
              && (AI.get_idx(fa, CP.start_reg(c)) >= 0 ==> AI.get_idx(fa, CP.start_reg(c)) == AI.get_idx(fb, CP.start_reg(c)))
              && AI.get_idx(fa, CP.end_reg(c)) == AI.get_idx(fb, CP.end_reg(c))
    {
      if c in PIV.CapIdsInLooks(r) {
        assert AI.get_idx(a.0.a_cp, CP.start_reg(c)) < 0 && AI.get_idx(b.0.a_cp, CP.start_reg(c)) < 0;
        PIV.FilterCaptureNeg(r, a.0.a_cp, a.0.a_clk, a.1.a_clk, a.2.a_clk, mx, CP.start_reg(c));
        PIV.FilterCaptureNeg(r, b.0.a_cp, b.0.a_clk, b.1.a_clk, b.2.a_clk, mx, CP.start_reg(c));
      } else {
        NRR.FilterAtStartDep(r, a.0.a_cp, b.0.a_cp, a.0.a_clk, b.0.a_clk, a.1.a_clk, b.1.a_clk, a.2.a_clk, b.2.a_clk, mx, c);
      }
      PIV.FilterCaptureKeepsOdd(r, a.0.a_cp, a.0.a_clk, a.1.a_clk, a.2.a_clk, mx, CP.end_reg(c));
      PIV.FilterCaptureKeepsOdd(r, b.0.a_cp, b.0.a_clk, b.1.a_clk, b.2.a_clk, mx, CP.end_reg(c));
    }
    forall c: nat ensures (c in GmSub(r, a, mx) <==> c in GmSub(r, b, mx)) && (c in GmSub(r, a, mx) ==> GmSub(r, a, mx)[c] == GmSub(r, b, mx)[c]) {
      if c in PIV.CapIds(r) && AI.get_idx(fa, CP.start_reg(c)) >= 0 {
        assert PIV.LiveRange(fa, a.0.a_clk, c) == PIV.LiveRange(fb, b.0.a_clk, c);
      }
    }
  }

  /** `GmSub` of an alt/con is the union of the sides' (disjoint ids). */
  lemma GmSubSplit(r: R.regex, rg: Regs3, mx: int)
    requires (r.Re_alt? || r.Re_con?) && PIV.CapUnique(r) && NRR.LookCapsAbsent(r, rg)
    ensures GmSub(r, rg, mx) == GmSub(NRR.L1(r), rg, mx) + GmSub(NRR.L2(r), rg, mx)
  {
    var r1 := NRR.L1(r); var r2 := NRR.L2(r);
    assert PIV.CapIds(r1) * PIV.CapIds(r2) == {};
    var cr := rg.0.a_cp; var cc := rg.0.a_clk; var lc := rg.1.a_clk; var qc := rg.2.a_clk;
    var f1 := AI.filter_capture(r1, cr, cc, lc, qc, mx);
    var f := NRR.Filt(r, rg, mx);
    assert f == AI.filter_capture(r2, f1, cc, lc, qc, mx);
    var f2 := AI.filter_capture(r2, cr, cc, lc, qc, mx);
    forall c: nat | c in PIV.CapIds(r) ensures
        (c in PIV.CapIds(r1) ==> AI.get_idx(f, CP.start_reg(c)) == AI.get_idx(f1, CP.start_reg(c)))
        && (c in PIV.CapIds(r2) ==> AI.get_idx(f, CP.start_reg(c)) == AI.get_idx(f2, CP.start_reg(c)))
        && AI.get_idx(f, CP.end_reg(c)) == AI.get_idx(cr, CP.end_reg(c))
        && AI.get_idx(f1, CP.end_reg(c)) == AI.get_idx(cr, CP.end_reg(c))
        && AI.get_idx(f2, CP.end_reg(c)) == AI.get_idx(cr, CP.end_reg(c))
    {
      var j := CP.start_reg(c);
      if c in PIV.CapIds(r1) {
        CapSideDisjoint(r, c);
        assert forall c': nat :: c' in PIV.CapIds(r2) ==> c' != c && CP.start_reg(c') != j;
        NRR.FilterKeepsNonStart(r2, f1, cc, lc, qc, mx, j);
      } else {
        assert c in PIV.CapIds(r2);
        assert forall c': nat :: c' in PIV.CapIds(r1) ==> c' != c && CP.start_reg(c') != j by {
          forall c': nat | c' in PIV.CapIds(r1) ensures c' != c { CapSideDisjoint(r, c'); }
        }
        NRR.FilterKeepsNonStart(r1, cr, cc, lc, qc, mx, j);
        NRR.FilterCrPointwise(r2, f1, cr, cc, lc, qc, mx, j);
      }
      PIV.FilterCaptureKeepsOdd(r, cr, cc, lc, qc, mx, CP.end_reg(c));
      PIV.FilterCaptureKeepsOdd(r1, cr, cc, lc, qc, mx, CP.end_reg(c));
      PIV.FilterCaptureKeepsOdd(r2, cr, cc, lc, qc, mx, CP.end_reg(c));
    }
  }

  // ---- the local invariant on a subterm, and the theorem ----

  /** The per-stamp facts the readout needs, relative to a subterm reached at threshold `mx`. */
  ghost predicate StampsLocal(qm: AR.QMap, r: R.regex, str: string, rg: Regs3, mx: int) {
    forall q: nat :: q in PIV.QuantIds(r) && AI.get_idx(rg.2.a_cp, q) >= 0 ==>
      NRR.QidCinPlus(r, q)
      && 0 <= AI.get_idx(rg.2.a_cp, q) <= |str|
      && (q as int) in qm.bodies && qm.bodies[q as int] == PIV.QidBody(r, q)
      && (PIV.QChainFresh(r, rg.2.a_clk, mx, q) ==>
            PIV.PathPresentQ(r, rg.0.a_clk, rg.2.a_clk, mx, q)
            && NRR.RegsStale(PIV.QidBody(r, q), rg, AI.get_idx(rg.2.a_clk, q)))
  }

  lemma StampsLocalChild(qm: AR.QMap, r: R.regex, str: string, rg: Regs3, mx: int)
    requires PIV.QuantUnique(r) && StampsLocal(qm, r, str, rg, mx)
    ensures r.Re_alt? || r.Re_con? ==> StampsLocal(qm, NRR.L1(r), str, rg, mx) && StampsLocal(qm, NRR.L2(r), str, rg, mx)
    ensures r.Re_capture? ==> StampsLocal(qm, NRR.L1(r), str, rg, mx)
    ensures r.Re_quant? && AI.get_idx(rg.2.a_clk, r.qid) >= mx ==> StampsLocal(qm, NRR.L1(r), str, rg, AI.get_idx(rg.2.a_clk, r.qid))
  {
    match r
    case Re_alt(r1, r2) =>
      forall q: nat | q in PIV.QuantIds(r1) && AI.get_idx(rg.2.a_cp, q) >= 0 ensures
        NRR.QidCinPlus(r1, q) && (q as int) in qm.bodies && qm.bodies[q as int] == PIV.QidBody(r1, q)
        && (PIV.QChainFresh(r1, rg.2.a_clk, mx, q) ==> PIV.PathPresentQ(r1, rg.0.a_clk, rg.2.a_clk, mx, q) && NRR.RegsStale(PIV.QidBody(r1, q), rg, AI.get_idx(rg.2.a_clk, q)))
      { assert q in PIV.QuantIds(r); }
      forall q: nat | q in PIV.QuantIds(r2) && AI.get_idx(rg.2.a_cp, q) >= 0 ensures
        NRR.QidCinPlus(r2, q) && (q as int) in qm.bodies && qm.bodies[q as int] == PIV.QidBody(r2, q)
        && (PIV.QChainFresh(r2, rg.2.a_clk, mx, q) ==> PIV.PathPresentQ(r2, rg.0.a_clk, rg.2.a_clk, mx, q) && NRR.RegsStale(PIV.QidBody(r2, q), rg, AI.get_idx(rg.2.a_clk, q)))
      { QuantSideDisjoint(r, q); assert q in PIV.QuantIds(r); }
    case Re_con(r1, r2) =>
      forall q: nat | q in PIV.QuantIds(r1) && AI.get_idx(rg.2.a_cp, q) >= 0 ensures
        NRR.QidCinPlus(r1, q) && (q as int) in qm.bodies && qm.bodies[q as int] == PIV.QidBody(r1, q)
        && (PIV.QChainFresh(r1, rg.2.a_clk, mx, q) ==> PIV.PathPresentQ(r1, rg.0.a_clk, rg.2.a_clk, mx, q) && NRR.RegsStale(PIV.QidBody(r1, q), rg, AI.get_idx(rg.2.a_clk, q)))
      { assert q in PIV.QuantIds(r); }
      forall q: nat | q in PIV.QuantIds(r2) && AI.get_idx(rg.2.a_cp, q) >= 0 ensures
        NRR.QidCinPlus(r2, q) && (q as int) in qm.bodies && qm.bodies[q as int] == PIV.QidBody(r2, q)
        && (PIV.QChainFresh(r2, rg.2.a_clk, mx, q) ==> PIV.PathPresentQ(r2, rg.0.a_clk, rg.2.a_clk, mx, q) && NRR.RegsStale(PIV.QidBody(r2, q), rg, AI.get_idx(rg.2.a_clk, q)))
      { QuantSideDisjoint(r, q); assert q in PIV.QuantIds(r); }
    case Re_capture(cid, r1) =>
      forall q: nat | q in PIV.QuantIds(r1) && AI.get_idx(rg.2.a_cp, q) >= 0 ensures
        NRR.QidCinPlus(r1, q) && (q as int) in qm.bodies && qm.bodies[q as int] == PIV.QidBody(r1, q)
        && (PIV.QChainFresh(r1, rg.2.a_clk, mx, q) ==> PIV.PathPresentQ(r1, rg.0.a_clk, rg.2.a_clk, mx, q) && NRR.RegsStale(PIV.QidBody(r1, q), rg, AI.get_idx(rg.2.a_clk, q)))
      { assert q in PIV.QuantIds(r); }
    case Re_quant(nul, qid, qq, r1) =>
      var qv := AI.get_idx(rg.2.a_clk, qid);
      if qv >= mx {
        forall q: nat | q in PIV.QuantIds(r1) && AI.get_idx(rg.2.a_cp, q) >= 0 ensures
          NRR.QidCinPlus(r1, q) && (q as int) in qm.bodies && qm.bodies[q as int] == PIV.QidBody(r1, q)
          && (PIV.QChainFresh(r1, rg.2.a_clk, qv, q) ==> PIV.PathPresentQ(r1, rg.0.a_clk, rg.2.a_clk, qv, q) && NRR.RegsStale(PIV.QidBody(r1, q), rg, AI.get_idx(rg.2.a_clk, q)))
        { assert q in PIV.QuantIds(r) && q != qid as nat; }
      }
    case _ =>
  }

  lemma StampsLocalBodies(qm: AR.QMap, r: R.regex, str: string, rg: Regs3, mx: int)
    requires StampsLocal(qm, r, str, rg, mx)
    ensures forall q: nat :: q in PIV.QuantIds(r) && AI.get_idx(rg.2.a_cp, q) >= 0 ==> (q as int) in qm.bodies && qm.bodies[q as int] == PIV.QidBody(r, q)
  {}

  /** THE INDUCTION: at a subterm reached at threshold `mx`, the groups
      `filter_capture` reads after `FNulledPlus` are the stamped readout of the
      groups it read before. */
  lemma ReconReadoutSub(qm: AR.QMap, r: R.regex, rg: Regs3, plus_bcv: seq<RB.code>, str: string, ov: LOr.OracleView, mx: int)
    requires mx >= -1
    requires T.TransWf(r) && PIV.CapUnique(r) && PIV.QuantUnique(r) && NRR.LookUnique(r) && NRC.NoCdnPlusRE(r) && NRR.PlusTableOk(r, plus_bcv)
    requires ov == qm.ov
    requires NRR.WfRegs(rg) && NRR.CapValWf(rg) && NRR.Covers(r, rg) && NRR.LookCapsAbsent(r, rg)
    requires StampsLocal(qm, r, str, rg, mx)
    ensures StampsInRange(r, rg, str)
    ensures var rg' := FP(r, rg, plus_bcv, str, ov);
            GmSub(r, rg', mx) == PIV.LiveStampsGm(r, qm, str, rg.2.a_clk, rg.2.a_cp, mx, GmSub(r, rg, mx))
    decreases r
  {
    assert StampsInRange(r, rg, str);
    var rg' := FP(r, rg, plus_bcv, str, ov);
    FNulledPlusFrame(qm, r, rg, plus_bcv, str, ov);
    NRR.InnerSub(r);
    var qc := rg.2.a_clk; var qcp := rg.2.a_cp;
    var gmS := GmSub(r, rg, mx);
    match r {
      case Re_empty =>
        assert GmSub(r, rg', mx) == map[] == gmS;
      case Re_character(_) =>
        assert GmSub(r, rg', mx) == map[] == gmS;
      case Re_anchor(_) =>
        assert GmSub(r, rg', mx) == map[] == gmS;
      case Re_lookaround(_, _, _) =>
        assert rg' == rg;
      case Re_capture(cid, r1) =>
        assert {:split_here} true;
        ReconReadoutCapture(qm, r, rg, plus_bcv, str, ov, mx);
      case Re_quant(nul, qid, q, r1) =>
        assert {:split_here} true;
        ReconReadoutQuant(qm, r, rg, plus_bcv, str, ov, mx);
      case Re_alt(r1, r2) =>
        assert {:split_here} true;
        ReconReadoutBin(qm, r, rg, plus_bcv, str, ov, mx);
      case Re_con(r1, r2) =>
        assert {:split_here} true;
        ReconReadoutBin(qm, r, rg, plus_bcv, str, ov, mx);
    }
  }

  lemma ReconReadoutBin(qm: AR.QMap, r: R.regex, rg: Regs3, plus_bcv: seq<RB.code>, str: string, ov: LOr.OracleView, mx: int)
    requires mx >= -1
    requires r.Re_alt? || r.Re_con?
    requires T.TransWf(r) && PIV.CapUnique(r) && PIV.QuantUnique(r) && NRR.LookUnique(r) && NRC.NoCdnPlusRE(r) && NRR.PlusTableOk(r, plus_bcv)
    requires ov == qm.ov
    requires NRR.WfRegs(rg) && NRR.CapValWf(rg) && NRR.Covers(r, rg) && NRR.LookCapsAbsent(r, rg)
    requires StampsLocal(qm, r, str, rg, mx)
    ensures var rg' := FP(r, rg, plus_bcv, str, ov);
            GmSub(r, rg', mx) == PIV.LiveStampsGm(r, qm, str, rg.2.a_clk, rg.2.a_cp, mx, GmSub(r, rg, mx))
    decreases r, 0
  {
    var r1 := NRR.L1(r); var r2 := NRR.L2(r);
    var qc := rg.2.a_clk; var qcp := rg.2.a_cp;
    NRR.PlusTableOkChildren(r, plus_bcv);
    NRR.CapUniqueChild(r);
    NRR.DisjointRegs(r);
    StampsLocalChild(qm, r, str, rg, mx);
    NRR.InnerSub(r1); NRR.InnerSub(r2);
    NRR.CoversChild(r, rg);
    var rgA := FP(r1, rg, plus_bcv, str, ov);
    var rg' := FP(r, rg, plus_bcv, str, ov);
    ReconReadoutSub(qm, r1, rg, plus_bcv, str, ov, mx);
    FNulledPlusFrame(qm, r1, rg, plus_bcv, str, ov);
    assert rg' == FP(r2, rgA, plus_bcv, str, ov);
    // r2's hypotheses at rgA (its registers are rg's)
    assert NRR.Covers(r2, rgA) && NRR.LookCapsAbsent(r2, rgA) && StampsLocal(qm, r2, str, rgA, mx) by {
      NRR.CoversSized(r2, rg, rgA);
      NRR.SubAgree2(r, rg, rgA);
      NRR.CapIdsInLooksSub(r2); NRR.CapRegsOfChar(r2);
      assert NRR.LookCapsAbsent(r2, rgA) by {
        forall c: nat | c in PIV.CapIdsInLooks(r2) ensures AI.get_idx(rgA.0.a_cp, CP.start_reg(c)) < 0 { assert CP.start_reg(c) in NRR.CapRegsOf(r2); }
      }
      StampsLocalTransfer(qm, r2, str, rg, rgA, mx);
    }
    ReconReadoutSub(qm, r2, rgA, plus_bcv, str, ov, mx);
    FNulledPlusFrame(qm, r2, rgA, plus_bcv, str, ov);
    assert {:split_here} true;
    // GmSub pieces
    GmSubSplit(r, rg, mx);
    assert NRR.LookCapsAbsent(r, rg') by { FNulledPlusLookCapsAbsent(qm, r, rg, plus_bcv, str, ov); }
    GmSubSplit(r, rg', mx);
    NRR.AgreeOutsideWeaken(rg', rgA, NRR.InnerCapRegs(r2), NRR.InnerLookRegs(r2), NRR.InnerQuantRegs(r2), NRR.CapRegsOf(r2), NRR.LookRegsOf(r2), NRR.QuantRegsOf(r2));
    NRR.AgreeOutsideWeaken(rgA, rg, NRR.InnerCapRegs(r1), NRR.InnerLookRegs(r1), NRR.InnerQuantRegs(r1), NRR.CapRegsOf(r1), NRR.LookRegsOf(r1), NRR.QuantRegsOf(r1));
    assert GmSub(r1, rg', mx) == GmSub(r1, rgA, mx) by { GmSubDep(r1, rgA, rg', mx); }
    assert GmSub(r2, rgA, mx) == GmSub(r2, rg, mx) by { GmSubDep(r2, rg, rgA, mx); }
    var g1 := GmSub(r1, rg, mx); var g2 := GmSub(r2, rg, mx);
    var g1' := GmSub(r1, rg', mx); var g2' := GmSub(r2, rg', mx);
    assert g1' == PIV.LiveStampsGm(r1, qm, str, qc, qcp, mx, g1);
    assert g2' == PIV.LiveStampsGm(r2, qm, str, rgA.2.a_clk, rgA.2.a_cp, mx, g2);
    assert PIV.LiveStampsGm(r2, qm, str, rgA.2.a_clk, rgA.2.a_cp, mx, g2) == PIV.LiveStampsGm(r2, qm, str, qc, qcp, mx, g2) by {
      NRR.SubAgree2(r, rg, rgA);
      NRR.QuantRegsOfChar(r2);
      assert forall q: nat :: q in PIV.QuantIds(r2) ==> (q as int) in NRR.QuantRegsOf(r2);
      LiveStampsGmQcDep(r2, qm, str, rgA.2.a_clk, qc, rgA.2.a_cp, qcp, mx, g2);
    }
    assert {:split_here} true;
    // assemble: LSG(r, g1 + g2) = LSG(r2, LSG(r1, g1 + g2)); frames split it into g1' + g2'
    var gmS := g1 + g2;
    assert BodiesMatch(qm, r, qcp) by { StampsLocalBodies(qm, r, str, rg, mx); }
    BodiesMatchChild(qm, r, qcp);
    var a1 := PIV.LiveStampsGm(r1, qm, str, qc, qcp, mx, gmS);
    LiveStampsGmFrame(r1, qm, str, qc, qcp, mx, gmS, g1);
    var a2 := PIV.LiveStampsGm(r2, qm, str, qc, qcp, mx, a1);
    LiveStampsGmFrame(r2, qm, str, qc, qcp, mx, a1, g2);
    assert PIV.LiveStampsGm(r, qm, str, qc, qcp, mx, gmS) == a2;
    assert {:split_here} true;
    // keys: CapIds(r1) from g1', CapIds(r2) from g2', nothing else
    GmSubKeys(r1, rg, mx); GmSubKeys(r2, rg, mx); GmSubKeys(r1, rg', mx); GmSubKeys(r2, rg', mx);
    LiveStampsGmKeys(r1, qm, str, qc, qcp, mx, g1);
    LiveStampsGmKeys(r2, qm, str, qc, qcp, mx, g2);
    forall g: nat ensures (g in a2 <==> g in g1' + g2') && (g in a2 ==> a2[g] == (g1' + g2')[g]) {
      if g in PIV.CapIds(r1) {
        assert g !in PIV.CapIds(r2);
      } else if g in PIV.CapIds(r2) {
      } else {
      }
    }
    assert a2 == g1' + g2';
  }

  lemma GmSubKeys(r: R.regex, rg: Regs3, mx: int)
    ensures forall g: nat :: g in GmSub(r, rg, mx) ==> g in PIV.CapIds(r)
  {}

  /** `LiveStampsGm` never creates a key outside `r`'s groups. */
  lemma LiveStampsGmKeys(r: R.regex, qm: AR.QMap, str: string, qc: seq<int>, qcp: seq<int>, mx: int, gm: LG.GroupMap)
    requires T.TransWf(r) && PIV.CapUnique(r) && PIV.QuantUnique(r) && BodiesMatch(qm, r, qcp)
    requires forall g: nat :: g in gm ==> g in PIV.CapIds(r)
    ensures forall g: nat :: g in PIV.LiveStampsGm(r, qm, str, qc, qcp, mx, gm) ==> g in PIV.CapIds(r)
  {
    LiveStampsGmFrame(r, qm, str, qc, qcp, mx, gm, gm);
  }

  lemma LiveStampsGmQcDep(r: R.regex, qm: AR.QMap, str: string, qcA: seq<int>, qcB: seq<int>, qcpA: seq<int>, qcpB: seq<int>, mx: int, gm: LG.GroupMap)
    requires T.TransWf(r)
    requires forall q: nat :: q in PIV.QuantIds(r) ==> AI.get_idx(qcA, q) == AI.get_idx(qcB, q) && AI.get_idx(qcpA, q) == AI.get_idx(qcpB, q)
    ensures PIV.LiveStampsGm(r, qm, str, qcA, qcpA, mx, gm) == PIV.LiveStampsGm(r, qm, str, qcB, qcpB, mx, gm)
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      LiveStampsGmQcDep(r1, qm, str, qcA, qcB, qcpA, qcpB, mx, gm);
      LiveStampsGmQcDep(r2, qm, str, qcA, qcB, qcpA, qcpB, mx, PIV.LiveStampsGm(r1, qm, str, qcA, qcpA, mx, gm));
    case Re_con(r1, r2) =>
      LiveStampsGmQcDep(r1, qm, str, qcA, qcB, qcpA, qcpB, mx, gm);
      LiveStampsGmQcDep(r2, qm, str, qcA, qcB, qcpA, qcpB, mx, PIV.LiveStampsGm(r1, qm, str, qcA, qcpA, mx, gm));
    case Re_capture(_, r1) => LiveStampsGmQcDep(r1, qm, str, qcA, qcB, qcpA, qcpB, mx, gm);
    case Re_quant(nul, qid, q, r1) =>
      if qid >= 0 {
        assert AI.get_idx(qcA, qid) == AI.get_idx(qcB, qid) && AI.get_idx(qcpA, qid) == AI.get_idx(qcpB, qid);
        var qv := AI.get_idx(qcA, qid);
        if qv >= mx && AI.get_idx(qcpA, qid) >= 0 {
          assert PIV.StampReady(qm, str, qid as nat, qcpA) == PIV.StampReady(qm, str, qid as nat, qcpB);
          if PIV.StampReady(qm, str, qid as nat, qcpA) { assert PIV.StampCp(qcpA, qid as nat) == PIV.StampCp(qcpB, qid as nat); }
        } else if qv >= mx {
          LiveStampsGmQcDep(r1, qm, str, qcA, qcB, qcpA, qcpB, qv, gm);
        }
      } else {
        assert AI.get_idx(qcA, qid) == -1 && AI.get_idx(qcB, qid) == -1;
        if -1 >= mx { LiveStampsGmQcDep(r1, qm, str, qcA, qcB, qcpA, qcpB, -1, gm); }
      }
    case _ =>
  }

  lemma StampsLocalTransfer(qm: AR.QMap, r: R.regex, str: string, rg: Regs3, rg': Regs3, mx: int)
    requires PIV.CapUnique(r) && PIV.QuantUnique(r)
    requires StampsLocal(qm, r, str, rg, mx) && NRR.LookCapsAbsent(r, rg)
    requires forall k: int :: k in NRR.CapRegsOf(r) ==> AI.get_idx(rg'.0.a_cp, k) == AI.get_idx(rg.0.a_cp, k) && AI.get_idx(rg'.0.a_clk, k) == AI.get_idx(rg.0.a_clk, k)
    requires forall k: int :: k in NRR.QuantRegsOf(r) ==> AI.get_idx(rg'.2.a_cp, k) == AI.get_idx(rg.2.a_cp, k) && AI.get_idx(rg'.2.a_clk, k) == AI.get_idx(rg.2.a_clk, k)
    ensures StampsLocal(qm, r, str, rg', mx)
  {
    NRR.QuantRegsOfChar(r);
    NRR.CapRegsOfChar(r);
    forall q: nat | q in PIV.QuantIds(r) && AI.get_idx(rg'.2.a_cp, q) >= 0 ensures
      NRR.QidCinPlus(r, q) && 0 <= AI.get_idx(rg'.2.a_cp, q) <= |str|
      && (q as int) in qm.bodies && qm.bodies[q as int] == PIV.QidBody(r, q)
      && (PIV.QChainFresh(r, rg'.2.a_clk, mx, q) ==> PIV.PathPresentQ(r, rg'.0.a_clk, rg'.2.a_clk, mx, q) && NRR.RegsStale(PIV.QidBody(r, q), rg', AI.get_idx(rg'.2.a_clk, q)))
    {
      assert AI.get_idx(rg.2.a_cp, q) >= 0;
      QChainFreshDep(r, rg.2.a_clk, rg'.2.a_clk, mx, q);
      if PIV.QChainFresh(r, rg'.2.a_clk, mx, q) {
        PathPresentQDep(r, rg.0.a_clk, rg'.0.a_clk, rg.2.a_clk, rg'.2.a_clk, mx, q);
        QidBodyRegs(r, q);
        assert NRR.LookCapsAbsent(PIV.QidBody(r, q), rg);
        NRR.StaleFrame(PIV.QidBody(r, q), rg, rg', AI.get_idx(rg.2.a_clk, q));
      }
    }
  }

  lemma QChainFreshDep(r: R.regex, qcA: seq<int>, qcB: seq<int>, mx: int, qid: nat)
    requires qid in PIV.QuantIds(r)
    requires forall q: nat :: q in PIV.QuantIds(r) ==> AI.get_idx(qcA, q) == AI.get_idx(qcB, q)
    ensures PIV.QChainFresh(r, qcA, mx, qid) == PIV.QChainFresh(r, qcB, mx, qid)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => if qid in PIV.QuantIds(r1) { QChainFreshDep(r1, qcA, qcB, mx, qid); } else { QChainFreshDep(r2, qcA, qcB, mx, qid); }
    case Re_con(r1, r2) => if qid in PIV.QuantIds(r1) { QChainFreshDep(r1, qcA, qcB, mx, qid); } else { QChainFreshDep(r2, qcA, qcB, mx, qid); }
    case Re_quant(nul, qid0, q, r1) =>
      if qid0 >= 0 && (qid0 as nat) == qid { } else { assert qid in PIV.QuantIds(r1); QChainFreshDep(r1, qcA, qcB, AI.get_idx(qcA, qid0), qid); assert AI.get_idx(qcA, qid0) == AI.get_idx(qcB, qid0) by { if qid0 >= 0 { assert (qid0 as nat) in PIV.QuantIds(r); } } }
    case Re_capture(_, r1) => QChainFreshDep(r1, qcA, qcB, mx, qid);
    case Re_lookaround(_, _, r1) => QChainFreshDep(r1, qcA, qcB, -1, qid);
    case _ =>
  }

  lemma PathPresentQDep(r: R.regex, ccA: seq<int>, ccB: seq<int>, qcA: seq<int>, qcB: seq<int>, mx: int, qid: nat)
    requires qid in PIV.QuantIds(r)
    requires forall q: nat :: q in PIV.QuantIds(r) ==> AI.get_idx(qcA, q) == AI.get_idx(qcB, q)
    requires forall c: nat :: c in PIV.CapIds(r) ==> AI.get_idx(ccA, CP.start_reg(c)) == AI.get_idx(ccB, CP.start_reg(c))
    ensures PIV.PathPresentQ(r, ccA, qcA, mx, qid) == PIV.PathPresentQ(r, ccB, qcB, mx, qid)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => if qid in PIV.QuantIds(r1) { PathPresentQDep(r1, ccA, ccB, qcA, qcB, mx, qid); } else { PathPresentQDep(r2, ccA, ccB, qcA, qcB, mx, qid); }
    case Re_con(r1, r2) => if qid in PIV.QuantIds(r1) { PathPresentQDep(r1, ccA, ccB, qcA, qcB, mx, qid); } else { PathPresentQDep(r2, ccA, ccB, qcA, qcB, mx, qid); }
    case Re_quant(nul, qid0, q, r1) =>
      if qid0 >= 0 && (qid0 as nat) == qid { } else {
        assert qid in PIV.QuantIds(r1);
        assert AI.get_idx(qcA, qid0) == AI.get_idx(qcB, qid0) by { if qid0 >= 0 { assert (qid0 as nat) in PIV.QuantIds(r); } }
        PathPresentQDep(r1, ccA, ccB, qcA, qcB, AI.get_idx(qcA, qid0), qid);
      }
    case Re_capture(cid, r1) =>
      assert cid >= 0 ==> AI.get_idx(ccA, CP.start_reg(cid)) == AI.get_idx(ccB, CP.start_reg(cid)) by { if cid >= 0 { assert (cid as nat) in PIV.CapIds(r); } }
      if cid < 0 { assert CP.start_reg(cid) < 0; }
      PathPresentQDep(r1, ccA, ccB, qcA, qcB, mx, qid);
    case Re_lookaround(_, _, r1) => PathPresentQDep(r1, ccA, ccB, qcA, qcB, mx, qid);
    case _ =>
  }

  /** A quantifier's body's registers are among the regex's. */
  lemma QidBodyRegs(r: R.regex, qid: nat)
    requires qid in PIV.QuantIds(r) && PIV.CapUnique(r) && PIV.QuantUnique(r)
    ensures PIV.CapUnique(PIV.QidBody(r, qid)) && PIV.QuantUnique(PIV.QidBody(r, qid))
    ensures NRR.CapRegsOf(PIV.QidBody(r, qid)) <= NRR.CapRegsOf(r) && NRR.QuantRegsOf(PIV.QidBody(r, qid)) <= NRR.QuantRegsOf(r)
    ensures PIV.CapIds(PIV.QidBody(r, qid)) <= PIV.CapIds(r)
    ensures PIV.CapIdsInLooks(PIV.QidBody(r, qid)) <= PIV.CapIdsInLooks(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => if qid in PIV.QuantIds(r1) { QidBodyRegs(r1, qid); } else { QidBodyRegs(r2, qid); }
    case Re_con(r1, r2) => if qid in PIV.QuantIds(r1) { QidBodyRegs(r1, qid); } else { QidBodyRegs(r2, qid); }
    case Re_quant(nul, qid0, q, r1) => if qid0 >= 0 && (qid0 as nat) == qid { } else { QidBodyRegs(r1, qid); }
    case Re_capture(_, r1) => QidBodyRegs(r1, qid);
    case Re_lookaround(_, _, r1) => QidBodyRegs(r1, qid); NRR.CapIdsInLooksSub(r1);
    case _ =>
  }

  // ---- the capture arm ----
  lemma ReconReadoutCapture(qm: AR.QMap, r: R.regex, rg: Regs3, plus_bcv: seq<RB.code>, str: string, ov: LOr.OracleView, mx: int)
    requires mx >= -1
    requires r.Re_capture?
    requires T.TransWf(r) && PIV.CapUnique(r) && PIV.QuantUnique(r) && NRR.LookUnique(r) && NRC.NoCdnPlusRE(r) && NRR.PlusTableOk(r, plus_bcv)
    requires ov == qm.ov
    requires NRR.WfRegs(rg) && NRR.CapValWf(rg) && NRR.Covers(r, rg) && NRR.LookCapsAbsent(r, rg)
    requires StampsLocal(qm, r, str, rg, mx)
    ensures var rg' := FP(r, rg, plus_bcv, str, ov);
            GmSub(r, rg', mx) == PIV.LiveStampsGm(r, qm, str, rg.2.a_clk, rg.2.a_cp, mx, GmSub(r, rg, mx))
    decreases r, 0
  {
    var cid := r.cid; var r1 := NRR.L1(r);
    var qc := rg.2.a_clk; var qcp := rg.2.a_cp;
    NRR.PlusTableOkChildren(r, plus_bcv);
    NRR.CapUniqueChild(r);
    StampsLocalChild(qm, r, str, rg, mx);
    NRR.InnerSub(r1);
    NRR.CoversChild(r, rg);
    var rg' := FP(r, rg, plus_bcv, str, ov);
    assert rg' == FP(r1, rg, plus_bcv, str, ov);
    ReconReadoutSub(qm, r1, rg, plus_bcv, str, ov, mx);
    FNulledPlusFrame(qm, r1, rg, plus_bcv, str, ov);
    NRR.CapRegsOfOwn(r);
    var sr := CP.start_reg(cid); var er := CP.end_reg(cid);
    assert AI.get_idx(rg'.0.a_cp, sr) == AI.get_idx(rg.0.a_cp, sr) && AI.get_idx(rg'.0.a_clk, sr) == AI.get_idx(rg.0.a_clk, sr)
        && AI.get_idx(rg'.0.a_cp, er) == AI.get_idx(rg.0.a_cp, er) && AI.get_idx(rg'.0.a_clk, er) == AI.get_idx(rg.0.a_clk, er);
    var start := AI.get_idx(rg.0.a_clk, sr);
    var g: nat := cid as nat;
    if start < 0 || start < mx {
      // hidden: both readouts on r are empty; no chain-fresh stamp sits inside
      forall c: nat | c in PIV.CapIds(r) ensures AI.get_idx(NRR.Filt(r, rg, mx), CP.start_reg(c)) < 0 && AI.get_idx(NRR.Filt(r, rg', mx), CP.start_reg(c)) < 0 {
        HiddenCaptureClears(r, rg, mx, c);
        HiddenCaptureClears(r, rg', mx, c);
      }
      assert GmSub(r, rg, mx) == map[] && GmSub(r, rg', mx) == map[];
      assert PIV.NoFreshStamp(r1, qc, qcp, mx) by {
        forall q: nat | q in PIV.QuantIds(r1) && AI.get_idx(qcp, q) >= 0 ensures !PIV.QChainFresh(r1, qc, mx, q) {
          if PIV.QChainFresh(r1, qc, mx, q) {
            assert q in PIV.QuantIds(r) && PIV.QChainFresh(r, qc, mx, q);
            assert PIV.PathPresentQ(r, rg.0.a_clk, qc, mx, q);
            assert start >= 0 && start >= mx;
          }
        }
      }
      PIV.LiveStampsGmStaleIdentity(r1, qm, str, qc, qcp, mx, map[]);
    } else {
      // present: cid's own entry is unchanged, the body's is the inductive readout
      assert NRR.Filt(r, rg, mx) == AI.filter_capture(r1, rg.0.a_cp, rg.0.a_clk, rg.1.a_clk, rg.2.a_clk, mx);
      assert NRR.Filt(r, rg', mx) == AI.filter_capture(r1, rg'.0.a_cp, rg'.0.a_clk, rg'.1.a_clk, rg'.2.a_clk, mx);
      NRR.FilterKeepsNonStart(r1, rg.0.a_cp, rg.0.a_clk, rg.1.a_clk, rg.2.a_clk, mx, sr);
      NRR.FilterKeepsNonStart(r1, rg'.0.a_cp, rg'.0.a_clk, rg'.1.a_clk, rg'.2.a_clk, mx, sr);
      PIV.FilterCaptureKeepsOdd(r1, rg.0.a_cp, rg.0.a_clk, rg.1.a_clk, rg.2.a_clk, mx, er);
      PIV.FilterCaptureKeepsOdd(r1, rg'.0.a_cp, rg'.0.a_clk, rg'.1.a_clk, rg'.2.a_clk, mx, er);
      assert AI.get_idx(rg.0.a_cp, sr) >= 0;   // CapValWf
      var g1 := GmSub(r1, rg, mx); var g1' := GmSub(r1, rg', mx);
      var own := PIV.LiveRange(NRR.Filt(r, rg, mx), rg.0.a_clk, g);
      assert PIV.LiveRange(NRR.Filt(r, rg', mx), rg'.0.a_clk, g) == own;
      assert GmSub(r, rg, mx) == g1[g := own] && GmSub(r, rg', mx) == g1'[g := own] by {
        GmSubKeys(r1, rg, mx); GmSubKeys(r1, rg', mx);
        assert g !in PIV.CapIds(r1);
        forall c: nat | c in PIV.CapIds(r1) ensures
          AI.get_idx(NRR.Filt(r, rg, mx), CP.start_reg(c)) == AI.get_idx(NRR.Filt(r1, rg, mx), CP.start_reg(c))
          && AI.get_idx(NRR.Filt(r, rg', mx), CP.start_reg(c)) == AI.get_idx(NRR.Filt(r1, rg', mx), CP.start_reg(c)) {}
      }
      assert BodiesMatch(qm, r, qcp) by { StampsLocalBodies(qm, r, str, rg, mx); }
      BodiesMatchChild(qm, r, qcp);
      LiveStampsGmFrame(r1, qm, str, qc, qcp, mx, g1[g := own], g1);
      LiveStampsGmKeys(r1, qm, str, qc, qcp, mx, g1);
      var a := PIV.LiveStampsGm(r1, qm, str, qc, qcp, mx, g1[g := own]);
      assert a == g1'[g := own] by {
        forall x: nat ensures (x in a <==> x in g1'[g := own]) && (x in a ==> a[x] == g1'[g := own][x]) {
          if x in PIV.CapIds(r1) { } else if x == g { } else { }
        }
      }
    }
  }

  /** A hidden capture (start unset or stale) clears its whole subtree's starts. */
  lemma HiddenCaptureClears(r: R.regex, rg: Regs3, mx: int, c: nat)
    requires r.Re_capture? && PIV.CapUnique(r) && NRR.CapValWf(rg)
    requires c in PIV.CapIds(r)
    requires var start := AI.get_idx(rg.0.a_clk, CP.start_reg(r.cid)); start < 0 || start < mx
    ensures AI.get_idx(NRR.Filt(r, rg, mx), CP.start_reg(c)) < 0
  {
    var sr := CP.start_reg(r.cid);
    var start := AI.get_idx(rg.0.a_clk, sr);
    var cr := rg.0.a_cp;
    if start < 0 {
      if c == r.cid as nat { PIV.FilterAllNeg(NRR.L1(r), cr, sr); assert AI.get_idx(cr, sr) < 0; }
      else { PIV.FilterAllClearsStart(NRR.L1(r), cr, c); }
    } else {
      var Z := AI.set_idx(cr, sr, -1);
      if c == r.cid as nat { PIV.FilterAllNeg(NRR.L1(r), Z, sr); }
      else { PIV.FilterAllClearsStart(NRR.L1(r), Z, c); }
    }
  }

  // ---- the quantifier arm ----
  lemma ReconReadoutQuant(qm: AR.QMap, r: R.regex, rg: Regs3, plus_bcv: seq<RB.code>, str: string, ov: LOr.OracleView, mx: int)
    requires mx >= -1
    requires r.Re_quant?
    requires T.TransWf(r) && PIV.CapUnique(r) && PIV.QuantUnique(r) && NRR.LookUnique(r) && NRC.NoCdnPlusRE(r) && NRR.PlusTableOk(r, plus_bcv)
    requires ov == qm.ov
    requires NRR.WfRegs(rg) && NRR.CapValWf(rg) && NRR.Covers(r, rg) && NRR.LookCapsAbsent(r, rg)
    requires StampsLocal(qm, r, str, rg, mx)
    ensures var rg' := FP(r, rg, plus_bcv, str, ov);
            GmSub(r, rg', mx) == PIV.LiveStampsGm(r, qm, str, rg.2.a_clk, rg.2.a_cp, mx, GmSub(r, rg, mx))
    decreases r, 0
  {
    var qid := r.qid; var r1 := NRR.L1(r);
    var qc := rg.2.a_clk; var qcp := rg.2.a_cp;
    assert qid >= 0 && (qid as nat) in PIV.QuantIds(r);
    var qv := AI.get_idx(qc, qid);
    NRR.PlusTableOkChildren(r, plus_bcv);
    NRR.CapUniqueChild(r);
    StampsLocalChild(qm, r, str, rg, mx);
    NRR.InnerSub(r1);
    NRR.QuantRegsOfOwn(r);
    var rg' := FP(r, rg, plus_bcv, str, ov);
    FNulledPlusFrame(qm, r, rg, plus_bcv, str, ov);
    assert AI.get_idx(rg'.2.a_clk, qid) == qv;
    if qv < mx {
      assert {:split_here} true;
      // stale node: everything below is cleared on both sides, the readout leaves gm
      forall c: nat | c in PIV.CapIds(r) ensures AI.get_idx(NRR.Filt(r, rg, mx), CP.start_reg(c)) < 0 && AI.get_idx(NRR.Filt(r, rg', mx), CP.start_reg(c)) < 0 {
        PIV.FilterAllClearsStart(r1, rg.0.a_cp, c);
        PIV.FilterAllClearsStart(r1, rg'.0.a_cp, c);
      }
      assert GmSub(r, rg, mx) == map[] && GmSub(r, rg', mx) == map[];
    } else if AI.get_idx(qcp, qid) >= 0 {
      assert {:split_here} true;
      // a live stamp: the engine reconstructs the body; the readout folds the path
      assert PIV.QChainFresh(r, qc, mx, qid as nat);
      var K := qv;
      var cp: nat := AI.get_idx(qcp, qid) as nat;
      var inp := T.InputAt(str, cp);
      assert NRR.RegsStale(r1, rg, K) && NRR.QidCinPlus(r, qid as nat) && PIV.QidBody(r, qid as nat) == r1;
      assert (qid as int) in qm.bodies && qm.bodies[qid as int] == r1;
      assert NRR.LookCapsAbsent(r1, rg) by { assert PIV.CapIdsInLooks(r1) == PIV.CapIdsInLooks(r); }
      assert K >= -1;
      StampReadout(qm, r, rg, plus_bcv, str, ov);
      var (rg2, ov2) := PlusAt(qm, r, rg, plus_bcv, str, ov);
      assert rg2 == rg';
      QuantEngineSide(qm, r, rg, rg', plus_bcv, str, ov, mx);
      QuantSpecSide(qm, r, rg, plus_bcv, str, ov, mx);
    } else {
      assert {:split_here} true;
      // unstamped, present: recurse at threshold qv on all three
      assert rg' == FP(r1, rg, plus_bcv, str, ov) by { assert AReg.get_cp(rg.2, qid) == None; }
      NRR.CoversChild(r, rg);
      assert PIV.CapIdsInLooks(r1) == PIV.CapIdsInLooks(r);
      ReconReadoutSub(qm, r1, rg, plus_bcv, str, ov, qv);
      assert NRR.Filt(r, rg, mx) == NRR.Filt(r1, rg, qv) && NRR.Filt(r, rg', mx) == NRR.Filt(r1, rg', qv);
      assert GmSub(r, rg, mx) == GmSub(r1, rg, qv) && GmSub(r, rg', mx) == GmSub(r1, rg', qv) by {
        assert PIV.CapIds(r) == PIV.CapIds(r1);
      }
    }
  }

  /** The live-stamp branch, engine side: after the stamp's reconstruction the
      quantifier's groups read as the path map. */
  lemma QuantEngineSide(qm: AR.QMap, r: R.regex, rg: Regs3, rg': Regs3, plus_bcv: seq<RB.code>, str: string, ov: LOr.OracleView, mx: int)
    requires r.Re_quant? && r.qid >= 0 && mx >= -1
    requires T.TransWf(r) && PIV.CapUnique(r) && PIV.QuantUnique(r) && NRR.LookUnique(r) && NRC.NoCdnPlusRE(r) && NRR.PlusTableOk(r, plus_bcv)
    requires ov == qm.ov && NRR.WfRegs(rg) && NRR.CapValWf(rg) && NRR.Covers(r, rg) && NRR.LookCapsAbsent(r, rg)
    requires NRR.QidCinPlus(r, r.qid as nat) && 0 <= AI.get_idx(rg.2.a_cp, r.qid) <= |str|
    requires var K := AI.get_idx(rg.2.a_clk, r.qid); K >= mx && NRR.RegsStale(NRR.L1(r), rg, K) && NRR.LookCapsAbsent(NRR.L1(r), rg)
    requires rg' == PlusAt(qm, r, rg, plus_bcv, str, ov).0
    ensures var cp: nat := AI.get_idx(rg.2.a_cp, r.qid) as nat;
            var inp := T.InputAt(str, cp);
            TR.FirstEmptyPathR(qm, NRR.L1(r), inp).Some?
            && GmSub(r, rg', mx) == PathMap(NRR.PathGroupsR(qm, NRR.L1(r), inp), cp)
  {
    var qid := r.qid; var r1 := NRR.L1(r);
    var K := AI.get_idx(rg.2.a_clk, qid);
    var cp: nat := AI.get_idx(rg.2.a_cp, qid) as nat;
    var inp := T.InputAt(str, cp);
    StampReadout(qm, r, rg, plus_bcv, str, ov);
    assert AI.get_idx(rg'.2.a_clk, qid) == K;
    assert NRR.Filt(r, rg', mx) == AI.filter_capture(r1, rg'.0.a_cp, rg'.0.a_clk, rg'.1.a_clk, rg'.2.a_clk, K);
    var P := NRR.PathGroupsR(qm, r1, inp);
    NRR.PathGroupsInCapIds(qm, r1, inp);
    var f := NRR.Filt(r1, rg', K);
    assert f == NRR.Filt(r, rg', mx);
    forall c: nat ensures (c in GmSub(r, rg', mx) <==> c in PathMap(P, cp)) && (c in PathMap(P, cp) ==> GmSub(r, rg', mx)[c] == LG.Range(cp, Some(cp))) {
      if c in PIV.CapIds(r1) {
        assert NRR.ReadsAs(f, rg', c, cp, c in P);
        if c in P {
          PIV.FilterCaptureKeepsOdd(r1, rg'.0.a_cp, rg'.0.a_clk, rg'.1.a_clk, rg'.2.a_clk, K, CP.end_reg(c));
          assert PIV.LiveRange(f, rg'.0.a_clk, c) == LG.Range(cp, Some(cp));
        }
      }
    }
  }

  /** The live-stamp branch, spec side: the readout's stamp rule yields the same path map. */
  lemma QuantSpecSide(qm: AR.QMap, r: R.regex, rg: Regs3, plus_bcv: seq<RB.code>, str: string, ov: LOr.OracleView, mx: int)
    requires r.Re_quant? && r.qid >= 0 && mx >= -1
    requires T.TransWf(r) && PIV.CapUnique(r) && PIV.QuantUnique(r)
    requires 0 <= AI.get_idx(rg.2.a_cp, r.qid) <= |str|
    requires (r.qid as int) in qm.bodies && qm.bodies[r.qid as int] == NRR.L1(r)
    requires AI.get_idx(rg.2.a_clk, r.qid) >= mx
    requires var cp: nat := AI.get_idx(rg.2.a_cp, r.qid) as nat; TR.FirstEmptyPathR(qm, NRR.L1(r), T.InputAt(str, cp)).Some?
    ensures var cp: nat := AI.get_idx(rg.2.a_cp, r.qid) as nat;
            PIV.LiveStampsGm(r, qm, str, rg.2.a_clk, rg.2.a_cp, mx, GmSub(r, rg, mx))
              == PathMap(NRR.PathGroupsR(qm, NRR.L1(r), T.InputAt(str, cp)), cp)
  {
    var qid := r.qid; var r1 := NRR.L1(r);
    var qc := rg.2.a_clk; var qcp := rg.2.a_cp;
    var cp: nat := AI.get_idx(qcp, qid) as nat;
    var inp := T.InputAt(str, cp);
    var gmS := GmSub(r, rg, mx);
    var gl := L.DefGroups(T.Translate(r1));
    var p := TR.FirstEmptyPathR(qm, r1, inp);
    var P := NRR.PathGroupsR(qm, r1, inp);
    // (1) the stamp rule fires
    assert PIV.LiveStampsGm(r, qm, str, qc, qcp, mx, gmS) == NP.ApplyPath(p.value, cp, LG.GMReset(gl, gmS)) by {
      hide *;
      reveal LiveStampsGm, StampApply, StampReady, StampCp;
      assert AI.get_idx(qc, qid) >= mx && AI.get_idx(qcp, qid) >= 0;
      assert PIV.StampReady(qm, str, qid as nat, qcp) && PIV.StampCp(qcp, qid as nat) == cp;
      assert qm.bodies[qid as int] == r1;
    }
    assert {:split_here} true;
    // (2) gmS lives inside gl, so the reset empties it
    assert LG.GMReset(gl, gmS) == map[] by {
      hide *;
      reveal LG.GMReset;
      GmSubKeys(r, rg, mx);
      PIV.DefGroupsCapIds(r1);
      assert PIV.CapIds(r) == PIV.CapIds(r1);
      forall x: nat ensures x !in LG.GMReset(gl, gmS) { if x in gmS { assert x in PIV.CapIds(r1); assert x in gl; } }
      forall x ensures x !in LG.GMReset(gl, gmS) { }
    }
    assert {:split_here} true;
    // (3) the fold on the empty map is the path map
    NRR.CpOfInputAt(str, cp);
    PathFoldR(qm, r1, inp, map[]);
    assert TR.CpOf(inp) == cp;
    assert NP.ApplyPath(p.value, cp, map[]) == Minus(map[], NRR.ResetGroupsR(qm, r1, inp)) + PathMap(P, cp);
    assert Minus(map[], NRR.ResetGroupsR(qm, r1, inp)) == map[] by { reveal Minus; }
    assert map[] + PathMap(P, cp) == PathMap(P, cp);
  }


  /** Registers of groups outside the regex are unset. */
  ghost predicate OnlyCapIdsSet(re: R.regex, rg: Regs3) {
    forall gid: nat :: gid !in PIV.CapIds(re) ==> AI.get_idx(rg.0.a_cp, CP.start_reg(gid)) < 0
  }

  lemma GmOfLiveIsGmSub(re: R.regex, rg: Regs3)
    requires NRR.Covers(re, rg) && OnlyCapIdsSet(re, rg)
    ensures PIV.GmOfLive(re, rg.0, rg.1, rg.2) == GmSub(re, rg, -1)
  {
    var f := AI.filter_reset(re, rg.0, rg.1, rg.2, -1);
    assert f == NRR.Filt(re, rg, -1);
    PIV.FilterCaptureLen(re, rg.0.a_cp, rg.0.a_clk, rg.1.a_clk, rg.2.a_clk, -1);
    forall gid: nat ensures (gid in PIV.GmOfLive(re, rg.0, rg.1, rg.2) <==> gid in GmSub(re, rg, -1)) {
      if gid !in PIV.CapIds(re) {
        NRR.FilterKeepsNonStart(re, rg.0.a_cp, rg.0.a_clk, rg.1.a_clk, rg.2.a_clk, -1, CP.start_reg(gid));
      } else {
        assert CP.end_reg(gid) < |rg.0.a_cp|;
        assert gid < |f|;
      }
    }
  }

  /** THE THEOREM. */
  lemma ReconReadout(qm: AR.QMap, re: R.regex, rg: Regs3, plus_bcv: seq<RB.code>, str: string, ov: LOr.OracleView)
    requires T.TransWf(re) && PIV.CapUnique(re) && PIV.QuantUnique(re) && NRR.LookUnique(re) && NRC.NoCdnPlusRE(re) && NRR.PlusTableOk(re, plus_bcv)
    requires ov == qm.ov
    requires NRR.WfRegs(rg) && NRR.CapValWf(rg) && NRR.Covers(re, rg) && NRR.LookCapsAbsent(re, rg) && OnlyCapIdsSet(re, rg)
    requires StampsLocal(qm, re, str, rg, -1)
    ensures var rg' := FP(re, rg, plus_bcv, str, ov);
            FPov(re, rg, plus_bcv, str, ov) == ov
            && PIV.GmOfLive(re, rg'.0, rg'.1, rg'.2) == PIV.GmOfLiveR(re, qm, str, rg.0, rg.1, rg.2)
  {
    var rg' := FP(re, rg, plus_bcv, str, ov);
    ReconReadoutSub(qm, re, rg, plus_bcv, str, ov, -1);
    FNulledPlusFrame(qm, re, rg, plus_bcv, str, ov);
    GmOfLiveIsGmSub(re, rg);
    assert OnlyCapIdsSet(re, rg') by {
      NRR.InnerSub(re);
      NRR.CapRegsOfChar(re);
      forall gid: nat | gid !in PIV.CapIds(re) ensures AI.get_idx(rg'.0.a_cp, CP.start_reg(gid)) < 0 {
        assert CP.start_reg(gid) !in NRR.CapRegsOf(re);
      }
    }
    NRR.CoversSized(re, rg, rg');
    GmOfLiveIsGmSub(re, rg');
  }
}
