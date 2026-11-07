// §2.5b STAGE 2, RUNG F (F-b, register half) — the reconstructed bank is a
// well-formed register bank again (`CM.ThreadRegsWf`, which the capture-array
// extraction needs): `FNulledPlus` never stores a capture value below the unset
// marker `-1`. Rung E's frame lemmas (`NRR.FNulledChildrenFrame`,
// `NRR.ReconAtFrame`, `NRO.FNulledPlusFrame`) already give sizes, `CapValWf`
// (value set <==> clock set) and the frame; this file adds the value bound by
// the same induction, kept OUT of `NRR.CapValWf` itself: strengthened there, the
// extra quantifier perturbed `EngineReadoutAlt`/`EngineReadoutCon` (one failure,
// one 300 s timeout) — and nulled-recon stays cached.
module LindenElkFinalRegs {
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
  import AR = LindenElkActionsRep
  import TR = LindenElkTreeRep
  import PIV = LindenElkPikeInv
  import NRC = LindenElkNulledRecon
  import NRR = LindenElkNulledReconRegs
  import NRO = LindenElkNulledReconReadout

  /** No capture value below the unset marker. */
  ghost predicate CapValGe(rg: NRC.Regs3) {
    forall k: int :: AI.get_idx(rg.0.a_cp, k) >= -1
  }

  /** (F-c) No quant clock below the unset marker (`M.QuantRegsFinal`'s clock half). */
  ghost predicate QClkGe(rg: NRC.Regs3) {
    forall k: int :: AI.get_idx(rg.2.a_clk, k) >= -1
  }

  /** Writes at a nonnegative position keep the bound. */
  lemma ApplyWritesValGe(ws: seq<NRC.Write>, cp: int, clks: seq<int>, rg: NRC.Regs3)
    requires |clks| == |ws| && cp >= 0
    requires forall i :: 0 <= i < |clks| ==> clks[i] >= -1
    requires CapValGe(rg) && QClkGe(rg)
    ensures CapValGe(NRC.ApplyWrites(ws, cp, clks, rg)) && QClkGe(NRC.ApplyWrites(ws, cp, clks, rg))
    decreases |ws|
  {
    if |ws| > 0 {
      var rg1 := NRC.ApplyWrite(ws[0], cp, clks[0], rg);
      assert QClkGe(rg1) by {
        forall k: int ensures AI.get_idx(rg1.2.a_clk, k) >= -1 {
          assert AI.get_idx(rg.2.a_clk, k) >= -1;
          match ws[0]
          case WQuant(q, b) =>
            var q0 := rg.2;
            assert rg1.2 == AReg.set_reg(q0, q, if b then Some(cp) else None, clks[0]);
            if 0 <= q < |q0.a_cp| && 0 <= q < |q0.a_clk| {
              assert rg1.2.a_clk == q0.a_clk[q := clks[0]];
              if 0 <= k < |q0.a_clk| && k != q {
                assert rg1.2.a_clk[k] == q0.a_clk[k];
              }
            } else {
              assert rg1.2 == q0;
            }
          case WCap(_) =>
            assert rg1.2 == rg.2;
          case WLook(_) =>
            assert rg1.2 == rg.2;
        }
      }
      assert CapValGe(rg1) by {
        forall k: int ensures AI.get_idx(rg1.0.a_cp, k) >= -1 {
          assert AI.get_idx(rg.0.a_cp, k) >= -1;
          match ws[0]
          case WCap(reg) =>
            var c0 := rg.0;
            assert rg1.0 == AReg.set_reg(c0, reg, Some(cp), clks[0]);
            if 0 <= reg < |c0.a_cp| && 0 <= reg < |c0.a_clk| {
              assert rg1.0.a_cp == c0.a_cp[reg := cp];
              if k == reg {
                assert AI.get_idx(rg1.0.a_cp, k) == cp;
              } else if 0 <= k < |c0.a_cp| {
                assert rg1.0.a_cp[k] == c0.a_cp[k];
                assert AI.get_idx(rg1.0.a_cp, k) == AI.get_idx(c0.a_cp, k);
              } else {
                assert AI.get_idx(rg1.0.a_cp, k) == -1;
              }
            } else {
              assert rg1.0 == c0;
            }
          case WLook(_) =>
            assert rg1.0 == rg.0;
          case WQuant(_, _) =>
            assert rg1.0 == rg.0;
        }
      }
      ApplyWritesValGe(ws[1..], cp, clks[1..], rg1);
    }
  }

  /** `FNulledChildren` keeps the bound (the `NRR.FNulledChildrenFrame` induction). */
  lemma FCValGe(qm: AR.QMap, r: R.regex, cdnt: LCdn.cdn_table, cp: nat, rg: NRC.Regs3,
                plus_bcv: seq<RB.code>, str: string, ov: LOr.OracleView)
    requires PIV.QuantUnique(r) && NRC.NoCdnPlusRE(r) && NRR.PlusTableOk(r, plus_bcv)
    requires NRR.WfRegs(rg) && NRR.CapValWf(rg) && CapValGe(rg) && QClkGe(rg) && ov == qm.ov && cp <= |str|
    ensures CapValGe(NRR.FC(r, cdnt, cp, rg, plus_bcv, str, ov)) && QClkGe(NRR.FC(r, cdnt, cp, rg, plus_bcv, str, ov))
    decreases r, 1
  {
    var rg2 := NRR.FC(r, cdnt, cp, rg, plus_bcv, str, ov);
    match r
    case Re_empty =>
    case Re_character(_) =>
    case Re_anchor(_) =>
    case Re_lookaround(_, _, _) =>
    case Re_capture(_, r1) =>
      NRR.PlusTableOkChildren(r, plus_bcv);
      FCValGe(qm, r1, cdnt, cp, rg, plus_bcv, str, ov);
    case Re_alt(r1, r2) =>
      NRR.PlusTableOkChildren(r, plus_bcv);
      FCValGe(qm, r1, cdnt, cp, rg, plus_bcv, str, ov);
      NRR.FNulledChildrenFrame(qm, r1, cdnt, cp, rg, plus_bcv, str, ov);
      var rgA := NRR.FC(r1, cdnt, cp, rg, plus_bcv, str, ov);
      FCValGe(qm, r2, cdnt, cp, rgA, plus_bcv, str, ov);
      assert rg2 == NRR.FC(r2, cdnt, cp, rgA, plus_bcv, str, ov);
    case Re_con(r1, r2) =>
      NRR.PlusTableOkChildren(r, plus_bcv);
      FCValGe(qm, r1, cdnt, cp, rg, plus_bcv, str, ov);
      NRR.FNulledChildrenFrame(qm, r1, cdnt, cp, rg, plus_bcv, str, ov);
      var rgA := NRR.FC(r1, cdnt, cp, rg, plus_bcv, str, ov);
      FCValGe(qm, r2, cdnt, cp, rgA, plus_bcv, str, ov);
      assert rg2 == NRR.FC(r2, cdnt, cp, rgA, plus_bcv, str, ov);
    case Re_quant(nul, qid, q, body) =>
      NRR.PlusTableOkChildren(r, plus_bcv);
      match AReg.get_cp(rg.2, qid) {
        case None =>
          FCValGe(qm, body, cdnt, cp, rg, plus_bcv, str, ov);
        case Some(start_cp) =>
          if start_cp == cp {
            var start_clock := AI.opt_int(AReg.get_clock(rg.2, qid));
            assert start_clock >= -1;
            var code := AI.get_code_v(plus_bcv, qid);
            var (rgR, ovR) := NRR.ReconAt(code, body, cdnt, cp, rg, start_clock, plus_bcv, str, ov);
            assert rg2 == rgR;
            ReconAtValGe(qm, r, body, qid, code, cdnt, cp, rg, start_clock, plus_bcv, str, ov);
          }
      }
  }

  /** One nested reconstruction keeps the bound (the `NRR.ReconAtFrame` induction). */
  lemma ReconAtValGe(qm: AR.QMap, r: R.regex, body: R.regex, qid: int, code: RB.code, cdnt: LCdn.cdn_table,
                     cp: nat, rg: NRC.Regs3, start_clock: int, plus_bcv: seq<RB.code>, str: string,
                     ov: LOr.OracleView)
    requires r.Re_quant? && NRR.L1(r) == body && r.qid == qid && qid >= 0
    requires PIV.QuantUnique(r) && NRC.NoCdnPlusRE(r) && NRR.PlusTableOk(r, plus_bcv)
    requires code == AI.get_code_v(plus_bcv, qid)
    requires NRR.WfRegs(rg) && NRR.CapValWf(rg) && CapValGe(rg) && QClkGe(rg) && ov == qm.ov && cp <= |str| && start_clock >= -1
    ensures CapValGe(NRR.ReconAt(code, body, cdnt, cp, rg, start_clock, plus_bcv, str, ov).0)
    ensures QClkGe(NRR.ReconAt(code, body, cdnt, cp, rg, start_clock, plus_bcv, str, ov).0)
    decreases r, 0
  {
    var ctx := AI.cp_context(cp, str, RA.Forward);
    var inits0 := AI.FInitState(code, cp, rg.0, rg.1, rg.2, start_clock, ctx);
    var inits := inits0.(cdn := cdnt);
    var (result, _, ov1) := AI.FNullInterp(code, inits, ov, RA.Forward);
    var rg1 := match result case None => rg case Some(w) => (w.capture_regs, w.look_regs, w.quant_regs);
    NRR.PlusTableOkChildren(r, plus_bcv);
    assert (qid as nat) in PIV.QuantIds(r) && PIV.QidBody(r, qid as nat) == body;
    var inp := T.InputAt(str, cp);
    NRR.CpOfInputAt(str, cp);
    if NRR.QidCinPlus(r, qid as nat) {
      assert code == CP.compile_reconstruct_nulled(body);
      assert inits == AI.FInitState(code, TR.CpOf(inp) as int, rg.0, rg.1, rg.2, start_clock, TR.CtxOf(inp)).(cdn := inits.cdn);
      NRC.NullInterpNulled(qm, body, inp, inits, ov, rg.0, rg.1, rg.2, start_clock);
      assert ov1 == ov;
      if result.Some? {
        var ws := NRC.NulledWrites(qm, body, inp).value;
        var C := AI.FNullInterp(code, inits, ov, RA.Forward).1.clock;
        assert NRC.RegsFrom(NRC.RegsOf(result.value), ws, cp, rg, start_clock, C);
        var clks: seq<int> :| |clks| == |ws| && NRC.Incr(clks) && NRC.ClksIn(clks, start_clock, C)
                                && NRC.RegsOf(result.value) == NRC.ApplyWrites(ws, cp, clks, rg);
        NRR.ApplyWritesFrame(ws, cp, clks, rg);
        NRR.ApplyWritesCapValWf(ws, cp, clks, rg);
        assert forall i :: 0 <= i < |clks| ==> clks[i] >= -1;
        ApplyWritesValGe(ws, cp, clks, rg);
      }
    } else {
      assert code == [];
      NRR.NullInterpEmptyCode(inits, ov);
      assert result.None? && ov1 == ov;
    }
    assert NRR.WfRegs(rg1) && NRR.CapValWf(rg1) && CapValGe(rg1) && QClkGe(rg1);
    FCValGe(qm, body, cdnt, cp, rg1, plus_bcv, str, ov1);
  }

  /** `FNulledPlus` keeps the bound (the `NRO.FNulledPlusFrame` induction). */
  lemma FPValGe(qm: AR.QMap, r: R.regex, rg: NRC.Regs3, plus_bcv: seq<RB.code>, str: string, ov: LOr.OracleView)
    requires PIV.CapUnique(r) && PIV.QuantUnique(r) && NRC.NoCdnPlusRE(r) && NRR.PlusTableOk(r, plus_bcv)
    requires NRR.WfRegs(rg) && NRR.CapValWf(rg) && CapValGe(rg) && QClkGe(rg) && ov == qm.ov && NRO.StampsInRange(r, rg, str)
    ensures CapValGe(NRO.FP(r, rg, plus_bcv, str, ov)) && QClkGe(NRO.FP(r, rg, plus_bcv, str, ov))
    decreases r
  {
    var rg2 := NRO.FP(r, rg, plus_bcv, str, ov);
    match r
    case Re_empty =>
    case Re_character(_) =>
    case Re_anchor(_) =>
    case Re_lookaround(_, _, _) =>
    case Re_capture(_, r1) =>
      NRR.PlusTableOkChildren(r, plus_bcv);
      FPValGe(qm, r1, rg, plus_bcv, str, ov);
    case Re_alt(r1, r2) =>
      NRR.PlusTableOkChildren(r, plus_bcv);
      FPValGe(qm, r1, rg, plus_bcv, str, ov);
      NRO.FNulledPlusFrame(qm, r1, rg, plus_bcv, str, ov);
      var rgA := NRO.FP(r1, rg, plus_bcv, str, ov);
      assert NRO.StampsInRange(r2, rgA, str) by {
        NRR.DisjointRegs(r); NRR.InnerSub(r1);
        NRO.StampsInRangeTransfer(r, r2, rg, rgA, str);
      }
      FPValGe(qm, r2, rgA, plus_bcv, str, ov);
      assert rg2 == NRO.FP(r2, rgA, plus_bcv, str, ov);
    case Re_con(r1, r2) =>
      NRR.PlusTableOkChildren(r, plus_bcv);
      FPValGe(qm, r1, rg, plus_bcv, str, ov);
      NRO.FNulledPlusFrame(qm, r1, rg, plus_bcv, str, ov);
      var rgA := NRO.FP(r1, rg, plus_bcv, str, ov);
      assert NRO.StampsInRange(r2, rgA, str) by {
        NRR.DisjointRegs(r); NRR.InnerSub(r1);
        NRO.StampsInRangeTransfer(r, r2, rg, rgA, str);
      }
      FPValGe(qm, r2, rgA, plus_bcv, str, ov);
      assert rg2 == NRO.FP(r2, rgA, plus_bcv, str, ov);
    case Re_quant(nul, qid, q, body) =>
      NRR.PlusTableOkChildren(r, plus_bcv);
      match AReg.get_cp(rg.2, qid) {
        case None =>
          FPValGe(qm, body, rg, plus_bcv, str, ov);
        case Some(start_cp) =>
          assert qid >= 0 && (qid as nat) in PIV.QuantIds(r) && 0 <= start_cp <= |str|;
          var start_clock := AI.opt_int(AReg.get_clock(rg.2, qid));
          assert start_clock >= -1;
          var code := AI.get_code_v(plus_bcv, qid);
          var ctx := AI.cp_context(start_cp, str, RA.Forward);
          var subcdn := LCdn.compile_cdns(body);
          var subtable := LCdn.build_cdn_v(subcdn, start_cp, ov, ctx, RA.Forward);
          var (rgR, ovR) := NRR.ReconAt(code, body, subtable, start_cp, rg, start_clock, plus_bcv, str, ov);
          assert rg2 == rgR;
          ReconAtValGe(qm, r, body, qid, code, subtable, start_cp as nat, rg, start_clock, plus_bcv, str, ov);
      }
  }
}
