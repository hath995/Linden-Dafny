// (G4b-1) The look registers the nulled-plus reconstruction can WRITE are the looks on the empty paths of
// stamped bodies — not every look in a stamped body. `NRC.NulledWrites` writes a positive look only where its
// first empty path crosses it, and `FNulledChildren` replays a nested quantifier's code only at a stamp plus
// (`QidStampPlus`; any other node has empty code). So:
//   * `OwnLooksE(r)`: the looks `NulledWrites(r)` can write (a sequence's half only when the other half may be
//     empty, `MayNull`; `{0,…}`, NonNullable and stamp nodes write no look at this level);
//   * `InnerLookRegsE(r)`: what `FNulledChildren` can write below `r` (a stamp plus's own looks, recursively);
//   * `LooksQE(re, Q)`: `RF.LooksQ` with those sets.
// The frames are copies of rung E's (`NRR.NulledWritesTargets`, `FNulledChildrenFrame`, `ReconAtFrame`) and of
// `RF.FNulledPlusFrameQS`/`FrameQPairS` with the look set replaced: the look bank agrees outside `LooksQE`.
module LindenElkEmptyLooks {
  import opened Std.Wrappers
  import R = RegElkRegex
  import RB = Bytecode
  import CP = Compiler
  import AI = ArrayInterp
  import AReg = Array_Regs
  import LOr = Oracle
  import RA = Anchors
  import LCdn = Cdn
  import LC = Chars
  import L = Regex
  import T = LindenElkTranslate
  import NUL = LindenElkNullable
  import AR = LindenElkActionsRep
  import TR = LindenElkTreeRep
  import PIV = LindenElkPikeInv
  import NRC = LindenElkNulledRecon
  import NRR = LindenElkNulledReconRegs
  import NRO = LindenElkNulledReconReadout
  import RF = LindenElkReconFrame
  type Regs3 = NRC.Regs3

  // ===========================================================================
  // 1. The sets
  // ===========================================================================

  /** `r` may match empty somewhere (its translation is not `NonNullableL`). */
  predicate MayNull(r: R.regex) {
    T.TransWf(r) ==> !NUL.NonNullableL(T.Translate(r))
  }

  /** The stamp-plus shape (`NRR.QidStampPlus` at the node itself). */
  predicate StampNode(nul: R.nullability, q: R.counted_quantifier) {
    q.min != 0 && q.max == None && nul != R.NonNullable && q.greedy
  }

  ghost function OwnLooksE(r: R.regex): set<int>
    decreases r
  {
    match r
    case Re_alt(r1, r2) => OwnLooksE(r1) + OwnLooksE(r2)
    case Re_con(r1, r2) => (if MayNull(r2) then OwnLooksE(r1) else {}) + (if MayNull(r1) then OwnLooksE(r2) else {})
    case Re_quant(nul, _, q, r1) => if q.min == 0 || nul == R.NonNullable || StampNode(nul, q) then {} else OwnLooksE(r1)
    case Re_capture(_, r1) => OwnLooksE(r1)
    case Re_lookaround(lid, la, _) => if NRC.PositiveLk(la) then {lid} else {}
    case _ => {}
  }

  ghost function InnerLookRegsE(r: R.regex): set<int>
    decreases r
  {
    match r
    case Re_alt(r1, r2) => InnerLookRegsE(r1) + InnerLookRegsE(r2)
    case Re_con(r1, r2) => InnerLookRegsE(r1) + InnerLookRegsE(r2)
    case Re_quant(nul, _, q, r1) => (if StampNode(nul, q) then OwnLooksE(r1) else {}) + InnerLookRegsE(r1)
    case Re_capture(_, r1) => InnerLookRegsE(r1)
    case _ => {}
  }

  ghost function LooksQE(r: R.regex, Q: set<int>): set<int>
    decreases r
  {
    match r
    case Re_alt(r1, r2) => LooksQE(r1, Q) + LooksQE(r2, Q)
    case Re_con(r1, r2) => LooksQE(r1, Q) + LooksQE(r2, Q)
    case Re_quant(nul, qid, q, body) => (if qid in Q then InnerLookRegsE(r) else {}) + LooksQE(body, Q)
    case Re_capture(_, r1) => LooksQE(r1, Q)
    case _ => {}
  }

  lemma LooksQEBody(r: R.regex, Q: set<int>)
    requires r.Re_quant?
    ensures InnerLookRegsE(r.qr) <= InnerLookRegsE(r) && LooksQE(r.qr, Q) <= LooksQE(r, Q)
  {}

  // ===========================================================================
  // 2. One level: `NulledWrites`
  // ===========================================================================

  lemma NulledWritesMayNull(qm: AR.QMap, r: R.regex, inp: LC.Input)
    requires T.TransWf(r)
    requires NRC.NulledWrites(qm, r, inp).Some?
    ensures MayNull(r)
    decreases r
  {
    match r
    case Re_empty =>
    case Re_character(_) =>
    case Re_anchor(_) =>
    case Re_lookaround(_, _, _) =>
    case Re_alt(r1, r2) =>
      if NRC.NulledWrites(qm, r1, inp).Some? { NulledWritesMayNull(qm, r1, inp); } else { NulledWritesMayNull(qm, r2, inp); }
    case Re_con(r1, r2) =>
      NulledWritesMayNull(qm, r1, inp);
      NulledWritesMayNull(qm, r2, inp);
    case Re_capture(_, r1) => NulledWritesMayNull(qm, r1, inp);
    case Re_quant(nul, qid, q, r1) =>
      if q.min == 0 {
      } else if q.max == None && nul == R.CINullable && q.greedy {
        NUL.TransCINullable(r1);
        NUL.CINotNonNullableL(T.Translate(r1));
      } else {
        NulledWritesMayNull(qm, r1, inp);
      }
  }

  /** The writes of the first empty path: captures and quants as rung E's, looks in `OwnLooksE`. */
  lemma NulledWritesTargetsE(qm: AR.QMap, re: R.regex, inp: LC.Input)
    requires T.TransWf(re)
    requires NRC.NulledWrites(qm, re, inp).Some?
    ensures var ws := NRC.NulledWrites(qm, re, inp).value;
            NRR.CapTargets(ws) <= NRR.CapRegsOf(re) && NRR.LookTargets(ws) <= OwnLooksE(re)
            && NRR.QuantTargets(ws) <= NRR.QuantRegsOf(re)
    decreases re
  {
    NRR.NulledWritesTargets(qm, re, inp);
    var ws := NRC.NulledWrites(qm, re, inp).value;
    match re
    case Re_empty => assert ws == [];
    case Re_character(_) =>
    case Re_anchor(_) => assert ws == [];
    case Re_alt(r1, r2) =>
      if NRC.NulledWrites(qm, r1, inp).Some? { NulledWritesTargetsE(qm, r1, inp); }
      else { NulledWritesTargetsE(qm, r2, inp); }
    case Re_con(r1, r2) =>
      NulledWritesTargetsE(qm, r1, inp);
      NulledWritesTargetsE(qm, r2, inp);
      NulledWritesMayNull(qm, r1, inp);
      NulledWritesMayNull(qm, r2, inp);
      NRR.TargetsApp(NRC.NulledWrites(qm, r1, inp).value, NRC.NulledWrites(qm, r2, inp).value);
    case Re_quant(nul, qid, q, r1) =>
      if q.min == 0 {
        assert ws == [];
      } else if nul == R.NonNullable {
      } else if q.max == None && nul == R.CINullable && q.greedy {
        assert ws == [NRC.WQuant(qid, true)];
        assert NRR.LookTargets(ws) == {};
      } else if q.max == None && nul == R.CDNullable && q.greedy {
        assert ws == [NRC.WQuant(qid, true)];
        assert NRR.LookTargets(ws) == {};
      } else {
        assert !StampNode(nul, q);
        NulledWritesTargetsE(qm, r1, inp);
        var w1 := NRC.NulledWrites(qm, r1, inp).value;
        NRR.TargetsApp([NRC.WQuant(qid, false)], w1);
        assert NRR.LookTargets([NRC.WQuant(qid, false)]) == {};
      }
    case Re_capture(cid, r1) =>
      NulledWritesTargetsE(qm, r1, inp);
      var w1 := NRC.NulledWrites(qm, r1, inp).value;
      NRR.TargetsApp([NRC.WCap(CP.start_reg(cid))] + w1, [NRC.WCap(CP.end_reg(cid))]);
      NRR.TargetsApp([NRC.WCap(CP.start_reg(cid))], w1);
      assert NRR.LookTargets([NRC.WCap(CP.start_reg(cid))]) == {} && NRR.LookTargets([NRC.WCap(CP.end_reg(cid))]) == {};
    case Re_lookaround(lid, la, _) =>
      if NRC.PositiveLk(la) {
        assert ws == [NRC.WLook(lid)];
        forall k | k in NRR.LookTargets(ws) ensures k in OwnLooksE(re) { assert k == lid; }
      } else {
        assert ws == [];
      }
  }

  // ===========================================================================
  // 3. `FNulledChildren` and one nested reconstruction
  // ===========================================================================

  lemma FNulledChildrenFrameE(qm: AR.QMap, r: R.regex, cdnt: LCdn.cdn_table, cp: nat, rg: Regs3,
                              plus_bcv: seq<RB.code>, str: string, ov: LOr.OracleView)
    requires T.TransWf(r) && PIV.QuantUnique(r) && NRR.PlusTableOkS(r, plus_bcv)
    requires NRR.WfRegs(rg) && NRR.CapValWf(rg) && ov == qm.ov && cp <= |str|
    requires NRC.CdnBitsOk(qm, r, T.InputAt(str, cp), cdnt)
    ensures NRR.AgreeOutside(NRR.FC(r, cdnt, cp, rg, plus_bcv, str, ov), rg,
                             NRR.InnerCapRegs(r), InnerLookRegsE(r), NRR.InnerQuantRegs(r))
    decreases r, 1
  {
    NRR.FNulledChildrenFrame(qm, r, cdnt, cp, rg, plus_bcv, str, ov);
    NRR.CdnBitsOkSub(qm, r, T.InputAt(str, cp), cdnt);
    var rg2 := NRR.FC(r, cdnt, cp, rg, plus_bcv, str, ov);
    match r
    case Re_empty =>
    case Re_character(_) =>
    case Re_anchor(_) =>
    case Re_lookaround(_, _, _) =>
    case Re_capture(_, r1) =>
      NRR.PlusTableOkSChildren(r, plus_bcv);
      FNulledChildrenFrameE(qm, r1, cdnt, cp, rg, plus_bcv, str, ov);
    case Re_alt(r1, r2) =>
      NRR.PlusTableOkSChildren(r, plus_bcv);
      FNulledChildrenFrameE(qm, r1, cdnt, cp, rg, plus_bcv, str, ov);
      NRR.FNulledChildrenFrame(qm, r1, cdnt, cp, rg, plus_bcv, str, ov);
      var rgA := NRR.FC(r1, cdnt, cp, rg, plus_bcv, str, ov);
      FNulledChildrenFrameE(qm, r2, cdnt, cp, rgA, plus_bcv, str, ov);
      assert rg2 == NRR.FC(r2, cdnt, cp, rgA, plus_bcv, str, ov);
      NRR.AgreeOutsideWeaken(rg2, rgA, NRR.InnerCapRegs(r2), InnerLookRegsE(r2), NRR.InnerQuantRegs(r2), NRR.InnerCapRegs(r), InnerLookRegsE(r), NRR.InnerQuantRegs(r));
      NRR.AgreeOutsideWeaken(rgA, rg, NRR.InnerCapRegs(r1), InnerLookRegsE(r1), NRR.InnerQuantRegs(r1), NRR.InnerCapRegs(r), InnerLookRegsE(r), NRR.InnerQuantRegs(r));
      NRR.AgreeOutsideTrans(rg2, rgA, rg, NRR.InnerCapRegs(r), InnerLookRegsE(r), NRR.InnerQuantRegs(r));
    case Re_con(r1, r2) =>
      NRR.PlusTableOkSChildren(r, plus_bcv);
      FNulledChildrenFrameE(qm, r1, cdnt, cp, rg, plus_bcv, str, ov);
      NRR.FNulledChildrenFrame(qm, r1, cdnt, cp, rg, plus_bcv, str, ov);
      var rgA := NRR.FC(r1, cdnt, cp, rg, plus_bcv, str, ov);
      FNulledChildrenFrameE(qm, r2, cdnt, cp, rgA, plus_bcv, str, ov);
      assert rg2 == NRR.FC(r2, cdnt, cp, rgA, plus_bcv, str, ov);
      NRR.AgreeOutsideWeaken(rg2, rgA, NRR.InnerCapRegs(r2), InnerLookRegsE(r2), NRR.InnerQuantRegs(r2), NRR.InnerCapRegs(r), InnerLookRegsE(r), NRR.InnerQuantRegs(r));
      NRR.AgreeOutsideWeaken(rgA, rg, NRR.InnerCapRegs(r1), InnerLookRegsE(r1), NRR.InnerQuantRegs(r1), NRR.InnerCapRegs(r), InnerLookRegsE(r), NRR.InnerQuantRegs(r));
      NRR.AgreeOutsideTrans(rg2, rgA, rg, NRR.InnerCapRegs(r), InnerLookRegsE(r), NRR.InnerQuantRegs(r));
    case Re_quant(nul, qid, q, body) =>
      NRR.PlusTableOkSChildren(r, plus_bcv);
      NRR.InnerSub(body);
      match AReg.get_cp(rg.2, qid) {
        case None =>
          FNulledChildrenFrameE(qm, body, cdnt, cp, rg, plus_bcv, str, ov);
          NRR.AgreeOutsideWeaken(rg2, rg, NRR.InnerCapRegs(body), InnerLookRegsE(body), NRR.InnerQuantRegs(body), NRR.CapRegsOf(body), InnerLookRegsE(r), NRR.QuantRegsOf(body));
        case Some(start_cp) =>
          if start_cp == cp {
            var start_clock := AI.opt_int(AReg.get_clock(rg.2, qid));
            assert start_clock >= -1;
            var code := AI.get_code_v(plus_bcv, qid);
            var (rgR, ovR) := NRR.ReconAt(code, body, cdnt, cp, rg, start_clock, plus_bcv, str, ov);
            assert rg2 == rgR;
            ReconAtFrameE(qm, r, body, qid, code, cdnt, cp, rg, start_clock, plus_bcv, str, ov);
          } else {
            NRR.AgreeOutsideRefl(rg, NRR.InnerCapRegs(r), InnerLookRegsE(r), NRR.InnerQuantRegs(r));
          }
      }
  }

  /** One nested reconstruction: the null interpreter writes the body's own empty-path looks (stamp plus only;
      other nodes have empty code), the children write `InnerLookRegsE(body)`. */
  lemma ReconAtFrameE(qm: AR.QMap, r: R.regex, body: R.regex, qid: int, code: RB.code, cdnt: LCdn.cdn_table, cp: nat,
                      rg: Regs3, start_clock: int, plus_bcv: seq<RB.code>, str: string, ov: LOr.OracleView)
    requires r.Re_quant? && NRR.L1(r) == body && r.qid == qid && qid >= 0
    requires T.TransWf(r) && PIV.QuantUnique(r) && NRR.PlusTableOkS(r, plus_bcv)
    requires code == AI.get_code_v(plus_bcv, qid)
    requires NRR.WfRegs(rg) && NRR.CapValWf(rg) && ov == qm.ov && cp <= |str| && start_clock >= -1
    requires NRC.CdnBitsOk(qm, body, T.InputAt(str, cp), cdnt)
    ensures var (rg2, ov2) := NRR.ReconAt(code, body, cdnt, cp, rg, start_clock, plus_bcv, str, ov);
            NRR.AgreeOutside(rg2, rg, NRR.CapRegsOf(body), InnerLookRegsE(r), NRR.QuantRegsOf(body))
    decreases r, 0
  {
    NRR.ReconAtFrame(qm, r, body, qid, code, cdnt, cp, rg, start_clock, plus_bcv, str, ov);
    var (rg2, ov2) := NRR.ReconAt(code, body, cdnt, cp, rg, start_clock, plus_bcv, str, ov);
    var ctx := AI.cp_context(cp, str, RA.Forward);
    var inits0 := AI.FInitState(code, cp, rg.0, rg.1, rg.2, start_clock, ctx);
    var inits := inits0.(cdn := cdnt);
    var (result, _, ov1) := AI.FNullInterp(code, inits, ov, RA.Forward);
    var rg1 := match result case None => rg case Some(w) => (w.capture_regs, w.look_regs, w.quant_regs);
    NRR.PlusTableOkSChildren(r, plus_bcv);
    assert (qid as nat) in PIV.QuantIds(r) && PIV.QidBody(r, qid as nat) == body;
    var inp := T.InputAt(str, cp);
    NRR.CpOfInputAt(str, cp);
    var Own := if StampNode(r.qnul, r.quant) then OwnLooksE(body) else {};
    assert NRR.QidStampPlus(r, qid as nat) == StampNode(r.qnul, r.quant);
    if NRR.QidStampPlus(r, qid as nat) {
      assert code == CP.compile_reconstruct_nulled(body);
      assert inits == AI.FInitState(code, TR.CpOf(inp) as int, rg.0, rg.1, rg.2, start_clock, TR.CtxOf(inp)).(cdn := inits.cdn);
      NRC.NullInterpNulledT(qm, body, inp, inits, ov, rg.0, rg.1, rg.2, start_clock);
      assert ov1 == ov;
      if result.Some? {
        var ws := NRC.NulledWrites(qm, body, inp).value;
        var C := AI.FNullInterp(code, inits, ov, RA.Forward).1.clock;
        assert NRC.RegsFrom(NRC.RegsOf(result.value), ws, cp, rg, start_clock, C);
        var clks: seq<int> :| |clks| == |ws| && NRC.Incr(clks) && NRC.ClksIn(clks, start_clock, C)
                                && NRC.RegsOf(result.value) == NRC.ApplyWrites(ws, cp, clks, rg);
        NRR.ApplyWritesFrame(ws, cp, clks, rg);
        NulledWritesTargetsE(qm, body, inp);
        NRR.AgreeOutsideWeaken(rg1, rg, NRR.CapTargets(ws), NRR.LookTargets(ws), NRR.QuantTargets(ws), NRR.CapRegsOf(body), Own, NRR.QuantRegsOf(body));
      } else {
        NRR.AgreeOutsideRefl(rg, NRR.CapRegsOf(body), Own, NRR.QuantRegsOf(body));
      }
    } else {
      assert code == [];
      NRR.NullInterpEmptyCode(inits, ov);
      assert result.None? && ov1 == ov;
      NRR.AgreeOutsideRefl(rg, NRR.CapRegsOf(body), Own, NRR.QuantRegsOf(body));
    }
    assert NRR.WfRegs(rg1) && NRR.Sized3(rg1, rg) && NRR.CapValWf(rg1) by {
      if NRR.QidStampPlus(r, qid as nat) && result.Some? {
        var ws := NRC.NulledWrites(qm, body, inp).value;
        var C := AI.FNullInterp(code, inits, ov, RA.Forward).1.clock;
        var clks: seq<int> :| |clks| == |ws| && NRC.Incr(clks) && NRC.ClksIn(clks, start_clock, C)
                                && NRC.RegsOf(result.value) == NRC.ApplyWrites(ws, cp, clks, rg);
        NRR.ApplyWritesFrame(ws, cp, clks, rg);
        NRR.ApplyWritesCapValWf(ws, cp, clks, rg);
      }
    }
    FNulledChildrenFrameE(qm, body, cdnt, cp, rg1, plus_bcv, str, ov1);
    NRR.InnerSub(body);
    NRR.AgreeOutsideWeaken(rg2, rg1, NRR.InnerCapRegs(body), InnerLookRegsE(body), NRR.InnerQuantRegs(body), NRR.CapRegsOf(body), InnerLookRegsE(r), NRR.QuantRegsOf(body));
    NRR.AgreeOutsideWeaken(rg1, rg, NRR.CapRegsOf(body), Own, NRR.QuantRegsOf(body), NRR.CapRegsOf(body), InnerLookRegsE(r), NRR.QuantRegsOf(body));
    NRR.AgreeOutsideTrans(rg2, rg1, rg, NRR.CapRegsOf(body), InnerLookRegsE(r), NRR.QuantRegsOf(body));
  }

  // ===========================================================================
  // 4. The sharp frame on the E look set (`RF.FNulledPlusFrameQS`/`FrameQPairS` with `LooksQE`)
  // ===========================================================================

  lemma FNulledPlusFrameQSE(qm: AR.QMap, r: R.regex, rg: Regs3, plus_bcv: seq<RB.code>, str: string,
                            ov: LOr.OracleView, Q: set<int>)
    requires T.TransWf(r) && PIV.CapUnique(r) && PIV.QuantUnique(r) && NRC.CdnTopRE(r) && NRR.PlusTableOkS(r, plus_bcv)
    requires NRR.WfRegs(rg) && NRR.CapValWf(rg) && ov == qm.ov && NRO.StampsInRangeS(r, rg, str)
    requires RF.StampsIn(r, rg, Q)
    ensures NRR.AgreeOutside(NRO.FP(r, rg, plus_bcv, str, ov), rg, RF.CapsQ(r, Q), LooksQE(r, Q), RF.QuantsQ(r, Q))
    decreases r
  {
    NRC.CdnTopChild(r);
    NRO.CapUniqueChildS(r);
    NRO.StampsInRangeSChild(r, rg, str);
    var rg2 := NRO.FP(r, rg, plus_bcv, str, ov);
    match r
    case Re_empty =>
    case Re_character(_) =>
    case Re_anchor(_) =>
    case Re_lookaround(_, _, _) =>
    case Re_capture(_, r1) =>
      NRR.PlusTableOkSChildren(r, plus_bcv);
      FNulledPlusFrameQSE(qm, r1, rg, plus_bcv, str, ov, Q);
    case Re_alt(r1, r2) =>
      FrameQPairSE(qm, r, r1, r2, rg, plus_bcv, str, ov, Q);
    case Re_con(r1, r2) =>
      FrameQPairSE(qm, r, r1, r2, rg, plus_bcv, str, ov, Q);
    case Re_quant(nul, qid, q, body) =>
      NRR.PlusTableOkSChildren(r, plus_bcv);
      RF.QSetsSub(body, Q);
      LooksQEBody(r, Q);
      match AReg.get_cp(rg.2, qid) {
        case None =>
          FNulledPlusFrameQSE(qm, body, rg, plus_bcv, str, ov, Q);
          NRR.AgreeOutsideWeaken(rg2, rg, RF.CapsQ(body, Q), LooksQE(body, Q), RF.QuantsQ(body, Q),
                                 RF.CapsQ(r, Q), LooksQE(r, Q), RF.QuantsQ(r, Q));
        case Some(start_cp) =>
          assert qid >= 0 && (qid as nat) in PIV.QuantIds(r);
          assert AI.get_idx(rg.2.a_cp, qid) >= 0;
          assert (qid as int) in Q;
          var start_clock := AI.opt_int(AReg.get_clock(rg.2, qid));
          var code := AI.get_code_v(plus_bcv, qid);
          var ctx := AI.cp_context(start_cp, str, RA.Forward);
          var subcdn := LCdn.compile_cdns(body);
          var subtable := LCdn.build_cdn_v(subcdn, start_cp, ov, ctx, RA.Forward);
          var (rgR, ovR) := NRR.ReconAt(code, body, subtable, start_cp, rg, start_clock, plus_bcv, str, ov);
          assert rg2 == rgR;
          assert 0 <= start_cp <= |str| && start_clock >= -1;
          assert NRR.QidStampPlus(r, qid as nat);
          NRR.SubtableBitsOk(qm, body, str, start_cp as nat, ov);
          ReconAtFrameE(qm, r, body, qid, code, subtable, start_cp as nat, rg, start_clock, plus_bcv, str, ov);
          NRR.AgreeOutsideWeaken(rg2, rg, NRR.CapRegsOf(body), InnerLookRegsE(r), NRR.QuantRegsOf(body),
                                 RF.CapsQ(r, Q), LooksQE(r, Q), RF.QuantsQ(r, Q));
      }
  }

  lemma FrameQPairSE(qm: AR.QMap, r: R.regex, r1: R.regex, r2: R.regex, rg: Regs3, plus_bcv: seq<RB.code>,
                     str: string, ov: LOr.OracleView, Q: set<int>)
    requires r == R.Re_alt(r1, r2) || r == R.Re_con(r1, r2)
    requires T.TransWf(r) && PIV.CapUnique(r) && PIV.QuantUnique(r) && NRC.CdnTopRE(r) && NRR.PlusTableOkS(r, plus_bcv)
    requires NRR.WfRegs(rg) && NRR.CapValWf(rg) && ov == qm.ov && NRO.StampsInRangeS(r, rg, str)
    requires RF.StampsIn(r, rg, Q)
    ensures NRR.AgreeOutside(NRO.FP(r, rg, plus_bcv, str, ov), rg, RF.CapsQ(r, Q), LooksQE(r, Q), RF.QuantsQ(r, Q))
    decreases r, 0
  {
    NRC.CdnTopChild(r);
    NRO.CapUniqueChildS(r);
    var rg2 := NRO.FP(r, rg, plus_bcv, str, ov);
    NRR.PlusTableOkSChildren(r, plus_bcv);
    assert NRR.L1(r) == r1 && NRR.L2(r) == r2;
    assert PIV.QuantIds(r1) <= PIV.QuantIds(r) && PIV.QuantIds(r2) <= PIV.QuantIds(r);
    assert NRO.StampsInRangeS(r1, rg, str) by {
      NRO.StampsInRangeSTransfer(r, r1, rg, rg, str);
    }
    FNulledPlusFrameQSE(qm, r1, rg, plus_bcv, str, ov, Q);
    NRO.FNulledPlusFrameS(qm, r1, rg, plus_bcv, str, ov);
    var rgA := NRO.FP(r1, rg, plus_bcv, str, ov);
    NRR.DisjointRegs(r); NRR.InnerSub(r1); RF.QSetsSub(r1, Q);
    forall k: int | k in NRR.QuantRegsOf(r2) ensures AI.get_idx(rgA.2.a_cp, k) == AI.get_idx(rg.2.a_cp, k) {
      assert NRR.L1(r) == r1 && NRR.L2(r) == r2;
      assert k !in NRR.QuantRegsOf(r1) * NRR.QuantRegsOf(r2);
    }
    assert NRO.StampsInRangeS(r2, rgA, str) by {
      NRO.StampsInRangeSTransfer(r, r2, rg, rgA, str);
    }
    RF.QuantIdsInRegs(r2);
    RF.StampsInSub(r, r2, rg, rgA, Q);
    FNulledPlusFrameQSE(qm, r2, rgA, plus_bcv, str, ov, Q);
    assert rg2 == NRO.FP(r2, rgA, plus_bcv, str, ov);
    NRR.AgreeOutsideWeaken(rg2, rgA, RF.CapsQ(r2, Q), LooksQE(r2, Q), RF.QuantsQ(r2, Q), RF.CapsQ(r, Q), LooksQE(r, Q), RF.QuantsQ(r, Q));
    NRR.AgreeOutsideWeaken(rgA, rg, RF.CapsQ(r1, Q), LooksQE(r1, Q), RF.QuantsQ(r1, Q), RF.CapsQ(r, Q), LooksQE(r, Q), RF.QuantsQ(r, Q));
    NRR.AgreeOutsideTrans(rg2, rgA, rg, RF.CapsQ(r, Q), LooksQE(r, Q), RF.QuantsQ(r, Q));
  }
}
