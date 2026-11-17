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
  import NI = LindenElkNestInv
  import LTB = LindenElkLookTables
  import NRC = LindenElkNulledRecon
  import NRR = LindenElkNulledReconRegs
  import NRO = LindenElkNulledReconReadout
  import RF = LindenElkReconFrame
  import CLP = LindenElkCinLookPaths
  import SL = LindenElkStampLive
  import FV = LindenElkFinalVm
  import FRD = LindenElkFinalReadout
  import LAnc = Anchors
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

  /** The capture registers of `r` OUTSIDE its look bodies: the reconstruction never writes inside a look (a
      look body may capture under G4b-1, so the frame may not include its groups). */
  ghost function CapRegsO(r: R.regex): set<int>
    decreases r
  {
    match r
    case Re_alt(r1, r2) => CapRegsO(r1) + CapRegsO(r2)
    case Re_con(r1, r2) => CapRegsO(r1) + CapRegsO(r2)
    case Re_quant(_, _, _, r1) => CapRegsO(r1)
    case Re_capture(cid, r1) => {CP.start_reg(cid), CP.end_reg(cid)} + CapRegsO(r1)
    case _ => {}
  }

  ghost function InnerCapRegsO(r: R.regex): set<int>
    decreases r
  {
    match r
    case Re_alt(r1, r2) => InnerCapRegsO(r1) + InnerCapRegsO(r2)
    case Re_con(r1, r2) => InnerCapRegsO(r1) + InnerCapRegsO(r2)
    case Re_quant(_, _, _, r1) => CapRegsO(r1)
    case Re_capture(_, r1) => InnerCapRegsO(r1)
    case _ => {}
  }

  ghost function CapsQO(r: R.regex, Q: set<int>): set<int>
    decreases r
  {
    match r
    case Re_alt(r1, r2) => CapsQO(r1, Q) + CapsQO(r2, Q)
    case Re_con(r1, r2) => CapsQO(r1, Q) + CapsQO(r2, Q)
    case Re_quant(_, qid, _, body) => (if qid in Q then CapRegsO(body) else {}) + CapsQO(body, Q)
    case Re_capture(_, r1) => CapsQO(r1, Q)
    case _ => {}
  }

  lemma CapsOSub(r: R.regex, Q: set<int>)
    ensures InnerCapRegsO(r) <= CapRegsO(r) && CapRegsO(r) <= NRR.CapRegsOf(r)
    ensures CapsQO(r, Q) <= RF.CapsQ(r, Q) && CapsQO(r, Q) <= CapRegsO(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => CapsOSub(r1, Q); CapsOSub(r2, Q);
    case Re_con(r1, r2) => CapsOSub(r1, Q); CapsOSub(r2, Q);
    case Re_quant(_, _, _, r1) => CapsOSub(r1, Q);
    case Re_capture(_, r1) => CapsOSub(r1, Q);
    case _ =>
  }

  /** Scope-free: the out-of-look capture registers are those of the out-of-look groups. */
  lemma CapRegsOOutside(r: R.regex)
    requires PIV.CapUnique(r)
    ensures CapRegsO(r) <= PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(r))
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      CapRegsOOutside(r1); CapRegsOOutside(r2);
      PIV.CaptureRegsSetMono(PIV.CapIdsOutsideLooks(r1), PIV.CapIdsOutsideLooks(r));
      PIV.CaptureRegsSetMono(PIV.CapIdsOutsideLooks(r2), PIV.CapIdsOutsideLooks(r));
    case Re_con(r1, r2) =>
      CapRegsOOutside(r1); CapRegsOOutside(r2);
      PIV.CaptureRegsSetMono(PIV.CapIdsOutsideLooks(r1), PIV.CapIdsOutsideLooks(r));
      PIV.CaptureRegsSetMono(PIV.CapIdsOutsideLooks(r2), PIV.CapIdsOutsideLooks(r));
    case Re_quant(_, _, _, r1) =>
      CapRegsOOutside(r1);
    case Re_capture(cid, r1) =>
      CapRegsOOutside(r1);
      PIV.CaptureRegsSetMono(PIV.CapIdsOutsideLooks(r1), PIV.CapIdsOutsideLooks(r));
      var c: nat := cid as nat;
      assert c in PIV.CapIdsOutsideLooks(r);
      assert CP.start_reg(cid) in (set x | x in PIV.CapIdsOutsideLooks(r) :: CP.start_reg(x));
      assert CP.end_reg(cid) in (set x | x in PIV.CapIdsOutsideLooks(r) :: CP.end_reg(x));
    case _ =>
  }

  lemma CapsQOOutside(r: R.regex, Q: set<int>)
    requires PIV.CapUnique(r)
    ensures CapsQO(r, Q) <= PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(r))
  {
    CapsOSub(r, Q);
    CapRegsOOutside(r);
  }

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

  lemma CapTargetsSingle(k: int)
    ensures NRR.CapTargets([NRC.WCap(k)]) == {k}
  {
    var ws := [NRC.WCap(k)];
    assert ws[0].WCap? && ws[0].reg == k;
    assert k in NRR.CapTargets(ws);
  }

  /** The writes of the first empty path: captures outside looks, quants as rung E's, looks in `OwnLooksE`. */
  lemma NulledWritesTargetsE(qm: AR.QMap, re: R.regex, inp: LC.Input)
    requires T.TransWf(re)
    requires NRC.NulledWrites(qm, re, inp).Some?
    ensures var ws := NRC.NulledWrites(qm, re, inp).value;
            NRR.CapTargets(ws) <= CapRegsO(re) && NRR.LookTargets(ws) <= OwnLooksE(re)
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
        assert NRR.LookTargets(ws) == {} && NRR.CapTargets(ws) == {};
      } else if q.max == None && nul == R.CDNullable && q.greedy {
        assert ws == [NRC.WQuant(qid, true)];
        assert NRR.LookTargets(ws) == {} && NRR.CapTargets(ws) == {};
      } else {
        assert !StampNode(nul, q);
        NulledWritesTargetsE(qm, r1, inp);
        var w1 := NRC.NulledWrites(qm, r1, inp).value;
        NRR.TargetsApp([NRC.WQuant(qid, false)], w1);
        assert NRR.LookTargets([NRC.WQuant(qid, false)]) == {} && NRR.CapTargets([NRC.WQuant(qid, false)]) == {};
      }
    case Re_capture(cid, r1) =>
      NulledWritesTargetsE(qm, r1, inp);
      var w1 := NRC.NulledWrites(qm, r1, inp).value;
      NRR.TargetsApp([NRC.WCap(CP.start_reg(cid))] + w1, [NRC.WCap(CP.end_reg(cid))]);
      NRR.TargetsApp([NRC.WCap(CP.start_reg(cid))], w1);
      assert NRR.LookTargets([NRC.WCap(CP.start_reg(cid))]) == {} && NRR.LookTargets([NRC.WCap(CP.end_reg(cid))]) == {};
      CapTargetsSingle(CP.start_reg(cid)); CapTargetsSingle(CP.end_reg(cid));
    case Re_lookaround(lid, la, _) =>
      if NRC.PositiveLk(la) {
        assert ws == [NRC.WLook(lid)];
        forall k | k in NRR.LookTargets(ws) ensures k in OwnLooksE(re) { assert k == lid; }
        assert NRR.CapTargets(ws) == {};
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
                             InnerCapRegsO(r), InnerLookRegsE(r), NRR.InnerQuantRegs(r))
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
      NRR.AgreeOutsideWeaken(rg2, rgA, InnerCapRegsO(r2), InnerLookRegsE(r2), NRR.InnerQuantRegs(r2), InnerCapRegsO(r), InnerLookRegsE(r), NRR.InnerQuantRegs(r));
      NRR.AgreeOutsideWeaken(rgA, rg, InnerCapRegsO(r1), InnerLookRegsE(r1), NRR.InnerQuantRegs(r1), InnerCapRegsO(r), InnerLookRegsE(r), NRR.InnerQuantRegs(r));
      NRR.AgreeOutsideTrans(rg2, rgA, rg, InnerCapRegsO(r), InnerLookRegsE(r), NRR.InnerQuantRegs(r));
    case Re_con(r1, r2) =>
      NRR.PlusTableOkSChildren(r, plus_bcv);
      FNulledChildrenFrameE(qm, r1, cdnt, cp, rg, plus_bcv, str, ov);
      NRR.FNulledChildrenFrame(qm, r1, cdnt, cp, rg, plus_bcv, str, ov);
      var rgA := NRR.FC(r1, cdnt, cp, rg, plus_bcv, str, ov);
      FNulledChildrenFrameE(qm, r2, cdnt, cp, rgA, plus_bcv, str, ov);
      assert rg2 == NRR.FC(r2, cdnt, cp, rgA, plus_bcv, str, ov);
      NRR.AgreeOutsideWeaken(rg2, rgA, InnerCapRegsO(r2), InnerLookRegsE(r2), NRR.InnerQuantRegs(r2), InnerCapRegsO(r), InnerLookRegsE(r), NRR.InnerQuantRegs(r));
      NRR.AgreeOutsideWeaken(rgA, rg, InnerCapRegsO(r1), InnerLookRegsE(r1), NRR.InnerQuantRegs(r1), InnerCapRegsO(r), InnerLookRegsE(r), NRR.InnerQuantRegs(r));
      NRR.AgreeOutsideTrans(rg2, rgA, rg, InnerCapRegsO(r), InnerLookRegsE(r), NRR.InnerQuantRegs(r));
    case Re_quant(nul, qid, q, body) =>
      NRR.PlusTableOkSChildren(r, plus_bcv);
      NRR.InnerSub(body);
      match AReg.get_cp(rg.2, qid) {
        case None =>
          FNulledChildrenFrameE(qm, body, cdnt, cp, rg, plus_bcv, str, ov);
          CapsOSub(body, {});
          NRR.AgreeOutsideWeaken(rg2, rg, InnerCapRegsO(body), InnerLookRegsE(body), NRR.InnerQuantRegs(body), CapRegsO(body), InnerLookRegsE(r), NRR.QuantRegsOf(body));
        case Some(start_cp) =>
          if start_cp == cp {
            var start_clock := AI.opt_int(AReg.get_clock(rg.2, qid));
            assert start_clock >= -1;
            var code := AI.get_code_v(plus_bcv, qid);
            var (rgR, ovR) := NRR.ReconAt(code, body, cdnt, cp, rg, start_clock, plus_bcv, str, ov);
            assert rg2 == rgR;
            ReconAtFrameE(qm, r, body, qid, code, cdnt, cp, rg, start_clock, plus_bcv, str, ov);
          } else {
            NRR.AgreeOutsideRefl(rg, InnerCapRegsO(r), InnerLookRegsE(r), NRR.InnerQuantRegs(r));
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
            NRR.AgreeOutside(rg2, rg, CapRegsO(body), InnerLookRegsE(r), NRR.QuantRegsOf(body))
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
        NRR.AgreeOutsideWeaken(rg1, rg, NRR.CapTargets(ws), NRR.LookTargets(ws), NRR.QuantTargets(ws), CapRegsO(body), Own, NRR.QuantRegsOf(body));
      } else {
        NRR.AgreeOutsideRefl(rg, CapRegsO(body), Own, NRR.QuantRegsOf(body));
      }
    } else {
      assert code == [];
      NRR.NullInterpEmptyCode(inits, ov);
      assert result.None? && ov1 == ov;
      NRR.AgreeOutsideRefl(rg, CapRegsO(body), Own, NRR.QuantRegsOf(body));
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
    CapsOSub(body, {});
    NRR.AgreeOutsideWeaken(rg2, rg1, InnerCapRegsO(body), InnerLookRegsE(body), NRR.InnerQuantRegs(body), CapRegsO(body), InnerLookRegsE(r), NRR.QuantRegsOf(body));
    NRR.AgreeOutsideWeaken(rg1, rg, CapRegsO(body), Own, NRR.QuantRegsOf(body), CapRegsO(body), InnerLookRegsE(r), NRR.QuantRegsOf(body));
    NRR.AgreeOutsideTrans(rg2, rg1, rg, CapRegsO(body), InnerLookRegsE(r), NRR.QuantRegsOf(body));
  }

  // ===========================================================================
  // 4. The sharp frame on the E look set (`RF.FNulledPlusFrameQS`/`FrameQPairS` with `LooksQE`)
  // ===========================================================================

  lemma FNulledPlusFrameQSE(qm: AR.QMap, r: R.regex, rg: Regs3, plus_bcv: seq<RB.code>, str: string,
                            ov: LOr.OracleView, Q: set<int>)
    requires T.TransWf(r) && PIV.CapUnique(r) && PIV.QuantUnique(r) && NRC.CdnTopRE(r) && NRR.PlusTableOkS(r, plus_bcv)
    requires NRR.WfRegs(rg) && NRR.CapValWf(rg) && ov == qm.ov && NRO.StampsInRangeS(r, rg, str)
    requires RF.StampsIn(r, rg, Q)
    ensures NRR.AgreeOutside(NRO.FP(r, rg, plus_bcv, str, ov), rg, CapsQO(r, Q), LooksQE(r, Q), RF.QuantsQ(r, Q))
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
          NRR.AgreeOutsideWeaken(rg2, rg, CapsQO(body, Q), LooksQE(body, Q), RF.QuantsQ(body, Q),
                                 CapsQO(r, Q), LooksQE(r, Q), RF.QuantsQ(r, Q));
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
          NRR.AgreeOutsideWeaken(rg2, rg, CapRegsO(body), InnerLookRegsE(r), NRR.QuantRegsOf(body),
                                 CapsQO(r, Q), LooksQE(r, Q), RF.QuantsQ(r, Q));
      }
  }

  lemma FrameQPairSE(qm: AR.QMap, r: R.regex, r1: R.regex, r2: R.regex, rg: Regs3, plus_bcv: seq<RB.code>,
                     str: string, ov: LOr.OracleView, Q: set<int>)
    requires r == R.Re_alt(r1, r2) || r == R.Re_con(r1, r2)
    requires T.TransWf(r) && PIV.CapUnique(r) && PIV.QuantUnique(r) && NRC.CdnTopRE(r) && NRR.PlusTableOkS(r, plus_bcv)
    requires NRR.WfRegs(rg) && NRR.CapValWf(rg) && ov == qm.ov && NRO.StampsInRangeS(r, rg, str)
    requires RF.StampsIn(r, rg, Q)
    ensures NRR.AgreeOutside(NRO.FP(r, rg, plus_bcv, str, ov), rg, CapsQO(r, Q), LooksQE(r, Q), RF.QuantsQ(r, Q))
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
    NRR.AgreeOutsideWeaken(rg2, rgA, CapsQO(r2, Q), LooksQE(r2, Q), RF.QuantsQ(r2, Q), CapsQO(r, Q), LooksQE(r, Q), RF.QuantsQ(r, Q));
    NRR.AgreeOutsideWeaken(rgA, rg, CapsQO(r1, Q), LooksQE(r1, Q), RF.QuantsQ(r1, Q), CapsQO(r, Q), LooksQE(r, Q), RF.QuantsQ(r, Q));
    NRR.AgreeOutsideTrans(rg2, rgA, rg, CapsQO(r, Q), LooksQE(r, Q), RF.QuantsQ(r, Q));
  }

  // ===========================================================================
  // 5. The scope: every look an empty path can cross is capture-free (any polarity)
  // ===========================================================================

  /** The RE twin of `NPL.EmptyLooksGroupFreeL` (its con arm translates verbatim under `TransWf`). */
  ghost predicate EmptyPathLooksCapFree(r: R.regex)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => EmptyPathLooksCapFree(r1) && EmptyPathLooksCapFree(r2)
    case Re_con(r1, r2) => (MayNull(r2) ==> EmptyPathLooksCapFree(r1)) && (MayNull(r1) ==> EmptyPathLooksCapFree(r2))
    case Re_quant(_, _, q, r1) => q.min == 0 || EmptyPathLooksCapFree(r1)
    case Re_capture(_, r1) => EmptyPathLooksCapFree(r1)
    case Re_lookaround(_, _, b) => PIV.CapIds(b) == {}
    case _ => true
  }

  /** (G4b-1) `RF.StampLooksCapFreeRE` with the stamp arm weakened to the empty-path looks. */
  ghost predicate StampLooksCapFreeE(re: R.regex)
    decreases re
  {
    match re
    case Re_alt(r1, r2) => StampLooksCapFreeE(r1) && StampLooksCapFreeE(r2)
    case Re_con(r1, r2) => StampLooksCapFreeE(r1) && StampLooksCapFreeE(r2)
    case Re_quant(nul, qid, q, body) => (StampNode(nul, q) ==> EmptyPathLooksCapFree(body)) && StampLooksCapFreeE(body)
    case Re_capture(_, r1) => StampLooksCapFreeE(r1)
    case Re_lookaround(_, _, r1) => StampLooksCapFreeE(r1)
    case _ => true
  }

  /** The scope outside look bodies (what the top reconstruction reads; a look body has its own scope). */
  ghost predicate StampLooksCapFreeTop(re: R.regex)
    decreases re
  {
    match re
    case Re_alt(r1, r2) => StampLooksCapFreeTop(r1) && StampLooksCapFreeTop(r2)
    case Re_con(r1, r2) => StampLooksCapFreeTop(r1) && StampLooksCapFreeTop(r2)
    case Re_quant(nul, qid, q, body) => (StampNode(nul, q) ==> EmptyPathLooksCapFree(body)) && StampLooksCapFreeTop(body)
    case Re_capture(_, r1) => StampLooksCapFreeTop(r1)
    case _ => true
  }

  lemma StampLooksCapFreeETop(re: R.regex)
    requires StampLooksCapFreeE(re)
    ensures StampLooksCapFreeTop(re)
    decreases re
  {
    match re
    case Re_alt(r1, r2) => StampLooksCapFreeETop(r1); StampLooksCapFreeETop(r2);
    case Re_con(r1, r2) => StampLooksCapFreeETop(r1); StampLooksCapFreeETop(r2);
    case Re_quant(_, _, _, body) => StampLooksCapFreeETop(body);
    case Re_capture(_, r1) => StampLooksCapFreeETop(r1);
    case _ =>
  }

  lemma CapFreeLooksEPCF(r: R.regex)
    requires PIV.CapIdsInLooks(r) == {}
    ensures EmptyPathLooksCapFree(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => CapFreeLooksEPCF(r1); CapFreeLooksEPCF(r2);
    case Re_con(r1, r2) => CapFreeLooksEPCF(r1); CapFreeLooksEPCF(r2);
    case Re_quant(_, _, _, r1) => CapFreeLooksEPCF(r1);
    case Re_capture(_, r1) => CapFreeLooksEPCF(r1);
    case _ =>
  }

  /** G4a's scope is an instance. */
  lemma StampLooksCapFreeToE(re: R.regex)
    requires RF.StampLooksCapFreeRE(re)
    ensures StampLooksCapFreeE(re)
    decreases re
  {
    match re
    case Re_alt(r1, r2) => StampLooksCapFreeToE(r1); StampLooksCapFreeToE(r2);
    case Re_con(r1, r2) => StampLooksCapFreeToE(r1); StampLooksCapFreeToE(r2);
    case Re_quant(nul, qid, q, body) =>
      StampLooksCapFreeToE(body);
      if StampNode(nul, q) { CapFreeLooksEPCF(body); }
    case Re_capture(_, r1) => StampLooksCapFreeToE(r1);
    case Re_lookaround(_, _, r1) => StampLooksCapFreeToE(r1);
    case _ =>
  }

  // ===========================================================================
  // 6. Every lid the reconstruction may re-set has a capture-free body
  // ===========================================================================

  lemma OwnLooksCapFree(r: R.regex, lid: nat)
    requires (lid as int) in OwnLooksE(r) && EmptyPathLooksCapFree(r) && LTB.LookUnique(r)
    ensures lid in LTB.LookIds(r) && PIV.CapIds(NI.LookBodyOfRE(r, lid)) == {}
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      if (lid as int) in OwnLooksE(r1) {
        OwnLooksCapFree(r1, lid);
      } else {
        OwnLooksCapFree(r2, lid);
        assert lid !in LTB.LookIds(r1) by { if lid in LTB.LookIds(r1) { assert lid in LTB.LookIds(r1) * LTB.LookIds(r2); } }
      }
    case Re_con(r1, r2) =>
      if MayNull(r2) && (lid as int) in OwnLooksE(r1) {
        OwnLooksCapFree(r1, lid);
      } else {
        OwnLooksCapFree(r2, lid);
        assert lid !in LTB.LookIds(r1) by { if lid in LTB.LookIds(r1) { assert lid in LTB.LookIds(r1) * LTB.LookIds(r2); } }
      }
    case Re_quant(_, _, _, r1) => OwnLooksCapFree(r1, lid);
    case Re_capture(_, r1) => OwnLooksCapFree(r1, lid);
    case Re_lookaround(lid0, la, b) => assert lid0 == lid as int;
    case _ =>
  }

  lemma InnerLooksCapFree(r: R.regex, lid: nat)
    requires (lid as int) in InnerLookRegsE(r) && StampLooksCapFreeTop(r) && LTB.LookUnique(r)
    ensures lid in LTB.LookIds(r) && PIV.CapIds(NI.LookBodyOfRE(r, lid)) == {}
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      if (lid as int) in InnerLookRegsE(r1) {
        InnerLooksCapFree(r1, lid);
      } else {
        InnerLooksCapFree(r2, lid);
        assert lid !in LTB.LookIds(r1) by { if lid in LTB.LookIds(r1) { assert lid in LTB.LookIds(r1) * LTB.LookIds(r2); } }
      }
    case Re_con(r1, r2) =>
      if (lid as int) in InnerLookRegsE(r1) {
        InnerLooksCapFree(r1, lid);
      } else {
        InnerLooksCapFree(r2, lid);
        assert lid !in LTB.LookIds(r1) by { if lid in LTB.LookIds(r1) { assert lid in LTB.LookIds(r1) * LTB.LookIds(r2); } }
      }
    case Re_quant(nul, _, q, r1) =>
      if StampNode(nul, q) && (lid as int) in OwnLooksE(r1) { OwnLooksCapFree(r1, lid); }
      else { InnerLooksCapFree(r1, lid); }
    case Re_capture(_, r1) => InnerLooksCapFree(r1, lid);
    case _ =>
  }

  /** (G4b-1) `SLk.LooksQCapFree` on the E set, with no stamp-set premise. */
  lemma LooksQECapFree(r: R.regex, Q: set<int>, lid: nat)
    requires (lid as int) in LooksQE(r, Q) && StampLooksCapFreeTop(r) && LTB.LookUnique(r)
    ensures lid in LTB.LookIds(r) && PIV.CapIds(NI.LookBodyOfRE(r, lid)) == {}
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      if (lid as int) in LooksQE(r1, Q) {
        LooksQECapFree(r1, Q, lid);
      } else {
        LooksQECapFree(r2, Q, lid);
        assert lid !in LTB.LookIds(r1) by { if lid in LTB.LookIds(r1) { assert lid in LTB.LookIds(r1) * LTB.LookIds(r2); } }
      }
    case Re_con(r1, r2) =>
      if (lid as int) in LooksQE(r1, Q) {
        LooksQECapFree(r1, Q, lid);
      } else {
        LooksQECapFree(r2, Q, lid);
        assert lid !in LTB.LookIds(r1) by { if lid in LTB.LookIds(r1) { assert lid in LTB.LookIds(r1) * LTB.LookIds(r2); } }
      }
    case Re_quant(_, qid, _, body) =>
      if (lid as int) in LooksQE(body, Q) { LooksQECapFree(body, Q, lid); }
      else { InnerLooksCapFree(r, lid); }
    case Re_capture(_, r1) => LooksQECapFree(r1, Q, lid);
    case _ =>
  }

  // ===========================================================================
  // 7. (G4b-1, the transports' case 3a) An ancestor register of a top lid inside a stamped body kills the lid's
  //    presence: below the stamp the threshold is at least the stamp clock (`NI.LookPathPresent` raises it at
  //    every quantifier), while `SL.BodyStale` puts every capture/quant clock of the body under it.
  // ===========================================================================

  lemma StaleAncNotPresent(r: R.regex, cc: seq<int>, qc: seq<int>, K: int, mx: int, lid: nat)
    requires lid in NI.TopLookIds(r) && lid in LTB.LookIds(r)
    requires PIV.CapUnique(r) && PIV.QuantUnique(r) && LTB.LookUnique(r)
    requires SL.BodyStale(r, cc, qc, K) && mx >= K
    requires CLP.AncCapRegs(r, lid) != {} || CLP.AncQuants(r, lid) != {}
    ensures !NI.LookPathPresent(r, cc, qc, mx, lid)
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      NI.TopLookIdsIn(r1); NI.TopLookIdsIn(r2);
      if lid in LTB.LookIds(r1) {
        assert lid in NI.TopLookIds(r1) by { if lid in NI.TopLookIds(r2) { assert lid in LTB.LookIds(r1) * LTB.LookIds(r2); } }
        StaleAncNotPresent(r1, cc, qc, K, mx, lid);
      } else {
        StaleAncNotPresent(r2, cc, qc, K, mx, lid);
      }
    case Re_con(r1, r2) =>
      NI.TopLookIdsIn(r1); NI.TopLookIdsIn(r2);
      if lid in LTB.LookIds(r1) {
        assert lid in NI.TopLookIds(r1) by { if lid in NI.TopLookIds(r2) { assert lid in LTB.LookIds(r1) * LTB.LookIds(r2); } }
        StaleAncNotPresent(r1, cc, qc, K, mx, lid);
      } else {
        StaleAncNotPresent(r2, cc, qc, K, mx, lid);
      }
    case Re_capture(cid, r1) =>
      assert (cid as nat) in PIV.CapIds(r);
    case Re_quant(_, qid, _, r1) =>
      assert (qid as nat) in PIV.QuantIds(r);
    case _ =>
  }

  lemma StampedAncKillsPresence(r: R.regex, cc: seq<int>, qc: seq<int>, mx: int, lid: nat, Q: set<int>)
    requires lid in NI.TopLookIds(r) && lid in LTB.LookIds(r)
    requires PIV.CapUnique(r) && PIV.QuantUnique(r) && LTB.LookUnique(r)
    requires forall q: nat :: q in PIV.QuantIds(r) && (q as int) in Q ==>
               SL.BodyStale(PIV.QidBody(r, q), cc, qc, AI.get_idx(qc, q))
    requires CLP.AncCapRegs(r, lid) * RF.CapsQ(r, Q) != {} || CLP.AncQuants(r, lid) * RF.QuantsQ(r, Q) != {}
    ensures !NI.LookPathPresent(r, cc, qc, mx, lid)
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      NRR.DisjointRegs(r);
      assert NRR.L1(r) == r1 && NRR.L2(r) == r2;
      RF.QSetsSub(r1, Q); RF.QSetsSub(r2, Q);
      NI.TopLookIdsIn(r1); NI.TopLookIdsIn(r2);
      if lid in LTB.LookIds(r1) {
        assert lid in NI.TopLookIds(r1) by { if lid in NI.TopLookIds(r2) { assert lid in LTB.LookIds(r1) * LTB.LookIds(r2); } }
        CLP.AncSub(r1, lid);
        StampedAncKillsPresence(r1, cc, qc, mx, lid, Q);
      } else {
        CLP.AncSub(r2, lid);
        StampedAncKillsPresence(r2, cc, qc, mx, lid, Q);
      }
    case Re_con(r1, r2) =>
      NRR.DisjointRegs(r);
      assert NRR.L1(r) == r1 && NRR.L2(r) == r2;
      RF.QSetsSub(r1, Q); RF.QSetsSub(r2, Q);
      NI.TopLookIdsIn(r1); NI.TopLookIdsIn(r2);
      if lid in LTB.LookIds(r1) {
        assert lid in NI.TopLookIds(r1) by { if lid in NI.TopLookIds(r2) { assert lid in LTB.LookIds(r1) * LTB.LookIds(r2); } }
        CLP.AncSub(r1, lid);
        StampedAncKillsPresence(r1, cc, qc, mx, lid, Q);
      } else {
        CLP.AncSub(r2, lid);
        StampedAncKillsPresence(r2, cc, qc, mx, lid, Q);
      }
    case Re_capture(cid, r1) =>
      RF.QSetsSub(r1, Q);
      NRR.CapRegsOfOwn(r);
      assert NRR.L1(r) == r1;
      assert CP.start_reg(cid) !in RF.CapsQ(r1, Q);
      StampedAncKillsPresence(r1, cc, qc, mx, lid, Q);
    case Re_quant(nul, qid, q, body) =>
      RF.QSetsSub(body, Q);
      NRR.QuantRegsOfChar(body);
      assert (qid as int) !in RF.QuantsQ(body, Q) && (qid as int) !in NRR.QuantRegsOf(body);
      var K := AI.get_idx(qc, qid);
      if (qid as int) in Q && (CLP.AncCapRegs(body, lid) != {} || CLP.AncQuants(body, lid) != {}) {
        assert (qid as nat) in PIV.QuantIds(r) && PIV.QidBody(r, qid as nat) == body;
        StaleAncNotPresent(body, cc, qc, K, K, lid);
      } else {
        StampedAncKillsPresence(body, cc, qc, K, lid, Q);
      }
    case _ =>
  }

  // ===========================================================================
  // 8. (G4b-1, the transports' BackT/Deep) The replay only RAISES quant clocks (`ReplayQuantClkMono`).
  //    Every replay write lands above the start clock of the replayed stamp, and that start clock is above every
  //    BASELINE clock of the stamp's body (`StaleAbove`): a fresh re-stamp sits above its enclosing replay's start,
  //    an untouched stamp keeps `SL.BodyStale`. A stamp write never enters its own body, so the invariant is
  //    stated against the fixed baseline, not against the evolving registers.
  // ===========================================================================

  /** Every key of `Sq` reads below `K` in the baseline `qb`. */
  ghost predicate QBelow(Sq: set<int>, qb: seq<int>, K: int) {
    forall k :: k in Sq ==> AI.get_idx(qb, k) < K
  }

  ghost predicate QBelowN(Sq: set<nat>, qb: seq<int>, K: int) {
    forall k: nat :: k in Sq ==> AI.get_idx(qb, k) < K
  }

  /** Every quant clock of `qr` is at least the baseline's. */
  ghost predicate QClkGe(qr: AReg.Regs, qb: seq<int>) {
    forall k: int :: AI.get_idx(qr.a_clk, k) >= AI.get_idx(qb, k)
  }

  /** `a` and `b` agree at quant key `k` (stamp and clock). */
  ghost predicate QSame(a: AReg.Regs, b: AReg.Regs, k: int) {
    AI.get_idx(a.a_cp, k) == AI.get_idx(b.a_cp, k) && AI.get_idx(a.a_clk, k) == AI.get_idx(b.a_clk, k)
  }

  /** Every stamp set in `qr` (outside looks: the replay never enters one) is above the baseline clocks of its body. */
  ghost predicate StaleAbove(r: R.regex, qb: seq<int>, qr: AReg.Regs)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => StaleAbove(r1, qb, qr) && StaleAbove(r2, qb, qr)
    case Re_con(r1, r2) => StaleAbove(r1, qb, qr) && StaleAbove(r2, qb, qr)
    case Re_quant(_, qid, _, body) =>
      (AI.get_idx(qr.a_cp, qid) >= 0 ==> QBelow(NRR.QuantRegsOf(body), qb, AI.get_idx(qr.a_clk, qid)))
      && StaleAbove(body, qb, qr)
    case Re_capture(_, r1) => StaleAbove(r1, qb, qr)
    case _ => true
  }

  /** The id-indexed form (what `SL.StampLiveOk` provides at the baseline). */
  ghost predicate QStaleIds(r: R.regex, qb: seq<int>, qr: AReg.Regs)
    requires PIV.QuantUnique(r)
  {
    forall q: nat :: q in PIV.QuantIds(r) && AI.get_idx(qr.a_cp, q) >= 0 ==>
      QBelowN(PIV.QuantIds(PIV.QidBody(r, q)), qb, AI.get_idx(qr.a_clk, q))
  }

  lemma QuantRegsIds(r: R.regex)
    requires PIV.QuantUnique(r)
    ensures forall k :: k in NRR.QuantRegsOf(r) ==> k >= 0 && (k as nat) in PIV.QuantIds(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => QuantRegsIds(r1); QuantRegsIds(r2);
    case Re_con(r1, r2) => QuantRegsIds(r1); QuantRegsIds(r2);
    case Re_quant(_, _, _, r1) => QuantRegsIds(r1);
    case Re_capture(_, r1) => QuantRegsIds(r1);
    case Re_lookaround(_, _, r1) => QuantRegsIds(r1);
    case _ =>
  }

  /** The quant registers of the two sides of a binary node are disjoint (quant ids only, no `CapUnique`). */
  lemma QuantRegsDisjoint(r: R.regex, r1: R.regex, r2: R.regex)
    requires r == R.Re_alt(r1, r2) || r == R.Re_con(r1, r2)
    requires PIV.QuantUnique(r)
    ensures NRR.QuantRegsOf(r1) * NRR.QuantRegsOf(r2) == {}
  {
    QuantRegsIds(r1); QuantRegsIds(r2);
    forall k | k in NRR.QuantRegsOf(r1) ensures k !in NRR.QuantRegsOf(r2) {
      if k in NRR.QuantRegsOf(r2) { assert (k as nat) in PIV.QuantIds(r1) * PIV.QuantIds(r2); }
    }
  }

  lemma StaleAboveOfIds(r: R.regex, qb: seq<int>, qr: AReg.Regs)
    requires PIV.QuantUnique(r) && QStaleIds(r, qb, qr)
    ensures StaleAbove(r, qb, qr)
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      assert QStaleIds(r1, qb, qr) by {
        forall q: nat | q in PIV.QuantIds(r1) ensures PIV.QidBody(r, q) == PIV.QidBody(r1, q) {}
      }
      assert QStaleIds(r2, qb, qr) by {
        forall q: nat | q in PIV.QuantIds(r2) ensures PIV.QidBody(r, q) == PIV.QidBody(r2, q) {
          assert q !in PIV.QuantIds(r1) by { if q in PIV.QuantIds(r1) { assert q in PIV.QuantIds(r1) * PIV.QuantIds(r2); } }
        }
      }
      StaleAboveOfIds(r1, qb, qr); StaleAboveOfIds(r2, qb, qr);
    case Re_con(r1, r2) =>
      assert QStaleIds(r1, qb, qr) by {
        forall q: nat | q in PIV.QuantIds(r1) ensures PIV.QidBody(r, q) == PIV.QidBody(r1, q) {}
      }
      assert QStaleIds(r2, qb, qr) by {
        forall q: nat | q in PIV.QuantIds(r2) ensures PIV.QidBody(r, q) == PIV.QidBody(r2, q) {
          assert q !in PIV.QuantIds(r1) by { if q in PIV.QuantIds(r1) { assert q in PIV.QuantIds(r1) * PIV.QuantIds(r2); } }
        }
      }
      StaleAboveOfIds(r1, qb, qr); StaleAboveOfIds(r2, qb, qr);
    case Re_quant(_, qid, _, body) =>
      assert QStaleIds(body, qb, qr) by {
        forall q: nat | q in PIV.QuantIds(body) ensures PIV.QidBody(r, q) == PIV.QidBody(body, q) {
          assert q != qid as nat;
        }
      }
      StaleAboveOfIds(body, qb, qr);
      if AI.get_idx(qr.a_cp, qid) >= 0 {
        assert (qid as nat) in PIV.QuantIds(r) && PIV.QidBody(r, qid as nat) == body;
        QuantRegsIds(body);
        assert QBelowN(PIV.QuantIds(body), qb, AI.get_idx(qr.a_clk, qid));
      }
    case Re_capture(_, r1) =>
      assert QStaleIds(r1, qb, qr) by {
        forall q: nat | q in PIV.QuantIds(r1) ensures PIV.QidBody(r, q) == PIV.QidBody(r1, q) {}
      }
      StaleAboveOfIds(r1, qb, qr);
    case _ =>
  }

  lemma StaleAboveFrame(r: R.regex, qb: seq<int>, a: AReg.Regs, b: AReg.Regs)
    requires StaleAbove(r, qb, a)
    requires forall k :: k in NRR.QuantRegsOf(r) ==> QSame(a, b, k)
    ensures StaleAbove(r, qb, b)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => StaleAboveFrame(r1, qb, a, b); StaleAboveFrame(r2, qb, a, b);
    case Re_con(r1, r2) => StaleAboveFrame(r1, qb, a, b); StaleAboveFrame(r2, qb, a, b);
    case Re_quant(_, qid, _, body) =>
      assert qid in NRR.QuantRegsOf(r);
      StaleAboveFrame(body, qb, a, b);
    case Re_capture(_, r1) => StaleAboveFrame(r1, qb, a, b);
    case _ =>
  }

  /** After one replay's writes (every moved key above `S`, every baseline clock of `U` below `S`). */
  lemma StaleAboveStep(r: R.regex, U: set<int>, qb: seq<int>, a: AReg.Regs, b: AReg.Regs, S: int)
    requires StaleAbove(r, qb, a) && NRR.QuantRegsOf(r) <= U && QBelow(U, qb, S)
    requires forall k :: k in NRR.QuantRegsOf(r) ==> QSame(a, b, k) || AI.get_idx(b.a_clk, k) > S
    ensures StaleAbove(r, qb, b)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => StaleAboveStep(r1, U, qb, a, b, S); StaleAboveStep(r2, U, qb, a, b, S);
    case Re_con(r1, r2) => StaleAboveStep(r1, U, qb, a, b, S); StaleAboveStep(r2, U, qb, a, b, S);
    case Re_quant(_, qid, _, body) =>
      assert qid in NRR.QuantRegsOf(r);
      StaleAboveStep(body, U, qb, a, b, S);
      if !QSame(a, b, qid) && AI.get_idx(b.a_cp, qid) >= 0 {
        assert QBelow(NRR.QuantRegsOf(body), qb, AI.get_idx(b.a_clk, qid)) by {
          forall k | k in NRR.QuantRegsOf(body) ensures AI.get_idx(qb, k) < AI.get_idx(b.a_clk, qid) {
            assert k in U;
          }
        }
      }
    case Re_capture(_, r1) => StaleAboveStep(r1, U, qb, a, b, S);
    case _ =>
  }

  /** A write sequence at clocks above `S` moves a quant key only to a target, above `S`. */
  lemma ApplyWritesQuantAbove(ws: seq<NRC.Write>, cp: int, clks: seq<int>, rg: Regs3, S: int)
    requires |clks| == |ws| && forall i :: 0 <= i < |clks| ==> clks[i] > S
    ensures forall k: int :: QSame(NRC.ApplyWrites(ws, cp, clks, rg).2, rg.2, k)
                             || (k in NRR.QuantTargets(ws) && AI.get_idx(NRC.ApplyWrites(ws, cp, clks, rg).2.a_clk, k) > S)
    decreases |ws|
  {
    if |ws| > 0 {
      var rg1 := NRC.ApplyWrite(ws[0], cp, clks[0], rg);
      ApplyWritesQuantAbove(ws[1..], cp, clks[1..], rg1, S);
      NRR.TargetsTail(ws);
      var out := NRC.ApplyWrites(ws, cp, clks, rg);
      assert out == NRC.ApplyWrites(ws[1..], cp, clks[1..], rg1);
      forall k: int ensures QSame(out.2, rg.2, k) || (k in NRR.QuantTargets(ws) && AI.get_idx(out.2.a_clk, k) > S) {
        if QSame(out.2, rg1.2, k) && !QSame(rg1.2, rg.2, k) {
          assert ws[0].WQuant? && ws[0].qid == k && 0 <= k < |rg.2.a_clk|;
          assert AI.get_idx(rg1.2.a_clk, k) == clks[0];
        }
      }
    }
  }

  lemma FCMono(qm: AR.QMap, r: R.regex, cdnt: LCdn.cdn_table, cp: nat, rg: Regs3,
               plus_bcv: seq<RB.code>, str: string, ov: LOr.OracleView, qb: seq<int>)
    requires T.TransWf(r) && PIV.QuantUnique(r) && NRR.PlusTableOkS(r, plus_bcv)
    requires NRR.WfRegs(rg) && NRR.CapValWf(rg) && ov == qm.ov && cp <= |str|
    requires NRC.CdnBitsOk(qm, r, T.InputAt(str, cp), cdnt)
    requires QClkGe(rg.2, qb) && StaleAbove(r, qb, rg.2)
    ensures var rg2 := NRR.FC(r, cdnt, cp, rg, plus_bcv, str, ov);
            QClkGe(rg2.2, qb) && StaleAbove(r, qb, rg2.2)
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
      FCMono(qm, r1, cdnt, cp, rg, plus_bcv, str, ov, qb);
    case Re_alt(r1, r2) =>
      FCPairMono(qm, r, r1, r2, cdnt, cp, rg, plus_bcv, str, ov, qb);
    case Re_con(r1, r2) =>
      FCPairMono(qm, r, r1, r2, cdnt, cp, rg, plus_bcv, str, ov, qb);
    case Re_quant(nul, qid, q, body) =>
      NRR.PlusTableOkSChildren(r, plus_bcv);
      NRR.InnerSub(body);
      NRR.QuantRegsOfChar(body);
      assert (qid as int) !in NRR.QuantRegsOf(body);
      match AReg.get_cp(rg.2, qid) {
        case None =>
          FCMono(qm, body, cdnt, cp, rg, plus_bcv, str, ov, qb);
          NRR.FNulledChildrenFrame(qm, body, cdnt, cp, rg, plus_bcv, str, ov);
          assert rg2 == NRR.FC(body, cdnt, cp, rg, plus_bcv, str, ov);
          assert QSame(rg2.2, rg.2, qid);
        case Some(start_cp) =>
          if start_cp == cp {
            var start_clock := AI.opt_int(AReg.get_clock(rg.2, qid));
            assert start_clock >= -1 && start_clock >= AI.get_idx(rg.2.a_clk, qid);
            var code := AI.get_code_v(plus_bcv, qid);
            var (rgR, ovR) := NRR.ReconAt(code, body, cdnt, cp, rg, start_clock, plus_bcv, str, ov);
            assert rg2 == rgR;
            assert AI.get_idx(rg.2.a_cp, qid) >= 0;
            assert QBelow(NRR.QuantRegsOf(body), qb, start_clock);
            ReconAtMono(qm, r, body, qid, code, cdnt, cp, rg, start_clock, plus_bcv, str, ov, qb);
            NRR.ReconAtFrame(qm, r, body, qid, code, cdnt, cp, rg, start_clock, plus_bcv, str, ov);
            assert QSame(rg2.2, rg.2, qid);
          }
      }
  }

  lemma FCPairMono(qm: AR.QMap, r: R.regex, r1: R.regex, r2: R.regex, cdnt: LCdn.cdn_table, cp: nat, rg: Regs3,
                   plus_bcv: seq<RB.code>, str: string, ov: LOr.OracleView, qb: seq<int>)
    requires r == R.Re_alt(r1, r2) || r == R.Re_con(r1, r2)
    requires T.TransWf(r) && PIV.QuantUnique(r) && NRR.PlusTableOkS(r, plus_bcv)
    requires NRR.WfRegs(rg) && NRR.CapValWf(rg) && ov == qm.ov && cp <= |str|
    requires NRC.CdnBitsOk(qm, r, T.InputAt(str, cp), cdnt)
    requires QClkGe(rg.2, qb) && StaleAbove(r, qb, rg.2)
    ensures var rg2 := NRR.FC(r, cdnt, cp, rg, plus_bcv, str, ov);
            QClkGe(rg2.2, qb) && StaleAbove(r, qb, rg2.2)
    decreases r, 0
  {
    NRR.CdnBitsOkSub(qm, r, T.InputAt(str, cp), cdnt);
    NRR.PlusTableOkSChildren(r, plus_bcv);
    var rg2 := NRR.FC(r, cdnt, cp, rg, plus_bcv, str, ov);
    FCMono(qm, r1, cdnt, cp, rg, plus_bcv, str, ov, qb);
    NRR.FNulledChildrenFrame(qm, r1, cdnt, cp, rg, plus_bcv, str, ov);
    var rgA := NRR.FC(r1, cdnt, cp, rg, plus_bcv, str, ov);
    assert NRR.L1(r) == r1 && NRR.L2(r) == r2;
    QuantRegsDisjoint(r, r1, r2); NRR.InnerSub(r1); NRR.InnerSub(r2);
    forall k: int | k in NRR.QuantRegsOf(r2) ensures QSame(rg.2, rgA.2, k) {
      assert k !in NRR.QuantRegsOf(r1) * NRR.QuantRegsOf(r2);
    }
    StaleAboveFrame(r2, qb, rg.2, rgA.2);
    FCMono(qm, r2, cdnt, cp, rgA, plus_bcv, str, ov, qb);
    NRR.FNulledChildrenFrame(qm, r2, cdnt, cp, rgA, plus_bcv, str, ov);
    assert rg2 == NRR.FC(r2, cdnt, cp, rgA, plus_bcv, str, ov);
    forall k: int | k in NRR.QuantRegsOf(r1) ensures QSame(rgA.2, rg2.2, k) {
      assert k !in NRR.QuantRegsOf(r1) * NRR.QuantRegsOf(r2);
    }
    StaleAboveFrame(r1, qb, rgA.2, rg2.2);
  }

  /** One nested replay: the null interpreter's writes land above `start_clock`, the children keep the invariant. */
  lemma ReconAtMono(qm: AR.QMap, r: R.regex, body: R.regex, qid: int, code: RB.code, cdnt: LCdn.cdn_table, cp: nat,
                    rg: Regs3, start_clock: int, plus_bcv: seq<RB.code>, str: string, ov: LOr.OracleView, qb: seq<int>)
    requires r.Re_quant? && NRR.L1(r) == body && r.qid == qid && qid >= 0
    requires T.TransWf(r) && PIV.QuantUnique(r) && NRR.PlusTableOkS(r, plus_bcv)
    requires code == AI.get_code_v(plus_bcv, qid)
    requires NRR.WfRegs(rg) && NRR.CapValWf(rg) && ov == qm.ov && cp <= |str| && start_clock >= -1
    requires NRC.CdnBitsOk(qm, body, T.InputAt(str, cp), cdnt)
    requires QClkGe(rg.2, qb) && StaleAbove(body, qb, rg.2) && QBelow(NRR.QuantRegsOf(body), qb, start_clock)
    ensures var (rg2, ov2) := NRR.ReconAt(code, body, cdnt, cp, rg, start_clock, plus_bcv, str, ov);
            QClkGe(rg2.2, qb) && StaleAbove(body, qb, rg2.2)
    decreases r, 0
  {
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
        assert rg1 == NRC.ApplyWrites(ws, cp, clks, rg);
        ApplyWritesQuantAbove(ws, cp, clks, rg, start_clock);
        NRR.NulledWritesTargets(qm, body, inp);
        assert QClkGe(rg1.2, qb) by {
          forall k: int ensures AI.get_idx(rg1.2.a_clk, k) >= AI.get_idx(qb, k) {
            if !QSame(rg1.2, rg.2, k) { assert k in NRR.QuantRegsOf(body); }
          }
        }
        StaleAboveStep(body, NRR.QuantRegsOf(body), qb, rg.2, rg1.2, start_clock);
        NRR.ApplyWritesFrame(ws, cp, clks, rg);
        NRR.ApplyWritesCapValWf(ws, cp, clks, rg);
      } else {
        assert rg1 == rg;
      }
    } else {
      assert code == [];
      NRR.NullInterpEmptyCode(inits, ov);
      assert result.None? && ov1 == ov;
    }
    assert NRR.WfRegs(rg1) && NRR.CapValWf(rg1) && ov1 == ov;
    FCMono(qm, body, cdnt, cp, rg1, plus_bcv, str, ov1, qb);
    assert rg2 == NRR.FC(body, cdnt, cp, rg1, plus_bcv, str, ov1);
  }

  lemma FPMono(qm: AR.QMap, r: R.regex, rg: Regs3, plus_bcv: seq<RB.code>, str: string, ov: LOr.OracleView, qb: seq<int>)
    requires T.TransWf(r) && PIV.CapUnique(r) && PIV.QuantUnique(r) && NRC.CdnTopRE(r) && NRR.PlusTableOkS(r, plus_bcv)
    requires NRR.WfRegs(rg) && NRR.CapValWf(rg) && ov == qm.ov && NRO.StampsInRangeS(r, rg, str)
    requires QClkGe(rg.2, qb) && StaleAbove(r, qb, rg.2)
    ensures var rg2 := NRO.FP(r, rg, plus_bcv, str, ov);
            QClkGe(rg2.2, qb) && StaleAbove(r, qb, rg2.2)
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
      FPMono(qm, r1, rg, plus_bcv, str, ov, qb);
    case Re_alt(r1, r2) =>
      FPPairMono(qm, r, r1, r2, rg, plus_bcv, str, ov, qb);
    case Re_con(r1, r2) =>
      FPPairMono(qm, r, r1, r2, rg, plus_bcv, str, ov, qb);
    case Re_quant(nul, qid, q, body) =>
      NRR.PlusTableOkSChildren(r, plus_bcv);
      NRR.InnerSub(body);
      NRR.QuantRegsOfChar(body);
      assert (qid as int) !in NRR.QuantRegsOf(body);
      match AReg.get_cp(rg.2, qid) {
        case None =>
          FPMono(qm, body, rg, plus_bcv, str, ov, qb);
          NRO.FNulledPlusFrameS(qm, body, rg, plus_bcv, str, ov);
          assert QSame(rg2.2, rg.2, qid);
        case Some(start_cp) =>
          assert qid >= 0 && (qid as nat) in PIV.QuantIds(r);
          assert AI.get_idx(rg.2.a_cp, qid) >= 0;
          var start_clock := AI.opt_int(AReg.get_clock(rg.2, qid));
          assert start_clock >= AI.get_idx(rg.2.a_clk, qid);
          var code := AI.get_code_v(plus_bcv, qid);
          var ctx := AI.cp_context(start_cp, str, RA.Forward);
          var subcdn := LCdn.compile_cdns(body);
          var subtable := LCdn.build_cdn_v(subcdn, start_cp, ov, ctx, RA.Forward);
          var (rgR, ovR) := NRR.ReconAt(code, body, subtable, start_cp, rg, start_clock, plus_bcv, str, ov);
          assert rg2 == rgR;
          assert 0 <= start_cp <= |str| && start_clock >= -1;
          assert NRR.QidStampPlus(r, qid as nat);
          NRR.SubtableBitsOk(qm, body, str, start_cp as nat, ov);
          assert QBelow(NRR.QuantRegsOf(body), qb, start_clock);
          ReconAtMono(qm, r, body, qid, code, subtable, start_cp as nat, rg, start_clock, plus_bcv, str, ov, qb);
          NRR.ReconAtFrame(qm, r, body, qid, code, subtable, start_cp as nat, rg, start_clock, plus_bcv, str, ov);
          assert QSame(rg2.2, rg.2, qid);
      }
  }

  lemma FPPairMono(qm: AR.QMap, r: R.regex, r1: R.regex, r2: R.regex, rg: Regs3, plus_bcv: seq<RB.code>,
                   str: string, ov: LOr.OracleView, qb: seq<int>)
    requires r == R.Re_alt(r1, r2) || r == R.Re_con(r1, r2)
    requires T.TransWf(r) && PIV.CapUnique(r) && PIV.QuantUnique(r) && NRC.CdnTopRE(r) && NRR.PlusTableOkS(r, plus_bcv)
    requires NRR.WfRegs(rg) && NRR.CapValWf(rg) && ov == qm.ov && NRO.StampsInRangeS(r, rg, str)
    requires QClkGe(rg.2, qb) && StaleAbove(r, qb, rg.2)
    ensures var rg2 := NRO.FP(r, rg, plus_bcv, str, ov);
            QClkGe(rg2.2, qb) && StaleAbove(r, qb, rg2.2)
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
    FPMono(qm, r1, rg, plus_bcv, str, ov, qb);
    NRO.FNulledPlusFrameS(qm, r1, rg, plus_bcv, str, ov);
    var rgA := NRO.FP(r1, rg, plus_bcv, str, ov);
    NRR.DisjointRegs(r); NRR.InnerSub(r1); NRR.InnerSub(r2);
    forall k: int | k in NRR.QuantRegsOf(r2) ensures AI.get_idx(rgA.2.a_cp, k) == AI.get_idx(rg.2.a_cp, k) {
      assert k !in NRR.QuantRegsOf(r1) * NRR.QuantRegsOf(r2);
    }
    forall k: int | k in NRR.QuantRegsOf(r2) ensures QSame(rg.2, rgA.2, k) {
      assert k !in NRR.QuantRegsOf(r1) * NRR.QuantRegsOf(r2);
    }
    assert NRO.StampsInRangeS(r2, rgA, str) by {
      NRO.StampsInRangeSTransfer(r, r2, rg, rgA, str);
    }
    StaleAboveFrame(r2, qb, rg.2, rgA.2);
    FPMono(qm, r2, rgA, plus_bcv, str, ov, qb);
    NRO.FNulledPlusFrameS(qm, r2, rgA, plus_bcv, str, ov);
    assert rg2 == NRO.FP(r2, rgA, plus_bcv, str, ov);
    forall k: int | k in NRR.QuantRegsOf(r1) ensures QSame(rgA.2, rg2.2, k) {
      assert k !in NRR.QuantRegsOf(r1) * NRR.QuantRegsOf(r2);
    }
    StaleAboveFrame(r1, qb, rgA.2, rg2.2);
  }

  /** THE MONOTONICITY: from a live baseline, the reconstruction only raises quant clocks. */
  lemma ReplayQuantClkMono(qm: AR.QMap, re: R.regex, rg: Regs3, plus_bcv: seq<RB.code>, str: string,
                           ov: LOr.OracleView, cc: seq<int>)
    requires T.TransWf(re) && PIV.CapUnique(re) && PIV.QuantUnique(re) && NRC.CdnTopRE(re) && NRR.PlusTableOkS(re, plus_bcv)
    requires NRR.WfRegs(rg) && NRR.CapValWf(rg) && ov == qm.ov && NRO.StampsInRangeS(re, rg, str)
    requires SL.StampLiveOk(re, cc, rg.2.a_clk, rg.2.a_cp)
    ensures QClkGe(NRO.FP(re, rg, plus_bcv, str, ov).2, rg.2.a_clk)
  {
    assert QStaleIds(re, rg.2.a_clk, rg.2) by {
      forall q: nat | q in PIV.QuantIds(re) && AI.get_idx(rg.2.a_cp, q) >= 0
        ensures QBelowN(PIV.QuantIds(PIV.QidBody(re, q)), rg.2.a_clk, AI.get_idx(rg.2.a_clk, q))
      {
        SL.StampLiveAt(re, cc, rg.2.a_clk, rg.2.a_cp, q);
      }
    }
    StaleAboveOfIds(re, rg.2.a_clk, rg.2);
    FPMono(qm, re, rg, plus_bcv, str, ov, rg.2.a_clk);
  }

  /** Dominance at a pointwise-larger quant bank implies dominance at the smaller one. */
  lemma LookPathDomMono(r: R.regex, L: int, qa: seq<int>, qb: seq<int>, lid: nat)
    requires lid in LTB.LookIds(r)
    requires forall k: int :: AI.get_idx(qa, k) >= AI.get_idx(qb, k)
    requires NI.LookPathDom(r, L, qa, lid)
    ensures NI.LookPathDom(r, L, qb, lid)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => if lid in LTB.LookIds(r1) { LookPathDomMono(r1, L, qa, qb, lid); } else { LookPathDomMono(r2, L, qa, qb, lid); }
    case Re_con(r1, r2) => if lid in LTB.LookIds(r1) { LookPathDomMono(r1, L, qa, qb, lid); } else { LookPathDomMono(r2, L, qa, qb, lid); }
    case Re_quant(_, qid, _, r1) => LookPathDomMono(r1, L, qa, qb, lid);
    case Re_capture(_, r1) => LookPathDomMono(r1, L, qa, qb, lid);
    case Re_lookaround(lid0, _, r1) => if !(lid0 >= 0 && (lid0 as nat) == lid) { LookPathDomMono(r1, L, qa, qb, lid); }
    case _ =>
  }

  // ===========================================================================
  // 9. (G4b-1) The endpoint frame of the top reconstruction at the DYNAMIC stamp set: the banks agree outside
  //    `CapsQO`/`LooksQE`/`QuantsQ` of the set stamps, and every quant clock only rose.
  // ===========================================================================

  ghost function StampSet(qcp: seq<int>): set<int> {
    set q | 0 <= q < |qcp| && qcp[q] >= 0
  }

  lemma FinalReadoutFrameSE(qm: AR.QMap, ast: R.regex, str: string, th: AI.Thread)
    requires T.TransWf(R.lazy_prefix(ast))
    requires PIV.CapUnique(R.lazy_prefix(ast)) && PIV.QuantUnique(R.lazy_prefix(ast)) && NRC.CdnTopRE(ast)
    requires FV.RegsFinalOk(th, |str|, FRD.StampQids(R.lazy_prefix(ast)))
    requires NRR.WfRegs((th.capture_regs, th.look_regs, th.quant_regs))
    requires SL.StampLiveOk(R.lazy_prefix(ast), th.capture_regs.a_clk, th.quant_regs.a_clk, th.quant_regs.a_cp)
    ensures var re := R.lazy_prefix(ast);
            var Q := StampSet(th.quant_regs.a_cp);
            var rp := AI.FReconstructPlus(th, ast, CP.FFullCompilation(ast).f_plus_bc, str, qm.ov, LAnc.Forward).0;
            NRR.AgreeOutside((rp.capture_regs, rp.look_regs, rp.quant_regs),
                             (th.capture_regs, th.look_regs, th.quant_regs),
                             CapsQO(re, Q), LooksQE(re, Q), RF.QuantsQ(re, Q))
            && QClkGe(rp.quant_regs, th.quant_regs.a_clk)
            && RF.QInStamp(re, Q)
  {
    var re := R.lazy_prefix(ast);
    var pre := R.Re_quant(R.NonNullable, 0, R.CountedQuant(0, None, false), R.Re_character(R.Dot));
    assert re == R.Re_con(pre, ast);
    var Q := StampSet(th.quant_regs.a_cp);
    var rg: NRC.Regs3 := (th.capture_regs, th.look_regs, th.quant_regs);
    var plus := CP.FFullCompilation(ast).f_plus_bc;
    FRD.PlusTableOkFullS(ast);
    NRC.CdnTopPrefix(ast);
    assert NRC.CdnTopRE(re);
    assert NRR.CapValWf(rg);
    assert NRO.StampsInRangeS(re, rg, str) by {
      forall q: nat | q in PIV.QuantIds(re) && AI.get_idx(rg.2.a_cp, q) >= 0
        ensures AI.get_idx(rg.2.a_cp, q) <= |str| && NRR.QidStampPlus(re, q)
      {
        assert (q as int) in FRD.StampQids(re);
        var qn: nat :| qn in PIV.QuantIds(re) && NRR.QidStampPlus(re, qn) && qn as int == q as int;
        assert qn == q;
      }
    }
    assert RF.StampsIn(re, rg, Q) by {
      forall q: nat | q in PIV.QuantIds(re) && AI.get_idx(rg.2.a_cp, q) >= 0 ensures (q as int) in Q {
        assert 0 <= q < |th.quant_regs.a_cp| && th.quant_regs.a_cp[q] >= 0;
      }
    }
    assert RF.QInStamp(re, Q) by {
      forall q: nat | q in PIV.QuantIds(re) && (q as int) in Q ensures NRR.QidStampPlus(re, q) {
        assert AI.get_idx(rg.2.a_cp, q) >= 0;
      }
    }
    FNulledPlusFrameQSE(qm, re, rg, plus, str, qm.ov, Q);
    ReplayQuantClkMono(qm, re, rg, plus, str, qm.ov, th.capture_regs.a_clk);
    assert AReg.get_cp(rg.2, 0) == None by {
      assert 0 in PIV.QuantIds(re);
      if AI.get_idx(rg.2.a_cp, 0) >= 0 {
        assert (0 as int) in FRD.StampQids(re);
        var qn: nat :| qn in PIV.QuantIds(re) && NRR.QidStampPlus(re, qn) && qn as int == 0;
        assert qn == 0 && !NRR.QidStampPlus(re, 0);
      }
    }
    FRD.PrefixIdentity(ast, rg, plus, str, qm.ov);
  }
}
