// §2.5b rung F-c (c6): the SHARP frame of the nulled-plus reconstruction —
// only the bodies of STAMPED quantifiers move (rung E's `FNulledPlusFrame`
// bounds the move by every quantifier body). With the stamps confined to a
// set `Q` (the CIN-greedy pluses, by the run's `FV.RegsFinalOk`), the
// reconstructed thread agrees with the VM winner outside `Q`'s bodies; for
// look-free CIN bodies outside looks this keeps the look bank and every
// look-body register — what the final readout's look loop reads.
module LindenElkReconFrame {
  import opened Std.Wrappers
  import R = RegElkRegex
  import RB = Bytecode
  import AI = ArrayInterp
  import AReg = Array_Regs
  import LOr = Oracle
  import RA = Anchors
  import LCdn = Cdn
  import AR = LindenElkActionsRep
  import PIV = LindenElkPikeInv
  import NRC = LindenElkNulledRecon
  import NRR = LindenElkNulledReconRegs
  import NRO = LindenElkNulledReconReadout
  import NR = LindenElkNfaRep

  type Regs3 = NRC.Regs3

  /** The registers of the bodies of `r`'s quantifiers in `Q`, as
      `FNulledPlus` walks `r` (not into lookarounds). */
  ghost function CapsQ(r: R.regex, Q: set<int>): set<int>
    decreases r
  {
    match r
    case Re_alt(r1, r2) => CapsQ(r1, Q) + CapsQ(r2, Q)
    case Re_con(r1, r2) => CapsQ(r1, Q) + CapsQ(r2, Q)
    case Re_quant(_, qid, _, body) => (if qid in Q then NRR.CapRegsOf(body) else {}) + CapsQ(body, Q)
    case Re_capture(_, r1) => CapsQ(r1, Q)
    case _ => {}
  }

  ghost function LooksQ(r: R.regex, Q: set<int>): set<int>
    decreases r
  {
    match r
    case Re_alt(r1, r2) => LooksQ(r1, Q) + LooksQ(r2, Q)
    case Re_con(r1, r2) => LooksQ(r1, Q) + LooksQ(r2, Q)
    case Re_quant(_, qid, _, body) => (if qid in Q then NRR.LookRegsOf(body) else {}) + LooksQ(body, Q)
    case Re_capture(_, r1) => LooksQ(r1, Q)
    case _ => {}
  }

  ghost function QuantsQ(r: R.regex, Q: set<int>): set<int>
    decreases r
  {
    match r
    case Re_alt(r1, r2) => QuantsQ(r1, Q) + QuantsQ(r2, Q)
    case Re_con(r1, r2) => QuantsQ(r1, Q) + QuantsQ(r2, Q)
    case Re_quant(_, qid, _, body) => (if qid in Q then NRR.QuantRegsOf(body) else {}) + QuantsQ(body, Q)
    case Re_capture(_, r1) => QuantsQ(r1, Q)
    case _ => {}
  }

  lemma QSetsSub(r: R.regex, Q: set<int>)
    ensures CapsQ(r, Q) <= NRR.CapRegsOf(r) && LooksQ(r, Q) <= NRR.LookRegsOf(r) && QuantsQ(r, Q) <= NRR.QuantRegsOf(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => QSetsSub(r1, Q); QSetsSub(r2, Q);
    case Re_con(r1, r2) => QSetsSub(r1, Q); QSetsSub(r2, Q);
    case Re_quant(_, qid, _, body) => QSetsSub(body, Q);
    case Re_capture(_, r1) => QSetsSub(r1, Q);
    case _ =>
  }

  /** Every stamped quantifier of `r` is in `Q`. */
  ghost predicate StampsIn(r: R.regex, rg: Regs3, Q: set<int>) {
    forall q: nat :: q in PIV.QuantIds(r) && AI.get_idx(rg.2.a_cp, q) >= 0 ==> (q as int) in Q
  }

  lemma StampsInSub(r: R.regex, sub: R.regex, rg: Regs3, rg': Regs3, Q: set<int>)
    requires StampsIn(r, rg, Q)
    requires PIV.QuantIds(sub) <= PIV.QuantIds(r)
    requires forall k: int :: k in NRR.QuantRegsOf(sub) ==> AI.get_idx(rg'.2.a_cp, k) == AI.get_idx(rg.2.a_cp, k)
    requires forall q: nat :: q in PIV.QuantIds(sub) ==> (q as int) in NRR.QuantRegsOf(sub)
    ensures StampsIn(sub, rg', Q)
  {}

  lemma QuantIdsInRegs(r: R.regex)
    ensures forall q: nat :: q in PIV.QuantIds(r) ==> (q as int) in NRR.QuantRegsOf(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => QuantIdsInRegs(r1); QuantIdsInRegs(r2);
    case Re_con(r1, r2) => QuantIdsInRegs(r1); QuantIdsInRegs(r2);
    case Re_quant(_, qid, _, body) => QuantIdsInRegs(body);
    case Re_capture(_, r1) => QuantIdsInRegs(r1);
    case Re_lookaround(_, _, r1) => QuantIdsInRegs(r1);
    case _ =>
  }

  /** THE SHARP FRAME. */
  lemma FNulledPlusFrameQ(qm: AR.QMap, r: R.regex, rg: Regs3, plus_bcv: seq<RB.code>, str: string,
                          ov: LOr.OracleView, Q: set<int>)
    requires PIV.CapUnique(r) && PIV.QuantUnique(r) && NRC.NoCdnPlusRE(r) && NRR.PlusTableOk(r, plus_bcv)
    requires NRR.WfRegs(rg) && NRR.CapValWf(rg) && ov == qm.ov && NRO.StampsInRange(r, rg, str)
    requires StampsIn(r, rg, Q)
    ensures NRR.AgreeOutside(NRO.FP(r, rg, plus_bcv, str, ov), rg, CapsQ(r, Q), LooksQ(r, Q), QuantsQ(r, Q))
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
      FNulledPlusFrameQ(qm, r1, rg, plus_bcv, str, ov, Q);
    case Re_alt(r1, r2) =>
      FrameQPair(qm, r, r1, r2, rg, plus_bcv, str, ov, Q);
    case Re_con(r1, r2) =>
      FrameQPair(qm, r, r1, r2, rg, plus_bcv, str, ov, Q);
    case Re_quant(nul, qid, q, body) =>
      NRR.PlusTableOkChildren(r, plus_bcv);
      QSetsSub(body, Q);
      match AReg.get_cp(rg.2, qid) {
        case None =>
          FNulledPlusFrameQ(qm, body, rg, plus_bcv, str, ov, Q);
          NRR.AgreeOutsideWeaken(rg2, rg, CapsQ(body, Q), LooksQ(body, Q), QuantsQ(body, Q),
                                 CapsQ(r, Q), LooksQ(r, Q), QuantsQ(r, Q));
        case Some(start_cp) =>
          assert qid >= 0 && (qid as nat) in PIV.QuantIds(r);
          assert AI.get_idx(rg.2.a_cp, qid) >= 0;
          assert (qid as int) in Q;
          // rung E's frame at a stamped quantifier: the body's registers alone move
          var start_clock := AI.opt_int(AReg.get_clock(rg.2, qid));
          var code := AI.get_code_v(plus_bcv, qid);
          var ctx := AI.cp_context(start_cp, str, RA.Forward);
          var subcdn := LCdn.compile_cdns(body);
          var subtable := LCdn.build_cdn_v(subcdn, start_cp, ov, ctx, RA.Forward);
          var (rgR, ovR) := NRR.ReconAt(code, body, subtable, start_cp, rg, start_clock, plus_bcv, str, ov);
          assert rg2 == rgR;
          assert 0 <= start_cp <= |str| && start_clock >= -1;
          NRR.ReconAtFrame(qm, r, body, qid, code, subtable, start_cp as nat, rg, start_clock, plus_bcv, str, ov);
          NRR.AgreeOutsideWeaken(rg2, rg, NRR.CapRegsOf(body), NRR.LookRegsOf(body), NRR.QuantRegsOf(body),
                                 CapsQ(r, Q), LooksQ(r, Q), QuantsQ(r, Q));
      }
  }

  lemma FrameQPair(qm: AR.QMap, r: R.regex, r1: R.regex, r2: R.regex, rg: Regs3, plus_bcv: seq<RB.code>,
                   str: string, ov: LOr.OracleView, Q: set<int>)
    requires r == R.Re_alt(r1, r2) || r == R.Re_con(r1, r2)
    requires PIV.CapUnique(r) && PIV.QuantUnique(r) && NRC.NoCdnPlusRE(r) && NRR.PlusTableOk(r, plus_bcv)
    requires NRR.WfRegs(rg) && NRR.CapValWf(rg) && ov == qm.ov && NRO.StampsInRange(r, rg, str)
    requires StampsIn(r, rg, Q)
    ensures NRR.AgreeOutside(NRO.FP(r, rg, plus_bcv, str, ov), rg, CapsQ(r, Q), LooksQ(r, Q), QuantsQ(r, Q))
    decreases r, 0
  {
    var rg2 := NRO.FP(r, rg, plus_bcv, str, ov);
    NRR.PlusTableOkChildren(r, plus_bcv);
    assert NRR.L1(r) == r1 && NRR.L2(r) == r2;
    assert PIV.QuantIds(r1) <= PIV.QuantIds(r) && PIV.QuantIds(r2) <= PIV.QuantIds(r);
    assert NRO.StampsInRange(r1, rg, str) by {
      NRO.StampsInRangeTransfer(r, r1, rg, rg, str);
    }
    FNulledPlusFrameQ(qm, r1, rg, plus_bcv, str, ov, Q);
    NRO.FNulledPlusFrame(qm, r1, rg, plus_bcv, str, ov);
    var rgA := NRO.FP(r1, rg, plus_bcv, str, ov);
    NRR.DisjointRegs(r); NRR.InnerSub(r1); QSetsSub(r1, Q);
    assert forall k: int :: k in NRR.QuantRegsOf(r2) ==> AI.get_idx(rgA.2.a_cp, k) == AI.get_idx(rg.2.a_cp, k);
    assert NRO.StampsInRange(r2, rgA, str) by {
      NRO.StampsInRangeTransfer(r, r2, rg, rgA, str);
    }
    QuantIdsInRegs(r2);
    StampsInSub(r, r2, rg, rgA, Q);
    FNulledPlusFrameQ(qm, r2, rgA, plus_bcv, str, ov, Q);
    assert rg2 == NRO.FP(r2, rgA, plus_bcv, str, ov);
    NRR.AgreeOutsideWeaken(rg2, rgA, CapsQ(r2, Q), LooksQ(r2, Q), QuantsQ(r2, Q), CapsQ(r, Q), LooksQ(r, Q), QuantsQ(r, Q));
    NRR.AgreeOutsideWeaken(rgA, rg, CapsQ(r1, Q), LooksQ(r1, Q), QuantsQ(r1, Q), CapsQ(r, Q), LooksQ(r, Q), QuantsQ(r, Q));
    NRR.AgreeOutsideTrans(rg2, rgA, rg, CapsQ(r, Q), LooksQ(r, Q), QuantsQ(r, Q));
  }

  // ===========================================================================
  // CIN-tameness: look-free CIN bodies keep the look bank
  // ===========================================================================

  /** Every CIN-greedy plus body is look-free. */
  ghost predicate CinBodiesLookFreeRE(re: R.regex)
    decreases re
  {
    match re
    case Re_alt(r1, r2) => CinBodiesLookFreeRE(r1) && CinBodiesLookFreeRE(r2)
    case Re_con(r1, r2) => CinBodiesLookFreeRE(r1) && CinBodiesLookFreeRE(r2)
    case Re_quant(nul, qid, q, body) =>
      (q.min != 0 && q.max == None && nul == R.CINullable && q.greedy ==> NR.LookFreeRE(body))
      && CinBodiesLookFreeRE(body)
    case Re_capture(_, r1) => CinBodiesLookFreeRE(r1)
    case Re_lookaround(_, _, r1) => CinBodiesLookFreeRE(r1)
    case _ => true
  }

  /** `Q`'s quantifiers of `r` are its CIN-greedy pluses. */
  ghost predicate QInCin(r: R.regex, Q: set<int>) {
    forall q: nat :: q in PIV.QuantIds(r) && (q as int) in Q ==> NRR.QidCinPlus(r, q)
  }

  lemma LookFreeNoLookRegs(r: R.regex)
    requires NR.LookFreeRE(r)
    ensures NRR.LookRegsOf(r) == {}
    decreases r
  {
    match r
    case Re_alt(r1, r2) => LookFreeNoLookRegs(r1); LookFreeNoLookRegs(r2);
    case Re_con(r1, r2) => LookFreeNoLookRegs(r1); LookFreeNoLookRegs(r2);
    case Re_quant(_, _, _, r1) => LookFreeNoLookRegs(r1);
    case Re_capture(_, r1) => LookFreeNoLookRegs(r1);
    case _ =>
  }

  lemma LooksQEmpty(r: R.regex, Q: set<int>)
    requires CinBodiesLookFreeRE(r) && PIV.QuantUnique(r) && QInCin(r, Q)
    ensures LooksQ(r, Q) == {}
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      assert QInCin(r1, Q) by {
        forall q2: nat | q2 in PIV.QuantIds(r1) && (q2 as int) in Q ensures NRR.QidCinPlus(r1, q2) {
          assert q2 in PIV.QuantIds(r) && NRR.QidCinPlus(r, q2);
        }
      }
      assert QInCin(r2, Q) by {
        forall q2: nat | q2 in PIV.QuantIds(r2) && (q2 as int) in Q ensures NRR.QidCinPlus(r2, q2) {
          assert q2 !in PIV.QuantIds(r1) by { if q2 in PIV.QuantIds(r1) { assert q2 in PIV.QuantIds(r1) * PIV.QuantIds(r2); } }
          assert q2 in PIV.QuantIds(r) && NRR.QidCinPlus(r, q2);
        }
      }
      LooksQEmpty(r1, Q); LooksQEmpty(r2, Q);
    case Re_con(r1, r2) =>
      assert QInCin(r1, Q) by {
        forall q2: nat | q2 in PIV.QuantIds(r1) && (q2 as int) in Q ensures NRR.QidCinPlus(r1, q2) {
          assert q2 in PIV.QuantIds(r) && NRR.QidCinPlus(r, q2);
        }
      }
      assert QInCin(r2, Q) by {
        forall q2: nat | q2 in PIV.QuantIds(r2) && (q2 as int) in Q ensures NRR.QidCinPlus(r2, q2) {
          assert q2 !in PIV.QuantIds(r1) by { if q2 in PIV.QuantIds(r1) { assert q2 in PIV.QuantIds(r1) * PIV.QuantIds(r2); } }
          assert q2 in PIV.QuantIds(r) && NRR.QidCinPlus(r, q2);
        }
      }
      LooksQEmpty(r1, Q); LooksQEmpty(r2, Q);
    case Re_quant(nul, qid, q, body) =>
      assert QInCin(body, Q) by {
        forall q2: nat | q2 in PIV.QuantIds(body) && (q2 as int) in Q ensures NRR.QidCinPlus(body, q2) {
          assert q2 in PIV.QuantIds(r);
          assert !(qid >= 0 && (qid as nat) == q2);   // QuantUnique: the node's id is not in its body
        }
      }
      LooksQEmpty(body, Q);
      if qid in Q {
        assert qid >= 0 && (qid as nat) in PIV.QuantIds(r);
        assert NRR.QidCinPlus(r, qid as nat);
        LookFreeNoLookRegs(body);
      }
    case Re_capture(_, r1) =>
      assert QInCin(r1, Q) by {
        forall q2: nat | q2 in PIV.QuantIds(r1) && (q2 as int) in Q ensures NRR.QidCinPlus(r1, q2) {
          assert q2 in PIV.QuantIds(r) && NRR.QidCinPlus(r, q2);
        }
      }
      LooksQEmpty(r1, Q);
    case _ =>
  }
}
