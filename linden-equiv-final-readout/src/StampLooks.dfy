// (G5b-3) The reconstruction's look set at a stamp body whose looks capture nothing (moved down from main-cin-lk's
// G4a `CinLooks.dfy`, re-keyed on `RF.StampLooksCapFreeRE`): a lid the reconstruction may re-set (`RF.LooksQ`) has a
// capture-free body, and every other lid keeps its ancestors' registers. Valid at the top regex and at a look row.
module LindenElkStampLooks {
  import opened Std.Wrappers
  import R = RegElkRegex
  import CP = Compiler
  import PIV = LindenElkPikeInv
  import NI = LindenElkNestInv
  import LTB = LindenElkLookTables
  import NRR = LindenElkNulledReconRegs
  import RF = LindenElkReconFrame
  import CLP = LindenElkCinLookPaths
  import FRD = LindenElkFinalReadout

  lemma LooksQInIds(r: R.regex, Q: set<int>, lid: nat)
    requires LTB.LookUnique(r) && (lid as int) in RF.LooksQ(r, Q)
    ensures lid in LTB.LookIds(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      if (lid as int) in RF.LooksQ(r1, Q) { LooksQInIds(r1, Q, lid); } else { LooksQInIds(r2, Q, lid); }
    case Re_con(r1, r2) =>
      if (lid as int) in RF.LooksQ(r1, Q) { LooksQInIds(r1, Q, lid); } else { LooksQInIds(r2, Q, lid); }
    case Re_quant(_, qid, _, body) =>
      if (lid as int) in RF.LooksQ(body, Q) {
        LooksQInIds(body, Q, lid);
      } else {
        FRD.LookRegsOfIds(body);
        var x: nat :| x in LTB.LookIds(body) && x as int == lid as int;
        assert x == lid;
      }
    case Re_capture(_, r1) => LooksQInIds(r1, Q, lid);
    case _ =>
  }

  /** A lid the reconstruction may re-set lies in a capture-free look body. */
  lemma LooksQCapFree(r: R.regex, Q: set<int>, lid: nat)
    requires lid in LTB.LookIds(r) && (lid as int) in RF.LooksQ(r, Q)
    requires RF.StampLooksCapFreeRE(r) && PIV.QuantUnique(r) && LTB.LookUnique(r) && RF.QInStamp(r, Q)
    ensures PIV.CapIds(NI.LookBodyOfRE(r, lid)) == {}
    decreases r
  {
    CLP.QInStampDown(r, Q);
    match r
    case Re_alt(r1, r2) =>
      assert NRR.L1(r) == r1 && NRR.L2(r) == r2;
      if (lid as int) in RF.LooksQ(r1, Q) {
        LooksQInIds(r1, Q, lid);
        LooksQCapFree(r1, Q, lid);
      } else {
        LooksQInIds(r2, Q, lid);
        assert lid !in LTB.LookIds(r1) by { if lid in LTB.LookIds(r1) { assert lid in LTB.LookIds(r1) * LTB.LookIds(r2); } }
        LooksQCapFree(r2, Q, lid);
      }
    case Re_con(r1, r2) =>
      assert NRR.L1(r) == r1 && NRR.L2(r) == r2;
      if (lid as int) in RF.LooksQ(r1, Q) {
        LooksQInIds(r1, Q, lid);
        LooksQCapFree(r1, Q, lid);
      } else {
        LooksQInIds(r2, Q, lid);
        assert lid !in LTB.LookIds(r1) by { if lid in LTB.LookIds(r1) { assert lid in LTB.LookIds(r1) * LTB.LookIds(r2); } }
        LooksQCapFree(r2, Q, lid);
      }
    case Re_quant(nul, qid, q, body) =>
      assert NRR.L1(r) == body;
      if (lid as int) in RF.LooksQ(body, Q) {
        LooksQInIds(body, Q, lid);
        LooksQCapFree(body, Q, lid);
      } else {
        assert qid in Q && (lid as int) in NRR.LookRegsOf(body);
        assert qid >= 0 && (qid as nat) in PIV.QuantIds(r);
        assert NRR.QidStampPlus(r, qid as nat);
        assert q.min != 0 && q.max == None && nul != R.NonNullable && q.greedy;
        LooksQInIds(r, Q, lid);
        assert lid in LTB.LookIds(body);
        assert PIV.CapIdsInLooks(body) == {};   // `RF.StampLooksCapFreeRE`, CIN or CDN
        NI.LookBodyCapsIn(body, lid);
        assert NI.LookBodyOfRE(r, lid) == NI.LookBodyOfRE(body, lid);
      }
    case Re_capture(_, r1) =>
      assert NRR.L1(r) == r1;
      LooksQCapFree(r1, Q, lid);
    case _ =>
  }

  /** `CLP.AncAvoidQS` for a lid the reconstruction leaves alone: no scope condition needed. */
  lemma AncAvoidQG4(r: R.regex, Q: set<int>, lid: nat)
    requires lid in LTB.LookIds(r) && (lid as int) !in RF.LooksQ(r, Q)
    requires PIV.CapUnique(r) && PIV.QuantUnique(r) && LTB.LookUnique(r) && RF.QInStamp(r, Q)
    ensures CLP.AncCapRegs(r, lid) * RF.CapsQ(r, Q) == {}
    ensures CLP.AncQuants(r, lid) * RF.QuantsQ(r, Q) == {}
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      CLP.QInStampLeft(r, r1, r2, Q);
      NRR.DisjointRegs(r);
      assert NRR.L1(r) == r1 && NRR.L2(r) == r2;
      RF.QSetsSub(r1, Q); RF.QSetsSub(r2, Q);
      if lid in LTB.LookIds(r1) { AncAvoidQG4(r1, Q, lid); CLP.AncSub(r1, lid); }
      else { AncAvoidQG4(r2, Q, lid); CLP.AncSub(r2, lid); }
    case Re_con(r1, r2) =>
      CLP.QInStampLeft(r, r1, r2, Q);
      NRR.DisjointRegs(r);
      assert NRR.L1(r) == r1 && NRR.L2(r) == r2;
      RF.QSetsSub(r1, Q); RF.QSetsSub(r2, Q);
      if lid in LTB.LookIds(r1) { AncAvoidQG4(r1, Q, lid); CLP.AncSub(r1, lid); }
      else { AncAvoidQG4(r2, Q, lid); CLP.AncSub(r2, lid); }
    case Re_quant(nul, qid, q, body) =>
      assert RF.QInStamp(body, Q) by {
        forall q2: nat | q2 in PIV.QuantIds(body) && (q2 as int) in Q ensures NRR.QidStampPlus(body, q2) {
          assert q2 in PIV.QuantIds(r);
          assert !(qid >= 0 && (qid as nat) == q2);
        }
      }
      assert (qid as int) !in Q by {
        if (qid as int) in Q {   // then every look of the body is in the look set
          FRD.LookRegsOfIds(body);
          assert (lid as int) in NRR.LookRegsOf(body);
          assert (lid as int) in RF.LooksQ(r, Q);
        }
      }
      AncAvoidQG4(body, Q, lid);
      RF.QSetsSub(body, Q);
      NRR.QuantRegsOfChar(body);
      assert (qid as int) !in RF.QuantsQ(body, Q);
    case Re_capture(cid, r1) =>
      assert RF.QInStamp(r1, Q) by {
        forall q2: nat | q2 in PIV.QuantIds(r1) && (q2 as int) in Q ensures NRR.QidStampPlus(r1, q2) {
          assert q2 in PIV.QuantIds(r) && NRR.QidStampPlus(r, q2);
        }
      }
      AncAvoidQG4(r1, Q, lid);
      RF.QSetsSub(r1, Q);
      NRR.CapRegsOfOwn(r);
      assert NRR.L1(r) == r1;
      assert CP.start_reg(cid) !in RF.CapsQ(r1, Q);
    case Re_lookaround(lid0, _, r1) =>
    case _ =>
  }

  /** The capture half of `CLP.QsOutsideS` under the stamp scope (the quant half fails when a look body inside a
      CIN body has a quantifier, `((?=a*)b?)+`). */
  lemma CapsQOutside(r: R.regex, Q: set<int>)
    requires RF.StampLooksCapFreeRE(r) && PIV.CapUnique(r) && PIV.QuantUnique(r) && RF.QInStamp(r, Q)
    ensures RF.CapsQ(r, Q) <= PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(r))
    decreases r
  {
    CLP.QInStampDown(r, Q);
    match r
    case Re_alt(r1, r2) =>
      CapsQOutside(r1, Q); CapsQOutside(r2, Q);
      PIV.CaptureRegsSetMono(PIV.CapIdsOutsideLooks(r1), PIV.CapIdsOutsideLooks(r));
      PIV.CaptureRegsSetMono(PIV.CapIdsOutsideLooks(r2), PIV.CapIdsOutsideLooks(r));
    case Re_con(r1, r2) =>
      CapsQOutside(r1, Q); CapsQOutside(r2, Q);
      PIV.CaptureRegsSetMono(PIV.CapIdsOutsideLooks(r1), PIV.CapIdsOutsideLooks(r));
      PIV.CaptureRegsSetMono(PIV.CapIdsOutsideLooks(r2), PIV.CapIdsOutsideLooks(r));
    case Re_capture(cid, r1) =>
      CapsQOutside(r1, Q);
      PIV.CaptureRegsSetMono(PIV.CapIdsOutsideLooks(r1), PIV.CapIdsOutsideLooks(r));
    case Re_quant(nul, qid, q, body) =>
      CapsQOutside(body, Q);
      assert PIV.CapIdsOutsideLooks(r) == PIV.CapIdsOutsideLooks(body);
      if qid in Q {
        assert qid >= 0 && (qid as nat) in PIV.QuantIds(r);
        assert NRR.QidStampPlus(r, qid as nat);
        assert q.min != 0 && q.max == None && nul != R.NonNullable && q.greedy;
        assert PIV.CapIdsInLooks(body) == {};   // `RF.StampLooksCapFreeRE`, CIN or CDN
        PIV.CapIdsSplit(body);
        NRR.CapRegsOfChar(body);
        forall k | k in NRR.CapRegsOf(body) ensures k in PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(r)) {
          var c: nat :| c in PIV.CapIds(body) && (k == CP.start_reg(c) || k == CP.end_reg(c));
          assert c in PIV.CapIdsOutsideLooks(r);
          if k == CP.start_reg(c) {
            assert k in (set cid | cid in PIV.CapIdsOutsideLooks(r) :: CP.start_reg(cid));
          } else {
            assert k in (set cid | cid in PIV.CapIdsOutsideLooks(r) :: CP.end_reg(cid));
          }
        }
      }
    case Re_lookaround(_, _, _) =>
    case _ =>
  }

  /** The capture half of `CLP.QsAvoidLookBodyS` under the stamp scope. */
  lemma CapsQAvoidLookBody(r: R.regex, Q: set<int>, lid: nat)
    requires lid in LTB.LookIds(r)
    requires RF.StampLooksCapFreeRE(r) && PIV.CapUnique(r) && PIV.QuantUnique(r) && RF.QInStamp(r, Q)
    ensures RF.CapsQ(r, Q) * PIV.CaptureRegs(NI.LookBodyOfRE(r, lid)) == {}
  {
    var b := NI.LookBodyOfRE(r, lid);
    CapsQOutside(r, Q);
    NI.LookBodyCapsIn(r, lid);
    PIV.CaptureRegsIsSet(b);
    PIV.CaptureRegsSetMono(PIV.CapIds(b), PIV.CapIdsInLooks(r));
    PIV.CapIdsLooksDisjoint(r);
    PIV.CaptureRegsSetDisjoint(PIV.CapIdsOutsideLooks(r), PIV.CapIdsInLooks(r));
  }

}
