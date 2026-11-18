// (G5b-3) The reconstruction's look set (moved down from main-cin-lk's G4a `CinLooks.dfy`): a lid outside `RF.LooksQ`
// keeps its ancestors' registers (scope-free). (G4b-1) The capture-free half moved to `EmptyLooks.dfy` on the sharper
// set `ELk.LooksQE` (`ELk.CapsQOOutside`). Valid at the top regex and at a look row.
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
}
