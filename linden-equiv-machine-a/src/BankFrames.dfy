// (G3a, moved down from main-cin-lk) Register-bank frames shared by the tie transports
// and the readout at a fresh look-body winner (A3). Names nothing from main-theorem.
module LindenElkBankFrames {
  import R = RegElkRegex
  import CP = Compiler
  import AI = ArrayInterp
  import AReg = Array_Regs
  import LTB = LindenElkLookTables
  import PIV = LindenElkPikeInv
  import PSM = LindenElkPikeSim
  import CM = LindenElkClockMono
  import NI = LindenElkNestInv
  import NRC = LindenElkNulledRecon
  import NRR = LindenElkNulledReconRegs
  import FRD = LindenElkFinalReadout
  import RF = LindenElkReconFrame
  import CLP = LindenElkCinLookPaths

  /** The register frame the transport needs: look registers equal, capture and
      quant CLOCKS equal outside the reconstruction's write sets. */
  ghost predicate ClkFrame(re: R.regex, Q: set<int>, a: AI.Thread, b: AI.Thread) {
    a.look_regs == b.look_regs
    && (forall k :: k !in RF.CapsQ(re, Q) ==> AI.get_idx(a.capture_regs.a_clk, k) == AI.get_idx(b.capture_regs.a_clk, k))
    && (forall k :: k !in RF.QuantsQ(re, Q) ==> AI.get_idx(a.quant_regs.a_clk, k) == AI.get_idx(b.quant_regs.a_clk, k))
  }
  lemma AncFrame(re: R.regex, Q: set<int>, a: AI.Thread, b: AI.Thread, lid: nat)
    requires lid in LTB.LookIds(re)
    requires RF.CinBodiesLookFreeRE(re) && PIV.CapUnique(re) && PIV.QuantUnique(re) && RF.QInCin(re, Q)
    requires ClkFrame(re, Q, a, b)
    ensures forall mx :: NI.LookPathPresent(re, a.capture_regs.a_clk, a.quant_regs.a_clk, mx, lid)
                         == NI.LookPathPresent(re, b.capture_regs.a_clk, b.quant_regs.a_clk, mx, lid)
    ensures forall mx :: NI.MxAtLidLk(re, a.quant_regs.a_clk, mx, lid) == NI.MxAtLidLk(re, b.quant_regs.a_clk, mx, lid)
    ensures forall L :: NI.LookPathDom(re, L, a.quant_regs.a_clk, lid) == NI.LookPathDom(re, L, b.quant_regs.a_clk, lid)
  {
    CLP.AncAvoidQ(re, Q, lid);
    var cc1 := a.capture_regs.a_clk;
    var cc2 := b.capture_regs.a_clk;
    var qc1 := a.quant_regs.a_clk;
    var qc2 := b.quant_regs.a_clk;
    assert forall k :: k in CLP.AncCapRegs(re, lid) ==> AI.get_idx(cc1, k) == AI.get_idx(cc2, k) by {
      forall k | k in CLP.AncCapRegs(re, lid) ensures AI.get_idx(cc1, k) == AI.get_idx(cc2, k) {
        if k in RF.CapsQ(re, Q) { assert k in CLP.AncCapRegs(re, lid) * RF.CapsQ(re, Q); }
      }
    }
    assert forall k :: k in CLP.AncQuants(re, lid) ==> AI.get_idx(qc1, k) == AI.get_idx(qc2, k) by {
      forall k | k in CLP.AncQuants(re, lid) ensures AI.get_idx(qc1, k) == AI.get_idx(qc2, k) {
        if k in RF.QuantsQ(re, Q) { assert k in CLP.AncQuants(re, lid) * RF.QuantsQ(re, Q); }
      }
    }
    forall mx ensures NI.LookPathPresent(re, cc1, qc1, mx, lid) == NI.LookPathPresent(re, cc2, qc2, mx, lid)
                      && NI.MxAtLidLk(re, qc1, mx, lid) == NI.MxAtLidLk(re, qc2, mx, lid) {
      CLP.LookPathFrame(re, cc1, qc1, cc2, qc2, mx, lid);
    }
    forall L ensures NI.LookPathDom(re, L, qc1, lid) == NI.LookPathDom(re, L, qc2, lid) {
      CLP.LookPathDomFrame(re, L, qc1, qc2, lid);
    }
  }
  lemma QInCinQ(re: R.regex)
    ensures RF.QInCin(re, FRD.CinQids(re))
  {
    forall q: nat | q in PIV.QuantIds(re) && (q as int) in FRD.CinQids(re) ensures NRR.QidCinPlus(re, q) {
      var qn: nat :| qn in PIV.QuantIds(re) && NRR.QidCinPlus(re, qn) && qn as int == q as int;
      assert qn == q;
    }
  }
  lemma NRRLookIdsEq(r: R.regex)
    ensures NRR.LookIds(r) == LTB.LookIds(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => NRRLookIdsEq(r1); NRRLookIdsEq(r2);
    case Re_con(r1, r2) => NRRLookIdsEq(r1); NRRLookIdsEq(r2);
    case Re_quant(_, _, _, r1) => NRRLookIdsEq(r1);
    case Re_capture(_, r1) => NRRLookIdsEq(r1);
    case Re_lookaround(_, _, r1) => NRRLookIdsEq(r1);
    case _ =>
  }
  /** The bank sizes cover every id of `body`: the `>=` twin of `MainCinLk.CoversAll`, whose `==` sizes
      hold only at the top regex. A look body runs on the top regex's banks. */
  ghost predicate SizesCover(body: R.regex, ncap: int, nlook: int, nquant: int) {
    (forall c: nat :: c in PIV.CapIds(body) ==> CP.end_reg(c) < ncap)
    && (forall l: nat :: l in LTB.LookIds(body) ==> l < nlook)
    && (forall q: nat :: q in PIV.QuantIds(body) ==> q < nquant)
  }
  /** What callers hold: `PSM.SizesOkRE(body, …)` bounds captures and quantifiers; the look bound comes
      from the enclosing regex (`LTB.LookIdsLeMax`), since `SizesOkRE` says only `nlook >= 0`. */
  lemma SizesCoverFromOk(body: R.regex, ncap: int, nlook: int, nquant: int)
    requires PSM.SizesOkRE(body, ncap, nlook, nquant)
    requires forall l: nat :: l in LTB.LookIds(body) ==> l < nlook
    ensures SizesCover(body, ncap, nlook, nquant)
  {
    NI.CapIdsLEMaxGroup(body);
    NI.QuantIdsLEMaxQuant(body);
  }
  lemma CoversFromSizes(body: R.regex, rg: NRC.Regs3, ncap: int, nlook: int, nquant: int)
    requires SizesCover(body, ncap, nlook, nquant)
    requires |rg.0.a_cp| == ncap && |rg.1.a_cp| == nlook && |rg.2.a_cp| == nquant
    ensures NRR.Covers(body, rg)
  {
    NRRLookIdsEq(body);
  }
  /** The outside-look capture-write frame, read off at start registers. */
  lemma OnlyCapIdsFromFrameOuter(re: R.regex, caps: AReg.Regs, ncap: int)
    requires CM.RegsAgreeOutside(caps, AReg.init_regs(ncap), PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(re)))
    ensures forall gid: nat :: gid !in PIV.CapIds(re) ==> AI.get_idx(caps.a_cp, CP.start_reg(gid)) < 0
  {
    var capture := AReg.init_regs(ncap);
    var Sreg := PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(re));
    PIV.CapIdsSplit(re);
    forall gid: nat | gid !in PIV.CapIds(re) ensures AI.get_idx(caps.a_cp, CP.start_reg(gid)) < 0 {
      var k := CP.start_reg(gid);
      assert k !in Sreg by {
        if k in Sreg {
          if k in (set cid | cid in PIV.CapIdsOutsideLooks(re) :: CP.start_reg(cid)) {
            var c :| c in PIV.CapIdsOutsideLooks(re) && CP.start_reg(c) == k;
            assert c == gid;
          } else {
            var c :| c in PIV.CapIdsOutsideLooks(re) && CP.end_reg(c) == k;
            assert 2 * c + 1 == 2 * gid;
          }
        }
      }
      assert AI.get_idx(caps.a_cp, k) == AI.get_idx(capture.a_cp, k);
      if 0 <= k < |capture.a_cp| { assert capture.a_cp[k] == -1; }
    }
  }}
