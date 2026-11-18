// (G4a, G4b-1) The frame facts at the reconstructed top winner: the reconstruction's look set at the stamped set,
// the ancestor frame, and the clock frame `ClkFrameG4`. (G4b-2) The capture-free scope that once lived here
// (`CinLooksCapFreeRE` and its executable twins) is gone: a nullable plus body's looks may capture, on its empty
// paths too. Design: linden-equiv/endgame/G4a-design.md, G4b-design.md.
module LindenElkCinLooks {
  import opened Std.Wrappers
  import R = RegElkRegex
  import L = Regex
  import LG = Groups
  import LT = Tree
  import AI = ArrayInterp
  import AReg = Array_Regs
  import CP = Compiler
  import LOr = Oracle
  import LW = WarblreRegExpRecord
  import T = LindenElkTranslate
  import NR = LindenElkNfaRep
  import NUL = LindenElkNullable
  import PIV = LindenElkPikeInv
  import NI = LindenElkNestInv
  import LTB = LindenElkLookTables
  import LL = LindenElkLookLeaves
  import CW = LindenElkCinWalk
  import M = LindenElkMain
  import NRR = LindenElkNulledReconRegs
  import NRC = LindenElkNulledRecon
  import RF = LindenElkReconFrame
  import CLP = LindenElkCinLookPaths
  import FRD = LindenElkFinalReadout
  import TM = LindenElkTwoMachines
  import ELk = LindenElkEmptyLooks
  import NPL = LindenElkNulledPlusLk
  import PSM = LindenElkPikeSim
  import SL = LindenElkStampLive
  import opened LindenElkLiftSimCore
  import opened LindenElkLiftSimOracle

  // =========================================================================
  // 3. (G4b-1) The reconstruction's look set at the stamped set, and the ancestor frame.
  // =========================================================================

  /** The capture half of `CLP.QsAvoidLookBodyS`: the reconstruction writes no capture inside a look (scope-free). */
  lemma CapsQAvoidLookBody(r: R.regex, Q: set<int>, lid: nat)
    requires lid in LTB.LookIds(r) && PIV.CapUnique(r)
    ensures ELk.CapsQO(r, Q) * PIV.CaptureRegs(NI.LookBodyOfRE(r, lid)) == {}
  {
    var b := NI.LookBodyOfRE(r, lid);
    ELk.CapsQOOutside(r, Q);
    NI.LookBodyCapsIn(r, lid);
    PIV.CaptureRegsIsSet(b);
    PIV.CaptureRegsSetMono(PIV.CapIds(b), PIV.CapIdsInLooks(r));
    PIV.CapIdsLooksDisjoint(r);
    PIV.CaptureRegsSetDisjoint(PIV.CapIdsOutsideLooks(r), PIV.CapIdsInLooks(r));
  }

  /** The stamp-liveness facts of the winner at its stamped set. */
  lemma BodyStaleAtStamps(re: R.regex, best: AI.Thread, Q: set<int>)
    requires PSM.BestLiveRE(re, best) && Q == ELk.StampSet(best.quant_regs.a_cp)
    ensures forall q: nat :: q in PIV.QuantIds(re) && (q as int) in Q ==>
              SL.BodyStale(PIV.QidBody(re, q), best.capture_regs.a_clk, best.quant_regs.a_clk,
                           AI.get_idx(best.quant_regs.a_clk, q))
  {
    reveal PSM.BestLiveRE();
    forall q: nat | q in PIV.QuantIds(re) && (q as int) in Q
      ensures SL.BodyStale(PIV.QidBody(re, q), best.capture_regs.a_clk, best.quant_regs.a_clk,
                           AI.get_idx(best.quant_regs.a_clk, q))
    {
      assert AI.get_idx(best.quant_regs.a_cp, q) >= 0;
      SL.StampLiveAt(re, best.capture_regs.a_clk, best.quant_regs.a_clk, best.quant_regs.a_cp, q);
    }
  }

  // =========================================================================
  // 4. The frame at the reconstructed winner and the tie transports.
  // =========================================================================

  /** (G4b-1) The frame of the reconstruction at the stamped set `Q`: the look bank equal outside `ELk.LooksQE`, the
      capture clocks outside `ELk.CapsQO`, the quant clocks outside `RF.QuantsQ`, and every quant clock only rose. */
  ghost predicate ClkFrameG4(re: R.regex, Q: set<int>, a: AI.Thread, b: AI.Thread) {
    |a.look_regs.a_cp| == |b.look_regs.a_cp|
    && (forall k :: k !in ELk.LooksQE(re, Q) ==>
          AI.get_idx(a.look_regs.a_cp, k) == AI.get_idx(b.look_regs.a_cp, k)
          && AI.get_idx(a.look_regs.a_clk, k) == AI.get_idx(b.look_regs.a_clk, k))
    && (forall k :: k !in ELk.CapsQO(re, Q) ==> AI.get_idx(a.capture_regs.a_clk, k) == AI.get_idx(b.capture_regs.a_clk, k))
    && (forall k :: k !in RF.QuantsQ(re, Q) ==> AI.get_idx(a.quant_regs.a_clk, k) == AI.get_idx(b.quant_regs.a_clk, k))
    && ELk.QClkGe(a.quant_regs, b.quant_regs.a_clk)
  }

  /** A lid whose ancestors avoid the stamped bodies keeps its path facts. */
  lemma AncFrameAvoid(re: R.regex, Q: set<int>, a: AI.Thread, b: AI.Thread, lid: nat)
    requires lid in LTB.LookIds(re)
    requires CLP.AncCapRegs(re, lid) * RF.CapsQ(re, Q) == {} && CLP.AncQuants(re, lid) * RF.QuantsQ(re, Q) == {}
    requires ClkFrameG4(re, Q, a, b)
    ensures forall mx :: NI.LookPathPresent(re, a.capture_regs.a_clk, a.quant_regs.a_clk, mx, lid)
                         == NI.LookPathPresent(re, b.capture_regs.a_clk, b.quant_regs.a_clk, mx, lid)
    ensures forall mx :: NI.MxAtLidLk(re, a.quant_regs.a_clk, mx, lid) == NI.MxAtLidLk(re, b.quant_regs.a_clk, mx, lid)
  {
    ELk.CapsOSub(re, Q);
    var cc1 := a.capture_regs.a_clk;
    var cc2 := b.capture_regs.a_clk;
    var qc1 := a.quant_regs.a_clk;
    var qc2 := b.quant_regs.a_clk;
    assert forall k :: k in CLP.AncCapRegs(re, lid) ==> AI.get_idx(cc1, k) == AI.get_idx(cc2, k) by {
      forall k | k in CLP.AncCapRegs(re, lid) ensures AI.get_idx(cc1, k) == AI.get_idx(cc2, k) {
        if k in ELk.CapsQO(re, Q) { assert k in CLP.AncCapRegs(re, lid) * RF.CapsQ(re, Q); }
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
  }

  /** The three readers of a look record see only `get_cp(lk, l)`. */
  lemma GetCpCong(a: AReg.Regs, b: AReg.Regs, l: int)
    requires |a.a_cp| == |b.a_cp| && AI.get_idx(a.a_cp, l) == AI.get_idx(b.a_cp, l)
    ensures AReg.get_cp(a, l) == AReg.get_cp(b, l)
  {}

  lemma FreshBodyCong(crv: CP.FCompiled, str: string, l: int, a: AReg.Regs, b: AReg.Regs,
                      ov: LOr.OracleView, ncap: int, nlook: int, nquant: int)
    requires AReg.get_cp(a, l) == AReg.get_cp(b, l)
    ensures M.FreshBodyMatchPlus(crv, str, l, a, ov, ncap, nlook, nquant)
            == M.FreshBodyMatchPlus(crv, str, l, b, ov, ncap, nlook, nquant)
  {
    reveal M.FreshBodyMatchPlus();
  }

  lemma SubFirstLeafCong(rer: LW.RegExpRecord, crv: CP.FCompiled, str: string, l: int, a: AReg.Regs, b: AReg.Regs)
    requires AReg.get_cp(a, l) == AReg.get_cp(b, l)
    ensures SubFirstLeafAt(rer, crv, str, l, a) == SubFirstLeafAt(rer, crv, str, l, b)
  {}




}
