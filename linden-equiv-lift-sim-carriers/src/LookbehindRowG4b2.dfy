// (G4b-2, item (b)) The LOOKBEHIND row on the four-case transports.
//   1. `LR.WinnerLookRec` is order-free: it crosses the flip (`WinnerLookRecFlip`; `PathLooksR` is a set,
//      `PathLooksRMirror`).
//   2. The real backward row's look record (the backward reconstruction IS the forward one, `DB`), flipped:
//      `BackRowLookRecFlip` — what `T4.TieOkTTransportG4b2` / `T4.TieConvTransportG4b2P` read at the flip site.
//   3. The presence-premised converses come back through the flip per lid (`FlipBackP`): the per-lid flip lemmas
//      take the flipped Dom carrier of a thread, so they run on the SOLO thread (every other look record unset),
//      whose Dom carrier is the P carrier's instance at the lid.
module LindenElkLookbehindRowG4b2 {
  import opened Std.Wrappers
  import R = RegElkRegex
  import RB = Bytecode
  import CP = Compiler
  import NR = LindenElkNfaRep
  import AI = ArrayInterp
  import AReg = Array_Regs
  import LG = Groups
  import LT = Tree
  import LC = Chars
  import L = Regex
  import LS = Semantics
  import BS = BooleanSemantics
  import WP = WarblrePrimitives
  import LW = WarblreRegExpRecord
  import LOr = Oracle
  import LAnc = Anchors
  import LCdn = Cdn
  import PT = PikeTree
  import SS = SeenSets
  import AR = LindenElkActionsRep
  import EL = LindenElkEntryLk
  import WO = LindenElkWalkOk
  import ATR = LindenElkActionsTreeRep
  import NP = LindenElkNulledPlus
  import NB = LindenElkNulledPlusBool
  import PIV = LindenElkPikeInv
  import CM = LindenElkClockMono
  import PTL = LindenElkPikeTreeLk
  import M = LindenElkMain
  import LBK = LindenLookBehindKeystone
  import FG = LindenElkFlipGate
  import FC = LindenElkFlipClosed
  import FST = LindenElkFlipStatics
  import FK = LindenElkFlipKeystone
  import FO = LindenElkFlipOracle
  import FD = LindenElkFlipDisc
  import FM = LindenElkFlipMirror
  import FR = LindenElkFlipRev
  import TRM = LindenTreeResMirror
  import BGM = LindenBackGmMirror
  import LBV = LindenLookBehindValue
  import BV = LindenElkBackValue
  import SD = LindenSpanDuality
  import CD = LindenCloseDisc
  import OS = LindenElkOracleSpec
  import OB = LindenElkOracleBuild
  import OBr = LindenElkOracleBridge
  import ORc = LindenElkOracleReach
  import MIR = LindenElkMirror
  import OBV = LindenElkOracleBridgeV
  import ODV = LindenElkOracleDecompV
  import OAV = LindenElkOracleAcceptV
  import OMV = LindenElkOracleMirrorV
  import T = LindenElkTranslate
  import RC = Charclasses
  import LL = LindenElkLookLeaves
  import LFU = FunctionalUtils
  import FS = FunctionalSemantics
  import SSx = StrictSuffix
  import LN = WarblreNumeric
  import PSM = LindenElkPikeSim
  import RL = LindenElkRegsLaws
  import LKC = LindenElkLookCapture
  import OE = LindenElkOracleEntry
  import LES = LindenElkSpec
  import WOE = LindenElkWalkOkEntry
  import WkE = LindenElkWalkOkEntry
  import TT = LindenElkTreeThread
  import NUL = LindenElkNullable
  import CE = LindenElkCheckErase
  import TREP = LindenElkTreeRep
  import LTB = LindenElkLookTables
  import NI = LindenElkNestInv
  import opened LindenElkLiftSimCore
  import opened LindenElkLiftSimOracle
  import opened LindenElkLiftSimChain
  import opened LindenElkLiftSimGate
  import GG = LindenElkFlipGateG         // (gate B) flip-gate F6, scope-free
  import KG = LindenElkFlipKeystoneG     // (gate B) keystone, scope-free
  import OG = LindenElkFlipOracleG       // (gate B) generic F2/F3
  import G = LindenElkFlipMirrorG        // (gate B) generic tree mirror
  import NRR = LindenElkNulledReconRegs  // (G3a) the plus table
  import NRC = LindenElkNulledRecon      // (G3a) NoCdnPlusRE
  import RF = LindenElkReconFrame        // (G3a) CinBodiesLookFreeRE
  import TM = LindenElkTwoMachines       // (G3a) A6, TranslateCinOk
  import CG = LindenElkCdnGuards         // (G5b-1) N1 at a lookahead row
  import TB = LindenElkMirrorPlus        // (G3b)
  import RP = LindenElkMachineABack      // (G3b)
  import BRG = LindenElkBackRowGate      // (G3b)
  import BRS = LindenElkBackRowStatics   // (G3b)
  import MW = LindenElkMirrorWorld       // (G5b-2) SwapRunIsOwnRunPlus
  import ELk = LindenElkEmptyLooks       // (G4b-1b) the stamped set
  import FRD = LindenElkFinalReadout     // (G3b)
  import FRA = LindenElkFinalReadoutAt   // (G3b)
  import BF = LindenElkBankFrames        // (G3b)
  import W = LindenElkBackRowResidue     // (G3b)
  import FV = LindenElkFinalVm
  import FRG = LindenElkFinalRegs
  import SM = LindenElkStampMirror
  import DB = LindenElkDirBlind
  import WR = LindenElkBackRowPremises
  import LR = LindenElkLookRecord
  import SLS = LindenElkStampLookSite
  import T4 = LindenElkTransportsG4b2

  // ===========================================================================
  // 1. The look record crosses the flip.
  // ===========================================================================

  /** The positive lids on the first empty path are the flipped body's at the mirrored position. */
  lemma PathLooksRMirror(qm: AR.QMap, qmF: AR.QMap, re: R.regex, str: string, cp: nat)
    requires T.TransWf(re) && PIV.CapUnique(re)
    requires cp <= |str| && |qm.ov| == |str| + 1 && qmF.ov == MIR.MirrorView(qm.ov, |str|)
    ensures T.TransWf(FST.FXR(re)) && |LC.Reverse(str)| == |str|
    ensures LR.PathLooksR(qmF, FST.FXR(re), T.InputAt(LC.Reverse(str), |str| - cp))
            == LR.PathLooksR(qm, re, T.InputAt(str, cp))
    decreases re
  {
    SM.FirstEmptyPathMirror(qm, qmF, re, str, cp, LG.Empty);
    match re
    case Re_alt(r1, r2) =>
      W.FXRAlt(r1, r2);
      SM.FirstEmptyPathMirror(qm, qmF, r1, str, cp, LG.Empty);
      PathLooksRMirror(qm, qmF, r1, str, cp); PathLooksRMirror(qm, qmF, r2, str, cp);
    case Re_con(r1, r2) =>
      W.FXRCon(r1, r2);
      PathLooksRMirror(qm, qmF, r1, str, cp); PathLooksRMirror(qm, qmF, r2, str, cp);
    case Re_quant(nul, qid, q, r1) => W.FXRQuant(nul, qid, q, r1); PathLooksRMirror(qm, qmF, r1, str, cp);
    case Re_capture(cid, r1) => W.FXRCap(cid, r1); PathLooksRMirror(qm, qmF, r1, str, cp);
    case Re_lookaround(lid, la, r1) => W.FXRLook(lid, la, r1);
    case Re_anchor(x) => W.FXRAnchor(x);
    case Re_empty =>
    case Re_character(_) =>
  }

  /** One (q, l) instance of the flipped record. */
  lemma WinnerLookRecFlipAt(qm: AR.QMap, qmF: AR.QMap, body: R.regex, str: string, best: AI.Thread, rp: AI.Thread,
                            q: nat, l: nat)
    requires |qm.ov| == |str| + 1 && qmF.ov == MIR.MirrorView(qm.ov, |str|)
    requires T.TransWf(body) && PIV.CapUnique(body) && PIV.QuantUnique(body) && LTB.LookUnique(body)
    requires LR.WinnerLookRec(qm, body, str, best, rp)
    requires q in PIV.QuantIds(FST.FXR(body))
    requires PIV.QLive(FST.FXR(body), MIR.MirrorThread(best, |str|).quant_regs.a_clk,
                       MIR.MirrorThread(best, |str|).quant_regs.a_cp, q)
    requires l in NI.TopLookIds(PIV.QidBody(FST.FXR(body), q)) && l in LTB.LookIds(PIV.QidBody(FST.FXR(body), q))
    ensures var reF := FST.FXR(body); var rstr := LC.Reverse(str);
            var bestF := MIR.MirrorThread(best, |str|); var rpF := MIR.MirrorThread(rp, |str|);
            var cp := AI.get_idx(bestF.quant_regs.a_cp, q);
            var K := AI.get_idx(bestF.quant_regs.a_clk, q);
            0 <= cp <= |rstr| && T.TransWf(PIV.QidBody(reF, q)) && l in LTB.LookIds(reF)
            && AI.get_idx(rpF.quant_regs.a_clk, q) == K && AI.get_idx(rpF.quant_regs.a_cp, q) == cp
            && PIV.QChainFresh(reF, rpF.quant_regs.a_clk, -1, q)
            && PIV.PathPresentQ(reF, rpF.capture_regs.a_clk, rpF.quant_regs.a_clk, -1, q)
            && LR.LookRecTop(reF, LR.RgOf(bestF), LR.RgOf(rpF), cp, K, l,
                             l in LR.PathLooksR(qmF, PIV.QidBody(reF, q), T.InputAt(rstr, cp as nat)))
  {
    var n := |str|;
    var reF := FST.FXR(body);
    var bestF := MIR.MirrorThread(best, n);
    MIR.ReverseLen(str);
    W.IdsFXR(body);
    W.MirrorGetIdx(best.quant_regs, n, q); W.MirrorGetIdx(rp.quant_regs, n, q);
    W.MirrorGetIdx(best.look_regs, n, l); W.MirrorGetIdx(rp.look_regs, n, l);
    W.MirrorGetIdx(best.capture_regs, n, 0); W.MirrorGetIdx(rp.capture_regs, n, 0);
    var b := PIV.QidBody(body, q);
    W.PathsFXR(body, rp.capture_regs.a_clk, best.quant_regs.a_clk, -1, q);
    W.PathsFXR(body, rp.capture_regs.a_clk, rp.quant_regs.a_clk, -1, q);
    assert PIV.QidBody(reF, q) == FST.FXR(b);
    FG.TopLookIdsFXR(b); FG.LookIdsFXR(b); FG.LookIdsFXR(body);
    assert PIV.QLive(body, best.quant_regs.a_clk, best.quant_regs.a_cp, q);
    LR.WinnerLookRecAt(qm, body, str, best, rp, q, l);
    var cp := AI.get_idx(best.quant_regs.a_cp, q);
    var cpn: nat := cp as nat;
    SLS.CapUniqueQidBody(body, q);
    PathLooksRMirror(qm, qmF, b, str, cpn);
    assert AI.get_idx(bestF.quant_regs.a_cp, q) == n - cp;
    FG.LookPathPresentFXR(body, rp.capture_regs.a_clk, rp.quant_regs.a_clk, -1, l);
    FG.MxAtLidLkFXR(body, rp.quant_regs.a_clk, -1, l);
  }

  /** THE PREDICATE FLIP: every conjunct of `LR.WinnerLookRec` is order-free (ids, chains and presence under
      `FXR`; positions mirrored; the path's lids a set). No replay is mirrored. */
  lemma WinnerLookRecFlip(qm: AR.QMap, qmF: AR.QMap, body: R.regex, str: string, best: AI.Thread, rp: AI.Thread)
    requires |qm.ov| == |str| + 1 && qmF.ov == MIR.MirrorView(qm.ov, |str|)
    requires T.TransWf(body) && PIV.CapUnique(body) && PIV.QuantUnique(body) && LTB.LookUnique(body)
    requires LR.WinnerLookRec(qm, body, str, best, rp)
    ensures LR.WinnerLookRec(qmF, FST.FXR(body), LC.Reverse(str), MIR.MirrorThread(best, |str|),
                             MIR.MirrorThread(rp, |str|))
  {
    var n := |str|;
    var reF := FST.FXR(body);
    var rstr := LC.Reverse(str);
    var bestF := MIR.MirrorThread(best, n);
    var rpF := MIR.MirrorThread(rp, n);
    forall q: nat | q in PIV.QuantIds(reF) && PIV.QLive(reF, bestF.quant_regs.a_clk, bestF.quant_regs.a_cp, q)
      ensures forall l: nat | l in NI.TopLookIds(PIV.QidBody(reF, q)) && l in LTB.LookIds(PIV.QidBody(reF, q)) ::
              var cp := AI.get_idx(bestF.quant_regs.a_cp, q);
              var K := AI.get_idx(bestF.quant_regs.a_clk, q);
              0 <= cp <= |rstr| && T.TransWf(PIV.QidBody(reF, q)) && l in LTB.LookIds(reF)
              && AI.get_idx(rpF.quant_regs.a_clk, q) == K && AI.get_idx(rpF.quant_regs.a_cp, q) == cp
              && PIV.QChainFresh(reF, rpF.quant_regs.a_clk, -1, q)
              && PIV.PathPresentQ(reF, rpF.capture_regs.a_clk, rpF.quant_regs.a_clk, -1, q)
              && LR.LookRecTop(reF, LR.RgOf(bestF), LR.RgOf(rpF), cp, K, l,
                               l in LR.PathLooksR(qmF, PIV.QidBody(reF, q), T.InputAt(rstr, cp as nat)))
    {
      forall l: nat | l in NI.TopLookIds(PIV.QidBody(reF, q)) && l in LTB.LookIds(PIV.QidBody(reF, q))
        ensures var cp := AI.get_idx(bestF.quant_regs.a_cp, q);
                var K := AI.get_idx(bestF.quant_regs.a_clk, q);
                0 <= cp <= |rstr| && T.TransWf(PIV.QidBody(reF, q)) && l in LTB.LookIds(reF)
                && AI.get_idx(rpF.quant_regs.a_clk, q) == K && AI.get_idx(rpF.quant_regs.a_cp, q) == cp
                && PIV.QChainFresh(reF, rpF.quant_regs.a_clk, -1, q)
                && PIV.PathPresentQ(reF, rpF.capture_regs.a_clk, rpF.quant_regs.a_clk, -1, q)
                && LR.LookRecTop(reF, LR.RgOf(bestF), LR.RgOf(rpF), cp, K, l,
                                 l in LR.PathLooksR(qmF, PIV.QidBody(reF, q), T.InputAt(rstr, cp as nat)))
      {
        WinnerLookRecFlipAt(qm, qmF, body, str, best, rp, q, l);
      }
    }
    reveal LR.WinnerLookRec();
  }

  // ===========================================================================
  // 2. The backward row's look record, real world then flipped.
  // ===========================================================================

  /** From the readout's premises at a backward VM winner `tB`: the look record of its (direction-blind)
      reconstruction, flipped. */
  lemma LookRecFromPre(qm: AR.QMap, qmF: AR.QMap, body: R.regex, plus: seq<RB.code>, str: string, tB: AI.Thread,
                       ncap: int, nlook: int, nquant: int)
    requires FRA.ReadoutPreS(qm, body, plus, str, tB, ncap, nlook, nquant)
    requires |qm.ov| == |str| + 1 && qmF.ov == MIR.MirrorView(qm.ov, |str|)
    ensures LR.WinnerLookRec(qmF, FST.FXR(body), LC.Reverse(str), MIR.MirrorThread(tB, |str|),
                             MIR.MirrorThread(AI.FReconstructPlus(tB, body, plus, str, qm.ov, LAnc.Backward).0, |str|))
  {
    FRA.FinalReadoutLookRecAtS(qm, body, plus, str, tB, ncap, nlook, nquant);
    DB.ReconstructPlusDirBlind(tB, body, plus, str, qm.ov);
    var rp := AI.FReconstructPlus(tB, body, plus, str, qm.ov, LAnc.Backward).0;
    assert LR.WinnerLookRec(qm, body, str, tB, rp);
    WinnerLookRecFlip(qm, qmF, body, str, tB, rp);
  }

  /** The readout's premises at the real BACKWARD VM winner of a lookbehind row (re-derived as in
      `RP.BackRowReadoutS`, which does not export them), the row's plus match as its reconstruction, and the
      flipped VM winner as its mirror. */
  lemma BackRowReadoutPre(rer: LW.RegExpRecord, qm: AR.QMap, body: R.regex, str: string, cp: nat,
                     ov: LOr.OracleView, cdns: LCdn.cdns, plus: seq<RB.code>,
                     ncap: int, nlook: int, nquant: int, n: nat)
    requires T.TransWf(body) && NR.NestedFragmentCdnRE(body)
    requires PIV.CapUnique(body) && PIV.QuantUnique(body) && LTB.LookUnique(body)
    requires PSM.SizesOkRE(body, ncap, nlook, nquant)
    requires forall l: nat :: l in LTB.LookIds(body) ==> l < nlook
    requires NRC.CdnTopRE(body) && NRR.PlusTableOkS(body, plus)
    requires AR.QmapOk(body, qm) && qm.bodies == M.BodiesOfRE(body)
    requires cdns == LCdn.compile_cdns(body)
    requires !rer.ignoreCase && !rer.multiline
    requires n == |str| && cp <= n && |ov| == n + 1
    requires qm.ov == ov && AR.LmapOk(body, qm) && OE.OracleColsOk(rer, qm, str)
    ensures
      var bcB := CP.compile_to_bytecode(R.reverse_regex(body));
      var raB := AI.FFindMatch(bcB, str,
                   AI.FInitState(bcB, cp, AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant), 0,
                                 AI.cp_context(cp, str, LAnc.Backward)), ov, LAnc.Backward, cdns).0;
      var rf := AI.FFindMatchPlus(bcB, body, plus, str, ov, LAnc.Backward, cp,
                                  AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant), 0, cdns).0;
      var bcF := CP.compile_to_bytecode(FST.FXR(body));
      var fF := AI.FFindMatch(bcF, LC.Reverse(str),
                  AI.FInitState(bcF, n - cp, AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant), 0,
                                AI.cp_context(n - cp, LC.Reverse(str), LAnc.Forward)),
                  MIR.MirrorView(ov, n), LAnc.Forward, MIR.SwapAnchorsCdns(cdns)).0;
      rf.Some? ==>
        raB.Some? && fF.Some? && fF.value == MIR.MirrorThread(raB.value, n)
        && rf.value == AI.FReconstructPlus(raB.value, body, plus, str, ov, LAnc.Backward).0
        && FRA.ReadoutPreS(qm, body, plus, str, raB.value, ncap, nlook, nquant)
  {
    var capture := AReg.init_regs(ncap);
    var look := AReg.init_regs(nlook);
    var quant := AReg.init_regs(nquant);
    var Q := FRD.StampQids(body);
    var bcB := CP.compile_to_bytecode(R.reverse_regex(body));
    var ctxB := AI.cp_context(cp, str, LAnc.Backward);
    var initsB := AI.FInitState(bcB, cp, capture, look, quant, 0, ctxB);
    var fmB := AI.FFindMatch(bcB, str, initsB, ov, LAnc.Backward, cdns);
    var raB := fmB.0;
    var rr := AI.FFindMatchPlus(bcB, body, plus, str, ov, LAnc.Backward, cp, capture, look, quant, 0, cdns);
    var bcF := CP.compile_to_bytecode(FST.FXR(body));
    var rfF := AI.FFindMatch(bcF, LC.Reverse(str),
                 AI.FInitState(bcF, n - cp, capture, look, quant, 0, AI.cp_context(n - cp, LC.Reverse(str), LAnc.Forward)),
                 MIR.MirrorView(ov, n), LAnc.Forward, MIR.SwapAnchorsCdns(cdns)).0;
    var Gx, qmX, endlX := RP.BackRowReadoutS(rer, qm, body, str, cp, ov, cdns, plus, ncap, nlook, nquant, n);
    assert {:split_here} true;
    // ---- the view is kept by the backward run: the plus match is the reconstruction of the VM winner ----
    M.ReverseCdnPackage(body);
    M.NoWriteOracleBodyCodeCdn(R.reverse_regex(body));
    assert ctxB.nextchar == AI.get_char(str, cp - 1);
    CM.FFindMatchOvStable(bcB, str, initsB, ov, LAnc.Backward, cdns);
    assert fmB.1 == ov;
    assert rr.0 == (match raB
                    case None => None
                    case Some(thread) => Some(AI.FReconstructPlus(thread, body, plus, str, fmB.1, LAnc.Backward).0));
    assert rr.0.Some? ==> raB.Some? && rr.0.value == AI.FReconstructPlus(raB.value, body, plus, str, ov, LAnc.Backward).0;
    if rr.0.Some? {
      var tB := raB.value;
      var tF := rfF.value;
      assert tF == MIR.MirrorThread(tB, n);
      assert {:split_here} true;
      // ---- bank bounds, both sides ----
      RL.AInitLaws(ncap); RL.AInitLaws(nlook); RL.AInitLaws(nquant);
      assert MW.VmCpsIn(initsB, n) by {
        var th0 := AI.init_thread(capture, look, quant);
        assert MW.ThreadCpsIn(th0, n);
        forall t0 | t0 in initsB.active ensures MW.ThreadCpsIn(t0, n) { assert t0 == th0; }
      }
      MW.FFindMatchCpsIn(bcB, str, initsB, ov, LAnc.Backward, cdns);
      MW.MirrorThreadInvol(tB, n);
      assert tB == MIR.MirrorThread(tF, n);
      WR.CpsInMirror(tB.capture_regs, n); WR.CpsInMirror(tB.quant_regs, n);
      WR.CpsInBound(tF.capture_regs, n); WR.CpsInBound(tF.quant_regs, n);

      assert {:split_here} true;
      // ---- ReadoutPreS at the backward winner ----
      W.BestLiveREMirror(body, tF, n);
      assert PSM.BestLiveRE(body, tB);
      CM.FInitStateRegsWf(bcB, cp, ncap, nlook, nquant, 0, ctxB);
      M.FFindMatchRegsWf(bcB, str, initsB, ov, LAnc.Backward, cdns, ncap, nlook, nquant);
      assert CM.ThreadRegsWf(tB, ncap, nlook, nquant);
      W.BackRowEntryRegsFinalS(body, str, cp, ov, cdns, ncap, nlook, nquant);
      assert FV.RegsFinalOk(tB, n, Q);
      var rg: NRC.Regs3 := (tB.capture_regs, tB.look_regs, tB.quant_regs);
      FRA.StampsFinalAtSFromRegsFinalOk(body, tB, n);
      RP.StampPathOkMirror(qm, qmX, body, str, tF, n);
      assert tB.quant_regs == MIR.MirrorRegs(tF.quant_regs, n);
      assert NRR.CapValWf(rg) && FRG.QClkGe(rg) && NRR.WfRegs(rg);
      BF.SizesCoverFromOk(body, ncap, nlook, nquant);
      BF.CoversFromSizes(body, rg, ncap, nlook, nquant);
      assert FRA.ReadoutPreS(qm, body, plus, str, tB, ncap, nlook, nquant);

    }
  }

  /** The look record of a lookbehind row at the FLIPPED VM winner and the mirror of the real backward
      reconstruction: `FRA.FinalReadoutLookRecAtS` at the backward VM winner, direction blindness, then
      `WinnerLookRecFlip` (`LookRecFromPre`). */
  lemma BackRowLookRecFlip(rer: LW.RegExpRecord, qm: AR.QMap, qmF: AR.QMap, body: R.regex, str: string, cp: nat,
                           ov: LOr.OracleView, cdns: LCdn.cdns, plus: seq<RB.code>,
                           ncap: int, nlook: int, nquant: int, n: nat)
    requires T.TransWf(body) && NR.NestedFragmentCdnRE(body)
    requires PIV.CapUnique(body) && PIV.QuantUnique(body) && LTB.LookUnique(body)
    requires PSM.SizesOkRE(body, ncap, nlook, nquant)
    requires forall l: nat :: l in LTB.LookIds(body) ==> l < nlook
    requires NRC.CdnTopRE(body) && NRR.PlusTableOkS(body, plus)
    requires AR.QmapOk(body, qm) && qm.bodies == M.BodiesOfRE(body)
    requires cdns == LCdn.compile_cdns(body)
    requires !rer.ignoreCase && !rer.multiline
    requires n == |str| && cp <= n && |ov| == n + 1
    requires qm.ov == ov && AR.LmapOk(body, qm) && OE.OracleColsOk(rer, qm, str)
    requires qmF.ov == MIR.MirrorView(ov, n)
    ensures
      var bcB := CP.compile_to_bytecode(R.reverse_regex(body));
      var rf := AI.FFindMatchPlus(bcB, body, plus, str, ov, LAnc.Backward, cp,
                                  AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant), 0, cdns).0;
      var bcF := CP.compile_to_bytecode(FST.FXR(body));
      var fF := AI.FFindMatch(bcF, LC.Reverse(str),
                  AI.FInitState(bcF, n - cp, AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant), 0,
                                AI.cp_context(n - cp, LC.Reverse(str), LAnc.Forward)),
                  MIR.MirrorView(ov, n), LAnc.Forward, MIR.SwapAnchorsCdns(cdns)).0;
      rf.Some? ==>
        fF.Some? && LR.WinnerLookRec(qmF, FST.FXR(body), LC.Reverse(str), fF.value, MIR.MirrorThread(rf.value, n))
  {
    var bcB := CP.compile_to_bytecode(R.reverse_regex(body));
    var raB := AI.FFindMatch(bcB, str,
                 AI.FInitState(bcB, cp, AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant), 0,
                               AI.cp_context(cp, str, LAnc.Backward)), ov, LAnc.Backward, cdns).0;
    var rf := AI.FFindMatchPlus(bcB, body, plus, str, ov, LAnc.Backward, cp,
                                AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant), 0, cdns).0;
    BackRowReadoutPre(rer, qm, body, str, cp, ov, cdns, plus, ncap, nlook, nquant, n);
    if rf.Some? {
      LookRecFromPre(qm, qmF, body, plus, str, raB.value, ncap, nlook, nquant);
    }
  }

  // ===========================================================================
  // 3. The presence-premised converses come back through the flip.
  // ===========================================================================

  /** A look bank with every record but `l`'s unset (clocks kept). */
  function SoloLook(lk: AReg.Regs, l: int): AReg.Regs {
    AReg.ARegs(seq(|lk.a_cp|, i requires 0 <= i < |lk.a_cp| => if i == l then lk.a_cp[i] else -1), lk.a_clk)
  }

  lemma SoloLookFacts(lk: AReg.Regs, l: int, n: nat)
    ensures SoloLook(lk, l).a_clk == lk.a_clk
    ensures AReg.get_cp(SoloLook(lk, l), l) == AReg.get_cp(lk, l)
    ensures forall k: int :: k != l ==> AReg.get_cp(SoloLook(lk, l), k) == None
    ensures CM.LookCpsLE(lk, n) ==> CM.LookCpsLE(SoloLook(lk, l), n)
    ensures MIR.MirrorRegs(SoloLook(lk, l), n).a_clk == lk.a_clk
    ensures AReg.get_cp(MIR.MirrorRegs(SoloLook(lk, l), n), l) == AReg.get_cp(MIR.MirrorRegs(lk, n), l)
    ensures forall k: int :: k != l ==> AReg.get_cp(MIR.MirrorRegs(SoloLook(lk, l), n), k) == None
  {
    if CM.LookCpsLE(lk, n) {
      forall k: int ensures AI.get_idx(SoloLook(lk, l).a_cp, k) <= n {
        if 0 <= k < |lk.a_cp| && k == l { assert AI.get_idx(lk.a_cp, k) <= n; }
      }
    }
  }

  /** `LookNestBackTTopP` at one lid, back through the flip (via `LookNestBackTTopLidFlipPS` on the solo thread). */
  lemma BackLidFlipP(
    rer: LW.RegExpRecord, qm: AR.QMap, body: R.regex, crv: CP.FCompiled, str: string,
    ov: LOr.OracleView, gmt: LG.GroupMap, th: AI.Thread, lid: nat,
    ncap: int, nlook: int, nquant: int)
    requires T.TransWf(body) && NR.NestedFragmentCdnRE(body)
    requires PIV.CapUnique(body) && PIV.QuantUnique(body) && LTB.LookUnique(body)
    requires PSM.SizesOkRE(body, ncap, nlook, nquant)
    requires forall l: nat :: l in LTB.LookIds(body) ==> l < nlook
    requires !rer.ignoreCase && !rer.multiline
    requires |ov| == |str| + 1
    requires qm.ov == ov && AR.LmapOk(body, qm) && OE.OracleColsOk(rer, qm, str)
    requires LTB.LookTablesOk(body, crv) && |crv.f_look_types| == |crv.f_look_ast|
    requires TRM.GmInBounds(gmt, |str|)
    requires CM.LookCpsLE(th.look_regs, |str|)
    requires lid in NI.TopLookIds(body) && lid in LTB.LookIds(body)
    requires M.MatchedPosLA(crv, th.look_regs, lid as int)
    requires NI.LookPathDom(body, AI.get_idx(th.look_regs.a_clk, lid as int), th.quant_regs.a_clk, lid)
    requires NI.LookPathPresent(body, th.capture_regs.a_clk, th.quant_regs.a_clk, -1, lid)
    requires AI.get_idx(th.look_regs.a_clk, lid as int) >= NI.MxAtLidLk(body, th.quant_regs.a_clk, -1, lid)
    requires NRR.PlusTableOkS(body, crv.f_plus_bc)
    requires LookNestBackTTopP(FST.FXR(body), MirrorTablesPS(crv, body), LC.Reverse(str),
                               MIR.MirrorView(ov, |str|), PIV.CapIdsInLooks(body),
                               TRM.MirrorGm(gmt, |str|), MIR.MirrorThread(th, |str|), ncap, nlook, nquant)
    ensures var rf := M.FreshBodyMatchPlus(crv, str, lid as int, th.look_regs, ov, ncap, nlook, nquant);
            rf.Some? ==>
              forall g: LG.GroupId ::
                g in PIV.CapIdsInLooks(body) && g in PIV.CapIds(NI.LookBodyOfRE(body, lid))
                && g in PIV.GmOfLive(NI.LookBodyOfRE(body, lid), rf.value.capture_regs,
                                     rf.value.look_regs, rf.value.quant_regs)
                ==> g in gmt
  {
    var n := |str|;
    var rstr := LC.Reverse(str);
    var ov' := MIR.MirrorView(ov, n);
    var reF := FST.FXR(body);
    var crvF := MirrorTablesPS(crv, body);
    var S := PIV.CapIdsInLooks(body);
    var gmtF := TRM.MirrorGm(gmt, n);
    var thS := th.(look_regs := SoloLook(th.look_regs, lid as int));
    var thF := MIR.MirrorThread(th, n);
    var thSF := MIR.MirrorThread(thS, n);
    SoloLookFacts(th.look_regs, lid as int, n);
    FG.TopLookIdsFXR(body); FG.LookIdsFXR(body);
    FG.LookPathPresentFXR(body, th.capture_regs.a_clk, th.quant_regs.a_clk, -1, lid);
    FG.MxAtLidLkFXR(body, th.quant_regs.a_clk, -1, lid);
    assert LookNestBackTTop(reF, crvF, rstr, ov', S, gmtF, thSF, ncap, nlook, nquant) by {
      forall l2: nat | l2 in NI.TopLookIds(reF)
                       && (M.MatchedPosLA(crvF, thSF.look_regs, l2 as int)
                           && l2 in LTB.LookIds(reF)
                           && NI.LookPathDom(reF, AI.get_idx(thSF.look_regs.a_clk, l2 as int), thSF.quant_regs.a_clk, l2))
        ensures var rf := M.FreshBodyMatchPlus(crvF, rstr, l2 as int, thSF.look_regs, ov', ncap, nlook, nquant);
                rf.Some? ==>
                  forall g: LG.GroupId ::
                    g in S && g in PIV.CapIds(NI.LookBodyOfRE(reF, l2))
                    && g in PIV.GmOfLive(NI.LookBodyOfRE(reF, l2), rf.value.capture_regs,
                                         rf.value.look_regs, rf.value.quant_regs)
                    ==> g in gmtF
      {
        assert l2 == lid;
        T4.FreshBodyCong(crvF, rstr, lid as int, thSF.look_regs, thF.look_regs, ov', ncap, nlook, nquant);
        assert M.MatchedPosLA(crvF, thF.look_regs, lid as int);
        assert NI.LookPathDom(reF, AI.get_idx(thF.look_regs.a_clk, lid as int), thF.quant_regs.a_clk, lid);
        assert NI.LookPathPresent(reF, thF.capture_regs.a_clk, thF.quant_regs.a_clk, -1, lid);
        assert AI.get_idx(thF.look_regs.a_clk, lid as int) >= NI.MxAtLidLk(reF, thF.quant_regs.a_clk, -1, lid);
      }
    }
    assert {:split_here} true;
    LookNestBackTTopLidFlipPS(rer, qm, body, crv, str, ov, gmt, thS, lid, ncap, nlook, nquant);
    T4.FreshBodyCong(crv, str, lid as int, thS.look_regs, th.look_regs, ov, ncap, nlook, nquant);
  }

  /** `LookNestBackTTopDeepP` at one lid, back through the flip (via `LookNestBackTTopDeepLidFlipCdn` on the solo
      thread; the deep carrier reads the look tables only). */
  lemma DeepLidFlipP(
    rer: LW.RegExpRecord, qm: AR.QMap, body: R.regex, crv: CP.FCompiled, str: string,
    ov: LOr.OracleView, gmt: LG.GroupMap, th: AI.Thread, lid: nat,
    ncap: int, nlook: int, nquant: int)
    requires T.TransWf(body) && NR.NestedFragmentCdnRE(body)
    requires PIV.CapUnique(body) && PIV.QuantUnique(body) && LTB.LookUnique(body)
    requires PSM.SizesOkRE(body, ncap, nlook, nquant)
    requires !rer.ignoreCase && !rer.multiline
    requires |ov| == |str| + 1
    requires qm.ov == ov && AR.LmapOk(body, qm) && OE.OracleColsOk(rer, qm, str)
    requires LTB.LookTablesOk(body, crv) && |crv.f_look_types| == |crv.f_look_ast|
    requires TRM.GmInBounds(gmt, |str|)
    requires CM.LookCpsLE(th.look_regs, |str|)
    requires lid in NI.TopLookIds(body) && lid in LTB.LookIds(body)
    requires M.MatchedPosLA(crv, th.look_regs, lid as int)
    requires NI.LookPathDom(body, AI.get_idx(th.look_regs.a_clk, lid as int), th.quant_regs.a_clk, lid)
    requires NI.LookPathPresent(body, th.capture_regs.a_clk, th.quant_regs.a_clk, -1, lid)
    requires AI.get_idx(th.look_regs.a_clk, lid as int) >= NI.MxAtLidLk(body, th.quant_regs.a_clk, -1, lid)
    requires LookNestBackTTopDeepP(rer, FST.FXR(body), MirrorTablesPS(crv, body), LC.Reverse(str),
                                   MIR.MirrorView(ov, |str|), PIV.CapIdsInLooks(body),
                                   TRM.MirrorGm(gmt, |str|), MIR.MirrorThread(th, |str|), ncap, nlook, nquant)
    ensures var lsub := SubFirstLeafAt(rer, crv, str, lid as int, th.look_regs);
            lsub.Some? ==>
              forall g: LG.GroupId ::
                g in PIV.CapIdsInLooks(body) && g in PIV.CapIds(NI.LookBodyOfRE(body, lid)) ==>
                  (g in lsub.value ==> g in gmt && gmt[g] == lsub.value[g])
                  && (g in gmt ==> g in lsub.value)
  {
    var n := |str|;
    var rstr := LC.Reverse(str);
    var ov' := MIR.MirrorView(ov, n);
    var reF := FST.FXR(body);
    var crvF := MirrorTablesPS(crv, body);
    var crvM := FG.MirrorTables(crv);
    var S := PIV.CapIdsInLooks(body);
    var gmtF := TRM.MirrorGm(gmt, n);
    var thS := th.(look_regs := SoloLook(th.look_regs, lid as int));
    var thF := MIR.MirrorThread(th, n);
    var thSF := MIR.MirrorThread(thS, n);
    SoloLookFacts(th.look_regs, lid as int, n);
    FG.TopLookIdsFXR(body); FG.LookIdsFXR(body);
    FG.LookPathPresentFXR(body, th.capture_regs.a_clk, th.quant_regs.a_clk, -1, lid);
    FG.MxAtLidLkFXR(body, th.quant_regs.a_clk, -1, lid);
    assert LookNestBackTTopDeep(rer, reF, crvM, rstr, ov', S, gmtF, thSF, ncap, nlook, nquant) by {
      forall l2: nat | l2 in NI.TopLookIds(reF)
                       && (M.MatchedPosLA(crvM, thSF.look_regs, l2 as int)
                           && l2 in LTB.LookIds(reF)
                           && NI.LookPathDom(reF, AI.get_idx(thSF.look_regs.a_clk, l2 as int), thSF.quant_regs.a_clk, l2))
        ensures var lsub := SubFirstLeafAt(rer, crvM, rstr, l2 as int, thSF.look_regs);
                lsub.Some? ==>
                  forall g: LG.GroupId ::
                    g in S && g in PIV.CapIds(NI.LookBodyOfRE(reF, l2)) ==>
                      (g in lsub.value ==> g in gmtF && gmtF[g] == lsub.value[g])
                      && (g in gmtF ==> g in lsub.value)
      {
        assert l2 == lid;
        assert M.VBody(crvM, lid as int) == M.VBody(crvF, lid as int);
        assert LidDir(crvM, lid as int) == LidDir(crvF, lid as int);
        T4.SubFirstLeafCong(rer, crvF, rstr, lid as int, thSF.look_regs, thF.look_regs);
        assert SubFirstLeafAt(rer, crvM, rstr, lid as int, thSF.look_regs)
               == SubFirstLeafAt(rer, crvF, rstr, lid as int, thF.look_regs);
        assert M.MatchedPosLA(crvF, thF.look_regs, lid as int);
        assert NI.LookPathDom(reF, AI.get_idx(thF.look_regs.a_clk, lid as int), thF.quant_regs.a_clk, lid);
        assert NI.LookPathPresent(reF, thF.capture_regs.a_clk, thF.quant_regs.a_clk, -1, lid);
        assert AI.get_idx(thF.look_regs.a_clk, lid as int) >= NI.MxAtLidLk(reF, thF.quant_regs.a_clk, -1, lid);
      }
    }
    assert {:split_here} true;
    LookNestBackTTopDeepLidFlipCdn(rer, qm, body, crv, str, ov, gmt, thS, lid, ncap, nlook, nquant);
    T4.SubFirstLeafCong(rer, crv, str, lid as int, thS.look_regs, th.look_regs);
  }

  /** Both presence-premised converses of a lookbehind row, from the flipped world's. */
  lemma FlipBackP(
    rer: LW.RegExpRecord, qm: AR.QMap, body: R.regex, crv: CP.FCompiled, str: string,
    ov: LOr.OracleView, gmt: LG.GroupMap, th: AI.Thread, ncap: int, nlook: int, nquant: int)
    requires T.TransWf(body) && NR.NestedFragmentCdnRE(body)
    requires PIV.CapUnique(body) && PIV.QuantUnique(body) && LTB.LookUnique(body)
    requires PSM.SizesOkRE(body, ncap, nlook, nquant)
    requires forall l: nat :: l in LTB.LookIds(body) ==> l < nlook
    requires !rer.ignoreCase && !rer.multiline
    requires |ov| == |str| + 1
    requires qm.ov == ov && AR.LmapOk(body, qm) && OE.OracleColsOk(rer, qm, str)
    requires LTB.LookTablesOk(body, crv) && |crv.f_look_types| == |crv.f_look_ast|
    requires TRM.GmInBounds(gmt, |str|)
    requires CM.LookCpsLE(th.look_regs, |str|)
    requires NRR.PlusTableOkS(body, crv.f_plus_bc)
    requires LookNestBackTTopP(FST.FXR(body), MirrorTablesPS(crv, body), LC.Reverse(str),
                               MIR.MirrorView(ov, |str|), PIV.CapIdsInLooks(body),
                               TRM.MirrorGm(gmt, |str|), MIR.MirrorThread(th, |str|), ncap, nlook, nquant)
    requires LookNestBackTTopDeepP(rer, FST.FXR(body), MirrorTablesPS(crv, body), LC.Reverse(str),
                                   MIR.MirrorView(ov, |str|), PIV.CapIdsInLooks(body),
                                   TRM.MirrorGm(gmt, |str|), MIR.MirrorThread(th, |str|), ncap, nlook, nquant)
    ensures LookNestBackTTopP(body, crv, str, ov, PIV.CapIdsInLooks(body), gmt, th, ncap, nlook, nquant)
    ensures LookNestBackTTopDeepP(rer, body, crv, str, ov, PIV.CapIdsInLooks(body), gmt, th, ncap, nlook, nquant)
  {
    var S := PIV.CapIdsInLooks(body);
    forall lid: nat | lid in NI.TopLookIds(body)
                      && (M.MatchedPosLA(crv, th.look_regs, lid as int)
                          && lid in LTB.LookIds(body)
                          && NI.LookPathDom(body, AI.get_idx(th.look_regs.a_clk, lid as int), th.quant_regs.a_clk, lid)
                          && NI.LookPathPresent(body, th.capture_regs.a_clk, th.quant_regs.a_clk, -1, lid)
                          && AI.get_idx(th.look_regs.a_clk, lid as int) >= NI.MxAtLidLk(body, th.quant_regs.a_clk, -1, lid))
      ensures var rfl := M.FreshBodyMatchPlus(crv, str, lid as int, th.look_regs, ov, ncap, nlook, nquant);
              rfl.Some? ==>
                forall g: LG.GroupId ::
                  g in S && g in PIV.CapIds(NI.LookBodyOfRE(body, lid))
                  && g in PIV.GmOfLive(NI.LookBodyOfRE(body, lid), rfl.value.capture_regs,
                                       rfl.value.look_regs, rfl.value.quant_regs)
                  ==> g in gmt
    {
      BackLidFlipP(rer, qm, body, crv, str, ov, gmt, th, lid, ncap, nlook, nquant);
    }
    assert {:split_here} true;
    forall lid: nat | lid in NI.TopLookIds(body)
                      && (M.MatchedPosLA(crv, th.look_regs, lid as int)
                          && lid in LTB.LookIds(body)
                          && NI.LookPathDom(body, AI.get_idx(th.look_regs.a_clk, lid as int), th.quant_regs.a_clk, lid)
                          && NI.LookPathPresent(body, th.capture_regs.a_clk, th.quant_regs.a_clk, -1, lid)
                          && AI.get_idx(th.look_regs.a_clk, lid as int) >= NI.MxAtLidLk(body, th.quant_regs.a_clk, -1, lid))
      ensures var lsub := SubFirstLeafAt(rer, crv, str, lid as int, th.look_regs);
              lsub.Some? ==>
                forall g: LG.GroupId ::
                  g in S && g in PIV.CapIds(NI.LookBodyOfRE(body, lid)) ==>
                    (g in lsub.value ==> g in gmt && gmt[g] == lsub.value[g])
                    && (g in gmt ==> g in lsub.value)
    {
      DeepLidFlipP(rer, qm, body, crv, str, ov, gmt, th, lid, ncap, nlook, nquant);
    }
  }
}
