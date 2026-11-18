// (G3a) Machine A at a look body: the readout of a fresh forward run's winner (A3) and machine A on
// the plus match (MachineAAt and its corollaries, by the peer session). Below the band: the gate
// tier's plus-form statements (E4, the oracle pair) call it, and so does A6.
module LindenElkMachineA {
  import opened Std.Wrappers
  import R = RegElkRegex
  import RB = Bytecode
  import CP = Compiler
  import AI = ArrayInterp
  import AReg = Array_Regs
  import LOr = Oracle
  import LAnc = Anchors
  import LCdn = Cdn
  import NR = LindenElkNfaRep
  import T = LindenElkTranslate
  import AR = LindenElkActionsRep
  import PIV = LindenElkPikeInv
  import PSM = LindenElkPikeSim
  import LTB = LindenElkLookTables
  import CM = LindenElkClockMono
  import M = LindenElkMain
  import NI = LindenElkNestInv
  import NRC = LindenElkNulledRecon
  import NRR = LindenElkNulledReconRegs
  import NRO = LindenElkNulledReconReadout
  import FRG = LindenElkFinalRegs
  import FRD = LindenElkFinalReadout
  import FV = LindenElkFinalVm
  import RF = LindenElkReconFrame
  import FRA = LindenElkFinalReadoutAt
  import RRA = LindenElkRowReconAt
  import SBk = LindenElkStampBank      // (G5b-3)
  import ELk = LindenElkEmptyLooks     // (G4b-1)
  import LR = LindenElkLookRecord   // (G4b-2) the look record at the winner
  import SL = LindenElkStampLive
  import LG = Groups
  import LT = Tree
  import LC = Chars
  import L = Regex
  import LS = Semantics
  import BS = BooleanSemantics
  import WP = WarblrePrimitives
  import LW = WarblreRegExpRecord
  import PT = PikeTree
  import CR = Correctness
  import LFU = FunctionalUtils
  import EL = LindenElkEntryLk
  import WO = LindenElkWalkOk
  import WkE = LindenElkWalkOkEntry
  import ATR = LindenElkActionsTreeRep
  import NB = LindenElkNulledPlusBool
  import TT = LindenElkTreeThread
  import TREP = LindenElkTreeRep
  import LL = LindenElkLookLeaves
  import RL = LindenElkRegsLaws
  import opened LindenElkBankFrames

  // =========================================================================
  // 1. A3: the readout of a fresh forward run's winner at any (body, cp).
  // =========================================================================

  /** A3. The winner of a FRESH forward run of `body` at `cp`, reconstructed: the F-b readout
      (`GmOfLive` of the reconstructed thread is the spec-side `GmOfLiveR` of the winner) and the
      clock frame. No synthetic winner: the conclusion is at `rp` itself. */
  lemma ReadoutAtWinnerAt(qm: AR.QMap, body: R.regex, code: RB.code, endl: nat, plus: seq<RB.code>,
                          str: string, cp: nat, ov: LOr.OracleView, cdn: LCdn.cdns, inits: AI.VmState,
                          ncap: int, nlook: int, nquant: int, result: Option<AI.Thread>)
    returns (rp: AI.Thread)
    requires code == CP.compile_to_bytecode(body)
    requires T.TransWf(body) && NR.NestedFragmentRE(body) && RF.CinBodiesLookFreeRE(body)
    requires PIV.CapUnique(body) && PIV.QuantUnique(body) && LTB.LookUnique(body)
    requires NRC.NoCdnPlusRE(body) && NRR.PlusTableOk(body, plus)
    requires AR.QmapOk(body, qm) && qm.ov == ov
    requires NR.NfaRepRE(body, code, 0, endl) && |code| == endl + 1 && NR.GetPcRE(code, endl) == Some(RB.Accept)
    requires ncap >= 0 && nlook >= 0 && nquant >= 0
    requires SizesCover(body, ncap, nlook, nquant)
    requires cp <= |str|
    requires inits == AI.FInitState(code, cp, AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant),
                                    0, AI.cp_context(cp, str, LAnc.Forward))
    requires result == AI.FFindMatch(code, str, inits, ov, LAnc.Forward, cdn).0
    requires result.Some? && PSM.BestLiveRE(body, result.value)
    ensures AI.FFindMatch(code, str, inits, ov, LAnc.Forward, cdn).1 == ov
    ensures var rpp := AI.FReconstructPlus(result.value, body, plus, str, ov, LAnc.Forward);
            rp == rpp.0 && rpp.1 == ov
    ensures rp.pc == result.value.pc && rp.exit_allowed == result.value.exit_allowed
    ensures PIV.GmOfLive(body, rp.capture_regs, rp.look_regs, rp.quant_regs)
            == PIV.GmOfLiveR(body, qm, str, result.value.capture_regs, result.value.look_regs, result.value.quant_regs)
    ensures CM.ThreadRegsWf(rp, ncap, nlook, nquant)
    ensures CM.ThreadRegsWf(result.value, ncap, nlook, nquant)
    ensures ClkFrame(body, FRD.CinQids(body), rp, result.value)
  {
    var best := result.value;
    var ctx := AI.cp_context(cp, str, LAnc.Forward);
    var capture := AReg.init_regs(ncap);
    var look := AReg.init_regs(nlook);
    var quant := AReg.init_regs(nquant);
    var rg: NRC.Regs3 := (best.capture_regs, best.look_regs, best.quant_regs);
    var Q := FRD.CinQids(body);
    assert ctx.nextchar == AI.get_char(str, cp);
    // VM facts of the winning thread
    CM.FInitStateRegsWf(code, cp, ncap, nlook, nquant, 0, ctx);
    M.FFindMatchRegsWf(code, str, inits, ov, LAnc.Forward, cdn, ncap, nlook, nquant);
    assert CM.ThreadRegsWf(best, ncap, nlook, nquant);
    FRD.TrueStampsInCin(body, code, endl);
    FV.RegsFinalOkInit(ncap, nlook, nquant, |str|, Q);
    assert FV.VmRegsFinalOk(inits, |str|, Q) by {
      forall t0 | t0 in inits.active ensures FV.RegsFinalOk(t0, |str|, Q) {
        assert t0 == AI.init_thread(capture, look, quant);
      }
    }
    FV.FFindMatchRegsFinal(code, str, inits, ov, LAnc.Forward, cdn, Q);
    assert FV.RegsFinalOk(best, |str|, Q);
    assert {:split_here} true;
    // a fresh run sets no capture outside `body`'s own groups
    M.CaptureBytecodeClassifiedNestedOuter(body);
    var Sout := PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(body));
    assert CM.VmCapturesAgree(inits, capture, Sout) by {
      forall t0 | t0 in inits.active ensures CM.RegsAgreeOutside(t0.capture_regs, capture, Sout) {
        assert t0 == AI.init_thread(capture, look, quant);
      }
    }
    CM.FFindMatchCapWriteFrame(code, str, inits, ov, LAnc.Forward, cdn, capture, Sout);
    OnlyCapIdsFromFrameOuter(body, best.capture_regs, ncap);
    assert NRO.OnlyCapIdsSet(body, rg);
    assert {:split_here} true;
    // the local readout premises
    FRA.StampsFinalAtFromRegsFinalOk(body, best, |str|);
    assert NRR.CapValWf(rg) && FRG.QClkGe(rg) && NRR.WfRegs(rg);
    CoversFromSizes(body, rg, ncap, nlook, nquant);
    assert FRA.ReadoutPre(qm, body, plus, str, best, ncap, nlook, nquant);
    assert {:split_here} true;
    // THE READOUT (A1) + its frame (A2), and the untouched view
    FRA.FinalReadoutAt(qm, body, plus, str, best, ncap, nlook, nquant);
    FRA.FinalReadoutFrameAtCin(qm, body, plus, str, best);
    RRA.RowReconAt(qm, body, plus, str, best, ncap, nlook, nquant);   // the look bank is kept
    M.NoWriteOracleBodyCodeNested(body);
    CM.FFindMatchOvStable(code, str, inits, ov, LAnc.Forward, cdn);
    rp := AI.FReconstructPlus(best, body, plus, str, ov, LAnc.Forward).0;
    assert ClkFrame(body, Q, rp, best);
  }

  // =========================================================================
  // 2. Machine A on the plus match at a look body (for the gate tier's E4 and the oracle pair).
  // =========================================================================

  /** The premises shared by the three lemmas. */
  ghost predicate MachineAPre(rer: LW.RegExpRecord, qm: AR.QMap, body: R.regex, bodycode: RB.code, endl: nat,
                              str: string, cp: nat, ov: LOr.OracleView, plus_bc: seq<RB.code>,
                              ncap: int, nlook: int, nquant: int) {
    PSM.StaticCoreNestedRE(qm, body, bodycode, endl)
    && PSM.SizesOkRE(body, ncap, nlook, nquant)
    && nlook >= 0
    && (forall l: nat :: l in LTB.LookIds(body) ==> l < nlook)
    && LTB.LookUnique(body)
    && qm.ov == ov && !rer.multiline && !rer.ignoreCase
    && cp <= |str| && bodycode == CP.compile_to_bytecode(body)
    && NRC.NoCdnPlusRE(body) && NRR.PlusTableOk(body, plus_bc) && RF.CinBodiesLookFreeRE(body)
  }

  /** Machine A at a body: the fresh PLUS match against the body's spec first leaf, outside the body's
      own inner-look groups. `M.ReplayCapIsBodyLeafNested` (+ `FNulledPlusIdentity`) without
      `NoNulledPlusRE(body)`. */
  lemma MachineAAt(rer: LW.RegExpRecord, qm: AR.QMap, body: R.regex, bodycode: RB.code, endl: nat, ngroups: nat,
                   str: string, cp: nat, ov: LOr.OracleView, cdn: LCdn.cdns, plus_bc: seq<RB.code>,
                   ncap: int, nlook: int, nquant: int)
    requires MachineAPre(rer, qm, body, bodycode, endl, str, cp, ov, plus_bc, ncap, nlook, nquant)
    requires LL.OracleOkSuffix(rer, qm, PIV.InpOfCp(str, cp))
    ensures
      var inp := PIV.InpOfCp(str, cp);
      var t := LFU.ComputeTr(rer, [LS.Areg(T.Translate(body))], inp, LG.Empty, WP.Forward);
      var rr := AI.FFindMatchPlus(bodycode, body, plus_bc, str, ov, LAnc.Forward, cp,
                                  AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant), 0, cdn);
      rr.1 == ov
      && (rr.0.Some? <==> LT.FirstLeaf(t, inp).Some?)
      && (rr.0.Some? ==>
            LL.GmAgreeOutside(PIV.GmOfLive(body, rr.0.value.capture_regs, rr.0.value.look_regs, rr.0.value.quant_regs),
                              LT.FirstLeaf(t, inp).value.1, LL.LkBodyGroups(T.Translate(body)))
            && CM.ThreadRegsWf(rr.0.value, ncap, nlook, nquant)
            && CM.LookClkSetWithCp(rr.0.value.look_regs)
            && CM.LookCpSetWithClk(rr.0.value.look_regs)
            && CM.LookCpsLE(rr.0.value.look_regs, |str|))
  {
    var inp := PIV.InpOfCp(str, cp);
    var acts := [LS.Areg(T.Translate(body))];
    var S := PIV.CapIdsInLooks(body);

    // ---- the spec tree ----------------------------------------------------
    LFU.ComputeTrIsTree(rer, acts, inp, LG.Empty, WP.Forward);
    var t := LFU.ComputeTr(rer, acts, inp, LG.Empty, WP.Forward);
    assert LS.IsTree(rer, acts, inp, LG.Empty, WP.Forward, t);
    EL.TranslateFragmentPikeLkRec(body);
    EL.BooleanCorrectLkRec(rer, T.Translate(body), inp, t);
    assert forall i :: 0 <= i < |acts| ==> !acts[i].Acheck?;
    M.BoolTreeLbIrrel(rer, acts, inp, BS.CanExit, BS.CannotExit, t);
    assert EL.BoolTreeLk(rer, acts, inp, BS.CannotExit, t);

    assert {:split_here} true;
    // ---- the CHECKED tree ---------------------------------------------------
    WkE.WalkOkEntryNested(body);
    assert EL.PikeLkActionsRec(acts) by {
      assert acts == acts + [];
      assert EL.PikeLkActionsRec([]);
      EL.PikeLkActionsRecConsIff(LS.Areg(T.Translate(body)), []);
    }
    assert WO.WalkOk(acts, bodycode, 0, ATR.EaOf(BS.CannotExit));
    AR.CompileToBytecodeActionsRepNested(rer, qm, body);
    assert AR.ActionsRepL(rer, qm, acts, bodycode, 0);
    M.LkBodyGroupsEqCapIdsInLooks(body);
    assert S == LL.LkBodyGroups(T.Translate(body));
    LL.LkBodyGroupsConfines(T.Translate(body), S);
    assert LL.LkActsInS(acts, S) by { LL.LkActsInSCons(LS.Areg(T.Translate(body)), [], S); }
    LL.ComputeTrLkConfinedK(rer, acts, inp, LG.Empty, WP.Forward, S);
    assert NB.EncOk(acts, inp, BS.CannotExit) by { NB.EncOkNoChecks(acts, inp, BS.CannotExit); }
    var tstar := ATR.ActionsTreeRepRENested(rer, qm, acts, bodycode, 0, inp, BS.CannotExit, t, S);
    assert TREP.TreeRepRE(qm, tstar, bodycode, 0, inp, false);
    assert TT.TreeThreadRE(rer, qm, bodycode, inp, tstar, 0, false);
    NB.RAFirstLeafOutside(tstar, t, inp, S);

    assert {:split_here} true;
    // ---- the fresh entry VM + PikeInvFullRE --------------------------------
    var ctx := AI.cp_context(cp, str, LAnc.Forward);
    var capture := AReg.init_regs(ncap);
    var look := AReg.init_regs(nlook);
    var quant := AReg.init_regs(nquant);
    var vms := AI.FInitState(bodycode, cp, capture, look, quant, 0, ctx);
    assert ctx.nextchar == AI.get_char(str, cp);
    PSM.InitialPikeInvFullREAtCpNested(rer, qm, body, bodycode, endl, ngroups, str, cp, tstar,
                                       vms, ncap, nlook, nquant);
    assert PIV.ContextOkRE(str, vms.cp, vms.context);
    var fmres := AI.FFindMatch(bodycode, str, vms, ov, LAnc.Forward, cdn);
    var result := fmres.0;

    assert {:split_here} true;
    // ---- machine A: the VM's best is the checked tree's first leaf ----------
    var pts0 := PT.PikeTreeInitialState(tstar, inp);
    PSM.GuardsOkRunStaticNested(qm, body, bodycode, endl, cdn, ov, str);   // (G5a step 2) no guard in this code
    var bestT := PSM.FindMatchSimRENested(rer, qm, body, bodycode, endl, ngroups, str, pts0, vms,
                                          ov, LAnc.Forward, cdn, ncap, nlook, nquant);
    M.TrcREToLinden(pts0, PT.PTS_final(bestT));
    TREP.TreeRepPikeSubtree(qm, tstar, bodycode, 0, inp, false);
    PT.InitPiketreeInv(tstar, inp);
    CR.PikeTreeTrcCorrect(pts0, PT.PTS_final(bestT), LT.FirstLeaf(tstar, inp));
    assert bestT == LT.FirstLeaf(tstar, inp);
    assert PIV.BestMatchRE(body, qm, str, bestT, result);

    assert {:split_here} true;
    var rf := AI.FFindMatchPlus(bodycode, body, plus_bc, str, ov, LAnc.Forward, cp,
                                capture, look, quant, 0, cdn);
    assert rf.0 == (match result
                    case None => None
                    case Some(thread) =>
                      Some(AI.FReconstructPlus(thread, body, plus_bc, str, fmres.1, LAnc.Forward).0));
    M.NoWriteOracleBodyCodeNested(body);
    CM.FFindMatchOvStable(bodycode, str, vms, ov, LAnc.Forward, cdn);
    assert fmres.1 == ov;
    if result.Some? {
      var best := result.value;
      assert PSM.BestLiveRE(body, best);
      SizesCoverFromOk(body, ncap, nlook, nquant);
      var rp := ReadoutAtWinnerAt(qm, body, bodycode, endl, plus_bc, str, cp, ov, cdn, vms,
                                     ncap, nlook, nquant, result);
      assert rf.0 == Some(rp) && rf.1 == ov;

      assert {:split_here} true;
      assert LT.FirstLeaf(t, inp).Some? && bestT.Some?;
      assert PIV.ThreadTracksGm(body, qm, str, best, bestT.value.1);
      assert bestT.value.1 == PIV.GmOfLiveR(body, qm, str, best.capture_regs, best.look_regs, best.quant_regs)
        by { reveal PIV.TieGm; }
      assert PIV.GmOfLive(body, rp.capture_regs, rp.look_regs, rp.quant_regs) == bestT.value.1;
      assert LL.GmAgreeOutside(bestT.value.1, LT.FirstLeaf(t, inp).value.1, S);

      assert {:split_here} true;
      // ---- fresh-run look-bank invariants on the winner; rp keeps the look bank ----
      assert rp.look_regs == best.look_regs;   // ClkFrame
      RL.AInitLaws(nlook);
      assert CM.VmLookClkSet(vms) by {
        assert AI.init_thread(capture, look, quant).look_regs == look;
        forall l: int | AI.get_idx(look.a_cp, l) >= 0 ensures AI.get_idx(look.a_clk, l) >= 0 {
          if 0 <= l < |look.a_cp| { assert look.a_cp[l] == -1; }
        }
      }
      CM.FFindMatchLookClkSet(bodycode, str, vms, ov, LAnc.Forward, cdn);
      assert CM.VmLookCpSet(vms) by {
        forall l: int | AI.get_idx(look.a_clk, l) >= 0 ensures AI.get_idx(look.a_cp, l) >= 0 {
          if 0 <= l < |look.a_clk| { assert look.a_clk[l] == -1; }
        }
      }
      CM.FFindMatchLookCpSet(bodycode, str, vms, ov, LAnc.Forward, cdn);
      assert CM.VmLookCpOk(vms, |str|) by {
        forall l: int ensures AI.get_idx(look.a_cp, l) <= |str| {
          if 0 <= l < |look.a_cp| { assert look.a_cp[l] == -1; }
        }
      }
      CM.FFindMatchLookCpOk(bodycode, str, vms, ov, LAnc.Forward, cdn);
    } else {
      assert rf.0.None? && rf.1 == ov;
      assert bestT.None? && LT.FirstLeaf(t, inp).None?;
    }
  }

  // =========================================================================
  // 2S. (G5b-1) The S forms: a row body that may hold a greedy CDN plus. The run's guards read the table
  // (`PSM.GuardsOkRun`, the caller's premise: N1 `CG.GuardsOkRunRow` above this member); the winner's stamps
  // have empty paths (`PSM.StampPathOk`, from `PSM.FindMatchSimRECdn`), which the S readout consumes.
  // =========================================================================

  /** A3, S. */
  lemma ReadoutAtWinnerAtS(qm: AR.QMap, body: R.regex, code: RB.code, endl: nat, plus: seq<RB.code>,
                           str: string, cp: nat, ov: LOr.OracleView, cdn: LCdn.cdns, inits: AI.VmState,
                           ncap: int, nlook: int, nquant: int, result: Option<AI.Thread>)
    returns (rp: AI.Thread)
    requires code == CP.compile_to_bytecode(body)
    requires T.TransWf(body) && NR.NestedFragmentCdnRE(body) && RF.StampLooksCapFreeRE(body)   // (G5b-3)
    requires PIV.CapUnique(body) && PIV.QuantUnique(body) && LTB.LookUnique(body)
    requires NRC.CdnTopRE(body) && NRR.PlusTableOkS(body, plus)
    requires AR.QmapOk(body, qm) && qm.ov == ov
    requires NR.NfaRepRE(body, code, 0, endl) && |code| == endl + 1 && NR.GetPcRE(code, endl) == Some(RB.Accept)
    requires ncap >= 0 && nlook >= 0 && nquant >= 0
    requires SizesCover(body, ncap, nlook, nquant)
    requires cp <= |str|
    requires inits == AI.FInitState(code, cp, AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant),
                                    0, AI.cp_context(cp, str, LAnc.Forward))
    requires result == AI.FFindMatch(code, str, inits, ov, LAnc.Forward, cdn).0
    requires result.Some? && PSM.BestLiveRE(body, result.value)
    requires PSM.StampPathOk(qm, str, result.value.quant_regs.a_cp)
    ensures AI.FFindMatch(code, str, inits, ov, LAnc.Forward, cdn).1 == ov
    ensures var rpp := AI.FReconstructPlus(result.value, body, plus, str, ov, LAnc.Forward);
            rp == rpp.0 && rpp.1 == ov
    ensures rp.pc == result.value.pc && rp.exit_allowed == result.value.exit_allowed
    ensures PIV.GmOfLive(body, rp.capture_regs, rp.look_regs, rp.quant_regs)
            == PIV.GmOfLiveR(body, qm, str, result.value.capture_regs, result.value.look_regs, result.value.quant_regs)
    ensures CM.ThreadRegsWf(rp, ncap, nlook, nquant)
    ensures CM.ThreadRegsWf(result.value, ncap, nlook, nquant)
    // (G5b-3) the reconstruction may re-set lids inside a stamp body (capture-free looks): the frame outside them,
    // and every look-bank invariant the VM winner has
    ensures ClkFrameG4(body, ELk.StampSet(result.value.quant_regs.a_cp), rp, result.value)   // (G4b-1) at the stamped set
    ensures CM.RegsAgreeOutside(rp.look_regs, result.value.look_regs, SBk.DirectLidSetRN(body))
    ensures CM.LookCpsOracleTrue(result.value.look_regs, ov) ==> CM.LookCpsOracleTrue(rp.look_regs, ov)
    ensures CM.LookClkSetWithCp(result.value.look_regs) ==> CM.LookClkSetWithCp(rp.look_regs)
    ensures CM.LookCpSetWithClk(result.value.look_regs) ==> CM.LookCpSetWithClk(rp.look_regs)
    ensures CM.LookCpsLE(result.value.look_regs, |str|) ==> CM.LookCpsLE(rp.look_regs, |str|)
    ensures LR.WinnerLookRec(qm, body, str, result.value, rp)   // (G4b-2) the look record per live stamp
  {
    var best := result.value;
    var ctx := AI.cp_context(cp, str, LAnc.Forward);
    var capture := AReg.init_regs(ncap);
    var look := AReg.init_regs(nlook);
    var quant := AReg.init_regs(nquant);
    var rg: NRC.Regs3 := (best.capture_regs, best.look_regs, best.quant_regs);
    var Q := FRD.StampQids(body);
    assert ctx.nextchar == AI.get_char(str, cp);
    // VM facts of the winning thread
    CM.FInitStateRegsWf(code, cp, ncap, nlook, nquant, 0, ctx);
    M.FFindMatchRegsWf(code, str, inits, ov, LAnc.Forward, cdn, ncap, nlook, nquant);
    assert CM.ThreadRegsWf(best, ncap, nlook, nquant);
    FRD.TrueStampsInStamp(body, code, endl);
    FV.RegsFinalOkInit(ncap, nlook, nquant, |str|, Q);
    assert FV.VmRegsFinalOk(inits, |str|, Q) by {
      forall t0 | t0 in inits.active ensures FV.RegsFinalOk(t0, |str|, Q) {
        assert t0 == AI.init_thread(capture, look, quant);
      }
    }
    FV.FFindMatchRegsFinal(code, str, inits, ov, LAnc.Forward, cdn, Q);
    assert FV.RegsFinalOk(best, |str|, Q);
    assert {:split_here} true;
    // a fresh run sets no capture outside `body`'s own groups
    M.CaptureBytecodeClassifiedCdnOuter(body);
    var Sout := PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(body));
    assert CM.VmCapturesAgree(inits, capture, Sout) by {
      forall t0 | t0 in inits.active ensures CM.RegsAgreeOutside(t0.capture_regs, capture, Sout) {
        assert t0 == AI.init_thread(capture, look, quant);
      }
    }
    CM.FFindMatchCapWriteFrame(code, str, inits, ov, LAnc.Forward, cdn, capture, Sout);
    OnlyCapIdsFromFrameOuter(body, best.capture_regs, ncap);
    assert NRO.OnlyCapIdsSet(body, rg);
    assert {:split_here} true;
    // the local readout premises
    FRA.StampsFinalAtSFromRegsFinalOk(body, best, |str|);
    assert NRR.CapValWf(rg) && FRG.QClkGe(rg) && NRR.WfRegs(rg);
    CoversFromSizes(body, rg, ncap, nlook, nquant);
    assert FRA.ReadoutPreS(qm, body, plus, str, best, ncap, nlook, nquant);
    assert {:split_here} true;
    // THE READOUT (A1) + its frame (A2), and the untouched view
    FRA.FinalReadoutAtS(qm, body, plus, str, best, ncap, nlook, nquant);
    FRA.FinalReadoutFrameAtStamp(qm, body, plus, str, best);
    // (G5b-3) the bank and the look frame outside `LooksQ` (no longer "the look bank is kept")
    var F := SBk.Flags(CM.LookCpsOracleTrue(best.look_regs, ov), CM.LookClkSetWithCp(best.look_regs),
                       CM.LookCpSetWithClk(best.look_regs), CM.LookCpsLE(best.look_regs, |str|), |str|);
    RRA.RowReconAtG4(F, qm, body, plus, str, best, ncap, nlook, nquant);
    M.NoWriteOracleBodyCodeCdn(body);
    CM.FFindMatchOvStable(code, str, inits, ov, LAnc.Forward, cdn);
    rp := AI.FReconstructPlus(best, body, plus, str, ov, LAnc.Forward).0;
    // (G4b-1) the sharp frame at the stamped set, and the replay only raised quant clocks
    assert SL.StampLiveOk(body, best.capture_regs.a_clk, best.quant_regs.a_clk, best.quant_regs.a_cp) by {
      reveal PSM.BestLiveRE();
    }
    FRA.FinalReadoutFrameAtStampE(qm, body, plus, str, best);
    assert ClkFrameG4(body, ELk.StampSet(best.quant_regs.a_cp), rp, best);
    FRA.FinalReadoutLookRecAtS(qm, body, plus, str, best, ncap, nlook, nquant);   // (G4b-2)
  }

  /** `MachineAPre` on the S forms. */
  ghost predicate MachineAPreS(rer: LW.RegExpRecord, qm: AR.QMap, body: R.regex, bodycode: RB.code, endl: nat,
                               str: string, cp: nat, ov: LOr.OracleView, plus_bc: seq<RB.code>,
                               ncap: int, nlook: int, nquant: int) {
    PSM.StaticCoreCdnRE(qm, body, bodycode, endl)
    && PSM.SizesOkRE(body, ncap, nlook, nquant)
    && nlook >= 0
    && (forall l: nat :: l in LTB.LookIds(body) ==> l < nlook)
    && LTB.LookUnique(body)
    && qm.ov == ov && !rer.multiline && !rer.ignoreCase
    && cp <= |str| && bodycode == CP.compile_to_bytecode(body)
    && NRC.CdnTopRE(body) && NRR.PlusTableOkS(body, plus_bc) && RF.StampLooksCapFreeRE(body)   // (G5b-3)
  }

  /** Machine A at a body, S: the body may hold a greedy CDN plus. */
  lemma MachineAAtS(rer: LW.RegExpRecord, qm: AR.QMap, body: R.regex, bodycode: RB.code, endl: nat, ngroups: nat,
                    str: string, cp: nat, ov: LOr.OracleView, cdn: LCdn.cdns, plus_bc: seq<RB.code>,
                    ncap: int, nlook: int, nquant: int)
    requires MachineAPreS(rer, qm, body, bodycode, endl, str, cp, ov, plus_bc, ncap, nlook, nquant)
    requires PSM.GuardsOkRun(qm, bodycode, cdn, ov, str)   // (G5b-1) N1 at the row, from the caller
    requires LL.OracleOkSuffix(rer, qm, PIV.InpOfCp(str, cp))
    ensures
      var inp := PIV.InpOfCp(str, cp);
      var t := LFU.ComputeTr(rer, [LS.Areg(T.Translate(body))], inp, LG.Empty, WP.Forward);
      var rr := AI.FFindMatchPlus(bodycode, body, plus_bc, str, ov, LAnc.Forward, cp,
                                  AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant), 0, cdn);
      rr.1 == ov
      && (rr.0.Some? <==> LT.FirstLeaf(t, inp).Some?)
      && (rr.0.Some? ==>
            LL.GmAgreeOutside(PIV.GmOfLive(body, rr.0.value.capture_regs, rr.0.value.look_regs, rr.0.value.quant_regs),
                              LT.FirstLeaf(t, inp).value.1, LL.LkBodyGroups(T.Translate(body)))
            && CM.ThreadRegsWf(rr.0.value, ncap, nlook, nquant)
            && CM.LookClkSetWithCp(rr.0.value.look_regs)
            && CM.LookCpSetWithClk(rr.0.value.look_regs)
            && CM.LookCpsLE(rr.0.value.look_regs, |str|))
  {
    var inp := PIV.InpOfCp(str, cp);
    var acts := [LS.Areg(T.Translate(body))];
    var S := PIV.CapIdsInLooks(body);

    // ---- the spec tree ----------------------------------------------------
    LFU.ComputeTrIsTree(rer, acts, inp, LG.Empty, WP.Forward);
    var t := LFU.ComputeTr(rer, acts, inp, LG.Empty, WP.Forward);
    assert LS.IsTree(rer, acts, inp, LG.Empty, WP.Forward, t);
    EL.TranslateFragmentPikeLkRecCdn(body);
    EL.BooleanCorrectLkRec(rer, T.Translate(body), inp, t);
    assert forall i :: 0 <= i < |acts| ==> !acts[i].Acheck?;
    M.BoolTreeLbIrrel(rer, acts, inp, BS.CanExit, BS.CannotExit, t);
    assert EL.BoolTreeLk(rer, acts, inp, BS.CannotExit, t);

    assert {:split_here} true;
    // ---- the CHECKED tree ---------------------------------------------------
    WkE.WalkOkEntryCdn(body);
    assert EL.PikeLkActionsRec(acts) by {
      assert acts == acts + [];
      assert EL.PikeLkActionsRec([]);
      EL.PikeLkActionsRecConsIff(LS.Areg(T.Translate(body)), []);
    }
    assert WO.WalkOk(acts, bodycode, 0, ATR.EaOf(BS.CannotExit));
    AR.CompileToBytecodeActionsRepCdn(rer, qm, body);
    assert AR.ActionsRepL(rer, qm, acts, bodycode, 0);
    M.LkBodyGroupsEqCapIdsInLooks(body);
    assert S == LL.LkBodyGroups(T.Translate(body));
    LL.LkBodyGroupsConfines(T.Translate(body), S);
    assert LL.LkActsInS(acts, S) by { LL.LkActsInSCons(LS.Areg(T.Translate(body)), [], S); }
    LL.ComputeTrLkConfinedK(rer, acts, inp, LG.Empty, WP.Forward, S);
    assert NB.EncOk(acts, inp, BS.CannotExit) by { NB.EncOkNoChecks(acts, inp, BS.CannotExit); }
    var tstar := ATR.ActionsTreeRepRENested(rer, qm, acts, bodycode, 0, inp, BS.CannotExit, t, S);
    assert TREP.TreeRepRE(qm, tstar, bodycode, 0, inp, false);
    assert TT.TreeThreadRE(rer, qm, bodycode, inp, tstar, 0, false);
    NB.RAFirstLeafOutside(tstar, t, inp, S);

    assert {:split_here} true;
    // ---- the fresh entry VM + PikeInvFullRE --------------------------------
    var ctx := AI.cp_context(cp, str, LAnc.Forward);
    var capture := AReg.init_regs(ncap);
    var look := AReg.init_regs(nlook);
    var quant := AReg.init_regs(nquant);
    var vms := AI.FInitState(bodycode, cp, capture, look, quant, 0, ctx);
    assert ctx.nextchar == AI.get_char(str, cp);
    PSM.InitialPikeInvFullREAtCpCdn(rer, qm, body, bodycode, endl, ngroups, str, cp, tstar,
                                    vms, ncap, nlook, nquant);
    assert PIV.ContextOkRE(str, vms.cp, vms.context);
    var fmres := AI.FFindMatch(bodycode, str, vms, ov, LAnc.Forward, cdn);
    var result := fmres.0;

    assert {:split_here} true;
    // ---- machine A: the VM's best is the checked tree's first leaf ----------
    var pts0 := PT.PikeTreeInitialState(tstar, inp);
    var bestT := PSM.FindMatchSimRECdn(rer, qm, body, bodycode, endl, ngroups, str, pts0, vms,
                                       ov, LAnc.Forward, cdn, ncap, nlook, nquant);
    M.TrcREToLinden(pts0, PT.PTS_final(bestT));
    TREP.TreeRepPikeSubtree(qm, tstar, bodycode, 0, inp, false);
    PT.InitPiketreeInv(tstar, inp);
    CR.PikeTreeTrcCorrect(pts0, PT.PTS_final(bestT), LT.FirstLeaf(tstar, inp));
    assert bestT == LT.FirstLeaf(tstar, inp);
    assert PIV.BestMatchRE(body, qm, str, bestT, result);

    assert {:split_here} true;
    var rf := AI.FFindMatchPlus(bodycode, body, plus_bc, str, ov, LAnc.Forward, cp,
                                capture, look, quant, 0, cdn);
    assert rf.0 == (match result
                    case None => None
                    case Some(thread) =>
                      Some(AI.FReconstructPlus(thread, body, plus_bc, str, fmres.1, LAnc.Forward).0));
    M.NoWriteOracleBodyCodeCdn(body);
    CM.FFindMatchOvStable(bodycode, str, vms, ov, LAnc.Forward, cdn);
    assert fmres.1 == ov;
    if result.Some? {
      var best := result.value;
      assert PSM.BestLiveRE(body, best) && PSM.StampPathOk(qm, str, best.quant_regs.a_cp);
      SizesCoverFromOk(body, ncap, nlook, nquant);
      var rp := ReadoutAtWinnerAtS(qm, body, bodycode, endl, plus_bc, str, cp, ov, cdn, vms,
                                   ncap, nlook, nquant, result);
      assert rf.0 == Some(rp) && rf.1 == ov;

      assert {:split_here} true;
      assert LT.FirstLeaf(t, inp).Some? && bestT.Some?;
      assert PIV.ThreadTracksGm(body, qm, str, best, bestT.value.1);
      assert bestT.value.1 == PIV.GmOfLiveR(body, qm, str, best.capture_regs, best.look_regs, best.quant_regs)
        by { reveal PIV.TieGm; }
      assert PIV.GmOfLive(body, rp.capture_regs, rp.look_regs, rp.quant_regs) == bestT.value.1;
      assert LL.GmAgreeOutside(bestT.value.1, LT.FirstLeaf(t, inp).value.1, S);

      assert {:split_here} true;
      // ---- fresh-run look-bank invariants on the winner; (G5b-3) rp keeps each of them ----
      RL.AInitLaws(nlook);
      assert CM.VmLookClkSet(vms) by {
        assert AI.init_thread(capture, look, quant).look_regs == look;
        forall l: int | AI.get_idx(look.a_cp, l) >= 0 ensures AI.get_idx(look.a_clk, l) >= 0 {
          if 0 <= l < |look.a_cp| { assert look.a_cp[l] == -1; }
        }
      }
      CM.FFindMatchLookClkSet(bodycode, str, vms, ov, LAnc.Forward, cdn);
      assert CM.VmLookCpSet(vms) by {
        forall l: int | AI.get_idx(look.a_clk, l) >= 0 ensures AI.get_idx(look.a_cp, l) >= 0 {
          if 0 <= l < |look.a_clk| { assert look.a_clk[l] == -1; }
        }
      }
      CM.FFindMatchLookCpSet(bodycode, str, vms, ov, LAnc.Forward, cdn);
      assert CM.VmLookCpOk(vms, |str|) by {
        forall l: int ensures AI.get_idx(look.a_cp, l) <= |str| {
          if 0 <= l < |look.a_cp| { assert look.a_cp[l] == -1; }
        }
      }
      CM.FFindMatchLookCpOk(bodycode, str, vms, ov, LAnc.Forward, cdn);
    } else {
      assert rf.0.None? && rf.1 == ov;
      assert bestT.None? && LT.FirstLeaf(t, inp).None?;
    }
  }

  /** `M.LkReplayMatchesSpecNested` on the plus match: the passing gate's `LkResult` agrees with the fresh
      plus match on the body's OUTER groups. */
  lemma LkReplayMatchesSpecPlus(
    rer: LW.RegExpRecord, qm: AR.QMap, body: R.regex, bodycode: RB.code, endl: nat, ngroups: nat,
    str: string, cp: nat, ov: LOr.OracleView, cdn: LCdn.cdns, plus_bc: seq<RB.code>,
    tlk: LT.Tree, gmMain: LG.GroupMap, ncap: int, nlook: int, nquant: int)
    requires MachineAPre(rer, qm, body, bodycode, endl, str, cp, ov, plus_bc, ncap, nlook, nquant)
    requires LL.OracleOkSuffix(rer, qm, PIV.InpOfCp(str, cp))
    requires tlk == LFU.ComputeTr(rer, [LS.Areg(T.Translate(body))], PIV.InpOfCp(str, cp), gmMain, WP.Forward)
    requires M.GmAgreeOn(gmMain, LG.Empty, set g | g in L.DefGroups(T.Translate(body)))
    ensures var inp := PIV.InpOfCp(str, cp);
            var rf := AI.FFindMatchPlus(bodycode, body, plus_bc, str, ov, LAnc.Forward, cp,
                                        AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant),
                                        0, cdn).0;
            var Sout := set g | g in L.DefGroups(T.Translate(body)) && g !in LL.LkBodyGroups(T.Translate(body));
            var lkr := LS.LkResult(T.TrLookaround(R.Lookahead), tlk, gmMain, inp);
            (rf.None? <==> lkr.None?)
            && (rf.Some? ==>
                  lkr.Some?
                  && M.GmAgreeOn(lkr.value,
                                 PIV.GmOfLive(body, rf.value.capture_regs, rf.value.look_regs, rf.value.quant_regs),
                                 Sout))
  {
    var inp := PIV.InpOfCp(str, cp);
    var tr := T.Translate(body);
    var Sd := set g | g in L.DefGroups(tr);
    MachineAAt(rer, qm, body, bodycode, endl, ngroups, str, cp, ov, cdn, plus_bc, ncap, nlook, nquant);
    var tEmpty := LFU.ComputeTr(rer, [LS.Areg(tr)], inp, LG.Empty, WP.Forward);
    // tlk (at gmMain) == tEmpty (at Empty): depth-k group-map independence.
    EL.TranslateFragmentPikeLkRec(body);
    EL.ComputeTrGmIndepLkRec(rer, tr, inp, gmMain, WP.Forward);
    assert tlk == tEmpty;
    assert LT.FirstLeaf(tlk, inp) == LT.TreeRes(tlk, LG.Empty, inp, WP.Forward);
    // spec: TreeRes at gmMain agrees with TreeRes at Empty on Sd.
    M.TreeResGmFrameRec(tlk, gmMain, LG.Empty, inp, WP.Forward, Sd);
    assert L.Positivity(T.TrLookaround(R.Lookahead)) && L.LkDir(T.TrLookaround(R.Lookahead)) == WP.Forward;
  }

  /** `LiftSimCore.FreshBodyMatchGmOuter` on the plus match: the fresh plus match records no inner-look
      group (the VM and the reconstruction write captures only outside `body`'s looks). */
  lemma FreshPlusGmOuter(body: R.regex, bodycode: RB.code, str: string, cp: nat, ov: LOr.OracleView,
                         cdn: LCdn.cdns, plus_bc: seq<RB.code>, ncap: int, nlook: int, nquant: int)
    requires M.RowLAStatics(body, plus_bc)
    requires bodycode == CP.compile_to_bytecode(body)
    requires cp <= |str| && ncap >= 0 && nlook >= 0 && nquant >= 0
    ensures var rf := AI.FFindMatchPlus(bodycode, body, plus_bc, str, ov, LAnc.Forward, cp,
                                        AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant),
                                        0, cdn).0;
            rf.Some? ==>
              forall g: nat :: g in PIV.CapIdsInLooks(body) ==>
                                 g !in PIV.GmOfLive(body, rf.value.capture_regs, rf.value.look_regs, rf.value.quant_regs)
  {
    var capture := AReg.init_regs(ncap);
    var look := AReg.init_regs(nlook);
    var quant := AReg.init_regs(nquant);
    RL.AInitLaws(ncap); RL.AInitLaws(nlook); RL.AInitLaws(nquant);
    PIV.CapRegWfInit(ncap);
    assert CM.LookCpsLE(look, |str|) by {
      forall l: int ensures AI.get_idx(look.a_cp, l) <= |str| { if 0 <= l < |look.a_cp| { assert look.a_cp[l] == -1; } }
    }
    assert (forall k :: AI.get_idx(quant.a_cp, k) < 0) && (forall k :: AI.get_idx(quant.a_clk, k) >= -1) by {
      forall k ensures AI.get_idx(quant.a_cp, k) < 0 && AI.get_idx(quant.a_clk, k) >= -1 {
        if 0 <= k < |quant.a_cp| { assert quant.a_cp[k] == -1; }
        if 0 <= k < |quant.a_clk| { assert quant.a_clk[k] == -1; }
      }
    }
    M.ReplayPlusRowLA(bodycode, str, ov, cdn, plus_bc, cp, capture, look, quant, body, ncap, nlook, nquant);
    var rf := AI.FFindMatchPlus(bodycode, body, plus_bc, str, ov, LAnc.Forward, cp, capture, look, quant, 0, cdn).0;
    if rf.Some? {
      var caps := rf.value.capture_regs;
      var Sc := PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(body));
      assert CM.RegsAgreeOutside(caps, capture, Sc);
      assert PIV.CapRegWf(caps);
      reveal M.RowLAStatics();
      PIV.CapIdsLooksDisjoint(body);
      assert PIV.LooksCapUnset(body, caps.a_clk) by {
        forall c: nat | c in PIV.CapIdsInLooks(body)
          ensures AI.get_idx(caps.a_clk, CP.start_reg(c)) < 0
        {
          assert CP.start_reg(c as int) !in Sc by {
            if CP.start_reg(c as int) in Sc {
              if CP.start_reg(c as int) in (set cid | cid in PIV.CapIdsOutsideLooks(body) :: CP.start_reg(cid as int)) {
                var cid: nat :| cid in PIV.CapIdsOutsideLooks(body) && CP.start_reg(cid as int) == CP.start_reg(c as int);
                assert cid == c;
                assert c in PIV.CapIdsOutsideLooks(body) * PIV.CapIdsInLooks(body);
              } else {
                var cid: nat :| cid in PIV.CapIdsOutsideLooks(body) && CP.end_reg(cid as int) == CP.start_reg(c as int);
                assert 2 * (cid as int) + 1 == 2 * (c as int);
              }
              assert false;
            }
          }
          assert AI.get_idx(caps.a_clk, CP.start_reg(c as int))
              == AI.get_idx(capture.a_clk, CP.start_reg(c as int));
        }
      }
      forall g: nat | g in PIV.CapIdsInLooks(body)
        ensures g !in PIV.GmOfLive(body, caps, rf.value.look_regs, rf.value.quant_regs)
      {
        PIV.GmOfLiveInsideLookAbsent(body, caps, rf.value.look_regs, rf.value.quant_regs, g);
      }
    }
  }

  /** (G5b-1) `LkReplayMatchesSpecPlus` on the S forms. */
  lemma LkReplayMatchesSpecPlusS(
    rer: LW.RegExpRecord, qm: AR.QMap, body: R.regex, bodycode: RB.code, endl: nat, ngroups: nat,
    str: string, cp: nat, ov: LOr.OracleView, cdn: LCdn.cdns, plus_bc: seq<RB.code>,
    tlk: LT.Tree, gmMain: LG.GroupMap, ncap: int, nlook: int, nquant: int)
    requires MachineAPreS(rer, qm, body, bodycode, endl, str, cp, ov, plus_bc, ncap, nlook, nquant)
    requires PSM.GuardsOkRun(qm, bodycode, cdn, ov, str)
    requires LL.OracleOkSuffix(rer, qm, PIV.InpOfCp(str, cp))
    requires tlk == LFU.ComputeTr(rer, [LS.Areg(T.Translate(body))], PIV.InpOfCp(str, cp), gmMain, WP.Forward)
    requires M.GmAgreeOn(gmMain, LG.Empty, set g | g in L.DefGroups(T.Translate(body)))
    ensures var inp := PIV.InpOfCp(str, cp);
            var rf := AI.FFindMatchPlus(bodycode, body, plus_bc, str, ov, LAnc.Forward, cp,
                                        AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant),
                                        0, cdn).0;
            var Sout := set g | g in L.DefGroups(T.Translate(body)) && g !in LL.LkBodyGroups(T.Translate(body));
            var lkr := LS.LkResult(T.TrLookaround(R.Lookahead), tlk, gmMain, inp);
            (rf.None? <==> lkr.None?)
            && (rf.Some? ==>
                  lkr.Some?
                  && M.GmAgreeOn(lkr.value,
                                 PIV.GmOfLive(body, rf.value.capture_regs, rf.value.look_regs, rf.value.quant_regs),
                                 Sout))
  {
    var inp := PIV.InpOfCp(str, cp);
    var tr := T.Translate(body);
    var Sd := set g | g in L.DefGroups(tr);
    MachineAAtS(rer, qm, body, bodycode, endl, ngroups, str, cp, ov, cdn, plus_bc, ncap, nlook, nquant);
    var tEmpty := LFU.ComputeTr(rer, [LS.Areg(tr)], inp, LG.Empty, WP.Forward);
    // tlk (at gmMain) == tEmpty (at Empty): depth-k group-map independence.
    EL.TranslateFragmentPikeLkRecCdn(body);
    EL.ComputeTrGmIndepLkRec(rer, tr, inp, gmMain, WP.Forward);
    assert tlk == tEmpty;
    assert LT.FirstLeaf(tlk, inp) == LT.TreeRes(tlk, LG.Empty, inp, WP.Forward);
    // spec: TreeRes at gmMain agrees with TreeRes at Empty on Sd.
    M.TreeResGmFrameRec(tlk, gmMain, LG.Empty, inp, WP.Forward, Sd);
    assert L.Positivity(T.TrLookaround(R.Lookahead)) && L.LkDir(T.TrLookaround(R.Lookahead)) == WP.Forward;
  }
  /** (G5b-1) `FreshPlusGmOuter` on the S forms. */
  lemma FreshPlusGmOuterS(body: R.regex, bodycode: RB.code, str: string, cp: nat, ov: LOr.OracleView,
                         cdn: LCdn.cdns, plus_bc: seq<RB.code>, ncap: int, nlook: int, nquant: int)
    requires M.RowLAStaticsS(body, plus_bc)
    requires bodycode == CP.compile_to_bytecode(body)
    requires cp <= |str| && ncap >= 0 && nlook >= 0 && nquant >= 0
    ensures var rf := AI.FFindMatchPlus(bodycode, body, plus_bc, str, ov, LAnc.Forward, cp,
                                        AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant),
                                        0, cdn).0;
            rf.Some? ==>
              forall g: nat :: g in PIV.CapIdsInLooks(body) ==>
                                 g !in PIV.GmOfLive(body, rf.value.capture_regs, rf.value.look_regs, rf.value.quant_regs)
  {
    var capture := AReg.init_regs(ncap);
    var look := AReg.init_regs(nlook);
    var quant := AReg.init_regs(nquant);
    RL.AInitLaws(ncap); RL.AInitLaws(nlook); RL.AInitLaws(nquant);
    PIV.CapRegWfInit(ncap);
    assert CM.LookCpsLE(look, |str|) by {
      forall l: int ensures AI.get_idx(look.a_cp, l) <= |str| { if 0 <= l < |look.a_cp| { assert look.a_cp[l] == -1; } }
    }
    assert (forall k :: AI.get_idx(quant.a_cp, k) < 0) && (forall k :: AI.get_idx(quant.a_clk, k) >= -1) by {
      forall k ensures AI.get_idx(quant.a_cp, k) < 0 && AI.get_idx(quant.a_clk, k) >= -1 {
        if 0 <= k < |quant.a_cp| { assert quant.a_cp[k] == -1; }
        if 0 <= k < |quant.a_clk| { assert quant.a_clk[k] == -1; }
      }
    }
    M.ReplayPlusRowLAS(bodycode, str, ov, cdn, plus_bc, cp, capture, look, quant, body, ncap, nlook, nquant);
    var rf := AI.FFindMatchPlus(bodycode, body, plus_bc, str, ov, LAnc.Forward, cp, capture, look, quant, 0, cdn).0;
    if rf.Some? {
      var caps := rf.value.capture_regs;
      var Sc := PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(body));
      assert CM.RegsAgreeOutside(caps, capture, Sc);
      assert PIV.CapRegWf(caps);
      reveal M.RowLAStaticsS();
      PIV.CapIdsLooksDisjoint(body);
      assert PIV.LooksCapUnset(body, caps.a_clk) by {
        forall c: nat | c in PIV.CapIdsInLooks(body)
          ensures AI.get_idx(caps.a_clk, CP.start_reg(c)) < 0
        {
          assert CP.start_reg(c as int) !in Sc by {
            if CP.start_reg(c as int) in Sc {
              if CP.start_reg(c as int) in (set cid | cid in PIV.CapIdsOutsideLooks(body) :: CP.start_reg(cid as int)) {
                var cid: nat :| cid in PIV.CapIdsOutsideLooks(body) && CP.start_reg(cid as int) == CP.start_reg(c as int);
                assert cid == c;
                assert c in PIV.CapIdsOutsideLooks(body) * PIV.CapIdsInLooks(body);
              } else {
                var cid: nat :| cid in PIV.CapIdsOutsideLooks(body) && CP.end_reg(cid as int) == CP.start_reg(c as int);
                assert 2 * (cid as int) + 1 == 2 * (c as int);
              }
              assert false;
            }
          }
          assert AI.get_idx(caps.a_clk, CP.start_reg(c as int))
              == AI.get_idx(capture.a_clk, CP.start_reg(c as int));
        }
      }
      forall g: nat | g in PIV.CapIdsInLooks(body)
        ensures g !in PIV.GmOfLive(body, caps, rf.value.look_regs, rf.value.quant_regs)
      {
        PIV.GmOfLiveInsideLookAbsent(body, caps, rf.value.look_regs, rf.value.quant_regs, g);
      }
    }
  }
}
