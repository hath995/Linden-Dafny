// G3b probe (2026-11-12): machine A's first half and the lookbehind row lemma.
module LindenElkMachineABack {
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
  import ELk = LindenElkEmptyLooks      // (G4b-1b) the frame at the stamped set
  import SL = LindenElkStampLive
  import FRA = LindenElkFinalReadoutAt
  import RRA = LindenElkRowReconAt
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
  import MA = LindenElkMachineA
  import MIR = LindenElkMirror
  import FST = LindenElkFlipStatics
  import FR = LindenElkFlipRev
  import FM = LindenElkFlipMirror
  import FK = LindenElkFlipKeystone
  import FO = LindenElkFlipOracle
  import FG = LindenElkFlipGate
  import OG = LindenElkFlipOracleG
  import KG = LindenElkFlipKeystoneG
  import OE = LindenElkOracleEntry
  import BV = LindenElkBackValue
  import LBV = LindenLookBehindValue
  import LBK = LindenLookBehindKeystone
  import BGM = LindenBackGmMirror
  import SD = LindenSpanDuality
  import TML = LindenElkTreeMirrorLk
  import MW = LindenElkMirrorWorld
  import SM = LindenElkStampMirror
  import DB = LindenElkDirBlind
  import W = LindenElkBackRowResidue
  import WR = LindenElkBackRowPremises
  import WS = LindenElkBackRowStatics
  import TB = LindenElkMirrorPlus
  import FS = FunctionalSemantics
  import CMr = LindenElkCdnMirror      // (G5b-2) the mirrored CDN table
  import CS = LindenElkCdnSound
  import CTT = LindenElkCdnTreeTie
  import SBk = LindenElkStampBank      // (G5b-3)

  /** Machine A's first half: the fresh forward VM winner of `body` at `cp` against the spec first leaf.
      No plus table, no reconstruction. (`MachineAAt` up to its readout.) */
  lemma MachineAWinner(rer: LW.RegExpRecord, qm: AR.QMap, body: R.regex, bodycode: RB.code, endl: nat, ngroups: nat,
                       str: string, cp: nat, ov: LOr.OracleView, cdn: LCdn.cdns,
                       ncap: int, nlook: int, nquant: int)
    requires PSM.StaticCoreNestedRE(qm, body, bodycode, endl)
    requires PSM.SizesOkRE(body, ncap, nlook, nquant)
    requires qm.ov == ov && !rer.multiline && !rer.ignoreCase
    requires cp <= |str| && bodycode == CP.compile_to_bytecode(body)
    requires LL.OracleOkSuffix(rer, qm, PIV.InpOfCp(str, cp))
    ensures
      var inp := PIV.InpOfCp(str, cp);
      var t := LFU.ComputeTr(rer, [LS.Areg(T.Translate(body))], inp, LG.Empty, WP.Forward);
      var result := AI.FFindMatch(bodycode, str,
                      AI.FInitState(bodycode, cp, AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant),
                                    0, AI.cp_context(cp, str, LAnc.Forward)), ov, LAnc.Forward, cdn).0;
      (result.Some? <==> LT.FirstLeaf(t, inp).Some?)
      && (result.Some? ==>
            PSM.BestLiveRE(body, result.value)
            && LL.GmAgreeOutside(PIV.GmOfLiveR(body, qm, str, result.value.capture_regs, result.value.look_regs,
                                               result.value.quant_regs),
                                 LT.FirstLeaf(t, inp).value.1, LL.LkBodyGroups(T.Translate(body))))
  {
    var inp := PIV.InpOfCp(str, cp);
    var acts := [LS.Areg(T.Translate(body))];
    var S := PIV.CapIdsInLooks(body);
    LFU.ComputeTrIsTree(rer, acts, inp, LG.Empty, WP.Forward);
    var t := LFU.ComputeTr(rer, acts, inp, LG.Empty, WP.Forward);
    assert LS.IsTree(rer, acts, inp, LG.Empty, WP.Forward, t);
    EL.TranslateFragmentPikeLkRec(body);
    EL.BooleanCorrectLkRec(rer, T.Translate(body), inp, t);
    assert forall i :: 0 <= i < |acts| ==> !acts[i].Acheck?;
    M.BoolTreeLbIrrel(rer, acts, inp, BS.CanExit, BS.CannotExit, t);
    assert EL.BoolTreeLk(rer, acts, inp, BS.CannotExit, t);

    assert {:split_here} true;
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
    if result.Some? {
      var best := result.value;
      assert LT.FirstLeaf(t, inp).Some? && bestT.Some?;
      assert PIV.ThreadTracksGm(body, qm, str, best, bestT.value.1);
      assert bestT.value.1 == PIV.GmOfLiveR(body, qm, str, best.capture_regs, best.look_regs, best.quant_regs)
        by { reveal PIV.TieGm; }
      assert LL.GmAgreeOutside(bestT.value.1, LT.FirstLeaf(t, inp).value.1, S);
    } else {
      assert bestT.None? && LT.FirstLeaf(t, inp).None?;
    }
  }

  /** (G5b-2) `MachineAWinner` on the Cdn core: the body may hold a greedy CDN plus (its guards are sound by
      the caller's `GuardsOkRun`); the winner's stamps have their empty paths (`StampPathOk`).
      Machine A's first half: the fresh forward VM winner of `body` at `cp` against the spec first leaf.
      No plus table, no reconstruction. (`MachineAAt` up to its readout.) */
  lemma MachineAWinnerS(rer: LW.RegExpRecord, qm: AR.QMap, body: R.regex, bodycode: RB.code, endl: nat, ngroups: nat,
                       str: string, cp: nat, ov: LOr.OracleView, cdn: LCdn.cdns,
                       ncap: int, nlook: int, nquant: int)
    requires PSM.StaticCoreCdnRE(qm, body, bodycode, endl)
    requires PSM.GuardsOkRun(qm, bodycode, cdn, ov, str)   // (G5b-2) N1/N2 at the row, from the caller
    requires PSM.SizesOkRE(body, ncap, nlook, nquant)
    requires qm.ov == ov && !rer.multiline && !rer.ignoreCase
    requires cp <= |str| && bodycode == CP.compile_to_bytecode(body)
    requires LL.OracleOkSuffix(rer, qm, PIV.InpOfCp(str, cp))
    ensures
      var inp := PIV.InpOfCp(str, cp);
      var t := LFU.ComputeTr(rer, [LS.Areg(T.Translate(body))], inp, LG.Empty, WP.Forward);
      var result := AI.FFindMatch(bodycode, str,
                      AI.FInitState(bodycode, cp, AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant),
                                    0, AI.cp_context(cp, str, LAnc.Forward)), ov, LAnc.Forward, cdn).0;
      (result.Some? <==> LT.FirstLeaf(t, inp).Some?)
      && (result.Some? ==>
            PSM.BestLiveRE(body, result.value) && PSM.StampPathOk(qm, str, result.value.quant_regs.a_cp)
            && LL.GmAgreeOutside(PIV.GmOfLiveR(body, qm, str, result.value.capture_regs, result.value.look_regs,
                                               result.value.quant_regs),
                                 LT.FirstLeaf(t, inp).value.1, LL.LkBodyGroups(T.Translate(body))))
  {
    var inp := PIV.InpOfCp(str, cp);
    var acts := [LS.Areg(T.Translate(body))];
    var S := PIV.CapIdsInLooks(body);
    LFU.ComputeTrIsTree(rer, acts, inp, LG.Empty, WP.Forward);
    var t := LFU.ComputeTr(rer, acts, inp, LG.Empty, WP.Forward);
    assert LS.IsTree(rer, acts, inp, LG.Empty, WP.Forward, t);
    EL.TranslateFragmentPikeLkRecCdn(body);
    EL.BooleanCorrectLkRec(rer, T.Translate(body), inp, t);
    assert forall i :: 0 <= i < |acts| ==> !acts[i].Acheck?;
    M.BoolTreeLbIrrel(rer, acts, inp, BS.CanExit, BS.CannotExit, t);
    assert EL.BoolTreeLk(rer, acts, inp, BS.CannotExit, t);

    assert {:split_here} true;
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
    if result.Some? {
      var best := result.value;
      assert LT.FirstLeaf(t, inp).Some? && bestT.Some?;
      assert PIV.ThreadTracksGm(body, qm, str, best, bestT.value.1);
      assert bestT.value.1 == PIV.GmOfLiveR(body, qm, str, best.capture_regs, best.look_regs, best.quant_regs)
        by { reveal PIV.TieGm; }
      assert LL.GmAgreeOutside(bestT.value.1, LT.FirstLeaf(t, inp).value.1, S);
    } else {
      assert bestT.None? && LT.FirstLeaf(t, inp).None?;
    }
  }

  /** THE G3b ROW LEMMA. The fresh BACKWARD plus match of a lookbehind body: its reconstruction reads out
      (real side, real table), and the readout is the raw mirror of a group map `G` that agrees with the
      flipped forward spec leaf outside the body's inner-look groups. */
  lemma BackRowReadout(rer: LW.RegExpRecord, qm: AR.QMap, body: R.regex, str: string, cp: nat,
                       ov: LOr.OracleView, cdns: LCdn.cdns, plus: seq<RB.code>,
                       ncap: int, nlook: int, nquant: int, n: nat)
    returns (G: LG.GroupMap, qmF: AR.QMap, endlF: nat)
    requires T.TransWf(body) && NR.NestedFragmentRE(body)
    requires PIV.CapUnique(body) && PIV.QuantUnique(body) && LTB.LookUnique(body)
    requires PSM.SizesOkRE(body, ncap, nlook, nquant)
    requires forall l: nat :: l in LTB.LookIds(body) ==> l < nlook
    requires NRC.NoCdnPlusRE(body) && RF.CinBodiesLookFreeRE(body) && NRR.PlusTableOk(body, plus)
    requires AR.QmapOk(body, qm)
    requires !rer.ignoreCase && !rer.multiline
    requires n == |str| && cp <= n && |ov| == n + 1
    requires qm.ov == ov && AR.LmapOk(body, qm) && OE.OracleColsOk(rer, qm, str)
    ensures
      var bcB := CP.compile_to_bytecode(R.reverse_regex(body));
      var raB := AI.FFindMatch(bcB, str,
                   AI.FInitState(bcB, cp, AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant), 0,
                                 AI.cp_context(cp, str, LAnc.Backward)), ov, LAnc.Backward, cdns).0;
      var rr := AI.FFindMatchPlus(bcB, body, plus, str, ov, LAnc.Backward, cp,
                                  AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant), 0, cdns);
      var inpF := SD.SwapInput(PIV.InpOfCp(str, cp));
      var t_F := LFU.ComputeTr(rer, [LS.Areg(FM.FlipRevL(T.Translate(body)))], inpF, LG.Empty, WP.Forward);
      rr.1 == ov
      && (rr.0.Some? <==> raB.Some?) && (raB.Some? <==> LT.FirstLeaf(t_F, inpF).Some?)
      && (rr.0.Some? ==>
            PIV.GmOfLive(body, rr.0.value.capture_regs, rr.0.value.look_regs, rr.0.value.quant_regs)
              == PIV.GmOfLiveR(body, qm, str, raB.value.capture_regs, raB.value.look_regs, raB.value.quant_regs)
            && BGM.GmLeN(G, n)
            && PIV.GmOfLive(body, rr.0.value.capture_regs, rr.0.value.look_regs, rr.0.value.quant_regs)
              == BGM.RawMirrorGm(G, n)
            && LL.GmAgreeOutside(G, LT.FirstLeaf(t_F, inpF).value.1, LL.LkBodyGroups(T.Translate(body)))
            && ClkFrame(body, FRD.CinQids(body), rr.0.value, raB.value)
            && CM.ThreadRegsWf(rr.0.value, ncap, nlook, nquant))
    // the flipped side, for callers that read out there too
    ensures |LC.Reverse(str)| == n
    ensures PSM.StaticCoreNestedRE(qmF, FST.FXR(body), CP.compile_to_bytecode(FST.FXR(body)), endlF)
    ensures PSM.SizesOkRE(FST.FXR(body), ncap, nlook, nquant)
    ensures qmF.ov == MIR.MirrorView(ov, n) && OE.OracleColsOk(rer, qmF, LC.Reverse(str))
    ensures
      var bcB := CP.compile_to_bytecode(R.reverse_regex(body));
      var raB := AI.FFindMatch(bcB, str,
                   AI.FInitState(bcB, cp, AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant), 0,
                                 AI.cp_context(cp, str, LAnc.Backward)), ov, LAnc.Backward, cdns).0;
      var bcF := CP.compile_to_bytecode(FST.FXR(body));
      var rfF := AI.FFindMatch(bcF, LC.Reverse(str),
                   AI.FInitState(bcF, n - cp, AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant), 0,
                                 AI.cp_context(n - cp, LC.Reverse(str), LAnc.Forward)),
                   MIR.MirrorView(ov, n), LAnc.Forward, MIR.SwapAnchorsCdns(cdns)).0;
      (raB.Some? <==> rfF.Some?)
      && (raB.Some? ==>
            PSM.BestLiveRE(FST.FXR(body), rfF.value)
            && rfF.value == MIR.MirrorThread(raB.value, n)
            && G == PIV.GmOfLiveR(FST.FXR(body), qmF, LC.Reverse(str), rfF.value.capture_regs, rfF.value.look_regs,
                                  rfF.value.quant_regs))
  {
    G := map[];
    var tr := T.Translate(body);
    var reF := FST.FXR(body);
    MIR.ReverseLen(str);
    var rstr := LC.Reverse(str);
    var mcp := MIR.Mirror(cp, n);
    var mcpN: nat := n - cp;
    assert mcp == mcpN as int && 0 <= mcp <= n && |rstr| == n;
    var ov' := MIR.MirrorView(ov, n);
    var cdns' := MIR.SwapAnchorsCdns(cdns);
    var bcF := CP.compile_to_bytecode(reF);
    var inpF := PIV.InpOfCp(rstr, mcpN);
    LBV.InpOfCpSwap(str, cp, n);
    assert inpF == SD.SwapInput(PIV.InpOfCp(str, cp));
    var capture := AReg.init_regs(ncap);
    var look := AReg.init_regs(nlook);
    var quant := AReg.init_regs(nquant);
    var Q := FRD.CinQids(body);

    // ---- statics of the flipped body + its oracle (LBEngineLeafFlipG's preamble) ----
    FST.FXRStructural(body);
    var endl': nat;
    qmF, endl' := WS.FlipXRevStaticCoreNested(body, ov', ncap, nlook, nquant);
    endlF := endl';
    var qmB := AR.QMap(map[], OE.LmOf(body), ov, map[]);
    OE.LmapOkOfLmOf(body, qmB);
    FK.LmapOkEntriesMatchLmOf(body, qm);
    assert OE.OracleColsOk(rer, qmB, str) by {
      forall k: int | 0 <= k <= |str| ensures LL.OracleOkAt(rer, qmB, T.InputAt(str, k)) {
        FST.OracleOkAtSubmap(rer, qm, qmB, T.InputAt(str, k));
      }
    }
    KG.LmOfBodiesNoBackref(body);
    assert OG.QmBodiesNoBackref(qmB);
    FST.FlipLooksMapTie(qmB, qmF);
    assert |qmB.ov| == |str| + 1 && qmF.ov == MIR.MirrorView(qmB.ov, |str|);
    OG.MirrorOracleColsOkG(rer, qmB, qmF, str);
    FO.ColsOkToSuffix(rer, qmF, rstr, mcpN);
    assert PIV.InpOfCp(rstr, mcpN) == T.InputAt(rstr, mcpN);
    assert LL.OracleOkSuffix(rer, qmF, inpF);

    assert {:split_here} true;
    // ---- machine A's first half at the flipped body ----
    MachineAWinner(rer, qmF, reF, bcF, endl', 0, rstr, mcpN, ov', cdns', ncap, nlook, nquant);
    FST.TranslateFlipXRev(body);
    assert T.Translate(reF) == FM.FlipRevL(tr);
    FST.LkBodyGroupsFlipL(SD.RevL(tr));
    TML.LkBodyGroupsRevL(tr);
    assert LL.LkBodyGroups(T.Translate(reF)) == LL.LkBodyGroups(tr);
    var t_F := LFU.ComputeTr(rer, [LS.Areg(FM.FlipRevL(tr))], inpF, LG.Empty, WP.Forward);
    var ctxF := AI.cp_context(mcp, rstr, LAnc.Forward);
    var initsF := AI.FInitState(bcF, mcp, capture, look, quant, 0, ctxF);
    var rfF := AI.FFindMatch(bcF, rstr, initsF, ov', LAnc.Forward, cdns').0;
    assert rfF.Some? <==> LT.FirstLeaf(t_F, inpF).Some?;

    assert {:split_here} true;
    // ---- the tie: rfF == MirrorThread(raB) ----
    var bcB := CP.compile_to_bytecode(R.reverse_regex(body));
    var ctxB := AI.cp_context(cp, str, LAnc.Backward);
    var initsB := AI.FInitState(bcB, cp, capture, look, quant, 0, ctxB);
    var fmB := AI.FFindMatch(bcB, str, initsB, ov, LAnc.Backward, cdns);
    var raB := fmB.0;
    MIR.MirrorInitRegs(ncap, n); MIR.MirrorInitRegs(nlook, n); MIR.MirrorInitRegs(nquant, n);
    BV.BackwardReplayMirrorNested(body, str, cp, capture, look, quant, ov, cdns, n);
    FR.FlipCompileToBytecode(FST.XRV(body));
    assert bcF == CP.compile_to_bytecode(FST.XRV(body));
    assert raB.None? <==> rfF.None?;
    // the view is kept by the backward run
    M.ReverseNestedPackage(body);
    M.NoWriteOracleBodyCodeNested(R.reverse_regex(body));
    assert ctxB.nextchar == AI.get_char(str, cp - 1);
    CM.FFindMatchOvStable(bcB, str, initsB, ov, LAnc.Backward, cdns);
    assert fmB.1 == ov;
    var rr := AI.FFindMatchPlus(bcB, body, plus, str, ov, LAnc.Backward, cp, capture, look, quant, 0, cdns);
    assert rr.0 == (match raB
                    case None => None
                    case Some(thread) => Some(AI.FReconstructPlus(thread, body, plus, str, fmB.1, LAnc.Backward).0));

    if raB.Some? {
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
      // ---- ReadoutPre at the backward winner ----
      W.BestLiveREMirror(body, tF, n);
      assert PSM.BestLiveRE(body, tB);
      CM.FInitStateRegsWf(bcB, cp, ncap, nlook, nquant, 0, ctxB);
      M.FFindMatchRegsWf(bcB, str, initsB, ov, LAnc.Backward, cdns, ncap, nlook, nquant);
      assert CM.ThreadRegsWf(tB, ncap, nlook, nquant);
      W.BackRowEntryRegsFinal(body, str, cp, ov, cdns, ncap, nlook, nquant);
      assert FV.RegsFinalOk(tB, n, Q);
      var rg: NRC.Regs3 := (tB.capture_regs, tB.look_regs, tB.quant_regs);
      FRA.StampsFinalAtFromRegsFinalOk(body, tB, n);
      assert NRR.CapValWf(rg) && FRG.QClkGe(rg) && NRR.WfRegs(rg);
      SizesCoverFromOk(body, ncap, nlook, nquant);
      CoversFromSizes(body, rg, ncap, nlook, nquant);
      assert FRA.ReadoutPre(qm, body, plus, str, tB, ncap, nlook, nquant);

      assert {:split_here} true;
      // ---- OnlyCapIdsSet: forward write frame at the flipped body, moved across the mirror ----
      M.CaptureBytecodeClassifiedNestedOuter(reF);
      var Sout := PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(reF));
      assert CM.VmCapturesAgree(initsF, capture, Sout) by {
        forall t0 | t0 in initsF.active ensures CM.RegsAgreeOutside(t0.capture_regs, capture, Sout) {
          assert t0 == AI.init_thread(capture, look, quant);
        }
      }
      assert ctxF.nextchar == AI.get_char(rstr, mcp);
      CM.FFindMatchCapWriteFrame(bcF, rstr, initsF, ov', LAnc.Forward, cdns', capture, Sout);
      OnlyCapIdsFromFrameOuter(reF, tF.capture_regs, ncap);
      assert NRO.OnlyCapIdsSet(reF, W.Rg(tF));
      W.OnlyCapIdsSetMirror(body, tF, n);
      assert NRO.OnlyCapIdsSet(body, rg);

      assert {:split_here} true;
      // ---- the readout, the frame, and direction blindness ----
      FRA.FinalReadoutAt(qm, body, plus, str, tB, ncap, nlook, nquant);
      FRA.FinalReadoutFrameAtCin(qm, body, plus, str, tB);
      RRA.RowReconAt(qm, body, plus, str, tB, ncap, nlook, nquant);
      DB.ReconstructPlusDirBlind(tB, body, plus, str, ov);
      var rp := AI.FReconstructPlus(tB, body, plus, str, ov, LAnc.Backward).0;
      assert rr.0 == Some(rp);
      assert ClkFrame(body, Q, rp, tB);

      assert {:split_here} true;
      // ---- the stamp mirror ----
      G := PIV.GmOfLiveR(reF, qmF, rstr, tF.capture_regs, tF.look_regs, tF.quant_regs);
      SM.GmOfLiveRMirrorQ(body, qm, qmF, str, tF.capture_regs, tF.look_regs, tF.quant_regs);
      assert PIV.GmOfLive(body, rp.capture_regs, rp.look_regs, rp.quant_regs) == BGM.RawMirrorGm(G, n);
    }
  }

  /** (G5b-2) `StampPathOk` across the mirror: a stamp's empty path at the mirrored position of the reversed
      string is the real one (both are the stamp body's empty span: `CTT.FirstEmptyPathRMatchesV`,
      `CMr.EmptySpanMirror`). */
  lemma StampPathOkMirror(qm: AR.QMap, qmF: AR.QMap, body: R.regex, str: string, t: AI.Thread, n: nat)
    requires n == |str| && |qm.ov| == n + 1
    requires T.TransWf(body) && NR.NestedFragmentCdnRE(body) && PIV.CapUnique(body) && PIV.QuantUnique(body)
    requires T.TransWf(FST.FXR(body))
    requires qm.bodies == M.BodiesOfRE(body) && qmF.bodies == M.BodiesOfRE(FST.FXR(body))
    requires qmF.ov == MIR.MirrorView(qm.ov, n)
    requires forall k: int :: AI.get_idx(t.quant_regs.a_cp, k) <= n
    requires PSM.StampPathOk(qmF, LC.Reverse(str), t.quant_regs.a_cp)
    ensures PSM.StampPathOk(qm, str, MIR.MirrorRegs(t.quant_regs, n).a_cp)
  {
    var rstr := LC.Reverse(str);
    MIR.ReverseLen(str);
    var qcpB := MIR.MirrorRegs(t.quant_regs, n).a_cp;
    FST.FXRStructuralCdn(body);
    M.BodiesOfREDom(body); M.BodiesOfREEntries(body);
    M.BodiesOfREDom(FST.FXR(body)); M.BodiesOfREEntries(FST.FXR(body));
    reveal PSM.StampPathOk();
    forall q: int | 0 <= AI.get_idx(qcpB, q) <= |str| && q in qm.bodies && T.TransWf(qm.bodies[q])
      ensures TREP.FirstEmptyPathR(qm, qm.bodies[q], PIV.InpOfCp(str, AI.get_idx(qcpB, q) as nat)).Some?
    {
      var pos := AI.get_idx(qcpB, q);
      W.MirrorGetIdx(t.quant_regs, n, q);
      var x := AI.get_idx(t.quant_regs.a_cp, q);
      assert x >= 0 && pos == n - x;
      var qn: nat := q as nat;
      assert qn in PIV.QuantIds(body);
      W.PathsFXR(body, [], [], -1, qn);
      var b := PIV.QidBody(body, qn);
      assert qm.bodies[q] == b;
      assert q in qmF.bodies && qmF.bodies[q] == FST.FXR(b);
      M.TransWfQidBody(FST.FXR(body), qn);
      assert T.TransWf(qmF.bodies[q]);
      assert 0 <= x <= |rstr|;
      assert TREP.FirstEmptyPathR(qmF, qmF.bodies[q], PIV.InpOfCp(rstr, x as nat)).Some?;
      var xn: nat := x as nat;
      var pn: nat := pos as nat;
      PSM.InpOfCpIsInputAt(rstr, xn);
      PSM.InpOfCpIsInputAt(str, pn);
      CTT.FirstEmptyPathRMatchesV(qmF, FST.FXR(b), rstr, xn);
      CS.TransWfCdnWf(b);
      CMr.EmptySpanMirror(b, str, qm.ov, pos);
      assert MIR.Mirror(pos, n) == x;
      CTT.FirstEmptyPathRMatchesV(qm, b, str, pn);
    }
  }

  /** (G5b-2) `BackRowReadout` on the S forms: the lookbehind body may hold a greedy CDN plus. The flipped
      run's swapped list is guard-sound (`CMr.GuardsOkRunFlip`); the stamps' empty paths cross the mirror
      (`StampPathOkMirror`). THE G3b ROW LEMMA. The fresh BACKWARD plus match of a lookbehind body: its reconstruction reads out
      (real side, real table), and the readout is the raw mirror of a group map `G` that agrees with the
      flipped forward spec leaf outside the body's inner-look groups. */
  lemma BackRowReadoutS(rer: LW.RegExpRecord, qm: AR.QMap, body: R.regex, str: string, cp: nat,
                       ov: LOr.OracleView, cdns: LCdn.cdns, plus: seq<RB.code>,
                       ncap: int, nlook: int, nquant: int, n: nat)
    returns (G: LG.GroupMap, qmF: AR.QMap, endlF: nat)
    requires T.TransWf(body) && NR.NestedFragmentCdnRE(body)
    requires PIV.CapUnique(body) && PIV.QuantUnique(body) && LTB.LookUnique(body)
    requires PSM.SizesOkRE(body, ncap, nlook, nquant)
    requires forall l: nat :: l in LTB.LookIds(body) ==> l < nlook
    requires NRC.CdnTopRE(body) && RF.StampLooksCapFreeRE(body) && NRR.PlusTableOkS(body, plus)
    requires AR.QmapOk(body, qm) && qm.bodies == M.BodiesOfRE(body)
    requires cdns == LCdn.compile_cdns(body)   // (G5b-2) the row's own table (the mirrored run's guards)
    requires !rer.ignoreCase && !rer.multiline
    requires n == |str| && cp <= n && |ov| == n + 1
    requires qm.ov == ov && AR.LmapOk(body, qm) && OE.OracleColsOk(rer, qm, str)
    ensures
      var bcB := CP.compile_to_bytecode(R.reverse_regex(body));
      var raB := AI.FFindMatch(bcB, str,
                   AI.FInitState(bcB, cp, AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant), 0,
                                 AI.cp_context(cp, str, LAnc.Backward)), ov, LAnc.Backward, cdns).0;
      var rr := AI.FFindMatchPlus(bcB, body, plus, str, ov, LAnc.Backward, cp,
                                  AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant), 0, cdns);
      var inpF := SD.SwapInput(PIV.InpOfCp(str, cp));
      var t_F := LFU.ComputeTr(rer, [LS.Areg(FM.FlipRevL(T.Translate(body)))], inpF, LG.Empty, WP.Forward);
      rr.1 == ov
      && (rr.0.Some? <==> raB.Some?) && (raB.Some? <==> LT.FirstLeaf(t_F, inpF).Some?)
      && (rr.0.Some? ==>
            PIV.GmOfLive(body, rr.0.value.capture_regs, rr.0.value.look_regs, rr.0.value.quant_regs)
              == PIV.GmOfLiveR(body, qm, str, raB.value.capture_regs, raB.value.look_regs, raB.value.quant_regs)
            && BGM.GmLeN(G, n)
            && PIV.GmOfLive(body, rr.0.value.capture_regs, rr.0.value.look_regs, rr.0.value.quant_regs)
              == BGM.RawMirrorGm(G, n)
            && LL.GmAgreeOutside(G, LT.FirstLeaf(t_F, inpF).value.1, LL.LkBodyGroups(T.Translate(body)))
            && ClkFrameG4(body, ELk.StampSet(raB.value.quant_regs.a_cp), rr.0.value, raB.value)   // (G4b-1b) at the stamped set
            && (forall k: int :: AI.get_idx(raB.value.quant_regs.a_cp, k) <= n)
            && CM.RegsAgreeOutside(rr.0.value.look_regs, raB.value.look_regs, SBk.DirectLidSetRN(body))
            && (CM.LookCpsOracleTrue(raB.value.look_regs, ov) ==> CM.LookCpsOracleTrue(rr.0.value.look_regs, ov))
            && (CM.LookClkSetWithCp(raB.value.look_regs) ==> CM.LookClkSetWithCp(rr.0.value.look_regs))
            && (CM.LookCpSetWithClk(raB.value.look_regs) ==> CM.LookCpSetWithClk(rr.0.value.look_regs))
            && (CM.LookCpsLE(raB.value.look_regs, |str|) ==> CM.LookCpsLE(rr.0.value.look_regs, |str|))
            && CM.ThreadRegsWf(rr.0.value, ncap, nlook, nquant))
    // the flipped side, for callers that read out there too
    ensures |LC.Reverse(str)| == n
    ensures PSM.StaticCoreCdnRE(qmF, FST.FXR(body), CP.compile_to_bytecode(FST.FXR(body)), endlF)
    ensures qmF.bodies == M.BodiesOfRE(FST.FXR(body))
    ensures PSM.SizesOkRE(FST.FXR(body), ncap, nlook, nquant)
    ensures qmF.ov == MIR.MirrorView(ov, n) && OE.OracleColsOk(rer, qmF, LC.Reverse(str))
    ensures
      var bcB := CP.compile_to_bytecode(R.reverse_regex(body));
      var raB := AI.FFindMatch(bcB, str,
                   AI.FInitState(bcB, cp, AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant), 0,
                                 AI.cp_context(cp, str, LAnc.Backward)), ov, LAnc.Backward, cdns).0;
      var bcF := CP.compile_to_bytecode(FST.FXR(body));
      var rfF := AI.FFindMatch(bcF, LC.Reverse(str),
                   AI.FInitState(bcF, n - cp, AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant), 0,
                                 AI.cp_context(n - cp, LC.Reverse(str), LAnc.Forward)),
                   MIR.MirrorView(ov, n), LAnc.Forward, MIR.SwapAnchorsCdns(cdns)).0;
      (raB.Some? <==> rfF.Some?)
      && (raB.Some? ==>
            PSM.BestLiveRE(FST.FXR(body), rfF.value)
            && PSM.StampPathOk(qmF, LC.Reverse(str), rfF.value.quant_regs.a_cp)
            && rfF.value == MIR.MirrorThread(raB.value, n)
            && G == PIV.GmOfLiveR(FST.FXR(body), qmF, LC.Reverse(str), rfF.value.capture_regs, rfF.value.look_regs,
                                  rfF.value.quant_regs))
  {
    G := map[];
    var tr := T.Translate(body);
    var reF := FST.FXR(body);
    MIR.ReverseLen(str);
    var rstr := LC.Reverse(str);
    var mcp := MIR.Mirror(cp, n);
    var mcpN: nat := n - cp;
    assert mcp == mcpN as int && 0 <= mcp <= n && |rstr| == n;
    var ov' := MIR.MirrorView(ov, n);
    var cdns' := MIR.SwapAnchorsCdns(cdns);
    var bcF := CP.compile_to_bytecode(reF);
    var inpF := PIV.InpOfCp(rstr, mcpN);
    LBV.InpOfCpSwap(str, cp, n);
    assert inpF == SD.SwapInput(PIV.InpOfCp(str, cp));
    var capture := AReg.init_regs(ncap);
    var look := AReg.init_regs(nlook);
    var quant := AReg.init_regs(nquant);
    var Q := FRD.StampQids(body);

    // ---- statics of the flipped body + its oracle (LBEngineLeafFlipG's preamble) ----
    FST.FXRStructuralCdn(body);
    var endl': nat;
    qmF, endl' := WS.FlipXRevStaticCoreCdn(body, ov', ncap, nlook, nquant);
    endlF := endl';
    var qmB := AR.QMap(map[], OE.LmOf(body), ov, map[]);
    OE.LmapOkOfLmOf(body, qmB);
    FK.LmapOkEntriesMatchLmOf(body, qm);
    assert OE.OracleColsOk(rer, qmB, str) by {
      forall k: int | 0 <= k <= |str| ensures LL.OracleOkAt(rer, qmB, T.InputAt(str, k)) {
        FST.OracleOkAtSubmap(rer, qm, qmB, T.InputAt(str, k));
      }
    }
    KG.LmOfBodiesNoBackref(body);
    assert OG.QmBodiesNoBackref(qmB);
    FST.FlipLooksMapTie(qmB, qmF);
    assert |qmB.ov| == |str| + 1 && qmF.ov == MIR.MirrorView(qmB.ov, |str|);
    OG.MirrorOracleColsOkG(rer, qmB, qmF, str);
    FO.ColsOkToSuffix(rer, qmF, rstr, mcpN);
    assert PIV.InpOfCp(rstr, mcpN) == T.InputAt(rstr, mcpN);
    assert LL.OracleOkSuffix(rer, qmF, inpF);

    assert {:split_here} true;
    // ---- machine A's first half at the flipped body: the swapped list is guard-sound (N2 + N1) ----
    hide PSM.GuardsOkRun;   // (G5b-2, pack S25) passed on as a term, never unfolded: a quantifier the later sections must not see
    CMr.GuardsOkRunFlip(qmF, body, bcF, endl', str, ov);
    MachineAWinnerS(rer, qmF, reF, bcF, endl', 0, rstr, mcpN, ov', cdns', ncap, nlook, nquant);
    FST.TranslateFlipXRev(body);
    assert T.Translate(reF) == FM.FlipRevL(tr);
    FST.LkBodyGroupsFlipL(SD.RevL(tr));
    TML.LkBodyGroupsRevL(tr);
    assert LL.LkBodyGroups(T.Translate(reF)) == LL.LkBodyGroups(tr);
    var t_F := LFU.ComputeTr(rer, [LS.Areg(FM.FlipRevL(tr))], inpF, LG.Empty, WP.Forward);
    var ctxF := AI.cp_context(mcp, rstr, LAnc.Forward);
    var initsF := AI.FInitState(bcF, mcp, capture, look, quant, 0, ctxF);
    var rfF := AI.FFindMatch(bcF, rstr, initsF, ov', LAnc.Forward, cdns').0;
    assert rfF.Some? <==> LT.FirstLeaf(t_F, inpF).Some?;

    assert {:split_here} true;
    // ---- the tie: rfF == MirrorThread(raB) ----
    var bcB := CP.compile_to_bytecode(R.reverse_regex(body));
    var ctxB := AI.cp_context(cp, str, LAnc.Backward);
    var initsB := AI.FInitState(bcB, cp, capture, look, quant, 0, ctxB);
    var fmB := AI.FFindMatch(bcB, str, initsB, ov, LAnc.Backward, cdns);
    var raB := fmB.0;
    MIR.MirrorInitRegs(ncap, n); MIR.MirrorInitRegs(nlook, n); MIR.MirrorInitRegs(nquant, n);
    BV.BackwardReplayMirrorNested(body, str, cp, capture, look, quant, ov, cdns, n);
    FR.FlipCompileToBytecode(FST.XRV(body));
    assert bcF == CP.compile_to_bytecode(FST.XRV(body));
    assert raB.None? <==> rfF.None?;
    assert {:split_here} true;   // (G5b-2, pack S25) the tie's second half in its own batch
    // the view is kept by the backward run
    M.ReverseCdnPackage(body);
    M.NoWriteOracleBodyCodeCdn(R.reverse_regex(body));
    assert ctxB.nextchar == AI.get_char(str, cp - 1);
    CM.FFindMatchOvStable(bcB, str, initsB, ov, LAnc.Backward, cdns);
    assert fmB.1 == ov;
    var rr := AI.FFindMatchPlus(bcB, body, plus, str, ov, LAnc.Backward, cp, capture, look, quant, 0, cdns);
    assert rr.0 == (match raB
                    case None => None
                    case Some(thread) => Some(AI.FReconstructPlus(thread, body, plus, str, fmB.1, LAnc.Backward).0));

    if raB.Some? {
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
      // ---- ReadoutPre at the backward winner ----
      W.BestLiveREMirror(body, tF, n);
      assert PSM.BestLiveRE(body, tB);
      CM.FInitStateRegsWf(bcB, cp, ncap, nlook, nquant, 0, ctxB);
      M.FFindMatchRegsWf(bcB, str, initsB, ov, LAnc.Backward, cdns, ncap, nlook, nquant);
      assert CM.ThreadRegsWf(tB, ncap, nlook, nquant);
      W.BackRowEntryRegsFinalS(body, str, cp, ov, cdns, ncap, nlook, nquant);
      assert FV.RegsFinalOk(tB, n, Q);
      var rg: NRC.Regs3 := (tB.capture_regs, tB.look_regs, tB.quant_regs);
      FRA.StampsFinalAtSFromRegsFinalOk(body, tB, n);
      // (G5b-2) the stamps' empty paths, moved across the mirror
      StampPathOkMirror(qm, qmF, body, str, tF, n);
      assert tB.quant_regs == MIR.MirrorRegs(tF.quant_regs, n);
      assert NRR.CapValWf(rg) && FRG.QClkGe(rg) && NRR.WfRegs(rg);
      SizesCoverFromOk(body, ncap, nlook, nquant);
      CoversFromSizes(body, rg, ncap, nlook, nquant);
      assert FRA.ReadoutPreS(qm, body, plus, str, tB, ncap, nlook, nquant);

      assert {:split_here} true;
      // ---- OnlyCapIdsSet: forward write frame at the flipped body, moved across the mirror ----
      M.CaptureBytecodeClassifiedCdnOuter(reF);
      var Sout := PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(reF));
      assert CM.VmCapturesAgree(initsF, capture, Sout) by {
        forall t0 | t0 in initsF.active ensures CM.RegsAgreeOutside(t0.capture_regs, capture, Sout) {
          assert t0 == AI.init_thread(capture, look, quant);
        }
      }
      assert ctxF.nextchar == AI.get_char(rstr, mcp);
      CM.FFindMatchCapWriteFrame(bcF, rstr, initsF, ov', LAnc.Forward, cdns', capture, Sout);
      OnlyCapIdsFromFrameOuter(reF, tF.capture_regs, ncap);
      assert NRO.OnlyCapIdsSet(reF, W.Rg(tF));
      W.OnlyCapIdsSetMirror(body, tF, n);
      assert NRO.OnlyCapIdsSet(body, rg);

      assert {:split_here} true;
      // ---- the readout, the frame, and direction blindness ----
      FRA.FinalReadoutAtS(qm, body, plus, str, tB, ncap, nlook, nquant);
      FRA.FinalReadoutFrameAtStamp(qm, body, plus, str, tB);
      // (G5b-3) the bank and the look frame outside `LooksQ`
      var F := SBk.Flags(CM.LookCpsOracleTrue(tB.look_regs, ov), CM.LookClkSetWithCp(tB.look_regs),
                         CM.LookCpSetWithClk(tB.look_regs), CM.LookCpsLE(tB.look_regs, |str|), |str|);
      RRA.RowReconAtG4(F, qm, body, plus, str, tB, ncap, nlook, nquant);
      DB.ReconstructPlusDirBlind(tB, body, plus, str, ov);
      var rp := AI.FReconstructPlus(tB, body, plus, str, ov, LAnc.Backward).0;
      assert rr.0 == Some(rp);
      // (G4b-1b) the sharp frame at the stamped set, and the replay only raised quant clocks
      assert SL.StampLiveOk(body, tB.capture_regs.a_clk, tB.quant_regs.a_clk, tB.quant_regs.a_cp) by {
        reveal PSM.BestLiveRE();
      }
      FRA.FinalReadoutFrameAtStampE(qm, body, plus, str, tB);
      assert ClkFrameG4(body, ELk.StampSet(tB.quant_regs.a_cp), rp, tB);
      assert forall k: int :: AI.get_idx(tB.quant_regs.a_cp, k) <= n by {
        forall k: int ensures AI.get_idx(tB.quant_regs.a_cp, k) <= n {
          if AI.get_idx(tB.quant_regs.a_cp, k) >= 0 { assert FV.RegsFinalOk(tB, n, Q); }
        }
      }

      assert {:split_here} true;
      // ---- the stamp mirror ----
      G := PIV.GmOfLiveR(reF, qmF, rstr, tF.capture_regs, tF.look_regs, tF.quant_regs);
      SM.GmOfLiveRMirrorQ(body, qm, qmF, str, tF.capture_regs, tF.look_regs, tF.quant_regs);
      assert PIV.GmOfLive(body, rp.capture_regs, rp.look_regs, rp.quant_regs) == BGM.RawMirrorGm(G, n);
    }
  }

  /** A LOOKBEHIND row in both worlds: the real backward plus match of `body` (real table) and the
      flipped forward plus match of `FXR(body)` (a table correct for `FXR(body)`) read out as raw
      mirrors of each other. */
  lemma RowKeysLB(rer: LW.RegExpRecord, qm: AR.QMap, body: R.regex, str: string, cp: nat,
                  ov: LOr.OracleView, cdns: LCdn.cdns, plus: seq<RB.code>, plusF: seq<RB.code>,
                  ncap: int, nlook: int, nquant: int, n: nat)
    requires T.TransWf(body) && NR.NestedFragmentRE(body)
    requires PIV.CapUnique(body) && PIV.QuantUnique(body) && LTB.LookUnique(body)
    requires PSM.SizesOkRE(body, ncap, nlook, nquant)
    requires forall l: nat :: l in LTB.LookIds(body) ==> l < nlook
    requires NRC.NoCdnPlusRE(body) && RF.CinBodiesLookFreeRE(body) && NRR.PlusTableOk(body, plus)
    requires NRR.PlusTableOk(FST.FXR(body), plusF)
    requires AR.QmapOk(body, qm)
    requires !rer.ignoreCase && !rer.multiline
    requires n == |str| && cp <= n && |ov| == n + 1
    requires qm.ov == ov && AR.LmapOk(body, qm) && OE.OracleColsOk(rer, qm, str)
    ensures |LC.Reverse(str)| == n
    ensures
      var bcB := CP.compile_to_bytecode(R.reverse_regex(body));
      var rr := AI.FFindMatchPlus(bcB, body, plus, str, ov, LAnc.Backward, cp,
                                  AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant), 0, cdns).0;
      var bcF := CP.compile_to_bytecode(FST.FXR(body));
      var rrF := AI.FFindMatchPlus(bcF, FST.FXR(body), plusF, LC.Reverse(str), MIR.MirrorView(ov, n), LAnc.Forward,
                                   n - cp, AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant), 0,
                                   MIR.SwapAnchorsCdns(cdns)).0;
      (rr.Some? <==> rrF.Some?)
      && (rr.Some? ==>
            var GF := PIV.GmOfLive(FST.FXR(body), rrF.value.capture_regs, rrF.value.look_regs, rrF.value.quant_regs);
            BGM.GmLeN(GF, n)
            && PIV.GmOfLive(body, rr.value.capture_regs, rr.value.look_regs, rr.value.quant_regs)
               == BGM.RawMirrorGm(GF, n))
  {
    var reF := FST.FXR(body);
    var rstr := LC.Reverse(str);
    var ov' := MIR.MirrorView(ov, n);
    var cdns' := MIR.SwapAnchorsCdns(cdns);
    var bcF := CP.compile_to_bytecode(reF);
    var G, qmF, endlF := BackRowReadout(rer, qm, body, str, cp, ov, cdns, plus, ncap, nlook, nquant, n);
    var mcpN: nat := n - cp;
    var initsF := AI.FInitState(bcF, mcpN, AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant), 0,
                                AI.cp_context(mcpN, rstr, LAnc.Forward));
    var fmF := AI.FFindMatch(bcF, rstr, initsF, ov', LAnc.Forward, cdns');
    var rrF := AI.FFindMatchPlus(bcF, reF, plusF, rstr, ov', LAnc.Forward, mcpN,
                                 AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant), 0, cdns');
    assert rrF.0 == (match fmF.0
                     case None => None
                     case Some(thread) => Some(AI.FReconstructPlus(thread, reF, plusF, rstr, fmF.1, LAnc.Forward).0));
    if fmF.0.Some? {
      FST.FXRStructural(body);
      FG.LookUniqueFXR(body);
      FG.LookIdsFXR(body);
      TB.NoCdnPlusFXR(body);
      TB.CinBodiesLookFreeFXR(body);
      SizesCoverFromOk(reF, ncap, nlook, nquant);
      var rp := MA.ReadoutAtWinnerAt(qmF, reF, bcF, endlF, plusF, rstr, mcpN, ov', cdns', initsF,
                                     ncap, nlook, nquant, fmF.0);
      assert rrF.0 == Some(rp);
    }
  }

  /** A LOOKAHEAD row in both worlds: `RowKeysLB` at the flipped body, read backwards through the
      involutions. The mirrored row replays `reverse_regex(FXR(body))` BACKWARD over the reversed string.
      Row cdns are empty in the fragment. */
  lemma RowKeysLA(rer: LW.RegExpRecord, qm: AR.QMap, body: R.regex, str: string, cp: nat,
                  ov: LOr.OracleView, plus: seq<RB.code>, plusF: seq<RB.code>,
                  ncap: int, nlook: int, nquant: int, n: nat)
    requires T.TransWf(body) && NR.NestedFragmentRE(body)
    requires PIV.CapUnique(body) && PIV.QuantUnique(body) && LTB.LookUnique(body)
    requires PSM.SizesOkRE(body, ncap, nlook, nquant)
    requires forall l: nat :: l in LTB.LookIds(body) ==> l < nlook
    requires NRC.NoCdnPlusRE(body) && RF.CinBodiesLookFreeRE(body) && NRR.PlusTableOk(body, plus)
    requires NRR.PlusTableOk(FST.FXR(body), plusF)
    requires !rer.ignoreCase && !rer.multiline
    requires n == |str| && cp <= n && |ov| == n + 1
    requires qm.ov == ov && AR.LmapOk(body, qm) && OE.OracleColsOk(rer, qm, str)
    ensures |LC.Reverse(str)| == n
    ensures
      var bc := CP.compile_to_bytecode(body);
      var rr := AI.FFindMatchPlus(bc, body, plus, str, ov, LAnc.Forward, cp,
                                  AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant), 0, []).0;
      var bcFB := CP.compile_to_bytecode(R.reverse_regex(FST.FXR(body)));
      var rrF := AI.FFindMatchPlus(bcFB, FST.FXR(body), plusF, LC.Reverse(str), MIR.MirrorView(ov, n), LAnc.Backward,
                                   n - cp, AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant), 0,
                                   []).0;
      (rr.Some? <==> rrF.Some?)
      && (rr.Some? ==>
            var Gr := PIV.GmOfLive(body, rr.value.capture_regs, rr.value.look_regs, rr.value.quant_regs);
            BGM.GmLeN(Gr, n)
            && PIV.GmOfLive(FST.FXR(body), rrF.value.capture_regs, rrF.value.look_regs, rrF.value.quant_regs)
               == BGM.RawMirrorGm(Gr, n))
  {
    var reF := FST.FXR(body);
    MIR.ReverseLen(str);
    var rstr := LC.Reverse(str);
    var ov' := MIR.MirrorView(ov, n);
    var mcpN: nat := n - cp;
    // ---- the flipped body's statics and oracle ----
    FST.FXRStructural(body);
    var qmF, endl' := WS.FlipXRevStaticCoreNested(body, ov', ncap, nlook, nquant);
    var qmB := AR.QMap(map[], OE.LmOf(body), ov, map[]);
    OE.LmapOkOfLmOf(body, qmB);
    FK.LmapOkEntriesMatchLmOf(body, qm);
    assert OE.OracleColsOk(rer, qmB, str) by {
      forall k: int | 0 <= k <= |str| ensures LL.OracleOkAt(rer, qmB, T.InputAt(str, k)) {
        FST.OracleOkAtSubmap(rer, qm, qmB, T.InputAt(str, k));
      }
    }
    KG.LmOfBodiesNoBackref(body);
    assert OG.QmBodiesNoBackref(qmB);
    FST.FlipLooksMapTie(qmB, qmF);
    OG.MirrorOracleColsOkG(rer, qmB, qmF, str);
    FG.LookUniqueFXR(body);
    FG.LookIdsFXR(body);
    TB.NoCdnPlusFXR(body);
    TB.CinBodiesLookFreeFXR(body);
    // ---- the involutions ----
    MW.FXRInvol(body);
    FS.ReverseReverse(str);
    MIR.MirrorViewInvolution(ov, n);
    assert FST.FXR(reF) == body && LC.Reverse(rstr) == str && MIR.MirrorView(ov', n) == ov;
    assert MIR.SwapAnchorsCdns([]) == [];
    assert n - mcpN == cp;
    assert {:split_here} true;
    RowKeysLB(rer, qmF, reF, rstr, mcpN, ov', [], plusF, plus, ncap, nlook, nquant, n);
  }

  lemma RegsOfFXR(r: R.regex)
    ensures NRR.CapRegsOf(FST.FXR(r)) == NRR.CapRegsOf(r) && NRR.QuantRegsOf(FST.FXR(r)) == NRR.QuantRegsOf(r)
    ensures NRR.LookRegsOf(FST.FXR(r)) == NRR.LookRegsOf(r)   // (G5b-3)
    decreases r
  {
    match r
    case Re_alt(a, b) => W.FXRAlt(a, b); RegsOfFXR(a); RegsOfFXR(b);
    case Re_con(a, b) => W.FXRCon(a, b); RegsOfFXR(a); RegsOfFXR(b);
    case Re_quant(nul, qid, q, a) => W.FXRQuant(nul, qid, q, a); RegsOfFXR(a);
    case Re_capture(c, a) => W.FXRCap(c, a); RegsOfFXR(a);
    case Re_lookaround(l, la, a) => W.FXRLook(l, la, a); RegsOfFXR(a);
    case Re_anchor(x) => W.FXRAnchor(x);
    case Re_empty =>
    case Re_character(_) =>
  }
  lemma QSetsFXR(r: R.regex, Q: set<int>)
    ensures RF.CapsQ(FST.FXR(r), Q) == RF.CapsQ(r, Q) && RF.QuantsQ(FST.FXR(r), Q) == RF.QuantsQ(r, Q)
    ensures RF.LooksQ(FST.FXR(r), Q) == RF.LooksQ(r, Q)   // (G5b-3)
    decreases r
  {
    match r
    case Re_alt(a, b) => W.FXRAlt(a, b); QSetsFXR(a, Q); QSetsFXR(b, Q);
    case Re_con(a, b) => W.FXRCon(a, b); QSetsFXR(a, Q); QSetsFXR(b, Q);
    case Re_quant(nul, qid, q, a) => W.FXRQuant(nul, qid, q, a); QSetsFXR(a, Q); RegsOfFXR(a);
    case Re_capture(c, a) => W.FXRCap(c, a); QSetsFXR(a, Q);
    case Re_lookaround(l, la, a) => W.FXRLook(l, la, a);
    case Re_anchor(x) => W.FXRAnchor(x);
    case Re_empty =>
    case Re_character(_) =>
  }

  // (G4b-1b) The empty-path look sets and the out-of-look capture sets are FXR-invariant.
  lemma OwnLooksEFXR(r: R.regex)
    ensures ELk.OwnLooksE(FST.FXR(r)) == ELk.OwnLooksE(r)
    decreases r
  {
    match r
    case Re_alt(a, b) => W.FXRAlt(a, b); OwnLooksEFXR(a); OwnLooksEFXR(b);
    case Re_con(a, b) => W.FXRCon(a, b); OwnLooksEFXR(a); OwnLooksEFXR(b); CMr.NullableFXR(a); CMr.NullableFXR(b);
    case Re_quant(nul, qid, q, a) => W.FXRQuant(nul, qid, q, a); OwnLooksEFXR(a);
    case Re_capture(c, a) => W.FXRCap(c, a); OwnLooksEFXR(a);
    case Re_lookaround(l, la, a) => W.FXRLook(l, la, a);
    case Re_anchor(x) => W.FXRAnchor(x);
    case Re_empty =>
    case Re_character(_) =>
  }
  lemma InnerLookRegsEFXR(r: R.regex)
    ensures ELk.InnerLookRegsE(FST.FXR(r)) == ELk.InnerLookRegsE(r)
    decreases r
  {
    match r
    case Re_alt(a, b) => W.FXRAlt(a, b); InnerLookRegsEFXR(a); InnerLookRegsEFXR(b);
    case Re_con(a, b) => W.FXRCon(a, b); InnerLookRegsEFXR(a); InnerLookRegsEFXR(b);
    case Re_quant(nul, qid, q, a) => W.FXRQuant(nul, qid, q, a); InnerLookRegsEFXR(a); OwnLooksEFXR(a);
    case Re_capture(c, a) => W.FXRCap(c, a); InnerLookRegsEFXR(a);
    case Re_lookaround(l, la, a) => W.FXRLook(l, la, a);
    case Re_anchor(x) => W.FXRAnchor(x);
    case Re_empty =>
    case Re_character(_) =>
  }
  lemma CapRegsOFXR(r: R.regex)
    ensures ELk.CapRegsO(FST.FXR(r)) == ELk.CapRegsO(r)
    decreases r
  {
    match r
    case Re_alt(a, b) => W.FXRAlt(a, b); CapRegsOFXR(a); CapRegsOFXR(b);
    case Re_con(a, b) => W.FXRCon(a, b); CapRegsOFXR(a); CapRegsOFXR(b);
    case Re_quant(nul, qid, q, a) => W.FXRQuant(nul, qid, q, a); CapRegsOFXR(a);
    case Re_capture(c, a) => W.FXRCap(c, a); CapRegsOFXR(a);
    case Re_lookaround(l, la, a) => W.FXRLook(l, la, a);
    case Re_anchor(x) => W.FXRAnchor(x);
    case Re_empty =>
    case Re_character(_) =>
  }
  lemma QSetsFXRE(r: R.regex, Q: set<int>)
    ensures ELk.LooksQE(FST.FXR(r), Q) == ELk.LooksQE(r, Q) && ELk.CapsQO(FST.FXR(r), Q) == ELk.CapsQO(r, Q)
    decreases r
  {
    match r
    case Re_alt(a, b) => W.FXRAlt(a, b); QSetsFXRE(a, Q); QSetsFXRE(b, Q);
    case Re_con(a, b) => W.FXRCon(a, b); QSetsFXRE(a, Q); QSetsFXRE(b, Q);
    case Re_quant(nul, qid, q, a) =>
      W.FXRQuant(nul, qid, q, a); QSetsFXRE(a, Q); InnerLookRegsEFXR(R.Re_quant(nul, qid, q, a)); CapRegsOFXR(a);
    case Re_capture(c, a) => W.FXRCap(c, a); QSetsFXRE(a, Q);
    case Re_lookaround(l, la, a) => W.FXRLook(l, la, a);
    case Re_anchor(x) => W.FXRAnchor(x);
    case Re_empty =>
    case Re_character(_) =>
  }

  /** (G4b-1b) The stamped set crosses the mirror (a bank bounded by `n` keeps every sign). */
  lemma StampSetMirror(r: AReg.Regs, n: nat)
    requires forall k: int :: AI.get_idx(r.a_cp, k) <= n
    ensures ELk.StampSet(MIR.MirrorRegs(r, n).a_cp) == ELk.StampSet(r.a_cp)
  {
    W.MirrorSign(r, n);
    forall q: int ensures q in ELk.StampSet(MIR.MirrorRegs(r, n).a_cp) <==> q in ELk.StampSet(r.a_cp) {
      W.MirrorGetIdx(r, n, q);
      assert (AI.get_idx(MIR.MirrorRegs(r, n).a_cp, q) >= 0) == (AI.get_idx(r.a_cp, q) >= 0);
    }
  }

  /** THE CARRIER'S FRAME across the mirror: the mirror image of the real backward plus winner and the
      flipped forward plus winner (its own table) agree on the look bank and on every clock outside the
      CIN reconstruction sets of the flipped body. */
  lemma BackRowClkFrame(rer: LW.RegExpRecord, qm: AR.QMap, body: R.regex, str: string, cp: nat,
                        ov: LOr.OracleView, cdns: LCdn.cdns, plus: seq<RB.code>, plusF: seq<RB.code>,
                        ncap: int, nlook: int, nquant: int, n: nat)
    requires T.TransWf(body) && NR.NestedFragmentRE(body)
    requires PIV.CapUnique(body) && PIV.QuantUnique(body) && LTB.LookUnique(body)
    requires PSM.SizesOkRE(body, ncap, nlook, nquant)
    requires forall l: nat :: l in LTB.LookIds(body) ==> l < nlook
    requires NRC.NoCdnPlusRE(body) && RF.CinBodiesLookFreeRE(body) && NRR.PlusTableOk(body, plus)
    requires NRR.PlusTableOk(FST.FXR(body), plusF)
    requires AR.QmapOk(body, qm)
    requires !rer.ignoreCase && !rer.multiline
    requires n == |str| && cp <= n && |ov| == n + 1
    requires qm.ov == ov && AR.LmapOk(body, qm) && OE.OracleColsOk(rer, qm, str)
    ensures |LC.Reverse(str)| == n
    ensures
      var bcB := CP.compile_to_bytecode(R.reverse_regex(body));
      var rr := AI.FFindMatchPlus(bcB, body, plus, str, ov, LAnc.Backward, cp,
                                  AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant), 0, cdns).0;
      var bcF := CP.compile_to_bytecode(FST.FXR(body));
      var rrF := AI.FFindMatchPlus(bcF, FST.FXR(body), plusF, LC.Reverse(str), MIR.MirrorView(ov, n), LAnc.Forward,
                                   n - cp, AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant), 0,
                                   MIR.SwapAnchorsCdns(cdns)).0;
      (rr.Some? <==> rrF.Some?)
      && (rr.Some? ==>
            ClkFrame(FST.FXR(body), FRD.CinQids(FST.FXR(body)), MIR.MirrorThread(rr.value, n), rrF.value))
  {
    var reF := FST.FXR(body);
    var rstr := LC.Reverse(str);
    var ov' := MIR.MirrorView(ov, n);
    var cdns' := MIR.SwapAnchorsCdns(cdns);
    var bcF := CP.compile_to_bytecode(reF);
    var G, qmF, endlF := BackRowReadout(rer, qm, body, str, cp, ov, cdns, plus, ncap, nlook, nquant, n);
    var mcpN: nat := n - cp;
    var initsF := AI.FInitState(bcF, mcpN, AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant), 0,
                                AI.cp_context(mcpN, rstr, LAnc.Forward));
    var fmF := AI.FFindMatch(bcF, rstr, initsF, ov', LAnc.Forward, cdns');
    var rrF := AI.FFindMatchPlus(bcF, reF, plusF, rstr, ov', LAnc.Forward, mcpN,
                                 AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant), 0, cdns');
    assert rrF.0 == (match fmF.0
                     case None => None
                     case Some(thread) => Some(AI.FReconstructPlus(thread, reF, plusF, rstr, fmF.1, LAnc.Forward).0));
    var bcB := CP.compile_to_bytecode(R.reverse_regex(body));
    var raB := AI.FFindMatch(bcB, str,
                 AI.FInitState(bcB, cp, AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant), 0,
                               AI.cp_context(cp, str, LAnc.Backward)), ov, LAnc.Backward, cdns).0;
    var rr := AI.FFindMatchPlus(bcB, body, plus, str, ov, LAnc.Backward, cp,
                                AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant), 0, cdns).0;
    if fmF.0.Some? {
      FST.FXRStructural(body);
      FG.LookUniqueFXR(body);
      FG.LookIdsFXR(body);
      TB.NoCdnPlusFXR(body);
      TB.CinBodiesLookFreeFXR(body);
      SizesCoverFromOk(reF, ncap, nlook, nquant);
      var rpF := MA.ReadoutAtWinnerAt(qmF, reF, bcF, endlF, plusF, rstr, mcpN, ov', cdns', initsF,
                                      ncap, nlook, nquant, fmF.0);
      assert rrF.0 == Some(rpF);
      var Q := FRD.CinQids(body);
      W.CinQidsFXR(body);
      QSetsFXR(body, Q);
      var tB := raB.value; var tF := fmF.0.value; var rp := rr.value;
      assert ClkFrame(body, Q, rp, tB) && ClkFrame(reF, Q, rpF, tF) && tF == MIR.MirrorThread(tB, n);
      var m := MIR.MirrorThread(rp, n);
      assert m.look_regs == rpF.look_regs;
      assert m.capture_regs.a_clk == rp.capture_regs.a_clk && m.quant_regs.a_clk == rp.quant_regs.a_clk;
      assert tF.capture_regs.a_clk == tB.capture_regs.a_clk && tF.quant_regs.a_clk == tB.quant_regs.a_clk;
    }
  }

  /** (G5b-2) `RowKeysLB` on the S forms (the row's own table). A LOOKBEHIND row in both worlds: the real backward plus match of `body` (real table) and the
      flipped forward plus match of `FXR(body)` (a table correct for `FXR(body)`) read out as raw
      mirrors of each other. */
  lemma RowKeysLBS(rer: LW.RegExpRecord, qm: AR.QMap, body: R.regex, str: string, cp: nat,
                  ov: LOr.OracleView, cdns: LCdn.cdns, plus: seq<RB.code>, plusF: seq<RB.code>,
                  ncap: int, nlook: int, nquant: int, n: nat)
    requires T.TransWf(body) && NR.NestedFragmentCdnRE(body)
    requires PIV.CapUnique(body) && PIV.QuantUnique(body) && LTB.LookUnique(body)
    requires PSM.SizesOkRE(body, ncap, nlook, nquant)
    requires forall l: nat :: l in LTB.LookIds(body) ==> l < nlook
    requires NRC.CdnTopRE(body) && RF.StampLooksCapFreeRE(body) && NRR.PlusTableOkS(body, plus)
    requires NRR.PlusTableOkS(FST.FXR(body), plusF)
    requires AR.QmapOk(body, qm) && qm.bodies == M.BodiesOfRE(body)
    requires cdns == LCdn.compile_cdns(body)
    requires !rer.ignoreCase && !rer.multiline
    requires n == |str| && cp <= n && |ov| == n + 1
    requires qm.ov == ov && AR.LmapOk(body, qm) && OE.OracleColsOk(rer, qm, str)
    ensures |LC.Reverse(str)| == n
    ensures
      var bcB := CP.compile_to_bytecode(R.reverse_regex(body));
      var rr := AI.FFindMatchPlus(bcB, body, plus, str, ov, LAnc.Backward, cp,
                                  AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant), 0, cdns).0;
      var bcF := CP.compile_to_bytecode(FST.FXR(body));
      var rrF := AI.FFindMatchPlus(bcF, FST.FXR(body), plusF, LC.Reverse(str), MIR.MirrorView(ov, n), LAnc.Forward,
                                   n - cp, AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant), 0,
                                   MIR.SwapAnchorsCdns(cdns)).0;
      (rr.Some? <==> rrF.Some?)
      && (rr.Some? ==>
            var GF := PIV.GmOfLive(FST.FXR(body), rrF.value.capture_regs, rrF.value.look_regs, rrF.value.quant_regs);
            BGM.GmLeN(GF, n)
            && PIV.GmOfLive(body, rr.value.capture_regs, rr.value.look_regs, rr.value.quant_regs)
               == BGM.RawMirrorGm(GF, n))
  {
    var reF := FST.FXR(body);
    var rstr := LC.Reverse(str);
    var ov' := MIR.MirrorView(ov, n);
    var cdns' := MIR.SwapAnchorsCdns(cdns);
    var bcF := CP.compile_to_bytecode(reF);
    var G, qmF, endlF := BackRowReadoutS(rer, qm, body, str, cp, ov, cdns, plus, ncap, nlook, nquant, n);
    assert {:split_here} true;   // (G5b-2, pack S25) one batch per section under `dafny build`
    var mcpN: nat := n - cp;
    var initsF := AI.FInitState(bcF, mcpN, AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant), 0,
                                AI.cp_context(mcpN, rstr, LAnc.Forward));
    var fmF := AI.FFindMatch(bcF, rstr, initsF, ov', LAnc.Forward, cdns');
    var rrF := AI.FFindMatchPlus(bcF, reF, plusF, rstr, ov', LAnc.Forward, mcpN,
                                 AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant), 0, cdns');
    assert rrF.0 == (match fmF.0
                     case None => None
                     case Some(thread) => Some(AI.FReconstructPlus(thread, reF, plusF, rstr, fmF.1, LAnc.Forward).0));
    if fmF.0.Some? {
      FST.FXRStructuralCdn(body);
      FG.LookUniqueFXR(body);
      FG.LookIdsFXR(body);
      NRC.CdnTopAll(reF);
      TB.StampLooksCapFreeFXR(body);
      SizesCoverFromOk(reF, ncap, nlook, nquant);
      var rp := MA.ReadoutAtWinnerAtS(qmF, reF, bcF, endlF, plusF, rstr, mcpN, ov', cdns', initsF,
                                     ncap, nlook, nquant, fmF.0);
      assert rrF.0 == Some(rp);
    }
  }

  /** (G5b-2) `RowKeysLA` on the S forms. A LOOKAHEAD row in both worlds: `RowKeysLB` at the flipped body, read backwards through the
      involutions. The mirrored row replays `reverse_regex(FXR(body))` BACKWARD over the reversed string.
      (G5b-2) Each world runs its row's own table. */
  lemma RowKeysLAS(rer: LW.RegExpRecord, qm: AR.QMap, body: R.regex, str: string, cp: nat,
                  ov: LOr.OracleView, plus: seq<RB.code>, plusF: seq<RB.code>,
                  ncap: int, nlook: int, nquant: int, n: nat)
    requires T.TransWf(body) && NR.NestedFragmentCdnRE(body)
    requires PIV.CapUnique(body) && PIV.QuantUnique(body) && LTB.LookUnique(body)
    requires PSM.SizesOkRE(body, ncap, nlook, nquant)
    requires forall l: nat :: l in LTB.LookIds(body) ==> l < nlook
    requires NRC.CdnTopRE(body) && RF.StampLooksCapFreeRE(body) && NRR.PlusTableOkS(body, plus)
    requires NRR.PlusTableOkS(FST.FXR(body), plusF)
    requires !rer.ignoreCase && !rer.multiline
    requires n == |str| && cp <= n && |ov| == n + 1
    requires qm.ov == ov && AR.LmapOk(body, qm) && OE.OracleColsOk(rer, qm, str)
    ensures |LC.Reverse(str)| == n
    ensures
      var bc := CP.compile_to_bytecode(body);
      var rr := AI.FFindMatchPlus(bc, body, plus, str, ov, LAnc.Forward, cp,
                                  AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant), 0,
                                  LCdn.compile_cdns(body)).0;
      var bcFB := CP.compile_to_bytecode(R.reverse_regex(FST.FXR(body)));
      var rrF := AI.FFindMatchPlus(bcFB, FST.FXR(body), plusF, LC.Reverse(str), MIR.MirrorView(ov, n), LAnc.Backward,
                                   n - cp, AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant), 0,
                                   LCdn.compile_cdns(FST.FXR(body))).0;
      (rr.Some? <==> rrF.Some?)
      && (rr.Some? ==>
            var Gr := PIV.GmOfLive(body, rr.value.capture_regs, rr.value.look_regs, rr.value.quant_regs);
            BGM.GmLeN(Gr, n)
            && PIV.GmOfLive(FST.FXR(body), rrF.value.capture_regs, rrF.value.look_regs, rrF.value.quant_regs)
               == BGM.RawMirrorGm(Gr, n))
  {
    var reF := FST.FXR(body);
    MIR.ReverseLen(str);
    var rstr := LC.Reverse(str);
    var ov' := MIR.MirrorView(ov, n);
    var mcpN: nat := n - cp;
    // ---- the flipped body's statics and oracle ----
    FST.FXRStructuralCdn(body);
    var qmF, endl' := WS.FlipXRevStaticCoreCdn(body, ov', ncap, nlook, nquant);
    var qmB := AR.QMap(map[], OE.LmOf(body), ov, map[]);
    OE.LmapOkOfLmOf(body, qmB);
    FK.LmapOkEntriesMatchLmOf(body, qm);
    assert OE.OracleColsOk(rer, qmB, str) by {
      forall k: int | 0 <= k <= |str| ensures LL.OracleOkAt(rer, qmB, T.InputAt(str, k)) {
        FST.OracleOkAtSubmap(rer, qm, qmB, T.InputAt(str, k));
      }
    }
    KG.LmOfBodiesNoBackref(body);
    assert OG.QmBodiesNoBackref(qmB);
    FST.FlipLooksMapTie(qmB, qmF);
    OG.MirrorOracleColsOkG(rer, qmB, qmF, str);
    FG.LookUniqueFXR(body);
    FG.LookIdsFXR(body);
    NRC.CdnTopAll(reF);
    TB.StampLooksCapFreeFXR(body);
    // ---- the involutions ----
    MW.FXRInvol(body);
    FS.ReverseReverse(str);
    MIR.MirrorViewInvolution(ov, n);
    assert FST.FXR(reF) == body && LC.Reverse(rstr) == str && MIR.MirrorView(ov', n) == ov;
    assert n - mcpN == cp;
    // (G5b-2) the real forward run's own list is the swapped list of the flipped body (tables agree)
    MW.SwapRunIsOwnRunPlus(reF, rstr, cp, AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant),
                           ov', plus);
    assert LCdn.compile_cdns(FST.FXR(reF)) == LCdn.compile_cdns(body);
    // (G5b-3, build path) the descent's premises in their own batch; under `dafny build` (lem's source order) the
    // call batch looped while every body was visible
    assert {:split_here} true;
    assert T.TransWf(reF) && NR.NestedFragmentCdnRE(reF);
    assert PIV.CapUnique(reF) && PIV.QuantUnique(reF) && LTB.LookUnique(reF);
    assert PSM.SizesOkRE(reF, ncap, nlook, nquant);
    assert forall l: nat :: l in LTB.LookIds(reF) ==> l < nlook;
    assert NRC.CdnTopRE(reF) && RF.StampLooksCapFreeRE(reF) && NRR.PlusTableOkS(reF, plusF);
    assert NRR.PlusTableOkS(FST.FXR(reF), plus);
    assert AR.QmapOk(reF, qmF) && qmF.bodies == M.BodiesOfRE(reF);
    assert n == |rstr| && mcpN <= n && |ov'| == n + 1;
    assert qmF.ov == ov' && AR.LmapOk(reF, qmF) && OE.OracleColsOk(rer, qmF, rstr);
    // the call: its postcondition transfers to ours by congruence on the involution equalities above
    assert {:split_here} true;
    hide *;
    RowKeysLBS(rer, qmF, reF, rstr, mcpN, ov', LCdn.compile_cdns(reF), plusF, plus, ncap, nlook, nquant, n);
  }

  /** (G5b-2) `BackRowClkFrame` on the S forms. THE CARRIER'S FRAME across the mirror: the mirror image of the real backward plus winner and the
      flipped forward plus winner (its own table) agree on the look bank and on every clock outside the
      CIN reconstruction sets of the flipped body. */
  lemma BackRowClkFrameS(rer: LW.RegExpRecord, qm: AR.QMap, body: R.regex, str: string, cp: nat,
                        ov: LOr.OracleView, cdns: LCdn.cdns, plus: seq<RB.code>, plusF: seq<RB.code>,
                        ncap: int, nlook: int, nquant: int, n: nat)
    requires T.TransWf(body) && NR.NestedFragmentCdnRE(body)
    requires PIV.CapUnique(body) && PIV.QuantUnique(body) && LTB.LookUnique(body)
    requires PSM.SizesOkRE(body, ncap, nlook, nquant)
    requires forall l: nat :: l in LTB.LookIds(body) ==> l < nlook
    requires NRC.CdnTopRE(body) && RF.StampLooksCapFreeRE(body) && NRR.PlusTableOkS(body, plus)
    requires NRR.PlusTableOkS(FST.FXR(body), plusF)
    requires AR.QmapOk(body, qm) && qm.bodies == M.BodiesOfRE(body)
    requires cdns == LCdn.compile_cdns(body)
    requires !rer.ignoreCase && !rer.multiline
    requires n == |str| && cp <= n && |ov| == n + 1
    requires qm.ov == ov && AR.LmapOk(body, qm) && OE.OracleColsOk(rer, qm, str)
    ensures |LC.Reverse(str)| == n
    ensures
      var bcB := CP.compile_to_bytecode(R.reverse_regex(body));
      var rr := AI.FFindMatchPlus(bcB, body, plus, str, ov, LAnc.Backward, cp,
                                  AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant), 0, cdns).0;
      var bcF := CP.compile_to_bytecode(FST.FXR(body));
      var rrF := AI.FFindMatchPlus(bcF, FST.FXR(body), plusF, LC.Reverse(str), MIR.MirrorView(ov, n), LAnc.Forward,
                                   n - cp, AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant), 0,
                                   MIR.SwapAnchorsCdns(cdns)).0;
      var fF := AI.FFindMatch(bcF, LC.Reverse(str),
                  AI.FInitState(bcF, n - cp, AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant), 0,
                                AI.cp_context(n - cp, LC.Reverse(str), LAnc.Forward)),
                  MIR.MirrorView(ov, n), LAnc.Forward, MIR.SwapAnchorsCdns(cdns)).0;
      (rr.Some? <==> rrF.Some?) && (rr.Some? <==> fF.Some?)
      // (G4b-1b) the frame from the FORWARD VM WINNER (live) to the mirror of the backward reconstruction
      && (rr.Some? ==>
            ClkFrameG4(FST.FXR(body), ELk.StampSet(fF.value.quant_regs.a_cp), MIR.MirrorThread(rr.value, n), fF.value)
            && PSM.BestLiveRE(FST.FXR(body), fF.value))
  {
    var reF := FST.FXR(body);
    var rstr := LC.Reverse(str);
    var ov' := MIR.MirrorView(ov, n);
    var cdns' := MIR.SwapAnchorsCdns(cdns);
    var bcF := CP.compile_to_bytecode(reF);
    var G, qmF, endlF := BackRowReadoutS(rer, qm, body, str, cp, ov, cdns, plus, ncap, nlook, nquant, n);
    var mcpN: nat := n - cp;
    var initsF := AI.FInitState(bcF, mcpN, AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant), 0,
                                AI.cp_context(mcpN, rstr, LAnc.Forward));
    var fmF := AI.FFindMatch(bcF, rstr, initsF, ov', LAnc.Forward, cdns');
    var rrF := AI.FFindMatchPlus(bcF, reF, plusF, rstr, ov', LAnc.Forward, mcpN,
                                 AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant), 0, cdns');
    assert rrF.0 == (match fmF.0
                     case None => None
                     case Some(thread) => Some(AI.FReconstructPlus(thread, reF, plusF, rstr, fmF.1, LAnc.Forward).0));
    var bcB := CP.compile_to_bytecode(R.reverse_regex(body));
    var raB := AI.FFindMatch(bcB, str,
                 AI.FInitState(bcB, cp, AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant), 0,
                               AI.cp_context(cp, str, LAnc.Backward)), ov, LAnc.Backward, cdns).0;
    var rr := AI.FFindMatchPlus(bcB, body, plus, str, ov, LAnc.Backward, cp,
                                AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant), 0, cdns).0;
    assert {:split_here} true;   // (G5b-2, pack S25) one batch per section under `dafny build`
    if rr.Some? {
      var tB := raB.value; var tF := fmF.0.value; var rp := rr.value;
      assert tF == MIR.MirrorThread(tB, n) && PSM.BestLiveRE(reF, tF);
      var Q := ELk.StampSet(tB.quant_regs.a_cp);
      assert ClkFrameG4(body, Q, rp, tB);
      StampSetMirror(tB.quant_regs, n);
      assert ELk.StampSet(tF.quant_regs.a_cp) == Q;
      QSetsFXR(body, Q);
      QSetsFXRE(body, Q);
      var m := MIR.MirrorThread(rp, n);
      assert m.capture_regs.a_clk == rp.capture_regs.a_clk && m.quant_regs.a_clk == rp.quant_regs.a_clk;
      assert tF.capture_regs.a_clk == tB.capture_regs.a_clk && tF.quant_regs.a_clk == tB.quant_regs.a_clk;
      // the look registers outside LooksQE: rp == tB there, and the mirror acts pointwise
      assert |m.look_regs.a_cp| == |tF.look_regs.a_cp|;
      forall k | k !in ELk.LooksQE(reF, Q)
        ensures AI.get_idx(m.look_regs.a_cp, k) == AI.get_idx(tF.look_regs.a_cp, k)
                && AI.get_idx(m.look_regs.a_clk, k) == AI.get_idx(tF.look_regs.a_clk, k)
      {
        assert k !in ELk.LooksQE(body, Q);
        W.MirrorGetIdx(rp.look_regs, n, k);
        W.MirrorGetIdx(tB.look_regs, n, k);
      }
      assert ClkFrameG4(reF, Q, m, tF);
    }
  }

}
