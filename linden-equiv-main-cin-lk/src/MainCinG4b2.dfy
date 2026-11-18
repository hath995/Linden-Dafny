// (G4b-2) THE THEOREM on the four-case transports: the top winner is the reconstructed one with its outer stamps
// cleared AND its dead look clocks lowered (`DL.LowerDeadLookClks`); machine B's carriers reach it through
// `T4.TieOkTTransportG4b2` / `T4.TieConvTransportG4b2Dom`, and the engine answer is unchanged
// (`DL.AnswerSyntheticLowered`). Lives above `LindenElkMainCinLk` and `LindenElkDeadLooks` (which imports it).
module LindenElkMainCinG4b2 {
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
  import LN = WarblreNumeric
  import AR = LindenElkActionsRep
  import EL = LindenElkEntryLk
  import GR = LindenElkGuardsRun         // (G5a-1 row N) the guard premise, for real
  import PIV = LindenElkPikeInv
  import CM = LindenElkClockMono
  import M = LindenElkMain
  import T = LindenElkTranslate
  import LL = LindenElkLookLeaves
  import NUL = LindenElkNullable
  import LTB = LindenElkLookTables
  import NI = LindenElkNestInv
  import CW = LindenElkCinWalk
  import RF = LindenElkReconFrame
  import CLP = LindenElkCinLookPaths
  import QCI = LindenElkQuantCpIrrel
  import FRD = LindenElkFinalReadout
  import FV = LindenElkFinalVm
  import NRR = LindenElkNulledReconRegs
  import NRC = LindenElkNulledRecon
  import RL = LindenElkRegsLaws
  import LES = LindenElkSpec
  import FC = LindenElkFlipClosed
  import TRM = LindenTreeResMirror
  import SD = LindenSpanDuality
  import OS = LindenElkOracleSpec
  import NRO = LindenElkNulledReconReadout
  import opened LindenElkLiftSimCore
  import opened LindenElkLiftSimOracle
  import opened LindenElkLiftSimChain
  import opened LindenElkLiftSimGate
  import opened LindenElkLiftSimCarriers
  import opened LindenElkLiftSimDeep
  import opened LindenElkLiftSimForward
  import opened LindenElkLiftSimMain
  import PSM = LindenElkPikeSim
  import PT = PikeTree
  import CR = Correctness
  import TT = LindenElkTreeThread
  import TREP = LindenElkTreeRep
  import ATR = LindenElkActionsTreeRep
  import WO = LindenElkWalkOk
  import WkE = LindenElkWalkOkEntry
  import NB = LindenElkNulledPlusBool
  import OE = LindenElkOracleEntry
  import OB = LindenElkOracleBuild
  import LFU = FunctionalUtils
  import FS = FunctionalSemantics
  import PTL = LindenElkPikeTreeLk
  import CG = LindenElkFlipClosedG       // (gate B) the scope-free closedness ladder
  import LB = LindenElkLookBank          // (gate C, G2) the look-bank invariant
  import opened LindenElkBankFrames      // (G3a, two-machines) ClkFrame, AncFrame, QInCinQ, NRRLookIdsEq, OnlyCapIdsFromFrameOuter
  import opened LindenElkTwoMachines     // (G3a) TranslateCinOk, the four tie transports
  import CL = LindenElkCinLooks          // (G4a) the scope, machine B's entry, the frame and the transports
  import RBk = LindenElkReconBank        // (G4a) the replayed look and quant banks
  import ELk = LindenElkEmptyLooks       // (G4b-1) the empty-path look set, the frames at the stamped set
  import SL = LindenElkStampLive
  import opened LindenElkMainCinLk
  import DL = LindenElkDeadLooks
  import T4 = LindenElkTransportsG4b2
  import LR = LindenElkLookRecord
  import BF = LindenElkBankFrames

  /** THE THEOREM (G4b-2 wiring): machine B's carriers reach the top synthetic winner through the four-case
      transports; its dead look clocks are lowered, which leaves the engine answer unchanged. The scope premise
      `CL.CinLooksCapFreeRE` is still carried here (its removal is the last G4b step). */
  lemma MainTheoremL5Cin(raw: R.raw_regex, str: string)
    requires NR.NestedFragmentCdnRaw(raw)
    requires NRC.CdnTopRE(R.lazy_prefix(R.annotate(raw)))   // (G5a-1) every CDN plus at top level, body look-free
    requires T.Latin1Wf(raw)
    requires M.LookBodiesPlusGateRE(R.lazy_prefix(R.annotate(raw)))   // (G3a) lookbehind bodies stamp-free, lookahead bodies CIN
    requires CL.CinLooksCapFreeRE(R.lazy_prefix(R.annotate(raw)))   // (G4a) a CIN plus body's looks capture nothing
    ensures LES.MatcherSpec(raw, str, LES.Normalize(AI.FFullMatch(raw, str)))
  {
    hide NUL.NonNullableL, NUL.CINullableL, NUL.NoNulledPlusL, AR.NfaRepCinL;
    // the two recursive gates are facts here, never unfolded (in context they blew batch 6 past 19 GB)
    hide M.LookBodiesPlusGateRE, CL.CinLooksCapFreeRE;
    var ast := R.annotate(raw);
    var re := R.lazy_prefix(ast);
    var rer := LES.TheRer(raw);
    var inp := LC.InitInput(str);
    var ngroups := LES.NGroups(raw);
    assert !rer.multiline && !rer.ignoreCase;

    // ---- static packages -------------------------------------------------
    T.AnnotateWf(raw);
    NR.SpecRegexNestedFragmentCdn(raw);
    LTB.SpecRegexLookUnique(raw);
    LTB.SpecRegexLidsWellNested(raw);
    PIV.SpecRegexCapUnique(raw);
    PIV.SpecRegexQuantUnique(raw);
    var qm := AR.QMap(M.QmOfRE(re), OE.LmOf(re), AI.FBuildOracle(CP.FFullCompilation(ast), str), M.BodiesOfRE(re));
    M.QmOfREEntries(re);
    M.BodiesOfREEntries(re);
    M.QmapOkFromEntries(re, qm);
    OE.LmapOkOfLmOf(re, qm);
    assert AR.QmapOk(re, qm) && AR.LmapOk(re, qm);
    assert {:split_here} true;
    // ---- the nested oracle entry -------------------------------------------
    assert LL.OracleOkSuffix(rer, qm, inp) by {
      var crv0 := CP.FFullCompilation(ast);
      var pre := R.Re_quant(R.NonNullable, 0, R.CountedQuant(0, None, false), R.Re_character(R.Dot));
      assert re == R.Re_con(pre, ast);
      LTB.FFullCompilationLookOk(ast);
      assert LTB.LookTablesOk(pre, crv0);
      assert LTB.LookTablesOk(re, crv0);
      assert LTB.LookIds(pre) == {};
      assert LTB.LookIds(re) == LTB.LookIds(ast);
      assert NR.NestedFragmentCdnRE(ast);
      OracleOkRowsL5Cdn(rer, ast, crv0, str, re);
    }

    NR.CompileToBytecodeRepCdn(re);
    var code := CP.compile_to_bytecode(re);
    var next := CP.compile(re, 0, CP.Progress).1;
    var endl: nat := next as nat;
    assert NR.NfaRepRE(re, code, 0, endl)
           && NR.GetPcRE(code, endl) == Some(RB.Accept) && |code| == endl + 1;
    CompileStutterTameRECdn(re);
    assert PSM.StaticCoreCdnRE(qm, re, code, endl);

    var maxcap := R.max_group(ast);
    var maxquant := R.max_quant(ast);
    assert R.max_group(re) == maxcap;
    assert R.max_quant(re) == R.imax(0, maxquant) == maxquant;
    var ncap := 2 * maxcap + 2;
    var nlook := R.max_lookaround(ast) + 1;
    var nquant := maxquant + 1;
    assert PSM.SizesOkRE(re, ncap, nlook, nquant);
    assert ngroups == (maxcap + 1) as nat;
    var maxlook := R.max_lookaround(ast);
    assert R.max_lookaround(re) == maxlook by {
      var pre := R.Re_quant(R.NonNullable, 0, R.CountedQuant(0, None, false), R.Re_character(R.Dot));
      assert re == R.Re_con(pre, ast);
    }

    assert {:split_here} true;
    // ---- the spec tree -----------------------------------------------------
    LFU.ComputeTrIsTree(rer, [LS.Areg(T.Translate(re))], inp, LG.Empty, WP.Forward);
    var t := LFU.ComputeTr(rer, [LS.Areg(T.Translate(re))], inp, LG.Empty, WP.Forward);
    assert LS.IsTree(rer, [LS.Areg(T.Translate(re))], inp, LG.Empty, WP.Forward, t);
    assert LES.SpecRegex(raw) == T.Translate(re);
    EL.CdnHeadsAreOn();   // (G5a-1 rows F, N) the switch is on
    TranslateFragmentPikeLkRecLkCdn(re);
    EL.BooleanCorrectLkRec(rer, T.Translate(re), inp, t);
    assert forall i :: 0 <= i < |[LS.Areg(T.Translate(re))]| ==> ![LS.Areg(T.Translate(re))][i].Acheck?;
    M.BoolTreeLbIrrel(rer, [LS.Areg(T.Translate(re))], inp, BS.CanExit, BS.CannotExit, t);
    assert EL.BoolTreeLk(rer, [LS.Areg(T.Translate(re))], inp, BS.CannotExit, t);

    assert {:split_here} true;
    // ---- the CHECKED tree (machine A's, shared with B) ----------------------
    WkE.WalkOkEntryCdn(re);
    assert EL.PikeLkActionsRec([LS.Areg(T.Translate(re))]) by {
      assert [LS.Areg(T.Translate(re))] == [LS.Areg(T.Translate(re))] + [];
      assert EL.PikeLkActionsRec([]);
      EL.PikeLkActionsRecConsIff(LS.Areg(T.Translate(re)), []);
    }
    var S := PIV.CapIdsInLooks(re);
    M.LkBodyGroupsEqCapIdsInLooks(re);
    assert S == LL.LkBodyGroups(T.Translate(re));
    assert WO.WalkOk([LS.Areg(T.Translate(re))], code, 0, ATR.EaOf(BS.CannotExit));
    AR.CompileToBytecodeActionsRepCdn(rer, qm, re);
    assert AR.ActionsRepL(rer, qm, [LS.Areg(T.Translate(re))], code, 0);
    assert LL.LkActsInS([LS.Areg(T.Translate(re))], S) by {
      LL.LkBodyGroupsConfines(T.Translate(re), S);
      LL.LkActsInSCons(LS.Areg(T.Translate(re)), [], S);
    }
    LL.ComputeTrLkConfinedK(rer, [LS.Areg(T.Translate(re))], inp, LG.Empty, WP.Forward, S);
    assert NB.EncOk([LS.Areg(T.Translate(re))], inp, BS.CannotExit) by { NB.EncOkNoChecks([LS.Areg(T.Translate(re))], inp, BS.CannotExit); }
    var tstar := ATR.ActionsTreeRepRENested(rer, qm, [LS.Areg(T.Translate(re))], code, 0, inp, BS.CannotExit, t, S);
    assert TREP.TreeRepRE(qm, tstar, code, 0, inp, false);
    assert TT.TreeThreadRE(rer, qm, code, inp, tstar, 0, false);
    NB.RAFirstLeafOutside(tstar, t, inp, S);

    assert {:split_here} true;
    // ---- the engine pipeline ---------------------------------------------
    var crv := CP.FFullCompilation(ast);
    M.FFullCompilationFactsNested(ast);
    assert crv.f_main_ast == ast && crv.f_main_bc == code && crv.f_main_cdns == LCdn.compile_cdns(ast);
    FFullCompilationLookLens(ast);
    assert |crv.f_look_types| == |crv.f_look_ast|;
    assert {:split_here} true;
    var ov := AI.FBuildOracle(crv, str);
    OB.FBuildOracleViewLen(crv, str);
    assert qm.ov == ov;
    var capture := AReg.init_regs(ncap);
    var look := AReg.init_regs(nlook);
    var quant := AReg.init_regs(nquant);
    var ctx := AI.cp_context(0, str, LAnc.Forward);
    var inits := AI.FInitState(code, 0, capture, look, quant, 0, ctx);
    var fmres := AI.FFindMatch(code, str, inits, ov, LAnc.Forward, crv.f_main_cdns);
    var result := fmres.0;

    assert {:split_here} true;
    // ---- gate statics + look tables ---------------------------------------
    LTB.FFullCompilationLookOk(ast);
    assert LTB.LookTablesOk(re, crv) by {
      var pre := R.Re_quant(R.NonNullable, 0, R.CountedQuant(0, None, false), R.Re_character(R.Dot));
      assert re == R.Re_con(pre, ast);
      assert LTB.LookTablesOk(pre, crv);
      assert LTB.LookTablesOk(ast, crv);
    }
    OE.LmOfDom(re);
    LTB.LookIdsLeMax(re);
    assert forall l: int :: l in qm.looks ==>
                              l >= 0 && (l as nat) in LTB.LookIds(re) && l < nlook;
    assert forall x: nat :: x in LTB.LookIds(re) ==> (x as int) in qm.looks by {
      forall x: nat | x in LTB.LookIds(re) ensures (x as int) in qm.looks { }
    }
    assert GateStaticsOkNested(qm, re, crv, ncap, nlook, nquant) by {
      // (G3a) the plus-row premises at the top regex, scoped: as context facts they stalled the final call
      // (G5a-1 row N) the top may hold a CDN plus: the widened table, and the narrow one at each look node
      assert LookNodesPlusOk(re, crv.f_plus_bc) by {
        FRD.PlusTableOkFullS(ast);
        LookNodesPlusOkFromS(re, crv.f_plus_bc);
      }
      assert forall l: nat :: l in LTB.LookIds(re) ==> l < nlook;
      GateStaticsFromTablesCdn(qm, re, crv, ncap, nlook, nquant);
    }

    assert {:split_here} true;
    // ---- the two machines on the same checked tree --------------------------
    PSM.InitialPikeInvFullREAtCpCdn(rer, qm, re, code, endl, ngroups, str, 0, tstar,
                                       inits, ncap, nlook, nquant);
    assert ctx.nextchar == AI.get_char(str, 0);
    assert PIV.ContextOkRE(str, inits.cp, inits.context);
    assert M.OracleSufAllO(rer, qm, str) by {
      reveal M.OracleSufAllO();
      forall cp: nat | cp <= |str| ensures LL.OracleOkSuffix(rer, qm, PIV.InpOfCp(str, cp)) {
        OracleOkSuffixAtCp(rer, qm, str, cp);
      }
    }
    SufAllToColsOk(rer, qm, str);
    // machine B on the engine-shaped walk, agreeing with the spec leaf outside G
    var G: set<LG.GroupId> := PIV.CapIdsOutsideLooks(re);
    CL.TranslateCinOkG4(re, G);
    PIV.CapIdsLooksDisjoint(re);
    assert G * S == {};
    // (G5a-1 row N) the run premise of the guard, for real (cdn-sound through `GR.GuardsOkRunTop`).
    // Scoped: `OracleOkAt` is a transparent quantifier; at the top level it blew this batch past 10 GB.
    assert {:split_here} true;
    assert PSM.GuardsOkRun(qm, code, crv.f_main_cdns, ov, str) by {
      assert forall cp: nat :: cp <= |str| ==> LL.OracleOkAt(rer, qm, PIV.InpOfCp(str, cp)) by {
        forall cp: nat | cp <= |str| ensures LL.OracleOkAt(rer, qm, PIV.InpOfCp(str, cp)) {
          OracleOkSuffixAtCp(rer, qm, str, cp);   // the source of the suffix fact (no longer in scope here)
          assert LL.OracleOkSuffix(rer, qm, PIV.InpOfCp(str, cp));
        }
      }
      GR.GuardsOkRunTop(rer, qm, ast, re, code, endl, str, ov);
    }
    assert {:split_here} true;
    var bleaf := L3aCompositeCloseRecGCdn(rer, qm, re, code, endl, ngroups, crv, str, ov, S, tstar, t, inp,
                                       inits, crv.f_main_cdns, result, ncap, nlook, nquant, G);
    // machine A: the VM's best is the checked tree's first leaf
    assert {:split_here} true;
    var pts0 := PT.PikeTreeInitialState(tstar, inp);
    var bestT := PSM.FindMatchSimRECdn(rer, qm, re, code, endl, ngroups, str, pts0, inits,
                                          ov, LAnc.Forward, crv.f_main_cdns, ncap, nlook, nquant);
    M.TrcREToLinden(pts0, PT.PTS_final(bestT));
    TREP.TreeRepPikeSubtree(qm, tstar, code, 0, inp, false);
    PT.InitPiketreeInv(tstar, inp);
    CR.PikeTreeTrcCorrect(pts0, PT.PTS_final(bestT), LT.FirstLeaf(tstar, inp));
    assert bestT == LT.FirstLeaf(tstar, inp);
    assert PIV.BestMatchRE(re, qm, str, bestT, result);

    assert {:split_here} true;
    // ---- stage the engine answer ------------------------------------------
    var bc := AI.FBuildCapture(crv, str, ov);
    assert AI.FMatcher(crv, str) == bc.0;
    assert AI.FFullMatch(raw, str) == bc.0;
    var fmp := AI.FFindMatchPlus(crv.f_main_bc, crv.f_main_ast, crv.f_plus_bc, str, ov,
                                 LAnc.Forward, 0, capture, look, quant, 0, crv.f_main_cdns);
    assert AI.FInitState(crv.f_main_bc, 0, capture, look, quant, 0,
                         AI.cp_context(0, str, LAnc.Forward)) == inits;
    assert fmp.0 == (match result
                     case None => None
                     case Some(thread) =>
                       Some(AI.FReconstructPlus(thread, ast, crv.f_plus_bc, str, fmres.1, LAnc.Forward).0));
    assert R.max_group(crv.f_main_ast) == maxcap && R.max_quant(crv.f_main_ast) == maxquant;
    assert ncap == 2 * R.max_group(crv.f_main_ast) + 2;
    assert nquant == R.max_quant(crv.f_main_ast) + 1;

    if result.None? {
      assert fmp.0 == None;
      M.FBuildCaptureUnfoldL3a(crv, str, ov, ncap, nlook, nquant, capture, look, quant, fmp);
      assert bc.0 == None;
      assert LT.FirstLeaf(t, inp) == None;
      assert LES.Normalize(AI.FFullMatch(raw, str)) == None;
      assert LES.MatcherSpec(raw, str, None);
    } else {
      assert {:split_here} true;
      var best := result.value;
      assert PSM.BestLiveRE(re, best);
      NRC.CdnTopPrefix(ast);   // (G5a-1 row N) the scope on `ast`
      assert PSM.StampPathOk(qm, str, best.quant_regs.a_cp);   // FindMatchSimRECdn, for the winner
      var rp := ReadoutAtWinner(qm, ast, re, crv, code, endl, str, ov, inits, capture, look, quant,
                                ncap, nlook, nquant, result);
      var D := M.QIdsOuter(re);
      var rp0 := ClearQuantCps(rp, D);
      ClearQuantCpsGm(re, rp, D);
      ClearQuantCpsFacts(rp, D);
      assert fmres.1 == ov;
      assert fmp.0 == Some(rp) && fmp.1 == ov;

      assert {:split_here} true;
      // ---- the tie at (spec leaf, rp0) ---------------------------------------
      assert LT.FirstLeaf(t, inp).Some?;
      var leaf := LT.FirstLeaf(t, inp).value;
      assert bestT.Some?;
      assert PIV.ThreadTracksGm(re, qm, str, best, bestT.value.1);
      assert bestT.value.1 == PIV.GmOfLiveR(re, qm, str, best.capture_regs, best.look_regs, best.quant_regs)
        by { reveal PIV.TieGm; }
      assert PIV.GmOfLive(re, rp0.capture_regs, rp0.look_regs, rp0.quant_regs) == bestT.value.1;
      assert LL.GmAgreeOutside(bestT.value.1, leaf.1, S);
      assert GmtTieOutside(re, rp0, leaf.1, S);
      assert bleaf.Some? && LL.GmAgreeOutside(bleaf.value.1, leaf.1, G);
      M.FirstLeafOrdered(t, inp, leaf);

      assert {:split_here} true;
      // ---- (G4b-2) the four-case transports, at the LOWERED synthetic winner -------------
      var Q := ELk.StampSet(best.quant_regs.a_cp);
      var rp0L := ClearQuantCps(DL.LowerDeadLookClks(re, Q, rp), D);
      DL.FFindMatchQClkPosInit(code, str, ov, LAnc.Forward, crv.f_main_cdns, 0, capture, look, nquant);
      assert DL.QClkPosT(best);
      assert BestTieLkNestedTop(rer, re, crv, str, ov, S, bleaf, result, ncap, nlook, nquant);
      TopTieLowered(rer, qm, ast, re, crv, code, endl, str, ov, S, G, best, bleaf.value, leaf, rp, ncap, nlook, nquant);
      assert BestTieLkNestedTop(rer, re, crv, str, ov, S, Some(leaf), Some(rp0L), ncap, nlook, nquant)
             && M.WinRegsOk(ast, re, crv, str, ov, rp0L, ncap, nlook, nquant);

      assert {:split_here} true;
      // ---- the endpoint at rp0L ------------------------------------------------
      EndpointAtRp0(rer, qm, crv, str, ast, re, code, endl, ov, rp0L, leaf, t, inp, S, ncap, nlook, nquant);
      var res := AI.FLookLoop(crv, str, 1, maxlook, rp0L.capture_regs, rp0L.look_regs, rp0L.quant_regs, ov);
      var synthetic := AI.Thread(rp0L.pc, res.0, res.1, res.2, rp0L.exit_allowed);
      assert leaf.1 == PIV.NormGm(PIV.GmOfLive(re, res.0, res.1, res.2));

      assert {:split_here} true;
      // ---- the engine answer, read at rp0L (the lowering leaves it unchanged) ----------------
      M.FBuildCaptureUnfoldL3a(crv, str, ov, ncap, nlook, nquant, capture, look, quant, fmp);
      DL.AnswerSyntheticLowered(ast, re, crv, str, ov, rp, Q, ncap, nlook, nquant);
      assert bc.0 == Some(AI.filter_reset(crv.f_main_ast, res.0, res.1, res.2, -1)) by {
        assert fmp.0.value == rp;
        var r1 := AI.FLookLoop(crv, str, 1, R.max_lookaround(crv.f_main_ast),
                               rp.capture_regs, rp.look_regs, rp.quant_regs, fmp.1);
        assert bc.0 == Some(AI.filter_reset(crv.f_main_ast, r1.0, r1.1, r1.2, -1));
      }
      assert AI.FFullMatch(raw, str)
          == Some(AI.filter_reset(ast, synthetic.capture_regs, synthetic.look_regs,
                                  synthetic.quant_regs, -1));

      assert {:split_here} true;
      // ---- extraction ------------------------------------------------------
      assert EL.BoolTreeLk(LES.TheRer(raw), [LS.Areg(LES.SpecRegex(raw))], LC.InitInput(str), BS.CannotExit, t);
      assert {:split_here} true;   // (G3a) the extraction section, one batch per step
      assert LS.IsTree(LES.TheRer(raw), [LS.Areg(LES.SpecRegex(raw))], LC.InitInput(str), LG.Empty, WP.Forward, t);
      assert {:split_here} true;   // (G3a) the extraction section, one batch per step
      assert CM.ThreadRegsWf(synthetic, ncap, nlook, nquant);
      assert ncap == 2 * R.max_group(R.annotate(raw)) + 2
             && nlook == R.max_lookaround(R.annotate(raw)) + 1
             && nquant == R.max_quant(R.annotate(raw)) + 1;
      assert {:split_here} true;   // (G3a) the extraction section, one batch per step
      assert M.QuantClkFinal(synthetic);
      assert {:split_here} true;   // (G3a) the extraction section, one batch per step
      assert leaf.1 == PIV.NormGm(PIV.GmOfLive(re, synthetic.capture_regs, synthetic.look_regs,
                                               synthetic.quant_regs));
      assert {:split_here} true;   // (G3a) the extraction section, one batch per step
      assert LT.FirstLeaf(t, LC.InitInput(str)) == Some(leaf);
      assert {:split_here} true;   // (G3a) the extraction section, one batch per step
      // (G3a) MainExtractionL5Lk's premises in its own syntax, one batch each: the call below is then
      // a match against ground facts (as one batch with the call it ran past 600 s twice).
      assert AI.FFullMatch(raw, str)
          == Some(AI.filter_reset(R.annotate(raw), synthetic.capture_regs, synthetic.look_regs,
                                  synthetic.quant_regs, -1));
      assert {:split_here} true;   // (G3a) the extraction section, one batch per step
      assert var re' := R.lazy_prefix(R.annotate(raw));
             leaf.1 == PIV.NormGm(PIV.GmOfLive(re', synthetic.capture_regs, synthetic.look_regs, synthetic.quant_regs));
      assert {:split_here} true;   // (G3a) the extraction section, one batch per step
      assert NR.NestedFragmentCdnRaw(raw) && T.Latin1Wf(raw);
      assert {:split_here} true;   // (G3a) the extraction section, one batch per step
      assert ExtractionPre(raw, str, t, synthetic, leaf) by {
        hide *;
        ExtractionPreIntro(raw, str, t, synthetic, leaf);   // (G5a-1) the body stays folded here
      }
      assert {:split_here} true;   // (G3a) the extraction section, one batch per step
      assert LES.MatcherSpec(raw, str, LES.Normalize(AI.FFullMatch(raw, str))) by {
        hide *;
        MainExtractionL5LkPre(raw, str, t, synthetic, leaf);
      }
    }
  }


  /** (G4b-2) Machine B's best tie at the TOP synthetic winner `rp0L` (the reconstructed winner, outer stamps
      cleared, dead look clocks lowered): the four-case transports at `rp0`, moved to `rp0L`. */
  lemma TopTieLowered(rer: LW.RegExpRecord, qm: AR.QMap, ast: R.regex, re: R.regex, crv: CP.FCompiled, code: RB.code,
                      endl: nat, str: string, ov: LOr.OracleView, S: set<LG.GroupId>, G: set<LG.GroupId>,
                      best: AI.Thread, bleaf: LT.Leaf, leaf: LT.Leaf, rp: AI.Thread, ncap: int, nlook: int, nquant: int)
    requires crv == CP.FFullCompilation(ast) && re == R.lazy_prefix(ast)
    requires PSM.StaticCoreCdnRE(qm, re, code, endl) && LTB.LookUnique(re)
    requires qm.ov == ov && !rer.multiline && !rer.ignoreCase && |ov| == |str| + 1 && OE.OracleColsOk(rer, qm, str)
    requires S == PIV.CapIdsInLooks(re) && G == PIV.CapIdsOutsideLooks(re) && G * S == {}
    requires GateStaticsOkNested(qm, re, crv, ncap, nlook, nquant) && LTB.LookTablesOk(re, crv)
    requires PSM.BestLiveRE(re, best) && PSM.StampPathOk(qm, str, best.quant_regs.a_cp) && DL.QClkPosT(best)
    requires BestTieLkNestedTop(rer, re, crv, str, ov, S, Some(bleaf), Some(best), ncap, nlook, nquant)
    requires LL.GmAgreeOutside(bleaf.1, leaf.1, G)
    requires GmtTieOutside(re, ClearQuantCps(rp, M.QIdsOuter(re)), leaf.1, S)
    requires CL.ClkFrameG4(re, ELk.StampSet(best.quant_regs.a_cp), ClearQuantCps(rp, M.QIdsOuter(re)), best)
    requires LR.WinnerLookRec(qm, re, str, best, rp)
    requires M.WinRegsOk(ast, re, crv, str, ov, ClearQuantCps(rp, M.QIdsOuter(re)), ncap, nlook, nquant)
    ensures var rp0L := ClearQuantCps(DL.LowerDeadLookClks(re, ELk.StampSet(best.quant_regs.a_cp), rp), M.QIdsOuter(re));
            BestTieLkNestedTop(rer, re, crv, str, ov, S, Some(leaf), Some(rp0L), ncap, nlook, nquant)
            && M.WinRegsOk(ast, re, crv, str, ov, rp0L, ncap, nlook, nquant)
  {
    var D := M.QIdsOuter(re);
    var Q := ELk.StampSet(best.quant_regs.a_cp);
    var rp0 := ClearQuantCps(rp, D);
    var rp0L := ClearQuantCps(DL.LowerDeadLookClks(re, Q, rp), D);
    DL.LowerClearCommute(re, Q, rp, D);
    assert rp0L == DL.LowerDeadLookClks(re, Q, rp0);
    ClearQuantCpsFacts(rp, D);
    DL.LowerDeadLookClksFacts(re, Q, rp0);
    DL.WinRegsOkRp0(ast, re, crv, str, ov, rp, Q, ncap, nlook, nquant);
    assert BF.ClkFrameG4(re, Q, rp0, best);
    assert FrozenOk(rer, re, str, bleaf.1, best) && LookNestOkTTop(re, S, bleaf.1, best)
           && LookNestBackTTop(re, crv, str, ov, S, bleaf.1, best, ncap, nlook, nquant)
           && LookNestBackTTopDeep(rer, re, crv, str, ov, S, bleaf.1, best, ncap, nlook, nquant);
    EL.TranslateFragmentPikeLkRecCdn(re);
    T4.OracleEverywhere(rer, qm, str);
    assert {:split_here} true;
    // OkT: unguarded at rp0, hence at rp0L (a lowered lid is not present, so names no group), guarded there
    T4.TieOkTTransportG4b2(rer, qm, re, str, Q, S, G, bleaf.1, leaf.1, best, rp, rp0);
    OkTULowered(re, Q, S, leaf.1, rp0);
    OkTUToGuarded(re, S, leaf.1, rp0L);
    assert {:split_here} true;
    // the converses at rp0L: the lowered lids lose dominance
    assert M.WinRegsOk(ast, re, crv, str, ov, rp0, ncap, nlook, nquant);
    assert CM.LookCpSetWithClk(rp0.look_regs) && ELk.QClkGe(rp0.quant_regs, best.quant_regs.a_clk) by {
      reveal M.WinRegsOk();
    }
    DL.LowerDeadNotDom(re, Q, best, rp0);
    T4.TieConvTransportG4b2Dom(rer, qm, re, crv, str, ov, Q, S, G, bleaf.1, leaf.1, best, rp, rp0, rp0L,
                               ncap, nlook, nquant);
    assert {:split_here} true;
    // the value tie outside S (the lowering is invisible to `filter_reset`) and no stamp at rp0L
    GmOfLiveLowered(re, Q, rp0);
    assert GmtTieOutside(re, rp0L, leaf.1, S);
    assert forall k: int :: AI.get_idx(rp0L.quant_regs.a_cp, k) < 0 by { reveal M.WinRegsOk(); }
    FrozenOkNoStamps(rer, re, str, leaf.1, rp0L);
  }

  /** The unguarded presence carrier survives the lowering: a lowered lid is not present, so it names no group. */
  lemma OkTULowered(re: R.regex, Q: set<int>, S: set<LG.GroupId>, gm: LG.GroupMap, th: AI.Thread)
    requires LookNestOkTTopU(re, S, gm, th)
    ensures LookNestOkTTopU(re, S, gm, DL.LowerDeadLookClks(re, Q, th))
  {
    var thL := DL.LowerDeadLookClks(re, Q, th);
    DL.LowerDeadLookClksFacts(re, Q, th);
    forall lid: nat | lid in NI.TopLookIds(re)
                      && (lid in LTB.LookIds(re)
                          && exists g: LG.GroupId :: g in S && g in gm && g in PIV.CapIds(NI.LookBodyOfRE(re, lid)))
      ensures NI.LookPathPresent(re, thL.capture_regs.a_clk, thL.quant_regs.a_clk, -1, lid)
              && AI.get_idx(thL.look_regs.a_clk, lid as int) >= 0
              && AI.get_idx(thL.look_regs.a_clk, lid as int) >= NI.MxAtLidLk(re, thL.quant_regs.a_clk, -1, lid)
    {
      assert NI.LookPathPresent(re, th.capture_regs.a_clk, th.quant_regs.a_clk, -1, lid);
      assert !DL.DeadLid(re, Q, th, lid as int);
      assert AI.get_idx(thL.look_regs.a_clk, lid as int) == AI.get_idx(th.look_regs.a_clk, lid as int);
    }
  }

  /** The live map is blind to the lowering: `filter_capture` never reads a dead lid's clock. */
  lemma GmOfLiveLowered(re: R.regex, Q: set<int>, th: AI.Thread)
    requires LTB.LookUnique(re)
    ensures var thL := DL.LowerDeadLookClks(re, Q, th);
            PIV.GmOfLive(re, thL.capture_regs, thL.look_regs, thL.quant_regs)
            == PIV.GmOfLive(re, th.capture_regs, th.look_regs, th.quant_regs)
  {
    var thL := DL.LowerDeadLookClks(re, Q, th);
    DL.LowerDeadLookClksFacts(re, Q, th);
    var lc1 := AReg.as_arrays(thL.look_regs).1;
    var lc2 := AReg.as_arrays(th.look_regs).1;
    forall l: nat | AI.get_idx(lc1, l) != AI.get_idx(lc2, l)
      ensures l !in LTB.LookIds(re)
              || (l in NI.TopLookIds(re) && !NI.LookPathPresent(re, th.capture_regs.a_clk, th.quant_regs.a_clk, -1, l))
    {
      assert DL.DeadLid(re, Q, th, l as int);
    }
    var (cr, cc) := AReg.as_arrays(th.capture_regs);
    var (_, qc) := AReg.as_arrays(th.quant_regs);
    DL.FilterCaptureLookClkDead(re, cr, cc, lc1, lc2, qc, -1);
    assert AI.filter_reset(re, thL.capture_regs, thL.look_regs, thL.quant_regs, -1)
        == AI.filter_reset(re, th.capture_regs, th.look_regs, th.quant_regs, -1);
  }
}
