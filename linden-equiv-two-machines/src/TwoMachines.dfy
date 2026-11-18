// (G3a) The two machines at a lookahead body (A6, `TwoMachinesAt`) and the tie transports from
// machine B's winner to the reconstructed one, moved down from main-cin-lk so the carriers can use
// them. Sits between lift-sim-gate and lift-sim-carriers; machine A itself is in machine-a.
module LindenElkTwoMachines {
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
  import NRC = LindenElkNulledRecon
  import NRR = LindenElkNulledReconRegs
  import NRO = LindenElkNulledReconReadout
  import FRG = LindenElkFinalRegs
  import FRD = LindenElkFinalReadout
  import FV = LindenElkFinalVm
  import RF = LindenElkReconFrame
  import CLP = LindenElkCinLookPaths
  import CW = LindenElkCinWalk
  import QCI = LindenElkQuantCpIrrel
  import FRA = LindenElkFinalReadoutAt
  import RRA = LindenElkRowReconAt
  import CR = Correctness
  import opened LindenElkBankFrames
  import SLk = LindenElkStampLooks   // (G5b-3)
  import ELk = LindenElkEmptyLooks   // (G4b-1) the empty-path look scope
  import NPL = LindenElkNulledPlusLk   // (G4b-1) machine B's static scope
  import LR = LindenElkLookRecord   // (G4b-2) the look record at the winner
  import SBk = LindenElkStampBank
  import opened LindenElkMachineA
  import T4 = LindenElkTransportsG4b2   // (G4b-2) the four-case transports

  // =========================================================================
  // 0. Statics: the glue's side condition on the translated regex.
  // =========================================================================

  lemma LookFreeLkBodies(r: R.regex, S: set<LG.GroupId>)
    requires T.TransWf(r) && NR.LookFreeRE(r)
    ensures LL.LkBodiesInS(T.Translate(r), S)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => LookFreeLkBodies(r1, S); LookFreeLkBodies(r2, S);
    case Re_con(r1, r2) => LookFreeLkBodies(r1, S); LookFreeLkBodies(r2, S);
    case Re_quant(_, _, _, r1) => LookFreeLkBodies(r1, S);
    case Re_capture(_, r1) => LookFreeLkBodies(r1, S);
    case _ =>
  }
  /** Every CIN-greedy plus of the translation has a look-free body whose groups
      lie in `G` (any `G` covering the outside-look captures). */
  lemma TranslateCinOk(r: R.regex, G: set<LG.GroupId>)
    requires T.TransWf(r) && NR.NestedFragmentRE(r)
    requires RF.CinBodiesLookFreeRE(r)   // (G3a) `CinOk`'s look arm is `true`: no look-body gate
    requires forall g: nat :: g in PIV.CapIdsOutsideLooks(r) ==> g in G
    ensures CW.CinOk(T.Translate(r), G)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => TranslateCinOk(r1, G); TranslateCinOk(r2, G);
    case Re_con(r1, r2) => TranslateCinOk(r1, G); TranslateCinOk(r2, G);
    case Re_capture(_, r1) => TranslateCinOk(r1, G);
    case Re_lookaround(_, _, _) =>
    case Re_quant(nul, qid, q, body) =>
      TranslateCinOk(body, G);
      var tb := T.Translate(body);
      assert T.Translate(r) == L.Quantified(q.greedy, q.min as nat, T.TrDelta(q), tb);
      if q.min > 0 && CW.CinGreedyL(q.greedy, T.TrDelta(q), tb) {
        assert q.greedy && T.TrDelta(q) == LN.Inf by { reveal CW.CinGreedyL(); }
        assert q.max == None;
        if nul == R.NonNullable {
          NUL.TransNonNullable(body);
          CW.NotCinGreedyNonNullable(q.greedy, T.TrDelta(q), tb);
          assert false;
        }
        assert nul == R.CINullable;
        assert NR.LookFreeRE(body);
        LookFreeLkBodies(body, {});
        PIV.DefGroupsCapIds(body);
        PIV.LookFreeCapIdsInLooksEmpty(body);
        PIV.CapIdsSplit(body);
        forall g | g in L.DefGroups(tb) ensures g in G {
          assert g in PIV.CapIds(body);
          assert g in PIV.CapIdsOutsideLooks(r);
        }
        CW.CinArmFromOld(tb, G);   // (G4b-1) the old arm implies today's
      }
      if q.min > 0 && CW.CdnGreedyL(q.greedy, T.TrDelta(q), tb) {
        // (G5a-1 row G) `CinOk` also asks the body condition of a CDN head; the narrow fragment has none
        assert q.greedy && T.TrDelta(q) == LN.Inf && !NUL.NonNullableL(tb) && !NUL.CINullableL(tb) by { reveal CW.CdnGreedyL(); }
        assert q.max == None;
        if nul == R.NonNullable { NUL.TransNonNullable(body); assert false; }
        assert nul == R.CINullable;
        NUL.TransCINullable(body);
        assert false;
      }
    case _ =>
  }

  // =========================================================================
  // 1. The tie transport: machine B's carriers at (bleaf, best) become carriers
  //    at (the spec leaf, the reconstructed winner).
  // =========================================================================




  /** (G3a) The fresh VM run of `bodycode` at `cp` has a winner, and `th` carries its look bank. Opaque: it
      names `FFindMatch` on a fresh initial state, which the solver would otherwise unfold at every use. */
  opaque ghost predicate WinnerLookKept(bodycode: RB.code, str: string, cp: nat, ov: LOr.OracleView,
                                        lookcdn: LCdn.cdns, ncap: int, nlook: int, nquant: int, th: AI.Thread) {
    var r := AI.FFindMatch(bodycode, str, AI.FInitState(bodycode, cp, AReg.init_regs(ncap), AReg.init_regs(nlook),
                                                        AReg.init_regs(nquant), 0, AI.cp_context(cp, str, LAnc.Forward)),
                           ov, LAnc.Forward, lookcdn).0;
    r.Some? && (CM.LookCpsOracleTrue(r.value.look_regs, ov) ==> CM.LookCpsOracleTrue(th.look_regs, ov))   // (G5b-3)
  }

  // =========================================================================
  // 2. A6: the two machines at a lookahead body.
  // =========================================================================


  // ===========================================================================
  // (G5b-1) The S forms: a lookahead row body that may hold a greedy CDN plus. Restored from `a8adac7^` on
  // `RF.StampBodiesLookFreeRE` (every stamp body look-free); machine B is `L3aCompositeCloseRecGCdn`.
  // ===========================================================================

  lemma TranslateCinOkS(r: R.regex, G: set<LG.GroupId>)
    requires T.TransWf(r) && NR.NestedFragmentCdnRE(r)
    requires RF.StampBodiesLookFreeRE(r)
    requires forall g: nat :: g in PIV.CapIdsOutsideLooks(r) ==> g in G
    ensures CW.CinOk(T.Translate(r), G)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => TranslateCinOkS(r1, G); TranslateCinOkS(r2, G);
    case Re_con(r1, r2) => TranslateCinOkS(r1, G); TranslateCinOkS(r2, G);
    case Re_capture(_, r1) => TranslateCinOkS(r1, G);
    case Re_lookaround(_, _, _) =>
    case Re_quant(nul, qid, q, body) =>
      TranslateCinOkS(body, G);
      var tb := T.Translate(body);
      assert T.Translate(r) == L.Quantified(q.greedy, q.min as nat, T.TrDelta(q), tb);
      if q.min > 0 && (CW.CinGreedyL(q.greedy, T.TrDelta(q), tb) || CW.CdnGreedyL(q.greedy, T.TrDelta(q), tb)) {
        CW.NulGreedyFacts(q.greedy, T.TrDelta(q), tb);   // greedy, Inf, the body is not NonNullable
        assert q.max == None;
        if nul == R.NonNullable {
          NUL.TransNonNullable(body);
          assert false;
        }
        // the body is look-free: `StampBodiesLookFreeRE`
        assert nul == R.CINullable || nul == R.CDNullable;
        assert NR.LookFreeRE(body);
        LookFreeLkBodies(body, {});
        PIV.DefGroupsCapIds(body);
        PIV.LookFreeCapIdsInLooksEmpty(body);
        PIV.CapIdsSplit(body);
        forall g | g in L.DefGroups(tb) ensures g in G {
          assert g in PIV.CapIds(body);
          assert g in PIV.CapIdsOutsideLooks(r);
        }
        CW.CinArmFromOld(tb, G);   // (G4b-1) the old arm implies today's
      }
    case _ =>
  }
  /** (G5b-1) A6 on the S forms. */
  // ===========================================================================
  // (G5b-3, G4b-2) Machine B's entry when a stamp body may hold lookarounds: G4a's top-level lemmas (main-cin-lk
  // `CinLooks.dfy`), moved down to the rows.
  // ===========================================================================

  lemma CapFreeLooksLkBodies(r: R.regex, S: set<LG.GroupId>)
    requires T.TransWf(r) && PIV.CapIdsInLooks(r) == {}
    ensures LL.LkBodiesInS(T.Translate(r), S)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => CapFreeLooksLkBodies(r1, S); CapFreeLooksLkBodies(r2, S);
    case Re_con(r1, r2) => CapFreeLooksLkBodies(r1, S); CapFreeLooksLkBodies(r2, S);
    case Re_quant(_, _, _, r1) => CapFreeLooksLkBodies(r1, S);
    case Re_capture(_, r1) => CapFreeLooksLkBodies(r1, S);
    case Re_lookaround(_, _, r1) =>
      PIV.DefGroupsCapIds(r1);
      assert PIV.CapIds(r1) == {};
      assert LL.DefGroupsIn(T.Translate(r1), S);
      reveal LL.LookBodyInS();
    case _ =>
  }

  /** (G4b-2) `TranslateCinOkS` for any stamp body: machine B's arm asks only that the body's out-of-look groups
      lie in `G` (its looks may capture). */
  lemma TranslateCinOkG4(r: R.regex, G: set<LG.GroupId>)
    requires T.TransWf(r) && NR.NestedFragmentCdnRE(r)
    requires forall g: nat :: g in PIV.CapIdsOutsideLooks(r) ==> g in G
    ensures CW.CinOk(T.Translate(r), G)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => TranslateCinOkG4(r1, G); TranslateCinOkG4(r2, G);
    case Re_con(r1, r2) => TranslateCinOkG4(r1, G); TranslateCinOkG4(r2, G);
    case Re_capture(_, r1) => TranslateCinOkG4(r1, G);
    case Re_lookaround(_, _, _) =>
    case Re_quant(nul, qid, q, body) =>
      TranslateCinOkG4(body, G);
      var tb := T.Translate(body);
      assert T.Translate(r) == L.Quantified(q.greedy, q.min as nat, T.TrDelta(q), tb);
      if q.min > 0 && (CW.CinGreedyL(q.greedy, T.TrDelta(q), tb) || CW.CdnGreedyL(q.greedy, T.TrDelta(q), tb)) {
        CW.NulGreedyFacts(q.greedy, T.TrDelta(q), tb);   // greedy, Inf, the body is not NonNullable
        assert q.max == None;
        if nul == R.NonNullable {
          NUL.TransNonNullable(body);
          assert false;
        }
        assert nul == R.CINullable || nul == R.CDNullable;
        OutLkTranslate(body);
        assert NPL.OutLk(tb) <= G;
      }
    case _ =>
  }

  /** (G4b-1) The translation's out-of-look groups are the out-of-look captures. */
  lemma OutLkTranslate(r: R.regex)
    requires T.TransWf(r)
    ensures forall g :: g in NPL.OutLk(T.Translate(r)) ==> g in PIV.CapIdsOutsideLooks(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => OutLkTranslate(r1); OutLkTranslate(r2);
    case Re_con(r1, r2) => OutLkTranslate(r1); OutLkTranslate(r2);
    case Re_quant(_, _, _, r1) => OutLkTranslate(r1);
    case Re_capture(_, r1) => OutLkTranslate(r1);
    case _ =>
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

  /** (G4b-1b) Machine B and machine A at a row's VM winner: B's carriers at the winner itself, the spec leaf
      outside `G`, machine A's readout outside `S`, and the winner's live stamps (what the transports read). Split out of
      `TwoMachinesAtS` so a lookbehind row can transport from its mirrored VM winner. */
  lemma TwoMachinesAtVMS(
    rer: LW.RegExpRecord, qm: AR.QMap, body: R.regex, bodycode: RB.code,
    endl: nat, ngroups: nat, crv: CP.FCompiled, str: string, cp: nat, ov: LOr.OracleView,
    lookcdn: LCdn.cdns, plus_bc: seq<RB.code>, ncap: int, nlook: int, nquant: int)
    returns (bleaf: Option<LT.Leaf>)
    requires PSM.StaticCoreCdnRE(qm, body, bodycode, endl)
    requires PSM.GuardsOkRun(qm, bodycode, lookcdn, ov, str)   // (G5b-1) N1 at the row, from the caller
    requires PSM.SizesOkRE(body, ncap, nlook, nquant)
    requires forall l: nat :: l in LTB.LookIds(body) ==> l < nlook
    requires qm.ov == ov && !rer.multiline && !rer.ignoreCase
    requires cp <= |str|
    requires bodycode == CP.compile_to_bytecode(body)
    requires LL.OracleOkSuffix(rer, qm, PIV.InpOfCp(str, cp))
    requires |ov| == |str| + 1
    requires OE.OracleColsOk(rer, qm, str)
    requires GateStaticsOkNested(qm, body, crv, ncap, nlook, nquant)
    requires LTB.LookUnique(body)
    requires LTB.LookTablesOk(body, crv)
    // (G3a) the CIN fragment at this body
    requires NRC.CdnTopRE(body) && NRR.PlusTableOkS(body, plus_bc)
    requires CW.CinOk(T.Translate(body), PIV.CapIdsOutsideLooks(body))
    ensures
      var inp := PIV.InpOfCp(str, cp);
      var t := LFU.ComputeTr(rer, [LS.Areg(T.Translate(body))], inp, LG.Empty, WP.Forward);
      var vms := AI.FInitState(bodycode, cp, AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant), 0,
                               AI.cp_context(cp, str, LAnc.Forward));
      var result := AI.FFindMatch(bodycode, str, vms, ov, LAnc.Forward, lookcdn).0;
      BestTieLkNestedTop(rer, body, crv, str, ov, PIV.CapIdsInLooks(body), bleaf, result, ncap, nlook, nquant)
      && (result.Some? <==> LT.FirstLeaf(t, inp).Some?)
      && (bleaf.Some? <==> LT.FirstLeaf(t, inp).Some?)
      && (result.Some? ==>
            bleaf.Some? && LT.FirstLeaf(t, inp).Some?
            && LL.GmAgreeOutside(bleaf.value.1, LT.FirstLeaf(t, inp).value.1, PIV.CapIdsOutsideLooks(body))
            && LL.GmAgreeOutside(PIV.GmOfLiveR(body, qm, str, result.value.capture_regs, result.value.look_regs,
                                               result.value.quant_regs),
                                 LT.FirstLeaf(t, inp).value.1, PIV.CapIdsInLooks(body))
            && PSM.BestLiveRE(body, result.value) && PSM.StampPathOk(qm, str, result.value.quant_regs.a_cp))
  {
    hide ClkFrameG4;   // (G5b-3) passed on as terms: their quantifiers stay out of every batch

    var inp := PIV.InpOfCp(str, cp);
    var acts := [LS.Areg(T.Translate(body))];
    var S := PIV.CapIdsInLooks(body);
    var G: set<LG.GroupId> := PIV.CapIdsOutsideLooks(body);

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
    // ---- the CHECKED tree (machine A's, shared with B) ---------------------
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
    var fmres := AI.FFindMatch(bodycode, str, vms, ov, LAnc.Forward, lookcdn);
    var result := fmres.0;

    assert {:split_here} true;
    // ---- machine B on the engine-shaped walk, agreeing with the spec leaf outside G ----
    PIV.CapIdsLooksDisjoint(body);
    assert G * S == {};
    bleaf := L3aCompositeCloseRecGCdn(rer, qm, body, bodycode, endl, ngroups, crv, str, ov, S, tstar, t, inp,
                                       vms, lookcdn, result, ncap, nlook, nquant, G);

    assert {:split_here} true;
    // ---- machine A: the VM's best is the checked tree's first leaf ----------
    var pts0 := PT.PikeTreeInitialState(tstar, inp);
    var bestT := PSM.FindMatchSimRECdn(rer, qm, body, bodycode, endl, ngroups, str, pts0, vms,
                                          ov, LAnc.Forward, lookcdn, ncap, nlook, nquant);
    M.TrcREToLinden(pts0, PT.PTS_final(bestT));
    TREP.TreeRepPikeSubtree(qm, tstar, bodycode, 0, inp, false);
    PT.InitPiketreeInv(tstar, inp);
    CR.PikeTreeTrcCorrect(pts0, PT.PTS_final(bestT), LT.FirstLeaf(tstar, inp));
    assert bestT == LT.FirstLeaf(tstar, inp);
    assert PIV.BestMatchRE(body, qm, str, bestT, result);

    assert {:split_here} true;
    if result.Some? {
      var best := result.value;
      assert PSM.BestLiveRE(body, best) && PSM.StampPathOk(qm, str, best.quant_regs.a_cp);
      assert LT.FirstLeaf(t, inp).Some?;
      var leaf := LT.FirstLeaf(t, inp).value;
      assert bestT.Some?;
      assert PIV.ThreadTracksGm(body, qm, str, best, bestT.value.1);
      assert bestT.value.1 == PIV.GmOfLiveR(body, qm, str, best.capture_regs, best.look_regs, best.quant_regs)
        by { reveal PIV.TieGm; }
      assert LL.GmAgreeOutside(bestT.value.1, leaf.1, S);
      assert bleaf.Some? && LL.GmAgreeOutside(bleaf.value.1, leaf.1, G);
    } else {
      assert bleaf.None? && LT.FirstLeaf(t, inp).None?;
    }
  }

  lemma TwoMachinesAtS(
    rer: LW.RegExpRecord, qm: AR.QMap, body: R.regex, bodycode: RB.code,
    endl: nat, ngroups: nat, crv: CP.FCompiled, str: string, cp: nat, ov: LOr.OracleView,
    lookcdn: LCdn.cdns, plus_bc: seq<RB.code>, ncap: int, nlook: int, nquant: int)
    requires PSM.StaticCoreCdnRE(qm, body, bodycode, endl)
    requires PSM.GuardsOkRun(qm, bodycode, lookcdn, ov, str)   // (G5b-1) N1 at the row, from the caller
    requires PSM.SizesOkRE(body, ncap, nlook, nquant)
    requires forall l: nat :: l in LTB.LookIds(body) ==> l < nlook
    requires qm.ov == ov && !rer.multiline && !rer.ignoreCase
    requires cp <= |str|
    requires bodycode == CP.compile_to_bytecode(body)
    requires LL.OracleOkSuffix(rer, qm, PIV.InpOfCp(str, cp))
    requires |ov| == |str| + 1
    requires OE.OracleColsOk(rer, qm, str)
    requires GateStaticsOkNested(qm, body, crv, ncap, nlook, nquant)
    requires LTB.LookUnique(body)
    requires LTB.LookTablesOk(body, crv)
    // (G3a) the CIN fragment at this body
    requires NRC.CdnTopRE(body) && NRR.PlusTableOkS(body, plus_bc)
    requires CW.CinOk(T.Translate(body), PIV.CapIdsOutsideLooks(body))
    ensures
      var inp := PIV.InpOfCp(str, cp);
      var t := LFU.ComputeTr(rer, [LS.Areg(T.Translate(body))], inp, LG.Empty, WP.Forward);
      var rf := AI.FFindMatchPlus(bodycode, body, plus_bc, str, ov, LAnc.Forward, cp,
                                  AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant),
                                  0, lookcdn).0;
      (rf.Some? <==> LT.FirstLeaf(t, inp).Some?)
      && (rf.Some? ==>
            LT.FirstLeaf(t, inp).Some?
            && GmtTieOutside(body, rf.value, LT.FirstLeaf(t, inp).value.1, PIV.CapIdsInLooks(body))
            // (G4b-2) the row's winner keeps dead stamps' records: presence-premised converses, unguarded OkT
            && LookNestBackTTopP(body, crv, str, ov, PIV.CapIdsInLooks(body),
                                 LT.FirstLeaf(t, inp).value.1, rf.value, ncap, nlook, nquant)
            && LookNestBackTTopDeepP(rer, body, crv, str, ov, PIV.CapIdsInLooks(body),
                                     LT.FirstLeaf(t, inp).value.1, rf.value, ncap, nlook, nquant)
            && LookNestOkTTopU(body, PIV.CapIdsInLooks(body), LT.FirstLeaf(t, inp).value.1, rf.value)
            && LookNestOkTTop(body, PIV.CapIdsInLooks(body), LT.FirstLeaf(t, inp).value.1, rf.value)
            && CM.ThreadRegsWf(rf.value, ncap, nlook, nquant)
            && CM.LookClkSetWithCp(rf.value.look_regs)
            && CM.LookCpSetWithClk(rf.value.look_regs)
            && CM.LookCpsLE(rf.value.look_regs, |str|)
            // (G3a) the reconstruction keeps the VM winner's look bank
            && WinnerLookKept(bodycode, str, cp, ov, lookcdn, ncap, nlook, nquant, rf.value))
  {
    hide ClkFrameG4;   // (G5b-3) passed on as terms: their quantifiers stay out of every batch

    var inp := PIV.InpOfCp(str, cp);
    var S := PIV.CapIdsInLooks(body);
    var G: set<LG.GroupId> := PIV.CapIdsOutsideLooks(body);
    var t := LFU.ComputeTr(rer, [LS.Areg(T.Translate(body))], inp, LG.Empty, WP.Forward);
    var ctx := AI.cp_context(cp, str, LAnc.Forward);
    var capture := AReg.init_regs(ncap);
    var look := AReg.init_regs(nlook);
    var quant := AReg.init_regs(nquant);
    var vms := AI.FInitState(bodycode, cp, capture, look, quant, 0, ctx);
    assert ctx.nextchar == AI.get_char(str, cp);
    var fmres := AI.FFindMatch(bodycode, str, vms, ov, LAnc.Forward, lookcdn);
    var result := fmres.0;
    // (G4b-1b) machines B and A at the VM winner
    var bleaf := TwoMachinesAtVMS(rer, qm, body, bodycode, endl, ngroups, crv, str, cp, ov, lookcdn, plus_bc,
                                  ncap, nlook, nquant);
    PIV.CapIdsLooksDisjoint(body);
    assert G * S == {};

    assert {:split_here} true;
    var rf := AI.FFindMatchPlus(bodycode, body, plus_bc, str, ov, LAnc.Forward, cp,
                                capture, look, quant, 0, lookcdn);
    assert rf.0 == (match result
                    case None => None
                    case Some(thread) =>
                      Some(AI.FReconstructPlus(thread, body, plus_bc, str, fmres.1, LAnc.Forward).0));
    if result.Some? {
      var best := result.value;
      assert PSM.BestLiveRE(body, best) && PSM.StampPathOk(qm, str, best.quant_regs.a_cp);
      SizesCoverFromOk(body, ncap, nlook, nquant);
      var rp := ReadoutAtWinnerAtS(qm, body, bodycode, endl, plus_bc, str, cp, ov, lookcdn, vms,
                                  ncap, nlook, nquant, result);
      assert fmres.1 == ov;
      assert rf.0 == Some(rp);

      assert {:split_here} true;
      // ---- the tie at (spec leaf, rp) ----------------------------------------
      assert LT.FirstLeaf(t, inp).Some?;
      var leaf := LT.FirstLeaf(t, inp).value;
      assert LL.GmAgreeOutside(PIV.GmOfLiveR(body, qm, str, best.capture_regs, best.look_regs, best.quant_regs),
                               leaf.1, S);
      assert PIV.GmOfLive(body, rp.capture_regs, rp.look_regs, rp.quant_regs)
             == PIV.GmOfLiveR(body, qm, str, best.capture_regs, best.look_regs, best.quant_regs);
      assert GmtTieOutside(body, rp, leaf.1, S);
      assert bleaf.Some? && LL.GmAgreeOutside(bleaf.value.1, leaf.1, G);
      // (G4b-2) the four-case transports, at the winner itself (rows keep the stamps)
      var Q := ELk.StampSet(best.quant_regs.a_cp);
      assert BestTieLkNestedTop(rer, body, crv, str, ov, S, bleaf, result, ncap, nlook, nquant);
      assert FrozenOk(rer, body, str, bleaf.value.1, best) && LookNestOkTTop(body, S, bleaf.value.1, best)
             && LookNestBackTTop(body, crv, str, ov, S, bleaf.value.1, best, ncap, nlook, nquant)
             && LookNestBackTTopDeep(rer, body, crv, str, ov, S, bleaf.value.1, best, ncap, nlook, nquant);
      assert LR.WinnerLookRec(qm, body, str, best, rp) && ClkFrameG4(body, Q, rp, best);
      EL.TranslateFragmentPikeLkRecCdn(body);
      T4.OracleEverywhere(rer, qm, str);
      T4.TieOkTTransportG4b2(rer, qm, body, str, Q, S, G, bleaf.value.1, leaf.1, best, rp, rp);
      OkTUToGuarded(body, S, leaf.1, rp);
      assert {:split_here} true;
      T4.TieConvTransportG4b2P(rer, qm, body, crv, str, ov, Q, S, G, bleaf.value.1, leaf.1, best, rp, rp,
                               ncap, nlook, nquant);

      assert {:split_here} true;
      // ---- fresh-run look-bank invariants on the winner; (G5b-3) rp keeps each of them ----
      RL.AInitLaws(nlook);
      assert CM.VmLookClkSet(vms) by {
        assert AI.init_thread(capture, look, quant).look_regs == look;
        forall l: int | AI.get_idx(look.a_cp, l) >= 0 ensures AI.get_idx(look.a_clk, l) >= 0 {
          if 0 <= l < |look.a_cp| { assert look.a_cp[l] == -1; }
        }
      }
      CM.FFindMatchLookClkSet(bodycode, str, vms, ov, LAnc.Forward, lookcdn);
      assert CM.VmLookCpSet(vms) by {
        forall l: int | AI.get_idx(look.a_clk, l) >= 0 ensures AI.get_idx(look.a_cp, l) >= 0 {
          if 0 <= l < |look.a_clk| { assert look.a_clk[l] == -1; }
        }
      }
      CM.FFindMatchLookCpSet(bodycode, str, vms, ov, LAnc.Forward, lookcdn);
      assert CM.VmLookCpOk(vms, |str|) by {
        forall l: int ensures AI.get_idx(look.a_cp, l) <= |str| {
          if 0 <= l < |look.a_cp| { assert look.a_cp[l] == -1; }
        }
      }
      CM.FFindMatchLookCpOk(bodycode, str, vms, ov, LAnc.Forward, lookcdn);
      assert {:split_here} true;
      assert CM.LookCpsOracleTrue(result.value.look_regs, ov) ==> CM.LookCpsOracleTrue(rp.look_regs, ov);
      assert WinnerLookKept(bodycode, str, cp, ov, lookcdn, ncap, nlook, nquant, rp) by {
        hide *;
        reveal WinnerLookKept();
      }
    } else {
      assert rf.0.None?;
      assert bleaf.None? && LT.FirstLeaf(t, inp).None?;
    }
  }}
