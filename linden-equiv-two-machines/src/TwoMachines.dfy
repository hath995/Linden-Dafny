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
  import opened LindenElkMachineA

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

  lemma TieOkTTransport(re: R.regex, Q: set<int>, S: set<LG.GroupId>, G: set<LG.GroupId>,
                        gmB: LG.GroupMap, gm: LG.GroupMap, best: AI.Thread, th: AI.Thread)
    requires RF.CinBodiesLookFreeRE(re) && PIV.CapUnique(re) && PIV.QuantUnique(re) && RF.QInCin(re, Q)
    requires G * S == {} && LL.GmAgreeOutside(gmB, gm, G)
    requires ClkFrame(re, Q, th, best)
    requires LookNestOkTTop(re, S, gmB, best)
    ensures LookNestOkTTop(re, S, gm, th)
  {
    forall lid: nat | lid in NI.TopLookIds(re)
                      && (lid in LTB.LookIds(re)
                          && exists g: LG.GroupId :: g in S && g in gm && g in PIV.CapIds(NI.LookBodyOfRE(re, lid)))
      ensures NI.LookPathPresent(re, th.capture_regs.a_clk, th.quant_regs.a_clk, -1, lid)
              && AI.get_idx(th.look_regs.a_clk, lid as int) >= 0
              && AI.get_idx(th.look_regs.a_clk, lid as int) >= NI.MxAtLidLk(re, th.quant_regs.a_clk, -1, lid)
    {
      var g: LG.GroupId :| g in S && g in gm && g in PIV.CapIds(NI.LookBodyOfRE(re, lid));
      assert g !in G by { if g in G { assert g in G * S; } }
      assert g in gmB;
      assert exists g0: LG.GroupId :: g0 in S && g0 in gmB && g0 in PIV.CapIds(NI.LookBodyOfRE(re, lid));
      assert NI.LookPathPresent(re, best.capture_regs.a_clk, best.quant_regs.a_clk, -1, lid)
             && AI.get_idx(best.look_regs.a_clk, lid as int) >= 0
             && AI.get_idx(best.look_regs.a_clk, lid as int) >= NI.MxAtLidLk(re, best.quant_regs.a_clk, -1, lid);
      AncFrame(re, Q, th, best, lid);
    }
  }

  lemma TieBackTransport(re: R.regex, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
                         Q: set<int>, S: set<LG.GroupId>, G: set<LG.GroupId>,
                         gmB: LG.GroupMap, gm: LG.GroupMap, best: AI.Thread, th: AI.Thread,
                         ncap: int, nlook: int, nquant: int)
    requires RF.CinBodiesLookFreeRE(re) && PIV.CapUnique(re) && PIV.QuantUnique(re) && RF.QInCin(re, Q)
    requires G * S == {} && LL.GmAgreeOutside(gmB, gm, G)
    requires ClkFrame(re, Q, th, best)
    requires LookNestBackTTop(re, crv, str, ov, S, gmB, best, ncap, nlook, nquant)
    ensures LookNestBackTTop(re, crv, str, ov, S, gm, th, ncap, nlook, nquant)
  {
    forall lid: nat | lid in NI.TopLookIds(re)
                      && (M.MatchedPosLA(crv, th.look_regs, lid as int)
                          && lid in LTB.LookIds(re)
                          && NI.LookPathDom(re, AI.get_idx(th.look_regs.a_clk, lid as int), th.quant_regs.a_clk, lid))
      ensures var rf := M.FreshBodyMatchPlus(crv, str, lid as int, th.look_regs, ov, ncap, nlook, nquant);
              rf.Some? ==>
                forall g: LG.GroupId ::
                  g in S && g in PIV.CapIds(NI.LookBodyOfRE(re, lid))
                  && g in PIV.GmOfLive(NI.LookBodyOfRE(re, lid), rf.value.capture_regs,
                                       rf.value.look_regs, rf.value.quant_regs)
                  ==> g in gm
    {
      AncFrame(re, Q, th, best, lid);
      var rf := M.FreshBodyMatchPlus(crv, str, lid as int, th.look_regs, ov, ncap, nlook, nquant);
      if rf.Some? {
        forall g: LG.GroupId | g in S && g in PIV.CapIds(NI.LookBodyOfRE(re, lid))
                               && g in PIV.GmOfLive(NI.LookBodyOfRE(re, lid), rf.value.capture_regs,
                                                    rf.value.look_regs, rf.value.quant_regs)
          ensures g in gm
        {
          assert g !in G by { if g in G { assert g in G * S; } }
          assert g in gmB;
        }
      }
    }
  }

  lemma TieDeepTransport(rer: LW.RegExpRecord, re: R.regex, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
                         Q: set<int>, S: set<LG.GroupId>, G: set<LG.GroupId>,
                         gmB: LG.GroupMap, gm: LG.GroupMap, best: AI.Thread, th: AI.Thread,
                         ncap: int, nlook: int, nquant: int)
    requires RF.CinBodiesLookFreeRE(re) && PIV.CapUnique(re) && PIV.QuantUnique(re) && RF.QInCin(re, Q)
    requires G * S == {} && LL.GmAgreeOutside(gmB, gm, G)
    requires ClkFrame(re, Q, th, best)
    requires LookNestBackTTopDeep(rer, re, crv, str, ov, S, gmB, best, ncap, nlook, nquant)
    ensures LookNestBackTTopDeep(rer, re, crv, str, ov, S, gm, th, ncap, nlook, nquant)
  {
    forall lid: nat | lid in NI.TopLookIds(re)
                      && (M.MatchedPosLA(crv, th.look_regs, lid as int)
                          && lid in LTB.LookIds(re)
                          && NI.LookPathDom(re, AI.get_idx(th.look_regs.a_clk, lid as int), th.quant_regs.a_clk, lid))
      ensures var lsub := SubFirstLeafAt(rer, crv, str, lid as int, th.look_regs);
              lsub.Some? ==>
                forall g: LG.GroupId ::
                  g in S && g in PIV.CapIds(NI.LookBodyOfRE(re, lid)) ==>
                    (g in lsub.value ==> g in gm && gm[g] == lsub.value[g])
                    && (g in gm ==> g in lsub.value)
    {
      AncFrame(re, Q, th, best, lid);
      var lsub := SubFirstLeafAt(rer, crv, str, lid as int, th.look_regs);
      if lsub.Some? {
        forall g: LG.GroupId | g in S && g in PIV.CapIds(NI.LookBodyOfRE(re, lid))
          ensures (g in lsub.value ==> g in gm && gm[g] == lsub.value[g])
                  && (g in gm ==> g in lsub.value)
        {
          assert g !in G by { if g in G { assert g in G * S; } }
          assert (g in gmB <==> g in gm) && (g in gmB ==> gmB[g] == gm[g]);
        }
      }
    }
  }
  /** THE TRANSPORT. */
  lemma TieTransport(rer: LW.RegExpRecord, re: R.regex, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
                     Q: set<int>, S: set<LG.GroupId>, G: set<LG.GroupId>,
                     bleaf: LT.Leaf, leaf: LT.Leaf, best: AI.Thread, th: AI.Thread,
                     ncap: int, nlook: int, nquant: int)
    requires RF.CinBodiesLookFreeRE(re) && PIV.CapUnique(re) && PIV.QuantUnique(re) && RF.QInCin(re, Q)
    requires G * S == {} && LL.GmAgreeOutside(bleaf.1, leaf.1, G)
    requires ClkFrame(re, Q, th, best)
    requires BestTieLkNestedTop(rer, re, crv, str, ov, S, Some(bleaf), Some(best), ncap, nlook, nquant)
    requires GmtTieOutside(re, th, leaf.1, S)   // machine A
    ensures BestTieLkNestedTop(rer, re, crv, str, ov, S, Some(leaf), Some(th), ncap, nlook, nquant)
  {
    TieOkTTransport(re, Q, S, G, bleaf.1, leaf.1, best, th);
    TieBackTransport(re, crv, str, ov, Q, S, G, bleaf.1, leaf.1, best, th, ncap, nlook, nquant);
    TieDeepTransport(rer, re, crv, str, ov, Q, S, G, bleaf.1, leaf.1, best, th, ncap, nlook, nquant);
  }

  /** (G3a) The fresh VM run of `bodycode` at `cp` has a winner, and `th` carries its look bank. Opaque: it
      names `FFindMatch` on a fresh initial state, which the solver would otherwise unfold at every use. */
  opaque ghost predicate WinnerLookKept(bodycode: RB.code, str: string, cp: nat, ov: LOr.OracleView,
                                        lookcdn: LCdn.cdns, ncap: int, nlook: int, nquant: int, th: AI.Thread) {
    var r := AI.FFindMatch(bodycode, str, AI.FInitState(bodycode, cp, AReg.init_regs(ncap), AReg.init_regs(nlook),
                                                        AReg.init_regs(nquant), 0, AI.cp_context(cp, str, LAnc.Forward)),
                           ov, LAnc.Forward, lookcdn).0;
    r.Some? && th.look_regs == r.value.look_regs
  }

  // =========================================================================
  // 2. A6: the two machines at a lookahead body.
  // =========================================================================

  /** A6. `LookNestBackTFromBodyReplay` without `NoNulledPlusRE(body)`: the fresh PLUS match of a
      lookahead body at `cp` against the spec tree's first leaf. Machine B (`L3aCompositeCloseRecG`,
      the engine-shaped walk) ties the VM winner to a leaf agreeing with the spec leaf outside
      `G := CapIdsOutsideLooks(body)`; machine A + the readout (A3) tie the RECONSTRUCTED winner to
      the checked tree's leaf; `TieTransport` moves B's carriers onto (spec leaf, reconstructed winner). */
  lemma TwoMachinesAt(
    rer: LW.RegExpRecord, qm: AR.QMap, body: R.regex, bodycode: RB.code,
    endl: nat, ngroups: nat, crv: CP.FCompiled, str: string, cp: nat, ov: LOr.OracleView,
    lookcdn: LCdn.cdns, plus_bc: seq<RB.code>, ncap: int, nlook: int, nquant: int)
    requires PSM.StaticCoreNestedRE(qm, body, bodycode, endl)
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
    requires NRC.NoCdnPlusRE(body) && NRR.PlusTableOk(body, plus_bc)
    requires RF.CinBodiesLookFreeRE(body)
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
            && LookNestBackTTop(body, crv, str, ov, PIV.CapIdsInLooks(body),
                                LT.FirstLeaf(t, inp).value.1, rf.value, ncap, nlook, nquant)
            && LookNestBackTTopDeep(rer, body, crv, str, ov, PIV.CapIdsInLooks(body),
                                    LT.FirstLeaf(t, inp).value.1, rf.value, ncap, nlook, nquant)
            && LookNestOkTTop(body, PIV.CapIdsInLooks(body), LT.FirstLeaf(t, inp).value.1, rf.value)
            && CM.ThreadRegsWf(rf.value, ncap, nlook, nquant)
            && CM.LookClkSetWithCp(rf.value.look_regs)
            && CM.LookCpSetWithClk(rf.value.look_regs)
            && CM.LookCpsLE(rf.value.look_regs, |str|)
            // (G3a) the reconstruction keeps the VM winner's look bank
            && WinnerLookKept(bodycode, str, cp, ov, lookcdn, ncap, nlook, nquant, rf.value))
  {
    var inp := PIV.InpOfCp(str, cp);
    var acts := [LS.Areg(T.Translate(body))];
    var S := PIV.CapIdsInLooks(body);
    var G: set<LG.GroupId> := PIV.CapIdsOutsideLooks(body);

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
    // ---- the CHECKED tree (machine A's, shared with B) ---------------------
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
    var fmres := AI.FFindMatch(bodycode, str, vms, ov, LAnc.Forward, lookcdn);
    var result := fmres.0;

    assert {:split_here} true;
    // ---- machine B on the engine-shaped walk, agreeing with the spec leaf outside G ----
    PIV.CapIdsLooksDisjoint(body);
    assert G * S == {};
    var bleaf := L3aCompositeCloseRecG(rer, qm, body, bodycode, endl, ngroups, crv, str, ov, S, tstar, t, inp,
                                       vms, lookcdn, result, ncap, nlook, nquant, G);

    assert {:split_here} true;
    // ---- machine A: the VM's best is the checked tree's first leaf ----------
    var pts0 := PT.PikeTreeInitialState(tstar, inp);
    PSM.GuardsOkRunStaticNested(qm, body, bodycode, endl, lookcdn, ov, str);   // (G5a step 2) no guard in this code
    var bestT := PSM.FindMatchSimRENested(rer, qm, body, bodycode, endl, ngroups, str, pts0, vms,
                                          ov, LAnc.Forward, lookcdn, ncap, nlook, nquant);
    M.TrcREToLinden(pts0, PT.PTS_final(bestT));
    TREP.TreeRepPikeSubtree(qm, tstar, bodycode, 0, inp, false);
    PT.InitPiketreeInv(tstar, inp);
    CR.PikeTreeTrcCorrect(pts0, PT.PTS_final(bestT), LT.FirstLeaf(tstar, inp));
    assert bestT == LT.FirstLeaf(tstar, inp);
    assert PIV.BestMatchRE(body, qm, str, bestT, result);

    assert {:split_here} true;
    var rf := AI.FFindMatchPlus(bodycode, body, plus_bc, str, ov, LAnc.Forward, cp,
                                capture, look, quant, 0, lookcdn);
    assert rf.0 == (match result
                    case None => None
                    case Some(thread) =>
                      Some(AI.FReconstructPlus(thread, body, plus_bc, str, fmres.1, LAnc.Forward).0));
    if result.Some? {
      var best := result.value;
      assert PSM.BestLiveRE(body, best);
      SizesCoverFromOk(body, ncap, nlook, nquant);
      var rp := ReadoutAtWinnerAt(qm, body, bodycode, endl, plus_bc, str, cp, ov, lookcdn, vms,
                                  ncap, nlook, nquant, result);
      assert fmres.1 == ov;
      assert rf.0 == Some(rp);

      assert {:split_here} true;
      // ---- the tie at (spec leaf, rp) ----------------------------------------
      assert LT.FirstLeaf(t, inp).Some?;
      var leaf := LT.FirstLeaf(t, inp).value;
      assert bestT.Some?;
      assert PIV.ThreadTracksGm(body, qm, str, best, bestT.value.1);
      assert bestT.value.1 == PIV.GmOfLiveR(body, qm, str, best.capture_regs, best.look_regs, best.quant_regs)
        by { reveal PIV.TieGm; }
      assert PIV.GmOfLive(body, rp.capture_regs, rp.look_regs, rp.quant_regs) == bestT.value.1;
      assert LL.GmAgreeOutside(bestT.value.1, leaf.1, S);
      assert GmtTieOutside(body, rp, leaf.1, S);
      assert bleaf.Some? && LL.GmAgreeOutside(bleaf.value.1, leaf.1, G);
      QInCinQ(body);
      TieTransport(rer, body, crv, str, ov, FRD.CinQids(body), S, G, bleaf.value, leaf, best, rp,
                   ncap, nlook, nquant);
      assert BestTieLkNestedTop(rer, body, crv, str, ov, S, Some(leaf), Some(rp), ncap, nlook, nquant);

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
      assert rp.look_regs == result.value.look_regs;
      assert WinnerLookKept(bodycode, str, cp, ov, lookcdn, ncap, nlook, nquant, rp) by {
        hide *;
        reveal WinnerLookKept();
      }
    } else {
      assert rf.0.None?;
      assert bleaf.None? && LT.FirstLeaf(t, inp).None?;
    }
  }
}
