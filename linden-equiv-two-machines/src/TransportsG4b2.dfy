// (G4b-2) The four-case transports: machine B's carriers at (bleaf, best) become carriers at (the spec leaf,
// the reconstructed winner) when looks on the empty path of a nullable plus body CAPTURE. Per top lid `l` with
// a group in play: (A) `l` under a live stamp of `best` (machine B's guard set): `FrozenOk` (crossed by the
// frozen empty path, or its groups unset) + the replay's look record (`LR.WinnerLookRec`); (B) not guarded:
// B's guarded carrier applies; a stamped host of `l` is then dead, which kills presence
// (`LR.DeadStampKillsPresence`); otherwise the G4b-1 frame (`AncFrameAvoid`). Plan:
// `~/code/Linden-Dafny-scratch/work/g4b2/transport-plan.md` §1.
module LindenElkTransportsG4b2 {
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
  import SBk = LindenElkStampBank
  import opened LindenElkMachineA
  import LR = LindenElkLookRecord
  import SLS = LindenElkStampLookSite
  import NST = LindenElkNestStamp

  // (moved here from `LindenElkTwoMachines`, which imports this module)
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

  // ===========================================================================
  // 1. Body-level statics.
  // ===========================================================================

  lemma QidBodyStatics(re: R.regex, qm: AR.QMap, q: nat)
    requires T.TransWf(re) && AR.LmapOk(re, qm) && PIV.CapUnique(re) && LTB.LookUnique(re)
    requires q in PIV.QuantIds(re)
    ensures T.TransWf(PIV.QidBody(re, q)) && AR.LmapOk(PIV.QidBody(re, q), qm)
    ensures PIV.CapUnique(PIV.QidBody(re, q)) && LTB.LookUnique(PIV.QidBody(re, q))
    decreases re
  {
    SLS.CapUniqueQidBody(re, q);
    match re
    case Re_alt(r1, r2) => if q in PIV.QuantIds(r1) { QidBodyStatics(r1, qm, q); } else { QidBodyStatics(r2, qm, q); }
    case Re_con(r1, r2) => if q in PIV.QuantIds(r1) { QidBodyStatics(r1, qm, q); } else { QidBodyStatics(r2, qm, q); }
    case Re_quant(_, qid0, _, r1) => if !(qid0 >= 0 && (qid0 as nat) == q) { QidBodyStatics(r1, qm, q); }
    case Re_capture(_, r1) => QidBodyStatics(r1, qm, q);
    case Re_lookaround(_, _, r1) => QidBodyStatics(r1, qm, q);
  }

  /** A top lid of `re` inside a quantifier's body is a top lid of the body, with the same look body. */
  lemma TopLidBody(re: R.regex, q: nat, l: nat)
    requires LTB.LookUnique(re) && q in PIV.QuantIds(re)
    requires l in NI.TopLookIds(re) && l in LTB.LookIds(PIV.QidBody(re, q))
    ensures l in LTB.LookIds(re) && l in NI.TopLookIds(PIV.QidBody(re, q))
    ensures NI.LookBodyOfRE(re, l) == NI.LookBodyOfRE(PIV.QidBody(re, q), l)
    decreases re
  {
    NI.QidBodyLookIdsSub(re, q);
    match re
    case Re_alt(r1, r2) =>
      NI.TopLookIdsIn(r1); NI.TopLookIdsIn(r2);
      if q in PIV.QuantIds(r1) {
        NI.QidBodyLookIdsSub(r1, q);
        assert l !in NI.TopLookIds(r2) by { if l in NI.TopLookIds(r2) { assert l in LTB.LookIds(r1) * LTB.LookIds(r2); } }
        TopLidBody(r1, q, l);
      } else {
        NI.QidBodyLookIdsSub(r2, q);
        assert l !in NI.TopLookIds(r1) by { if l in NI.TopLookIds(r1) { assert l in LTB.LookIds(r1) * LTB.LookIds(r2); } }
        assert l !in LTB.LookIds(r1) by { if l in LTB.LookIds(r1) { assert l in LTB.LookIds(r1) * LTB.LookIds(r2); } }
        TopLidBody(r2, q, l);
      }
    case Re_con(r1, r2) =>
      NI.TopLookIdsIn(r1); NI.TopLookIdsIn(r2);
      if q in PIV.QuantIds(r1) {
        NI.QidBodyLookIdsSub(r1, q);
        assert l !in NI.TopLookIds(r2) by { if l in NI.TopLookIds(r2) { assert l in LTB.LookIds(r1) * LTB.LookIds(r2); } }
        TopLidBody(r1, q, l);
      } else {
        NI.QidBodyLookIdsSub(r2, q);
        assert l !in NI.TopLookIds(r1) by { if l in NI.TopLookIds(r1) { assert l in LTB.LookIds(r1) * LTB.LookIds(r2); } }
        assert l !in LTB.LookIds(r1) by { if l in LTB.LookIds(r1) { assert l in LTB.LookIds(r1) * LTB.LookIds(r2); } }
        TopLidBody(r2, q, l);
      }
    case Re_quant(_, qid0, _, r1) =>
      if !(qid0 >= 0 && (qid0 as nat) == q) { TopLidBody(r1, q, l); }
    case Re_capture(_, r1) => TopLidBody(r1, q, l);
    case Re_lookaround(lid0, _, r1) =>
      NI.QidBodyLookIdsSub(r1, q);
      assert l == lid0 as nat;
      assert false;   // LookUnique: the look's own id is not in its body
  }

  /** A look's body groups are among the regex's in-look groups. */
  lemma CapIdsLookBodyInLooks(r: R.regex, l: nat)
    requires l in LTB.LookIds(r)
    ensures PIV.CapIds(NI.LookBodyOfRE(r, l)) <= PIV.CapIdsInLooks(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => if l in LTB.LookIds(r1) { CapIdsLookBodyInLooks(r1, l); } else { CapIdsLookBodyInLooks(r2, l); }
    case Re_con(r1, r2) => if l in LTB.LookIds(r1) { CapIdsLookBodyInLooks(r1, l); } else { CapIdsLookBodyInLooks(r2, l); }
    case Re_quant(_, _, _, r1) => CapIdsLookBodyInLooks(r1, l);
    case Re_capture(_, r1) => CapIdsLookBodyInLooks(r1, l);
    case Re_lookaround(lid0, _, r1) =>
      if !(lid0 >= 0 && (lid0 as nat) == l) { SLS.CapIdsLookBodySub(r1, l); }
  }

  // ===========================================================================
  // 2. OkT at the winner (unguarded).
  // ===========================================================================

  /** Case (A) of OkT: a guarded lid with a group in the leaf is crossed by its live host's frozen path, so the
      replay recorded it at the host's position, present and fresh. */
  lemma OkTLiveLid(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, str: string, gmB: LG.GroupMap,
                   best: AI.Thread, rp: AI.Thread, l: nat, g: LG.GroupId)
    requires !rer.multiline && T.TransWf(re) && AR.LmapOk(re, qm) && AR.QmapOk(re, qm)
    requires PIV.CapUnique(re) && PIV.QuantUnique(re) && LTB.LookUnique(re)
    requires PSM.StampPathOk(qm, str, best.quant_regs.a_cp)
    requires forall cp: nat :: cp <= |str| ==> LL.OracleOkAt(rer, qm, PIV.InpOfCp(str, cp))
    requires FrozenOk(rer, re, str, gmB, best)
    requires LR.WinnerLookRec(qm, re, str, best, rp)
    requires l in LiveStampLids(re, best.quant_regs) && l in LTB.LookIds(re)
    requires g in gmB && g in PIV.CapIds(NI.LookBodyOfRE(re, l))
    ensures NI.LookPathPresent(re, rp.capture_regs.a_clk, rp.quant_regs.a_clk, -1, l)
            && AI.get_idx(rp.look_regs.a_clk, l as int) >= 0
            && AI.get_idx(rp.look_regs.a_clk, l as int) >= NI.MxAtLidLk(re, rp.quant_regs.a_clk, -1, l)
  {
    var q := LiveStampLidHost(re, best.quant_regs, l);
    var cp := AI.get_idx(best.quant_regs.a_cp, q as int);
    assert FrozenAtQ(rer, re, str, gmB, q, cp) && PIV.QChainFresh(re, best.quant_regs.a_clk, -1, q) by {
      reveal FrozenOk();
    }
    assert PIV.QLive(re, best.quant_regs.a_clk, best.quant_regs.a_cp, q);
    TopLidBody(re, q, l);
    var body := PIV.QidBody(re, q);
    LR.WinnerLookRecAt(qm, re, str, best, rp, q, l);
    var K := AI.get_idx(best.quant_regs.a_clk, q as int);
    SL.QChainFreshGe(re, best.quant_regs.a_clk, -1, q);
    assert K >= -1;
    var cq: nat := cp as nat;
    var inp := PIV.InpOfCp(str, cq);
    PSM.InpOfCpIsInputAt(str, cq);
    QidBodyStatics(re, qm, q);
    PIV.QmapOkBodyAtQid(re, qm, q);
    assert TREP.FirstEmptyPathR(qm, body, inp).Some? by {
      reveal PSM.StampPathOk();
      assert AI.get_idx(best.quant_regs.a_cp, q as int) == cq;
    }
    LR.PathLooksSteps(rer, qm, body, inp);
    var r1 := T.Translate(body);
    var p := NPL.FirstEmptyPathLkL(rer, r1, inp);
    // the frozen path crosses g: an uncrossed body-look group is unset in machine B's leaf
    CapIdsLookBodyInLooks(body, l);
    M.LkBodyGroupsEqCapIdsInLooks(body);
    assert g in LL.LkBodyGroups(r1);
    assert NPL.FrozenAt(rer, r1, inp, gmB);
    assert NPL.Crossed(p.value, g);
    assert l in LR.PathLooksR(qm, body, inp);
    assert LR.LookRecTop(re, LR.RgOf(best), LR.RgOf(rp), cp, K, l, true);
  }

  /** Case (B), the stamped half: a stamped host of an unguarded lid is dead, and a dead host kills presence. */
  lemma OkTDeadHost(re: R.regex, Q: set<int>, best: AI.Thread, l: nat)
    requires PIV.QuantUnique(re) && LTB.LookUnique(re)
    requires l in NI.TopLookIds(re) && l in LTB.LookIds(re)
    requires (l as int) in ELk.LooksQE(re, Q) && Q == ELk.StampSet(best.quant_regs.a_cp)
    requires l !in LiveStampLids(re, best.quant_regs)
    ensures !NI.LookPathPresent(re, best.capture_regs.a_clk, best.quant_regs.a_clk, -1, l)
  {
    var q := LR.LooksQEUnderStamp(re, Q, l);
    assert AI.get_idx(best.quant_regs.a_cp, q as int) >= 0;
    if ChainFresh(re, best.quant_regs, q) {
      assert LiveStampAt(re, best.quant_regs, q);
      assert LidUnderLiveStamp(re, best.quant_regs, l);
      assert l in LiveStampLids(re, best.quant_regs) by { reveal LiveStampLids(); }
      assert false;
    }
    LR.DeadStampKillsPresence(re, best.capture_regs.a_clk, best.quant_regs.a_clk, q, l);
  }

  /** OkT at the winner, UNGUARDED: the four cases per lid (no scope premise on the empty-path looks). */
  lemma TieOkTTransportG4b2(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, str: string, Q: set<int>,
                            S: set<LG.GroupId>, G: set<LG.GroupId>, gmB: LG.GroupMap, gm: LG.GroupMap,
                            best: AI.Thread, rp: AI.Thread, th: AI.Thread)
    requires !rer.multiline && T.TransWf(re) && AR.LmapOk(re, qm) && AR.QmapOk(re, qm)
    requires PIV.CapUnique(re) && PIV.QuantUnique(re) && LTB.LookUnique(re)
    requires PSM.BestLiveRE(re, best) && PSM.StampPathOk(qm, str, best.quant_regs.a_cp)
    requires Q == ELk.StampSet(best.quant_regs.a_cp)
    requires forall cp: nat :: cp <= |str| ==> LL.OracleOkAt(rer, qm, PIV.InpOfCp(str, cp))
    requires G * S == {} && LL.GmAgreeOutside(gmB, gm, G)
    requires ClkFrameG4(re, Q, th, best)
    requires LookNestOkTTop(re, S, gmB, best) && FrozenOk(rer, re, str, gmB, best)
    requires LR.WinnerLookRec(qm, re, str, best, rp)
    requires th.capture_regs == rp.capture_regs && th.look_regs == rp.look_regs
             && th.quant_regs.a_clk == rp.quant_regs.a_clk
    ensures LookNestOkTTopU(re, S, gm, th)
  {
    hide ClkFrameG4;
    ELk.BodyStaleAtStamps(re, best, Q);
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
      if lid in LiveStampLids(re, best.quant_regs) {
        assert {:split_here} true;   // (A) a live host: the replay's record
        OkTLiveLid(rer, qm, re, str, gmB, best, rp, lid, g);
      } else {
        assert {:split_here} true;   // (B) B's guarded carrier applies
        assert exists g0: LG.GroupId :: g0 in S && g0 in gmB && g0 in PIV.CapIds(NI.LookBodyOfRE(re, lid));
        assert NI.LookPathPresent(re, best.capture_regs.a_clk, best.quant_regs.a_clk, -1, lid)
               && AI.get_idx(best.look_regs.a_clk, lid as int) >= 0
               && AI.get_idx(best.look_regs.a_clk, lid as int) >= NI.MxAtLidLk(re, best.quant_regs.a_clk, -1, lid);
        if (lid as int) in ELk.LooksQE(re, Q) {
          OkTDeadHost(re, Q, best, lid);
          assert false;
        }
        reveal ClkFrameG4;
        if CLP.AncCapRegs(re, lid) * RF.CapsQ(re, Q) != {} || CLP.AncQuants(re, lid) * RF.QuantsQ(re, Q) != {} {
          ELk.StampedAncKillsPresence(re, best.capture_regs.a_clk, best.quant_regs.a_clk, -1, lid, Q);
          assert false;
        }
        AncFrameAvoid(re, Q, th, best, lid);
        assert AI.get_idx(th.look_regs.a_clk, lid as int) == AI.get_idx(best.look_regs.a_clk, lid as int);
      }
    }
  }

  // ===========================================================================
  // 3. Per-lid statics: the look tables, the look map, the body's fragment.
  // ===========================================================================

  lemma LookEntryAt(re: R.regex, crv: CP.FCompiled, l: nat)
    requires LTB.LookTablesOk(re, crv) && l in LTB.LookIds(re)
    ensures LTB.LookEntryOk(crv, l as int, LR.LookLaOfRE(re, l), NI.LookBodyOfRE(re, l))
    decreases re
  {
    match re
    case Re_alt(r1, r2) => if l in LTB.LookIds(r1) { LookEntryAt(r1, crv, l); } else { LookEntryAt(r2, crv, l); }
    case Re_con(r1, r2) => if l in LTB.LookIds(r1) { LookEntryAt(r1, crv, l); } else { LookEntryAt(r2, crv, l); }
    case Re_quant(_, _, _, r1) => LookEntryAt(r1, crv, l);
    case Re_capture(_, r1) => LookEntryAt(r1, crv, l);
    case Re_lookaround(lid0, _, r1) => if !(lid0 >= 0 && (lid0 as nat) == l) { LookEntryAt(r1, crv, l); }
  }

  lemma LmapOkLookAt(re: R.regex, qm: AR.QMap, l: nat)
    requires T.TransWf(re) && AR.LmapOk(re, qm) && l in LTB.LookIds(re)
    ensures (l as int) in qm.looks && T.TransWf(NI.LookBodyOfRE(re, l))
    ensures qm.looks[l as int] == (T.TrLookaround(LR.LookLaOfRE(re, l)), T.Translate(NI.LookBodyOfRE(re, l)))
    decreases re
  {
    LmapOkLookBodyTW(re, qm, l);
    match re
    case Re_alt(r1, r2) => if l in LTB.LookIds(r1) { LmapOkLookAt(r1, qm, l); } else { LmapOkLookAt(r2, qm, l); }
    case Re_con(r1, r2) => if l in LTB.LookIds(r1) { LmapOkLookAt(r1, qm, l); } else { LmapOkLookAt(r2, qm, l); }
    case Re_quant(_, _, _, r1) => LmapOkLookAt(r1, qm, l);
    case Re_capture(_, r1) => LmapOkLookAt(r1, qm, l);
    case Re_lookaround(lid0, _, r1) => if !(lid0 >= 0 && (lid0 as nat) == l) { LmapOkLookAt(r1, qm, l); }
  }

  /** The flavour of a top lid inside a quantifier's body is the body's. */
  lemma TopLidBodyLa(re: R.regex, q: nat, l: nat)
    requires LTB.LookUnique(re) && q in PIV.QuantIds(re)
    requires l in NI.TopLookIds(re) && l in LTB.LookIds(PIV.QidBody(re, q))
    ensures l in LTB.LookIds(re) && LR.LookLaOfRE(re, l) == LR.LookLaOfRE(PIV.QidBody(re, q), l)
    decreases re
  {
    NI.QidBodyLookIdsSub(re, q);
    match re
    case Re_alt(r1, r2) =>
      if q in PIV.QuantIds(r1) {
        NI.QidBodyLookIdsSub(r1, q); NI.TopLookIdsIn(r2);
        assert l !in NI.TopLookIds(r2) by { if l in NI.TopLookIds(r2) { assert l in LTB.LookIds(r1) * LTB.LookIds(r2); } }
        TopLidBodyLa(r1, q, l);
      } else {
        NI.QidBodyLookIdsSub(r2, q); NI.TopLookIdsIn(r1);
        assert l !in NI.TopLookIds(r1) by { if l in NI.TopLookIds(r1) { assert l in LTB.LookIds(r1) * LTB.LookIds(r2); } }
        assert l !in LTB.LookIds(r1) by { if l in LTB.LookIds(r1) { assert l in LTB.LookIds(r1) * LTB.LookIds(r2); } }
        TopLidBodyLa(r2, q, l);
      }
    case Re_con(r1, r2) =>
      if q in PIV.QuantIds(r1) {
        NI.QidBodyLookIdsSub(r1, q); NI.TopLookIdsIn(r2);
        assert l !in NI.TopLookIds(r2) by { if l in NI.TopLookIds(r2) { assert l in LTB.LookIds(r1) * LTB.LookIds(r2); } }
        TopLidBodyLa(r1, q, l);
      } else {
        NI.QidBodyLookIdsSub(r2, q); NI.TopLookIdsIn(r1);
        assert l !in NI.TopLookIds(r1) by { if l in NI.TopLookIds(r1) { assert l in LTB.LookIds(r1) * LTB.LookIds(r2); } }
        assert l !in LTB.LookIds(r1) by { if l in LTB.LookIds(r1) { assert l in LTB.LookIds(r1) * LTB.LookIds(r2); } }
        TopLidBodyLa(r2, q, l);
      }
    case Re_quant(_, qid0, _, r1) => if !(qid0 >= 0 && (qid0 as nat) == q) { TopLidBodyLa(r1, q, l); }
    case Re_capture(_, r1) => TopLidBodyLa(r1, q, l);
    case Re_lookaround(lid0, _, r1) =>
      NI.QidBodyLookIdsSub(r1, q);
      assert l == lid0 as nat;
      assert false;
  }

  /** The fragment descends to a quantifier's body. */
  lemma PikeLkQidBody(re: R.regex, q: nat)
    requires T.TransWf(re) && EL.PikeLkRegexRec(T.Translate(re)) && q in PIV.QuantIds(re)
    ensures T.TransWf(PIV.QidBody(re, q)) && EL.PikeLkRegexRec(T.Translate(PIV.QidBody(re, q)))
    decreases re
  {
    M.TransWfQidBody(re, q);
    match re
    case Re_alt(r1, r2) => if q in PIV.QuantIds(r1) { PikeLkQidBody(r1, q); } else { PikeLkQidBody(r2, q); }
    case Re_con(r1, r2) => if q in PIV.QuantIds(r1) { PikeLkQidBody(r1, q); } else { PikeLkQidBody(r2, q); }
    case Re_quant(_, qid0, _, r1) => if !(qid0 >= 0 && (qid0 as nat) == q) { PikeLkQidBody(r1, q); }
    case Re_capture(_, r1) => PikeLkQidBody(r1, q);
    case Re_lookaround(_, _, r1) => PikeLkQidBody(r1, q);
  }

  // ===========================================================================
  // 4. The converse carriers at one lid.
  // ===========================================================================

  ghost predicate DeepAt(rer: LW.RegExpRecord, re: R.regex, crv: CP.FCompiled, str: string, S: set<LG.GroupId>,
                         gm: LG.GroupMap, th: AI.Thread, lid: nat)
    requires lid in LTB.LookIds(re)
  {
    var lsub := SubFirstLeafAt(rer, crv, str, lid as int, th.look_regs);
    lsub.Some? ==>
      forall g: LG.GroupId ::
        g in S && g in PIV.CapIds(NI.LookBodyOfRE(re, lid)) ==>
          (g in lsub.value ==> g in gm && gm[g] == lsub.value[g])
          && (g in gm ==> g in lsub.value)
  }

  ghost predicate BackAt(re: R.regex, crv: CP.FCompiled, str: string, ov: LOr.OracleView, S: set<LG.GroupId>,
                         gm: LG.GroupMap, th: AI.Thread, lid: nat, ncap: int, nlook: int, nquant: int)
    requires lid in LTB.LookIds(re)
  {
    var rf := M.FreshBodyMatchPlus(crv, str, lid as int, th.look_regs, ov, ncap, nlook, nquant);
    rf.Some? ==>
      forall g: LG.GroupId ::
        g in S && g in PIV.CapIds(NI.LookBodyOfRE(re, lid))
        && g in PIV.GmOfLive(NI.LookBodyOfRE(re, lid), rf.value.capture_regs, rf.value.look_regs, rf.value.quant_regs)
        ==> g in gm
  }

  /** Case (a): a lid on its live host's frozen path whose winner record sits at the host's position. The frozen
      leaf there is the look body's leaf from `Empty`: Deep by the virtual gate pass (`DeepGateReqFromCrossing`),
      the converse by the gate's landing at `Empty` (`LookGateLanding`). */
  lemma CrossedLidCarriers(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, crv: CP.FCompiled, str: string,
                           ov: LOr.OracleView, S: set<LG.GroupId>, gmB: LG.GroupMap, th: AI.Thread,
                           q: nat, cp: nat, l: nat, ncap: int, nlook: int, nquant: int)
    requires T.TransWf(re) && AR.LmapOk(re, qm) && EL.PikeLkRegexRec(T.Translate(re))
    requires PIV.CapUnique(re) && PIV.QuantUnique(re) && LTB.LookUnique(re)
    requires qm.ov == ov && !rer.multiline && !rer.ignoreCase && |ov| == |str| + 1 && OE.OracleColsOk(rer, qm, str)
    requires S == PIV.CapIdsInLooks(re)
    requires GateStaticsOkNested(qm, re, crv, ncap, nlook, nquant) && LTB.LookTablesOk(re, crv)
    requires cp <= |str| && LL.OracleOkAt(rer, qm, PIV.InpOfCp(str, cp)) && LL.OracleOkSuffix(rer, qm, PIV.InpOfCp(str, cp))
    requires q in PIV.QuantIds(re) && FrozenAtQ(rer, re, str, gmB, q, cp as int)
    requires TREP.FirstEmptyPathR(qm, PIV.QidBody(re, q), PIV.InpOfCp(str, cp)).Some?
    requires l in NI.TopLookIds(re) && l in LTB.LookIds(PIV.QidBody(re, q))
    requires l in LR.PathLooksR(qm, PIV.QidBody(re, q), T.InputAt(str, cp))
    requires AReg.get_cp(th.look_regs, l as int) == Some(cp as int)
    ensures l in LTB.LookIds(re)
    ensures DeepAt(rer, re, crv, str, S, gmB, th, l)
    ensures BackAt(re, crv, str, ov, S, gmB, th, l, ncap, nlook, nquant)
  {
    TopLidBody(re, q, l);
    TopLidBodyLa(re, q, l);
    QidBodyStatics(re, qm, q);
    PikeLkQidBody(re, q);
    var bq := PIV.QidBody(re, q);
    var inp := PIV.InpOfCp(str, cp);
    PSM.InpOfCpIsInputAt(str, cp);
    LR.PathLooksSteps(rer, qm, bq, inp);
    var R1 := T.Translate(bq);
    var p := NPL.FirstEmptyPathLkL(rer, R1, inp);
    var la := LR.LookLaOfRE(re, l);
    var body := NI.LookBodyOfRE(re, l);
    LmapOkLookBodyTW(re, qm, l);
    var lk := T.TrLookaround(la);
    var r1 := T.Translate(body);
    assert NRC.PositiveLk(la) && LR.LkStepOf(bq, l) in p.value;
    assert LR.LkStepOf(bq, l) == NPL.LkS(lk, r1);
    var i :| 0 <= i < |p.value| && p.value[i] == NPL.LkS(lk, r1);
    assert L.Positivity(lk) && AR.PositiveL(lk);
    // the frozen leaf at the crossing, and the look's verdict there
    assert NPL.FrozenAt(rer, R1, inp, gmB);
    assert LL.GmAgreeInside(gmB, NPL.BodyLeafE(rer, lk, r1, inp), NPL.DG(r1));
    NPL.StepsOkL(rer, R1, inp);
    assert NP.LkVerdictL(rer, lk, r1, inp) && EL.PikeLkRegexRec(r1);
    var tlk := LFU.ComputeTr(rer, [LS.Areg(r1)], inp, LG.Empty, L.LkDir(lk));
    var res := LS.LkResult(lk, tlk, LG.Empty, inp);
    assert res.Some? && NPL.BodyLeafE(rer, lk, r1, inp) == res.value;
    M.TranslateDefGroupsEqCapIds(body);
    // the tables at l
    LookEntryAt(re, crv, l);
    LmapOkLookAt(re, qm, l);
    assert crv.f_look_types[l as int] == la && crv.f_look_ast[l as int] == body;
    assert body == M.VBody(crv, l as int) && L.LkDir(lk) == LidDir(crv, l as int);
    LmapOkLookBodyTW(re, qm, l);
    assert {:split_here} true;
    // Deep: the virtual gate pass at `Empty`
    DeepGateReqFromCrossing(rer, re, crv, str, ov, S, LG.Empty, res.value, lk, r1, tlk, th, l as int, cp, body,
                            ncap, nlook, nquant);
    assert DeepAt(rer, re, crv, str, S, gmB, th, l) by {
      var lsub := SubFirstLeafAt(rer, crv, str, l as int, th.look_regs);
      if lsub.Some? {
        forall g: LG.GroupId | g in S && g in PIV.CapIds(body)
          ensures (g in lsub.value ==> g in gmB && gmB[g] == lsub.value[g]) && (g in gmB ==> g in lsub.value)
        {
          assert g in NPL.DG(r1);
          assert (g in gmB <==> g in res.value) && (g in gmB ==> gmB[g] == res.value[g]);
        }
      }
    }
    assert {:split_here} true;
    // the converse: the gate's landing at `Empty`
    assert qm.looks[l as int] == (lk, r1);
    LookGateLanding(rer, qm, re, crv, str, ov, S, l as int, cp, th.look_regs, LG.Empty, ncap, nlook, nquant);
    assert BackAt(re, crv, str, ov, S, gmB, th, l, ncap, nlook, nquant) by {
      var rf := M.FreshBodyMatchPlus(crv, str, l as int, th.look_regs, ov, ncap, nlook, nquant);
      if rf.Some? {
        forall g: LG.GroupId | g in S && g in PIV.CapIds(body)
                               && g in PIV.GmOfLive(body, rf.value.capture_regs, rf.value.look_regs, rf.value.quant_regs)
          ensures g in gmB
        {
          assert g in res.value;
          assert g in NPL.DG(r1);
        }
      }
    }
  }

  lemma LmapOkLookBodyTW(re: R.regex, qm: AR.QMap, l: nat)
    requires T.TransWf(re) && l in LTB.LookIds(re)
    ensures T.TransWf(NI.LookBodyOfRE(re, l))
    decreases re
  {
    match re
    case Re_alt(r1, r2) => if l in LTB.LookIds(r1) { LmapOkLookBodyTW(r1, qm, l); } else { LmapOkLookBodyTW(r2, qm, l); }
    case Re_con(r1, r2) => if l in LTB.LookIds(r1) { LmapOkLookBodyTW(r1, qm, l); } else { LmapOkLookBodyTW(r2, qm, l); }
    case Re_quant(_, _, _, r1) => LmapOkLookBodyTW(r1, qm, l);
    case Re_capture(_, r1) => LmapOkLookBodyTW(r1, qm, l);
    case Re_lookaround(lid0, _, r1) => if !(lid0 >= 0 && (lid0 as nat) == l) { LmapOkLookBodyTW(r1, qm, l); }
  }

  // ===========================================================================
  // 5. The kept case and the dead-only case.
  // ===========================================================================

  /** The winner's record for `lid` is best's: B's converse carriers at best transfer (G4b-1's else branch). */
  lemma KeptLidCarriers(rer: LW.RegExpRecord, re: R.regex, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
                        S: set<LG.GroupId>, G: set<LG.GroupId>, gmB: LG.GroupMap, gm: LG.GroupMap,
                        best: AI.Thread, th: AI.Thread, lid: nat, ncap: int, nlook: int, nquant: int)
    requires lid in NI.TopLookIds(re) && lid in LTB.LookIds(re)
    requires G * S == {} && LL.GmAgreeOutside(gmB, gm, G)
    requires |th.look_regs.a_cp| == |best.look_regs.a_cp|
    requires AI.get_idx(th.look_regs.a_cp, lid as int) == AI.get_idx(best.look_regs.a_cp, lid as int)
    requires AI.get_idx(th.look_regs.a_clk, lid as int) == AI.get_idx(best.look_regs.a_clk, lid as int)
    requires ELk.QClkGe(th.quant_regs, best.quant_regs.a_clk)
    requires M.MatchedPosLA(crv, th.look_regs, lid as int)
    requires NI.LookPathDom(re, AI.get_idx(th.look_regs.a_clk, lid as int), th.quant_regs.a_clk, lid)
    requires LookNestBackTTop(re, crv, str, ov, S, gmB, best, ncap, nlook, nquant)
    requires LookNestBackTTopDeep(rer, re, crv, str, ov, S, gmB, best, ncap, nlook, nquant)
    ensures DeepAt(rer, re, crv, str, S, gm, th, lid) && BackAt(re, crv, str, ov, S, gm, th, lid, ncap, nlook, nquant)
  {
    GetCpCong(th.look_regs, best.look_regs, lid as int);
    SubFirstLeafCong(rer, crv, str, lid as int, th.look_regs, best.look_regs);
    FreshBodyCong(crv, str, lid as int, th.look_regs, best.look_regs, ov, ncap, nlook, nquant);
    assert M.MatchedPosLA(crv, best.look_regs, lid as int);
    ELk.LookPathDomMono(re, AI.get_idx(th.look_regs.a_clk, lid as int), th.quant_regs.a_clk,
                        best.quant_regs.a_clk, lid);
    assert NI.LookPathDom(re, AI.get_idx(best.look_regs.a_clk, lid as int), best.quant_regs.a_clk, lid);
    assert DeepAt(rer, re, crv, str, S, gm, th, lid) by {
      var lsub := SubFirstLeafAt(rer, crv, str, lid as int, th.look_regs);
      if lsub.Some? {
        forall g: LG.GroupId | g in S && g in PIV.CapIds(NI.LookBodyOfRE(re, lid))
          ensures (g in lsub.value ==> g in gm && gm[g] == lsub.value[g]) && (g in gm ==> g in lsub.value)
        {
          assert g !in G by { if g in G { assert g in G * S; } }
          assert (g in gmB <==> g in gm) && (g in gmB ==> gmB[g] == gm[g]);
        }
      }
    }
    assert BackAt(re, crv, str, ov, S, gm, th, lid, ncap, nlook, nquant) by {
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

  lemma QuantsQSub(r: R.regex, Q: set<int>)
    ensures RF.QuantsQ(r, Q) <= NRR.QuantRegsOf(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => QuantsQSub(r1, Q); QuantsQSub(r2, Q);
    case Re_con(r1, r2) => QuantsQSub(r1, Q); QuantsQSub(r2, Q);
    case Re_quant(_, _, _, r1) => QuantsQSub(r1, Q);
    case Re_capture(_, r1) => QuantsQSub(r1, Q);
    case _ =>
  }

  lemma QuantRegsOfIds(r: R.regex, x: int)
    requires PIV.QuantUnique(r)
    ensures x in NRR.QuantRegsOf(r) <==> (x >= 0 && (x as nat) in PIV.QuantIds(r))
    decreases r
  {
    match r
    case Re_alt(r1, r2) => QuantRegsOfIds(r1, x); QuantRegsOfIds(r2, x);
    case Re_con(r1, r2) => QuantRegsOfIds(r1, x); QuantRegsOfIds(r2, x);
    case Re_quant(_, _, _, r1) => QuantRegsOfIds(r1, x);
    case Re_capture(_, r1) => QuantRegsOfIds(r1, x);
    case Re_lookaround(_, _, r1) => QuantRegsOfIds(r1, x);
    case _ =>
  }

  /** `RF.QuantsQ` is closed downwards: a quantifier inside one of its members' bodies is a member too. */
  lemma QuantsQDown(re: R.regex, Q: set<int>, qo: nat, q: nat)
    requires PIV.QuantUnique(re) && qo in PIV.QuantIds(re) && q in PIV.QuantIds(PIV.QidBody(re, qo))
    requires (qo as int) in RF.QuantsQ(re, Q)
    ensures (q as int) in RF.QuantsQ(re, Q)
    decreases re
  {
    NST.QuantIdsQidBodySubset(re, qo);
    match re
    case Re_alt(r1, r2) =>
      if qo in PIV.QuantIds(r1) {
        NST.QuantIdsQidBodySubset(r1, qo);
        assert (qo as int) !in RF.QuantsQ(r2, Q) by {
          QuantsQSub(r2, Q); QuantRegsOfIds(r2, qo as int);
          if (qo as int) in RF.QuantsQ(r2, Q) { assert qo in PIV.QuantIds(r1) * PIV.QuantIds(r2); }
        }
        QuantsQDown(r1, Q, qo, q);
      } else {
        NST.QuantIdsQidBodySubset(r2, qo);
        assert (qo as int) !in RF.QuantsQ(r1, Q) by {
          QuantsQSub(r1, Q); QuantRegsOfIds(r1, qo as int);
          if (qo as int) in RF.QuantsQ(r1, Q) { assert qo in PIV.QuantIds(r1) * PIV.QuantIds(r2); }
        }
        QuantsQDown(r2, Q, qo, q);
      }
    case Re_con(r1, r2) =>
      if qo in PIV.QuantIds(r1) {
        NST.QuantIdsQidBodySubset(r1, qo);
        assert (qo as int) !in RF.QuantsQ(r2, Q) by {
          QuantsQSub(r2, Q); QuantRegsOfIds(r2, qo as int);
          if (qo as int) in RF.QuantsQ(r2, Q) { assert qo in PIV.QuantIds(r1) * PIV.QuantIds(r2); }
        }
        QuantsQDown(r1, Q, qo, q);
      } else {
        NST.QuantIdsQidBodySubset(r2, qo);
        assert (qo as int) !in RF.QuantsQ(r1, Q) by {
          QuantsQSub(r1, Q); QuantRegsOfIds(r1, qo as int);
          if (qo as int) in RF.QuantsQ(r1, Q) { assert qo in PIV.QuantIds(r1) * PIV.QuantIds(r2); }
        }
        QuantsQDown(r2, Q, qo, q);
      }
    case Re_quant(_, qid0, _, r1) =>
      QuantRegsOfIds(r1, q as int);
      if qid0 >= 0 && (qid0 as nat) == qo {
        assert PIV.QidBody(re, qo) == r1;
        if qid0 in Q {
          assert (q as int) in NRR.QuantRegsOf(r1);
        } else {
          assert (qo as int) in RF.QuantsQ(r1, Q);
          QuantsQSub(r1, Q); QuantRegsOfIds(r1, qo as int);
          assert false;   // QuantUnique: qid0 is not in its body
        }
      } else {
        if qid0 in Q {
          assert q in PIV.QuantIds(r1) by { NST.QuantIdsQidBodySubset(r1, qo); }
          assert (q as int) in NRR.QuantRegsOf(r1);
        } else {
          assert (qo as int) in RF.QuantsQ(r1, Q);
          QuantsQDown(r1, Q, qo, q);
        }
      }
    case Re_capture(_, r1) => QuantsQDown(r1, Q, qo, q);
    case Re_lookaround(_, _, r1) =>
      assert RF.QuantsQ(re, Q) == {};
      assert false;
  }

  /** The OUTERMOST stamped host of a lid: in no stamped body. */
  lemma TopHost(re: R.regex, Q: set<int>, l: nat, q0: nat) returns (q: nat)
    requires PIV.QuantUnique(re) && LTB.LookUnique(re)
    requires q0 in PIV.QuantIds(re) && (q0 as int) in Q && l in LTB.LookIds(PIV.QidBody(re, q0))
    ensures q in PIV.QuantIds(re) && (q as int) in Q && l in LTB.LookIds(PIV.QidBody(re, q))
    ensures (q as int) !in RF.QuantsQ(re, Q)
    decreases re
  {
    NI.QidBodyLookIdsSub(re, q0);
    match re
    case Re_alt(r1, r2) =>
      if q0 in PIV.QuantIds(r1) {
        NI.QidBodyLookIdsSub(r1, q0);
        q := TopHost(r1, Q, l, q0);
        QuantsQSub(r2, Q); QuantRegsOfIds(r2, q as int);
        assert (q as int) !in RF.QuantsQ(r2, Q) by {
          if (q as int) in RF.QuantsQ(r2, Q) { assert q in PIV.QuantIds(r1) * PIV.QuantIds(r2); }
        }
      } else {
        NI.QidBodyLookIdsSub(r2, q0);
        q := TopHost(r2, Q, l, q0);
        QuantsQSub(r1, Q); QuantRegsOfIds(r1, q as int);
        assert (q as int) !in RF.QuantsQ(r1, Q) by {
          if (q as int) in RF.QuantsQ(r1, Q) { assert q in PIV.QuantIds(r1) * PIV.QuantIds(r2); }
        }
      }
    case Re_con(r1, r2) =>
      if q0 in PIV.QuantIds(r1) {
        NI.QidBodyLookIdsSub(r1, q0);
        q := TopHost(r1, Q, l, q0);
        QuantsQSub(r2, Q); QuantRegsOfIds(r2, q as int);
        assert (q as int) !in RF.QuantsQ(r2, Q) by {
          if (q as int) in RF.QuantsQ(r2, Q) { assert q in PIV.QuantIds(r1) * PIV.QuantIds(r2); }
        }
      } else {
        NI.QidBodyLookIdsSub(r2, q0);
        q := TopHost(r2, Q, l, q0);
        QuantsQSub(r1, Q); QuantRegsOfIds(r1, q as int);
        assert (q as int) !in RF.QuantsQ(r1, Q) by {
          if (q as int) in RF.QuantsQ(r1, Q) { assert q in PIV.QuantIds(r1) * PIV.QuantIds(r2); }
        }
      }
    case Re_quant(_, qid0, _, r1) =>
      if qid0 in Q && l in LTB.LookIds(r1) {
        q := qid0 as nat;
        assert PIV.QidBody(re, q) == r1;
        QuantsQSub(r1, Q); QuantRegsOfIds(r1, qid0);
      } else if qid0 >= 0 && (qid0 as nat) == q0 {
        assert PIV.QidBody(re, q0) == r1;
        assert false;
      } else {
        q := TopHost(r1, Q, l, q0);
        if qid0 in Q {
          assert l in LTB.LookIds(r1) by { NI.QidBodyLookIdsSub(r1, q0); }
          assert false;
        }
      }
    case Re_capture(_, r1) => q := TopHost(r1, Q, l, q0);
    case Re_lookaround(_, _, r1) => q := q0;
  }

  /** (c) Only dead hosts: the outermost one stays dead in the winner (it and its killer are in no stamped body,
      so their clocks are best's), and a dead host kills presence. */
  lemma DeadOnlyNotPresent(re: R.regex, Q: set<int>, best: AI.Thread, th: AI.Thread, l: nat)
    requires PIV.QuantUnique(re) && LTB.LookUnique(re)
    requires Q == ELk.StampSet(best.quant_regs.a_cp)
    requires l in NI.TopLookIds(re) && l in LTB.LookIds(re) && (l as int) in ELk.LooksQE(re, Q)
    requires l !in LiveStampLids(re, best.quant_regs)
    requires forall k :: k !in RF.QuantsQ(re, Q) ==> AI.get_idx(th.quant_regs.a_clk, k) == AI.get_idx(best.quant_regs.a_clk, k)
    ensures !NI.LookPathPresent(re, th.capture_regs.a_clk, th.quant_regs.a_clk, -1, l)
  {
    var q0 := LR.LooksQEUnderStamp(re, Q, l);
    var q := TopHost(re, Q, l, q0);
    assert AI.get_idx(best.quant_regs.a_cp, q as int) >= 0;
    if ChainFresh(re, best.quant_regs, q) {
      assert LiveStampAt(re, best.quant_regs, q);
      assert LidUnderLiveStamp(re, best.quant_regs, l);
      assert l in LiveStampLids(re, best.quant_regs) by { reveal LiveStampLids(); }
      assert false;
    }
    var qo: nat :| qo in PIV.QuantIds(re) && q in PIV.QuantIds(PIV.QidBody(re, qo))
                   && AI.get_idx(best.quant_regs.a_clk, qo as int) > AI.get_idx(best.quant_regs.a_clk, q as int);
    assert (qo as int) !in RF.QuantsQ(re, Q) by {
      if (qo as int) in RF.QuantsQ(re, Q) { QuantsQDown(re, Q, qo, q); }
    }
    LR.DeadStampKillsPresence(re, th.capture_regs.a_clk, th.quant_regs.a_clk, q, l);
  }

  // ===========================================================================
  // 6. The converse transports.
  // ===========================================================================

  lemma CarriersGmTransfer(rer: LW.RegExpRecord, re: R.regex, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
                           S: set<LG.GroupId>, G: set<LG.GroupId>, gmB: LG.GroupMap, gm: LG.GroupMap,
                           th: AI.Thread, lid: nat, ncap: int, nlook: int, nquant: int)
    requires lid in LTB.LookIds(re)
    requires G * S == {} && LL.GmAgreeOutside(gmB, gm, G)
    requires DeepAt(rer, re, crv, str, S, gmB, th, lid) && BackAt(re, crv, str, ov, S, gmB, th, lid, ncap, nlook, nquant)
    ensures DeepAt(rer, re, crv, str, S, gm, th, lid) && BackAt(re, crv, str, ov, S, gm, th, lid, ncap, nlook, nquant)
  {
    var lsub := SubFirstLeafAt(rer, crv, str, lid as int, th.look_regs);
    if lsub.Some? {
      forall g: LG.GroupId | g in S && g in PIV.CapIds(NI.LookBodyOfRE(re, lid))
        ensures (g in lsub.value ==> g in gm && gm[g] == lsub.value[g]) && (g in gm ==> g in lsub.value)
      {
        assert g !in G by { if g in G { assert g in G * S; } }
      }
    }
    var rf := M.FreshBodyMatchPlus(crv, str, lid as int, th.look_regs, ov, ncap, nlook, nquant);
    if rf.Some? {
      forall g: LG.GroupId | g in S && g in PIV.CapIds(NI.LookBodyOfRE(re, lid))
                             && g in PIV.GmOfLive(NI.LookBodyOfRE(re, lid), rf.value.capture_regs,
                                                  rf.value.look_regs, rf.value.quant_regs)
        ensures g in gm
      {
        assert g !in G by { if g in G { assert g in G * S; } }
      }
    }
  }

  /** One lid, under the presence alternative `present or not in LooksQE` (rows: the P premise; the top: the
      lowering). */
  lemma LidCarriers(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
                    Q: set<int>, S: set<LG.GroupId>, G: set<LG.GroupId>, gmB: LG.GroupMap, gm: LG.GroupMap,
                    best: AI.Thread, rp: AI.Thread, th: AI.Thread, lid: nat, ncap: int, nlook: int, nquant: int)
    requires T.TransWf(re) && AR.LmapOk(re, qm) && AR.QmapOk(re, qm) && EL.PikeLkRegexRec(T.Translate(re))
    requires PIV.CapUnique(re) && PIV.QuantUnique(re) && LTB.LookUnique(re)
    requires qm.ov == ov && !rer.multiline && !rer.ignoreCase && |ov| == |str| + 1 && OE.OracleColsOk(rer, qm, str)
    requires S == PIV.CapIdsInLooks(re)
    requires GateStaticsOkNested(qm, re, crv, ncap, nlook, nquant) && LTB.LookTablesOk(re, crv)
    requires PSM.BestLiveRE(re, best) && PSM.StampPathOk(qm, str, best.quant_regs.a_cp)
    requires Q == ELk.StampSet(best.quant_regs.a_cp)
    requires forall cp: nat :: cp <= |str| ==>
               LL.OracleOkAt(rer, qm, PIV.InpOfCp(str, cp)) && LL.OracleOkSuffix(rer, qm, PIV.InpOfCp(str, cp))
    requires G * S == {} && LL.GmAgreeOutside(gmB, gm, G)
    requires ClkFrameG4(re, Q, th, best)
    requires FrozenOk(rer, re, str, gmB, best)
    requires LookNestBackTTop(re, crv, str, ov, S, gmB, best, ncap, nlook, nquant)
    requires LookNestBackTTopDeep(rer, re, crv, str, ov, S, gmB, best, ncap, nlook, nquant)
    requires LR.WinnerLookRec(qm, re, str, best, rp)
    requires th.capture_regs == rp.capture_regs && th.look_regs == rp.look_regs
             && th.quant_regs.a_clk == rp.quant_regs.a_clk
    requires lid in NI.TopLookIds(re) && lid in LTB.LookIds(re)
    requires M.MatchedPosLA(crv, th.look_regs, lid as int)
    requires NI.LookPathDom(re, AI.get_idx(th.look_regs.a_clk, lid as int), th.quant_regs.a_clk, lid)
    requires NI.LookPathPresent(re, th.capture_regs.a_clk, th.quant_regs.a_clk, -1, lid)
             || (lid as int) !in ELk.LooksQE(re, Q)
    ensures DeepAt(rer, re, crv, str, S, gm, th, lid) && BackAt(re, crv, str, ov, S, gm, th, lid, ncap, nlook, nquant)
  {
    assert |th.look_regs.a_cp| == |best.look_regs.a_cp| && ELk.QClkGe(th.quant_regs, best.quant_regs.a_clk);
    if (lid as int) !in ELk.LooksQE(re, Q) {
      assert {:split_here} true;   // (d) the record is best's
      KeptLidCarriers(rer, re, crv, str, ov, S, G, gmB, gm, best, th, lid, ncap, nlook, nquant);
    } else if lid in LiveStampLids(re, best.quant_regs) {
      assert {:split_here} true;   // (a)/(b) a live host
      var q := LiveStampLidHost(re, best.quant_regs, lid);
      var cp := AI.get_idx(best.quant_regs.a_cp, q as int);
      assert FrozenAtQ(rer, re, str, gmB, q, cp) && PIV.QChainFresh(re, best.quant_regs.a_clk, -1, q) by {
        reveal FrozenOk();
      }
      assert PIV.QLive(re, best.quant_regs.a_clk, best.quant_regs.a_cp, q);
      TopLidBody(re, q, lid);
      LR.WinnerLookRecAt(qm, re, str, best, rp, q, lid);
      var K := AI.get_idx(best.quant_regs.a_clk, q as int);
      var cq: nat := cp as nat;
      if lid in LR.PathLooksR(qm, PIV.QidBody(re, q), T.InputAt(str, cq)) {
        assert {:split_here} true;   // (a) crossed: the replay's record at the host's position
        assert AI.get_idx(rp.look_regs.a_cp, lid as int) == cp;
        assert AReg.get_cp(th.look_regs, lid as int) == Some(cp);
        PIV.QmapOkBodyAtQid(re, qm, q);
        PSM.InpOfCpIsInputAt(str, cq);
        assert TREP.FirstEmptyPathR(qm, PIV.QidBody(re, q), PIV.InpOfCp(str, cq)).Some? by {
          reveal PSM.StampPathOk();
          assert AI.get_idx(best.quant_regs.a_cp, q as int) == cq;
        }
        CrossedLidCarriers(rer, qm, re, crv, str, ov, S, gmB, th, q, cq, lid, ncap, nlook, nquant);
        CarriersGmTransfer(rer, re, crv, str, ov, S, G, gmB, gm, th, lid, ncap, nlook, nquant);
      } else {
        assert {:split_here} true;   // (b) uncrossed: kept, or not present
        if AI.get_idx(th.look_regs.a_cp, lid as int) == AI.get_idx(best.look_regs.a_cp, lid as int)
           && AI.get_idx(th.look_regs.a_clk, lid as int) == AI.get_idx(best.look_regs.a_clk, lid as int) {
          KeptLidCarriers(rer, re, crv, str, ov, S, G, gmB, gm, best, th, lid, ncap, nlook, nquant);
        } else {
          assert !NI.LookPathPresent(re, rp.capture_regs.a_clk, rp.quant_regs.a_clk, -1, lid);
          assert false;
        }
      }
    } else {
      assert {:split_here} true;   // (c) only dead hosts
      DeadOnlyNotPresent(re, Q, best, th, lid);
      assert false;
    }
  }

  /** The converse carriers at a row's reconstructed winner, presence-premised (it keeps dead stamps' records). */
  lemma TieConvTransportG4b2P(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, crv: CP.FCompiled, str: string,
                              ov: LOr.OracleView, Q: set<int>, S: set<LG.GroupId>, G: set<LG.GroupId>,
                              gmB: LG.GroupMap, gm: LG.GroupMap, best: AI.Thread, rp: AI.Thread, th: AI.Thread,
                              ncap: int, nlook: int, nquant: int)
    requires T.TransWf(re) && AR.LmapOk(re, qm) && AR.QmapOk(re, qm) && EL.PikeLkRegexRec(T.Translate(re))
    requires PIV.CapUnique(re) && PIV.QuantUnique(re) && LTB.LookUnique(re)
    requires qm.ov == ov && !rer.multiline && !rer.ignoreCase && |ov| == |str| + 1 && OE.OracleColsOk(rer, qm, str)
    requires S == PIV.CapIdsInLooks(re)
    requires GateStaticsOkNested(qm, re, crv, ncap, nlook, nquant) && LTB.LookTablesOk(re, crv)
    requires PSM.BestLiveRE(re, best) && PSM.StampPathOk(qm, str, best.quant_regs.a_cp)
    requires Q == ELk.StampSet(best.quant_regs.a_cp)
    requires forall cp: nat :: cp <= |str| ==>
               LL.OracleOkAt(rer, qm, PIV.InpOfCp(str, cp)) && LL.OracleOkSuffix(rer, qm, PIV.InpOfCp(str, cp))
    requires G * S == {} && LL.GmAgreeOutside(gmB, gm, G)
    requires ClkFrameG4(re, Q, th, best)
    requires FrozenOk(rer, re, str, gmB, best)
    requires LookNestBackTTop(re, crv, str, ov, S, gmB, best, ncap, nlook, nquant)
    requires LookNestBackTTopDeep(rer, re, crv, str, ov, S, gmB, best, ncap, nlook, nquant)
    requires LR.WinnerLookRec(qm, re, str, best, rp)
    requires th.capture_regs == rp.capture_regs && th.look_regs == rp.look_regs
             && th.quant_regs.a_clk == rp.quant_regs.a_clk
    ensures LookNestBackTTopP(re, crv, str, ov, S, gm, th, ncap, nlook, nquant)
    ensures LookNestBackTTopDeepP(rer, re, crv, str, ov, S, gm, th, ncap, nlook, nquant)
  {
    hide FrozenOk, ClkFrameG4;
    forall lid: nat | lid in NI.TopLookIds(re)
                      && (M.MatchedPosLA(crv, th.look_regs, lid as int)
                          && lid in LTB.LookIds(re)
                          && NI.LookPathDom(re, AI.get_idx(th.look_regs.a_clk, lid as int), th.quant_regs.a_clk, lid)
                          && NI.LookPathPresent(re, th.capture_regs.a_clk, th.quant_regs.a_clk, -1, lid)
                          && AI.get_idx(th.look_regs.a_clk, lid as int) >= NI.MxAtLidLk(re, th.quant_regs.a_clk, -1, lid))
      ensures DeepAt(rer, re, crv, str, S, gm, th, lid) && BackAt(re, crv, str, ov, S, gm, th, lid, ncap, nlook, nquant)
    {
      LidCarriers(rer, qm, re, crv, str, ov, Q, S, G, gmB, gm, best, rp, th, lid, ncap, nlook, nquant);
    }
  }

  /** The converse carriers at the TOP synthetic winner `thL`: `th` with the dead lids' clocks lowered (cps kept),
      so a lowered lid is not dominant and every other lid reads `th`'s record. */
  lemma TieConvTransportG4b2Dom(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, crv: CP.FCompiled, str: string,
                                ov: LOr.OracleView, Q: set<int>, S: set<LG.GroupId>, G: set<LG.GroupId>,
                                gmB: LG.GroupMap, gm: LG.GroupMap, best: AI.Thread, rp: AI.Thread,
                                th: AI.Thread, thL: AI.Thread, ncap: int, nlook: int, nquant: int)
    requires T.TransWf(re) && AR.LmapOk(re, qm) && AR.QmapOk(re, qm) && EL.PikeLkRegexRec(T.Translate(re))
    requires PIV.CapUnique(re) && PIV.QuantUnique(re) && LTB.LookUnique(re)
    requires qm.ov == ov && !rer.multiline && !rer.ignoreCase && |ov| == |str| + 1 && OE.OracleColsOk(rer, qm, str)
    requires S == PIV.CapIdsInLooks(re)
    requires GateStaticsOkNested(qm, re, crv, ncap, nlook, nquant) && LTB.LookTablesOk(re, crv)
    requires PSM.BestLiveRE(re, best) && PSM.StampPathOk(qm, str, best.quant_regs.a_cp)
    requires Q == ELk.StampSet(best.quant_regs.a_cp)
    requires forall cp: nat :: cp <= |str| ==>
               LL.OracleOkAt(rer, qm, PIV.InpOfCp(str, cp)) && LL.OracleOkSuffix(rer, qm, PIV.InpOfCp(str, cp))
    requires G * S == {} && LL.GmAgreeOutside(gmB, gm, G)
    requires ClkFrameG4(re, Q, th, best)
    requires FrozenOk(rer, re, str, gmB, best)
    requires LookNestBackTTop(re, crv, str, ov, S, gmB, best, ncap, nlook, nquant)
    requires LookNestBackTTopDeep(rer, re, crv, str, ov, S, gmB, best, ncap, nlook, nquant)
    requires LR.WinnerLookRec(qm, re, str, best, rp)
    requires th.capture_regs == rp.capture_regs && th.look_regs == rp.look_regs
             && th.quant_regs.a_clk == rp.quant_regs.a_clk
    // the lowering: the same banks but look clocks; the lowered lids lose dominance
    requires thL.capture_regs == th.capture_regs && thL.quant_regs == th.quant_regs
    requires thL.look_regs.a_cp == th.look_regs.a_cp
    requires forall l: nat :: l in NI.TopLookIds(re) && l in LTB.LookIds(re) && (l as int) in ELk.LooksQE(re, Q)
               && !NI.LookPathPresent(re, th.capture_regs.a_clk, th.quant_regs.a_clk, -1, l)
               ==> !NI.LookPathDom(re, AI.get_idx(thL.look_regs.a_clk, l as int), th.quant_regs.a_clk, l)
    requires forall l: nat :: l in NI.TopLookIds(re) && l in LTB.LookIds(re)
               && !((l as int) in ELk.LooksQE(re, Q) && !NI.LookPathPresent(re, th.capture_regs.a_clk, th.quant_regs.a_clk, -1, l))
               ==> AI.get_idx(thL.look_regs.a_clk, l as int) == AI.get_idx(th.look_regs.a_clk, l as int)
    ensures LookNestBackTTop(re, crv, str, ov, S, gm, thL, ncap, nlook, nquant)
    ensures LookNestBackTTopDeep(rer, re, crv, str, ov, S, gm, thL, ncap, nlook, nquant)
  {
    hide FrozenOk, ClkFrameG4;
    forall lid: nat | lid in NI.TopLookIds(re)
                      && (M.MatchedPosLA(crv, thL.look_regs, lid as int)
                          && lid in LTB.LookIds(re)
                          && NI.LookPathDom(re, AI.get_idx(thL.look_regs.a_clk, lid as int), thL.quant_regs.a_clk, lid))
      ensures DeepAt(rer, re, crv, str, S, gm, thL, lid) && BackAt(re, crv, str, ov, S, gm, thL, lid, ncap, nlook, nquant)
    {
      if (lid as int) in ELk.LooksQE(re, Q) && !NI.LookPathPresent(re, th.capture_regs.a_clk, th.quant_regs.a_clk, -1, lid) {
        assert false;
      }
      assert AI.get_idx(thL.look_regs.a_clk, lid as int) == AI.get_idx(th.look_regs.a_clk, lid as int);
      assert AReg.get_cp(thL.look_regs, lid as int) == AReg.get_cp(th.look_regs, lid as int);
      assert M.MatchedPosLA(crv, th.look_regs, lid as int);
      LidCarriers(rer, qm, re, crv, str, ov, Q, S, G, gmB, gm, best, rp, th, lid, ncap, nlook, nquant);
      SubFirstLeafCong(rer, crv, str, lid as int, thL.look_regs, th.look_regs);
      FreshBodyCong(crv, str, lid as int, thL.look_regs, th.look_regs, ov, ncap, nlook, nquant);
    }
  }

  /** The whole-string oracle correctness gives the per-position facts the transports read. */
  lemma OracleEverywhere(rer: LW.RegExpRecord, qm: AR.QMap, str: string)
    requires OE.OracleColsOk(rer, qm, str)
    ensures forall cp: nat :: cp <= |str| ==>
              LL.OracleOkAt(rer, qm, PIV.InpOfCp(str, cp)) && LL.OracleOkSuffix(rer, qm, PIV.InpOfCp(str, cp))
  {
    OE.InitInputAt(str);
    assert LL.OracleOkSuffix(rer, qm, LC.InitInput(str)) by {
      forall inp: LC.Input | inp == LC.InitInput(str) || SSx.IsStrictSuffix(inp, LC.InitInput(str), WP.Forward)
        ensures LL.OracleOkAt(rer, qm, inp)
      {
        if inp != LC.InitInput(str) {
          assert LC.InitInput(str) == T.InputAt(str, 0);
          OE.SuffixIsInputAt(str, 0, inp);
          var m: nat :| 0 < m <= |str| && inp == T.InputAt(str, m);
        } else {
          assert inp == T.InputAt(str, 0);
        }
      }
    }
    forall cp: nat | cp <= |str|
      ensures LL.OracleOkAt(rer, qm, PIV.InpOfCp(str, cp)) && LL.OracleOkSuffix(rer, qm, PIV.InpOfCp(str, cp))
    {
      OracleOkSuffixAtCp(rer, qm, str, cp);
    }
  }
}
