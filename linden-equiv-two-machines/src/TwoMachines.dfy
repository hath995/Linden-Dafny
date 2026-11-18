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
  // (G5b-3) Machine B's entry and the tie transports when a stamp body may hold capture-free lookarounds
  // (`RF.StampLooksCapFreeRE`): G4a's top-level lemmas (main-cin-lk `CinLooks.dfy`), moved down to the rows.
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

  /** `TranslateCinOkS` under the stamp scope (G5b-3): the body of a greedy nullable plus, CIN or CDN, has
      capture-free look bodies, and its groups lie in `G`. */
  lemma TranslateCinOkG4(r: R.regex, G: set<LG.GroupId>)
    requires T.TransWf(r) && NR.NestedFragmentCdnRE(r)
    requires RF.StampLooksCapFreeRE(r)
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
        assert RF.StampNode(nul, q) && RF.EmptyPathLooksCapFree(body);   // `RF.StampLooksCapFreeRE`, CIN or CDN
        EPCFTranslate(body);   // (G4b-1) machine B's arm: the crossed looks are group-free
        OutLkTranslate(body);
        assert NPL.OutLk(tb) <= G;
      }
    case _ =>
  }

  /** (G4b-1) The RE scope translates to machine B's: every look an empty path can cross is group-free. */
  lemma EPCFTranslate(r: R.regex)
    requires T.TransWf(r) && RF.EmptyPathLooksCapFree(r)
    ensures NPL.EmptyLooksGroupFreeL(T.Translate(r))
    decreases r
  {
    match r
    case Re_alt(r1, r2) => EPCFTranslate(r1); EPCFTranslate(r2);
    case Re_con(r1, r2) =>
      // a half the Linden side calls nullable is nullable for the engine (`NUL.TransNonNullable`, contrapositive)
      if !NUL.NonNullableL(T.Translate(r2)) {
        if R.nullable(r2) == R.NonNullable { NUL.TransNonNullable(r2); }
        EPCFTranslate(r1);
      }
      if !NUL.NonNullableL(T.Translate(r1)) {
        if R.nullable(r1) == R.NonNullable { NUL.TransNonNullable(r1); }
        EPCFTranslate(r2);
      }
    case Re_quant(_, _, q, r1) => if q.min != 0 { EPCFTranslate(r1); }
    case Re_capture(_, r1) => EPCFTranslate(r1);
    case Re_lookaround(_, _, b) =>
      PIV.DefGroupsCapIds(b);
      assert NPL.DG(T.Translate(b)) == {} by {
        forall g | g in L.DefGroups(T.Translate(b)) ensures false { assert g in PIV.CapIds(b); }
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

  /** (G4b-1) OkT: a re-set lid (`ELk.LooksQE`) has no carrier content; a kept lid either keeps its ancestors' clocks
      (`AncFrameAvoid`) or has an ancestor in a stamped body, where the winner's stale body kills its presence (so B's
      OkT names none of its groups, `ELk.StampedAncKillsPresence`). */
  /** (G4b-2) Under the G4b-1 scope a guarded lid's groups are unset in machine B's leaf: the live host's frozen
      path crosses only capture-free looks (`NPL.CrossedGroupFreeOfScope`). */
  lemma GuardedLidUnset(rer: LW.RegExpRecord, re: R.regex, str: string, Q: set<int>, gmB: LG.GroupMap,
                        best: AI.Thread, lid: nat, g: LG.GroupId)
    requires RF.StampLooksCapFreeRE(re) && T.TransWf(re) && PIV.QuantUnique(re) && LTB.LookUnique(re)
    requires Q == ELk.StampSet(best.quant_regs.a_cp) && RF.QInStamp(re, Q)
    requires FrozenOk(rer, re, str, gmB, best)
    requires lid in LiveStampLids(re, best.quant_regs) && lid in LTB.LookIds(re)
    requires g in PIV.CapIds(NI.LookBodyOfRE(re, lid))
    ensures g !in gmB
  {
    var q := LiveStampLidHost(re, best.quant_regs, lid);
    var cp := AI.get_idx(best.quant_regs.a_cp, q as int);
    assert FrozenAtQ(rer, re, str, gmB, q, cp) by { reveal FrozenOk(); }
    assert (q as int) in Q;
    assert NRR.QidStampPlus(re, q);
    StampScopeAtQid(re, q);
    var body := PIV.QidBody(re, q);
    M.TransWfQidBody(re, q);
    EPCFTranslate(body);
    var R1 := T.Translate(body);
    var inp := PIV.InpOfCp(str, cp);
    assert NPL.FrozenAt(rer, R1, inp, gmB);
    var p := NPL.FirstEmptyPathLkL(rer, R1, inp);
    NPL.CrossedGroupFreeOfScope(rer, R1, inp);
    T4.TopLidBody(re, q, lid);
    T4.CapIdsLookBodyInLooks(body, lid);
    M.LkBodyGroupsEqCapIdsInLooks(body);
    assert g in LL.LkBodyGroups(R1);
    if g in gmB {
      assert NPL.Crossed(p.value, g);
      var i :| 0 <= i < |p.value| && p.value[i].LkS? && L.Positivity(p.value[i].lk) && g in L.DefGroups(p.value[i].b);
      assert g in NPL.DG(p.value[i].b);
      assert false;
    }
  }

  /** (G4b-2) A forward run's winner stamps only stamp pluses (the true-stamp sites), as machine A's readout. */
  lemma QInStampOfRun(re: R.regex, code: RB.code, endl: nat, str: string, cp: nat, ov: LOr.OracleView,
                      cdn: LCdn.cdns, ncap: int, nlook: int, nquant: int)
    requires NR.NfaRepRE(re, code, 0, endl) && PIV.QuantUnique(re)
    requires NR.GetPcRE(code, endl) == Some(RB.Accept) && |code| == endl + 1
    requires cp <= |str|
    ensures var inits := AI.FInitState(code, cp, AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant), 0,
                                       AI.cp_context(cp, str, LAnc.Forward));
            var r := AI.FFindMatch(code, str, inits, ov, LAnc.Forward, cdn).0;
            r.Some? ==> RF.QInStamp(re, ELk.StampSet(r.value.quant_regs.a_cp))
  {
    var ctx := AI.cp_context(cp, str, LAnc.Forward);
    var capture := AReg.init_regs(ncap);
    var look := AReg.init_regs(nlook);
    var quant := AReg.init_regs(nquant);
    var inits := AI.FInitState(code, cp, capture, look, quant, 0, ctx);
    var Q := FRD.StampQids(re);
    assert ctx.nextchar == AI.get_char(str, cp);
    FRD.TrueStampsInStamp(re, code, endl);
    FV.RegsFinalOkInit(ncap, nlook, nquant, |str|, Q);
    assert FV.VmRegsFinalOk(inits, |str|, Q) by {
      forall t0 | t0 in inits.active ensures FV.RegsFinalOk(t0, |str|, Q) {
        assert t0 == AI.init_thread(capture, look, quant);
      }
    }
    FV.FFindMatchRegsFinal(code, str, inits, ov, LAnc.Forward, cdn, Q);
    var r := AI.FFindMatch(code, str, inits, ov, LAnc.Forward, cdn).0;
    if r.Some? {
      assert FV.RegsFinalOk(r.value, |str|, Q);
      forall q: nat | q in PIV.QuantIds(re) && (q as int) in ELk.StampSet(r.value.quant_regs.a_cp)
        ensures NRR.QidStampPlus(re, q)
      {
        assert AI.get_idx(r.value.quant_regs.a_cp, q as int) >= 0;
        assert (q as int) in Q;
        var qn: nat :| qn in PIV.QuantIds(re) && NRR.QidStampPlus(re, qn) && qn as int == q as int;
      }
    }
  }

  /** Under `RF.StampLooksCapFreeRE`, a stamp plus's body has capture-free empty-path looks. */
  lemma StampScopeAtQid(re: R.regex, q: nat)
    requires RF.StampLooksCapFreeRE(re) && PIV.QuantUnique(re) && q in PIV.QuantIds(re) && NRR.QidStampPlus(re, q)
    ensures RF.EmptyPathLooksCapFree(PIV.QidBody(re, q))
    decreases re
  {
    match re
    case Re_alt(r1, r2) => if q in PIV.QuantIds(r1) { StampScopeAtQid(r1, q); } else { StampScopeAtQid(r2, q); }
    case Re_con(r1, r2) => if q in PIV.QuantIds(r1) { StampScopeAtQid(r1, q); } else { StampScopeAtQid(r2, q); }
    case Re_quant(_, qid0, _, r1) => if !(qid0 >= 0 && (qid0 as nat) == q) { StampScopeAtQid(r1, q); }
    case Re_capture(_, r1) => StampScopeAtQid(r1, q);
    case Re_lookaround(_, _, r1) => StampScopeAtQid(r1, q);
  }

  lemma TieOkTTransportG4(rer: LW.RegExpRecord, re: R.regex, str: string, Q: set<int>, S: set<LG.GroupId>,
                          G: set<LG.GroupId>, gmB: LG.GroupMap, gm: LG.GroupMap, best: AI.Thread, th: AI.Thread)
    requires RF.StampLooksCapFreeRE(re) && T.TransWf(re) && PIV.CapUnique(re) && PIV.QuantUnique(re) && LTB.LookUnique(re)
    requires PSM.BestLiveRE(re, best) && Q == ELk.StampSet(best.quant_regs.a_cp) && RF.QInStamp(re, Q)
    requires G * S == {} && LL.GmAgreeOutside(gmB, gm, G)
    requires ClkFrameG4(re, Q, th, best)
    requires LookNestOkTTop(re, S, gmB, best) && FrozenOk(rer, re, str, gmB, best)   // (G4b-2) the guard
    ensures LookNestOkTTopU(re, S, gm, th)   // (G4b-2) unguarded at the winner
  {
    ELk.StampLooksCapFreeETop(re);
    ELk.BodyStaleAtStamps(re, best, Q);
    forall lid: nat | lid in NI.TopLookIds(re)
                      && (lid in LTB.LookIds(re)
                          && exists g: LG.GroupId :: g in S && g in gm && g in PIV.CapIds(NI.LookBodyOfRE(re, lid)))
      ensures NI.LookPathPresent(re, th.capture_regs.a_clk, th.quant_regs.a_clk, -1, lid)
              && AI.get_idx(th.look_regs.a_clk, lid as int) >= 0
              && AI.get_idx(th.look_regs.a_clk, lid as int) >= NI.MxAtLidLk(re, th.quant_regs.a_clk, -1, lid)
    {
      var g: LG.GroupId :| g in S && g in gm && g in PIV.CapIds(NI.LookBodyOfRE(re, lid));
      if (lid as int) in ELk.LooksQE(re, Q) { ELk.LooksQECapFree(re, Q, lid); assert false; }
      assert g !in G by { if g in G { assert g in G * S; } }
      assert g in gmB;
      if lid in LiveStampLids(re, best.quant_regs) {
        GuardedLidUnset(rer, re, str, Q, gmB, best, lid, g);
        assert false;
      }
      assert exists g0: LG.GroupId :: g0 in S && g0 in gmB && g0 in PIV.CapIds(NI.LookBodyOfRE(re, lid));
      assert NI.LookPathPresent(re, best.capture_regs.a_clk, best.quant_regs.a_clk, -1, lid)
             && AI.get_idx(best.look_regs.a_clk, lid as int) >= 0
             && AI.get_idx(best.look_regs.a_clk, lid as int) >= NI.MxAtLidLk(re, best.quant_regs.a_clk, -1, lid);
      if CLP.AncCapRegs(re, lid) * RF.CapsQ(re, Q) != {} || CLP.AncQuants(re, lid) * RF.QuantsQ(re, Q) != {} {
        ELk.StampedAncKillsPresence(re, best.capture_regs.a_clk, best.quant_regs.a_clk, -1, lid, Q);
        assert false;
      }
      AncFrameAvoid(re, Q, th, best, lid);
      assert AI.get_idx(th.look_regs.a_clk, lid as int) == AI.get_idx(best.look_regs.a_clk, lid as int);
    }
  }

  /** (G4b-1) BackT: a kept lid keeps its record, and its dominance moves down to the winner (the replay only raised
      quant clocks). */
  lemma TieBackTransportG4(re: R.regex, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
                           Q: set<int>, S: set<LG.GroupId>, G: set<LG.GroupId>,
                           gmB: LG.GroupMap, gm: LG.GroupMap, best: AI.Thread, th: AI.Thread,
                           ncap: int, nlook: int, nquant: int)
    requires RF.StampLooksCapFreeRE(re) && LTB.LookUnique(re)
    requires G * S == {} && LL.GmAgreeOutside(gmB, gm, G)
    requires ClkFrameG4(re, Q, th, best)
    requires LookNestBackTTop(re, crv, str, ov, S, gmB, best, ncap, nlook, nquant)
    ensures LookNestBackTTop(re, crv, str, ov, S, gm, th, ncap, nlook, nquant)
  {
    ELk.StampLooksCapFreeETop(re);
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
      if (lid as int) in ELk.LooksQE(re, Q) {
        ELk.LooksQECapFree(re, Q, lid);   // no group of the body: the conclusion is vacuous
      } else {
        GetCpCong(th.look_regs, best.look_regs, lid as int);
        FreshBodyCong(crv, str, lid as int, th.look_regs, best.look_regs, ov, ncap, nlook, nquant);
        assert M.MatchedPosLA(crv, best.look_regs, lid as int);
        assert AI.get_idx(th.look_regs.a_clk, lid as int) == AI.get_idx(best.look_regs.a_clk, lid as int);
        ELk.LookPathDomMono(re, AI.get_idx(th.look_regs.a_clk, lid as int), th.quant_regs.a_clk,
                            best.quant_regs.a_clk, lid);
        assert NI.LookPathDom(re, AI.get_idx(best.look_regs.a_clk, lid as int), best.quant_regs.a_clk, lid);
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
  }

  lemma TieDeepTransportG4(rer: LW.RegExpRecord, re: R.regex, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
                           Q: set<int>, S: set<LG.GroupId>, G: set<LG.GroupId>,
                           gmB: LG.GroupMap, gm: LG.GroupMap, best: AI.Thread, th: AI.Thread,
                           ncap: int, nlook: int, nquant: int)
    requires RF.StampLooksCapFreeRE(re) && LTB.LookUnique(re)
    requires G * S == {} && LL.GmAgreeOutside(gmB, gm, G)
    requires ClkFrameG4(re, Q, th, best)
    requires LookNestBackTTopDeep(rer, re, crv, str, ov, S, gmB, best, ncap, nlook, nquant)
    ensures LookNestBackTTopDeep(rer, re, crv, str, ov, S, gm, th, ncap, nlook, nquant)
  {
    ELk.StampLooksCapFreeETop(re);
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
      if (lid as int) in ELk.LooksQE(re, Q) {
        ELk.LooksQECapFree(re, Q, lid);   // no group of the body: the conclusion is vacuous
      } else {
        GetCpCong(th.look_regs, best.look_regs, lid as int);
        SubFirstLeafCong(rer, crv, str, lid as int, th.look_regs, best.look_regs);
        assert M.MatchedPosLA(crv, best.look_regs, lid as int);
        assert AI.get_idx(th.look_regs.a_clk, lid as int) == AI.get_idx(best.look_regs.a_clk, lid as int);
        ELk.LookPathDomMono(re, AI.get_idx(th.look_regs.a_clk, lid as int), th.quant_regs.a_clk,
                            best.quant_regs.a_clk, lid);
        assert NI.LookPathDom(re, AI.get_idx(best.look_regs.a_clk, lid as int), best.quant_regs.a_clk, lid);
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
  }


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
    requires RF.StampLooksCapFreeRE(body)   // (G5b-3) stamp looks capture-free
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
    hide ClkFrameG4, RF.StampLooksCapFreeRE;   // (G5b-3) passed on as terms: their quantifiers stay out of every batch

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
    requires RF.StampLooksCapFreeRE(body)   // (G5b-3) stamp looks capture-free
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
    hide ClkFrameG4, RF.StampLooksCapFreeRE;   // (G5b-3) passed on as terms: their quantifiers stay out of every batch

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
