// L3a — THE LIFT: the standalone parallel simulation VM ↔ machine B.
//
// SCAFFOLD (2026-08-02): definitions are REAL and resolve; the lemmas are
// BODILESS — each carries a FILL note naming its template and ingredients.
// Fill order (historical; `TtLkSameTree` was superseded by the quotient
// `ETreeRepLkDeterm` and its dead admitted statement removed 2026-08-25): TtLkSameTree → GateStepValue → LiftInit → LiftAdvanceEpsilon →
// LiftConsume → LiftFindMatch → LiftEndpoint. Verify per-symbol as you go
// (bodiless lemmas verify trivially and warn; the warnings disappear as
// bodies land).
//
// WHAT THIS PROVES, once filled: the VM run induces a valid LK-aware
// PikeTree trace (PikeTreeLk) on the SPEC tree t, whose states pair with the
// VM's — per thread, the B-side group map `gmt` carries the t-side
// accumulated captures, tied OUTSIDE S to GmOfLive(thread regs) and INSIDE S
// to the fresh body replay at the thread's own a_cp[l]. At the end,
// PTL.PikeTreeLkComputesFirstLeaf pins B's best to FirstLeaf(t, inp), so the
// winner's leaf values — inside-look groups INCLUDED — equal the engine's
// reconstruction with no position theorem and no leaf-occurrence reasoning.
//
// WHY NO A-MACHINE / NO PikeSimRE COMPOSITION: B's own correctness layer
// (PtsPreservationLk) already handles priority and memoization soundness on
// the t side, so the lift only has to produce LEGAL B steps mirroring VM
// behavior; the one genuinely shared obligation with the old sim is the
// processed↔seen pairing (SeenRepLk below, mirrored from SeenInclusionRE).
// The existing sim and its files stay UNTOUCHED.
//
// GRANULARITY: the ClockMono frame trio (FAdvanceEpsilon / FConsume /
// FFindMatch parallel induction) — the shape that went first-try five times
// in this campaign (FFindMatchLookCpOk, LookClkSet, LookOracleTrue,
// FFindMatchLookFrame, FFindMatchCapWriteFrame). LiftAdvanceEpsilon's
// per-instruction cases mirror those recursions; the CheckOracle case is the
// only one that STEPS B through a gate, and its value content is
// GateStepValue = the proven keystone LkReplayMatchesSpec at cp = s1.cp.
include "MainTheorem.dfy"
include "PikeTreeLk.dfy"
include "LookBehindKeystone.dfy"
include "OracleMirrorV.dfy"
include "FlipGate.dfy"
include "FlipClosed.dfy"

/** The lift: a per-thread pairing between the RegElk VM and the LK-aware
    PikeTree machine on the SPEC tree, whose group-map tie carries the
    reconstructed inside-look capture values. Scaffold — lemmas are bodiless. */
module LindenElkLiftSimForward {
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
  import opened LindenElkLiftSimCarriers
  import opened LindenElkLiftSimDeep

  /** (perf) The DEEP arm of `ForwardFindRecLB` (a LOOKBEHIND owner), extracted: the whole LB arm
      OOM-kills the 80G slice alone at CORES=4. Mutually recursive with `ForwardFindRec` on
      `(|LookIds(host)|, arm)`: ForwardFindRec 2 > ForwardFindRecLB 1 > this 0. */
  lemma ForwardFindRecLBDeep(
    rer: LW.RegExpRecord, qm: AR.QMap, crv: CP.FCompiled, str: string, ast: R.regex, re: R.regex,
    ov: LOr.OracleView, res0: AReg.Regs, res1: AReg.Regs, res2: AReg.Regs,
    host: R.regex, A: nat, g: nat, ncap: int, nlook: int, nquant: int)
    // ---- whole-regex statics (fixed) ----
    requires T.TransWf(re) && NR.NestedFragmentRE(re) && NR.L5ScopeRE(re) && L5ScopeV1RE(re)
    requires PIV.CapUnique(re) && PIV.QuantUnique(re) && LTB.LookUnique(re)
    requires LTB.LookTablesOk(re, crv)
    requires |crv.f_look_types| == |crv.f_look_ast|
    requires forall x: nat :: x in LTB.LookIds(re) ==> 1 <= x <= R.max_lookaround(ast)
    requires forall x: nat :: x in LTB.LookIds(re) ==> (x as int) in qm.looks
    requires nlook == R.max_lookaround(ast) + 1
    requires qm.ov == ov && !rer.multiline && !rer.ignoreCase && |ov| == |str| + 1
    requires forall l: int :: l in qm.looks ==> l >= 0
    requires forall cp: nat :: cp <= |str| ==> LL.OracleOkSuffix(rer, qm, PIV.InpOfCp(str, cp))
    requires GateStaticsOkNested(qm, re, crv, ncap, nlook, nquant)
    requires forall l: int, la: R.lookaround, b: R.regex ::
               1 <= l <= R.max_lookaround(ast) && LTB.LookEntryOk(crv, l, la, b) ==>
                 M.FrameEntryOk(crv, la, b, PIV.CaptureRegsSet(PIV.CapIdsInLooks(re)), M.LookIdSet(re))
    requires forall c: nat :: c in PIV.CapIdsInLooks(re) ==> M.GNotUnderQuantL(T.Translate(re), c)
    // ---- global res-side facts ----
    requires |res1.a_cp| == nlook && |res1.a_clk| == nlook
    requires CM.LookCpSetWithClk(res1) && CM.LookCpsLE(res1, |str|)
    requires M.FLookLoopChildLinkOk(crv, str, res1, 1, R.max_lookaround(ast), ov, ncap, nlook, nquant)
    requires M.FLookLoopValueOkFull(crv, str, res0, res1, 1, R.max_lookaround(ast), ov, ncap, nlook, nquant)
    requires M.FLookLoopQuantValueOkFull(crv, str, res2, res1, 1, R.max_lookaround(ast), ov, ncap, nlook, nquant)
    // ---- per-level data ----
    requires A in LTB.LookIds(re)
    requires host == NI.LookBodyOfRE(re, A)
    requires M.MatchedPosLA(crv, res1, A as int)
    requires g in PIV.CapIds(host) && g in PIV.CapIdsInLooks(re)
    requires var lsub := SubFirstLeafAt(rer, crv, str, A as int, res1);
             lsub.Some? && g in lsub.value
    ensures PIV.PathPresentLk(host, res0.a_clk, res1.a_clk, res2.a_clk, -1, g)
    ensures AI.get_idx(res0.a_clk, CP.start_reg(g)) >= 0
    ensures AI.get_idx(res0.a_cp, CP.start_reg(g)) >= 0
    ensures AI.get_idx(res0.a_clk, CP.start_reg(g))
         >= PIV.MxAtGidLk(host, res0.a_clk, res1.a_clk, res2.a_clk, -1, g)
    // (L5 F7c-4) the value tie is stated as a `NormRange` equality so that the
    // backward fresh match's reversed read (LB arm) and the forward read (LA
    // arm) chain uniformly; `NormSwapCong` absorbs the LB swap.
    ensures PIV.NormRange(SubFirstLeafAt(rer, crv, str, A as int, res1).value[g])
         == PIV.NormRange(PIV.LiveRange(res0.a_cp, res0.a_clk, g))
    requires crv.f_look_types[A as int].Lookbehind?
    requires g in PIV.CapIdsInLooks(host)
    decreases |LTB.LookIds(host)|, 0
  {
    var maxlook := R.max_lookaround(ast);
    var cpA := AReg.get_cp(res1, A as int).value;
    RL.AAsArraysLaws(res1);
    assert AI.get_idx(res1.a_cp, A as int) >= 0 && cpA == AI.get_idx(res1.a_cp, A as int);
    assert 0 <= cpA <= |str|;                                    // LookCpsLE(res1)
    var inpA := PIV.InpOfCp(str, cpA);
    var bodycode := CP.compile_to_bytecode(host);

    // ---- the row at A (VERBATIM DeepFindRec) ----
    assert 1 <= A <= maxlook && (A as int) in qm.looks;
    assert GateStaticAtNested(qm, re, crv, A as int, ncap, nlook, nquant);
    var laA: R.lookaround, bA: R.regex :|
      LTB.LookEntryOk(crv, A as int, laA, bA)
      && T.TransWf(bA) && NR.NestedFragmentRE(bA)
      && NR.NegLooksLookFreeRE(bA)
      && (laA.Lookbehind? ==> NR.LBOnlyLooksRE(bA))
      && (!laA.Lookbehind? ==> L5ScopeV1RE(bA))
      && qm.looks[A as int].0 == T.TrLookaround(laA)
      && qm.looks[A as int].1 == T.Translate(bA)
      && (set g0: LG.GroupId | g0 in L.DefGroups(T.Translate(bA))) <= PIV.CapIdsInLooks(re)
      && var bc := CP.compile_to_bytecode(bA);
      |bc| >= 1
      && PSM.StaticOkNestedRE(qm, bA, bc, |bc| - 1)
      && PSM.SizesOkRE(bA, ncap, nlook, nquant)
      && ((laA.NegLookbehind? || laA.NegLookahead?) ==> NR.CaptureFreeRE(bA));
    NI.LookBodyOfTablesTie(re, crv, A);
    var laT: R.lookaround :| LTB.LookEntryOk(crv, A as int, laT, NI.LookBodyOfRE(re, A));
    assert bA == host by { assert crv.f_look_ast[A as int] == bA == host; }
    assert host == M.VBody(crv, A as int);
    var endlH: nat := |bodycode| - 1;
    assert PSM.StaticOkNestedRE(qm, host, bodycode, endlH);
    assert crv.f_look_types[A as int] == laA;
    assert (laA.Lookahead? || laA.Lookbehind?) by {
      assert AI.capture_type(crv.f_look_types[A as int]);        // MatchedPosLA
    }
    assert laA.Lookbehind? by { assert crv.f_look_types[A as int] == laA; }
    // ==== (L5 F7c-4) LOOKBEHIND lid: lift via the FLIP twins ====
    M.LookBodyFactsL5(re, crv, A);
    var laN: R.lookaround :| LTB.LookEntryOk(crv, A as int, laN, host) && (laN.Lookbehind? ==> NR.LBOnlyLooksRE(host));
    assert laN == laA;
    assert NR.LBOnlyLooksRE(host);
    FG.LBOnlyEquiv(host);
    assert FST.LBOnlyLooksRE(host);
    // ---- rf_A: the fresh BACKWARD body match (Some via the LB carrier's None-iff — the
    //      backward leaf EXISTS by hypothesis) ----
    assert M.FrameEntryOk(crv, laA, host,
                          PIV.CaptureRegsSet(PIV.CapIdsInLooks(re)), M.LookIdSet(re));
    assert PIV.CapUnique(host) && PIV.QuantUnique(host) && LTB.LookUnique(host)
           && LTB.LookTablesOk(host, crv);                          // FrameEntryOk
    var qmB := AR.QMap(qm.quants,
                       map l: int | l in qm.looks && l >= 0 && (l as nat) in LTB.LookIds(host) :: qm.looks[l],
                       qm.ov);
    assert AR.QmapOk(host, qmB) by { QmapOkLooksIrrel(host, qm, qmB); }
    assert AR.LmapOk(host, qmB) by { LmapOkRestrict(host, qm, qmB); }
    assert OE.OracleColsOk(rer, qmB, str) by {
      SufForallToColsOk(rer, qm, str);
      OracleColsOkRestrict(rer, qm, qmB, str);
    }
    var bodycodeB := CP.compile_to_bytecode(R.reverse_regex(host));
    var cdnA := crv.f_look_cdns[A as int];
    LookNestBackTFromBodyReplayLB(rer, qmB, laA, host, bodycodeB, crv, str, cpA, ov,
                                  cdnA, crv.f_plus_bc, ncap, nlook, nquant);
    var rbT := LFU.ComputeTr(rer, [LS.Areg(T.Translate(host))], inpA, LG.Empty, WP.Backward);
    var rb := LT.TreeRes(rbT, LG.Empty, inpA, WP.Backward);
    var rfP := AI.FFindMatchPlus(bodycodeB, host, crv.f_plus_bc, str, ov, LAnc.Backward, cpA,
                                 AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant),
                                 0, cdnA).0;
    // the backward leaf exists (hypothesis) — unfold SubFirstLeafAt to rb
    assert LidDir(crv, A as int) == WP.Backward;             // dispatch: laA.Lookbehind?
    var lsubA := SubFirstLeafAt(rer, crv, str, A as int, res1);
    SubFirstLeafAtIsBackLeaf(rer, crv, str, A as int, res1, host);
    assert lsubA == FG.BackLeafAt(rer, host, str, cpA);
    assert lsubA.Some? && rb.Some? && lsubA.value == rb.value.1;
    assert rfP.Some?;                                            // None-iff
    var rfA := rfP.value;
    var Sh := PIV.CapIdsInLooks(host);
    var gmtH := rb.value.1;
    assert gmtH == lsubA.value;

    // rf_A IS FreshBodyMatch(A, res1) — the backward fresh run
    // (L5 F7f) the unfold's row witnesses, hoisted
    assert host == M.VBody(crv, A as int) by {
      NI.LookBodyOfTablesTie(re, crv, A);
      var laT2: R.lookaround :| LTB.LookEntryOk(crv, A as int, laT2, host);
    }
    assert 0 <= (A as int) < |crv.f_look_types| && crv.f_look_types[A as int].Lookbehind?;
    assert 0 <= (A as int) < |crv.f_look_cdns| && cdnA == crv.f_look_cdns[A as int];
    assert AReg.get_cp(res1, A as int).Some? && AReg.get_cp(res1, A as int).value == cpA;
    var rfFresh := M.FreshBodyMatch(crv, str, A as int, res1, ov, ncap, nlook, nquant);
    assert rfFresh == AI.FFindMatch(bodycodeB, str,
                                    AI.FInitState(bodycodeB, cpA, AReg.init_regs(ncap), AReg.init_regs(nlook),
                                                  AReg.init_regs(nquant), 0, AI.cp_context(cpA, str, LAnc.Backward)),
                                    ov, LAnc.Backward, cdnA).0 by {
      FG.FreshBodyMatchLBUnfold(crv, str, A as int, res1, ov, host, ncap, nlook, nquant);
    }
    assert rfA == rfFresh.value by {                        // (L5 F7f perf) via the helper
      BackFreshPlusIsPlain(host, bodycodeB, crv.f_plus_bc, str, ov, cpA, cdnA, ncap, nlook, nquant);
    }
    assert rfFresh.Some?;

    // the FLookLoop value/quant lifts at owner == A
    assert CM.RegsAgreeInside(res0, rfFresh.value.capture_regs,
                              PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(host))) by {
      assert 1 <= A as int <= maxlook && M.MatchedPosLA(crv, res1, A as int);
      assert M.VBody(crv, A as int) == host;
    }
    assert CM.RegsAgreeInside(res2, rfFresh.value.quant_regs, M.QIdsOuter(host)) by {
      assert 1 <= A as int <= maxlook && M.MatchedPosLA(crv, res1, A as int);
    }
    // the fragment scope at host
    GNotUnderQuantLLookBody(re, A, g);
    assert M.GNotUnderQuantL(T.Translate(host), g);

    // ==== DEEP: descend through g's top-in-host ancestor A1 ====
    var ownH := NI.InnermostOwnerDirect(host, g);
    var A1 := ReconLiveTopAncestor(host, g, ownH);
    assert A1 in NI.TopLookIds(host) && A1 in LTB.LookIds(host)
           && g in PIV.CapIds(NI.LookBodyOfRE(host, A1));
    NI.LookBodyLookIdsIn(re, A);
    assert A1 in LTB.LookIds(re);
    NI.LookBodyCompose(re, A, A1);
    var bodyA1 := NI.LookBodyOfRE(re, A1);
    assert bodyA1 == NI.LookBodyOfRE(host, A1);

    // (a) the FORWARD carrier at A1 (leaf-witness g): crossed + dominant on rf_A
    assert LookNestOkTTop(host, Sh, gmtH, rfA);
    assert g in Sh && g in gmtH && g in PIV.CapIds(NI.LookBodyOfRE(host, A1));
    assert NI.LookPathPresent(host, rfA.capture_regs.a_clk, rfA.quant_regs.a_clk, -1, A1)
           && AI.get_idx(rfA.look_regs.a_clk, A1 as int) >= 0
           && AI.get_idx(rfA.look_regs.a_clk, A1 as int)
              >= NI.MxAtLidLk(host, rfA.quant_regs.a_clk, -1, A1);
    var L1 := AI.get_idx(rfA.look_regs.a_clk, A1 as int);
    NI.LookPathDomIntroTop(host, rfA.capture_regs.a_clk, rfA.quant_regs.a_clk, -1, A1, L1);
    assert NI.LookPathDom(host, L1, rfA.quant_regs.a_clk, A1);
    // A1 matched on rf_A (forward invariant: clk set => cp set on the fresh run)
    assert CM.LookCpSetWithClk(rfA.look_regs);
    assert AI.get_idx(rfA.look_regs.a_cp, A1 as int) >= 0;
    assert AReg.get_cp(rfA.look_regs, A1 as int).Some?;        // get_idx >= 0 ==> in-range, Some
    assert M.MatchedPosLA(crv, rfA.look_regs, A1 as int) by {
      assert GateStaticAtNested(qm, re, crv, A1 as int, ncap, nlook, nquant);
      var la1: R.lookaround, b1: R.regex :|
        LTB.LookEntryOk(crv, A1 as int, la1, b1);
      assert crv.f_look_types[A1 as int] == la1;
      assert la1.Lookbehind? || la1.NegLookbehind? by {
        FG.LookRowLBOnly(host, crv, A1);
      }
      assert AI.capture_type(crv.f_look_types[A1 as int]);
    }

    // (b) the ⊆ direction of the REGION-EQUALITY deep carrier at A1 needs
    //     A1's sub-leaf to EXIST — from the fresh run's oracle-true records
    //     (backward tree Some? via the LB carrier's None-iff at the A1-restricted qm).
    var ctxB := AI.cp_context(cpA, str, LAnc.Backward);
    var initsB := AI.FInitState(bodycodeB, cpA, AReg.init_regs(ncap), AReg.init_regs(nlook),
                                AReg.init_regs(nquant), 0, ctxB);
    assert CM.VmLookOracleTrue(initsB, ov) by {
      RL.AInitLaws(nlook);
      forall l: int | AI.get_idx(AReg.init_regs(nlook).a_cp, l) >= 0
        ensures LOr.view_get_oracle(ov, AI.get_idx(AReg.init_regs(nlook).a_cp, l), l)
      {
        if 0 <= l < nlook { assert AReg.init_regs(nlook).a_cp[l] == -1; }
      }
    }
    M.NoWriteOracleBodyCodeNested(R.reverse_regex(host));
    assert ctxB.nextchar == AI.get_char(str, cpA);
    CM.FFindMatchLookOracleTrueB(bodycodeB, str, initsB, ov, LAnc.Backward, cdnA);
    assert CM.LookCpsOracleTrue(rfA.look_regs, ov) by {
      assert rfA == rfFresh.value;
    }
    var cp1 := AReg.get_cp(rfA.look_regs, A1 as int).value;
    assert cp1 == AI.get_idx(rfA.look_regs.a_cp, A1 as int);
    assert LOr.view_get_oracle(ov, cp1, A1 as int);
    assert 0 <= cp1 <= |str| by {
      M.ReplayLookCpOkNestedLB(bodycodeB, str, ov, cdnA, crv.f_plus_bc, cpA,
                               AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant), host);
      assert CM.LookCpsLE(rfA.look_regs, |str|);
    }
    var inp1 := PIV.InpOfCp(str, cp1);
    assert T.TransWf(bodyA1) by { M.TransWfLookBodyOfRE(re, A1); }
    var dir1 := LidDir(crv, A1 as int);
    var t1 := LFU.ComputeTr(rer, [LS.Areg(T.Translate(bodyA1))], inp1, LG.Empty, dir1);
    assert LT.FirstLeaf(t1, inp1).Some? by {
      assert LL.OracleOkSuffix(rer, qm, inp1);
      assert LL.OracleOkAt(rer, qm, inp1);
      assert (A1 as int) in qm.looks;
      assert GateStaticAtNested(qm, re, crv, A1 as int, ncap, nlook, nquant);
      var la1G: R.lookaround, b1G: R.regex :| LTB.LookEntryOk(crv, A1 as int, la1G, b1G)
                                              && T.TransWf(b1G) && NR.NestedFragmentRE(b1G)
                                              && NR.NegLooksLookFreeRE(b1G)
                                              && (la1G.Lookbehind? ==> NR.LBOnlyLooksRE(b1G))
                                              && (!la1G.Lookbehind? ==> L5ScopeV1RE(b1G))
                                              && qm.looks[A1 as int].0 == T.TrLookaround(la1G)
                                              && qm.looks[A1 as int].1 == T.Translate(b1G)
                                              && (set gx: LG.GroupId | gx in L.DefGroups(T.Translate(b1G))) <= PIV.CapIdsInLooks(re)
                                              && var bc1 := CP.compile_to_bytecode(b1G);
                                              |bc1| >= 1
                                              && PSM.StaticOkNestedRE(qm, b1G, bc1, |bc1| - 1)
                                              && PSM.SizesOkRE(b1G, ncap, nlook, nquant)
                                              && ((la1G.NegLookbehind? || la1G.NegLookahead?) ==> NR.CaptureFreeRE(b1G));
      assert b1G == bodyA1 by {
        NI.LookBodyOfTablesTie(re, crv, A1);
        var la1T: R.lookaround :| LTB.LookEntryOk(crv, A1 as int, la1T, bodyA1);
        assert crv.f_look_ast[A1 as int] == b1G == bodyA1;
      }
      assert crv.f_look_types[A1 as int] == la1G && dir1 == L.LkDir(T.TrLookaround(la1G)) by {
        assert M.MatchedPosLA(crv, rfA.look_regs, A1 as int);
        assert AI.capture_type(crv.f_look_types[A1 as int]);
      }
      assert TREP.CpOf(inp1) == cp1 by { LS.ReverseLength(str[..cp1]); }
      assert LT.TreeRes(LFU.ComputeTr(rer, [LS.Areg(T.Translate(bodyA1))], inp1, LG.Empty, dir1),
                        LG.Empty, inp1, dir1).Some?;
      assert LT.FirstLeaf(t1, inp1) == LT.TreeRes(t1, LG.Empty, inp1, dir1);
    }
    var lsub1rf := SubFirstLeafAt(rer, crv, str, A1 as int, rfA.look_regs);
    assert bodyA1 == M.VBody(crv, A1 as int) by {
      NI.LookBodyOfTablesTie(re, crv, A1);
      var la1T: R.lookaround :| LTB.LookEntryOk(crv, A1 as int, la1T, bodyA1);
    }
    assert lsub1rf.Some? && lsub1rf.value == LT.FirstLeaf(t1, inp1).value.1 by {
      assert AReg.get_cp(rfA.look_regs, A1 as int) == Some(cp1 as int);
      assert LT.FirstLeaf(t1, inp1) == LT.TreeRes(t1, LG.Empty, inp1, dir1);
    }
    // the carrier: region equality at A1 — the ⊆ direction pushes g in, the
    // ⊇ direction's value clause gives the value tie.
    assert LookNestBackTTopDeep(rer, host, crv, str, ov, Sh, gmtH, rfA, ncap, nlook, nquant);
    assert g in lsub1rf.value && gmtH[g] == lsub1rf.value[g] by {
      assert g in gmtH;
    }

    // (c) LEVEL-LINK: re-key A1's sub-leaf onto res1
    TopEqDirectLookIds(host);
    assert A1 as int in M.DirectLidSet(host) by { assert A1 in M.DirectLookIds(host); }
    assert AReg.get_cp(res1, A1 as int) == AReg.get_cp(rfFresh.value.look_regs, A1 as int)
           && AI.get_idx(res1.a_clk, A1 as int) == AI.get_idx(rfFresh.value.look_regs.a_clk, A1 as int) by {
      assert M.FLookLoopChildLinkOk(crv, str, res1, 1, maxlook, ov, ncap, nlook, nquant);
      assert 1 <= A as int <= maxlook && M.MatchedPosLA(crv, res1, A as int);
      assert rfFresh.Some?;
    }
    var lsub1 := SubFirstLeafAt(rer, crv, str, A1 as int, res1);
    assert lsub1 == lsub1rf;                                   // reads only get_cp at A1
    assert M.MatchedPosLA(crv, res1, A1 as int) by {
      assert AReg.get_cp(res1, A1 as int).Some?;
    }

    // (d) RECURSE at (bodyA1, A1)
    assert |LTB.LookIds(bodyA1)| < |LTB.LookIds(host)| by {
      NI.LookBodyLookIdsIn(host, A1);
      LookIdNotInOwnBody(host, A1);
      SubsetCardLt(LTB.LookIds(bodyA1), LTB.LookIds(host), A1);
    }
    assert g in PIV.CapIds(bodyA1) && g in lsub1.value;
    ForwardFindRec(rer, qm, crv, str, ast, re, ov, res0, res1, res2,
                   bodyA1, A1, g, ncap, nlook, nquant);
    assert PIV.PathPresentLk(bodyA1, res0.a_clk, res1.a_clk, res2.a_clk, -1, g);
    assert AI.get_idx(res0.a_clk, CP.start_reg(g)) >= 0
           && AI.get_idx(res0.a_cp, CP.start_reg(g)) >= 0;
    assert AI.get_idx(res0.a_clk, CP.start_reg(g))
        >= PIV.MxAtGidLk(bodyA1, res0.a_clk, res1.a_clk, res2.a_clk, -1, g);
    assert PIV.NormRange(lsub1.value[g]) == PIV.NormRange(PIV.LiveRange(res0.a_cp, res0.a_clk, g));

    // (e) compose the presence up to host level
    //     rf-side path presence to A1, transported onto the reconstructed banks
    assert forall c: nat :: c in PIV.CapIdsOutsideLooks(host) ==>
                              AI.get_idx(rfA.capture_regs.a_clk, CP.start_reg(c)) == AI.get_idx(res0.a_clk, CP.start_reg(c))
    by {
      forall c: nat | c in PIV.CapIdsOutsideLooks(host)
        ensures AI.get_idx(rfA.capture_regs.a_clk, CP.start_reg(c)) == AI.get_idx(res0.a_clk, CP.start_reg(c))
      {
        assert CP.start_reg(c) in PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(host));
        assert rfA.capture_regs == rfFresh.value.capture_regs;
      }
    }
    assert forall q0: nat :: q0 in PIV.QuantIdsOutsideLooks(host) ==>
                               AI.get_idx(rfA.quant_regs.a_clk, q0 as int) == AI.get_idx(res2.a_clk, q0 as int)
    by {
      forall q0: nat | q0 in PIV.QuantIdsOutsideLooks(host)
        ensures AI.get_idx(rfA.quant_regs.a_clk, q0 as int) == AI.get_idx(res2.a_clk, q0 as int)
      {
        assert (q0 as int) in M.QIdsOuter(host);
        assert rfA.quant_regs == rfFresh.value.quant_regs;
      }
    }
    NI.LookPathPresentAgreeTop(host, rfA.capture_regs.a_clk, rfA.quant_regs.a_clk,
                               res0.a_clk, res2.a_clk, -1, A1);
    assert NI.LookPathPresent(host, res0.a_clk, res2.a_clk, -1, A1);
    assert NI.MxAtLidLk(host, res2.a_clk, -1, A1) == NI.MxAtLidLk(host, rfA.quant_regs.a_clk, -1, A1);
    NI.LookPathPresentLkFromPresentTop(host, res0.a_clk, res1.a_clk, res2.a_clk, -1, A1);
    assert NI.LookPathPresentLk(host, res0.a_clk, res1.a_clk, res2.a_clk, -1, A1);
    assert AI.get_idx(res1.a_clk, A1 as int) >= 0 by {
      assert AI.get_idx(res1.a_clk, A1 as int) == AI.get_idx(rfFresh.value.look_regs.a_clk, A1 as int);
      assert AI.get_idx(rfA.look_regs.a_clk, A1 as int) >= 0;
    }
    assert AI.get_idx(res1.a_clk, A1 as int) >= NI.MxAtLidLk(host, res2.a_clk, -1, A1) by {
      assert AI.get_idx(res1.a_clk, A1 as int) == L1;
      assert L1 >= NI.MxAtLidLk(host, rfA.quant_regs.a_clk, -1, A1);
    }
    NI.LookPathComposeNested(host, bodyA1, res0.a_clk, res1.a_clk, res2.a_clk, -1, A1, g);
    assert PIV.PathPresentLk(host, res0.a_clk, res1.a_clk, res2.a_clk, -1, g);
    assert PIV.MxAtGidLk(host, res0.a_clk, res1.a_clk, res2.a_clk, -1, g)
        == PIV.MxAtGidLk(bodyA1, res0.a_clk, res1.a_clk, res2.a_clk, -1, g);

    // (f) the value chain (NormRange-form): lsubA[g] == gmtH[g] == lsub1[g] == LiveRange(res0, g)
    assert PIV.NormRange(lsubA.value[g]) == PIV.NormRange(PIV.LiveRange(res0.a_cp, res0.a_clk, g));
  }

  lemma ForwardFindRecLB(
    rer: LW.RegExpRecord, qm: AR.QMap, crv: CP.FCompiled, str: string, ast: R.regex, re: R.regex,
    ov: LOr.OracleView, res0: AReg.Regs, res1: AReg.Regs, res2: AReg.Regs,
    host: R.regex, A: nat, g: nat, ncap: int, nlook: int, nquant: int)
    // ---- whole-regex statics (fixed) ----
    requires T.TransWf(re) && NR.NestedFragmentRE(re) && NR.L5ScopeRE(re) && L5ScopeV1RE(re)
    requires PIV.CapUnique(re) && PIV.QuantUnique(re) && LTB.LookUnique(re)
    requires LTB.LookTablesOk(re, crv)
    requires |crv.f_look_types| == |crv.f_look_ast|
    requires forall x: nat :: x in LTB.LookIds(re) ==> 1 <= x <= R.max_lookaround(ast)
    requires forall x: nat :: x in LTB.LookIds(re) ==> (x as int) in qm.looks
    requires nlook == R.max_lookaround(ast) + 1
    requires qm.ov == ov && !rer.multiline && !rer.ignoreCase && |ov| == |str| + 1
    requires forall l: int :: l in qm.looks ==> l >= 0
    requires forall cp: nat :: cp <= |str| ==> LL.OracleOkSuffix(rer, qm, PIV.InpOfCp(str, cp))
    requires GateStaticsOkNested(qm, re, crv, ncap, nlook, nquant)
    requires forall l: int, la: R.lookaround, b: R.regex ::
               1 <= l <= R.max_lookaround(ast) && LTB.LookEntryOk(crv, l, la, b) ==>
                 M.FrameEntryOk(crv, la, b, PIV.CaptureRegsSet(PIV.CapIdsInLooks(re)), M.LookIdSet(re))
    requires forall c: nat :: c in PIV.CapIdsInLooks(re) ==> M.GNotUnderQuantL(T.Translate(re), c)
    // ---- global res-side facts ----
    requires |res1.a_cp| == nlook && |res1.a_clk| == nlook
    requires CM.LookCpSetWithClk(res1) && CM.LookCpsLE(res1, |str|)
    requires M.FLookLoopChildLinkOk(crv, str, res1, 1, R.max_lookaround(ast), ov, ncap, nlook, nquant)
    requires M.FLookLoopValueOkFull(crv, str, res0, res1, 1, R.max_lookaround(ast), ov, ncap, nlook, nquant)
    requires M.FLookLoopQuantValueOkFull(crv, str, res2, res1, 1, R.max_lookaround(ast), ov, ncap, nlook, nquant)
    // ---- per-level data ----
    requires A in LTB.LookIds(re)
    requires host == NI.LookBodyOfRE(re, A)
    requires M.MatchedPosLA(crv, res1, A as int)
    requires g in PIV.CapIds(host) && g in PIV.CapIdsInLooks(re)
    requires var lsub := SubFirstLeafAt(rer, crv, str, A as int, res1);
             lsub.Some? && g in lsub.value
    ensures PIV.PathPresentLk(host, res0.a_clk, res1.a_clk, res2.a_clk, -1, g)
    ensures AI.get_idx(res0.a_clk, CP.start_reg(g)) >= 0
    ensures AI.get_idx(res0.a_cp, CP.start_reg(g)) >= 0
    ensures AI.get_idx(res0.a_clk, CP.start_reg(g))
         >= PIV.MxAtGidLk(host, res0.a_clk, res1.a_clk, res2.a_clk, -1, g)
    // (L5 F7c-4) the value tie is stated as a `NormRange` equality so that the
    // backward fresh match's reversed read (LB arm) and the forward read (LA
    // arm) chain uniformly; `NormSwapCong` absorbs the LB swap.
    ensures PIV.NormRange(SubFirstLeafAt(rer, crv, str, A as int, res1).value[g])
         == PIV.NormRange(PIV.LiveRange(res0.a_cp, res0.a_clk, g))
    requires crv.f_look_types[A as int].Lookbehind?
    decreases |LTB.LookIds(host)|, 1
  {
    var maxlook := R.max_lookaround(ast);
    var cpA := AReg.get_cp(res1, A as int).value;
    RL.AAsArraysLaws(res1);
    assert AI.get_idx(res1.a_cp, A as int) >= 0 && cpA == AI.get_idx(res1.a_cp, A as int);
    assert 0 <= cpA <= |str|;                                    // LookCpsLE(res1)
    var inpA := PIV.InpOfCp(str, cpA);
    var bodycode := CP.compile_to_bytecode(host);

    // ---- the row at A (VERBATIM DeepFindRec) ----
    assert 1 <= A <= maxlook && (A as int) in qm.looks;
    assert GateStaticAtNested(qm, re, crv, A as int, ncap, nlook, nquant);
    var laA: R.lookaround, bA: R.regex :|
      LTB.LookEntryOk(crv, A as int, laA, bA)
      && T.TransWf(bA) && NR.NestedFragmentRE(bA)
      && NR.NegLooksLookFreeRE(bA)
      && (laA.Lookbehind? ==> NR.LBOnlyLooksRE(bA))
      && (!laA.Lookbehind? ==> L5ScopeV1RE(bA))
      && qm.looks[A as int].0 == T.TrLookaround(laA)
      && qm.looks[A as int].1 == T.Translate(bA)
      && (set g0: LG.GroupId | g0 in L.DefGroups(T.Translate(bA))) <= PIV.CapIdsInLooks(re)
      && var bc := CP.compile_to_bytecode(bA);
      |bc| >= 1
      && PSM.StaticOkNestedRE(qm, bA, bc, |bc| - 1)
      && PSM.SizesOkRE(bA, ncap, nlook, nquant)
      && ((laA.NegLookbehind? || laA.NegLookahead?) ==> NR.CaptureFreeRE(bA));
    NI.LookBodyOfTablesTie(re, crv, A);
    var laT: R.lookaround :| LTB.LookEntryOk(crv, A as int, laT, NI.LookBodyOfRE(re, A));
    assert bA == host by { assert crv.f_look_ast[A as int] == bA == host; }
    assert host == M.VBody(crv, A as int);
    var endlH: nat := |bodycode| - 1;
    assert PSM.StaticOkNestedRE(qm, host, bodycode, endlH);
    assert crv.f_look_types[A as int] == laA;
    assert (laA.Lookahead? || laA.Lookbehind?) by {
      assert AI.capture_type(crv.f_look_types[A as int]);        // MatchedPosLA
    }
    assert laA.Lookbehind? by { assert crv.f_look_types[A as int] == laA; }
    if g !in PIV.CapIdsInLooks(host) {
      // (perf) the BASE arm lives in its own lemma.
      ForwardFindRecLBBase(rer, qm, crv, str, ast, re, ov, res0, res1, res2,
                           host, A, g, ncap, nlook, nquant);
    } else {
      // (perf) the DEEP arm lives in its own lemma.
      ForwardFindRecLBDeep(rer, qm, crv, str, ast, re, ov, res0, res1, res2,
                           host, A, g, ncap, nlook, nquant);
    }
  }

  /** (perf) The FORWARD DEEP arm of `ForwardFindRec`, extracted so its assertions are
      checked in a small context (same treatment as `ForwardFindRecLB`).
      Mutually recursive with `ForwardFindRec` on `(|LookIds(host)|, arm)`. */
  lemma ForwardFindRecFwdDeep(
    rer: LW.RegExpRecord, qm: AR.QMap, crv: CP.FCompiled, str: string, ast: R.regex, re: R.regex,
    ov: LOr.OracleView, res0: AReg.Regs, res1: AReg.Regs, res2: AReg.Regs,
    host: R.regex, A: nat, g: nat, ncap: int, nlook: int, nquant: int)
    // ---- whole-regex statics (fixed) ----
    requires T.TransWf(re) && NR.NestedFragmentRE(re) && NR.L5ScopeRE(re) && L5ScopeV1RE(re)
    requires PIV.CapUnique(re) && PIV.QuantUnique(re) && LTB.LookUnique(re)
    requires LTB.LookTablesOk(re, crv)
    requires |crv.f_look_types| == |crv.f_look_ast|
    requires forall x: nat :: x in LTB.LookIds(re) ==> 1 <= x <= R.max_lookaround(ast)
    requires forall x: nat :: x in LTB.LookIds(re) ==> (x as int) in qm.looks
    requires nlook == R.max_lookaround(ast) + 1
    requires qm.ov == ov && !rer.multiline && !rer.ignoreCase && |ov| == |str| + 1
    requires forall l: int :: l in qm.looks ==> l >= 0
    requires forall cp: nat :: cp <= |str| ==> LL.OracleOkSuffix(rer, qm, PIV.InpOfCp(str, cp))
    requires GateStaticsOkNested(qm, re, crv, ncap, nlook, nquant)
    requires forall l: int, la: R.lookaround, b: R.regex ::
               1 <= l <= R.max_lookaround(ast) && LTB.LookEntryOk(crv, l, la, b) ==>
                 M.FrameEntryOk(crv, la, b, PIV.CaptureRegsSet(PIV.CapIdsInLooks(re)), M.LookIdSet(re))
    requires forall c: nat :: c in PIV.CapIdsInLooks(re) ==> M.GNotUnderQuantL(T.Translate(re), c)
    // ---- global res-side facts ----
    requires |res1.a_cp| == nlook && |res1.a_clk| == nlook
    requires CM.LookCpSetWithClk(res1) && CM.LookCpsLE(res1, |str|)
    requires M.FLookLoopChildLinkOk(crv, str, res1, 1, R.max_lookaround(ast), ov, ncap, nlook, nquant)
    requires M.FLookLoopValueOkFull(crv, str, res0, res1, 1, R.max_lookaround(ast), ov, ncap, nlook, nquant)
    requires M.FLookLoopQuantValueOkFull(crv, str, res2, res1, 1, R.max_lookaround(ast), ov, ncap, nlook, nquant)
    // ---- per-level data ----
    requires A in LTB.LookIds(re)
    requires host == NI.LookBodyOfRE(re, A)
    requires M.MatchedPosLA(crv, res1, A as int)
    requires g in PIV.CapIds(host) && g in PIV.CapIdsInLooks(re)
    requires var lsub := SubFirstLeafAt(rer, crv, str, A as int, res1);
             lsub.Some? && g in lsub.value
    ensures PIV.PathPresentLk(host, res0.a_clk, res1.a_clk, res2.a_clk, -1, g)
    ensures AI.get_idx(res0.a_clk, CP.start_reg(g)) >= 0
    ensures AI.get_idx(res0.a_cp, CP.start_reg(g)) >= 0
    ensures AI.get_idx(res0.a_clk, CP.start_reg(g))
         >= PIV.MxAtGidLk(host, res0.a_clk, res1.a_clk, res2.a_clk, -1, g)
    // (L5 F7c-4) the value tie is stated as a `NormRange` equality so that the
    // backward fresh match's reversed read (LB arm) and the forward read (LA
    // arm) chain uniformly; `NormSwapCong` absorbs the LB swap.
    ensures PIV.NormRange(SubFirstLeafAt(rer, crv, str, A as int, res1).value[g])
         == PIV.NormRange(PIV.LiveRange(res0.a_cp, res0.a_clk, g))
    requires !crv.f_look_types[A as int].Lookbehind?
    requires g in PIV.CapIdsInLooks(host)
    decreases |LTB.LookIds(host)|, 0
  {
    var maxlook := R.max_lookaround(ast);
    var cpA := AReg.get_cp(res1, A as int).value;
    RL.AAsArraysLaws(res1);
    assert AI.get_idx(res1.a_cp, A as int) >= 0 && cpA == AI.get_idx(res1.a_cp, A as int);
    assert 0 <= cpA <= |str|;                                    // LookCpsLE(res1)
    var inpA := PIV.InpOfCp(str, cpA);
    var bodycode := CP.compile_to_bytecode(host);

    // ---- the row at A (VERBATIM DeepFindRec) ----
    assert 1 <= A <= maxlook && (A as int) in qm.looks;
    assert GateStaticAtNested(qm, re, crv, A as int, ncap, nlook, nquant);
    var laA: R.lookaround, bA: R.regex :|
      LTB.LookEntryOk(crv, A as int, laA, bA)
      && T.TransWf(bA) && NR.NestedFragmentRE(bA)
      && NR.NegLooksLookFreeRE(bA)
      && (laA.Lookbehind? ==> NR.LBOnlyLooksRE(bA))
      && (!laA.Lookbehind? ==> L5ScopeV1RE(bA))
      && qm.looks[A as int].0 == T.TrLookaround(laA)
      && qm.looks[A as int].1 == T.Translate(bA)
      && (set g0: LG.GroupId | g0 in L.DefGroups(T.Translate(bA))) <= PIV.CapIdsInLooks(re)
      && var bc := CP.compile_to_bytecode(bA);
      |bc| >= 1
      && PSM.StaticOkNestedRE(qm, bA, bc, |bc| - 1)
      && PSM.SizesOkRE(bA, ncap, nlook, nquant)
      && ((laA.NegLookbehind? || laA.NegLookahead?) ==> NR.CaptureFreeRE(bA));
    NI.LookBodyOfTablesTie(re, crv, A);
    var laT: R.lookaround :| LTB.LookEntryOk(crv, A as int, laT, NI.LookBodyOfRE(re, A));
    assert bA == host by { assert crv.f_look_ast[A as int] == bA == host; }
    assert host == M.VBody(crv, A as int);
    var endlH: nat := |bodycode| - 1;
    assert PSM.StaticOkNestedRE(qm, host, bodycode, endlH);
    assert crv.f_look_types[A as int] == laA;
    assert (laA.Lookahead? || laA.Lookbehind?) by {
      assert AI.capture_type(crv.f_look_types[A as int]);        // MatchedPosLA
    }
    assert !laA.Lookbehind? by { assert crv.f_look_types[A as int] == laA; }
    assert M.FrameEntryOk(crv, laA, host,
                          PIV.CaptureRegsSet(PIV.CapIdsInLooks(re)), M.LookIdSet(re));
    assert PIV.CapUnique(host) && PIV.QuantUnique(host) && LTB.LookUnique(host)
           && LTB.LookTablesOk(host, crv);                          // FrameEntryOk

    // ---- rf_A: the fresh body match at res1's position (Some via the replay
    //      None-iff — the leaf EXISTS by hypothesis) ----
    var qmB := AR.QMap(qm.quants,
                       map l: int | l in qm.looks && l >= 0 && (l as nat) in LTB.LookIds(host) :: qm.looks[l],
                       qm.ov);
    assert AR.QmapOk(host, qmB) by { QmapOkLooksIrrel(host, qm, qmB); }
    assert AR.LmapOk(host, qmB) by { LmapOkRestrict(host, qm, qmB); }
    assert PSM.StaticOkNestedRE(qmB, host, bodycode, endlH) by {
      assert PSM.StaticOkNestedRE(qm, host, bodycode, endlH);
    }
    assert LL.OracleOkSuffix(rer, qmB, inpA) by {
      assert LL.OracleOkSuffix(rer, qm, inpA);
      OracleOkSuffixRestrict(rer, qm, qmB, inpA);
    }
    assert GateStaticsOkNested(qmB, host, crv, ncap, nlook, nquant) by {
      L5ScopeV1LookBody(re, A);          // (L5 F7f) the v1 scope descends to the body
      GateStaticsFromTablesNested(qmB, host, crv, ncap, nlook, nquant);
    }
    assert OE.OracleColsOk(rer, qmB, str) by {                         // (L5 F7d)
      SufForallToColsOk(rer, qm, str);
      OracleColsOkRestrict(rer, qm, qmB, str);
    }
    var cdnA := crv.f_look_cdns[A as int];
    LookNestBackTFromBodyReplay(rer, qmB, laA, host, bodycode, endlH, 0, crv, str, cpA, ov,
                                cdnA, crv.f_plus_bc, ncap, nlook, nquant);
    var t := LFU.ComputeTr(rer, [LS.Areg(T.Translate(host))], inpA, LG.Empty, WP.Forward);
    var rfP := AI.FFindMatchPlus(bodycode, host, crv.f_plus_bc, str, ov, LAnc.Forward, cpA,
                                 AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant),
                                 0, cdnA).0;
    // the leaf exists (hypothesis) — unfold SubFirstLeafAt to FirstLeaf(t)
    assert LT.FirstLeaf(t, inpA) == LT.TreeRes(t, LG.Empty, inpA, WP.Forward);
    assert LidDir(crv, A as int) == WP.Forward by { assert crv.f_look_types[A as int] == laA; }   // laA.Lookahead? (dispatch)
    var lsubA := SubFirstLeafAt(rer, crv, str, A as int, res1);
    assert lsubA.Some? && lsubA.value == LT.FirstLeaf(t, inpA).value.1 && LT.FirstLeaf(t, inpA).Some?;
    assert rfP.Some?;                                            // None-iff
    var rfA := rfP.value;
    var Sh := PIV.CapIdsInLooks(host);
    var gmtH := LT.FirstLeaf(t, inpA).value.1;
    assert gmtH == lsubA.value;

    // rf_A IS FreshBodyMatch(A, res1) (identity block, VERBATIM DeepFindRec (ζ))
    var rfFresh := M.FreshBodyMatch(crv, str, A as int, res1, ov, ncap, nlook, nquant);
    assert rfFresh == AI.FFindMatch(bodycode, str,
                                    AI.FInitState(bodycode, cpA, AReg.init_regs(ncap), AReg.init_regs(nlook),
                                                  AReg.init_regs(nquant), 0, AI.cp_context(cpA, str, LAnc.Forward)),
                                    ov, LAnc.Forward, cdnA).0 by {
      assert AI.capture_direction(crv.f_look_types[A as int]) == LAnc.Forward;
      assert CP.capture_regex(crv.f_look_types[A as int], M.VBody(crv, A as int)) == host;
    }
    assert rfA == rfFresh.value by {
      var ctxF := AI.cp_context(cpA, str, LAnc.Forward);
      var initsF := AI.FInitState(bodycode, cpA, AReg.init_regs(ncap), AReg.init_regs(nlook),
                                  AReg.init_regs(nquant), 0, ctxF);
      M.NoTrueQuantStampNested(host);
      assert M.VmQuantFinal(initsF) by {
        var th0 := AI.init_thread(AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant));
        assert M.QuantRegsFinal(th0) by {
          RL.AInitLaws(nquant);
          forall k ensures AI.get_idx(AReg.init_regs(nquant).a_cp, k) < 0
                           && AI.get_idx(AReg.init_regs(nquant).a_clk, k) >= -1 {
            if 0 <= k < nquant { }
          }
        }
        forall t2 | t2 in initsF.active ensures M.QuantRegsFinal(t2) { assert t2 == th0; }
      }
      M.FFindMatchQuantFinalAny(bodycode, str, initsF, ov, LAnc.Forward, cdnA);
      var (fm, ovx) := AI.FFindMatch(bodycode, str, initsF, ov, LAnc.Forward, cdnA);
      assert fm == rfFresh by { assert rfFresh == AI.FFindMatch(bodycode, str, initsF, ov, LAnc.Forward, cdnA).0; }
      assert fm.Some?;
      assert M.QuantRegsFinal(fm.value);
      M.FNulledPlusIdentity(host, fm.value.capture_regs, fm.value.look_regs, fm.value.quant_regs,
                            crv.f_plus_bc, str, ovx, LAnc.Forward);
      assert AI.FReconstructPlus(fm.value, host, crv.f_plus_bc, str, ovx, LAnc.Forward).0 == fm.value;
    }
    assert rfFresh.Some?;

    // the FLookLoop value/quant lifts at owner == A
    assert CM.RegsAgreeInside(res0, rfFresh.value.capture_regs,
                              PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(host))) by {
      assert 1 <= A as int <= maxlook && M.MatchedPosLA(crv, res1, A as int);
      assert M.VBody(crv, A as int) == host;
    }
    assert CM.RegsAgreeInside(res2, rfFresh.value.quant_regs, M.QIdsOuter(host)) by {
      assert 1 <= A as int <= maxlook && M.MatchedPosLA(crv, res1, A as int);
    }
    // the fragment scope at host
    GNotUnderQuantLLookBody(re, A, g);
    assert M.GNotUnderQuantL(T.Translate(host), g);

    // ==== DEEP: descend through g's top-in-host ancestor A1 ====
    var ownH := NI.InnermostOwnerDirect(host, g);
    var A1 := ReconLiveTopAncestor(host, g, ownH);
    assert A1 in NI.TopLookIds(host) && A1 in LTB.LookIds(host)
           && g in PIV.CapIds(NI.LookBodyOfRE(host, A1));
    NI.LookBodyLookIdsIn(re, A);
    assert A1 in LTB.LookIds(re);
    NI.LookBodyCompose(re, A, A1);
    var bodyA1 := NI.LookBodyOfRE(re, A1);
    assert bodyA1 == NI.LookBodyOfRE(host, A1);

    // (a) the FORWARD carrier at A1 (leaf-witness g): crossed + dominant on rf_A
    assert LookNestOkTTop(host, Sh, gmtH, rfA);
    assert g in Sh && g in gmtH && g in PIV.CapIds(NI.LookBodyOfRE(host, A1));
    assert NI.LookPathPresent(host, rfA.capture_regs.a_clk, rfA.quant_regs.a_clk, -1, A1)
           && AI.get_idx(rfA.look_regs.a_clk, A1 as int) >= 0
           && AI.get_idx(rfA.look_regs.a_clk, A1 as int)
              >= NI.MxAtLidLk(host, rfA.quant_regs.a_clk, -1, A1);
    var L1 := AI.get_idx(rfA.look_regs.a_clk, A1 as int);
    NI.LookPathDomIntroTop(host, rfA.capture_regs.a_clk, rfA.quant_regs.a_clk, -1, A1, L1);
    assert NI.LookPathDom(host, L1, rfA.quant_regs.a_clk, A1);
    // A1 matched on rf_A (forward invariant: clk set => cp set on the fresh run)
    assert CM.LookCpSetWithClk(rfA.look_regs);
    assert AI.get_idx(rfA.look_regs.a_cp, A1 as int) >= 0;
    assert AReg.get_cp(rfA.look_regs, A1 as int).Some?;        // get_idx >= 0 ==> in-range, Some
    assert M.MatchedPosLA(crv, rfA.look_regs, A1 as int) by {
      assert GateStaticAtNested(qm, re, crv, A1 as int, ncap, nlook, nquant);
      // (2026-08-25) full conjunct list (a subset timed out under {:isolate_assertions})
      var la1: R.lookaround, b1: R.regex :|
        LTB.LookEntryOk(crv, A1 as int, la1, b1)
        && T.TransWf(b1) && NR.NestedFragmentRE(b1)
        && NR.NegLooksLookFreeRE(b1)
        && (la1.Lookbehind? ==> NR.LBOnlyLooksRE(b1))
        && (!la1.Lookbehind? ==> L5ScopeV1RE(b1))
        && qm.looks[A1 as int].0 == T.TrLookaround(la1)
        && qm.looks[A1 as int].1 == T.Translate(b1)
        && (set gx: LG.GroupId | gx in L.DefGroups(T.Translate(b1))) <= PIV.CapIdsInLooks(re)
        && var bodycode1 := CP.compile_to_bytecode(b1);
        |bodycode1| >= 1
        && PSM.StaticOkNestedRE(qm, b1, bodycode1, |bodycode1| - 1)
        && PSM.SizesOkRE(b1, ncap, nlook, nquant)
        && ((la1.NegLookbehind? || la1.NegLookahead?) ==> NR.CaptureFreeRE(b1));
      assert crv.f_look_types[A1 as int] == la1;
      assert b1 == bodyA1 by {
        NI.LookBodyOfTablesTie(re, crv, A1);
        var la1T: R.lookaround :| LTB.LookEntryOk(crv, A1 as int, la1T, bodyA1);
        assert crv.f_look_ast[A1 as int] == b1 == bodyA1;
      }
      assert la1.Lookahead? || la1.Lookbehind? by {                        // (L5 F7c-4) kind dispatch:
        if la1.NegLookahead? || la1.NegLookbehind? {                        // an inner lid of a lookAHEAD
          assert NR.CaptureFreeRE(bodyA1);                                   // host may be a LOOKBEHIND
          PIV.CaptureFreeNoCapIds(bodyA1);                                   // under the L5 scope
          assert g in PIV.CapIds(bodyA1);
          assert false;
        }
      }
      assert AI.capture_type(crv.f_look_types[A1 as int]);
    }

    // (b) the ⊆ direction of the REGION-EQUALITY deep carrier at A1 needs
    //     A1's sub-leaf to EXIST — from the fresh run's oracle-true records,
    //     in the inner lid's OWN direction (`LidDir`, L5 F7c-4).
    var ctxF := AI.cp_context(cpA, str, LAnc.Forward);
    var initsF := AI.FInitState(bodycode, cpA, AReg.init_regs(ncap), AReg.init_regs(nlook),
                                AReg.init_regs(nquant), 0, ctxF);
    assert CM.VmLookOracleTrue(initsF, ov) by {
      RL.AInitLaws(nlook);
      forall l: int | AI.get_idx(AReg.init_regs(nlook).a_cp, l) >= 0
        ensures LOr.view_get_oracle(ov, AI.get_idx(AReg.init_regs(nlook).a_cp, l), l)
      {
        if 0 <= l < nlook { assert AReg.init_regs(nlook).a_cp[l] == -1; }
      }
    }
    M.NoWriteOracleBodyCodeNested(host);
    assert ctxF.nextchar == AI.get_char(str, cpA);
    CM.FFindMatchLookOracleTrue(bodycode, str, initsF, ov, LAnc.Forward, cdnA);
    assert CM.LookCpsOracleTrue(rfA.look_regs, ov) by {
      assert rfA == rfFresh.value;
    }
    var cp1 := AReg.get_cp(rfA.look_regs, A1 as int).value;
    assert cp1 == AI.get_idx(rfA.look_regs.a_cp, A1 as int);
    assert LOr.view_get_oracle(ov, cp1, A1 as int);
    assert 0 <= cp1 <= |str| by {
      M.ReplayLookCpOkNested(bodycode, str, ov, LAnc.Forward, cdnA, crv.f_plus_bc, cpA,
                             AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant), host);
      assert CM.LookCpsLE(rfA.look_regs, |str|);
    }
    var inp1 := PIV.InpOfCp(str, cp1);
    assert T.TransWf(bodyA1) by { M.TransWfLookBodyOfRE(re, A1); }   // (2026-08-25) hoisted above the Translate use
    var dir1 := LidDir(crv, A1 as int);
    var t1 := LFU.ComputeTr(rer, [LS.Areg(T.Translate(bodyA1))], inp1, LG.Empty, dir1);
    assert LT.TreeRes(t1, LG.Empty, inp1, dir1).Some? by {
      assert LL.OracleOkSuffix(rer, qm, inp1);
      assert LL.OracleOkAt(rer, qm, inp1);
      assert (A1 as int) in qm.looks;
      assert GateStaticAtNested(qm, re, crv, A1 as int, ncap, nlook, nquant);
      var la1G: R.lookaround, b1G: R.regex :| LTB.LookEntryOk(crv, A1 as int, la1G, b1G)
                                              && T.TransWf(b1G) && NR.NestedFragmentRE(b1G)
                                              && NR.NegLooksLookFreeRE(b1G)
                                              && (la1G.Lookbehind? ==> NR.LBOnlyLooksRE(b1G))
                                              && (!la1G.Lookbehind? ==> L5ScopeV1RE(b1G))
                                              && qm.looks[A1 as int].0 == T.TrLookaround(la1G)
                                              && qm.looks[A1 as int].1 == T.Translate(b1G)
                                              && (set gx: LG.GroupId | gx in L.DefGroups(T.Translate(b1G))) <= PIV.CapIdsInLooks(re)
                                              && var bc1 := CP.compile_to_bytecode(b1G);
                                              |bc1| >= 1
                                              && PSM.StaticOkNestedRE(qm, b1G, bc1, |bc1| - 1)
                                              && PSM.SizesOkRE(b1G, ncap, nlook, nquant)
                                              && ((la1G.NegLookbehind? || la1G.NegLookahead?) ==> NR.CaptureFreeRE(b1G));
      assert b1G == bodyA1 by {
        NI.LookBodyOfTablesTie(re, crv, A1);
        var la1T: R.lookaround :| LTB.LookEntryOk(crv, A1 as int, la1T, bodyA1);
        assert crv.f_look_ast[A1 as int] == b1G == bodyA1;
      }
      assert crv.f_look_types[A1 as int] == la1G && dir1 == L.LkDir(T.TrLookaround(la1G)) by {
        assert M.MatchedPosLA(crv, rfA.look_regs, A1 as int);
        assert AI.capture_type(crv.f_look_types[A1 as int]);
      }
      assert TREP.CpOf(inp1) == cp1 by { LS.ReverseLength(str[..cp1]); }
      assert LT.TreeRes(LFU.ComputeTr(rer, [LS.Areg(T.Translate(bodyA1))], inp1, LG.Empty, dir1),
                        LG.Empty, inp1, dir1).Some?;
    }
    var lsub1rf := SubFirstLeafAt(rer, crv, str, A1 as int, rfA.look_regs);
    assert bodyA1 == M.VBody(crv, A1 as int) by {
      NI.LookBodyOfTablesTie(re, crv, A1);
      var la1T: R.lookaround :| LTB.LookEntryOk(crv, A1 as int, la1T, bodyA1);
    }
    assert lsub1rf.Some? && lsub1rf.value == LT.TreeRes(t1, LG.Empty, inp1, dir1).value.1 by {
      assert AReg.get_cp(rfA.look_regs, A1 as int) == Some(cp1 as int);
    }
    // the carrier: region equality at A1 — the ⊆ direction pushes g in, the
    // ⊇ direction's value clause gives the value tie.
    assert LookNestBackTTopDeep(rer, host, crv, str, ov, Sh, gmtH, rfA, ncap, nlook, nquant);
    assert g in lsub1rf.value && gmtH[g] == lsub1rf.value[g] by {
      assert g in gmtH;
    }

    // (c) LEVEL-LINK: re-key A1's sub-leaf onto res1
    TopEqDirectLookIds(host);
    assert A1 as int in M.DirectLidSet(host) by { assert A1 in M.DirectLookIds(host); }
    assert AReg.get_cp(res1, A1 as int) == AReg.get_cp(rfFresh.value.look_regs, A1 as int)
           && AI.get_idx(res1.a_clk, A1 as int) == AI.get_idx(rfFresh.value.look_regs.a_clk, A1 as int) by {
      assert M.FLookLoopChildLinkOk(crv, str, res1, 1, maxlook, ov, ncap, nlook, nquant);
      assert 1 <= A as int <= maxlook && M.MatchedPosLA(crv, res1, A as int);
      assert rfFresh.Some?;
    }
    var lsub1 := SubFirstLeafAt(rer, crv, str, A1 as int, res1);
    assert lsub1 == lsub1rf;                                   // reads only get_cp at A1
    assert M.MatchedPosLA(crv, res1, A1 as int) by {
      assert AReg.get_cp(res1, A1 as int).Some?;
    }

    // (d) RECURSE at (bodyA1, A1)
    assert |LTB.LookIds(bodyA1)| < |LTB.LookIds(host)| by {
      NI.LookBodyLookIdsIn(host, A1);
      LookIdNotInOwnBody(host, A1);
      SubsetCardLt(LTB.LookIds(bodyA1), LTB.LookIds(host), A1);
    }
    assert g in PIV.CapIds(bodyA1) && g in lsub1.value;
    ForwardFindRec(rer, qm, crv, str, ast, re, ov, res0, res1, res2,
                   bodyA1, A1, g, ncap, nlook, nquant);
    assert PIV.PathPresentLk(bodyA1, res0.a_clk, res1.a_clk, res2.a_clk, -1, g);
    assert AI.get_idx(res0.a_clk, CP.start_reg(g)) >= 0
           && AI.get_idx(res0.a_cp, CP.start_reg(g)) >= 0;
    assert AI.get_idx(res0.a_clk, CP.start_reg(g))
        >= PIV.MxAtGidLk(bodyA1, res0.a_clk, res1.a_clk, res2.a_clk, -1, g);
    assert PIV.NormRange(lsub1.value[g]) == PIV.NormRange(PIV.LiveRange(res0.a_cp, res0.a_clk, g));

    // (e) compose the presence up to host level
    //     rf-side path presence to A1, transported onto the reconstructed banks
    assert forall c: nat :: c in PIV.CapIdsOutsideLooks(host) ==>
                              AI.get_idx(rfA.capture_regs.a_clk, CP.start_reg(c)) == AI.get_idx(res0.a_clk, CP.start_reg(c))
    by {
      forall c: nat | c in PIV.CapIdsOutsideLooks(host)
        ensures AI.get_idx(rfA.capture_regs.a_clk, CP.start_reg(c)) == AI.get_idx(res0.a_clk, CP.start_reg(c))
      {
        assert CP.start_reg(c) in PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(host));
        assert rfA.capture_regs == rfFresh.value.capture_regs;
      }
    }
    assert forall q0: nat :: q0 in PIV.QuantIdsOutsideLooks(host) ==>
                               AI.get_idx(rfA.quant_regs.a_clk, q0 as int) == AI.get_idx(res2.a_clk, q0 as int)
    by {
      forall q0: nat | q0 in PIV.QuantIdsOutsideLooks(host)
        ensures AI.get_idx(rfA.quant_regs.a_clk, q0 as int) == AI.get_idx(res2.a_clk, q0 as int)
      {
        assert (q0 as int) in M.QIdsOuter(host);
        assert rfA.quant_regs == rfFresh.value.quant_regs;
      }
    }
    NI.LookPathPresentAgreeTop(host, rfA.capture_regs.a_clk, rfA.quant_regs.a_clk,
                               res0.a_clk, res2.a_clk, -1, A1);
    assert NI.LookPathPresent(host, res0.a_clk, res2.a_clk, -1, A1);
    assert NI.MxAtLidLk(host, res2.a_clk, -1, A1) == NI.MxAtLidLk(host, rfA.quant_regs.a_clk, -1, A1);
    NI.LookPathPresentLkFromPresentTop(host, res0.a_clk, res1.a_clk, res2.a_clk, -1, A1);
    assert NI.LookPathPresentLk(host, res0.a_clk, res1.a_clk, res2.a_clk, -1, A1);
    assert AI.get_idx(res1.a_clk, A1 as int) >= 0 by {
      assert AI.get_idx(res1.a_clk, A1 as int) == AI.get_idx(rfFresh.value.look_regs.a_clk, A1 as int);
      assert AI.get_idx(rfA.look_regs.a_clk, A1 as int) >= 0;
    }
    assert AI.get_idx(res1.a_clk, A1 as int) >= NI.MxAtLidLk(host, res2.a_clk, -1, A1) by {
      assert AI.get_idx(res1.a_clk, A1 as int) == L1;
      assert L1 >= NI.MxAtLidLk(host, rfA.quant_regs.a_clk, -1, A1);
    }
    NI.LookPathComposeNested(host, bodyA1, res0.a_clk, res1.a_clk, res2.a_clk, -1, A1, g);
    assert PIV.PathPresentLk(host, res0.a_clk, res1.a_clk, res2.a_clk, -1, g);
    assert PIV.MxAtGidLk(host, res0.a_clk, res1.a_clk, res2.a_clk, -1, g)
        == PIV.MxAtGidLk(bodyA1, res0.a_clk, res1.a_clk, res2.a_clk, -1, g);

    // (f) the value chain (NormRange-form): lsubA[g] == gmtH[g] == lsub1[g] == LiveRange(res0, g)
    assert PIV.NormRange(lsubA.value[g]) == PIV.NormRange(PIV.LiveRange(res0.a_cp, res0.a_clk, g));
  }

  lemma ForwardFindRec(
    rer: LW.RegExpRecord, qm: AR.QMap, crv: CP.FCompiled, str: string, ast: R.regex, re: R.regex,
    ov: LOr.OracleView, res0: AReg.Regs, res1: AReg.Regs, res2: AReg.Regs,
    host: R.regex, A: nat, g: nat, ncap: int, nlook: int, nquant: int)
    // ---- whole-regex statics (fixed) ----
    requires T.TransWf(re) && NR.NestedFragmentRE(re) && NR.L5ScopeRE(re) && L5ScopeV1RE(re)
    requires PIV.CapUnique(re) && PIV.QuantUnique(re) && LTB.LookUnique(re)
    requires LTB.LookTablesOk(re, crv)
    requires |crv.f_look_types| == |crv.f_look_ast|
    requires forall x: nat :: x in LTB.LookIds(re) ==> 1 <= x <= R.max_lookaround(ast)
    requires forall x: nat :: x in LTB.LookIds(re) ==> (x as int) in qm.looks
    requires nlook == R.max_lookaround(ast) + 1
    requires qm.ov == ov && !rer.multiline && !rer.ignoreCase && |ov| == |str| + 1
    requires forall l: int :: l in qm.looks ==> l >= 0
    requires forall cp: nat :: cp <= |str| ==> LL.OracleOkSuffix(rer, qm, PIV.InpOfCp(str, cp))
    requires GateStaticsOkNested(qm, re, crv, ncap, nlook, nquant)
    requires forall l: int, la: R.lookaround, b: R.regex ::
               1 <= l <= R.max_lookaround(ast) && LTB.LookEntryOk(crv, l, la, b) ==>
                 M.FrameEntryOk(crv, la, b, PIV.CaptureRegsSet(PIV.CapIdsInLooks(re)), M.LookIdSet(re))
    requires forall c: nat :: c in PIV.CapIdsInLooks(re) ==> M.GNotUnderQuantL(T.Translate(re), c)
    // ---- global res-side facts ----
    requires |res1.a_cp| == nlook && |res1.a_clk| == nlook
    requires CM.LookCpSetWithClk(res1) && CM.LookCpsLE(res1, |str|)
    requires M.FLookLoopChildLinkOk(crv, str, res1, 1, R.max_lookaround(ast), ov, ncap, nlook, nquant)
    requires M.FLookLoopValueOkFull(crv, str, res0, res1, 1, R.max_lookaround(ast), ov, ncap, nlook, nquant)
    requires M.FLookLoopQuantValueOkFull(crv, str, res2, res1, 1, R.max_lookaround(ast), ov, ncap, nlook, nquant)
    // ---- per-level data ----
    requires A in LTB.LookIds(re)
    requires host == NI.LookBodyOfRE(re, A)
    requires M.MatchedPosLA(crv, res1, A as int)
    requires g in PIV.CapIds(host) && g in PIV.CapIdsInLooks(re)
    requires var lsub := SubFirstLeafAt(rer, crv, str, A as int, res1);
             lsub.Some? && g in lsub.value
    ensures PIV.PathPresentLk(host, res0.a_clk, res1.a_clk, res2.a_clk, -1, g)
    ensures AI.get_idx(res0.a_clk, CP.start_reg(g)) >= 0
    ensures AI.get_idx(res0.a_cp, CP.start_reg(g)) >= 0
    ensures AI.get_idx(res0.a_clk, CP.start_reg(g))
         >= PIV.MxAtGidLk(host, res0.a_clk, res1.a_clk, res2.a_clk, -1, g)
    // (L5 F7c-4) the value tie is stated as a `NormRange` equality so that the
    // backward fresh match's reversed read (LB arm) and the forward read (LA
    // arm) chain uniformly; `NormSwapCong` absorbs the LB swap.
    ensures PIV.NormRange(SubFirstLeafAt(rer, crv, str, A as int, res1).value[g])
         == PIV.NormRange(PIV.LiveRange(res0.a_cp, res0.a_clk, g))
    decreases |LTB.LookIds(host)|, 2
  {
    var maxlook := R.max_lookaround(ast);
    var cpA := AReg.get_cp(res1, A as int).value;
    RL.AAsArraysLaws(res1);
    assert AI.get_idx(res1.a_cp, A as int) >= 0 && cpA == AI.get_idx(res1.a_cp, A as int);
    assert 0 <= cpA <= |str|;                                    // LookCpsLE(res1)
    var inpA := PIV.InpOfCp(str, cpA);
    var bodycode := CP.compile_to_bytecode(host);

    // ---- the row at A (VERBATIM DeepFindRec) ----
    assert 1 <= A <= maxlook && (A as int) in qm.looks;
    assert GateStaticAtNested(qm, re, crv, A as int, ncap, nlook, nquant);
    var laA: R.lookaround, bA: R.regex :|
      LTB.LookEntryOk(crv, A as int, laA, bA)
      && T.TransWf(bA) && NR.NestedFragmentRE(bA)
      && NR.NegLooksLookFreeRE(bA)
      && (laA.Lookbehind? ==> NR.LBOnlyLooksRE(bA))
      && (!laA.Lookbehind? ==> L5ScopeV1RE(bA))
      && qm.looks[A as int].0 == T.TrLookaround(laA)
      && qm.looks[A as int].1 == T.Translate(bA)
      && (set g0: LG.GroupId | g0 in L.DefGroups(T.Translate(bA))) <= PIV.CapIdsInLooks(re)
      && var bc := CP.compile_to_bytecode(bA);
      |bc| >= 1
      && PSM.StaticOkNestedRE(qm, bA, bc, |bc| - 1)
      && PSM.SizesOkRE(bA, ncap, nlook, nquant)
      && ((laA.NegLookbehind? || laA.NegLookahead?) ==> NR.CaptureFreeRE(bA));
    NI.LookBodyOfTablesTie(re, crv, A);
    var laT: R.lookaround :| LTB.LookEntryOk(crv, A as int, laT, NI.LookBodyOfRE(re, A));
    assert bA == host by { assert crv.f_look_ast[A as int] == bA == host; }
    assert host == M.VBody(crv, A as int);
    var endlH: nat := |bodycode| - 1;
    assert PSM.StaticOkNestedRE(qm, host, bodycode, endlH);
    assert crv.f_look_types[A as int] == laA;
    assert (laA.Lookahead? || laA.Lookbehind?) by {
      assert AI.capture_type(crv.f_look_types[A as int]);        // MatchedPosLA
    }
    if laA.Lookbehind? {
      // (L5 F7f perf) the LOOKBEHIND arm lives in its own lemma.
      ForwardFindRecLB(rer, qm, crv, str, ast, re, ov, res0, res1, res2,
                       host, A, g, ncap, nlook, nquant);
    } else {
      assert !laA.Lookbehind? by { assert crv.f_look_types[A as int] == laA; }
      if g !in PIV.CapIdsInLooks(host) {
        // (perf) the forward BASE arm lives in its own lemma.
        ForwardFindRecFwdBase(rer, qm, crv, str, ast, re, ov, res0, res1, res2,
                              host, A, g, ncap, nlook, nquant);
      } else {
        // (perf) the forward DEEP arm lives in its own lemma.
        ForwardFindRecFwdDeep(rer, qm, crv, str, ast, re, ov, res0, res1, res2,
                              host, A, g, ncap, nlook, nquant);
      }
    }
  }

  /** (REVERSE-(c) COMPLETE) The whole-regex inside-`S` reverse value tie: every
      reconstruction-LIVE inside-look capture is in the winning LEAF. Per live
      `g`: extract the presence path (`GmOfLivePresenceExtractLkNested` output as
      hypothesis), peel `g`'s outermost TOP ancestor `A0`
      (`ReconLiveTopAncestor`); `A0` is matched+dominant on the WINNING THREAD
      (dominance by the liveness connective `LookPathDomFromLivenessThread`;
      matched by the res-side ancestor clock + reverse invariant + the res→thread
      top-look frames); the deep landing recursion (`DeepFindRec`) puts `g` in
      `A0`'s sub-first-leaf at `res1`'s position == the THREAD's recorded
      position (top-look cp frame); the whole-regex DEEP carrier
      (`DescentLandTopDeep`) lands `g` in the leaf. */
  lemma ReverseCDeepFull(
    rer: LW.RegExpRecord, qm: AR.QMap, crv: CP.FCompiled, str: string, ast: R.regex, re: R.regex,
    ov: LOr.OracleView, thread: AI.Thread, res0: AReg.Regs, res1: AReg.Regs, res2: AReg.Regs,
    S: set<LG.GroupId>, gmt: LG.GroupMap, ncap: int, nlook: int, nquant: int)
    // ---- whole-regex statics (verbatim DeepFindRec block) ----
    requires T.TransWf(re) && NR.NestedFragmentRE(re) && NR.L5ScopeRE(re) && L5ScopeV1RE(re)
    requires PIV.CapUnique(re) && PIV.QuantUnique(re) && LTB.LookUnique(re)
    requires LTB.LookTablesOk(re, crv)
    requires |crv.f_look_types| == |crv.f_look_ast|
    requires forall x: nat :: x in LTB.LookIds(re) ==> 1 <= x <= R.max_lookaround(ast)
    requires forall x: nat :: x in LTB.LookIds(re) ==> (x as int) in qm.looks
    requires nlook == R.max_lookaround(ast) + 1
    requires qm.ov == ov && !rer.multiline && !rer.ignoreCase && |ov| == |str| + 1
    requires forall l: int :: l in qm.looks ==> l >= 0
    requires forall cp: nat :: cp <= |str| ==> LL.OracleOkSuffix(rer, qm, PIV.InpOfCp(str, cp))
    requires GateStaticsOkNested(qm, re, crv, ncap, nlook, nquant)
    requires forall l: int, la: R.lookaround, b: R.regex ::
               1 <= l <= R.max_lookaround(ast) && LTB.LookEntryOk(crv, l, la, b) ==>
                 M.FrameEntryOk(crv, la, b, PIV.CaptureRegsSet(PIV.CapIdsInLooks(re)), M.LookIdSet(re))
    requires forall c: nat :: c in PIV.CapIdsInLooks(re) ==> M.GNotUnderQuantL(T.Translate(re), c)
    // ---- global res-side facts ----
    requires |res1.a_cp| == nlook && |res1.a_clk| == nlook
    requires CM.LookCpSetWithClk(res1) && CM.LookCpsLE(res1, |str|)
    requires CM.LookCpsOracleTrue(res1, ov)
    requires M.FLookLoopChildLinkOk(crv, str, res1, 1, R.max_lookaround(ast), ov, ncap, nlook, nquant)
    requires forall c: nat :: c in PIV.CapIds(re) && AI.get_idx(res0.a_clk, CP.start_reg(c)) < 0
                              ==> AI.get_idx(res0.a_cp, CP.start_reg(c)) < 0
    // ---- per-live-g OWNER package (A1/A2's outputs) ----
    requires S == PIV.CapIdsInLooks(re)
    requires forall g: LG.GroupId :: g in S && g in PIV.GmOfLive(re, res0, res1, res2) ==>
                                       exists owner: nat :: OwnerPkg(crv, str, re, ov, res1, g, owner, ncap, nlook, nquant)
    // ---- res -> thread frames at TOP looks + thread invariants ----
    requires forall l: nat :: l in NI.TopLookIds(re) ==>
                                AI.get_idx(res1.a_clk, l as int) == AI.get_idx(thread.look_regs.a_clk, l as int)
                                && AReg.get_cp(res1, l as int) == AReg.get_cp(thread.look_regs, l as int)
    requires forall q: nat :: q in PIV.QuantIdsOutsideLooks(re) ==>
                                AI.get_idx(res2.a_clk, q as int) == AI.get_idx(thread.quant_regs.a_clk, q as int)
    requires CM.LookCpSetWithClk(thread.look_regs)
    requires |thread.look_regs.a_cp| == |thread.look_regs.a_clk|
    // ---- the whole-regex DEEP carrier at the winning thread ----
    requires LookNestBackTTopDeep(rer, re, crv, str, ov, S, gmt, thread, ncap, nlook, nquant)
    ensures forall g: LG.GroupId :: g in S && g in PIV.GmOfLive(re, res0, res1, res2) ==> g in gmt
  {
    var maxlook := R.max_lookaround(ast);
    forall g: LG.GroupId | g in S && g in PIV.GmOfLive(re, res0, res1, res2)
      ensures g in gmt
    {
      // presence path on the reconstructed banks
      PIV.CapIdsSplit(re);
      assert g in PIV.CapIds(re);
      NI.GmOfLivePresenceExtractLkNested(re, res0, res1, res2, g);
      assert AReg.as_arrays(res1).1 == res1.a_clk && AReg.as_arrays(res2).1 == res2.a_clk;
      assert PIV.PathPresentLk(re, res0.a_clk, res1.a_clk, res2.a_clk, -1, g);
      // the owner package
      assert g in S && g in PIV.GmOfLive(re, res0, res1, res2);
      assert exists owner: nat :: OwnerPkg(crv, str, re, ov, res1, g, owner, ncap, nlook, nquant);
      var owner: nat :| OwnerPkg(crv, str, re, ov, res1, g, owner, ncap, nlook, nquant);
      // the outermost TOP ancestor
      var A0 := ReconLiveTopAncestor(re, g, owner);
      assert A0 in NI.TopLookIds(re) && A0 in LTB.LookIds(re)
             && g in PIV.CapIds(NI.LookBodyOfRE(re, A0));
      var bA0 := NI.LookBodyOfRE(re, A0);
      // presence descends into A0's body; A0's res1 clock is set
      NI.LookPathDecomposeNested(re, bA0, res0.a_clk, res1.a_clk, res2.a_clk, -1, A0, g);
      assert AI.get_idx(res1.a_clk, A0 as int) >= 0;
      assert PIV.PathPresentLk(bA0, res0.a_clk, res1.a_clk, res2.a_clk, -1, g);
      // A0 matched in res1 (reverse invariant + type pin)
      assert AI.get_idx(res1.a_cp, A0 as int) >= 0;               // LookCpSetWithClk(res1)
      assert AReg.get_cp(res1, A0 as int).Some? by { RL.AAsArraysLaws(res1); }
      assert (A0 as int) in qm.looks && 1 <= A0 <= maxlook;
      assert GateStaticAtNested(qm, re, crv, A0 as int, ncap, nlook, nquant);
      // (2026-08-25) full conjunct list of `GateStaticAtNested`'s exists (a subset
      // is not reliably instantiated under {:isolate_assertions}).
      var laA0: R.lookaround, bT: R.regex :|
        LTB.LookEntryOk(crv, A0 as int, laA0, bT)
        && T.TransWf(bT) && NR.NestedFragmentRE(bT)
        && NR.NegLooksLookFreeRE(bT)
        && (laA0.Lookbehind? ==> NR.LBOnlyLooksRE(bT))
        && (!laA0.Lookbehind? ==> L5ScopeV1RE(bT))
        && qm.looks[A0 as int].0 == T.TrLookaround(laA0)
        && qm.looks[A0 as int].1 == T.Translate(bT)
        && (set gx: LG.GroupId | gx in L.DefGroups(T.Translate(bT))) <= PIV.CapIdsInLooks(re)
        && var bodycode := CP.compile_to_bytecode(bT);
        |bodycode| >= 1
        && PSM.StaticOkNestedRE(qm, bT, bodycode, |bodycode| - 1)
        && PSM.SizesOkRE(bT, ncap, nlook, nquant)
        && ((laA0.NegLookbehind? || laA0.NegLookahead?) ==> NR.CaptureFreeRE(bT));
      assert bT == bA0 by {
        NI.LookBodyOfTablesTie(re, crv, A0);
        var laT: R.lookaround :| LTB.LookEntryOk(crv, A0 as int, laT, bA0);
        assert crv.f_look_ast[A0 as int] == bT == bA0;
      }
      assert (laA0.Lookahead? || laA0.Lookbehind?) by {                       // (L5 F7c-4) kind dispatch
        if laA0.NegLookahead? || laA0.NegLookbehind? {
          assert NR.CaptureFreeRE(bA0);
          PIV.CaptureFreeNoCapIds(bA0);
          assert g in PIV.CapIds(bA0);
          assert false;
        }
      }
      assert crv.f_look_types[A0 as int] == laA0;
      assert M.MatchedPosLA(crv, res1, A0 as int) by {
        assert AI.capture_type(crv.f_look_types[A0 as int]);
      }
      // the deep landing recursion at (body(A0), A0)
      // (2026-08-25) `DeepFindRec` takes the L4-perf OPAQUE bundles (`117b6aa`);
      // this lemma carries their unfolded foralls — reveal to hand them over.
      // (This call site was never re-verified after the perf pass.)
      reveal M.OracleSufAllO(), M.FrameEntryAllO();
      assert M.OracleSufAllO(rer, qm, str);
      assert M.FrameEntryAllO(crv, re, ast);
      DeepFindRec(rer, qm, crv, str, ast, re, ov, res0, res1, res2,
                  bA0, A0, owner, g, ncap, nlook, nquant);
      var lsub := SubFirstLeafAt(rer, crv, str, A0 as int, res1);
      assert lsub.Some? && g in lsub.value;
      // transport onto the thread's bank (top-look cp frame)
      assert AReg.get_cp(res1, A0 as int) == AReg.get_cp(thread.look_regs, A0 as int);
      assert SubFirstLeafAt(rer, crv, str, A0 as int, thread.look_regs) == lsub;
      // A0 matched + dominant on the THREAD
      assert M.MatchedPosLA(crv, thread.look_regs, A0 as int) by {
        assert AReg.get_cp(thread.look_regs, A0 as int).Some?;
      }
      NI.LookPathDomFromLivenessThread(re, res0, res1, res2, thread, g, A0);
      // LAND via the whole-regex DEEP carrier
      DescentLandTopDeep(rer, re, crv, str, ov, S, gmt, thread, A0, g, ncap, nlook, nquant);
    }
  }

}
