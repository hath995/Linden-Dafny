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

/** The lift: a per-thread pairing between the RegElk VM and the LK-aware
    PikeTree machine on the SPEC tree, whose group-map tie carries the
    reconstructed inside-look capture values. Scaffold — lemmas are bodiless. */
module LindenElkLiftSimMain {
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
  import opened LindenElkLiftSimForward

  /** (FORWARD membership + VALUE, whole-regex, per leaf-present g) A leaf-present
      inside-`S` capture is LIVE in the reconstruction with the LEAF's value:
      `g in GmOfLive(re, res)` and `leafgm[g] == GmOfLive[g] == LiveRange(res0, g)`.
      Chain: the whole-regex FORWARD carrier (`LookNestOkTTop`, leaf-witness `g`)
      gives `g`'s top ancestor `A0` crossed + dominant on the WINNING THREAD; the
      REGION-EQUALITY deep carrier's ⊆ direction pushes `g` (with value) into
      `A0`'s sub-first-leaf; the top-look frames re-key it onto `res1`;
      `ForwardFindRec` descends to the engine facts; the top-lid transports
      compose the presence up to `re` and `GmOfLiveKeepsPresentLkNested` closes. */
  lemma ForwardMemberOne(
    rer: LW.RegExpRecord, qm: AR.QMap, crv: CP.FCompiled, str: string, ast: R.regex, re: R.regex,
    ov: LOr.OracleView, thread: AI.Thread, res0: AReg.Regs, res1: AReg.Regs, res2: AReg.Regs,
    S: set<LG.GroupId>, leafgm: LG.GroupMap, g: nat, ncap: int, nlook: int, nquant: int)
    // ---- whole-regex statics (verbatim ForwardFindRec block) ----
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
    // ---- the whole-regex carriers at the winning thread ----
    requires S == PIV.CapIdsInLooks(re)
    requires LookNestOkTTop(re, S, leafgm, thread)
    requires LookNestBackTTopDeep(rer, re, crv, str, ov, S, leafgm, thread, ncap, nlook, nquant)
    // ---- res -> thread frames + thread invariants ----
    requires forall l: nat :: l in NI.TopLookIds(re) ==>
                                AI.get_idx(res1.a_clk, l as int) == AI.get_idx(thread.look_regs.a_clk, l as int)
                                && AReg.get_cp(res1, l as int) == AReg.get_cp(thread.look_regs, l as int)
    requires forall q: nat :: q in PIV.QuantIdsOutsideLooks(re) ==>
                                AI.get_idx(res2.a_clk, q as int) == AI.get_idx(thread.quant_regs.a_clk, q as int)
    // recon_outer capture frame: res0 == thread.caps outside the inside-look regs
    requires forall k: int :: k !in PIV.CaptureRegsSet(PIV.CapIdsInLooks(re)) ==>
                                AI.get_idx(res0.a_cp, k) == AI.get_idx(thread.capture_regs.a_cp, k)
                                && AI.get_idx(res0.a_clk, k) == AI.get_idx(thread.capture_regs.a_clk, k)
    requires CM.LookCpSetWithClk(thread.look_regs)
    requires CM.LookCpsOracleTrue(thread.look_regs, ov)
    requires CM.LookCpsLE(thread.look_regs, |str|)
    // ---- the leaf-present g ----
    requires g in S && g in leafgm
    ensures g in PIV.CapIds(re)
    ensures AI.get_idx(res0.a_cp, CP.start_reg(g)) >= 0
    ensures g in PIV.GmOfLive(re, res0, res1, res2)
    ensures PIV.GmOfLive(re, res0, res1, res2)[g] == PIV.LiveRange(res0.a_cp, res0.a_clk, g)
    // (L5 F7c-4) value tie as a `NormRange` equality: the backward fresh match's
    // reversed read (LB owner) and the forward read (LA owner) chain uniformly.
    ensures PIV.NormRange(leafgm[g]) == PIV.NormRange(PIV.LiveRange(res0.a_cp, res0.a_clk, g))
  {
    var maxlook := R.max_lookaround(ast);
    PIV.CapIdsSplit(re);
    assert g in PIV.CapIds(re);
    // g's outermost TOP ancestor
    var ownG := NI.InnermostOwnerDirect(re, g);
    var A0 := ReconLiveTopAncestor(re, g, ownG);
    assert A0 in NI.TopLookIds(re) && A0 in LTB.LookIds(re)
           && g in PIV.CapIds(NI.LookBodyOfRE(re, A0));
    var bA0 := NI.LookBodyOfRE(re, A0);

    // (1) the FORWARD carrier at A0 (leaf-witness g): crossed + dominant on thread
    assert NI.LookPathPresent(re, thread.capture_regs.a_clk, thread.quant_regs.a_clk, -1, A0)
           && AI.get_idx(thread.look_regs.a_clk, A0 as int) >= 0
           && AI.get_idx(thread.look_regs.a_clk, A0 as int)
              >= NI.MxAtLidLk(re, thread.quant_regs.a_clk, -1, A0)
    by {
      assert g in S && g in leafgm && g in PIV.CapIds(NI.LookBodyOfRE(re, A0));
    }
    var L0 := AI.get_idx(thread.look_regs.a_clk, A0 as int);
    NI.LookPathDomIntroTop(re, thread.capture_regs.a_clk, thread.quant_regs.a_clk, -1, A0, L0);
    assert NI.LookPathDom(re, L0, thread.quant_regs.a_clk, A0);
    // matched on the thread (forward invariant)
    assert AI.get_idx(thread.look_regs.a_cp, A0 as int) >= 0;    // LookCpSetWithClk
    assert AReg.get_cp(thread.look_regs, A0 as int).Some?;
    // the row at A0 (type pin)
    assert (A0 as int) in qm.looks && 1 <= A0 <= maxlook;
    assert GateStaticAtNested(qm, re, crv, A0 as int, ncap, nlook, nquant);
    var laA0: R.lookaround, bT: R.regex :| LTB.LookEntryOk(crv, A0 as int, laA0, bT)
                                           && qm.looks[A0 as int].0 == T.TrLookaround(laA0)
                                           && qm.looks[A0 as int].1 == T.Translate(bT)
                                           && ((laA0.NegLookbehind? || laA0.NegLookahead?) ==> NR.CaptureFreeRE(bT));
    assert bT == bA0 by {
      NI.LookBodyOfTablesTie(re, crv, A0);
      var laT: R.lookaround :| LTB.LookEntryOk(crv, A0 as int, laT, bA0);
      assert crv.f_look_ast[A0 as int] == bT == bA0;
    }
    assert crv.f_look_types[A0 as int] == laA0;
    assert (laA0.Lookahead? || laA0.Lookbehind?) by {                       // (L5 F7c-4) kind dispatch
      if laA0.NegLookahead? || laA0.NegLookbehind? {
        assert NR.CaptureFreeRE(bA0);
        PIV.CaptureFreeNoCapIds(bA0);
        assert g in PIV.CapIds(bA0);
        assert false;
      }
    }
    assert M.MatchedPosLA(crv, thread.look_regs, A0 as int) by {
      assert AI.capture_type(crv.f_look_types[A0 as int]);
    }

    // (2) A0's sub-leaf EXISTS (thread record is oracle-true), so the deep
    //     carrier's region equality pushes g (with value) into it.
    var cpA0 := AReg.get_cp(thread.look_regs, A0 as int).value;
    assert cpA0 == AI.get_idx(thread.look_regs.a_cp, A0 as int);
    assert 0 <= cpA0 <= |str|;                                   // LookCpsLE(thread)
    var inpA0 := PIV.InpOfCp(str, cpA0);
    var dir0 := LidDir(crv, A0 as int);
    var t0 := LFU.ComputeTr(rer, [LS.Areg(T.Translate(bA0))], inpA0, LG.Empty, dir0);
    assert T.TransWf(bA0) by { M.TransWfLookBodyOfRE(re, A0); }
    // (L5 F7c-4) the spec result in the lid's OWN direction — `FirstLeaf` is
    // Forward-only, so the leaf is identified with the direction-general
    // `TreeRes(t0, Empty, inpA0, dir0)`, not with `FirstLeaf`.
    var res0t := LT.TreeRes(t0, LG.Empty, inpA0, dir0);
    assert res0t.Some? by {
      assert LOr.view_get_oracle(ov, cpA0, A0 as int);           // LookCpsOracleTrue(thread)
      assert LL.OracleOkSuffix(rer, qm, inpA0);
      assert LL.OracleOkAt(rer, qm, inpA0);
      assert (A0 as int) in qm.looks
             && qm.looks[A0 as int] == (T.TrLookaround(laA0), T.Translate(bA0));
      assert TREP.CpOf(inpA0) == cpA0 by { LS.ReverseLength(str[..cpA0]); }
      assert L.LkDir(T.TrLookaround(laA0)) == dir0;              // (L5 F7c-4) kind-matched direction
      assert LT.TreeRes(LFU.ComputeTr(rer, [LS.Areg(T.Translate(bA0))], inpA0, LG.Empty, dir0),
                        LG.Empty, inpA0, dir0).Some?;
    }
    var lsubTh := SubFirstLeafAt(rer, crv, str, A0 as int, thread.look_regs);
    assert bA0 == M.VBody(crv, A0 as int) by {
      NI.LookBodyOfTablesTie(re, crv, A0);
      var laT: R.lookaround :| LTB.LookEntryOk(crv, A0 as int, laT, bA0);
    }
    assert lsubTh.Some? && lsubTh.value == res0t.value.1 by {
      assert AReg.get_cp(thread.look_regs, A0 as int) == Some(cpA0 as int);
    }
    // the carrier's region equality at A0 (matched + dominant on thread)
    assert g in lsubTh.value && leafgm[g] == lsubTh.value[g] by {
      assert g in S && g in PIV.CapIds(NI.LookBodyOfRE(re, A0)) && g in leafgm;
    }

    // (3) re-key onto res1
    assert AReg.get_cp(res1, A0 as int) == AReg.get_cp(thread.look_regs, A0 as int);
    var lsubA0 := SubFirstLeafAt(rer, crv, str, A0 as int, res1);
    assert lsubA0 == lsubTh;                                     // reads only get_cp at A0
    assert M.MatchedPosLA(crv, res1, A0 as int) by {
      assert AReg.get_cp(res1, A0 as int).Some?;
    }

    // (4) descend
    ForwardFindRec(rer, qm, crv, str, ast, re, ov, res0, res1, res2,
                   bA0, A0, g, ncap, nlook, nquant);
    assert PIV.PathPresentLk(bA0, res0.a_clk, res1.a_clk, res2.a_clk, -1, g);
    assert AI.get_idx(res0.a_clk, CP.start_reg(g)) >= 0
           && AI.get_idx(res0.a_cp, CP.start_reg(g)) >= 0;
    assert AI.get_idx(res0.a_clk, CP.start_reg(g))
        >= PIV.MxAtGidLk(bA0, res0.a_clk, res1.a_clk, res2.a_clk, -1, g);
    assert PIV.NormRange(lsubA0.value[g]) == PIV.NormRange(PIV.LiveRange(res0.a_cp, res0.a_clk, g));

    // (5) compose to re level: presence path to A0 on the reconstructed banks
    assert forall c: nat :: c in PIV.CapIdsOutsideLooks(re) ==>
                              AI.get_idx(thread.capture_regs.a_clk, CP.start_reg(c)) == AI.get_idx(res0.a_clk, CP.start_reg(c))
    by {
      forall c: nat | c in PIV.CapIdsOutsideLooks(re)
        ensures AI.get_idx(thread.capture_regs.a_clk, CP.start_reg(c)) == AI.get_idx(res0.a_clk, CP.start_reg(c))
      {
        assert CP.start_reg(c) !in PIV.CaptureRegsSet(PIV.CapIdsInLooks(re)) by {
          if CP.start_reg(c) in PIV.CaptureRegsSet(PIV.CapIdsInLooks(re)) {
            if CP.start_reg(c) in (set cid | cid in PIV.CapIdsInLooks(re) :: CP.start_reg(cid as int)) {
              var cid: nat :| cid in PIV.CapIdsInLooks(re) && CP.start_reg(cid as int) == CP.start_reg(c);
              assert cid == c;
              assert c in PIV.CapIdsOutsideLooks(re) * PIV.CapIdsInLooks(re);
              PIV.CapIdsLooksDisjoint(re);
            } else {
              var cid: nat :| cid in PIV.CapIdsInLooks(re) && CP.end_reg(cid as int) == CP.start_reg(c);
              assert 2 * (cid as int) + 1 == 2 * (c as int);
            }
            assert false;
          }
        }
      }
    }
    assert forall q0: nat :: q0 in PIV.QuantIdsOutsideLooks(re) ==>
                               AI.get_idx(thread.quant_regs.a_clk, q0 as int) == AI.get_idx(res2.a_clk, q0 as int);
    NI.LookPathPresentAgreeTop(re, thread.capture_regs.a_clk, thread.quant_regs.a_clk,
                               res0.a_clk, res2.a_clk, -1, A0);
    assert NI.LookPathPresent(re, res0.a_clk, res2.a_clk, -1, A0);
    assert NI.MxAtLidLk(re, res2.a_clk, -1, A0) == NI.MxAtLidLk(re, thread.quant_regs.a_clk, -1, A0);
    NI.LookPathPresentLkFromPresentTop(re, res0.a_clk, res1.a_clk, res2.a_clk, -1, A0);
    assert NI.LookPathPresentLk(re, res0.a_clk, res1.a_clk, res2.a_clk, -1, A0);
    assert AI.get_idx(res1.a_clk, A0 as int) == L0 && L0 >= 0;
    assert AI.get_idx(res1.a_clk, A0 as int) >= NI.MxAtLidLk(re, res2.a_clk, -1, A0);
    NI.LookPathComposeNested(re, bA0, res0.a_clk, res1.a_clk, res2.a_clk, -1, A0, g);
    assert PIV.PathPresentLk(re, res0.a_clk, res1.a_clk, res2.a_clk, -1, g);
    assert PIV.MxAtGidLk(re, res0.a_clk, res1.a_clk, res2.a_clk, -1, g)
        == PIV.MxAtGidLk(bA0, res0.a_clk, res1.a_clk, res2.a_clk, -1, g);

    // (6) close
    NI.GmOfLiveKeepsPresentLkNested(re, res0, res1, res2, g);
    assert g in PIV.GmOfLive(re, res0, res1, res2);
    assert PIV.GmOfLive(re, res0, res1, res2)[g] == PIV.LiveRange(res0.a_cp, res0.a_clk, g);
    assert PIV.NormRange(leafgm[g]) == PIV.NormRange(PIV.LiveRange(res0.a_cp, res0.a_clk, g)) by {
      assert leafgm[g] == lsubA0.value[g];                       // region equality (raw)
      assert PIV.NormRange(lsubA0.value[g]) == PIV.NormRange(PIV.LiveRange(res0.a_cp, res0.a_clk, g));
    }
  }

  // ==========================================================================
  // L4 PERF: the deep-case CONCLUSION — the two descent wrappers + endpoint
  // assembly, hoisted into a MINIMAL context. In MainTheoremL4 the
  // `ReverseCDeepFull` / `ForwardMemberOne` precondition CHECKS timed out (even
  // at 450s) — not from any hard proof (their preconditions are all assumptions
  // produced by the endpoint adapters and the owner-package forall) but from Z3
  // MATCHING ~25 quantified requires against MainTheoremL4's thousands of
  // ambient facts. Here they match against only this lemma's own requires.
  // ==========================================================================
  lemma MainTheoremL4DeepConclude(
    rer: LW.RegExpRecord, qm: AR.QMap, crv: CP.FCompiled, str: string, ast: R.regex, re: R.regex,
    code: RB.code, endl: nat, ov: LOr.OracleView, thread: AI.Thread, leaf: LT.Leaf,
    t: LT.Tree, inp: LC.Input, S: set<LG.GroupId>, ncap: int, nlook: int, nquant: int)
    requires T.TransWf(re) && NR.NestedFragmentRE(re) && NR.L5ScopeRE(re) && L5ScopeV1RE(re)
             && NR.NegLooksLookFreeRE(re)
    requires PIV.CapUnique(re) && PIV.QuantUnique(re) && LTB.LookUnique(re)
    requires LTB.LookTablesOk(re, crv)
    requires |crv.f_look_types| == |crv.f_look_ast|
    requires forall x: nat :: x in LTB.LookIds(re) ==> 1 <= x <= R.max_lookaround(ast)
    requires forall x: nat :: x in LTB.LookIds(re) ==> (x as int) in qm.looks
    requires nlook == R.max_lookaround(ast) + 1
    requires R.max_lookaround(re) == R.max_lookaround(ast)
    requires qm.ov == ov && !rer.multiline && !rer.ignoreCase && |ov| == |str| + 1
    requires forall l: int :: l in qm.looks ==> l >= 0
    requires M.OracleSufAllO(rer, qm, str)
    requires GateStaticsOkNested(qm, re, crv, ncap, nlook, nquant)
    requires M.FrameEntryAllO(crv, re, ast)
    requires forall c: nat :: c in PIV.CapIdsInLooks(re) ==> M.GNotUnderQuantL(T.Translate(re), c)
    requires S == PIV.CapIdsInLooks(re)
    requires M.OrderedGm(leaf.1)
    requires LT.FirstLeaf(t, inp) == Some(leaf)
    requires BestTieLkNestedTop(rer, re, crv, str, ov, S, Some(leaf), Some(thread), ncap, nlook, nquant)
    // ---- global res-side facts, OPAQUE (the endpoint adapters' outputs) ----
    requires var res := AI.FLookLoop(crv, str, 1, R.max_lookaround(ast),
                                     thread.capture_regs, thread.look_regs, thread.quant_regs, ov);
             CM.ThreadRegsWf(AI.Thread(thread.pc, res.0, res.1, res.2, thread.exit_allowed), ncap, nlook, nquant)
             && M.QuantRegsFinal(AI.Thread(thread.pc, res.0, res.1, res.2, thread.exit_allowed))
             && M.LookInvO(res.1, ov, str)
             && M.ChildLinkO(crv, str, res.1, 1, R.max_lookaround(ast), ov, ncap, nlook, nquant)
             && M.ValueOkO(crv, str, res.0, res.1, 1, R.max_lookaround(ast), ov, ncap, nlook, nquant)
             && M.QuantValueOkO(crv, str, res.2, res.1, 1, R.max_lookaround(ast), ov, ncap, nlook, nquant)
             && M.Res0LiveO(re, res.0)
             && M.TopLookFrameO(re, res.1, thread.look_regs)
             && M.QuantFrameO(re, res.2, thread.quant_regs)
             && M.CaptureFrameO(re, res.0, thread.capture_regs)
    // ---- thread invariants (opaque) ----
    requires M.ThreadLookInvO(thread.look_regs, ov, str)
    // ---- the OWNER-package forall, OPAQUE ----
    requires var res := AI.FLookLoop(crv, str, 1, R.max_lookaround(ast),
                                     thread.capture_regs, thread.look_regs, thread.quant_regs, ov);
             OwnerForallO(crv, str, re, ov, res.0, res.1, res.2, S, ncap, nlook, nquant)
    ensures var res := AI.FLookLoop(crv, str, 1, R.max_lookaround(ast),
                                    thread.capture_regs, thread.look_regs, thread.quant_regs, ov);
            leaf.1 == PIV.NormGm(PIV.GmOfLive(re, res.0, res.1, res.2))
  {
    reveal M.LookInvO(), M.ChildLinkO(), M.ValueOkO(), M.QuantValueOkO(), M.Res0LiveO(),
           M.TopLookFrameO(), M.QuantFrameO(), M.CaptureFrameO(), OwnerForallO(),
           M.ThreadLookInvO(), M.FrameEntryAllO(), M.OracleSufAllO();
    var maxlook := R.max_lookaround(ast);
    var res := AI.FLookLoop(crv, str, 1, maxlook, thread.capture_regs, thread.look_regs, thread.quant_regs, ov);

    // (R): reverse membership
    ReverseCDeepFull(rer, qm, crv, str, ast, re, ov, thread, res.0, res.1, res.2,
                     S, leaf.1, ncap, nlook, nquant);
    assert forall g: LG.GroupId :: g in S && g in PIV.GmOfLive(re, res.0, res.1, res.2) ==> g in leaf.1;

    // (F): forward membership + value (Norm-range form)
    assert forall g: LG.GroupId :: g in S && g in leaf.1 ==>
                                     g in PIV.GmOfLive(re, res.0, res.1, res.2)
                                     && PIV.NormRange(leaf.1[g]) == PIV.NormRange(PIV.GmOfLive(re, res.0, res.1, res.2)[g])
    by {
      forall g: LG.GroupId | g in S && g in leaf.1
        ensures g in PIV.GmOfLive(re, res.0, res.1, res.2)
                && PIV.NormRange(leaf.1[g]) == PIV.NormRange(PIV.GmOfLive(re, res.0, res.1, res.2)[g])
      {
        ForwardMemberOne(rer, qm, crv, str, ast, re, ov, thread, res.0, res.1, res.2,
                         S, leaf.1, g, ncap, nlook, nquant);
      }
    }

    // endpoint assembly
    L3aEndpointAssemblyNestedFull2(ast, re, crv, code, endl, str, ov, S, thread, leaf,
                                   ncap, nlook, nquant, rer, qm, t, inp);
  }

  lemma MainTheoremL5(raw: R.raw_regex, str: string)
    requires NR.NestedFragmentRaw(raw)
    requires T.Latin1Wf(raw)
    requires L5Scope(raw)
    ensures LES.MatcherSpec(raw, str, LES.Normalize(AI.FFullMatch(raw, str)))
  {
    var ast := R.annotate(raw);
    var re := R.lazy_prefix(ast);
    var rer := LES.TheRer(raw);
    var inp := LC.InitInput(str);
    var ngroups := LES.NGroups(raw);
    assert !rer.multiline && !rer.ignoreCase;

    // ---- static packages -------------------------------------------------
    T.AnnotateWf(raw);                     // TransWf(ast) && TransWf(re)
    NR.SpecRegexNestedFragment(raw);       // NestedFragmentRE(re)
    LTB.SpecRegexLookUnique(raw);          // unique lids, all >= 1
    LTB.SpecRegexLidsWellNested(raw);      // LidsWellNested(re)
    PIV.SpecRegexCapUnique(raw);           // CapUnique(re)
    PIV.SpecRegexQuantUnique(raw);         // QuantUnique(re)
    assert L5ScopeV1RE(re);                // L5Scope (v1: kind-split hub)
    L5ScopeV1ImpliesL5(re);                // NR.L5ScopeRE(re) for the descent/carriers
    assert NR.NegLooksLookFreeRE(re);      // L4Scope
    var qm := AR.QMap(M.QmOfRE(re), OE.LmOf(re), AI.FBuildOracle(CP.FFullCompilation(ast), str));
    // the nested static package (qm correctness minus the oracle entry)
    M.QmOfREEntries(re);
    M.QmapOkFromEntries(re, qm);
    OE.LmapOkOfLmOf(re, qm);
    assert AR.QmapOk(re, qm) && AR.LmapOk(re, qm);
    // ---- THE NESTED ORACLE ENTRY (formerly the sole hypothesis) ------------
    assert LL.OracleOkSuffix(rer, qm, inp) by {
      var crv0 := CP.FFullCompilation(ast);
      var pre := R.Re_quant(R.NonNullable, 0, R.CountedQuant(0, None, false), R.Re_character(R.Dot));
      assert re == R.Re_con(pre, ast);
      LTB.FFullCompilationLookOk(ast);
      assert LTB.LookTablesOk(pre, crv0);
      assert LTB.LookTablesOk(re, crv0);
      assert LTB.LookIds(pre) == {};
      assert LTB.LookIds(re) == LTB.LookIds(ast);
      assert NR.NestedFragmentRE(ast);
      OracleOkRowsL5(rer, ast, crv0, str, re);            // (L5 F7g)
    }

    NR.CompileToBytecodeRepNested(re);
    var code := CP.compile_to_bytecode(re);
    var next := CP.compile(re, 0, CP.Progress).1;
    var endl: nat := next as nat;
    assert NR.NfaRepRE(re, code, 0, endl)
           && NR.GetPcRE(code, endl) == Some(RB.Accept) && |code| == endl + 1;
    CompileStutterTameRENested(re);
    assert PSM.StaticOkNestedRE(qm, re, code, endl);

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

    // fragment code shape: every SetQuantToClock has b == false.
    forall pc: nat, q: int, b: bool | NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(q, b))
      ensures !b
    {
      if pc < endl {
        NI.CodeShapeAt(re, code, 0, endl, pc);
      } else if pc == endl {
      } else {
        assert pc >= |code|;
      }
    }

    // ---- the spec tree (Rec tier) ----------------------------------------
    LFU.ComputeTrIsTree(rer, [LS.Areg(T.Translate(re))], inp, LG.Empty, WP.Forward);
    var t := LFU.ComputeTr(rer, [LS.Areg(T.Translate(re))], inp, LG.Empty, WP.Forward);
    assert LS.IsTree(rer, [LS.Areg(T.Translate(re))], inp, LG.Empty, WP.Forward, t);
    assert LES.SpecRegex(raw) == T.Translate(re);
    EL.TranslateFragmentPikeLkRec(re);
    EL.BooleanCorrectLkRec(rer, T.Translate(re), inp, t);
    assert forall i :: 0 <= i < |[LS.Areg(T.Translate(re))]| ==> ![LS.Areg(T.Translate(re))][i].Acheck?;
    M.BoolTreeLbIrrel(rer, [LS.Areg(T.Translate(re))], inp, BS.CanExit, BS.CannotExit, t);
    assert EL.BoolTreeLk(rer, [LS.Areg(T.Translate(re))], inp, BS.CannotExit, t);
    TranslateNoBackref(re);
    assert NoBackrefActions([LS.Areg(T.Translate(re))]);
    var fuel0 := FS.ActionsFuel([LS.Areg(T.Translate(re))], inp, WP.Forward) + 1;
    FS.FunctionalTerminates(rer, [LS.Areg(T.Translate(re))], inp, LG.Empty, WP.Forward, fuel0);
    assert FS.ComputeTree(rer, [LS.Areg(T.Translate(re))], inp, LG.Empty, WP.Forward, fuel0) == Some(t);
    ComputePikeSubtreeLk(rer, [LS.Areg(T.Translate(re))], inp, LG.Empty, WP.Forward, fuel0, t);
    assert PTL.PikeSubtreeLk(t);

    // ---- the CHECKED tree (Rec walk carrier) ------------------------------
    WkE.WalkOkEntryNested(re);
    assert EL.PikeLkActionsRec([LS.Areg(T.Translate(re))]) by {
      assert [LS.Areg(T.Translate(re))] == [LS.Areg(T.Translate(re))] + [];
      assert EL.PikeLkActionsRec([]);
      EL.PikeLkActionsRecConsIff(LS.Areg(T.Translate(re)), []);
    }
    var S := PIV.CapIdsInLooks(re);
    M.LkBodyGroupsEqCapIdsInLooks(re);
    assert S == LL.LkBodyGroups(T.Translate(re));
    assert WO.WalkOk([LS.Areg(T.Translate(re))], code, 0, ATR.EaOf(BS.CannotExit));
    AR.CompileToBytecodeActionsRepNested(rer, qm, re);
    assert AR.ActionsRepL(rer, qm, [LS.Areg(T.Translate(re))], code, 0);
    assert LL.LkActsInS([LS.Areg(T.Translate(re))], S) by {
      LL.LkBodyGroupsConfines(T.Translate(re), S);
      LL.LkActsInSCons(LS.Areg(T.Translate(re)), [], S);
    }
    LL.ComputeTrLkConfinedK(rer, [LS.Areg(T.Translate(re))], inp, LG.Empty, WP.Forward, S);
    var tstar := ATR.ActionsTreeRepRENested(rer, qm, [LS.Areg(T.Translate(re))], code, 0, inp, BS.CannotExit, t, S);
    assert TREP.TreeRepRE(qm, tstar, code, 0, inp, false);
    assert TT.TreeThreadRE(rer, qm, code, inp, tstar, 0, false);

    // ---- the engine pipeline ---------------------------------------------
    var crv := CP.FFullCompilation(ast);
    M.FFullCompilationFactsNested(ast);   // L4: nested ast is NOT LookBehindFragmentRE
    assert crv.f_main_ast == ast && crv.f_main_bc == code && crv.f_main_cdns == LCdn.compile_cdns(ast);
    assert |crv.f_look_types| == |crv.f_look_ast| by {                    // (L5 F7c-4) table shape
      var maxlook0 := R.max_lookaround(ast);
      var seed := CP.FCompiled(ast, CP.compile_to_bytecode(R.lazy_prefix(ast)), LCdn.compile_cdns(ast),
                               seq(maxlook0 + 1, i => R.Lookahead), seq(maxlook0 + 1, i => R.Re_empty),
                               seq(maxlook0 + 1, i => []), seq(maxlook0 + 1, i => []),
                               seq(maxlook0 + 1, i => []), seq(R.max_quant(ast) + 1, i => []));
      assert CP.FFullCompilation(ast) == CP.FCompileExtra(ast, seed);
      LTB.FCompileExtraLookFrame(ast, seed);
      assert LTB.SameLookSizes(seed, crv);
      assert |seed.f_look_types| == |seed.f_look_ast|;
    }
    var ov := AI.FBuildOracle(crv, str);
    OB.FBuildOracleViewLen(crv, str);                     // |ov| == |str| + 1
    assert qm.ov == ov;
    var capture := AReg.init_regs(ncap);
    var look := AReg.init_regs(nlook);
    var quant := AReg.init_regs(nquant);
    var ctx := AI.cp_context(0, str, LAnc.Forward);
    var inits := AI.FInitState(code, 0, capture, look, quant, 0, ctx);
    var fmres := AI.FFindMatch(code, str, inits, ov, LAnc.Forward, crv.f_main_cdns);
    var result := fmres.0;

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
    GateStaticsFromTablesNested(qm, re, crv, ncap, nlook, nquant);
    assert GateStaticsOkNested(qm, re, crv, ncap, nlook, nquant);

    // ---- the Rec composite lockstep ---------------------------------------
    PSM.InitialPikeInvFullREAtCpNested(rer, qm, re, code, endl, ngroups, str, 0, tstar,
                                       inits, ncap, nlook, nquant);
    assert ctx.nextchar == AI.get_char(str, 0);
    assert PIV.ContextOkRE(str, inits.cp, inits.context);
    assert M.OracleSufAllO(rer, qm, str) by {                          // (L5 F7d) hoisted from below
      reveal M.OracleSufAllO();
      forall cp: nat | cp <= |str| ensures LL.OracleOkSuffix(rer, qm, PIV.InpOfCp(str, cp)) {
        OracleOkSuffixAtCp(rer, qm, str, cp);
      }
    }
    SufAllToColsOk(rer, qm, str);
    L3aCompositeCloseRec(rer, qm, re, code, endl, ngroups, crv, str, ov, S, tstar, t, inp,
                         inits, crv.f_main_cdns, result, ncap, nlook, nquant);
    assert BestTieLkNestedTop(rer, re, crv, str, ov, S, LT.FirstLeaf(t, inp), result, ncap, nlook, nquant);

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
      var thread := result.value;
      // winning-thread wf + reconstruct identity + oracle stability
      CM.RegsClocksLEInit(ncap, 0);
      CM.RegsClocksLEInit(nlook, 0);
      CM.RegsClocksLEInit(nquant, 0);
      CM.FInitStateClocksLE(code, 0, capture, look, quant, 0, ctx);
      CM.FInitStateRegsWf(code, 0, ncap, nlook, nquant, 0, ctx);
      assert M.VmQuantFinal(inits) by {
        var th0 := AI.init_thread(capture, look, quant);
        assert M.QuantRegsFinal(th0) by {
          forall k ensures AI.get_idx(quant.a_cp, k) < 0 && AI.get_idx(quant.a_clk, k) >= -1 {
            if 0 <= k < |quant.a_cp| { assert quant.a_cp[k] == -1; }
            if 0 <= k < |quant.a_clk| { assert quant.a_clk[k] == -1; }
          }
        }
        forall t2 | t2 in inits.active ensures M.QuantRegsFinal(t2) { assert t2 == th0; }
      }
      M.FFindMatchThreadFacts(code, str, inits, ov, LAnc.Forward, crv.f_main_cdns, ncap, nlook, nquant);
      assert CM.ThreadRegsWf(thread, ncap, nlook, nquant) && M.QuantRegsFinal(thread);
      M.FNulledPlusIdentity(ast, thread.capture_regs, thread.look_regs, thread.quant_regs,
                            crv.f_plus_bc, str, fmres.1, LAnc.Forward);
      assert AI.FReconstructPlus(thread, ast, crv.f_plus_bc, str, fmres.1, LAnc.Forward).0 == thread;
      assert fmp.0 == Some(thread);
      M.NoWriteOracleBodyCodeNested(re);
      CM.FFindMatchOvStable(code, str, inits, ov, LAnc.Forward, crv.f_main_cdns);
      assert fmres.1 == ov;
      assert fmp.1 == ov by {
        assert fmp == (Some(AI.FReconstructPlus(thread, ast, crv.f_plus_bc, str, ov, LAnc.Forward).0),
                       AI.FReconstructPlus(thread, ast, crv.f_plus_bc, str, ov, LAnc.Forward).1);
        M.FNulledPlusIdentity(ast, thread.capture_regs, thread.look_regs, thread.quant_regs,
                              crv.f_plus_bc, str, ov, LAnc.Forward);
      }

      // the leaf
      assert LT.FirstLeaf(t, inp).Some?;
      var leaf := LT.FirstLeaf(t, inp).value;
      assert BestTieLkNestedTop(rer, re, crv, str, ov, S, Some(leaf), Some(thread), ncap, nlook, nquant);
      M.FirstLeafOrdered(t, inp, leaf);

      // ==== ENDPOINT: OPAQUE endpoint facts (adapters + scoped by-blocks) ====
      // Heavy quantified endpoint facts are produced by the per-fact adapters as
      // OPAQUE wrappers (M.*O) so MainTheoremL4's ~5000-fact context carries no
      // triggers for them; DeepConclude matches them atomically and reveals
      // internally. The a-h tables the owner-forall needs stay SCOPED to its
      // by-block, never entering the outer context.
      assert NR.L5ScopeRE(re);                     // (L5 F7c-2c) the Endpoint*/owner lemmas are L5-scoped
      M.EndpointValueOk(ast, re, crv, code, str, ov, crv.f_main_cdns, inits, capture, look, quant, ncap, nlook, nquant, endl, result);
      M.EndpointQuantValueOk(ast, re, crv, code, str, ov, crv.f_main_cdns, inits, capture, look, quant, ncap, nlook, nquant, endl, result);
      M.EndpointChildLinkOk(ast, re, crv, code, str, ov, crv.f_main_cdns, inits, capture, look, quant, ncap, nlook, nquant, endl, result);
      M.EndpointLookInv(ast, re, crv, code, str, ov, crv.f_main_cdns, inits, capture, look, quant, ncap, nlook, nquant, endl, result);
      M.EndpointTopLookFrame(ast, re, crv, code, str, ov, crv.f_main_cdns, inits, capture, look, quant, ncap, nlook, nquant, endl, result);
      var res := AI.FLookLoop(crv, str, 1, maxlook, thread.capture_regs, thread.look_regs, thread.quant_regs, ov);
      var lkT := thread.look_regs;
      var qtT := thread.quant_regs;
      var Sreg := PIV.CaptureRegsSet(PIV.CapIdsInLooks(re));
      var Slook := M.LookIdSet(re);

      assert M.OracleSufAllO(rer, qm, str) by {
        reveal M.OracleSufAllO();
        forall cp: nat | cp <= |str| ensures LL.OracleOkSuffix(rer, qm, PIV.InpOfCp(str, cp)) {
          OracleOkSuffixAtCp(rer, qm, str, cp);
        }
      }
      assert forall c: nat :: c in PIV.CapIdsInLooks(re) ==> M.GNotUnderQuantL(T.Translate(re), c);

      // owner-forall -> OwnerForallO (a-h tables SCOPED to this by-block)
      assert NR.L5ScopeRE(re);                     // (L5 F7c-2c)
      ProduceOwnerForall(qm, crv, str, ast, re, code, endl, ov, thread, S, inits,
                         capture, look, quant, result, ncap, nlook, nquant);

      var synthetic := AI.Thread(thread.pc, res.0, res.1, res.2, thread.exit_allowed);
      assert CM.ThreadRegsWf(synthetic, ncap, nlook, nquant) && M.QuantRegsFinal(synthetic);
      // (R)+(F) descent wrappers + endpoint assembly — hoisted to a minimal
      // context (`MainTheoremL4DeepConclude`); inline, the two wrappers'
      // precondition checks timed out even at 450s.
      MainTheoremL4DeepConclude(rer, qm, crv, str, ast, re, code, endl, ov, thread, leaf,
                                t, inp, S, ncap, nlook, nquant);
      assert leaf.1 == PIV.NormGm(PIV.GmOfLive(re, res.0, res.1, res.2));

      // the engine answer via the L3a unfold, at the SAME res
      M.FBuildCaptureUnfoldL3a(crv, str, ov, ncap, nlook, nquant, capture, look, quant, fmp);
      assert bc.0 == Some(AI.filter_reset(crv.f_main_ast, res.0, res.1, res.2, -1)) by {
        assert fmp.0.value == thread;
        assert AI.FLookLoop(crv, str, 1, R.max_lookaround(crv.f_main_ast),
                            thread.capture_regs, thread.look_regs, thread.quant_regs, fmp.1) == res;
      }
      assert AI.FFullMatch(raw, str)
          == Some(AI.filter_reset(ast, synthetic.capture_regs, synthetic.look_regs,
                                  synthetic.quant_regs, -1));

      // ---- extraction ------------------------------------------------------
      assert EL.BoolTreeLk(LES.TheRer(raw), [LS.Areg(LES.SpecRegex(raw))], LC.InitInput(str), BS.CannotExit, t);
      assert LS.IsTree(LES.TheRer(raw), [LS.Areg(LES.SpecRegex(raw))], LC.InitInput(str), LG.Empty, WP.Forward, t);
      assert CM.ThreadRegsWf(synthetic, 2 * R.max_group(R.annotate(raw)) + 2,
                             R.max_lookaround(R.annotate(raw)) + 1,
                             R.max_quant(R.annotate(raw)) + 1);
      assert M.QuantRegsFinal(synthetic);
      assert leaf.1 == PIV.NormGm(PIV.GmOfLive(re, synthetic.capture_regs, synthetic.look_regs,
                                               synthetic.quant_regs));
      assert LT.FirstLeaf(t, LC.InitInput(str)) == Some(leaf);
      MainExtractionL5(raw, str, t, synthetic, leaf);           // (L5 F7e-2)
      assert LES.MatcherSpec(raw, str, LES.Normalize(AI.FFullMatch(raw, str)));
    }
  }

  /** The L4 entry point (forward-only positive looks), a special case of `MainTheoremL5`. */
  lemma MainTheoremL4(raw: R.raw_regex, str: string)
    requires NR.NestedFragmentRaw(raw)
    requires T.Latin1Wf(raw)
    requires L4Scope(raw)
    ensures LES.MatcherSpec(raw, str, LES.Normalize(AI.FFullMatch(raw, str)))
  {
    L4ScopeImpliesL5(raw);
    MainTheoremL5(raw, str);
  }

}
