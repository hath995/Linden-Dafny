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
  lemma {:isolate_assertions} ForwardMemberOne(
    rer: LW.RegExpRecord, qm: AR.QMap, crv: CP.FCompiled, str: string, ast: R.regex, re: R.regex,
    ov: LOr.OracleView, thread: AI.Thread, res0: AReg.Regs, res1: AReg.Regs, res2: AReg.Regs,
    S: set<LG.GroupId>, leafgm: LG.GroupMap, g: nat, ncap: int, nlook: int, nquant: int)
    // ---- whole-regex statics (verbatim ForwardFindRec block) ----
    requires T.TransWf(re) && NR.NestedFragmentRE(re) && NR.L5ScopeRE(re) && L5ScopeV1RE(re)
    requires M.LooksNoNulledPlusRE(re)   // (§2.5b F-c) look bodies stay stamp-free
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
    hide M.LooksNoNulledPlusRE;   // (§2.5b F-c) a fact here, never unfolded (recursive: batch memory)
    // (§2.5b/z3 4.14) recursive nullability predicates + the CIN disjunct's
    // triggered existential storm the solver; all uses here are opaque.
    hide NUL.NonNullableL, NUL.CINullableL, NUL.NoNulledPlusL, AR.NfaRepCinL;
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
            assert false by {
              hide *;   // (§2.5b/z3 4.14) both branches' facts are opaque; the close is pure arithmetic/sets
            }
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
    requires M.LooksNoNulledPlusRE(re)   // (§2.5b F-c) look bodies stay stamp-free
             && EL.NegBehindLBOnlyRE(re)
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
    hide M.LooksNoNulledPlusRE;   // (§2.5b F-c) a fact here, never unfolded (recursive: batch memory)
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

}
