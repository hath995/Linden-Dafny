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
module LindenElkLiftSimDeep {
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

  /** (L5 F7f perf) The LOOKBEHIND arm of `DeepFindRec`, extracted so each of its
      assertions is checked in the small context of this lemma rather than in the
      3000-assertion parent (with the hub's `NoPosLookbehindRE` conjunct gone, several
      of the arm's VCs timed out at 900 s inside the parent). Mutually recursive with
      `DeepFindRec` on the lexicographic metric `(|LookIds(host)|, arm)`. */
  lemma DeepFindRecLB(
    rer: LW.RegExpRecord, qm: AR.QMap, crv: CP.FCompiled, str: string, ast: R.regex, re: R.regex,
    ov: LOr.OracleView, res0: AReg.Regs, res1: AReg.Regs, res2: AReg.Regs,
    host: R.regex, A: nat, owner: nat, g2: nat, ncap: int, nlook: int, nquant: int)
    // ---- whole-regex statics (fixed through the recursion) ----
    requires T.TransWf(re) && NR.NestedFragmentRE(re) && NR.L5ScopeRE(re) && L5ScopeV1RE(re)
    requires PIV.CapUnique(re) && PIV.QuantUnique(re) && LTB.LookUnique(re)
    requires LTB.LookTablesOk(re, crv)
    requires |crv.f_look_types| == |crv.f_look_ast|
    requires forall x: nat :: x in LTB.LookIds(re) ==> 1 <= x <= R.max_lookaround(ast)
    requires forall x: nat :: x in LTB.LookIds(re) ==> (x as int) in qm.looks
    requires nlook == R.max_lookaround(ast) + 1
    requires qm.ov == ov && !rer.multiline && !rer.ignoreCase && |ov| == |str| + 1
    requires forall l: int :: l in qm.looks ==> l >= 0
    requires M.OracleSufAllO(rer, qm, str)
    requires GateStaticsOkNested(qm, re, crv, ncap, nlook, nquant)
    requires M.FrameEntryAllO(crv, re, ast)
    // ---- the fragment's no-quant scope for g2 ----
    requires M.GNotUnderQuantL(T.Translate(re), g2)
    // ---- global res-side facts (fixed) ----
    requires |res1.a_cp| == nlook && |res1.a_clk| == nlook
    requires CM.LookCpSetWithClk(res1) && CM.LookCpsLE(res1, |str|)
    requires CM.LookCpsOracleTrue(res1, ov)
    requires M.FLookLoopChildLinkOk(crv, str, res1, 1, R.max_lookaround(ast), ov, ncap, nlook, nquant)
    // ---- the OWNER package (A1/A2's conclusions at g2's innermost owner) ----
    requires g2 in PIV.CapIdsInLooks(re)
    requires owner in LTB.LookIds(re)
    requires g2 in PIV.CapIds(NI.LookBodyOfRE(re, owner))
    requires g2 !in PIV.CapIdsInLooks(NI.LookBodyOfRE(re, owner))
    requires var rfO := M.FreshBodyMatch(crv, str, owner as int, res1, ov, ncap, nlook, nquant);
             rfO.Some? && g2 in PIV.GmOfLive(NI.LookBodyOfRE(re, owner),
                                             rfO.value.capture_regs, rfO.value.look_regs, rfO.value.quant_regs)
    // ---- per-level data ----
    requires A in LTB.LookIds(re)
    requires host == NI.LookBodyOfRE(re, A)
    requires M.MatchedPosLA(crv, res1, A as int)
    requires g2 in PIV.CapIds(host)
    requires PIV.PathPresentLk(host, res0.a_clk, res1.a_clk, res2.a_clk, -1, g2)
    ensures var lsub := SubFirstLeafAt(rer, crv, str, A as int, res1);
            lsub.Some? && g2 in lsub.value
    requires crv.f_look_types[A as int].Lookbehind?
    decreases |LTB.LookIds(host)|, 0
  {
    // (2026-08-25) this lemma takes the L4-perf OPAQUE bundles (`117b6aa`) but its
    // body reads their foralls (`FrameEntryOk` at A, `OracleOkSuffix` at cps) —
    // reveal them. (Never re-verified after the perf pass; failed 3 asserts.)
    reveal M.OracleSufAllO(), M.FrameEntryAllO();
    var maxlook := R.max_lookaround(ast);
    var cpA := AReg.get_cp(res1, A as int).value;
    RL.AAsArraysLaws(res1);
    assert AI.get_idx(res1.a_cp, A as int) >= 0 && cpA == AI.get_idx(res1.a_cp, A as int);
    assert 0 <= cpA <= |str|;                                    // LookCpsLE(res1)
    var inpA := PIV.InpOfCp(str, cpA);
    var bodycode := CP.compile_to_bytecode(host);

    assert {:split_here} true;   // (E3) section boundary: its own assertion batch
    // ---- the row at A: la_A + host tie + statics ----
    assert 1 <= A <= maxlook && (A as int) in qm.looks;
    assert GateStaticAtNested(qm, re, crv, A as int, ncap, nlook, nquant);   // GateStaticsOkNested
    var laA: R.lookaround, bA: R.regex :|
      LTB.LookEntryOk(crv, A as int, laA, bA)
      && T.TransWf(bA) && NR.NestedFragmentRE(bA)
      && NR.NegLooksLookFreeRE(bA)
      && (laA.Lookbehind? ==> NR.LBOnlyLooksRE(bA))
      && (!laA.Lookbehind? ==> L5ScopeV1RE(bA))
      && qm.looks[A as int].0 == T.TrLookaround(laA)
      && qm.looks[A as int].1 == T.Translate(bA)
      && (set g: LG.GroupId | g in L.DefGroups(T.Translate(bA))) <= PIV.CapIdsInLooks(re)
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
    assert {:split_here} true;   // (E3) section boundary: its own assertion batch
    // ==== (L5 F7c-4) LOOKBEHIND lid: lift via the FLIP twins ====
    M.LookBodyFactsL5(re, crv, A);
    var laN: R.lookaround :| LTB.LookEntryOk(crv, A as int, laN, host) && (laN.Lookbehind? ==> NR.LBOnlyLooksRE(host));
    assert laN == laA;
    assert NR.LBOnlyLooksRE(host);
    FG.LBOnlyEquiv(host);
    assert FST.LBOnlyLooksRE(host);
    if g2 !in PIV.CapIdsInLooks(host) {
      assert {:split_here} true;   // (E3) section boundary: its own assertion batch
      // ---- BASE: g2 DIRECT in host ====
      assert M.FrameEntryOk(crv, laA, host,
                            PIV.CaptureRegsSet(PIV.CapIdsInLooks(re)), M.LookIdSet(re));
      M.InnermostOwnerUnique(re, g2, owner, A);
      assert owner == A;
      var rfO := M.FreshBodyMatch(crv, str, A as int, res1, ov, ncap, nlook, nquant);
      assert rfO.Some?
             && g2 in PIV.GmOfLive(host, rfO.value.capture_regs, rfO.value.look_regs, rfO.value.quant_regs);
      // the body-restricted qmap (LmapOk on `host`, all-columns oracle)
      var qmB0 := AR.QMap(qm.quants,
                          map l: int | l in qm.looks && l >= 0 && (l as nat) in LTB.LookIds(host) :: qm.looks[l],
                          qm.ov);
      assert AR.QmapOk(host, qmB0) by { QmapOkLooksIrrel(host, qm, qmB0); }
      assert AR.LmapOk(host, qmB0) by { LmapOkRestrict(host, qm, qmB0); }
      assert OE.OracleColsOk(rer, qmB0, str) by {
        SufAllToColsOk(rer, qm, str);
        OracleColsOkRestrict(rer, qm, qmB0, str);
      }
      FreshBodyDirectInSubFirstLeafLB(rer, qmB0, crv, str, ov, A, res1, host, g2,
                                      ncap, nlook, nquant);
    } else {
      assert {:split_here} true;   // (E3) section boundary: its own assertion batch
      // ---- DEEP: descend through g2's top-in-host ancestor A1 (per-hop kind dispatch) ----
      assert M.FrameEntryOk(crv, laA, host,
                            PIV.CaptureRegsSet(PIV.CapIdsInLooks(re)), M.LookIdSet(re));
      var ownH := NI.InnermostOwnerDirect(host, g2);
      var A1 := ReconLiveTopAncestor(host, g2, ownH);
      assert A1 in NI.TopLookIds(host) && A1 in LTB.LookIds(host)
             && g2 in PIV.CapIds(NI.LookBodyOfRE(host, A1));
      NI.LookBodyLookIdsIn(re, A);                                // LookIds(host) <= LookIds(re)
      assert A1 in LTB.LookIds(re);
      NI.LookBodyCompose(re, A, A1);                              // bodies compose
      var bodyA1 := NI.LookBodyOfRE(re, A1);
      assert bodyA1 == NI.LookBodyOfRE(host, A1);

      // (α) presence descends + A1's res1 clock is set
      NI.LookPathDecomposeNested(host, bodyA1, res0.a_clk, res1.a_clk, res2.a_clk, -1, A1, g2);
      assert AI.get_idx(res1.a_clk, A1 as int) >= 0;
      assert PIV.PathPresentLk(bodyA1, res0.a_clk, res1.a_clk, res2.a_clk, -1, g2);

      // (β) A1 matched in res1 (reverse invariant + LB-only kind pin)
      assert AI.get_idx(res1.a_cp, A1 as int) >= 0;               // LookCpSetWithClk
      assert AReg.get_cp(res1, A1 as int).Some?;
      assert M.MatchedPosLA(crv, res1, A1 as int) by {
        assert GateStaticAtNested(qm, re, crv, A1 as int, ncap, nlook, nquant);
        // (L5 F7f) ONE pick with the hub's FULL conjunct list — a SUBSET pick times
        // out under {:isolate_assertions} (the hub's list changed with the flip).
        var la1: R.lookaround, b1: R.regex :| LTB.LookEntryOk(crv, A1 as int, la1, b1)
                                              && T.TransWf(b1) && NR.NestedFragmentRE(b1)
                                              && NR.NegLooksLookFreeRE(b1)
                                              && (la1.Lookbehind? ==> NR.LBOnlyLooksRE(b1))
                                              && (!la1.Lookbehind? ==> L5ScopeV1RE(b1))
                                              && qm.looks[A1 as int].0 == T.TrLookaround(la1)
                                              && qm.looks[A1 as int].1 == T.Translate(b1)
                                              && (set gx: LG.GroupId | gx in L.DefGroups(T.Translate(b1))) <= PIV.CapIdsInLooks(re)
                                              && var bc1 := CP.compile_to_bytecode(b1);
                                              |bc1| >= 1
                                              && PSM.StaticOkNestedRE(qm, b1, bc1, |bc1| - 1)
                                              && PSM.SizesOkRE(b1, ncap, nlook, nquant)
                                              && ((la1.NegLookbehind? || la1.NegLookahead?) ==> NR.CaptureFreeRE(b1));
        assert crv.f_look_types[A1 as int] == la1;
        assert b1 == bodyA1 by {
          NI.LookBodyOfTablesTie(re, crv, A1);
          var la1T: R.lookaround :| LTB.LookEntryOk(crv, A1 as int, la1T, bodyA1);
          assert crv.f_look_ast[A1 as int] == b1 == bodyA1;
        }
        assert la1.Lookbehind? || la1.NegLookbehind? by {
          assert LTB.LookTablesOk(host, crv);                     // FrameEntryOk
          FG.LookRowLBOnly(host, crv, A1);
        }
        if la1.NegLookbehind? {
          assert NR.CaptureFreeRE(bodyA1);                       // the pick's negative clause
          PIV.CaptureFreeNoCapIds(bodyA1);
          assert g2 in PIV.CapIds(bodyA1);
          assert false;
        }
        assert la1.Lookbehind?;                                  // the only kind left
        assert AI.capture_type(crv.f_look_types[A1 as int]) by {
          assert crv.f_look_types[A1 as int] == la1;
        }
      }

      // (δ) the body-restricted qmap + statics (site supplies statics for the
      //     flipped world inside the LB carrier — it only needs LmapOk +
      //     whole-string oracle on `host`).
      var qmB := AR.QMap(qm.quants,
                         map l: int | l in qm.looks && l >= 0 && (l as nat) in LTB.LookIds(host) :: qm.looks[l],
                         qm.ov);
      assert AR.QmapOk(host, qmB) by { QmapOkLooksIrrel(host, qm, qmB); }
      assert AR.LmapOk(host, qmB) by { LmapOkRestrict(host, qm, qmB); }
      assert OE.OracleColsOk(rer, qmB, str) by {
        SufAllToColsOk(rer, qm, str);
        OracleColsOkRestrict(rer, qm, qmB, str);
      }

      // (γ) A1's BACKWARD spec leaf EXISTS (oracle at the recorded cp) — the
      //     per-hop kind dispatch is by `LidDir`, so the backward arm builds
      //     the WP.Backward tree and the forward arm the WP.Forward one.
      // (ε) the BACKWARD body replay: the LB carrier at `compile(reverse_regex(host))`.
      var cpA := AReg.get_cp(res1, A as int).value;
      var inpA := PIV.InpOfCp(str, cpA);
      var bodycodeB := CP.compile_to_bytecode(R.reverse_regex(host));
      var cdnA := crv.f_look_cdns[A as int];
      LookNestBackTFromBodyReplayLB(rer, qmB, laA, host, bodycodeB, crv, str, cpA, ov,
                                    cdnA, crv.f_plus_bc, ncap, nlook, nquant);
      var rbT := LFU.ComputeTr(rer, [LS.Areg(T.Translate(host))], inpA, LG.Empty, WP.Backward);
      var rb := LT.TreeRes(rbT, LG.Empty, inpA, WP.Backward);
      // (gamma) the BACKWARD spec leaf EXISTS: res1's record at A is oracle-true,
      // so host's spec tree matches BACKWARD at cpA (the LB twin of the forward
      // arm's FirstLeaf(t, inpA).Some? block).
      assert rb.Some? by {
        assert LOr.view_get_oracle(ov, AI.get_idx(res1.a_cp, A as int), A as int);   // LookCpsOracleTrue
        assert LL.OracleOkSuffix(rer, qm, inpA);
        assert LL.OracleOkAt(rer, qm, inpA);
        assert (A as int) in qm.looks
               && qm.looks[A as int] == (T.TrLookaround(laA), T.Translate(host));
        assert TREP.CpOf(inpA) == cpA by { LS.ReverseLength(str[..cpA]); }
        assert L.LkDir(T.TrLookaround(laA)) == WP.Backward;      // laA.Lookbehind?
      }
      var rfP := AI.FFindMatchPlus(bodycodeB, host, crv.f_plus_bc, str, ov, LAnc.Backward, cpA,
                                   AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant),
                                   0, cdnA).0;
      assert rfP.Some?;                                            // the carrier's None-iff at rb.Some?
      var rfA := rfP.value;
      var Sh := PIV.CapIdsInLooks(host);
      var gmtH := rb.value.1;
      assert LookNestBackTTopDeep(rer, host, crv, str, ov, Sh, gmtH, rfA, ncap, nlook, nquant);
      assert CM.LookClkSetWithCp(rfA.look_regs) && CM.LookCpSetWithClk(rfA.look_regs);

      // (ζ) rf_A IS FreshBodyMatch(A, res1) — the backward fresh run.
      // The unfold's row witnesses, hoisted (they are what the by-block needs):
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
      assert rfA == rfFresh.value by {                      // (L5 F7f perf) via the helper
        BackFreshPlusIsPlain(host, bodycodeB, crv.f_plus_bc, str, ov, cpA, cdnA, ncap, nlook, nquant);
      }
      // (η) the LEVEL-LINK at (A, A1): res1's record at A1 IS rf_A's
      assert A1 as int in M.DirectLidSet(host) by {
        TopEqDirectLookIds(host);
        assert A1 in M.DirectLookIds(host);
      }
      assert rfFresh.Some? by { assert rfA == rfFresh.value; }
      assert AReg.get_cp(res1, A1 as int) == AReg.get_cp(rfFresh.value.look_regs, A1 as int) by {
        assert M.FLookLoopChildLinkOk(crv, str, res1, 1, maxlook, ov, ncap, nlook, nquant);
        assert 1 <= A as int <= maxlook && M.MatchedPosLA(crv, res1, A as int);
        assert host == M.VBody(crv, A as int);
        assert (A1 as int) in M.DirectLidSet(host);
      }
      assert AReg.get_cp(res1, A1 as int) == AReg.get_cp(rfA.look_regs, A1 as int) by {
        assert rfA == rfFresh.value;
      }

      // (θ) A1 matched + dominant ON rf_A's banks
      assert M.MatchedPosLA(crv, rfA.look_regs, A1 as int) by {
        assert AReg.get_cp(rfA.look_regs, A1 as int).Some?;
        assert AI.capture_type(crv.f_look_types[A1 as int]);      // established at (β)
      }
      var L1 := AI.get_idx(rfA.look_regs.a_clk, A1 as int);
      assert L1 >= 0 by {
        assert 0 <= A1 as int < |rfA.look_regs.a_cp| && rfA.look_regs.a_cp[A1 as int] >= 0;
        assert AI.get_idx(rfA.look_regs.a_cp, A1 as int) >= 0;
        assert CM.LookClkSetWithCp(rfA.look_regs);
      }
      assert NI.LookPathDom(host, L1, rfA.quant_regs.a_clk, A1) by {
        GNotUnderQuantLLookBody(re, A, g2);
        assert M.GNotUnderQuantL(T.Translate(host), g2);
        M.GNotUnderQuantLNoAncQuants(host, g2);
        assert PIV.AncQuants(host, g2) == {};
        NI.LookPathDomNoAncQuants(host, L1, rfA.quant_regs.a_clk, A1, g2);
      }

      // (ι) the RECURSIVE landing at A1, transported onto rf_A's bank
      assert |LTB.LookIds(bodyA1)| < |LTB.LookIds(host)| by {
        NI.LookBodyLookIdsIn(host, A1);
        LookIdNotInOwnBody(host, A1);
        SubsetCardLt(LTB.LookIds(bodyA1), LTB.LookIds(host), A1);
      }
      DeepFindRec(rer, qm, crv, str, ast, re, ov, res0, res1, res2,
                  bodyA1, A1, owner, g2, ncap, nlook, nquant);
      var lsub1 := SubFirstLeafAt(rer, crv, str, A1 as int, res1);
      assert lsub1.Some? && g2 in lsub1.value;
      assert SubFirstLeafAt(rer, crv, str, A1 as int, rfA.look_regs) == lsub1;   // reads only get_cp at A1

      // (κ) LAND via the DEEP carrier, then identify the leaf with the
      //     backward `BackLeafAt(host, cpA)` (== SubFirstLeafAt(A, res1))
      DescentLandTopDeep(rer, host, crv, str, ov, Sh, gmtH, rfA, A1, g2, ncap, nlook, nquant);
      assert g2 in gmtH;
      assert host == M.VBody(crv, A as int);
      assert crv.f_look_types[A as int].Lookbehind?;
      SubFirstLeafAtIsBackLeaf(rer, crv, str, A as int, res1, host);
      assert SubFirstLeafAt(rer, crv, str, A as int, res1) == FG.BackLeafAt(rer, host, str, cpA);
      assert SubFirstLeafAt(rer, crv, str, A as int, res1).value == gmtH;
    }
  }

  /** (perf) The FORWARD DEEP arm of `DeepFindRec`, extracted so its assertions are
      checked in a small context (same treatment as `DeepFindRecLB`).
      Mutually recursive with `DeepFindRec` on `(|LookIds(host)|, arm)`. */
  lemma DeepFindRecFwdDeep(
    rer: LW.RegExpRecord, qm: AR.QMap, crv: CP.FCompiled, str: string, ast: R.regex, re: R.regex,
    ov: LOr.OracleView, res0: AReg.Regs, res1: AReg.Regs, res2: AReg.Regs,
    host: R.regex, A: nat, owner: nat, g2: nat, ncap: int, nlook: int, nquant: int)
    // ---- whole-regex statics (fixed through the recursion) ----
    requires T.TransWf(re) && NR.NestedFragmentRE(re) && NR.L5ScopeRE(re) && L5ScopeV1RE(re)
    requires PIV.CapUnique(re) && PIV.QuantUnique(re) && LTB.LookUnique(re)
    requires LTB.LookTablesOk(re, crv)
    requires |crv.f_look_types| == |crv.f_look_ast|
    requires forall x: nat :: x in LTB.LookIds(re) ==> 1 <= x <= R.max_lookaround(ast)
    requires forall x: nat :: x in LTB.LookIds(re) ==> (x as int) in qm.looks
    requires nlook == R.max_lookaround(ast) + 1
    requires qm.ov == ov && !rer.multiline && !rer.ignoreCase && |ov| == |str| + 1
    requires forall l: int :: l in qm.looks ==> l >= 0
    requires M.OracleSufAllO(rer, qm, str)
    requires GateStaticsOkNested(qm, re, crv, ncap, nlook, nquant)
    requires M.FrameEntryAllO(crv, re, ast)
    // ---- the fragment's no-quant scope for g2 ----
    requires M.GNotUnderQuantL(T.Translate(re), g2)
    // ---- global res-side facts (fixed) ----
    requires |res1.a_cp| == nlook && |res1.a_clk| == nlook
    requires CM.LookCpSetWithClk(res1) && CM.LookCpsLE(res1, |str|)
    requires CM.LookCpsOracleTrue(res1, ov)
    requires M.FLookLoopChildLinkOk(crv, str, res1, 1, R.max_lookaround(ast), ov, ncap, nlook, nquant)
    // ---- the OWNER package (A1/A2's conclusions at g2's innermost owner) ----
    requires g2 in PIV.CapIdsInLooks(re)
    requires owner in LTB.LookIds(re)
    requires g2 in PIV.CapIds(NI.LookBodyOfRE(re, owner))
    requires g2 !in PIV.CapIdsInLooks(NI.LookBodyOfRE(re, owner))
    requires var rfO := M.FreshBodyMatch(crv, str, owner as int, res1, ov, ncap, nlook, nquant);
             rfO.Some? && g2 in PIV.GmOfLive(NI.LookBodyOfRE(re, owner),
                                             rfO.value.capture_regs, rfO.value.look_regs, rfO.value.quant_regs)
    // ---- per-level data ----
    requires A in LTB.LookIds(re)
    requires host == NI.LookBodyOfRE(re, A)
    requires M.MatchedPosLA(crv, res1, A as int)
    requires g2 in PIV.CapIds(host)
    requires PIV.PathPresentLk(host, res0.a_clk, res1.a_clk, res2.a_clk, -1, g2)
    ensures var lsub := SubFirstLeafAt(rer, crv, str, A as int, res1);
            lsub.Some? && g2 in lsub.value
    requires !crv.f_look_types[A as int].Lookbehind?
    requires g2 in PIV.CapIdsInLooks(host)
    decreases |LTB.LookIds(host)|, 0
  {
    // (2026-08-25) this lemma takes the L4-perf OPAQUE bundles (`117b6aa`) but its
    // body reads their foralls (`FrameEntryOk` at A, `OracleOkSuffix` at cps) —
    // reveal them. (Never re-verified after the perf pass; failed 3 asserts.)
    reveal M.OracleSufAllO(), M.FrameEntryAllO();
    var maxlook := R.max_lookaround(ast);
    var cpA := AReg.get_cp(res1, A as int).value;
    RL.AAsArraysLaws(res1);
    assert AI.get_idx(res1.a_cp, A as int) >= 0 && cpA == AI.get_idx(res1.a_cp, A as int);
    assert 0 <= cpA <= |str|;                                    // LookCpsLE(res1)
    var inpA := PIV.InpOfCp(str, cpA);
    var bodycode := CP.compile_to_bytecode(host);

    // ---- the row at A: la_A + host tie + statics ----
    assert 1 <= A <= maxlook && (A as int) in qm.looks;
    assert GateStaticAtNested(qm, re, crv, A as int, ncap, nlook, nquant);   // GateStaticsOkNested
    var laA: R.lookaround, bA: R.regex :|
      LTB.LookEntryOk(crv, A as int, laA, bA)
      && T.TransWf(bA) && NR.NestedFragmentRE(bA)
      && NR.NegLooksLookFreeRE(bA)
      && (laA.Lookbehind? ==> NR.LBOnlyLooksRE(bA))
      && (!laA.Lookbehind? ==> L5ScopeV1RE(bA))
      && qm.looks[A as int].0 == T.TrLookaround(laA)
      && qm.looks[A as int].1 == T.Translate(bA)
      && (set g: LG.GroupId | g in L.DefGroups(T.Translate(bA))) <= PIV.CapIdsInLooks(re)
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
    assert laA.Lookahead?;
    assert M.FrameEntryOk(crv, laA, host,
                          PIV.CaptureRegsSet(PIV.CapIdsInLooks(re)), M.LookIdSet(re));
    assert PIV.CapUnique(host) && PIV.QuantUnique(host) && LTB.LookUnique(host)
           && LTB.LookTablesOk(host, crv);                          // FrameEntryOk

    // ==== DEEP: descend through g2's top-in-host ancestor A1 ====
    var ownH := NI.InnermostOwnerDirect(host, g2);
    var A1 := ReconLiveTopAncestor(host, g2, ownH);
    assert A1 in NI.TopLookIds(host) && A1 in LTB.LookIds(host)
           && g2 in PIV.CapIds(NI.LookBodyOfRE(host, A1));
    NI.LookBodyLookIdsIn(re, A);                                // LookIds(host) <= LookIds(re)
    assert A1 in LTB.LookIds(re);
    NI.LookBodyCompose(re, A, A1);                              // bodies compose
    var bodyA1 := NI.LookBodyOfRE(re, A1);
    assert bodyA1 == NI.LookBodyOfRE(host, A1);

    // (α) presence descends + A1's res1 clock is set
    NI.LookPathDecomposeNested(host, bodyA1, res0.a_clk, res1.a_clk, res2.a_clk, -1, A1, g2);
    assert AI.get_idx(res1.a_clk, A1 as int) >= 0;
    assert PIV.PathPresentLk(bodyA1, res0.a_clk, res1.a_clk, res2.a_clk, -1, g2);

    // (β) A1 matched in res1 (reverse invariant + type pin)
    assert AI.get_idx(res1.a_cp, A1 as int) >= 0;               // LookCpSetWithClk
    assert AReg.get_cp(res1, A1 as int).Some?;
    assert M.MatchedPosLA(crv, res1, A1 as int) by {
      assert GateStaticAtNested(qm, re, crv, A1 as int, ncap, nlook, nquant);
      // (L5 F7f) FULL conjunct list: a subset pick times out under the kind-split hub
      var la1: R.lookaround, b1: R.regex :|
        LTB.LookEntryOk(crv, A1 as int, la1, b1)
        && T.TransWf(b1) && NR.NestedFragmentRE(b1)
        && NR.NegLooksLookFreeRE(b1)
        && (la1.Lookbehind? ==> NR.LBOnlyLooksRE(b1))
        && (!la1.Lookbehind? ==> L5ScopeV1RE(b1))
        && qm.looks[A1 as int].0 == T.TrLookaround(la1)
        && qm.looks[A1 as int].1 == T.Translate(b1)
        && (set gx: LG.GroupId | gx in L.DefGroups(T.Translate(b1))) <= PIV.CapIdsInLooks(re)
        && var bc1 := CP.compile_to_bytecode(b1);
        |bc1| >= 1
        && PSM.StaticOkNestedRE(qm, b1, bc1, |bc1| - 1)
        && PSM.SizesOkRE(b1, ncap, nlook, nquant)
        && ((la1.NegLookbehind? || la1.NegLookahead?) ==> NR.CaptureFreeRE(b1));
      assert crv.f_look_types[A1 as int] == la1;
      assert b1 == bodyA1 by {
        NI.LookBodyOfTablesTie(re, crv, A1);
        var la1T: R.lookaround :| LTB.LookEntryOk(crv, A1 as int, la1T, bodyA1);
        assert crv.f_look_ast[A1 as int] == b1 == bodyA1;
      }
      // the negatives are capture-free, but g2 lives in bodyA1
      if la1.NegLookahead? || la1.NegLookbehind? {
        assert NR.CaptureFreeRE(bodyA1);
        PIV.CaptureFreeNoCapIds(bodyA1);
        assert g2 in PIV.CapIds(bodyA1);
        assert false;
      }
      assert AI.capture_type(crv.f_look_types[A1 as int]);
    }

    // (γ) rf_A.Some? via the oracle: res1's record at A is oracle-true, so
    //     host's spec tree matches at cpA.
    var t := LFU.ComputeTr(rer, [LS.Areg(T.Translate(host))], inpA, LG.Empty, WP.Forward);
    assert LT.FirstLeaf(t, inpA).Some? by {
      assert LOr.view_get_oracle(ov, AI.get_idx(res1.a_cp, A as int), A as int);   // LookCpsOracleTrue
      assert LL.OracleOkSuffix(rer, qm, inpA);
      assert LL.OracleOkAt(rer, qm, inpA);
      assert (A as int) in qm.looks
             && qm.looks[A as int] == (T.TrLookaround(laA), T.Translate(host));
      assert TREP.CpOf(inpA) == cpA by { LS.ReverseLength(str[..cpA]); }
      assert L.LkDir(T.TrLookaround(laA)) == WP.Forward;        // Lookahead
      assert LT.TreeRes(LFU.ComputeTr(rer, [LS.Areg(T.Translate(host))], inpA, LG.Empty, WP.Forward),
                        LG.Empty, inpA, WP.Forward).Some?;
      assert LT.FirstLeaf(t, inpA) == LT.TreeRes(t, LG.Empty, inpA, WP.Forward);
    }

    // (δ) the body-restricted qmap + statics
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
    assert OE.OracleColsOk(rer, qmB, str) by {                       // (L5 F7d)
      SufAllToColsOk(rer, qm, str);
      OracleColsOkRestrict(rer, qm, qmB, str);
    }

    // (ε) the per-body replay: both carriers + None-iff + bank invariants at rf_A
    var cdnA := crv.f_look_cdns[A as int];
    LookNestBackTFromBodyReplay(rer, qmB, laA, host, bodycode, endlH, 0, crv, str, cpA, ov,
                                cdnA, crv.f_plus_bc, ncap, nlook, nquant);
    var rfP := AI.FFindMatchPlus(bodycode, host, crv.f_plus_bc, str, ov, LAnc.Forward, cpA,
                                 AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant),
                                 0, cdnA).0;
    assert rfP.Some?;                                            // None-iff + FirstLeaf.Some?
    var rfA := rfP.value;
    var Sh := PIV.CapIdsInLooks(host);
    var gmtH := LT.FirstLeaf(t, inpA).value.1;
    assert LookNestBackTTopDeep(rer, host, crv, str, ov, Sh, gmtH, rfA, ncap, nlook, nquant);
    assert CM.LookClkSetWithCp(rfA.look_regs) && CM.LookCpSetWithClk(rfA.look_regs);

    // (ζ) rf_A IS FreshBodyMatch(A, res1) (same fresh run at the same position)
    var rfFresh := M.FreshBodyMatch(crv, str, A as int, res1, ov, ncap, nlook, nquant);
    assert rfFresh == AI.FFindMatch(bodycode, str,
                                    AI.FInitState(bodycode, cpA, AReg.init_regs(ncap), AReg.init_regs(nlook),
                                                  AReg.init_regs(nquant), 0, AI.cp_context(cpA, str, LAnc.Forward)),
                                    ov, LAnc.Forward, cdnA).0 by {
      assert AI.capture_direction(crv.f_look_types[A as int]) == LAnc.Forward;
      assert CP.capture_regex(crv.f_look_types[A as int], M.VBody(crv, A as int)) == host;
    }
    // (η) the LEVEL-LINK at (A, A1): res1's record at A1 IS rf_A's
    assert A1 as int in M.DirectLidSet(host) by {
      TopEqDirectLookIds(host);
      assert A1 in M.DirectLookIds(host);
    }
    assert AReg.get_cp(res1, A1 as int) == AReg.get_cp(rfFresh.value.look_regs, A1 as int) by {
      assert M.FLookLoopChildLinkOk(crv, str, res1, 1, maxlook, ov, ncap, nlook, nquant);
      assert 1 <= A as int <= maxlook && M.MatchedPosLA(crv, res1, A as int);
      assert rfFresh.Some?;
    }
    assert rfA == rfFresh.value by {
      // FReconstructPlus is the identity on the QuantRegsFinal fresh run.
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
    assert AReg.get_cp(res1, A1 as int) == AReg.get_cp(rfA.look_regs, A1 as int);

    // (θ) A1 matched + dominant ON rf_A's banks
    assert M.MatchedPosLA(crv, rfA.look_regs, A1 as int) by {
      assert AReg.get_cp(rfA.look_regs, A1 as int).Some?;
    }
    var L1 := AI.get_idx(rfA.look_regs.a_clk, A1 as int);
    assert L1 >= 0 by {
      // get_cp Some ==> in-range with a_cp[A1] >= 0 (definitional), then the
      // forward invariant LookClkSetWithCp lifts it to the clock.
      assert 0 <= A1 as int < |rfA.look_regs.a_cp| && rfA.look_regs.a_cp[A1 as int] >= 0;
      assert AI.get_idx(rfA.look_regs.a_cp, A1 as int) >= 0;
      assert CM.LookClkSetWithCp(rfA.look_regs);
    }
    assert NI.LookPathDom(host, L1, rfA.quant_regs.a_clk, A1) by {
      GNotUnderQuantLLookBody(re, A, g2);
      assert M.GNotUnderQuantL(T.Translate(host), g2);
      M.GNotUnderQuantLNoAncQuants(host, g2);
      assert PIV.AncQuants(host, g2) == {};
      NI.LookPathDomNoAncQuants(host, L1, rfA.quant_regs.a_clk, A1, g2);
    }

    // (ι) the RECURSIVE landing at A1, transported onto rf_A's bank
    assert |LTB.LookIds(bodyA1)| < |LTB.LookIds(host)| by {
      NI.LookBodyLookIdsIn(host, A1);
      LookIdNotInOwnBody(host, A1);
      SubsetCardLt(LTB.LookIds(bodyA1), LTB.LookIds(host), A1);
    }
    DeepFindRec(rer, qm, crv, str, ast, re, ov, res0, res1, res2,
                bodyA1, A1, owner, g2, ncap, nlook, nquant);
    var lsub1 := SubFirstLeafAt(rer, crv, str, A1 as int, res1);
    assert lsub1.Some? && g2 in lsub1.value;
    assert SubFirstLeafAt(rer, crv, str, A1 as int, rfA.look_regs) == lsub1;   // reads only get_cp at A1

    // (κ) LAND via the DEEP carrier, then identify the leaf with SubFirstLeafAt(A, res1)
    DescentLandTopDeep(rer, host, crv, str, ov, Sh, gmtH, rfA, A1, g2, ncap, nlook, nquant);
    assert g2 in gmtH;
    assert LidDir(crv, A as int) == WP.Forward;               // laA.Lookahead? (dispatch)
    BodyReplayGmtIsSubFirstLeaf(rer, crv, str, A as int, res1, host);
    assert SubFirstLeafAt(rer, crv, str, A as int, res1) == Some(gmtH);
  }

  lemma DeepFindRec(
    rer: LW.RegExpRecord, qm: AR.QMap, crv: CP.FCompiled, str: string, ast: R.regex, re: R.regex,
    ov: LOr.OracleView, res0: AReg.Regs, res1: AReg.Regs, res2: AReg.Regs,
    host: R.regex, A: nat, owner: nat, g2: nat, ncap: int, nlook: int, nquant: int)
    // ---- whole-regex statics (fixed through the recursion) ----
    requires T.TransWf(re) && NR.NestedFragmentRE(re) && NR.L5ScopeRE(re) && L5ScopeV1RE(re)
    requires PIV.CapUnique(re) && PIV.QuantUnique(re) && LTB.LookUnique(re)
    requires LTB.LookTablesOk(re, crv)
    requires |crv.f_look_types| == |crv.f_look_ast|
    requires forall x: nat :: x in LTB.LookIds(re) ==> 1 <= x <= R.max_lookaround(ast)
    requires forall x: nat :: x in LTB.LookIds(re) ==> (x as int) in qm.looks
    requires nlook == R.max_lookaround(ast) + 1
    requires qm.ov == ov && !rer.multiline && !rer.ignoreCase && |ov| == |str| + 1
    requires forall l: int :: l in qm.looks ==> l >= 0
    requires M.OracleSufAllO(rer, qm, str)
    requires GateStaticsOkNested(qm, re, crv, ncap, nlook, nquant)
    requires M.FrameEntryAllO(crv, re, ast)
    // ---- the fragment's no-quant scope for g2 ----
    requires M.GNotUnderQuantL(T.Translate(re), g2)
    // ---- global res-side facts (fixed) ----
    requires |res1.a_cp| == nlook && |res1.a_clk| == nlook
    requires CM.LookCpSetWithClk(res1) && CM.LookCpsLE(res1, |str|)
    requires CM.LookCpsOracleTrue(res1, ov)
    requires M.FLookLoopChildLinkOk(crv, str, res1, 1, R.max_lookaround(ast), ov, ncap, nlook, nquant)
    // ---- the OWNER package (A1/A2's conclusions at g2's innermost owner) ----
    requires g2 in PIV.CapIdsInLooks(re)
    requires owner in LTB.LookIds(re)
    requires g2 in PIV.CapIds(NI.LookBodyOfRE(re, owner))
    requires g2 !in PIV.CapIdsInLooks(NI.LookBodyOfRE(re, owner))
    requires var rfO := M.FreshBodyMatch(crv, str, owner as int, res1, ov, ncap, nlook, nquant);
             rfO.Some? && g2 in PIV.GmOfLive(NI.LookBodyOfRE(re, owner),
                                             rfO.value.capture_regs, rfO.value.look_regs, rfO.value.quant_regs)
    // ---- per-level data ----
    requires A in LTB.LookIds(re)
    requires host == NI.LookBodyOfRE(re, A)
    requires M.MatchedPosLA(crv, res1, A as int)
    requires g2 in PIV.CapIds(host)
    requires PIV.PathPresentLk(host, res0.a_clk, res1.a_clk, res2.a_clk, -1, g2)
    ensures var lsub := SubFirstLeafAt(rer, crv, str, A as int, res1);
            lsub.Some? && g2 in lsub.value
    decreases |LTB.LookIds(host)|, 1
  {
    // (2026-08-25) this lemma takes the L4-perf OPAQUE bundles (`117b6aa`) but its
    // body reads their foralls (`FrameEntryOk` at A, `OracleOkSuffix` at cps) —
    // reveal them. (Never re-verified after the perf pass; failed 3 asserts.)
    reveal M.OracleSufAllO(), M.FrameEntryAllO();
    var maxlook := R.max_lookaround(ast);
    var cpA := AReg.get_cp(res1, A as int).value;
    RL.AAsArraysLaws(res1);
    assert AI.get_idx(res1.a_cp, A as int) >= 0 && cpA == AI.get_idx(res1.a_cp, A as int);
    assert 0 <= cpA <= |str|;                                    // LookCpsLE(res1)
    var inpA := PIV.InpOfCp(str, cpA);
    var bodycode := CP.compile_to_bytecode(host);

    // ---- the row at A: la_A + host tie + statics ----
    assert 1 <= A <= maxlook && (A as int) in qm.looks;
    assert GateStaticAtNested(qm, re, crv, A as int, ncap, nlook, nquant);   // GateStaticsOkNested
    var laA: R.lookaround, bA: R.regex :|
      LTB.LookEntryOk(crv, A as int, laA, bA)
      && T.TransWf(bA) && NR.NestedFragmentRE(bA)
      && NR.NegLooksLookFreeRE(bA)
      && (laA.Lookbehind? ==> NR.LBOnlyLooksRE(bA))
      && (!laA.Lookbehind? ==> L5ScopeV1RE(bA))
      && qm.looks[A as int].0 == T.TrLookaround(laA)
      && qm.looks[A as int].1 == T.Translate(bA)
      && (set g: LG.GroupId | g in L.DefGroups(T.Translate(bA))) <= PIV.CapIdsInLooks(re)
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
      // (L5 F7f perf) the LOOKBEHIND arm lives in its own lemma (small VC context).
      DeepFindRecLB(rer, qm, crv, str, ast, re, ov, res0, res1, res2,
                    host, A, owner, g2, ncap, nlook, nquant);
    } else {
      assert !laA.Lookbehind? by { assert crv.f_look_types[A as int] == laA; }
      if g2 !in PIV.CapIdsInLooks(host) {
        // (perf) the forward BASE arm lives in its own lemma.
        DeepFindRecFwdBase(rer, qm, crv, str, ast, re, ov, res0, res1, res2,
                           host, A, owner, g2, ncap, nlook, nquant);
      } else {
        // (perf) the forward DEEP arm lives in its own lemma.
        DeepFindRecFwdDeep(rer, qm, crv, str, ast, re, ov, res0, res1, res2,
                           host, A, owner, g2, ncap, nlook, nquant);
      }
    }
  }

  /** (FORWARD membership + VALUE recursion — the mirror of `DeepFindRec`) For a
      capture `g` PRESENT in ancestor `A`'s sub-first-leaf at `res1`'s recorded
      position, the ENGINE reconstruction carries `g`: presence path within
      `host` on the reconstructed banks, `res0` set at `g`, dominance, and the
      VALUE tie (the leaf value IS the raw `LiveRange` of `res0`, as a
      `NormRange` equality). Recursion on `|LookIds(host)|`.

      BASE (`g` DIRECT): `SubFirstLeafDirectInFresh` moves `g` (with value) into
      the FRESH body match; the presence extractor + the no-look/no-quant path
      transport (`PathPresentLkDirectAgree`) move it onto the reconstructed banks
      (the FLookLoop value lift `FLookLoopValueOkFull` supplies the register
      agreements at `A`'s direct captures).

      DEEP: `A1` := `g`'s top-in-`host` ancestor. The replay's FORWARD carrier
      (`LookNestOkTTop`, leaf-witness `g`) gives `A1` crossed + dominant on the
      fresh body match `rf_A`; the REGION-EQUALITY deep carrier's ⊆ direction
      pushes `g` (with value) into `A1`'s sub-first-leaf; the LEVEL-LINK re-keys
      it onto `res1`; the RECURSIVE call delivers the body-level engine facts;
      `LookPathComposeNested` + the top-lid transports (`LookPathPresentAgreeTop`
      / `LookPathPresentLkFromPresentTop`) compose the presence up to `host`.

      (L5 F7c-4) The owner lid `A` dispatches on its kind: a LOOKAHEAD lid uses
      the forward fresh match + `SubFirstLeafDirectInFresh` (unchanged); a
      LOOKBEHIND lid uses the backward fresh match through `FG.FreshBodyMatch
      LBUnfold` + the FLIP carrier `LookNestBackTFromBodyReplayLB` and the F7b
      wrappers (`SubFirstLeafDirectInFreshLB`), exactly `GmtTieInside`'s
      `SwapRange` in the LB arm. */
  /** (L5 F7f perf) The LOOKBEHIND arm of `ForwardFindRec`, extracted so its
      assertions are checked in a small context (same treatment as `DeepFindRecLB`).
      Mutually recursive with `ForwardFindRec` on `(|LookIds(host)|, arm)`. */
  /** (perf) The BASE arm of `ForwardFindRecLB` (a LOOKBEHIND owner), extracted: the whole LB arm
      OOM-kills the 80G slice alone at CORES=4. Mutually recursive with `ForwardFindRec` on
      `(|LookIds(host)|, arm)`: ForwardFindRec 2 > ForwardFindRecLB 1 > this 0. */
  lemma ForwardFindRecLBBase(   // (E3) opaque preamble block

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
    requires g !in PIV.CapIdsInLooks(host)
    decreases |LTB.LookIds(host)|, 0
  {
    // (2026-08-29 E3) the preamble is an OPAQUE block: only the facts below reach the arm's VC.
    var maxlook := *;
    var cpA := *;
    var inpA := *;
    var bodycode := *;
    var laA: R.lookaround := *;
    var bA: R.regex := *;
    var laT: R.lookaround := *;
    var endlH: nat := *;
    var laN: R.lookaround := *;
    var qmB := *;
    var bodycodeB := *;
    var cdnA := *;
    var rbT := *;
    var rb := *;
    var rfP := *;
    var lsubA := *;
    var rfA := *;
    var Sh := *;
    var gmtH := *;
    var rfFresh := *;
    opaque
      ensures (rfP.Some?)
      ensures (rb.Some?)
      ensures (rfFresh.Some?)
      ensures (maxlook == R.max_lookaround(ast))
      ensures (cpA == AReg.get_cp(res1, A as int).value)
      ensures (inpA == PIV.InpOfCp(str, cpA))
      ensures (bodycode == CP.compile_to_bytecode(host))
      ensures (LTB.LookEntryOk(crv, A as int, laA, bA)
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
              && ((laA.NegLookbehind? || laA.NegLookahead?) ==> NR.CaptureFreeRE(bA)))
      ensures (LTB.LookEntryOk(crv, A as int, laT, NI.LookBodyOfRE(re, A)))
      ensures (endlH == |bodycode| - 1)
      ensures (LTB.LookEntryOk(crv, A as int, laN, host) && (laN.Lookbehind? ==> NR.LBOnlyLooksRE(host)))
      ensures (qmB == AR.QMap(qm.quants,
                               map l: int | l in qm.looks && l >= 0 && (l as nat) in LTB.LookIds(host) :: qm.looks[l],
                               qm.ov))
      ensures (bodycodeB == CP.compile_to_bytecode(R.reverse_regex(host)))
      ensures (cdnA == crv.f_look_cdns[A as int])
      ensures (rbT == LFU.ComputeTr(rer, [LS.Areg(T.Translate(host))], inpA, LG.Empty, WP.Backward))
      ensures (rb == LT.TreeRes(rbT, LG.Empty, inpA, WP.Backward))
      ensures (rfP == AI.FFindMatchPlus(bodycodeB, host, crv.f_plus_bc, str, ov, LAnc.Backward, cpA,
                                         AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant),
                                         0, cdnA).0)
      ensures (lsubA == SubFirstLeafAt(rer, crv, str, A as int, res1))
      ensures (rfA == rfP.value)
      ensures (Sh == PIV.CapIdsInLooks(host))
      ensures (gmtH == rb.value.1)
      ensures (rfFresh == M.FreshBodyMatch(crv, str, A as int, res1, ov, ncap, nlook, nquant))
      ensures (AI.get_idx(res1.a_cp, A as int) >= 0 && cpA == AI.get_idx(res1.a_cp, A as int))
      ensures (0 <= cpA <= |str|)
      ensures (1 <= A <= maxlook && (A as int) in qm.looks)
      ensures (GateStaticAtNested(qm, re, crv, A as int, ncap, nlook, nquant))
      ensures (bA == host)
      ensures (host == M.VBody(crv, A as int))
      ensures (PSM.StaticOkNestedRE(qm, host, bodycode, endlH))
      ensures (crv.f_look_types[A as int] == laA)
      ensures (NR.LBOnlyLooksRE(host))
      ensures (FST.LBOnlyLooksRE(host))
      ensures (M.FrameEntryOk(crv, laA, host,
                                  PIV.CaptureRegsSet(PIV.CapIdsInLooks(re)), M.LookIdSet(re)))
      ensures (PIV.CapUnique(host) && PIV.QuantUnique(host) && LTB.LookUnique(host)
                   && LTB.LookTablesOk(host, crv))
      ensures (AR.QmapOk(host, qmB))
      ensures (AR.LmapOk(host, qmB))
      ensures (OE.OracleColsOk(rer, qmB, str))
      ensures (LidDir(crv, A as int) == WP.Backward)
      ensures (lsubA == FG.BackLeafAt(rer, host, str, cpA))
      ensures (lsubA.Some? && rb.Some? && lsubA.value == rb.value.1)
      ensures (gmtH == lsubA.value)
      ensures (host == M.VBody(crv, A as int))
      ensures (0 <= (A as int) < |crv.f_look_types| && crv.f_look_types[A as int].Lookbehind?)
      ensures (0 <= (A as int) < |crv.f_look_cdns| && cdnA == crv.f_look_cdns[A as int])
      ensures (AReg.get_cp(res1, A as int).Some? && AReg.get_cp(res1, A as int).value == cpA)
      ensures (rfFresh == AI.FFindMatch(bodycodeB, str,
                                            AI.FInitState(bodycodeB, cpA, AReg.init_regs(ncap), AReg.init_regs(nlook),
                                                          AReg.init_regs(nquant), 0, AI.cp_context(cpA, str, LAnc.Backward)),
                                            ov, LAnc.Backward, cdnA).0)
      ensures (rfA == rfFresh.value)
      ensures (CM.RegsAgreeInside(res0, rfFresh.value.capture_regs,
                                      PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(host))))
      ensures (CM.RegsAgreeInside(res2, rfFresh.value.quant_regs, M.QIdsOuter(host)))
      ensures (M.GNotUnderQuantL(T.Translate(host), g))
    {
      maxlook := R.max_lookaround(ast);
      cpA := AReg.get_cp(res1, A as int).value;
      RL.AAsArraysLaws(res1);
      assert AI.get_idx(res1.a_cp, A as int) >= 0 && cpA == AI.get_idx(res1.a_cp, A as int);
      assert 0 <= cpA <= |str|;                                    // LookCpsLE(res1)
      inpA := PIV.InpOfCp(str, cpA);
      bodycode := CP.compile_to_bytecode(host);
  
      // ---- the row at A (VERBATIM DeepFindRec) ----
      assert 1 <= A <= maxlook && (A as int) in qm.looks;
      assert GateStaticAtNested(qm, re, crv, A as int, ncap, nlook, nquant);
      laA, bA :|
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
      laT :| LTB.LookEntryOk(crv, A as int, laT, NI.LookBodyOfRE(re, A));
      assert bA == host by { assert crv.f_look_ast[A as int] == bA == host; }
      assert host == M.VBody(crv, A as int);
      endlH := |bodycode| - 1;
      assert PSM.StaticOkNestedRE(qm, host, bodycode, endlH);
      assert crv.f_look_types[A as int] == laA;
      assert (laA.Lookahead? || laA.Lookbehind?) by {
        assert AI.capture_type(crv.f_look_types[A as int]);        // MatchedPosLA
      }
      assert laA.Lookbehind? by { assert crv.f_look_types[A as int] == laA; }
      // ==== (L5 F7c-4) LOOKBEHIND lid: lift via the FLIP twins ====
      M.LookBodyFactsL5(re, crv, A);
      laN :| LTB.LookEntryOk(crv, A as int, laN, host) && (laN.Lookbehind? ==> NR.LBOnlyLooksRE(host));
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
      qmB := AR.QMap(qm.quants,
                         map l: int | l in qm.looks && l >= 0 && (l as nat) in LTB.LookIds(host) :: qm.looks[l],
                         qm.ov);
      assert AR.QmapOk(host, qmB) by { QmapOkLooksIrrel(host, qm, qmB); }
      assert AR.LmapOk(host, qmB) by { LmapOkRestrict(host, qm, qmB); }
      assert OE.OracleColsOk(rer, qmB, str) by {
        SufForallToColsOk(rer, qm, str);
        OracleColsOkRestrict(rer, qm, qmB, str);
      }
      bodycodeB := CP.compile_to_bytecode(R.reverse_regex(host));
      cdnA := crv.f_look_cdns[A as int];
      rbT := LFU.ComputeTr(rer, [LS.Areg(T.Translate(host))], inpA, LG.Empty, WP.Backward);
      rb := LT.TreeRes(rbT, LG.Empty, inpA, WP.Backward);
      rfP := AI.FFindMatchPlus(bodycodeB, host, crv.f_plus_bc, str, ov, LAnc.Backward, cpA,
                                   AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant),
                                   0, cdnA).0;
      // (2026-08-29 proof-engineering) the BASE arm needs only the None-iff from the LB carrier; its
      // three quantified carrier predicates stay out of every later batch's context.
      assert (rfP.Some? <==> rb.Some?) by {
        LookNestBackTFromBodyReplayLB(rer, qmB, laA, host, bodycodeB, crv, str, cpA, ov,
                                      cdnA, crv.f_plus_bc, ncap, nlook, nquant);
      }
      // the backward leaf exists (hypothesis) — unfold SubFirstLeafAt to rb
      assert LidDir(crv, A as int) == WP.Backward;             // dispatch: laA.Lookbehind?
      lsubA := SubFirstLeafAt(rer, crv, str, A as int, res1);
      SubFirstLeafAtIsBackLeaf(rer, crv, str, A as int, res1, host);
      assert lsubA == FG.BackLeafAt(rer, host, str, cpA);
      assert lsubA.Some? && rb.Some? && lsubA.value == rb.value.1;
      assert rfP.Some?;                                            // None-iff
      rfA := rfP.value;
      Sh := PIV.CapIdsInLooks(host);
      gmtH := rb.value.1;
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
      rfFresh := M.FreshBodyMatch(crv, str, A as int, res1, ov, ncap, nlook, nquant);
      assert rfFresh == AI.FFindMatch(bodycodeB, str,
                                      AI.FInitState(bodycodeB, cpA, AReg.init_regs(ncap), AReg.init_regs(nlook),
                                                    AReg.init_regs(nquant), 0, AI.cp_context(cpA, str, LAnc.Backward)),
                                      ov, LAnc.Backward, cdnA).0 by {
        hide M.FreshBodyMatch; hide AI.FFindMatch;   // (2026-08-29) a congruence step over the lemma's ensures —
                  // left unfoldable, Z3 explores the engine loop here and the batch runs past 2700 s in the split module
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
    }
    assert {:split_here} true;   // (E3) section boundary: its own assertion batch

    // ==== BASE: g DIRECT in host ====
    SubFirstLeafDirectInFreshLB(rer, qmB, crv, str, ov, A, res1, host, g, ncap, nlook, nquant);
    var rfc := rfFresh.value.capture_regs;
    var rfl := rfFresh.value.look_regs;
    var rfq := rfFresh.value.quant_regs;
    assert g in PIV.GmOfLive(host, rfc, rfl, rfq)
           && lsubA.value[g] == LBV.SwapRange(PIV.GmOfLive(host, rfc, rfl, rfq)[g]);
    // presence + dominance on the FRESH banks
    M.LookBodyFactsL5(re, crv, A);          // NestedFragmentRE/CapUnique/QuantUnique(host)
    FreshBodyMatchCapWfNested(crv, str, A as int, res1, ov, ncap, nlook, nquant, host);
    assert PIV.CapRegWf(rfc);
    assert forall c: nat :: c in PIV.CapIds(host) && AI.get_idx(rfc.a_clk, CP.start_reg(c)) < 0
                            ==> AI.get_idx(rfc.a_cp, CP.start_reg(c)) < 0;
    NI.GmOfLivePresenceExtractLkNested(host, rfFresh.value.capture_regs, rfl, rfq, g);
    assert AReg.as_arrays(rfl).1 == rfl.a_clk && AReg.as_arrays(rfq).1 == rfq.a_clk;
    assert PIV.PathPresentLk(host, rfc.a_clk, rfl.a_clk, rfq.a_clk, -1, g);
    assert AI.get_idx(rfc.a_clk, CP.start_reg(g)) >= 0
           && AI.get_idx(rfc.a_cp, CP.start_reg(g)) >= 0
           && AI.get_idx(rfc.a_clk, CP.start_reg(g))
              >= PIV.MxAtGidLk(host, rfc.a_clk, rfl.a_clk, rfq.a_clk, -1, g);
    assert {:split_here} true;   // (E3) residual sub-section
    // transport onto the reconstructed banks (no-look/no-quant path)
    M.GNotUnderQuantLNoAncQuants(host, g);
    assert PIV.AncQuants(host, g) == {};
    assert forall c: nat :: c in PIV.CapIdsOutsideLooks(host) ==>
                              AI.get_idx(res0.a_clk, CP.start_reg(c)) == AI.get_idx(rfc.a_clk, CP.start_reg(c))
    by {
      forall c: nat | c in PIV.CapIdsOutsideLooks(host)
        ensures AI.get_idx(res0.a_clk, CP.start_reg(c)) == AI.get_idx(rfc.a_clk, CP.start_reg(c))
      {
        assert CP.start_reg(c) in PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(host));
      }
    }
    NI.PathPresentLkDirectAgree(host, res0.a_clk, res1.a_clk, res2.a_clk,
                                rfc.a_clk, rfl.a_clk, rfq.a_clk, g);
    assert PIV.PathPresentLk(host, res0.a_clk, res1.a_clk, res2.a_clk, -1, g);
    assert {:split_here} true;   // (E3) residual sub-section
    // res0 == rf at g's registers (start + end): the value lift at A
    PIV.CapIdsSplit(host);
    assert g in PIV.CapIdsOutsideLooks(host);
    assert CP.start_reg(g) in PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(host))
           && CP.end_reg(g) in PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(host));
    assert AI.get_idx(res0.a_clk, CP.start_reg(g)) == AI.get_idx(rfc.a_clk, CP.start_reg(g));
    assert AI.get_idx(res0.a_cp, CP.start_reg(g)) == AI.get_idx(rfc.a_cp, CP.start_reg(g));   // (2026-08-29) was rfc.a_clk — a slip that verified only the slow way
    assert AI.get_idx(res0.a_clk, CP.end_reg(g)) == AI.get_idx(rfc.a_clk, CP.end_reg(g));
    assert AI.get_idx(res0.a_cp, CP.end_reg(g)) == AI.get_idx(rfc.a_cp, CP.end_reg(g));
    // dominance transported (Mx equality from the same transport)
    assert PIV.MxAtGidLk(host, res0.a_clk, res1.a_clk, res2.a_clk, -1, g)
        == PIV.MxAtGidLk(host, rfc.a_clk, rfl.a_clk, rfq.a_clk, -1, g);
    // the value chain with the endpoint swap absorbed by NormRange: leaf[g] ==
    // SwapRange(GmOfLive[g]) (the LB wrapper), GmOfLive[g] == LiveRange(rf,g),
    // LiveRange(rf,g) == LiveRange(res0,g)
    NI.GmOfLiveKeepsPresentLkNested(host, rfFresh.value.capture_regs, rfl, rfq, g);
    assert PIV.GmOfLive(host, rfc, rfl, rfq)[g] == PIV.LiveRange(rfc.a_cp, rfc.a_clk, g);
    assert PIV.LiveRange(rfc.a_cp, rfc.a_clk, g) == PIV.LiveRange(res0.a_cp, res0.a_clk, g);
    NormSwapCong(PIV.LiveRange(res0.a_cp, res0.a_clk, g));
    assert PIV.NormRange(lsubA.value[g]) == PIV.NormRange(PIV.LiveRange(res0.a_cp, res0.a_clk, g));
  }

}
