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
  import BRG = LindenElkBackRowGate   // (G3b) FreshPlusLBUnfold
  import GF = LindenElkGateFlip        // (G3b) GateFXR
  import opened LindenElkLiftSimCore
  import opened LindenElkLiftSimOracle
  import opened LindenElkLiftSimChain
  import opened LindenElkLiftSimGate
  import opened LindenElkLiftSimCarriers

  // (G3a) `GateStaticPick` moved to lift-sim-core.

  /** (L5 F7f perf) The LOOKBEHIND arm of `DeepFindRec`, extracted so each of its
      assertions is checked in the small context of this lemma rather than in the
      3000-assertion parent (with the hub's `NoPosLookbehindRE` conjunct gone, several
      of the arm's VCs timed out at 900 s inside the parent). Mutually recursive with
      `DeepFindRec` on the lexicographic metric `(|LookIds(host)|, arm)`. */
/** (G5a-1 P5b) `DeepFindRecLB` on the top-level fragment: the same proof, the premise widened and its callees
      on their `…Cdn` forms where the argument is the top regex or a non-look subterm of it. */
  lemma DeepFindRecLBCdn(
    rer: LW.RegExpRecord, qm: AR.QMap, crv: CP.FCompiled, str: string, ast: R.regex, re: R.regex,
    ov: LOr.OracleView, res0: AReg.Regs, res1: AReg.Regs, res2: AReg.Regs,
    host: R.regex, A: nat, owner: nat, g2: nat, ncap: int, nlook: int, nquant: int)
    // ---- whole-regex statics (fixed through the recursion) ----
    requires T.TransWf(re) && NR.NestedFragmentCdnRE(re)
    requires M.LookBodiesPlusGateRE(re)   // (G3a) the weak gate: lookbehind bodies stamp-free, lookahead bodies CIN
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
    // ---- (§2.3/§2.4) the FLookLoop value lifts: the reverse descent reads its dominance off them ----
    requires M.ValueOkO(crv, str, res0, res1, 1, R.max_lookaround(ast), ov, ncap, nlook, nquant)
    requires M.LookPosO(res1, crv)   // (gate C, G2) set look records sit at positive rows
    requires M.QuantValueOkO(crv, str, res2, res1, 1, R.max_lookaround(ast), ov, ncap, nlook, nquant)
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
    requires var rfO := M.FreshBodyMatchPlus(crv, str, owner as int, res1, ov, ncap, nlook, nquant);   // (G3a) OwnerPkg
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
    decreases |LTB.LookIds(host)|, 0, 0
  {
    hide M.LookBodiesPlusGateRE;   // (G3a) a fact here, never unfolded (recursive: batch memory)
    // (§2.5b/z3 4.14) recursive nullability predicates + the CIN disjunct's
    // triggered existential storm the solver; all uses here are opaque.
    hide NUL.NonNullableL, NUL.CINullableL, NUL.NoNulledPlusL, AR.NfaRepCinL;
    // (2026-08-25) this lemma takes the L4-perf OPAQUE bundles (`117b6aa`) but its
    // body reads their foralls (`FrameEntryOk` at A, `OracleOkSuffix` at cps) —
    // reveal them. (Never re-verified after the perf pass; failed 3 asserts.)
    reveal M.OracleSufAllO(), M.FrameEntryAllO();
    var maxlook := R.max_lookaround(ast);
    var cpA := AReg.get_cp(res1, A as int).value;
    assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
    RL.AAsArraysLaws(res1);
    assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
    assert AI.get_idx(res1.a_cp, A as int) >= 0 && cpA == AI.get_idx(res1.a_cp, A as int);
    assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
    assert 0 <= cpA <= |str|;                                    // LookCpsLE(res1)
    var inpA := PIV.InpOfCp(str, cpA);
    var bodycode := CP.compile_to_bytecode(host);

    assert {:split_here} true;   // (E3) section boundary: its own assertion batch
    // ---- the row at A: la_A + host tie + statics ----
    assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
    assert 1 <= A <= maxlook && (A as int) in qm.looks;
    assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
    assert GateStaticAtNested(qm, re, crv, A as int, ncap, nlook, nquant);   // GateStaticsOkNested
    var laA: R.lookaround, bA: R.regex := GateStaticPick(qm, re, crv, A as int, ncap, nlook, nquant);   // (G3a) the picker
    assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
    NI.LookBodyOfTablesTie(re, crv, A);
    var laT: R.lookaround :| LTB.LookEntryOk(crv, A as int, laT, NI.LookBodyOfRE(re, A));
    assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
    assert bA == host by { assert crv.f_look_ast[A as int] == bA == host; }
    assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
    assert host == M.VBody(crv, A as int);
    var endlH: nat := |bodycode| - 1;
    assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
    assert PSM.StaticCoreCdnRE(qm, host, bodycode, endlH);
    assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
    assert crv.f_look_types[A as int] == laA;
    assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
    assert (laA.Lookahead? || laA.Lookbehind?) by {
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert AI.capture_type(crv.f_look_types[A as int]);        // MatchedPosLA
    }
    assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
    assert laA.Lookbehind? by { assert crv.f_look_types[A as int] == laA; }
    assert {:split_here} true;   // (E3) section boundary: its own assertion batch
    // ==== (L5 F7c-4) LOOKBEHIND lid: lift via the FLIP twins ====
    assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
    LookBodyUniqAny(re, A);   // (W11) uniqueness only; no LBOnlyLooksRE(host)
    assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
    if g2 !in PIV.CapIdsInLooks(host) {
      assert {:split_here} true;   // (E3) section boundary: its own assertion batch
      // ---- BASE: g2 DIRECT in host ====
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert M.FrameEntryOk(crv, laA, host,
                            PIV.CaptureRegsSet(PIV.CapIdsInLooks(re)), M.LookIdSet(re));
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      M.InnermostOwnerUnique(re, g2, owner, A);
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert owner == A;
      var rfO := M.FreshBodyMatchPlus(crv, str, A as int, res1, ov, ncap, nlook, nquant);   // (G3a) OwnerPkg
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert rfO.Some?
             && g2 in PIV.GmOfLive(host, rfO.value.capture_regs, rfO.value.look_regs, rfO.value.quant_regs);
      // the body-restricted qmap (LmapOk on `host`, all-columns oracle)
      var qmB0 := AR.QMap(qm.quants,
                          map l: int | l in qm.looks && l >= 0 && (l as nat) in LTB.LookIds(host) :: qm.looks[l],
                          qm.ov, qm.bodies);
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert AR.QmapOk(host, qmB0) by { QmapOkLooksIrrel(host, qm, qmB0); }
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert AR.LmapOk(host, qmB0) by { LmapOkRestrict(host, qm, qmB0); }
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert OE.OracleColsOk(rer, qmB0, str) by {
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        SufAllToColsOk(rer, qm, str);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        OracleColsOkRestrict(rer, qm, qmB0, str);
      }
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      M.PlusGateBodyCdn(re, crv, A, laA, host);   // (G3b) the uniform gate at the row body
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      RowPlusFactsS(host, crv.f_plus_bc, nlook);   // (G3b) the plus twin's premises
      assert {:split_here} true;
      assert crv.f_look_cdns[A as int] == LCdn.compile_cdns(host);   // (G5b-2) LookEntryOk
      FreshBodyDirectInSubFirstLeafLBS(rer, qmB0, crv, str, ov, A, res1, host, g2,
                                      ncap, nlook, nquant);
    assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
    } else {
      assert {:split_here} true;   // (E3) section boundary: its own assertion batch
      // ---- DEEP: descend through g2's top-in-host ancestor A1 (per-hop kind dispatch) ----
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert M.FrameEntryOk(crv, laA, host,
                            PIV.CaptureRegsSet(PIV.CapIdsInLooks(re)), M.LookIdSet(re));
      var ownH := NI.InnermostOwnerDirect(host, g2);
      var A1 := ReconLiveTopAncestor(host, g2, ownH);
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert A1 in NI.TopLookIds(host) && A1 in LTB.LookIds(host)
             && g2 in PIV.CapIds(NI.LookBodyOfRE(host, A1));
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      NI.LookBodyLookIdsIn(re, A);                                // LookIds(host) <= LookIds(re)
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert A1 in LTB.LookIds(re);
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      NI.LookBodyCompose(re, A, A1);                              // bodies compose
      var bodyA1 := NI.LookBodyOfRE(re, A1);
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert bodyA1 == NI.LookBodyOfRE(host, A1);

      assert {:split_here} true;   // (E3) step boundary: its own assertion batch
      // (α) presence descends + A1's res1 clock is set
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      NI.LookPathDecomposeCdn(host, bodyA1, res0.a_clk, res1.a_clk, res2.a_clk, -1, A1, g2);
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert AI.get_idx(res1.a_clk, A1 as int) >= 0;
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert PIV.PathPresentLk(bodyA1, res0.a_clk, res1.a_clk, res2.a_clk, -1, g2);

      assert {:split_here} true;   // (E3) step boundary: its own assertion batch
      // (β) A1 matched in res1 (reverse invariant + LB-only kind pin)
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert AI.get_idx(res1.a_cp, A1 as int) >= 0;               // LookCpSetWithClk
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert AReg.get_cp(res1, A1 as int).Some?;
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert M.MatchedPosLA(crv, res1, A1 as int) by {
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        // (§2.5b F-c) a bare forall instance: the inlined hub goal (its existential)
        // timed out at 900 s in the swept context
        assert GateStaticAtNested(qm, re, crv, A1 as int, ncap, nlook, nquant) by {
          assert (A1 as int) in qm.looks;
          hide *; reveal GateStaticsOkNested;
        }
        assert {:split_here} true;   // (§2.5b F-c) the pick: its own batch
        // (L5 F7f) ONE pick with the hub's FULL conjunct list — a SUBSET pick times
        // out under {:isolate_assertions} (the hub's list changed with the flip).
        var la1: R.lookaround, b1: R.regex := GateStaticPick(qm, re, crv, A1 as int, ncap, nlook, nquant);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert crv.f_look_types[A1 as int] == la1;
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert b1 == bodyA1 by {
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          NI.LookBodyOfTablesTie(re, crv, A1);
          var la1T: R.lookaround :| LTB.LookEntryOk(crv, A1 as int, la1T, bodyA1);
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          assert crv.f_look_ast[A1 as int] == b1 == bodyA1;
        }
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        // (W11) NO kind pin: in a mixed host A1 may be a lookAHEAD. Only the
        // negative kinds are excluded (capture-free bodies hold no g2).
        if la1.NegLookbehind? || la1.NegLookahead? {
          assert {:split_here} true;   // (gate C, G2) a set record sits at a POSITIVE row
          M.MatchedPosFromBank(crv, res1, A1 as int);
          assert false;
        }
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert la1.Lookbehind? || la1.Lookahead?;                // (W11) the kinds left
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert AI.capture_type(crv.f_look_types[A1 as int]) by {
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          assert crv.f_look_types[A1 as int] == la1;
        }
      }

      assert {:split_here} true;   // (E3) step boundary: its own assertion batch
      // (δ) the body-restricted qmap + statics (site supplies statics for the
      //     flipped world inside the LB carrier — it only needs LmapOk +
      //     whole-string oracle on `host`).
      var qmB := AR.QMap(qm.quants,
                         map l: int | l in qm.looks && l >= 0 && (l as nat) in LTB.LookIds(host) :: qm.looks[l],
                         qm.ov, qm.bodies);
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert AR.QmapOk(host, qmB) by { QmapOkLooksIrrel(host, qm, qmB); }
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert AR.LmapOk(host, qmB) by { LmapOkRestrict(host, qm, qmB); }
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert OE.OracleColsOk(rer, qmB, str) by {
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        SufAllToColsOk(rer, qm, str);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        OracleColsOkRestrict(rer, qm, qmB, str);
      }

      assert {:split_here} true;   // (E3) step boundary: its own assertion batch
      // (γ) A1's BACKWARD spec leaf EXISTS (oracle at the recorded cp) — the
      //     per-hop kind dispatch is by `LidDir`, so the backward arm builds
      //     the WP.Backward tree and the forward arm the WP.Forward one.
      assert {:split_here} true;   // (E3) step boundary: its own assertion batch
      // (ε) the BACKWARD body replay: the LB carrier at `compile(reverse_regex(host))`.
      var cpA := AReg.get_cp(res1, A as int).value;
      var inpA := PIV.InpOfCp(str, cpA);
      var bodycodeB := CP.compile_to_bytecode(R.reverse_regex(host));
      var cdnA := crv.f_look_cdns[A as int];
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      RowPlusFactsS(host, crv.f_plus_bc, nlook);   // (G3a)
      M.PlusGateBodyCdn(re, crv, A, laA, host);   // (G5b-2) the gate's lookbehind arm: NoCdnPlusRE(host) for GateFXR
      GF.GateFXR(host);   // (G3b) the flipped host's rows
      assert cdnA == LCdn.compile_cdns(host);   // (G5b-2) the row's own table (LookEntryOk)
      LookNestBackTFromBodyReplayLBS(rer, qmB, laA, host, bodycodeB, crv, str, cpA, ov,
                                    cdnA, crv.f_plus_bc, ncap, nlook, nquant);
      var rbT := LFU.ComputeTr(rer, [LS.Areg(T.Translate(host))], inpA, LG.Empty, WP.Backward);
      var rb := LT.TreeRes(rbT, LG.Empty, inpA, WP.Backward);
      // (gamma) the BACKWARD spec leaf EXISTS: res1's record at A is oracle-true,
      // so host's spec tree matches BACKWARD at cpA (the LB twin of the forward
      // arm's FirstLeaf(t, inpA).Some? block).
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert rb.Some? by {
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert LOr.view_get_oracle(ov, AI.get_idx(res1.a_cp, A as int), A as int);   // LookCpsOracleTrue
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert LL.OracleOkSuffix(rer, qm, inpA);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert LL.OracleOkAt(rer, qm, inpA);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert (A as int) in qm.looks
               && qm.looks[A as int] == (T.TrLookaround(laA), T.Translate(host));
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert TREP.CpOf(inpA) == cpA by { LS.ReverseLength(str[..cpA]); }
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert L.LkDir(T.TrLookaround(laA)) == WP.Backward;      // laA.Lookbehind?
      }
      var rfP := AI.FFindMatchPlus(bodycodeB, host, crv.f_plus_bc, str, ov, LAnc.Backward, cpA,
                                   AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant),
                                   0, cdnA).0;
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert rfP.Some?;                                            // the carrier's None-iff at rb.Some?
      var rfA := rfP.value;
      var Sh := PIV.CapIdsInLooks(host);
      var gmtH := rb.value.1;
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert LookNestBackTTopDeepP(rer, host, crv, str, ov, Sh, gmtH, rfA, ncap, nlook, nquant);   // (G4b-2) the row's P form
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert CM.LookClkSetWithCp(rfA.look_regs) && CM.LookCpSetWithClk(rfA.look_regs);

      assert {:split_here} true;   // (E3) step boundary: its own assertion batch
      // (ζ) rf_A IS FreshBodyMatch(A, res1) — the backward fresh run.
      // The unfold's row witnesses, hoisted (they are what the by-block needs):
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert host == M.VBody(crv, A as int) by {
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        NI.LookBodyOfTablesTie(re, crv, A);
        var laT2: R.lookaround :| LTB.LookEntryOk(crv, A as int, laT2, host);
      }
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert 0 <= (A as int) < |crv.f_look_types| && crv.f_look_types[A as int].Lookbehind?;
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert 0 <= (A as int) < |crv.f_look_cdns| && cdnA == crv.f_look_cdns[A as int];
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert AReg.get_cp(res1, A as int).Some? && AReg.get_cp(res1, A as int).value == cpA;
      var rfFresh := M.FreshBodyMatchPlus(crv, str, A as int, res1, ov, ncap, nlook, nquant);   // (G3b) the plus replay
      assert rfFresh == AI.FFindMatchPlus(bodycodeB, host, crv.f_plus_bc, str, ov, LAnc.Backward, cpA,
                         AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant), 0, cdnA).0 by {
        BRG.FreshPlusLBUnfold(crv, str, A as int, res1, ov, host, ncap, nlook, nquant);
      }
      assert rfA == rfFresh.value;
      assert {:split_here} true;   // (E3) step boundary: its own assertion batch
      // (η) the LEVEL-LINK at (A, A1): res1's record at A1 IS rf_A's
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert A1 as int in M.DirectLidSet(host) by {
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        TopEqDirectLookIds(host);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert A1 in M.DirectLookIds(host);
      }
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert rfFresh.Some? by { assert rfA == rfFresh.value; }
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert AReg.get_cp(res1, A1 as int) == AReg.get_cp(rfFresh.value.look_regs, A1 as int) by {
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert M.FLookLoopChildLinkOk(crv, str, res1, 1, maxlook, ov, ncap, nlook, nquant);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert 1 <= A as int <= maxlook && M.MatchedPosLA(crv, res1, A as int);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert host == M.VBody(crv, A as int);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert (A1 as int) in M.DirectLidSet(host);
      }
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert AReg.get_cp(res1, A1 as int) == AReg.get_cp(rfA.look_regs, A1 as int) by {
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert rfA == rfFresh.value;
      }

      assert {:split_here} true;   // (E3) step boundary: its own assertion batch
      // (θ) A1 matched + dominant ON rf_A's banks
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert M.MatchedPosLA(crv, rfA.look_regs, A1 as int) by {
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert AReg.get_cp(rfA.look_regs, A1 as int).Some?;
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert AI.capture_type(crv.f_look_types[A1 as int]);      // established at (β)
      }
      var L1 := AI.get_idx(rfA.look_regs.a_clk, A1 as int);
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert L1 >= 0 by {
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert 0 <= A1 as int < |rfA.look_regs.a_cp| && rfA.look_regs.a_cp[A1 as int] >= 0;
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert AI.get_idx(rfA.look_regs.a_cp, A1 as int) >= 0;
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert CM.LookClkSetWithCp(rfA.look_regs);
      }
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      // (§2.3/§2.4) dominance from the presence path on the reconstructed banks:
      // the value lifts carry the quant clocks, the level-link A1's own clock
      assert {:split_here} true;
      assert AI.get_idx(res1.a_clk, A1 as int) == AI.get_idx(rfA.look_regs.a_clk, A1 as int) by {
        assert rfA == rfFresh.value;
        assert M.FLookLoopChildLinkOk(crv, str, res1, 1, maxlook, ov, ncap, nlook, nquant);
        assert 1 <= A as int <= maxlook && M.MatchedPosLA(crv, res1, A as int);
        assert host == M.VBody(crv, A as int);
        assert (A1 as int) in M.DirectLidSet(host);
      }
      assert {:split_here} true;
      assert CM.RegsAgreeInside(res0, rfA.capture_regs, PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(host)))
             && M.QuantClkAgreeInside(res2, rfA.quant_regs, M.QIdsOuter(host)) by {
        assert rfA == rfFresh.value && rfFresh.Some?;
        reveal M.ValueOkO(), M.QuantValueOkO();
        assert 1 <= A as int <= maxlook && M.MatchedPosLA(crv, res1, A as int);
        assert host == M.VBody(crv, A as int);
      }
      assert {:split_here} true;
      ReverseLookDomOnFreshCdn(host, res0, res1, res2, rfA, A1, g2);
      assert NI.LookPathDom(host, L1, rfA.quant_regs.a_clk, A1);

      assert {:split_here} true;   // (E3) step boundary: its own assertion batch
      // (ι) the RECURSIVE landing at A1, transported onto rf_A's bank
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert |LTB.LookIds(bodyA1)| < |LTB.LookIds(host)| by {
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        NI.LookBodyLookIdsIn(host, A1);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        LookIdNotInOwnBody(host, A1);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        SubsetCardLt(LTB.LookIds(bodyA1), LTB.LookIds(host), A1);
      }
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      DeepFindRecCdn(rer, qm, crv, str, ast, re, ov, res0, res1, res2,
                  bodyA1, A1, owner, g2, ncap, nlook, nquant);
      var lsub1 := SubFirstLeafAt(rer, crv, str, A1 as int, res1);
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert lsub1.Some? && g2 in lsub1.value;
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert SubFirstLeafAt(rer, crv, str, A1 as int, rfA.look_regs) == lsub1;   // reads only get_cp at A1

      assert {:split_here} true;   // (E3) step boundary: its own assertion batch
      // (κ) LAND via the DEEP carrier, then identify the leaf with the
      //     backward `BackLeafAt(host, cpA)` (== SubFirstLeafAt(A, res1)); (G4b-2) the presence-premised form
      //     (`ReverseLookDomOnFreshCdn` gave presence and freshness at A1)
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      DescentLandTopDeepP(rer, host, crv, str, ov, Sh, gmtH, rfA, A1, g2, ncap, nlook, nquant);
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert g2 in gmtH;
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert host == M.VBody(crv, A as int);
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert crv.f_look_types[A as int].Lookbehind?;
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      SubFirstLeafAtIsBackLeaf(rer, crv, str, A as int, res1, host);
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert SubFirstLeafAt(rer, crv, str, A as int, res1) == FG.BackLeafAt(rer, host, str, cpA);
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert SubFirstLeafAt(rer, crv, str, A as int, res1).value == gmtH;
    }
  }

  /** (G5a-1 P5b) The narrow form, as a corollary of `DeepFindRecLBCdn`. */
  lemma DeepFindRecLB(
    rer: LW.RegExpRecord, qm: AR.QMap, crv: CP.FCompiled, str: string, ast: R.regex, re: R.regex,
    ov: LOr.OracleView, res0: AReg.Regs, res1: AReg.Regs, res2: AReg.Regs,
    host: R.regex, A: nat, owner: nat, g2: nat, ncap: int, nlook: int, nquant: int)
    // ---- whole-regex statics (fixed through the recursion) ----
    requires T.TransWf(re) && NR.NestedFragmentRE(re)
    requires M.LookBodiesPlusGateRE(re)   // (G3a) the weak gate: lookbehind bodies stamp-free, lookahead bodies CIN
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
    // ---- (§2.3/§2.4) the FLookLoop value lifts: the reverse descent reads its dominance off them ----
    requires M.ValueOkO(crv, str, res0, res1, 1, R.max_lookaround(ast), ov, ncap, nlook, nquant)
    requires M.LookPosO(res1, crv)   // (gate C, G2) set look records sit at positive rows
    requires M.QuantValueOkO(crv, str, res2, res1, 1, R.max_lookaround(ast), ov, ncap, nlook, nquant)
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
    requires var rfO := M.FreshBodyMatchPlus(crv, str, owner as int, res1, ov, ncap, nlook, nquant);   // (G3a) OwnerPkg
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
    NR.NarrowIsCdn(re);
    hide *;   // the wide premises are this lemma's own: match by name
    DeepFindRecLBCdn(rer, qm, crv, str, ast, re, ov, res0, res1, res2, host, A, owner, g2, ncap, nlook, nquant);
  }

  /** (perf) The FORWARD DEEP arm of `DeepFindRec`, extracted so its assertions are
      checked in a small context (same treatment as `DeepFindRecLB`).
      Mutually recursive with `DeepFindRec` on `(|LookIds(host)|, arm)`. */
  // (gate C) `{:induction false}`: the recursion is explicit (`DeepFindRec`); with the bare look
  // arm of `NestedFragmentRE` the automatic induction hypothesis pushed two sections past 900 s.
/** (G5a-1 P5b) `DeepFindRecFwdDeep` on the top-level fragment: the same proof, the premise widened and its callees
      on their `…Cdn` forms where the argument is the top regex or a non-look subterm of it. */
  lemma {:induction false} DeepFindRecFwdDeepCdn(
    rer: LW.RegExpRecord, qm: AR.QMap, crv: CP.FCompiled, str: string, ast: R.regex, re: R.regex,
    ov: LOr.OracleView, res0: AReg.Regs, res1: AReg.Regs, res2: AReg.Regs,
    host: R.regex, A: nat, owner: nat, g2: nat, ncap: int, nlook: int, nquant: int)
    // ---- whole-regex statics (fixed through the recursion) ----
    requires T.TransWf(re) && NR.NestedFragmentCdnRE(re)
    requires M.LookBodiesPlusGateRE(re)   // (G3a) the weak gate: lookbehind bodies stamp-free, lookahead bodies CIN
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
    // ---- (§2.3/§2.4) the FLookLoop value lifts: the reverse descent reads its dominance off them ----
    requires M.ValueOkO(crv, str, res0, res1, 1, R.max_lookaround(ast), ov, ncap, nlook, nquant)
    requires M.LookPosO(res1, crv)   // (gate C, G2) set look records sit at positive rows
    requires M.QuantValueOkO(crv, str, res2, res1, 1, R.max_lookaround(ast), ov, ncap, nlook, nquant)
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
    requires var rfO := M.FreshBodyMatchPlus(crv, str, owner as int, res1, ov, ncap, nlook, nquant);   // (G3a) OwnerPkg
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
    decreases |LTB.LookIds(host)|, 0, 0
  {
    hide M.LookBodiesPlusGateRE;   // (G3a) a fact here, never unfolded (recursive: batch memory)
    // (§2.5b/z3 4.14) recursive nullability predicates + the CIN disjunct's
    // triggered existential storm the solver; all uses here are opaque.
    hide NUL.NonNullableL, NUL.CINullableL, NUL.NoNulledPlusL, AR.NfaRepCinL;
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
    var laA: R.lookaround, bA: R.regex := GateStaticPick(qm, re, crv, A as int, ncap, nlook, nquant);   // (G3a) the picker
    NI.LookBodyOfTablesTie(re, crv, A);
    var laT: R.lookaround :| LTB.LookEntryOk(crv, A as int, laT, NI.LookBodyOfRE(re, A));
    assert bA == host by { assert crv.f_look_ast[A as int] == bA == host; }
    assert host == M.VBody(crv, A as int);
    var endlH: nat := |bodycode| - 1;
    assert PSM.StaticCoreCdnRE(qm, host, bodycode, endlH);   // (G5b-1) a lookahead host may hold a greedy CDN plus
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

    assert {:split_here} true;   // (E3) step boundary: its own assertion batch
    // (α) presence descends + A1's res1 clock is set
    NI.LookPathDecomposeCdn(host, bodyA1, res0.a_clk, res1.a_clk, res2.a_clk, -1, A1, g2);
    assert AI.get_idx(res1.a_clk, A1 as int) >= 0;
    assert PIV.PathPresentLk(bodyA1, res0.a_clk, res1.a_clk, res2.a_clk, -1, g2);

    assert {:split_here} true;   // (E3) step boundary: its own assertion batch
    // (β) A1 matched in res1 (reverse invariant + type pin)
    assert AI.get_idx(res1.a_cp, A1 as int) >= 0;               // LookCpSetWithClk
    assert AReg.get_cp(res1, A1 as int).Some?;
    M.MatchedPosFromBank(crv, res1, A1 as int);   // (gate C, G2) a set record sits at a positive row
    assert M.MatchedPosLA(crv, res1, A1 as int);

    assert {:split_here} true;   // (E3) step boundary: its own assertion batch
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

    assert {:split_here} true;   // (E3) step boundary: its own assertion batch
    // (δ) the body-restricted qmap + statics
    var qmB := AR.QMap(qm.quants,
                       map l: int | l in qm.looks && l >= 0 && (l as nat) in LTB.LookIds(host) :: qm.looks[l],
                       qm.ov, qm.bodies);
    assert AR.QmapOk(host, qmB) by { QmapOkLooksIrrel(host, qm, qmB); }
    assert AR.LmapOk(host, qmB) by { LmapOkRestrict(host, qm, qmB); }
    assert PSM.StaticCoreCdnRE(qmB, host, bodycode, endlH) by {
      assert PSM.StaticCoreCdnRE(qm, host, bodycode, endlH);   // (G5b-1) a lookahead host may hold a greedy CDN plus
    }
    assert LL.OracleOkSuffix(rer, qmB, inpA) by {
      assert LL.OracleOkSuffix(rer, qm, inpA);
      OracleOkSuffixRestrict(rer, qm, qmB, inpA);
    }
    assert GateStaticsOkNested(qmB, host, crv, ncap, nlook, nquant) by {
      RowPlusFactsS(host, crv.f_plus_bc, nlook);   // (G3a)
      GateStaticsFromTablesCdn(qmB, host, crv, ncap, nlook, nquant);
    }
    assert OE.OracleColsOk(rer, qmB, str) by {                       // (L5 F7d)
      SufAllToColsOk(rer, qm, str);
      OracleColsOkRestrict(rer, qm, qmB, str);
    }

    assert {:split_here} true;   // (E3) step boundary: its own assertion batch
    // (ε) the per-body replay: both carriers + None-iff + bank invariants at rf_A
    var cdnA := crv.f_look_cdns[A as int];
    LookNestBackTFromBodyReplayS(rer, qmB, laA, host, bodycode, endlH, 0, crv, str, cpA, ov,
                                cdnA, crv.f_plus_bc, ncap, nlook, nquant);
    var rfP := AI.FFindMatchPlus(bodycode, host, crv.f_plus_bc, str, ov, LAnc.Forward, cpA,
                                 AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant),
                                 0, cdnA).0;
    assert rfP.Some?;                                            // None-iff + FirstLeaf.Some?
    var rfA := rfP.value;
    var Sh := PIV.CapIdsInLooks(host);
    var gmtH := LT.FirstLeaf(t, inpA).value.1;
    assert LookNestBackTTopDeepP(rer, host, crv, str, ov, Sh, gmtH, rfA, ncap, nlook, nquant);   // (G4b-2) the row's P form
    assert CM.LookClkSetWithCp(rfA.look_regs) && CM.LookCpSetWithClk(rfA.look_regs);

    assert {:split_here} true;   // (E3) step boundary: its own assertion batch
    // (ζ) rf_A IS FreshBodyMatch(A, res1) (same fresh run at the same position)
    var rfFresh := M.FreshBodyMatchPlus(crv, str, A as int, res1, ov, ncap, nlook, nquant);   // (G3a)
    assert rfFresh == rfP by {
      assert AI.capture_direction(crv.f_look_types[A as int]) == LAnc.Forward;
      assert CP.capture_regex(crv.f_look_types[A as int], M.VBody(crv, A as int)) == host;
      reveal M.FreshBodyMatchPlus();
    }
    assert {:split_here} true;   // (E3) step boundary: its own assertion batch
    // (η) the LEVEL-LINK at (A, A1): res1's record at A1 IS rf_A's
    assert A1 as int in M.DirectLidSet(host) by {
      TopEqDirectLookIds(host);
      assert A1 in M.DirectLookIds(host);
    }
    assert {:split_here} true;   // (gate B) sub-split of (η): the whole section timed out at 900 s once de-isolated
    assert AReg.get_cp(res1, A1 as int) == AReg.get_cp(rfFresh.value.look_regs, A1 as int) by {
      assert M.FLookLoopChildLinkOk(crv, str, res1, 1, maxlook, ov, ncap, nlook, nquant);
      assert 1 <= A as int <= maxlook && M.MatchedPosLA(crv, res1, A as int);
      assert rfFresh.Some?;
    }
    assert {:split_here} true;   // (gate B) sub-split of (η): the whole section timed out at 900 s once de-isolated
    assert rfA == rfFresh.value;   // (G3a) both are the fresh plus replay
    assert {:split_here} true;   // (gate B) sub-split of (η): the whole section timed out at 900 s once de-isolated
    assert AReg.get_cp(res1, A1 as int) == AReg.get_cp(rfA.look_regs, A1 as int);

    assert {:split_here} true;   // (E3) step boundary: its own assertion batch
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
    // (§2.3/§2.4) dominance from the presence path on the reconstructed banks:
    // the value lifts carry the quant clocks, the level-link A1's own clock
    assert AI.get_idx(res1.a_clk, A1 as int) == AI.get_idx(rfA.look_regs.a_clk, A1 as int) by {
      assert M.FLookLoopChildLinkOk(crv, str, res1, 1, maxlook, ov, ncap, nlook, nquant);
      assert 1 <= A as int <= maxlook && M.MatchedPosLA(crv, res1, A as int);
      assert host == M.VBody(crv, A as int);
      assert rfFresh.Some? && (A1 as int) in M.DirectLidSet(host);
    }
    assert CM.RegsAgreeInside(res0, rfA.capture_regs, PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(host)))
           && M.QuantClkAgreeInside(res2, rfA.quant_regs, M.QIdsOuter(host)) by {
      assert rfFresh.Some?;
      reveal M.ValueOkO(), M.QuantValueOkO();
      assert 1 <= A as int <= maxlook && M.MatchedPosLA(crv, res1, A as int);
      assert host == M.VBody(crv, A as int);
    }
    ReverseLookDomOnFreshCdn(host, res0, res1, res2, rfA, A1, g2);
    assert NI.LookPathDom(host, L1, rfA.quant_regs.a_clk, A1);

    assert {:split_here} true;   // (E3) step boundary: its own assertion batch
    // (ι) the RECURSIVE landing at A1, transported onto rf_A's bank
    assert |LTB.LookIds(bodyA1)| < |LTB.LookIds(host)| by {
      NI.LookBodyLookIdsIn(host, A1);
      LookIdNotInOwnBody(host, A1);
      SubsetCardLt(LTB.LookIds(bodyA1), LTB.LookIds(host), A1);
    }
    DeepFindRecCdn(rer, qm, crv, str, ast, re, ov, res0, res1, res2,
                bodyA1, A1, owner, g2, ncap, nlook, nquant);
    var lsub1 := SubFirstLeafAt(rer, crv, str, A1 as int, res1);
    assert lsub1.Some? && g2 in lsub1.value;
    assert SubFirstLeafAt(rer, crv, str, A1 as int, rfA.look_regs) == lsub1;   // reads only get_cp at A1

    assert {:split_here} true;   // (E3) step boundary: its own assertion batch
    // (κ) LAND via the DEEP carrier (G4b-2: its presence-premised form; ReverseLookDomOnFreshCdn gave presence),
    //     then identify the leaf with SubFirstLeafAt(A, res1)
    DescentLandTopDeepP(rer, host, crv, str, ov, Sh, gmtH, rfA, A1, g2, ncap, nlook, nquant);
    assert g2 in gmtH;
    assert LidDir(crv, A as int) == WP.Forward;               // laA.Lookahead? (dispatch)
    BodyReplayGmtIsSubFirstLeaf(rer, crv, str, A as int, res1, host);
    assert SubFirstLeafAt(rer, crv, str, A as int, res1) == Some(gmtH);
  }

  /** (G5a-1 P5b) The narrow form, as a corollary of `DeepFindRecFwdDeepCdn`. */
  lemma {:induction false} DeepFindRecFwdDeep(
    rer: LW.RegExpRecord, qm: AR.QMap, crv: CP.FCompiled, str: string, ast: R.regex, re: R.regex,
    ov: LOr.OracleView, res0: AReg.Regs, res1: AReg.Regs, res2: AReg.Regs,
    host: R.regex, A: nat, owner: nat, g2: nat, ncap: int, nlook: int, nquant: int)
    // ---- whole-regex statics (fixed through the recursion) ----
    requires T.TransWf(re) && NR.NestedFragmentRE(re)
    requires M.LookBodiesPlusGateRE(re)   // (G3a) the weak gate: lookbehind bodies stamp-free, lookahead bodies CIN
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
    // ---- (§2.3/§2.4) the FLookLoop value lifts: the reverse descent reads its dominance off them ----
    requires M.ValueOkO(crv, str, res0, res1, 1, R.max_lookaround(ast), ov, ncap, nlook, nquant)
    requires M.LookPosO(res1, crv)   // (gate C, G2) set look records sit at positive rows
    requires M.QuantValueOkO(crv, str, res2, res1, 1, R.max_lookaround(ast), ov, ncap, nlook, nquant)
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
    requires var rfO := M.FreshBodyMatchPlus(crv, str, owner as int, res1, ov, ncap, nlook, nquant);   // (G3a) OwnerPkg
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
    NR.NarrowIsCdn(re);
    hide *;   // the wide premises are this lemma's own: match by name
    DeepFindRecFwdDeepCdn(rer, qm, crv, str, ast, re, ov, res0, res1, res2, host, A, owner, g2, ncap, nlook, nquant);
  }

/** (G5a-1 P5b) `DeepFindRec` on the top-level fragment: the same proof, the premise widened and its callees
      on their `…Cdn` forms where the argument is the top regex or a non-look subterm of it. */
  lemma DeepFindRecCdn(
    rer: LW.RegExpRecord, qm: AR.QMap, crv: CP.FCompiled, str: string, ast: R.regex, re: R.regex,
    ov: LOr.OracleView, res0: AReg.Regs, res1: AReg.Regs, res2: AReg.Regs,
    host: R.regex, A: nat, owner: nat, g2: nat, ncap: int, nlook: int, nquant: int)
    // ---- whole-regex statics (fixed through the recursion) ----
    requires T.TransWf(re) && NR.NestedFragmentCdnRE(re)
    requires M.LookBodiesPlusGateRE(re)   // (G3a) the weak gate: lookbehind bodies stamp-free, lookahead bodies CIN
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
    // ---- (§2.3/§2.4) the FLookLoop value lifts: the reverse descent reads its dominance off them ----
    requires M.ValueOkO(crv, str, res0, res1, 1, R.max_lookaround(ast), ov, ncap, nlook, nquant)
    requires M.LookPosO(res1, crv)   // (gate C, G2) set look records sit at positive rows
    requires M.QuantValueOkO(crv, str, res2, res1, 1, R.max_lookaround(ast), ov, ncap, nlook, nquant)
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
    requires var rfO := M.FreshBodyMatchPlus(crv, str, owner as int, res1, ov, ncap, nlook, nquant);   // (G3a) OwnerPkg
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
    decreases |LTB.LookIds(host)|, 1, 0
  {
    hide M.LookBodiesPlusGateRE;   // (G3a) a fact here, never unfolded (recursive: batch memory)
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
    var laA: R.lookaround, bA: R.regex := GateStaticPick(qm, re, crv, A as int, ncap, nlook, nquant);   // (G3a) the picker
    NI.LookBodyOfTablesTie(re, crv, A);
    var laT: R.lookaround :| LTB.LookEntryOk(crv, A as int, laT, NI.LookBodyOfRE(re, A));
    assert bA == host by { assert crv.f_look_ast[A as int] == bA == host; }
    assert host == M.VBody(crv, A as int);
    var endlH: nat := |bodycode| - 1;
    assert PSM.StaticCoreCdnRE(qm, host, bodycode, endlH);   // (G5b-1) any kind
    assert crv.f_look_types[A as int] == laA;
    assert (laA.Lookahead? || laA.Lookbehind?) by {
      assert AI.capture_type(crv.f_look_types[A as int]);        // MatchedPosLA
    }
    if laA.Lookbehind? {
      // (L5 F7f perf) the LOOKBEHIND arm lives in its own lemma (small VC context).
      DeepFindRecLBCdn(rer, qm, crv, str, ast, re, ov, res0, res1, res2,
                    host, A, owner, g2, ncap, nlook, nquant);
    } else {
      assert !laA.Lookbehind? by { assert crv.f_look_types[A as int] == laA; }
      if g2 !in PIV.CapIdsInLooks(host) {
        // (perf) the forward BASE arm lives in its own lemma.
        DeepFindRecFwdBaseCdn(rer, qm, crv, str, ast, re, ov, res0, res1, res2,
                           host, A, owner, g2, ncap, nlook, nquant);
      } else {
        // (perf) the forward DEEP arm lives in its own lemma.
        DeepFindRecFwdDeepCdn(rer, qm, crv, str, ast, re, ov, res0, res1, res2,
                           host, A, owner, g2, ncap, nlook, nquant);
      }
    }
  }

  /** (G5a-1 P5b) The narrow form, as a corollary of `DeepFindRecCdn`. */
  lemma DeepFindRec(
    rer: LW.RegExpRecord, qm: AR.QMap, crv: CP.FCompiled, str: string, ast: R.regex, re: R.regex,
    ov: LOr.OracleView, res0: AReg.Regs, res1: AReg.Regs, res2: AReg.Regs,
    host: R.regex, A: nat, owner: nat, g2: nat, ncap: int, nlook: int, nquant: int)
    // ---- whole-regex statics (fixed through the recursion) ----
    requires T.TransWf(re) && NR.NestedFragmentRE(re)
    requires M.LookBodiesPlusGateRE(re)   // (G3a) the weak gate: lookbehind bodies stamp-free, lookahead bodies CIN
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
    // ---- (§2.3/§2.4) the FLookLoop value lifts: the reverse descent reads its dominance off them ----
    requires M.ValueOkO(crv, str, res0, res1, 1, R.max_lookaround(ast), ov, ncap, nlook, nquant)
    requires M.LookPosO(res1, crv)   // (gate C, G2) set look records sit at positive rows
    requires M.QuantValueOkO(crv, str, res2, res1, 1, R.max_lookaround(ast), ov, ncap, nlook, nquant)
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
    requires var rfO := M.FreshBodyMatchPlus(crv, str, owner as int, res1, ov, ncap, nlook, nquant);   // (G3a) OwnerPkg
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
    NR.NarrowIsCdn(re);
    hide *;   // the wide premises are this lemma's own: match by name
    DeepFindRecCdn(rer, qm, crv, str, ast, re, ov, res0, res1, res2, host, A, owner, g2, ncap, nlook, nquant);
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
/** (G5a-1 P5b) `ForwardFindRecLBBase` on the top-level fragment: the same proof, the premise widened and its callees
      on their `…Cdn` forms where the argument is the top regex or a non-look subterm of it. */
  lemma ForwardFindRecLBBaseCdn(   // (E3) opaque preamble block

    rer: LW.RegExpRecord, qm: AR.QMap, crv: CP.FCompiled, str: string, ast: R.regex, re: R.regex,
    ov: LOr.OracleView, res0: AReg.Regs, res1: AReg.Regs, res2: AReg.Regs,
    host: R.regex, A: nat, g: nat, ncap: int, nlook: int, nquant: int)
    // ---- whole-regex statics (fixed) ----
    requires T.TransWf(re) && NR.NestedFragmentCdnRE(re)
    requires M.LookBodiesPlusGateRE(re)   // (G3a) the weak gate: lookbehind bodies stamp-free, lookahead bodies CIN
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
    requires M.LookPosO(res1, crv)   // (gate C, G2) set look records sit at positive rows
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
    decreases |LTB.LookIds(host)|, 0, 0
  {
    hide M.LookBodiesPlusGateRE;   // (G3a) a fact here, never unfolded (recursive: batch memory)
    // (2026-08-29 E3) the preamble is an OPAQUE block: only the facts below reach the arm's VC.
    var maxlook := *;
    var cpA := *;
    var inpA := *;
    var bodycode := *;
    var laA: R.lookaround := *;
    var bA: R.regex := *;
    var laT: R.lookaround := *;
    var endlH: nat := *;
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
              && T.TransWf(bA) && NR.NestedFragmentCdnRE(bA)
              && qm.looks[A as int].0 == T.TrLookaround(laA)
              && qm.looks[A as int].1 == T.Translate(bA)
              && (set g0: LG.GroupId | g0 in L.DefGroups(T.Translate(bA))) <= PIV.CapIdsInLooks(re)
              && var bc := CP.compile_to_bytecode(bA);
              |bc| >= 1
              && PSM.StaticCoreCdnRE(qm, bA, bc, |bc| - 1)
              && PSM.SizesOkRE(bA, ncap, nlook, nquant))
      ensures (LTB.LookEntryOk(crv, A as int, laT, NI.LookBodyOfRE(re, A)))
      ensures (endlH == |bodycode| - 1)
      ensures (qmB == AR.QMap(qm.quants,
                               map l: int | l in qm.looks && l >= 0 && (l as nat) in LTB.LookIds(host) :: qm.looks[l],
                               qm.ov, qm.bodies))
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
      ensures (rfFresh == M.FreshBodyMatchPlus(crv, str, A as int, res1, ov, ncap, nlook, nquant))   // (G3b)
      ensures (AI.get_idx(res1.a_cp, A as int) >= 0 && cpA == AI.get_idx(res1.a_cp, A as int))
      ensures (0 <= cpA <= |str|)
      ensures (1 <= A <= maxlook && (A as int) in qm.looks)
      ensures (GateStaticAtNested(qm, re, crv, A as int, ncap, nlook, nquant))
      ensures (bA == host)
      ensures (RowPlusOkS(host, crv.f_plus_bc, nlook))   // (G3a, G5b-2) the row's plus facts
      ensures (host == M.VBody(crv, A as int))
      ensures (PSM.StaticCoreCdnRE(qm, host, bodycode, endlH))
      ensures (crv.f_look_types[A as int] == laA)
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
      ensures (rfFresh == rfP)   // (G3b) the plus replay
      ensures (rfA == rfFresh.value)
      ensures (CM.ThreadRegsWf(rfA, ncap, nlook, nquant))   // (G3b) from the carrier
      ensures (CM.RegsAgreeInside(res0, rfFresh.value.capture_regs,
                                      PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(host))))
      ensures (M.QuantClkAgreeInside(res2, rfFresh.value.quant_regs, M.QIdsOuter(host)))
    {
      maxlook := R.max_lookaround(ast);
      cpA := AReg.get_cp(res1, A as int).value;
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      RL.AAsArraysLaws(res1);
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert AI.get_idx(res1.a_cp, A as int) >= 0 && cpA == AI.get_idx(res1.a_cp, A as int);
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert 0 <= cpA <= |str|;                                    // LookCpsLE(res1)
      inpA := PIV.InpOfCp(str, cpA);
      bodycode := CP.compile_to_bytecode(host);
  
      // ---- the row at A (VERBATIM DeepFindRec) ----
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert 1 <= A <= maxlook && (A as int) in qm.looks;
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert GateStaticAtNested(qm, re, crv, A as int, ncap, nlook, nquant);
      laA, bA := GateStaticPick(qm, re, crv, A as int, ncap, nlook, nquant);   // (G3a) the picker
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      NI.LookBodyOfTablesTie(re, crv, A);
      laT :| LTB.LookEntryOk(crv, A as int, laT, NI.LookBodyOfRE(re, A));
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert bA == host by { assert crv.f_look_ast[A as int] == bA == host; }
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert host == M.VBody(crv, A as int);
      endlH := |bodycode| - 1;
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      M.PlusGateBodyCdn(re, crv, A, laA, host);   // (G3b) the uniform gate at the row body
      assert PSM.StaticCoreCdnRE(qm, host, bodycode, endlH);   // (G3b) the hub row, no stamp-free conjunct
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert crv.f_look_types[A as int] == laA;
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert (laA.Lookahead? || laA.Lookbehind?) by {
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert AI.capture_type(crv.f_look_types[A as int]);        // MatchedPosLA
      }
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert laA.Lookbehind? by { assert crv.f_look_types[A as int] == laA; }
      // ==== (L5 F7c-4) LOOKBEHIND lid: lift via the FLIP twins ====
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      LookBodyFactsKBCdn(re, crv, A);   // (W16) uniqueness only; no LBOnlyLooksRE(host)
      // ---- rf_A: the fresh BACKWARD body match (Some via the LB carrier's None-iff — the
      //      backward leaf EXISTS by hypothesis) ----
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert M.FrameEntryOk(crv, laA, host,
                            PIV.CaptureRegsSet(PIV.CapIdsInLooks(re)), M.LookIdSet(re));
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert PIV.CapUnique(host) && PIV.QuantUnique(host) && LTB.LookUnique(host)
             && LTB.LookTablesOk(host, crv);                          // FrameEntryOk
      qmB := AR.QMap(qm.quants,
                         map l: int | l in qm.looks && l >= 0 && (l as nat) in LTB.LookIds(host) :: qm.looks[l],
                         qm.ov, qm.bodies);
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert AR.QmapOk(host, qmB) by { QmapOkLooksIrrel(host, qm, qmB); }
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert AR.LmapOk(host, qmB) by { LmapOkRestrict(host, qm, qmB); }
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert OE.OracleColsOk(rer, qmB, str) by {
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        SufForallToColsOk(rer, qm, str);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
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
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert (rfP.Some? <==> rb.Some?) && (rfP.Some? ==> CM.ThreadRegsWf(rfP.value, ncap, nlook, nquant)) by {
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        RowPlusFactsS(host, crv.f_plus_bc, nlook);   // (G3a)
        GF.GateFXR(host);   // (G3b) the flipped host's rows
        assert cdnA == LCdn.compile_cdns(host);   // (G5b-2) the row's own table (LookEntryOk)
        LookNestBackTFromBodyReplayLBS(rer, qmB, laA, host, bodycodeB, crv, str, cpA, ov,
                                      cdnA, crv.f_plus_bc, ncap, nlook, nquant);
      }
      // the backward leaf exists (hypothesis) — unfold SubFirstLeafAt to rb
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert LidDir(crv, A as int) == WP.Backward;             // dispatch: laA.Lookbehind?
      lsubA := SubFirstLeafAt(rer, crv, str, A as int, res1);
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      SubFirstLeafAtIsBackLeaf(rer, crv, str, A as int, res1, host);
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert lsubA == FG.BackLeafAt(rer, host, str, cpA);
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert lsubA.Some? && rb.Some? && lsubA.value == rb.value.1;
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert rfP.Some?;                                            // None-iff
      rfA := rfP.value;
      Sh := PIV.CapIdsInLooks(host);
      gmtH := rb.value.1;
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert gmtH == lsubA.value;
  
      // rf_A IS FreshBodyMatch(A, res1) — the backward fresh run
      // (L5 F7f) the unfold's row witnesses, hoisted
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert host == M.VBody(crv, A as int) by {
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        NI.LookBodyOfTablesTie(re, crv, A);
        var laT2: R.lookaround :| LTB.LookEntryOk(crv, A as int, laT2, host);
      }
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert 0 <= (A as int) < |crv.f_look_types| && crv.f_look_types[A as int].Lookbehind?;
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert 0 <= (A as int) < |crv.f_look_cdns| && cdnA == crv.f_look_cdns[A as int];
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert AReg.get_cp(res1, A as int).Some? && AReg.get_cp(res1, A as int).value == cpA;
      rfFresh := M.FreshBodyMatchPlus(crv, str, A as int, res1, ov, ncap, nlook, nquant);   // (G3b) the plus replay
      assert rfFresh == AI.FFindMatchPlus(bodycodeB, host, crv.f_plus_bc, str, ov, LAnc.Backward, cpA,
                         AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant), 0, cdnA).0 by {
        BRG.FreshPlusLBUnfold(crv, str, A as int, res1, ov, host, ncap, nlook, nquant);
      }
      assert rfA == rfFresh.value;
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert rfFresh.Some?;
  
      // the FLookLoop value/quant lifts at owner == A
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert CM.RegsAgreeInside(res0, rfFresh.value.capture_regs,
                                PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(host))) by {
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert 1 <= A as int <= maxlook && M.MatchedPosLA(crv, res1, A as int);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert M.VBody(crv, A as int) == host;
      }
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert M.QuantClkAgreeInside(res2, rfFresh.value.quant_regs, M.QIdsOuter(host)) by {
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert 1 <= A as int <= maxlook && M.MatchedPosLA(crv, res1, A as int);
      }
    }
    assert {:split_here} true;   // (E3) section boundary: its own assertion batch

    // ==== BASE: g DIRECT in host ====
    assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
    M.PlusGateBodyCdn(re, crv, A, laA, host);   // (G3b) the uniform gate at the row body
    RowPlusFactsS(host, crv.f_plus_bc, nlook);   // (G3b) the plus twin's premises
    assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
    assert crv.f_look_cdns[A as int] == LCdn.compile_cdns(host);   // (G5b-2) LookEntryOk
    SubFirstLeafDirectInFreshLBS(rer, qmB, crv, str, ov, A, res1, host, g, ncap, nlook, nquant);
    var rfc := rfFresh.value.capture_regs;
    var rfl := rfFresh.value.look_regs;
    var rfq := rfFresh.value.quant_regs;
    assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
    assert g in PIV.GmOfLive(host, rfc, rfl, rfq)
           && lsubA.value[g] == LBV.SwapRange(PIV.GmOfLive(host, rfc, rfl, rfq)[g]);
    // presence + dominance on the FRESH banks
    assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
    LookBodyFactsKBCdn(re, crv, A);          // (W16) CapUnique/QuantUnique/LookUnique(host)
    assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
    assert CM.ThreadRegsWf(rfFresh.value, ncap, nlook, nquant);   // (G3b) from the carrier
    assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
    assert PIV.CapRegWf(rfc);
    assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
    assert forall c: nat :: c in PIV.CapIds(host) && AI.get_idx(rfc.a_clk, CP.start_reg(c)) < 0
                            ==> AI.get_idx(rfc.a_cp, CP.start_reg(c)) < 0;
    assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
    NI.GmOfLivePresenceExtractLkCdn(host, rfFresh.value.capture_regs, rfl, rfq, g);
    assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
    assert AReg.as_arrays(rfl).1 == rfl.a_clk && AReg.as_arrays(rfq).1 == rfq.a_clk;
    assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
    assert PIV.PathPresentLk(host, rfc.a_clk, rfl.a_clk, rfq.a_clk, -1, g);
    assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
    assert AI.get_idx(rfc.a_clk, CP.start_reg(g)) >= 0
           && AI.get_idx(rfc.a_cp, CP.start_reg(g)) >= 0
           && AI.get_idx(rfc.a_clk, CP.start_reg(g))
              >= PIV.MxAtGidLk(host, rfc.a_clk, rfl.a_clk, rfq.a_clk, -1, g);
    assert {:split_here} true;   // (E3) residual sub-section
    // transport onto the reconstructed banks (no-look path; quant clocks from the value lift)
    assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
    assert forall c: nat :: c in PIV.CapIdsOutsideLooks(host) ==>
                              AI.get_idx(res0.a_clk, CP.start_reg(c)) == AI.get_idx(rfc.a_clk, CP.start_reg(c))
    by {
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      forall c: nat | c in PIV.CapIdsOutsideLooks(host)
        ensures AI.get_idx(res0.a_clk, CP.start_reg(c)) == AI.get_idx(rfc.a_clk, CP.start_reg(c))
      {
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert CP.start_reg(c) in PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(host));
      }
    }
    assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
    assert forall q: nat :: q in PIV.QuantIdsOutsideLooks(host) ==>
                              AI.get_idx(res2.a_clk, q as int) == AI.get_idx(rfq.a_clk, q as int)
    by {
      forall q: nat | q in PIV.QuantIdsOutsideLooks(host)
        ensures AI.get_idx(res2.a_clk, q as int) == AI.get_idx(rfq.a_clk, q as int)
      {
        assert (q as int) in M.QIdsOuter(host);
      }
    }
    PathPresentLkDirectAgreeQ(host, res0.a_clk, res1.a_clk, res2.a_clk,
                              rfc.a_clk, rfl.a_clk, rfq.a_clk, -1, g);
    assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
    assert PIV.PathPresentLk(host, res0.a_clk, res1.a_clk, res2.a_clk, -1, g);
    assert {:split_here} true;   // (E3) residual sub-section
    // res0 == rf at g's registers (start + end): the value lift at A
    assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
    PIV.CapIdsSplit(host);
    assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
    assert g in PIV.CapIdsOutsideLooks(host);
    assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
    assert CP.start_reg(g) in PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(host))
           && CP.end_reg(g) in PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(host));
    assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
    assert AI.get_idx(res0.a_clk, CP.start_reg(g)) == AI.get_idx(rfc.a_clk, CP.start_reg(g));
    assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
    assert AI.get_idx(res0.a_cp, CP.start_reg(g)) == AI.get_idx(rfc.a_cp, CP.start_reg(g));   // (2026-08-29) was rfc.a_clk — a slip that verified only the slow way
    assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
    assert AI.get_idx(res0.a_clk, CP.end_reg(g)) == AI.get_idx(rfc.a_clk, CP.end_reg(g));
    assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
    assert AI.get_idx(res0.a_cp, CP.end_reg(g)) == AI.get_idx(rfc.a_cp, CP.end_reg(g));
    // dominance transported (Mx equality from the same transport)
    assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
    assert PIV.MxAtGidLk(host, res0.a_clk, res1.a_clk, res2.a_clk, -1, g)
        == PIV.MxAtGidLk(host, rfc.a_clk, rfl.a_clk, rfq.a_clk, -1, g);
    // the value chain with the endpoint swap absorbed by NormRange: leaf[g] ==
    // SwapRange(GmOfLive[g]) (the LB wrapper), GmOfLive[g] == LiveRange(rf,g),
    // LiveRange(rf,g) == LiveRange(res0,g)
    assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
    NI.GmOfLiveKeepsPresentLkCdn(host, rfFresh.value.capture_regs, rfl, rfq, g);
    assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
    assert PIV.GmOfLive(host, rfc, rfl, rfq)[g] == PIV.LiveRange(rfc.a_cp, rfc.a_clk, g);
    assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
    assert PIV.LiveRange(rfc.a_cp, rfc.a_clk, g) == PIV.LiveRange(res0.a_cp, res0.a_clk, g);
    assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
    NormSwapCong(PIV.LiveRange(res0.a_cp, res0.a_clk, g));
    assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
    assert PIV.NormRange(lsubA.value[g]) == PIV.NormRange(PIV.LiveRange(res0.a_cp, res0.a_clk, g));
  }

  /** (G5a-1 P5b) The narrow form, as a corollary of `ForwardFindRecLBBaseCdn`. */
  lemma ForwardFindRecLBBase(   // (E3) opaque preamble block

    rer: LW.RegExpRecord, qm: AR.QMap, crv: CP.FCompiled, str: string, ast: R.regex, re: R.regex,
    ov: LOr.OracleView, res0: AReg.Regs, res1: AReg.Regs, res2: AReg.Regs,
    host: R.regex, A: nat, g: nat, ncap: int, nlook: int, nquant: int)
    // ---- whole-regex statics (fixed) ----
    requires T.TransWf(re) && NR.NestedFragmentRE(re)
    requires M.LookBodiesPlusGateRE(re)   // (G3a) the weak gate: lookbehind bodies stamp-free, lookahead bodies CIN
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
    requires M.LookPosO(res1, crv)   // (gate C, G2) set look records sit at positive rows
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
    NR.NarrowIsCdn(re);
    hide *;   // the wide premises are this lemma's own: match by name
    ForwardFindRecLBBaseCdn(// (E3) opaque preamble block

    rer, qm, crv, str, ast, re, ov, res0, res1, res2, host, A, g, ncap, nlook, nquant);
  }

}
