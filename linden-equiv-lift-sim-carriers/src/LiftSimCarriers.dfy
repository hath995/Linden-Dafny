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
module LindenElkLiftSimCarriers {
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

  // ==========================================================================
  // THE MAIN THEOREM, L3a: capturing positive lookaheads included. The
  // engine's full pipeline output IS the Linden tree-semantics answer, for
  // the whole lookbehind fragment with capturing forward lookaheads. This is
  // the (F) integration: the composite lockstep simulation delivers the leaf
  // ties, the endpoint assembly converts them into the reconstructed-register
  // denotation, and the existing extraction finishes.
  // ==========================================================================
  lemma MainTheoremL3(raw: R.raw_regex, str: string)
    requires NR.LookBehindFragmentRaw(raw)
    requires T.Latin1Wf(raw)
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
    NR.SpecRegexLookBehindFragment(raw);   // LookBehindFragmentRE(re)
    LTB.SpecRegexLookUnique(raw);          // unique lids, all >= 1
    assert NR.LookBehindFragmentRE(ast);
    PIV.SpecRegexCapUnique(raw);           // CapUnique(re)
    PIV.SpecRegexQuantUnique(raw);         // QuantUnique(re)
    var qm := AR.QMap(M.QmOfRE(re), OE.LmOf(re), AI.FBuildOracle(CP.FFullCompilation(ast), str));
    M.LookStaticPackage(raw, str, qm);

    NR.CompileToBytecodeRepLookBehind(re);
    var code := CP.compile_to_bytecode(re);
    var next := CP.compile(re, 0, CP.Progress).1;
    var endl: nat := next as nat;
    assert NR.NfaRepRE(re, code, 0, endl)
           && NR.GetPcRE(code, endl) == Some(RB.Accept) && |code| == endl + 1;
    PIV.CompileStutterTameRE(re);
    assert PSM.StaticOkRE(qm, re, code, endl);

    var maxcap := R.max_group(ast);
    var maxquant := R.max_quant(ast);
    assert R.max_group(re) == maxcap;
    assert R.max_quant(re) == R.imax(0, maxquant) == maxquant;
    var ncap := 2 * maxcap + 2;
    var nlook := R.max_lookaround(ast) + 1;
    var nquant := maxquant + 1;
    assert PSM.SizesOkRE(re, ncap, nlook, nquant);
    assert ngroups == (maxcap + 1) as nat;
    assert R.max_lookaround(re) == R.max_lookaround(ast) by {
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

    assert {:split_here} true;
    // ---- the spec tree ---------------------------------------------------
    LFU.ComputeTrIsTree(rer, [LS.Areg(T.Translate(re))], inp, LG.Empty, WP.Forward);
    var t := LFU.ComputeTr(rer, [LS.Areg(T.Translate(re))], inp, LG.Empty, WP.Forward);
    assert LS.IsTree(rer, [LS.Areg(T.Translate(re))], inp, LG.Empty, WP.Forward, t);
    assert LES.SpecRegex(raw) == T.Translate(re);
    EL.TranslateFragmentPikeLk(re);
    EL.BooleanCorrectLk(rer, T.Translate(re), inp, t);
    assert forall i :: 0 <= i < |[LS.Areg(T.Translate(re))]| ==> ![LS.Areg(T.Translate(re))][i].Acheck?;
    M.BoolTreeLbIrrel(rer, [LS.Areg(T.Translate(re))], inp, BS.CanExit, BS.CannotExit, t);
    assert EL.BoolTreeLk(rer, [LS.Areg(T.Translate(re))], inp, BS.CannotExit, t);
    TranslateNoBackref(re);
    assert NoBackrefActions([LS.Areg(T.Translate(re))]);
    var fuel0 := FS.ActionsFuel([LS.Areg(T.Translate(re))], inp, WP.Forward) + 1;
    assert FS.ComputeTree(rer, [LS.Areg(T.Translate(re))], inp, LG.Empty, WP.Forward, fuel0) == Some(t);
    ComputePikeSubtreeLk(rer, [LS.Areg(T.Translate(re))], inp, LG.Empty, WP.Forward, fuel0, t);
    assert PTL.PikeSubtreeLk(t);

    assert {:split_here} true;
    // ---- the CHECKED tree (machine A's carrier) ---------------------------
    WOE.WalkOkEntry(re);
    assert EL.PikeLkActions([LS.Areg(T.Translate(re))]) by {
      assert [LS.Areg(T.Translate(re))] == [LS.Areg(T.Translate(re))] + [];
      assert EL.PikeLkActions([]);
      EL.PikeLkActionsConsIff(LS.Areg(T.Translate(re)), []);
    }
    assert LL.OracleOkSuffix(rer, qm, inp);
    var S := PIV.CapIdsInLooks(re);
    M.LkBodyGroupsEqCapIdsInLooks(re);
    assert S == LL.LkBodyGroups(T.Translate(re));
    assert LL.LkActsInS([LS.Areg(T.Translate(re))], S) by {
      LL.LkBodyGroupsConfines(T.Translate(re), S);
      assert LL.LkBodiesInS(T.Translate(re), S);
    }
    LL.ComputeTrLkConfined(rer, [LS.Areg(T.Translate(re))], inp, LG.Empty, WP.Forward, S);
    var tstar := ATR.ActionsTreeRepRE(rer, qm, [LS.Areg(T.Translate(re))], code, 0, inp, BS.CannotExit, t, S);
    assert TREP.TreeRepRE(qm, tstar, code, 0, inp, false);

    assert {:split_here} true;
    // ---- the engine pipeline ---------------------------------------------
    var crv := CP.FFullCompilation(ast);
    M.FFullCompilationFacts(ast);
    assert crv.f_main_ast == ast && crv.f_main_bc == code && crv.f_main_cdns == LCdn.compile_cdns(ast);
    var ov := AI.FBuildOracle(crv, str);
    OB.FBuildOracleViewLen(crv, str);                     // |ov| == |str| + 1 (for the backward LB gate)
    var capture := AReg.init_regs(ncap);
    var look := AReg.init_regs(nlook);
    var quant := AReg.init_regs(nquant);
    var ctx := AI.cp_context(0, str, LAnc.Forward);
    var inits := AI.FInitState(code, 0, capture, look, quant, 0, ctx);
    var fmres := AI.FFindMatch(code, str, inits, ov, LAnc.Forward, crv.f_main_cdns);
    var result := fmres.0;
    assert AI.FFindMatchPlus(code, ast, crv.f_plus_bc, str, ov, LAnc.Forward, 0,
                             capture, look, quant, 0, crv.f_main_cdns).0
        == (match result
            case None => None
            case Some(thread) => Some(AI.FReconstructPlus(thread, ast, crv.f_plus_bc, str, fmres.1, LAnc.Forward).0));

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
    GateStaticsFromTables(qm, re, crv, ncap, nlook, nquant);
    assert GateStaticsOk(qm, re, crv, ncap, nlook, nquant);

    assert {:split_here} true;
    // ---- the composite lockstep (both machines) ---------------------------
    PSM.InitialPikeInvFullRE(rer, qm, re, code, endl, ngroups, str, tstar, inits, ncap, nlook, nquant);
    assert ctx.nextchar == AI.get_char(str, 0);
    assert PIV.ContextOkRE(str, inits.cp, inits.context);
    assert qm.ov == ov;
    L3aCompositeClose(rer, qm, re, code, endl, ngroups, crv, str, ov, S, tstar, t, inp,
                      inits, crv.f_main_cdns, result, ncap, nlook, nquant);
    assert BestTieLk(re, crv, str, ov, S, LT.FirstLeaf(t, inp), result, ncap, nlook, nquant);

    assert {:split_here} true;
    // ---- stage the engine answer ------------------------------------------
    var bc := AI.FBuildCapture(crv, str, ov);
    assert AI.FMatcher(crv, str) == bc.0;
    assert AI.FFullMatch(raw, str) == bc.0;
    var fmp := AI.FFindMatchPlus(crv.f_main_bc, crv.f_main_ast, crv.f_plus_bc, str, ov,
                                 LAnc.Forward, 0, capture, look, quant, 0, crv.f_main_cdns);
    assert fmp == AI.FFindMatchPlus(code, ast, crv.f_plus_bc, str, ov,
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
      // winning-thread wf (mirrors the endpoint's own derivation, needed here
      // for the reconstruct identity)
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

      // the oracle is stable through the whole pipeline: fmp.1 == ov
      PSM.StaticOkNoWrite(qm, re, code, endl);
      CM.FFindMatchOvStable(code, str, inits, ov, LAnc.Forward, crv.f_main_cdns);
      assert fmres.1 == ov;
      assert fmp.1 == ov by {
        assert fmp == (Some(AI.FReconstructPlus(thread, ast, crv.f_plus_bc, str, ov, LAnc.Forward).0),
                       AI.FReconstructPlus(thread, ast, crv.f_plus_bc, str, ov, LAnc.Forward).1);
        M.FNulledPlusIdentity(ast, thread.capture_regs, thread.look_regs, thread.quant_regs,
                              crv.f_plus_bc, str, ov, LAnc.Forward);
      }

      // the leaf + the endpoint assembly
      assert LT.FirstLeaf(t, inp).Some?;
      var leaf := LT.FirstLeaf(t, inp).value;
      assert BestTieLk(re, crv, str, ov, S, Some(leaf), Some(thread), ncap, nlook, nquant);
      assert forall lx: nat :: lx in LTB.LookIds(re) ==> 1 <= lx;
      M.FirstLeafOrdered(t, inp, leaf);                     // leaf.1 ORDERED (item 0)
      L3aEndpointAssembly(ast, re, crv, code, endl, str, ov, S, thread, leaf,
                          inits, capture, look, quant, crv.f_main_cdns, ncap, nlook, nquant);
      var res := AI.FLookLoop(crv, str, 1, R.max_lookaround(ast),
                              thread.capture_regs, thread.look_regs, thread.quant_regs, ov);
      var synthetic := AI.Thread(thread.pc, res.0, res.1, res.2, thread.exit_allowed);
      assert leaf.1 == PIV.NormGm(PIV.GmOfLive(re, res.0, thread.look_regs, res.2));
      assert res.1 == thread.look_regs;
      assert CM.ThreadRegsWf(synthetic, ncap, nlook, nquant) && M.QuantRegsFinal(synthetic);

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

      // ---- extraction (the L1 discipline: restate + hide) ------------------
      assert EL.BoolTreeLk(LES.TheRer(raw), [LS.Areg(LES.SpecRegex(raw))], LC.InitInput(str), BS.CannotExit, t);
      assert LS.IsTree(LES.TheRer(raw), [LS.Areg(LES.SpecRegex(raw))], LC.InitInput(str), LG.Empty, WP.Forward, t);
      assert CM.ThreadRegsWf(synthetic, 2 * R.max_group(R.annotate(raw)) + 2,
                             R.max_lookaround(R.annotate(raw)) + 1,
                             R.max_quant(R.annotate(raw)) + 1) by {
        hide *;
        assert ast == R.annotate(raw);
        assert R.max_lookaround(ast) + 1 == nlook;
        assert CM.ThreadRegsWf(synthetic, ncap, nlook, nquant);
      }
      assert M.QuantRegsFinal(synthetic);
      assert leaf.1 == PIV.NormGm(PIV.GmOfLive(R.lazy_prefix(R.annotate(raw)), synthetic.capture_regs,
                                               synthetic.look_regs, synthetic.quant_regs)) by {
        hide *;
        assert ast == R.annotate(raw) && re == R.lazy_prefix(ast);
        assert synthetic.capture_regs == res.0 && synthetic.look_regs == res.1 == thread.look_regs
               && synthetic.quant_regs == res.2;
        assert leaf.1 == PIV.NormGm(PIV.GmOfLive(re, res.0, thread.look_regs, res.2));
      }
      assert LT.FirstLeaf(t, LC.InitInput(str)) == Some(leaf);
      assert AI.FFullMatch(raw, str)
          == Some(AI.filter_reset(R.annotate(raw), synthetic.capture_regs, synthetic.look_regs,
                                  synthetic.quant_regs, -1));
      { hide *; M.MainExtraction(raw, str, t, synthetic, leaf); }
    }
  }

  /** BRICK D1 — the per-body composite sim for a matched positive lookAHEAD.
      Runs the (nested-capable) recursive composite simulation
      `L3aCompositeCloseRec` on a matched forward-lookahead's IN-CONTEXT FRESH body
      replay and projects the (E3) look-path carrier
      `LookNestOkT(body, CapIdsInLooks(body), leafgm_body, rf)` — coupling the engine
      replay `rf` to the body's SPEC first-leaf group map `leafgm_body` (the
      non-vacuous coupling of the C4d finding; a bare `GmOfLive(body, rf)` keying
      is vacuously true, MainMatchInsideCapsInit).

      Body-match framing (mirrors `M.BodyTreeAtCpNested` — the `FindMatchSimRENested`
      body precedent): `bodycode == compile_to_bytecode(body)` (which is
      `compile_to_bytecode(capture_regex(la, body))` for a lookahead, since
      `capture_regex(Lookahead, body) == body`); the shared TOP-LEVEL `crv`/`ov`
      (NOT a fresh `FFullCompilation(body)`). The replay is the actual FLookLoop
      REPLAY value `FFindMatchPlus`, from FRESH registers — `FNulledPlusIdentity` on
      the `QuantRegsFinal` match makes the plus reconstruction the identity, so
      `rf == FFindMatch`, and `LookNestOkT` (which reads only the three register
      banks) transports across that identity.

      FRAMING VERDICT (brick D1): `L3aCompositeCloseRec` / `LiftFindMatchCRec` are
      stated GENERALLY over `re/code/crv/ov` — the ONLY whole-regex-shaped
      hypothesis is `code == compile_to_bytecode(re)`, discharged here by
      `bodycode == compile_to_bytecode(body)`. So the driver applies to a body
      match DIRECTLY (mirroring how `FindMatchSimRENested` is applied to bodies),
      WITHOUT the `FFullCompilation` wrapper. The crv-keyed statics
      `GateStaticsOk`/`LookTablesOk`/`LookUnique(body)` are taken as hypotheses (the
      FLookLoop caller descends them from the top-level regex — `LookTablesOk` and
      `LookUnique` descend STRUCTURALLY through `Re_lookaround`).

      DEPTH BOUNDARY (the residual sub-brick): `GateStaticsOk(qm, body, crv, ...)`
      is the DEPTH-1-locked hypothesis — via `GateStaticAt` (LiftSim :5515) it forces
      every directly-gated look of `body` to have a LOOK-FREE body (`StaticOkRE` +
      `LookFreeRE(gatebody)`), and the gate-pass carrier preserver (:20693) derives
      `CapIdsInLooks(gatebody) == {}` from it. So it is establishable (via
      `GateStaticsFromTables`, which needs `LookBehindFragmentRE(body)`) exactly when
      `body`'s directly-gated looks are look-free. Deeper nesting needs `GateStaticAt`
      generalized to nested gate bodies (`StaticOkNestedRE`) and the gate-pass carrier
      fed the recursive per-body `LookNestOkT` — that generalization IS the remaining
      recursion, reported as the precise blocker. */
  lemma LookNestOkTFromBodyReplay(
    rer: LW.RegExpRecord, qm: AR.QMap, la: R.lookaround, body: R.regex, bodycode: RB.code,
    endl: nat, ngroups: nat, crv: CP.FCompiled, str: string, cp: nat, ov: LOr.OracleView,
    lookcdn: LCdn.cdns, plus_bc: seq<RB.code>, ncap: int, nlook: int, nquant: int)
    requires la.Lookahead?
    requires PSM.StaticOkNestedRE(qm, body, bodycode, endl)
    requires NR.NegLooksLookFreeRE(body)
    requires PSM.SizesOkRE(body, ncap, nlook, nquant)
    requires qm.ov == ov && !rer.multiline && !rer.ignoreCase
    requires cp <= |str|
    requires bodycode == CP.compile_to_bytecode(body)
    requires LL.OracleOkSuffix(rer, qm, PIV.InpOfCp(str, cp))
    requires |ov| == |str| + 1
    requires OE.OracleColsOk(rer, qm, str)                    // (L5 F7d) whole-string oracle correctness (backward keystone)
    // crv-keyed statics (caller descends from the top-level regex)
    // (BRICK D5) NESTED per-lid package + positive-lookahead-nesting scope, so the
    // per-body composite sim `L3aCompositeCloseRec` applies at depth >= 2.
    requires GateStaticsOkNested(qm, body, crv, ncap, nlook, nquant)
    requires L5ScopeV1RE(body)               // (s6 widening; was M.NoPosLookbehindRE(body))
    requires LTB.LookUnique(body)
    requires LTB.LookTablesOk(body, crv)
    ensures
      var inp := PIV.InpOfCp(str, cp);
      var t := LFU.ComputeTr(rer, [LS.Areg(T.Translate(body))], inp, LG.Empty, WP.Forward);
      var rf := AI.FFindMatchPlus(bodycode, body, plus_bc, str, ov, LAnc.Forward, cp,
                                  AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant),
                                  0, lookcdn).0;
      rf.Some? ==>
        LT.FirstLeaf(t, inp).Some?
        && LookNestOkTTop(body, PIV.CapIdsInLooks(body), LT.FirstLeaf(t, inp).value.1, rf.value)
  {
    var inp := PIV.InpOfCp(str, cp);
    var acts := [LS.Areg(T.Translate(body))];
    var S := PIV.CapIdsInLooks(body);

    // ---- the spec tree (mirror BodyTreeAtCpNested) -----------------------
    LFU.ComputeTrIsTree(rer, acts, inp, LG.Empty, WP.Forward);
    var t := LFU.ComputeTr(rer, acts, inp, LG.Empty, WP.Forward);
    assert LS.IsTree(rer, acts, inp, LG.Empty, WP.Forward, t);
    EL.TranslateFragmentPikeLkRec(body);
    EL.BooleanCorrectLkRec(rer, T.Translate(body), inp, t);
    assert forall i :: 0 <= i < |acts| ==> !acts[i].Acheck?;
    M.BoolTreeLbIrrel(rer, acts, inp, BS.CanExit, BS.CannotExit, t);
    assert EL.BoolTreeLk(rer, acts, inp, BS.CannotExit, t);

    // PikeSubtreeLk(t) (mirror the whole-regex entry, :15798)
    TranslateNoBackref(body);
    assert NoBackrefActions(acts);
    var fuel0 := FS.ActionsFuel(acts, inp, WP.Forward) + 1;
    FS.FunctionalTerminates(rer, acts, inp, LG.Empty, WP.Forward, fuel0);
    assert FS.ComputeTree(rer, acts, inp, LG.Empty, WP.Forward, fuel0) == Some(t);
    ComputePikeSubtreeLk(rer, acts, inp, LG.Empty, WP.Forward, fuel0, t);
    assert PTL.PikeSubtreeLk(t);

    // ---- the CHECKED tree (mirror BodyTreeAtCpNested) --------------------
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
    var tstar := ATR.ActionsTreeRepRENested(rer, qm, acts, bodycode, 0, inp, BS.CannotExit, t, S);
    assert TREP.TreeRepRE(qm, tstar, bodycode, 0, inp, false);
    assert TT.TreeThreadRE(rer, qm, bodycode, inp, tstar, 0, false);

    // ---- the fresh entry VM + PikeInvFullRE (mirror FindMatchBodyAtCpNested) --
    var ctx := AI.cp_context(cp, str, LAnc.Forward);
    var capture := AReg.init_regs(ncap);
    var look := AReg.init_regs(nlook);
    var quant := AReg.init_regs(nquant);
    var vms := AI.FInitState(bodycode, cp, capture, look, quant, 0, ctx);
    assert ctx.nextchar == AI.get_char(str, cp);
    PSM.InitialPikeInvFullREAtCpNested(rer, qm, body, bodycode, endl, ngroups, str, cp, tstar,
                                       vms, ncap, nlook, nquant);
    assert PSM.PikeInvFullRE(rer, qm, body, bodycode, endl, ngroups, str,
                             PT.PikeTreeInitialState(tstar, inp), vms, ncap, nlook, nquant);
    assert PIV.ContextOkRE(str, vms.cp, vms.context);

    // code shape: every SetQuantToClock has b == false (mirror :15777)
    forall pc: nat, q: int, b: bool | NR.GetPcRE(bodycode, pc) == Some(RB.SetQuantToClock(q, b))
      ensures !b
    {
      if pc < endl {
        NI.CodeShapeAt(body, bodycode, 0, endl, pc);
      } else if pc == endl {
      } else {
        assert pc >= |bodycode|;
      }
    }

    // ---- run the composite sim on the body match -------------------------
    var result := AI.FFindMatch(bodycode, str, vms, ov, LAnc.Forward, lookcdn).0;
    L5ScopeV1ImpliesL5(body);               // (L5 F7f) the composite chain is L5-scoped
    L3aCompositeCloseRec(rer, qm, body, bodycode, endl, ngroups, crv, str, ov, S, tstar, t, inp,
                         vms, lookcdn, result, ncap, nlook, nquant);
    assert BestTieLkNestedTop(rer, body, crv, str, ov, S, LT.FirstLeaf(t, inp), result, ncap, nlook, nquant);

    // ---- reconcile FFindMatchPlus (fresh) with FFindMatch ----------------
    var fmres := AI.FFindMatch(bodycode, str, vms, ov, LAnc.Forward, lookcdn);
    assert result == fmres.0;
    var rf := AI.FFindMatchPlus(bodycode, body, plus_bc, str, ov, LAnc.Forward, cp,
                                capture, look, quant, 0, lookcdn);
    assert rf.0 == (match result
                    case None => None
                    case Some(thread) =>
                      Some(AI.FReconstructPlus(thread, body, plus_bc, str, fmres.1, LAnc.Forward).0));
    if rf.0.Some? {
      assert result.Some?;
      var thread := result.value;
      // winning-thread wf + quant-final -> reconstruct identity (mirror :15896)
      CM.RegsClocksLEInit(ncap, 0);
      CM.RegsClocksLEInit(nlook, 0);
      CM.RegsClocksLEInit(nquant, 0);
      CM.FInitStateClocksLE(bodycode, cp, capture, look, quant, 0, ctx);
      CM.FInitStateRegsWf(bodycode, cp, ncap, nlook, nquant, 0, ctx);
      assert M.VmQuantFinal(vms) by {
        var th0 := AI.init_thread(capture, look, quant);
        assert M.QuantRegsFinal(th0) by {
          forall k ensures AI.get_idx(quant.a_cp, k) < 0 && AI.get_idx(quant.a_clk, k) >= -1 {
            if 0 <= k < |quant.a_cp| { assert quant.a_cp[k] == -1; }
            if 0 <= k < |quant.a_clk| { assert quant.a_clk[k] == -1; }
          }
        }
        forall t2 | t2 in vms.active ensures M.QuantRegsFinal(t2) { assert t2 == th0; }
      }
      M.FFindMatchThreadFacts(bodycode, str, vms, ov, LAnc.Forward, lookcdn, ncap, nlook, nquant);
      assert CM.ThreadRegsWf(thread, ncap, nlook, nquant) && M.QuantRegsFinal(thread);
      M.FNulledPlusIdentity(body, thread.capture_regs, thread.look_regs, thread.quant_regs,
                            plus_bc, str, fmres.1, LAnc.Forward);
      assert AI.FReconstructPlus(thread, body, plus_bc, str, fmres.1, LAnc.Forward).0 == thread;
      assert rf.0.value == thread;
      // project the (E3) carrier out of BestTieLkNestedTop and transport it
      assert LT.FirstLeaf(t, inp).Some?;
      assert LookNestOkTTop(body, S, LT.FirstLeaf(t, inp).value.1, thread);
    }
  }

  /** (BRICK D-8 FINDING 1) The BACKWARD per-body carrier: a verbatim twin of
      `LookNestOkTFromBodyReplay` whose only difference is the projected conjunct.
      The SAME `BestTieLkNestedTop(body, ...)` (obtained at :23036 via
      `L3aCompositeCloseRec`) ALSO ensures `LookNestBackTTop(body, ...)` (its third
      conjunct); we project THAT out of the winning body replay instead of the
      forward `LookNestOkTTop`. Used by the reverse-recon descent lemma to tie a
      deep, recon-live inner capture into the body's spec group map. */
  lemma LookNestBackTFromBodyReplay(
    rer: LW.RegExpRecord, qm: AR.QMap, la: R.lookaround, body: R.regex, bodycode: RB.code,
    endl: nat, ngroups: nat, crv: CP.FCompiled, str: string, cp: nat, ov: LOr.OracleView,
    lookcdn: LCdn.cdns, plus_bc: seq<RB.code>, ncap: int, nlook: int, nquant: int)
    requires la.Lookahead?
    requires PSM.StaticOkNestedRE(qm, body, bodycode, endl)
    requires NR.NegLooksLookFreeRE(body)
    requires PSM.SizesOkRE(body, ncap, nlook, nquant)
    requires qm.ov == ov && !rer.multiline && !rer.ignoreCase
    requires cp <= |str|
    requires bodycode == CP.compile_to_bytecode(body)
    requires LL.OracleOkSuffix(rer, qm, PIV.InpOfCp(str, cp))
    requires |ov| == |str| + 1
    requires OE.OracleColsOk(rer, qm, str)                    // (L5 F7d) whole-string oracle correctness (backward keystone)
    requires GateStaticsOkNested(qm, body, crv, ncap, nlook, nquant)
    requires L5ScopeV1RE(body)               // (s6 widening; was M.NoPosLookbehindRE(body))
    requires LTB.LookUnique(body)
    requires LTB.LookTablesOk(body, crv)
    ensures
      var inp := PIV.InpOfCp(str, cp);
      var t := LFU.ComputeTr(rer, [LS.Areg(T.Translate(body))], inp, LG.Empty, WP.Forward);
      var rf := AI.FFindMatchPlus(bodycode, body, plus_bc, str, ov, LAnc.Forward, cp,
                                  AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant),
                                  0, lookcdn).0;
      (rf.Some? <==> LT.FirstLeaf(t, inp).Some?)
      && (rf.Some? ==>
            LT.FirstLeaf(t, inp).Some?
            && LookNestBackTTop(body, crv, str, ov, PIV.CapIdsInLooks(body),
                                LT.FirstLeaf(t, inp).value.1, rf.value, ncap, nlook, nquant)
            && LookNestBackTTopDeep(rer, body, crv, str, ov, PIV.CapIdsInLooks(body),
                                    LT.FirstLeaf(t, inp).value.1, rf.value, ncap, nlook, nquant)
            // the FORWARD presence carrier (leaf-witness ==> gate crossed + dominant)
            && LookNestOkTTop(body, PIV.CapIdsInLooks(body), LT.FirstLeaf(t, inp).value.1, rf.value)
            // the carrier thread's own look-bank invariants (fresh run): the deep
            // per-g2 package reads them at the crossed inner lids.
            && CM.LookClkSetWithCp(rf.value.look_regs)
            && CM.LookCpSetWithClk(rf.value.look_regs)
            && CM.LookCpsLE(rf.value.look_regs, |str|))
  {
    var inp := PIV.InpOfCp(str, cp);
    var acts := [LS.Areg(T.Translate(body))];
    var S := PIV.CapIdsInLooks(body);

    // ---- the spec tree (mirror BodyTreeAtCpNested) -----------------------
    LFU.ComputeTrIsTree(rer, acts, inp, LG.Empty, WP.Forward);
    var t := LFU.ComputeTr(rer, acts, inp, LG.Empty, WP.Forward);
    assert LS.IsTree(rer, acts, inp, LG.Empty, WP.Forward, t);
    EL.TranslateFragmentPikeLkRec(body);
    EL.BooleanCorrectLkRec(rer, T.Translate(body), inp, t);
    assert forall i :: 0 <= i < |acts| ==> !acts[i].Acheck?;
    M.BoolTreeLbIrrel(rer, acts, inp, BS.CanExit, BS.CannotExit, t);
    assert EL.BoolTreeLk(rer, acts, inp, BS.CannotExit, t);

    // PikeSubtreeLk(t) (mirror the whole-regex entry, :15798)
    TranslateNoBackref(body);
    assert NoBackrefActions(acts);
    var fuel0 := FS.ActionsFuel(acts, inp, WP.Forward) + 1;
    FS.FunctionalTerminates(rer, acts, inp, LG.Empty, WP.Forward, fuel0);
    assert FS.ComputeTree(rer, acts, inp, LG.Empty, WP.Forward, fuel0) == Some(t);
    ComputePikeSubtreeLk(rer, acts, inp, LG.Empty, WP.Forward, fuel0, t);
    assert PTL.PikeSubtreeLk(t);

    // ---- the CHECKED tree (mirror BodyTreeAtCpNested) --------------------
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
    var tstar := ATR.ActionsTreeRepRENested(rer, qm, acts, bodycode, 0, inp, BS.CannotExit, t, S);
    assert TREP.TreeRepRE(qm, tstar, bodycode, 0, inp, false);
    assert TT.TreeThreadRE(rer, qm, bodycode, inp, tstar, 0, false);

    // ---- the fresh entry VM + PikeInvFullRE (mirror FindMatchBodyAtCpNested) --
    var ctx := AI.cp_context(cp, str, LAnc.Forward);
    var capture := AReg.init_regs(ncap);
    var look := AReg.init_regs(nlook);
    var quant := AReg.init_regs(nquant);
    var vms := AI.FInitState(bodycode, cp, capture, look, quant, 0, ctx);
    assert ctx.nextchar == AI.get_char(str, cp);
    PSM.InitialPikeInvFullREAtCpNested(rer, qm, body, bodycode, endl, ngroups, str, cp, tstar,
                                       vms, ncap, nlook, nquant);
    assert PSM.PikeInvFullRE(rer, qm, body, bodycode, endl, ngroups, str,
                             PT.PikeTreeInitialState(tstar, inp), vms, ncap, nlook, nquant);
    assert PIV.ContextOkRE(str, vms.cp, vms.context);

    // code shape: every SetQuantToClock has b == false (mirror :15777)
    forall pc: nat, q: int, b: bool | NR.GetPcRE(bodycode, pc) == Some(RB.SetQuantToClock(q, b))
      ensures !b
    {
      if pc < endl {
        NI.CodeShapeAt(body, bodycode, 0, endl, pc);
      } else if pc == endl {
      } else {
        assert pc >= |bodycode|;
      }
    }

    // ---- run the composite sim on the body match -------------------------
    var result := AI.FFindMatch(bodycode, str, vms, ov, LAnc.Forward, lookcdn).0;
    L5ScopeV1ImpliesL5(body);               // (L5 F7f) the composite chain is L5-scoped
    L3aCompositeCloseRec(rer, qm, body, bodycode, endl, ngroups, crv, str, ov, S, tstar, t, inp,
                         vms, lookcdn, result, ncap, nlook, nquant);
    assert BestTieLkNestedTop(rer, body, crv, str, ov, S, LT.FirstLeaf(t, inp), result, ncap, nlook, nquant);

    // ---- reconcile FFindMatchPlus (fresh) with FFindMatch ----------------
    var fmres := AI.FFindMatch(bodycode, str, vms, ov, LAnc.Forward, lookcdn);
    assert result == fmres.0;
    var rf := AI.FFindMatchPlus(bodycode, body, plus_bc, str, ov, LAnc.Forward, cp,
                                capture, look, quant, 0, lookcdn);
    assert rf.0 == (match result
                    case None => None
                    case Some(thread) =>
                      Some(AI.FReconstructPlus(thread, body, plus_bc, str, fmres.1, LAnc.Forward).0));
    if rf.0.Some? {
      assert result.Some?;
      var thread := result.value;
      // winning-thread wf + quant-final -> reconstruct identity (mirror :15896)
      CM.RegsClocksLEInit(ncap, 0);
      CM.RegsClocksLEInit(nlook, 0);
      CM.RegsClocksLEInit(nquant, 0);
      CM.FInitStateClocksLE(bodycode, cp, capture, look, quant, 0, ctx);
      CM.FInitStateRegsWf(bodycode, cp, ncap, nlook, nquant, 0, ctx);
      assert M.VmQuantFinal(vms) by {
        var th0 := AI.init_thread(capture, look, quant);
        assert M.QuantRegsFinal(th0) by {
          forall k ensures AI.get_idx(quant.a_cp, k) < 0 && AI.get_idx(quant.a_clk, k) >= -1 {
            if 0 <= k < |quant.a_cp| { assert quant.a_cp[k] == -1; }
            if 0 <= k < |quant.a_clk| { assert quant.a_clk[k] == -1; }
          }
        }
        forall t2 | t2 in vms.active ensures M.QuantRegsFinal(t2) { assert t2 == th0; }
      }
      M.FFindMatchThreadFacts(bodycode, str, vms, ov, LAnc.Forward, lookcdn, ncap, nlook, nquant);
      assert CM.ThreadRegsWf(thread, ncap, nlook, nquant) && M.QuantRegsFinal(thread);
      M.FNulledPlusIdentity(body, thread.capture_regs, thread.look_regs, thread.quant_regs,
                            plus_bc, str, fmres.1, LAnc.Forward);
      assert AI.FReconstructPlus(thread, body, plus_bc, str, fmres.1, LAnc.Forward).0 == thread;
      assert rf.0.value == thread;
      // project the (E4) BACKWARD carrier out of BestTieLkNestedTop and transport it
      assert LT.FirstLeaf(t, inp).Some?;
      assert LookNestBackTTop(body, crv, str, ov, S, LT.FirstLeaf(t, inp).value.1, thread,
                              ncap, nlook, nquant);
      // project the DEEP carrier too (BestTieLkNestedTop now carries it after R2 wiring).
      assert LookNestBackTTopDeep(rer, body, crv, str, ov, S, LT.FirstLeaf(t, inp).value.1, thread,
                                  ncap, nlook, nquant);
      // project the FORWARD presence carrier (E3-Top).
      assert LookNestOkTTop(body, S, LT.FirstLeaf(t, inp).value.1, thread);
      // fresh-run look-bank invariants on the winner (init banks are all-unset)
      RL.AInitLaws(nlook);
      assert CM.VmLookClkSet(vms) by {
        assert AI.init_thread(capture, look, quant).look_regs == look;
        forall l: int | AI.get_idx(look.a_cp, l) >= 0 ensures AI.get_idx(look.a_clk, l) >= 0 {
          if 0 <= l < |look.a_cp| { assert look.a_cp[l] == -1; }
        }
      }
      CM.FFindMatchLookClkSet(bodycode, str, vms, ov, LAnc.Forward, lookcdn);
      assert CM.LookClkSetWithCp(thread.look_regs);
      assert CM.VmLookCpSet(vms) by {
        forall l: int | AI.get_idx(look.a_clk, l) >= 0 ensures AI.get_idx(look.a_cp, l) >= 0 {
          if 0 <= l < |look.a_clk| { assert look.a_clk[l] == -1; }
        }
      }
      CM.FFindMatchLookCpSet(bodycode, str, vms, ov, LAnc.Forward, lookcdn);
      assert CM.LookCpSetWithClk(thread.look_regs);
      assert CM.VmLookCpOk(vms, |str|) by {
        forall l: int ensures AI.get_idx(look.a_cp, l) <= |str| {
          if 0 <= l < |look.a_cp| { assert look.a_cp[l] == -1; }
        }
      }
      CM.FFindMatchLookCpOk(bodycode, str, vms, ov, LAnc.Forward, lookcdn);
      assert CM.LookCpsLE(thread.look_regs, |str|);
    }
  }

  /** (L5 F7c-3) THE LOOKBEHIND TWIN of `LookNestBackTFromBodyReplay`: for a
      positive lookbehind lid whose body is in the L5 scope, the FRESH BACKWARD
      body run (what `FLookLoop` runs for the lid) matches iff the body's
      backward spec tree has a result, and its winner carries all three nested
      carriers + the look-bank invariants against that backward leaf. */
  lemma LookNestBackTFromBodyReplayLB(
    rer: LW.RegExpRecord, qm: AR.QMap, la: R.lookaround, body: R.regex, bodycodeB: RB.code,
    crv: CP.FCompiled, str: string, cp: nat, ov: LOr.OracleView,
    lookcdn: LCdn.cdns, plus_bc: seq<RB.code>, ncap: int, nlook: int, nquant: int)
    requires la.Lookbehind?
    requires T.TransWf(body) && NR.NestedFragmentRE(body) && NR.NegLooksLookFreeRE(body)
    requires NR.NoNulledPlusRE(body)   // §2.5b interim: all stamps false
    requires FST.LBOnlyLooksRE(body)
    requires PIV.CapUnique(body) && PIV.QuantUnique(body) && LTB.LookUnique(body)
    requires PSM.SizesOkRE(body, ncap, nlook, nquant)
    requires !rer.ignoreCase && !rer.multiline
    requires cp <= |str| && |ov| == |str| + 1
    requires bodycodeB == CP.compile_to_bytecode(R.reverse_regex(body))
    requires qm.ov == ov && AR.LmapOk(body, qm) && OE.OracleColsOk(rer, qm, str)
    requires LTB.LookTablesOk(body, crv) && |crv.f_look_types| == |crv.f_look_ast|
    requires forall l: nat :: l in LTB.LookIds(body) ==> l < nlook
    ensures
      var inp := PIV.InpOfCp(str, cp);
      var t := LFU.ComputeTr(rer, [LS.Areg(T.Translate(body))], inp, LG.Empty, WP.Backward);
      var rb := LT.TreeRes(t, LG.Empty, inp, WP.Backward);
      var rf := AI.FFindMatchPlus(bodycodeB, body, plus_bc, str, ov, LAnc.Backward, cp,
                                  AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant),
                                  0, lookcdn).0;
      (rf.Some? <==> rb.Some?)
      && (rf.Some? ==>
            rb.Some?
            && LookNestBackTTop(body, crv, str, ov, PIV.CapIdsInLooks(body),
                                rb.value.1, rf.value, ncap, nlook, nquant)
            && LookNestBackTTopDeep(rer, body, crv, str, ov, PIV.CapIdsInLooks(body),
                                    rb.value.1, rf.value, ncap, nlook, nquant)
            && LookNestOkTTop(body, PIV.CapIdsInLooks(body), rb.value.1, rf.value)
            && CM.LookClkSetWithCp(rf.value.look_regs)
            && CM.LookCpSetWithClk(rf.value.look_regs)
            && CM.LookCpsLE(rf.value.look_regs, |str|))
  {
    var n := |str|;
    MIR.ReverseLen(str);
    var rstr := LC.Reverse(str);
    var mcpN: nat := n - cp;
    var mcp := MIR.Mirror(cp, n);
    assert mcp == mcpN as int;
    var ov' := MIR.MirrorView(ov, n);
    var cdn' := MIR.SwapAnchorsCdns(lookcdn);
    var reF := FST.FXR(body);
    var bcF := CP.compile_to_bytecode(reF);
    var crvF := FG.MirrorTables(crv);
    var S := PIV.CapIdsInLooks(body);
    var capture := AReg.init_regs(ncap);
    var look := AReg.init_regs(nlook);
    var quant := AReg.init_regs(nquant);

    // ---- statics of the flipped body + the flipped/mirrored tables ----
    FST.FXRStructural(body);
    var qmF, endl' := FK.FlipXRevStaticOkNested(body, ov', ncap, nlook, nquant);
    FG.NoPosLookbehindFXR(body);
    FG.LookUniqueFXR(body);
    FG.LookTablesOkFXR(body, crv);
    FG.LookIdsFXR(body);
    OE.LmOfDom(body);
    var qmB := AR.QMap(map[], OE.LmOf(body), ov);
    FST.FlipLooksMapTie(qmB, qmF);
    assert FO.FlipQmTie(qmB, qmF);
    assert forall l: int :: l in qmF.looks ==> l >= 0 && (l as nat) in LTB.LookIds(reF) && l < nlook by {
      forall l: int | l in qmF.looks
        ensures l >= 0 && (l as nat) in LTB.LookIds(reF) && l < nlook
      {
        assert l in qmB.looks;
        assert l in OE.LmOf(body);
        assert l >= 0 && (l as nat) in LTB.LookIds(body);
      }
    }
    NoPosImpliesL5ScopeV1(reF);             // FXR(body) has no positive lookbehinds
    GateStaticsFromTablesNested(qmF, reF, crvF, ncap, nlook, nquant);

    // ---- oracle for the flipped table: F3 on the body-restricted site table ----
    OE.LmapOkOfLmOf(body, qmB);
    FK.LmapOkEntriesMatchLmOf(body, qm);
    assert OE.OracleColsOk(rer, qmB, str) by {
      forall k: int | 0 <= k <= |str| ensures LL.OracleOkAt(rer, qmB, T.InputAt(str, k)) {
        FST.OracleOkAtSubmap(rer, qm, qmB, T.InputAt(str, k));
      }
    }
    FK.LmOfBodiesLBOk(body);
    assert FO.QmBodiesLBOk(qmB);
    assert |qmB.ov| == |str| + 1 && qmF.ov == MIR.MirrorView(qmB.ov, |str|);
    FO.MirrorOracleColsOk(rer, qmB, qmF, str);
    FO.ColsOkToSuffix(rer, qmF, rstr, mcpN);
    var inpF := PIV.InpOfCp(rstr, mcpN);
    assert inpF == T.InputAt(rstr, mcpN);
    assert LL.OracleOkSuffix(rer, qmF, inpF);

    // ---- the FORWARD carrier at the flipped body over the reversed string ----
    LookNestBackTFromBodyReplay(rer, qmF, R.Lookahead, reF, bcF, endl', 0, crvF, rstr, mcpN, ov',
                                cdn', plus_bc, ncap, nlook, nquant);
    var tF := LFU.ComputeTr(rer, [LS.Areg(T.Translate(reF))], inpF, LG.Empty, WP.Forward);
    var leafF := LT.FirstLeaf(tF, inpF);
    var rfFP := AI.FFindMatchPlus(bcF, reF, plus_bc, rstr, ov', LAnc.Forward, mcpN as int,
                                  capture, look, quant, 0, cdn').0;
    assert (rfFP.Some? <==> leafF.Some?);

    // ---- reduce both Plus runs to plain runs (no nulled plus in the fragment) ----
    var ctxF := AI.cp_context(mcp, rstr, LAnc.Forward);
    var initsF := AI.FInitState(bcF, mcp, capture, look, quant, 0, ctxF);
    var rfF := AI.FFindMatch(bcF, rstr, initsF, ov', LAnc.Forward, cdn').0;
    FST.NoNulledPlusFXR(body);
    M.NoTrueQuantStampNested(reF);
    assert M.VmQuantFinal(initsF) by {
      var th0 := AI.init_thread(capture, look, quant);
      assert M.QuantRegsFinal(th0) by {
        forall k ensures AI.get_idx(quant.a_cp, k) < 0 && AI.get_idx(quant.a_clk, k) >= -1 {
          if 0 <= k < |quant.a_cp| { assert quant.a_cp[k] == -1; }
          if 0 <= k < |quant.a_clk| { assert quant.a_clk[k] == -1; }
        }
      }
      forall t2 | t2 in initsF.active ensures M.QuantRegsFinal(t2) { assert t2 == th0; }
    }
    M.FFindMatchQuantFinalAny(bcF, rstr, initsF, ov', LAnc.Forward, cdn');
    var (fmF, ovF) := AI.FFindMatch(bcF, rstr, initsF, ov', LAnc.Forward, cdn');
    if fmF.Some? {
      M.FNulledPlusIdentity(reF, fmF.value.capture_regs, fmF.value.look_regs, fmF.value.quant_regs,
                            plus_bc, rstr, ovF, LAnc.Forward);
      assert AI.FReconstructPlus(fmF.value, reF, plus_bc, rstr, ovF, LAnc.Forward).0 == fmF.value;
    }
    assert rfFP == rfF;

    var ctxB := AI.cp_context(cp, str, LAnc.Backward);
    var initsB := AI.FInitState(bodycodeB, cp, capture, look, quant, 0, ctxB);
    var raB := AI.FFindMatch(bodycodeB, str, initsB, ov, LAnc.Backward, lookcdn).0;
    var rev := R.reverse_regex(body);
    M.ReverseNestedPackage(body);
    NR.NoNulledPlusReverse(body);
    M.NoTrueQuantStampNested(rev);
    assert M.VmQuantFinal(initsB) by {
      var th0 := AI.init_thread(capture, look, quant);
      assert M.QuantRegsFinal(th0) by {
        forall k ensures AI.get_idx(quant.a_cp, k) < 0 && AI.get_idx(quant.a_clk, k) >= -1 {
          if 0 <= k < |quant.a_cp| { assert quant.a_cp[k] == -1; }
          if 0 <= k < |quant.a_clk| { assert quant.a_clk[k] == -1; }
        }
      }
      forall t2 | t2 in initsB.active ensures M.QuantRegsFinal(t2) { assert t2 == th0; }
    }
    assert ctxB.nextchar == AI.get_char(str, cp - 1);
    M.FFindMatchQuantFinalAny(bodycodeB, str, initsB, ov, LAnc.Backward, lookcdn);
    var (fmB, ovB) := AI.FFindMatch(bodycodeB, str, initsB, ov, LAnc.Backward, lookcdn);
    if fmB.Some? {
      M.FNulledPlusIdentity(body, fmB.value.capture_regs, fmB.value.look_regs, fmB.value.quant_regs,
                            plus_bc, str, ovB, LAnc.Backward);
      assert AI.FReconstructPlus(fmB.value, body, plus_bc, str, ovB, LAnc.Backward).0 == fmB.value;
    }
    var rf := AI.FFindMatchPlus(bodycodeB, body, plus_bc, str, ov, LAnc.Backward, cp,
                                capture, look, quant, 0, lookcdn).0;
    assert rf == raB;

    // ---- F6 core: rfF == MirrorThread(raB) ----
    FG.BackFreshCoreNested(rer, qm, body, str, cp, ov, lookcdn, ncap, nlook, nquant, n);
    assert (raB.None? <==> rfF.None?);

    // ---- F2: the spec leaves mirror ----
    var inp := PIV.InpOfCp(str, cp);
    var t := LFU.ComputeTr(rer, [LS.Areg(T.Translate(body))], inp, LG.Empty, WP.Backward);
    var rb := LT.TreeRes(t, LG.Empty, inp, WP.Backward);
    FST.TranslateGroupOkLB(body);
    FST.TranslateNegBodiesGroupFree(body);
    FK.TranslateDefGroupsNoDupK(body);
    LBV.InpOfCpSwap(str, cp, n);
    assert inpF == SD.SwapInput(inp);
    MIR.ReverseLen(str[..cp]);
    assert |inp.pref| + |inp.next| == n;
    FST.TranslateFlipXRev(body);
    assert T.Translate(reF) == FM.FlipRevL(T.Translate(body));
    FD.BackBodyGmTieFlip(rer, T.Translate(body), inp, n);
    assert tF == LFU.ComputeTr(rer, [LS.Areg(FM.FlipRevL(T.Translate(body)))], SD.SwapInput(inp),
                               LG.Empty, WP.Forward);
    assert leafF == LT.TreeRes(tF, LG.Empty, inpF, WP.Forward);
    assert (rb.None? <==> leafF.None?);
    assert rb.Some? ==> TRM.GmInBounds(rb.value.1, n) && leafF.value.1 == TRM.MirrorGm(rb.value.1, n);

    // ---- None-iff ----
    assert (rf.Some? <==> rb.Some?);

    if rf.Some? {
      var th := rf.value;
      var gmt := rb.value.1;
      assert rfF.Some? && rfF.value == MIR.MirrorThread(th, n);
      assert leafF.Some? && leafF.value.1 == TRM.MirrorGm(gmt, n);
      var thF := MIR.MirrorThread(th, n);
      var gmtF := TRM.MirrorGm(gmt, n);
      FG.CapIdsInLooksFXR(body);
      assert PIV.CapIdsInLooks(reF) == S;
      // the forward carrier's conclusions, in transport form
      assert LookNestBackTTop(reF, crvF, rstr, ov', S, gmtF, thF, ncap, nlook, nquant);
      assert LookNestBackTTopDeep(rer, reF, crvF, rstr, ov', S, gmtF, thF, ncap, nlook, nquant);
      assert LookNestOkTTop(reF, S, gmtF, thF);

      // ---- look-bank invariants on the BACKWARD winner (fresh init banks) ----
      RL.AInitLaws(nlook);
      assert CM.VmLookClkSet(initsB) by {
        assert AI.init_thread(capture, look, quant).look_regs == look;
        forall l: int | AI.get_idx(look.a_cp, l) >= 0 ensures AI.get_idx(look.a_clk, l) >= 0 {
          if 0 <= l < |look.a_cp| { assert look.a_cp[l] == -1; }
        }
      }
      CM.FFindMatchLookClkSetB(bodycodeB, str, initsB, ov, LAnc.Backward, lookcdn);
      assert CM.LookClkSetWithCp(th.look_regs);
      assert CM.VmLookCpSet(initsB) by {
        forall l: int | AI.get_idx(look.a_clk, l) >= 0 ensures AI.get_idx(look.a_cp, l) >= 0 {
          if 0 <= l < |look.a_clk| { assert look.a_clk[l] == -1; }
        }
      }
      CM.FFindMatchLookCpSetB(bodycodeB, str, initsB, ov, LAnc.Backward, lookcdn);
      assert CM.LookCpSetWithClk(th.look_regs);
      assert CM.VmLookCpOk(initsB, |str|) by {
        forall l: int ensures AI.get_idx(look.a_cp, l) <= |str| {
          if 0 <= l < |look.a_cp| { assert look.a_cp[l] == -1; }
        }
      }
      CM.FFindMatchLookCpOkB(bodycodeB, str, initsB, ov, LAnc.Backward, lookcdn);
      assert CM.LookCpsLE(th.look_regs, |str|);

      // ---- presence carrier: congruence ----
      LookNestOkTTopFlip(body, S, gmt, th, n);

      // ---- key + deep carriers: per top lid, through T2a / F2 at the lid body ----
      NI.TopLookIdsIn(body);
      forall lid: nat | lid in NI.TopLookIds(body)
                        && (M.MatchedPosLA(crv, th.look_regs, lid as int)
                            && lid in LTB.LookIds(body)
                            && NI.LookPathDom(body, AI.get_idx(th.look_regs.a_clk, lid as int), th.quant_regs.a_clk, lid))
        ensures var rfl := M.FreshBodyMatch(crv, str, lid as int, th.look_regs, ov, ncap, nlook, nquant);
                rfl.Some? ==>
                  forall g: LG.GroupId ::
                    g in S && g in PIV.CapIds(NI.LookBodyOfRE(body, lid))
                    && g in PIV.GmOfLive(NI.LookBodyOfRE(body, lid), rfl.value.capture_regs,
                                         rfl.value.look_regs, rfl.value.quant_regs)
                    ==> g in gmt
      {
        LookNestBackTTopLidFlip(rer, qm, body, crv, str, ov, gmt, th, lid, ncap, nlook, nquant);
      }
      assert LookNestBackTTop(body, crv, str, ov, S, gmt, th, ncap, nlook, nquant);

      forall lid: nat | lid in NI.TopLookIds(body)
                        && (M.MatchedPosLA(crv, th.look_regs, lid as int)
                            && lid in LTB.LookIds(body)
                            && NI.LookPathDom(body, AI.get_idx(th.look_regs.a_clk, lid as int), th.quant_regs.a_clk, lid))
        ensures var lsub := SubFirstLeafAt(rer, crv, str, lid as int, th.look_regs);
                lsub.Some? ==>
                  forall g: LG.GroupId ::
                    g in S && g in PIV.CapIds(NI.LookBodyOfRE(body, lid)) ==>
                      (g in lsub.value ==> g in gmt && gmt[g] == lsub.value[g])
                      && (g in gmt ==> g in lsub.value)
      {
        LookNestBackTTopDeepLidFlip(rer, qm, body, crv, str, ov, gmt, th, lid, ncap, nlook, nquant);
      }
      assert LookNestBackTTopDeep(rer, body, crv, str, ov, S, gmt, th, ncap, nlook, nquant);
    }
  }

  /** (perf) The FORWARD BASE arm of `ForwardFindRec`, extracted so its assertions are
      checked in a small context (same treatment as `ForwardFindRecLB`).
      Mutually recursive with `ForwardFindRec` on `(|LookIds(host)|, arm)`. */
  lemma ForwardFindRecFwdBase(
    rer: LW.RegExpRecord, qm: AR.QMap, crv: CP.FCompiled, str: string, ast: R.regex, re: R.regex,
    ov: LOr.OracleView, res0: AReg.Regs, res1: AReg.Regs, res2: AReg.Regs,
    host: R.regex, A: nat, g: nat, ncap: int, nlook: int, nquant: int)
    // ---- whole-regex statics (fixed) ----
    requires T.TransWf(re) && NR.NestedFragmentRE(re) && NR.L5ScopeRE(re) && L5ScopeV1RE(re)
    requires NR.NoNulledPlusRE(re)   // §2.5b interim: all stamps false
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
    requires g !in PIV.CapIdsInLooks(host)
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
      NI.NoNulledPlusLookBody(re, A);
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

    // ==== BASE: g DIRECT in host ====
    SubFirstLeafDirectInFresh(rer, qm, crv, str, ov, A, res1, host, bodycode,
                              endlH, 0, g, ncap, nlook, nquant);
    var rfc := rfFresh.value.capture_regs;
    var rfl := rfFresh.value.look_regs;
    var rfq := rfFresh.value.quant_regs;
    assert g in PIV.GmOfLive(host, rfc, rfl, rfq)
           && lsubA.value[g] == PIV.GmOfLive(host, rfc, rfl, rfq)[g];
    // presence + dominance on the FRESH banks
    // (2026-08-25) nested host: the depth-1 `FreshBodyMatchCapWf` was unprovable here.
    M.LookBodyFactsL5(re, crv, A);              // NestedFragmentRE/CapUnique/QuantUnique(host)
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
    // res0 == rf at g's registers (start + end): the value lift at A
    PIV.CapIdsSplit(host);
    assert g in PIV.CapIdsOutsideLooks(host);
    assert CP.start_reg(g) in PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(host))
           && CP.end_reg(g) in PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(host));
    assert AI.get_idx(res0.a_clk, CP.start_reg(g)) == AI.get_idx(rfc.a_clk, CP.start_reg(g));
    assert AI.get_idx(res0.a_cp, CP.start_reg(g)) == AI.get_idx(rfc.a_cp, CP.start_reg(g));
    assert AI.get_idx(res0.a_clk, CP.end_reg(g)) == AI.get_idx(rfc.a_clk, CP.end_reg(g));
    assert AI.get_idx(res0.a_cp, CP.end_reg(g)) == AI.get_idx(rfc.a_cp, CP.end_reg(g));
    // dominance transported (Mx equality from the same transport)
    assert PIV.MxAtGidLk(host, res0.a_clk, res1.a_clk, res2.a_clk, -1, g)
        == PIV.MxAtGidLk(host, rfc.a_clk, rfl.a_clk, rfq.a_clk, -1, g);
    // the value: GmOfLive[g] == LiveRange(rf) == LiveRange(res0)
    NI.GmOfLiveKeepsPresentLkNested(host, rfFresh.value.capture_regs, rfl, rfq, g);
    assert PIV.GmOfLive(host, rfc, rfl, rfq)[g] == PIV.LiveRange(rfc.a_cp, rfc.a_clk, g);
    assert PIV.LiveRange(rfc.a_cp, rfc.a_clk, g) == PIV.LiveRange(res0.a_cp, res0.a_clk, g);
  }

}
