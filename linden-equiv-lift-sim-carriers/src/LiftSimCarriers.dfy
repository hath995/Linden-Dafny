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
  import NRR = LindenElkNulledReconRegs  // (G3a) the plus table
  import NRC = LindenElkNulledRecon      // (G3a) NoCdnPlusRE
  import RF = LindenElkReconFrame        // (G3a) CinBodiesLookFreeRE
  import TM = LindenElkTwoMachines       // (G3a) A6, TranslateCinOk

  // ==========================================================================
  // THE MAIN THEOREM, L3a: capturing positive lookaheads included. The
  // engine's full pipeline output IS the Linden tree-semantics answer, for
  // the whole lookbehind fragment with capturing forward lookaheads. This is
  // the (F) integration: the composite lockstep simulation delivers the leaf
  // ties, the endpoint assembly converts them into the reconstructed-register
  // denotation, and the existing extraction finishes.
  // ==========================================================================

  /** (G3a) The plain facts inside a row's `RowPlusOk`: what `GateStaticsFromTablesNested` and the
      lookbehind carrier ask of a row body. */
  lemma RowPlusFacts(body: R.regex, plus: seq<RB.code>, nlook: int)
    requires RowPlusOk(body, plus, nlook)
    ensures LTB.LookUnique(body) && NRR.PlusTableOk(body, plus)
    ensures forall l: nat :: l in LTB.LookIds(body) ==> l < nlook
    ensures M.LookBodiesPlusGateRE(body)
  {
    reveal RowPlusOk(); reveal M.RowLAStatics();
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
    requires PSM.StaticCoreNestedRE(qm, body, bodycode, endl)
    requires RowPlusOk(body, plus_bc, nlook)   // (G3a) the CIN fragment at this body (A6's premises)
    requires PSM.SizesOkRE(body, ncap, nlook, nquant)
    requires qm.ov == ov && !rer.multiline && !rer.ignoreCase
    requires cp <= |str|
    requires bodycode == CP.compile_to_bytecode(body)
    requires LL.OracleOkSuffix(rer, qm, PIV.InpOfCp(str, cp))
    requires |ov| == |str| + 1
    requires OE.OracleColsOk(rer, qm, str)                    // (L5 F7d) whole-string oracle correctness (backward keystone)
    requires GateStaticsOkNested(qm, body, crv, ncap, nlook, nquant)
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
            && CM.ThreadRegsWf(rf.value, ncap, nlook, nquant)   // (G3a) from A6
            && CM.LookClkSetWithCp(rf.value.look_regs)
            && CM.LookCpSetWithClk(rf.value.look_regs)
            && CM.LookCpsLE(rf.value.look_regs, |str|)
            // (G3a) the reconstruction keeps the VM winner's look bank (from A6)
            && TM.WinnerLookKept(bodycode, str, cp, ov, lookcdn, ncap, nlook, nquant, rf.value))
  {
    // (G3a) A6: machine A (the fresh plus replay, reconstructed) tied to machine B's winner.
    assert NR.NestedFragmentRE(body) && T.TransWf(body);
    assert NRC.NoCdnPlusRE(body) && NRR.PlusTableOk(body, plus_bc) && RF.CinBodiesLookFreeRE(body)
           && (forall l: nat :: l in LTB.LookIds(body) ==> l < nlook) by {
      reveal RowPlusOk(); reveal M.RowLAStatics();
    }
    TM.TranslateCinOk(body, PIV.CapIdsOutsideLooks(body));
    TM.TwoMachinesAt(rer, qm, body, bodycode, endl, ngroups, crv, str, cp, ov, lookcdn, plus_bc,
                     ncap, nlook, nquant);
  }


  /** (§2.2) The flip-reversal of a lookbehind-only body holds only lookaheads, so
      the negative-lookbehind scope condition is vacuous on it. */
  lemma NegBehindLBOnlyFXR(body: R.regex)
    requires FST.LBOnlyLooksRE(body)
    ensures EL.NegBehindLBOnlyRE(FST.FXR(body))
    decreases body
  {
    match body
    case Re_alt(r1, r2) => FG.FXRAlt(r1, r2); NegBehindLBOnlyFXR(r1); NegBehindLBOnlyFXR(r2);
    case Re_con(r1, r2) => FG.FXRCon(r1, r2); NegBehindLBOnlyFXR(r1); NegBehindLBOnlyFXR(r2);
    case Re_quant(nul, qid, q, r1) => FG.FXRQuant(nul, qid, q, r1); NegBehindLBOnlyFXR(r1);
    case Re_capture(cid, r1) => FG.FXRCapture(cid, r1); NegBehindLBOnlyFXR(r1);
    case Re_lookaround(lid, la, r1) =>
      FG.FXRLook(lid, la, r1); NegBehindLBOnlyFXR(r1);
      assert la.Lookbehind? || la.NegLookbehind?;
      assert !FR.FlipLkRE(la).NegLookbehind?;
    case _ =>
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
    requires T.TransWf(body) && NR.NestedFragmentRE(body)
    requires NR.NoNulledPlusRE(body)   // §2.5b interim: all stamps false
    requires PIV.CapUnique(body) && PIV.QuantUnique(body) && LTB.LookUnique(body)
    requires PSM.SizesOkRE(body, ncap, nlook, nquant)
    requires !rer.ignoreCase && !rer.multiline
    requires cp <= |str| && |ov| == |str| + 1
    requires bodycodeB == CP.compile_to_bytecode(R.reverse_regex(body))
    requires qm.ov == ov && AR.LmapOk(body, qm) && OE.OracleColsOk(rer, qm, str)
    requires LTB.LookTablesOk(body, crv) && |crv.f_look_types| == |crv.f_look_ast|
    requires forall l: nat :: l in LTB.LookIds(body) ==> l < nlook
    requires NRR.PlusTableOk(body, crv.f_plus_bc)   // (G3a) the flipped body's rows carry the plus table
    requires plus_bc == crv.f_plus_bc
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
    // (§2.5b/z3 4.14) recursive nullability predicates + the CIN disjunct's
    // triggered existential storm the solver; all uses here are opaque.
    hide NUL.NonNullableL, NUL.CINullableL, NUL.NoNulledPlusL, AR.NfaRepCinL;
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
    FG.LookUniqueFXR(body);
    FG.LookTablesOkFXR(body, crv);
    FG.LookIdsFXR(body);
    OE.LmOfDom(body);
    var qmB := AR.QMap(map[], OE.LmOf(body), ov, map[]);
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
    FST.NoNulledPlusFXR(body);
    M.PlusGateFromFull(reF);                // (G3a) the flipped body is nulled-plus-free: the weak gate holds
    // (G3a) the plus-row premises at the flipped body (`MirrorTables` keeps `f_plus_bc`)
    assert crvF.f_plus_bc == crv.f_plus_bc;
    PlusTableOkFXR(body, crv.f_plus_bc);
    assert forall l: nat :: l in LTB.LookIds(reF) ==> l < nlook;
    GateStaticsFromTablesNested(qmF, reF, crvF, ncap, nlook, nquant);
    assert RowPlusOk(reF, plus_bc, nlook) by {   // (G3a) the forward carrier's CIN premises, vacuous at reF
      M.NoNulledPlusCinFragment(reF);
      reveal RowPlusOk(); reveal M.RowLAStatics();
    }

    assert {:split_here} true;   // (gate B) W12 perf split (131 M unsplit -> 11 M worst)
    // ---- oracle for the flipped table: F3 on the body-restricted site table ----
    OE.LmapOkOfLmOf(body, qmB);
    FK.LmapOkEntriesMatchLmOf(body, qm);
    assert OE.OracleColsOk(rer, qmB, str) by {
      forall k: int | 0 <= k <= |str| ensures LL.OracleOkAt(rer, qmB, T.InputAt(str, k)) {
        FST.OracleOkAtSubmap(rer, qm, qmB, T.InputAt(str, k));
      }
    }
    KG.LmOfBodiesNoBackref(body);
    assert OG.QmBodiesNoBackref(qmB);
    assert |qmB.ov| == |str| + 1 && qmF.ov == MIR.MirrorView(qmB.ov, |str|);
    OG.MirrorOracleColsOkG(rer, qmB, qmF, str);
    FO.ColsOkToSuffix(rer, qmF, rstr, mcpN);
    var inpF := PIV.InpOfCp(rstr, mcpN);
    assert inpF == T.InputAt(rstr, mcpN);
    assert LL.OracleOkSuffix(rer, qmF, inpF);

    assert {:split_here} true;   // (gate B) W12 perf split (131 M unsplit -> 11 M worst)
    // ---- the FORWARD carrier at the flipped body over the reversed string ----
    assert PSM.StaticCoreNestedRE(qmF, reF, bcF, endl');
    LookNestBackTFromBodyReplay(rer, qmF, R.Lookahead, reF, bcF, endl', 0, crvF, rstr, mcpN, ov',
                                cdn', plus_bc, ncap, nlook, nquant);
    var tF := LFU.ComputeTr(rer, [LS.Areg(T.Translate(reF))], inpF, LG.Empty, WP.Forward);
    var leafF := LT.FirstLeaf(tF, inpF);
    var rfFP := AI.FFindMatchPlus(bcF, reF, plus_bc, rstr, ov', LAnc.Forward, mcpN as int,
                                  capture, look, quant, 0, cdn').0;
    assert (rfFP.Some? <==> leafF.Some?);

    assert {:split_here} true;   // (gate B) W12 perf split (131 M unsplit -> 11 M worst)
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

    assert {:split_here} true;   // (gate B) W12 perf split (131 M unsplit -> 11 M worst)
    // ---- F6 core: rfF == MirrorThread(raB) ----
    GG.BackFreshCoreNested(rer, qm, body, str, cp, ov, lookcdn, ncap, nlook, nquant, n);
    assert (raB.None? <==> rfF.None?);

    assert {:split_here} true;   // (gate B) W12 perf split (131 M unsplit -> 11 M worst)
    // ---- F2: the spec leaves mirror ----
    var inp := PIV.InpOfCp(str, cp);
    var t := LFU.ComputeTr(rer, [LS.Areg(T.Translate(body))], inp, LG.Empty, WP.Backward);
    var rb := LT.TreeRes(t, LG.Empty, inp, WP.Backward);
    KG.TranslateNoBackref(body);
    FK.TranslateDefGroupsNoDupK(body);
    LBV.InpOfCpSwap(str, cp, n);
    assert inpF == SD.SwapInput(inp);
    MIR.ReverseLen(str[..cp]);
    assert |inp.pref| + |inp.next| == n;
    FST.TranslateFlipXRev(body);
    assert T.Translate(reF) == FM.FlipRevL(T.Translate(body));
    NUL.TransNoNulledPlus(body);   // §2.5b interim: NoNulledPlusL(Translate(body))
    OG.BodyGmTieFlipG(rer, T.Translate(body), inp, n, WP.Backward);
    assert G.OppDir(WP.Backward) == WP.Forward;
    assert tF == LFU.ComputeTr(rer, [LS.Areg(FM.FlipRevL(T.Translate(body)))], SD.SwapInput(inp),
                               LG.Empty, WP.Forward);
    assert leafF == LT.TreeRes(tF, LG.Empty, inpF, WP.Forward);
    assert (rb.None? <==> leafF.None?);
    assert rb.Some? ==> TRM.GmInBounds(rb.value.1, n) && leafF.value.1 == TRM.MirrorGm(rb.value.1, n);

    assert {:split_here} true;   // (gate B) W12 perf split (131 M unsplit -> 11 M worst)
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

      assert {:split_here} true;   // (gate B) W12 perf split
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

      assert {:split_here} true;   // (gate B) W12 perf split
      // ---- presence carrier: congruence ----
      LookNestOkTTopFlip(body, S, gmt, th, n);

      assert {:split_here} true;   // (gate B) W12 perf split
      // ---- key + deep carriers: per top lid, through T2a / F2 at the lid body ----
      NI.TopLookIdsIn(body);
      forall lid: nat | lid in NI.TopLookIds(body)
                        && (M.MatchedPosLA(crv, th.look_regs, lid as int)
                            && lid in LTB.LookIds(body)
                            && NI.LookPathDom(body, AI.get_idx(th.look_regs.a_clk, lid as int), th.quant_regs.a_clk, lid))
        ensures var rfl := M.FreshBodyMatchPlus(crv, str, lid as int, th.look_regs, ov, ncap, nlook, nquant);
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
    requires T.TransWf(re) && NR.NestedFragmentRE(re)
    requires M.LookBodiesPlusGateRE(re)   // (G3a) the weak gate
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
    requires !crv.f_look_types[A as int].Lookbehind?
    requires g !in PIV.CapIdsInLooks(host)
    decreases |LTB.LookIds(host)|, 0
  {
    hide M.LookBodiesPlusGateRE;   // (G3a) a fact here, never unfolded (recursive: batch memory)
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
    var laA: R.lookaround, bA: R.regex := GateStaticPick(qm, re, crv, A as int, ncap, nlook, nquant);   // (G3a)
    NI.LookBodyOfTablesTie(re, crv, A);
    var laT: R.lookaround :| LTB.LookEntryOk(crv, A as int, laT, NI.LookBodyOfRE(re, A));
    assert bA == host by { assert crv.f_look_ast[A as int] == bA == host; }
    assert host == M.VBody(crv, A as int);
    var endlH: nat := |bodycode| - 1;
    assert PSM.StaticCoreNestedRE(qm, host, bodycode, endlH);
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
                       qm.ov, qm.bodies);
    assert AR.QmapOk(host, qmB) by { QmapOkLooksIrrel(host, qm, qmB); }
    assert AR.LmapOk(host, qmB) by { LmapOkRestrict(host, qm, qmB); }
    assert PSM.StaticCoreNestedRE(qmB, host, bodycode, endlH) by {
      assert PSM.StaticCoreNestedRE(qm, host, bodycode, endlH);
    }
    assert LL.OracleOkSuffix(rer, qmB, inpA) by {
      assert LL.OracleOkSuffix(rer, qm, inpA);
      OracleOkSuffixRestrict(rer, qm, qmB, inpA);
    }
    assert GateStaticsOkNested(qmB, host, crv, ncap, nlook, nquant) by {
      RowPlusFacts(host, crv.f_plus_bc, nlook);   // (G3a) the row's plus facts and the gate at host
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

    // (G3a) rf_A IS the fresh plus replay at A (the row replays `FFindMatchPlus` from init banks)
    var rfFresh := M.FreshBodyMatchPlus(crv, str, A as int, res1, ov, ncap, nlook, nquant);
    assert rfFresh == rfP by {
      assert AI.capture_direction(crv.f_look_types[A as int]) == LAnc.Forward;
      assert CP.capture_regex(crv.f_look_types[A as int], M.VBody(crv, A as int)) == host;
      reveal M.FreshBodyMatchPlus();
    }
    assert rfA == rfFresh.value;
    assert rfFresh.Some?;

    // the FLookLoop value/quant lifts at owner == A
    assert CM.RegsAgreeInside(res0, rfFresh.value.capture_regs,
                              PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(host))) by {
      assert 1 <= A as int <= maxlook && M.MatchedPosLA(crv, res1, A as int);
      assert M.VBody(crv, A as int) == host;
    }
    assert M.QuantClkAgreeInside(res2, rfFresh.value.quant_regs, M.QIdsOuter(host)) by {
      assert 1 <= A as int <= maxlook && M.MatchedPosLA(crv, res1, A as int);
    }

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
    LookBodyFactsKB(re, crv, A);              // (gate B) scope-free row facts
    assert CM.ThreadRegsWf(rfA, ncap, nlook, nquant);   // (G3a) the carrier (A6) gives the winner's wf
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
    // transport onto the reconstructed banks (no-look path; quant clocks from the value lift)
    assert forall c: nat :: c in PIV.CapIdsOutsideLooks(host) ==>
                              AI.get_idx(res0.a_clk, CP.start_reg(c)) == AI.get_idx(rfc.a_clk, CP.start_reg(c))
    by {
      forall c: nat | c in PIV.CapIdsOutsideLooks(host)
        ensures AI.get_idx(res0.a_clk, CP.start_reg(c)) == AI.get_idx(rfc.a_clk, CP.start_reg(c))
      {
        assert CP.start_reg(c) in PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(host));
      }
    }
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
