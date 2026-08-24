// L5 CAPTURES — BRICK F4 (MainTheorem-independent half): statics for the
// FLIP-reversed body `re' := FlipRE(XRev(body))`.
//
// The forward keystone applied at `re'` needs `StaticOkNestedRE(qm'', re',
// compile(re'), endl')` + `SizesOkRE` + `NegLooksLookFreeRE(re')`, a looks-map
// `qm''` that is the FLIP of the original's (so F3 applies), and the
// `GmOfLive` readout to be flip-invariant. Everything here is structural:
//  - `XRevIsRevRENested`: `SwapAnchorsRegex o reverse_regex == SD.RevRE`,
//    UNCONDITIONALLY (the two anchor swaps are the same map) — so every
//    RevRE-preservation lemma (CapUnique/QuantUnique/max_*/TransWf/
//    TranslateRevRE) transfers to XRev at any depth.
//  - `TranslateFlipXRev`: `Translate(FlipRE(XRev(r))) == FlipRevL(Translate(r))`.
//  - Flip-preservation family (fragment, uniqueness, sizes, look-freeness).
//  - `FlipXRevCompileFacts`: NfaRepRE/Accept/length/StutterTame at `re'`
//    (instantiating the nested compile correspondence at `re'` directly).
//  - `FlipLooksMap`/`LmapOkFlipXRev`: the flipped table serves `re'`.
//  - `GmOfLiveFlip`: the engine readout is flip-blind (the FilterReset chain).
//  - The v1 scope predicate `LBOnlyLooksRE` + its Translate bridges.

include "FlipOracle.dfy"
include "BackGmMirror.dfy"
include "OracleMirrorV.dfy"

/** F4 (M-independent): statics of the flip-reversed body. */
module LindenElkFlipStatics {
  import opened Std.Wrappers
  import LW = WarblreRegExpRecord
  import WP = WarblrePrimitives
  import LC = Chars
  import LG = Groups
  import L = Regex
  import LS = Semantics
  import LT = Tree
  import FU = FunctionalUtils
  import SD = LindenSpanDuality
  import CD = LindenCloseDisc
  import R = RegElkRegex
  import RB = Bytecode
  import CP = Compiler
  import AI = ArrayInterp
  import AReg = Array_Regs
  import LOr = Oracle
  import T = LindenElkTranslate
  import NR = LindenElkNfaRep
  import PIV = LindenElkPikeInv
  import OBu = LindenElkOracleBuild
  import MIR = LindenElkMirror
  import AR = LindenElkActionsRep
  import LL = LindenElkLookLeaves
  import OS = LindenElkOracleSpec
  import LBV = LindenLookBehindValue
  import BGM = LindenBackGmMirror
  import OMV = LindenElkOracleMirrorV
  import FR = LindenElkFlipRev
  import FM = LindenElkFlipMirror
  import FD = LindenElkFlipDisc
  import FO = LindenElkFlipOracle

  /** The engine-side reversal (`XRev`), spelled out. */
  function XRV(r: R.regex): R.regex { OBu.SwapAnchorsRegex(R.reverse_regex(r)) }

  /** The flip-reversed body. */
  function FXR(r: R.regex): R.regex { FR.FlipRE(XRV(r)) }

  // ===========================================================================
  // XRev IS RevRE (no fragment premise)
  // ===========================================================================

  /** The engine reversal + anchor swap is exactly SpanDuality's recursive
      `RevRE`, at ANY depth: both keep lids and kinds, both reverse `Re_con`,
      and the two anchor swaps are the same map. */
  lemma XRevIsRevRENested(r: R.regex)
    ensures XRV(r) == SD.RevRE(r)
    decreases r
  {
    match r
    case Re_anchor(a) =>
      assert MIR.SwapAnchor(a) == SD.SwapAnchorRE(a);
    case Re_alt(r1, r2) => XRevIsRevRENested(r1); XRevIsRevRENested(r2);
    case Re_con(r1, r2) => XRevIsRevRENested(r1); XRevIsRevRENested(r2);
    case Re_quant(_, _, _, r1) => XRevIsRevRENested(r1);
    case Re_capture(_, r1) => XRevIsRevRENested(r1);
    case Re_lookaround(_, _, r1) => XRevIsRevRENested(r1);
    case _ =>
  }

  /** The translation chain: `Translate(FXR(r)) == FlipRevL(Translate(r))`. */
  lemma TranslateFlipXRev(r: R.regex)
    requires T.TransWf(r)
    ensures T.TransWf(XRV(r)) && T.TransWf(FXR(r))
    ensures T.Translate(FXR(r)) == FM.FlipRevL(T.Translate(r))
  {
    XRevIsRevRENested(r);
    SD.TranslateRevRE(r);
    FR.TranslateFlip(SD.RevRE(r));
  }

  // ===========================================================================
  // Flip-preservation family (kinds carry no ids, no captures, no chars)
  // ===========================================================================

  lemma FlipLookFree(r: R.regex)
    ensures NR.LookFreeRE(FR.FlipRE(r)) == NR.LookFreeRE(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => FlipLookFree(r1); FlipLookFree(r2);
    case Re_con(r1, r2) => FlipLookFree(r1); FlipLookFree(r2);
    case Re_quant(_, _, _, r1) => FlipLookFree(r1);
    case Re_capture(_, r1) => FlipLookFree(r1);
    case Re_lookaround(_, _, r1) => FlipLookFree(r1);
    case _ =>
  }

  lemma FlipCaptureFree(r: R.regex)
    ensures NR.CaptureFreeRE(FR.FlipRE(r)) == NR.CaptureFreeRE(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => FlipCaptureFree(r1); FlipCaptureFree(r2);
    case Re_con(r1, r2) => FlipCaptureFree(r1); FlipCaptureFree(r2);
    case Re_quant(_, _, _, r1) => FlipCaptureFree(r1);
    case Re_capture(_, r1) => FlipCaptureFree(r1);
    case Re_lookaround(_, _, r1) => FlipCaptureFree(r1);
    case _ =>
  }

  /** Nullability never looks at a look kind. */
  lemma FlipNullable(r: R.regex)
    ensures R.nullable(FR.FlipRE(r)) == R.nullable(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => FlipNullable(r1); FlipNullable(r2);
    case Re_con(r1, r2) => FlipNullable(r1); FlipNullable(r2);
    case Re_quant(_, _, _, r1) => FlipNullable(r1);
    case Re_capture(_, r1) => FlipNullable(r1);
    case Re_lookaround(_, _, r1) => FlipNullable(r1);
    case _ =>
  }

  /** The nested fragment is positivity-keyed, hence flip-invariant. */
  lemma FlipNestedFragment(r: R.regex)
    ensures NR.NestedFragmentRE(FR.FlipRE(r)) == NR.NestedFragmentRE(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => FlipNestedFragment(r1); FlipNestedFragment(r2);
    case Re_con(r1, r2) => FlipNestedFragment(r1); FlipNestedFragment(r2);
    case Re_quant(_, _, _, r1) => FlipNullable(r1); FlipNestedFragment(r1);
    case Re_capture(_, r1) => FlipNestedFragment(r1);
    case Re_lookaround(_, la, r1) =>
      FlipCaptureFree(r1); FlipNestedFragment(r1);
      assert (FR.FlipLkRE(la).Lookahead? || FR.FlipLkRE(la).Lookbehind?)
          == (la.Lookahead? || la.Lookbehind?);
    case _ =>
  }

  lemma FlipNegLooksLookFree(r: R.regex)
    ensures NR.NegLooksLookFreeRE(FR.FlipRE(r)) == NR.NegLooksLookFreeRE(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => FlipNegLooksLookFree(r1); FlipNegLooksLookFree(r2);
    case Re_con(r1, r2) => FlipNegLooksLookFree(r1); FlipNegLooksLookFree(r2);
    case Re_quant(_, _, _, r1) => FlipNegLooksLookFree(r1);
    case Re_capture(_, r1) => FlipNegLooksLookFree(r1);
    case Re_lookaround(_, la, r1) =>
      FlipLookFree(r1); FlipNegLooksLookFree(r1);
      assert (FR.FlipLkRE(la).NegLookahead? || FR.FlipLkRE(la).NegLookbehind?)
          == (la.NegLookahead? || la.NegLookbehind?);
    case _ =>
  }

  lemma FlipCapIds(r: R.regex)
    ensures PIV.CapIds(FR.FlipRE(r)) == PIV.CapIds(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => FlipCapIds(r1); FlipCapIds(r2);
    case Re_con(r1, r2) => FlipCapIds(r1); FlipCapIds(r2);
    case Re_quant(_, _, _, r1) => FlipCapIds(r1);
    case Re_capture(_, r1) => FlipCapIds(r1);
    case Re_lookaround(_, _, r1) => FlipCapIds(r1);
    case _ =>
  }

  lemma FlipQuantIds(r: R.regex)
    ensures PIV.QuantIds(FR.FlipRE(r)) == PIV.QuantIds(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => FlipQuantIds(r1); FlipQuantIds(r2);
    case Re_con(r1, r2) => FlipQuantIds(r1); FlipQuantIds(r2);
    case Re_quant(_, _, _, r1) => FlipQuantIds(r1);
    case Re_capture(_, r1) => FlipQuantIds(r1);
    case Re_lookaround(_, _, r1) => FlipQuantIds(r1);
    case _ =>
  }

  lemma FlipCapUnique(r: R.regex)
    ensures PIV.CapUnique(FR.FlipRE(r)) == PIV.CapUnique(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => FlipCapUnique(r1); FlipCapUnique(r2); FlipCapIds(r1); FlipCapIds(r2);
    case Re_con(r1, r2) => FlipCapUnique(r1); FlipCapUnique(r2); FlipCapIds(r1); FlipCapIds(r2);
    case Re_quant(_, _, _, r1) => FlipCapUnique(r1);
    case Re_capture(_, r1) => FlipCapUnique(r1); FlipCapIds(r1);
    case Re_lookaround(_, _, r1) => FlipCapUnique(r1);
    case _ =>
  }

  lemma FlipQuantUnique(r: R.regex)
    ensures PIV.QuantUnique(FR.FlipRE(r)) == PIV.QuantUnique(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => FlipQuantUnique(r1); FlipQuantUnique(r2); FlipQuantIds(r1); FlipQuantIds(r2);
    case Re_con(r1, r2) => FlipQuantUnique(r1); FlipQuantUnique(r2); FlipQuantIds(r1); FlipQuantIds(r2);
    case Re_quant(_, _, _, r1) => FlipQuantUnique(r1); FlipQuantIds(r1);
    case Re_capture(_, r1) => FlipQuantUnique(r1);
    case Re_lookaround(_, _, r1) => FlipQuantUnique(r1);
    case _ =>
  }

  lemma FlipMaxGroup(r: R.regex)
    ensures R.max_group(FR.FlipRE(r)) == R.max_group(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => FlipMaxGroup(r1); FlipMaxGroup(r2);
    case Re_con(r1, r2) => FlipMaxGroup(r1); FlipMaxGroup(r2);
    case Re_quant(_, _, _, r1) => FlipMaxGroup(r1);
    case Re_capture(_, r1) => FlipMaxGroup(r1);
    case Re_lookaround(_, _, r1) => FlipMaxGroup(r1);
    case _ =>
  }

  lemma FlipMaxQuant(r: R.regex)
    ensures R.max_quant(FR.FlipRE(r)) == R.max_quant(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => FlipMaxQuant(r1); FlipMaxQuant(r2);
    case Re_con(r1, r2) => FlipMaxQuant(r1); FlipMaxQuant(r2);
    case Re_quant(_, _, _, r1) => FlipMaxQuant(r1);
    case Re_capture(_, r1) => FlipMaxQuant(r1);
    case Re_lookaround(_, _, r1) => FlipMaxQuant(r1);
    case _ =>
  }

  // ===========================================================================
  // XRev-preservation family (structural over the composition)
  // ===========================================================================

  lemma XRVLookFree(r: R.regex)
    ensures NR.LookFreeRE(XRV(r)) == NR.LookFreeRE(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => XRVLookFree(r1); XRVLookFree(r2);
    case Re_con(r1, r2) => XRVLookFree(r1); XRVLookFree(r2);
    case Re_quant(_, _, _, r1) => XRVLookFree(r1);
    case Re_capture(_, r1) => XRVLookFree(r1);
    case Re_lookaround(_, _, r1) => XRVLookFree(r1);
    case _ =>
  }

  lemma XRVCaptureFree(r: R.regex)
    ensures NR.CaptureFreeRE(XRV(r)) == NR.CaptureFreeRE(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => XRVCaptureFree(r1); XRVCaptureFree(r2);
    case Re_con(r1, r2) => XRVCaptureFree(r1); XRVCaptureFree(r2);
    case Re_quant(_, _, _, r1) => XRVCaptureFree(r1);
    case Re_capture(_, r1) => XRVCaptureFree(r1);
    case Re_lookaround(_, _, r1) => XRVCaptureFree(r1);
    case _ =>
  }

  lemma XRVNestedFragment(r: R.regex)
    ensures NR.NestedFragmentRE(XRV(r)) == NR.NestedFragmentRE(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => XRVNestedFragment(r1); XRVNestedFragment(r2);
    case Re_con(r1, r2) => XRVNestedFragment(r1); XRVNestedFragment(r2);
    case Re_quant(_, _, _, r1) => OMV.XRevNullable(r1); XRVNestedFragment(r1);
    case Re_capture(_, r1) => XRVNestedFragment(r1);
    case Re_lookaround(_, _, r1) => XRVCaptureFree(r1); XRVNestedFragment(r1);
    case _ =>
  }

  lemma XRVNegLooksLookFree(r: R.regex)
    ensures NR.NegLooksLookFreeRE(XRV(r)) == NR.NegLooksLookFreeRE(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => XRVNegLooksLookFree(r1); XRVNegLooksLookFree(r2);
    case Re_con(r1, r2) => XRVNegLooksLookFree(r1); XRVNegLooksLookFree(r2);
    case Re_quant(_, _, _, r1) => XRVNegLooksLookFree(r1);
    case Re_capture(_, r1) => XRVNegLooksLookFree(r1);
    case Re_lookaround(_, _, r1) => XRVLookFree(r1); XRVNegLooksLookFree(r1);
    case _ =>
  }

  /** The structural statics of the flip-reversed body, from the body's. */
  lemma FXRStructural(body: R.regex)
    requires T.TransWf(body) && NR.NestedFragmentRE(body) && NR.NegLooksLookFreeRE(body)
    requires PIV.CapUnique(body) && PIV.QuantUnique(body)
    ensures T.TransWf(FXR(body)) && NR.NestedFragmentRE(FXR(body))
    ensures NR.NegLooksLookFreeRE(FXR(body))
    ensures PIV.CapUnique(FXR(body)) && PIV.QuantUnique(FXR(body))
    ensures R.max_group(FXR(body)) == R.max_group(body)
    ensures R.max_quant(FXR(body)) == R.max_quant(body)
  {
    XRevIsRevRENested(body);
    SD.RevRETransWf(body);
    FR.FlipTransWf(XRV(body));
    XRVNestedFragment(body); FlipNestedFragment(XRV(body));
    XRVNegLooksLookFree(body); FlipNegLooksLookFree(XRV(body));
    LBV.CapUniqueRevRE(body); FlipCapUnique(XRV(body));
    LBV.QuantUniqueRevRE(body); FlipQuantUnique(XRV(body));
    LBV.MaxGroupRevRE(body); FlipMaxGroup(XRV(body));
    LBV.MaxQuantRevRE(body); FlipMaxQuant(XRV(body));
  }

  // ===========================================================================
  // Compile facts at the flipped body
  // ===========================================================================

  /** NfaRepRE / Accept / length / StutterTame of `compile(FXR(body))` — the
      nested compile correspondence instantiated AT `re'`, plus the Jmp-tameness
      argument (`CompileStutterTameRENested`'s proof, which is LiftSim-local). */
  lemma FXRCompileFacts(body: R.regex) returns (endl: nat)
    requires NR.NestedFragmentRE(FXR(body))
    ensures var code := CP.compile_to_bytecode(FXR(body));
            && NR.NfaRepRE(FXR(body), code, 0, endl)
            && NR.GetPcRE(code, endl) == Some(RB.Accept)
            && |code| == endl + 1
            && PIV.StutterTameRE(code)
  {
    var re := FXR(body);
    var code := CP.compile_to_bytecode(re);
    NR.CompileToBytecodeRepNested(re);
    var next := CP.compile(re, 0, CP.Progress).1;
    endl := next as nat;
    forall pc: nat | pc < |code|
      ensures match NR.GetPcRE(code, pc)
              case Some(Jmp(nxt)) =>
                pc < nxt
                || (nxt >= 0 && NR.GetPcRE(code, nxt as nat).Some? && NR.GetPcRE(code, nxt as nat).value.Fork?)
              case _ => true
    {
      match NR.GetPcRE(code, pc)
      case Some(Jmp(nn)) =>
        assert pc < endl;
        PIV.CompileJumpsRE(re, code, 0, endl, pc, nn);
      case _ =>
    }
  }

  // ===========================================================================
  // The flipped looks-map serves the flipped regex
  // ===========================================================================

  /** Flip every entry of a looks-table pointwise (same lids). */
  ghost function FlipLooksMap(m: map<int, (L.Lookaround, L.Regex)>): map<int, (L.Lookaround, L.Regex)> {
    map lid | lid in m :: (FR.FlipLk(m[lid].0), FM.FlipRevL(m[lid].1))
  }

  lemma FlipLooksMapTie(qm: AR.QMap, qm2: AR.QMap)
    requires qm2.looks == FlipLooksMap(qm.looks)
    ensures FO.FlipQmTie(qm, qm2)
  {}

  /** A table correct for `body` flips to a table correct for `FXR(body)`:
      pure conjunction recursion (order-agnostic, so the `Re_con` swap is
      harmless; extra entries tolerated). */
  lemma LmapOkFlipXRev(body: R.regex, qm: AR.QMap, qm2: AR.QMap)
    requires T.TransWf(body)
    requires AR.LmapOk(body, qm)
    requires qm2.looks == FlipLooksMap(qm.looks)
    ensures T.TransWf(FXR(body))
    ensures AR.LmapOk(FXR(body), qm2)
    decreases body
  {
    TranslateFlipXRev(body);
    match body
    case Re_alt(r1, r2) =>
      LmapOkFlipXRev(r1, qm, qm2); LmapOkFlipXRev(r2, qm, qm2);
    case Re_con(r1, r2) =>
      LmapOkFlipXRev(r1, qm, qm2); LmapOkFlipXRev(r2, qm, qm2);
      assert FXR(body) == R.Re_con(FXR(r2), FXR(r1));
    case Re_quant(_, _, _, r1) => LmapOkFlipXRev(r1, qm, qm2);
    case Re_capture(_, r1) => LmapOkFlipXRev(r1, qm, qm2);
    case Re_lookaround(lid, la, r1) =>
      assert FXR(body) == R.Re_lookaround(lid, FR.FlipLkRE(la), FXR(r1));
      assert lid in qm.looks && qm.looks[lid] == (T.TrLookaround(la), T.Translate(r1));
      FR.FlipLkRELaws(la);
      TranslateFlipXRev(r1);
      assert qm2.looks[lid] == (T.TrLookaround(FR.FlipLkRE(la)), T.Translate(FXR(r1)));
      LmapOkFlipXRev(r1, qm, qm2);
    case _ =>
  }

  /** Restricting a table to a pointwise sub-table (same view) keeps column
      correctness — the way the site's whole-regex table feeds the body's. */
  lemma OracleOkAtSubmap(rer: LW.RegExpRecord, qm: AR.QMap, qmB: AR.QMap, inp: LC.Input)
    requires qmB.ov == qm.ov
    requires forall lid: int :: lid in qmB.looks ==> lid in qm.looks && qm.looks[lid] == qmB.looks[lid]
    requires LL.OracleOkAt(rer, qm, inp)
    ensures LL.OracleOkAt(rer, qmB, inp)
  {}

  // ===========================================================================
  // The engine readout is flip-blind
  // ===========================================================================

  lemma ZeroSetAllFlip(r: R.regex)
    ensures BGM.ZeroSetAll(FR.FlipRE(r)) == BGM.ZeroSetAll(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => ZeroSetAllFlip(r1); ZeroSetAllFlip(r2);
    case Re_con(r1, r2) => ZeroSetAllFlip(r1); ZeroSetAllFlip(r2);
    case Re_quant(_, _, _, r1) => ZeroSetAllFlip(r1);
    case Re_capture(_, r1) => ZeroSetAllFlip(r1);
    case Re_lookaround(_, _, r1) => ZeroSetAllFlip(r1);
    case _ =>
  }

  lemma ZeroSetCapFlip(r: R.regex, cc: seq<int>, lc: seq<int>, qc: seq<int>, mc: int)
    ensures BGM.ZeroSetCap(FR.FlipRE(r), cc, lc, qc, mc) == BGM.ZeroSetCap(r, cc, lc, qc, mc)
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      ZeroSetCapFlip(r1, cc, lc, qc, mc); ZeroSetCapFlip(r2, cc, lc, qc, mc);
    case Re_con(r1, r2) =>
      ZeroSetCapFlip(r1, cc, lc, qc, mc); ZeroSetCapFlip(r2, cc, lc, qc, mc);
    case Re_quant(nul, qid, quant, r1) =>
      var quant_val := AI.get_idx(qc, qid);
      if quant_val < mc { ZeroSetAllFlip(r1); }
      else { ZeroSetCapFlip(r1, cc, lc, qc, quant_val); }
    case Re_capture(cid, r1) =>
      var start := AI.get_idx(cc, CP.start_reg(cid));
      if start < 0 { ZeroSetAllFlip(r1); }
      else if start < mc { ZeroSetAllFlip(r1); }
      else { ZeroSetCapFlip(r1, cc, lc, qc, mc); }
    case Re_lookaround(lid, la, r1) =>
      var look_val := AI.get_idx(lc, lid);
      if look_val < 0 { ZeroSetAllFlip(r1); }
      else if look_val < mc { ZeroSetAllFlip(r1); }
      else { ZeroSetCapFlip(r1, cc, lc, qc, -1); }
    case _ =>
  }

  lemma FilterCaptureFlip(r: R.regex, a: seq<int>, cc: seq<int>, lc: seq<int>, qc: seq<int>, mc: int)
    ensures AI.filter_capture(FR.FlipRE(r), a, cc, lc, qc, mc) == AI.filter_capture(r, a, cc, lc, qc, mc)
  {
    BGM.FilterCaptureZero(FR.FlipRE(r), a, cc, lc, qc, mc);
    BGM.FilterCaptureZero(r, a, cc, lc, qc, mc);
    ZeroSetCapFlip(r, cc, lc, qc, mc);
  }

  lemma FilterResetFlip(r: R.regex, cap: AReg.Regs, look: AReg.Regs, quant: AReg.Regs, mc: int)
    ensures AI.filter_reset(FR.FlipRE(r), cap, look, quant, mc)
         == AI.filter_reset(r, cap, look, quant, mc)
  {
    FilterCaptureFlip(r, AReg.as_arrays(cap).0, AReg.as_arrays(cap).1,
                      AReg.as_arrays(look).1, AReg.as_arrays(quant).1, mc);
  }

  /** `GmOfLive` is flip-blind (sibling of `GmOfLiveXRev`). */
  lemma GmOfLiveFlip(body: R.regex, cap: AReg.Regs, look: AReg.Regs, quant: AReg.Regs)
    ensures PIV.GmOfLive(FR.FlipRE(body), cap, look, quant)
         == PIV.GmOfLive(body, cap, look, quant)
  {
    FilterResetFlip(body, cap, look, quant, -1);
  }

  /** The composite readout invariance: `GmOfLive(FXR(body), X) == GmOfLive(body, X)`. */
  lemma GmOfLiveFXR(body: R.regex, cap: AReg.Regs, look: AReg.Regs, quant: AReg.Regs)
    ensures PIV.GmOfLive(FXR(body), cap, look, quant) == PIV.GmOfLive(body, cap, look, quant)
  {
    GmOfLiveFlip(XRV(body), cap, look, quant);
    BGM.GmOfLiveXRev(body, cap, look, quant);
  }

  // ===========================================================================
  // The v1 scope: lookbehind-only nesting, and its Translate bridges
  // ===========================================================================

  /** Every lookaround in `r` (at any depth) is lookbehind-flavoured. */
  predicate LBOnlyLooksRE(r: R.regex)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => LBOnlyLooksRE(r1) && LBOnlyLooksRE(r2)
    case Re_con(r1, r2) => LBOnlyLooksRE(r1) && LBOnlyLooksRE(r2)
    case Re_quant(_, _, _, r1) => LBOnlyLooksRE(r1)
    case Re_capture(_, r1) => LBOnlyLooksRE(r1)
    case Re_lookaround(_, la, r1) => (la.Lookbehind? || la.NegLookbehind?) && LBOnlyLooksRE(r1)
    case _ => true
  }

  /** A lookbehind-only body translates into `GroupOkLB` (RegElk has no
      backreference node, so the only `GroupOkLB` obstruction is a lookahead). */
  lemma TranslateGroupOkLB(r: R.regex)
    requires T.TransWf(r) && LBOnlyLooksRE(r)
    ensures SD.GroupOkLB(T.Translate(r))
    decreases r
  {
    match r
    case Re_alt(r1, r2) => TranslateGroupOkLB(r1); TranslateGroupOkLB(r2);
    case Re_con(r1, r2) => TranslateGroupOkLB(r1); TranslateGroupOkLB(r2);
    case Re_quant(_, _, _, r1) => TranslateGroupOkLB(r1);
    case Re_capture(_, r1) => TranslateGroupOkLB(r1);
    case Re_lookaround(_, la, r1) => TranslateGroupOkLB(r1);
    case _ =>
  }

  /** The fragment's negative arm (capture-free + look-free negative bodies)
      translates into group-free negative bodies. */
  lemma TranslateNegBodiesGroupFree(r: R.regex)
    requires T.TransWf(r) && NR.NestedFragmentRE(r) && NR.NegLooksLookFreeRE(r)
    ensures FD.NegBodiesGroupFree(T.Translate(r))
    decreases r
  {
    match r
    case Re_alt(r1, r2) => TranslateNegBodiesGroupFree(r1); TranslateNegBodiesGroupFree(r2);
    case Re_con(r1, r2) => TranslateNegBodiesGroupFree(r1); TranslateNegBodiesGroupFree(r2);
    case Re_quant(_, _, _, r1) => TranslateNegBodiesGroupFree(r1);
    case Re_capture(_, r1) => TranslateNegBodiesGroupFree(r1);
    case Re_lookaround(_, la, r1) =>
      if la.Lookahead? || la.Lookbehind? {
        TranslateNegBodiesGroupFree(r1);
      } else {
        assert NR.CaptureFreeRE(r1) && NR.LookFreeRE(r1);
        OS.TranslateGroupFree(r1);
      }
    case _ =>
  }

  /** `LkBodyGroups` ignores look kinds. */
  lemma LkBodyGroupsFlipL(r: L.Regex)
    ensures LL.LkBodyGroups(FR.FlipL(r)) == LL.LkBodyGroups(r)
    decreases r
  {
    match r
    case Disjunction(r1, r2) => LkBodyGroupsFlipL(r1); LkBodyGroupsFlipL(r2);
    case Sequence(r1, r2) => LkBodyGroupsFlipL(r1); LkBodyGroupsFlipL(r2);
    case Quantified(_, _, _, r1) => LkBodyGroupsFlipL(r1);
    case Group(_, r1) => LkBodyGroupsFlipL(r1);
    case LookaroundR(_, r1) => FM.FlipLDefGroups(r1); LkBodyGroupsFlipL(r1);
    case _ =>
  }
}
