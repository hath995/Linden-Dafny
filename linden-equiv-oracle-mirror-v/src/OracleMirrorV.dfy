// L4 depth-k, nested ORACLE ENTRY, rung V3: the MIRROR + REMOVE-CAPTURE layer
// for the gated span predicate `MatchesV`.
//
//   - `MatchesVRemoveCapture`: matching is group-transparent, gates carry
//     their lid through `remove_capture` unchanged.
//   - `MatchesVMirror`: a gated span of `re` over `(str, ov)` is a gated span
//     of the anchor-swapped reversal `X(re) := SwapAnchorsRegex(reverse_regex(re))`
//     over `(Reverse(str), MirrorView(ov))` at the mirrored endpoints. Unlike
//     the depth-1 chain (which detoured through the Linden-side `MatchesL`),
//     this stays ENTIRELY on the RegElk side: characters and anchors mirror by
//     `CpContextMirror`/`IsSatisfiedMirror`, and a GATE mirrors by
//     `MirrorViewGet` — the mirrored view at the mirrored position IS the
//     original bit. Lookaround nodes pass through both `reverse_regex` and
//     `SwapAnchorsRegex` with their lid and flavour intact.
//   - fragment/involution bookkeeping: `X` preserves `NestedFragmentRE` and
//     is an involution, which turns the one-directional induction into the
//     biconditional.
/** V3 of the nested oracle entry: `MatchesVRemoveCapture` + `MatchesVMirror`. */
module LindenElkOracleMirrorV {
  import opened Std.Wrappers
  import R = RegElkRegex
  import RB = Bytecode
  import CP = Compiler
  import AI = ArrayInterp
  import LOr = Oracle
  import LAnc = Anchors
  import RC = Charclasses
  import T = LindenElkTranslate
  import NR = LindenElkNfaRep
  import ORc = LindenElkOracleReach
  import OBu = LindenElkOracleBuild
  import MIR = LindenElkMirror
  import OBV = LindenElkOracleBridgeV
  import ODV = LindenElkOracleDecompV
  import LC = Chars
  import LFS = FunctionalSemantics
  import SD = LindenSpanDuality

  /** The spec-side mirror operation on the RegElk AST: reverse, then swap
      anchors. Lookaround nodes keep their lid, flavour, and (reversed) body —
      only the gate matters to `MatchesV`, and the gate is untouched. */
  function XRev(re: R.regex): R.regex {
    OBu.SwapAnchorsRegex(R.reverse_regex(re))
  }

  // ===========================================================================
  // remove_capture is MatchesV-transparent
  // ===========================================================================

  /** Group-transparency, gated: `remove_capture` preserves the `MatchesV`
      span set (gates keep their lid). */
  lemma MatchesVRemoveCapture(re: R.regex, str: string, ov: LOr.OracleView, i: int, j: int)
    ensures OBV.MatchesV(R.remove_capture(re), str, ov, i, j) <==> OBV.MatchesV(re, str, ov, i, j)
    decreases CP.rsize(re), 0, 0
  {
    match re
    case Re_alt(r1, r2) =>
      MatchesVRemoveCapture(r1, str, ov, i, j); MatchesVRemoveCapture(r2, str, ov, i, j);
    case Re_con(r1, r2) =>
      forall m: int
        ensures (OBV.MatchesV(R.remove_capture(r1), str, ov, i, m) && OBV.MatchesV(R.remove_capture(r2), str, ov, m, j))
            <==> (OBV.MatchesV(r1, str, ov, i, m) && OBV.MatchesV(r2, str, ov, m, j))
      { MatchesVRemoveCapture(r1, str, ov, i, m); MatchesVRemoveCapture(r2, str, ov, m, j); }
    case Re_quant(nul, qid, q, r1) =>
      forall k: nat
        ensures OBV.MatchesIterV(R.remove_capture(r1), k, str, ov, i, j) <==> OBV.MatchesIterV(r1, k, str, ov, i, j)
      { MatchesIterVRemoveCapture(r1, k, str, ov, i, j); }
    case Re_capture(cid, r1) => MatchesVRemoveCapture(r1, str, ov, i, j);
    case _ =>
  }

  /** The iteration-chain analogue (mutually recursive). */
  lemma MatchesIterVRemoveCapture(r: R.regex, k: nat, str: string, ov: LOr.OracleView, i: int, j: int)
    ensures OBV.MatchesIterV(R.remove_capture(r), k, str, ov, i, j) <==> OBV.MatchesIterV(r, k, str, ov, i, j)
    decreases CP.rsize(r), 1, k
  {
    if k > 0 {
      forall m: int
        ensures (OBV.MatchesV(R.remove_capture(r), str, ov, i, m) && OBV.MatchesIterV(R.remove_capture(r), k - 1, str, ov, m, j))
            <==> (OBV.MatchesV(r, str, ov, i, m) && OBV.MatchesIterV(r, k - 1, str, ov, m, j))
      { MatchesVRemoveCapture(r, str, ov, i, m); MatchesIterVRemoveCapture(r, k - 1, str, ov, m, j); }
    }
  }

  /** `remove_capture` preserves the nested fragment. */
  lemma RemoveCaptureNestedFragment(re: R.regex)
    requires NR.NestedFragmentRE(re)
    ensures NR.NestedFragmentRE(R.remove_capture(re))
    decreases re
  {
    match re
    case Re_alt(r1, r2) => RemoveCaptureNestedFragment(r1); RemoveCaptureNestedFragment(r2);
    case Re_con(r1, r2) => RemoveCaptureNestedFragment(r1); RemoveCaptureNestedFragment(r2);
    case Re_quant(_, _, _, r1) => RemoveCaptureNestedFragment(r1); RemoveCaptureNullableX(r1);
    case Re_capture(_, r1) => RemoveCaptureNestedFragment(r1);
    case Re_lookaround(_, _, r1) => RemoveCaptureNestedFragment(r1); RemoveCaptureCapFreeX(r1);
    case _ =>
  }

  /** Local copy: `remove_capture` preserves nullability. */
  lemma RemoveCaptureNullableX(re: R.regex)
    ensures R.nullable(R.remove_capture(re)) == R.nullable(re)
    decreases re
  {
    match re
    case Re_alt(r1, r2) => RemoveCaptureNullableX(r1); RemoveCaptureNullableX(r2);
    case Re_con(r1, r2) => RemoveCaptureNullableX(r1); RemoveCaptureNullableX(r2);
    case Re_quant(_, _, _, r1) => RemoveCaptureNullableX(r1);
    case Re_capture(_, r1) => RemoveCaptureNullableX(r1);
    case Re_lookaround(_, _, r1) => RemoveCaptureNullableX(r1);
    case _ =>
  }

  /** Local copy: `remove_capture`'s output is capture-free. */
  lemma RemoveCaptureCapFreeX(re: R.regex)
    ensures NR.CaptureFreeRE(R.remove_capture(re))
    decreases re
  {
    match re
    case Re_alt(r1, r2) => RemoveCaptureCapFreeX(r1); RemoveCaptureCapFreeX(r2);
    case Re_con(r1, r2) => RemoveCaptureCapFreeX(r1); RemoveCaptureCapFreeX(r2);
    case Re_quant(_, _, _, r1) => RemoveCaptureCapFreeX(r1);
    case Re_capture(_, r1) => RemoveCaptureCapFreeX(r1);
    case Re_lookaround(_, _, r1) => RemoveCaptureCapFreeX(r1);
    case _ =>
  }

  // ===========================================================================
  // XRev bookkeeping: nullability, fragment, involution
  // ===========================================================================

  /** The anchor swap preserves nullability (anchors are `CDNullable`). */
  lemma SwapAnchorsNullable(r: R.regex)
    ensures R.nullable(OBu.SwapAnchorsRegex(r)) == R.nullable(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => SwapAnchorsNullable(r1); SwapAnchorsNullable(r2);
    case Re_con(r1, r2) => SwapAnchorsNullable(r1); SwapAnchorsNullable(r2);
    case Re_quant(_, _, _, r1) => SwapAnchorsNullable(r1);
    case Re_capture(_, r1) => SwapAnchorsNullable(r1);
    case Re_lookaround(_, _, r1) => SwapAnchorsNullable(r1);
    case _ =>
  }

  /** `XRev` preserves nullability. */
  lemma XRevNullable(r: R.regex)
    ensures R.nullable(XRev(r)) == R.nullable(r)
  {
    NR.ReverseNullableRE(r);
    SwapAnchorsNullable(R.reverse_regex(r));
  }

  /** The anchor swap preserves capture-freedom. */
  lemma SwapAnchorsCapFree(r: R.regex)
    requires NR.CaptureFreeRE(r)
    ensures NR.CaptureFreeRE(OBu.SwapAnchorsRegex(r))
    decreases r
  {
    match r
    case Re_alt(r1, r2) => SwapAnchorsCapFree(r1); SwapAnchorsCapFree(r2);
    case Re_con(r1, r2) => SwapAnchorsCapFree(r1); SwapAnchorsCapFree(r2);
    case Re_quant(_, _, _, r1) => SwapAnchorsCapFree(r1);
    case Re_lookaround(_, _, r1) => SwapAnchorsCapFree(r1);
    case _ =>
  }

  /** `reverse_regex` preserves capture-freedom. */
  lemma ReverseCapFree(r: R.regex)
    requires NR.CaptureFreeRE(r)
    ensures NR.CaptureFreeRE(R.reverse_regex(r))
    decreases r
  {
    match r
    case Re_alt(r1, r2) => ReverseCapFree(r1); ReverseCapFree(r2);
    case Re_con(r1, r2) => ReverseCapFree(r1); ReverseCapFree(r2);
    case Re_quant(_, _, _, r1) => ReverseCapFree(r1);
    case Re_lookaround(_, _, r1) => ReverseCapFree(r1);
    case _ =>
  }

  /** `XRev` preserves the nested fragment (quant shapes ride the preserved
      nullability; negative-look capture-freedom rides the preserved
      capture-freedom). */
  lemma XRevNestedFragment(re: R.regex)
    requires NR.NestedFragmentRE(re)
    ensures NR.NestedFragmentRE(XRev(re))
    decreases re
  {
    match re
    case Re_alt(r1, r2) => XRevNestedFragment(r1); XRevNestedFragment(r2);
    case Re_con(r1, r2) => XRevNestedFragment(r1); XRevNestedFragment(r2);
    case Re_quant(nul, qid, q, r1) =>
      XRevNestedFragment(r1);
      XRevNullable(r1);
    case Re_capture(_, r1) => XRevNestedFragment(r1);
    case Re_lookaround(lid, la, r1) =>
      XRevNestedFragment(r1);
      if !(la.Lookahead? || la.Lookbehind?) {
        ReverseCapFree(r1);
        SwapAnchorsCapFree(R.reverse_regex(r1));
      }
    case _ =>
  }

  /** `XRev` is an involution. */
  lemma XRevInvolution(re: R.regex)
    ensures XRev(XRev(re)) == re
    decreases re
  {
    match re
    case Re_alt(r1, r2) => XRevInvolution(r1); XRevInvolution(r2);
    case Re_con(r1, r2) => XRevInvolution(r1); XRevInvolution(r2);
    case Re_quant(_, _, _, r1) => XRevInvolution(r1);
    case Re_capture(_, r1) => XRevInvolution(r1);
    case Re_lookaround(_, _, r1) => XRevInvolution(r1);
    case Re_anchor(a) => MIR.SwapAnchorInvolution(a);
    case _ =>
  }

  // ===========================================================================
  // THE MIRROR
  // ===========================================================================

  /** One direction: a gated span mirrors onto the anchor-swapped reversal,
      over the reversed string against the mirrored view. */
  lemma MatchesVMirrorFwd(re: R.regex, str: string, ov: LOr.OracleView, i: int, j: int)
    requires |ov| == |str| + 1
    requires 0 <= i && j <= |str|
    requires OBV.MatchesV(re, str, ov, i, j)
    ensures OBV.MatchesV(XRev(re), LC.Reverse(str), MIR.MirrorView(ov, |str|), |str| - j, |str| - i)
    decreases CP.rsize(re), 0, 0
  {
    var n := |str|;
    var rstr := LC.Reverse(str);
    var mv := MIR.MirrorView(ov, n);
    OBV.MatchesVBounds(re, str, ov, i, j);
    match re
    case Re_empty =>
    case Re_character(ch) =>
      // j == i + 1; the mirrored span consumes rstr[n - j] == str[i]
      MIR.CpContextMirror(str, i);
      assert AI.cp_context(i, str, LAnc.Backward).prevchar == AI.get_char(str, i);
      assert AI.cp_context(n - i, rstr, LAnc.Forward).prevchar == AI.get_char(rstr, n - i - 1);
      assert AI.get_char(rstr, n - j) == AI.get_char(str, i);
    case Re_anchor(a) =>
      // i == j; the swapped anchor at the mirrored position reads the
      // field-swapped context
      MIR.CpContextMirror(str, i);
      assert ORc.CtxAt(rstr, n - i) == AI.cp_context(i, str, LAnc.Backward);
      MIR.IsSatisfiedMirror(a, AI.cp_context(i, str, LAnc.Backward));
      assert LAnc.is_satisfied(a, AI.cp_context(i, str, LAnc.Backward), LAnc.Backward)
          <==> LAnc.is_satisfied(MIR.SwapAnchor(a), ORc.CtxAt(rstr, n - i), LAnc.Forward);
    case Re_alt(r1, r2) =>
      if OBV.MatchesV(r1, str, ov, i, j) { MatchesVMirrorFwd(r1, str, ov, i, j); }
      else { MatchesVMirrorFwd(r2, str, ov, i, j); }
    case Re_con(r1, r2) =>
      var m: int :| OBV.MatchesV(r1, str, ov, i, m) && OBV.MatchesV(r2, str, ov, m, j);
      OBV.MatchesVBounds(r1, str, ov, i, m);
      OBV.MatchesVBounds(r2, str, ov, m, j);
      MatchesVMirrorFwd(r1, str, ov, i, m);
      MatchesVMirrorFwd(r2, str, ov, m, j);
      assert OBV.MatchesV(XRev(r2), rstr, mv, n - j, n - m)
          && OBV.MatchesV(XRev(r1), rstr, mv, n - m, n - i);
      assert XRev(re) == R.Re_con(XRev(r2), XRev(r1));
    case Re_capture(cid, r1) =>
      MatchesVMirrorFwd(r1, str, ov, i, j);
    case Re_quant(nul, qid, q, r1) =>
      var k: nat :| q.min <= k && (q.max.Some? ==> k <= q.max.value)
                 && OBV.MatchesIterV(r1, k, str, ov, i, j);
      MatchesIterVMirrorFwd(r1, k, str, ov, i, j);
      assert XRev(re) == R.Re_quant(nul, qid, q, XRev(r1));
      assert OBV.MatchesIterV(XRev(r1), k, rstr, mv, n - j, n - i);
    case Re_lookaround(lid, la, r1) =>
      // i == j; the mirrored view at the mirrored position IS the bit
      MIR.MirrorViewGet(ov, n, i, lid);
      assert LOr.view_get_oracle(mv, n - i, lid) == LOr.view_get_oracle(ov, i, lid);
      assert XRev(re) == R.Re_lookaround(lid, la, XRev(r1));
  }

  /** The iteration-chain mirror: the span order reverses, so the mirrored
      chain is built by appending each mirrored head at the END. */
  lemma MatchesIterVMirrorFwd(r: R.regex, k: nat, str: string, ov: LOr.OracleView, i: int, j: int)
    requires |ov| == |str| + 1
    requires 0 <= i && j <= |str|
    requires OBV.MatchesIterV(r, k, str, ov, i, j)
    ensures OBV.MatchesIterV(XRev(r), k, LC.Reverse(str), MIR.MirrorView(ov, |str|), |str| - j, |str| - i)
    decreases CP.rsize(r), 1, k
  {
    var n := |str|;
    var rstr := LC.Reverse(str);
    var mv := MIR.MirrorView(ov, n);
    if k == 0 { return; }
    var m: int :| OBV.MatchesV(r, str, ov, i, m) && OBV.MatchesIterV(r, k - 1, str, ov, m, j);
    OBV.MatchesVBounds(r, str, ov, i, m);
    OBV.MatchesIterVBounds(r, k - 1, str, ov, m, j);
    MatchesVMirrorFwd(r, str, ov, i, m);
    MatchesIterVMirrorFwd(r, k - 1, str, ov, m, j);
    // tail chain [n-j, n-m], then the mirrored head [n-m, n-i] appended
    ODV.IterSnocV(XRev(r), k - 1, rstr, mv, n - j, n - m, n - i);
  }

  /** THE biconditional mirror, via the involution. */
  lemma MatchesVMirror(re: R.regex, str: string, ov: LOr.OracleView, i: int, j: int)
    requires |ov| == |str| + 1
    requires 0 <= i && j <= |str|
    requires 0 <= |str| - j && |str| - i <= |str|
    ensures OBV.MatchesV(re, str, ov, i, j)
        <==> OBV.MatchesV(XRev(re), LC.Reverse(str), MIR.MirrorView(ov, |str|), |str| - j, |str| - i)
  {
    var n := |str|;
    var rstr := LC.Reverse(str);
    var mv := MIR.MirrorView(ov, n);
    if OBV.MatchesV(re, str, ov, i, j) {
      MatchesVMirrorFwd(re, str, ov, i, j);
    }
    if OBV.MatchesV(XRev(re), rstr, mv, n - j, n - i) {
      LFS.ReverseReverse(str);
      SD.ReverseLength(str);
      assert |rstr| == n;
      MatchesVMirrorFwd(XRev(re), rstr, mv, n - j, n - i);
      XRevInvolution(re);
      MIR.MirrorViewInvolution(ov, n);
      assert LC.Reverse(rstr) == str;
      assert OBV.MatchesV(re, str, ov, n - (n - i), n - (n - j));
    }
  }
}
