// Lookaround campaign (L1), part C5 glue (§6.4 of LOOKAROUND_CAMPAIGN.md):
// the AST transfer and the oracle's SPEC-LEVEL characterization.
//
// Two engine-free-ish steps close the gap between the engine's oracle
// theorem and the Linden semantics:
//
//   MatchesTransfer — the RegElk-side span predicate `OB.Matches` (over the
//   annotated RegElk AST, testing characters through the compiler's own
//   `ExpectationOf` and anchors through `is_satisfied`) agrees with the
//   Linden-side `SD.MatchesL` (over the translated AST, testing `CharMatch`
//   and `AnchorSatisfied`). Structural induction, discharged by the two
//   agreement lemmas `T.CharSemAgree` / `T.AnchorSemAgree`; the only
//   hypotheses are the record's `!ignoreCase`/`!multiline` (the L1 record
//   shape), `T.TransWf`, and that the span lives inside the string —
//   outside it the two disagree, since `MatchesL` pins its positions to
//   `0..|str|` while the engine's context functions silently return `None`.
//   No capture- or look-freedom is needed: captures translate to `Group`
//   (both predicates see through it) and lookarounds have no rule on
//   either side.
//
//   OracleColumnSpec — the capstone chain: an oracle bit for a lookbehind
//   lid at position cp is EXACTLY the success of the BACKWARD walk of the
//   translated body from cp. Composed from `OD.OracleColumnCharacterized`
//   (engine: bit <==> a forward body span ending at cp), `MatchesTransfer`
//   (that span, over the Linden AST), and `SD.SpanDualityComplete`/
//   `SpanDualitySound` (that span <==> the backward walk succeeds). This is
//   the shape §6.5's `OracleOk` conjunct of `StaticOkRE` consumes, and it
//   is what §6.6's assembly discharges.
include "OracleDecomp.dfy"

/** §6.4 glue: `MatchesTransfer` (RegElk spans ⟷ Linden spans through
    `Translate`) and `OracleColumnSpec` (oracle bit ⟷ backward walk). */
module LindenElkOracleSpec {
  import opened Std.Wrappers
  import R = RegElkRegex
  import CP = Compiler
  import AI = ArrayInterp
  import LOr = Oracle
  import LAnc = Anchors
  import RC = Charclasses
  import LW = WarblreRegExpRecord
  import WP = WarblrePrimitives
  import LC = Chars
  import LG = Groups
  import L = Regex
  import LN = WarblreNumeric
  import LS = Semantics
  import T = LindenElkTranslate
  import SD = LindenSpanDuality
  import NR = LindenElkNfaRep
  import LT = LindenElkLookTables
  import ORc = LindenElkOracleReach
  import OB = LindenElkOracleBridge
  import OD = LindenElkOracleDecomp
  import OBu = LindenElkOracleBuild
  import MIR = LindenElkMirror

  // ===========================================================================
  // Position contexts
  // ===========================================================================

  /** Inside the string the engine's position context (built from
      `get_char`, which returns `None` off both ends) is literally the
      translation's `CpContext`. */
  lemma CtxAtIsCpContext(str: string, cp: int)
    requires 0 <= cp <= |str|
    ensures ORc.CtxAt(str, cp) == T.CpContext(str, cp, LAnc.Forward)
  {
  }

  // ===========================================================================
  // The AST transfer
  // ===========================================================================

  /** THE transfer: a RegElk span match is a Linden span match of the
      translated regex. Both directions, by structural induction over the
      annotated AST. */
  lemma MatchesTransfer(rer: LW.RegExpRecord, re: R.regex, str: string, i: int, j: int)
    requires !rer.ignoreCase && !rer.multiline
    requires T.TransWf(re)
    // `MatchesL` now gives a lookaround REAL span semantics (what L4's nesting
    // needs), while `OB.Matches` still reports false for one. The transfer
    // therefore holds exactly where no lookaround can occur -- which every
    // caller has, since these are lookaround BODIES.
    requires NR.LookFreeRE(re)
    requires 0 <= i && j <= |str|
    ensures OB.Matches(re, str, i, j) <==> SD.MatchesL(rer, T.Translate(re), str, i, j)
    decreases CP.rsize(re), 0, 0
  {
    match re
    case Re_empty =>
    case Re_character(c) =>
      if j == i + 1 {
        assert 0 <= i < |str|;
        assert AI.get_char(str, i) == Some(str[i]);
        T.CharSemAgree(rer, c, str[i]);
      }
    case Re_anchor(a) =>
      if i == j {
        CtxAtIsCpContext(str, i);
        T.AnchorSemAgree(rer, a, str, i, LAnc.Forward);
      }
    case Re_alt(r1, r2) =>
      MatchesTransfer(rer, r1, str, i, j);
      MatchesTransfer(rer, r2, str, i, j);
    case Re_con(r1, r2) =>
      if OB.Matches(re, str, i, j) {
        assert OB.Matches(R.Re_con(r1, r2), str, i, j);
        var m: int :| OB.Matches(r1, str, i, m) && OB.Matches(r2, str, m, j);
        OB.MatchesBounds(r1, str, i, m);
        OB.MatchesBounds(r2, str, m, j);
        MatchesTransfer(rer, r1, str, i, m);
        MatchesTransfer(rer, r2, str, m, j);
        assert SD.MatchesL(rer, T.Translate(r2), str, m, j);
      }
      if SD.MatchesL(rer, T.Translate(re), str, i, j) {
        assert SD.MatchesL(rer, L.Sequence(T.Translate(r1), T.Translate(r2)), str, i, j);
        var m: int :| SD.MatchesL(rer, T.Translate(r1), str, i, m)
                   && SD.MatchesL(rer, T.Translate(r2), str, m, j);
        SD.MatchesLBounds(rer, T.Translate(r1), str, i, m);
        SD.MatchesLBounds(rer, T.Translate(r2), str, m, j);
        MatchesTransfer(rer, r1, str, i, m);
        MatchesTransfer(rer, r2, str, m, j);
      }
    case Re_quant(nul, qid, q, r1) =>
      if OB.Matches(re, str, i, j) {
        assert OB.Matches(R.Re_quant(nul, qid, q, r1), str, i, j);
        var k: nat :| q.min <= k && (q.max.Some? ==> k <= q.max.value)
                   && OB.MatchesIter(r1, k, str, i, j);
        QuantBoundsAgree(q, k);
        OB.MatchesIterBounds(r1, k, str, i, j);
        IterTransfer(rer, r1, k, str, i, j);
        assert SD.IterL(rer, T.Translate(r1), k, str, i, j);
        assert SD.MatchesL(rer, L.Quantified(q.greedy, q.min as nat, T.TrDelta(q),
                                             T.Translate(r1)), str, i, j);
      }
      if SD.MatchesL(rer, T.Translate(re), str, i, j) {
        assert SD.MatchesL(rer, L.Quantified(q.greedy, q.min as nat, T.TrDelta(q),
                                             T.Translate(r1)), str, i, j);
        var k: nat :| (q.min as nat) <= k
                   && (match T.TrDelta(q)
                       case Inf => true
                       case NN(dx) => k <= (q.min as nat) + dx)
                   && SD.IterL(rer, T.Translate(r1), k, str, i, j);
        QuantBoundsAgree(q, k);
        SD.IterLBounds(rer, T.Translate(r1), k, str, i, j);
        IterTransfer(rer, r1, k, str, i, j);
        assert OB.MatchesIter(r1, k, str, i, j);
        assert OB.Matches(R.Re_quant(nul, qid, q, r1), str, i, j);
      }
    case Re_capture(cid, r1) =>
      MatchesTransfer(rer, r1, str, i, j);
    case Re_lookaround(lid, lk, r1) =>   // excluded by LookFreeRE
  }

  /** The two quantifier bound encodings pick out the same counters: RegElk
      carries `(min, max)` with `max` optional, Linden carries `(min, delta)`
      with `delta` `Inf`/`NN(max-min)`. */
  lemma QuantBoundsAgree(q: R.counted_quantifier, k: nat)
    requires T.QuantWf(q)
    ensures (q.min <= k && (q.max.Some? ==> k <= q.max.value))
        <==> ((q.min as nat) <= k
              && (match T.TrDelta(q) case Inf => true case NN(dx) => k <= (q.min as nat) + dx))
  {
    match q.max
    case None =>
    case Some(mx) =>
      assert T.TrDelta(q) == LN.NN((mx - q.min) as nat);
      assert (q.min as nat) + ((mx - q.min) as nat) == mx;
  }

  /** `MatchesTransfer` for iteration chains. */
  lemma IterTransfer(rer: LW.RegExpRecord, r: R.regex, k: nat, str: string, i: int, j: int)
    requires !rer.ignoreCase && !rer.multiline
    requires T.TransWf(r)
    requires NR.LookFreeRE(r)
    requires 0 <= i && j <= |str|
    ensures OB.MatchesIter(r, k, str, i, j) <==> SD.IterL(rer, T.Translate(r), k, str, i, j)
    decreases CP.rsize(r), 1, k
  {
    if k > 0 {
      if OB.MatchesIter(r, k, str, i, j) {
        var m := OB.MatchesIterHead(r, k, str, i, j);
        OB.MatchesBounds(r, str, i, m);
        OB.MatchesIterBounds(r, k - 1, str, m, j);
        MatchesTransfer(rer, r, str, i, m);
        IterTransfer(rer, r, k - 1, str, m, j);
        SD.IterLCons(rer, T.Translate(r), k - 1, str, i, m, j);
      }
      if SD.IterL(rer, T.Translate(r), k, str, i, j) {
        var m := SD.IterLHead(rer, T.Translate(r), k, str, i, j);
        SD.MatchesLBounds(rer, T.Translate(r), str, i, m);
        SD.IterLBounds(rer, T.Translate(r), k - 1, str, m, j);
        MatchesTransfer(rer, r, str, i, m);
        IterTransfer(rer, r, k - 1, str, m, j);
        OD.IterCons(r, k - 1, str, i, m, j);
      }
    }
  }

  // ===========================================================================
  // Group-freedom of translated L1 bodies
  // ===========================================================================

  /** Capture-free, lookaround-free RegElk bodies translate into the
      group-free fragment the span duality is proved for (RegElk has no
      backreference node at all). */
  lemma TranslateGroupFree(re: R.regex)
    requires T.TransWf(re)
    requires NR.CaptureFreeRE(re) && NR.LookFreeRE(re)
    ensures SD.GroupFreeL(T.Translate(re))
    decreases re
  {
    match re
    case Re_alt(r1, r2) => TranslateGroupFree(r1); TranslateGroupFree(r2);
    case Re_con(r1, r2) => TranslateGroupFree(r1); TranslateGroupFree(r2);
    case Re_quant(_, _, _, r1) => TranslateGroupFree(r1);
    case _ =>
  }

  /** L3a: a LOOK-free RegElk body (captures allowed) translates into the
      `GroupOkL` fragment — `GroupOkL` forbids only lookarounds and backreferences
      (RegElk has no backref node), so captures (`Group` nodes) are fine. This is
      what a CAPTURING lookahead body needs where the L1 lookbehind path used
      `TranslateGroupFree` + `GroupFreeIsGroupOk`. */
  lemma TranslateLookFreeGroupOk(re: R.regex)
    requires T.TransWf(re)
    requires NR.LookFreeRE(re)
    ensures SD.GroupOkL(T.Translate(re))
    decreases re
  {
    match re
    case Re_alt(r1, r2) => TranslateLookFreeGroupOk(r1); TranslateLookFreeGroupOk(r2);
    case Re_con(r1, r2) => TranslateLookFreeGroupOk(r1); TranslateLookFreeGroupOk(r2);
    case Re_quant(_, _, _, r1) => TranslateLookFreeGroupOk(r1);
    case Re_capture(_, r1) => TranslateLookFreeGroupOk(r1);
    case _ =>   // empty/char/anchor: GroupOkL true; Re_lookaround excluded by LookFreeRE
  }

  /** L3a: matching is GROUP-TRANSPARENT — a `Re_capture` node matches exactly its
      child — so `remove_capture` preserves the match set. This bridges the oracle
      (built over `remove_capture(body)`, group-free) to the body's own spans (over
      which the `GroupOkL` span duality is stated). */
  lemma MatchesRemoveCapture(re: R.regex, str: string, i: int, j: int)
    ensures OB.Matches(R.remove_capture(re), str, i, j) <==> OB.Matches(re, str, i, j)
    decreases CP.rsize(re), 0, 0
  {
    match re
    case Re_alt(r1, r2) => MatchesRemoveCapture(r1, str, i, j); MatchesRemoveCapture(r2, str, i, j);
    case Re_con(r1, r2) =>
      forall m: int
        ensures (OB.Matches(R.remove_capture(r1), str, i, m) && OB.Matches(R.remove_capture(r2), str, m, j))
            <==> (OB.Matches(r1, str, i, m) && OB.Matches(r2, str, m, j))
      { MatchesRemoveCapture(r1, str, i, m); MatchesRemoveCapture(r2, str, m, j); }
    case Re_quant(nul, qid, q, r1) =>
      forall k: nat
        ensures OB.MatchesIter(R.remove_capture(r1), k, str, i, j) <==> OB.MatchesIter(r1, k, str, i, j)
      { MatchesIterRemoveCapture(r1, k, str, i, j); }
    case Re_capture(cid, r1) => MatchesRemoveCapture(r1, str, i, j);
    case _ =>
  }

  /** The iteration-chain analogue of `MatchesRemoveCapture` (mutually recursive). */
  lemma MatchesIterRemoveCapture(r: R.regex, k: nat, str: string, i: int, j: int)
    ensures OB.MatchesIter(R.remove_capture(r), k, str, i, j) <==> OB.MatchesIter(r, k, str, i, j)
    decreases CP.rsize(r), 1, k
  {
    if k > 0 {
      forall m: int
        ensures (OB.Matches(R.remove_capture(r), str, i, m) && OB.MatchesIter(R.remove_capture(r), k - 1, str, m, j))
            <==> (OB.Matches(r, str, i, m) && OB.MatchesIter(r, k - 1, str, m, j))
      { MatchesRemoveCapture(r, str, i, m); MatchesIterRemoveCapture(r, k - 1, str, m, j); }
    }
  }

  /** `remove_capture` structural preservation: its output is capture-free, and it
      preserves look-freeness, the plus fragment, and translation well-formedness
      (it only deletes `Group` nodes). Establishes the fragment facts for the
      capture-stripped body the oracle is actually built over. */
  lemma RemoveCaptureCaptureFree(re: R.regex)
    ensures NR.CaptureFreeRE(R.remove_capture(re))
    decreases re
  {
    match re
    case Re_alt(r1, r2) => RemoveCaptureCaptureFree(r1); RemoveCaptureCaptureFree(r2);
    case Re_con(r1, r2) => RemoveCaptureCaptureFree(r1); RemoveCaptureCaptureFree(r2);
    case Re_quant(_, _, _, r1) => RemoveCaptureCaptureFree(r1);
    case Re_capture(_, r1) => RemoveCaptureCaptureFree(r1);
    case Re_lookaround(_, _, r1) => RemoveCaptureCaptureFree(r1);
    case _ =>
  }
  lemma RemoveCaptureLookFree(re: R.regex)
    requires NR.LookFreeRE(re)
    ensures NR.LookFreeRE(R.remove_capture(re))
    decreases re
  {
    match re
    case Re_alt(r1, r2) => RemoveCaptureLookFree(r1); RemoveCaptureLookFree(r2);
    case Re_con(r1, r2) => RemoveCaptureLookFree(r1); RemoveCaptureLookFree(r2);
    case Re_quant(_, _, _, r1) => RemoveCaptureLookFree(r1);
    case Re_capture(_, r1) => RemoveCaptureLookFree(r1);
    case _ =>
  }
  /** `remove_capture` preserves nullability (a `Group(r)` is nullable iff `r`
      is) — the plus-fragment's `nullable(body) == NonNullable` side condition. */
  lemma RemoveCaptureNullable(re: R.regex)
    ensures R.nullable(R.remove_capture(re)) == R.nullable(re)
    decreases re
  {
    match re
    case Re_alt(r1, r2) => RemoveCaptureNullable(r1); RemoveCaptureNullable(r2);
    case Re_con(r1, r2) => RemoveCaptureNullable(r1); RemoveCaptureNullable(r2);
    case Re_quant(_, _, _, r1) => RemoveCaptureNullable(r1);
    case Re_capture(_, r1) => RemoveCaptureNullable(r1);
    case Re_lookaround(_, _, r1) => RemoveCaptureNullable(r1);
    case _ =>
  }
  lemma RemoveCapturePlusFragment(re: R.regex)
    requires NR.PlusFragmentRE(re)
    ensures NR.PlusFragmentRE(R.remove_capture(re))
    decreases re
  {
    match re
    case Re_alt(r1, r2) => RemoveCapturePlusFragment(r1); RemoveCapturePlusFragment(r2);
    case Re_con(r1, r2) => RemoveCapturePlusFragment(r1); RemoveCapturePlusFragment(r2);
    case Re_quant(_, _, _, r1) => RemoveCapturePlusFragment(r1); RemoveCaptureNullable(r1);
    case Re_capture(_, r1) => RemoveCapturePlusFragment(r1);
    case _ =>
  }
  lemma RemoveCaptureTransWf(re: R.regex)
    requires T.TransWf(re)
    ensures T.TransWf(R.remove_capture(re))
    decreases re
  {
    match re
    case Re_alt(r1, r2) => RemoveCaptureTransWf(r1); RemoveCaptureTransWf(r2);
    case Re_con(r1, r2) => RemoveCaptureTransWf(r1); RemoveCaptureTransWf(r2);
    case Re_quant(_, _, _, r1) => RemoveCaptureTransWf(r1);
    case Re_capture(_, r1) => RemoveCaptureTransWf(r1);
    case _ =>
  }

  // ===========================================================================
  // The spec-level oracle characterization
  // ===========================================================================

  /** THE §6.4 capstone: for an L1 lookbehind, the oracle bit at `cp` holds
      exactly when the BACKWARD walk of the translated body from `cp`
      succeeds — the statement `OracleOk` (§6.5) is built from, and the one
      the tree-rep layer's `tr_lk`/`tr_lkfail` disjuncts will read.
      Group-freedom makes the walk's success independent of `gm`, so the
      right-hand side is a boolean of `(body, str, cp)` alone. */
  lemma OracleColumnSpec(rer: LW.RegExpRecord, re: R.regex, str: string, lid: R.lookid,
                         la: R.lookaround, body: R.regex, cp: int, gm: LG.GroupMap)
    requires !rer.ignoreCase && !rer.multiline
    requires NR.LookBehindFragmentRE(re)
    requires LT.LookUnique(re)
    requires LT.LookEntryOk(CP.FFullCompilation(re), lid, la, body)
    requires la.Lookbehind? || la.NegLookbehind?
    requires NR.CaptureFreeRE(body) && NR.LookFreeRE(body) && NR.PlusFragmentRE(body)
    requires T.TransWf(body)
    requires 1 <= lid
    requires 0 <= cp <= |str|
    ensures LOr.view_get_oracle(AI.FBuildOracle(CP.FFullCompilation(re), str), cp, lid)
        <==> SD.SuccActs(rer, [LS.Areg(T.Translate(body))], T.InputAt(str, cp), gm, WP.Backward)
  {
    OD.OracleColumnCharacterized(re, str, lid, la, body, cp);
    TranslateGroupFree(body);
    SD.GroupFreeIsGroupOk(T.Translate(body));   // SpanDuality now gates on GroupOkL (L3-0)
    if LOr.view_get_oracle(AI.FBuildOracle(CP.FFullCompilation(re), str), cp, lid) {
      var i := OD.RecorderHitInv(body, str, cp);
      MatchesTransfer(rer, body, str, i, cp);
      SD.SpanDualityComplete(rer, T.Translate(body), str, i, cp, gm);
    }
    if SD.SuccActs(rer, [LS.Areg(T.Translate(body))], T.InputAt(str, cp), gm, WP.Backward) {
      var i := SD.SpanDualitySound(rer, T.Translate(body), str, cp, gm);
      MatchesTransfer(rer, body, str, i, cp);
      OD.RecorderHitIntro(body, str, cp, i);
    }
  }

  // ==========================================================================
  // The span reversal, transferred to the engine side (L2)
  // ==========================================================================

  /** `MatchesLReverse` carried across the translation: an engine-side span of
      `re` over `str` is a span of `RevRE(re)` over the reversed string, at the
      mirrored interval.

      This is what turns a lookAHEAD's reversed oracle build back into a
      statement about the body matching FORWARD from `cp`. */
  /** The reversal preserves look-freedom (it only reorders concatenations and
      swaps anchors). */
  lemma RevRELookFree(re: R.regex)
    requires NR.LookFreeRE(re)
    ensures NR.LookFreeRE(SD.RevRE(re))
    decreases re
  {
    match re
    case Re_alt(r1, r2) => RevRELookFree(r1); RevRELookFree(r2);
    case Re_con(r1, r2) => RevRELookFree(r1); RevRELookFree(r2);
    case Re_quant(_, _, _, r1) => RevRELookFree(r1);
    case Re_capture(_, r1) => RevRELookFree(r1);
    case _ =>
  }

  lemma MatchesReverseRE(rer: LW.RegExpRecord, re: R.regex, str: string, i: int, j: int)
    requires !rer.ignoreCase && !rer.multiline
    requires T.TransWf(re)
    requires NR.LookFreeRE(re)
    requires SD.GroupOkL(T.Translate(re))
    requires 0 <= i <= j <= |str|
    ensures |LC.Reverse(str)| == |str|
    ensures T.TransWf(SD.RevRE(re))
    ensures OB.Matches(SD.RevRE(re), LC.Reverse(str), |str| - j, |str| - i)
        <==> OB.Matches(re, str, i, j)
  {
    SD.ReverseLength(str);
    SD.TranslateRevRE(re);
    RevRELookFree(re);
    MatchesTransfer(rer, re, str, i, j);
    MatchesTransfer(rer, SD.RevRE(re), LC.Reverse(str), |str| - j, |str| - i);
    SD.MatchesLReverse(rer, T.Translate(re), str, i, j);
    assert T.Translate(SD.RevRE(re)) == SD.RevL(T.Translate(re));
  }

  // ==========================================================================
  // The LOOKAHEAD column spec (L2)
  // ==========================================================================

  /** On an anchor-free regex the spec-side reversal IS the engine's
      `reverse_regex` -- they differ only in the anchor case. */
  lemma RevREIsReverse(r: R.regex)
    requires NR.StarFragmentRE(r)
    ensures SD.RevRE(r) == R.reverse_regex(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => RevREIsReverse(r1); RevREIsReverse(r2);
    case Re_con(r1, r2) => RevREIsReverse(r1); RevREIsReverse(r2);
    case Re_quant(_, _, _, r1) => RevREIsReverse(r1);
    case Re_capture(_, r1) => RevREIsReverse(r1);
    case _ =>
  }

  /** The spec-side reversal preserves nullability -- it only reorders
      concatenation (`null_and` is commutative) and swaps anchors (all anchors
      are `CDNullable`). Mirrors `PIV.ReverseNullable` for `RevRE`. */
  lemma RevRENullable(r: R.regex)
    ensures R.nullable(SD.RevRE(r)) == R.nullable(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => RevRENullable(r1); RevRENullable(r2);
    case Re_con(r1, r2) => RevRENullable(r1); RevRENullable(r2);
    case Re_quant(_, _, _, r1) => RevRENullable(r1);
    case Re_capture(_, r1) => RevRENullable(r1);
    case _ =>
  }

  /** ...and it keeps a regex in the plus fragment (the `+` side condition is
      phrased on the body's nullability, which `RevRENullable` preserves). */
  lemma RevREPlusFragment(r: R.regex)
    requires NR.PlusFragmentRE(r)
    ensures NR.PlusFragmentRE(SD.RevRE(r))
    decreases r
  {
    match r
    case Re_alt(r1, r2) => RevREPlusFragment(r1); RevREPlusFragment(r2);
    case Re_con(r1, r2) => RevREPlusFragment(r1); RevREPlusFragment(r2);
    case Re_quant(nul, qid, q, r1) => RevREPlusFragment(r1); RevRENullable(r1);
    case Re_capture(_, r1) => RevREPlusFragment(r1);
    case _ =>
  }

  /** The engine's `reverse_regex` followed by the bytecode-level anchor swap
      IS the spec-side `RevRE` (which reverses AND swaps anchors), on a
      look-free regex. This is what identifies the anchor-swapped backward
      build program with a compiled `RevRE(body)`. */
  lemma SwapReverseIsRevRE(r: R.regex)
    requires NR.LookFreeRE(r)
    ensures OBu.SwapAnchorsRegex(R.reverse_regex(r)) == SD.RevRE(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => SwapReverseIsRevRE(r1); SwapReverseIsRevRE(r2);
    case Re_con(r1, r2) => SwapReverseIsRevRE(r1); SwapReverseIsRevRE(r2);
    case Re_quant(_, _, _, r1) => SwapReverseIsRevRE(r1);
    case Re_capture(_, r1) => SwapReverseIsRevRE(r1);
    case Re_anchor(a) => assert MIR.SwapAnchor(a) == SD.SwapAnchorRE(a);
    case _ =>
  }

  /** THE LOOKAHEAD COLUMN SPEC. A lookAHEAD's oracle column at `cp` holds
      exactly when the spec's FORWARD walk of its body from `cp` succeeds --
      the mirror image of `OracleColumnSpec`, and the statement
      `OracleOkAt` needs for a lookahead row (where `LkDir` is Forward).

      The chain, and where each link came from:
        oracle bit                          FBuildOracleCorrect
          == LidReaches (Backward build)
          == forward reach of SwapAnchorsCode(build) over Reverse(str)
                                              LidReachesBackward
          == forward reach of compile_to_write(lazy_prefix(RevRE(body)))
                                              CompileToWriteSwap /
                                              SwapAnchorsLazyPrefix /
                                              SwapReverseIsRevRE
                                              (the anchor swap on the BYTECODE
                                               is the compile of RevRE(body),
                                               which reverses AND swaps anchors)
          <-> a span of RevRE(body) ending at Mirror(cp)
                                              ReachesWriteToMatches /
                                              MatchesToReachesWrite
          <-> a span of body STARTING at cp   MatchesReverseRE
          <-> the forward walk succeeds       MatchesTransfer +
                                              SpanDualityForward{Complete,Sound}

      Lookahead bodies may be anywhere in the plus fragment (no star-shape
      restriction): the compile/anchor-swap commutation makes the backward
      build's anchors well-behaved.
   */
  lemma OracleColumnSpecLookahead(rer: LW.RegExpRecord, re: R.regex, str: string,
                                  lid: R.lookid, la: R.lookaround, body: R.regex,
                                  cp: int, gm: LG.GroupMap)
    requires !rer.ignoreCase && !rer.multiline
    requires NR.LookBehindFragmentRE(re) && LT.LookUnique(re)
    requires LT.LookEntryOk(CP.FFullCompilation(re), lid, la, body)
    requires la.Lookahead? || la.NegLookahead?
    requires NR.LookFreeRE(body) && NR.PlusFragmentRE(body)   // L3a: capturing bodies allowed
    requires T.TransWf(body)
    requires 1 <= lid <= R.max_lookaround(re)
    requires 0 <= cp <= |str|
    ensures LOr.view_get_oracle(AI.FBuildOracle(CP.FFullCompilation(re), str), cp, lid)
        <==> SD.SuccActs(rer, [LS.Areg(T.Translate(body))], T.InputAt(str, cp), gm,
                         WP.Forward)
  {
    var crv := CP.FFullCompilation(re);
    var n := |str|;
    var rstr := LC.Reverse(str);
    // L3a: the oracle is built over the CAPTURE-STRIPPED body (oracle_regex uses
    // remove_capture) — group-free, so the L1 oracle chain applies verbatim to
    // `rcb`. The `MatchesRemoveCapture` bridge then transfers to the body's own
    // spans (match existence is capture-blind), where the GroupOkL span duality
    // reconstructs `SuccActs(Translate(body))`.
    var rcb := R.remove_capture(body);
    RemoveCaptureCaptureFree(body); RemoveCaptureLookFree(body);
    RemoveCapturePlusFragment(body); RemoveCaptureTransWf(body);
    TranslateLookFreeGroupOk(rcb);   // GroupOkL(Translate(rcb)) for MatchesReverseRE
    TranslateLookFreeGroupOk(body);  // GroupOkL(Translate(body)) for the span duality
    var rb := R.reverse_regex(rcb);
    var rrb := SD.RevRE(rcb);
    SD.ReverseLength(str);

    // --- the build program for this row ------------------------------------
    assert CP.oracle_regex(la, body) == R.lazy_prefix(rb);   // = lazy_prefix(reverse_regex(remove_capture(body)))
    NR.ReverseLookFreeRE(rcb);
    OBu.LookFreeLazyPrefix(rb);
    var bc := CP.compile_to_write(R.lazy_prefix(rb), lid);
    assert AI.get_code_v(crv.f_look_build_bc, lid) == bc;

    // --- the anchor-swapped build program IS compile_to_write(lazy_prefix(RevRE(rcb))) ---
    OBu.CompileToWriteSwap(R.lazy_prefix(rb), lid);
    OBu.SwapAnchorsLazyPrefix(rb);
    SwapReverseIsRevRE(rcb);
    assert MIR.SwapAnchorsCode(bc) == CP.compile_to_write(R.lazy_prefix(rrb), lid);

    // --- fragment facts for RevRE(rcb) (capture-/look-free + plus) ---
    RevRELookFree(rcb);
    RevREPlusFragment(rcb);

    // --- oracle bit == a FORWARD reach of the swapped program over Reverse(str) ---
    OBu.FBuildOracleCorrect(re, str);
    assert OBu.LidDir(crv, lid) == LAnc.Backward;
    OBu.LidReachesBackward(crv, str, lid, cp);
    assert LOr.view_get_oracle(AI.FBuildOracle(crv, str), cp, lid)
        <==> ORc.ReachesWrite(CP.compile_to_write(R.lazy_prefix(rrb), lid), rstr, 0, lid,
                              MIR.Mirror(cp, n));

    if LOr.view_get_oracle(AI.FBuildOracle(crv, str), cp, lid) {
      var m := OD.ReachesWriteToMatches(rrb, lid, rstr, MIR.Mirror(cp, n));
      // m is the span's START in the reversal; mirror it back
      var j := n - m;
      MatchesReverseRE(rer, rcb, str, cp, j);       // Matches(rcb, str, cp, j)
      MatchesRemoveCapture(body, str, cp, j);        // <==> Matches(body, str, cp, j)
      assert OB.Matches(body, str, cp, j);
      MatchesTransfer(rer, body, str, cp, j);
      SD.SpanDualityForwardComplete(rer, T.Translate(body), str, cp, j, gm);
    }
    if SD.SuccActs(rer, [LS.Areg(T.Translate(body))], T.InputAt(str, cp), gm, WP.Forward) {
      var j := SD.SpanDualityForwardSound(rer, T.Translate(body), str, cp, gm);
      MatchesTransfer(rer, body, str, cp, j);
      MatchesRemoveCapture(body, str, cp, j);        // Matches(body) <==> Matches(rcb)
      MatchesReverseRE(rer, rcb, str, cp, j);
      assert OB.Matches(rrb, rstr, n - j, MIR.Mirror(cp, n));
      OB.MatchesToReachesWrite(rrb, lid, rstr, n - j, MIR.Mirror(cp, n));
    }
  }
}
