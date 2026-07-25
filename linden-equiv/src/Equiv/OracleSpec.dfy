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
    case Re_lookaround(lid, lk, r1) =>
      assert !OB.Matches(re, str, i, j);
      assert T.Translate(re) == L.LookaroundR(T.TrLookaround(lk), T.Translate(r1));
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
}
