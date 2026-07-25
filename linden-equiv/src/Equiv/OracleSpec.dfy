// Lookaround campaign (L1), §6.4 glue of LOOKAROUND_CAMPAIGN.md: the seam
// between the engine-side span predicate and the spec-side one.
//
// C4 ended at OracleColumnCharacterized: the oracle bit at (cp, lid) holds iff
// `RecorderHit(body, str, cp)` — some span of `str` ending at cp is matched by
// the body, stated with OracleBridge's `Matches` over the RegElk AST. C5 ended
// at SpanDualityComplete/SpanDualitySound: a backward walk of a Linden `Regex`
// from cp succeeds iff `MatchesL` holds of some span ending at cp. The two
// speak different ASTs; this file transfers between them.
//
// The transfer is lighter than §6.4 anticipated: `Matches` and `MatchesL` are
// BOTH transparent on captures (`Re_capture` / `Group` just recurse), so the
// induction needs no capture-freedom hypothesis and covers the whole RegElk
// AST. Capture-freedom is needed only to feed the duality its `GroupFreeL`
// precondition (CaptureFreeGroupFreeL below).

include "OracleDecomp.dfy"

/** §6.4 glue: `Matches` (RegElk AST) ⟺ `MatchesL` (translated Linden AST). */
module LindenElkOracleSpec {
  import opened Std.Wrappers
  import R = RegElkRegex
  import RA = Anchors
  import AI = ArrayInterp
  import CP = Compiler
  import LOr = Oracle
  import LW = WarblreRegExpRecord
  import LN = WarblreNumeric
  import L = Regex
  import LG = Groups
  import LS = Semantics
  import WP = WarblrePrimitives
  import LT = LindenElkLookTables
  import NR = LindenElkNfaRep
  import T = LindenElkTranslate
  import SD = LindenSpanDuality
  import OB = LindenElkOracleBridge
  import OD = LindenElkOracleDecomp
  import ORc = LindenElkOracleReach

  // ===========================================================================
  // Definitional agreement at a position
  // ===========================================================================

  /** The position contexts agree: RegElk's `cp_context` at an in-range
      position reads exactly the neighbours `T.CpContext` reads. Definitional
      (both are built from `get_char`), but stated once so the anchor case of
      the transfer does not re-derive it. */
  lemma CtxAtAgree(str: string, cp: int)
    requires 0 <= cp <= |str|
    ensures ORc.CtxAt(str, cp) == T.CpContext(str, cp as nat, RA.Forward)
  {
  }

  // ===========================================================================
  // Inversion helpers for the two branching arms
  // ===========================================================================
  // Both span predicates match on their AST, and across a module boundary that
  // unfold does not fire inside a lemma's branch — `var m :| ...` reports
  // "cannot establish the existence of LHS values". Taking the predicate as a
  // PRECONDITION over the syntactic constructor makes it fire (the idiom of
  // NR.NfaRepREQuantInv). The intro directions need no such help.

  /** Inversion for `Matches`'s concatenation arm: recover the split point. */
  lemma MatchesConInv(r1: R.regex, r2: R.regex, str: string, i: int, j: int)
    returns (m: int)
    requires OB.Matches(R.Re_con(r1, r2), str, i, j)
    ensures OB.Matches(r1, str, i, m) && OB.Matches(r2, str, m, j)
  {
    m :| OB.Matches(r1, str, i, m) && OB.Matches(r2, str, m, j);
  }

  /** Inversion for `Matches`'s quantifier arm: recover the iteration count. */
  lemma MatchesQuantInv(nul: R.nullability, qid: R.quantid, q: R.counted_quantifier,
                        r1: R.regex, str: string, i: int, j: int) returns (k: nat)
    requires OB.Matches(R.Re_quant(nul, qid, q, r1), str, i, j)
    ensures q.min <= k && (q.max.Some? ==> k <= q.max.value)
    ensures OB.MatchesIter(r1, k, str, i, j)
  {
    k :| q.min <= k && (q.max.Some? ==> k <= q.max.value)
      && OB.MatchesIter(r1, k, str, i, j);
  }

  /** Inversion for `MatchesL`'s sequence arm. */
  lemma MatchesLSeqInv(rer: LW.RegExpRecord, ra: L.Regex, rb: L.Regex,
                       str: string, i: int, j: int) returns (m: int)
    requires SD.MatchesL(rer, L.Sequence(ra, rb), str, i, j)
    ensures SD.MatchesL(rer, ra, str, i, m) && SD.MatchesL(rer, rb, str, m, j)
  {
    m :| SD.MatchesL(rer, ra, str, i, m) && SD.MatchesL(rer, rb, str, m, j);
  }

  /** Inversion for `MatchesL`'s quantifier arm. */
  lemma MatchesLQuantInv(rer: LW.RegExpRecord, greedy: bool, min: nat, delta: LN.NoI,
                         r1: L.Regex, str: string, i: int, j: int) returns (k: nat)
    requires SD.MatchesL(rer, L.Quantified(greedy, min, delta, r1), str, i, j)
    ensures min <= k && (match delta case Inf => true case NN(dx) => k <= min + dx)
    ensures SD.IterL(rer, r1, k, str, i, j)
  {
    k :| min <= k && (match delta case Inf => true case NN(dx) => k <= min + dx)
      && SD.IterL(rer, r1, k, str, i, j);
  }

  // ===========================================================================
  // (b) The transfer: Matches ⟺ MatchesL ∘ Translate
  // ===========================================================================

  /** THE transfer lemma: the engine-side span predicate over a RegElk AST and
      the spec-side one over its translation are the same relation, on in-range
      spans. Structural induction; the only non-definitional cases are
      characters (`CharSemAgree`) and anchors (`AnchorSemAgree`), which is why
      the fixed record must be case-sensitive and non-multiline.

      Captures need no hypothesis: both predicates recurse straight through
      `Re_capture` / `Group`. Lookarounds are `false` on both sides. */
  lemma MatchesTransfer(rer: LW.RegExpRecord, re: R.regex, str: string, i: int, j: int)
    requires !rer.ignoreCase && !rer.multiline
    requires T.TransWf(re)
    requires 0 <= i <= j <= |str|
    ensures OB.Matches(re, str, i, j) <==> SD.MatchesL(rer, T.Translate(re), str, i, j)
    decreases CP.rsize(re), 0, 0
  {
    match re
    case Re_empty =>
    case Re_character(ch) =>
      if j == i + 1 {
        // In range because j <= |str|: the character read is Some(str[i]).
        assert 0 <= i < |str|;
        assert AI.get_char(str, i) == Some(str[i]);
        T.CharSemAgree(rer, ch, str[i]);
      }
    case Re_anchor(a) =>
      if i == j {
        CtxAtAgree(str, i);
        T.AnchorSemAgree(rer, a, str, i as nat, RA.Forward);
      }
    case Re_alt(r1, r2) =>
      MatchesTransfer(rer, r1, str, i, j);
      MatchesTransfer(rer, r2, str, i, j);
    case Re_con(r1, r2) =>
      assert T.Translate(re) == L.Sequence(T.Translate(r1), T.Translate(r2));
      if OB.Matches(re, str, i, j) {
        var m := MatchesConInv(r1, r2, str, i, j);
        OB.MatchesBounds(r1, str, i, m);
        OB.MatchesBounds(r2, str, m, j);
        MatchesTransfer(rer, r1, str, i, m);
        MatchesTransfer(rer, r2, str, m, j);
        assert SD.MatchesL(rer, T.Translate(r1), str, i, m)
            && SD.MatchesL(rer, T.Translate(r2), str, m, j);
      }
      if SD.MatchesL(rer, T.Translate(re), str, i, j) {
        var m := MatchesLSeqInv(rer, T.Translate(r1), T.Translate(r2), str, i, j);
        SD.MatchesLBounds(rer, T.Translate(r1), str, i, m);
        SD.MatchesLBounds(rer, T.Translate(r2), str, m, j);
        MatchesTransfer(rer, r1, str, i, m);
        MatchesTransfer(rer, r2, str, m, j);
        assert OB.Matches(r1, str, i, m) && OB.Matches(r2, str, m, j);
      }
    case Re_quant(nul, qid, q, r1) =>
      // The bound arithmetic lines up: `min` carries across as `q.min as nat`,
      // and TrDelta turns `max` into the offset (max - min), so Linden's
      // `k <= min + dx` is exactly RegElk's `k <= q.max.value`.
      var tq := T.Translate(re);
      assert tq == L.Quantified(q.greedy, q.min as nat, T.TrDelta(q), T.Translate(r1));
      if OB.Matches(re, str, i, j) {
        var k := MatchesQuantInv(nul, qid, q, r1, str, i, j);
        MatchesIterTransfer(rer, r1, k, str, i, j);
        assert SD.IterL(rer, T.Translate(r1), k, str, i, j);
        assert (q.min as nat) <= k;
        assert match T.TrDelta(q) case Inf => true case NN(dx) => k <= (q.min as nat) + dx;
        assert SD.MatchesL(rer, tq, str, i, j);
      }
      if SD.MatchesL(rer, tq, str, i, j) {
        var k := MatchesLQuantInv(rer, q.greedy, q.min as nat, T.TrDelta(q),
                                  T.Translate(r1), str, i, j);
        MatchesIterTransfer(rer, r1, k, str, i, j);
        assert OB.MatchesIter(r1, k, str, i, j);
        assert q.min <= k;
        assert q.max.Some? ==> k <= q.max.value;
        assert OB.Matches(re, str, i, j);
      }
    case Re_capture(cid, r1) =>
      MatchesTransfer(rer, r1, str, i, j);
    case Re_lookaround(_, _, _) =>
  }

  /** The iteration-chain half of the transfer, by induction on the counter. */
  lemma MatchesIterTransfer(rer: LW.RegExpRecord, r: R.regex, k: nat,
                            str: string, i: int, j: int)
    requires !rer.ignoreCase && !rer.multiline
    requires T.TransWf(r)
    requires 0 <= i <= j <= |str|
    ensures OB.MatchesIter(r, k, str, i, j)
        <==> SD.IterL(rer, T.Translate(r), k, str, i, j)
    decreases CP.rsize(r), 1, k
  {
    if k > 0 {
      if OB.MatchesIter(r, k, str, i, j) {
        var m := OB.MatchesIterHead(r, k, str, i, j);
        OB.MatchesBounds(r, str, i, m);
        OB.MatchesIterBounds(r, k - 1, str, m, j);
        MatchesTransfer(rer, r, str, i, m);
        MatchesIterTransfer(rer, r, k - 1, str, m, j);
        assert SD.MatchesL(rer, T.Translate(r), str, i, m)
            && SD.IterL(rer, T.Translate(r), k - 1, str, m, j);
      }
      if SD.IterL(rer, T.Translate(r), k, str, i, j) {
        var m := SD.IterLHead(rer, T.Translate(r), k, str, i, j);
        SD.MatchesLBounds(rer, T.Translate(r), str, i, m);
        SD.IterLBounds(rer, T.Translate(r), k - 1, str, m, j);
        MatchesTransfer(rer, r, str, i, m);
        MatchesIterTransfer(rer, r, k - 1, str, m, j);
        assert OB.Matches(r, str, i, m) && OB.MatchesIter(r, k - 1, str, m, j);
      }
    }
  }

  // ===========================================================================
  // Capture-freedom feeds the duality its GroupFreeL precondition
  // ===========================================================================

  /** A capture-free, look-free RegElk body translates group-free: `Group`
      comes only from `Re_capture` and `LookaroundR` only from
      `Re_lookaround`, and `Translate` never emits `Backreference` at all. */
  lemma CaptureFreeGroupFreeL(re: R.regex)
    requires T.TransWf(re)
    requires NR.CaptureFreeRE(re) && NR.LookFreeRE(re)
    ensures SD.GroupFreeL(T.Translate(re))
    decreases re
  {
    match re
    case Re_alt(r1, r2) =>
      CaptureFreeGroupFreeL(r1); CaptureFreeGroupFreeL(r2);
    case Re_con(r1, r2) =>
      CaptureFreeGroupFreeL(r1); CaptureFreeGroupFreeL(r2);
    case Re_quant(_, _, _, r1) => CaptureFreeGroupFreeL(r1);
    case _ =>
  }

  // ===========================================================================
  // (c) The oracle column, spec-side: the StaticOkRE conjunct §6.5 consumes
  // ===========================================================================

  /** THE §6.4 payoff: an oracle column of the build sweep holds exactly the
      positions where the SPEC's backward walk of the (translated) lookbehind
      body succeeds. Chains the three campaign capstones —
      `OracleColumnCharacterized` (C4: the bit is a `Matches` span ending at
      cp), `MatchesTransfer` (this file: that span is a `MatchesL` span), and
      `SpanDualityComplete`/`SpanDualitySound` (C5: such a span exists iff the
      backward walk succeeds).

      Note the bit encodes the POSITIVE body-match question for both flavours;
      `NegCheckOracle` inverts at the gate, which is why `la` may be either
      lookbehind form here. `gm` is irrelevant on the right (the body is
      capture-free, hence group-free after translation), so the statement holds
      for every group map. */
  lemma OracleColumnSpec(rer: LW.RegExpRecord, re: R.regex, str: string,
                         lid: R.lookid, la: R.lookaround, body: R.regex,
                         cp: int, gm: LG.GroupMap)
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
        <==> SD.SuccActs(rer, [LS.Areg(T.Translate(body))],
                         T.InputAt(str, cp), gm, WP.Backward)
  {
    OD.OracleColumnCharacterized(re, str, lid, la, body, cp);
    CaptureFreeGroupFreeL(body);
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
