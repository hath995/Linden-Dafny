// Phase 4a: representation predicates relating RegElk's compiled bytecode to
// the (annotated) regex it was compiled from — the port of Linden's proven
// Engine/NFA.dfy rep-predicate layer onto RegElk's compiler.
//
// Scope: the star fragment (Phase 4) — empty, characters, alt, con,
// greedy/lazy star (min==0, max==None), captures. This fragment includes the
// implicit search wrapper lazy_prefix(annotate(raw)) of every fragment raw.

/** Phase 4a representation layer: relates RegElk's compiled bytecode to the Linden
    regex it was compiled from, restricted to the star fragment (`StarFragmentRE` /
    `StarFragmentRaw`). The central predicate `NfaRepRE` is the RegElk-bytecode port of
    Linden's proven `Engine/NFA.dfy` representation predicate. */
include "LookTables.dfy"
include "OracleSweep.dfy"

module LindenElkNfaRep {
  import opened Std.Wrappers
  import R = RegElkRegex
  import RC = Charclasses
  import RB = Bytecode
  import CP = Compiler
  import T = LindenElkTranslate
  import LTB = LindenElkLookTables
  import OS = LindenElkOracleSweep

  // ===========================================================================
  // The Phase-4 fragment
  // ===========================================================================

  /** The Phase-4 "star fragment" of translated regexes: empty, characters,
      alternation, concatenation, unbounded (`min==0`, `max==None`) greedy/lazy star,
      and captures — the shapes this layer's equivalence proof currently covers.
      Lookarounds and anchors fall outside the fragment. */
  predicate StarFragmentRE(re: R.regex)
    decreases re
  {
    match re
    case Re_empty => true
    case Re_character(_) => true
    case Re_alt(r1, r2) => StarFragmentRE(r1) && StarFragmentRE(r2)
    case Re_con(r1, r2) => StarFragmentRE(r1) && StarFragmentRE(r2)
    case Re_quant(nul, qid, q, r1) => q.min == 0 && q.max == None && StarFragmentRE(r1)
    case Re_capture(cid, r1) => StarFragmentRE(r1)
    case Re_lookaround(_, _, _) => false
    case Re_anchor(_) => false
  }

  /** The `raw_regex` (pre-annotation) counterpart of `StarFragmentRE`, checked before
      compilation/annotation assigns pcs, capture ids and quantifier ids. */
  predicate StarFragmentRaw(raw: R.raw_regex)
    decreases raw
  {
    match raw
    case Raw_empty => true
    case Raw_character(_) => true
    case Raw_alt(r1, r2) => StarFragmentRaw(r1) && StarFragmentRaw(r2)
    case Raw_con(r1, r2) => StarFragmentRaw(r1) && StarFragmentRaw(r2)
    case Raw_quant(q, r1) => (q.Star? || q.LazyStar?) && StarFragmentRaw(r1)
    case Raw_count(q, r1) => q.min == 0 && q.max == None && StarFragmentRaw(r1)
    case Raw_capture(r1) => StarFragmentRaw(r1)
    case Raw_lookaround(_, _) => false
    case Raw_anchor(_) => false
  }

  /** Annotating a raw regex that is in the star fragment (`StarFragmentRaw`) produces
      an annotated regex still in the fragment (`StarFragmentRE`) — annotation only
      assigns ids, it never changes shape. */
  lemma AnnotateStarFragment(ra: R.raw_regex, c: int, l: int, q: int)
    requires StarFragmentRaw(ra)
    ensures StarFragmentRE(R.annotate_regex(ra, c, l, q).0)
    decreases ra
  {
    match ra
    case Raw_empty =>
    case Raw_character(_) =>
    case Raw_alt(r1, r2) =>
      AnnotateStarFragment(r1, c, l, q);
      var (_, c1, l1, q1) := R.annotate_regex(r1, c, l, q);
      AnnotateStarFragment(r2, c1, l1, q1);
    case Raw_con(r1, r2) =>
      AnnotateStarFragment(r1, c, l, q);
      var (_, c1, l1, q1) := R.annotate_regex(r1, c, l, q);
      AnnotateStarFragment(r2, c1, l1, q1);
    case Raw_quant(quant, r1) =>
      AnnotateStarFragment(r1, c, l, q + 1);
    case Raw_count(quant, r1) =>
      AnnotateStarFragment(r1, c, l, q + 1);
    case Raw_capture(r1) =>
      AnnotateStarFragment(r1, c + 1, l, q);
    case Raw_lookaround(_, _) =>
    case Raw_anchor(_) =>
  }

  // The full spec-side regex of a fragment raw is in the fragment.
  /** What actually gets compiled — `lazy_prefix(annotate(raw))` — stays in the star
      fragment whenever the input `raw` is. */
  lemma SpecRegexStarFragment(raw: R.raw_regex)
    requires StarFragmentRaw(raw)
    ensures StarFragmentRE(R.lazy_prefix(R.annotate(raw)))
  {
    AnnotateStarFragment(R.Raw_capture(raw), 0, 1, 1);
  }


  /** The anchor fragment: the star fragment plus anchors (`^ $ \b \B`) — the
      next fragment on LIBRARY_PLAN §7's growth path. The NfaRep layer below is
      proven against THIS fragment; the downstream simulation layers still gate
      on `StarFragmentRE` and widen file by file. */
  predicate AnchorFragmentRE(re: R.regex)
    decreases re
  {
    match re
    case Re_empty => true
    case Re_character(_) => true
    case Re_anchor(_) => true
    case Re_alt(r1, r2) => AnchorFragmentRE(r1) && AnchorFragmentRE(r2)
    case Re_con(r1, r2) => AnchorFragmentRE(r1) && AnchorFragmentRE(r2)
    case Re_quant(nul, qid, q, r1) => q.min == 0 && q.max == None && AnchorFragmentRE(r1)
    case Re_capture(cid, r1) => AnchorFragmentRE(r1)
    case Re_lookaround(_, _, _) => false
  }

  /** The `raw_regex` counterpart of `AnchorFragmentRE`. */
  predicate AnchorFragmentRaw(raw: R.raw_regex)
    decreases raw
  {
    match raw
    case Raw_empty => true
    case Raw_character(_) => true
    case Raw_anchor(_) => true
    case Raw_alt(r1, r2) => AnchorFragmentRaw(r1) && AnchorFragmentRaw(r2)
    case Raw_con(r1, r2) => AnchorFragmentRaw(r1) && AnchorFragmentRaw(r2)
    case Raw_quant(q, r1) => (q.Star? || q.LazyStar?) && AnchorFragmentRaw(r1)
    case Raw_count(q, r1) => q.min == 0 && q.max == None && AnchorFragmentRaw(r1)
    case Raw_capture(r1) => AnchorFragmentRaw(r1)
    case Raw_lookaround(_, _) => false
  }

  /** The star fragment embeds in the anchor fragment. */
  lemma StarIsAnchorFragmentRE(re: R.regex)
    requires StarFragmentRE(re)
    ensures AnchorFragmentRE(re)
    decreases re
  {
    match re
    case Re_alt(r1, r2) => StarIsAnchorFragmentRE(r1); StarIsAnchorFragmentRE(r2);
    case Re_con(r1, r2) => StarIsAnchorFragmentRE(r1); StarIsAnchorFragmentRE(r2);
    case Re_quant(_, _, _, r1) => StarIsAnchorFragmentRE(r1);
    case Re_capture(_, r1) => StarIsAnchorFragmentRE(r1);
    case _ =>
  }

  /** The raw star fragment embeds in the raw anchor fragment. */
  lemma StarIsAnchorFragmentRaw(ra: R.raw_regex)
    requires StarFragmentRaw(ra)
    ensures AnchorFragmentRaw(ra)
    decreases ra
  {
    match ra
    case Raw_alt(r1, r2) => StarIsAnchorFragmentRaw(r1); StarIsAnchorFragmentRaw(r2);
    case Raw_con(r1, r2) => StarIsAnchorFragmentRaw(r1); StarIsAnchorFragmentRaw(r2);
    case Raw_quant(_, r1) => StarIsAnchorFragmentRaw(r1);
    case Raw_count(_, r1) => StarIsAnchorFragmentRaw(r1);
    case Raw_capture(r1) => StarIsAnchorFragmentRaw(r1);
    case _ =>
  }

  /** Annotation preserves the anchor fragment. */
  lemma AnnotateAnchorFragment(ra: R.raw_regex, c: int, l: int, q: int)
    requires AnchorFragmentRaw(ra)
    ensures AnchorFragmentRE(R.annotate_regex(ra, c, l, q).0)
    decreases ra
  {
    match ra
    case Raw_alt(r1, r2) =>
      AnnotateAnchorFragment(r1, c, l, q);
      var (_, c1, l1, q1) := R.annotate_regex(r1, c, l, q);
      AnnotateAnchorFragment(r2, c1, l1, q1);
    case Raw_con(r1, r2) =>
      AnnotateAnchorFragment(r1, c, l, q);
      var (_, c1, l1, q1) := R.annotate_regex(r1, c, l, q);
      AnnotateAnchorFragment(r2, c1, l1, q1);
    case Raw_quant(quant, r1) => AnnotateAnchorFragment(r1, c, l, q + 1);
    case Raw_count(quant, r1) => AnnotateAnchorFragment(r1, c, l, q + 1);
    case Raw_capture(r1) => AnnotateAnchorFragment(r1, c + 1, l, q);
    case _ =>
  }

  /** `lazy_prefix(annotate(raw))` stays in the anchor fragment. */
  lemma SpecRegexAnchorFragment(raw: R.raw_regex)
    requires AnchorFragmentRaw(raw)
    ensures AnchorFragmentRE(R.lazy_prefix(R.annotate(raw)))
  {
    AnnotateAnchorFragment(R.Raw_capture(raw), 0, 1, 1);
  }

  /** The quantifier fragment: the anchor fragment plus general quantifiers
      whose compilation goes through the compiler's GENERIC `repeat_min` /
      `repeat_optional` schemes: `min == 0` with unbounded max (the star), or
      bounded `{min,max}` (which subsumes `?`, `{n}`, `{n,m}`, `{0,m}`).
      Unbounded `min > 0` quantifiers (`+`, `{n,}`) are excluded: the compiler
      gives them SPECIAL schemes (the last-repetition-loop for NonNullable
      bodies, the CheckNullable end-fork layouts for greedy nullable bodies)
      whose simulation proofs are separate follow-up campaigns. */
  predicate QuantFragmentRE(re: R.regex)
    decreases re
  {
    match re
    case Re_empty => true
    case Re_character(_) => true
    case Re_anchor(_) => true
    case Re_alt(r1, r2) => QuantFragmentRE(r1) && QuantFragmentRE(r2)
    case Re_con(r1, r2) => QuantFragmentRE(r1) && QuantFragmentRE(r2)
    case Re_quant(nul, qid, q, r1) =>
      ((q.min == 0 && q.max == None)
       || (0 <= q.min && q.max.Some? && q.min <= q.max.value))
      && QuantFragmentRE(r1)
    case Re_capture(cid, r1) => QuantFragmentRE(r1)
    case Re_lookaround(_, _, _) => false
  }

  /** The `raw_regex` counterpart of `QuantFragmentRE`: quantifier shorthands
      other than `+` (`*`, `?` and their lazy forms) and bounded counted
      repetitions. */
  predicate QuantFragmentRaw(raw: R.raw_regex)
    decreases raw
  {
    match raw
    case Raw_empty => true
    case Raw_character(_) => true
    case Raw_anchor(_) => true
    case Raw_alt(r1, r2) => QuantFragmentRaw(r1) && QuantFragmentRaw(r2)
    case Raw_con(r1, r2) => QuantFragmentRaw(r1) && QuantFragmentRaw(r2)
    case Raw_quant(q, r1) => !q.Plus? && !q.LazyPlus? && QuantFragmentRaw(r1)
    case Raw_count(q, r1) =>
      ((q.min == 0 && q.max == None)
       || (0 <= q.min && q.max.Some? && q.min <= q.max.value))
      && QuantFragmentRaw(r1)
    case Raw_capture(r1) => QuantFragmentRaw(r1)
    case Raw_lookaround(_, _) => false
  }

  /** The anchor fragment embeds in the quantifier fragment. */
  lemma AnchorIsQuantFragmentRE(re: R.regex)
    requires AnchorFragmentRE(re)
    ensures QuantFragmentRE(re)
    decreases re
  {
    match re
    case Re_alt(r1, r2) => AnchorIsQuantFragmentRE(r1); AnchorIsQuantFragmentRE(r2);
    case Re_con(r1, r2) => AnchorIsQuantFragmentRE(r1); AnchorIsQuantFragmentRE(r2);
    case Re_quant(_, _, _, r1) => AnchorIsQuantFragmentRE(r1);
    case Re_capture(_, r1) => AnchorIsQuantFragmentRE(r1);
    case _ =>
  }

  /** The raw anchor fragment embeds in the raw quantifier fragment. */
  lemma AnchorIsQuantFragmentRaw(ra: R.raw_regex)
    requires AnchorFragmentRaw(ra)
    ensures QuantFragmentRaw(ra)
    decreases ra
  {
    match ra
    case Raw_alt(r1, r2) => AnchorIsQuantFragmentRaw(r1); AnchorIsQuantFragmentRaw(r2);
    case Raw_con(r1, r2) => AnchorIsQuantFragmentRaw(r1); AnchorIsQuantFragmentRaw(r2);
    case Raw_quant(_, r1) => AnchorIsQuantFragmentRaw(r1);
    case Raw_count(_, r1) => AnchorIsQuantFragmentRaw(r1);
    case Raw_capture(r1) => AnchorIsQuantFragmentRaw(r1);
    case _ =>
  }

  /** Annotation preserves the quantifier fragment: `quant_canonicalize` sends
      the allowed shorthands to `min == 0` quantifiers (unbounded for `*`,
      `{0,1}` for `?`), and `Raw_count` bounds carry over verbatim. */
  lemma AnnotateQuantFragment(ra: R.raw_regex, c: int, l: int, q: int)
    requires QuantFragmentRaw(ra)
    ensures QuantFragmentRE(R.annotate_regex(ra, c, l, q).0)
    decreases ra
  {
    match ra
    case Raw_alt(r1, r2) =>
      AnnotateQuantFragment(r1, c, l, q);
      var (_, c1, l1, q1) := R.annotate_regex(r1, c, l, q);
      AnnotateQuantFragment(r2, c1, l1, q1);
    case Raw_con(r1, r2) =>
      AnnotateQuantFragment(r1, c, l, q);
      var (_, c1, l1, q1) := R.annotate_regex(r1, c, l, q);
      AnnotateQuantFragment(r2, c1, l1, q1);
    case Raw_quant(quant, r1) => AnnotateQuantFragment(r1, c, l, q + 1);
    case Raw_count(quant, r1) => AnnotateQuantFragment(r1, c, l, q + 1);
    case Raw_capture(r1) => AnnotateQuantFragment(r1, c + 1, l, q);
    case _ =>
  }

  /** `lazy_prefix(annotate(raw))` stays in the quantifier fragment. */
  lemma SpecRegexQuantFragment(raw: R.raw_regex)
    requires QuantFragmentRaw(raw)
    ensures QuantFragmentRE(R.lazy_prefix(R.annotate(raw)))
  {
    AnnotateQuantFragment(R.Raw_capture(raw), 0, 1, 1);
  }

  /** The plus fragment: the quantifier fragment plus unbounded `min > 0`
      quantifiers (`+`, `{n,}`) whose bodies the annotator marked
      `NonNullable` — exactly the shapes the compiler gives its
      "last repetition is the final loop" do-while scheme
      (Compiler.dfy:107-112). The greedy-nullable CheckNullable schemes
      remain excluded. */
  predicate PlusFragmentRE(re: R.regex)
    decreases re
  {
    match re
    case Re_empty => true
    case Re_character(_) => true
    case Re_anchor(_) => true
    case Re_alt(r1, r2) => PlusFragmentRE(r1) && PlusFragmentRE(r2)
    case Re_con(r1, r2) => PlusFragmentRE(r1) && PlusFragmentRE(r2)
    case Re_quant(nul, qid, q, r1) =>
      ((q.min == 0 && q.max == None)
       || (0 <= q.min && q.max.Some? && q.min <= q.max.value)
       || (q.min > 0 && q.max == None && nul == R.NonNullable
           && R.nullable(r1) == R.NonNullable))
      && PlusFragmentRE(r1)
    case Re_capture(cid, r1) => PlusFragmentRE(r1)
    case Re_lookaround(_, _, _) => false
  }

  /** The `raw_regex` counterpart of `PlusFragmentRE`: `+`/`{n,}` admitted
      when the body's raw nullability is `NonNullable` (an executable
      check — `raw_nullable` is a plain function). */
  predicate PlusFragmentRaw(raw: R.raw_regex)
    decreases raw
  {
    match raw
    case Raw_empty => true
    case Raw_character(_) => true
    case Raw_anchor(_) => true
    case Raw_alt(r1, r2) => PlusFragmentRaw(r1) && PlusFragmentRaw(r2)
    case Raw_con(r1, r2) => PlusFragmentRaw(r1) && PlusFragmentRaw(r2)
    case Raw_quant(q, r1) =>
      ((q.Plus? || q.LazyPlus?) ==> R.raw_nullable(r1) == R.NonNullable)
      && PlusFragmentRaw(r1)
    case Raw_count(q, r1) =>
      ((q.min == 0 && q.max == None)
       || (0 <= q.min && q.max.Some? && q.min <= q.max.value)
       || (q.min > 0 && q.max == None && R.raw_nullable(r1) == R.NonNullable))
      && PlusFragmentRaw(r1)
    case Raw_capture(r1) => PlusFragmentRaw(r1)
    case Raw_lookaround(_, _) => false
  }

  /** The quantifier fragment embeds in the plus fragment. */
  lemma QuantIsPlusFragmentRE(re: R.regex)
    requires QuantFragmentRE(re)
    ensures PlusFragmentRE(re)
    decreases re
  {
    match re
    case Re_alt(r1, r2) => QuantIsPlusFragmentRE(r1); QuantIsPlusFragmentRE(r2);
    case Re_con(r1, r2) => QuantIsPlusFragmentRE(r1); QuantIsPlusFragmentRE(r2);
    case Re_quant(_, _, _, r1) => QuantIsPlusFragmentRE(r1);
    case Re_capture(_, r1) => QuantIsPlusFragmentRE(r1);
    case _ =>
  }

  /** The raw quantifier fragment embeds in the raw plus fragment. */
  lemma QuantIsPlusFragmentRaw(ra: R.raw_regex)
    requires QuantFragmentRaw(ra)
    ensures PlusFragmentRaw(ra)
    decreases ra
  {
    match ra
    case Raw_alt(r1, r2) => QuantIsPlusFragmentRaw(r1); QuantIsPlusFragmentRaw(r2);
    case Raw_con(r1, r2) => QuantIsPlusFragmentRaw(r1); QuantIsPlusFragmentRaw(r2);
    case Raw_quant(_, r1) => QuantIsPlusFragmentRaw(r1);
    case Raw_count(_, r1) => QuantIsPlusFragmentRaw(r1);
    case Raw_capture(r1) => QuantIsPlusFragmentRaw(r1);
    case _ =>
  }

  /** Annotation computes exactly the raw nullability: `annotate_regex` only
      assigns ids, and `nullable` mirrors `raw_nullable` structurally. */
  lemma AnnotateNullable(ra: R.raw_regex, c: int, l: int, q: int)
    ensures R.nullable(R.annotate_regex(ra, c, l, q).0) == R.raw_nullable(ra)
    decreases ra
  {
    match ra
    case Raw_empty =>
    case Raw_character(_) =>
    case Raw_anchor(_) =>
    case Raw_alt(r1, r2) =>
      AnnotateNullable(r1, c, l, q);
      var (_, c1, l1, q1) := R.annotate_regex(r1, c, l, q);
      AnnotateNullable(r2, c1, l1, q1);
    case Raw_con(r1, r2) =>
      AnnotateNullable(r1, c, l, q);
      var (_, c1, l1, q1) := R.annotate_regex(r1, c, l, q);
      AnnotateNullable(r2, c1, l1, q1);
    case Raw_quant(quant, r1) =>
      AnnotateNullable(r1, c, l, q + 1);
    case Raw_count(quant, r1) =>
      AnnotateNullable(r1, c, l, q + 1);
    case Raw_capture(r1) =>
      AnnotateNullable(r1, c + 1, l, q);
    case Raw_lookaround(_, _) =>
  }

  /** Annotation preserves the plus fragment: the annotator's cached `nul`
      IS `nullable(ar1)`, which `AnnotateNullable` ties to the raw check. */
  lemma AnnotatePlusFragment(ra: R.raw_regex, c: int, l: int, q: int)
    requires PlusFragmentRaw(ra)
    ensures PlusFragmentRE(R.annotate_regex(ra, c, l, q).0)
    decreases ra
  {
    match ra
    case Raw_alt(r1, r2) =>
      AnnotatePlusFragment(r1, c, l, q);
      var (_, c1, l1, q1) := R.annotate_regex(r1, c, l, q);
      AnnotatePlusFragment(r2, c1, l1, q1);
    case Raw_con(r1, r2) =>
      AnnotatePlusFragment(r1, c, l, q);
      var (_, c1, l1, q1) := R.annotate_regex(r1, c, l, q);
      AnnotatePlusFragment(r2, c1, l1, q1);
    case Raw_quant(quant, r1) =>
      AnnotatePlusFragment(r1, c, l, q + 1);
      AnnotateNullable(r1, c, l, q + 1);
    case Raw_count(quant, r1) =>
      AnnotatePlusFragment(r1, c, l, q + 1);
      AnnotateNullable(r1, c, l, q + 1);
    case Raw_capture(r1) =>
      AnnotatePlusFragment(r1, c + 1, l, q);
    case _ =>
  }

  /** `lazy_prefix(annotate(raw))` stays in the plus fragment. */
  lemma SpecRegexPlusFragment(raw: R.raw_regex)
    requires PlusFragmentRaw(raw)
    ensures PlusFragmentRE(R.lazy_prefix(R.annotate(raw)))
  {
    AnnotatePlusFragment(R.Raw_capture(raw), 0, 1, 1);
  }

  // ===========================================================================
  // The lookbehind fragment: the plus fragment extended with capture-free,
  // non-nested lookbehinds (`(?<=...)`, `(?<!...)`). Their oracle build
  // passes run FORWARD over the (capture-free) body — `oracle_regex` for a
  // lookbehind is `lazy_prefix(remove_capture(body))` with no reversal — so
  // the existing forward pipeline covers the build bytecode, while the main
  // pass sees a single zero-width oracle-consulting instruction, anchor-like.
  // ===========================================================================

  /** No `Re_capture` node anywhere in `re`. Capture-free lookaround bodies
      expose no groups, so a positive lookaround's `LkResult` returns the
      group map unchanged — the LK wrapper is leaf-transparent. */
  predicate CaptureFreeRE(re: R.regex)
    decreases re
  {
    match re
    case Re_empty => true
    case Re_character(_) => true
    case Re_anchor(_) => true
    case Re_alt(r1, r2) => CaptureFreeRE(r1) && CaptureFreeRE(r2)
    case Re_con(r1, r2) => CaptureFreeRE(r1) && CaptureFreeRE(r2)
    case Re_quant(_, _, _, r1) => CaptureFreeRE(r1)
    case Re_capture(_, _) => false
    case Re_lookaround(_, _, r1) => CaptureFreeRE(r1)
  }

  /** No `Re_lookaround` node anywhere in `re` — lookaround bodies in the
      lookbehind fragment are non-nested. */
  predicate LookFreeRE(re: R.regex)
    decreases re
  {
    match re
    case Re_empty => true
    case Re_character(_) => true
    case Re_anchor(_) => true
    case Re_alt(r1, r2) => LookFreeRE(r1) && LookFreeRE(r2)
    case Re_con(r1, r2) => LookFreeRE(r1) && LookFreeRE(r2)
    case Re_quant(_, _, _, r1) => LookFreeRE(r1)
    case Re_capture(_, r1) => LookFreeRE(r1)
    case Re_lookaround(_, _, _) => false
  }

  /** The `raw_regex` counterpart of `CaptureFreeRE`. */
  predicate CaptureFreeRaw(raw: R.raw_regex)
    decreases raw
  {
    match raw
    case Raw_empty => true
    case Raw_character(_) => true
    case Raw_anchor(_) => true
    case Raw_alt(r1, r2) => CaptureFreeRaw(r1) && CaptureFreeRaw(r2)
    case Raw_con(r1, r2) => CaptureFreeRaw(r1) && CaptureFreeRaw(r2)
    case Raw_quant(_, r1) => CaptureFreeRaw(r1)
    case Raw_count(_, r1) => CaptureFreeRaw(r1)
    case Raw_capture(_) => false
    case Raw_lookaround(_, r1) => CaptureFreeRaw(r1)
  }


  // ==========================================================================
  // (C5 scope predicates) The L4 fragment's EXECUTABLE raw-level scope — the
  // `GNotUnderQuantL` shadow ((1) no capture under a quant INSIDE look bodies,
  // (2) no capturing-look under any quant) + positive-lookbehind exclusion +
  // look-free negative bodies — with their RE twins and annotate transfers.
  // ==========================================================================

  /** RE: no capture sits under any quantifier (recursing through everything). */
  predicate NoCapUnderQuantRE(re: R.regex)
    decreases re
  {
    match re
    case Re_alt(r1, r2) => NoCapUnderQuantRE(r1) && NoCapUnderQuantRE(r2)
    case Re_con(r1, r2) => NoCapUnderQuantRE(r1) && NoCapUnderQuantRE(r2)
    case Re_quant(_, _, _, r1) => CaptureFreeRE(r1) && NoCapUnderQuantRE(r1)
    case Re_capture(_, r1) => NoCapUnderQuantRE(r1)
    case Re_lookaround(_, _, r1) => NoCapUnderQuantRE(r1)
    case _ => true
  }

  /** RE: every look body is capture-free. */
  predicate LookBodiesCaptureFreeRE(re: R.regex)
    decreases re
  {
    match re
    case Re_alt(r1, r2) => LookBodiesCaptureFreeRE(r1) && LookBodiesCaptureFreeRE(r2)
    case Re_con(r1, r2) => LookBodiesCaptureFreeRE(r1) && LookBodiesCaptureFreeRE(r2)
    case Re_quant(_, _, _, r1) => LookBodiesCaptureFreeRE(r1)
    case Re_capture(_, r1) => LookBodiesCaptureFreeRE(r1)
    case Re_lookaround(_, _, r1) => CaptureFreeRE(r1)
    case _ => true
  }

  /** RE: inside every look body, no capture under a quant. */
  predicate LookBodiesNoCapUnderQuantRE(re: R.regex)
    decreases re
  {
    match re
    case Re_alt(r1, r2) => LookBodiesNoCapUnderQuantRE(r1) && LookBodiesNoCapUnderQuantRE(r2)
    case Re_con(r1, r2) => LookBodiesNoCapUnderQuantRE(r1) && LookBodiesNoCapUnderQuantRE(r2)
    case Re_quant(_, _, _, r1) => LookBodiesNoCapUnderQuantRE(r1)
    case Re_capture(_, r1) => LookBodiesNoCapUnderQuantRE(r1)
    case Re_lookaround(_, _, r1) => NoCapUnderQuantRE(r1)
    case _ => true
  }

  /** RE: every quantifier body's look bodies are capture-free. */
  predicate QuantsLookCapFreeRE(re: R.regex)
    decreases re
  {
    match re
    case Re_alt(r1, r2) => QuantsLookCapFreeRE(r1) && QuantsLookCapFreeRE(r2)
    case Re_con(r1, r2) => QuantsLookCapFreeRE(r1) && QuantsLookCapFreeRE(r2)
    case Re_quant(_, _, _, r1) => LookBodiesCaptureFreeRE(r1) && QuantsLookCapFreeRE(r1)
    case Re_capture(_, r1) => QuantsLookCapFreeRE(r1)
    case Re_lookaround(_, _, r1) => QuantsLookCapFreeRE(r1)
    case _ => true
  }

  /** RAW twins. */
  predicate NoCapUnderQuantRaw(ra: R.raw_regex)
    decreases ra
  {
    match ra
    case Raw_alt(r1, r2) => NoCapUnderQuantRaw(r1) && NoCapUnderQuantRaw(r2)
    case Raw_con(r1, r2) => NoCapUnderQuantRaw(r1) && NoCapUnderQuantRaw(r2)
    case Raw_quant(_, r1) => CaptureFreeRaw(r1) && NoCapUnderQuantRaw(r1)
    case Raw_count(_, r1) => CaptureFreeRaw(r1) && NoCapUnderQuantRaw(r1)
    case Raw_capture(r1) => NoCapUnderQuantRaw(r1)
    case Raw_lookaround(_, r1) => NoCapUnderQuantRaw(r1)
    case _ => true
  }

  predicate LookBodiesCaptureFreeRaw(ra: R.raw_regex)
    decreases ra
  {
    match ra
    case Raw_alt(r1, r2) => LookBodiesCaptureFreeRaw(r1) && LookBodiesCaptureFreeRaw(r2)
    case Raw_con(r1, r2) => LookBodiesCaptureFreeRaw(r1) && LookBodiesCaptureFreeRaw(r2)
    case Raw_quant(_, r1) => LookBodiesCaptureFreeRaw(r1)
    case Raw_count(_, r1) => LookBodiesCaptureFreeRaw(r1)
    case Raw_capture(r1) => LookBodiesCaptureFreeRaw(r1)
    case Raw_lookaround(_, r1) => CaptureFreeRaw(r1)
    case _ => true
  }

  predicate LookBodiesNoCapUnderQuantRaw(ra: R.raw_regex)
    decreases ra
  {
    match ra
    case Raw_alt(r1, r2) => LookBodiesNoCapUnderQuantRaw(r1) && LookBodiesNoCapUnderQuantRaw(r2)
    case Raw_con(r1, r2) => LookBodiesNoCapUnderQuantRaw(r1) && LookBodiesNoCapUnderQuantRaw(r2)
    case Raw_quant(_, r1) => LookBodiesNoCapUnderQuantRaw(r1)
    case Raw_count(_, r1) => LookBodiesNoCapUnderQuantRaw(r1)
    case Raw_capture(r1) => LookBodiesNoCapUnderQuantRaw(r1)
    case Raw_lookaround(_, r1) => NoCapUnderQuantRaw(r1)
    case _ => true
  }

  predicate QuantsLookCapFreeRaw(ra: R.raw_regex)
    decreases ra
  {
    match ra
    case Raw_alt(r1, r2) => QuantsLookCapFreeRaw(r1) && QuantsLookCapFreeRaw(r2)
    case Raw_con(r1, r2) => QuantsLookCapFreeRaw(r1) && QuantsLookCapFreeRaw(r2)
    case Raw_quant(_, r1) => LookBodiesCaptureFreeRaw(r1) && QuantsLookCapFreeRaw(r1)
    case Raw_count(_, r1) => LookBodiesCaptureFreeRaw(r1) && QuantsLookCapFreeRaw(r1)
    case Raw_capture(r1) => QuantsLookCapFreeRaw(r1)
    case Raw_lookaround(_, r1) => QuantsLookCapFreeRaw(r1)
    case _ => true
  }

  /** RAW: no POSITIVE lookbehind. */
  predicate NoPosLookbehindRaw(ra: R.raw_regex)
    decreases ra
  {
    match ra
    case Raw_alt(r1, r2) => NoPosLookbehindRaw(r1) && NoPosLookbehindRaw(r2)
    case Raw_con(r1, r2) => NoPosLookbehindRaw(r1) && NoPosLookbehindRaw(r2)
    case Raw_quant(_, r1) => NoPosLookbehindRaw(r1)
    case Raw_count(_, r1) => NoPosLookbehindRaw(r1)
    case Raw_capture(r1) => NoPosLookbehindRaw(r1)
    case Raw_lookaround(look, r1) => !look.Lookbehind? && NoPosLookbehindRaw(r1)
    case _ => true
  }

  /** RAW (L5): every look inside is LOOKBEHIND-flavoured (positive or negative)
      — the v1 shape of a positive lookbehind's body (`Translate` lands in
      `SD.GroupOkLB`; the gate side `OracleColumnSpecNested` and the captures
      keystone `LkReplayMatchesSpecLBNested` both need it). */
  predicate LBOnlyLooksRaw(ra: R.raw_regex)
    decreases ra
  {
    match ra
    case Raw_alt(r1, r2) => LBOnlyLooksRaw(r1) && LBOnlyLooksRaw(r2)
    case Raw_con(r1, r2) => LBOnlyLooksRaw(r1) && LBOnlyLooksRaw(r2)
    case Raw_quant(_, r1) => LBOnlyLooksRaw(r1)
    case Raw_count(_, r1) => LBOnlyLooksRaw(r1)
    case Raw_capture(r1) => LBOnlyLooksRaw(r1)
    case Raw_lookaround(look, r1) => (look.Lookbehind? || look.NegLookbehind?) && LBOnlyLooksRaw(r1)
    case _ => true
  }

  /** RAW (L5 scope): positive lookbehinds are allowed iff their bodies are
      `LBOnlyLooksRaw`. Strictly weaker than `NoPosLookbehindRaw`. */
  predicate L5ScopeRaw(ra: R.raw_regex)
    decreases ra
  {
    match ra
    case Raw_alt(r1, r2) => L5ScopeRaw(r1) && L5ScopeRaw(r2)
    case Raw_con(r1, r2) => L5ScopeRaw(r1) && L5ScopeRaw(r2)
    case Raw_quant(_, r1) => L5ScopeRaw(r1)
    case Raw_count(_, r1) => L5ScopeRaw(r1)
    case Raw_capture(r1) => L5ScopeRaw(r1)
    case Raw_lookaround(look, r1) => (look.Lookbehind? ==> LBOnlyLooksRaw(r1)) && L5ScopeRaw(r1)
    case _ => true
  }

  /** RAW: every NEGATIVE-look body is look-free. */
  predicate NegLooksLookFreeRaw(ra: R.raw_regex)
    decreases ra
  {
    match ra
    case Raw_alt(r1, r2) => NegLooksLookFreeRaw(r1) && NegLooksLookFreeRaw(r2)
    case Raw_con(r1, r2) => NegLooksLookFreeRaw(r1) && NegLooksLookFreeRaw(r2)
    case Raw_quant(_, r1) => NegLooksLookFreeRaw(r1)
    case Raw_count(_, r1) => NegLooksLookFreeRaw(r1)
    case Raw_capture(r1) => NegLooksLookFreeRaw(r1)
    case Raw_lookaround(look, r1) =>
      ((look.NegLookahead? || look.NegLookbehind?) ==> LookFreeRaw(r1)) && NegLooksLookFreeRaw(r1)
    case _ => true
  }

  /** The `raw_regex` counterpart of `LookFreeRE`. */
  predicate LookFreeRaw(raw: R.raw_regex)
    decreases raw
  {
    match raw
    case Raw_empty => true
    case Raw_character(_) => true
    case Raw_anchor(_) => true
    case Raw_alt(r1, r2) => LookFreeRaw(r1) && LookFreeRaw(r2)
    case Raw_con(r1, r2) => LookFreeRaw(r1) && LookFreeRaw(r2)
    case Raw_quant(_, r1) => LookFreeRaw(r1)
    case Raw_count(_, r1) => LookFreeRaw(r1)
    case Raw_capture(r1) => LookFreeRaw(r1)
    case Raw_lookaround(_, _) => false
  }

  /** The lookbehind fragment: every plus-fragment shape, plus lookbehind
      leaves `(?<=...)`/`(?<!...)` whose bodies are capture-free, non-nested
      plus-fragment regexes. Lookaheads remain excluded (their build passes
      run backward — the L2 campaign). */
  predicate LookBehindFragmentRE(re: R.regex)
    decreases re
  {
    match re
    case Re_empty => true
    case Re_character(_) => true
    case Re_anchor(_) => true
    case Re_alt(r1, r2) => LookBehindFragmentRE(r1) && LookBehindFragmentRE(r2)
    case Re_con(r1, r2) => LookBehindFragmentRE(r1) && LookBehindFragmentRE(r2)
    case Re_quant(nul, qid, q, r1) =>
      ((q.min == 0 && q.max == None)
       || (0 <= q.min && q.max.Some? && q.min <= q.max.value)
       || (q.min > 0 && q.max == None && nul == R.NonNullable
           && R.nullable(r1) == R.NonNullable))
      && LookBehindFragmentRE(r1)
    case Re_capture(cid, r1) => LookBehindFragmentRE(r1)
    case Re_lookaround(lid, la, r1) =>
      // BOTH flavours, whole plus fragment. A lookAHEAD's body no longer needs
      // to be star-shaped: its oracle builds BACKWARD, and the compile/anchor-
      // swap commutation (OracleBuild.CompileToWriteSwap) reads that build as a
      // forward run of `compile_to_write(RevRE(body))` -- so anchors in the
      // body are handled, not forbidden.
      // L3a/L3b: a POSITIVE lookaround -- forward (lookAHEAD) OR backward
      // (lookBEHIND) -- may now CAPTURE (its body's captures are reconstructed by
      // FLookLoop; the lookbehind case runs the backward capture replay, keystone
      // LkReplayMatchesSpecLB). Only the NEGATIVE flavours still require a
      // capture-free body (a negative look records nothing).
      (la.Lookahead? || la.Lookbehind? || CaptureFreeRE(r1)) && LookFreeRE(r1) && PlusFragmentRE(r1)
  }

  /** The `raw_regex` counterpart of `LookBehindFragmentRE`. */
  predicate LookBehindFragmentRaw(raw: R.raw_regex)
    decreases raw
  {
    match raw
    case Raw_empty => true
    case Raw_character(_) => true
    case Raw_anchor(_) => true
    case Raw_alt(r1, r2) => LookBehindFragmentRaw(r1) && LookBehindFragmentRaw(r2)
    case Raw_con(r1, r2) => LookBehindFragmentRaw(r1) && LookBehindFragmentRaw(r2)
    case Raw_quant(q, r1) =>
      ((q.Plus? || q.LazyPlus?) ==> R.raw_nullable(r1) == R.NonNullable)
      && LookBehindFragmentRaw(r1)
    case Raw_count(q, r1) =>
      ((q.min == 0 && q.max == None)
       || (0 <= q.min && q.max.Some? && q.min <= q.max.value)
       || (q.min > 0 && q.max == None && R.raw_nullable(r1) == R.NonNullable))
      && LookBehindFragmentRaw(r1)
    case Raw_capture(r1) => LookBehindFragmentRaw(r1)
    case Raw_lookaround(look, r1) =>
      // L3a/L3b: a POSITIVE lookaround (lookAHEAD or lookBEHIND) may CAPTURE
      // (mirrors LookBehindFragmentRE); only the NEGATIVE flavours require a
      // capture-free body.
      (look.Lookahead? || look.Lookbehind? || CaptureFreeRaw(r1)) && LookFreeRaw(r1) && PlusFragmentRaw(r1)
  }

  /** The plus fragment embeds in the lookbehind fragment. */
  lemma PlusIsLookBehindFragmentRE(re: R.regex)
    requires PlusFragmentRE(re)
    ensures LookBehindFragmentRE(re)
    decreases re
  {
    match re
    case Re_alt(r1, r2) => PlusIsLookBehindFragmentRE(r1); PlusIsLookBehindFragmentRE(r2);
    case Re_con(r1, r2) => PlusIsLookBehindFragmentRE(r1); PlusIsLookBehindFragmentRE(r2);
    case Re_quant(_, _, _, r1) => PlusIsLookBehindFragmentRE(r1);
    case Re_capture(_, r1) => PlusIsLookBehindFragmentRE(r1);
    case _ =>
  }

  // ===========================================================================
  // The NESTED fragment (L4): lookaround bodies may themselves contain
  // lookarounds. `LookBehindFragmentRE` forces `LookFreeRE(body)` at every
  // lookaround leaf (depth-1 only); `NestedFragmentRE` replaces that leaf
  // constraint with a RECURSIVE `NestedFragmentRE(body)`, admitting arbitrary
  // nesting while keeping the same plus-fragment quant shapes and capture rule
  // (negative flavours still need capture-free bodies). `NestDepth` is the
  // induction measure the depth-parametric keystone (W4) decreases on.
  // ===========================================================================

  /** Maximum lookaround NESTING depth of `re`: 0 for a look-free regex, and
      `1 + (deepest body)` at each lookaround node. The termination measure for
      the depth-inductive keystone — a body's `NestDepth` is strictly smaller
      than its enclosing lookaround's. */
  function NestDepth(re: R.regex): nat
    decreases re
  {
    match re
    case Re_empty => 0
    case Re_character(_) => 0
    case Re_anchor(_) => 0
    case Re_alt(r1, r2) => var a := NestDepth(r1); var b := NestDepth(r2); if a < b then b else a
    case Re_con(r1, r2) => var a := NestDepth(r1); var b := NestDepth(r2); if a < b then b else a
    case Re_quant(_, _, _, r1) => NestDepth(r1)
    case Re_capture(_, r1) => NestDepth(r1)
    case Re_lookaround(_, _, r1) => 1 + NestDepth(r1)
  }

  /** The nested lookaround fragment: every plus-fragment shape, plus
      lookaround leaves `(?=...)`/`(?<=...)`/`(?!...)`/`(?<!...)` whose bodies
      are THEMSELVES in the nested fragment (so looks may nest to any depth).
      Identical to `LookBehindFragmentRE` except the lookaround case drops
      `LookFreeRE(body) && PlusFragmentRE(body)` for the recursive
      `NestedFragmentRE(body)`. `NestedFragmentRE(re) && NestDepth(re) == 0`
      coincides with `LookBehindFragmentRE(re)` on look-free `re`. */
  predicate NestedFragmentRE(re: R.regex)
    decreases re
  {
    match re
    case Re_empty => true
    case Re_character(_) => true
    case Re_anchor(_) => true
    case Re_alt(r1, r2) => NestedFragmentRE(r1) && NestedFragmentRE(r2)
    case Re_con(r1, r2) => NestedFragmentRE(r1) && NestedFragmentRE(r2)
    case Re_quant(nul, qid, q, r1) =>
      ((q.min == 0 && q.max == None)
       || (0 <= q.min && q.max.Some? && q.min <= q.max.value)
       || (q.min > 0 && q.max == None && nul == R.NonNullable
           && R.nullable(r1) == R.NonNullable))
      && NestedFragmentRE(r1)
    case Re_capture(cid, r1) => NestedFragmentRE(r1)
    case Re_lookaround(lid, la, r1) =>
      (la.Lookahead? || la.Lookbehind? || CaptureFreeRE(r1)) && NestedFragmentRE(r1)
  }

  // ===========================================================================
  // L4 depth-k (ADDITIVE): the POSITIVE-nesting sub-fragment of NestedFragmentRE.
  //
  // `NestedFragmentRE` admits nested looks inside NEGATIVE bodies too (as long as
  // they capture nothing). The recursive Pike/spec fragment `EL.PikeLkRegexRec`,
  // however, keeps NEGATIVE-look bodies GROUP-FREE (`SD.GroupFreeL`, records
  // nothing) — exactly the depth-1 shape — and only lets POSITIVE looks nest.
  // `NegLooksLookFreeRE` is the extra side condition (negative bodies look-free)
  // that carves the sub-fragment `PikeLkRegexRec` supports out of the full
  // nested fragment. This is the honest scope of the recursive keystone:
  // arbitrarily nested CAPTURING positive looks, depth-1 negative gates.
  // ===========================================================================

  /** Every NEGATIVE-look body of `re` is look-free (no lookaround nodes). With
      `NestedFragmentRE`, this is the image of `EL.PikeLkRegexRec` under
      `Translate`: positive looks nest to any depth, negative looks stay
      group-free. Additive. */

  /** Annotation transfers `NoCapUnderQuantRaw`. */
  lemma AnnotateNoCapUnderQuant(ra: R.raw_regex, c: int, l: int, q: int)
    requires NoCapUnderQuantRaw(ra)
    ensures NoCapUnderQuantRE(R.annotate_regex(ra, c, l, q).0)
    decreases ra
  {
    match ra
    case Raw_alt(r1, r2) =>
      AnnotateNoCapUnderQuant(r1, c, l, q);
      var (_, c1, l1, q1) := R.annotate_regex(r1, c, l, q);
      AnnotateNoCapUnderQuant(r2, c1, l1, q1);
    case Raw_con(r1, r2) =>
      AnnotateNoCapUnderQuant(r1, c, l, q);
      var (_, c1, l1, q1) := R.annotate_regex(r1, c, l, q);
      AnnotateNoCapUnderQuant(r2, c1, l1, q1);
    case Raw_quant(_, r1) =>
      AnnotateCaptureFree(r1, c, l, q + 1);
      AnnotateNoCapUnderQuant(r1, c, l, q + 1);
    case Raw_count(_, r1) =>
      AnnotateCaptureFree(r1, c, l, q + 1);
      AnnotateNoCapUnderQuant(r1, c, l, q + 1);
    case Raw_capture(r1) => AnnotateNoCapUnderQuant(r1, c + 1, l, q);
    case Raw_lookaround(_, r1) => AnnotateNoCapUnderQuant(r1, c, l + 1, q);
    case _ =>
  }

  /** Annotation transfers `LookBodiesCaptureFreeRaw`. */
  lemma AnnotateLookBodiesCaptureFree(ra: R.raw_regex, c: int, l: int, q: int)
    requires LookBodiesCaptureFreeRaw(ra)
    ensures LookBodiesCaptureFreeRE(R.annotate_regex(ra, c, l, q).0)
    decreases ra
  {
    match ra
    case Raw_alt(r1, r2) =>
      AnnotateLookBodiesCaptureFree(r1, c, l, q);
      var (_, c1, l1, q1) := R.annotate_regex(r1, c, l, q);
      AnnotateLookBodiesCaptureFree(r2, c1, l1, q1);
    case Raw_con(r1, r2) =>
      AnnotateLookBodiesCaptureFree(r1, c, l, q);
      var (_, c1, l1, q1) := R.annotate_regex(r1, c, l, q);
      AnnotateLookBodiesCaptureFree(r2, c1, l1, q1);
    case Raw_quant(_, r1) => AnnotateLookBodiesCaptureFree(r1, c, l, q + 1);
    case Raw_count(_, r1) => AnnotateLookBodiesCaptureFree(r1, c, l, q + 1);
    case Raw_capture(r1) => AnnotateLookBodiesCaptureFree(r1, c + 1, l, q);
    case Raw_lookaround(_, r1) => AnnotateCaptureFree(r1, c, l + 1, q);
    case _ =>
  }

  /** Annotation transfers `LookBodiesNoCapUnderQuantRaw`. */
  lemma AnnotateLookBodiesNoCapUnderQuant(ra: R.raw_regex, c: int, l: int, q: int)
    requires LookBodiesNoCapUnderQuantRaw(ra)
    ensures LookBodiesNoCapUnderQuantRE(R.annotate_regex(ra, c, l, q).0)
    decreases ra
  {
    match ra
    case Raw_alt(r1, r2) =>
      AnnotateLookBodiesNoCapUnderQuant(r1, c, l, q);
      var (_, c1, l1, q1) := R.annotate_regex(r1, c, l, q);
      AnnotateLookBodiesNoCapUnderQuant(r2, c1, l1, q1);
    case Raw_con(r1, r2) =>
      AnnotateLookBodiesNoCapUnderQuant(r1, c, l, q);
      var (_, c1, l1, q1) := R.annotate_regex(r1, c, l, q);
      AnnotateLookBodiesNoCapUnderQuant(r2, c1, l1, q1);
    case Raw_quant(_, r1) => AnnotateLookBodiesNoCapUnderQuant(r1, c, l, q + 1);
    case Raw_count(_, r1) => AnnotateLookBodiesNoCapUnderQuant(r1, c, l, q + 1);
    case Raw_capture(r1) => AnnotateLookBodiesNoCapUnderQuant(r1, c + 1, l, q);
    case Raw_lookaround(_, r1) => AnnotateNoCapUnderQuant(r1, c, l + 1, q);
    case _ =>
  }

  /** Annotation transfers `QuantsLookCapFreeRaw`. */
  lemma AnnotateQuantsLookCapFree(ra: R.raw_regex, c: int, l: int, q: int)
    requires QuantsLookCapFreeRaw(ra)
    ensures QuantsLookCapFreeRE(R.annotate_regex(ra, c, l, q).0)
    decreases ra
  {
    match ra
    case Raw_alt(r1, r2) =>
      AnnotateQuantsLookCapFree(r1, c, l, q);
      var (_, c1, l1, q1) := R.annotate_regex(r1, c, l, q);
      AnnotateQuantsLookCapFree(r2, c1, l1, q1);
    case Raw_con(r1, r2) =>
      AnnotateQuantsLookCapFree(r1, c, l, q);
      var (_, c1, l1, q1) := R.annotate_regex(r1, c, l, q);
      AnnotateQuantsLookCapFree(r2, c1, l1, q1);
    case Raw_quant(_, r1) =>
      AnnotateLookBodiesCaptureFree(r1, c, l, q + 1);
      AnnotateQuantsLookCapFree(r1, c, l, q + 1);
    case Raw_count(_, r1) =>
      AnnotateLookBodiesCaptureFree(r1, c, l, q + 1);
      AnnotateQuantsLookCapFree(r1, c, l, q + 1);
    case Raw_capture(r1) => AnnotateQuantsLookCapFree(r1, c + 1, l, q);
    case Raw_lookaround(_, r1) => AnnotateQuantsLookCapFree(r1, c, l + 1, q);
    case _ =>
  }

  /** Annotation transfers `NegLooksLookFreeRaw`. */
  lemma AnnotateNegLooksLookFree(ra: R.raw_regex, c: int, l: int, q: int)
    requires NegLooksLookFreeRaw(ra)
    ensures NegLooksLookFreeRE(R.annotate_regex(ra, c, l, q).0)
    decreases ra
  {
    match ra
    case Raw_alt(r1, r2) =>
      AnnotateNegLooksLookFree(r1, c, l, q);
      var (_, c1, l1, q1) := R.annotate_regex(r1, c, l, q);
      AnnotateNegLooksLookFree(r2, c1, l1, q1);
    case Raw_con(r1, r2) =>
      AnnotateNegLooksLookFree(r1, c, l, q);
      var (_, c1, l1, q1) := R.annotate_regex(r1, c, l, q);
      AnnotateNegLooksLookFree(r2, c1, l1, q1);
    case Raw_quant(_, r1) => AnnotateNegLooksLookFree(r1, c, l, q + 1);
    case Raw_count(_, r1) => AnnotateNegLooksLookFree(r1, c, l, q + 1);
    case Raw_capture(r1) => AnnotateNegLooksLookFree(r1, c + 1, l, q);
    case Raw_lookaround(look, r1) =>
      if look.NegLookahead? || look.NegLookbehind? { AnnotateLookFree(r1, c, l + 1, q); }
      AnnotateNegLooksLookFree(r1, c, l + 1, q);
    case _ =>
  }

  predicate NegLooksLookFreeRE(re: R.regex)
    decreases re
  {
    match re
    case Re_empty => true
    case Re_character(_) => true
    case Re_anchor(_) => true
    case Re_alt(r1, r2) => NegLooksLookFreeRE(r1) && NegLooksLookFreeRE(r2)
    case Re_con(r1, r2) => NegLooksLookFreeRE(r1) && NegLooksLookFreeRE(r2)
    case Re_quant(_, _, _, r1) => NegLooksLookFreeRE(r1)
    case Re_capture(_, r1) => NegLooksLookFreeRE(r1)
    case Re_lookaround(lid, la, r1) =>
      ((la.NegLookahead? || la.NegLookbehind?) ==> LookFreeRE(r1)) && NegLooksLookFreeRE(r1)
  }
  /** (L5) Every look inside is LOOKBEHIND-flavoured (RE level; identical to
      `LindenElkFlipStatics.LBOnlyLooksRE`, which the Flip bricks use — the
      equivalence is `LindenElkFlipGate.LBOnlyEquiv`). */
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

  /** (L5 scope, RE level) positive lookbehinds are allowed iff their bodies are
      `LBOnlyLooksRE`. `LindenElkMain.NoPosLookbehindRE(re) ==> L5ScopeRE(re)`
      (`NoPosImpliesL5Scope`). */
  predicate L5ScopeRE(re: R.regex)
    decreases re
  {
    match re
    case Re_alt(r1, r2) => L5ScopeRE(r1) && L5ScopeRE(r2)
    case Re_con(r1, r2) => L5ScopeRE(r1) && L5ScopeRE(r2)
    case Re_quant(_, _, _, r1) => L5ScopeRE(r1)
    case Re_capture(_, r1) => L5ScopeRE(r1)
    case Re_lookaround(_, la, r1) => (la.Lookbehind? ==> LBOnlyLooksRE(r1)) && L5ScopeRE(r1)
    case _ => true
  }

  /** Annotation transfers `LBOnlyLooksRaw` (the look constructor is preserved). */
  lemma AnnotateLBOnlyLooks(ra: R.raw_regex, c: int, l: int, q: int)
    requires LBOnlyLooksRaw(ra)
    ensures LBOnlyLooksRE(R.annotate_regex(ra, c, l, q).0)
    decreases ra
  {
    match ra
    case Raw_alt(r1, r2) =>
      AnnotateLBOnlyLooks(r1, c, l, q);
      var (_, c1, l1, q1) := R.annotate_regex(r1, c, l, q);
      AnnotateLBOnlyLooks(r2, c1, l1, q1);
    case Raw_con(r1, r2) =>
      AnnotateLBOnlyLooks(r1, c, l, q);
      var (_, c1, l1, q1) := R.annotate_regex(r1, c, l, q);
      AnnotateLBOnlyLooks(r2, c1, l1, q1);
    case Raw_quant(_, r1) => AnnotateLBOnlyLooks(r1, c, l, q + 1);
    case Raw_count(_, r1) => AnnotateLBOnlyLooks(r1, c, l, q + 1);
    case Raw_capture(r1) => AnnotateLBOnlyLooks(r1, c + 1, l, q);
    case Raw_lookaround(_, r1) => AnnotateLBOnlyLooks(r1, c, l + 1, q);
    case _ =>
  }

  /** Annotation transfers `L5ScopeRaw`. */
  lemma AnnotateL5Scope(ra: R.raw_regex, c: int, l: int, q: int)
    requires L5ScopeRaw(ra)
    ensures L5ScopeRE(R.annotate_regex(ra, c, l, q).0)
    decreases ra
  {
    match ra
    case Raw_alt(r1, r2) =>
      AnnotateL5Scope(r1, c, l, q);
      var (_, c1, l1, q1) := R.annotate_regex(r1, c, l, q);
      AnnotateL5Scope(r2, c1, l1, q1);
    case Raw_con(r1, r2) =>
      AnnotateL5Scope(r1, c, l, q);
      var (_, c1, l1, q1) := R.annotate_regex(r1, c, l, q);
      AnnotateL5Scope(r2, c1, l1, q1);
    case Raw_quant(_, r1) => AnnotateL5Scope(r1, c, l, q + 1);
    case Raw_count(_, r1) => AnnotateL5Scope(r1, c, l, q + 1);
    case Raw_capture(r1) => AnnotateL5Scope(r1, c + 1, l, q);
    case Raw_lookaround(look, r1) =>
      if look.Lookbehind? { AnnotateLBOnlyLooks(r1, c, l + 1, q); }
      AnnotateL5Scope(r1, c, l + 1, q);
    case _ =>
  }

  /** A lookbehind-only body is itself in the L5 scope (its positive lookbehinds
      have lookbehind-only bodies by construction). */
  lemma LBOnlyImpliesL5Scope(r: R.regex)
    requires LBOnlyLooksRE(r)
    ensures L5ScopeRE(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => LBOnlyImpliesL5Scope(r1); LBOnlyImpliesL5Scope(r2);
    case Re_con(r1, r2) => LBOnlyImpliesL5Scope(r1); LBOnlyImpliesL5Scope(r2);
    case Re_quant(_, _, _, r1) => LBOnlyImpliesL5Scope(r1);
    case Re_capture(_, r1) => LBOnlyImpliesL5Scope(r1);
    case Re_lookaround(_, _, r1) => LBOnlyImpliesL5Scope(r1);
    case _ =>
  }

  /** Look-free regexes are trivially lookbehind-only and in scope (the
      `lazy_prefix` dot-star wrapper). */
  lemma LookFreeLBOnly(r: R.regex)
    requires LookFreeRE(r)
    ensures LBOnlyLooksRE(r) && L5ScopeRE(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => LookFreeLBOnly(r1); LookFreeLBOnly(r2);
    case Re_con(r1, r2) => LookFreeLBOnly(r1); LookFreeLBOnly(r2);
    case Re_quant(_, _, _, r1) => LookFreeLBOnly(r1);
    case Re_capture(_, r1) => LookFreeLBOnly(r1);
    case _ =>
  }


  /** A look-free regex has no lookarounds at all, so it vacuously satisfies
      `NegLooksLookFreeRE`. */
  lemma LookFreeNegLooksLookFree(re: R.regex)
    requires LookFreeRE(re)
    ensures NegLooksLookFreeRE(re)
    decreases re
  {
    match re
    case Re_alt(r1, r2) => LookFreeNegLooksLookFree(r1); LookFreeNegLooksLookFree(r2);
    case Re_con(r1, r2) => LookFreeNegLooksLookFree(r1); LookFreeNegLooksLookFree(r2);
    case Re_quant(_, _, _, r1) => LookFreeNegLooksLookFree(r1);
    case Re_capture(_, r1) => LookFreeNegLooksLookFree(r1);
    case _ =>
  }

  /** The depth-1 lookbehind fragment has look-free bodies at every lookaround
      leaf, so every negative-look body is look-free: `NegLooksLookFreeRE`
      holds. Every input supported today satisfies the recursive-keystone side
      condition, so the recursive keystone genuinely subsumes the depth-1 one. */
  lemma LookBehindNegLooksLookFree(re: R.regex)
    requires LookBehindFragmentRE(re)
    ensures NegLooksLookFreeRE(re)
    decreases re
  {
    match re
    case Re_alt(r1, r2) => LookBehindNegLooksLookFree(r1); LookBehindNegLooksLookFree(r2);
    case Re_con(r1, r2) => LookBehindNegLooksLookFree(r1); LookBehindNegLooksLookFree(r2);
    case Re_quant(_, _, _, r1) => LookBehindNegLooksLookFree(r1);
    case Re_capture(_, r1) => LookBehindNegLooksLookFree(r1);
    case Re_lookaround(lid, la, r1) => LookFreeNegLooksLookFree(r1);
    case _ =>
  }

  /** A look-free plus fragment is in the nested fragment (with `NestDepth 0`):
      no lookaround nodes, so the two predicates enforce exactly the same
      plus-fragment quant shapes. */
  lemma LookFreePlusIsNestedRE(re: R.regex)
    requires LookFreeRE(re) && PlusFragmentRE(re)
    ensures NestedFragmentRE(re) && NestDepth(re) == 0
    decreases re
  {
    match re
    case Re_alt(r1, r2) => LookFreePlusIsNestedRE(r1); LookFreePlusIsNestedRE(r2);
    case Re_con(r1, r2) => LookFreePlusIsNestedRE(r1); LookFreePlusIsNestedRE(r2);
    case Re_quant(_, _, _, r1) => LookFreePlusIsNestedRE(r1);
    case Re_capture(_, r1) => LookFreePlusIsNestedRE(r1);
    case _ =>
  }

  /** On a LOOK-FREE regex the lookbehind and plus fragments coincide: with no
      lookaround nodes, both predicates exercise only the alt/con/quant/capture
      cases, which are conjunct-for-conjunct identical (same quant shapes). Lets
      a gate body — known look-free (`GateStaticsOk`) and `LookBehindFragmentRE`
      (`StaticOkRE(body)`) — recover `PlusFragmentRE` under the nested flip. */
  lemma LookFreeIsPlusFragmentRE(re: R.regex)
    requires LookFreeRE(re) && LookBehindFragmentRE(re)
    ensures PlusFragmentRE(re)
    decreases re
  {
    match re
    case Re_alt(r1, r2) => LookFreeIsPlusFragmentRE(r1); LookFreeIsPlusFragmentRE(r2);
    case Re_con(r1, r2) => LookFreeIsPlusFragmentRE(r1); LookFreeIsPlusFragmentRE(r2);
    case Re_quant(_, _, _, r1) => LookFreeIsPlusFragmentRE(r1);
    case Re_capture(_, r1) => LookFreeIsPlusFragmentRE(r1);
    case _ =>
  }

  /** The depth-1 lookbehind fragment embeds in the nested fragment — every
      input supported today stays supported at L4. The lookaround case uses
      `LookFreePlusIsNestedRE` on the (look-free) body. */
  lemma LookBehindFragmentIsNestedRE(re: R.regex)
    requires LookBehindFragmentRE(re)
    ensures NestedFragmentRE(re)
    decreases re
  {
    match re
    case Re_alt(r1, r2) => LookBehindFragmentIsNestedRE(r1); LookBehindFragmentIsNestedRE(r2);
    case Re_con(r1, r2) => LookBehindFragmentIsNestedRE(r1); LookBehindFragmentIsNestedRE(r2);
    case Re_quant(_, _, _, r1) => LookBehindFragmentIsNestedRE(r1);
    case Re_capture(_, r1) => LookBehindFragmentIsNestedRE(r1);
    case Re_lookaround(lid, la, r1) => LookFreePlusIsNestedRE(r1);
    case _ =>
  }

  /** The raw plus fragment embeds in the raw lookbehind fragment. */
  lemma PlusIsLookBehindFragmentRaw(ra: R.raw_regex)
    requires PlusFragmentRaw(ra)
    ensures LookBehindFragmentRaw(ra)
    decreases ra
  {
    match ra
    case Raw_alt(r1, r2) => PlusIsLookBehindFragmentRaw(r1); PlusIsLookBehindFragmentRaw(r2);
    case Raw_con(r1, r2) => PlusIsLookBehindFragmentRaw(r1); PlusIsLookBehindFragmentRaw(r2);
    case Raw_quant(_, r1) => PlusIsLookBehindFragmentRaw(r1);
    case Raw_count(_, r1) => PlusIsLookBehindFragmentRaw(r1);
    case Raw_capture(r1) => PlusIsLookBehindFragmentRaw(r1);
    case _ =>
  }

  /** Annotation preserves capture-freedom — it only assigns ids. */
  lemma AnnotateCaptureFree(ra: R.raw_regex, c: int, l: int, q: int)
    requires CaptureFreeRaw(ra)
    ensures CaptureFreeRE(R.annotate_regex(ra, c, l, q).0)
    decreases ra
  {
    match ra
    case Raw_alt(r1, r2) =>
      AnnotateCaptureFree(r1, c, l, q);
      var (_, c1, l1, q1) := R.annotate_regex(r1, c, l, q);
      AnnotateCaptureFree(r2, c1, l1, q1);
    case Raw_con(r1, r2) =>
      AnnotateCaptureFree(r1, c, l, q);
      var (_, c1, l1, q1) := R.annotate_regex(r1, c, l, q);
      AnnotateCaptureFree(r2, c1, l1, q1);
    case Raw_quant(_, r1) => AnnotateCaptureFree(r1, c, l, q + 1);
    case Raw_count(_, r1) => AnnotateCaptureFree(r1, c, l, q + 1);
    case Raw_lookaround(_, r1) => AnnotateCaptureFree(r1, c, l + 1, q);
    case _ =>
  }

  /** Annotation preserves lookaround-freedom. */
  lemma AnnotateLookFree(ra: R.raw_regex, c: int, l: int, q: int)
    requires LookFreeRaw(ra)
    ensures LookFreeRE(R.annotate_regex(ra, c, l, q).0)
    decreases ra
  {
    match ra
    case Raw_alt(r1, r2) =>
      AnnotateLookFree(r1, c, l, q);
      var (_, c1, l1, q1) := R.annotate_regex(r1, c, l, q);
      AnnotateLookFree(r2, c1, l1, q1);
    case Raw_con(r1, r2) =>
      AnnotateLookFree(r1, c, l, q);
      var (_, c1, l1, q1) := R.annotate_regex(r1, c, l, q);
      AnnotateLookFree(r2, c1, l1, q1);
    case Raw_quant(_, r1) => AnnotateLookFree(r1, c, l, q + 1);
    case Raw_count(_, r1) => AnnotateLookFree(r1, c, l, q + 1);
    case Raw_capture(r1) => AnnotateLookFree(r1, c + 1, l, q);
    case _ =>
  }

  /** Annotation preserves the lookbehind fragment: the lookaround flavour is
      copied verbatim, and the body's three side-conditions are preserved by
      the three lemmas above. */
  lemma AnnotateLookBehindFragment(ra: R.raw_regex, c: int, l: int, q: int)
    requires LookBehindFragmentRaw(ra)
    ensures LookBehindFragmentRE(R.annotate_regex(ra, c, l, q).0)
    decreases ra
  {
    match ra
    case Raw_alt(r1, r2) =>
      AnnotateLookBehindFragment(r1, c, l, q);
      var (_, c1, l1, q1) := R.annotate_regex(r1, c, l, q);
      AnnotateLookBehindFragment(r2, c1, l1, q1);
    case Raw_con(r1, r2) =>
      AnnotateLookBehindFragment(r1, c, l, q);
      var (_, c1, l1, q1) := R.annotate_regex(r1, c, l, q);
      AnnotateLookBehindFragment(r2, c1, l1, q1);
    case Raw_quant(quant, r1) =>
      AnnotateLookBehindFragment(r1, c, l, q + 1);
      AnnotateNullable(r1, c, l, q + 1);
    case Raw_count(quant, r1) =>
      AnnotateLookBehindFragment(r1, c, l, q + 1);
      AnnotateNullable(r1, c, l, q + 1);
    case Raw_capture(r1) => AnnotateLookBehindFragment(r1, c + 1, l, q);
    case Raw_lookaround(look, r1) =>
      // annotate copies the flavour `look` verbatim. A capturing POSITIVE look
      // (lookahead OR lookbehind) skips AnnotateCaptureFree (its precondition would
      // fail); the RE fragment is satisfied by `la.Lookahead?`/`la.Lookbehind?`.
      // Only the negative flavours carry the capture-free body onward.
      if look.NegLookahead? || look.NegLookbehind? {
        AnnotateCaptureFree(r1, c, l + 1, q);
      }
      AnnotateLookFree(r1, c, l + 1, q);
      AnnotatePlusFragment(r1, c, l + 1, q);
    case _ =>
  }

  /** `lazy_prefix(annotate(raw))` stays in the lookbehind fragment. */
  lemma SpecRegexLookBehindFragment(raw: R.raw_regex)
    requires LookBehindFragmentRaw(raw)
    ensures LookBehindFragmentRE(R.lazy_prefix(R.annotate(raw)))
  {
    AnnotateLookBehindFragment(R.Raw_capture(raw), 0, 1, 1);
  }

  // ---------------------------------------------------------------------------
  // The raw counterpart of the NESTED fragment (L4), and its annotate bridge.
  // ---------------------------------------------------------------------------

  /** The `raw_regex` counterpart of `NestedFragmentRE`: identical to
      `LookBehindFragmentRaw` except the lookaround case admits a body that is
      itself in the nested fragment (so looks may nest to any depth). The
      predicate the widened `Supported` will eventually use. */
  predicate NestedFragmentRaw(raw: R.raw_regex)
    decreases raw
  {
    match raw
    case Raw_empty => true
    case Raw_character(_) => true
    case Raw_anchor(_) => true
    case Raw_alt(r1, r2) => NestedFragmentRaw(r1) && NestedFragmentRaw(r2)
    case Raw_con(r1, r2) => NestedFragmentRaw(r1) && NestedFragmentRaw(r2)
    case Raw_quant(q, r1) =>
      ((q.Plus? || q.LazyPlus?) ==> R.raw_nullable(r1) == R.NonNullable)
      && NestedFragmentRaw(r1)
    case Raw_count(q, r1) =>
      ((q.min == 0 && q.max == None)
       || (0 <= q.min && q.max.Some? && q.min <= q.max.value)
       || (q.min > 0 && q.max == None && R.raw_nullable(r1) == R.NonNullable))
      && NestedFragmentRaw(r1)
    case Raw_capture(r1) => NestedFragmentRaw(r1)
    case Raw_lookaround(look, r1) =>
      (look.Lookahead? || look.Lookbehind? || CaptureFreeRaw(r1)) && NestedFragmentRaw(r1)
  }

  /** A look-free raw plus fragment is in the raw nested fragment. */
  lemma LookFreePlusIsNestedRaw(ra: R.raw_regex)
    requires LookFreeRaw(ra) && PlusFragmentRaw(ra)
    ensures NestedFragmentRaw(ra)
    decreases ra
  {
    match ra
    case Raw_alt(r1, r2) => LookFreePlusIsNestedRaw(r1); LookFreePlusIsNestedRaw(r2);
    case Raw_con(r1, r2) => LookFreePlusIsNestedRaw(r1); LookFreePlusIsNestedRaw(r2);
    case Raw_quant(_, r1) => LookFreePlusIsNestedRaw(r1);
    case Raw_count(_, r1) => LookFreePlusIsNestedRaw(r1);
    case Raw_capture(r1) => LookFreePlusIsNestedRaw(r1);
    case _ =>
  }

  /** Today's raw lookbehind fragment embeds in the raw nested fragment —
      every raw input `Supported` today stays supported at L4. */
  lemma LookBehindFragmentIsNestedRaw(ra: R.raw_regex)
    requires LookBehindFragmentRaw(ra)
    ensures NestedFragmentRaw(ra)
    decreases ra
  {
    match ra
    case Raw_alt(r1, r2) => LookBehindFragmentIsNestedRaw(r1); LookBehindFragmentIsNestedRaw(r2);
    case Raw_con(r1, r2) => LookBehindFragmentIsNestedRaw(r1); LookBehindFragmentIsNestedRaw(r2);
    case Raw_quant(_, r1) => LookBehindFragmentIsNestedRaw(r1);
    case Raw_count(_, r1) => LookBehindFragmentIsNestedRaw(r1);
    case Raw_capture(r1) => LookBehindFragmentIsNestedRaw(r1);
    case Raw_lookaround(look, r1) => LookFreePlusIsNestedRaw(r1);
    case _ =>
  }

  /** Annotation preserves the nested fragment: the flavour is copied verbatim
      and the body recurses (nesting allowed). The nested analogue of
      `AnnotateLookBehindFragment`. */
  lemma AnnotateNestedFragment(ra: R.raw_regex, c: int, l: int, q: int)
    requires NestedFragmentRaw(ra)
    ensures NestedFragmentRE(R.annotate_regex(ra, c, l, q).0)
    decreases ra
  {
    match ra
    case Raw_alt(r1, r2) =>
      AnnotateNestedFragment(r1, c, l, q);
      var (_, c1, l1, q1) := R.annotate_regex(r1, c, l, q);
      AnnotateNestedFragment(r2, c1, l1, q1);
    case Raw_con(r1, r2) =>
      AnnotateNestedFragment(r1, c, l, q);
      var (_, c1, l1, q1) := R.annotate_regex(r1, c, l, q);
      AnnotateNestedFragment(r2, c1, l1, q1);
    case Raw_quant(quant, r1) =>
      AnnotateNestedFragment(r1, c, l, q + 1);
      AnnotateNullable(r1, c, l, q + 1);
    case Raw_count(quant, r1) =>
      AnnotateNestedFragment(r1, c, l, q + 1);
      AnnotateNullable(r1, c, l, q + 1);
    case Raw_capture(r1) => AnnotateNestedFragment(r1, c + 1, l, q);
    case Raw_lookaround(look, r1) =>
      // flavour copied verbatim; negative flavours keep the capture-free body;
      // the body recurses into the nested fragment (any depth).
      if look.NegLookahead? || look.NegLookbehind? {
        AnnotateCaptureFree(r1, c, l + 1, q);
      }
      AnnotateNestedFragment(r1, c, l + 1, q);
    case _ =>
  }

  /** `lazy_prefix(annotate(raw))` stays in the nested fragment. */
  lemma SpecRegexNestedFragment(raw: R.raw_regex)
    requires NestedFragmentRaw(raw)
    ensures NestedFragmentRE(R.lazy_prefix(R.annotate(raw)))
  {
    AnnotateNestedFragment(R.Raw_capture(raw), 0, 1, 1);
  }

  /** On capture-free regexes `remove_capture` is the identity, so an L1
      lookbehind's oracle build regex is `lazy_prefix(body)` itself. */
  lemma RemoveCaptureFreeId(re: R.regex)
    requires CaptureFreeRE(re)
    ensures R.remove_capture(re) == re
    decreases re
  {
    match re
    case Re_alt(r1, r2) => RemoveCaptureFreeId(r1); RemoveCaptureFreeId(r2);
    case Re_con(r1, r2) => RemoveCaptureFreeId(r1); RemoveCaptureFreeId(r2);
    case Re_quant(_, _, _, r1) => RemoveCaptureFreeId(r1);
    case Re_lookaround(_, _, r1) => RemoveCaptureFreeId(r1);
    case _ =>
  }

  /** `remove_capture` preserves look-freedom (it only deletes `Group` nodes). */
  lemma RemoveCaptureLookFreeRE(re: R.regex)
    requires LookFreeRE(re)
    ensures LookFreeRE(R.remove_capture(re))
    decreases re
  {
    match re
    case Re_alt(r1, r2) => RemoveCaptureLookFreeRE(r1); RemoveCaptureLookFreeRE(r2);
    case Re_con(r1, r2) => RemoveCaptureLookFreeRE(r1); RemoveCaptureLookFreeRE(r2);
    case Re_quant(_, _, _, r1) => RemoveCaptureLookFreeRE(r1);
    case Re_capture(_, r1) => RemoveCaptureLookFreeRE(r1);
    case _ =>
  }

  /** `remove_capture` preserves nullability (a `Group(r)` is nullable iff `r` is)
      — the plus-fragment's `nullable(body) == NonNullable` side condition. */
  lemma RemoveCaptureNullableRE(re: R.regex)
    ensures R.nullable(R.remove_capture(re)) == R.nullable(re)
    decreases re
  {
    match re
    case Re_alt(r1, r2) => RemoveCaptureNullableRE(r1); RemoveCaptureNullableRE(r2);
    case Re_con(r1, r2) => RemoveCaptureNullableRE(r1); RemoveCaptureNullableRE(r2);
    case Re_quant(_, _, _, r1) => RemoveCaptureNullableRE(r1);
    case Re_capture(_, r1) => RemoveCaptureNullableRE(r1);
    case Re_lookaround(_, _, r1) => RemoveCaptureNullableRE(r1);
    case _ =>
  }

  /** `remove_capture` keeps a regex in the PLUS fragment (the `+` side condition
      is phrased on the body's nullability, which `RemoveCaptureNullableRE`
      preserves). */
  lemma RemoveCapturePlusFragmentRE(re: R.regex)
    requires PlusFragmentRE(re)
    ensures PlusFragmentRE(R.remove_capture(re))
    decreases re
  {
    match re
    case Re_alt(r1, r2) => RemoveCapturePlusFragmentRE(r1); RemoveCapturePlusFragmentRE(r2);
    case Re_con(r1, r2) => RemoveCapturePlusFragmentRE(r1); RemoveCapturePlusFragmentRE(r2);
    case Re_quant(_, _, _, r1) => RemoveCapturePlusFragmentRE(r1); RemoveCaptureNullableRE(r1);
    case Re_capture(_, r1) => RemoveCapturePlusFragmentRE(r1);
    case _ =>
  }

  /** The oracle build regex of a lookbehind-fragment lookaround stays in the
      PLUS fragment: `oracle_regex` is `lazy_prefix(remove_capture(body))` (a
      lookAHEAD reverses first), `remove_capture` preserves the plus fragment
      (L3a/L3b: the body may now CAPTURE — no capture-freedom needed), and the
      lazy prefix's quantifier is star-shaped. */
  lemma OracleRegexPlusFragment(la: R.lookaround, body: R.regex)
    requires PlusFragmentRE(body)
    ensures PlusFragmentRE(CP.oracle_regex(la, body))
  {
    RemoveCapturePlusFragmentRE(body);   // PlusFragmentRE(remove_capture(body))
    if la.Lookahead? || la.NegLookahead? {
      // the lookAHEAD build reverses the (capture-stripped) body first; reversal
      // preserves the plus fragment (only concatenation order and anchors change)
      ReversePlusFragmentRE(R.remove_capture(body));
    }
  }

  /** `reverse_regex` preserves nullability -- it only reorders concatenation
      (`null_and` is commutative) and leaves anchors. */
  lemma ReverseNullableRE(r: R.regex)
    ensures R.nullable(R.reverse_regex(r)) == R.nullable(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => ReverseNullableRE(r1); ReverseNullableRE(r2);
    case Re_con(r1, r2) => ReverseNullableRE(r1); ReverseNullableRE(r2);
    case Re_quant(_, _, _, r1) => ReverseNullableRE(r1);
    case Re_capture(_, r1) => ReverseNullableRE(r1);
    case _ =>
  }

  /** `reverse_regex` preserves the plus fragment (the `+` side condition is on
      the body's nullability, which reversal preserves). */
  lemma ReversePlusFragmentRE(r: R.regex)
    requires PlusFragmentRE(r)
    ensures PlusFragmentRE(R.reverse_regex(r))
    decreases r
  {
    match r
    case Re_alt(r1, r2) => ReversePlusFragmentRE(r1); ReversePlusFragmentRE(r2);
    case Re_con(r1, r2) => ReversePlusFragmentRE(r1); ReversePlusFragmentRE(r2);
    case Re_quant(_, _, _, r1) => ReversePlusFragmentRE(r1); ReverseNullableRE(r1);
    case Re_capture(_, r1) => ReversePlusFragmentRE(r1);
    case _ =>
  }

  /** `reverse_regex` preserves look-freedom. */
  lemma ReverseLookFreeRE(r: R.regex)
    requires LookFreeRE(r)
    ensures LookFreeRE(R.reverse_regex(r))
    decreases r
  {
    match r
    case Re_alt(r1, r2) => ReverseLookFreeRE(r1); ReverseLookFreeRE(r2);
    case Re_con(r1, r2) => ReverseLookFreeRE(r1); ReverseLookFreeRE(r2);
    case Re_quant(_, _, _, r1) => ReverseLookFreeRE(r1);
    case Re_capture(_, r1) => ReverseLookFreeRE(r1);
    case _ =>
  }

  /** `reverse_regex` preserves the star fragment (it only reorders
      concatenations). */
  lemma ReverseStarFragmentRE(r: R.regex)
    requires StarFragmentRE(r)
    ensures StarFragmentRE(R.reverse_regex(r))
    decreases r
  {
    match r
    case Re_alt(r1, r2) => ReverseStarFragmentRE(r1); ReverseStarFragmentRE(r2);
    case Re_con(r1, r2) => ReverseStarFragmentRE(r1); ReverseStarFragmentRE(r2);
    case Re_quant(_, _, _, r1) => ReverseStarFragmentRE(r1);
    case Re_capture(_, r1) => ReverseStarFragmentRE(r1);
    case _ =>
  }

  // ===========================================================================
  // Code access and flattening
  // ===========================================================================

  // Option-valued instruction fetch (the rep predicates need in-range facts;
  // RegElk's total get_instr returns Fail out of range, which loses them).
  /** Instruction fetch at `pc` in `c`, `None` when out of range — used throughout so
      the rep predicates below carry in-range facts. */
  function GetPcRE(c: RB.code, pc: nat): Option<RB.instruction> {
    if pc < |c| then Some(c[pc]) else None
  }

  /** Fetching at `pc` in `c` agrees with fetching at `|prev| + pc` in `prev + c` —
      prepending code doesn't disturb lookups at shifted offsets. */
  lemma GetPrefixRE(c: RB.code, pc: nat, prev: RB.code)
    ensures GetPcRE(prev + c, |prev| + pc) == GetPcRE(c, pc)
  {
    if pc < |c| { assert (prev + c)[|prev| + pc] == c[pc]; }
  }

  /** The instruction at the very start of `c` is still found at offset `|prev|` once
      `c` is appended after `prev`. */
  lemma GetFirstRE(c: RB.code, prev: RB.code)
    ensures GetPcRE(prev + c, |prev|) == GetPcRE(c, 0)
  { GetPrefixRE(c, 0, prev); }

  /** An in-range fetch at `pc` in `c` survives appending any `suffix` after `c`. */
  lemma GetSuffixRE(c: RB.code, suffix: RB.code, pc: nat, i: RB.instruction)
    requires GetPcRE(c, pc) == Some(i)
    ensures GetPcRE(c + suffix, pc) == Some(i)
  {
    assert (c + suffix)[pc] == c[pc];
  }

  // tl_flatten with a tail is flatten-empty plus the tail.
  /** `CP.tl_flatten` with a tail equals flattening with no tail and then appending the
      tail — lets flattening facts build up compositionally over `chain`/`Concat` trees. */
  lemma FlattenApp(t: CP.treelist, tail: RB.code)
    ensures CP.tl_flatten(t, tail) == CP.tl_flatten(t, []) + tail
    decreases t
  {
    match t
    case Leaf(l) =>
      assert l + [] == l;
    case Concat(a, b) =>
      FlattenApp(b, tail);
      FlattenApp(a, CP.tl_flatten(b, tail));
      FlattenApp(b, []);
      FlattenApp(a, CP.tl_flatten(b, []));
  }

  // flatten of a compiled tree, with no tail
  /** The bytecode a compiled `treelist` denotes: `tl_flatten` with an empty tail. */
  function Flat(t: CP.treelist): RB.code {
    CP.tl_flatten(t, [])
  }

  // ===========================================================================
  // The representation predicate (mirror of Linden NfaRep, RegElk shapes)
  // ===========================================================================
  //
  // Shapes emitted by CP.compile(re, pc1, Progress) for the fragment:
  //   Re_empty:      (nothing), pc2 == pc1
  //   Re_character:  Consume(ExpectationOf(ch)) at pc1, pc2 == pc1+1
  //   Re_alt:        Fork(pc1+1, e1+1) at pc1; r1 at pc1+1..e1; Jmp(pc2) at e1;
  //                  r2 at e1+1..pc2
  //   Re_con:        r1 at pc1..e1; r2 at e1..pc2
  //   Re_quant(*):   fork(greedy: pc1+1 / e1+2) at pc1; SetQuantToClock(qid,false)
  //                  at pc1+1; BeginLoop at pc1+2; body at pc1+3..e1; EndLoop at
  //                  e1; Jmp(pc1) at e1+1; pc2 == e1+2
  //   Re_capture:    SetRegisterToCP(2cid) at pc1; body at pc1+1..e1;
  //                  SetRegisterToCP(2cid+1) at e1; pc2 == e1+1
  //   Re_quant({n,m}): n forced copies (each: SetQuantToClock(qid,false) at pc;
  //                  body at pc+1..e), then m-n optional fork-guarded layers
  //                  (each: fork(greedy: pc+1 / common end pc2) at pc;
  //                  SetQuantToClock at pc+1; BeginLoop at pc+2; body at
  //                  pc+3..e; EndLoop at e; next layer at e+1) — the generic
  //                  repeat_min/repeat_optional schemes

  /** The representation predicate: `NfaRepRE(re, c, pc1, pc2)` holds exactly when the
      code `c` between `pc1` and `pc2` is what `CP.compile` emits for `re`, per the
      shapes tabulated above — the RegElk-bytecode mirror of Linden's `NfaRep`.
      Everything downstream (`ActionsRepRE`, `TreeRepRE`, ...) builds on this
      correspondence. */
  /** `k` forced copies of `r1`'s block, each headed by
      `SetQuantToClock(qid, false)` — the representation of `repeat_min`'s
      output (the RegElk mirror of Linden's `NfaRepMin`; the clock-mark
      instruction plays `ResetRegs`'s per-forced-iteration role). */
  ghost predicate NfaRepMinRE(k: nat, qid: R.quantid, r1: R.regex, c: RB.code, pc1: nat, pc2: nat)
    decreases CP.rsize(r1), k + 2
  {
    if k == 0 then pc1 == pc2
    else
      var body := pc1 + 1;
      var rest := k - 1;
      exists e1: nat ::
        GetPcRE(c, pc1) == Some(RB.SetQuantToClock(qid, false))
        && NfaRepRE(r1, c, body, e1)
        && NfaRepMinRE(rest, qid, r1, c, e1, pc2)
  }

  /** `k` optional fork-guarded layers of `r1`'s block — the representation of
      `repeat_optional`'s output. Every layer's fork skips to the common `pc2`;
      the layer's `EndLoop` falls through to the next layer (the RegElk mirror
      of Linden's `NfaRepOpt`, with the head reordered to the compiler's
      fork/clock-mark/BeginLoop layout). */
  ghost predicate NfaRepOptRE(k: nat, greedy: bool, qid: R.quantid, r1: R.regex, c: RB.code, pc1: nat, pc2: nat)
    decreases CP.rsize(r1), k + 2
  {
    if k == 0 then pc1 == pc2
    else exists e1: nat ::
      GetPcRE(c, pc1) == Some(if greedy then RB.Fork(pc1 + 1, pc2) else RB.Fork(pc2, pc1 + 1))
      && GetPcRE(c, pc1 + 1) == Some(RB.SetQuantToClock(qid, false))
      && GetPcRE(c, pc1 + 2) == Some(RB.BeginLoop)
      && NfaRepRE(r1, c, pc1 + 3, e1)
      && GetPcRE(c, e1) == Some(RB.EndLoop)
      && NfaRepOptRE(k - 1, greedy, qid, r1, c, e1 + 1, pc2)
  }

  ghost predicate NfaRepRE(re: R.regex, c: RB.code, pc1: nat, pc2: nat)
    decreases CP.rsize(re), 1
  {
    match re
    case Re_empty => pc1 == pc2
    case Re_character(ch) =>
      pc2 == pc1 + 1 && GetPcRE(c, pc1) == Some(RB.Consume(T.ExpectationOf(ch)))
    case Re_alt(r1, r2) =>
      exists e1: nat ::
        GetPcRE(c, pc1) == Some(RB.Fork(pc1 + 1, e1 + 1))
        && NfaRepRE(r1, c, pc1 + 1, e1)
        && GetPcRE(c, e1) == Some(RB.Jmp(pc2))
        && NfaRepRE(r2, c, e1 + 1, pc2)
    case Re_con(r1, r2) =>
      exists e1: nat :: NfaRepRE(r1, c, pc1, e1) && NfaRepRE(r2, c, e1, pc2)
    case Re_quant(nul, qid, q, r1) =>
      if q.min == 0 && q.max == None then
        // the star: fast-path arm, kept verbatim so star-fragment consumers
        // (and their solver behavior) are untouched
        exists e1: nat ::
          GetPcRE(c, pc1) == Some(if q.greedy then RB.Fork(pc1 + 1, e1 + 2) else RB.Fork(e1 + 2, pc1 + 1))
          && GetPcRE(c, pc1 + 1) == Some(RB.SetQuantToClock(qid, false))
          && GetPcRE(c, pc1 + 2) == Some(RB.BeginLoop)
          && NfaRepRE(r1, c, pc1 + 3, e1)
          && GetPcRE(c, e1) == Some(RB.EndLoop)
          && GetPcRE(c, e1 + 1) == Some(RB.Jmp(pc1))
          && pc2 == e1 + 2
      else if q.max.Some? then
        // bounded {min,max}: min forced copies, then max-min optional layers
        0 <= q.min && q.min <= q.max.value
        && var mn := q.min as nat;
           var kx := (q.max.value - q.min) as nat;
           exists em: nat ::
             NfaRepMinRE(mn, qid, r1, c, pc1, em)
             && NfaRepOptRE(kx, q.greedy, qid, r1, c, em, pc2)
      else
        // unbounded min > 0 (+, {n,}): the do-while scheme, represented only
        // for NonNullable bodies - min-1 forced copies, then the guaranteed
        // last repetition [SetQuantToClock; body; backward Fork]
        q.min > 0 && nul == R.NonNullable
        && var mn1 := (q.min - 1) as nat;
           exists em: nat ::
             NfaRepMinRE(mn1, qid, r1, c, pc1, em)
             && GetPcRE(c, em) == Some(RB.SetQuantToClock(qid, false))
             && (exists e1: nat ::
                   NfaRepRE(r1, c, em + 1, e1)
                   && GetPcRE(c, e1) == Some(if q.greedy then RB.Fork(em, e1 + 1) else RB.Fork(e1 + 1, em))
                   && pc2 == e1 + 1)
    case Re_capture(cid, r1) =>
      exists e1: nat ::
        GetPcRE(c, pc1) == Some(RB.SetRegisterToCP(CP.start_reg(cid)))
        && NfaRepRE(r1, c, pc1 + 1, e1)
        && GetPcRE(c, e1) == Some(RB.SetRegisterToCP(CP.end_reg(cid)))
        && pc2 == e1 + 1
    case Re_lookaround(lid, la, r1) =>
      // the main pass carries only the oracle consultation: one zero-width
      // instruction; the body lives in the per-lookaround tables
      pc2 == pc1 + 1
      && GetPcRE(c, pc1) == Some(if la.Lookahead? || la.Lookbehind?
                                 then RB.CheckOracle(lid)
                                 else RB.NegCheckOracle(lid))
    case Re_anchor(a) =>
      pc2 == pc1 + 1 && GetPcRE(c, pc1) == Some(RB.AnchorAssertion(a))
  }

  // ===========================================================================
  // Compiler correctness for the representation
  // ===========================================================================

  // Label arithmetic: the next-fresh label equals start + emitted length.
  /** The compiler's returned "next fresh label" equals `start` plus the length of the
      emitted code — needed to reason about code layout ahead of establishing `NfaRepRE`
      itself. */
  /** `FreshCorrectRE` for `repeat_min`: label arithmetic of the forced-copy
      chain. */
  lemma FreshCorrectMinRE(k: nat, qid: R.quantid, r1: R.regex, start: nat, tl: CP.treelist, next: int)
    requires LookBehindFragmentRE(r1)
    requires CP.repeat_min(k, qid, r1, start, CP.Progress) == (tl, next)
    ensures next == start + |Flat(tl)|
    decreases CP.rsize(r1), k + 2
  {
    if k == 0 {
      FlattenApp(CP.Leaf([]), []);
    } else {
      var (body_code, new_f) := CP.compile(r1, start + 1, CP.Progress);
      FreshCorrectRE(r1, start + 1, body_code, new_f);
      var (next_code, next_f) := CP.repeat_min(k - 1, qid, r1, new_f, CP.Progress);
      FreshCorrectMinRE(k - 1, qid, r1, new_f as nat, next_code, next_f);
      var ch := CP.chain([CP.Leaf([RB.SetQuantToClock(qid, false)]), body_code, next_code]);
      assert Flat(ch) == [RB.SetQuantToClock(qid, false)] + Flat(body_code) + Flat(next_code) by {
        ChainThree(CP.Leaf([RB.SetQuantToClock(qid, false)]), body_code, next_code);
      }
    }
  }

  /** `FreshCorrectRE` for `repeat_optional`: label arithmetic of the
      optional-layer chain. */
  lemma FreshCorrectOptRE(k: nat, greedy: bool, qid: R.quantid, r1: R.regex, start: nat, tl: CP.treelist, next: int)
    requires LookBehindFragmentRE(r1)
    requires CP.repeat_optional(k, qid, r1, start, CP.Progress, greedy) == (tl, next)
    ensures next == start + |Flat(tl)|
    decreases CP.rsize(r1), k + 2
  {
    if k == 0 {
      FlattenApp(CP.Leaf([]), []);
    } else {
      var (body_code, new_f) := CP.compile(r1, start + 3, CP.Progress);
      FreshCorrectRE(r1, start + 3, body_code, new_f);
      var (next_code, next_f) := CP.repeat_optional(k - 1, qid, r1, new_f + 1, CP.Progress, greedy);
      FreshCorrectOptRE(k - 1, greedy, qid, r1, (new_f + 1) as nat, next_code, next_f);
      var fork := if greedy then RB.Fork(start + 1, next_f) else RB.Fork(next_f, start + 1);
      var ch := CP.chain([CP.Leaf([fork, RB.SetQuantToClock(qid, false), RB.BeginLoop]), body_code, CP.Leaf([RB.EndLoop]), next_code]);
      assert Flat(ch) == [fork, RB.SetQuantToClock(qid, false), RB.BeginLoop] + Flat(body_code) + [RB.EndLoop] + Flat(next_code) by {
        ChainFour(CP.Leaf([fork, RB.SetQuantToClock(qid, false), RB.BeginLoop]), body_code, CP.Leaf([RB.EndLoop]), next_code);
      }
    }
  }

  lemma FreshCorrectRE(re: R.regex, start: nat, tl: CP.treelist, next: int)
    requires LookBehindFragmentRE(re)
    requires CP.compile(re, start, CP.Progress) == (tl, next)
    ensures next == start + |Flat(tl)|
    decreases CP.rsize(re), 1
  {
    match re
    case Re_empty =>
    case Re_character(_) =>
    case Re_anchor(_) =>
    case Re_lookaround(_, _, _) =>
    case Re_alt(r1, r2) =>
      var (l1, f1) := CP.compile(r1, start + 1, CP.Progress);
      var (l2, f2) := CP.compile(r2, f1 + 1, CP.Progress);
      FreshCorrectRE(r1, start + 1, l1, f1);
      assert f1 >= 0;
      FreshCorrectRE(r2, f1 + 1, l2, f2);
      // flatten the 4-element chain
      var ch := CP.chain([CP.Leaf([RB.Fork(start + 1, f1 + 1)]), l1, CP.Leaf([RB.Jmp(f2)]), l2]);
      FlattenApp(l1, [RB.Jmp(f2)] + Flat(l2));
      FlattenApp(l2, []);
      assert Flat(ch) == [RB.Fork(start + 1, f1 + 1)] + Flat(l1) + [RB.Jmp(f2)] + Flat(l2) by {
        ChainFour(CP.Leaf([RB.Fork(start + 1, f1 + 1)]), l1, CP.Leaf([RB.Jmp(f2)]), l2);
      }
    case Re_con(r1, r2) =>
      var (l1, f1) := CP.compile(r1, start, CP.Progress);
      FreshCorrectRE(r1, start, l1, f1);
      var (l2, f2) := CP.compile(r2, f1, CP.Progress);
      FreshCorrectRE(r2, f1, l2, f2);
      FlattenApp(l1, Flat(l2));
    case Re_quant(nul, qid, q, r1) =>
      // the fragment (min == 0 unbounded, or bounded max) excludes the three
      // special + schemes (all of which require max == None with min > 0), so
      // compile always takes its generic branch here.
      if q.min == 0 && q.max == None {
        // repeat_min(0, ...) emits nothing; max == None selects the star scheme.
        var (iter_code, iter_f) := CP.compile(r1, start + 3, CP.Progress);
        FreshCorrectRE(r1, start + 3, iter_code, iter_f);
        var fork := if q.greedy then RB.Fork(start + 1, iter_f + 2) else RB.Fork(iter_f + 2, start + 1);
        var ch := CP.chain([CP.Leaf([]),
                            CP.Leaf([fork, RB.SetQuantToClock(qid, false), RB.BeginLoop]),
                            iter_code,
                            CP.Leaf([RB.EndLoop, RB.Jmp(start)])]);
        assert Flat(ch) == [fork, RB.SetQuantToClock(qid, false), RB.BeginLoop] + Flat(iter_code) + [RB.EndLoop, RB.Jmp(start)] by {
          ChainFour(CP.Leaf([]), CP.Leaf([fork, RB.SetQuantToClock(qid, false), RB.BeginLoop]), iter_code, CP.Leaf([RB.EndLoop, RB.Jmp(start)]));
        }
      } else if q.max.Some? {
        // bounded {min,max}: repeat_min then repeat_optional, concatenated
        var (min_code, min_f) := CP.repeat_min(q.min, qid, r1, start, CP.Progress);
        FreshCorrectMinRE(q.min as nat, qid, r1, start, min_code, min_f);
        var (opt_code, opt_f) := CP.repeat_optional(q.max.value - q.min, qid, r1, min_f, CP.Progress, q.greedy);
        FreshCorrectOptRE((q.max.value - q.min) as nat, q.greedy, qid, r1, min_f as nat, opt_code, opt_f);
        FlattenApp(min_code, Flat(opt_code));
        assert Flat(tl) == Flat(min_code) + Flat(opt_code);
      } else {
        // the do-while: min-1 forced copies; SetQuantToClock; body; the fork
        var (min_code, min_f) := CP.repeat_min(q.min - 1, qid, r1, start, CP.Progress);
        FreshCorrectMinRE((q.min - 1) as nat, qid, r1, start, min_code, min_f);
        var (body_code, body_f) := CP.compile(r1, min_f + 1, CP.Progress);
        FreshCorrectRE(r1, (min_f + 1) as nat, body_code, body_f);
        var fork := if q.greedy then RB.Fork(min_f, body_f + 1) else RB.Fork(body_f + 1, min_f);
        var ch := CP.chain([min_code, CP.Leaf([RB.SetQuantToClock(qid, false)]), body_code, CP.Leaf([fork])]);
        assert Flat(ch) == Flat(min_code) + [RB.SetQuantToClock(qid, false)] + Flat(body_code) + [fork] by {
          ChainFour(min_code, CP.Leaf([RB.SetQuantToClock(qid, false)]), body_code, CP.Leaf([fork]));
        }
      }
    case Re_capture(cid, r1) =>
      var (l1, f1) := CP.compile(r1, start + 1, CP.Progress);
      FreshCorrectRE(r1, start + 1, l1, f1);
      var ch := CP.chain([CP.Leaf([RB.SetRegisterToCP(CP.start_reg(cid))]), l1, CP.Leaf([RB.SetRegisterToCP(CP.end_reg(cid))])]);
      assert Flat(ch) == [RB.SetRegisterToCP(CP.start_reg(cid))] + Flat(l1) + [RB.SetRegisterToCP(CP.end_reg(cid))] by {
        ChainThree(CP.Leaf([RB.SetRegisterToCP(CP.start_reg(cid))]), l1, CP.Leaf([RB.SetRegisterToCP(CP.end_reg(cid))]));
      }
  }

  // chain/flatten linearization helpers
  /** Flattening a 3-element `chain` equals concatenating the flattening of each
      element, in order. */
  lemma ChainThree(a: CP.treelist, b: CP.treelist, d: CP.treelist)
    ensures Flat(CP.chain([a, b, d])) == Flat(a) + Flat(b) + Flat(d)
  {
    calc {
      Flat(CP.chain([a, b, d]));
      { assert [a, b, d][..2] == [a, b] && [a, b][..1] == [a];
        assert CP.chain([a]) == a;
        assert CP.chain([a, b]) == CP.Concat(a, b);
        assert CP.chain([a, b, d]) == CP.Concat(CP.Concat(a, b), d); }
      CP.tl_flatten(CP.Concat(CP.Concat(a, b), d), []);
      CP.tl_flatten(CP.Concat(a, b), CP.tl_flatten(d, []));
      CP.tl_flatten(a, CP.tl_flatten(b, Flat(d)));
      { FlattenApp(b, Flat(d)); }
      CP.tl_flatten(a, Flat(b) + Flat(d));
      { FlattenApp(a, Flat(b) + Flat(d)); }
      Flat(a) + (Flat(b) + Flat(d));
      Flat(a) + Flat(b) + Flat(d);
    }
  }

  /** Flattening a 4-element `chain` equals concatenating the flattening of each
      element, in order. */
  lemma ChainFour(a: CP.treelist, b: CP.treelist, d: CP.treelist, e: CP.treelist)
    ensures Flat(CP.chain([a, b, d, e])) == Flat(a) + Flat(b) + Flat(d) + Flat(e)
  {
    calc {
      Flat(CP.chain([a, b, d, e]));
      { assert [a, b, d, e][..3] == [a, b, d] && [a, b, d][..2] == [a, b] && [a, b][..1] == [a];
        assert CP.chain([a]) == a;
        assert CP.chain([a, b]) == CP.Concat(a, b);
        assert CP.chain([a, b, d]) == CP.Concat(CP.Concat(a, b), d);
        assert CP.chain([a, b, d, e]) == CP.Concat(CP.Concat(CP.Concat(a, b), d), e); }
      CP.tl_flatten(CP.Concat(CP.Concat(CP.Concat(a, b), d), e), []);
      CP.tl_flatten(CP.Concat(CP.Concat(a, b), d), CP.tl_flatten(e, []));
      CP.tl_flatten(CP.Concat(a, b), CP.tl_flatten(d, Flat(e)));
      CP.tl_flatten(a, CP.tl_flatten(b, CP.tl_flatten(d, Flat(e))));
      { FlattenApp(d, Flat(e)); }
      CP.tl_flatten(a, CP.tl_flatten(b, Flat(d) + Flat(e)));
      { FlattenApp(b, Flat(d) + Flat(e)); }
      CP.tl_flatten(a, Flat(b) + (Flat(d) + Flat(e)));
      { FlattenApp(a, Flat(b) + (Flat(d) + Flat(e))); }
      Flat(a) + (Flat(b) + (Flat(d) + Flat(e)));
      Flat(a) + Flat(b) + Flat(d) + Flat(e);
    }
  }

  // A representation survives appending code on the right.
  /** `NfaRepRE` is stable under appending arbitrary code after the represented
      region — needed to assemble the representation of a compound regex from its
      compiled subexpressions before the surrounding code is fully known. */
  /** `NfaRepExtendRE` for `NfaRepMinRE`: forced-copy chains survive appending
      code past their end. */
  lemma NfaRepExtendMinRE(k: nat, qid: R.quantid, r1: R.regex, c: RB.code, start: nat, endl: nat, suffix: RB.code)
    requires NfaRepMinRE(k, qid, r1, c, start, endl)
    ensures NfaRepMinRE(k, qid, r1, c + suffix, start, endl)
    decreases CP.rsize(r1), k + 2
  {
    if k > 0 {
      var e1: nat :| GetPcRE(c, start) == Some(RB.SetQuantToClock(qid, false))
        && NfaRepRE(r1, c, start + 1, e1)
        && NfaRepMinRE(k - 1, qid, r1, c, e1, endl);
      GetSuffixRE(c, suffix, start, RB.SetQuantToClock(qid, false));
      NfaRepExtendRE(r1, c, start + 1, e1, suffix);
      NfaRepExtendMinRE(k - 1, qid, r1, c, e1, endl, suffix);
      assert GetPcRE(c + suffix, start) == Some(RB.SetQuantToClock(qid, false))
          && NfaRepRE(r1, c + suffix, start + 1, e1)
          && NfaRepMinRE(k - 1, qid, r1, c + suffix, e1, endl);
    }
  }

  /** `NfaRepExtendRE` for `NfaRepOptRE`: optional-layer chains survive
      appending code past their end. */
  lemma NfaRepExtendOptRE(k: nat, greedy: bool, qid: R.quantid, r1: R.regex, c: RB.code, start: nat, endl: nat, suffix: RB.code)
    requires NfaRepOptRE(k, greedy, qid, r1, c, start, endl)
    ensures NfaRepOptRE(k, greedy, qid, r1, c + suffix, start, endl)
    decreases CP.rsize(r1), k + 2
  {
    if k > 0 {
      var e1: nat :| GetPcRE(c, start) == Some(if greedy then RB.Fork(start + 1, endl) else RB.Fork(endl, start + 1))
        && GetPcRE(c, start + 1) == Some(RB.SetQuantToClock(qid, false))
        && GetPcRE(c, start + 2) == Some(RB.BeginLoop)
        && NfaRepRE(r1, c, start + 3, e1)
        && GetPcRE(c, e1) == Some(RB.EndLoop)
        && NfaRepOptRE(k - 1, greedy, qid, r1, c, e1 + 1, endl);
      GetSuffixRE(c, suffix, start, if greedy then RB.Fork(start + 1, endl) else RB.Fork(endl, start + 1));
      GetSuffixRE(c, suffix, start + 1, RB.SetQuantToClock(qid, false));
      GetSuffixRE(c, suffix, start + 2, RB.BeginLoop);
      GetSuffixRE(c, suffix, e1, RB.EndLoop);
      NfaRepExtendRE(r1, c, start + 3, e1, suffix);
      NfaRepExtendOptRE(k - 1, greedy, qid, r1, c, e1 + 1, endl, suffix);
      assert GetPcRE(c + suffix, start) == Some(if greedy then RB.Fork(start + 1, endl) else RB.Fork(endl, start + 1))
          && GetPcRE(c + suffix, start + 1) == Some(RB.SetQuantToClock(qid, false))
          && GetPcRE(c + suffix, start + 2) == Some(RB.BeginLoop)
          && NfaRepRE(r1, c + suffix, start + 3, e1)
          && GetPcRE(c + suffix, e1) == Some(RB.EndLoop)
          && NfaRepOptRE(k - 1, greedy, qid, r1, c + suffix, e1 + 1, endl);
    }
  }

  lemma NfaRepExtendRE(re: R.regex, c: RB.code, start: nat, endl: nat, suffix: RB.code)
    requires NfaRepRE(re, c, start, endl)
    ensures NfaRepRE(re, c + suffix, start, endl)
    decreases CP.rsize(re), 1
  {
    match re
    case Re_empty =>
    case Re_character(ch) =>
      GetSuffixRE(c, suffix, start, RB.Consume(T.ExpectationOf(ch)));
    case Re_alt(r1, r2) =>
      var e1: nat :| GetPcRE(c, start) == Some(RB.Fork(start + 1, e1 + 1))
        && NfaRepRE(r1, c, start + 1, e1)
        && GetPcRE(c, e1) == Some(RB.Jmp(endl))
        && NfaRepRE(r2, c, e1 + 1, endl);
      GetSuffixRE(c, suffix, start, RB.Fork(start + 1, e1 + 1));
      GetSuffixRE(c, suffix, e1, RB.Jmp(endl));
      NfaRepExtendRE(r1, c, start + 1, e1, suffix);
      NfaRepExtendRE(r2, c, e1 + 1, endl, suffix);
      assert GetPcRE(c + suffix, start) == Some(RB.Fork(start + 1, e1 + 1))
          && NfaRepRE(r1, c + suffix, start + 1, e1)
          && GetPcRE(c + suffix, e1) == Some(RB.Jmp(endl))
          && NfaRepRE(r2, c + suffix, e1 + 1, endl);
    case Re_con(r1, r2) =>
      var e1: nat :| NfaRepRE(r1, c, start, e1) && NfaRepRE(r2, c, e1, endl);
      NfaRepExtendRE(r1, c, start, e1, suffix);
      NfaRepExtendRE(r2, c, e1, endl, suffix);
      assert NfaRepRE(r1, c + suffix, start, e1) && NfaRepRE(r2, c + suffix, e1, endl);
    case Re_quant(nul, qid, q, r1) =>
      if q.min == 0 && q.max == None {
        var e1: nat :| GetPcRE(c, start) == Some(if q.greedy then RB.Fork(start + 1, e1 + 2) else RB.Fork(e1 + 2, start + 1))
          && GetPcRE(c, start + 1) == Some(RB.SetQuantToClock(qid, false))
          && GetPcRE(c, start + 2) == Some(RB.BeginLoop)
          && NfaRepRE(r1, c, start + 3, e1)
          && GetPcRE(c, e1) == Some(RB.EndLoop)
          && GetPcRE(c, e1 + 1) == Some(RB.Jmp(start))
          && endl == e1 + 2;
        GetSuffixRE(c, suffix, start, if q.greedy then RB.Fork(start + 1, e1 + 2) else RB.Fork(e1 + 2, start + 1));
        GetSuffixRE(c, suffix, start + 1, RB.SetQuantToClock(qid, false));
        GetSuffixRE(c, suffix, start + 2, RB.BeginLoop);
        GetSuffixRE(c, suffix, e1, RB.EndLoop);
        GetSuffixRE(c, suffix, e1 + 1, RB.Jmp(start));
        NfaRepExtendRE(r1, c, start + 3, e1, suffix);
        assert GetPcRE(c + suffix, start) == Some(if q.greedy then RB.Fork(start + 1, e1 + 2) else RB.Fork(e1 + 2, start + 1))
            && GetPcRE(c + suffix, start + 1) == Some(RB.SetQuantToClock(qid, false))
            && GetPcRE(c + suffix, start + 2) == Some(RB.BeginLoop)
            && NfaRepRE(r1, c + suffix, start + 3, e1)
            && GetPcRE(c + suffix, e1) == Some(RB.EndLoop)
            && GetPcRE(c + suffix, e1 + 1) == Some(RB.Jmp(start))
            && endl == e1 + 2;
      } else if q.max.Some? {
        var em: nat :| NfaRepMinRE(q.min as nat, qid, r1, c, start, em)
          && NfaRepOptRE((q.max.value - q.min) as nat, q.greedy, qid, r1, c, em, endl);
        NfaRepExtendMinRE(q.min as nat, qid, r1, c, start, em, suffix);
        NfaRepExtendOptRE((q.max.value - q.min) as nat, q.greedy, qid, r1, c, em, endl, suffix);
        assert NfaRepMinRE(q.min as nat, qid, r1, c + suffix, start, em)
            && NfaRepOptRE((q.max.value - q.min) as nat, q.greedy, qid, r1, c + suffix, em, endl);
      } else {
        var mn1 := (q.min - 1) as nat;
        var em: nat :| NfaRepMinRE(mn1, qid, r1, c, start, em)
          && GetPcRE(c, em) == Some(RB.SetQuantToClock(qid, false))
          && (exists e1: nat ::
                NfaRepRE(r1, c, em + 1, e1)
                && GetPcRE(c, e1) == Some(if q.greedy then RB.Fork(em, e1 + 1) else RB.Fork(e1 + 1, em))
                && endl == e1 + 1);
        var e1: nat :| NfaRepRE(r1, c, em + 1, e1)
          && GetPcRE(c, e1) == Some(if q.greedy then RB.Fork(em, e1 + 1) else RB.Fork(e1 + 1, em))
          && endl == e1 + 1;
        NfaRepExtendMinRE(mn1, qid, r1, c, start, em, suffix);
        GetSuffixRE(c, suffix, em, RB.SetQuantToClock(qid, false));
        NfaRepExtendRE(r1, c, em + 1, e1, suffix);
        GetSuffixRE(c, suffix, e1, if q.greedy then RB.Fork(em, e1 + 1) else RB.Fork(e1 + 1, em));
        assert NfaRepMinRE(mn1, qid, r1, c + suffix, start, em)
            && GetPcRE(c + suffix, em) == Some(RB.SetQuantToClock(qid, false))
            && NfaRepRE(r1, c + suffix, em + 1, e1)
            && GetPcRE(c + suffix, e1) == Some(if q.greedy then RB.Fork(em, e1 + 1) else RB.Fork(e1 + 1, em))
            && endl == e1 + 1;
      }
    case Re_capture(cid, r1) =>
      var e1: nat :| GetPcRE(c, start) == Some(RB.SetRegisterToCP(CP.start_reg(cid)))
        && NfaRepRE(r1, c, start + 1, e1)
        && GetPcRE(c, e1) == Some(RB.SetRegisterToCP(CP.end_reg(cid)))
        && endl == e1 + 1;
      GetSuffixRE(c, suffix, start, RB.SetRegisterToCP(CP.start_reg(cid)));
      GetSuffixRE(c, suffix, e1, RB.SetRegisterToCP(CP.end_reg(cid)));
      NfaRepExtendRE(r1, c, start + 1, e1, suffix);
      assert GetPcRE(c + suffix, start) == Some(RB.SetRegisterToCP(CP.start_reg(cid)))
          && NfaRepRE(r1, c + suffix, start + 1, e1)
          && GetPcRE(c + suffix, e1) == Some(RB.SetRegisterToCP(CP.end_reg(cid)))
          && endl == e1 + 1;
    case Re_lookaround(lid, la, _) =>
      GetSuffixRE(c, suffix, start,
                  if la.Lookahead? || la.Lookbehind?
                  then RB.CheckOracle(lid) else RB.NegCheckOracle(lid));
    case Re_anchor(a) =>
      GetSuffixRE(c, suffix, start, RB.AnchorAssertion(a));
  }

  /** `CompileNfaRepRE` for `repeat_min`: the forced-copy chain the compiler
      emits satisfies `NfaRepMinRE`. */
  lemma CompileNfaRepMinRE(k: nat, qid: R.quantid, r1: R.regex, start: nat, tl: CP.treelist, next: int, prev: RB.code)
    requires LookBehindFragmentRE(r1)
    requires CP.repeat_min(k, qid, r1, start, CP.Progress) == (tl, next)
    requires start == |prev|
    ensures next >= 0 && NfaRepMinRE(k, qid, r1, prev + Flat(tl), start, next as nat)
    decreases CP.rsize(r1), k + 2
  {
    FreshCorrectMinRE(k, qid, r1, start, tl, next);
    if k == 0 {
      assert prev + Flat(tl) == prev;
    } else {
      var (body_code, new_f) := CP.compile(r1, start + 1, CP.Progress);
      var (next_code, next_f) := CP.repeat_min(k - 1, qid, r1, new_f, CP.Progress);
      FreshCorrectRE(r1, start + 1, body_code, new_f);
      FreshCorrectMinRE(k - 1, qid, r1, new_f as nat, next_code, next_f);
      ChainThree(CP.Leaf([RB.SetQuantToClock(qid, false)]), body_code, next_code);
      assert Flat(tl) == [RB.SetQuantToClock(qid, false)] + Flat(body_code) + Flat(next_code);
      // body region
      var pre1 := prev + [RB.SetQuantToClock(qid, false)];
      assert |pre1| == start + 1;
      CompileNfaRepRE(r1, start + 1, body_code, new_f, pre1);
      NfaRepExtendRE(r1, pre1 + Flat(body_code), start + 1, new_f as nat, Flat(next_code));
      assert (pre1 + Flat(body_code)) + Flat(next_code) == prev + Flat(tl);
      // remaining copies
      var pre2 := prev + [RB.SetQuantToClock(qid, false)] + Flat(body_code);
      assert |pre2| == new_f;
      CompileNfaRepMinRE(k - 1, qid, r1, new_f as nat, next_code, next_f, pre2);
      assert pre2 + Flat(next_code) == prev + Flat(tl);
      // instruction fact
      GetFirstRE(Flat(tl), prev);
      assert GetPcRE(prev + Flat(tl), start) == Some(RB.SetQuantToClock(qid, false))
          && NfaRepRE(r1, prev + Flat(tl), start + 1, new_f as nat)
          && NfaRepMinRE(k - 1, qid, r1, prev + Flat(tl), new_f as nat, next_f as nat);
    }
  }

  /** `CompileNfaRepRE` for `repeat_optional`: the optional-layer chain the
      compiler emits satisfies `NfaRepOptRE`. */
  lemma CompileNfaRepOptRE(k: nat, greedy: bool, qid: R.quantid, r1: R.regex, start: nat, tl: CP.treelist, next: int, prev: RB.code)
    requires LookBehindFragmentRE(r1)
    requires CP.repeat_optional(k, qid, r1, start, CP.Progress, greedy) == (tl, next)
    requires start == |prev|
    ensures next >= 0 && NfaRepOptRE(k, greedy, qid, r1, prev + Flat(tl), start, next as nat)
    decreases CP.rsize(r1), k + 2
  {
    FreshCorrectOptRE(k, greedy, qid, r1, start, tl, next);
    if k == 0 {
      assert prev + Flat(tl) == prev;
    } else {
      var (body_code, new_f) := CP.compile(r1, start + 3, CP.Progress);
      var (next_code, next_f) := CP.repeat_optional(k - 1, qid, r1, new_f + 1, CP.Progress, greedy);
      FreshCorrectRE(r1, start + 3, body_code, new_f);
      FreshCorrectOptRE(k - 1, greedy, qid, r1, (new_f + 1) as nat, next_code, next_f);
      var fork := if greedy then RB.Fork(start + 1, next_f) else RB.Fork(next_f, start + 1);
      var hdr := [fork, RB.SetQuantToClock(qid, false), RB.BeginLoop];
      ChainFour(CP.Leaf(hdr), body_code, CP.Leaf([RB.EndLoop]), next_code);
      assert Flat(tl) == hdr + Flat(body_code) + [RB.EndLoop] + Flat(next_code);
      // body region
      var pre1 := prev + hdr;
      assert |pre1| == start + 3;
      CompileNfaRepRE(r1, start + 3, body_code, new_f, pre1);
      NfaRepExtendRE(r1, pre1 + Flat(body_code), start + 3, new_f as nat, [RB.EndLoop] + Flat(next_code));
      assert (pre1 + Flat(body_code)) + ([RB.EndLoop] + Flat(next_code)) == prev + Flat(tl);
      // remaining layers
      var pre2 := prev + hdr + Flat(body_code) + [RB.EndLoop];
      assert |pre2| == new_f + 1;
      CompileNfaRepOptRE(k - 1, greedy, qid, r1, (new_f + 1) as nat, next_code, next_f, pre2);
      assert pre2 + Flat(next_code) == prev + Flat(tl);
      // instruction facts
      GetPrefixRE(Flat(tl), 0, prev);
      GetPrefixRE(Flat(tl), 1, prev);
      GetPrefixRE(Flat(tl), 2, prev);
      assert prev + Flat(tl) == (prev + hdr + Flat(body_code)) + ([RB.EndLoop] + Flat(next_code));
      assert |prev + hdr + Flat(body_code)| == new_f;
      GetFirstRE([RB.EndLoop] + Flat(next_code), prev + hdr + Flat(body_code));
      assert GetPcRE(prev + Flat(tl), start) == Some(fork)
          && GetPcRE(prev + Flat(tl), start + 1) == Some(RB.SetQuantToClock(qid, false))
          && GetPcRE(prev + Flat(tl), start + 2) == Some(RB.BeginLoop)
          && NfaRepRE(r1, prev + Flat(tl), start + 3, new_f as nat)
          && GetPcRE(prev + Flat(tl), new_f as nat) == Some(RB.EndLoop)
          && NfaRepOptRE(k - 1, greedy, qid, r1, prev + Flat(tl), (new_f + 1) as nat, next_f as nat);
    }
  }

  /** Introduction lemma for the bounded-quantifier arm of `NfaRepRE`: package a
      forced-copy chain and an optional-layer chain into the quantifier's rep,
      without exposing downstream proofs to the existential (the RegElk mirror
      of Linden's `NfaRepQuantIntroNN`). */
  lemma NfaRepREQuantIntro(nul: R.nullability, qid: R.quantid, q: R.counted_quantifier, r1: R.regex, c: RB.code, pc1: nat, em: nat, pc2: nat)
    requires 0 <= q.min && q.max.Some? && q.min <= q.max.value
    requires NfaRepMinRE(q.min as nat, qid, r1, c, pc1, em)
    requires NfaRepOptRE((q.max.value - q.min) as nat, q.greedy, qid, r1, c, em, pc2)
    ensures NfaRepRE(R.Re_quant(nul, qid, q, r1), c, pc1, pc2)
  {
  }

  /** Inversion lemma for the bounded-quantifier arm of `NfaRepRE`: recover the
      seam label `em` between the forced copies and the optional layers (the
      RegElk mirror of Linden's `NfaRepQuantInvNN`). */
  lemma NfaRepREQuantInv(nul: R.nullability, qid: R.quantid, q: R.counted_quantifier, r1: R.regex, c: RB.code, pc1: nat, pc2: nat) returns (em: nat)
    requires q.max.Some?
    requires NfaRepRE(R.Re_quant(nul, qid, q, r1), c, pc1, pc2)
    ensures 0 <= q.min && q.min <= q.max.value
    ensures NfaRepMinRE(q.min as nat, qid, r1, c, pc1, em)
    ensures NfaRepOptRE((q.max.value - q.min) as nat, q.greedy, qid, r1, c, em, pc2)
  {
    var mn := q.min as nat;
    var kx := (q.max.value - q.min) as nat;
    em :| NfaRepMinRE(mn, qid, r1, c, pc1, em)
      && NfaRepOptRE(kx, q.greedy, qid, r1, c, em, pc2);
  }

  /** Introduction lemma for the do-while arm of `NfaRepRE`. */
  lemma NfaRepREPlusIntro(nul: R.nullability, qid: R.quantid, q: R.counted_quantifier, r1: R.regex, c: RB.code, pc1: nat, em: nat, e1: nat, pc2: nat)
    requires q.min > 0 && q.max == None && nul == R.NonNullable
    requires NfaRepMinRE((q.min - 1) as nat, qid, r1, c, pc1, em)
    requires GetPcRE(c, em) == Some(RB.SetQuantToClock(qid, false))
    requires NfaRepRE(r1, c, em + 1, e1)
    requires GetPcRE(c, e1) == Some(if q.greedy then RB.Fork(em, e1 + 1) else RB.Fork(e1 + 1, em))
    requires pc2 == e1 + 1
    ensures NfaRepRE(R.Re_quant(nul, qid, q, r1), c, pc1, pc2)
  {
  }

  /** Inversion lemma for the do-while arm of `NfaRepRE`: recover the last
      copy's clock-mark position and the body end. */
  lemma NfaRepREPlusInv(nul: R.nullability, qid: R.quantid, q: R.counted_quantifier, r1: R.regex, c: RB.code, pc1: nat, pc2: nat) returns (em: nat, e1: nat)
    requires q.min > 0 && q.max == None
    requires NfaRepRE(R.Re_quant(nul, qid, q, r1), c, pc1, pc2)
    ensures nul == R.NonNullable
    ensures NfaRepMinRE((q.min - 1) as nat, qid, r1, c, pc1, em)
    ensures GetPcRE(c, em) == Some(RB.SetQuantToClock(qid, false))
    ensures NfaRepRE(r1, c, em + 1, e1)
    ensures GetPcRE(c, e1) == Some(if q.greedy then RB.Fork(em, e1 + 1) else RB.Fork(e1 + 1, em))
    ensures pc2 == e1 + 1
  {
    var mn1 := (q.min - 1) as nat;
    em :| NfaRepMinRE(mn1, qid, r1, c, pc1, em)
      && GetPcRE(c, em) == Some(RB.SetQuantToClock(qid, false))
      && (exists ex: nat ::
            NfaRepRE(r1, c, em + 1, ex)
            && GetPcRE(c, ex) == Some(if q.greedy then RB.Fork(em, ex + 1) else RB.Fork(ex + 1, em))
            && pc2 == ex + 1);
    e1 :| NfaRepRE(r1, c, em + 1, e1)
      && GetPcRE(c, e1) == Some(if q.greedy then RB.Fork(em, e1 + 1) else RB.Fork(e1 + 1, em))
      && pc2 == e1 + 1;
  }

  // The compiler adheres to the representation predicate (Thm: compile_nfa_rep).
  /** The main compiler-correctness theorem: for any fragment regex, `CP.compile` emits
      code satisfying `NfaRepRE` against it — the RegElk analogue of Linden's
      `compile_nfa_rep`. */
  lemma CompileNfaRepRE(re: R.regex, start: nat, tl: CP.treelist, next: int, prev: RB.code)
    requires LookBehindFragmentRE(re)
    requires CP.compile(re, start, CP.Progress) == (tl, next)
    requires start == |prev|
    ensures next >= 0 && NfaRepRE(re, prev + Flat(tl), start, next as nat)
    decreases CP.rsize(re), 1
  {
    FreshCorrectRE(re, start, tl, next);
    match re
    case Re_empty =>
      assert prev + Flat(tl) == prev;
    case Re_character(ch) =>
      assert Flat(tl) == [RB.Consume(T.ExpectationOf(ch))];
      GetFirstRE(Flat(tl), prev);
    case Re_anchor(a) =>
      assert Flat(tl) == [RB.AnchorAssertion(a)];
      GetFirstRE(Flat(tl), prev);
    case Re_lookaround(lid, la, _) =>
      assert Flat(tl) == [if la.Lookahead? || la.Lookbehind?
                          then RB.CheckOracle(lid) else RB.NegCheckOracle(lid)];
      GetFirstRE(Flat(tl), prev);
    case Re_alt(r1, r2) =>
      var (l1, f1) := CP.compile(r1, start + 1, CP.Progress);
      var (l2, f2) := CP.compile(r2, f1 + 1, CP.Progress);
      FreshCorrectRE(r1, start + 1, l1, f1);
      FreshCorrectRE(r2, f1 + 1, l2, f2);
      ChainFour(CP.Leaf([RB.Fork(start + 1, f1 + 1)]), l1, CP.Leaf([RB.Jmp(f2)]), l2);
      assert Flat(tl) == [RB.Fork(start + 1, f1 + 1)] + Flat(l1) + [RB.Jmp(f2)] + Flat(l2);
      // r1 region
      var pre1 := prev + [RB.Fork(start + 1, f1 + 1)];
      CompileNfaRepRE(r1, start + 1, l1, f1, pre1);
      NfaRepExtendRE(r1, pre1 + Flat(l1), start + 1, f1 as nat, [RB.Jmp(f2)] + Flat(l2));
      assert (pre1 + Flat(l1)) + ([RB.Jmp(f2)] + Flat(l2)) == prev + Flat(tl);
      // r2 region
      var pre2 := prev + [RB.Fork(start + 1, f1 + 1)] + Flat(l1) + [RB.Jmp(f2)];
      assert |pre2| == f1 + 1;
      CompileNfaRepRE(r2, (f1 + 1) as nat, l2, f2, pre2);
      assert pre2 + Flat(l2) == prev + Flat(tl);
      // instruction facts
      GetFirstRE(Flat(tl), prev);
      assert prev + Flat(tl) == (prev + [RB.Fork(start + 1, f1 + 1)] + Flat(l1)) + ([RB.Jmp(f2)] + Flat(l2));
      assert |prev + [RB.Fork(start + 1, f1 + 1)] + Flat(l1)| == f1;
      GetFirstRE([RB.Jmp(f2)] + Flat(l2), prev + [RB.Fork(start + 1, f1 + 1)] + Flat(l1));
      assert GetPcRE(prev + Flat(tl), start) == Some(RB.Fork(start + 1, f1 + 1))
          && NfaRepRE(r1, prev + Flat(tl), start + 1, f1 as nat)
          && GetPcRE(prev + Flat(tl), f1 as nat) == Some(RB.Jmp(f2))
          && NfaRepRE(r2, prev + Flat(tl), (f1 + 1) as nat, f2 as nat);
      assert next == f2;
      // Guide the NfaRepRE(Re_alt) fold in a collapsed context: the perturbed
      // LookBehindFragmentRE axiom (now one conjunct lighter) otherwise sends
      // this existential witness into a matching loop (batch 45, ~242M rlimit).
      assert NfaRepRE(re, prev + Flat(tl), start, next as nat) by {
        hide *;
        reveal NfaRepRE;
        assert GetPcRE(prev + Flat(tl), start) == Some(RB.Fork(start + 1, f1 + 1));
        assert NfaRepRE(r1, prev + Flat(tl), start + 1, f1 as nat);
        assert GetPcRE(prev + Flat(tl), f1 as nat) == Some(RB.Jmp(f2));
        assert NfaRepRE(r2, prev + Flat(tl), (f1 + 1) as nat, f2 as nat);
        assert next == f2;
      }
    case Re_con(r1, r2) =>
      var (l1, f1) := CP.compile(r1, start, CP.Progress);
      var (l2, f2) := CP.compile(r2, f1, CP.Progress);
      FreshCorrectRE(r1, start, l1, f1);
      FreshCorrectRE(r2, f1, l2, f2);
      FlattenApp(l1, Flat(l2));
      assert Flat(tl) == Flat(l1) + Flat(l2);
      CompileNfaRepRE(r1, start, l1, f1, prev);
      NfaRepExtendRE(r1, prev + Flat(l1), start, f1 as nat, Flat(l2));
      assert (prev + Flat(l1)) + Flat(l2) == prev + Flat(tl);
      assert |prev + Flat(l1)| == f1;
      CompileNfaRepRE(r2, f1 as nat, l2, f2, prev + Flat(l1));
      assert (prev + Flat(l1)) + Flat(l2) == prev + Flat(tl);
      assert NfaRepRE(r1, prev + Flat(tl), start, f1 as nat) && NfaRepRE(r2, prev + Flat(tl), f1 as nat, f2 as nat);
    case Re_quant(nul, qid, q, r1) =>
      if q.min == 0 && q.max == None {
        var (iter_code, iter_f) := CP.compile(r1, start + 3, CP.Progress);
        FreshCorrectRE(r1, start + 3, iter_code, iter_f);
        var fork := if q.greedy then RB.Fork(start + 1, iter_f + 2) else RB.Fork(iter_f + 2, start + 1);
        var hdr := [fork, RB.SetQuantToClock(qid, false), RB.BeginLoop];
        ChainFour(CP.Leaf([]), CP.Leaf(hdr), iter_code, CP.Leaf([RB.EndLoop, RB.Jmp(start)]));
        assert Flat(tl) == hdr + Flat(iter_code) + [RB.EndLoop, RB.Jmp(start)];
        var pre1 := prev + hdr;
        assert |pre1| == start + 3;
        CompileNfaRepRE(r1, start + 3, iter_code, iter_f, pre1);
        NfaRepExtendRE(r1, pre1 + Flat(iter_code), start + 3, iter_f as nat, [RB.EndLoop, RB.Jmp(start)]);
        assert (pre1 + Flat(iter_code)) + [RB.EndLoop, RB.Jmp(start)] == prev + Flat(tl);
        GetPrefixRE(Flat(tl), 0, prev);
        GetPrefixRE(Flat(tl), 1, prev);
        GetPrefixRE(Flat(tl), 2, prev);
        assert prev + Flat(tl) == (prev + hdr + Flat(iter_code)) + [RB.EndLoop, RB.Jmp(start)];
        assert |prev + hdr + Flat(iter_code)| == iter_f;
        GetFirstRE([RB.EndLoop, RB.Jmp(start)], prev + hdr + Flat(iter_code));
        GetPrefixRE([RB.EndLoop, RB.Jmp(start)], 1, prev + hdr + Flat(iter_code));
        assert GetPcRE(prev + Flat(tl), start) == Some(fork)
            && GetPcRE(prev + Flat(tl), start + 1) == Some(RB.SetQuantToClock(qid, false))
            && GetPcRE(prev + Flat(tl), start + 2) == Some(RB.BeginLoop)
            && NfaRepRE(r1, prev + Flat(tl), start + 3, iter_f as nat)
            && GetPcRE(prev + Flat(tl), iter_f as nat) == Some(RB.EndLoop)
            && GetPcRE(prev + Flat(tl), (iter_f + 1) as nat) == Some(RB.Jmp(start))
            && next == iter_f + 2;
      } else if q.max.Some? {
        var (min_code, min_f) := CP.repeat_min(q.min, qid, r1, start, CP.Progress);
        var (opt_code, opt_f) := CP.repeat_optional(q.max.value - q.min, qid, r1, min_f, CP.Progress, q.greedy);
        FreshCorrectMinRE(q.min as nat, qid, r1, start, min_code, min_f);
        FreshCorrectOptRE((q.max.value - q.min) as nat, q.greedy, qid, r1, min_f as nat, opt_code, opt_f);
        FlattenApp(min_code, Flat(opt_code));
        assert Flat(tl) == Flat(min_code) + Flat(opt_code);
        // forced copies
        CompileNfaRepMinRE(q.min as nat, qid, r1, start, min_code, min_f, prev);
        NfaRepExtendMinRE(q.min as nat, qid, r1, prev + Flat(min_code), start, min_f as nat, Flat(opt_code));
        assert (prev + Flat(min_code)) + Flat(opt_code) == prev + Flat(tl);
        // optional layers
        assert |prev + Flat(min_code)| == min_f;
        CompileNfaRepOptRE((q.max.value - q.min) as nat, q.greedy, qid, r1, min_f as nat, opt_code, opt_f, prev + Flat(min_code));
        assert NfaRepMinRE(q.min as nat, qid, r1, prev + Flat(tl), start, min_f as nat)
            && NfaRepOptRE((q.max.value - q.min) as nat, q.greedy, qid, r1, prev + Flat(tl), min_f as nat, opt_f as nat);
        NfaRepREQuantIntro(nul, qid, q, r1, prev + Flat(tl), start, min_f as nat, opt_f as nat);
      } else {
        // the do-while scheme (Compiler.dfy:107-112)
        var (min_code, min_f) := CP.repeat_min(q.min - 1, qid, r1, start, CP.Progress);
        var (body_code, body_f) := CP.compile(r1, min_f + 1, CP.Progress);
        FreshCorrectMinRE((q.min - 1) as nat, qid, r1, start, min_code, min_f);
        FreshCorrectRE(r1, (min_f + 1) as nat, body_code, body_f);
        var fork := if q.greedy then RB.Fork(min_f, body_f + 1) else RB.Fork(body_f + 1, min_f);
        ChainFour(min_code, CP.Leaf([RB.SetQuantToClock(qid, false)]), body_code, CP.Leaf([fork]));
        assert Flat(tl) == Flat(min_code) + [RB.SetQuantToClock(qid, false)] + Flat(body_code) + [fork];
        // forced copies
        CompileNfaRepMinRE((q.min - 1) as nat, qid, r1, start, min_code, min_f, prev);
        NfaRepExtendMinRE((q.min - 1) as nat, qid, r1, prev + Flat(min_code), start, min_f as nat,
                          [RB.SetQuantToClock(qid, false)] + Flat(body_code) + [fork]);
        assert (prev + Flat(min_code)) + ([RB.SetQuantToClock(qid, false)] + Flat(body_code) + [fork]) == prev + Flat(tl);
        // the last copy's clock-mark
        assert |prev + Flat(min_code)| == min_f;
        GetFirstRE([RB.SetQuantToClock(qid, false)] + Flat(body_code) + [fork], prev + Flat(min_code));
        // the guaranteed body
        var pre1 := prev + Flat(min_code) + [RB.SetQuantToClock(qid, false)];
        assert |pre1| == min_f + 1;
        CompileNfaRepRE(r1, (min_f + 1) as nat, body_code, body_f, pre1);
        NfaRepExtendRE(r1, pre1 + Flat(body_code), (min_f + 1) as nat, body_f as nat, [fork]);
        // Collapsed context: the perturbed LookBehindFragmentRE axiom otherwise
        // loops here (do-while case has the largest fact set), turning this
        // sequence equality into a >900s batch.
        assert (pre1 + Flat(body_code)) + [fork] == prev + Flat(tl) by {
          hide *;
          assert Flat(tl) == Flat(min_code) + [RB.SetQuantToClock(qid, false)] + Flat(body_code) + [fork];
          assert pre1 == prev + Flat(min_code) + [RB.SetQuantToClock(qid, false)];
        }
        // the backward fork
        assert |pre1 + Flat(body_code)| == body_f;
        GetFirstRE([fork], pre1 + Flat(body_code));
        assert GetPcRE(prev + Flat(tl), min_f as nat) == Some(RB.SetQuantToClock(qid, false))
            && NfaRepRE(r1, prev + Flat(tl), (min_f + 1) as nat, body_f as nat)
            && GetPcRE(prev + Flat(tl), body_f as nat) == Some(fork)
            && next == body_f + 1;
        NfaRepREPlusIntro(nul, qid, q, r1, prev + Flat(tl), start, min_f as nat, body_f as nat, (body_f + 1) as nat);
      }
    case Re_capture(cid, r1) =>
      var (l1, f1) := CP.compile(r1, start + 1, CP.Progress);
      FreshCorrectRE(r1, start + 1, l1, f1);
      ChainThree(CP.Leaf([RB.SetRegisterToCP(CP.start_reg(cid))]), l1, CP.Leaf([RB.SetRegisterToCP(CP.end_reg(cid))]));
      assert Flat(tl) == [RB.SetRegisterToCP(CP.start_reg(cid))] + Flat(l1) + [RB.SetRegisterToCP(CP.end_reg(cid))];
      var pre1 := prev + [RB.SetRegisterToCP(CP.start_reg(cid))];
      assert |pre1| == start + 1;
      CompileNfaRepRE(r1, start + 1, l1, f1, pre1);
      NfaRepExtendRE(r1, pre1 + Flat(l1), start + 1, f1 as nat, [RB.SetRegisterToCP(CP.end_reg(cid))]);
      assert (pre1 + Flat(l1)) + [RB.SetRegisterToCP(CP.end_reg(cid))] == prev + Flat(tl);
      GetFirstRE(Flat(tl), prev);
      assert prev + Flat(tl) == (prev + [RB.SetRegisterToCP(CP.start_reg(cid))] + Flat(l1)) + [RB.SetRegisterToCP(CP.end_reg(cid))];
      assert |prev + [RB.SetRegisterToCP(CP.start_reg(cid))] + Flat(l1)| == f1;
      GetFirstRE([RB.SetRegisterToCP(CP.end_reg(cid))], prev + [RB.SetRegisterToCP(CP.start_reg(cid))] + Flat(l1));
      assert GetPcRE(prev + Flat(tl), start) == Some(RB.SetRegisterToCP(CP.start_reg(cid)))
          && NfaRepRE(r1, prev + Flat(tl), start + 1, f1 as nat)
          && GetPcRE(prev + Flat(tl), f1 as nat) == Some(RB.SetRegisterToCP(CP.end_reg(cid)))
          && next == f1 + 1;
  }

  // Top-level: compile_to_bytecode of a fragment regex represents it from 0,
  // with the Accept terminator at the end label.
  /** Corollary of `CompileNfaRepRE` for the actual entry point
      `CP.compile_to_bytecode`: the whole program represents `re` from pc 0 to the
      compiler's fresh label, exactly where the trailing `Accept` instruction sits. */
  lemma CompileToBytecodeRepLookBehind(re: R.regex)
    requires LookBehindFragmentRE(re)
    ensures var code := CP.compile_to_bytecode(re);
      var next := CP.compile(re, 0, CP.Progress).1;
      next >= 0 && NfaRepRE(re, code, 0, next as nat)
      && GetPcRE(code, next as nat) == Some(RB.Accept)
      && |code| == next + 1
  {
    var (tl, next) := CP.compile(re, 0, CP.Progress);
    FreshCorrectRE(re, 0, tl, next);
    CompileNfaRepRE(re, 0, tl, next, []);
    assert [] + Flat(tl) == Flat(tl);
    FlattenApp(tl, [RB.Accept]);
    assert CP.compile_to_bytecode(re) == Flat(tl) + [RB.Accept];
    NfaRepExtendRE(re, Flat(tl), 0, next as nat, [RB.Accept]);
    assert GetPcRE(Flat(tl) + [RB.Accept], next as nat) == Some(RB.Accept) by {
      assert (Flat(tl) + [RB.Accept])[next as nat] == RB.Accept;
    }
  }

  /** `CompileToBytecodeRepLookBehind` for the ORACLE-BUILD entry point
      `CP.compile_to_write`: the build program represents `re` from pc 0 to
      the compiler's fresh label, where the `WriteOracle(l)` recorder sits
      instead of `Accept` — a build sweep records (and kills) rather than
      accepting, which is what makes the oracle statement all-positions. */
  lemma CompileToWriteRep(re: R.regex, l: R.lookid)
    requires LookBehindFragmentRE(re)
    ensures var code := CP.compile_to_write(re, l);
      var next := CP.compile(re, 0, CP.Progress).1;
      next >= 0 && NfaRepRE(re, code, 0, next as nat)
      && GetPcRE(code, next as nat) == Some(RB.WriteOracle(l))
      && |code| == next + 1
  {
    var (tl, next) := CP.compile(re, 0, CP.Progress);
    FreshCorrectRE(re, 0, tl, next);
    CompileNfaRepRE(re, 0, tl, next, []);
    assert [] + Flat(tl) == Flat(tl);
    FlattenApp(tl, [RB.WriteOracle(l)]);
    assert CP.compile_to_write(re, l) == Flat(tl) + [RB.WriteOracle(l)];
    NfaRepExtendRE(re, Flat(tl), 0, next as nat, [RB.WriteOracle(l)]);
    assert GetPcRE(Flat(tl) + [RB.WriteOracle(l)], next as nat) == Some(RB.WriteOracle(l)) by {
      assert (Flat(tl) + [RB.WriteOracle(l)])[next as nat] == RB.WriteOracle(l);
    }
  }

  // ===========================================================================
  // L4 (SHARED wall): the NESTED-fragment generalization of the
  // compile -> NfaRepRE correspondence. Every lemma below is a VERBATIM copy of
  // its `LookBehindFragmentRE`-gated original with the fragment hypothesis
  // WEAKENED to `NestedFragmentRE` and the mutual recursion routed to the
  // `*Nested` siblings. The swap is sound because the MAIN correspondence emits
  // a SINGLE `CheckOracle`/`NegCheckOracle` gate leaf at each lookaround node
  // (the body compiles into a separate per-lookaround table, NOT inline), so
  // NEITHER the label-arithmetic pass NOR the representation proof ever
  // destructs a look body: at `Re_lookaround` both proofs stop at the gate. The
  // structural cases thread the fragment unchanged (NestedFragmentRE has the
  // SAME plus-fragment quant shapes as LookBehindFragmentRE); the only relaxed
  // leaf, the lookaround, is exactly the one the proofs treat opaquely. This is
  // what lets a genuinely NESTED regex flow through the main correspondence.
  // ===========================================================================

  /** `FreshCorrectNestedRE` for `repeat_min` (nested-fragment variant of
      `FreshCorrectMinRE`). */
  lemma FreshCorrectMinNestedRE(k: nat, qid: R.quantid, r1: R.regex, start: nat, tl: CP.treelist, next: int)
    requires NestedFragmentRE(r1)
    requires CP.repeat_min(k, qid, r1, start, CP.Progress) == (tl, next)
    ensures next == start + |Flat(tl)|
    decreases CP.rsize(r1), k + 2
  {
    if k == 0 {
      FlattenApp(CP.Leaf([]), []);
    } else {
      var (body_code, new_f) := CP.compile(r1, start + 1, CP.Progress);
      FreshCorrectNestedRE(r1, start + 1, body_code, new_f);
      var (next_code, next_f) := CP.repeat_min(k - 1, qid, r1, new_f, CP.Progress);
      FreshCorrectMinNestedRE(k - 1, qid, r1, new_f as nat, next_code, next_f);
      var ch := CP.chain([CP.Leaf([RB.SetQuantToClock(qid, false)]), body_code, next_code]);
      assert Flat(ch) == [RB.SetQuantToClock(qid, false)] + Flat(body_code) + Flat(next_code) by {
        ChainThree(CP.Leaf([RB.SetQuantToClock(qid, false)]), body_code, next_code);
      }
    }
  }

  /** `FreshCorrectNestedRE` for `repeat_optional` (nested-fragment variant of
      `FreshCorrectOptRE`). */
  lemma FreshCorrectOptNestedRE(k: nat, greedy: bool, qid: R.quantid, r1: R.regex, start: nat, tl: CP.treelist, next: int)
    requires NestedFragmentRE(r1)
    requires CP.repeat_optional(k, qid, r1, start, CP.Progress, greedy) == (tl, next)
    ensures next == start + |Flat(tl)|
    decreases CP.rsize(r1), k + 2
  {
    if k == 0 {
      FlattenApp(CP.Leaf([]), []);
    } else {
      var (body_code, new_f) := CP.compile(r1, start + 3, CP.Progress);
      FreshCorrectNestedRE(r1, start + 3, body_code, new_f);
      var (next_code, next_f) := CP.repeat_optional(k - 1, qid, r1, new_f + 1, CP.Progress, greedy);
      FreshCorrectOptNestedRE(k - 1, greedy, qid, r1, (new_f + 1) as nat, next_code, next_f);
      var fork := if greedy then RB.Fork(start + 1, next_f) else RB.Fork(next_f, start + 1);
      var ch := CP.chain([CP.Leaf([fork, RB.SetQuantToClock(qid, false), RB.BeginLoop]), body_code, CP.Leaf([RB.EndLoop]), next_code]);
      assert Flat(ch) == [fork, RB.SetQuantToClock(qid, false), RB.BeginLoop] + Flat(body_code) + [RB.EndLoop] + Flat(next_code) by {
        ChainFour(CP.Leaf([fork, RB.SetQuantToClock(qid, false), RB.BeginLoop]), body_code, CP.Leaf([RB.EndLoop]), next_code);
      }
    }
  }

  /** Nested-fragment variant of `FreshCorrectRE`: the label-arithmetic pass for
      a regex whose lookaround bodies may nest. The `Re_lookaround` case is
      vacuous (the body is not touched — one gate leaf is emitted). */
  lemma FreshCorrectNestedRE(re: R.regex, start: nat, tl: CP.treelist, next: int)
    requires NestedFragmentRE(re)
    requires CP.compile(re, start, CP.Progress) == (tl, next)
    ensures next == start + |Flat(tl)|
    decreases CP.rsize(re), 1
  {
    match re
    case Re_empty =>
    case Re_character(_) =>
    case Re_anchor(_) =>
    case Re_lookaround(_, _, _) =>
    case Re_alt(r1, r2) =>
      var (l1, f1) := CP.compile(r1, start + 1, CP.Progress);
      var (l2, f2) := CP.compile(r2, f1 + 1, CP.Progress);
      FreshCorrectNestedRE(r1, start + 1, l1, f1);
      assert f1 >= 0;
      FreshCorrectNestedRE(r2, f1 + 1, l2, f2);
      var ch := CP.chain([CP.Leaf([RB.Fork(start + 1, f1 + 1)]), l1, CP.Leaf([RB.Jmp(f2)]), l2]);
      FlattenApp(l1, [RB.Jmp(f2)] + Flat(l2));
      FlattenApp(l2, []);
      assert Flat(ch) == [RB.Fork(start + 1, f1 + 1)] + Flat(l1) + [RB.Jmp(f2)] + Flat(l2) by {
        ChainFour(CP.Leaf([RB.Fork(start + 1, f1 + 1)]), l1, CP.Leaf([RB.Jmp(f2)]), l2);
      }
    case Re_con(r1, r2) =>
      var (l1, f1) := CP.compile(r1, start, CP.Progress);
      FreshCorrectNestedRE(r1, start, l1, f1);
      var (l2, f2) := CP.compile(r2, f1, CP.Progress);
      FreshCorrectNestedRE(r2, f1, l2, f2);
      FlattenApp(l1, Flat(l2));
    case Re_quant(nul, qid, q, r1) =>
      if q.min == 0 && q.max == None {
        var (iter_code, iter_f) := CP.compile(r1, start + 3, CP.Progress);
        FreshCorrectNestedRE(r1, start + 3, iter_code, iter_f);
        var fork := if q.greedy then RB.Fork(start + 1, iter_f + 2) else RB.Fork(iter_f + 2, start + 1);
        var ch := CP.chain([CP.Leaf([]),
                            CP.Leaf([fork, RB.SetQuantToClock(qid, false), RB.BeginLoop]),
                            iter_code,
                            CP.Leaf([RB.EndLoop, RB.Jmp(start)])]);
        assert Flat(ch) == [fork, RB.SetQuantToClock(qid, false), RB.BeginLoop] + Flat(iter_code) + [RB.EndLoop, RB.Jmp(start)] by {
          ChainFour(CP.Leaf([]), CP.Leaf([fork, RB.SetQuantToClock(qid, false), RB.BeginLoop]), iter_code, CP.Leaf([RB.EndLoop, RB.Jmp(start)]));
        }
      } else if q.max.Some? {
        var (min_code, min_f) := CP.repeat_min(q.min, qid, r1, start, CP.Progress);
        FreshCorrectMinNestedRE(q.min as nat, qid, r1, start, min_code, min_f);
        var (opt_code, opt_f) := CP.repeat_optional(q.max.value - q.min, qid, r1, min_f, CP.Progress, q.greedy);
        FreshCorrectOptNestedRE((q.max.value - q.min) as nat, q.greedy, qid, r1, min_f as nat, opt_code, opt_f);
        FlattenApp(min_code, Flat(opt_code));
        assert Flat(tl) == Flat(min_code) + Flat(opt_code);
      } else {
        var (min_code, min_f) := CP.repeat_min(q.min - 1, qid, r1, start, CP.Progress);
        FreshCorrectMinNestedRE((q.min - 1) as nat, qid, r1, start, min_code, min_f);
        var (body_code, body_f) := CP.compile(r1, min_f + 1, CP.Progress);
        FreshCorrectNestedRE(r1, (min_f + 1) as nat, body_code, body_f);
        var fork := if q.greedy then RB.Fork(min_f, body_f + 1) else RB.Fork(body_f + 1, min_f);
        var ch := CP.chain([min_code, CP.Leaf([RB.SetQuantToClock(qid, false)]), body_code, CP.Leaf([fork])]);
        assert Flat(ch) == Flat(min_code) + [RB.SetQuantToClock(qid, false)] + Flat(body_code) + [fork] by {
          ChainFour(min_code, CP.Leaf([RB.SetQuantToClock(qid, false)]), body_code, CP.Leaf([fork]));
        }
      }
    case Re_capture(cid, r1) =>
      var (l1, f1) := CP.compile(r1, start + 1, CP.Progress);
      FreshCorrectNestedRE(r1, start + 1, l1, f1);
      var ch := CP.chain([CP.Leaf([RB.SetRegisterToCP(CP.start_reg(cid))]), l1, CP.Leaf([RB.SetRegisterToCP(CP.end_reg(cid))])]);
      assert Flat(ch) == [RB.SetRegisterToCP(CP.start_reg(cid))] + Flat(l1) + [RB.SetRegisterToCP(CP.end_reg(cid))] by {
        ChainThree(CP.Leaf([RB.SetRegisterToCP(CP.start_reg(cid))]), l1, CP.Leaf([RB.SetRegisterToCP(CP.end_reg(cid))]));
      }
  }

  /** Nested-fragment variant of `CompileNfaRepMinRE`. */
  lemma CompileNfaRepMinNestedRE(k: nat, qid: R.quantid, r1: R.regex, start: nat, tl: CP.treelist, next: int, prev: RB.code)
    requires NestedFragmentRE(r1)
    requires CP.repeat_min(k, qid, r1, start, CP.Progress) == (tl, next)
    requires start == |prev|
    ensures next >= 0 && NfaRepMinRE(k, qid, r1, prev + Flat(tl), start, next as nat)
    decreases CP.rsize(r1), k + 2
  {
    FreshCorrectMinNestedRE(k, qid, r1, start, tl, next);
    if k == 0 {
      assert prev + Flat(tl) == prev;
    } else {
      var (body_code, new_f) := CP.compile(r1, start + 1, CP.Progress);
      var (next_code, next_f) := CP.repeat_min(k - 1, qid, r1, new_f, CP.Progress);
      FreshCorrectNestedRE(r1, start + 1, body_code, new_f);
      FreshCorrectMinNestedRE(k - 1, qid, r1, new_f as nat, next_code, next_f);
      ChainThree(CP.Leaf([RB.SetQuantToClock(qid, false)]), body_code, next_code);
      assert Flat(tl) == [RB.SetQuantToClock(qid, false)] + Flat(body_code) + Flat(next_code);
      // body region
      var pre1 := prev + [RB.SetQuantToClock(qid, false)];
      assert |pre1| == start + 1;
      CompileNfaRepNestedRE(r1, start + 1, body_code, new_f, pre1);
      NfaRepExtendRE(r1, pre1 + Flat(body_code), start + 1, new_f as nat, Flat(next_code));
      assert (pre1 + Flat(body_code)) + Flat(next_code) == prev + Flat(tl);
      // remaining copies
      var pre2 := prev + [RB.SetQuantToClock(qid, false)] + Flat(body_code);
      assert |pre2| == new_f;
      CompileNfaRepMinNestedRE(k - 1, qid, r1, new_f as nat, next_code, next_f, pre2);
      assert pre2 + Flat(next_code) == prev + Flat(tl);
      // instruction fact
      GetFirstRE(Flat(tl), prev);
      assert GetPcRE(prev + Flat(tl), start) == Some(RB.SetQuantToClock(qid, false))
          && NfaRepRE(r1, prev + Flat(tl), start + 1, new_f as nat)
          && NfaRepMinRE(k - 1, qid, r1, prev + Flat(tl), new_f as nat, next_f as nat);
    }
  }

  /** Nested-fragment variant of `CompileNfaRepOptRE`. */
  lemma CompileNfaRepOptNestedRE(k: nat, greedy: bool, qid: R.quantid, r1: R.regex, start: nat, tl: CP.treelist, next: int, prev: RB.code)
    requires NestedFragmentRE(r1)
    requires CP.repeat_optional(k, qid, r1, start, CP.Progress, greedy) == (tl, next)
    requires start == |prev|
    ensures next >= 0 && NfaRepOptRE(k, greedy, qid, r1, prev + Flat(tl), start, next as nat)
    decreases CP.rsize(r1), k + 2
  {
    FreshCorrectOptNestedRE(k, greedy, qid, r1, start, tl, next);
    if k == 0 {
      assert prev + Flat(tl) == prev;
    } else {
      var (body_code, new_f) := CP.compile(r1, start + 3, CP.Progress);
      var (next_code, next_f) := CP.repeat_optional(k - 1, qid, r1, new_f + 1, CP.Progress, greedy);
      FreshCorrectNestedRE(r1, start + 3, body_code, new_f);
      FreshCorrectOptNestedRE(k - 1, greedy, qid, r1, (new_f + 1) as nat, next_code, next_f);
      var fork := if greedy then RB.Fork(start + 1, next_f) else RB.Fork(next_f, start + 1);
      var hdr := [fork, RB.SetQuantToClock(qid, false), RB.BeginLoop];
      ChainFour(CP.Leaf(hdr), body_code, CP.Leaf([RB.EndLoop]), next_code);
      assert Flat(tl) == hdr + Flat(body_code) + [RB.EndLoop] + Flat(next_code);
      // body region
      var pre1 := prev + hdr;
      assert |pre1| == start + 3;
      CompileNfaRepNestedRE(r1, start + 3, body_code, new_f, pre1);
      NfaRepExtendRE(r1, pre1 + Flat(body_code), start + 3, new_f as nat, [RB.EndLoop] + Flat(next_code));
      assert (pre1 + Flat(body_code)) + ([RB.EndLoop] + Flat(next_code)) == prev + Flat(tl);
      // remaining layers
      var pre2 := prev + hdr + Flat(body_code) + [RB.EndLoop];
      assert |pre2| == new_f + 1;
      CompileNfaRepOptNestedRE(k - 1, greedy, qid, r1, (new_f + 1) as nat, next_code, next_f, pre2);
      assert pre2 + Flat(next_code) == prev + Flat(tl);
      // instruction facts
      GetPrefixRE(Flat(tl), 0, prev);
      GetPrefixRE(Flat(tl), 1, prev);
      GetPrefixRE(Flat(tl), 2, prev);
      assert prev + Flat(tl) == (prev + hdr + Flat(body_code)) + ([RB.EndLoop] + Flat(next_code));
      assert |prev + hdr + Flat(body_code)| == new_f;
      GetFirstRE([RB.EndLoop] + Flat(next_code), prev + hdr + Flat(body_code));
      assert GetPcRE(prev + Flat(tl), start) == Some(fork)
          && GetPcRE(prev + Flat(tl), start + 1) == Some(RB.SetQuantToClock(qid, false))
          && GetPcRE(prev + Flat(tl), start + 2) == Some(RB.BeginLoop)
          && NfaRepRE(r1, prev + Flat(tl), start + 3, new_f as nat)
          && GetPcRE(prev + Flat(tl), new_f as nat) == Some(RB.EndLoop)
          && NfaRepOptRE(k - 1, greedy, qid, r1, prev + Flat(tl), (new_f + 1) as nat, next_f as nat);
    }
  }

  /** The main compiler-correctness theorem, NESTED-fragment variant of
      `CompileNfaRepRE`: for any regex in the nested lookaround fragment,
      `CP.compile` emits code satisfying `NfaRepRE`. The `Re_lookaround` case is
      unchanged from the depth-1 original — it emits the single gate leaf and
      never inspects the (possibly nested) body. */
  lemma CompileNfaRepNestedRE(re: R.regex, start: nat, tl: CP.treelist, next: int, prev: RB.code)
    requires NestedFragmentRE(re)
    requires CP.compile(re, start, CP.Progress) == (tl, next)
    requires start == |prev|
    ensures next >= 0 && NfaRepRE(re, prev + Flat(tl), start, next as nat)
    decreases CP.rsize(re), 1
  {
    FreshCorrectNestedRE(re, start, tl, next);
    match re
    case Re_empty =>
      assert prev + Flat(tl) == prev;
    case Re_character(ch) =>
      assert Flat(tl) == [RB.Consume(T.ExpectationOf(ch))];
      GetFirstRE(Flat(tl), prev);
    case Re_anchor(a) =>
      assert Flat(tl) == [RB.AnchorAssertion(a)];
      GetFirstRE(Flat(tl), prev);
    case Re_lookaround(lid, la, _) =>
      assert Flat(tl) == [if la.Lookahead? || la.Lookbehind?
                          then RB.CheckOracle(lid) else RB.NegCheckOracle(lid)];
      GetFirstRE(Flat(tl), prev);
    case Re_alt(r1, r2) =>
      var (l1, f1) := CP.compile(r1, start + 1, CP.Progress);
      var (l2, f2) := CP.compile(r2, f1 + 1, CP.Progress);
      FreshCorrectNestedRE(r1, start + 1, l1, f1);
      FreshCorrectNestedRE(r2, f1 + 1, l2, f2);
      ChainFour(CP.Leaf([RB.Fork(start + 1, f1 + 1)]), l1, CP.Leaf([RB.Jmp(f2)]), l2);
      assert Flat(tl) == [RB.Fork(start + 1, f1 + 1)] + Flat(l1) + [RB.Jmp(f2)] + Flat(l2);
      // r1 region
      var pre1 := prev + [RB.Fork(start + 1, f1 + 1)];
      CompileNfaRepNestedRE(r1, start + 1, l1, f1, pre1);
      NfaRepExtendRE(r1, pre1 + Flat(l1), start + 1, f1 as nat, [RB.Jmp(f2)] + Flat(l2));
      assert (pre1 + Flat(l1)) + ([RB.Jmp(f2)] + Flat(l2)) == prev + Flat(tl);
      // r2 region
      var pre2 := prev + [RB.Fork(start + 1, f1 + 1)] + Flat(l1) + [RB.Jmp(f2)];
      assert |pre2| == f1 + 1;
      CompileNfaRepNestedRE(r2, (f1 + 1) as nat, l2, f2, pre2);
      assert pre2 + Flat(l2) == prev + Flat(tl);
      // instruction facts
      GetFirstRE(Flat(tl), prev);
      assert prev + Flat(tl) == (prev + [RB.Fork(start + 1, f1 + 1)] + Flat(l1)) + ([RB.Jmp(f2)] + Flat(l2));
      assert |prev + [RB.Fork(start + 1, f1 + 1)] + Flat(l1)| == f1;
      GetFirstRE([RB.Jmp(f2)] + Flat(l2), prev + [RB.Fork(start + 1, f1 + 1)] + Flat(l1));
      assert GetPcRE(prev + Flat(tl), start) == Some(RB.Fork(start + 1, f1 + 1))
          && NfaRepRE(r1, prev + Flat(tl), start + 1, f1 as nat)
          && GetPcRE(prev + Flat(tl), f1 as nat) == Some(RB.Jmp(f2))
          && NfaRepRE(r2, prev + Flat(tl), (f1 + 1) as nat, f2 as nat);
      assert next == f2;
      // Guide the NfaRepRE(Re_alt) fold in a collapsed context (mirrors the
      // depth-1 original: the fragment axiom otherwise loops the witness).
      assert NfaRepRE(re, prev + Flat(tl), start, next as nat) by {
        hide *;
        reveal NfaRepRE;
        assert GetPcRE(prev + Flat(tl), start) == Some(RB.Fork(start + 1, f1 + 1));
        assert NfaRepRE(r1, prev + Flat(tl), start + 1, f1 as nat);
        assert GetPcRE(prev + Flat(tl), f1 as nat) == Some(RB.Jmp(f2));
        assert NfaRepRE(r2, prev + Flat(tl), (f1 + 1) as nat, f2 as nat);
        assert next == f2;
      }
    case Re_con(r1, r2) =>
      var (l1, f1) := CP.compile(r1, start, CP.Progress);
      var (l2, f2) := CP.compile(r2, f1, CP.Progress);
      FreshCorrectNestedRE(r1, start, l1, f1);
      FreshCorrectNestedRE(r2, f1, l2, f2);
      FlattenApp(l1, Flat(l2));
      assert Flat(tl) == Flat(l1) + Flat(l2);
      CompileNfaRepNestedRE(r1, start, l1, f1, prev);
      NfaRepExtendRE(r1, prev + Flat(l1), start, f1 as nat, Flat(l2));
      assert (prev + Flat(l1)) + Flat(l2) == prev + Flat(tl);
      assert |prev + Flat(l1)| == f1;
      CompileNfaRepNestedRE(r2, f1 as nat, l2, f2, prev + Flat(l1));
      assert (prev + Flat(l1)) + Flat(l2) == prev + Flat(tl);
      assert NfaRepRE(r1, prev + Flat(tl), start, f1 as nat) && NfaRepRE(r2, prev + Flat(tl), f1 as nat, f2 as nat);
    case Re_quant(nul, qid, q, r1) =>
      if q.min == 0 && q.max == None {
        var (iter_code, iter_f) := CP.compile(r1, start + 3, CP.Progress);
        FreshCorrectNestedRE(r1, start + 3, iter_code, iter_f);
        var fork := if q.greedy then RB.Fork(start + 1, iter_f + 2) else RB.Fork(iter_f + 2, start + 1);
        var hdr := [fork, RB.SetQuantToClock(qid, false), RB.BeginLoop];
        ChainFour(CP.Leaf([]), CP.Leaf(hdr), iter_code, CP.Leaf([RB.EndLoop, RB.Jmp(start)]));
        assert Flat(tl) == hdr + Flat(iter_code) + [RB.EndLoop, RB.Jmp(start)];
        var pre1 := prev + hdr;
        assert |pre1| == start + 3;
        CompileNfaRepNestedRE(r1, start + 3, iter_code, iter_f, pre1);
        NfaRepExtendRE(r1, pre1 + Flat(iter_code), start + 3, iter_f as nat, [RB.EndLoop, RB.Jmp(start)]);
        assert (pre1 + Flat(iter_code)) + [RB.EndLoop, RB.Jmp(start)] == prev + Flat(tl);
        GetPrefixRE(Flat(tl), 0, prev);
        GetPrefixRE(Flat(tl), 1, prev);
        GetPrefixRE(Flat(tl), 2, prev);
        assert prev + Flat(tl) == (prev + hdr + Flat(iter_code)) + [RB.EndLoop, RB.Jmp(start)];
        assert |prev + hdr + Flat(iter_code)| == iter_f;
        GetFirstRE([RB.EndLoop, RB.Jmp(start)], prev + hdr + Flat(iter_code));
        GetPrefixRE([RB.EndLoop, RB.Jmp(start)], 1, prev + hdr + Flat(iter_code));
        assert GetPcRE(prev + Flat(tl), start) == Some(fork)
            && GetPcRE(prev + Flat(tl), start + 1) == Some(RB.SetQuantToClock(qid, false))
            && GetPcRE(prev + Flat(tl), start + 2) == Some(RB.BeginLoop)
            && NfaRepRE(r1, prev + Flat(tl), start + 3, iter_f as nat)
            && GetPcRE(prev + Flat(tl), iter_f as nat) == Some(RB.EndLoop)
            && GetPcRE(prev + Flat(tl), (iter_f + 1) as nat) == Some(RB.Jmp(start))
            && next == iter_f + 2;
      } else if q.max.Some? {
        var (min_code, min_f) := CP.repeat_min(q.min, qid, r1, start, CP.Progress);
        var (opt_code, opt_f) := CP.repeat_optional(q.max.value - q.min, qid, r1, min_f, CP.Progress, q.greedy);
        FreshCorrectMinNestedRE(q.min as nat, qid, r1, start, min_code, min_f);
        FreshCorrectOptNestedRE((q.max.value - q.min) as nat, q.greedy, qid, r1, min_f as nat, opt_code, opt_f);
        FlattenApp(min_code, Flat(opt_code));
        assert Flat(tl) == Flat(min_code) + Flat(opt_code);
        // forced copies
        CompileNfaRepMinNestedRE(q.min as nat, qid, r1, start, min_code, min_f, prev);
        NfaRepExtendMinRE(q.min as nat, qid, r1, prev + Flat(min_code), start, min_f as nat, Flat(opt_code));
        assert (prev + Flat(min_code)) + Flat(opt_code) == prev + Flat(tl);
        // optional layers
        assert |prev + Flat(min_code)| == min_f;
        CompileNfaRepOptNestedRE((q.max.value - q.min) as nat, q.greedy, qid, r1, min_f as nat, opt_code, opt_f, prev + Flat(min_code));
        assert NfaRepMinRE(q.min as nat, qid, r1, prev + Flat(tl), start, min_f as nat)
            && NfaRepOptRE((q.max.value - q.min) as nat, q.greedy, qid, r1, prev + Flat(tl), min_f as nat, opt_f as nat);
        NfaRepREQuantIntro(nul, qid, q, r1, prev + Flat(tl), start, min_f as nat, opt_f as nat);
      } else {
        // the do-while scheme (Compiler.dfy:107-112)
        var (min_code, min_f) := CP.repeat_min(q.min - 1, qid, r1, start, CP.Progress);
        var (body_code, body_f) := CP.compile(r1, min_f + 1, CP.Progress);
        FreshCorrectMinNestedRE((q.min - 1) as nat, qid, r1, start, min_code, min_f);
        FreshCorrectNestedRE(r1, (min_f + 1) as nat, body_code, body_f);
        var fork := if q.greedy then RB.Fork(min_f, body_f + 1) else RB.Fork(body_f + 1, min_f);
        ChainFour(min_code, CP.Leaf([RB.SetQuantToClock(qid, false)]), body_code, CP.Leaf([fork]));
        assert Flat(tl) == Flat(min_code) + [RB.SetQuantToClock(qid, false)] + Flat(body_code) + [fork];
        // forced copies
        CompileNfaRepMinNestedRE((q.min - 1) as nat, qid, r1, start, min_code, min_f, prev);
        NfaRepExtendMinRE((q.min - 1) as nat, qid, r1, prev + Flat(min_code), start, min_f as nat,
                          [RB.SetQuantToClock(qid, false)] + Flat(body_code) + [fork]);
        assert (prev + Flat(min_code)) + ([RB.SetQuantToClock(qid, false)] + Flat(body_code) + [fork]) == prev + Flat(tl);
        // the last copy's clock-mark
        assert |prev + Flat(min_code)| == min_f;
        GetFirstRE([RB.SetQuantToClock(qid, false)] + Flat(body_code) + [fork], prev + Flat(min_code));
        // the guaranteed body
        var pre1 := prev + Flat(min_code) + [RB.SetQuantToClock(qid, false)];
        assert |pre1| == min_f + 1;
        CompileNfaRepNestedRE(r1, (min_f + 1) as nat, body_code, body_f, pre1);
        NfaRepExtendRE(r1, pre1 + Flat(body_code), (min_f + 1) as nat, body_f as nat, [fork]);
        // Collapsed context (mirrors the depth-1 original's do-while guard).
        assert (pre1 + Flat(body_code)) + [fork] == prev + Flat(tl) by {
          hide *;
          assert Flat(tl) == Flat(min_code) + [RB.SetQuantToClock(qid, false)] + Flat(body_code) + [fork];
          assert pre1 == prev + Flat(min_code) + [RB.SetQuantToClock(qid, false)];
        }
        // the backward fork
        assert |pre1 + Flat(body_code)| == body_f;
        GetFirstRE([fork], pre1 + Flat(body_code));
        assert GetPcRE(prev + Flat(tl), min_f as nat) == Some(RB.SetQuantToClock(qid, false))
            && NfaRepRE(r1, prev + Flat(tl), (min_f + 1) as nat, body_f as nat)
            && GetPcRE(prev + Flat(tl), body_f as nat) == Some(fork)
            && next == body_f + 1;
        NfaRepREPlusIntro(nul, qid, q, r1, prev + Flat(tl), start, min_f as nat, body_f as nat, (body_f + 1) as nat);
      }
    case Re_capture(cid, r1) =>
      var (l1, f1) := CP.compile(r1, start + 1, CP.Progress);
      FreshCorrectNestedRE(r1, start + 1, l1, f1);
      ChainThree(CP.Leaf([RB.SetRegisterToCP(CP.start_reg(cid))]), l1, CP.Leaf([RB.SetRegisterToCP(CP.end_reg(cid))]));
      assert Flat(tl) == [RB.SetRegisterToCP(CP.start_reg(cid))] + Flat(l1) + [RB.SetRegisterToCP(CP.end_reg(cid))];
      var pre1 := prev + [RB.SetRegisterToCP(CP.start_reg(cid))];
      assert |pre1| == start + 1;
      CompileNfaRepNestedRE(r1, start + 1, l1, f1, pre1);
      NfaRepExtendRE(r1, pre1 + Flat(l1), start + 1, f1 as nat, [RB.SetRegisterToCP(CP.end_reg(cid))]);
      assert (pre1 + Flat(l1)) + [RB.SetRegisterToCP(CP.end_reg(cid))] == prev + Flat(tl);
      GetFirstRE(Flat(tl), prev);
      assert prev + Flat(tl) == (prev + [RB.SetRegisterToCP(CP.start_reg(cid))] + Flat(l1)) + [RB.SetRegisterToCP(CP.end_reg(cid))];
      assert |prev + [RB.SetRegisterToCP(CP.start_reg(cid))] + Flat(l1)| == f1;
      GetFirstRE([RB.SetRegisterToCP(CP.end_reg(cid))], prev + [RB.SetRegisterToCP(CP.start_reg(cid))] + Flat(l1));
      assert GetPcRE(prev + Flat(tl), start) == Some(RB.SetRegisterToCP(CP.start_reg(cid)))
          && NfaRepRE(r1, prev + Flat(tl), start + 1, f1 as nat)
          && GetPcRE(prev + Flat(tl), f1 as nat) == Some(RB.SetRegisterToCP(CP.end_reg(cid)))
          && next == f1 + 1;
  }

  /** Nested-fragment variant of `CompileToBytecodeRepLookBehind`: the whole
      program represents a nested-fragment `re` from pc 0 to the fresh label
      where the trailing `Accept` sits. */
  lemma CompileToBytecodeRepNested(re: R.regex)
    requires NestedFragmentRE(re)
    ensures var code := CP.compile_to_bytecode(re);
      var next := CP.compile(re, 0, CP.Progress).1;
      next >= 0 && NfaRepRE(re, code, 0, next as nat)
      && GetPcRE(code, next as nat) == Some(RB.Accept)
      && |code| == next + 1
  {
    var (tl, next) := CP.compile(re, 0, CP.Progress);
    FreshCorrectNestedRE(re, 0, tl, next);
    CompileNfaRepNestedRE(re, 0, tl, next, []);
    assert [] + Flat(tl) == Flat(tl);
    FlattenApp(tl, [RB.Accept]);
    assert CP.compile_to_bytecode(re) == Flat(tl) + [RB.Accept];
    NfaRepExtendRE(re, Flat(tl), 0, next as nat, [RB.Accept]);
    assert GetPcRE(Flat(tl) + [RB.Accept], next as nat) == Some(RB.Accept) by {
      assert (Flat(tl) + [RB.Accept])[next as nat] == RB.Accept;
    }
  }

  /** Nested-fragment variant of `CompileToWriteRep`: the ORACLE-BUILD entry
      point for a nested-fragment `re` — the build program represents `re` from
      pc 0 to the fresh label where the `WriteOracle(l)` recorder sits. This is
      the correspondence the oracle-build establisher and the value keystone
      need at depth k. */
  lemma CompileToWriteRepNested(re: R.regex, l: R.lookid)
    requires NestedFragmentRE(re)
    ensures var code := CP.compile_to_write(re, l);
      var next := CP.compile(re, 0, CP.Progress).1;
      next >= 0 && NfaRepRE(re, code, 0, next as nat)
      && GetPcRE(code, next as nat) == Some(RB.WriteOracle(l))
      && |code| == next + 1
  {
    var (tl, next) := CP.compile(re, 0, CP.Progress);
    FreshCorrectNestedRE(re, 0, tl, next);
    CompileNfaRepNestedRE(re, 0, tl, next, []);
    assert [] + Flat(tl) == Flat(tl);
    FlattenApp(tl, [RB.WriteOracle(l)]);
    assert CP.compile_to_write(re, l) == Flat(tl) + [RB.WriteOracle(l)];
    NfaRepExtendRE(re, Flat(tl), 0, next as nat, [RB.WriteOracle(l)]);
    assert GetPcRE(Flat(tl) + [RB.WriteOracle(l)], next as nat) == Some(RB.WriteOracle(l)) by {
      assert (Flat(tl) + [RB.WriteOracle(l)])[next as nat] == RB.WriteOracle(l);
    }
  }

  /** `CompileToBytecodeRepLookBehind` restricted to the plus fragment — the
      signature the plus-gated downstream files consume. */
  lemma CompileToBytecodeRepPlus(re: R.regex)
    requires PlusFragmentRE(re)
    ensures var code := CP.compile_to_bytecode(re);
      var next := CP.compile(re, 0, CP.Progress).1;
      next >= 0 && NfaRepRE(re, code, 0, next as nat)
      && GetPcRE(code, next as nat) == Some(RB.Accept)
      && |code| == next + 1
  {
    PlusIsLookBehindFragmentRE(re);
    CompileToBytecodeRepLookBehind(re);
  }

  /** `CompileToBytecodeRepPlus` restricted to the quantifier fragment — the
      signature the quant-gated downstream files consume. */
  lemma CompileToBytecodeRepQuant(re: R.regex)
    requires QuantFragmentRE(re)
    ensures var code := CP.compile_to_bytecode(re);
      var next := CP.compile(re, 0, CP.Progress).1;
      next >= 0 && NfaRepRE(re, code, 0, next as nat)
      && GetPcRE(code, next as nat) == Some(RB.Accept)
      && |code| == next + 1
  {
    QuantIsPlusFragmentRE(re);
    CompileToBytecodeRepPlus(re);
  }

  /** `CompileToBytecodeRepQuant` restricted to the anchor fragment — the
      signature the anchor-gated downstream files consume. */
  lemma CompileToBytecodeRepAnchor(re: R.regex)
    requires AnchorFragmentRE(re)
    ensures var code := CP.compile_to_bytecode(re);
      var next := CP.compile(re, 0, CP.Progress).1;
      next >= 0 && NfaRepRE(re, code, 0, next as nat)
      && GetPcRE(code, next as nat) == Some(RB.Accept)
      && |code| == next + 1
  {
    AnchorIsQuantFragmentRE(re);
    CompileToBytecodeRepQuant(re);
  }

  /** `CompileToBytecodeRepAnchor` restricted to the star fragment — the
      signature every downstream (simulation-layer) file still consumes. */
  lemma CompileToBytecodeRep(re: R.regex)
    requires StarFragmentRE(re)
    ensures var code := CP.compile_to_bytecode(re);
      var next := CP.compile(re, 0, CP.Progress).1;
      next >= 0 && NfaRepRE(re, code, 0, next as nat)
      && GetPcRE(code, next as nat) == Some(RB.Accept)
      && |code| == next + 1
  {
    StarIsAnchorFragmentRE(re);
    CompileToBytecodeRepAnchor(re);
  }

  // ===========================================================================
  // Label-range facts (ports of nfa_rep_incr / compile_jumps)
  // ===========================================================================

  /** Star-fragment code contains no anchor instructions: every position
      strictly inside a star-fragment `NfaRepRE` block holds something other
      than an `AnchorAssertion`. Restores the unreachability argument the
      simulation layers use while they remain star-gated, now that
      `NfaRepRE`/`StepSpec` give anchors real meaning. */
  lemma StarFragmentNoAnchorInstr(re: R.regex, code: RB.code, start: nat, endl: nat, pc: nat)
    requires StarFragmentRE(re)
    requires NfaRepRE(re, code, start, endl)
    requires start <= pc < endl
    ensures GetPcRE(code, pc).Some? ==> !GetPcRE(code, pc).value.AnchorAssertion?
    decreases re
  {
    match re
    case Re_empty =>
      // start == endl: no pc strictly inside
      NfaRepIncrRE(re, code, start, endl);
    case Re_character(_) =>
      // pc == start: the Consume
    case Re_alt(r1, r2) =>
      var e1: nat :| GetPcRE(code, start) == Some(RB.Fork(start + 1, e1 + 1))
        && NfaRepRE(r1, code, start + 1, e1)
        && GetPcRE(code, e1) == Some(RB.Jmp(endl))
        && NfaRepRE(r2, code, e1 + 1, endl);
      NfaRepIncrRE(r1, code, start + 1, e1);
      NfaRepIncrRE(r2, code, e1 + 1, endl);
      if pc == start {
      } else if pc < e1 {
        StarFragmentNoAnchorInstr(r1, code, start + 1, e1, pc);
      } else if pc == e1 {
      } else {
        StarFragmentNoAnchorInstr(r2, code, e1 + 1, endl, pc);
      }
    case Re_con(r1, r2) =>
      var e1: nat :| NfaRepRE(r1, code, start, e1) && NfaRepRE(r2, code, e1, endl);
      NfaRepIncrRE(r1, code, start, e1);
      NfaRepIncrRE(r2, code, e1, endl);
      if pc < e1 {
        StarFragmentNoAnchorInstr(r1, code, start, e1, pc);
      } else {
        StarFragmentNoAnchorInstr(r2, code, e1, endl, pc);
      }
    case Re_quant(nul, qid, q, r1) =>
      var e1: nat :| GetPcRE(code, start) == Some(if q.greedy then RB.Fork(start + 1, e1 + 2) else RB.Fork(e1 + 2, start + 1))
        && GetPcRE(code, start + 1) == Some(RB.SetQuantToClock(qid, false))
        && GetPcRE(code, start + 2) == Some(RB.BeginLoop)
        && NfaRepRE(r1, code, start + 3, e1)
        && GetPcRE(code, e1) == Some(RB.EndLoop)
        && GetPcRE(code, e1 + 1) == Some(RB.Jmp(start))
        && endl == e1 + 2;
      NfaRepIncrRE(r1, code, start + 3, e1);
      if pc <= start + 2 {
      } else if pc < e1 {
        StarFragmentNoAnchorInstr(r1, code, start + 3, e1, pc);
      } else {
      }
    case Re_capture(cid, r1) =>
      var e1: nat :| GetPcRE(code, start) == Some(RB.SetRegisterToCP(CP.start_reg(cid)))
        && NfaRepRE(r1, code, start + 1, e1)
        && GetPcRE(code, e1) == Some(RB.SetRegisterToCP(CP.end_reg(cid)))
        && endl == e1 + 1;
      NfaRepIncrRE(r1, code, start + 1, e1);
      if pc == start {
      } else if pc < e1 {
        StarFragmentNoAnchorInstr(r1, code, start + 1, e1, pc);
      } else {
      }
    case Re_lookaround(_, _, _) =>
    case Re_anchor(_) =>
      // not in the STAR fragment: vacuous
  }

  // The oracle-build classification: look-free plus-fragment code contains
  // none of the four instructions the sweep lemmas (OracleSweep.dfy) must
  // exclude — CheckOracle/NegCheckOracle (would make the run oracle-
  // dependent), WriteOracle (only the appended recorder writes), and
  // CheckNullable (would make the run cdn-dependent).
  /** `NoOracleInstrRE` for the `repeat_min` forced-copy chain. */
  lemma NoOracleInstrMinRE(k: nat, qid: R.quantid, r1: R.regex, code: RB.code, start: nat, endl: nat, pc: nat)
    requires PlusFragmentRE(r1) && LookFreeRE(r1)
    requires NfaRepMinRE(k, qid, r1, code, start, endl)
    requires start <= pc < endl
    ensures GetPcRE(code, pc).Some? ==>
      var i := GetPcRE(code, pc).value;
      !i.CheckOracle? && !i.NegCheckOracle? && !i.WriteOracle? && !i.CheckNullable? && !i.Accept?
    decreases CP.rsize(r1), k + 2
  {
    if k == 0 { return; }
    var e1: nat :| GetPcRE(code, start) == Some(RB.SetQuantToClock(qid, false))
      && NfaRepRE(r1, code, start + 1, e1)
      && NfaRepMinRE(k - 1, qid, r1, code, e1, endl);
    NfaRepIncrRE(r1, code, start + 1, e1);
    NfaRepIncrMinRE(k - 1, qid, r1, code, e1, endl);
    if pc == start {
    } else if pc < e1 {
      NoOracleInstrRE(r1, code, start + 1, e1, pc);
    } else {
      NoOracleInstrMinRE(k - 1, qid, r1, code, e1, endl, pc);
    }
  }

  /** `NoOracleInstrRE` for the `repeat_optional` layer chain. */
  lemma NoOracleInstrOptRE(k: nat, greedy: bool, qid: R.quantid, r1: R.regex, code: RB.code, start: nat, endl: nat, pc: nat)
    requires PlusFragmentRE(r1) && LookFreeRE(r1)
    requires NfaRepOptRE(k, greedy, qid, r1, code, start, endl)
    requires start <= pc < endl
    ensures GetPcRE(code, pc).Some? ==>
      var i := GetPcRE(code, pc).value;
      !i.CheckOracle? && !i.NegCheckOracle? && !i.WriteOracle? && !i.CheckNullable? && !i.Accept?
    decreases CP.rsize(r1), k + 2
  {
    if k == 0 { return; }
    var e1: nat :| GetPcRE(code, start) == Some(if greedy then RB.Fork(start + 1, endl) else RB.Fork(endl, start + 1))
      && GetPcRE(code, start + 1) == Some(RB.SetQuantToClock(qid, false))
      && GetPcRE(code, start + 2) == Some(RB.BeginLoop)
      && NfaRepRE(r1, code, start + 3, e1)
      && GetPcRE(code, e1) == Some(RB.EndLoop)
      && NfaRepOptRE(k - 1, greedy, qid, r1, code, e1 + 1, endl);
    NfaRepIncrRE(r1, code, start + 3, e1);
    NfaRepIncrOptRE(k - 1, greedy, qid, r1, code, e1 + 1, endl);
    if pc <= start + 2 {
    } else if pc < e1 {
      NoOracleInstrRE(r1, code, start + 3, e1, pc);
    } else if pc == e1 {
    } else {
      NoOracleInstrOptRE(k - 1, greedy, qid, r1, code, e1 + 1, endl, pc);
    }
  }

  /** Look-free plus-fragment code contains no oracle or cdn instructions:
      every position strictly inside such an `NfaRepRE` block holds something
      other than `CheckOracle`/`NegCheckOracle`/`WriteOracle`/`CheckNullable`
      — the classification the oracle-build sweep lemmas consume. */
  lemma NoOracleInstrRE(re: R.regex, code: RB.code, start: nat, endl: nat, pc: nat)
    requires PlusFragmentRE(re) && LookFreeRE(re)
    requires NfaRepRE(re, code, start, endl)
    requires start <= pc < endl
    ensures GetPcRE(code, pc).Some? ==>
      var i := GetPcRE(code, pc).value;
      !i.CheckOracle? && !i.NegCheckOracle? && !i.WriteOracle? && !i.CheckNullable? && !i.Accept?
    decreases CP.rsize(re), 1
  {
    match re
    case Re_empty =>
    case Re_character(_) =>
    case Re_anchor(_) =>
    case Re_alt(r1, r2) =>
      var e1: nat :| GetPcRE(code, start) == Some(RB.Fork(start + 1, e1 + 1))
        && NfaRepRE(r1, code, start + 1, e1)
        && GetPcRE(code, e1) == Some(RB.Jmp(endl))
        && NfaRepRE(r2, code, e1 + 1, endl);
      NfaRepIncrRE(r1, code, start + 1, e1);
      NfaRepIncrRE(r2, code, e1 + 1, endl);
      if pc == start {
      } else if pc < e1 {
        NoOracleInstrRE(r1, code, start + 1, e1, pc);
      } else if pc == e1 {
      } else {
        NoOracleInstrRE(r2, code, e1 + 1, endl, pc);
      }
    case Re_con(r1, r2) =>
      var e1: nat :| NfaRepRE(r1, code, start, e1) && NfaRepRE(r2, code, e1, endl);
      NfaRepIncrRE(r1, code, start, e1);
      NfaRepIncrRE(r2, code, e1, endl);
      if pc < e1 {
        NoOracleInstrRE(r1, code, start, e1, pc);
      } else {
        NoOracleInstrRE(r2, code, e1, endl, pc);
      }
    case Re_quant(nul, qid, q, r1) =>
      if q.min == 0 && q.max == None {
        var e1: nat :| GetPcRE(code, start) == Some(if q.greedy then RB.Fork(start + 1, e1 + 2) else RB.Fork(e1 + 2, start + 1))
          && GetPcRE(code, start + 1) == Some(RB.SetQuantToClock(qid, false))
          && GetPcRE(code, start + 2) == Some(RB.BeginLoop)
          && NfaRepRE(r1, code, start + 3, e1)
          && GetPcRE(code, e1) == Some(RB.EndLoop)
          && GetPcRE(code, e1 + 1) == Some(RB.Jmp(start))
          && endl == e1 + 2;
        NfaRepIncrRE(r1, code, start + 3, e1);
        if pc <= start + 2 {
        } else if pc < e1 {
          NoOracleInstrRE(r1, code, start + 3, e1, pc);
        } else {
        }
      } else if q.max.Some? {
        var em := NfaRepREQuantInv(nul, qid, q, r1, code, start, endl);
        NfaRepIncrMinRE(q.min as nat, qid, r1, code, start, em);
        NfaRepIncrOptRE((q.max.value - q.min) as nat, q.greedy, qid, r1, code, em, endl);
        if pc < em {
          NoOracleInstrMinRE(q.min as nat, qid, r1, code, start, em, pc);
        } else {
          NoOracleInstrOptRE((q.max.value - q.min) as nat, q.greedy, qid, r1, code, em, endl, pc);
        }
      } else {
        var em, e1 := NfaRepREPlusInv(nul, qid, q, r1, code, start, endl);
        NfaRepIncrMinRE((q.min - 1) as nat, qid, r1, code, start, em);
        NfaRepIncrRE(r1, code, em + 1, e1);
        if pc < em {
          NoOracleInstrMinRE((q.min - 1) as nat, qid, r1, code, start, em, pc);
        } else if pc == em {
        } else if pc < e1 {
          NoOracleInstrRE(r1, code, em + 1, e1, pc);
        } else {
        }
      }
    case Re_capture(cid, r1) =>
      var e1: nat :| GetPcRE(code, start) == Some(RB.SetRegisterToCP(CP.start_reg(cid)))
        && NfaRepRE(r1, code, start + 1, e1)
        && GetPcRE(code, e1) == Some(RB.SetRegisterToCP(CP.end_reg(cid)))
        && endl == e1 + 1;
      NfaRepIncrRE(r1, code, start + 1, e1);
      if pc == start {
      } else if pc < e1 {
        NoOracleInstrRE(r1, code, start + 1, e1, pc);
      } else {
      }
    case Re_lookaround(_, _, _) =>
      // excluded by LookFreeRE: vacuous
  }

  // ===========================================================================
  // L4: the GATE-FLOOR generalization of the NoOracle classification. Where
  // `NoOracleInstrRE` FORBIDS oracle gates over a LOOK-FREE plus-fragment body,
  // this family ADMITS them over a NESTED fragment and BOUNDS them: if every
  // lookaround id in the shell sits strictly above a floor `k`, then every gate
  // the code emits reads a column strictly above `k`. The look-free case
  // (`NestDepth 0`, no gates) degenerates to `NoOracleReads`; each nested
  // lookaround leaf contributes exactly one gate, at its own above-floor id.
  // `LookUnique` supplies `lid >= 0` at each lookaround leaf so its id lands in
  // `LookIds` and the floor hypothesis then bounds it.
  // ===========================================================================

  /** `GatesAboveInstrRE` for the `repeat_min` forced-copy chain. */
  lemma GatesAboveInstrMinRE(cnt: nat, qid: R.quantid, r1: R.regex, code: RB.code, start: nat, endl: nat, k: nat, pc: nat)
    requires NestedFragmentRE(r1)
    requires LTB.LookUnique(r1)
    requires forall x: nat :: x in LTB.LookIds(r1) ==> x > k
    requires NfaRepMinRE(cnt, qid, r1, code, start, endl)
    requires start <= pc < endl
    ensures GetPcRE(code, pc).Some? ==>
      var i := GetPcRE(code, pc).value;
      (i.CheckOracle? ==> i.col > k) && (i.NegCheckOracle? ==> i.ncl > k)
    decreases CP.rsize(r1), cnt + 2
  {
    if cnt == 0 { return; }
    var e1: nat :| GetPcRE(code, start) == Some(RB.SetQuantToClock(qid, false))
      && NfaRepRE(r1, code, start + 1, e1)
      && NfaRepMinRE(cnt - 1, qid, r1, code, e1, endl);
    NfaRepIncrRE(r1, code, start + 1, e1);
    NfaRepIncrMinRE(cnt - 1, qid, r1, code, e1, endl);
    if pc == start {
    } else if pc < e1 {
      GatesAboveInstrRE(r1, code, start + 1, e1, k, pc);
    } else {
      GatesAboveInstrMinRE(cnt - 1, qid, r1, code, e1, endl, k, pc);
    }
  }

  /** `GatesAboveInstrRE` for the `repeat_optional` layer chain. */
  lemma GatesAboveInstrOptRE(cnt: nat, greedy: bool, qid: R.quantid, r1: R.regex, code: RB.code, start: nat, endl: nat, k: nat, pc: nat)
    requires NestedFragmentRE(r1)
    requires LTB.LookUnique(r1)
    requires forall x: nat :: x in LTB.LookIds(r1) ==> x > k
    requires NfaRepOptRE(cnt, greedy, qid, r1, code, start, endl)
    requires start <= pc < endl
    ensures GetPcRE(code, pc).Some? ==>
      var i := GetPcRE(code, pc).value;
      (i.CheckOracle? ==> i.col > k) && (i.NegCheckOracle? ==> i.ncl > k)
    decreases CP.rsize(r1), cnt + 2
  {
    if cnt == 0 { return; }
    var e1: nat :| GetPcRE(code, start) == Some(if greedy then RB.Fork(start + 1, endl) else RB.Fork(endl, start + 1))
      && GetPcRE(code, start + 1) == Some(RB.SetQuantToClock(qid, false))
      && GetPcRE(code, start + 2) == Some(RB.BeginLoop)
      && NfaRepRE(r1, code, start + 3, e1)
      && GetPcRE(code, e1) == Some(RB.EndLoop)
      && NfaRepOptRE(cnt - 1, greedy, qid, r1, code, e1 + 1, endl);
    NfaRepIncrRE(r1, code, start + 3, e1);
    NfaRepIncrOptRE(cnt - 1, greedy, qid, r1, code, e1 + 1, endl);
    if pc <= start + 2 {
    } else if pc < e1 {
      GatesAboveInstrRE(r1, code, start + 3, e1, k, pc);
    } else if pc == e1 {
    } else {
      GatesAboveInstrOptRE(cnt - 1, greedy, qid, r1, code, e1 + 1, endl, k, pc);
    }
  }

  /** Nested-fragment code whose lookaround ids all sit strictly above `k` emits
      only gates that READ strictly above `k`: at every position inside the
      `NfaRepRE` block a `CheckOracle`/`NegCheckOracle` (if any) reads a column
      `> k`. The additive L4 generalization of `NoOracleInstrRE` — which FORBADE
      gates over a look-free body; here the gates are ADMITTED and BOUNDED. */
  lemma GatesAboveInstrRE(re: R.regex, code: RB.code, start: nat, endl: nat, k: nat, pc: nat)
    requires NestedFragmentRE(re)
    requires LTB.LookUnique(re)
    requires forall x: nat :: x in LTB.LookIds(re) ==> x > k
    requires NfaRepRE(re, code, start, endl)
    requires start <= pc < endl
    ensures GetPcRE(code, pc).Some? ==>
      var i := GetPcRE(code, pc).value;
      (i.CheckOracle? ==> i.col > k) && (i.NegCheckOracle? ==> i.ncl > k)
    decreases CP.rsize(re), 1
  {
    match re
    case Re_empty =>
    case Re_character(_) =>
    case Re_anchor(_) =>
    case Re_alt(r1, r2) =>
      var e1: nat :| GetPcRE(code, start) == Some(RB.Fork(start + 1, e1 + 1))
        && NfaRepRE(r1, code, start + 1, e1)
        && GetPcRE(code, e1) == Some(RB.Jmp(endl))
        && NfaRepRE(r2, code, e1 + 1, endl);
      NfaRepIncrRE(r1, code, start + 1, e1);
      NfaRepIncrRE(r2, code, e1 + 1, endl);
      assert LTB.LookIds(re) == LTB.LookIds(r1) + LTB.LookIds(r2);
      assert forall x: nat :: x in LTB.LookIds(r1) ==> x in LTB.LookIds(re);
      assert forall x: nat :: x in LTB.LookIds(r2) ==> x in LTB.LookIds(re);
      if pc == start {
      } else if pc < e1 {
        GatesAboveInstrRE(r1, code, start + 1, e1, k, pc);
      } else if pc == e1 {
      } else {
        GatesAboveInstrRE(r2, code, e1 + 1, endl, k, pc);
      }
    case Re_con(r1, r2) =>
      var e1: nat :| NfaRepRE(r1, code, start, e1) && NfaRepRE(r2, code, e1, endl);
      NfaRepIncrRE(r1, code, start, e1);
      NfaRepIncrRE(r2, code, e1, endl);
      assert LTB.LookIds(re) == LTB.LookIds(r1) + LTB.LookIds(r2);
      assert forall x: nat :: x in LTB.LookIds(r1) ==> x in LTB.LookIds(re);
      assert forall x: nat :: x in LTB.LookIds(r2) ==> x in LTB.LookIds(re);
      if pc < e1 {
        GatesAboveInstrRE(r1, code, start, e1, k, pc);
      } else {
        GatesAboveInstrRE(r2, code, e1, endl, k, pc);
      }
    case Re_quant(nul, qid, q, r1) =>
      assert LTB.LookIds(re) == LTB.LookIds(r1);
      if q.min == 0 && q.max == None {
        var e1: nat :| GetPcRE(code, start) == Some(if q.greedy then RB.Fork(start + 1, e1 + 2) else RB.Fork(e1 + 2, start + 1))
          && GetPcRE(code, start + 1) == Some(RB.SetQuantToClock(qid, false))
          && GetPcRE(code, start + 2) == Some(RB.BeginLoop)
          && NfaRepRE(r1, code, start + 3, e1)
          && GetPcRE(code, e1) == Some(RB.EndLoop)
          && GetPcRE(code, e1 + 1) == Some(RB.Jmp(start))
          && endl == e1 + 2;
        NfaRepIncrRE(r1, code, start + 3, e1);
        if pc <= start + 2 {
        } else if pc < e1 {
          GatesAboveInstrRE(r1, code, start + 3, e1, k, pc);
        } else {
        }
      } else if q.max.Some? {
        var em := NfaRepREQuantInv(nul, qid, q, r1, code, start, endl);
        NfaRepIncrMinRE(q.min as nat, qid, r1, code, start, em);
        NfaRepIncrOptRE((q.max.value - q.min) as nat, q.greedy, qid, r1, code, em, endl);
        if pc < em {
          GatesAboveInstrMinRE(q.min as nat, qid, r1, code, start, em, k, pc);
        } else {
          GatesAboveInstrOptRE((q.max.value - q.min) as nat, q.greedy, qid, r1, code, em, endl, k, pc);
        }
      } else {
        var em, e1 := NfaRepREPlusInv(nul, qid, q, r1, code, start, endl);
        NfaRepIncrMinRE((q.min - 1) as nat, qid, r1, code, start, em);
        NfaRepIncrRE(r1, code, em + 1, e1);
        if pc < em {
          GatesAboveInstrMinRE((q.min - 1) as nat, qid, r1, code, start, em, k, pc);
        } else if pc == em {
        } else if pc < e1 {
          GatesAboveInstrRE(r1, code, em + 1, e1, k, pc);
        } else {
        }
      }
    case Re_capture(cid, r1) =>
      var e1: nat :| GetPcRE(code, start) == Some(RB.SetRegisterToCP(CP.start_reg(cid)))
        && NfaRepRE(r1, code, start + 1, e1)
        && GetPcRE(code, e1) == Some(RB.SetRegisterToCP(CP.end_reg(cid)))
        && endl == e1 + 1;
      NfaRepIncrRE(r1, code, start + 1, e1);
      assert LTB.LookIds(re) == LTB.LookIds(r1);
      if pc == start {
      } else if pc < e1 {
        GatesAboveInstrRE(r1, code, start + 1, e1, k, pc);
      } else {
      }
    case Re_lookaround(lid, la, r1) =>
      // The whole block is the single gate at `start`: NfaRepRE pins
      // `endl == start + 1`, so `start <= pc < endl` forces `pc == start`, and
      // the instruction there is `CheckOracle(lid)`/`NegCheckOracle(lid)`.
      assert pc == start;
      assert GetPcRE(code, start)
        == Some(if la.Lookahead? || la.Lookbehind? then RB.CheckOracle(lid) else RB.NegCheckOracle(lid));
      // `LookUnique(re)` gives `lid >= 0`, so `lid` lands in `LookIds(re)` and
      // the floor hypothesis bounds it: `lid > k`.
      assert lid >= 0;
      assert (lid as nat) in LTB.LookIds(re);
      assert lid > k;
  }

  /** Bridge to the sweep-side floor predicate `OS.AllGatesAbove`: a STANDALONE
      nested-fragment build whose whole program IS the block `[0, |code|)` and
      whose lookaround ids all sit strictly above `k` has ALL its gates above
      `k`. The L4 mirror of the `NoOracleReads` bridge (OracleBuild) — where a
      look-free body classified to `NoOracleReads`, a nested body classifies to
      the gated form. */
  lemma GatesAboveClassified(re: R.regex, code: RB.code, k: nat)
    requires NestedFragmentRE(re)
    requires LTB.LookUnique(re)
    requires forall x: nat :: x in LTB.LookIds(re) ==> x > k
    requires NfaRepRE(re, code, 0, |code|)
    ensures OS.AllGatesAbove(code, k)
  {
    forall pc | 0 <= pc < |code|
      ensures (code[pc].CheckOracle? ==> code[pc].col > k)
              && (code[pc].NegCheckOracle? ==> code[pc].ncl > k)
    {
      GatesAboveInstrRE(re, code, 0, |code|, k, pc);
      assert GetPcRE(code, pc) == Some(code[pc]);
    }
  }

  /** `NoWriteInstrRE` for the `repeat_min` forced-copy chain. */
  lemma NoWriteInstrMinRE(k: nat, qid: R.quantid, r1: R.regex, code: RB.code, start: nat, endl: nat, pc: nat)
    requires LookBehindFragmentRE(r1)
    requires NfaRepMinRE(k, qid, r1, code, start, endl)
    requires start <= pc < endl
    ensures GetPcRE(code, pc).Some? ==>
      var i := GetPcRE(code, pc).value;
      !i.WriteOracle? && !i.CheckNullable? && !i.Accept?
    decreases CP.rsize(r1), k + 2
  {
    if k == 0 { return; }
    var e1: nat :| GetPcRE(code, start) == Some(RB.SetQuantToClock(qid, false))
      && NfaRepRE(r1, code, start + 1, e1)
      && NfaRepMinRE(k - 1, qid, r1, code, e1, endl);
    NfaRepIncrRE(r1, code, start + 1, e1);
    NfaRepIncrMinRE(k - 1, qid, r1, code, e1, endl);
    if pc == start {
    } else if pc < e1 {
      NoWriteInstrRE(r1, code, start + 1, e1, pc);
    } else {
      NoWriteInstrMinRE(k - 1, qid, r1, code, e1, endl, pc);
    }
  }

  /** `NoWriteInstrRE` for the `repeat_optional` layer chain. */
  lemma NoWriteInstrOptRE(k: nat, greedy: bool, qid: R.quantid, r1: R.regex, code: RB.code, start: nat, endl: nat, pc: nat)
    requires LookBehindFragmentRE(r1)
    requires NfaRepOptRE(k, greedy, qid, r1, code, start, endl)
    requires start <= pc < endl
    ensures GetPcRE(code, pc).Some? ==>
      var i := GetPcRE(code, pc).value;
      !i.WriteOracle? && !i.CheckNullable? && !i.Accept?
    decreases CP.rsize(r1), k + 2
  {
    if k == 0 { return; }
    var e1: nat :| GetPcRE(code, start) == Some(if greedy then RB.Fork(start + 1, endl) else RB.Fork(endl, start + 1))
      && GetPcRE(code, start + 1) == Some(RB.SetQuantToClock(qid, false))
      && GetPcRE(code, start + 2) == Some(RB.BeginLoop)
      && NfaRepRE(r1, code, start + 3, e1)
      && GetPcRE(code, e1) == Some(RB.EndLoop)
      && NfaRepOptRE(k - 1, greedy, qid, r1, code, e1 + 1, endl);
    NfaRepIncrRE(r1, code, start + 3, e1);
    NfaRepIncrOptRE(k - 1, greedy, qid, r1, code, e1 + 1, endl);
    if pc <= start + 2 {
    } else if pc < e1 {
      NoWriteInstrRE(r1, code, start + 3, e1, pc);
    } else if pc == e1 {
    } else {
      NoWriteInstrOptRE(k - 1, greedy, qid, r1, code, e1 + 1, endl, pc);
    }
  }

  /** Lookbehind-fragment main-pass code writes no oracle and reads no cdn:
      every position strictly inside such an `NfaRepRE` block holds something
      other than `WriteOracle`/`CheckNullable` (the lookaround GATES are of
      course allowed). This is what makes the oracle view static across the
      main pass. */
  lemma NoWriteInstrRE(re: R.regex, code: RB.code, start: nat, endl: nat, pc: nat)
    requires LookBehindFragmentRE(re)
    requires NfaRepRE(re, code, start, endl)
    requires start <= pc < endl
    ensures GetPcRE(code, pc).Some? ==>
      var i := GetPcRE(code, pc).value;
      !i.WriteOracle? && !i.CheckNullable? && !i.Accept?
    decreases CP.rsize(re), 1
  {
    match re
    case Re_empty =>
    case Re_character(_) =>
    case Re_anchor(_) =>
    case Re_alt(r1, r2) =>
      var e1: nat :| GetPcRE(code, start) == Some(RB.Fork(start + 1, e1 + 1))
        && NfaRepRE(r1, code, start + 1, e1)
        && GetPcRE(code, e1) == Some(RB.Jmp(endl))
        && NfaRepRE(r2, code, e1 + 1, endl);
      NfaRepIncrRE(r1, code, start + 1, e1);
      NfaRepIncrRE(r2, code, e1 + 1, endl);
      if pc == start {
      } else if pc < e1 {
        NoWriteInstrRE(r1, code, start + 1, e1, pc);
      } else if pc == e1 {
      } else {
        NoWriteInstrRE(r2, code, e1 + 1, endl, pc);
      }
    case Re_con(r1, r2) =>
      var e1: nat :| NfaRepRE(r1, code, start, e1) && NfaRepRE(r2, code, e1, endl);
      NfaRepIncrRE(r1, code, start, e1);
      NfaRepIncrRE(r2, code, e1, endl);
      if pc < e1 {
        NoWriteInstrRE(r1, code, start, e1, pc);
      } else {
        NoWriteInstrRE(r2, code, e1, endl, pc);
      }
    case Re_quant(nul, qid, q, r1) =>
      if q.min == 0 && q.max == None {
        var e1: nat :| GetPcRE(code, start) == Some(if q.greedy then RB.Fork(start + 1, e1 + 2) else RB.Fork(e1 + 2, start + 1))
          && GetPcRE(code, start + 1) == Some(RB.SetQuantToClock(qid, false))
          && GetPcRE(code, start + 2) == Some(RB.BeginLoop)
          && NfaRepRE(r1, code, start + 3, e1)
          && GetPcRE(code, e1) == Some(RB.EndLoop)
          && GetPcRE(code, e1 + 1) == Some(RB.Jmp(start))
          && endl == e1 + 2;
        NfaRepIncrRE(r1, code, start + 3, e1);
        if pc <= start + 2 {
        } else if pc < e1 {
          NoWriteInstrRE(r1, code, start + 3, e1, pc);
        } else {
        }
      } else if q.max.Some? {
        var em := NfaRepREQuantInv(nul, qid, q, r1, code, start, endl);
        NfaRepIncrMinRE(q.min as nat, qid, r1, code, start, em);
        NfaRepIncrOptRE((q.max.value - q.min) as nat, q.greedy, qid, r1, code, em, endl);
        if pc < em {
          NoWriteInstrMinRE(q.min as nat, qid, r1, code, start, em, pc);
        } else {
          NoWriteInstrOptRE((q.max.value - q.min) as nat, q.greedy, qid, r1, code, em, endl, pc);
        }
      } else {
        var em, e1 := NfaRepREPlusInv(nul, qid, q, r1, code, start, endl);
        NfaRepIncrMinRE((q.min - 1) as nat, qid, r1, code, start, em);
        NfaRepIncrRE(r1, code, em + 1, e1);
        if pc < em {
          NoWriteInstrMinRE((q.min - 1) as nat, qid, r1, code, start, em, pc);
        } else if pc == em {
        } else if pc < e1 {
          NoWriteInstrRE(r1, code, em + 1, e1, pc);
        } else {
        }
      }
    case Re_capture(cid, r1) =>
      var e1: nat :| GetPcRE(code, start) == Some(RB.SetRegisterToCP(CP.start_reg(cid)))
        && NfaRepRE(r1, code, start + 1, e1)
        && GetPcRE(code, e1) == Some(RB.SetRegisterToCP(CP.end_reg(cid)))
        && endl == e1 + 1;
      NfaRepIncrRE(r1, code, start + 1, e1);
      if pc == start {
      } else if pc < e1 {
        NoWriteInstrRE(r1, code, start + 1, e1, pc);
      } else {
      }
    case Re_lookaround(lid, la, r1) =>
      // the whole block is the single gate instruction at `start`
      assert pc == start;
  }


  // The CAPTURE classification: a capture-free block emits no
  // SetRegisterToCP, so running it cannot disturb any thread's capture bank.
  // What it buys: the lookaround capture pass (FLookLoop's replay) leaves the
  // final answer alone when the lookaround's body is capture-free — the L1
  // shape of "the look pass is the identity".
  /** `NoCaptureInstrRE` for the `repeat_min` forced-copy chain. */
  lemma NoCaptureInstrMinRE(k: nat, qid: R.quantid, r1: R.regex, code: RB.code, start: nat, endl: nat, pc: nat)
    requires LookBehindFragmentRE(r1) && CaptureFreeRE(r1)
    requires NfaRepMinRE(k, qid, r1, code, start, endl)
    requires start <= pc < endl
    ensures GetPcRE(code, pc).Some? ==>
      var i := GetPcRE(code, pc).value;
      !i.SetRegisterToCP?
    decreases CP.rsize(r1), k + 2
  {
    if k == 0 { return; }
    var e1: nat :| GetPcRE(code, start) == Some(RB.SetQuantToClock(qid, false))
      && NfaRepRE(r1, code, start + 1, e1)
      && NfaRepMinRE(k - 1, qid, r1, code, e1, endl);
    NfaRepIncrRE(r1, code, start + 1, e1);
    NfaRepIncrMinRE(k - 1, qid, r1, code, e1, endl);
    if pc == start {
    } else if pc < e1 {
      NoCaptureInstrRE(r1, code, start + 1, e1, pc);
    } else {
      NoCaptureInstrMinRE(k - 1, qid, r1, code, e1, endl, pc);
    }
  }

  /** `NoCaptureInstrRE` for the `repeat_optional` layer chain. */
  lemma NoCaptureInstrOptRE(k: nat, greedy: bool, qid: R.quantid, r1: R.regex, code: RB.code, start: nat, endl: nat, pc: nat)
    requires LookBehindFragmentRE(r1) && CaptureFreeRE(r1)
    requires NfaRepOptRE(k, greedy, qid, r1, code, start, endl)
    requires start <= pc < endl
    ensures GetPcRE(code, pc).Some? ==>
      var i := GetPcRE(code, pc).value;
      !i.SetRegisterToCP?
    decreases CP.rsize(r1), k + 2
  {
    if k == 0 { return; }
    var e1: nat :| GetPcRE(code, start) == Some(if greedy then RB.Fork(start + 1, endl) else RB.Fork(endl, start + 1))
      && GetPcRE(code, start + 1) == Some(RB.SetQuantToClock(qid, false))
      && GetPcRE(code, start + 2) == Some(RB.BeginLoop)
      && NfaRepRE(r1, code, start + 3, e1)
      && GetPcRE(code, e1) == Some(RB.EndLoop)
      && NfaRepOptRE(k - 1, greedy, qid, r1, code, e1 + 1, endl);
    NfaRepIncrRE(r1, code, start + 3, e1);
    NfaRepIncrOptRE(k - 1, greedy, qid, r1, code, e1 + 1, endl);
    if pc <= start + 2 {
    } else if pc < e1 {
      NoCaptureInstrRE(r1, code, start + 3, e1, pc);
    } else if pc == e1 {
    } else {
      NoCaptureInstrOptRE(k - 1, greedy, qid, r1, code, e1 + 1, endl, pc);
    }
  }

  /** Capture-free code writes no capture register: every position strictly
      inside such an `NfaRepRE` block holds something other than
      `SetRegisterToCP`. */
  lemma NoCaptureInstrRE(re: R.regex, code: RB.code, start: nat, endl: nat, pc: nat)
    requires LookBehindFragmentRE(re) && CaptureFreeRE(re)
    requires NfaRepRE(re, code, start, endl)
    requires start <= pc < endl
    ensures GetPcRE(code, pc).Some? ==>
      var i := GetPcRE(code, pc).value;
      !i.SetRegisterToCP?
    decreases CP.rsize(re), 1
  {
    match re
    case Re_empty =>
    case Re_character(_) =>
    case Re_anchor(_) =>
    case Re_alt(r1, r2) =>
      var e1: nat :| GetPcRE(code, start) == Some(RB.Fork(start + 1, e1 + 1))
        && NfaRepRE(r1, code, start + 1, e1)
        && GetPcRE(code, e1) == Some(RB.Jmp(endl))
        && NfaRepRE(r2, code, e1 + 1, endl);
      NfaRepIncrRE(r1, code, start + 1, e1);
      NfaRepIncrRE(r2, code, e1 + 1, endl);
      if pc == start {
      } else if pc < e1 {
        NoCaptureInstrRE(r1, code, start + 1, e1, pc);
      } else if pc == e1 {
      } else {
        NoCaptureInstrRE(r2, code, e1 + 1, endl, pc);
      }
    case Re_con(r1, r2) =>
      var e1: nat :| NfaRepRE(r1, code, start, e1) && NfaRepRE(r2, code, e1, endl);
      NfaRepIncrRE(r1, code, start, e1);
      NfaRepIncrRE(r2, code, e1, endl);
      if pc < e1 {
        NoCaptureInstrRE(r1, code, start, e1, pc);
      } else {
        NoCaptureInstrRE(r2, code, e1, endl, pc);
      }
    case Re_quant(nul, qid, q, r1) =>
      if q.min == 0 && q.max == None {
        var e1: nat :| GetPcRE(code, start) == Some(if q.greedy then RB.Fork(start + 1, e1 + 2) else RB.Fork(e1 + 2, start + 1))
          && GetPcRE(code, start + 1) == Some(RB.SetQuantToClock(qid, false))
          && GetPcRE(code, start + 2) == Some(RB.BeginLoop)
          && NfaRepRE(r1, code, start + 3, e1)
          && GetPcRE(code, e1) == Some(RB.EndLoop)
          && GetPcRE(code, e1 + 1) == Some(RB.Jmp(start))
          && endl == e1 + 2;
        NfaRepIncrRE(r1, code, start + 3, e1);
        if pc <= start + 2 {
        } else if pc < e1 {
          NoCaptureInstrRE(r1, code, start + 3, e1, pc);
        } else {
        }
      } else if q.max.Some? {
        var em := NfaRepREQuantInv(nul, qid, q, r1, code, start, endl);
        NfaRepIncrMinRE(q.min as nat, qid, r1, code, start, em);
        NfaRepIncrOptRE((q.max.value - q.min) as nat, q.greedy, qid, r1, code, em, endl);
        if pc < em {
          NoCaptureInstrMinRE(q.min as nat, qid, r1, code, start, em, pc);
        } else {
          NoCaptureInstrOptRE((q.max.value - q.min) as nat, q.greedy, qid, r1, code, em, endl, pc);
        }
      } else {
        var em, e1 := NfaRepREPlusInv(nul, qid, q, r1, code, start, endl);
        NfaRepIncrMinRE((q.min - 1) as nat, qid, r1, code, start, em);
        NfaRepIncrRE(r1, code, em + 1, e1);
        if pc < em {
          NoCaptureInstrMinRE((q.min - 1) as nat, qid, r1, code, start, em, pc);
        } else if pc == em {
        } else if pc < e1 {
          NoCaptureInstrRE(r1, code, em + 1, e1, pc);
        } else {
        }
      }
    case Re_capture(cid, r1) =>
      // excluded by CaptureFreeRE
    case Re_lookaround(lid, la, r1) =>
      // the whole block is the single gate instruction at `start`
      assert pc == start;
  }



  /** The full oracle-build program of a look-free plus-fragment build regex,
      classified for the sweep lemmas: no oracle reads, no `CheckNullable`,
      and the only `WriteOracle` is the final recorder for `lid`. */
  lemma CompileToWriteClassified(re: R.regex, lid: R.lookid)
    requires PlusFragmentRE(re) && LookFreeRE(re)
    ensures var code := CP.compile_to_write(re, lid);
      forall pc :: 0 <= pc < |code| ==>
        !code[pc].CheckOracle? && !code[pc].NegCheckOracle? && !code[pc].CheckNullable? && !code[pc].Accept?
        && (code[pc].WriteOracle? ==> code[pc].wol == lid)
  {
    PlusIsLookBehindFragmentRE(re);
    CompileToWriteRep(re, lid);
    var code := CP.compile_to_write(re, lid);
    var next := CP.compile(re, 0, CP.Progress).1;
    forall pc | 0 <= pc < |code|
      ensures !code[pc].CheckOracle? && !code[pc].NegCheckOracle? && !code[pc].CheckNullable? && !code[pc].Accept?
              && (code[pc].WriteOracle? ==> code[pc].wol == lid)
    {
      if pc < next as nat {
        NoOracleInstrRE(re, code, 0, next as nat, pc);
        assert GetPcRE(code, pc) == Some(code[pc]);
      } else {
        assert pc == next as nat;
        assert GetPcRE(code, pc) == Some(RB.WriteOracle(lid));
      }
    }
  }

  /** Star-fragment build code carries no anchor instruction. The point is
      that the anchor SWAP is then the identity on it, so a BACKWARD build of
      such a body can be read as a forward run of the very same program over
      the reversed string -- no compile/swap commutation needed. */
  lemma CompileToWriteNoAnchor(re: R.regex, lid: R.lookid)
    requires StarFragmentRE(re)
    ensures var code := CP.compile_to_write(re, lid);
      forall pc :: 0 <= pc < |code| ==> !code[pc].AnchorAssertion?
  {
    StarIsAnchorFragmentRE(re);
    AnchorIsQuantFragmentRE(re);
    QuantIsPlusFragmentRE(re);
    PlusIsLookBehindFragmentRE(re);
    CompileToWriteRep(re, lid);
    var code := CP.compile_to_write(re, lid);
    var next := CP.compile(re, 0, CP.Progress).1;
    forall pc | 0 <= pc < |code| ensures !code[pc].AnchorAssertion? {
      if pc < next as nat {
        StarFragmentNoAnchorInstr(re, code, 0, next as nat, pc);
        assert GetPcRE(code, pc) == Some(code[pc]);
      } else {
        assert pc == next as nat;
        assert GetPcRE(code, pc) == Some(RB.WriteOracle(lid));
      }
    }
  }

  /** Labels only increase: `NfaRepRE(re, code, start, endl)` implies `start <= endl` —
      the RegElk port of Linden's `nfa_rep_incr`, used in termination/measure arguments
      elsewhere. */
  /** `NfaRepIncrRE` for `NfaRepMinRE`. */
  lemma NfaRepIncrMinRE(k: nat, qid: R.quantid, r1: R.regex, code: RB.code, start: nat, endl: nat)
    requires NfaRepMinRE(k, qid, r1, code, start, endl)
    ensures start <= endl
    decreases CP.rsize(r1), k + 2
  {
    if k > 0 {
      var e1: nat :| GetPcRE(code, start) == Some(RB.SetQuantToClock(qid, false))
        && NfaRepRE(r1, code, start + 1, e1)
        && NfaRepMinRE(k - 1, qid, r1, code, e1, endl);
      NfaRepIncrRE(r1, code, start + 1, e1);
      NfaRepIncrMinRE(k - 1, qid, r1, code, e1, endl);
    }
  }

  /** `NfaRepIncrRE` for `NfaRepOptRE`. */
  lemma NfaRepIncrOptRE(k: nat, greedy: bool, qid: R.quantid, r1: R.regex, code: RB.code, start: nat, endl: nat)
    requires NfaRepOptRE(k, greedy, qid, r1, code, start, endl)
    ensures start <= endl
    decreases CP.rsize(r1), k + 2
  {
    if k > 0 {
      var e1: nat :| GetPcRE(code, start) == Some(if greedy then RB.Fork(start + 1, endl) else RB.Fork(endl, start + 1))
        && GetPcRE(code, start + 1) == Some(RB.SetQuantToClock(qid, false))
        && GetPcRE(code, start + 2) == Some(RB.BeginLoop)
        && NfaRepRE(r1, code, start + 3, e1)
        && GetPcRE(code, e1) == Some(RB.EndLoop)
        && NfaRepOptRE(k - 1, greedy, qid, r1, code, e1 + 1, endl);
      NfaRepIncrRE(r1, code, start + 3, e1);
      NfaRepIncrOptRE(k - 1, greedy, qid, r1, code, e1 + 1, endl);
    }
  }

  lemma NfaRepIncrRE(re: R.regex, code: RB.code, start: nat, endl: nat)
    requires NfaRepRE(re, code, start, endl)
    ensures start <= endl
    decreases CP.rsize(re), 1
  {
    match re
    case Re_empty =>
    case Re_character(_) =>
    case Re_alt(r1, r2) =>
      var e1: nat :| GetPcRE(code, start) == Some(RB.Fork(start + 1, e1 + 1))
        && NfaRepRE(r1, code, start + 1, e1) && GetPcRE(code, e1) == Some(RB.Jmp(endl))
        && NfaRepRE(r2, code, e1 + 1, endl);
      NfaRepIncrRE(r1, code, start + 1, e1);
      NfaRepIncrRE(r2, code, e1 + 1, endl);
    case Re_con(r1, r2) =>
      var e1: nat :| NfaRepRE(r1, code, start, e1) && NfaRepRE(r2, code, e1, endl);
      NfaRepIncrRE(r1, code, start, e1);
      NfaRepIncrRE(r2, code, e1, endl);
    case Re_quant(nul, qid, q, r1) =>
      if q.min == 0 && q.max == None {
        var e1: nat :| GetPcRE(code, start) == Some(if q.greedy then RB.Fork(start + 1, e1 + 2) else RB.Fork(e1 + 2, start + 1))
          && GetPcRE(code, start + 1) == Some(RB.SetQuantToClock(qid, false))
          && GetPcRE(code, start + 2) == Some(RB.BeginLoop)
          && NfaRepRE(r1, code, start + 3, e1)
          && GetPcRE(code, e1) == Some(RB.EndLoop)
          && GetPcRE(code, e1 + 1) == Some(RB.Jmp(start))
          && endl == e1 + 2;
        NfaRepIncrRE(r1, code, start + 3, e1);
      } else if q.max.Some? {
        var em: nat :| NfaRepMinRE(q.min as nat, qid, r1, code, start, em)
          && NfaRepOptRE((q.max.value - q.min) as nat, q.greedy, qid, r1, code, em, endl);
        NfaRepIncrMinRE(q.min as nat, qid, r1, code, start, em);
        NfaRepIncrOptRE((q.max.value - q.min) as nat, q.greedy, qid, r1, code, em, endl);
      } else {
        var mn1 := (q.min - 1) as nat;
        var em: nat :| NfaRepMinRE(mn1, qid, r1, code, start, em)
          && GetPcRE(code, em) == Some(RB.SetQuantToClock(qid, false))
          && (exists e1: nat ::
                NfaRepRE(r1, code, em + 1, e1)
                && GetPcRE(code, e1) == Some(if q.greedy then RB.Fork(em, e1 + 1) else RB.Fork(e1 + 1, em))
                && endl == e1 + 1);
        var e1: nat :| NfaRepRE(r1, code, em + 1, e1)
          && GetPcRE(code, e1) == Some(if q.greedy then RB.Fork(em, e1 + 1) else RB.Fork(e1 + 1, em))
          && endl == e1 + 1;
        NfaRepIncrMinRE(mn1, qid, r1, code, start, em);
        NfaRepIncrRE(r1, code, em + 1, e1);
      }
    case Re_capture(cid, r1) =>
      var e1: nat :| GetPcRE(code, start) == Some(RB.SetRegisterToCP(CP.start_reg(cid)))
        && NfaRepRE(r1, code, start + 1, e1)
        && GetPcRE(code, e1) == Some(RB.SetRegisterToCP(CP.end_reg(cid)))
        && endl == e1 + 1;
      NfaRepIncrRE(r1, code, start + 1, e1);
    case Re_lookaround(_, _, _) =>
    case Re_anchor(_) =>
  }

  // ===========================================================================
  // L4 depth-k establisher support: the NESTED build-code classification.
  //
  // A nested lookaround's oracle build regex `oracle_regex(la, body)` stays in
  // the NESTED fragment, keeps unique / position-preserved look ids, and — by
  // `LidsWellNested` at the enclosing lookaround — has every look id strictly
  // ABOVE the outer lid. So `compile_to_write(oracle_regex(la, body), lid)` is
  // classified for `LidBuildOkAbove`: gates all read strictly above `lid`
  // (`AllGatesAbove`), writes only column `lid`, no `CheckNullable`, no `Accept`.
  // This is the L4 analogue of `CompileToWriteClassified` (depth-1, look-free).
  // ===========================================================================

  /** `remove_capture` yields a capture-free regex (it deletes every `Group`). */
  lemma CaptureFreeRemoveCaptureRE(r: R.regex)
    ensures CaptureFreeRE(R.remove_capture(r))
    decreases r
  {
    match r
    case Re_alt(r1, r2) => CaptureFreeRemoveCaptureRE(r1); CaptureFreeRemoveCaptureRE(r2);
    case Re_con(r1, r2) => CaptureFreeRemoveCaptureRE(r1); CaptureFreeRemoveCaptureRE(r2);
    case Re_quant(_, _, _, r1) => CaptureFreeRemoveCaptureRE(r1);
    case Re_capture(_, r1) => CaptureFreeRemoveCaptureRE(r1);
    case Re_lookaround(_, _, r1) => CaptureFreeRemoveCaptureRE(r1);
    case _ =>
  }

  /** `reverse_regex` preserves capture-freedom (it keeps `Group` nodes, only
      reorders concatenation). */
  lemma CaptureFreeReverseRE(r: R.regex)
    requires CaptureFreeRE(r)
    ensures CaptureFreeRE(R.reverse_regex(r))
    decreases r
  {
    match r
    case Re_alt(r1, r2) => CaptureFreeReverseRE(r1); CaptureFreeReverseRE(r2);
    case Re_con(r1, r2) => CaptureFreeReverseRE(r2); CaptureFreeReverseRE(r1);
    case Re_quant(_, _, _, r1) => CaptureFreeReverseRE(r1);
    case Re_lookaround(_, _, r1) => CaptureFreeReverseRE(r1);
    case _ =>
  }

  /** `remove_capture` preserves the LOOK-ID SET (it keeps every lookaround with
      its id, only deletes capture groups, which carry no look id). */
  lemma LookIdsRemoveCaptureRE(r: R.regex)
    ensures LTB.LookIds(R.remove_capture(r)) == LTB.LookIds(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => LookIdsRemoveCaptureRE(r1); LookIdsRemoveCaptureRE(r2);
    case Re_con(r1, r2) => LookIdsRemoveCaptureRE(r1); LookIdsRemoveCaptureRE(r2);
    case Re_quant(_, _, _, r1) => LookIdsRemoveCaptureRE(r1);
    case Re_capture(_, r1) => LookIdsRemoveCaptureRE(r1);
    case Re_lookaround(_, _, r1) => LookIdsRemoveCaptureRE(r1);
    case _ =>
  }

  /** `reverse_regex` preserves the look-id set (only reorders concatenation). */
  lemma LookIdsReverseRE(r: R.regex)
    ensures LTB.LookIds(R.reverse_regex(r)) == LTB.LookIds(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => LookIdsReverseRE(r1); LookIdsReverseRE(r2);
    case Re_con(r1, r2) => LookIdsReverseRE(r1); LookIdsReverseRE(r2);
    case Re_quant(_, _, _, r1) => LookIdsReverseRE(r1);
    case Re_capture(_, r1) => LookIdsReverseRE(r1);
    case Re_lookaround(_, _, r1) => LookIdsReverseRE(r1);
    case _ =>
  }

  /** `lazy_prefix` adds a look-free `.*?` head, so the look-id set is unchanged. */
  lemma LookIdsLazyPrefixRE(r: R.regex)
    ensures LTB.LookIds(R.lazy_prefix(r)) == LTB.LookIds(r)
  {
    var pre := R.Re_quant(R.NonNullable, 0, R.CountedQuant(0, None, false), R.Re_character(R.Dot));
    assert R.lazy_prefix(r) == R.Re_con(pre, r);
    assert LTB.LookIds(pre) == {};
  }

  /** `remove_capture` keeps look ids unique (they are the same set, and the
      structure is preserved but for deleted groups). */
  lemma LookUniqueRemoveCaptureRE(r: R.regex)
    requires LTB.LookUnique(r)
    ensures LTB.LookUnique(R.remove_capture(r))
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      LookUniqueRemoveCaptureRE(r1); LookUniqueRemoveCaptureRE(r2);
      LookIdsRemoveCaptureRE(r1); LookIdsRemoveCaptureRE(r2);
    case Re_con(r1, r2) =>
      LookUniqueRemoveCaptureRE(r1); LookUniqueRemoveCaptureRE(r2);
      LookIdsRemoveCaptureRE(r1); LookIdsRemoveCaptureRE(r2);
    case Re_quant(_, _, _, r1) => LookUniqueRemoveCaptureRE(r1);
    case Re_capture(_, r1) => LookUniqueRemoveCaptureRE(r1);
    case Re_lookaround(lid, _, r1) => LookUniqueRemoveCaptureRE(r1); LookIdsRemoveCaptureRE(r1);
    case _ =>
  }

  /** `reverse_regex` keeps look ids unique (the same set; `*` intersection is
      commutative, covering the swapped concatenation order). */
  lemma LookUniqueReverseRE(r: R.regex)
    requires LTB.LookUnique(r)
    ensures LTB.LookUnique(R.reverse_regex(r))
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      LookUniqueReverseRE(r1); LookUniqueReverseRE(r2);
      LookIdsReverseRE(r1); LookIdsReverseRE(r2);
    case Re_con(r1, r2) =>
      LookUniqueReverseRE(r1); LookUniqueReverseRE(r2);
      LookIdsReverseRE(r1); LookIdsReverseRE(r2);
    case Re_quant(_, _, _, r1) => LookUniqueReverseRE(r1);
    case Re_capture(_, r1) => LookUniqueReverseRE(r1);
    case Re_lookaround(lid, _, r1) => LookUniqueReverseRE(r1); LookIdsReverseRE(r1);
    case _ =>
  }

  /** `lazy_prefix` keeps look ids unique (its `.*?` head is look-free). */
  lemma LookUniqueLazyPrefixRE(r: R.regex)
    requires LTB.LookUnique(r)
    ensures LTB.LookUnique(R.lazy_prefix(r))
  {
    var pre := R.Re_quant(R.NonNullable, 0, R.CountedQuant(0, None, false), R.Re_character(R.Dot));
    assert R.lazy_prefix(r) == R.Re_con(pre, r);
    assert LTB.LookIds(pre) == {};
    assert LTB.LookUnique(pre);
  }

  /** `remove_capture` keeps a regex in the NESTED fragment: quant shapes survive
      (nullability preserved), and every lookaround leaf stays admissible — its
      body becomes capture-free, so the negative-flavour side condition holds
      outright. */
  lemma RemoveCaptureNestedFragmentRE(r: R.regex)
    requires NestedFragmentRE(r)
    ensures NestedFragmentRE(R.remove_capture(r))
    decreases r
  {
    match r
    case Re_alt(r1, r2) => RemoveCaptureNestedFragmentRE(r1); RemoveCaptureNestedFragmentRE(r2);
    case Re_con(r1, r2) => RemoveCaptureNestedFragmentRE(r1); RemoveCaptureNestedFragmentRE(r2);
    case Re_quant(nul, qid, q, r1) => RemoveCaptureNestedFragmentRE(r1); RemoveCaptureNullableRE(r1);
    case Re_capture(_, r1) => RemoveCaptureNestedFragmentRE(r1);
    case Re_lookaround(lid, la, r1) =>
      RemoveCaptureNestedFragmentRE(r1);
      CaptureFreeRemoveCaptureRE(r1);   // remove_capture(r1) is capture-free -> disjunct holds
    case _ =>
  }

  /** `reverse_regex` keeps a regex in the NESTED fragment (quant nullability
      preserved; a negative lookaround's capture-free body stays capture-free). */
  lemma ReverseNestedFragmentRE(r: R.regex)
    requires NestedFragmentRE(r)
    ensures NestedFragmentRE(R.reverse_regex(r))
    decreases r
  {
    match r
    case Re_alt(r1, r2) => ReverseNestedFragmentRE(r1); ReverseNestedFragmentRE(r2);
    case Re_con(r1, r2) => ReverseNestedFragmentRE(r1); ReverseNestedFragmentRE(r2);
    case Re_quant(nul, qid, q, r1) => ReverseNestedFragmentRE(r1); ReverseNullableRE(r1);
    case Re_capture(_, r1) => ReverseNestedFragmentRE(r1);
    case Re_lookaround(lid, la, r1) =>
      ReverseNestedFragmentRE(r1);
      if !(la.Lookahead? || la.Lookbehind?) { CaptureFreeReverseRE(r1); }
    case _ =>
  }

  /** `lazy_prefix` keeps a regex in the NESTED fragment (its `.*?` head is a
      look-free star). */
  lemma LazyPrefixNestedFragmentRE(r: R.regex)
    requires NestedFragmentRE(r)
    ensures NestedFragmentRE(R.lazy_prefix(r))
  {
    var pre := R.Re_quant(R.NonNullable, 0, R.CountedQuant(0, None, false), R.Re_character(R.Dot));
    assert R.lazy_prefix(r) == R.Re_con(pre, r);
    assert NestedFragmentRE(pre);
  }

  /** `oracle_regex(la, body)` stays in the NESTED fragment when `body` does. */
  lemma OracleRegexNestedFragment(la: R.lookaround, body: R.regex)
    requires NestedFragmentRE(body)
    ensures NestedFragmentRE(CP.oracle_regex(la, body))
  {
    RemoveCaptureNestedFragmentRE(body);
    if la.Lookahead? || la.NegLookahead? {
      assert CP.oracle_regex(la, body) == R.lazy_prefix(R.reverse_regex(R.remove_capture(body)));
      ReverseNestedFragmentRE(R.remove_capture(body));
      LazyPrefixNestedFragmentRE(R.reverse_regex(R.remove_capture(body)));
    } else {
      assert CP.oracle_regex(la, body) == R.lazy_prefix(R.remove_capture(body));
      LazyPrefixNestedFragmentRE(R.remove_capture(body));
    }
  }

  /** `oracle_regex(la, body)` keeps look ids unique. */
  lemma OracleRegexLookUnique(la: R.lookaround, body: R.regex)
    requires LTB.LookUnique(body)
    ensures LTB.LookUnique(CP.oracle_regex(la, body))
  {
    LookUniqueRemoveCaptureRE(body);
    if la.Lookahead? || la.NegLookahead? {
      assert CP.oracle_regex(la, body) == R.lazy_prefix(R.reverse_regex(R.remove_capture(body)));
      LookUniqueReverseRE(R.remove_capture(body));
      LookUniqueLazyPrefixRE(R.reverse_regex(R.remove_capture(body)));
    } else {
      assert CP.oracle_regex(la, body) == R.lazy_prefix(R.remove_capture(body));
      LookUniqueLazyPrefixRE(R.remove_capture(body));
    }
  }

  /** `oracle_regex(la, body)` preserves the look-id SET — so `LidsWellNested`'s
      "body ids above the outer lid" transfers to the build regex. */
  lemma OracleRegexLookIds(la: R.lookaround, body: R.regex)
    ensures LTB.LookIds(CP.oracle_regex(la, body)) == LTB.LookIds(body)
  {
    LookIdsRemoveCaptureRE(body);
    if la.Lookahead? || la.NegLookahead? {
      assert CP.oracle_regex(la, body) == R.lazy_prefix(R.reverse_regex(R.remove_capture(body)));
      LookIdsReverseRE(R.remove_capture(body));
      LookIdsLazyPrefixRE(R.reverse_regex(R.remove_capture(body)));
    } else {
      assert CP.oracle_regex(la, body) == R.lazy_prefix(R.remove_capture(body));
      LookIdsLazyPrefixRE(R.remove_capture(body));
    }
  }

  // --- the NESTED write/nullable/accept classification (NoWriteInstr family
  //     with NestedFragmentRE, gates ADMITTED; identical shape to NoWriteInstrRE) ---

  /** `NoWriteInstrNestedRE` for the `repeat_min` forced-copy chain. */
  lemma NoWriteInstrMinNestedRE(k: nat, qid: R.quantid, r1: R.regex, code: RB.code, start: nat, endl: nat, pc: nat)
    requires NestedFragmentRE(r1)
    requires NfaRepMinRE(k, qid, r1, code, start, endl)
    requires start <= pc < endl
    ensures GetPcRE(code, pc).Some? ==>
      var i := GetPcRE(code, pc).value;
      !i.WriteOracle? && !i.CheckNullable? && !i.Accept?
    decreases CP.rsize(r1), k + 2
  {
    if k == 0 { return; }
    var e1: nat :| GetPcRE(code, start) == Some(RB.SetQuantToClock(qid, false))
      && NfaRepRE(r1, code, start + 1, e1)
      && NfaRepMinRE(k - 1, qid, r1, code, e1, endl);
    NfaRepIncrRE(r1, code, start + 1, e1);
    NfaRepIncrMinRE(k - 1, qid, r1, code, e1, endl);
    if pc == start {
    } else if pc < e1 {
      NoWriteInstrNestedRE(r1, code, start + 1, e1, pc);
    } else {
      NoWriteInstrMinNestedRE(k - 1, qid, r1, code, e1, endl, pc);
    }
  }

  /** `NoWriteInstrNestedRE` for the `repeat_optional` layer chain. */
  lemma NoWriteInstrOptNestedRE(k: nat, greedy: bool, qid: R.quantid, r1: R.regex, code: RB.code, start: nat, endl: nat, pc: nat)
    requires NestedFragmentRE(r1)
    requires NfaRepOptRE(k, greedy, qid, r1, code, start, endl)
    requires start <= pc < endl
    ensures GetPcRE(code, pc).Some? ==>
      var i := GetPcRE(code, pc).value;
      !i.WriteOracle? && !i.CheckNullable? && !i.Accept?
    decreases CP.rsize(r1), k + 2
  {
    if k == 0 { return; }
    var e1: nat :| GetPcRE(code, start) == Some(if greedy then RB.Fork(start + 1, endl) else RB.Fork(endl, start + 1))
      && GetPcRE(code, start + 1) == Some(RB.SetQuantToClock(qid, false))
      && GetPcRE(code, start + 2) == Some(RB.BeginLoop)
      && NfaRepRE(r1, code, start + 3, e1)
      && GetPcRE(code, e1) == Some(RB.EndLoop)
      && NfaRepOptRE(k - 1, greedy, qid, r1, code, e1 + 1, endl);
    NfaRepIncrRE(r1, code, start + 3, e1);
    NfaRepIncrOptRE(k - 1, greedy, qid, r1, code, e1 + 1, endl);
    if pc <= start + 2 {
    } else if pc < e1 {
      NoWriteInstrNestedRE(r1, code, start + 3, e1, pc);
    } else if pc == e1 {
    } else {
      NoWriteInstrOptNestedRE(k - 1, greedy, qid, r1, code, e1 + 1, endl, pc);
    }
  }

  /** The NESTED analogue of `NoWriteInstrRE`: nested-fragment main code emits no
      `WriteOracle`, `CheckNullable`, or `Accept` (the compiler adds those only at
      the `compile_to_write`/`compile_to_bytecode` seam). Lookaround leaves are a
      single gate (allowed); the plus-fragment quant shapes carry over verbatim. */
  lemma NoWriteInstrNestedRE(re: R.regex, code: RB.code, start: nat, endl: nat, pc: nat)
    requires NestedFragmentRE(re)
    requires NfaRepRE(re, code, start, endl)
    requires start <= pc < endl
    ensures GetPcRE(code, pc).Some? ==>
      var i := GetPcRE(code, pc).value;
      !i.WriteOracle? && !i.CheckNullable? && !i.Accept?
    decreases CP.rsize(re), 1
  {
    match re
    case Re_empty =>
    case Re_character(_) =>
    case Re_anchor(_) =>
    case Re_alt(r1, r2) =>
      var e1: nat :| GetPcRE(code, start) == Some(RB.Fork(start + 1, e1 + 1))
        && NfaRepRE(r1, code, start + 1, e1)
        && GetPcRE(code, e1) == Some(RB.Jmp(endl))
        && NfaRepRE(r2, code, e1 + 1, endl);
      NfaRepIncrRE(r1, code, start + 1, e1);
      NfaRepIncrRE(r2, code, e1 + 1, endl);
      if pc == start {
      } else if pc < e1 {
        NoWriteInstrNestedRE(r1, code, start + 1, e1, pc);
      } else if pc == e1 {
      } else {
        NoWriteInstrNestedRE(r2, code, e1 + 1, endl, pc);
      }
    case Re_con(r1, r2) =>
      var e1: nat :| NfaRepRE(r1, code, start, e1) && NfaRepRE(r2, code, e1, endl);
      NfaRepIncrRE(r1, code, start, e1);
      NfaRepIncrRE(r2, code, e1, endl);
      if pc < e1 {
        NoWriteInstrNestedRE(r1, code, start, e1, pc);
      } else {
        NoWriteInstrNestedRE(r2, code, e1, endl, pc);
      }
    case Re_quant(nul, qid, q, r1) =>
      if q.min == 0 && q.max == None {
        var e1: nat :| GetPcRE(code, start) == Some(if q.greedy then RB.Fork(start + 1, e1 + 2) else RB.Fork(e1 + 2, start + 1))
          && GetPcRE(code, start + 1) == Some(RB.SetQuantToClock(qid, false))
          && GetPcRE(code, start + 2) == Some(RB.BeginLoop)
          && NfaRepRE(r1, code, start + 3, e1)
          && GetPcRE(code, e1) == Some(RB.EndLoop)
          && GetPcRE(code, e1 + 1) == Some(RB.Jmp(start))
          && endl == e1 + 2;
        NfaRepIncrRE(r1, code, start + 3, e1);
        if pc <= start + 2 {
        } else if pc < e1 {
          NoWriteInstrNestedRE(r1, code, start + 3, e1, pc);
        } else {
        }
      } else if q.max.Some? {
        var em := NfaRepREQuantInv(nul, qid, q, r1, code, start, endl);
        NfaRepIncrMinRE(q.min as nat, qid, r1, code, start, em);
        NfaRepIncrOptRE((q.max.value - q.min) as nat, q.greedy, qid, r1, code, em, endl);
        if pc < em {
          NoWriteInstrMinNestedRE(q.min as nat, qid, r1, code, start, em, pc);
        } else {
          NoWriteInstrOptNestedRE((q.max.value - q.min) as nat, q.greedy, qid, r1, code, em, endl, pc);
        }
      } else {
        var em, e1 := NfaRepREPlusInv(nul, qid, q, r1, code, start, endl);
        NfaRepIncrMinRE((q.min - 1) as nat, qid, r1, code, start, em);
        NfaRepIncrRE(r1, code, em + 1, e1);
        if pc < em {
          NoWriteInstrMinNestedRE((q.min - 1) as nat, qid, r1, code, start, em, pc);
        } else if pc == em {
        } else if pc < e1 {
          NoWriteInstrNestedRE(r1, code, em + 1, e1, pc);
        } else {
        }
      }
    case Re_capture(cid, r1) =>
      var e1: nat :| GetPcRE(code, start) == Some(RB.SetRegisterToCP(CP.start_reg(cid)))
        && NfaRepRE(r1, code, start + 1, e1)
        && GetPcRE(code, e1) == Some(RB.SetRegisterToCP(CP.end_reg(cid)))
        && endl == e1 + 1;
      NfaRepIncrRE(r1, code, start + 1, e1);
      if pc == start {
      } else if pc < e1 {
        NoWriteInstrNestedRE(r1, code, start + 1, e1, pc);
      } else {
      }
    case Re_lookaround(lid, la, r1) =>
      assert pc == start;
  }

  /** THE NESTED BUILD-CODE CLASSIFICATION. For a nested-fragment build regex
      `og` with unique look ids all strictly above `lid`, the build program
      `compile_to_write(og, lid)` satisfies exactly `LidBuildOkAbove`'s four
      classification conjuncts: gates read strictly above `lid`, writes only
      column `lid`, no `CheckNullable`, no `Accept`. Bounds gates via
      `GatesAboveInstrRE` on the body block `[0, next)` and the write/accept via
      `NoWriteInstrNestedRE`; the trailing pc `next` is the recorder
      `WriteOracle(lid)`. */
  lemma NestedCompileToWriteClassifiedAbove(og: R.regex, lid: R.lookid)
    requires NestedFragmentRE(og)
    requires LTB.LookUnique(og)
    requires lid >= 0
    requires forall x: nat :: x in LTB.LookIds(og) ==> x > lid
    ensures var bc := CP.compile_to_write(og, lid);
      OS.AllGatesAbove(bc, lid) && OS.NoCheckNullable(bc) && OS.WritesOnlyLid(bc, lid) && OS.NoAccept(bc)
  {
    CompileToWriteRepNested(og, lid);
    var bc := CP.compile_to_write(og, lid);
    var next := CP.compile(og, 0, CP.Progress).1;
    assert forall x: nat :: x in LTB.LookIds(og) ==> x > (lid as nat);
    forall pc | 0 <= pc < |bc|
      ensures (bc[pc].CheckOracle? ==> bc[pc].col > lid)
              && (bc[pc].NegCheckOracle? ==> bc[pc].ncl > lid)
              && !bc[pc].CheckNullable? && !bc[pc].Accept?
              && (bc[pc].WriteOracle? ==> bc[pc].wol == lid)
    {
      if pc < next as nat {
        GatesAboveInstrRE(og, bc, 0, next as nat, lid as nat, pc);
        NoWriteInstrNestedRE(og, bc, 0, next as nat, pc);
        assert GetPcRE(bc, pc) == Some(bc[pc]);
      } else {
        assert pc == next as nat;
        assert GetPcRE(bc, pc) == Some(RB.WriteOracle(lid));
      }
    }
  }
}
