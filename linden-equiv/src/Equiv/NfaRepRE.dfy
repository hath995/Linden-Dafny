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
module LindenElkNfaRep {
  import opened Std.Wrappers
  import R = RegElkRegex
  import RC = Charclasses
  import RB = Bytecode
  import CP = Compiler
  import T = LindenElkTranslate

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
      (la.Lookbehind? || la.NegLookbehind?)
      && CaptureFreeRE(r1) && LookFreeRE(r1) && PlusFragmentRE(r1)
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
      (look.Lookbehind? || look.NegLookbehind?)
      && CaptureFreeRaw(r1) && LookFreeRaw(r1) && PlusFragmentRaw(r1)
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
      AnnotateCaptureFree(r1, c, l + 1, q);
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

  /** The oracle build regex of a lookbehind-fragment lookaround stays in the
      PLUS fragment: for lookbehinds `oracle_regex` is
      `lazy_prefix(remove_capture(body))`, `remove_capture` is the identity on
      the capture-free body, and the lazy prefix's quantifier is star-shaped —
      so the whole existing forward build pipeline applies unchanged. */
  lemma OracleRegexPlusFragment(la: R.lookaround, body: R.regex)
    requires la.Lookbehind? || la.NegLookbehind?
    requires CaptureFreeRE(body) && PlusFragmentRE(body)
    ensures PlusFragmentRE(CP.oracle_regex(la, body))
  {
    RemoveCaptureFreeId(body);
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
  lemma {:isolate_assertions} CompileNfaRepMinRE(k: nat, qid: R.quantid, r1: R.regex, start: nat, tl: CP.treelist, next: int, prev: RB.code)
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
  lemma {:isolate_assertions} CompileNfaRepOptRE(k: nat, greedy: bool, qid: R.quantid, r1: R.regex, start: nat, tl: CP.treelist, next: int, prev: RB.code)
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
  lemma {:isolate_assertions} CompileNfaRepRE(re: R.regex, start: nat, tl: CP.treelist, next: int, prev: RB.code)
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
        assert (pre1 + Flat(body_code)) + [fork] == prev + Flat(tl);
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
}
