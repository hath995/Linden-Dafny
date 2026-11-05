// §2.5a non-vacuity witness: the LAZY nullable plus is in the supported
// fragment; §2.5b (rung F-d0): the GREEDY CI-nullable one is in for
// lookaround-free patterns, and still out next to a lookaround (rung F-c).
module NullablePlusWitness {
  import opened Std.Wrappers
  import R = RegElkRegex
  import API = LindenRegexApi
  import NR = LindenElkNfaRep

  // `a?`  — a nullable body
  const AOPT := R.Raw_quant(R.QuestionMark, R.Raw_character(R.Dot))

  lemma LazyNullablePlusIsSupported()
    // `(a?)+?`  — LAZY plus over a nullable body: NEWLY supported by §2.5a
    ensures API.Supported(R.Raw_quant(R.LazyPlus, AOPT))
    // `(a?){2,}?` — the counted lazy form, also newly supported
    ensures API.Supported(R.Raw_count(R.CountedQuant(2, None, false), AOPT))
  {
    assert R.raw_nullable(AOPT) != R.NonNullable;
    assert NR.LookBehindFragmentRaw(R.Raw_quant(R.LazyPlus, AOPT));
    assert NR.LookBehindFragmentRaw(R.Raw_count(R.CountedQuant(2, None, false), AOPT));
  }

  lemma GreedyNullablePlusIsSupported()
    // `(a?)+` — GREEDY plus over a CI-nullable body: supported (§2.5b, F-d0)
    ensures API.SupportedCin(R.Raw_quant(R.Plus, AOPT)) && API.Supported(R.Raw_quant(R.Plus, AOPT))
  {
    assert R.raw_nullable(AOPT) == R.CINullable;
  }

  // `(?=a)` — a lookahead next to the plus
  const LOOK_A := R.Raw_lookaround(R.Lookahead, R.Raw_character(R.Dot))

  lemma GreedyNullablePlusWithLookIsStillOut()
    // `(?=a)(a?)+` — a lookaround and a greedy nullable plus: still excluded
    // (machine B, the lift-sim band, is not stamp-aware yet: rung F-c)
    ensures !API.Supported(R.Raw_con(LOOK_A, R.Raw_quant(R.Plus, AOPT)))
  {
    assert R.raw_nullable(AOPT) != R.NonNullable;
    assert !NR.LookFreeRaw(R.Raw_con(LOOK_A, R.Raw_quant(R.Plus, AOPT)));
  }

  // ==========================================================================
  // §2.3 / §2.4 boundary (investigated 2026-08-30). Both conditions are
  // conjuncts of SupportedL4/L5 ONLY, so a DEPTH-1 pattern takes the L3
  // disjunct and is already covered. These pin that, so SUPPORTED_FRAGMENT.md
  // cannot drift from the predicates again.
  // ==========================================================================
  const CAP_A       := R.Raw_capture(R.Raw_character(R.Dot))          // (a)
  const CAP_STAR    := R.Raw_quant(R.Star, CAP_A)                     // (a)*
  const LOOK_CAP    := R.Raw_lookaround(R.Lookahead, CAP_A)           // (?=(a))
  const LOOK_CAPSTAR := R.Raw_lookaround(R.Lookahead, CAP_STAR)       // (?=(a)*)
  const QUANT_LOOK  := R.Raw_quant(R.Star, R.Raw_capture(LOOK_CAP))   // ((?=(a)))*

  /** §2.3's own example verifies TODAY, via the depth-1 fragment. */
  lemma Frag23_DepthOneIsSupported()
    ensures API.SupportedL3(LOOK_CAPSTAR) && API.Supported(LOOK_CAPSTAR)
    ensures !API.SupportedL4(LOOK_CAPSTAR) && !API.SupportedL5(LOOK_CAPSTAR)
  { assert !NR.LookBodiesNoCapUnderQuantRaw(LOOK_CAPSTAR); }

  /** ...and the NESTED form really is out — nesting forces L4/L5. */
  lemma Frag23_NestedIsNotSupported()
    ensures !API.Supported(R.Raw_lookaround(R.Lookahead, LOOK_CAPSTAR))
  {
    assert !NR.LookFreeRaw(LOOK_CAPSTAR);
    assert !NR.LookBodiesNoCapUnderQuantRaw(R.Raw_lookaround(R.Lookahead, LOOK_CAPSTAR));
  }

  /** §2.4's own example, same story. */
  lemma Frag24_DepthOneIsSupported()
    ensures API.SupportedL3(QUANT_LOOK) && API.Supported(QUANT_LOOK)
    ensures !API.SupportedL4(QUANT_LOOK) && !API.SupportedL5(QUANT_LOOK)
  { assert !NR.QuantsLookCapFreeRaw(QUANT_LOOK); }

  lemma Frag24_NestedIsNotSupported()
    ensures !API.Supported(R.Raw_quant(R.Star,
                             R.Raw_capture(R.Raw_lookaround(R.Lookahead, LOOK_CAP))))
  {
    assert !NR.LookFreeRaw(LOOK_CAP);
    assert !NR.QuantsLookCapFreeRaw(R.Raw_quant(R.Star,
                                      R.Raw_capture(R.Raw_lookaround(R.Lookahead, LOOK_CAP))));
  }
}
