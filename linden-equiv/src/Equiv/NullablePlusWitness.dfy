// §2.5a non-vacuity witness: the LAZY nullable plus is in the supported
// fragment; §2.5b (rung F-d0): the GREEDY CI-nullable one is in for
// lookaround-free patterns, and (rung F-c) next to a lookaround too.
module NullablePlusWitness {
  import opened Std.Wrappers
  import R = RegElkRegex
  import API = LindenRegexApi
  import NR = LindenElkNfaRep
  import M = LindenElkMain
  import LSIMCOR = LindenElkLiftSimCore

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

  lemma GreedyNullablePlusWithLookIsSupported()
    // `(?=a)(a?)+` — a lookaround next to a greedy CI-nullable plus: supported
    // (§2.5b, F-c: `MainTheoremL5Cin`), though outside every gated disjunct
    ensures API.SupportedL5Cin(R.Raw_con(LOOK_A, R.Raw_quant(R.Plus, AOPT)))
    ensures API.Supported(R.Raw_con(LOOK_A, R.Raw_quant(R.Plus, AOPT)))
    ensures !API.SupportedL5(R.Raw_con(LOOK_A, R.Raw_quant(R.Plus, AOPT)))
  {
    var p := R.Raw_con(LOOK_A, R.Raw_quant(R.Plus, AOPT));
    assert R.raw_nullable(AOPT) == R.CINullable;
    assert !NR.NoNulledPlusRaw(p);
    var re := R.lazy_prefix(R.annotate(p));
    assert M.NoPosLookbehindRE(re);
    LSIMCOR.NoPosImpliesL5ScopeV1(re);
  }

  // ==========================================================================
  // §2.3 / §2.4: capture under a quantifier, inside or around a look body. No
  // scope condition remains (2026-11-08): the depth-k descent reads its
  // dominance off the presence path on the reconstructed banks. These pin it,
  // so SUPPORTED_FRAGMENT.md cannot drift from the predicates.
  // ==========================================================================
  const CAP_A       := R.Raw_capture(R.Raw_character(R.Dot))          // (a)
  const CAP_STAR    := R.Raw_quant(R.Star, CAP_A)                     // (a)*
  const LOOK_CAP    := R.Raw_lookaround(R.Lookahead, CAP_A)           // (?=(a))
  const LOOK_CAPSTAR := R.Raw_lookaround(R.Lookahead, CAP_STAR)       // (?=(a)*)
  const QUANT_LOOK  := R.Raw_quant(R.Star, R.Raw_capture(LOOK_CAP))   // ((?=(a)))*

  /** §2.3's own example is in every look fragment. */
  lemma Frag23_DepthOne()
    ensures API.SupportedL3(LOOK_CAPSTAR) && API.SupportedL4(LOOK_CAPSTAR) && API.Supported(LOOK_CAPSTAR)
  { }

  /** ...and its NESTED form `(?=(?=(a)*))` is supported. */
  lemma Frag23_Nested()
    ensures API.SupportedL4(R.Raw_lookaround(R.Lookahead, LOOK_CAPSTAR))
    ensures API.Supported(R.Raw_lookaround(R.Lookahead, LOOK_CAPSTAR))
  { }

  /** §2.4's own example, same story. */
  lemma Frag24_DepthOne()
    ensures API.SupportedL3(QUANT_LOOK) && API.SupportedL4(QUANT_LOOK) && API.Supported(QUANT_LOOK)
  { }

  /** `((?=(?=(a))))*` */
  lemma Frag24_Nested()
    ensures API.SupportedL4(R.Raw_quant(R.Star, R.Raw_capture(R.Raw_lookaround(R.Lookahead, LOOK_CAP))))
    ensures API.Supported(R.Raw_quant(R.Star, R.Raw_capture(R.Raw_lookaround(R.Lookahead, LOOK_CAP))))
  { }

  /** The L3 gap F-c left open: `(?=(a)*)(a?)+`, a capture under a quantifier in a
      look body next to a greedy CI-nullable plus. */
  lemma CaptureUnderQuantNextToNullablePlus()
    ensures API.SupportedL5Cin(R.Raw_con(LOOK_CAPSTAR, R.Raw_quant(R.Plus, AOPT)))
    ensures API.Supported(R.Raw_con(LOOK_CAPSTAR, R.Raw_quant(R.Plus, AOPT)))
  {
    var p := R.Raw_con(LOOK_CAPSTAR, R.Raw_quant(R.Plus, AOPT));
    assert R.raw_nullable(AOPT) == R.CINullable;
    var re := R.lazy_prefix(R.annotate(p));
    assert M.NoPosLookbehindRE(re);
    LSIMCOR.NoPosImpliesL5ScopeV1(re);
  }

  // ==========================================================================
  // §2.2 step A: looks inside a capture-free NEGATIVE LOOKAHEAD body. Negative
  // lookbehind bodies stay look-free until step B.
  // ==========================================================================
  const NEG_AHEAD_NESTED := R.Raw_lookaround(R.NegLookahead, R.Raw_con(R.Raw_character(R.Dot), LOOK_A))   // (?!a(?=a))
  const NEG_BEHIND_NESTED := R.Raw_lookaround(R.NegLookbehind,
    R.Raw_con(R.Raw_character(R.Dot), R.Raw_lookaround(R.Lookbehind, R.Raw_character(R.Dot))))            // (?<!a(?<=a))

  lemma Frag22_NegAheadNested()
    ensures API.SupportedL4(NEG_AHEAD_NESTED) && API.Supported(NEG_AHEAD_NESTED)
  { }

  lemma Frag22_NegBehindNestedStillOut()
    ensures !API.SupportedL5(NEG_BEHIND_NESTED)
  { }
}
