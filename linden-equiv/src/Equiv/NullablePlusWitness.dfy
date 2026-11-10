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

  /** The opaque scope conjunct of `API.Supported`, for a pattern with no positive lookbehind. */
  lemma ScopeNoPos(p: R.raw_regex)
    requires M.NoPosLookbehindRE(R.lazy_prefix(R.annotate(p)))
    ensures LSIMCOR.L5ScopeV1RE(R.lazy_prefix(R.annotate(p)))
  {
    LSIMCOR.NoPosImpliesL5ScopeV1(R.lazy_prefix(R.annotate(p)));
  }

  // `a?`  — a nullable body
  const AOPT := R.Raw_quant(R.QuestionMark, R.Raw_character(R.Dot))

  lemma LazyNullablePlusIsSupported()
    // `(a?)+?`  — LAZY plus over a nullable body: NEWLY supported by §2.5a
    ensures API.Supported(R.Raw_quant(R.LazyPlus, AOPT))
    // `(a?){2,}?` — the counted lazy form, also newly supported
    ensures API.Supported(R.Raw_count(R.CountedQuant(2, None, false), AOPT))
  {
    assert R.raw_nullable(AOPT) != R.NonNullable;
    ScopeNoPos(R.Raw_quant(R.LazyPlus, AOPT));
    ScopeNoPos(R.Raw_count(R.CountedQuant(2, None, false), AOPT));
  }

  lemma GreedyNullablePlusIsSupported()
    // `(a?)+` — GREEDY plus over a CI-nullable body: supported (§2.5b, F-d0)
    ensures API.Supported(R.Raw_quant(R.Plus, AOPT))
  {
    assert R.raw_nullable(AOPT) == R.CINullable;
    ScopeNoPos(R.Raw_quant(R.Plus, AOPT));
  }

  // `(?=a)` — a lookahead next to the plus
  const LOOK_A := R.Raw_lookaround(R.Lookahead, R.Raw_character(R.Dot))

  lemma GreedyNullablePlusWithLookIsSupported()
    // `(?=a)(a?)+` — a lookaround next to a greedy CI-nullable plus: supported
    // (§2.5b, F-c: `MainTheoremL5Cin`)
    ensures API.Supported(R.Raw_con(LOOK_A, R.Raw_quant(R.Plus, AOPT)))
  {
    assert R.raw_nullable(AOPT) == R.CINullable;
    ScopeNoPos(R.Raw_con(LOOK_A, R.Raw_quant(R.Plus, AOPT)));
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

  /** §2.3's own example. */
  lemma Frag23_DepthOne()
    ensures API.Supported(LOOK_CAPSTAR)
  {
    ScopeNoPos(LOOK_CAPSTAR);
  }

  /** ...and its NESTED form `(?=(?=(a)*))` is supported. */
  lemma Frag23_Nested()
    ensures API.Supported(R.Raw_lookaround(R.Lookahead, LOOK_CAPSTAR))
  {
    ScopeNoPos(R.Raw_lookaround(R.Lookahead, LOOK_CAPSTAR));
  }

  /** §2.4's own example, same story. */
  lemma Frag24_DepthOne()
    ensures API.Supported(QUANT_LOOK)
  {
    ScopeNoPos(QUANT_LOOK);
  }

  /** `((?=(?=(a))))*` */
  lemma Frag24_Nested()
    ensures API.Supported(R.Raw_quant(R.Star, R.Raw_capture(R.Raw_lookaround(R.Lookahead, LOOK_CAP))))
  {
    ScopeNoPos(R.Raw_quant(R.Star, R.Raw_capture(R.Raw_lookaround(R.Lookahead, LOOK_CAP))));
  }

  /** `(?=(a)*)(a?)+`, a capture under a quantifier in a look body next to a greedy
      CI-nullable plus. */
  lemma CaptureUnderQuantNextToNullablePlus()
    ensures API.Supported(R.Raw_con(LOOK_CAPSTAR, R.Raw_quant(R.Plus, AOPT)))
  {
    assert R.raw_nullable(AOPT) == R.CINullable;
    ScopeNoPos(R.Raw_con(LOOK_CAPSTAR, R.Raw_quant(R.Plus, AOPT)));
  }

  // ==========================================================================
  // §2.2: looks inside a capture-free NEGATIVE look body. A negative lookahead's
  // body may hold any looks; a negative lookbehind's must be lookbehind-only.
  // ==========================================================================
  const NEG_AHEAD_NESTED := R.Raw_lookaround(R.NegLookahead, R.Raw_con(R.Raw_character(R.Dot), LOOK_A))   // (?!a(?=a))
  const NEG_BEHIND_NESTED := R.Raw_lookaround(R.NegLookbehind,
    R.Raw_con(R.Raw_character(R.Dot), R.Raw_lookaround(R.Lookbehind, R.Raw_character(R.Dot))))            // (?<!a(?<=a))
  const NEG_BEHIND_AHEAD := R.Raw_lookaround(R.NegLookbehind, R.Raw_con(R.Raw_character(R.Dot), LOOK_A))  // (?<!a(?=a))

  lemma Frag22_NegAheadNested()
    ensures API.Supported(NEG_AHEAD_NESTED)
  {
    ScopeNoPos(NEG_AHEAD_NESTED);
  }

  lemma Frag22_NegBehindNested()
    ensures API.Supported(NEG_BEHIND_NESTED)
  {
    var re := R.lazy_prefix(R.annotate(NEG_BEHIND_NESTED));
    reveal LSIMCOR.L5ScopeV1RE();
    assert LSIMCOR.L5ScopeV1RE(re);
  }

  /** A lookahead inside a negative lookbehind stays out: the backward span duality
      has no `GroupOkLB` for a lookahead (same limit as a positive lookbehind's body). */
  lemma Frag22_NegBehindAheadStillOut()
    ensures !API.Supported(NEG_BEHIND_AHEAD)
  { }
}
