// Gate B (G1, full depth) and gate C (G2) non-vacuity witnesses: lookaheads inside lookbehinds,
// and captures inside negative looks, are in the
// supported fragment. The lookbehind-only scope (`L5ScopeV1RE`, `EL.NegBehindLBOnlyRaw`)
// has left `API.Supported`; these pin it, so SUPPORTED_FRAGMENT.md cannot drift from the
// predicate. (`R.Dot` stands for a literal character, as in NullablePlusWitness.)
module LookNestWitness {
  import R = RegElkRegex
  import API = LindenRegexApi

  const CH       := R.Raw_character(R.Dot)                                     // a
  const LA_CH    := R.Raw_lookaround(R.Lookahead, CH)                           // (?=a)
  const LA_CAP   := R.Raw_lookaround(R.Lookahead, R.Raw_capture(CH))            // (?=(a))
  const LB_LA    := R.Raw_lookaround(R.Lookbehind, R.Raw_con(CH, LA_CH))        // (?<=a(?=a))
  const LB_CAPLA := R.Raw_lookaround(R.Lookbehind, R.Raw_con(LA_CAP, CH))       // (?<=(?=(a))a)
  const NLB_LA   := R.Raw_lookaround(R.NegLookbehind, R.Raw_con(CH, LA_CH))     // (?<!a(?=a))
  const LA_LB_LA := R.Raw_lookaround(R.Lookahead,
                      R.Raw_lookaround(R.Lookbehind, R.Raw_con(CH, LA_CH)))     // (?=(?<=a(?=a)))
  // Gate C (G2): captures inside NEGATIVE look bodies (their groups stay unset).
  const NLA_CAP    := R.Raw_lookaround(R.NegLookahead, R.Raw_capture(CH))     // (?!(a))
  const NLB_CAP    := R.Raw_lookaround(R.NegLookbehind, R.Raw_capture(CH))    // (?<!(a))
  const NLB_LA_CAP := R.Raw_lookaround(R.NegLookbehind, R.Raw_con(CH, LA_CAP)) // (?<!a(?=(a)))

  /** A lookahead inside a lookbehind, with and without a capture, a negative lookbehind
      holding a lookahead, and three-deep alternation of directions. */
  lemma LookaheadInLookbehindIsSupported()
    ensures API.Supported(LB_LA)
    ensures API.Supported(LB_CAPLA)
    ensures API.Supported(NLB_LA)
    ensures API.Supported(LA_LB_LA)
  {
  }

  /** Gate C (G2): a capture inside a negative lookahead or lookbehind, and inside a
      lookahead nested in a negative lookbehind. */
  lemma CaptureInNegativeLookIsSupported()
    ensures API.Supported(NLA_CAP)
    ensures API.Supported(NLB_CAP)
    ensures API.Supported(NLB_LA_CAP)
  {
  }
}
