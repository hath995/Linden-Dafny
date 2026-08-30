// §2.5a non-vacuity witness: the LAZY nullable plus is now in the supported
// fragment, and the GREEDY one is still out (that is §2.5b).
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

  lemma GreedyNullablePlusIsStillOut()
    // `(a?)+` — GREEDY plus over a nullable body: still excluded (§2.5b)
    ensures !API.Supported(R.Raw_quant(R.Plus, AOPT))
  {
    assert R.raw_nullable(AOPT) != R.NonNullable;
  }
}
