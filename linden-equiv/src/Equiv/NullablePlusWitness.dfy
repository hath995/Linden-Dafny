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
  import T = LindenElkTranslate
  import CL = LindenElkCinLooks
  import MCL = LindenElkMainCinLk

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

  /** A lookahead inside a negative lookbehind is IN since gate B (G1): the lookbehind
      column is matched through the mirror world, so a lookbehind's body may hold
      lookaheads (see also `LookNestWitness`). */
  lemma Frag22_NegBehindAheadIn()
    ensures API.Supported(NEG_BEHIND_AHEAD)
  { }

  // ==========================================================================
  // G3a: a greedy CI-nullable plus INSIDE a lookahead body, either polarity
  // (the look loop replays the body with the plus reconstruction).
  // ==========================================================================
  const PLUS_B := R.Raw_con(R.Raw_quant(R.Plus, AOPT), R.Raw_character(R.Dot))   // (a?)+b

  lemma G3a_PlusInLookahead()
    ensures API.Supported(R.Raw_lookaround(R.Lookahead, PLUS_B))      // (?=(a?)+b)
    ensures API.Supported(R.Raw_lookaround(R.NegLookahead, PLUS_B))   // (?!(a?)+b)
  {
    assert R.raw_nullable(AOPT) == R.CINullable;
  }

  // ==========================================================================
  // G3b: a greedy CI-nullable plus INSIDE a lookbehind body, either polarity
  // (the backward look replay reconstructs too; the proof reads it through the mirror).
  // ==========================================================================
  lemma G3b_PlusInLookbehind()
    ensures API.Supported(R.Raw_lookaround(R.Lookbehind, PLUS_B))      // (?<=(a?)+b)
    ensures API.Supported(R.Raw_lookaround(R.NegLookbehind, PLUS_B))   // (?<!(a?)+b)
  {
    assert R.raw_nullable(AOPT) == R.CINullable;
  }

  // ==========================================================================
  // G5a-1 (2026-11-15): a greedy plus over a context-dependent nullable body
  // (CDN), at top level with a look-free body.
  // ==========================================================================
  const WB_OR_A  := R.Raw_alt(R.Raw_anchor(R.WordBoundary), R.Raw_character(R.Dot))   // \b|a
  const A_OPT_END := R.Raw_con(AOPT, R.Raw_anchor(R.EndInput))                         // a?$

  lemma CdnPlusIsSupported()
    ensures API.Supported(R.Raw_quant(R.Plus, WB_OR_A))     // (\b|a)+
    ensures API.Supported(R.Raw_quant(R.Plus, A_OPT_END))   // (a?$)+
  {
    assert R.raw_nullable(WB_OR_A) == R.CDNullable;
    assert R.raw_nullable(A_OPT_END) == R.CDNullable;
  }

  // ==========================================================================
  // G4a (2026-11-15): capture-free lookarounds inside a greedy CI-nullable plus body. A lookaround
  // is context-dependent nullable, so it sits where the body stays CI-nullable (`((?=a)a?)+` is a
  // CDN plus, outside G4a).
  // ==========================================================================
  const LOOK_OR_AOPT   := R.Raw_alt(LOOK_A, AOPT)                                                 // (?=a)|a?
  const A_LOOK_OR_AOPT := R.Raw_alt(R.Raw_con(R.Raw_character(R.Dot), LOOK_A), AOPT)            // a(?=a)|a?
  const NLOOK_OR_AOPT  := R.Raw_alt(R.Raw_lookaround(R.NegLookahead, R.Raw_character(R.Dot)), AOPT)   // (?!a)|a?
  const BLOOK_OR_AOPT  := R.Raw_alt(R.Raw_lookaround(R.Lookbehind, R.Raw_character(R.Dot)), AOPT)     // (?<=a)|a?

  lemma G4a_LookInCinPlus()
    ensures API.Supported(R.Raw_quant(R.Plus, LOOK_OR_AOPT))     // ((?=a)|a?)+
    ensures API.Supported(R.Raw_quant(R.Plus, A_LOOK_OR_AOPT))   // (a(?=a)|a?)+
    ensures API.Supported(R.Raw_quant(R.Plus, NLOOK_OR_AOPT))    // ((?!a)|a?)+
    ensures API.Supported(R.Raw_quant(R.Plus, BLOOK_OR_AOPT))    // ((?<=a)|a?)+
  {
    assert R.raw_nullable(LOOK_OR_AOPT) == R.CINullable;
    assert R.raw_nullable(A_LOOK_OR_AOPT) == R.CINullable;
    assert R.raw_nullable(NLOOK_OR_AOPT) == R.CINullable;
    assert R.raw_nullable(BLOOK_OR_AOPT) == R.CINullable;
  }

  // ==========================================================================
  // G5a-2a (2026-11-15): a greedy CDN plus whose body holds capture-free lookarounds or a CIN plus.
  // A lookaround is context-dependent nullable, so `((?=a)a?)+` is a CDN plus and is now in.
  // ==========================================================================
  const LOOK_OR_B    := R.Raw_alt(LOOK_A, R.Raw_character(R.Dot))                                     // (?=a)|b
  const NLOOK_OR_B   := R.Raw_alt(R.Raw_lookaround(R.NegLookahead, R.Raw_character(R.Dot)), R.Raw_character(R.Dot))   // (?!a)|b
  const BLOOK_OR_B   := R.Raw_alt(R.Raw_lookaround(R.Lookbehind, R.Raw_character(R.Dot)), R.Raw_character(R.Dot))     // (?<=a)|b
  const LOOK_AOPT    := R.Raw_con(LOOK_A, AOPT)                                                        // (?=a)a?
  const WB_CINPLUS   := R.Raw_con(R.Raw_anchor(R.WordBoundary), R.Raw_quant(R.Plus, AOPT))             // \b(a?)+

  lemma G5a2a_CdnPlusBodies()
    ensures API.Supported(R.Raw_quant(R.Plus, LOOK_OR_B))     // ((?=a)|b)+
    ensures API.Supported(R.Raw_quant(R.Plus, NLOOK_OR_B))    // ((?!a)|b)+
    ensures API.Supported(R.Raw_quant(R.Plus, BLOOK_OR_B))    // ((?<=a)|b)+
    ensures API.Supported(R.Raw_quant(R.Plus, LOOK_AOPT))     // ((?=a)a?)+
    ensures API.Supported(R.Raw_quant(R.Plus, WB_CINPLUS))    // (\b(a?)+)+
  {
    assert R.raw_nullable(LOOK_OR_B) == R.CDNullable;
    assert R.raw_nullable(NLOOK_OR_B) == R.CDNullable;
    assert R.raw_nullable(BLOOK_OR_B) == R.CDNullable;
    assert R.raw_nullable(LOOK_AOPT) == R.CDNullable;
    assert R.raw_nullable(AOPT) == R.CINullable;
    assert R.raw_nullable(WB_CINPLUS) == R.CDNullable;
  }

  // ==========================================================================
  // G5a-2b (2026-11-15): a greedy CDN plus inside a nulled plus's body. The reconstruct code of the outer
  // plus holds the inner one's guard, which reads the sub-table `FNulledPlus` builds.
  // ==========================================================================
  const WB_PLUS        := R.Raw_quant(R.Plus, R.Raw_anchor(R.WordBoundary))   // \b+
  const WB_PLUS_OR_E   := R.Raw_alt(WB_PLUS, R.Raw_empty)                     // \b+|
  const WB_OR_A_PLUS   := R.Raw_quant(R.Plus, WB_OR_A)                        // (\b|a)+

  lemma G5a2b_CdnPlusInNulledBody()
    ensures API.Supported(R.Raw_quant(R.Plus, WB_PLUS_OR_E))   // (\b+|)+   a CDN plus in a CIN plus body
    ensures API.Supported(R.Raw_quant(R.Plus, WB_OR_A_PLUS))   // ((\b|a)+)+  a CDN plus in a CDN plus body
  {
    assert R.raw_nullable(R.Raw_anchor(R.WordBoundary)) == R.CDNullable;
    assert R.raw_nullable(WB_PLUS) == R.CDNullable;
    assert R.raw_nullable(WB_PLUS_OR_E) == R.CINullable;
    assert R.raw_nullable(WB_OR_A) == R.CDNullable;
    assert R.raw_nullable(WB_OR_A_PLUS) == R.CDNullable;
  }

  // ==========================================================================
  // G5b-0 (2026-11-16): a greedy CDN plus inside a NEGATIVE lookaround body. The look's oracle column is
  // built by code holding the plus's guard (the oracle V graph carries the table); a negative look is never
  // replayed. (G5b-1, G5b-2 below: a positive look body of either direction may hold one too.)
  // ==========================================================================
  const NEG_AHEAD_CDN  := R.Raw_lookaround(R.NegLookahead, WB_OR_A_PLUS)               // (?!(\b|a)+)
  const NEG_BEHIND_CDN := R.Raw_lookaround(R.NegLookbehind, WB_OR_A_PLUS)              // (?<!(\b|a)+)

  lemma G5b0_CdnPlusInNegLook()
    ensures API.Supported(NEG_AHEAD_CDN)                                      // (?!(\b|a)+)
    ensures API.Supported(NEG_BEHIND_CDN)                                     // (?<!(\b|a)+)
  {
    assert R.raw_nullable(WB_OR_A) == R.CDNullable;
    assert R.raw_nullable(WB_OR_A_PLUS) == R.CDNullable;
  }

  // (G5b-1) A greedy CDN plus inside a LOOKAHEAD body, at the top and nested in another lookahead.
  const POS_AHEAD_CDN := R.Raw_lookaround(R.Lookahead, WB_OR_A_PLUS)                     // (?=(\b|a)+)
  const POS_AHEAD_NESTED_CDN :=
    R.Raw_lookaround(R.Lookahead, R.Raw_con(R.Raw_character(R.Dot), POS_AHEAD_CDN))   // (?=a(?=(\b|a)+))

  lemma G5b1_CdnPlusInLookahead()
    ensures API.Supported(POS_AHEAD_CDN)                                      // (?=(\b|a)+)
    ensures API.Supported(POS_AHEAD_NESTED_CDN)                               // (?=a(?=(\b|a)+))
  {
    assert R.raw_nullable(WB_OR_A) == R.CDNullable;
    assert R.raw_nullable(WB_OR_A_PLUS) == R.CDNullable;
    // `Supported`'s conjuncts, one by one (the solver needs the unfolding spelled out)
    var re1 := R.lazy_prefix(R.annotate(POS_AHEAD_CDN));
    assert NR.NestedFragmentCdnRaw(POS_AHEAD_CDN) && T.Latin1Wf(POS_AHEAD_CDN);
    assert CL.CinLooksCapFreeX(re1) && MCL.CdnTopX(re1);
    var re2 := R.lazy_prefix(R.annotate(POS_AHEAD_NESTED_CDN));
    assert NR.NestedFragmentCdnRaw(POS_AHEAD_NESTED_CDN) && T.Latin1Wf(POS_AHEAD_NESTED_CDN);
    assert CL.CinLooksCapFreeX(re2) && MCL.CdnTopX(re2);
  }

  // (G5b-2) A greedy CDN plus inside a LOOKBEHIND body: at the top, nested in another lookbehind, and inside a
  // lookahead inside a lookbehind (the flipped world holds it in a lookbehind).
  const POS_BEHIND_CDN := R.Raw_lookaround(R.Lookbehind, WB_OR_A_PLUS)                    // (?<=(\b|a)+)
  const POS_BEHIND_NESTED_CDN :=
    R.Raw_lookaround(R.Lookbehind, R.Raw_con(R.Raw_character(R.Dot), POS_BEHIND_CDN))  // (?<=a(?<=(\b|a)+))
  const AHEAD_IN_BEHIND_CDN := R.Raw_lookaround(R.Lookbehind, POS_AHEAD_CDN)               // (?<=(?=(\b|a)+))

  lemma G5b2_CdnPlusInLookbehind()
    ensures API.Supported(POS_BEHIND_CDN)                                     // (?<=(\b|a)+)
    ensures API.Supported(POS_BEHIND_NESTED_CDN)                              // (?<=a(?<=(\b|a)+))
    ensures API.Supported(AHEAD_IN_BEHIND_CDN)                                // (?<=(?=(\b|a)+))
  {
    assert R.raw_nullable(WB_OR_A) == R.CDNullable;
    assert R.raw_nullable(WB_OR_A_PLUS) == R.CDNullable;
    var re1 := R.lazy_prefix(R.annotate(POS_BEHIND_CDN));
    assert NR.NestedFragmentCdnRaw(POS_BEHIND_CDN) && T.Latin1Wf(POS_BEHIND_CDN);
    assert CL.CinLooksCapFreeX(re1) && MCL.CdnTopX(re1);
    var re2 := R.lazy_prefix(R.annotate(POS_BEHIND_NESTED_CDN));
    assert NR.NestedFragmentCdnRaw(POS_BEHIND_NESTED_CDN) && T.Latin1Wf(POS_BEHIND_NESTED_CDN);
    assert CL.CinLooksCapFreeX(re2) && MCL.CdnTopX(re2);
    var re3 := R.lazy_prefix(R.annotate(AHEAD_IN_BEHIND_CDN));
    assert NR.NestedFragmentCdnRaw(AHEAD_IN_BEHIND_CDN) && T.Latin1Wf(AHEAD_IN_BEHIND_CDN);
    assert CL.CinLooksCapFreeX(re3) && MCL.CdnTopX(re3);
  }

  // (G5b-3) Inside a look body, a greedy nullable plus whose body holds a capture-free lookaround: G4a/G5a-2a at
  // look depth, in a positive lookahead, a positive lookbehind, and a negative look.
  const AHEAD_LOOKPLUS_CDN  := R.Raw_lookaround(R.Lookahead, R.Raw_quant(R.Plus, LOOK_OR_B))      // (?=((?=a)|b)+)
  const AHEAD_LOOKPLUS_CIN  := R.Raw_lookaround(R.Lookahead, R.Raw_quant(R.Plus, LOOK_OR_AOPT))   // (?=((?=a)|a?)+)
  const BEHIND_LOOKPLUS_CIN := R.Raw_lookaround(R.Lookbehind, R.Raw_quant(R.Plus, LOOK_OR_AOPT))  // (?<=((?=a)|a?)+)
  const NEG_LOOKPLUS_CIN    := R.Raw_lookaround(R.NegLookahead, R.Raw_quant(R.Plus, LOOK_OR_AOPT)) // (?!((?=a)|a?)+)

  lemma G5b3_LookPlusInLookBody()
    ensures API.Supported(AHEAD_LOOKPLUS_CDN)    // (?=((?=a)|b)+)
    ensures API.Supported(AHEAD_LOOKPLUS_CIN)    // (?=((?=a)|a?)+)
    ensures API.Supported(BEHIND_LOOKPLUS_CIN)   // (?<=((?=a)|a?)+)
    ensures API.Supported(NEG_LOOKPLUS_CIN)      // (?!((?=a)|a?)+)
  {
    assert R.raw_nullable(LOOK_OR_B) == R.CDNullable;
    assert R.raw_nullable(LOOK_OR_AOPT) == R.CINullable;
    var re1 := R.lazy_prefix(R.annotate(AHEAD_LOOKPLUS_CDN));
    assert NR.NestedFragmentCdnRaw(AHEAD_LOOKPLUS_CDN) && T.Latin1Wf(AHEAD_LOOKPLUS_CDN);
    assert CL.CinLooksCapFreeX(re1) && MCL.CdnTopX(re1);
    var re2 := R.lazy_prefix(R.annotate(AHEAD_LOOKPLUS_CIN));
    assert NR.NestedFragmentCdnRaw(AHEAD_LOOKPLUS_CIN) && T.Latin1Wf(AHEAD_LOOKPLUS_CIN);
    assert CL.CinLooksCapFreeX(re2) && MCL.CdnTopX(re2);
    var re3 := R.lazy_prefix(R.annotate(BEHIND_LOOKPLUS_CIN));
    assert NR.NestedFragmentCdnRaw(BEHIND_LOOKPLUS_CIN) && T.Latin1Wf(BEHIND_LOOKPLUS_CIN);
    assert CL.CinLooksCapFreeX(re3) && MCL.CdnTopX(re3);
    var re4 := R.lazy_prefix(R.annotate(NEG_LOOKPLUS_CIN));
    assert NR.NestedFragmentCdnRaw(NEG_LOOKPLUS_CIN) && T.Latin1Wf(NEG_LOOKPLUS_CIN);
    assert CL.CinLooksCapFreeX(re4) && MCL.CdnTopX(re4);
  }

  // ==========================================================================
  // G4b-1 (2026-11-18): a CAPTURING lookaround inside a greedy nullable plus body, off the body's empty paths:
  // every look an empty path of a stamp body can cross is capture-free (`CL.EmptyPathLooksCapFreeX`), the others
  // may capture. At the top regex; a look body keeps G5b-3's scope.
  // ==========================================================================
  const A_LOOKCAP_OR_AOPT := R.Raw_alt(R.Raw_con(R.Raw_character(R.Dot), LOOK_CAP), AOPT)   // a(?=(a))|a?
  const G4B1_PLUS := R.Raw_quant(R.Plus, R.Raw_capture(A_LOOKCAP_OR_AOPT))                // (a(?=(a))|a?)+
  const G4B1_STAR := R.Raw_quant(R.Star, R.Raw_con(G4B1_PLUS, R.Raw_character(R.Dot)))    // (?:(a(?=(a))|a?)+a)*

  /** `annotate`'s output on `G4B1_PLUS` (quant ids from `q`), spelled out: the patterns are too deep for the
      solver to evaluate `annotate_regex` as a ground term, so each step is one unfolding. */
  function PlusA(q: int): R.regex {
    var dot := R.Re_character(R.Dot);
    var alt := R.Re_alt(R.Re_con(dot, R.Re_lookaround(1, R.Lookahead, R.Re_capture(2, dot))),
                        R.Re_quant(R.NonNullable, q + 1, R.CountedQuant(0, Some(1), true), dot));
    R.Re_quant(R.CINullable, q, R.CountedQuant(1, None, true), R.Re_capture(1, alt))
  }

  lemma AnnotPlus(q: int)
    ensures R.annotate_regex(G4B1_PLUS, 1, 1, q) == (PlusA(q), 3, 2, q + 2)
  {
    var dot := R.Re_character(R.Dot);
    var look := R.Re_lookaround(1, R.Lookahead, R.Re_capture(2, dot));
    var aopt := R.Re_quant(R.NonNullable, q + 1, R.CountedQuant(0, Some(1), true), dot);
    var alt := R.Re_alt(R.Re_con(dot, look), aopt);
    assert R.annotate_regex(R.Raw_character(R.Dot), 3, 2, q + 1) == (dot, 3, 2, q + 1);
    assert R.annotate_regex(CAP_A, 2, 2, q + 1) == (R.Re_capture(2, dot), 3, 2, q + 1);
    assert R.annotate_regex(LOOK_CAP, 2, 1, q + 1) == (look, 3, 2, q + 1);
    assert R.annotate_regex(R.Raw_character(R.Dot), 2, 1, q + 1) == (dot, 2, 1, q + 1);
    assert R.annotate_regex(R.Raw_con(R.Raw_character(R.Dot), LOOK_CAP), 2, 1, q + 1) == (R.Re_con(dot, look), 3, 2, q + 1);
    assert R.annotate_regex(R.Raw_character(R.Dot), 3, 2, q + 2) == (dot, 3, 2, q + 2);
    assert R.nullable(dot) == R.NonNullable;
    assert R.annotate_regex(AOPT, 3, 2, q + 1) == (aopt, 3, 2, q + 2);
    assert R.annotate_regex(A_LOOKCAP_OR_AOPT, 2, 1, q + 1) == (alt, 3, 2, q + 2);
    assert R.annotate_regex(R.Raw_capture(A_LOOKCAP_OR_AOPT), 1, 1, q + 1) == (R.Re_capture(1, alt), 3, 2, q + 2);
    assert R.nullable(look) == R.CDNullable;
    assert R.nullable(R.Re_con(dot, look)) == R.NonNullable;
    assert R.nullable(aopt) == R.CINullable;
    assert R.nullable(alt) == R.CINullable;
    assert R.nullable(R.Re_capture(1, alt)) == R.CINullable;
  }

  lemma G4b1_CapLookInPlusBody()
    ensures API.Supported(G4B1_PLUS)    // (a(?=(a))|a?)+
  {
    AnnotPlus(1);
    var re1 := R.lazy_prefix(R.annotate(G4B1_PLUS));
    assert R.annotate(G4B1_PLUS) == R.Re_capture(0, PlusA(1));
    assert NR.NestedFragmentCdnRaw(G4B1_PLUS) && T.Latin1Wf(G4B1_PLUS);
    assert MCL.CdnTopX(re1);
    assert CL.CinLooksCapFreeX(re1);
  }

  lemma G4b1_CapLookInPlusBodyUnderStar()
    ensures API.Supported(G4B1_STAR)    // (?:(a(?=(a))|a?)+a)*
  {
    AnnotPlus(2);
    var dot := R.Re_character(R.Dot);
    assert R.annotate_regex(R.Raw_character(R.Dot), 3, 2, 4) == (dot, 3, 2, 4);
    var con := R.Re_con(PlusA(2), dot);
    assert R.annotate_regex(R.Raw_con(G4B1_PLUS, R.Raw_character(R.Dot)), 1, 1, 2) == (con, 3, 2, 4);
    assert R.nullable(con) == R.NonNullable;
    var star := R.Re_quant(R.NonNullable, 1, R.CountedQuant(0, None, true), con);
    assert R.annotate_regex(G4B1_STAR, 1, 1, 1) == (star, 3, 2, 4);
    assert R.annotate(G4B1_STAR) == R.Re_capture(0, star);
    var re2 := R.lazy_prefix(R.annotate(G4B1_STAR));
    assert NR.NestedFragmentCdnRaw(G4B1_STAR) && T.Latin1Wf(G4B1_STAR);
    assert MCL.CdnTopX(re2);
    assert CL.CinLooksCapFreeX(re2);
  }
}
