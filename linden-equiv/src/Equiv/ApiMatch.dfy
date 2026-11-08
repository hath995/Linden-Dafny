// The user-facing API (future linden-regex src/API/Match.dfy), drafted here
// per LIBRARY_PLAN §"Sequencing" to validate the contract against the real
// theorem before the merge.
//
// VMC-guideline style: Match is a plain function with NO postcondition; its
// correctness is the separate lemma MatchCorrect.

/** The user-facing matcher API (prototype for the future
    `src/API/Match.dfy`): wraps `MainTheorem` behind a plain, postcondition-
    free `Match` function whose correctness lives in the separate
    `MatchCorrect` lemma — the VMC-guideline style of keeping executable code
    unencumbered by specs. */
module LindenRegexApi {
  import opened Std.Wrappers
  import R = RegElkRegex
  import AI = ArrayInterp
  import LC = Chars
  import LG = Groups
  import LT = Tree
  import LS = Semantics
  import WP = WarblrePrimitives
  import NR = LindenElkNfaRep
  import T = LindenElkTranslate
  import LES = LindenElkSpec
  import MAIN = LindenElkMain
  import LSIMCAR = LindenElkLiftSimCarriers
  import LSIMCOR = LindenElkLiftSimCore
  import LSIM = LindenElkLiftSimMain
  import LSIMORA = LindenElkLiftSimOracle
  import MCIN = LindenElkMainCin
  import MCL = LindenElkMainCinLk
  // ==========================================================================
  // The supported fragment — total and executable, so callers can check
  // membership at runtime or by assertion in their own proofs.
  // ==========================================================================
  /** The regex fragment this API actually supports: the plus fragment —
      the star fragment plus anchors `^ $ \b \B`, every quantifier that
      compiles through the engine's generic repetition schemes (`*`, `?`,
      `{n}`, `{n,m}`, `{0,m}` and their lazy forms), and the unbounded
      `min > 0` forms `+`/`{n,}` whose bodies cannot match empty (the
      compiler's do-while scheme; `NR.PlusFragmentRaw` checks the body's
      `raw_nullable` executably — a nullable-bodied `a?+` still needs a
      rewrite) — over Latin-1-well-formed patterns (`T.Latin1Wf`); exactly
      `MainTheorem`'s precondition, exposed so callers can check membership
      at runtime or in their own proofs.

      LOOKAROUNDS. Both flavours are supported, with look-free (non-nested)
      plus-fragment bodies:
        - `(?<=…)` / `(?<!…)` — capture-free body;
        - `(?=…)`  — body may CAPTURE; the lookahead's captures are
          reconstructed into the overall match (the L3a value-lift /
          FLookLoop machinery);
        - `(?!…)`  — capture-free body (a negative look records nothing).

      NOTE the predicate below is still spelled `LookBehindFragmentRaw` for
      historical reasons; it admits both flavours. Renaming is pending. */
  predicate SupportedL3(pattern: R.raw_regex) {
    NR.LookBehindFragmentRaw(pattern) && T.Latin1Wf(pattern)
    // §2.5b INTERIM: the layout arms for the greedy-nullable `+` (the
    // CIN-GREEDY end-fork scheme) are in place beneath this gate, but the
    // nulled-plus capture RECONSTRUCTION theorem is not — so the gate holds
    // greedy-nullable `+` out until it lands. Drop this conjunct to flip.
    && NR.NoNulledPlusRaw(pattern)
  }

  /** L4: arbitrarily NESTED capturing positive lookaheads. The nested fragment
      (`NR.NestedFragmentRaw`: look bodies may themselves contain looks) under
      two purely syntactic, executable scope conditions:
        - no POSITIVE lookbehind anywhere (`NoPosLookbehindRaw`; negative
          lookbehinds are fine);
        - NEGATIVE look bodies are look-free (`NegLooksLookFreeRaw`).
      Captures may sit under quantifiers, inside and around look bodies (§2.3/§2.4).
      Exactly `MainTheoremL4`'s precondition (via `LSIMCOR.L4ScopeFromRaw`). */
  predicate SupportedL4(pattern: R.raw_regex) {
    NR.NestedFragmentRaw(pattern) && T.Latin1Wf(pattern)
    && NR.NoPosLookbehindRaw(pattern)
    && NR.NegLooksLookFreeRaw(pattern)
    && NR.NoNulledPlusRaw(pattern)   // §2.5b interim (see SupportedL3)
  }

  /** (L5) The nested fragment with POSITIVE LOOKBEHINDS: a positive lookbehind's
      body is lookbehind-only, a lookahead's body is scoped recursively (it may itself
      contain positive lookbehinds, e.g. `(?=x(?<=y))`) — the EXECUTABLE
      `LSIMCOR.L5ScopeV1RE` on the annotated regex — plus the negative-look
      condition as in `SupportedL4`. Exactly `MainTheoremL5`'s precondition (via
      `LSIMORA.L5ScopeFromRawFull`). */
  predicate SupportedL5(pattern: R.raw_regex) {
    NR.NestedFragmentRaw(pattern) && T.Latin1Wf(pattern)
    && LSIMCOR.L5ScopeV1RE(R.lazy_prefix(R.annotate(pattern)))
    && NR.NegLooksLookFreeRaw(pattern)
    && NR.NoNulledPlusRaw(pattern)   // §2.5b interim (see SupportedL3)
  }

  /** The supported fragment: the depth-1 fragment (`SupportedL3`), the nested
      forward fragment (`SupportedL4`) or the nested lookbehind fragment (`SupportedL5`). */
  predicate Supported(pattern: R.raw_regex) {
    SupportedL3(pattern) || SupportedL4(pattern) || SupportedL5(pattern) || SupportedCin(pattern)
    || SupportedL5Cin(pattern)
  }

  /** (§2.5b F-c) `SupportedL5` WITHOUT the interim gate conjunct: greedy
      CI-nullable pluses (`(a?)+`) may sit next to lookarounds, provided no look
      body holds a nulled plus (`MCL.LooksNoNulledPlusX`) and every greedy
      CI-nullable plus has a look-free body (`MCL.CinBodiesLookFreeX`), both
      checked executably on the annotated regex. Exactly
      `MCL.MainTheoremL5Cin`'s precondition (via `LSIMORA.L5ScopeFromRawFull`). */
  predicate SupportedL5Cin(pattern: R.raw_regex) {
    NR.NestedFragmentRaw(pattern) && T.Latin1Wf(pattern)
    && LSIMCOR.L5ScopeV1RE(R.lazy_prefix(R.annotate(pattern)))
    && NR.NegLooksLookFreeRaw(pattern)
    && MCL.LooksNoNulledPlusX(R.lazy_prefix(R.annotate(pattern)))
    && MCL.CinBodiesLookFreeX(R.lazy_prefix(R.annotate(pattern)))
  }

  /** (§2.5b) The LOOKAROUND-FREE nested fragment with NO nulled-plus gate: the
      greedy CI-nullable `+`/`{n,}` (`(a?)+`, `(a|b?)+`, ...) is supported, its
      captures reconstructed by the engine's `FReconstructPlus` and proved to be
      the spec's (`MCIN.MainTheoremCin`). CDN-greedy pluses stay out (the
      nested fragment's `Plus` arm excludes them). Lookarounds together with a
      greedy nullable `+` are `SupportedL5Cin` (rung F-c). */
  predicate SupportedCin(pattern: R.raw_regex) {
    NR.NestedFragmentRaw(pattern) && T.Latin1Wf(pattern) && NR.LookFreeRaw(pattern)
  }

  // ==========================================================================
  // The depth-1 fragment is a sub-fragment of the L5 scope: a depth-1 look body
  // is look-free, hence trivially lookbehind-only and negative-look-free.
  // ==========================================================================
  lemma LookFreeNegLooksRaw(ra: R.raw_regex)
    requires NR.LookFreeRaw(ra)
    ensures NR.NegLooksLookFreeRaw(ra)
    decreases ra
  {
    match ra
    case Raw_alt(r1, r2) => LookFreeNegLooksRaw(r1); LookFreeNegLooksRaw(r2);
    case Raw_con(r1, r2) => LookFreeNegLooksRaw(r1); LookFreeNegLooksRaw(r2);
    case Raw_quant(_, r1) => LookFreeNegLooksRaw(r1);
    case Raw_count(_, r1) => LookFreeNegLooksRaw(r1);
    case Raw_capture(r1) => LookFreeNegLooksRaw(r1);
    case _ =>
  }

  lemma DepthOneNegLooksRaw(ra: R.raw_regex)
    requires NR.LookBehindFragmentRaw(ra)
    ensures NR.NegLooksLookFreeRaw(ra)
    decreases ra
  {
    match ra
    case Raw_alt(r1, r2) => DepthOneNegLooksRaw(r1); DepthOneNegLooksRaw(r2);
    case Raw_con(r1, r2) => DepthOneNegLooksRaw(r1); DepthOneNegLooksRaw(r2);
    case Raw_quant(_, r1) => DepthOneNegLooksRaw(r1);
    case Raw_count(_, r1) => DepthOneNegLooksRaw(r1);
    case Raw_capture(r1) => DepthOneNegLooksRaw(r1);
    case Raw_lookaround(_, r1) => LookFreeNegLooksRaw(r1);
    case _ =>
  }

  lemma LookFreeL5ScopeV1(re: R.regex)
    requires NR.LookFreeRE(re)
    ensures LSIMCOR.L5ScopeV1RE(re)
    decreases re
  {
    reveal LSIMCOR.L5ScopeV1RE();
    match re
    case Re_alt(r1, r2) => LookFreeL5ScopeV1(r1); LookFreeL5ScopeV1(r2);
    case Re_con(r1, r2) => LookFreeL5ScopeV1(r1); LookFreeL5ScopeV1(r2);
    case Re_quant(_, _, _, r1) => LookFreeL5ScopeV1(r1);
    case Re_capture(_, r1) => LookFreeL5ScopeV1(r1);
    case _ =>
  }

  lemma DepthOneL5ScopeV1(re: R.regex)
    requires NR.LookBehindFragmentRE(re)
    ensures LSIMCOR.L5ScopeV1RE(re)
    decreases re
  {
    reveal LSIMCOR.L5ScopeV1RE();
    match re
    case Re_alt(r1, r2) => DepthOneL5ScopeV1(r1); DepthOneL5ScopeV1(r2);
    case Re_con(r1, r2) => DepthOneL5ScopeV1(r1); DepthOneL5ScopeV1(r2);
    case Re_quant(_, _, _, r1) => DepthOneL5ScopeV1(r1);
    case Re_capture(_, r1) => DepthOneL5ScopeV1(r1);
    case Re_lookaround(_, _, r1) => NR.LookFreeLBOnly(r1); LookFreeL5ScopeV1(r1);
    case _ =>
  }

  /** The three L5 conditions of a depth-1 pattern. */
  lemma DepthOneL5Conditions(raw: R.raw_regex)
    requires NR.LookBehindFragmentRaw(raw)
    ensures NR.NestedFragmentRaw(raw) && NR.NegLooksLookFreeRaw(raw)
    ensures LSIMCOR.L5ScopeV1RE(R.lazy_prefix(R.annotate(raw)))
  {
    NR.LookBehindFragmentIsNestedRaw(raw);
    DepthOneNegLooksRaw(raw);
    var ast := R.annotate(raw);
    assert NR.LookBehindFragmentRaw(R.Raw_capture(raw));
    NR.AnnotateLookBehindFragment(R.Raw_capture(raw), 0, 1, 1);
    assert ast == R.annotate_regex(R.Raw_capture(raw), 0, 1, 1).0;
    DepthOneL5ScopeV1(ast);
    reveal LSIMCOR.L5ScopeV1RE();
    var pre := R.Re_quant(R.NonNullable, 0, R.CountedQuant(0, None, false), R.Re_character(R.Dot));
    assert R.lazy_prefix(ast) == R.Re_con(pre, ast);
  }

  /** Every `SupportedL3` pattern is `SupportedL5`. */
  lemma SupportedL3ImpliesL5(pattern: R.raw_regex)
    requires SupportedL3(pattern)
    ensures SupportedL5(pattern)
  {
    DepthOneL5Conditions(pattern);
  }

  /** A depth-1 pattern with greedy CI-nullable pluses is `SupportedL5Cin` under
      the same two conditions as any other: no look body holds one, and each has
      a look-free body. */
  lemma DepthOneCinIsL5Cin(pattern: R.raw_regex)
    requires NR.LookBehindFragmentRaw(pattern) && T.Latin1Wf(pattern)
    requires MCL.LooksNoNulledPlusX(R.lazy_prefix(R.annotate(pattern)))
    requires MCL.CinBodiesLookFreeX(R.lazy_prefix(R.annotate(pattern)))
    ensures SupportedL5Cin(pattern)
  {
    DepthOneL5Conditions(pattern);
  }

  // ==========================================================================
  // The verified matcher. Returns the JS-style capture array: slots 2i/2i+1
  // hold group i's start/end (group 0 = the whole match), -1 for unset.
  // ==========================================================================
  /** The verified matcher: runs the compiled RegElk engine
      (`AI.FFullMatch`) and normalizes its result into the JS-style capture
      array (slots `2i`/`2i+1` = group `i`'s start/end, group 0 = the whole
      match, `-1` for unset). No postcondition — see `MatchCorrect`. */
  function Match(pattern: R.raw_regex, str: string): Option<seq<int>> {
    LES.Normalize(AI.FFullMatch(pattern, str))
  }

  // THE contract: on the supported fragment, Match IS the answer the
  // ECMAScript tree semantics demands.
  /** THE contract: on any `Supported` pattern, `Match` computes exactly the
      answer the ECMAScript tree semantics (`LES.MatcherSpec`) demands. A thin
      dispatch over `LSIM.MainTheoremL4` / `LSIM.MainTheoremL5` (the depth-1
      fragment is a sub-fragment of L5, `SupportedL3ImpliesL5`). */
  lemma MatchCorrect(pattern: R.raw_regex, str: string)
    requires Supported(pattern)
    ensures LES.MatcherSpec(pattern, str, Match(pattern, str))
  {
    if SupportedL3(pattern) {
      SupportedL3ImpliesL5(pattern);
    }
    if SupportedL4(pattern) {
      LSIMCOR.L4ScopeFromRaw(pattern);
      LSIM.MainTheoremL4(pattern, str);
    } else if SupportedL5(pattern) {
      LSIMORA.L5ScopeFromRawFull(pattern);
      LSIM.MainTheoremL5(pattern, str);
    } else if SupportedL5Cin(pattern) {
      LSIMORA.L5ScopeFromRawFull(pattern);
      MCL.LooksNoNulledPlusXSound(R.lazy_prefix(R.annotate(pattern)));
      MCL.CinBodiesLookFreeXSound(R.lazy_prefix(R.annotate(pattern)));
      MCL.MainTheoremL5Cin(pattern, str);
    } else {
      MCIN.MainTheoremCin(pattern, str);
    }
  }

  // ==========================================================================
  // The transfer principle: any fact proven of THE backtracking tree of
  // `pattern` on `str` is a fact about Match's answer — the answer is the
  // capture array of the tree's first leaf, no more and no less.
  // ==========================================================================
  /** The transfer principle: for a `Supported` pattern, any fact proven about
      THE backtracking tree `t` of `pattern` on `str` transfers to `Match`'s
      answer — it is exactly the capture array of `t`'s first leaf
      (`LT.FirstLeaf`), no more and no less. */
  lemma MatchIsFirstLeaf(pattern: R.raw_regex, str: string, t: LT.Tree)
    requires Supported(pattern)
    requires LS.IsTree(LES.TheRer(pattern), [LS.Areg(LES.SpecRegex(pattern))],
                       LC.InitInput(str), LG.Empty, WP.Forward, t)
    ensures Match(pattern, str)
         == (match LT.FirstLeaf(t, LC.InitInput(str))
             case None => None
             case Some(leaf) => Some(LES.CapArrayOfLeaf(leaf, LES.NGroups(pattern))))
  {
    MatchCorrect(pattern, str);
    var res := (match LT.FirstLeaf(t, LC.InitInput(str))
                case None => None
                case Some(leaf) => Some(LES.CapArrayOfLeaf(leaf, LES.NGroups(pattern))));
    assert LES.MatcherSpec(pattern, str, res);
    LES.MatcherSpecExistsUnique(pattern, str);
  }

  // Match agrees with the (exponential-time) executable reference semantics —
  // both satisfy MatcherSpec, which has a unique answer. This is the bridge
  // the differential-testing harness and the worked examples run on.
  /** `Match` agrees with the (exponential-time) executable reference semantics
      `LES.SpecResultByComputation` — both satisfy the same `MatcherSpec`, which
      has a unique answer. The bridge differential testing and the worked
      examples run on. */
  lemma MatchEqualsComputedSpec(pattern: R.raw_regex, str: string)
    requires Supported(pattern)
    ensures Match(pattern, str) == LES.SpecResultByComputation(pattern, str)
  {
    MatchCorrect(pattern, str);
    LES.MatcherSpecExistsUnique(pattern, str);
  }
}
