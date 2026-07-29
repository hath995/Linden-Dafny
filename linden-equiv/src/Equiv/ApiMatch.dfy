// The user-facing API (future linden-regex src/API/Match.dfy), drafted here
// per LIBRARY_PLAN §"Sequencing" to validate the contract against the real
// theorem before the merge.
//
// VMC-guideline style: Match is a plain function with NO postcondition; its
// correctness is the separate lemma MatchCorrect.
include "MainTheorem.dfy"

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
  predicate Supported(pattern: R.raw_regex) {
    NR.LookBehindFragmentRaw(pattern) && T.Latin1Wf(pattern)
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
      wrapper around `MAIN.MainTheorem`. */
  lemma MatchCorrect(pattern: R.raw_regex, str: string)
    requires Supported(pattern)
    ensures LES.MatcherSpec(pattern, str, Match(pattern, str))
  {
    MAIN.MainTheorem(pattern, str);
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
