// The user-facing API (future linden-regex src/API/Match.dfy), drafted here
// per LIBRARY_PLAN §"Sequencing" to validate the contract against the real
// theorem before the merge.
//
// VMC-guideline style: Match is a plain function with NO postcondition; its
// correctness is the separate lemma MatchCorrect.

/** The user-facing matcher API (prototype for the future
    `src/API/Match.dfy`): wraps `MCL.MainTheoremL5Cin` behind a plain, postcondition-
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
  import EL = LindenElkEntryLk
  import T = LindenElkTranslate
  import LES = LindenElkSpec
  import LSIMCAR = LindenElkLiftSimCarriers
  import LSIMCOR = LindenElkLiftSimCore
  import LSIMORA = LindenElkLiftSimOracle
  import MCL = LindenElkMainCinLk
  import MCG = LindenElkMainCinG4b2   // (G4b-2) the theorem on the four-case transports
  import CL = LindenElkCinLooks     // (G4a) the CIN-body scope
  import NRC = LindenElkNulledRecon
  import M = LindenElkMain
  import GF = LindenElkGateFlip   // (G3b) the uniform gate from the CIN fragment
  import RF = LindenElkReconFrame   // (G5b) CinBodiesLookFreeRE
  // ==========================================================================
  // The supported fragment — total and executable, so callers can check
  // membership at runtime or by assertion in their own proofs.
  // ==========================================================================
  /** The supported fragment. A pattern is supported when:
        - it is in the nested fragment (`NR.NestedFragmentCdnRaw`): looks may hold
          looks, captures may sit under quantifiers and inside negative look bodies;
        - it is Latin-1 well-formed (`T.Latin1Wf`).
      Nothing else. Greedy nullable pluses (CI: `(a?)+`; CDN: `(\\b|a)+`) may sit anywhere, top level or inside
      a look body of either direction (G3a/G3b, G5a-1/2, G5b-0..3), and their bodies may hold lookarounds that
      CAPTURE, on the body's empty paths too (G4a, G4b-1, G4b-2: `((?=(a))|b?)+`, `(?=((?=(a))|b?)+)`,
      `(?<=((?=(a))|b?)+)`). Looks nest to any depth in either direction: lookaheads inside lookbehinds and
      lookbehinds inside lookaheads (gate B, G1 full depth). `MCG.MainTheoremL5Cin`'s precondition, with the
      vacuous CDN-top scope (`MCL.CdnTopXAll`) and look gate (`M.LookBodiesPlusGateAll`) discharged.
      `SUPPORTED_FRAGMENT.md` lists what this admits and why each gap exists. */
  predicate Supported(pattern: R.raw_regex) {
    NR.NestedFragmentCdnRaw(pattern) && T.Latin1Wf(pattern)
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
      answer the ECMAScript tree semantics (`LES.MatcherSpec`) demands. */
  lemma MatchCorrect(pattern: R.raw_regex, str: string)
    requires Supported(pattern)
    ensures LES.MatcherSpec(pattern, str, Match(pattern, str))
  {
    MCL.CdnTopXAll(R.lazy_prefix(R.annotate(pattern)));
    MCL.CdnTopXSound(R.lazy_prefix(R.annotate(pattern)));
    MCG.MainTheoremL5Cin(pattern, str);
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
