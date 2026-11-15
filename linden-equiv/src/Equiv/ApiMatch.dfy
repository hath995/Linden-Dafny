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
  import CL = LindenElkCinLooks     // (G4a) the CIN-body scope
  import NRC = LindenElkNulledRecon
  import M = LindenElkMain
  import GF = LindenElkGateFlip   // (G3b) the uniform gate from the CIN fragment
  // ==========================================================================
  // The supported fragment — total and executable, so callers can check
  // membership at runtime or by assertion in their own proofs.
  // ==========================================================================
  /** The supported fragment. A pattern is supported when:
        - it is in the nested fragment (`NR.NestedFragmentRaw`): looks may hold
          looks, captures may sit under quantifiers, and negative look bodies are
          capture-free;
        - it is Latin-1 well-formed (`T.Latin1Wf`);
        - every lookaround inside a greedy nullable plus body is capture-free
          (`CL.CinLooksCapFreeX`; G4a: `((?=a)|a?)+`, G5a-2a: `((?=a)|b)+`). A look body of either
          kind may hold a greedy CI-nullable plus with a look-free body (G3a lookahead, G3b lookbehind);
        - a greedy CDN plus sits outside every look body and every greedy nullable plus body
          (`MCL.CdnTopX`; G5a-1: `(\\b|a)+`).
      Looks nest to any depth in either direction: lookaheads inside lookbehinds and
      lookbehinds inside lookaheads (gate B, G1 full depth). Exactly
      `MCL.MainTheoremL5Cin`'s precondition. `SUPPORTED_FRAGMENT.md` lists what this admits
      and why each gap exists. */
  predicate Supported(pattern: R.raw_regex) {
    NR.NestedFragmentCdnRaw(pattern) && T.Latin1Wf(pattern)
    && CL.CinLooksCapFreeX(R.lazy_prefix(R.annotate(pattern)))
    // (G5a-1, G5a-2a) a greedy CDN plus is supported outside look bodies and nullable plus bodies; its body
    // may hold capture-free looks and CIN pluses: `(\\b|a)+`, `(a?$)+`, `(^|a)+b`, `((?=a)|b)+`, `(\\b(a?)+)+`
    && MCL.CdnTopX(R.lazy_prefix(R.annotate(pattern)))
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
    CL.CinLooksCapFreeXSound(R.lazy_prefix(R.annotate(pattern)));
    MCL.CdnTopXSound(R.lazy_prefix(R.annotate(pattern)));
    GateFromCdnTopG4(R.lazy_prefix(R.annotate(pattern)));              // (G5a-1, G4a) the gate from the scope
    MCL.MainTheoremL5Cin(pattern, str);
  }

  /** (G4a, G5a-2a) The look-bodies gate from the scope: a nullable plus body may hold capture-free looks,
      and every look body is in the look-free CIN fragment, which is what the gate asks at a look node. */
  lemma GateFromCdnTopG4(re: R.regex)
    requires NRC.CdnTopRE(re) && CL.CinLooksCapFreeRE(re)
    ensures M.LookBodiesPlusGateRE(re)
    decreases re
  {
    match re
    case Re_alt(r1, r2) => GateFromCdnTopG4(r1); GateFromCdnTopG4(r2);
    case Re_con(r1, r2) => GateFromCdnTopG4(r1); GateFromCdnTopG4(r2);
    case Re_capture(_, r1) => GateFromCdnTopG4(r1);
    case Re_lookaround(_, _, r1) => GF.GateFromCin(r1);
    case Re_quant(nul, _, q, r1) =>
      if q.min != 0 && q.max.None? && q.greedy && nul == R.CDNullable {
        GateFromCinG4(r1);   // (G5a-2a) a CDN plus body may hold capture-free looks
      } else if q.min != 0 && q.max.None? && q.greedy && nul == R.CINullable {
        GateFromCinG4(r1);
      } else {
        GateFromCdnTopG4(r1);
      }
    case _ =>
  }

  lemma GateFromCinG4(re: R.regex)
    requires NRC.NoCdnPlusRE(re) && CL.CinLooksCapFreeRE(re)
    ensures M.LookBodiesPlusGateRE(re)
    decreases re
  {
    match re
    case Re_alt(r1, r2) => GateFromCinG4(r1); GateFromCinG4(r2);
    case Re_con(r1, r2) => GateFromCinG4(r1); GateFromCinG4(r2);
    case Re_quant(_, _, _, r1) => GateFromCinG4(r1);
    case Re_capture(_, r1) => GateFromCinG4(r1);
    case Re_lookaround(_, _, r1) => GF.GateFromCin(r1);
    case _ =>
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
