// Lookaround campaign (L1), oracle theorem part C4 (§6.3 of
// LOOKAROUND_CAMPAIGN.md): the bridge between the configuration graph and
// span matches — groundwork.
//
// Target, for look-free plus-fragment bodies:
//
//   ReachesWrite(compile_to_write(lazy_prefix(body), lid), str, 0, lid, cp)
//     <==>  exists i :: 0 <= i <= cp && Matches(body, str, i, cp)
//
// This file provides:
//   - Matches/MatchesIter — the existence-level "re matches the span
//     [i, j) of str, scanning forward" predicate over the RegElk AST.
//     Quantifier iterations MAY match empty (language-faithful: `(ε){2,3}`
//     matches ε); the engine's BeginLoop/EndLoop guard only ever forbids
//     empty LOOP iterations, and dropping/keeping empty iterations does not
//     change the language, which is what the two bridge directions exploit.
//   - ReachF constructor lemmas (eps/consume step packaging).
//   - LazyPrefixBodyEntry — the dot-star walker: the build program's
//     lazy prefix (`.*?`) reaches the body's entry label at EVERY position
//     0..|str| (ExpectationOf(Dot) == All accepts every character), which is
//     the "start anywhere" half of both directions.
//
// Still open (next): MatchesToPath (match ==> a ReachF path through the
// body's NfaRepRE block — structural induction with Min/Opt companions) and
// PathToMatches (ReachF at the write-pc ==> a match — path decomposition
// over the block structure; within one position the reachable graph cannot
// cycle without consuming, thanks to the BeginLoop/EndLoop flag discipline).
include "OracleBuild.dfy"

/** §6.3 groundwork: the span-match predicate `Matches`, `ReachF` step
    packaging, and the lazy-prefix "start anywhere" walker. */
module LindenElkOracleBridge {
  import opened Std.Wrappers
  import R = RegElkRegex
  import RB = Bytecode
  import CP = Compiler
  import AI = ArrayInterp
  import LOr = Oracle
  import LAnc = Anchors
  import RC = Charclasses
  import T = LindenElkTranslate
  import NR = LindenElkNfaRep
  import ORc = LindenElkOracleReach

  // ===========================================================================
  // The span-match predicate
  // ===========================================================================

  /** `re` matches exactly the span `[i, j)` of `str`, scanning forward —
      the existence-level, engine-free statement of a body match. Characters
      are tested through the SAME expectation the compiler emits
      (`ExpectationOf`), so no separate character-agreement lemma is needed
      on the engine side of the bridge. Lookarounds have no rule (bridge
      scope is look-free code). */
  ghost predicate Matches(re: R.regex, str: string, i: int, j: int)
    decreases CP.rsize(re), 0, 0
  {
    match re
    case Re_empty => i == j
    case Re_character(ch) =>
      j == i + 1 && RC.is_accepted(AI.get_char(str, i), T.ExpectationOf(ch))
    case Re_anchor(a) =>
      i == j && LAnc.is_satisfied(a, ORc.CtxAt(str, i), LAnc.Forward)
    case Re_alt(r1, r2) => Matches(r1, str, i, j) || Matches(r2, str, i, j)
    case Re_con(r1, r2) =>
      exists m: int :: Matches(r1, str, i, m) && Matches(r2, str, m, j)
    case Re_quant(nul, qid, q, r1) =>
      exists k: nat ::
        q.min <= k && (q.max.Some? ==> k <= q.max.value)
        && MatchesIter(r1, k, str, i, j)
    case Re_capture(cid, r1) => Matches(r1, str, i, j)
    case Re_lookaround(_, _, _) => false
  }

  /** `k` consecutive `r`-spans: the iteration counter for quantifiers. */
  ghost predicate MatchesIter(r: R.regex, k: nat, str: string, i: int, j: int)
    decreases CP.rsize(r), 1, k
  {
    if k == 0 then i == j
    else exists m: int :: Matches(r, str, i, m) && MatchesIter(r, k - 1, str, m, j)
  }

  // ===========================================================================
  // Span algebra: bounds, splitting, dropping empty iterations, nullability
  // ===========================================================================

  /** Spans never go backward. */
  lemma MatchesBounds(re: R.regex, str: string, i: int, j: int)
    requires Matches(re, str, i, j)
    ensures i <= j
    decreases CP.rsize(re), 0, 0
  {
    match re
    case Re_alt(r1, r2) =>
      if Matches(r1, str, i, j) { MatchesBounds(r1, str, i, j); }
      else { MatchesBounds(r2, str, i, j); }
    case Re_con(r1, r2) =>
      var m: int :| Matches(r1, str, i, m) && Matches(r2, str, m, j);
      MatchesBounds(r1, str, i, m);
      MatchesBounds(r2, str, m, j);
    case Re_quant(nul, qid, q, r1) =>
      var k: nat :| q.min <= k && (q.max.Some? ==> k <= q.max.value)
                 && MatchesIter(r1, k, str, i, j);
      MatchesIterBounds(r1, k, str, i, j);
    case Re_capture(_, r1) => MatchesBounds(r1, str, i, j);
    case _ =>
  }

  /** `MatchesBounds` for iteration chains. */
  lemma MatchesIterBounds(r: R.regex, k: nat, str: string, i: int, j: int)
    requires MatchesIter(r, k, str, i, j)
    ensures i <= j
    decreases CP.rsize(r), 1, k
  {
    if k > 0 {
      var m: int :| Matches(r, str, i, m) && MatchesIter(r, k - 1, str, m, j);
      MatchesBounds(r, str, i, m);
      MatchesIterBounds(r, k - 1, str, m, j);
    }
  }

  /** Head inversion for a nonempty iteration chain (a top-level helper —
      the definitional unfold is fuel-fragile in nested proof contexts). */
  lemma MatchesIterHead(r: R.regex, k: nat, str: string, i: int, j: int) returns (m: int)
    requires k > 0
    requires MatchesIter(r, k, str, i, j)
    ensures Matches(r, str, i, m) && MatchesIter(r, k - 1, str, m, j)
  {
    m :| Matches(r, str, i, m) && MatchesIter(r, k - 1, str, m, j);
  }

  /** Split an iteration chain after its first `n` spans. */
  lemma IterSplit(r: R.regex, k: nat, n: nat, str: string, i: int, j: int) returns (mid: int)
    requires MatchesIter(r, k, str, i, j)
    requires n <= k
    ensures MatchesIter(r, n, str, i, mid) && MatchesIter(r, k - n, str, mid, j)
    decreases n
  {
    if n == 0 { mid := i; return; }
    var m: int :| Matches(r, str, i, m) && MatchesIter(r, k - 1, str, m, j);
    mid := IterSplit(r, k - 1, n - 1, str, m, j);
  }

  /** Iteration chains whose every span CONSUMES — what the engine's
      `BeginLoop`/`EndLoop` guard admits through a loop. */
  ghost predicate MatchesIterNE(r: R.regex, k: nat, str: string, i: int, j: int)
    decreases CP.rsize(r), 2, k
  {
    if k == 0 then i == j
    else exists m: int :: i < m && Matches(r, str, i, m) && MatchesIterNE(r, k - 1, str, m, j)
  }

  /** Empty iterations are droppable: any chain thins to a nonempty chain of
      no greater length over the same span. */
  lemma IterDropEmpty(r: R.regex, k: nat, str: string, i: int, j: int) returns (k2: nat)
    requires MatchesIter(r, k, str, i, j)
    ensures k2 <= k && MatchesIterNE(r, k2, str, i, j)
    decreases k
  {
    if k == 0 { k2 := 0; return; }
    var m: int :| Matches(r, str, i, m) && MatchesIter(r, k - 1, str, m, j);
    if m == i {
      k2 := IterDropEmpty(r, k - 1, str, m, j);
    } else {
      MatchesBounds(r, str, i, m);
      var kk := IterDropEmpty(r, k - 1, str, m, j);
      k2 := kk + 1;
    }
  }

  /** A syntactically `NonNullable` regex never matches the empty span — the
      fact that keeps the do-while scheme's loop iterations consuming. The
      fragment hypothesis rules out malformed negative-`min` quantifiers,
      for which the claim would be false (`k == 0` slips under `min <= k`). */
  lemma NonNullableNoEmptyMatch(re: R.regex, str: string, i: int)
    requires NR.PlusFragmentRE(re)
    requires R.nullable(re) == R.NonNullable
    ensures !Matches(re, str, i, i)
    decreases CP.rsize(re), 0, 0
  {
    match re
    case Re_alt(r1, r2) =>
      NonNullableNoEmptyMatch(r1, str, i);
      NonNullableNoEmptyMatch(r2, str, i);
    case Re_con(r1, r2) =>
      if Matches(re, str, i, i) {
        assert Matches(R.Re_con(r1, r2), str, i, i);
        assert exists m: int :: Matches(r1, str, i, m) && Matches(r2, str, m, i);
        var m: int :| Matches(r1, str, i, m) && Matches(r2, str, m, i);
        MatchesBounds(r1, str, i, m);
        MatchesBounds(r2, str, m, i);
        assert m == i;
        if R.nullable(r1) == R.NonNullable { NonNullableNoEmptyMatch(r1, str, i); }
        else { NonNullableNoEmptyMatch(r2, str, i); }
      }
    case Re_quant(nul, qid, q, r1) =>
      // NonNullable rules out min == 0; the fragment's shapes then force
      // min > 0, so every admissible k is positive
      assert q.min > 0;
      if Matches(re, str, i, i) {
        assert Matches(R.Re_quant(nul, qid, q, r1), str, i, i);
        assert exists k: nat :: q.min <= k && (q.max.Some? ==> k <= q.max.value)
                             && MatchesIter(r1, k, str, i, i);
        var k: nat :| q.min <= k && (q.max.Some? ==> k <= q.max.value)
                   && MatchesIter(r1, k, str, i, i);
        assert k > 0;
        var m := MatchesIterHead(r1, k, str, i, i);
        MatchesBounds(r1, str, i, m);
        MatchesIterBounds(r1, k - 1, str, m, i);
        assert m == i;
        NonNullableNoEmptyMatch(r1, str, i);
      }
    case Re_capture(_, r1) => NonNullableNoEmptyMatch(r1, str, i);
    case _ =>
  }

  // ===========================================================================
  // ReachF step packaging
  // ===========================================================================

  /** Take one epsilon edge from a reachable configuration. */
  lemma ReachFEpsIntro(c: RB.code, str: string, cp0: int, pc: nat, eb: bool,
                       pc2: nat, eb2: bool, cp: int)
    requires ORc.ReachF(c, str, cp0, pc, eb, cp)
    requires ORc.EpsEdge(c, str, cp, pc, eb, pc2, eb2)
    ensures ORc.ReachF(c, str, cp0, pc2, eb2, cp)
  {
  }

  /** Take one consume edge from a reachable configuration: the successor is
      `(pc + 1, exit re-armed)` at the next position. */
  lemma ReachFConsumeIntro(c: RB.code, str: string, cp0: int, pc: nat, eb: bool, cp: int)
    requires ORc.ReachF(c, str, cp0, pc, eb, cp)
    requires ORc.ConsumeEdge(c, str, cp, pc)
    ensures ORc.ReachF(c, str, cp0, pc + 1, true, cp + 1)
  {
  }

  // ===========================================================================
  // The lazy-prefix walker: the body entry is reachable at every position
  // ===========================================================================

  /** The lazy `.*?` head reaches its own loop head `(pc 0)` at every
      position `0..|str|`: position 0 is the initial configuration; each
      further position takes one loop iteration — fork into the loop, stamp,
      `BeginLoop`, consume the (always-accepted, `ExpectationOf(Dot) == All`)
      character, `EndLoop`, jump back. */
  lemma LazyPrefixHeadReach(body: R.regex, code: RB.code, endl: nat, str: string, i: int)
    requires NR.NfaRepRE(R.lazy_prefix(body), code, 0, endl)
    requires 0 <= i <= |str|
    ensures ORc.ReachF(code, str, 0, 0, false, i) || ORc.ReachF(code, str, 0, 0, true, i)
    decreases i
  {
    var pre := R.Re_quant(R.NonNullable, 0, R.CountedQuant(0, None, false), R.Re_character(R.Dot));
    assert R.lazy_prefix(body) == R.Re_con(pre, body);
    var e1: nat :| NR.NfaRepRE(pre, code, 0, e1) && NR.NfaRepRE(body, code, e1, endl);
    var es1: nat :|
      NR.GetPcRE(code, 0) == Some(RB.Fork(es1 + 2, 1))
      && NR.GetPcRE(code, 1) == Some(RB.SetQuantToClock(0, false))
      && NR.GetPcRE(code, 2) == Some(RB.BeginLoop)
      && NR.NfaRepRE(R.Re_character(R.Dot), code, 3, es1)
      && NR.GetPcRE(code, es1) == Some(RB.EndLoop)
      && NR.GetPcRE(code, es1 + 1) == Some(RB.Jmp(0))
      && e1 == es1 + 2;
    assert NR.GetPcRE(code, 3) == Some(RB.Consume(T.ExpectationOf(R.Dot))) && es1 == 4;
    if i == 0 {
      assert ORc.ReachF(code, str, 0, 0, false, 0);
    } else {
      LazyPrefixHeadReach(body, code, endl, str, i - 1);
      var eb: bool :| ORc.ReachF(code, str, 0, 0, eb, i - 1);
      // fork into the loop arm, stamp, open the loop
      assert ORc.EpsEdge(code, str, i - 1, 0, eb, 1, eb);
      ReachFEpsIntro(code, str, 0, 0, eb, 1, eb, i - 1);
      assert ORc.EpsEdge(code, str, i - 1, 1, eb, 2, eb);
      ReachFEpsIntro(code, str, 0, 1, eb, 2, eb, i - 1);
      assert ORc.EpsEdge(code, str, i - 1, 2, eb, 3, false);
      ReachFEpsIntro(code, str, 0, 2, eb, 3, false, i - 1);
      // consume the character at i - 1 (Dot accepts everything in range)
      assert AI.get_char(str, i - 1).Some?;
      assert RC.is_accepted(AI.get_char(str, i - 1), T.ExpectationOf(R.Dot));
      assert ORc.ConsumeEdge(code, str, i - 1, 3);
      ReachFConsumeIntro(code, str, 0, 3, false, i - 1);
      // close the loop and jump back to the head
      assert ORc.ReachF(code, str, 0, 4, true, i);
      assert ORc.EpsEdge(code, str, i, es1, true, es1 + 1, true);
      ReachFEpsIntro(code, str, 0, es1, true, es1 + 1, true, i);
      assert ORc.EpsEdge(code, str, i, es1 + 1, true, 0, true);
      ReachFEpsIntro(code, str, 0, es1 + 1, true, 0, true, i);
    }
  }

  /** The "start anywhere" walker: in a compiled `lazy_prefix(body)` program,
      the BODY's entry label is reachable at every position `0..|str|` (take
      the head's exit fork). Returns the entry label with the body's own
      `NfaRepRE` block, ready for `MatchesToPath`. */
  lemma LazyPrefixBodyEntry(body: R.regex, code: RB.code, endl: nat, str: string, i: int)
    returns (bentry: nat)
    requires NR.NfaRepRE(R.lazy_prefix(body), code, 0, endl)
    requires 0 <= i <= |str|
    ensures NR.NfaRepRE(body, code, bentry, endl)
    ensures ORc.ReachF(code, str, 0, bentry, false, i) || ORc.ReachF(code, str, 0, bentry, true, i)
  {
    var pre := R.Re_quant(R.NonNullable, 0, R.CountedQuant(0, None, false), R.Re_character(R.Dot));
    assert R.lazy_prefix(body) == R.Re_con(pre, body);
    var e1: nat :| NR.NfaRepRE(pre, code, 0, e1) && NR.NfaRepRE(body, code, e1, endl);
    var es1: nat :|
      NR.GetPcRE(code, 0) == Some(RB.Fork(es1 + 2, 1))
      && NR.GetPcRE(code, 1) == Some(RB.SetQuantToClock(0, false))
      && NR.GetPcRE(code, 2) == Some(RB.BeginLoop)
      && NR.NfaRepRE(R.Re_character(R.Dot), code, 3, es1)
      && NR.GetPcRE(code, es1) == Some(RB.EndLoop)
      && NR.GetPcRE(code, es1 + 1) == Some(RB.Jmp(0))
      && e1 == es1 + 2;
    bentry := e1;
    LazyPrefixHeadReach(body, code, endl, str, i);
    var eb: bool :| ORc.ReachF(code, str, 0, 0, eb, i);
    // the fork's exit arm lands on the body entry
    assert ORc.EpsEdge(code, str, i, 0, eb, es1 + 2, eb);
    ReachFEpsIntro(code, str, 0, 0, eb, es1 + 2, eb, i);
  }
}
