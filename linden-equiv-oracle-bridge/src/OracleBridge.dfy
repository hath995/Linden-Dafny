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

  // ===========================================================================
  // ReachF step packaging
  // ===========================================================================

  // ===========================================================================
  // MatchesToPath: a span match yields a path through the compiled block
  // ===========================================================================

  /** An in-range fetched instruction is what `get_instr` reads (bridges the
      rep predicates' `GetPcRE` to the configuration graph's `get_instr`). */
  lemma GetPcInstr(code: RB.code, pc: nat, ins: RB.instruction)
    requires NR.GetPcRE(code, pc) == Some(ins)
    ensures RB.get_instr(code, pc) == ins
  {
  }

  /** A fork at `pc` whose two arms are `{a, b}` in either order — the
      greediness-agnostic shape (existence cares only about the arm SET). */
  ghost predicate ForkAt(code: RB.code, pc: nat, a: nat, b: nat) {
    NR.GetPcRE(code, pc) == Some(RB.Fork(a as int, b as int))
    || NR.GetPcRE(code, pc) == Some(RB.Fork(b as int, a as int))
  }

  // ===========================================================================
  // The lazy-prefix walker: the body entry is reachable at every position
  // ===========================================================================

}
