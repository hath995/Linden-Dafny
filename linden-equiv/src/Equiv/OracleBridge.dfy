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

  /** `MatchesIterBounds` for nonempty chains. */
  lemma MatchesIterNEBounds(r: R.regex, k: nat, str: string, i: int, j: int)
    requires MatchesIterNE(r, k, str, i, j)
    ensures i <= j
    decreases CP.rsize(r), 2, k
  {
    if k > 0 {
      var m: int :| i < m && Matches(r, str, i, m) && MatchesIterNE(r, k - 1, str, m, j);
      MatchesIterNEBounds(r, k - 1, str, m, j);
    }
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
  // MatchesToPath: a span match yields a path through the compiled block
  // ===========================================================================

  /** `MatchesIterHead` for nonempty chains. */
  lemma MatchesIterNEHead(r: R.regex, k: nat, str: string, i: int, j: int) returns (m: int)
    requires k > 0
    requires MatchesIterNE(r, k, str, i, j)
    ensures i < m && Matches(r, str, i, m) && MatchesIterNE(r, k - 1, str, m, j)
  {
    m :| i < m && Matches(r, str, i, m) && MatchesIterNE(r, k - 1, str, m, j);
  }

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

  /** Both arms of a fork are epsilon successors, whichever the order. */
  lemma ForkEdges(code: RB.code, str: string, cp: int, pc: nat, eb: bool, a: nat, b: nat)
    requires ForkAt(code, pc, a, b)
    ensures ORc.EpsEdge(code, str, cp, pc, eb, a, eb)
    ensures ORc.EpsEdge(code, str, cp, pc, eb, b, eb)
  {
    if NR.GetPcRE(code, pc) == Some(RB.Fork(a as int, b as int)) {
      GetPcInstr(code, pc, RB.Fork(a as int, b as int));
    } else {
      GetPcInstr(code, pc, RB.Fork(b as int, a as int));
    }
  }

  /** The star loop: `k` NONEMPTY spans of `r1` walk the loop `k` times from
      its head, then the fork's exit arm leaves at `endl`. */
  lemma StarLoopPath(qid: R.quantid, r1: R.regex, code: RB.code, start: nat, es1: nat, endl: nat,
                     str: string, k: nat, i: int, j: int, eb: bool)
    requires NR.PlusFragmentRE(r1) && NR.LookFreeRE(r1)
    requires ForkAt(code, start, start + 1, endl)
    requires NR.GetPcRE(code, start + 1) == Some(RB.SetQuantToClock(qid, false))
    requires NR.GetPcRE(code, start + 2) == Some(RB.BeginLoop)
    requires NR.NfaRepRE(r1, code, start + 3, es1)
    requires NR.GetPcRE(code, es1) == Some(RB.EndLoop)
    requires NR.GetPcRE(code, es1 + 1) == Some(RB.Jmp(start as int))
    requires MatchesIterNE(r1, k, str, i, j)
    requires ORc.ReachF(code, str, 0, start, eb, i)
    ensures ORc.ReachF(code, str, 0, endl, if j > i then true else eb, j)
    decreases CP.rsize(r1), 1, k
  {
    if k == 0 {
      ForkEdges(code, str, i, start, eb, start + 1, endl);
      ReachFEpsIntro(code, str, 0, start, eb, endl, eb, i);
      return;
    }
    var m := MatchesIterNEHead(r1, k, str, i, j);
    MatchesIterNEBounds(r1, k - 1, str, m, j);
    // into the loop: fork arm, stamp, open
    ForkEdges(code, str, i, start, eb, start + 1, endl);
    ReachFEpsIntro(code, str, 0, start, eb, start + 1, eb, i);
    GetPcInstr(code, start + 1, RB.SetQuantToClock(qid, false));
    ReachFEpsIntro(code, str, 0, start + 1, eb, start + 2, eb, i);
    GetPcInstr(code, start + 2, RB.BeginLoop);
    ReachFEpsIntro(code, str, 0, start + 2, eb, start + 3, false, i);
    // the body consumes i -> m
    MatchesToPath(r1, code, start + 3, es1, str, i, m, false);
    assert ORc.ReachF(code, str, 0, es1, true, m);
    // close the loop and jump back
    GetPcInstr(code, es1, RB.EndLoop);
    ReachFEpsIntro(code, str, 0, es1, true, es1 + 1, true, m);
    GetPcInstr(code, es1 + 1, RB.Jmp(start as int));
    ReachFEpsIntro(code, str, 0, es1 + 1, true, start, true, m);
    StarLoopPath(qid, r1, code, start, es1, endl, str, k - 1, m, j, true);
  }

  /** The forced-copy chain: `n` spans of `r1` (empty allowed — forced copies
      carry no loop guard) walk `n` stamped body blocks. */
  lemma MinChainPath(n: nat, qid: R.quantid, r1: R.regex, code: RB.code, start: nat, endl: nat,
                     str: string, i: int, j: int, eb: bool)
    requires NR.PlusFragmentRE(r1) && NR.LookFreeRE(r1)
    requires NR.NfaRepMinRE(n, qid, r1, code, start, endl)
    requires MatchesIter(r1, n, str, i, j)
    requires ORc.ReachF(code, str, 0, start, eb, i)
    ensures ORc.ReachF(code, str, 0, endl, if j > i then true else eb, j)
    decreases CP.rsize(r1), 1, n
  {
    if n == 0 { return; }
    var e1: nat :| NR.GetPcRE(code, start) == Some(RB.SetQuantToClock(qid, false))
      && NR.NfaRepRE(r1, code, start + 1, e1)
      && NR.NfaRepMinRE(n - 1, qid, r1, code, e1, endl);
    var m := MatchesIterHead(r1, n, str, i, j);
    MatchesBounds(r1, str, i, m);
    MatchesIterBounds(r1, n - 1, str, m, j);
    GetPcInstr(code, start, RB.SetQuantToClock(qid, false));
    ReachFEpsIntro(code, str, 0, start, eb, start + 1, eb, i);
    MatchesToPath(r1, code, start + 1, e1, str, i, m, eb);
    MinChainPath(n - 1, qid, r1, code, e1, endl, str, m, j, if m > i then true else eb);
  }

  /** The optional layers: `k2 <= layers` NONEMPTY spans take `k2` guarded
      layers; the remaining layers are skipped in ONE step (every layer's
      fork exits directly to the chain's common end). */
  lemma OptChainPath(layers: nat, k2: nat, greedy: bool, qid: R.quantid, r1: R.regex,
                     code: RB.code, start: nat, endl: nat, str: string, i: int, j: int, eb: bool)
    requires NR.PlusFragmentRE(r1) && NR.LookFreeRE(r1)
    requires NR.NfaRepOptRE(layers, greedy, qid, r1, code, start, endl)
    requires MatchesIterNE(r1, k2, str, i, j)
    requires k2 <= layers
    requires ORc.ReachF(code, str, 0, start, eb, i)
    ensures ORc.ReachF(code, str, 0, endl, if j > i then true else eb, j)
    decreases CP.rsize(r1), 1, layers
  {
    if layers == 0 { return; }
    var e1: nat :| NR.GetPcRE(code, start) == Some(if greedy then RB.Fork(start + 1, endl as int) else RB.Fork(endl as int, start + 1))
      && NR.GetPcRE(code, start + 1) == Some(RB.SetQuantToClock(qid, false))
      && NR.GetPcRE(code, start + 2) == Some(RB.BeginLoop)
      && NR.NfaRepRE(r1, code, start + 3, e1)
      && NR.GetPcRE(code, e1) == Some(RB.EndLoop)
      && NR.NfaRepOptRE(layers - 1, greedy, qid, r1, code, e1 + 1, endl);
    assert ForkAt(code, start, start + 1, endl);
    if k2 == 0 {
      // skip everything: this layer's fork exits straight to the common end
      ForkEdges(code, str, i, start, eb, start + 1, endl);
      ReachFEpsIntro(code, str, 0, start, eb, endl, eb, i);
      return;
    }
    var m := MatchesIterNEHead(r1, k2, str, i, j);
    MatchesIterNEBounds(r1, k2 - 1, str, m, j);
    ForkEdges(code, str, i, start, eb, start + 1, endl);
    ReachFEpsIntro(code, str, 0, start, eb, start + 1, eb, i);
    GetPcInstr(code, start + 1, RB.SetQuantToClock(qid, false));
    ReachFEpsIntro(code, str, 0, start + 1, eb, start + 2, eb, i);
    GetPcInstr(code, start + 2, RB.BeginLoop);
    ReachFEpsIntro(code, str, 0, start + 2, eb, start + 3, false, i);
    MatchesToPath(r1, code, start + 3, e1, str, i, m, false);
    assert ORc.ReachF(code, str, 0, e1, true, m);
    GetPcInstr(code, e1, RB.EndLoop);
    ReachFEpsIntro(code, str, 0, e1, true, e1 + 1, true, m);
    OptChainPath(layers - 1, k2 - 1, greedy, qid, r1, code, e1 + 1, endl, str, m, j, true);
  }

  /** The do-while loop: `krem >= 1` spans of the NonNullable body — the last
      repetition falls through the backward fork's exit arm. */
  lemma DoWhilePath(krem: nat, qid: R.quantid, r1: R.regex, code: RB.code, em: nat, e1: nat,
                    endl: nat, str: string, i: int, j: int, eb: bool)
    requires NR.PlusFragmentRE(r1) && NR.LookFreeRE(r1)
    requires R.nullable(r1) == R.NonNullable
    requires NR.GetPcRE(code, em) == Some(RB.SetQuantToClock(qid, false))
    requires NR.NfaRepRE(r1, code, em + 1, e1)
    requires ForkAt(code, e1, em, endl)
    requires endl == e1 + 1
    requires krem >= 1
    requires MatchesIter(r1, krem, str, i, j)
    requires ORc.ReachF(code, str, 0, em, eb, i)
    ensures ORc.ReachF(code, str, 0, endl, true, j)
    decreases CP.rsize(r1), 1, krem
  {
    var m := MatchesIterHead(r1, krem, str, i, j);
    // NonNullable bodies never match empty, so this span consumes
    NonNullableNoEmptyMatch(r1, str, i);
    MatchesBounds(r1, str, i, m);
    assert i < m;
    GetPcInstr(code, em, RB.SetQuantToClock(qid, false));
    ReachFEpsIntro(code, str, 0, em, eb, em + 1, eb, i);
    MatchesToPath(r1, code, em + 1, e1, str, i, m, eb);
    assert ORc.ReachF(code, str, 0, e1, true, m);
    ForkEdges(code, str, m, e1, true, em, endl);
    if krem == 1 {
      ReachFEpsIntro(code, str, 0, e1, true, endl, true, m);
      assert m == j;
    } else {
      ReachFEpsIntro(code, str, 0, e1, true, em, true, m);
      DoWhilePath(krem - 1, qid, r1, code, em, e1, endl, str, m, j, true);
    }
  }

  /** THE forward bridge direction: a span match of a look-free plus-fragment
      regex yields a path through its compiled block — from any reachable
      entry configuration to the block's end, with the exit flag re-armed iff
      the span consumed. */
  lemma MatchesToPath(re: R.regex, code: RB.code, start: nat, endl: nat,
                      str: string, i: int, j: int, eb: bool)
    requires NR.PlusFragmentRE(re) && NR.LookFreeRE(re)
    requires NR.NfaRepRE(re, code, start, endl)
    requires Matches(re, str, i, j)
    requires ORc.ReachF(code, str, 0, start, eb, i)
    ensures ORc.ReachF(code, str, 0, endl, if j > i then true else eb, j)
    decreases CP.rsize(re), 0, 0
  {
    match re
    case Re_empty =>
    case Re_character(ch) =>
      GetPcInstr(code, start, RB.Consume(T.ExpectationOf(ch)));
      assert ORc.ConsumeEdge(code, str, i, start);
      ReachFConsumeIntro(code, str, 0, start, eb, i);
    case Re_anchor(a) =>
      GetPcInstr(code, start, RB.AnchorAssertion(a));
      assert ORc.EpsEdge(code, str, i, start, eb, start + 1, eb);
      ReachFEpsIntro(code, str, 0, start, eb, start + 1, eb, i);
    case Re_alt(r1, r2) =>
      var e1: nat :| NR.GetPcRE(code, start) == Some(RB.Fork(start + 1, e1 + 1))
        && NR.NfaRepRE(r1, code, start + 1, e1)
        && NR.GetPcRE(code, e1) == Some(RB.Jmp(endl as int))
        && NR.NfaRepRE(r2, code, e1 + 1, endl);
      assert Matches(R.Re_alt(r1, r2), str, i, j);
      GetPcInstr(code, start, RB.Fork(start + 1, e1 + 1));
      if Matches(r1, str, i, j) {
        ReachFEpsIntro(code, str, 0, start, eb, start + 1, eb, i);
        MatchesToPath(r1, code, start + 1, e1, str, i, j, eb);
        GetPcInstr(code, e1, RB.Jmp(endl as int));
        ReachFEpsIntro(code, str, 0, e1, if j > i then true else eb, endl, if j > i then true else eb, j);
      } else {
        ReachFEpsIntro(code, str, 0, start, eb, e1 + 1, eb, i);
        MatchesToPath(r2, code, e1 + 1, endl, str, i, j, eb);
      }
    case Re_con(r1, r2) =>
      var e1: nat :| NR.NfaRepRE(r1, code, start, e1) && NR.NfaRepRE(r2, code, e1, endl);
      assert Matches(R.Re_con(r1, r2), str, i, j);
      assert exists m: int :: Matches(r1, str, i, m) && Matches(r2, str, m, j);
      var m: int :| Matches(r1, str, i, m) && Matches(r2, str, m, j);
      MatchesBounds(r1, str, i, m);
      MatchesBounds(r2, str, m, j);
      MatchesToPath(r1, code, start, e1, str, i, m, eb);
      MatchesToPath(r2, code, e1, endl, str, m, j, if m > i then true else eb);
    case Re_capture(cid, r1) =>
      var e1: nat :| NR.GetPcRE(code, start) == Some(RB.SetRegisterToCP(CP.start_reg(cid)))
        && NR.NfaRepRE(r1, code, start + 1, e1)
        && NR.GetPcRE(code, e1) == Some(RB.SetRegisterToCP(CP.end_reg(cid)))
        && endl == e1 + 1;
      GetPcInstr(code, start, RB.SetRegisterToCP(CP.start_reg(cid)));
      ReachFEpsIntro(code, str, 0, start, eb, start + 1, eb, i);
      MatchesToPath(r1, code, start + 1, e1, str, i, j, eb);
      GetPcInstr(code, e1, RB.SetRegisterToCP(CP.end_reg(cid)));
      ReachFEpsIntro(code, str, 0, e1, if j > i then true else eb, endl, if j > i then true else eb, j);
    case Re_quant(nul, qid, q, r1) =>
      assert Matches(R.Re_quant(nul, qid, q, r1), str, i, j);
      assert exists k: nat :: q.min <= k && (q.max.Some? ==> k <= q.max.value)
                           && MatchesIter(r1, k, str, i, j);
      var k: nat :| q.min <= k && (q.max.Some? ==> k <= q.max.value)
                 && MatchesIter(r1, k, str, i, j);
      if q.min == 0 && q.max == None {
        // the star scheme
        var es1: nat :|
          NR.GetPcRE(code, start) == Some(if q.greedy then RB.Fork(start + 1, es1 + 2) else RB.Fork(es1 + 2, start + 1))
          && NR.GetPcRE(code, start + 1) == Some(RB.SetQuantToClock(qid, false))
          && NR.GetPcRE(code, start + 2) == Some(RB.BeginLoop)
          && NR.NfaRepRE(r1, code, start + 3, es1)
          && NR.GetPcRE(code, es1) == Some(RB.EndLoop)
          && NR.GetPcRE(code, es1 + 1) == Some(RB.Jmp(start as int))
          && endl == es1 + 2;
        assert ForkAt(code, start, start + 1, endl);
        var k2 := IterDropEmpty(r1, k, str, i, j);
        StarLoopPath(qid, r1, code, start, es1, endl, str, k2, i, j, eb);
      } else if q.max.Some? {
        // bounded: min forced copies, then optional layers
        var em := NR.NfaRepREQuantInv(nul, qid, q, r1, code, start, endl);
        var mn := q.min as nat;
        var kx := (q.max.value - q.min) as nat;
        var mid := IterSplit(r1, k, mn, str, i, j);
        MinChainPath(mn, qid, r1, code, start, em, str, i, mid, eb);
        var k2 := IterDropEmpty(r1, k - mn, str, mid, j);
        MatchesIterBounds(r1, mn, str, i, mid);
        MatchesIterBounds(r1, k - mn, str, mid, j);
        OptChainPath(kx, k2, q.greedy, qid, r1, code, em, endl, str, mid, j,
                     if mid > i then true else eb);
      } else {
        // the do-while scheme: min-1 forced copies, then >= 1 looped spans
        var em, e1 := NR.NfaRepREPlusInv(nul, qid, q, r1, code, start, endl);
        var mn1 := (q.min - 1) as nat;
        var mid := IterSplit(r1, k, mn1, str, i, j);
        MinChainPath(mn1, qid, r1, code, start, em, str, i, mid, eb);
        MatchesIterBounds(r1, mn1, str, i, mid);
        assert ForkAt(code, e1, em, endl);
        DoWhilePath(k - mn1, qid, r1, code, em, e1, endl, str, mid, j,
                    if mid > i then true else eb);
        // DoWhilePath lands with the flag true; the target needs
        // `if j > i then true else eb` — its spans are nonempty, so j > mid >= i
        assert j > mid by {
          var mm := MatchesIterHead(r1, k - mn1, str, mid, j);
          NonNullableNoEmptyMatch(r1, str, mid);
          MatchesBounds(r1, str, mid, mm);
          MatchesIterBounds(r1, k - mn1 - 1, str, mm, j);
        }
      }
    case Re_lookaround(_, _, _) =>
      // excluded by LookFreeRE
  }

  /** THE forward bridge, assembled: a body match ending at `cp` makes the
      build program's `WriteOracle(lid)` reachable at `cp`. */
  lemma MatchesToReachesWrite(body: R.regex, lid: R.lookid, str: string, i: int, cp: int)
    requires NR.PlusFragmentRE(body) && NR.LookFreeRE(body)
    requires 0 <= i <= |str|
    requires Matches(body, str, i, cp)
    requires cp <= |str|
    ensures ORc.ReachesWrite(CP.compile_to_write(R.lazy_prefix(body), lid), str, 0, lid, cp)
  {
    assert NR.PlusFragmentRE(R.lazy_prefix(body));
    LookFreeLazyPrefixB(body);
    NR.PlusIsLookBehindFragmentRE(R.lazy_prefix(body));
    NR.CompileToWriteRep(R.lazy_prefix(body), lid);
    var code := CP.compile_to_write(R.lazy_prefix(body), lid);
    var next := CP.compile(R.lazy_prefix(body), 0, CP.Progress).1;
    var bentry := LazyPrefixBodyEntry(body, code, next as nat, str, i);
    var eb: bool :| ORc.ReachF(code, str, 0, bentry, eb, i);
    MatchesToPath(body, code, bentry, next as nat, str, i, cp, eb);
    GetPcInstr(code, next as nat, RB.WriteOracle(lid));
    assert ORc.ReachF(code, str, 0, next as nat, if cp > i then true else eb, cp);
  }

  /** Local copy of the look-freedom of `lazy_prefix` (also in OracleBuild;
      restated here to keep this file's helper self-contained). */
  lemma LookFreeLazyPrefixB(body: R.regex)
    requires NR.LookFreeRE(body)
    ensures NR.LookFreeRE(R.lazy_prefix(body))
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
