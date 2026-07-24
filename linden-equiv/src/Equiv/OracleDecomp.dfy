// Lookaround campaign (L1), oracle theorem part C4, second half (§6.3):
// PathToMatches — a reachable recorder implies a body match.
//
// Strategy (the "TreeThreadRE-lite" of the campaign doc): an EXISTENCE-level
// mid-parse invariant over the block structure, with no priorities, no group
// maps, and no exit-flag bookkeeping (the path is GIVEN; we only read off
// what it parsed):
//
//   InBlock(re, code, start, endl, str, i, pc, cp) — configuration (pc, cp)
//   is a legitimate mid-parse state of re's block, entered at string
//   position i. Each arm carries its own NfaRepRE-style instruction pins
//   (via the *Shape predicates), so consumers are self-contained.
//
//   BlockStep: every configuration-graph edge out of a mid-parse state
//   lands in a mid-parse state or exits the block at `endl` with a
//   completed span match — structural induction, with InMin/InOpt
//   companions for the forced-copy and optional-layer chains.
//
//   ProgReachInv (least lemma over ReachF): in the two-block build program
//   `lazy_prefix(body)` + WriteOracle, every reachable configuration is in
//   the dot-star zone (pcs 0..5), a body mid-parse state, or the recorder
//   with a completed match. ReachesWriteToMatches reads the goal off the
//   recorder disjunct, with NoOracleInstrRE pinning the recorder's pc.
//
// Soundness needs no exit-flag reasoning and no fragment hypotheses beyond
// look-freedom: an edge the engine could not take is simply absent, and
// absent edges cannot break an invariant.
//
// Encoding notes: no let-expressions inside the predicates (they tickled a
// Boogie translation fault under quantifiers), and every existential is
// single-purpose with a natural trigger — the instruction pins live in the
// *Shape predicates, and iteration counts hide behind `IterFrom`.
include "OracleBridge.dfy"

/** §6.3, the decomposition direction: the mid-parse invariant `InBlock`,
    its step/entry/empty lemmas, and `ReachesWriteToMatches`. */
module LindenElkOracleDecomp {
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
  import OB = LindenElkOracleBridge

  // ===========================================================================
  // Span-chain helpers
  // ===========================================================================

  /** Prepend a span to a chain (the definitional constructor, packaged). */
  lemma IterCons(r: R.regex, k: nat, str: string, i: int, m: int, j: int)
    requires OB.Matches(r, str, i, m)
    requires OB.MatchesIter(r, k, str, m, j)
    ensures OB.MatchesIter(r, k + 1, str, i, j)
  {
  }

  /** Append a span to a chain. */
  lemma IterSnoc(r: R.regex, k: nat, str: string, i: int, m: int, j: int)
    requires OB.MatchesIter(r, k, str, i, m)
    requires OB.Matches(r, str, m, j)
    ensures OB.MatchesIter(r, k + 1, str, i, j)
    decreases k
  {
    if k == 0 { return; }
    var m1 := OB.MatchesIterHead(r, k, str, i, m);
    IterSnoc(r, k - 1, str, m1, m, j);
    IterCons(r, k, str, i, m1, j);
  }

  /** At least `n` spans lie between `i` and `m` — the count abstraction the
      loop-revisiting invariant arms store (single-binder, clean trigger). */
  ghost predicate IterFrom(r: R.regex, n: nat, str: string, i: int, m: int) {
    exists k: nat {:trigger OB.MatchesIter(r, k, str, i, m)} ::
      n <= k && OB.MatchesIter(r, k, str, i, m)
  }

  lemma IterFromZero(r: R.regex, str: string, i: int)
    ensures IterFrom(r, 0, str, i, i)
  {
    assert OB.MatchesIter(r, 0, str, i, i);
  }

  lemma IterFromInv(r: R.regex, n: nat, str: string, i: int, m: int) returns (k: nat)
    requires IterFrom(r, n, str, i, m)
    ensures n <= k && OB.MatchesIter(r, k, str, i, m)
  {
    k :| n <= k && OB.MatchesIter(r, k, str, i, m);
  }

  /** Append one span to an at-least-`n` chain. */
  lemma IterFromSnoc(r: R.regex, n: nat, str: string, i: int, m: int, j: int)
    requires IterFrom(r, n, str, i, m)
    requires OB.Matches(r, str, m, j)
    ensures IterFrom(r, n, str, i, j)
  {
    var k := IterFromInv(r, n, str, i, m);
    IterSnoc(r, k, str, i, m, j);
    assert OB.MatchesIter(r, k + 1, str, i, j);
  }

  // ===========================================================================
  // Block shapes (the instruction pins, packaged for triggers and reuse)
  // ===========================================================================

  /** The alternation block's layout. */
  ghost predicate AltShape(r1: R.regex, r2: R.regex, code: RB.code, start: nat, e1: nat, endl: nat) {
    NR.GetPcRE(code, start) == Some(RB.Fork(start + 1, e1 + 1))
    && NR.NfaRepRE(r1, code, start + 1, e1)
    && NR.GetPcRE(code, e1) == Some(RB.Jmp(endl as int))
    && NR.NfaRepRE(r2, code, e1 + 1, endl)
  }

  /** The concatenation seam. */
  ghost predicate ConShape(r1: R.regex, r2: R.regex, code: RB.code, start: nat, e1: nat, endl: nat) {
    NR.NfaRepRE(r1, code, start, e1) && NR.NfaRepRE(r2, code, e1, endl)
  }

  /** The capture block's layout. */
  ghost predicate CapShape(cid: R.capture, r1: R.regex, code: RB.code, start: nat, e1: nat, endl: nat) {
    NR.GetPcRE(code, start) == Some(RB.SetRegisterToCP(CP.start_reg(cid)))
    && NR.NfaRepRE(r1, code, start + 1, e1)
    && NR.GetPcRE(code, e1) == Some(RB.SetRegisterToCP(CP.end_reg(cid)))
    && endl == e1 + 1
  }

  /** The star block's layout (greediness-agnostic fork). */
  ghost predicate StarShape(qid: R.quantid, r1: R.regex, code: RB.code, start: nat, es1: nat, endl: nat) {
    (NR.GetPcRE(code, start) == Some(RB.Fork(start + 1, (es1 + 2) as int))
     || NR.GetPcRE(code, start) == Some(RB.Fork((es1 + 2) as int, start + 1)))
    && NR.GetPcRE(code, start + 1) == Some(RB.SetQuantToClock(qid, false))
    && NR.GetPcRE(code, start + 2) == Some(RB.BeginLoop)
    && NR.NfaRepRE(r1, code, start + 3, es1)
    && NR.GetPcRE(code, es1) == Some(RB.EndLoop)
    && NR.GetPcRE(code, es1 + 1) == Some(RB.Jmp(start as int))
    && endl == es1 + 2
  }

  /** One forced copy's layout plus the rest of its chain. */
  ghost predicate MinShape(k: nat, qid: R.quantid, r1: R.regex, code: RB.code, start: nat, e1: nat, endl: nat) {
    NR.GetPcRE(code, start) == Some(RB.SetQuantToClock(qid, false))
    && NR.NfaRepRE(r1, code, start + 1, e1)
    && (k > 0 ==> NR.NfaRepMinRE(k - 1, qid, r1, code, e1, endl))
  }

  /** One optional layer's layout plus the rest of its chain. */
  ghost predicate OptShape(layers: nat, greedy: bool, qid: R.quantid, r1: R.regex, code: RB.code, start: nat, e1: nat, endl: nat) {
    NR.GetPcRE(code, start) == Some(if greedy then RB.Fork(start + 1, endl as int) else RB.Fork(endl as int, start + 1))
    && NR.GetPcRE(code, start + 1) == Some(RB.SetQuantToClock(qid, false))
    && NR.GetPcRE(code, start + 2) == Some(RB.BeginLoop)
    && NR.NfaRepRE(r1, code, start + 3, e1)
    && NR.GetPcRE(code, e1) == Some(RB.EndLoop)
    && (layers > 0 ==> NR.NfaRepOptRE(layers - 1, greedy, qid, r1, code, e1 + 1, endl))
  }

  /** The do-while tail's layout: the stamped, guaranteed body and its
      backward fork. */
  ghost predicate DoWhileShape(qid: R.quantid, r1: R.regex, code: RB.code, em: nat, e1: nat, endl: nat) {
    NR.GetPcRE(code, em) == Some(RB.SetQuantToClock(qid, false))
    && NR.NfaRepRE(r1, code, em + 1, e1)
    && (NR.GetPcRE(code, e1) == Some(RB.Fork(em as int, (e1 + 1) as int))
        || NR.GetPcRE(code, e1) == Some(RB.Fork((e1 + 1) as int, em as int)))
    && endl == e1 + 1
  }

  // ===========================================================================
  // The mid-parse invariant
  // ===========================================================================

  /** The star arm's interior: some prefix of iterations is done (entry `i`,
      currently at `m`), and the configuration sits on the loop head, inside
      the body, or on the loop's closing pair. */
  ghost predicate StTail(qid: R.quantid, r1: R.regex, code: RB.code, start: nat, es1: nat,
                         str: string, i: int, pc: nat, cp: int)
    decreases CP.rsize(r1), 3, 0
  {
    exists m: int {:trigger IterFrom(r1, 0, str, i, m)} ::
      IterFrom(r1, 0, str, i, m)
      && (((pc == start || pc == start + 1 || pc == start + 2) && cp == m)
          || InBlock(r1, code, start + 3, es1, str, m, pc, cp)
          || ((pc == es1 || pc == es1 + 1) && OB.Matches(r1, str, m, cp)))
  }

  /** The bounded arm's post-copies interior: the `mn` forced copies span
      `[i, m)` and the configuration is inside the optional layers. */
  ghost predicate BdTail(mn: nat, kx: nat, greedy: bool, qid: R.quantid, r1: R.regex, code: RB.code,
                         em: nat, endl: nat, str: string, i: int, pc: nat, cp: int)
    decreases CP.rsize(r1), 3, 0
  {
    exists m: int {:trigger InOpt(kx, greedy, qid, r1, code, em, endl, str, m, pc, cp)} ::
      OB.MatchesIter(r1, mn, str, i, m)
      && InOpt(kx, greedy, qid, r1, code, em, endl, str, m, pc, cp)
  }

  /** The do-while arm's looped interior: at least `mn1` spans are done
      (entry `i`, currently at `m`), and the configuration sits on the stamp,
      inside the guaranteed body, or on the backward fork. */
  ghost predicate DwTail(mn1: nat, qid: R.quantid, r1: R.regex, code: RB.code, em: nat, e1: nat,
                         str: string, i: int, pc: nat, cp: int)
    decreases CP.rsize(r1), 3, 0
  {
    exists m: int {:trigger IterFrom(r1, mn1, str, i, m)} ::
      IterFrom(r1, mn1, str, i, m)
      && ((pc == em && cp == m)
          || InBlock(r1, code, em + 1, e1, str, m, pc, cp)
          || (pc == e1 && OB.Matches(r1, str, m, cp)))
  }

  /** Configuration `(pc, cp)` is a legitimate mid-parse state of `re`'s
      block, entered at string position `i`. Every arm carries its own
      instruction pins; the exit flag is deliberately absent (soundness only
      reads the path, it never justifies it). */
  ghost predicate InBlock(re: R.regex, code: RB.code, start: nat, endl: nat,
                          str: string, i: int, pc: nat, cp: int)
    decreases CP.rsize(re), 0, 0
  {
    match re
    case Re_empty => false
    case Re_lookaround(_, _, _) => false
    case Re_character(ch) =>
      pc == start && cp == i && endl == start + 1
      && NR.GetPcRE(code, start) == Some(RB.Consume(T.ExpectationOf(ch)))
    case Re_anchor(a) =>
      pc == start && cp == i && endl == start + 1
      && NR.GetPcRE(code, start) == Some(RB.AnchorAssertion(a))
    case Re_alt(r1, r2) =>
      exists e1: nat {:trigger AltShape(r1, r2, code, start, e1, endl)} ::
        AltShape(r1, r2, code, start, e1, endl)
        && ((pc == start && cp == i)
            || InBlock(r1, code, start + 1, e1, str, i, pc, cp)
            || (pc == e1 && OB.Matches(r1, str, i, cp))
            || InBlock(r2, code, e1 + 1, endl, str, i, pc, cp))
    case Re_con(r1, r2) =>
      exists e1: nat {:trigger ConShape(r1, r2, code, start, e1, endl)} ::
        ConShape(r1, r2, code, start, e1, endl)
        && (InBlock(r1, code, start, e1, str, i, pc, cp)
            || exists m: int {:trigger InBlock(r2, code, e1, endl, str, m, pc, cp)} ::
                 OB.Matches(r1, str, i, m) && InBlock(r2, code, e1, endl, str, m, pc, cp))
    case Re_capture(cid, r1) =>
      exists e1: nat {:trigger CapShape(cid, r1, code, start, e1, endl)} ::
        CapShape(cid, r1, code, start, e1, endl)
        && ((pc == start && cp == i)
            || InBlock(r1, code, start + 1, e1, str, i, pc, cp)
            || (pc == e1 && OB.Matches(r1, str, i, cp)))
    case Re_quant(nul, qid, q, r1) =>
      if q.min == 0 && q.max == None then
        exists es1: nat {:trigger StarShape(qid, r1, code, start, es1, endl)} ::
          StarShape(qid, r1, code, start, es1, endl)
          && StTail(qid, r1, code, start, es1, str, i, pc, cp)
      else if q.max.Some? then
        0 <= q.min && q.min <= q.max.value
        && exists em: nat {:trigger NR.NfaRepOptRE((q.max.value - q.min) as nat, q.greedy, qid, r1, code, em, endl)} ::
             NR.NfaRepMinRE(q.min as nat, qid, r1, code, start, em)
             && NR.NfaRepOptRE((q.max.value - q.min) as nat, q.greedy, qid, r1, code, em, endl)
             && (InMin(q.min as nat, qid, r1, code, start, em, str, i, pc, cp)
                 || BdTail(q.min as nat, (q.max.value - q.min) as nat, q.greedy, qid, r1, code, em, endl, str, i, pc, cp))
      else
        q.min > 0
        && exists em: nat, e1: nat {:trigger DoWhileShape(qid, r1, code, em, e1, endl)} ::
             NR.NfaRepMinRE((q.min - 1) as nat, qid, r1, code, start, em)
             && DoWhileShape(qid, r1, code, em, e1, endl)
             && (InMin((q.min - 1) as nat, qid, r1, code, start, em, str, i, pc, cp)
                 || DwTail((q.min - 1) as nat, qid, r1, code, em, e1, str, i, pc, cp))
  }

  // --- inversion / intro helpers for the tails (top-level, fuel-safe) ---

  lemma StTailInv(qid: R.quantid, r1: R.regex, code: RB.code, start: nat, es1: nat,
                  str: string, i: int, pc: nat, cp: int) returns (m: int)
    requires StTail(qid, r1, code, start, es1, str, i, pc, cp)
    ensures IterFrom(r1, 0, str, i, m)
    ensures ((pc == start || pc == start + 1 || pc == start + 2) && cp == m)
         || InBlock(r1, code, start + 3, es1, str, m, pc, cp)
         || ((pc == es1 || pc == es1 + 1) && OB.Matches(r1, str, m, cp))
  {
    m :| IterFrom(r1, 0, str, i, m)
      && (((pc == start || pc == start + 1 || pc == start + 2) && cp == m)
          || InBlock(r1, code, start + 3, es1, str, m, pc, cp)
          || ((pc == es1 || pc == es1 + 1) && OB.Matches(r1, str, m, cp)));
  }

  lemma StTailIntro(qid: R.quantid, r1: R.regex, code: RB.code, start: nat, es1: nat,
                    str: string, i: int, pc: nat, cp: int, m: int)
    requires IterFrom(r1, 0, str, i, m)
    requires ((pc == start || pc == start + 1 || pc == start + 2) && cp == m)
          || InBlock(r1, code, start + 3, es1, str, m, pc, cp)
          || ((pc == es1 || pc == es1 + 1) && OB.Matches(r1, str, m, cp))
    ensures StTail(qid, r1, code, start, es1, str, i, pc, cp)
  {
  }

  lemma BdTailInv(mn: nat, kx: nat, greedy: bool, qid: R.quantid, r1: R.regex, code: RB.code,
                  em: nat, endl: nat, str: string, i: int, pc: nat, cp: int) returns (m: int)
    requires BdTail(mn, kx, greedy, qid, r1, code, em, endl, str, i, pc, cp)
    ensures OB.MatchesIter(r1, mn, str, i, m)
    ensures InOpt(kx, greedy, qid, r1, code, em, endl, str, m, pc, cp)
  {
    m :| OB.MatchesIter(r1, mn, str, i, m)
      && InOpt(kx, greedy, qid, r1, code, em, endl, str, m, pc, cp);
  }

  lemma BdTailIntro(mn: nat, kx: nat, greedy: bool, qid: R.quantid, r1: R.regex, code: RB.code,
                    em: nat, endl: nat, str: string, i: int, pc: nat, cp: int, m: int)
    requires OB.MatchesIter(r1, mn, str, i, m)
    requires InOpt(kx, greedy, qid, r1, code, em, endl, str, m, pc, cp)
    ensures BdTail(mn, kx, greedy, qid, r1, code, em, endl, str, i, pc, cp)
  {
  }

  lemma DwTailInv(mn1: nat, qid: R.quantid, r1: R.regex, code: RB.code, em: nat, e1: nat,
                  str: string, i: int, pc: nat, cp: int) returns (m: int)
    requires DwTail(mn1, qid, r1, code, em, e1, str, i, pc, cp)
    ensures IterFrom(r1, mn1, str, i, m)
    ensures (pc == em && cp == m)
         || InBlock(r1, code, em + 1, e1, str, m, pc, cp)
         || (pc == e1 && OB.Matches(r1, str, m, cp))
  {
    m :| IterFrom(r1, mn1, str, i, m)
      && ((pc == em && cp == m)
          || InBlock(r1, code, em + 1, e1, str, m, pc, cp)
          || (pc == e1 && OB.Matches(r1, str, m, cp)));
  }

  lemma DwTailIntro(mn1: nat, qid: R.quantid, r1: R.regex, code: RB.code, em: nat, e1: nat,
                    str: string, i: int, pc: nat, cp: int, m: int)
    requires IterFrom(r1, mn1, str, i, m)
    requires (pc == em && cp == m)
          || InBlock(r1, code, em + 1, e1, str, m, pc, cp)
          || (pc == e1 && OB.Matches(r1, str, m, cp))
    ensures DwTail(mn1, qid, r1, code, em, e1, str, i, pc, cp)
  {
  }

  /** `InBlock` for the forced-copy chain: `k` copies remain, entered at
      string position `j`. */
  ghost predicate InMin(k: nat, qid: R.quantid, r1: R.regex, code: RB.code,
                        start: nat, endl: nat, str: string, j: int, pc: nat, cp: int)
    decreases CP.rsize(r1), 1, k
  {
    k > 0
    && exists e1: nat {:trigger MinShape(k, qid, r1, code, start, e1, endl)} ::
         MinShape(k, qid, r1, code, start, e1, endl)
         && ((pc == start && cp == j)
             || InBlock(r1, code, start + 1, e1, str, j, pc, cp)
             || exists m: int {:trigger InMin(k - 1, qid, r1, code, e1, endl, str, m, pc, cp)} ::
                  OB.Matches(r1, str, j, m) && InMin(k - 1, qid, r1, code, e1, endl, str, m, pc, cp))
  }

  /** `InBlock` for the optional-layer chain: `layers` remain, entered at
      string position `j`. */
  ghost predicate InOpt(layers: nat, greedy: bool, qid: R.quantid, r1: R.regex, code: RB.code,
                        start: nat, endl: nat, str: string, j: int, pc: nat, cp: int)
    decreases CP.rsize(r1), 2, layers
  {
    layers > 0
    && exists e1: nat {:trigger OptShape(layers, greedy, qid, r1, code, start, e1, endl)} ::
         OptShape(layers, greedy, qid, r1, code, start, e1, endl)
         && (((pc == start || pc == start + 1 || pc == start + 2) && cp == j)
             || InBlock(r1, code, start + 3, e1, str, j, pc, cp)
             || (pc == e1 && OB.Matches(r1, str, j, cp))
             || exists m: int {:trigger InOpt(layers - 1, greedy, qid, r1, code, e1 + 1, endl, str, m, pc, cp)} ::
                  OB.Matches(r1, str, j, m)
                  && InOpt(layers - 1, greedy, qid, r1, code, e1 + 1, endl, str, m, pc, cp))
  }

  // ===========================================================================
  // Empty-block and zero-chain facts
  // ===========================================================================

  /** A zero-copy chain is label-empty. */
  lemma MinZeroSame(qid: R.quantid, r1: R.regex, code: RB.code, start: nat, endl: nat)
    requires NR.NfaRepMinRE(0, qid, r1, code, start, endl)
    ensures start == endl
  {
  }

  /** A zero-layer chain is label-empty. */
  lemma OptZeroSame(greedy: bool, qid: R.quantid, r1: R.regex, code: RB.code, start: nat, endl: nat)
    requires NR.NfaRepOptRE(0, greedy, qid, r1, code, start, endl)
    ensures start == endl
  {
  }

  /** A zero-length forced-copy chain has zero copies. */
  lemma MinEmptyCount(k: nat, qid: R.quantid, r1: R.regex, code: RB.code, start: nat)
    requires NR.NfaRepMinRE(k, qid, r1, code, start, start)
    ensures k == 0
  {
    if k > 0 {
      var e1: nat :| NR.GetPcRE(code, start) == Some(RB.SetQuantToClock(qid, false))
        && NR.NfaRepRE(r1, code, start + 1, e1)
        && NR.NfaRepMinRE(k - 1, qid, r1, code, e1, start);
      NR.NfaRepIncrRE(r1, code, start + 1, e1);
      NR.NfaRepIncrMinRE(k - 1, qid, r1, code, e1, start);
    }
  }

  /** A zero-length optional-layer chain has zero layers. */
  lemma OptEmptyCount(k: nat, greedy: bool, qid: R.quantid, r1: R.regex, code: RB.code, start: nat)
    requires NR.NfaRepOptRE(k, greedy, qid, r1, code, start, start)
    ensures k == 0
  {
    if k > 0 {
      var e1: nat :| NR.GetPcRE(code, start) == Some(if greedy then RB.Fork(start + 1, start as int) else RB.Fork(start as int, start + 1))
        && NR.GetPcRE(code, start + 1) == Some(RB.SetQuantToClock(qid, false))
        && NR.GetPcRE(code, start + 2) == Some(RB.BeginLoop)
        && NR.NfaRepRE(r1, code, start + 3, e1)
        && NR.GetPcRE(code, e1) == Some(RB.EndLoop)
        && NR.NfaRepOptRE(k - 1, greedy, qid, r1, code, e1 + 1, start);
      NR.NfaRepIncrRE(r1, code, start + 3, e1);
      NR.NfaRepIncrOptRE(k - 1, greedy, qid, r1, code, e1 + 1, start);
    }
  }

  /** An empty block means an empty-capable regex: `Matches(re, p, p)` at
      every position (only `Re_empty`, concatenations of empties, and
      `{0,0}` quantifiers compile to zero instructions). */
  lemma BlockEmpty(re: R.regex, code: RB.code, start: nat, str: string, p: int)
    requires NR.NfaRepRE(re, code, start, start)
    ensures OB.Matches(re, str, p, p)
    decreases CP.rsize(re), 0, 0
  {
    match re
    case Re_empty =>
    case Re_character(_) =>
    case Re_anchor(_) =>
    case Re_lookaround(_, _, _) =>
    case Re_alt(r1, r2) =>
      var e1: nat :| NR.GetPcRE(code, start) == Some(RB.Fork(start + 1, e1 + 1))
        && NR.NfaRepRE(r1, code, start + 1, e1)
        && NR.GetPcRE(code, e1) == Some(RB.Jmp(start as int))
        && NR.NfaRepRE(r2, code, e1 + 1, start);
      NR.NfaRepIncrRE(r1, code, start + 1, e1);
      NR.NfaRepIncrRE(r2, code, e1 + 1, start);
    case Re_con(r1, r2) =>
      var e1: nat :| NR.NfaRepRE(r1, code, start, e1) && NR.NfaRepRE(r2, code, e1, start);
      NR.NfaRepIncrRE(r1, code, start, e1);
      NR.NfaRepIncrRE(r2, code, e1, start);
      assert e1 == start;
      BlockEmpty(r1, code, start, str, p);
      BlockEmpty(r2, code, start, str, p);
    case Re_capture(cid, r1) =>
      var e1: nat :| NR.GetPcRE(code, start) == Some(RB.SetRegisterToCP(CP.start_reg(cid)))
        && NR.NfaRepRE(r1, code, start + 1, e1)
        && NR.GetPcRE(code, e1) == Some(RB.SetRegisterToCP(CP.end_reg(cid)))
        && start == e1 + 1;
      NR.NfaRepIncrRE(r1, code, start + 1, e1);
    case Re_quant(nul, qid, q, r1) =>
      if q.min == 0 && q.max == None {
        var es1: nat :|
          NR.GetPcRE(code, start) == Some(if q.greedy then RB.Fork(start + 1, es1 + 2) else RB.Fork(es1 + 2, start + 1))
          && NR.GetPcRE(code, start + 1) == Some(RB.SetQuantToClock(qid, false))
          && NR.GetPcRE(code, start + 2) == Some(RB.BeginLoop)
          && NR.NfaRepRE(r1, code, start + 3, es1)
          && NR.GetPcRE(code, es1) == Some(RB.EndLoop)
          && NR.GetPcRE(code, es1 + 1) == Some(RB.Jmp(start as int))
          && start == es1 + 2;
        NR.NfaRepIncrRE(r1, code, start + 3, es1);
      } else if q.max.Some? {
        var em := NR.NfaRepREQuantInv(nul, qid, q, r1, code, start, start);
        NR.NfaRepIncrMinRE(q.min as nat, qid, r1, code, start, em);
        NR.NfaRepIncrOptRE((q.max.value - q.min) as nat, q.greedy, qid, r1, code, em, start);
        assert em == start;
        MinEmptyCount(q.min as nat, qid, r1, code, start);
        OptEmptyCount((q.max.value - q.min) as nat, q.greedy, qid, r1, code, start);
        assert q.min == 0;
        assert OB.MatchesIter(r1, 0, str, p, p);
      } else {
        var em, e1 := NR.NfaRepREPlusInv(nul, qid, q, r1, code, start, start);
        NR.NfaRepIncrMinRE((q.min - 1) as nat, qid, r1, code, start, em);
        NR.NfaRepIncrRE(r1, code, em + 1, e1);
      }
  }

  // ===========================================================================
  // Range and entry lemmas
  // ===========================================================================

  /** Mid-parse states live strictly inside the block. */
  lemma InBlockRange(re: R.regex, code: RB.code, start: nat, endl: nat,
                     str: string, i: int, pc: nat, cp: int)
    requires InBlock(re, code, start, endl, str, i, pc, cp)
    ensures start <= pc < endl
    decreases CP.rsize(re), 0, 0
  {
    match re
    case Re_empty => case Re_lookaround(_, _, _) =>
    case Re_character(_) => case Re_anchor(_) =>
    case Re_alt(r1, r2) =>
      var e1: nat :| AltShape(r1, r2, code, start, e1, endl)
        && ((pc == start && cp == i)
            || InBlock(r1, code, start + 1, e1, str, i, pc, cp)
            || (pc == e1 && OB.Matches(r1, str, i, cp))
            || InBlock(r2, code, e1 + 1, endl, str, i, pc, cp));
      NR.NfaRepIncrRE(r1, code, start + 1, e1);
      NR.NfaRepIncrRE(r2, code, e1 + 1, endl);
      if InBlock(r1, code, start + 1, e1, str, i, pc, cp) {
        InBlockRange(r1, code, start + 1, e1, str, i, pc, cp);
      } else if InBlock(r2, code, e1 + 1, endl, str, i, pc, cp) {
        InBlockRange(r2, code, e1 + 1, endl, str, i, pc, cp);
      }
    case Re_con(r1, r2) =>
      var e1: nat :| ConShape(r1, r2, code, start, e1, endl)
        && (InBlock(r1, code, start, e1, str, i, pc, cp)
            || exists m: int :: OB.Matches(r1, str, i, m) && InBlock(r2, code, e1, endl, str, m, pc, cp));
      NR.NfaRepIncrRE(r1, code, start, e1);
      NR.NfaRepIncrRE(r2, code, e1, endl);
      if InBlock(r1, code, start, e1, str, i, pc, cp) {
        InBlockRange(r1, code, start, e1, str, i, pc, cp);
      } else {
        var m: int :| OB.Matches(r1, str, i, m) && InBlock(r2, code, e1, endl, str, m, pc, cp);
        InBlockRange(r2, code, e1, endl, str, m, pc, cp);
      }
    case Re_capture(cid, r1) =>
      var e1: nat :| CapShape(cid, r1, code, start, e1, endl)
        && ((pc == start && cp == i)
            || InBlock(r1, code, start + 1, e1, str, i, pc, cp)
            || (pc == e1 && OB.Matches(r1, str, i, cp)));
      NR.NfaRepIncrRE(r1, code, start + 1, e1);
      if InBlock(r1, code, start + 1, e1, str, i, pc, cp) {
        InBlockRange(r1, code, start + 1, e1, str, i, pc, cp);
      }
    case Re_quant(nul, qid, q, r1) =>
      if q.min == 0 && q.max == None {
        var es1: nat :| StarShape(qid, r1, code, start, es1, endl)
          && StTail(qid, r1, code, start, es1, str, i, pc, cp);
        var m := StTailInv(qid, r1, code, start, es1, str, i, pc, cp);
        NR.NfaRepIncrRE(r1, code, start + 3, es1);
        if InBlock(r1, code, start + 3, es1, str, m, pc, cp) {
          InBlockRange(r1, code, start + 3, es1, str, m, pc, cp);
        }
      } else if q.max.Some? {
        var em: nat :|
          NR.NfaRepMinRE(q.min as nat, qid, r1, code, start, em)
          && NR.NfaRepOptRE((q.max.value - q.min) as nat, q.greedy, qid, r1, code, em, endl)
          && (InMin(q.min as nat, qid, r1, code, start, em, str, i, pc, cp)
              || BdTail(q.min as nat, (q.max.value - q.min) as nat, q.greedy, qid, r1, code, em, endl, str, i, pc, cp));
        NR.NfaRepIncrMinRE(q.min as nat, qid, r1, code, start, em);
        NR.NfaRepIncrOptRE((q.max.value - q.min) as nat, q.greedy, qid, r1, code, em, endl);
        if InMin(q.min as nat, qid, r1, code, start, em, str, i, pc, cp) {
          InMinRange(q.min as nat, qid, r1, code, start, em, str, i, pc, cp);
        } else {
          var m := BdTailInv(q.min as nat, (q.max.value - q.min) as nat, q.greedy, qid, r1, code, em, endl, str, i, pc, cp);
          InOptRange((q.max.value - q.min) as nat, q.greedy, qid, r1, code, em, endl, str, m, pc, cp);
        }
      } else {
        var em: nat, e1: nat :|
          NR.NfaRepMinRE((q.min - 1) as nat, qid, r1, code, start, em)
          && DoWhileShape(qid, r1, code, em, e1, endl)
          && (InMin((q.min - 1) as nat, qid, r1, code, start, em, str, i, pc, cp)
              || DwTail((q.min - 1) as nat, qid, r1, code, em, e1, str, i, pc, cp));
        NR.NfaRepIncrMinRE((q.min - 1) as nat, qid, r1, code, start, em);
        NR.NfaRepIncrRE(r1, code, em + 1, e1);
        if InMin((q.min - 1) as nat, qid, r1, code, start, em, str, i, pc, cp) {
          InMinRange((q.min - 1) as nat, qid, r1, code, start, em, str, i, pc, cp);
        } else {
          var m := DwTailInv((q.min - 1) as nat, qid, r1, code, em, e1, str, i, pc, cp);
          if InBlock(r1, code, em + 1, e1, str, m, pc, cp) {
            InBlockRange(r1, code, em + 1, e1, str, m, pc, cp);
          }
        }
      }
  }

  /** `InBlockRange` for the forced-copy chain. */
  lemma InMinRange(k: nat, qid: R.quantid, r1: R.regex, code: RB.code,
                   start: nat, endl: nat, str: string, j: int, pc: nat, cp: int)
    requires InMin(k, qid, r1, code, start, endl, str, j, pc, cp)
    ensures start <= pc < endl
    decreases CP.rsize(r1), 1, k
  {
    var e1: nat :| MinShape(k, qid, r1, code, start, e1, endl)
      && ((pc == start && cp == j)
          || InBlock(r1, code, start + 1, e1, str, j, pc, cp)
          || exists m: int :: OB.Matches(r1, str, j, m) && InMin(k - 1, qid, r1, code, e1, endl, str, m, pc, cp));
    NR.NfaRepIncrRE(r1, code, start + 1, e1);
    NR.NfaRepIncrMinRE(k - 1, qid, r1, code, e1, endl);
    if pc == start && cp == j {
    } else if InBlock(r1, code, start + 1, e1, str, j, pc, cp) {
      InBlockRange(r1, code, start + 1, e1, str, j, pc, cp);
    } else {
      var m: int :| OB.Matches(r1, str, j, m) && InMin(k - 1, qid, r1, code, e1, endl, str, m, pc, cp);
      InMinRange(k - 1, qid, r1, code, e1, endl, str, m, pc, cp);
    }
  }

  /** `InBlockRange` for the optional-layer chain. */
  lemma InOptRange(layers: nat, greedy: bool, qid: R.quantid, r1: R.regex, code: RB.code,
                   start: nat, endl: nat, str: string, j: int, pc: nat, cp: int)
    requires InOpt(layers, greedy, qid, r1, code, start, endl, str, j, pc, cp)
    ensures start <= pc < endl
    decreases CP.rsize(r1), 2, layers
  {
    var e1: nat :| OptShape(layers, greedy, qid, r1, code, start, e1, endl)
      && (((pc == start || pc == start + 1 || pc == start + 2) && cp == j)
          || InBlock(r1, code, start + 3, e1, str, j, pc, cp)
          || (pc == e1 && OB.Matches(r1, str, j, cp))
          || exists m: int ::
               OB.Matches(r1, str, j, m)
               && InOpt(layers - 1, greedy, qid, r1, code, e1 + 1, endl, str, m, pc, cp));
    NR.NfaRepIncrRE(r1, code, start + 3, e1);
    NR.NfaRepIncrOptRE(layers - 1, greedy, qid, r1, code, e1 + 1, endl);
    if (pc == start || pc == start + 1 || pc == start + 2) && cp == j {
    } else if InBlock(r1, code, start + 3, e1, str, j, pc, cp) {
      InBlockRange(r1, code, start + 3, e1, str, j, pc, cp);
    } else if pc == e1 && OB.Matches(r1, str, j, cp) {
    } else {
      var m: int :| OB.Matches(r1, str, j, m)
        && InOpt(layers - 1, greedy, qid, r1, code, e1 + 1, endl, str, m, pc, cp);
      InOptRange(layers - 1, greedy, qid, r1, code, e1 + 1, endl, str, m, pc, cp);
    }
  }

  /** `BlockEntry` for a nonempty forced-copy chain. */
  lemma MinEntry(k: nat, qid: R.quantid, r1: R.regex, code: RB.code,
                 start: nat, endl: nat, str: string, cp: int)
    requires k > 0
    requires NR.NfaRepMinRE(k, qid, r1, code, start, endl)
    ensures InMin(k, qid, r1, code, start, endl, str, cp, start, cp)
  {
    var e1: nat :| NR.GetPcRE(code, start) == Some(RB.SetQuantToClock(qid, false))
      && NR.NfaRepRE(r1, code, start + 1, e1)
      && NR.NfaRepMinRE(k - 1, qid, r1, code, e1, endl);
    assert MinShape(k, qid, r1, code, start, e1, endl);
  }

  /** `BlockEntry` for a nonempty optional-layer chain. */
  lemma OptEntry(k: nat, greedy: bool, qid: R.quantid, r1: R.regex, code: RB.code,
                 start: nat, endl: nat, str: string, cp: int)
    requires k > 0
    requires NR.NfaRepOptRE(k, greedy, qid, r1, code, start, endl)
    ensures InOpt(k, greedy, qid, r1, code, start, endl, str, cp, start, cp)
  {
    var e1: nat :| NR.GetPcRE(code, start) == Some(if greedy then RB.Fork(start + 1, endl as int) else RB.Fork(endl as int, start + 1))
      && NR.GetPcRE(code, start + 1) == Some(RB.SetQuantToClock(qid, false))
      && NR.GetPcRE(code, start + 2) == Some(RB.BeginLoop)
      && NR.NfaRepRE(r1, code, start + 3, e1)
      && NR.GetPcRE(code, e1) == Some(RB.EndLoop)
      && NR.NfaRepOptRE(k - 1, greedy, qid, r1, code, e1 + 1, endl);
    assert OptShape(k, greedy, qid, r1, code, start, e1, endl);
  }

  // ===========================================================================
  // Edge inversion per pinned instruction
  // ===========================================================================

  /** Any one configuration-graph step: an epsilon edge (same position) or a
      consume edge (next position, exit flag re-armed). */
  ghost predicate AnyEdge(code: RB.code, str: string, pc: nat, eb: bool, cp: int,
                          pc2: nat, eb2: bool, cp2: int) {
    (ORc.EpsEdge(code, str, cp, pc, eb, pc2, eb2) && cp2 == cp)
    || (ORc.ConsumeEdge(code, str, cp, pc) && pc2 == pc + 1 && eb2 == true && cp2 == cp + 1)
  }

  lemma EdgeFromConsume(code: RB.code, str: string, ce: RC.char_expectation,
                        pc: nat, eb: bool, cp: int, pc2: nat, eb2: bool, cp2: int)
    requires NR.GetPcRE(code, pc) == Some(RB.Consume(ce))
    requires AnyEdge(code, str, pc, eb, cp, pc2, eb2, cp2)
    ensures pc2 == pc + 1 && eb2 == true && cp2 == cp + 1
    ensures RC.is_accepted(AI.get_char(str, cp), ce)
  {
    OB.GetPcInstr(code, pc, RB.Consume(ce));
  }

  lemma EdgeFromJmp(code: RB.code, str: string, x: int,
                    pc: nat, eb: bool, cp: int, pc2: nat, eb2: bool, cp2: int)
    requires NR.GetPcRE(code, pc) == Some(RB.Jmp(x))
    requires AnyEdge(code, str, pc, eb, cp, pc2, eb2, cp2)
    ensures x >= 0 && pc2 == x && eb2 == eb && cp2 == cp
  {
    OB.GetPcInstr(code, pc, RB.Jmp(x));
  }

  lemma EdgeFromForkAt(code: RB.code, str: string, a: nat, b: nat,
                       pc: nat, eb: bool, cp: int, pc2: nat, eb2: bool, cp2: int)
    requires OB.ForkAt(code, pc, a, b)
    requires AnyEdge(code, str, pc, eb, cp, pc2, eb2, cp2)
    ensures (pc2 == a || pc2 == b) && eb2 == eb && cp2 == cp
  {
    if NR.GetPcRE(code, pc) == Some(RB.Fork(a as int, b as int)) {
      OB.GetPcInstr(code, pc, RB.Fork(a as int, b as int));
    } else {
      OB.GetPcInstr(code, pc, RB.Fork(b as int, a as int));
    }
  }

  lemma EdgeFromSetReg(code: RB.code, str: string, reg: RB.Register,
                       pc: nat, eb: bool, cp: int, pc2: nat, eb2: bool, cp2: int)
    requires NR.GetPcRE(code, pc) == Some(RB.SetRegisterToCP(reg))
    requires AnyEdge(code, str, pc, eb, cp, pc2, eb2, cp2)
    ensures pc2 == pc + 1 && eb2 == eb && cp2 == cp
  {
    OB.GetPcInstr(code, pc, RB.SetRegisterToCP(reg));
  }

  lemma EdgeFromSetQuant(code: RB.code, str: string, q: R.quantid, b: bool,
                         pc: nat, eb: bool, cp: int, pc2: nat, eb2: bool, cp2: int)
    requires NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(q, b))
    requires AnyEdge(code, str, pc, eb, cp, pc2, eb2, cp2)
    ensures pc2 == pc + 1 && eb2 == eb && cp2 == cp
  {
    OB.GetPcInstr(code, pc, RB.SetQuantToClock(q, b));
  }

  lemma EdgeFromBeginLoop(code: RB.code, str: string,
                          pc: nat, eb: bool, cp: int, pc2: nat, eb2: bool, cp2: int)
    requires NR.GetPcRE(code, pc) == Some(RB.BeginLoop)
    requires AnyEdge(code, str, pc, eb, cp, pc2, eb2, cp2)
    ensures pc2 == pc + 1 && eb2 == false && cp2 == cp
  {
    OB.GetPcInstr(code, pc, RB.BeginLoop);
  }

  lemma EdgeFromEndLoop(code: RB.code, str: string,
                        pc: nat, eb: bool, cp: int, pc2: nat, eb2: bool, cp2: int)
    requires NR.GetPcRE(code, pc) == Some(RB.EndLoop)
    requires AnyEdge(code, str, pc, eb, cp, pc2, eb2, cp2)
    ensures pc2 == pc + 1 && eb2 == eb && cp2 == cp
  {
    OB.GetPcInstr(code, pc, RB.EndLoop);
  }

  lemma EdgeFromAnchor(code: RB.code, str: string, a: R.anchor,
                       pc: nat, eb: bool, cp: int, pc2: nat, eb2: bool, cp2: int)
    requires NR.GetPcRE(code, pc) == Some(RB.AnchorAssertion(a))
    requires AnyEdge(code, str, pc, eb, cp, pc2, eb2, cp2)
    ensures pc2 == pc + 1 && eb2 == eb && cp2 == cp
    ensures LAnc.is_satisfied(a, ORc.CtxAt(str, cp), LAnc.Forward)
  {
    OB.GetPcInstr(code, pc, RB.AnchorAssertion(a));
  }

  // ===========================================================================
  // Chain-exit vocabulary and small intros
  // ===========================================================================

  /** The optional-layer chain completed with at most `layers` spans. */
  ghost predicate OptDone(layers: nat, r1: R.regex, str: string, j: int, cp2: int) {
    exists k: nat {:trigger OB.MatchesIter(r1, k, str, j, cp2)} ::
      k <= layers && OB.MatchesIter(r1, k, str, j, cp2)
  }

  lemma OptDoneIntro(layers: nat, r1: R.regex, str: string, j: int, cp2: int, k: nat)
    requires k <= layers && OB.MatchesIter(r1, k, str, j, cp2)
    ensures OptDone(layers, r1, str, j, cp2)
  {
  }

  lemma OptDoneInv(layers: nat, r1: R.regex, str: string, j: int, cp2: int) returns (k: nat)
    requires OptDone(layers, r1, str, j, cp2)
    ensures k <= layers && OB.MatchesIter(r1, k, str, j, cp2)
  {
    k :| k <= layers && OB.MatchesIter(r1, k, str, j, cp2);
  }

  lemma IterFromIntro(r: R.regex, n: nat, k: nat, str: string, i: int, m: int)
    requires n <= k && OB.MatchesIter(r, k, str, i, m)
    ensures IterFrom(r, n, str, i, m)
  {
  }

  /** Entering a nonempty block at its start label, at string position `cp`,
      is a mid-parse state with entry `cp` (an empty block has no mid states
      — pair with `BlockEmpty`). */
  lemma BlockEntry(re: R.regex, code: RB.code, start: nat, endl: nat, str: string, cp: int)
    requires NR.LookFreeRE(re)
    requires NR.NfaRepRE(re, code, start, endl)
    ensures InBlock(re, code, start, endl, str, cp, start, cp) || start == endl
    decreases CP.rsize(re), 0, 0
  {
    match re
    case Re_empty =>
    case Re_lookaround(_, _, _) =>
    case Re_character(_) =>
    case Re_anchor(_) =>
    case Re_alt(r1, r2) =>
      var e1: nat :| NR.GetPcRE(code, start) == Some(RB.Fork(start + 1, e1 + 1))
        && NR.NfaRepRE(r1, code, start + 1, e1)
        && NR.GetPcRE(code, e1) == Some(RB.Jmp(endl as int))
        && NR.NfaRepRE(r2, code, e1 + 1, endl);
      assert AltShape(r1, r2, code, start, e1, endl);
      assert InBlock(re, code, start, endl, str, cp, start, cp);
    case Re_con(r1, r2) =>
      var e1: nat :| NR.NfaRepRE(r1, code, start, e1) && NR.NfaRepRE(r2, code, e1, endl);
      assert ConShape(r1, r2, code, start, e1, endl);
      BlockEntry(r1, code, start, e1, str, cp);
      if start == e1 {
        BlockEmpty(r1, code, start, str, cp);
        BlockEntry(r2, code, e1, endl, str, cp);
        if e1 == endl {
        } else {
          assert OB.Matches(r1, str, cp, cp) && InBlock(r2, code, e1, endl, str, cp, start, cp);
          assert InBlock(re, code, start, endl, str, cp, start, cp);
        }
      } else {
        assert InBlock(r1, code, start, e1, str, cp, start, cp);
        assert InBlock(re, code, start, endl, str, cp, start, cp);
      }
    case Re_capture(cid, r1) =>
      var e1: nat :| NR.GetPcRE(code, start) == Some(RB.SetRegisterToCP(CP.start_reg(cid)))
        && NR.NfaRepRE(r1, code, start + 1, e1)
        && NR.GetPcRE(code, e1) == Some(RB.SetRegisterToCP(CP.end_reg(cid)))
        && endl == e1 + 1;
      assert CapShape(cid, r1, code, start, e1, endl);
      assert InBlock(re, code, start, endl, str, cp, start, cp);
    case Re_quant(nul, qid, q, r1) =>
      if q.min == 0 && q.max == None {
        var es1: nat :|
          NR.GetPcRE(code, start) == Some(if q.greedy then RB.Fork(start + 1, es1 + 2) else RB.Fork(es1 + 2, start + 1))
          && NR.GetPcRE(code, start + 1) == Some(RB.SetQuantToClock(qid, false))
          && NR.GetPcRE(code, start + 2) == Some(RB.BeginLoop)
          && NR.NfaRepRE(r1, code, start + 3, es1)
          && NR.GetPcRE(code, es1) == Some(RB.EndLoop)
          && NR.GetPcRE(code, es1 + 1) == Some(RB.Jmp(start as int))
          && endl == es1 + 2;
        assert StarShape(qid, r1, code, start, es1, endl);
        IterFromZero(r1, str, cp);
        StTailIntro(qid, r1, code, start, es1, str, cp, start, cp, cp);
        assert InBlock(re, code, start, endl, str, cp, start, cp);
      } else if q.max.Some? {
        var em := NR.NfaRepREQuantInv(nul, qid, q, r1, code, start, endl);
        if q.min as nat > 0 {
          MinEntry(q.min as nat, qid, r1, code, start, em, str, cp);
          assert InBlock(re, code, start, endl, str, cp, start, cp);
        } else {
          MinZeroSame(qid, r1, code, start, em);
          if (q.max.value - q.min) as nat > 0 {
            OptEntry((q.max.value - q.min) as nat, q.greedy, qid, r1, code, em, endl, str, cp);
            assert OB.MatchesIter(r1, 0, str, cp, cp);
            BdTailIntro(q.min as nat, (q.max.value - q.min) as nat, q.greedy, qid, r1, code, em, endl, str, cp, start, cp, cp);
            assert InBlock(re, code, start, endl, str, cp, start, cp);
          } else {
            OptZeroSame(q.greedy, qid, r1, code, em, endl);
          }
        }
      } else {
        var em, e1 := NR.NfaRepREPlusInv(nul, qid, q, r1, code, start, endl);
        assert DoWhileShape(qid, r1, code, em, e1, endl);
        if (q.min - 1) as nat > 0 {
          MinEntry((q.min - 1) as nat, qid, r1, code, start, em, str, cp);
          assert InBlock(re, code, start, endl, str, cp, start, cp);
        } else {
          MinZeroSame(qid, r1, code, start, em);
          IterFromZero(r1, str, cp);
          DwTailIntro((q.min - 1) as nat, qid, r1, code, em, e1, str, cp, start, cp, cp);
          assert InBlock(re, code, start, endl, str, cp, start, cp);
        }
      }
  }

  // ===========================================================================
  // The step lemmas: every edge out of a mid-parse state stays mid-parse or
  // exits the block with a completed span
  // ===========================================================================

  /** Concatenate two chains. */
  lemma IterConcat(r: R.regex, a: nat, b: nat, str: string, i: int, m: int, j: int)
    requires OB.MatchesIter(r, a, str, i, m)
    requires OB.MatchesIter(r, b, str, m, j)
    ensures OB.MatchesIter(r, a + b, str, i, j)
    decreases a
  {
    if a == 0 { return; }
    var m1 := OB.MatchesIterHead(r, a, str, i, m);
    IterConcat(r, a - 1, b, str, m1, m, j);
    IterCons(r, a + b - 1, str, i, m1, j);
  }

  /** `BlockStep` for the forced-copy chain: exits carry exactly `k` spans. */
  lemma BlockStepMin(k: nat, qid: R.quantid, r1: R.regex, code: RB.code,
                     start: nat, endl: nat, str: string, j: int,
                     pc: nat, eb: bool, cp: int, pc2: nat, eb2: bool, cp2: int)
    requires NR.LookFreeRE(r1)
    requires InMin(k, qid, r1, code, start, endl, str, j, pc, cp)
    requires AnyEdge(code, str, pc, eb, cp, pc2, eb2, cp2)
    ensures InMin(k, qid, r1, code, start, endl, str, j, pc2, cp2)
         || (pc2 == endl && OB.MatchesIter(r1, k, str, j, cp2))
    decreases CP.rsize(r1), 1, k
  {
    var e1: nat :| MinShape(k, qid, r1, code, start, e1, endl)
      && ((pc == start && cp == j)
          || InBlock(r1, code, start + 1, e1, str, j, pc, cp)
          || exists m: int :: OB.Matches(r1, str, j, m) && InMin(k - 1, qid, r1, code, e1, endl, str, m, pc, cp));
    if pc == start && cp == j {
      EdgeFromSetQuant(code, str, qid, false, pc, eb, cp, pc2, eb2, cp2);
      BlockEntry(r1, code, start + 1, e1, str, j);
      if start + 1 == e1 {
        BlockEmpty(r1, code, start + 1, str, j);
        // pc2 == e1: the first copy matched empty; hand over to the rest
        if k - 1 > 0 {
          MinEntry(k - 1, qid, r1, code, e1, endl, str, j);
          assert InMin(k, qid, r1, code, start, endl, str, j, pc2, cp2);
        } else {
          MinZeroSame(qid, r1, code, e1, endl);
          IterCons(r1, 0, str, j, j, j);
          assert pc2 == endl && OB.MatchesIter(r1, k, str, j, cp2);
        }
      } else {
        assert InBlock(r1, code, start + 1, e1, str, j, pc2, cp2);
        assert InMin(k, qid, r1, code, start, endl, str, j, pc2, cp2);
      }
    } else if InBlock(r1, code, start + 1, e1, str, j, pc, cp) {
      BlockStep(r1, code, start + 1, e1, str, j, pc, eb, cp, pc2, eb2, cp2);
      if InBlock(r1, code, start + 1, e1, str, j, pc2, cp2) {
        assert InMin(k, qid, r1, code, start, endl, str, j, pc2, cp2);
      } else {
        // pc2 == e1 with Matches(r1, j, cp2): first copy done
        if k - 1 > 0 {
          MinEntry(k - 1, qid, r1, code, e1, endl, str, cp2);
          assert InMin(k, qid, r1, code, start, endl, str, j, pc2, cp2);
        } else {
          MinZeroSame(qid, r1, code, e1, endl);
          IterCons(r1, 0, str, j, cp2, cp2);
          assert pc2 == endl && OB.MatchesIter(r1, k, str, j, cp2);
        }
      }
    } else {
      var m: int :| OB.Matches(r1, str, j, m) && InMin(k - 1, qid, r1, code, e1, endl, str, m, pc, cp);
      BlockStepMin(k - 1, qid, r1, code, e1, endl, str, m, pc, eb, cp, pc2, eb2, cp2);
      if InMin(k - 1, qid, r1, code, e1, endl, str, m, pc2, cp2) {
        assert InMin(k, qid, r1, code, start, endl, str, j, pc2, cp2);
      } else {
        IterCons(r1, k - 1, str, j, m, cp2);
        assert pc2 == endl && OB.MatchesIter(r1, k, str, j, cp2);
      }
    }
  }

  /** `BlockStep` for the optional-layer chain: exits carry at most `layers`
      spans (skipping is one fork edge straight to the common end). */
  lemma BlockStepOpt(layers: nat, greedy: bool, qid: R.quantid, r1: R.regex, code: RB.code,
                     start: nat, endl: nat, str: string, j: int,
                     pc: nat, eb: bool, cp: int, pc2: nat, eb2: bool, cp2: int)
    requires NR.LookFreeRE(r1)
    requires InOpt(layers, greedy, qid, r1, code, start, endl, str, j, pc, cp)
    requires AnyEdge(code, str, pc, eb, cp, pc2, eb2, cp2)
    ensures InOpt(layers, greedy, qid, r1, code, start, endl, str, j, pc2, cp2)
         || (pc2 == endl && OptDone(layers, r1, str, j, cp2))
    decreases CP.rsize(r1), 2, layers
  {
    var e1: nat :| OptShape(layers, greedy, qid, r1, code, start, e1, endl)
      && (((pc == start || pc == start + 1 || pc == start + 2) && cp == j)
          || InBlock(r1, code, start + 3, e1, str, j, pc, cp)
          || (pc == e1 && OB.Matches(r1, str, j, cp))
          || exists m: int ::
               OB.Matches(r1, str, j, m)
               && InOpt(layers - 1, greedy, qid, r1, code, e1 + 1, endl, str, m, pc, cp));
    if (pc == start || pc == start + 1 || pc == start + 2) && cp == j {
      if pc == start {
        assert OB.ForkAt(code, start, start + 1, endl);
        EdgeFromForkAt(code, str, start + 1, endl, pc, eb, cp, pc2, eb2, cp2);
        if pc2 == start + 1 {
          assert InOpt(layers, greedy, qid, r1, code, start, endl, str, j, pc2, cp2);
        } else {
          assert OB.MatchesIter(r1, 0, str, j, j);
          OptDoneIntro(layers, r1, str, j, cp2, 0);
        }
      } else if pc == start + 1 {
        EdgeFromSetQuant(code, str, qid, false, pc, eb, cp, pc2, eb2, cp2);
        assert InOpt(layers, greedy, qid, r1, code, start, endl, str, j, pc2, cp2);
      } else {
        EdgeFromBeginLoop(code, str, pc, eb, cp, pc2, eb2, cp2);
        BlockEntry(r1, code, start + 3, e1, str, j);
        if start + 3 == e1 {
          BlockEmpty(r1, code, start + 3, str, j);
          assert pc2 == e1 && OB.Matches(r1, str, j, cp2);
          assert InOpt(layers, greedy, qid, r1, code, start, endl, str, j, pc2, cp2);
        } else {
          assert InBlock(r1, code, start + 3, e1, str, j, pc2, cp2);
          assert InOpt(layers, greedy, qid, r1, code, start, endl, str, j, pc2, cp2);
        }
      }
    } else if InBlock(r1, code, start + 3, e1, str, j, pc, cp) {
      BlockStep(r1, code, start + 3, e1, str, j, pc, eb, cp, pc2, eb2, cp2);
      if InBlock(r1, code, start + 3, e1, str, j, pc2, cp2) {
        assert InOpt(layers, greedy, qid, r1, code, start, endl, str, j, pc2, cp2);
      } else {
        assert pc2 == e1 && OB.Matches(r1, str, j, cp2);
        assert InOpt(layers, greedy, qid, r1, code, start, endl, str, j, pc2, cp2);
      }
    } else if pc == e1 && OB.Matches(r1, str, j, cp) {
      EdgeFromEndLoop(code, str, pc, eb, cp, pc2, eb2, cp2);
      // pc2 == e1 + 1: the next layer's chain begins (or the chain is done)
      if layers - 1 > 0 {
        OptEntry(layers - 1, greedy, qid, r1, code, e1 + 1, endl, str, cp);
        assert InOpt(layers, greedy, qid, r1, code, start, endl, str, j, pc2, cp2);
      } else {
        OptZeroSame(greedy, qid, r1, code, e1 + 1, endl);
        IterCons(r1, 0, str, j, cp, cp);
        OptDoneIntro(layers, r1, str, j, cp2, 1);
      }
    } else {
      var m: int :| OB.Matches(r1, str, j, m)
        && InOpt(layers - 1, greedy, qid, r1, code, e1 + 1, endl, str, m, pc, cp);
      BlockStepOpt(layers - 1, greedy, qid, r1, code, e1 + 1, endl, str, m, pc, eb, cp, pc2, eb2, cp2);
      if InOpt(layers - 1, greedy, qid, r1, code, e1 + 1, endl, str, m, pc2, cp2) {
        assert InOpt(layers, greedy, qid, r1, code, start, endl, str, j, pc2, cp2);
      } else {
        var k := OptDoneInv(layers - 1, r1, str, m, cp2);
        IterCons(r1, k, str, j, m, cp2);
        OptDoneIntro(layers, r1, str, j, cp2, k + 1);
      }
    }
  }

  /** THE step lemma: every configuration-graph edge out of a mid-parse state
      of `re`'s block lands in a mid-parse state or exits at `endl` with a
      completed span match. */
  lemma BlockStep(re: R.regex, code: RB.code, start: nat, endl: nat, str: string, i: int,
                  pc: nat, eb: bool, cp: int, pc2: nat, eb2: bool, cp2: int)
    requires NR.LookFreeRE(re)
    requires InBlock(re, code, start, endl, str, i, pc, cp)
    requires AnyEdge(code, str, pc, eb, cp, pc2, eb2, cp2)
    ensures InBlock(re, code, start, endl, str, i, pc2, cp2)
         || (pc2 == endl && OB.Matches(re, str, i, cp2))
    decreases CP.rsize(re), 0, 0
  {
    match re
    case Re_empty =>
    case Re_lookaround(_, _, _) =>
    case Re_character(ch) =>
      EdgeFromConsume(code, str, T.ExpectationOf(ch), pc, eb, cp, pc2, eb2, cp2);
      assert OB.Matches(re, str, i, cp2);
    case Re_anchor(a) =>
      EdgeFromAnchor(code, str, a, pc, eb, cp, pc2, eb2, cp2);
      assert OB.Matches(re, str, i, cp2);
    case Re_alt(r1, r2) =>
      var e1: nat :| AltShape(r1, r2, code, start, e1, endl)
        && ((pc == start && cp == i)
            || InBlock(r1, code, start + 1, e1, str, i, pc, cp)
            || (pc == e1 && OB.Matches(r1, str, i, cp))
            || InBlock(r2, code, e1 + 1, endl, str, i, pc, cp));
      if pc == start && cp == i {
        OB.GetPcInstr(code, start, RB.Fork(start + 1, e1 + 1));
        assert ORc.EpsEdge(code, str, cp, pc, eb, pc2, eb2) && cp2 == cp;
        assert pc2 == start + 1 || pc2 == e1 + 1;
        if pc2 == start + 1 {
          BlockEntry(r1, code, start + 1, e1, str, i);
          if start + 1 == e1 {
            BlockEmpty(r1, code, start + 1, str, i);
            assert pc2 == e1 && OB.Matches(r1, str, i, cp2);
            assert InBlock(re, code, start, endl, str, i, pc2, cp2);
          } else {
            assert InBlock(re, code, start, endl, str, i, pc2, cp2);
          }
        } else {
          BlockEntry(r2, code, e1 + 1, endl, str, i);
          if e1 + 1 == endl {
            BlockEmpty(r2, code, e1 + 1, str, i);
            assert pc2 == endl && OB.Matches(re, str, i, cp2);
          } else {
            assert InBlock(re, code, start, endl, str, i, pc2, cp2);
          }
        }
      } else if InBlock(r1, code, start + 1, e1, str, i, pc, cp) {
        BlockStep(r1, code, start + 1, e1, str, i, pc, eb, cp, pc2, eb2, cp2);
        assert InBlock(re, code, start, endl, str, i, pc2, cp2);
      } else if pc == e1 && OB.Matches(r1, str, i, cp) {
        EdgeFromJmp(code, str, endl as int, pc, eb, cp, pc2, eb2, cp2);
        assert pc2 == endl && OB.Matches(re, str, i, cp2);
      } else {
        BlockStep(r2, code, e1 + 1, endl, str, i, pc, eb, cp, pc2, eb2, cp2);
        if InBlock(r2, code, e1 + 1, endl, str, i, pc2, cp2) {
          assert InBlock(re, code, start, endl, str, i, pc2, cp2);
        } else {
          assert pc2 == endl && OB.Matches(re, str, i, cp2);
        }
      }
    case Re_con(r1, r2) =>
      var e1: nat :| ConShape(r1, r2, code, start, e1, endl)
        && (InBlock(r1, code, start, e1, str, i, pc, cp)
            || exists m: int :: OB.Matches(r1, str, i, m) && InBlock(r2, code, e1, endl, str, m, pc, cp));
      if InBlock(r1, code, start, e1, str, i, pc, cp) {
        BlockStep(r1, code, start, e1, str, i, pc, eb, cp, pc2, eb2, cp2);
        if InBlock(r1, code, start, e1, str, i, pc2, cp2) {
          assert InBlock(re, code, start, endl, str, i, pc2, cp2);
        } else {
          // pc2 == e1 with Matches(r1, i, cp2): cross the seam into r2
          BlockEntry(r2, code, e1, endl, str, cp2);
          if e1 == endl {
            BlockEmpty(r2, code, e1, str, cp2);
            assert pc2 == endl && OB.Matches(re, str, i, cp2);
          } else {
            assert OB.Matches(r1, str, i, cp2) && InBlock(r2, code, e1, endl, str, cp2, pc2, cp2);
            assert InBlock(re, code, start, endl, str, i, pc2, cp2);
          }
        }
      } else {
        var m: int :| OB.Matches(r1, str, i, m) && InBlock(r2, code, e1, endl, str, m, pc, cp);
        BlockStep(r2, code, e1, endl, str, m, pc, eb, cp, pc2, eb2, cp2);
        if InBlock(r2, code, e1, endl, str, m, pc2, cp2) {
          assert InBlock(re, code, start, endl, str, i, pc2, cp2);
        } else {
          assert pc2 == endl && OB.Matches(re, str, i, cp2);
        }
      }
    case Re_capture(cid, r1) =>
      var e1: nat :| CapShape(cid, r1, code, start, e1, endl)
        && ((pc == start && cp == i)
            || InBlock(r1, code, start + 1, e1, str, i, pc, cp)
            || (pc == e1 && OB.Matches(r1, str, i, cp)));
      if pc == start && cp == i {
        EdgeFromSetReg(code, str, CP.start_reg(cid), pc, eb, cp, pc2, eb2, cp2);
        BlockEntry(r1, code, start + 1, e1, str, i);
        if start + 1 == e1 {
          BlockEmpty(r1, code, start + 1, str, i);
          assert pc2 == e1 && OB.Matches(r1, str, i, cp2);
          assert InBlock(re, code, start, endl, str, i, pc2, cp2);
        } else {
          assert InBlock(re, code, start, endl, str, i, pc2, cp2);
        }
      } else if InBlock(r1, code, start + 1, e1, str, i, pc, cp) {
        BlockStep(r1, code, start + 1, e1, str, i, pc, eb, cp, pc2, eb2, cp2);
        assert InBlock(re, code, start, endl, str, i, pc2, cp2);
      } else {
        EdgeFromSetReg(code, str, CP.end_reg(cid), pc, eb, cp, pc2, eb2, cp2);
        assert pc2 == endl && OB.Matches(re, str, i, cp2);
      }
    case Re_quant(nul, qid, q, r1) =>
      if q.min == 0 && q.max == None {
        var es1: nat :| StarShape(qid, r1, code, start, es1, endl)
          && StTail(qid, r1, code, start, es1, str, i, pc, cp);
        var m := StTailInv(qid, r1, code, start, es1, str, i, pc, cp);
        if (pc == start || pc == start + 1 || pc == start + 2) && cp == m {
          if pc == start {
            assert OB.ForkAt(code, start, start + 1, endl);
            EdgeFromForkAt(code, str, start + 1, endl, pc, eb, cp, pc2, eb2, cp2);
            if pc2 == start + 1 {
              StTailIntro(qid, r1, code, start, es1, str, i, pc2, cp2, m);
              assert InBlock(re, code, start, endl, str, i, pc2, cp2);
            } else {
              var k := IterFromInv(r1, 0, str, i, m);
              assert OB.Matches(re, str, i, cp2);
            }
          } else if pc == start + 1 {
            EdgeFromSetQuant(code, str, qid, false, pc, eb, cp, pc2, eb2, cp2);
            StTailIntro(qid, r1, code, start, es1, str, i, pc2, cp2, m);
            assert InBlock(re, code, start, endl, str, i, pc2, cp2);
          } else {
            EdgeFromBeginLoop(code, str, pc, eb, cp, pc2, eb2, cp2);
            BlockEntry(r1, code, start + 3, es1, str, m);
            if start + 3 == es1 {
              BlockEmpty(r1, code, start + 3, str, m);
              assert pc2 == es1 && OB.Matches(r1, str, m, cp2);
              StTailIntro(qid, r1, code, start, es1, str, i, pc2, cp2, m);
              assert InBlock(re, code, start, endl, str, i, pc2, cp2);
            } else {
              StTailIntro(qid, r1, code, start, es1, str, i, pc2, cp2, m);
              assert InBlock(re, code, start, endl, str, i, pc2, cp2);
            }
          }
        } else if InBlock(r1, code, start + 3, es1, str, m, pc, cp) {
          BlockStep(r1, code, start + 3, es1, str, m, pc, eb, cp, pc2, eb2, cp2);
          StTailIntro(qid, r1, code, start, es1, str, i, pc2, cp2, m);
          assert InBlock(re, code, start, endl, str, i, pc2, cp2);
        } else if pc == es1 {
          EdgeFromEndLoop(code, str, pc, eb, cp, pc2, eb2, cp2);
          StTailIntro(qid, r1, code, start, es1, str, i, pc2, cp2, m);
          assert InBlock(re, code, start, endl, str, i, pc2, cp2);
        } else {
          EdgeFromJmp(code, str, start as int, pc, eb, cp, pc2, eb2, cp2);
          IterFromSnoc(r1, 0, str, i, m, cp);
          StTailIntro(qid, r1, code, start, es1, str, i, pc2, cp2, cp);
          assert InBlock(re, code, start, endl, str, i, pc2, cp2);
        }
      } else if q.max.Some? {
        var em: nat :|
          NR.NfaRepMinRE(q.min as nat, qid, r1, code, start, em)
          && NR.NfaRepOptRE((q.max.value - q.min) as nat, q.greedy, qid, r1, code, em, endl)
          && (InMin(q.min as nat, qid, r1, code, start, em, str, i, pc, cp)
              || BdTail(q.min as nat, (q.max.value - q.min) as nat, q.greedy, qid, r1, code, em, endl, str, i, pc, cp));
        if InMin(q.min as nat, qid, r1, code, start, em, str, i, pc, cp) {
          BlockStepMin(q.min as nat, qid, r1, code, start, em, str, i, pc, eb, cp, pc2, eb2, cp2);
          if InMin(q.min as nat, qid, r1, code, start, em, str, i, pc2, cp2) {
            assert InBlock(re, code, start, endl, str, i, pc2, cp2);
          } else {
            // pc2 == em with the min copies done: enter the layers (or exit)
            if (q.max.value - q.min) as nat > 0 {
              OptEntry((q.max.value - q.min) as nat, q.greedy, qid, r1, code, em, endl, str, cp2);
              BdTailIntro(q.min as nat, (q.max.value - q.min) as nat, q.greedy, qid, r1, code, em, endl, str, i, pc2, cp2, cp2);
              assert InBlock(re, code, start, endl, str, i, pc2, cp2);
            } else {
              OptZeroSame(q.greedy, qid, r1, code, em, endl);
              assert pc2 == endl && OB.Matches(re, str, i, cp2);
            }
          }
        } else {
          var m := BdTailInv(q.min as nat, (q.max.value - q.min) as nat, q.greedy, qid, r1, code, em, endl, str, i, pc, cp);
          BlockStepOpt((q.max.value - q.min) as nat, q.greedy, qid, r1, code, em, endl, str, m, pc, eb, cp, pc2, eb2, cp2);
          if InOpt((q.max.value - q.min) as nat, q.greedy, qid, r1, code, em, endl, str, m, pc2, cp2) {
            BdTailIntro(q.min as nat, (q.max.value - q.min) as nat, q.greedy, qid, r1, code, em, endl, str, i, pc2, cp2, m);
            assert InBlock(re, code, start, endl, str, i, pc2, cp2);
          } else {
            var k := OptDoneInv((q.max.value - q.min) as nat, r1, str, m, cp2);
            IterConcat(r1, q.min as nat, k, str, i, m, cp2);
            assert OB.MatchesIter(r1, q.min as nat + k, str, i, cp2);
            assert pc2 == endl && OB.Matches(re, str, i, cp2);
          }
        }
      } else {
        var em: nat, e1: nat :|
          NR.NfaRepMinRE((q.min - 1) as nat, qid, r1, code, start, em)
          && DoWhileShape(qid, r1, code, em, e1, endl)
          && (InMin((q.min - 1) as nat, qid, r1, code, start, em, str, i, pc, cp)
              || DwTail((q.min - 1) as nat, qid, r1, code, em, e1, str, i, pc, cp));
        if InMin((q.min - 1) as nat, qid, r1, code, start, em, str, i, pc, cp) {
          BlockStepMin((q.min - 1) as nat, qid, r1, code, start, em, str, i, pc, eb, cp, pc2, eb2, cp2);
          if InMin((q.min - 1) as nat, qid, r1, code, start, em, str, i, pc2, cp2) {
            assert InBlock(re, code, start, endl, str, i, pc2, cp2);
          } else {
            // pc2 == em with the min-1 copies done
            IterFromIntro(r1, (q.min - 1) as nat, (q.min - 1) as nat, str, i, cp2);
            DwTailIntro((q.min - 1) as nat, qid, r1, code, em, e1, str, i, pc2, cp2, cp2);
            assert InBlock(re, code, start, endl, str, i, pc2, cp2);
          }
        } else {
          var m := DwTailInv((q.min - 1) as nat, qid, r1, code, em, e1, str, i, pc, cp);
          if pc == em && cp == m {
            EdgeFromSetQuant(code, str, qid, false, pc, eb, cp, pc2, eb2, cp2);
            BlockEntry(r1, code, em + 1, e1, str, m);
            if em + 1 == e1 {
              BlockEmpty(r1, code, em + 1, str, m);
              DwTailIntro((q.min - 1) as nat, qid, r1, code, em, e1, str, i, pc2, cp2, m);
              assert InBlock(re, code, start, endl, str, i, pc2, cp2);
            } else {
              DwTailIntro((q.min - 1) as nat, qid, r1, code, em, e1, str, i, pc2, cp2, m);
              assert InBlock(re, code, start, endl, str, i, pc2, cp2);
            }
          } else if InBlock(r1, code, em + 1, e1, str, m, pc, cp) {
            BlockStep(r1, code, em + 1, e1, str, m, pc, eb, cp, pc2, eb2, cp2);
            DwTailIntro((q.min - 1) as nat, qid, r1, code, em, e1, str, i, pc2, cp2, m);
            assert InBlock(re, code, start, endl, str, i, pc2, cp2);
          } else {
            // pc == e1 with this repetition's span complete: loop or exit
            assert OB.ForkAt(code, e1, em, endl);
            EdgeFromForkAt(code, str, em, endl, pc, eb, cp, pc2, eb2, cp2);
            if pc2 == em {
              IterFromSnoc(r1, (q.min - 1) as nat, str, i, m, cp);
              DwTailIntro((q.min - 1) as nat, qid, r1, code, em, e1, str, i, pc2, cp2, cp);
              assert InBlock(re, code, start, endl, str, i, pc2, cp2);
            } else {
              var k := IterFromInv(r1, (q.min - 1) as nat, str, i, m);
              IterSnoc(r1, k, str, i, m, cp);
              assert OB.MatchesIter(r1, k + 1, str, i, cp2);
              assert pc2 == endl && OB.Matches(re, str, i, cp2);
            }
          }
        }
      }
  }
}
