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
  import LT = LindenElkLookTables
  import ORc = LindenElkOracleReach
  import OBu = LindenElkOracleBuild
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

  /** (§2.5b) The CIN-GREEDY end-fork loop's layout: head fork, stamp,
      guarded body, end fork, and the trailing `SetQuantToClock(qid, true)`
      the skip path crosses. */
  ghost predicate CinShape(qid: R.quantid, r1: R.regex, code: RB.code, em: nat, e1: nat, endl: nat) {
    NR.GetPcRE(code, em) == Some(RB.Fork((em + 1) as int, (e1 + 2) as int))
    && NR.GetPcRE(code, em + 1) == Some(RB.SetQuantToClock(qid, false))
    && NR.GetPcRE(code, em + 2) == Some(RB.BeginLoop)
    && NR.NfaRepRE(r1, code, em + 3, e1)
    && NR.GetPcRE(code, e1) == Some(RB.EndLoop)
    && NR.GetPcRE(code, e1 + 1) == Some(RB.Fork((em + 1) as int, (e1 + 3) as int))
    && NR.GetPcRE(code, e1 + 2) == Some(RB.SetQuantToClock(qid, true))
    && endl == e1 + 3
  }

  // ===========================================================================
  // The mid-parse invariant
  // ===========================================================================

  // --- inversion / intro helpers for the tails (top-level, fuel-safe) ---

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

  // ===========================================================================
  // Range and entry lemmas
  // ===========================================================================

  // ===========================================================================
  // Edge inversion per pinned instruction
  // ===========================================================================

  // ===========================================================================
  // Chain-exit vocabulary and small intros
  // ===========================================================================

  // ===========================================================================
  // The step lemmas: every edge out of a mid-parse state stays mid-parse or
  // exits the block with a completed span
  // ===========================================================================

  // ===========================================================================
  // The program-level sweep: every reachable configuration of a build
  // program is in the dot-star zone, mid-parse in the body, or done
  // ===========================================================================

  // ===========================================================================
  // PathToMatches, assembled
  // ===========================================================================

  // ===========================================================================
  // THE L1 oracle characterization, per column
  // ===========================================================================

}
