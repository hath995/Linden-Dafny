// L4 depth-k, nested ORACLE ENTRY, rung V2 (the §6.3 decomposition, V-model):
// PathToMatchesV — a V-reachable recorder implies a GATED body match.
//
// The V-model clone of `OracleDecomp` over the NESTED fragment: the mid-parse
// invariant `InBlockV`, its step/entry/empty lemmas, and
// `ReachesWriteVToMatchesV`. Three systematic changes from the blind original:
//   - `Matches`/`InBlock` -> `MatchesV`/`InBlockV` with the partial view `ov`
//     threaded through, and `Re_lookaround` promoted from `false` to a
//     one-instruction mid-parse state (the gate pin), exactly like
//     `Re_character`.
//   - `ReachF`/`EpsEdge`/`AnyEdge` -> `ReachFV`/`EpsEdgeV`/`AnyEdgeV`. THE
//     point of the V-model: the gate edge's guard IS the lookaround's
//     `MatchesV` clause, so `BlockStepV`'s new case reads the bit off the
//     edge it was given.
//   - fragment: look-freedom dropped; `NestedFragmentRE` where nullability
//     shape facts are needed, plain `NfaRepRE` elsewhere.
// The code-shape predicates (`AltShape` .. `DoWhileShape`) are view-free and
// reused from `OracleDecomp` verbatim.
/** V2 of the nested oracle entry: `InBlockV`, `BlockStepV`, `ProgReachInvV`,
    and the decomposition direction `ReachesWriteVToMatchesV`. */
module LindenElkOracleDecompV {
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
  import OD = LindenElkOracleDecomp
  import OBV = LindenElkOracleBridgeV

  // ===========================================================================
  // Span-chain helpers (gated)
  // ===========================================================================

  /** Prepend a span to a chain. */
  lemma IterConsV(r: R.regex, k: nat, str: string, ov: LOr.OracleView, i: int, m: int, j: int)
    requires OBV.MatchesV(r, str, ov, i, m)
    requires OBV.MatchesIterV(r, k, str, ov, m, j)
    ensures OBV.MatchesIterV(r, k + 1, str, ov, i, j)
  {
  }

  /** Append a span to a chain. */
  lemma IterSnocV(r: R.regex, k: nat, str: string, ov: LOr.OracleView, i: int, m: int, j: int)
    requires OBV.MatchesIterV(r, k, str, ov, i, m)
    requires OBV.MatchesV(r, str, ov, m, j)
    ensures OBV.MatchesIterV(r, k + 1, str, ov, i, j)
    decreases k
  {
    if k == 0 { return; }
    var m1 := OBV.MatchesIterVHead(r, k, str, ov, i, m);
    IterSnocV(r, k - 1, str, ov, m1, m, j);
    IterConsV(r, k, str, ov, i, m1, j);
  }

  /** At least `n` spans lie between `i` and `m`. */
  ghost predicate IterFromV(r: R.regex, n: nat, str: string, ov: LOr.OracleView, i: int, m: int) {
    exists k: nat {:trigger OBV.MatchesIterV(r, k, str, ov, i, m)} ::
      n <= k && OBV.MatchesIterV(r, k, str, ov, i, m)
  }

  lemma IterFromZeroV(r: R.regex, str: string, ov: LOr.OracleView, i: int)
    ensures IterFromV(r, 0, str, ov, i, i)
  {
    assert OBV.MatchesIterV(r, 0, str, ov, i, i);
  }

  lemma IterFromInvV(r: R.regex, n: nat, str: string, ov: LOr.OracleView, i: int, m: int) returns (k: nat)
    requires IterFromV(r, n, str, ov, i, m)
    ensures n <= k && OBV.MatchesIterV(r, k, str, ov, i, m)
  {
    k :| n <= k && OBV.MatchesIterV(r, k, str, ov, i, m);
  }

  /** Append one span to an at-least-`n` chain. */
  lemma IterFromSnocV(r: R.regex, n: nat, str: string, ov: LOr.OracleView, i: int, m: int, j: int)
    requires IterFromV(r, n, str, ov, i, m)
    requires OBV.MatchesV(r, str, ov, m, j)
    ensures IterFromV(r, n, str, ov, i, j)
  {
    var k := IterFromInvV(r, n, str, ov, i, m);
    IterSnocV(r, k, str, ov, i, m, j);
    assert OBV.MatchesIterV(r, k + 1, str, ov, i, j);
  }

  lemma IterFromIntroV(r: R.regex, n: nat, k: nat, str: string, ov: LOr.OracleView, i: int, m: int)
    requires n <= k && OBV.MatchesIterV(r, k, str, ov, i, m)
    ensures IterFromV(r, n, str, ov, i, m)
  {
  }

  /** Concatenate two chains. */
  lemma IterConcatV(r: R.regex, a: nat, b: nat, str: string, ov: LOr.OracleView, i: int, m: int, j: int)
    requires OBV.MatchesIterV(r, a, str, ov, i, m)
    requires OBV.MatchesIterV(r, b, str, ov, m, j)
    ensures OBV.MatchesIterV(r, a + b, str, ov, i, j)
    decreases a
  {
    if a == 0 { return; }
    var m1 := OBV.MatchesIterVHead(r, a, str, ov, i, m);
    IterConcatV(r, a - 1, b, str, ov, m1, m, j);
    IterConsV(r, a + b - 1, str, ov, i, m1, j);
  }

  // ===========================================================================
  // The mid-parse invariant, gated (code shapes reused from OracleDecomp)
  // ===========================================================================

  /** The star arm's interior, gated. */
  ghost predicate StTailV(qid: R.quantid, r1: R.regex, code: RB.code, start: nat, es1: nat,
                          str: string, ov: LOr.OracleView, i: int, pc: nat, cp: int)
    decreases CP.rsize(r1), 3, 0
  {
    exists m: int {:trigger IterFromV(r1, 0, str, ov, i, m)} ::
      IterFromV(r1, 0, str, ov, i, m)
      && (((pc == start || pc == start + 1 || pc == start + 2) && cp == m)
          || InBlockV(r1, code, start + 3, es1, str, ov, m, pc, cp)
          || ((pc == es1 || pc == es1 + 1) && OBV.MatchesV(r1, str, ov, m, cp)))
  }

  /** The bounded arm's post-copies interior, gated. */
  ghost predicate BdTailV(mn: nat, kx: nat, greedy: bool, qid: R.quantid, r1: R.regex, code: RB.code,
                          em: nat, endl: nat, str: string, ov: LOr.OracleView, i: int, pc: nat, cp: int)
    decreases CP.rsize(r1), 3, 0
  {
    exists m: int {:trigger InOptV(kx, greedy, qid, r1, code, em, endl, str, ov, m, pc, cp)} ::
      OBV.MatchesIterV(r1, mn, str, ov, i, m)
      && InOptV(kx, greedy, qid, r1, code, em, endl, str, ov, m, pc, cp)
  }

  /** The do-while arm's looped interior, gated. */
  ghost predicate DwTailV(mn1: nat, qid: R.quantid, r1: R.regex, code: RB.code, em: nat, e1: nat,
                          str: string, ov: LOr.OracleView, i: int, pc: nat, cp: int)
    decreases CP.rsize(r1), 3, 0
  {
    exists m: int {:trigger IterFromV(r1, mn1, str, ov, i, m)} ::
      IterFromV(r1, mn1, str, ov, i, m)
      && ((pc == em && cp == m)
          || InBlockV(r1, code, em + 1, e1, str, ov, m, pc, cp)
          || (pc == e1 && OBV.MatchesV(r1, str, ov, m, cp)))
  }

  /** Configuration `(pc, cp)` is a legitimate mid-parse state of `re`'s block,
      entered at string position `i`, against the view `ov`. NEW versus the
      blind original: `Re_lookaround` is a one-instruction state (the gate
      pin), exactly like `Re_character`. */
  ghost predicate InBlockV(re: R.regex, code: RB.code, start: nat, endl: nat,
                           str: string, ov: LOr.OracleView, i: int, pc: nat, cp: int)
    decreases CP.rsize(re), 0, 0
  {
    match re
    case Re_empty => false
    case Re_lookaround(lid, la, r1) =>
      pc == start && cp == i && endl == start + 1
      && NR.GetPcRE(code, start) == Some(if la.Lookahead? || la.Lookbehind?
                                         then RB.CheckOracle(lid)
                                         else RB.NegCheckOracle(lid))
    case Re_character(ch) =>
      pc == start && cp == i && endl == start + 1
      && NR.GetPcRE(code, start) == Some(RB.Consume(T.ExpectationOf(ch)))
    case Re_anchor(a) =>
      pc == start && cp == i && endl == start + 1
      && NR.GetPcRE(code, start) == Some(RB.AnchorAssertion(a))
    case Re_alt(r1, r2) =>
      exists e1: nat {:trigger OD.AltShape(r1, r2, code, start, e1, endl)} ::
        OD.AltShape(r1, r2, code, start, e1, endl)
        && ((pc == start && cp == i)
            || InBlockV(r1, code, start + 1, e1, str, ov, i, pc, cp)
            || (pc == e1 && OBV.MatchesV(r1, str, ov, i, cp))
            || InBlockV(r2, code, e1 + 1, endl, str, ov, i, pc, cp))
    case Re_con(r1, r2) =>
      exists e1: nat {:trigger OD.ConShape(r1, r2, code, start, e1, endl)} ::
        OD.ConShape(r1, r2, code, start, e1, endl)
        && (InBlockV(r1, code, start, e1, str, ov, i, pc, cp)
            || exists m: int {:trigger InBlockV(r2, code, e1, endl, str, ov, m, pc, cp)} ::
                 OBV.MatchesV(r1, str, ov, i, m) && InBlockV(r2, code, e1, endl, str, ov, m, pc, cp))
    case Re_capture(cid, r1) =>
      exists e1: nat {:trigger OD.CapShape(cid, r1, code, start, e1, endl)} ::
        OD.CapShape(cid, r1, code, start, e1, endl)
        && ((pc == start && cp == i)
            || InBlockV(r1, code, start + 1, e1, str, ov, i, pc, cp)
            || (pc == e1 && OBV.MatchesV(r1, str, ov, i, cp)))
    case Re_quant(nul, qid, q, r1) =>
      if q.min == 0 && q.max == None then
        exists es1: nat {:trigger OD.StarShape(qid, r1, code, start, es1, endl)} ::
          OD.StarShape(qid, r1, code, start, es1, endl)
          && StTailV(qid, r1, code, start, es1, str, ov, i, pc, cp)
      else if q.max.Some? then
        0 <= q.min && q.min <= q.max.value
        && exists em: nat {:trigger NR.NfaRepOptRE((q.max.value - q.min) as nat, q.greedy, qid, r1, code, em, endl)} ::
             NR.NfaRepMinRE(q.min as nat, qid, r1, code, start, em)
             && NR.NfaRepOptRE((q.max.value - q.min) as nat, q.greedy, qid, r1, code, em, endl)
             && (InMinV(q.min as nat, qid, r1, code, start, em, str, ov, i, pc, cp)
                 || BdTailV(q.min as nat, (q.max.value - q.min) as nat, q.greedy, qid, r1, code, em, endl, str, ov, i, pc, cp))
      else
        q.min > 0
        && exists em: nat, e1: nat {:trigger OD.DoWhileShape(qid, r1, code, em, e1, endl)} ::
             NR.NfaRepMinRE((q.min - 1) as nat, qid, r1, code, start, em)
             && OD.DoWhileShape(qid, r1, code, em, e1, endl)
             && (InMinV((q.min - 1) as nat, qid, r1, code, start, em, str, ov, i, pc, cp)
                 || DwTailV((q.min - 1) as nat, qid, r1, code, em, e1, str, ov, i, pc, cp))
  }

  // --- inversion / intro helpers for the tails ---

  lemma StTailVInv(qid: R.quantid, r1: R.regex, code: RB.code, start: nat, es1: nat,
                   str: string, ov: LOr.OracleView, i: int, pc: nat, cp: int) returns (m: int)
    requires StTailV(qid, r1, code, start, es1, str, ov, i, pc, cp)
    ensures IterFromV(r1, 0, str, ov, i, m)
    ensures ((pc == start || pc == start + 1 || pc == start + 2) && cp == m)
         || InBlockV(r1, code, start + 3, es1, str, ov, m, pc, cp)
         || ((pc == es1 || pc == es1 + 1) && OBV.MatchesV(r1, str, ov, m, cp))
  {
    m :| IterFromV(r1, 0, str, ov, i, m)
      && (((pc == start || pc == start + 1 || pc == start + 2) && cp == m)
          || InBlockV(r1, code, start + 3, es1, str, ov, m, pc, cp)
          || ((pc == es1 || pc == es1 + 1) && OBV.MatchesV(r1, str, ov, m, cp)));
  }

  lemma StTailVIntro(qid: R.quantid, r1: R.regex, code: RB.code, start: nat, es1: nat,
                     str: string, ov: LOr.OracleView, i: int, pc: nat, cp: int, m: int)
    requires IterFromV(r1, 0, str, ov, i, m)
    requires ((pc == start || pc == start + 1 || pc == start + 2) && cp == m)
          || InBlockV(r1, code, start + 3, es1, str, ov, m, pc, cp)
          || ((pc == es1 || pc == es1 + 1) && OBV.MatchesV(r1, str, ov, m, cp))
    ensures StTailV(qid, r1, code, start, es1, str, ov, i, pc, cp)
  {
  }

  lemma BdTailVInv(mn: nat, kx: nat, greedy: bool, qid: R.quantid, r1: R.regex, code: RB.code,
                   em: nat, endl: nat, str: string, ov: LOr.OracleView, i: int, pc: nat, cp: int) returns (m: int)
    requires BdTailV(mn, kx, greedy, qid, r1, code, em, endl, str, ov, i, pc, cp)
    ensures OBV.MatchesIterV(r1, mn, str, ov, i, m)
    ensures InOptV(kx, greedy, qid, r1, code, em, endl, str, ov, m, pc, cp)
  {
    m :| OBV.MatchesIterV(r1, mn, str, ov, i, m)
      && InOptV(kx, greedy, qid, r1, code, em, endl, str, ov, m, pc, cp);
  }

  lemma BdTailVIntro(mn: nat, kx: nat, greedy: bool, qid: R.quantid, r1: R.regex, code: RB.code,
                     em: nat, endl: nat, str: string, ov: LOr.OracleView, i: int, pc: nat, cp: int, m: int)
    requires OBV.MatchesIterV(r1, mn, str, ov, i, m)
    requires InOptV(kx, greedy, qid, r1, code, em, endl, str, ov, m, pc, cp)
    ensures BdTailV(mn, kx, greedy, qid, r1, code, em, endl, str, ov, i, pc, cp)
  {
  }

  lemma DwTailVInv(mn1: nat, qid: R.quantid, r1: R.regex, code: RB.code, em: nat, e1: nat,
                   str: string, ov: LOr.OracleView, i: int, pc: nat, cp: int) returns (m: int)
    requires DwTailV(mn1, qid, r1, code, em, e1, str, ov, i, pc, cp)
    ensures IterFromV(r1, mn1, str, ov, i, m)
    ensures (pc == em && cp == m)
         || InBlockV(r1, code, em + 1, e1, str, ov, m, pc, cp)
         || (pc == e1 && OBV.MatchesV(r1, str, ov, m, cp))
  {
    m :| IterFromV(r1, mn1, str, ov, i, m)
      && ((pc == em && cp == m)
          || InBlockV(r1, code, em + 1, e1, str, ov, m, pc, cp)
          || (pc == e1 && OBV.MatchesV(r1, str, ov, m, cp)));
  }

  lemma DwTailVIntro(mn1: nat, qid: R.quantid, r1: R.regex, code: RB.code, em: nat, e1: nat,
                     str: string, ov: LOr.OracleView, i: int, pc: nat, cp: int, m: int)
    requires IterFromV(r1, mn1, str, ov, i, m)
    requires (pc == em && cp == m)
          || InBlockV(r1, code, em + 1, e1, str, ov, m, pc, cp)
          || (pc == e1 && OBV.MatchesV(r1, str, ov, m, cp))
    ensures DwTailV(mn1, qid, r1, code, em, e1, str, ov, i, pc, cp)
  {
  }

  /** `InBlockV` for the forced-copy chain. */
  ghost predicate InMinV(k: nat, qid: R.quantid, r1: R.regex, code: RB.code,
                         start: nat, endl: nat, str: string, ov: LOr.OracleView, j: int, pc: nat, cp: int)
    decreases CP.rsize(r1), 1, k
  {
    k > 0
    && exists e1: nat {:trigger OD.MinShape(k, qid, r1, code, start, e1, endl)} ::
         OD.MinShape(k, qid, r1, code, start, e1, endl)
         && ((pc == start && cp == j)
             || InBlockV(r1, code, start + 1, e1, str, ov, j, pc, cp)
             || exists m: int {:trigger InMinV(k - 1, qid, r1, code, e1, endl, str, ov, m, pc, cp)} ::
                  OBV.MatchesV(r1, str, ov, j, m) && InMinV(k - 1, qid, r1, code, e1, endl, str, ov, m, pc, cp))
  }

  /** `InBlockV` for the optional-layer chain. */
  ghost predicate InOptV(layers: nat, greedy: bool, qid: R.quantid, r1: R.regex, code: RB.code,
                         start: nat, endl: nat, str: string, ov: LOr.OracleView, j: int, pc: nat, cp: int)
    decreases CP.rsize(r1), 2, layers
  {
    layers > 0
    && exists e1: nat {:trigger OD.OptShape(layers, greedy, qid, r1, code, start, e1, endl)} ::
         OD.OptShape(layers, greedy, qid, r1, code, start, e1, endl)
         && (((pc == start || pc == start + 1 || pc == start + 2) && cp == j)
             || InBlockV(r1, code, start + 3, e1, str, ov, j, pc, cp)
             || (pc == e1 && OBV.MatchesV(r1, str, ov, j, cp))
             || exists m: int {:trigger InOptV(layers - 1, greedy, qid, r1, code, e1 + 1, endl, str, ov, m, pc, cp)} ::
                  OBV.MatchesV(r1, str, ov, j, m)
                  && InOptV(layers - 1, greedy, qid, r1, code, e1 + 1, endl, str, ov, m, pc, cp))
  }

  // ===========================================================================
  // Empty-block facts (zero-chain facts reused from OracleDecomp)
  // ===========================================================================

  /** An empty block means an empty-capable regex, gated: `MatchesV(re, p, p)`
      at every position. A lookaround block is never empty (one instruction),
      so the new case is vacuous. */
  lemma BlockEmptyV(re: R.regex, code: RB.code, start: nat, str: string, ov: LOr.OracleView, p: int)
    requires NR.NfaRepRE(re, code, start, start)
    ensures OBV.MatchesV(re, str, ov, p, p)
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
      BlockEmptyV(r1, code, start, str, ov, p);
      BlockEmptyV(r2, code, start, str, ov, p);
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
        OD.MinEmptyCount(q.min as nat, qid, r1, code, start);
        OD.OptEmptyCount((q.max.value - q.min) as nat, q.greedy, qid, r1, code, start);
        assert q.min == 0;
        assert OBV.MatchesIterV(r1, 0, str, ov, p, p);
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
  lemma InBlockVRange(re: R.regex, code: RB.code, start: nat, endl: nat,
                      str: string, ov: LOr.OracleView, i: int, pc: nat, cp: int)
    requires InBlockV(re, code, start, endl, str, ov, i, pc, cp)
    ensures start <= pc < endl
    decreases CP.rsize(re), 0, 0
  {
    match re
    case Re_empty => case Re_lookaround(_, _, _) =>
    case Re_character(_) => case Re_anchor(_) =>
    case Re_alt(r1, r2) =>
      var e1: nat :| OD.AltShape(r1, r2, code, start, e1, endl)
        && ((pc == start && cp == i)
            || InBlockV(r1, code, start + 1, e1, str, ov, i, pc, cp)
            || (pc == e1 && OBV.MatchesV(r1, str, ov, i, cp))
            || InBlockV(r2, code, e1 + 1, endl, str, ov, i, pc, cp));
      NR.NfaRepIncrRE(r1, code, start + 1, e1);
      NR.NfaRepIncrRE(r2, code, e1 + 1, endl);
      if InBlockV(r1, code, start + 1, e1, str, ov, i, pc, cp) {
        InBlockVRange(r1, code, start + 1, e1, str, ov, i, pc, cp);
      } else if InBlockV(r2, code, e1 + 1, endl, str, ov, i, pc, cp) {
        InBlockVRange(r2, code, e1 + 1, endl, str, ov, i, pc, cp);
      }
    case Re_con(r1, r2) =>
      var e1: nat :| OD.ConShape(r1, r2, code, start, e1, endl)
        && (InBlockV(r1, code, start, e1, str, ov, i, pc, cp)
            || exists m: int :: OBV.MatchesV(r1, str, ov, i, m) && InBlockV(r2, code, e1, endl, str, ov, m, pc, cp));
      NR.NfaRepIncrRE(r1, code, start, e1);
      NR.NfaRepIncrRE(r2, code, e1, endl);
      if InBlockV(r1, code, start, e1, str, ov, i, pc, cp) {
        InBlockVRange(r1, code, start, e1, str, ov, i, pc, cp);
      } else {
        var m: int :| OBV.MatchesV(r1, str, ov, i, m) && InBlockV(r2, code, e1, endl, str, ov, m, pc, cp);
        InBlockVRange(r2, code, e1, endl, str, ov, m, pc, cp);
      }
    case Re_capture(cid, r1) =>
      var e1: nat :| OD.CapShape(cid, r1, code, start, e1, endl)
        && ((pc == start && cp == i)
            || InBlockV(r1, code, start + 1, e1, str, ov, i, pc, cp)
            || (pc == e1 && OBV.MatchesV(r1, str, ov, i, cp)));
      NR.NfaRepIncrRE(r1, code, start + 1, e1);
      if InBlockV(r1, code, start + 1, e1, str, ov, i, pc, cp) {
        InBlockVRange(r1, code, start + 1, e1, str, ov, i, pc, cp);
      }
    case Re_quant(nul, qid, q, r1) =>
      if q.min == 0 && q.max == None {
        var es1: nat :| OD.StarShape(qid, r1, code, start, es1, endl)
          && StTailV(qid, r1, code, start, es1, str, ov, i, pc, cp);
        var m := StTailVInv(qid, r1, code, start, es1, str, ov, i, pc, cp);
        NR.NfaRepIncrRE(r1, code, start + 3, es1);
        if InBlockV(r1, code, start + 3, es1, str, ov, m, pc, cp) {
          InBlockVRange(r1, code, start + 3, es1, str, ov, m, pc, cp);
        }
      } else if q.max.Some? {
        var em: nat :|
          NR.NfaRepMinRE(q.min as nat, qid, r1, code, start, em)
          && NR.NfaRepOptRE((q.max.value - q.min) as nat, q.greedy, qid, r1, code, em, endl)
          && (InMinV(q.min as nat, qid, r1, code, start, em, str, ov, i, pc, cp)
              || BdTailV(q.min as nat, (q.max.value - q.min) as nat, q.greedy, qid, r1, code, em, endl, str, ov, i, pc, cp));
        NR.NfaRepIncrMinRE(q.min as nat, qid, r1, code, start, em);
        NR.NfaRepIncrOptRE((q.max.value - q.min) as nat, q.greedy, qid, r1, code, em, endl);
        if InMinV(q.min as nat, qid, r1, code, start, em, str, ov, i, pc, cp) {
          InMinVRange(q.min as nat, qid, r1, code, start, em, str, ov, i, pc, cp);
        } else {
          var m := BdTailVInv(q.min as nat, (q.max.value - q.min) as nat, q.greedy, qid, r1, code, em, endl, str, ov, i, pc, cp);
          InOptVRange((q.max.value - q.min) as nat, q.greedy, qid, r1, code, em, endl, str, ov, m, pc, cp);
        }
      } else {
        var em: nat, e1: nat :|
          NR.NfaRepMinRE((q.min - 1) as nat, qid, r1, code, start, em)
          && OD.DoWhileShape(qid, r1, code, em, e1, endl)
          && (InMinV((q.min - 1) as nat, qid, r1, code, start, em, str, ov, i, pc, cp)
              || DwTailV((q.min - 1) as nat, qid, r1, code, em, e1, str, ov, i, pc, cp));
        NR.NfaRepIncrMinRE((q.min - 1) as nat, qid, r1, code, start, em);
        NR.NfaRepIncrRE(r1, code, em + 1, e1);
        if InMinV((q.min - 1) as nat, qid, r1, code, start, em, str, ov, i, pc, cp) {
          InMinVRange((q.min - 1) as nat, qid, r1, code, start, em, str, ov, i, pc, cp);
        } else {
          var m := DwTailVInv((q.min - 1) as nat, qid, r1, code, em, e1, str, ov, i, pc, cp);
          if InBlockV(r1, code, em + 1, e1, str, ov, m, pc, cp) {
            InBlockVRange(r1, code, em + 1, e1, str, ov, m, pc, cp);
          }
        }
      }
  }

  /** `InBlockVRange` for the forced-copy chain. */
  lemma InMinVRange(k: nat, qid: R.quantid, r1: R.regex, code: RB.code,
                    start: nat, endl: nat, str: string, ov: LOr.OracleView, j: int, pc: nat, cp: int)
    requires InMinV(k, qid, r1, code, start, endl, str, ov, j, pc, cp)
    ensures start <= pc < endl
    decreases CP.rsize(r1), 1, k
  {
    var e1: nat :| OD.MinShape(k, qid, r1, code, start, e1, endl)
      && ((pc == start && cp == j)
          || InBlockV(r1, code, start + 1, e1, str, ov, j, pc, cp)
          || exists m: int :: OBV.MatchesV(r1, str, ov, j, m) && InMinV(k - 1, qid, r1, code, e1, endl, str, ov, m, pc, cp));
    NR.NfaRepIncrRE(r1, code, start + 1, e1);
    NR.NfaRepIncrMinRE(k - 1, qid, r1, code, e1, endl);
    if pc == start && cp == j {
    } else if InBlockV(r1, code, start + 1, e1, str, ov, j, pc, cp) {
      InBlockVRange(r1, code, start + 1, e1, str, ov, j, pc, cp);
    } else {
      var m: int :| OBV.MatchesV(r1, str, ov, j, m) && InMinV(k - 1, qid, r1, code, e1, endl, str, ov, m, pc, cp);
      InMinVRange(k - 1, qid, r1, code, e1, endl, str, ov, m, pc, cp);
    }
  }

  /** `InBlockVRange` for the optional-layer chain. */
  lemma InOptVRange(layers: nat, greedy: bool, qid: R.quantid, r1: R.regex, code: RB.code,
                    start: nat, endl: nat, str: string, ov: LOr.OracleView, j: int, pc: nat, cp: int)
    requires InOptV(layers, greedy, qid, r1, code, start, endl, str, ov, j, pc, cp)
    ensures start <= pc < endl
    decreases CP.rsize(r1), 2, layers
  {
    var e1: nat :| OD.OptShape(layers, greedy, qid, r1, code, start, e1, endl)
      && (((pc == start || pc == start + 1 || pc == start + 2) && cp == j)
          || InBlockV(r1, code, start + 3, e1, str, ov, j, pc, cp)
          || (pc == e1 && OBV.MatchesV(r1, str, ov, j, cp))
          || exists m: int ::
               OBV.MatchesV(r1, str, ov, j, m)
               && InOptV(layers - 1, greedy, qid, r1, code, e1 + 1, endl, str, ov, m, pc, cp));
    NR.NfaRepIncrRE(r1, code, start + 3, e1);
    NR.NfaRepIncrOptRE(layers - 1, greedy, qid, r1, code, e1 + 1, endl);
    if (pc == start || pc == start + 1 || pc == start + 2) && cp == j {
    } else if InBlockV(r1, code, start + 3, e1, str, ov, j, pc, cp) {
      InBlockVRange(r1, code, start + 3, e1, str, ov, j, pc, cp);
    } else if pc == e1 && OBV.MatchesV(r1, str, ov, j, cp) {
    } else {
      var m: int :| OBV.MatchesV(r1, str, ov, j, m)
        && InOptV(layers - 1, greedy, qid, r1, code, e1 + 1, endl, str, ov, m, pc, cp);
      InOptVRange(layers - 1, greedy, qid, r1, code, e1 + 1, endl, str, ov, m, pc, cp);
    }
  }

  /** `BlockEntryV` for a nonempty forced-copy chain. */
  lemma MinEntryV(k: nat, qid: R.quantid, r1: R.regex, code: RB.code,
                  start: nat, endl: nat, str: string, ov: LOr.OracleView, cp: int)
    requires k > 0
    requires NR.NfaRepMinRE(k, qid, r1, code, start, endl)
    ensures InMinV(k, qid, r1, code, start, endl, str, ov, cp, start, cp)
  {
    var e1: nat :| NR.GetPcRE(code, start) == Some(RB.SetQuantToClock(qid, false))
      && NR.NfaRepRE(r1, code, start + 1, e1)
      && NR.NfaRepMinRE(k - 1, qid, r1, code, e1, endl);
    assert OD.MinShape(k, qid, r1, code, start, e1, endl);
  }

  /** `BlockEntryV` for a nonempty optional-layer chain. */
  lemma OptEntryV(k: nat, greedy: bool, qid: R.quantid, r1: R.regex, code: RB.code,
                  start: nat, endl: nat, str: string, ov: LOr.OracleView, cp: int)
    requires k > 0
    requires NR.NfaRepOptRE(k, greedy, qid, r1, code, start, endl)
    ensures InOptV(k, greedy, qid, r1, code, start, endl, str, ov, cp, start, cp)
  {
    var e1: nat :| NR.GetPcRE(code, start) == Some(if greedy then RB.Fork(start + 1, endl as int) else RB.Fork(endl as int, start + 1))
      && NR.GetPcRE(code, start + 1) == Some(RB.SetQuantToClock(qid, false))
      && NR.GetPcRE(code, start + 2) == Some(RB.BeginLoop)
      && NR.NfaRepRE(r1, code, start + 3, e1)
      && NR.GetPcRE(code, e1) == Some(RB.EndLoop)
      && NR.NfaRepOptRE(k - 1, greedy, qid, r1, code, e1 + 1, endl);
    assert OD.OptShape(k, greedy, qid, r1, code, start, e1, endl);
  }

  /** Entering a nonempty block at its start label is a mid-parse state (an
      empty block has no mid states — pair with `BlockEmptyV`). Look-freedom
      is NOT needed: a lookaround block enters onto its own gate pin. */
  lemma BlockEntryV(re: R.regex, code: RB.code, start: nat, endl: nat, str: string, ov: LOr.OracleView, cp: int)
    requires NR.NfaRepRE(re, code, start, endl)
    ensures InBlockV(re, code, start, endl, str, ov, cp, start, cp) || start == endl
    decreases CP.rsize(re), 0, 0
  {
    match re
    case Re_empty =>
    case Re_lookaround(lid, la, r1) =>
      assert InBlockV(re, code, start, endl, str, ov, cp, start, cp);
    case Re_character(_) =>
    case Re_anchor(_) =>
    case Re_alt(r1, r2) =>
      var e1: nat :| NR.GetPcRE(code, start) == Some(RB.Fork(start + 1, e1 + 1))
        && NR.NfaRepRE(r1, code, start + 1, e1)
        && NR.GetPcRE(code, e1) == Some(RB.Jmp(endl as int))
        && NR.NfaRepRE(r2, code, e1 + 1, endl);
      assert OD.AltShape(r1, r2, code, start, e1, endl);
      assert InBlockV(re, code, start, endl, str, ov, cp, start, cp);
    case Re_con(r1, r2) =>
      var e1: nat :| NR.NfaRepRE(r1, code, start, e1) && NR.NfaRepRE(r2, code, e1, endl);
      assert OD.ConShape(r1, r2, code, start, e1, endl);
      BlockEntryV(r1, code, start, e1, str, ov, cp);
      if start == e1 {
        BlockEmptyV(r1, code, start, str, ov, cp);
        BlockEntryV(r2, code, e1, endl, str, ov, cp);
        if e1 == endl {
        } else {
          assert OBV.MatchesV(r1, str, ov, cp, cp) && InBlockV(r2, code, e1, endl, str, ov, cp, start, cp);
          assert InBlockV(re, code, start, endl, str, ov, cp, start, cp);
        }
      } else {
        assert InBlockV(r1, code, start, e1, str, ov, cp, start, cp);
        assert InBlockV(re, code, start, endl, str, ov, cp, start, cp);
      }
    case Re_capture(cid, r1) =>
      var e1: nat :| NR.GetPcRE(code, start) == Some(RB.SetRegisterToCP(CP.start_reg(cid)))
        && NR.NfaRepRE(r1, code, start + 1, e1)
        && NR.GetPcRE(code, e1) == Some(RB.SetRegisterToCP(CP.end_reg(cid)))
        && endl == e1 + 1;
      assert OD.CapShape(cid, r1, code, start, e1, endl);
      assert InBlockV(re, code, start, endl, str, ov, cp, start, cp);
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
        assert OD.StarShape(qid, r1, code, start, es1, endl);
        IterFromZeroV(r1, str, ov, cp);
        StTailVIntro(qid, r1, code, start, es1, str, ov, cp, start, cp, cp);
        assert InBlockV(re, code, start, endl, str, ov, cp, start, cp);
      } else if q.max.Some? {
        var em := NR.NfaRepREQuantInv(nul, qid, q, r1, code, start, endl);
        if q.min as nat > 0 {
          MinEntryV(q.min as nat, qid, r1, code, start, em, str, ov, cp);
          assert InBlockV(re, code, start, endl, str, ov, cp, start, cp);
        } else {
          OD.MinZeroSame(qid, r1, code, start, em);
          if (q.max.value - q.min) as nat > 0 {
            OptEntryV((q.max.value - q.min) as nat, q.greedy, qid, r1, code, em, endl, str, ov, cp);
            assert OBV.MatchesIterV(r1, 0, str, ov, cp, cp);
            BdTailVIntro(q.min as nat, (q.max.value - q.min) as nat, q.greedy, qid, r1, code, em, endl, str, ov, cp, start, cp, cp);
            assert InBlockV(re, code, start, endl, str, ov, cp, start, cp);
          } else {
            OD.OptZeroSame(q.greedy, qid, r1, code, em, endl);
          }
        }
      } else {
        var em, e1 := NR.NfaRepREPlusInv(nul, qid, q, r1, code, start, endl);
        assert OD.DoWhileShape(qid, r1, code, em, e1, endl);
        if (q.min - 1) as nat > 0 {
          MinEntryV((q.min - 1) as nat, qid, r1, code, start, em, str, ov, cp);
          assert InBlockV(re, code, start, endl, str, ov, cp, start, cp);
        } else {
          OD.MinZeroSame(qid, r1, code, start, em);
          IterFromZeroV(r1, str, ov, cp);
          DwTailVIntro((q.min - 1) as nat, qid, r1, code, em, e1, str, ov, cp, start, cp, cp);
          assert InBlockV(re, code, start, endl, str, ov, cp, start, cp);
        }
      }
  }

  // ===========================================================================
  // Edge inversion, V (the gate cases are the NEW content)
  // ===========================================================================

  /** Any one V configuration-graph step. */
  ghost predicate AnyEdgeV(code: RB.code, str: string, ov: LOr.OracleView, pc: nat, eb: bool, cp: int,
                           pc2: nat, eb2: bool, cp2: int) {
    (ORc.EpsEdgeV(code, str, ov, cp, pc, eb, pc2, eb2) && cp2 == cp)
    || (ORc.ConsumeEdge(code, str, cp, pc) && pc2 == pc + 1 && eb2 == true && cp2 == cp + 1)
  }

  lemma EdgeFromConsumeV(code: RB.code, str: string, ov: LOr.OracleView, ce: RC.char_expectation,
                         pc: nat, eb: bool, cp: int, pc2: nat, eb2: bool, cp2: int)
    requires NR.GetPcRE(code, pc) == Some(RB.Consume(ce))
    requires AnyEdgeV(code, str, ov, pc, eb, cp, pc2, eb2, cp2)
    ensures pc2 == pc + 1 && eb2 == true && cp2 == cp + 1
    ensures RC.is_accepted(AI.get_char(str, cp), ce)
  {
    OB.GetPcInstr(code, pc, RB.Consume(ce));
  }

  lemma EdgeFromJmpV(code: RB.code, str: string, ov: LOr.OracleView, x: int,
                     pc: nat, eb: bool, cp: int, pc2: nat, eb2: bool, cp2: int)
    requires NR.GetPcRE(code, pc) == Some(RB.Jmp(x))
    requires AnyEdgeV(code, str, ov, pc, eb, cp, pc2, eb2, cp2)
    ensures x >= 0 && pc2 == x && eb2 == eb && cp2 == cp
  {
    OB.GetPcInstr(code, pc, RB.Jmp(x));
  }

  lemma EdgeFromForkAtV(code: RB.code, str: string, ov: LOr.OracleView, a: nat, b: nat,
                        pc: nat, eb: bool, cp: int, pc2: nat, eb2: bool, cp2: int)
    requires OB.ForkAt(code, pc, a, b)
    requires AnyEdgeV(code, str, ov, pc, eb, cp, pc2, eb2, cp2)
    ensures (pc2 == a || pc2 == b) && eb2 == eb && cp2 == cp
  {
    if NR.GetPcRE(code, pc) == Some(RB.Fork(a as int, b as int)) {
      OB.GetPcInstr(code, pc, RB.Fork(a as int, b as int));
    } else {
      OB.GetPcInstr(code, pc, RB.Fork(b as int, a as int));
    }
  }

  lemma EdgeFromSetRegV(code: RB.code, str: string, ov: LOr.OracleView, reg: RB.Register,
                        pc: nat, eb: bool, cp: int, pc2: nat, eb2: bool, cp2: int)
    requires NR.GetPcRE(code, pc) == Some(RB.SetRegisterToCP(reg))
    requires AnyEdgeV(code, str, ov, pc, eb, cp, pc2, eb2, cp2)
    ensures pc2 == pc + 1 && eb2 == eb && cp2 == cp
  {
    OB.GetPcInstr(code, pc, RB.SetRegisterToCP(reg));
  }

  lemma EdgeFromSetQuantV(code: RB.code, str: string, ov: LOr.OracleView, q: R.quantid, b: bool,
                          pc: nat, eb: bool, cp: int, pc2: nat, eb2: bool, cp2: int)
    requires NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(q, b))
    requires AnyEdgeV(code, str, ov, pc, eb, cp, pc2, eb2, cp2)
    ensures pc2 == pc + 1 && eb2 == eb && cp2 == cp
  {
    OB.GetPcInstr(code, pc, RB.SetQuantToClock(q, b));
  }

  lemma EdgeFromBeginLoopV(code: RB.code, str: string, ov: LOr.OracleView,
                           pc: nat, eb: bool, cp: int, pc2: nat, eb2: bool, cp2: int)
    requires NR.GetPcRE(code, pc) == Some(RB.BeginLoop)
    requires AnyEdgeV(code, str, ov, pc, eb, cp, pc2, eb2, cp2)
    ensures pc2 == pc + 1 && eb2 == false && cp2 == cp
  {
    OB.GetPcInstr(code, pc, RB.BeginLoop);
  }

  lemma EdgeFromEndLoopV(code: RB.code, str: string, ov: LOr.OracleView,
                         pc: nat, eb: bool, cp: int, pc2: nat, eb2: bool, cp2: int)
    requires NR.GetPcRE(code, pc) == Some(RB.EndLoop)
    requires AnyEdgeV(code, str, ov, pc, eb, cp, pc2, eb2, cp2)
    ensures pc2 == pc + 1 && eb2 == eb && cp2 == cp
  {
    OB.GetPcInstr(code, pc, RB.EndLoop);
  }

  lemma EdgeFromAnchorV(code: RB.code, str: string, ov: LOr.OracleView, a: R.anchor,
                        pc: nat, eb: bool, cp: int, pc2: nat, eb2: bool, cp2: int)
    requires NR.GetPcRE(code, pc) == Some(RB.AnchorAssertion(a))
    requires AnyEdgeV(code, str, ov, pc, eb, cp, pc2, eb2, cp2)
    ensures pc2 == pc + 1 && eb2 == eb && cp2 == cp
    ensures LAnc.is_satisfied(a, ORc.CtxAt(str, cp), LAnc.Forward)
  {
    OB.GetPcInstr(code, pc, RB.AnchorAssertion(a));
  }

  /** THE gate inversion, positive: the only V edge out of a `CheckOracle` is
      the eps step to `pc + 1`, and it CARRIES the bit. */
  lemma EdgeFromCheckOracleV(code: RB.code, str: string, ov: LOr.OracleView, l: R.lookid,
                             pc: nat, eb: bool, cp: int, pc2: nat, eb2: bool, cp2: int)
    requires NR.GetPcRE(code, pc) == Some(RB.CheckOracle(l))
    requires AnyEdgeV(code, str, ov, pc, eb, cp, pc2, eb2, cp2)
    ensures pc2 == pc + 1 && eb2 == eb && cp2 == cp
    ensures LOr.view_get_oracle(ov, cp, l)
  {
    OB.GetPcInstr(code, pc, RB.CheckOracle(l));
  }

  /** THE gate inversion, negative. */
  lemma EdgeFromNegCheckOracleV(code: RB.code, str: string, ov: LOr.OracleView, l: R.lookid,
                                pc: nat, eb: bool, cp: int, pc2: nat, eb2: bool, cp2: int)
    requires NR.GetPcRE(code, pc) == Some(RB.NegCheckOracle(l))
    requires AnyEdgeV(code, str, ov, pc, eb, cp, pc2, eb2, cp2)
    ensures pc2 == pc + 1 && eb2 == eb && cp2 == cp
    ensures !LOr.view_get_oracle(ov, cp, l)
  {
    OB.GetPcInstr(code, pc, RB.NegCheckOracle(l));
  }

  // ===========================================================================
  // Chain-exit vocabulary
  // ===========================================================================

  /** The optional-layer chain completed with at most `layers` spans. */
  ghost predicate OptDoneV(layers: nat, r1: R.regex, str: string, ov: LOr.OracleView, j: int, cp2: int) {
    exists k: nat {:trigger OBV.MatchesIterV(r1, k, str, ov, j, cp2)} ::
      k <= layers && OBV.MatchesIterV(r1, k, str, ov, j, cp2)
  }

  lemma OptDoneVIntro(layers: nat, r1: R.regex, str: string, ov: LOr.OracleView, j: int, cp2: int, k: nat)
    requires k <= layers && OBV.MatchesIterV(r1, k, str, ov, j, cp2)
    ensures OptDoneV(layers, r1, str, ov, j, cp2)
  {
  }

  lemma OptDoneVInv(layers: nat, r1: R.regex, str: string, ov: LOr.OracleView, j: int, cp2: int) returns (k: nat)
    requires OptDoneV(layers, r1, str, ov, j, cp2)
    ensures k <= layers && OBV.MatchesIterV(r1, k, str, ov, j, cp2)
  {
    k :| k <= layers && OBV.MatchesIterV(r1, k, str, ov, j, cp2);
  }

  // ===========================================================================
  // The step lemmas
  // ===========================================================================

  /** `BlockStepV` for the forced-copy chain. */
  lemma BlockStepMinV(k: nat, qid: R.quantid, r1: R.regex, code: RB.code,
                      start: nat, endl: nat, str: string, ov: LOr.OracleView, j: int,
                      pc: nat, eb: bool, cp: int, pc2: nat, eb2: bool, cp2: int)
    requires InMinV(k, qid, r1, code, start, endl, str, ov, j, pc, cp)
    requires AnyEdgeV(code, str, ov, pc, eb, cp, pc2, eb2, cp2)
    ensures InMinV(k, qid, r1, code, start, endl, str, ov, j, pc2, cp2)
         || (pc2 == endl && OBV.MatchesIterV(r1, k, str, ov, j, cp2))
    decreases CP.rsize(r1), 1, k
  {
    var e1: nat :| OD.MinShape(k, qid, r1, code, start, e1, endl)
      && ((pc == start && cp == j)
          || InBlockV(r1, code, start + 1, e1, str, ov, j, pc, cp)
          || exists m: int :: OBV.MatchesV(r1, str, ov, j, m) && InMinV(k - 1, qid, r1, code, e1, endl, str, ov, m, pc, cp));
    if pc == start && cp == j {
      EdgeFromSetQuantV(code, str, ov, qid, false, pc, eb, cp, pc2, eb2, cp2);
      BlockEntryV(r1, code, start + 1, e1, str, ov, j);
      if start + 1 == e1 {
        BlockEmptyV(r1, code, start + 1, str, ov, j);
        if k - 1 > 0 {
          MinEntryV(k - 1, qid, r1, code, e1, endl, str, ov, j);
          assert InMinV(k, qid, r1, code, start, endl, str, ov, j, pc2, cp2);
        } else {
          OD.MinZeroSame(qid, r1, code, e1, endl);
          IterConsV(r1, 0, str, ov, j, j, j);
          assert pc2 == endl && OBV.MatchesIterV(r1, k, str, ov, j, cp2);
        }
      } else {
        assert InBlockV(r1, code, start + 1, e1, str, ov, j, pc2, cp2);
        assert InMinV(k, qid, r1, code, start, endl, str, ov, j, pc2, cp2);
      }
    } else if InBlockV(r1, code, start + 1, e1, str, ov, j, pc, cp) {
      BlockStepV(r1, code, start + 1, e1, str, ov, j, pc, eb, cp, pc2, eb2, cp2);
      if InBlockV(r1, code, start + 1, e1, str, ov, j, pc2, cp2) {
        assert InMinV(k, qid, r1, code, start, endl, str, ov, j, pc2, cp2);
      } else {
        if k - 1 > 0 {
          MinEntryV(k - 1, qid, r1, code, e1, endl, str, ov, cp2);
          assert InMinV(k, qid, r1, code, start, endl, str, ov, j, pc2, cp2);
        } else {
          OD.MinZeroSame(qid, r1, code, e1, endl);
          IterConsV(r1, 0, str, ov, j, cp2, cp2);
          assert pc2 == endl && OBV.MatchesIterV(r1, k, str, ov, j, cp2);
        }
      }
    } else {
      var m: int :| OBV.MatchesV(r1, str, ov, j, m) && InMinV(k - 1, qid, r1, code, e1, endl, str, ov, m, pc, cp);
      BlockStepMinV(k - 1, qid, r1, code, e1, endl, str, ov, m, pc, eb, cp, pc2, eb2, cp2);
      if InMinV(k - 1, qid, r1, code, e1, endl, str, ov, m, pc2, cp2) {
        assert InMinV(k, qid, r1, code, start, endl, str, ov, j, pc2, cp2);
      } else {
        IterConsV(r1, k - 1, str, ov, j, m, cp2);
        assert pc2 == endl && OBV.MatchesIterV(r1, k, str, ov, j, cp2);
      }
    }
  }

  /** `BlockStepV` for the optional-layer chain. */
  lemma BlockStepOptV(layers: nat, greedy: bool, qid: R.quantid, r1: R.regex, code: RB.code,
                      start: nat, endl: nat, str: string, ov: LOr.OracleView, j: int,
                      pc: nat, eb: bool, cp: int, pc2: nat, eb2: bool, cp2: int)
    requires InOptV(layers, greedy, qid, r1, code, start, endl, str, ov, j, pc, cp)
    requires AnyEdgeV(code, str, ov, pc, eb, cp, pc2, eb2, cp2)
    ensures InOptV(layers, greedy, qid, r1, code, start, endl, str, ov, j, pc2, cp2)
         || (pc2 == endl && OptDoneV(layers, r1, str, ov, j, cp2))
    decreases CP.rsize(r1), 2, layers
  {
    var e1: nat :| OD.OptShape(layers, greedy, qid, r1, code, start, e1, endl)
      && (((pc == start || pc == start + 1 || pc == start + 2) && cp == j)
          || InBlockV(r1, code, start + 3, e1, str, ov, j, pc, cp)
          || (pc == e1 && OBV.MatchesV(r1, str, ov, j, cp))
          || exists m: int ::
               OBV.MatchesV(r1, str, ov, j, m)
               && InOptV(layers - 1, greedy, qid, r1, code, e1 + 1, endl, str, ov, m, pc, cp));
    if (pc == start || pc == start + 1 || pc == start + 2) && cp == j {
      if pc == start {
        assert OB.ForkAt(code, start, start + 1, endl);
        EdgeFromForkAtV(code, str, ov, start + 1, endl, pc, eb, cp, pc2, eb2, cp2);
        if pc2 == start + 1 {
          assert InOptV(layers, greedy, qid, r1, code, start, endl, str, ov, j, pc2, cp2);
        } else {
          assert OBV.MatchesIterV(r1, 0, str, ov, j, j);
          OptDoneVIntro(layers, r1, str, ov, j, cp2, 0);
        }
      } else if pc == start + 1 {
        EdgeFromSetQuantV(code, str, ov, qid, false, pc, eb, cp, pc2, eb2, cp2);
        assert InOptV(layers, greedy, qid, r1, code, start, endl, str, ov, j, pc2, cp2);
      } else {
        EdgeFromBeginLoopV(code, str, ov, pc, eb, cp, pc2, eb2, cp2);
        BlockEntryV(r1, code, start + 3, e1, str, ov, j);
        if start + 3 == e1 {
          BlockEmptyV(r1, code, start + 3, str, ov, j);
          assert pc2 == e1 && OBV.MatchesV(r1, str, ov, j, cp2);
          assert InOptV(layers, greedy, qid, r1, code, start, endl, str, ov, j, pc2, cp2);
        } else {
          assert InBlockV(r1, code, start + 3, e1, str, ov, j, pc2, cp2);
          assert InOptV(layers, greedy, qid, r1, code, start, endl, str, ov, j, pc2, cp2);
        }
      }
    } else if InBlockV(r1, code, start + 3, e1, str, ov, j, pc, cp) {
      BlockStepV(r1, code, start + 3, e1, str, ov, j, pc, eb, cp, pc2, eb2, cp2);
      if InBlockV(r1, code, start + 3, e1, str, ov, j, pc2, cp2) {
        assert InOptV(layers, greedy, qid, r1, code, start, endl, str, ov, j, pc2, cp2);
      } else {
        assert pc2 == e1 && OBV.MatchesV(r1, str, ov, j, cp2);
        assert InOptV(layers, greedy, qid, r1, code, start, endl, str, ov, j, pc2, cp2);
      }
    } else if pc == e1 && OBV.MatchesV(r1, str, ov, j, cp) {
      EdgeFromEndLoopV(code, str, ov, pc, eb, cp, pc2, eb2, cp2);
      if layers - 1 > 0 {
        OptEntryV(layers - 1, greedy, qid, r1, code, e1 + 1, endl, str, ov, cp);
        assert InOptV(layers, greedy, qid, r1, code, start, endl, str, ov, j, pc2, cp2);
      } else {
        OD.OptZeroSame(greedy, qid, r1, code, e1 + 1, endl);
        IterConsV(r1, 0, str, ov, j, cp, cp);
        OptDoneVIntro(layers, r1, str, ov, j, cp2, 1);
      }
    } else {
      var m: int :| OBV.MatchesV(r1, str, ov, j, m)
        && InOptV(layers - 1, greedy, qid, r1, code, e1 + 1, endl, str, ov, m, pc, cp);
      BlockStepOptV(layers - 1, greedy, qid, r1, code, e1 + 1, endl, str, ov, m, pc, eb, cp, pc2, eb2, cp2);
      if InOptV(layers - 1, greedy, qid, r1, code, e1 + 1, endl, str, ov, m, pc2, cp2) {
        assert InOptV(layers, greedy, qid, r1, code, start, endl, str, ov, j, pc2, cp2);
      } else {
        var k := OptDoneVInv(layers - 1, r1, str, ov, m, cp2);
        IterConsV(r1, k, str, ov, j, m, cp2);
        OptDoneVIntro(layers, r1, str, ov, j, cp2, k + 1);
      }
    }
  }

  /** THE step lemma, gated: every V configuration-graph edge out of a
      mid-parse state of `re`'s block lands in a mid-parse state or exits at
      `endl` with a completed GATED span match. The NEW case is
      `Re_lookaround`: the given edge is the gate's own eps step, whose guard
      IS the `MatchesV` clause. */
  lemma BlockStepV(re: R.regex, code: RB.code, start: nat, endl: nat, str: string, ov: LOr.OracleView, i: int,
                   pc: nat, eb: bool, cp: int, pc2: nat, eb2: bool, cp2: int)
    requires InBlockV(re, code, start, endl, str, ov, i, pc, cp)
    requires AnyEdgeV(code, str, ov, pc, eb, cp, pc2, eb2, cp2)
    ensures InBlockV(re, code, start, endl, str, ov, i, pc2, cp2)
         || (pc2 == endl && OBV.MatchesV(re, str, ov, i, cp2))
    decreases CP.rsize(re), 0, 0
  {
    match re
    case Re_empty =>
    case Re_lookaround(lid, la, r1) =>
      if la.Lookahead? || la.Lookbehind? {
        EdgeFromCheckOracleV(code, str, ov, lid, pc, eb, cp, pc2, eb2, cp2);
        assert LOr.view_get_oracle(ov, i, lid);
      } else {
        EdgeFromNegCheckOracleV(code, str, ov, lid, pc, eb, cp, pc2, eb2, cp2);
        assert !LOr.view_get_oracle(ov, i, lid);
      }
      assert pc2 == endl && cp2 == i;
      assert OBV.MatchesV(re, str, ov, i, cp2);
    case Re_character(ch) =>
      EdgeFromConsumeV(code, str, ov, T.ExpectationOf(ch), pc, eb, cp, pc2, eb2, cp2);
      assert OBV.MatchesV(re, str, ov, i, cp2);
    case Re_anchor(a) =>
      EdgeFromAnchorV(code, str, ov, a, pc, eb, cp, pc2, eb2, cp2);
      assert OBV.MatchesV(re, str, ov, i, cp2);
    case Re_alt(r1, r2) =>
      var e1: nat :| OD.AltShape(r1, r2, code, start, e1, endl)
        && ((pc == start && cp == i)
            || InBlockV(r1, code, start + 1, e1, str, ov, i, pc, cp)
            || (pc == e1 && OBV.MatchesV(r1, str, ov, i, cp))
            || InBlockV(r2, code, e1 + 1, endl, str, ov, i, pc, cp));
      if pc == start && cp == i {
        OB.GetPcInstr(code, start, RB.Fork(start + 1, e1 + 1));
        assert ORc.EpsEdgeV(code, str, ov, cp, pc, eb, pc2, eb2) && cp2 == cp;
        assert pc2 == start + 1 || pc2 == e1 + 1;
        if pc2 == start + 1 {
          BlockEntryV(r1, code, start + 1, e1, str, ov, i);
          if start + 1 == e1 {
            BlockEmptyV(r1, code, start + 1, str, ov, i);
            assert pc2 == e1 && OBV.MatchesV(r1, str, ov, i, cp2);
            assert InBlockV(re, code, start, endl, str, ov, i, pc2, cp2);
          } else {
            assert InBlockV(re, code, start, endl, str, ov, i, pc2, cp2);
          }
        } else {
          BlockEntryV(r2, code, e1 + 1, endl, str, ov, i);
          if e1 + 1 == endl {
            BlockEmptyV(r2, code, e1 + 1, str, ov, i);
            assert pc2 == endl && OBV.MatchesV(re, str, ov, i, cp2);
          } else {
            assert InBlockV(re, code, start, endl, str, ov, i, pc2, cp2);
          }
        }
      } else if InBlockV(r1, code, start + 1, e1, str, ov, i, pc, cp) {
        BlockStepV(r1, code, start + 1, e1, str, ov, i, pc, eb, cp, pc2, eb2, cp2);
        assert InBlockV(re, code, start, endl, str, ov, i, pc2, cp2);
      } else if pc == e1 && OBV.MatchesV(r1, str, ov, i, cp) {
        EdgeFromJmpV(code, str, ov, endl as int, pc, eb, cp, pc2, eb2, cp2);
        assert pc2 == endl && OBV.MatchesV(re, str, ov, i, cp2);
      } else {
        BlockStepV(r2, code, e1 + 1, endl, str, ov, i, pc, eb, cp, pc2, eb2, cp2);
        if InBlockV(r2, code, e1 + 1, endl, str, ov, i, pc2, cp2) {
          assert InBlockV(re, code, start, endl, str, ov, i, pc2, cp2);
        } else {
          assert pc2 == endl && OBV.MatchesV(re, str, ov, i, cp2);
        }
      }
    case Re_con(r1, r2) =>
      var e1: nat :| OD.ConShape(r1, r2, code, start, e1, endl)
        && (InBlockV(r1, code, start, e1, str, ov, i, pc, cp)
            || exists m: int :: OBV.MatchesV(r1, str, ov, i, m) && InBlockV(r2, code, e1, endl, str, ov, m, pc, cp));
      if InBlockV(r1, code, start, e1, str, ov, i, pc, cp) {
        BlockStepV(r1, code, start, e1, str, ov, i, pc, eb, cp, pc2, eb2, cp2);
        if InBlockV(r1, code, start, e1, str, ov, i, pc2, cp2) {
          assert InBlockV(re, code, start, endl, str, ov, i, pc2, cp2);
        } else {
          BlockEntryV(r2, code, e1, endl, str, ov, cp2);
          if e1 == endl {
            BlockEmptyV(r2, code, e1, str, ov, cp2);
            assert pc2 == endl && OBV.MatchesV(re, str, ov, i, cp2);
          } else {
            assert OBV.MatchesV(r1, str, ov, i, cp2) && InBlockV(r2, code, e1, endl, str, ov, cp2, pc2, cp2);
            assert InBlockV(re, code, start, endl, str, ov, i, pc2, cp2);
          }
        }
      } else {
        var m: int :| OBV.MatchesV(r1, str, ov, i, m) && InBlockV(r2, code, e1, endl, str, ov, m, pc, cp);
        BlockStepV(r2, code, e1, endl, str, ov, m, pc, eb, cp, pc2, eb2, cp2);
        if InBlockV(r2, code, e1, endl, str, ov, m, pc2, cp2) {
          assert InBlockV(re, code, start, endl, str, ov, i, pc2, cp2);
        } else {
          assert pc2 == endl && OBV.MatchesV(re, str, ov, i, cp2);
        }
      }
    case Re_capture(cid, r1) =>
      var e1: nat :| OD.CapShape(cid, r1, code, start, e1, endl)
        && ((pc == start && cp == i)
            || InBlockV(r1, code, start + 1, e1, str, ov, i, pc, cp)
            || (pc == e1 && OBV.MatchesV(r1, str, ov, i, cp)));
      if pc == start && cp == i {
        EdgeFromSetRegV(code, str, ov, CP.start_reg(cid), pc, eb, cp, pc2, eb2, cp2);
        BlockEntryV(r1, code, start + 1, e1, str, ov, i);
        if start + 1 == e1 {
          BlockEmptyV(r1, code, start + 1, str, ov, i);
          assert pc2 == e1 && OBV.MatchesV(r1, str, ov, i, cp2);
          assert InBlockV(re, code, start, endl, str, ov, i, pc2, cp2);
        } else {
          assert InBlockV(re, code, start, endl, str, ov, i, pc2, cp2);
        }
      } else if InBlockV(r1, code, start + 1, e1, str, ov, i, pc, cp) {
        BlockStepV(r1, code, start + 1, e1, str, ov, i, pc, eb, cp, pc2, eb2, cp2);
        assert InBlockV(re, code, start, endl, str, ov, i, pc2, cp2);
      } else {
        EdgeFromSetRegV(code, str, ov, CP.end_reg(cid), pc, eb, cp, pc2, eb2, cp2);
        assert pc2 == endl && OBV.MatchesV(re, str, ov, i, cp2);
      }
    case Re_quant(nul, qid, q, r1) =>
      if q.min == 0 && q.max == None {
        var es1: nat :| OD.StarShape(qid, r1, code, start, es1, endl)
          && StTailV(qid, r1, code, start, es1, str, ov, i, pc, cp);
        var m := StTailVInv(qid, r1, code, start, es1, str, ov, i, pc, cp);
        if (pc == start || pc == start + 1 || pc == start + 2) && cp == m {
          if pc == start {
            assert OB.ForkAt(code, start, start + 1, endl);
            EdgeFromForkAtV(code, str, ov, start + 1, endl, pc, eb, cp, pc2, eb2, cp2);
            if pc2 == start + 1 {
              StTailVIntro(qid, r1, code, start, es1, str, ov, i, pc2, cp2, m);
              assert InBlockV(re, code, start, endl, str, ov, i, pc2, cp2);
            } else {
              var k := IterFromInvV(r1, 0, str, ov, i, m);
              assert OBV.MatchesV(re, str, ov, i, cp2);
            }
          } else if pc == start + 1 {
            EdgeFromSetQuantV(code, str, ov, qid, false, pc, eb, cp, pc2, eb2, cp2);
            StTailVIntro(qid, r1, code, start, es1, str, ov, i, pc2, cp2, m);
            assert InBlockV(re, code, start, endl, str, ov, i, pc2, cp2);
          } else {
            EdgeFromBeginLoopV(code, str, ov, pc, eb, cp, pc2, eb2, cp2);
            BlockEntryV(r1, code, start + 3, es1, str, ov, m);
            if start + 3 == es1 {
              BlockEmptyV(r1, code, start + 3, str, ov, m);
              assert pc2 == es1 && OBV.MatchesV(r1, str, ov, m, cp2);
              StTailVIntro(qid, r1, code, start, es1, str, ov, i, pc2, cp2, m);
              assert InBlockV(re, code, start, endl, str, ov, i, pc2, cp2);
            } else {
              StTailVIntro(qid, r1, code, start, es1, str, ov, i, pc2, cp2, m);
              assert InBlockV(re, code, start, endl, str, ov, i, pc2, cp2);
            }
          }
        } else if InBlockV(r1, code, start + 3, es1, str, ov, m, pc, cp) {
          BlockStepV(r1, code, start + 3, es1, str, ov, m, pc, eb, cp, pc2, eb2, cp2);
          StTailVIntro(qid, r1, code, start, es1, str, ov, i, pc2, cp2, m);
          assert InBlockV(re, code, start, endl, str, ov, i, pc2, cp2);
        } else if pc == es1 {
          EdgeFromEndLoopV(code, str, ov, pc, eb, cp, pc2, eb2, cp2);
          StTailVIntro(qid, r1, code, start, es1, str, ov, i, pc2, cp2, m);
          assert InBlockV(re, code, start, endl, str, ov, i, pc2, cp2);
        } else {
          EdgeFromJmpV(code, str, ov, start as int, pc, eb, cp, pc2, eb2, cp2);
          IterFromSnocV(r1, 0, str, ov, i, m, cp);
          StTailVIntro(qid, r1, code, start, es1, str, ov, i, pc2, cp2, cp);
          assert InBlockV(re, code, start, endl, str, ov, i, pc2, cp2);
        }
      } else if q.max.Some? {
        var em: nat :|
          NR.NfaRepMinRE(q.min as nat, qid, r1, code, start, em)
          && NR.NfaRepOptRE((q.max.value - q.min) as nat, q.greedy, qid, r1, code, em, endl)
          && (InMinV(q.min as nat, qid, r1, code, start, em, str, ov, i, pc, cp)
              || BdTailV(q.min as nat, (q.max.value - q.min) as nat, q.greedy, qid, r1, code, em, endl, str, ov, i, pc, cp));
        if InMinV(q.min as nat, qid, r1, code, start, em, str, ov, i, pc, cp) {
          BlockStepMinV(q.min as nat, qid, r1, code, start, em, str, ov, i, pc, eb, cp, pc2, eb2, cp2);
          if InMinV(q.min as nat, qid, r1, code, start, em, str, ov, i, pc2, cp2) {
            assert InBlockV(re, code, start, endl, str, ov, i, pc2, cp2);
          } else {
            if (q.max.value - q.min) as nat > 0 {
              OptEntryV((q.max.value - q.min) as nat, q.greedy, qid, r1, code, em, endl, str, ov, cp2);
              BdTailVIntro(q.min as nat, (q.max.value - q.min) as nat, q.greedy, qid, r1, code, em, endl, str, ov, i, pc2, cp2, cp2);
              assert InBlockV(re, code, start, endl, str, ov, i, pc2, cp2);
            } else {
              OD.OptZeroSame(q.greedy, qid, r1, code, em, endl);
              assert pc2 == endl && OBV.MatchesV(re, str, ov, i, cp2);
            }
          }
        } else {
          var m := BdTailVInv(q.min as nat, (q.max.value - q.min) as nat, q.greedy, qid, r1, code, em, endl, str, ov, i, pc, cp);
          BlockStepOptV((q.max.value - q.min) as nat, q.greedy, qid, r1, code, em, endl, str, ov, m, pc, eb, cp, pc2, eb2, cp2);
          if InOptV((q.max.value - q.min) as nat, q.greedy, qid, r1, code, em, endl, str, ov, m, pc2, cp2) {
            BdTailVIntro(q.min as nat, (q.max.value - q.min) as nat, q.greedy, qid, r1, code, em, endl, str, ov, i, pc2, cp2, m);
            assert InBlockV(re, code, start, endl, str, ov, i, pc2, cp2);
          } else {
            var k := OptDoneVInv((q.max.value - q.min) as nat, r1, str, ov, m, cp2);
            IterConcatV(r1, q.min as nat, k, str, ov, i, m, cp2);
            assert OBV.MatchesIterV(r1, q.min as nat + k, str, ov, i, cp2);
            assert pc2 == endl && OBV.MatchesV(re, str, ov, i, cp2);
          }
        }
      } else {
        var em: nat, e1: nat :|
          NR.NfaRepMinRE((q.min - 1) as nat, qid, r1, code, start, em)
          && OD.DoWhileShape(qid, r1, code, em, e1, endl)
          && (InMinV((q.min - 1) as nat, qid, r1, code, start, em, str, ov, i, pc, cp)
              || DwTailV((q.min - 1) as nat, qid, r1, code, em, e1, str, ov, i, pc, cp));
        if InMinV((q.min - 1) as nat, qid, r1, code, start, em, str, ov, i, pc, cp) {
          BlockStepMinV((q.min - 1) as nat, qid, r1, code, start, em, str, ov, i, pc, eb, cp, pc2, eb2, cp2);
          if InMinV((q.min - 1) as nat, qid, r1, code, start, em, str, ov, i, pc2, cp2) {
            assert InBlockV(re, code, start, endl, str, ov, i, pc2, cp2);
          } else {
            IterFromIntroV(r1, (q.min - 1) as nat, (q.min - 1) as nat, str, ov, i, cp2);
            DwTailVIntro((q.min - 1) as nat, qid, r1, code, em, e1, str, ov, i, pc2, cp2, cp2);
            assert InBlockV(re, code, start, endl, str, ov, i, pc2, cp2);
          }
        } else {
          var m := DwTailVInv((q.min - 1) as nat, qid, r1, code, em, e1, str, ov, i, pc, cp);
          if pc == em && cp == m {
            EdgeFromSetQuantV(code, str, ov, qid, false, pc, eb, cp, pc2, eb2, cp2);
            BlockEntryV(r1, code, em + 1, e1, str, ov, m);
            if em + 1 == e1 {
              BlockEmptyV(r1, code, em + 1, str, ov, m);
              DwTailVIntro((q.min - 1) as nat, qid, r1, code, em, e1, str, ov, i, pc2, cp2, m);
              assert InBlockV(re, code, start, endl, str, ov, i, pc2, cp2);
            } else {
              DwTailVIntro((q.min - 1) as nat, qid, r1, code, em, e1, str, ov, i, pc2, cp2, m);
              assert InBlockV(re, code, start, endl, str, ov, i, pc2, cp2);
            }
          } else if InBlockV(r1, code, em + 1, e1, str, ov, m, pc, cp) {
            BlockStepV(r1, code, em + 1, e1, str, ov, m, pc, eb, cp, pc2, eb2, cp2);
            DwTailVIntro((q.min - 1) as nat, qid, r1, code, em, e1, str, ov, i, pc2, cp2, m);
            assert InBlockV(re, code, start, endl, str, ov, i, pc2, cp2);
          } else {
            assert OB.ForkAt(code, e1, em, endl);
            EdgeFromForkAtV(code, str, ov, em, endl, pc, eb, cp, pc2, eb2, cp2);
            if pc2 == em {
              IterFromSnocV(r1, (q.min - 1) as nat, str, ov, i, m, cp);
              DwTailVIntro((q.min - 1) as nat, qid, r1, code, em, e1, str, ov, i, pc2, cp2, cp);
              assert InBlockV(re, code, start, endl, str, ov, i, pc2, cp2);
            } else {
              var k := IterFromInvV(r1, (q.min - 1) as nat, str, ov, i, m);
              IterSnocV(r1, k, str, ov, i, m, cp);
              assert OBV.MatchesIterV(r1, k + 1, str, ov, i, cp2);
              assert pc2 == endl && OBV.MatchesV(re, str, ov, i, cp2);
            }
          }
        }
      }
  }

  // ===========================================================================
  // The program-level sweep
  // ===========================================================================

  /** Some legitimate body entry position underlies this mid-parse state. */
  ghost predicate BodyMidV(body: R.regex, code: RB.code, next: nat, str: string, ov: LOr.OracleView, pc: nat, cp: int) {
    exists i: int {:trigger InBlockV(body, code, 6, next, str, ov, i, pc, cp)} ::
      0 <= i && InBlockV(body, code, 6, next, str, ov, i, pc, cp)
  }

  lemma BodyMidVIntro(body: R.regex, code: RB.code, next: nat, str: string, ov: LOr.OracleView, pc: nat, cp: int, i: int)
    requires 0 <= i && InBlockV(body, code, 6, next, str, ov, i, pc, cp)
    ensures BodyMidV(body, code, next, str, ov, pc, cp)
  {
  }

  lemma BodyMidVInv(body: R.regex, code: RB.code, next: nat, str: string, ov: LOr.OracleView, pc: nat, cp: int) returns (i: int)
    requires BodyMidV(body, code, next, str, ov, pc, cp)
    ensures 0 <= i && InBlockV(body, code, 6, next, str, ov, i, pc, cp)
  {
    i :| 0 <= i && InBlockV(body, code, 6, next, str, ov, i, pc, cp);
  }

  /** The recorder's claim, gated. */
  ghost predicate RecorderHitV(body: R.regex, str: string, ov: LOr.OracleView, cp: int) {
    exists i: int {:trigger OBV.MatchesV(body, str, ov, i, cp)} ::
      0 <= i <= cp && OBV.MatchesV(body, str, ov, i, cp)
  }

  lemma RecorderHitVIntro(body: R.regex, str: string, ov: LOr.OracleView, cp: int, i: int)
    requires 0 <= i <= cp && OBV.MatchesV(body, str, ov, i, cp)
    ensures RecorderHitV(body, str, ov, cp)
  {
  }

  lemma RecorderHitVInv(body: R.regex, str: string, ov: LOr.OracleView, cp: int) returns (i: int)
    requires RecorderHitV(body, str, ov, cp)
    ensures 0 <= i <= cp && OBV.MatchesV(body, str, ov, i, cp)
  {
    i :| 0 <= i <= cp && OBV.MatchesV(body, str, ov, i, cp);
  }

  /** The build program's V reachability invariant. */
  ghost predicate ProgInvV(body: R.regex, code: RB.code, next: nat, str: string, ov: LOr.OracleView, pc: nat, cp: int) {
    (pc <= 5 && 0 <= cp)
    || BodyMidV(body, code, next, str, ov, pc, cp)
    || (pc == next && RecorderHitV(body, str, ov, cp))
  }

  /** One step out of the dot-star zone, V. */
  lemma ZoneStepV(body: R.regex, code: RB.code, next: nat, str: string, ov: LOr.OracleView,
                  pc1: nat, eb1: bool, cp1: int, pc: nat, eb: bool, cp: int)
    requires OD.StarShape(0, R.Re_character(R.Dot), code, 0, 4, 6)
    requires NR.NfaRepRE(body, code, 6, next)
    requires 6 <= next
    requires pc1 <= 5 && 0 <= cp1
    requires AnyEdgeV(code, str, ov, pc1, eb1, cp1, pc, eb, cp)
    ensures ProgInvV(body, code, next, str, ov, pc, cp)
  {
    assert NR.GetPcRE(code, 3) == Some(RB.Consume(T.ExpectationOf(R.Dot)));
    if pc1 == 0 {
      assert OB.ForkAt(code, 0, 1, 6);
      EdgeFromForkAtV(code, str, ov, 1, 6, pc1, eb1, cp1, pc, eb, cp);
      if pc == 6 {
        BlockEntryV(body, code, 6, next, str, ov, cp);
        if 6 == next {
          BlockEmptyV(body, code, 6, str, ov, cp);
          RecorderHitVIntro(body, str, ov, cp, cp);
        } else {
          BodyMidVIntro(body, code, next, str, ov, pc, cp, cp);
        }
      }
    } else if pc1 == 1 {
      EdgeFromSetQuantV(code, str, ov, 0, false, pc1, eb1, cp1, pc, eb, cp);
    } else if pc1 == 2 {
      EdgeFromBeginLoopV(code, str, ov, pc1, eb1, cp1, pc, eb, cp);
    } else if pc1 == 3 {
      EdgeFromConsumeV(code, str, ov, T.ExpectationOf(R.Dot), pc1, eb1, cp1, pc, eb, cp);
    } else if pc1 == 4 {
      EdgeFromEndLoopV(code, str, ov, pc1, eb1, cp1, pc, eb, cp);
    } else {
      EdgeFromJmpV(code, str, ov, 0, pc1, eb1, cp1, pc, eb, cp);
    }
  }

  /** Every V-reachable configuration of the build program satisfies the
      invariant — the least-lemma sweep over `ReachFV`. */
  least lemma ProgReachInvV(body: R.regex, code: RB.code, next: nat, lid: R.lookid, str: string,
                            ov: LOr.OracleView, pc: nat, eb: bool, cp: int)
    requires OD.StarShape(0, R.Re_character(R.Dot), code, 0, 4, 6)
    requires NR.NfaRepRE(body, code, 6, next)
    requires 6 <= next
    requires NR.GetPcRE(code, next) == Some(RB.WriteOracle(lid))
    requires ORc.ReachFV(code, str, ov, 0, pc, eb, cp)
    ensures ProgInvV(body, code, next, str, ov, pc, cp)
  {
    if pc == 0 && eb == false && cp == 0 {
      // the initial configuration is in the zone
    } else if exists pc1: nat, eb1: bool ::
        ORc.ReachFV(code, str, ov, 0, pc1, eb1, cp) && ORc.EpsEdgeV(code, str, ov, cp, pc1, eb1, pc, eb) {
      var pc1: nat, eb1: bool :|
        ORc.ReachFV(code, str, ov, 0, pc1, eb1, cp) && ORc.EpsEdgeV(code, str, ov, cp, pc1, eb1, pc, eb);
      ProgReachInvV(body, code, next, lid, str, ov, pc1, eb1, cp);
      assert AnyEdgeV(code, str, ov, pc1, eb1, cp, pc, eb, cp);
      if pc1 <= 5 && 0 <= cp {
        ZoneStepV(body, code, next, str, ov, pc1, eb1, cp, pc, eb, cp);
      } else if BodyMidV(body, code, next, str, ov, pc1, cp) {
        var i := BodyMidVInv(body, code, next, str, ov, pc1, cp);
        BlockStepV(body, code, 6, next, str, ov, i, pc1, eb1, cp, pc, eb, cp);
        if InBlockV(body, code, 6, next, str, ov, i, pc, cp) {
          BodyMidVIntro(body, code, next, str, ov, pc, cp, i);
        } else {
          OBV.MatchesVBounds(body, str, ov, i, cp);
          RecorderHitVIntro(body, str, ov, cp, i);
        }
      } else {
        // the recorder has no outgoing edges
        OB.GetPcInstr(code, next, RB.WriteOracle(lid));
        assert false;
      }
    } else {
      assert eb == true && pc > 0 && ORc.ConsumeEdge(code, str, cp - 1, pc - 1);
      var eb1: bool :| (eb1 == false || eb1 == true)
        && ORc.ReachFV(code, str, ov, 0, pc - 1, eb1, cp - 1);
      ProgReachInvV(body, code, next, lid, str, ov, pc - 1, eb1, cp - 1);
      assert AnyEdgeV(code, str, ov, pc - 1, eb1, cp - 1, pc, eb, cp);
      if pc - 1 <= 5 && 0 <= cp - 1 {
        ZoneStepV(body, code, next, str, ov, pc - 1, eb1, cp - 1, pc, eb, cp);
      } else if BodyMidV(body, code, next, str, ov, pc - 1, cp - 1) {
        var i := BodyMidVInv(body, code, next, str, ov, pc - 1, cp - 1);
        BlockStepV(body, code, 6, next, str, ov, i, pc - 1, eb1, cp - 1, pc, eb, cp);
        if InBlockV(body, code, 6, next, str, ov, i, pc, cp) {
          BodyMidVIntro(body, code, next, str, ov, pc, cp, i);
        } else {
          OBV.MatchesVBounds(body, str, ov, i, cp);
          RecorderHitVIntro(body, str, ov, cp, i);
        }
      } else {
        OB.GetPcInstr(code, next, RB.WriteOracle(lid));
        assert false;
      }
    }
  }

  // ===========================================================================
  // PathToMatchesV, assembled
  // ===========================================================================

  /** THE decomposition direction, gated: a V-reachable `WriteOracle(lid)` in
      the build program means the body `MatchesV` some span ending at `cp`. */
  lemma ReachesWriteVToMatchesV(body: R.regex, lid: R.lookid, str: string, ov: LOr.OracleView, cp: int) returns (i: int)
    requires NR.NestedFragmentRE(body)
    requires ORc.ReachesWriteV(CP.compile_to_write(R.lazy_prefix(body), lid), str, ov, 0, lid, cp)
    ensures 0 <= i <= cp && OBV.MatchesV(body, str, ov, i, cp)
  {
    OBV.NestedLazyPrefix(body);
    NR.CompileToWriteRepNested(R.lazy_prefix(body), lid);
    var code := CP.compile_to_write(R.lazy_prefix(body), lid);
    var next := CP.compile(R.lazy_prefix(body), 0, CP.Progress).1;
    // the two-block layout: dot-star head at 0..5, body at [6, next)
    var pre := R.Re_quant(R.NonNullable, 0, R.CountedQuant(0, None, false), R.Re_character(R.Dot));
    assert R.lazy_prefix(body) == R.Re_con(pre, body);
    assert NR.NfaRepRE(R.Re_con(pre, body), code, 0, next as nat);
    assert exists e1: nat :: NR.NfaRepRE(pre, code, 0, e1) && NR.NfaRepRE(body, code, e1, next as nat);
    var e1x: nat :| NR.NfaRepRE(pre, code, 0, e1x) && NR.NfaRepRE(body, code, e1x, next as nat);
    var es1: nat :|
      NR.GetPcRE(code, 0) == Some(RB.Fork(es1 + 2, 1))
      && NR.GetPcRE(code, 1) == Some(RB.SetQuantToClock(0, false))
      && NR.GetPcRE(code, 2) == Some(RB.BeginLoop)
      && NR.NfaRepRE(R.Re_character(R.Dot), code, 3, es1)
      && NR.GetPcRE(code, es1) == Some(RB.EndLoop)
      && NR.GetPcRE(code, es1 + 1) == Some(RB.Jmp(0))
      && e1x == es1 + 2;
    assert es1 == 4 && e1x == 6;
    assert OD.StarShape(0, R.Re_character(R.Dot), code, 0, 4, 6);
    NR.NfaRepIncrRE(body, code, 6, next as nat);
    // the recorder's pc is pinned: inside the block nothing WRITES (the
    // nested body block contains GATES, but gates are not WriteOracle)
    var pc: nat, eb: bool :|
      ORc.ReachFV(code, str, ov, 0, pc, eb, cp) && RB.get_instr(code, pc) == RB.WriteOracle(lid);
    assert 0 <= pc < |code|;
    assert |code| == next + 1;
    if pc < next as nat {
      if pc <= 5 {
        assert NR.GetPcRE(code, pc).Some? && !NR.GetPcRE(code, pc).value.WriteOracle?;
        assert false;
      } else {
        NR.NoWriteInstrNestedRE(body, code, 6, next as nat, pc);
        assert false;
      }
    }
    assert pc == next as nat;
    ProgReachInvV(body, code, next as nat, lid, str, ov, pc, eb, cp);
    // the zone is below the body block, and mid-parse states sit before next
    assert !(pc <= 5);
    if BodyMidV(body, code, next as nat, str, ov, pc, cp) {
      var i0 := BodyMidVInv(body, code, next as nat, str, ov, pc, cp);
      InBlockVRange(body, code, 6, next as nat, str, ov, i0, pc, cp);
      assert false;
    }
    i := RecorderHitVInv(body, str, ov, cp);
  }
}
