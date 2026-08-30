// L4 depth-k, nested ORACLE ENTRY, rung V1 (the §6.3 bridge, V-model): the
// GATED span-match predicate `MatchesV` and the forward bridge direction
// `MatchesVToReachesWriteV` for NESTED-fragment bodies.
//
// This is the V-model clone of `OracleBridge`: same span algebra, same path
// constructions, with three systematic changes:
//   - `Matches`  -> `MatchesV`: a partial oracle view `ov` is threaded through,
//     and `Re_lookaround` (excluded there) gains its OWN clause — a zero-width
//     span whose truth is exactly the view's bit at the current position
//     (positive flavours) or its negation (negative flavours). This mirrors
//     the ONE instruction a lookaround compiles to (`CheckOracle` /
//     `NegCheckOracle`).
//   - `ReachF`/`EpsEdge` -> `ReachFV`/`EpsEdgeV`: the nesting-aware
//     configuration graph, whose gate edges consult the SAME view — which is
//     why the lookaround case of `MatchesVToPath` is one eps step: the match
//     clause IS the edge's guard.
//   - fragment: `PlusFragmentRE && LookFreeRE` -> `NestedFragmentRE` (the
//     depth-k fragment; quantifier shapes are identical, looks now admitted).
/** V1 of the nested oracle entry: `MatchesV`, its span algebra, and the
    forward direction `MatchesVToReachesWriteV`. */
module LindenElkOracleBridgeV {
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
  // The GATED span-match predicate
  // ===========================================================================

  /** `re` matches exactly the span `[i, j)` of `str`, scanning forward,
      with every lookaround resolved by the partial view `ov` — the
      existence-level, engine-free statement of a NESTED body match. The
      lookaround clause is zero-width and reads the view at the current
      position, exactly as the compiled gate instruction does. */
  ghost predicate MatchesV(re: R.regex, str: string, ov: LOr.OracleView, i: int, j: int)
    decreases CP.rsize(re), 0, 0
  {
    match re
    case Re_empty => i == j
    case Re_character(ch) =>
      j == i + 1 && RC.is_accepted(AI.get_char(str, i), T.ExpectationOf(ch))
    case Re_anchor(a) =>
      i == j && LAnc.is_satisfied(a, ORc.CtxAt(str, i), LAnc.Forward)
    case Re_alt(r1, r2) => MatchesV(r1, str, ov, i, j) || MatchesV(r2, str, ov, i, j)
    case Re_con(r1, r2) =>
      exists m: int :: MatchesV(r1, str, ov, i, m) && MatchesV(r2, str, ov, m, j)
    case Re_quant(nul, qid, q, r1) =>
      exists k: nat ::
        q.min <= k && (q.max.Some? ==> k <= q.max.value)
        && MatchesIterV(r1, k, str, ov, i, j)
    case Re_capture(cid, r1) => MatchesV(r1, str, ov, i, j)
    case Re_lookaround(lid, la, r1) =>
      i == j && (if la.Lookahead? || la.Lookbehind?
                 then LOr.view_get_oracle(ov, i, lid)
                 else !LOr.view_get_oracle(ov, i, lid))
  }

  /** `k` consecutive `r`-spans, gated. */
  ghost predicate MatchesIterV(r: R.regex, k: nat, str: string, ov: LOr.OracleView, i: int, j: int)
    decreases CP.rsize(r), 1, k
  {
    if k == 0 then i == j
    else exists m: int :: MatchesV(r, str, ov, i, m) && MatchesIterV(r, k - 1, str, ov, m, j)
  }

  // ===========================================================================
  // Span algebra (clones)
  // ===========================================================================

  /** Spans never go backward. */
  lemma MatchesVBounds(re: R.regex, str: string, ov: LOr.OracleView, i: int, j: int)
    requires MatchesV(re, str, ov, i, j)
    ensures i <= j
    decreases CP.rsize(re), 0, 0
  {
    match re
    case Re_alt(r1, r2) =>
      if MatchesV(r1, str, ov, i, j) { MatchesVBounds(r1, str, ov, i, j); }
      else { MatchesVBounds(r2, str, ov, i, j); }
    case Re_con(r1, r2) =>
      var m: int :| MatchesV(r1, str, ov, i, m) && MatchesV(r2, str, ov, m, j);
      MatchesVBounds(r1, str, ov, i, m);
      MatchesVBounds(r2, str, ov, m, j);
    case Re_quant(nul, qid, q, r1) =>
      var k: nat :| q.min <= k && (q.max.Some? ==> k <= q.max.value)
                 && MatchesIterV(r1, k, str, ov, i, j);
      MatchesIterVBounds(r1, k, str, ov, i, j);
    case Re_capture(_, r1) => MatchesVBounds(r1, str, ov, i, j);
    case _ =>
  }

  /** `MatchesVBounds` for iteration chains. */
  lemma MatchesIterVBounds(r: R.regex, k: nat, str: string, ov: LOr.OracleView, i: int, j: int)
    requires MatchesIterV(r, k, str, ov, i, j)
    ensures i <= j
    decreases CP.rsize(r), 1, k
  {
    if k > 0 {
      var m: int :| MatchesV(r, str, ov, i, m) && MatchesIterV(r, k - 1, str, ov, m, j);
      MatchesVBounds(r, str, ov, i, m);
      MatchesIterVBounds(r, k - 1, str, ov, m, j);
    }
  }

  /** Head inversion for a nonempty iteration chain. */
  lemma MatchesIterVHead(r: R.regex, k: nat, str: string, ov: LOr.OracleView, i: int, j: int) returns (m: int)
    requires k > 0
    requires MatchesIterV(r, k, str, ov, i, j)
    ensures MatchesV(r, str, ov, i, m) && MatchesIterV(r, k - 1, str, ov, m, j)
  {
    m :| MatchesV(r, str, ov, i, m) && MatchesIterV(r, k - 1, str, ov, m, j);
  }

  /** Split an iteration chain after its first `n` spans. */
  lemma IterVSplit(r: R.regex, k: nat, n: nat, str: string, ov: LOr.OracleView, i: int, j: int) returns (mid: int)
    requires MatchesIterV(r, k, str, ov, i, j)
    requires n <= k
    ensures MatchesIterV(r, n, str, ov, i, mid) && MatchesIterV(r, k - n, str, ov, mid, j)
    decreases n
  {
    if n == 0 { mid := i; return; }
    var m: int :| MatchesV(r, str, ov, i, m) && MatchesIterV(r, k - 1, str, ov, m, j);
    mid := IterVSplit(r, k - 1, n - 1, str, ov, m, j);
  }

  /** Iteration chains whose every span CONSUMES. */
  ghost predicate MatchesIterVNE(r: R.regex, k: nat, str: string, ov: LOr.OracleView, i: int, j: int)
    decreases CP.rsize(r), 2, k
  {
    if k == 0 then i == j
    else exists m: int :: i < m && MatchesV(r, str, ov, i, m) && MatchesIterVNE(r, k - 1, str, ov, m, j)
  }

  /** `MatchesIterVBounds` for nonempty chains. */
  lemma MatchesIterVNEBounds(r: R.regex, k: nat, str: string, ov: LOr.OracleView, i: int, j: int)
    requires MatchesIterVNE(r, k, str, ov, i, j)
    ensures i <= j
    decreases CP.rsize(r), 2, k
  {
    if k > 0 {
      var m: int :| i < m && MatchesV(r, str, ov, i, m) && MatchesIterVNE(r, k - 1, str, ov, m, j);
      MatchesIterVNEBounds(r, k - 1, str, ov, m, j);
    }
  }

  /** Empty iterations are droppable. */
  lemma IterVDropEmpty(r: R.regex, k: nat, str: string, ov: LOr.OracleView, i: int, j: int) returns (k2: nat)
    requires MatchesIterV(r, k, str, ov, i, j)
    ensures k2 <= k && MatchesIterVNE(r, k2, str, ov, i, j)
    decreases k
  {
    if k == 0 { k2 := 0; return; }
    var m: int :| MatchesV(r, str, ov, i, m) && MatchesIterV(r, k - 1, str, ov, m, j);
    if m == i {
      k2 := IterVDropEmpty(r, k - 1, str, ov, m, j);
    } else {
      MatchesVBounds(r, str, ov, i, m);
      var kk := IterVDropEmpty(r, k - 1, str, ov, m, j);
      k2 := kk + 1;
    }
  }

  /** A syntactically `NonNullable` regex never matches the empty span.
      Lookarounds are `CDNullable`, so the new case is vacuous under the
      `NonNullable` hypothesis. */
  lemma NonNullableNoEmptyMatchV(re: R.regex, str: string, ov: LOr.OracleView, i: int)
    requires NR.NestedFragmentRE(re)
    requires R.nullable(re) == R.NonNullable
    ensures !MatchesV(re, str, ov, i, i)
    decreases CP.rsize(re), 0, 0
  {
    match re
    case Re_alt(r1, r2) =>
      NonNullableNoEmptyMatchV(r1, str, ov, i);
      NonNullableNoEmptyMatchV(r2, str, ov, i);
    case Re_con(r1, r2) =>
      if MatchesV(re, str, ov, i, i) {
        assert MatchesV(R.Re_con(r1, r2), str, ov, i, i);
        assert exists m: int :: MatchesV(r1, str, ov, i, m) && MatchesV(r2, str, ov, m, i);
        var m: int :| MatchesV(r1, str, ov, i, m) && MatchesV(r2, str, ov, m, i);
        MatchesVBounds(r1, str, ov, i, m);
        MatchesVBounds(r2, str, ov, m, i);
        assert m == i;
        if R.nullable(r1) == R.NonNullable { NonNullableNoEmptyMatchV(r1, str, ov, i); }
        else { NonNullableNoEmptyMatchV(r2, str, ov, i); }
      }
    case Re_quant(nul, qid, q, r1) =>
      assert q.min > 0;
      if MatchesV(re, str, ov, i, i) {
        assert MatchesV(R.Re_quant(nul, qid, q, r1), str, ov, i, i);
        assert exists k: nat :: q.min <= k && (q.max.Some? ==> k <= q.max.value)
                             && MatchesIterV(r1, k, str, ov, i, i);
        var k: nat :| q.min <= k && (q.max.Some? ==> k <= q.max.value)
                   && MatchesIterV(r1, k, str, ov, i, i);
        assert k > 0;
        var m := MatchesIterVHead(r1, k, str, ov, i, i);
        MatchesVBounds(r1, str, ov, i, m);
        MatchesIterVBounds(r1, k - 1, str, ov, m, i);
        assert m == i;
        NonNullableNoEmptyMatchV(r1, str, ov, i);
      }
    case Re_capture(_, r1) => NonNullableNoEmptyMatchV(r1, str, ov, i);
    case _ =>
  }

  // ===========================================================================
  // ReachFV step packaging
  // ===========================================================================

  /** Take one V epsilon edge from a V-reachable configuration. */
  lemma ReachFVEpsIntro(c: RB.code, str: string, ov: LOr.OracleView, cp0: int, pc: nat, eb: bool,
                        pc2: nat, eb2: bool, cp: int)
    requires ORc.ReachFV(c, str, ov, cp0, pc, eb, cp)
    requires ORc.EpsEdgeV(c, str, ov, cp, pc, eb, pc2, eb2)
    ensures ORc.ReachFV(c, str, ov, cp0, pc2, eb2, cp)
  {
  }

  /** Take one consume edge from a V-reachable configuration. */
  lemma ReachFVConsumeIntro(c: RB.code, str: string, ov: LOr.OracleView, cp0: int, pc: nat, eb: bool, cp: int)
    requires ORc.ReachFV(c, str, ov, cp0, pc, eb, cp)
    requires ORc.ConsumeEdge(c, str, cp, pc)
    ensures ORc.ReachFV(c, str, ov, cp0, pc + 1, true, cp + 1)
  {
  }

  // ===========================================================================
  // MatchesVToPath
  // ===========================================================================

  /** `MatchesIterVHead` for nonempty chains. */
  lemma MatchesIterVNEHead(r: R.regex, k: nat, str: string, ov: LOr.OracleView, i: int, j: int) returns (m: int)
    requires k > 0
    requires MatchesIterVNE(r, k, str, ov, i, j)
    ensures i < m && MatchesV(r, str, ov, i, m) && MatchesIterVNE(r, k - 1, str, ov, m, j)
  {
    m :| i < m && MatchesV(r, str, ov, i, m) && MatchesIterVNE(r, k - 1, str, ov, m, j);
  }

  /** Both arms of a fork are V epsilon successors (fork edges are blind). */
  lemma ForkEdgesV(code: RB.code, str: string, ov: LOr.OracleView, cp: int, pc: nat, eb: bool, a: nat, b: nat)
    requires OB.ForkAt(code, pc, a, b)
    ensures ORc.EpsEdgeV(code, str, ov, cp, pc, eb, a, eb)
    ensures ORc.EpsEdgeV(code, str, ov, cp, pc, eb, b, eb)
  {
    if NR.GetPcRE(code, pc) == Some(RB.Fork(a as int, b as int)) {
      OB.GetPcInstr(code, pc, RB.Fork(a as int, b as int));
    } else {
      OB.GetPcInstr(code, pc, RB.Fork(b as int, a as int));
    }
  }

  /** The star loop, gated. */
  lemma StarLoopPathV(qid: R.quantid, r1: R.regex, code: RB.code, start: nat, es1: nat, endl: nat,
                      str: string, ov: LOr.OracleView, cp0: int, k: nat, i: int, j: int, eb: bool)
    requires NR.NestedFragmentRE(r1)
    requires OB.ForkAt(code, start, start + 1, endl)
    requires NR.GetPcRE(code, start + 1) == Some(RB.SetQuantToClock(qid, false))
    requires NR.GetPcRE(code, start + 2) == Some(RB.BeginLoop)
    requires NR.NfaRepRE(r1, code, start + 3, es1)
    requires NR.GetPcRE(code, es1) == Some(RB.EndLoop)
    requires NR.GetPcRE(code, es1 + 1) == Some(RB.Jmp(start as int))
    requires MatchesIterVNE(r1, k, str, ov, i, j)
    requires ORc.ReachFV(code, str, ov, cp0, start, eb, i)
    ensures ORc.ReachFV(code, str, ov, cp0, endl, if j > i then true else eb, j)
    decreases CP.rsize(r1), 1, k
  {
    if k == 0 {
      ForkEdgesV(code, str, ov, i, start, eb, start + 1, endl);
      ReachFVEpsIntro(code, str, ov, cp0, start, eb, endl, eb, i);
      return;
    }
    var m := MatchesIterVNEHead(r1, k, str, ov, i, j);
    MatchesIterVNEBounds(r1, k - 1, str, ov, m, j);
    ForkEdgesV(code, str, ov, i, start, eb, start + 1, endl);
    ReachFVEpsIntro(code, str, ov, cp0, start, eb, start + 1, eb, i);
    OB.GetPcInstr(code, start + 1, RB.SetQuantToClock(qid, false));
    ReachFVEpsIntro(code, str, ov, cp0, start + 1, eb, start + 2, eb, i);
    OB.GetPcInstr(code, start + 2, RB.BeginLoop);
    ReachFVEpsIntro(code, str, ov, cp0, start + 2, eb, start + 3, false, i);
    MatchesVToPath(r1, code, start + 3, es1, str, ov, cp0, i, m, false);
    assert ORc.ReachFV(code, str, ov, cp0, es1, true, m);
    OB.GetPcInstr(code, es1, RB.EndLoop);
    ReachFVEpsIntro(code, str, ov, cp0, es1, true, es1 + 1, true, m);
    OB.GetPcInstr(code, es1 + 1, RB.Jmp(start as int));
    ReachFVEpsIntro(code, str, ov, cp0, es1 + 1, true, start, true, m);
    StarLoopPathV(qid, r1, code, start, es1, endl, str, ov, cp0, k - 1, m, j, true);
  }

  /** The forced-copy chain, gated. */
  lemma MinChainPathV(n: nat, qid: R.quantid, r1: R.regex, code: RB.code, start: nat, endl: nat,
                      str: string, ov: LOr.OracleView, cp0: int, i: int, j: int, eb: bool)
    requires NR.NestedFragmentRE(r1)
    requires NR.NfaRepMinRE(n, qid, r1, code, start, endl)
    requires MatchesIterV(r1, n, str, ov, i, j)
    requires ORc.ReachFV(code, str, ov, cp0, start, eb, i)
    ensures ORc.ReachFV(code, str, ov, cp0, endl, if j > i then true else eb, j)
    decreases CP.rsize(r1), 1, n
  {
    if n == 0 { return; }
    var e1: nat :| NR.GetPcRE(code, start) == Some(RB.SetQuantToClock(qid, false))
      && NR.NfaRepRE(r1, code, start + 1, e1)
      && NR.NfaRepMinRE(n - 1, qid, r1, code, e1, endl);
    var m := MatchesIterVHead(r1, n, str, ov, i, j);
    MatchesVBounds(r1, str, ov, i, m);
    MatchesIterVBounds(r1, n - 1, str, ov, m, j);
    OB.GetPcInstr(code, start, RB.SetQuantToClock(qid, false));
    ReachFVEpsIntro(code, str, ov, cp0, start, eb, start + 1, eb, i);
    MatchesVToPath(r1, code, start + 1, e1, str, ov, cp0, i, m, eb);
    MinChainPathV(n - 1, qid, r1, code, e1, endl, str, ov, cp0, m, j, if m > i then true else eb);
  }

  /** The optional layers, gated. */
  lemma OptChainPathV(layers: nat, k2: nat, greedy: bool, qid: R.quantid, r1: R.regex,
                      code: RB.code, start: nat, endl: nat, str: string, ov: LOr.OracleView,
                      cp0: int, i: int, j: int, eb: bool)
    requires NR.NestedFragmentRE(r1)
    requires NR.NfaRepOptRE(layers, greedy, qid, r1, code, start, endl)
    requires MatchesIterVNE(r1, k2, str, ov, i, j)
    requires k2 <= layers
    requires ORc.ReachFV(code, str, ov, cp0, start, eb, i)
    ensures ORc.ReachFV(code, str, ov, cp0, endl, if j > i then true else eb, j)
    decreases CP.rsize(r1), 1, layers
  {
    if layers == 0 { return; }
    var e1: nat :| NR.GetPcRE(code, start) == Some(if greedy then RB.Fork(start + 1, endl as int) else RB.Fork(endl as int, start + 1))
      && NR.GetPcRE(code, start + 1) == Some(RB.SetQuantToClock(qid, false))
      && NR.GetPcRE(code, start + 2) == Some(RB.BeginLoop)
      && NR.NfaRepRE(r1, code, start + 3, e1)
      && NR.GetPcRE(code, e1) == Some(RB.EndLoop)
      && NR.NfaRepOptRE(layers - 1, greedy, qid, r1, code, e1 + 1, endl);
    assert OB.ForkAt(code, start, start + 1, endl);
    if k2 == 0 {
      ForkEdgesV(code, str, ov, i, start, eb, start + 1, endl);
      ReachFVEpsIntro(code, str, ov, cp0, start, eb, endl, eb, i);
      return;
    }
    var m := MatchesIterVNEHead(r1, k2, str, ov, i, j);
    MatchesIterVNEBounds(r1, k2 - 1, str, ov, m, j);
    ForkEdgesV(code, str, ov, i, start, eb, start + 1, endl);
    ReachFVEpsIntro(code, str, ov, cp0, start, eb, start + 1, eb, i);
    OB.GetPcInstr(code, start + 1, RB.SetQuantToClock(qid, false));
    ReachFVEpsIntro(code, str, ov, cp0, start + 1, eb, start + 2, eb, i);
    OB.GetPcInstr(code, start + 2, RB.BeginLoop);
    ReachFVEpsIntro(code, str, ov, cp0, start + 2, eb, start + 3, false, i);
    MatchesVToPath(r1, code, start + 3, e1, str, ov, cp0, i, m, false);
    assert ORc.ReachFV(code, str, ov, cp0, e1, true, m);
    OB.GetPcInstr(code, e1, RB.EndLoop);
    ReachFVEpsIntro(code, str, ov, cp0, e1, true, e1 + 1, true, m);
    OptChainPathV(layers - 1, k2 - 1, greedy, qid, r1, code, e1 + 1, endl, str, ov, cp0, m, j, true);
  }

  /** The do-while loop, gated. */
  lemma DoWhilePathV(krem: nat, qid: R.quantid, r1: R.regex, code: RB.code, em: nat, e1: nat,
                     endl: nat, str: string, ov: LOr.OracleView, cp0: int, i: int, j: int, eb: bool)
    requires NR.NestedFragmentRE(r1)
    requires R.nullable(r1) == R.NonNullable
    requires NR.GetPcRE(code, em) == Some(RB.SetQuantToClock(qid, false))
    requires NR.NfaRepRE(r1, code, em + 1, e1)
    requires OB.ForkAt(code, e1, em, endl)
    requires endl == e1 + 1
    requires krem >= 1
    requires MatchesIterV(r1, krem, str, ov, i, j)
    requires ORc.ReachFV(code, str, ov, cp0, em, eb, i)
    ensures ORc.ReachFV(code, str, ov, cp0, endl, true, j)
    decreases CP.rsize(r1), 1, krem
  {
    var m := MatchesIterVHead(r1, krem, str, ov, i, j);
    NonNullableNoEmptyMatchV(r1, str, ov, i);
    MatchesVBounds(r1, str, ov, i, m);
    assert i < m;
    OB.GetPcInstr(code, em, RB.SetQuantToClock(qid, false));
    ReachFVEpsIntro(code, str, ov, cp0, em, eb, em + 1, eb, i);
    MatchesVToPath(r1, code, em + 1, e1, str, ov, cp0, i, m, eb);
    assert ORc.ReachFV(code, str, ov, cp0, e1, true, m);
    ForkEdgesV(code, str, ov, m, e1, true, em, endl);
    if krem == 1 {
      ReachFVEpsIntro(code, str, ov, cp0, e1, true, endl, true, m);
      assert m == j;
    } else {
      ReachFVEpsIntro(code, str, ov, cp0, e1, true, em, true, m);
      DoWhilePathV(krem - 1, qid, r1, code, em, e1, endl, str, ov, cp0, m, j, true);
    }
  }

  /** THE forward bridge direction, gated: a `MatchesV` span of a NESTED-
      fragment regex yields a V path through its compiled block. The NEW case
      is `Re_lookaround`: its block is the single gate instruction, and the
      match clause IS the gate edge's guard. */
  lemma MatchesVToPath(re: R.regex, code: RB.code, start: nat, endl: nat,
                       str: string, ov: LOr.OracleView, cp0: int, i: int, j: int, eb: bool)
    requires NR.NestedFragmentRE(re)
    requires NR.NfaRepRE(re, code, start, endl)
    requires MatchesV(re, str, ov, i, j)
    requires ORc.ReachFV(code, str, ov, cp0, start, eb, i)
    ensures ORc.ReachFV(code, str, ov, cp0, endl, if j > i then true else eb, j)
    decreases CP.rsize(re), 0, 0
  {
    match re
    case Re_empty =>
    case Re_character(ch) =>
      OB.GetPcInstr(code, start, RB.Consume(T.ExpectationOf(ch)));
      assert ORc.ConsumeEdge(code, str, i, start);
      ReachFVConsumeIntro(code, str, ov, cp0, start, eb, i);
    case Re_anchor(a) =>
      OB.GetPcInstr(code, start, RB.AnchorAssertion(a));
      assert ORc.EpsEdgeV(code, str, ov, i, start, eb, start + 1, eb);
      ReachFVEpsIntro(code, str, ov, cp0, start, eb, start + 1, eb, i);
    case Re_lookaround(lid, la, r1) =>
      // one zero-width gate: the MatchesV clause is exactly the edge guard
      if la.Lookahead? || la.Lookbehind? {
        OB.GetPcInstr(code, start, RB.CheckOracle(lid));
        assert LOr.view_get_oracle(ov, i, lid);
        assert ORc.EpsEdgeV(code, str, ov, i, start, eb, start + 1, eb);
      } else {
        OB.GetPcInstr(code, start, RB.NegCheckOracle(lid));
        assert !LOr.view_get_oracle(ov, i, lid);
        assert ORc.EpsEdgeV(code, str, ov, i, start, eb, start + 1, eb);
      }
      ReachFVEpsIntro(code, str, ov, cp0, start, eb, start + 1, eb, i);
    case Re_alt(r1, r2) =>
      var e1: nat :| NR.GetPcRE(code, start) == Some(RB.Fork(start + 1, e1 + 1))
        && NR.NfaRepRE(r1, code, start + 1, e1)
        && NR.GetPcRE(code, e1) == Some(RB.Jmp(endl as int))
        && NR.NfaRepRE(r2, code, e1 + 1, endl);
      assert MatchesV(R.Re_alt(r1, r2), str, ov, i, j);
      OB.GetPcInstr(code, start, RB.Fork(start + 1, e1 + 1));
      if MatchesV(r1, str, ov, i, j) {
        ReachFVEpsIntro(code, str, ov, cp0, start, eb, start + 1, eb, i);
        MatchesVToPath(r1, code, start + 1, e1, str, ov, cp0, i, j, eb);
        OB.GetPcInstr(code, e1, RB.Jmp(endl as int));
        ReachFVEpsIntro(code, str, ov, cp0, e1, if j > i then true else eb, endl, if j > i then true else eb, j);
      } else {
        ReachFVEpsIntro(code, str, ov, cp0, start, eb, e1 + 1, eb, i);
        MatchesVToPath(r2, code, e1 + 1, endl, str, ov, cp0, i, j, eb);
      }
    case Re_con(r1, r2) =>
      var e1: nat :| NR.NfaRepRE(r1, code, start, e1) && NR.NfaRepRE(r2, code, e1, endl);
      assert MatchesV(R.Re_con(r1, r2), str, ov, i, j);
      assert exists m: int :: MatchesV(r1, str, ov, i, m) && MatchesV(r2, str, ov, m, j);
      var m: int :| MatchesV(r1, str, ov, i, m) && MatchesV(r2, str, ov, m, j);
      MatchesVBounds(r1, str, ov, i, m);
      MatchesVBounds(r2, str, ov, m, j);
      MatchesVToPath(r1, code, start, e1, str, ov, cp0, i, m, eb);
      MatchesVToPath(r2, code, e1, endl, str, ov, cp0, m, j, if m > i then true else eb);
    case Re_capture(cid, r1) =>
      var e1: nat :| NR.GetPcRE(code, start) == Some(RB.SetRegisterToCP(CP.start_reg(cid)))
        && NR.NfaRepRE(r1, code, start + 1, e1)
        && NR.GetPcRE(code, e1) == Some(RB.SetRegisterToCP(CP.end_reg(cid)))
        && endl == e1 + 1;
      OB.GetPcInstr(code, start, RB.SetRegisterToCP(CP.start_reg(cid)));
      ReachFVEpsIntro(code, str, ov, cp0, start, eb, start + 1, eb, i);
      MatchesVToPath(r1, code, start + 1, e1, str, ov, cp0, i, j, eb);
      OB.GetPcInstr(code, e1, RB.SetRegisterToCP(CP.end_reg(cid)));
      ReachFVEpsIntro(code, str, ov, cp0, e1, if j > i then true else eb, endl, if j > i then true else eb, j);
    case Re_quant(nul, qid, q, r1) =>
      assert MatchesV(R.Re_quant(nul, qid, q, r1), str, ov, i, j);
      assert exists k: nat :: q.min <= k && (q.max.Some? ==> k <= q.max.value)
                           && MatchesIterV(r1, k, str, ov, i, j);
      var k: nat :| q.min <= k && (q.max.Some? ==> k <= q.max.value)
                 && MatchesIterV(r1, k, str, ov, i, j);
      if q.min == 0 && q.max == None {
        var es1: nat :|
          NR.GetPcRE(code, start) == Some(if q.greedy then RB.Fork(start + 1, es1 + 2) else RB.Fork(es1 + 2, start + 1))
          && NR.GetPcRE(code, start + 1) == Some(RB.SetQuantToClock(qid, false))
          && NR.GetPcRE(code, start + 2) == Some(RB.BeginLoop)
          && NR.NfaRepRE(r1, code, start + 3, es1)
          && NR.GetPcRE(code, es1) == Some(RB.EndLoop)
          && NR.GetPcRE(code, es1 + 1) == Some(RB.Jmp(start as int))
          && endl == es1 + 2;
        assert OB.ForkAt(code, start, start + 1, endl);
        var k2 := IterVDropEmpty(r1, k, str, ov, i, j);
        StarLoopPathV(qid, r1, code, start, es1, endl, str, ov, cp0, k2, i, j, eb);
      } else if q.max.Some? {
        var em := NR.NfaRepREQuantInv(nul, qid, q, r1, code, start, endl);
        var mn := q.min as nat;
        var kx := (q.max.value - q.min) as nat;
        var mid := IterVSplit(r1, k, mn, str, ov, i, j);
        MinChainPathV(mn, qid, r1, code, start, em, str, ov, cp0, i, mid, eb);
        var k2 := IterVDropEmpty(r1, k - mn, str, ov, mid, j);
        MatchesIterVBounds(r1, mn, str, ov, i, mid);
        MatchesIterVBounds(r1, k - mn, str, ov, mid, j);
        OptChainPathV(kx, k2, q.greedy, qid, r1, code, em, endl, str, ov, cp0, mid, j,
                      if mid > i then true else eb);
      } else if nul != R.NonNullable {
        // §2.5a GENERIC: `min` forced copies, then the very star loop the
        // `q.min == 0` arm walks -- at `em` instead of `start`.
        var em, e1 := NR.NfaRepREGenInv(nul, qid, q, r1, code, start, endl);
        var mn := q.min as nat;
        var mid := IterVSplit(r1, k, mn, str, ov, i, j);
        MinChainPathV(mn, qid, r1, code, start, em, str, ov, cp0, i, mid, eb);
        MatchesIterVBounds(r1, mn, str, ov, i, mid);
        MatchesIterVBounds(r1, k - mn, str, ov, mid, j);
        assert OB.ForkAt(code, em, em + 1, endl);
        var k2 := IterVDropEmpty(r1, k - mn, str, ov, mid, j);
        StarLoopPathV(qid, r1, code, em, e1, endl, str, ov, cp0, k2, mid, j,
                      if mid > i then true else eb);
      } else {
        var em, e1 := NR.NfaRepREPlusInv(nul, qid, q, r1, code, start, endl);
        var mn1 := (q.min - 1) as nat;
        var mid := IterVSplit(r1, k, mn1, str, ov, i, j);
        MinChainPathV(mn1, qid, r1, code, start, em, str, ov, cp0, i, mid, eb);
        MatchesIterVBounds(r1, mn1, str, ov, i, mid);
        assert OB.ForkAt(code, e1, em, endl);
        DoWhilePathV(k - mn1, qid, r1, code, em, e1, endl, str, ov, cp0, mid, j,
                     if mid > i then true else eb);
        assert j > mid by {
          var mm := MatchesIterVHead(r1, k - mn1, str, ov, mid, j);
          NonNullableNoEmptyMatchV(r1, str, ov, mid);
          MatchesVBounds(r1, str, ov, mid, mm);
          MatchesIterVBounds(r1, k - mn1 - 1, str, ov, mm, j);
        }
      }
  }

  // ===========================================================================
  // The lazy-prefix walker, V (the dot-star head has no gates)
  // ===========================================================================

  /** The lazy `.*?` head reaches its own loop head at every position, in the
      V graph (all its edges are gate-free, so the blind walk replays). */
  lemma LazyPrefixHeadReachV(body: R.regex, code: RB.code, endl: nat, str: string, ov: LOr.OracleView, i: int)
    requires NR.NfaRepRE(R.lazy_prefix(body), code, 0, endl)
    requires 0 <= i <= |str|
    ensures ORc.ReachFV(code, str, ov, 0, 0, false, i) || ORc.ReachFV(code, str, ov, 0, 0, true, i)
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
      assert ORc.ReachFV(code, str, ov, 0, 0, false, 0);
    } else {
      LazyPrefixHeadReachV(body, code, endl, str, ov, i - 1);
      var eb: bool :| ORc.ReachFV(code, str, ov, 0, 0, eb, i - 1);
      assert ORc.EpsEdgeV(code, str, ov, i - 1, 0, eb, 1, eb);
      ReachFVEpsIntro(code, str, ov, 0, 0, eb, 1, eb, i - 1);
      assert ORc.EpsEdgeV(code, str, ov, i - 1, 1, eb, 2, eb);
      ReachFVEpsIntro(code, str, ov, 0, 1, eb, 2, eb, i - 1);
      assert ORc.EpsEdgeV(code, str, ov, i - 1, 2, eb, 3, false);
      ReachFVEpsIntro(code, str, ov, 0, 2, eb, 3, false, i - 1);
      assert AI.get_char(str, i - 1).Some?;
      assert RC.is_accepted(AI.get_char(str, i - 1), T.ExpectationOf(R.Dot));
      assert ORc.ConsumeEdge(code, str, i - 1, 3);
      ReachFVConsumeIntro(code, str, ov, 0, 3, false, i - 1);
      assert ORc.ReachFV(code, str, ov, 0, 4, true, i);
      assert ORc.EpsEdgeV(code, str, ov, i, es1, true, es1 + 1, true);
      ReachFVEpsIntro(code, str, ov, 0, es1, true, es1 + 1, true, i);
      assert ORc.EpsEdgeV(code, str, ov, i, es1 + 1, true, 0, true);
      ReachFVEpsIntro(code, str, ov, 0, es1 + 1, true, 0, true, i);
    }
  }

  /** The "start anywhere" walker, V. */
  lemma LazyPrefixBodyEntryV(body: R.regex, code: RB.code, endl: nat, str: string, ov: LOr.OracleView, i: int)
    returns (bentry: nat)
    requires NR.NfaRepRE(R.lazy_prefix(body), code, 0, endl)
    requires 0 <= i <= |str|
    ensures NR.NfaRepRE(body, code, bentry, endl)
    ensures ORc.ReachFV(code, str, ov, 0, bentry, false, i) || ORc.ReachFV(code, str, ov, 0, bentry, true, i)
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
    LazyPrefixHeadReachV(body, code, endl, str, ov, i);
    var eb: bool :| ORc.ReachFV(code, str, ov, 0, 0, eb, i);
    assert ORc.EpsEdgeV(code, str, ov, i, 0, eb, es1 + 2, eb);
    ReachFVEpsIntro(code, str, ov, 0, 0, eb, es1 + 2, eb, i);
  }

  /** `NestedFragmentRE` passes through `lazy_prefix` (the dot-star head is a
      plus-shape star over a character). */
  lemma NestedLazyPrefix(body: R.regex)
    requires NR.NestedFragmentRE(body)
    ensures NR.NestedFragmentRE(R.lazy_prefix(body))
  {
  }

  /** THE forward bridge, assembled and gated: a `MatchesV` span of the body
      ending at `cp` makes the build program's `WriteOracle(lid)` V-reachable
      at `cp` against the same view. */
  lemma MatchesVToReachesWriteV(body: R.regex, lid: R.lookid, str: string, ov: LOr.OracleView, i: int, cp: int)
    requires NR.NestedFragmentRE(body)
    requires 0 <= i <= |str|
    requires MatchesV(body, str, ov, i, cp)
    requires cp <= |str|
    ensures ORc.ReachesWriteV(CP.compile_to_write(R.lazy_prefix(body), lid), str, ov, 0, lid, cp)
  {
    NestedLazyPrefix(body);
    NR.CompileToWriteRepNested(R.lazy_prefix(body), lid);
    var code := CP.compile_to_write(R.lazy_prefix(body), lid);
    var next := CP.compile(R.lazy_prefix(body), 0, CP.Progress).1;
    var bentry := LazyPrefixBodyEntryV(body, code, next as nat, str, ov, i);
    var eb: bool :| ORc.ReachFV(code, str, ov, 0, bentry, eb, i);
    MatchesVToPath(body, code, bentry, next as nat, str, ov, 0, i, cp, eb);
    OB.GetPcInstr(code, next as nat, RB.WriteOracle(lid));
    assert ORc.ReachFV(code, str, ov, 0, next as nat, if cp > i then true else eb, cp);
  }
}
