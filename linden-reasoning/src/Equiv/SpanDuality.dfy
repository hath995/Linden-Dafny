// Lookaround campaign (L1), part C5 (§6.4 of linden-equiv's
// LOOKAROUND_CAMPAIGN.md): the spec-side span duality — groundwork.
//
// A lookbehind's spec truth at position cp is a BACKWARD tree walk of the
// (translated) body from cp; the engine's oracle characterization
// (OracleColumnCharacterized, linden-equiv) speaks of FORWARD span matches
// ending at cp. This file supplies the spec-side vocabulary and the two
// duality directions' targets:
//
//   MatchesL(rer, r, str, i, j) — "r matches exactly the span [i, j) of
//   str", an existence-level, DIRECTION-FREE predicate over the Linden AST
//   (spans have no scan order; direction only matters to walks).
//
//   SuccActs(rer, acts, inp, gm, dir) — the walk of `acts` from `inp`
//   succeeds: the (unique, ComputeTr) backtracking tree has a successful
//   leaf. By ResGroupMapIndep, success is independent of gm — and L1
//   bodies are GROUP-FREE after translation (capture-free bodies have no
//   Group nodes), so the group map is constant through the whole walk.
//
//   The duality (to prove, both directions, continuation-generalized):
//     SuccActs(rer, [Areg(r)] + cont, InputAt(str, j), gm, Backward)
//       <==> exists i :: MatchesL(rer, r, str, i, j)
//                        && SuccActs(rer, cont, InputAt(str, i), gm, Backward)
//   for group-free, lookaround-free, backreference-free `r`. Instantiated
//   at cont == [] this gives: the backward walk of the body from cp
//   succeeds iff the body matches some span ending at cp — the exact
//   counterpart of linden-equiv's RecorderHit.
include "Translate.dfy"

/** §6.4 groundwork: the Linden-side span predicate `MatchesL`, its chain
    algebra, the walk-success predicate `SuccActs`, and the group-free
    fragment facts. */
module LindenSpanDuality {
  import opened Std.Wrappers
  import LW = WarblreRegExpRecord
  import WP = WarblrePrimitives
  import LC = Chars
  import LG = Groups
  import L = Regex
  import LN = WarblreNumeric
  import LS = Semantics
  import LT = Tree
  import FU = FunctionalUtils
  import T = LindenElkTranslate

  // ===========================================================================
  // The fragment: what L1 lookbehind bodies translate to
  // ===========================================================================

  /** No `Group`, `LookaroundR`, or `Backreference` nodes — the image under
      `Translate` of a capture-free, look-free RegElk body (captures
      translate to `Group`, so capture-freedom erases them). */
  ghost predicate GroupFreeL(r: L.Regex)
    decreases r
  {
    match r
    case Epsilon => true
    case Character(_) => true
    case AnchorR(_) => true
    case Disjunction(r1, r2) => GroupFreeL(r1) && GroupFreeL(r2)
    case Sequence(r1, r2) => GroupFreeL(r1) && GroupFreeL(r2)
    case Quantified(_, _, _, r1) => GroupFreeL(r1)
    case Group(_, _) => false
    case LookaroundR(_, _) => false
    case Backreference(_) => false
  }

  /** Group-free regexes define no groups, so their quantifiers' `Reset`
      nodes reset nothing and the group map never changes. */
  lemma GroupFreeDefGroups(r: L.Regex)
    requires GroupFreeL(r)
    ensures L.DefGroups(r) == []
    decreases r
  {
    match r
    case Disjunction(r1, r2) => GroupFreeDefGroups(r1); GroupFreeDefGroups(r2);
    case Sequence(r1, r2) => GroupFreeDefGroups(r1); GroupFreeDefGroups(r2);
    case Quantified(_, _, _, r1) => GroupFreeDefGroups(r1);
    case _ =>
  }

  /** Resetting no groups is the identity. */
  lemma GMResetNil(gm: LG.GroupMap)
    ensures LG.GMReset([], gm) == gm
  {
  }

  // ===========================================================================
  // The span predicate
  // ===========================================================================

  /** `r` matches exactly the span `[i, j)` of `str` — existence-level and
      direction-free (a span is a span; only walks have directions).
      Characters test `CharMatch`; anchors test `AnchorSatisfied` at the
      span position. Lookarounds and backreferences have no rule (outside
      the L1 fragment). */
  ghost predicate MatchesL(rer: LW.RegExpRecord, r: L.Regex, str: string, i: int, j: int)
    decreases r, 0, 0
  {
    match r
    case Epsilon => i == j
    case Character(cd) =>
      j == i + 1 && 0 <= i < |str| && LC.CharMatch(rer, str[i], cd)
    case AnchorR(a) =>
      i == j && 0 <= i <= |str| && LS.AnchorSatisfied(rer, a, T.InputAt(str, i))
    case Disjunction(r1, r2) =>
      MatchesL(rer, r1, str, i, j) || MatchesL(rer, r2, str, i, j)
    case Sequence(r1, r2) =>
      exists m: int {:trigger MatchesL(rer, r2, str, m, j)} ::
        MatchesL(rer, r1, str, i, m) && MatchesL(rer, r2, str, m, j)
    case Quantified(greedy, min, delta, r1) =>
      exists k: nat {:trigger IterL(rer, r1, k, str, i, j)} ::
        min <= k
        && (match delta case Inf => true case NN(dx) => k <= min + dx)
        && IterL(rer, r1, k, str, i, j)
    case Group(gid, r1) => MatchesL(rer, r1, str, i, j)
    case LookaroundR(_, _) => false
    case Backreference(_) => false
  }

  /** `k` consecutive `r`-spans. */
  ghost predicate IterL(rer: LW.RegExpRecord, r: L.Regex, k: nat, str: string, i: int, j: int)
    decreases r, 1, k
  {
    if k == 0 then i == j
    else exists m: int {:trigger IterL(rer, r, k - 1, str, m, j)} ::
      MatchesL(rer, r, str, i, m) && IterL(rer, r, k - 1, str, m, j)
  }

  // ===========================================================================
  // Span-chain algebra (mirrors the engine side's, over the Linden AST)
  // ===========================================================================

  /** Spans never go backward. */
  lemma MatchesLBounds(rer: LW.RegExpRecord, r: L.Regex, str: string, i: int, j: int)
    requires MatchesL(rer, r, str, i, j)
    ensures i <= j
    decreases r, 0, 0
  {
    match r
    case Disjunction(r1, r2) =>
      if MatchesL(rer, r1, str, i, j) { MatchesLBounds(rer, r1, str, i, j); }
      else { MatchesLBounds(rer, r2, str, i, j); }
    case Sequence(r1, r2) =>
      var m: int :| MatchesL(rer, r1, str, i, m) && MatchesL(rer, r2, str, m, j);
      MatchesLBounds(rer, r1, str, i, m);
      MatchesLBounds(rer, r2, str, m, j);
    case Quantified(greedy, min, delta, r1) =>
      var k: nat :| min <= k
        && (match delta case Inf => true case NN(dx) => k <= min + dx)
        && IterL(rer, r1, k, str, i, j);
      IterLBounds(rer, r1, k, str, i, j);
    case Group(_, r1) => MatchesLBounds(rer, r1, str, i, j);
    case _ =>
  }

  /** `MatchesLBounds` for chains. */
  lemma IterLBounds(rer: LW.RegExpRecord, r: L.Regex, k: nat, str: string, i: int, j: int)
    requires IterL(rer, r, k, str, i, j)
    ensures i <= j
    decreases r, 1, k
  {
    if k > 0 {
      var m: int :| MatchesL(rer, r, str, i, m) && IterL(rer, r, k - 1, str, m, j);
      MatchesLBounds(rer, r, str, i, m);
      IterLBounds(rer, r, k - 1, str, m, j);
    }
  }

  /** Head inversion (top-level helper — nested destructures are
      fuel-fragile). */
  lemma IterLHead(rer: LW.RegExpRecord, r: L.Regex, k: nat, str: string, i: int, j: int)
    returns (m: int)
    requires k > 0
    requires IterL(rer, r, k, str, i, j)
    ensures MatchesL(rer, r, str, i, m) && IterL(rer, r, k - 1, str, m, j)
  {
    m :| MatchesL(rer, r, str, i, m) && IterL(rer, r, k - 1, str, m, j);
  }

  /** Prepend a span to a chain. */
  lemma IterLCons(rer: LW.RegExpRecord, r: L.Regex, k: nat, str: string, i: int, m: int, j: int)
    requires MatchesL(rer, r, str, i, m)
    requires IterL(rer, r, k, str, m, j)
    ensures IterL(rer, r, k + 1, str, i, j)
  {
  }

  /** Append a span to a chain. */
  lemma IterLSnoc(rer: LW.RegExpRecord, r: L.Regex, k: nat, str: string, i: int, m: int, j: int)
    requires IterL(rer, r, k, str, i, m)
    requires MatchesL(rer, r, str, m, j)
    ensures IterL(rer, r, k + 1, str, i, j)
    decreases k
  {
    if k == 0 {
      assert IterL(rer, r, 0, str, j, j);
      return;
    }
    var m1 := IterLHead(rer, r, k, str, i, m);
    IterLSnoc(rer, r, k - 1, str, m1, m, j);
    IterLCons(rer, r, k, str, i, m1, j);
  }

  /** Split a chain after its first `n` spans. */
  lemma IterLSplit(rer: LW.RegExpRecord, r: L.Regex, k: nat, n: nat, str: string, i: int, j: int)
    returns (mid: int)
    requires IterL(rer, r, k, str, i, j)
    requires n <= k
    ensures IterL(rer, r, n, str, i, mid) && IterL(rer, r, k - n, str, mid, j)
    decreases n
  {
    if n == 0 { mid := i; return; }
    var m := IterLHead(rer, r, k, str, i, j);
    mid := IterLSplit(rer, r, k - 1, n - 1, str, m, j);
  }

  /** Concatenate two chains. */
  lemma IterLConcat(rer: LW.RegExpRecord, r: L.Regex, a: nat, b: nat, str: string, i: int, m: int, j: int)
    requires IterL(rer, r, a, str, i, m)
    requires IterL(rer, r, b, str, m, j)
    ensures IterL(rer, r, a + b, str, i, j)
    decreases a
  {
    if a == 0 { return; }
    var m1 := IterLHead(rer, r, a, str, i, m);
    IterLConcat(rer, r, a - 1, b, str, m1, m, j);
    IterLCons(rer, r, a + b - 1, str, i, m1, j);
  }

  // ===========================================================================
  // Walk success
  // ===========================================================================

  /** The walk of `acts` from `inp` succeeds: the (unique) backtracking tree
      has a successful leaf. */
  ghost predicate SuccActs(rer: LW.RegExpRecord, acts: LS.Actions, inp: LC.Input,
                           gm: LG.GroupMap, dir: WP.Direction) {
    LT.TreeRes(FU.ComputeTr(rer, acts, inp, gm, dir), gm, inp, dir).Some?
  }

  /** The empty stack succeeds (its tree is the `Match` leaf). */
  lemma SuccActsNil(rer: LW.RegExpRecord, inp: LC.Input, gm: LG.GroupMap, dir: WP.Direction)
    ensures SuccActs(rer, [], inp, gm, dir)
  {
    FU.ComputeTrRw(rer, [], inp, gm, dir);
    assert FU.ComputeTrUnfold(rer, [], inp, gm, dir) == LT.Match;
  }
}
