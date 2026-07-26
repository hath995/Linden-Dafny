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
  import FS = FunctionalSemantics
  import SSx = StrictSuffix
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
    case LookaroundR(lk, r1) =>
      // L4 (nesting): a lookBEHIND is zero-width and succeeds at `i` exactly
      // when its body spans some `[m, i)` -- negated for the negative flavour.
      // Lookaheads are not in the fragment, so they still match nothing.
      (lk.LookBehind? || lk.NegLookBehind?)
      && i == j && 0 <= i <= |str|
      && (L.Positivity(lk) <==>
            exists m: int {:trigger MatchesL(rer, r1, str, m, i)} ::
              0 <= m <= i && MatchesL(rer, r1, str, m, i))
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

  // ===========================================================================
  // Reversing the STRING (L2): InputAt through the mirror
  // ===========================================================================

  /** Reversing the string reflects positions AND swaps the two halves of the
      input window: what was ahead of `cp` is now behind `|str| - cp`. This is
      the spec-side counterpart of `Mirror.cp_context` swapping prev/next. */
  lemma InputAtReverse(str: string, cp: int)
    requires 0 <= cp <= |str|
    ensures |LC.Reverse(str)| == |str|
    ensures T.InputAt(LC.Reverse(str), |str| - cp)
         == LC.Input(LC.Reverse(str[..cp]), str[cp..])
  {
    ReverseLength(str);
    var n := |str|;
    var rs := LC.Reverse(str);
    assert str == str[..cp] + str[cp..];
    SSx.ReverseApp(str[..cp], str[cp..]);
    assert rs == LC.Reverse(str[cp..]) + LC.Reverse(str[..cp]);
    ReverseLength(str[cp..]);
    ReverseLength(str[..cp]);
    assert |LC.Reverse(str[cp..])| == n - cp;
    // the tail of the reversal is the reversal of the head
    assert rs[n - cp..] == LC.Reverse(str[..cp]);
    assert rs[..n - cp] == LC.Reverse(str[cp..]);
    FS.ReverseReverse(str[cp..]);
    assert LC.Reverse(rs[..n - cp]) == str[cp..];
  }

  /** Index into a reversal. */
  lemma ReverseIndexAt<T>(sq: seq<T>, k: int)
    requires 0 <= k < |sq|
    ensures |LC.Reverse(sq)| == |sq|
    ensures LC.Reverse(sq)[k] == sq[|sq| - 1 - k]
    decreases |sq|
  {
    ReverseLength(sq);
    if |sq| > 0 {
      ReverseLength(sq[1..]);
      if k < |sq| - 1 {
        ReverseIndexAt(sq[1..], k);
        assert LC.Reverse(sq)[k] == LC.Reverse(sq[1..])[k];
      }
    }
  }

  /** `BeginInput <-> EndInput`; the boundary anchors are direction-blind.
      Reversing the string swaps which end is which. */
  function SwapAnchorL(a: L.Anchor): L.Anchor {
    match a
    case BeginInput => L.EndInput
    case EndInput => L.BeginInput
    case WordBoundary => L.WordBoundary
    case NonWordBoundary => L.NonWordBoundary
  }

  /** An anchor holds at `cp` in `str` exactly when its swap holds at the
      mirrored position in the reversal -- because `InputAtReverse` swaps the
      two halves of the window, and the boundary anchors read them
      symmetrically. */
  lemma AnchorSatisfiedReverse(rer: LW.RegExpRecord, a: L.Anchor, str: string, cp: int)
    requires 0 <= cp <= |str|
    ensures |LC.Reverse(str)| == |str|
    ensures LS.AnchorSatisfied(rer, SwapAnchorL(a), T.InputAt(LC.Reverse(str), |str| - cp))
        <==> LS.AnchorSatisfied(rer, a, T.InputAt(str, cp))
  {
    ReverseLength(str);
    InputAtReverse(str, cp);
    var inp := T.InputAt(str, cp);
    var rinp := T.InputAt(LC.Reverse(str), |str| - cp);
    assert rinp.pref == inp.next && rinp.next == inp.pref;
  }

  /** A regex reversed for the other scanning direction: concatenation order
      flips and input anchors swap. The spec-side counterpart of RegElk's
      `reverse_regex` (which leaves anchors alone, because the ENGINE handles
      them via its direction flag; reversing the STRING has to be explicit). */
  function RevL(r: L.Regex): L.Regex
    decreases r
  {
    match r
    case Epsilon => r
    case Character(_) => r
    case AnchorR(a) => L.AnchorR(SwapAnchorL(a))
    case Disjunction(r1, r2) => L.Disjunction(RevL(r1), RevL(r2))
    case Sequence(r1, r2) => L.Sequence(RevL(r2), RevL(r1))
    case Quantified(g, min, delta, r1) => L.Quantified(g, min, delta, RevL(r1))
    case Group(gid, r1) => L.Group(gid, RevL(r1))
    case LookaroundR(lk, r1) => r
    case Backreference(_) => r
  }

  lemma RevLGroupOk(r: L.Regex)
    requires GroupOkL(r)
    ensures GroupOkL(RevL(r))
    decreases r
  {
    match r
    case Disjunction(r1, r2) => RevLGroupOk(r1); RevLGroupOk(r2);
    case Sequence(r1, r2) => RevLGroupOk(r1); RevLGroupOk(r2);
    case Quantified(_, _, _, r1) => RevLGroupOk(r1);
    case Group(_, r1) => RevLGroupOk(r1);
    case _ =>
  }

  /** THE SPAN-LEVEL REVERSAL. `r` spans `[i, j)` of `str` exactly when
      `RevL(r)` spans the mirrored interval of the reversed string.

      Spans are existential, so unlike a tree-level reversal this needs no
      notion of priority -- which is why the ORACLE (a boolean) can be
      characterized this way while captures could not. */
  lemma MatchesLReverse(rer: LW.RegExpRecord, r: L.Regex, str: string, i: int, j: int)
    requires GroupOkL(r)
    requires 0 <= i <= j <= |str|
    ensures MatchesL(rer, RevL(r), LC.Reverse(str), |str| - j, |str| - i)
        <==> MatchesL(rer, r, str, i, j)
    decreases r, 0, 0
  {
    ReverseLength(str);
    var n := |str|;
    match r
    case Epsilon =>
    case Character(cd) =>
      if 0 <= i < n {
        ReverseIndexAt(str, n - 1 - i);
        assert LC.Reverse(str)[n - 1 - i] == str[i];
      }
      if 0 <= n - j < n {
        ReverseIndexAt(str, n - j);
        assert LC.Reverse(str)[n - j] == str[n - 1 - (n - j)];
      }
    case AnchorR(a) =>
      if i == j { AnchorSatisfiedReverse(rer, a, str, i); }
    case Disjunction(r1, r2) =>
      MatchesLReverse(rer, r1, str, i, j);
      MatchesLReverse(rer, r2, str, i, j);
    case Sequence(r1, r2) =>
      forall m: int | 0 <= m <= n
        ensures (MatchesL(rer, r1, str, i, m) && MatchesL(rer, r2, str, m, j))
            ==> (MatchesL(rer, RevL(r2), LC.Reverse(str), n - j, n - m)
                 && MatchesL(rer, RevL(r1), LC.Reverse(str), n - m, n - i))
      {
        if MatchesL(rer, r1, str, i, m) && MatchesL(rer, r2, str, m, j) {
          MatchesLBounds(rer, r1, str, i, m);
          MatchesLBounds(rer, r2, str, m, j);
          MatchesLReverse(rer, r1, str, i, m);
          MatchesLReverse(rer, r2, str, m, j);
        }
      }
      if MatchesL(rer, r, str, i, j) {
        assert MatchesL(rer, L.Sequence(r1, r2), str, i, j);
        assert exists m: int :: MatchesL(rer, r1, str, i, m) && MatchesL(rer, r2, str, m, j);
        var m: int :| MatchesL(rer, r1, str, i, m) && MatchesL(rer, r2, str, m, j);
        MatchesLBounds(rer, r1, str, i, m);
        MatchesLBounds(rer, r2, str, m, j);
        MatchesLReverse(rer, r1, str, i, m);
        MatchesLReverse(rer, r2, str, m, j);
        assert MatchesL(rer, RevL(r2), LC.Reverse(str), n - j, n - m);
        assert MatchesL(rer, RevL(r1), LC.Reverse(str), n - m, n - i);
      }
      if MatchesL(rer, RevL(r), LC.Reverse(str), n - j, n - i) {
        assert RevL(r) == L.Sequence(RevL(r2), RevL(r1));
        assert MatchesL(rer, L.Sequence(RevL(r2), RevL(r1)), LC.Reverse(str), n - j, n - i);
        assert exists q: int :: MatchesL(rer, RevL(r2), LC.Reverse(str), n - j, q)
                             && MatchesL(rer, RevL(r1), LC.Reverse(str), q, n - i);
        var m': int :| MatchesL(rer, RevL(r2), LC.Reverse(str), n - j, m')
                    && MatchesL(rer, RevL(r1), LC.Reverse(str), m', n - i);
        MatchesLBounds(rer, RevL(r2), LC.Reverse(str), n - j, m');
        MatchesLBounds(rer, RevL(r1), LC.Reverse(str), m', n - i);
        MatchesLReverse(rer, r2, str, n - m', j);
        MatchesLReverse(rer, r1, str, i, n - m');
        assert MatchesL(rer, r1, str, i, n - m') && MatchesL(rer, r2, str, n - m', j);
      }
    case Quantified(g, min, delta, r1) =>
      if MatchesL(rer, r, str, i, j) {
        assert MatchesL(rer, L.Quantified(g, min, delta, r1), str, i, j);
        assert exists k: nat :: min <= k
          && (match delta case Inf => true case NN(dx) => k <= min + dx)
          && IterL(rer, r1, k, str, i, j);
        var k: nat :| min <= k
          && (match delta case Inf => true case NN(dx) => k <= min + dx)
          && IterL(rer, r1, k, str, i, j);
        IterLReverse(rer, r1, k, str, i, j);
      }
      if MatchesL(rer, RevL(r), LC.Reverse(str), n - j, n - i) {
        assert RevL(r) == L.Quantified(g, min, delta, RevL(r1));
        assert MatchesL(rer, L.Quantified(g, min, delta, RevL(r1)), LC.Reverse(str),
                        n - j, n - i);
        assert exists k: nat :: min <= k
          && (match delta case Inf => true case NN(dx) => k <= min + dx)
          && IterL(rer, RevL(r1), k, LC.Reverse(str), n - j, n - i);
        var k: nat :| min <= k
          && (match delta case Inf => true case NN(dx) => k <= min + dx)
          && IterL(rer, RevL(r1), k, LC.Reverse(str), n - j, n - i);
        IterLReverseBack(rer, r1, k, str, i, j);
      }
    case Group(gid, r1) => MatchesLReverse(rer, r1, str, i, j);
  }

  /** The iterate form, forward direction. */
  lemma IterLReverse(rer: LW.RegExpRecord, r: L.Regex, k: nat, str: string, i: int, j: int)
    requires GroupOkL(r)
    requires 0 <= i <= j <= |str|
    requires IterL(rer, r, k, str, i, j)
    ensures IterL(rer, RevL(r), k, LC.Reverse(str), |str| - j, |str| - i)
    decreases r, 1, k
  {
    ReverseLength(str);
    var n := |str|;
    if k == 0 { return; }
    var m: int :| MatchesL(rer, r, str, i, m) && IterL(rer, r, k - 1, str, m, j);
    MatchesLBounds(rer, r, str, i, m);
    IterLBounds(rer, r, k - 1, str, m, j);
    MatchesLReverse(rer, r, str, i, m);
    IterLReverse(rer, r, k - 1, str, m, j);
    // the reversed chain runs the other way round
    assert IterL(rer, RevL(r), k - 1, LC.Reverse(str), n - j, n - m);
    assert MatchesL(rer, RevL(r), LC.Reverse(str), n - m, n - i);
    IterLSnoc(rer, RevL(r), k - 1, LC.Reverse(str), n - j, n - m, n - i);
  }

  /** ... and back. */
  lemma IterLReverseBack(rer: LW.RegExpRecord, r: L.Regex, k: nat, str: string, i: int, j: int)
    requires GroupOkL(r)
    requires 0 <= i <= j <= |str|
    requires IterL(rer, RevL(r), k, LC.Reverse(str), |str| - j, |str| - i)
    ensures IterL(rer, r, k, str, i, j)
    decreases r, 1, k
  {
    ReverseLength(str);
    var n := |str|;
    if k == 0 { return; }
    RevLGroupOk(r);
    var m': int :| MatchesL(rer, RevL(r), LC.Reverse(str), n - j, m')
                && IterL(rer, RevL(r), k - 1, LC.Reverse(str), m', n - i);
    MatchesLBounds(rer, RevL(r), LC.Reverse(str), n - j, m');
    IterLBounds(rer, RevL(r), k - 1, LC.Reverse(str), m', n - i);
    MatchesLReverse(rer, r, str, n - m', j);
    IterLReverseBack(rer, r, k - 1, str, i, n - m');
    IterLSnoc(rer, r, k - 1, str, i, n - m', j);
  }

  // ===========================================================================
  // Group maps do not decide SUCCESS
  // ===========================================================================

  /** `TreeRes` never lets the group map decide Some-vs-None: every node either
      ignores `gm`, threads it unchanged, or rewrites it (`GroupActionT`, and
      the positive `LK` arm) without touching whether a leaf is reached. So
      success of a fixed tree is gm-independent — for ANY tree, with no
      restriction on the regex that built it.

      This is the fact that lets the span duality carry `Group` nodes: a group
      changes the map the walk records, never whether the walk succeeds. */
  lemma TreeResSomeGmIndep(t: LT.Tree, gm1: LG.GroupMap, gm2: LG.GroupMap,
                           inp: LC.Input, dir: WP.Direction)
    ensures LT.TreeRes(t, gm1, inp, dir).Some? <==> LT.TreeRes(t, gm2, inp, dir).Some?
    decreases t
  {
    match t
    case Mismatch =>
    case Match =>
    case Choice(t1, t2) =>
      TreeResSomeGmIndep(t1, gm1, gm2, inp, dir);
      TreeResSomeGmIndep(t2, gm1, gm2, inp, dir);
    case Read(_, t1) =>
      TreeResSomeGmIndep(t1, gm1, gm2, LC.AdvanceInputP(inp, dir), dir);
    case Progress(t1) => TreeResSomeGmIndep(t1, gm1, gm2, inp, dir);
    case ReadBackRef(brStr, t0) =>
      TreeResSomeGmIndep(t0, gm1, gm2, LC.AdvanceInputN(inp, |brStr|, dir), dir);
    case AnchorPass(_, t0) => TreeResSomeGmIndep(t0, gm1, gm2, inp, dir);
    case GroupActionT(a, t1) =>
      TreeResSomeGmIndep(t1, LG.GMUpdate(a, LC.Idx(inp), gm1),
                             LG.GMUpdate(a, LC.Idx(inp), gm2), inp, dir);
    case LKFail(_, _) =>
    case LK(lk, tlk, t1) =>
      TreeResSomeGmIndep(tlk, gm1, gm2, inp, L.LkDir(lk));
      if L.Positivity(lk) {
        // the sub-walk's own result feeds t1's map; both sides reach t1
        // together by the IH on tlk, with (possibly different) maps
        match LT.TreeRes(tlk, gm1, inp, L.LkDir(lk)) {
          case None =>
          case Some(p1) =>
            var p2 := LT.TreeRes(tlk, gm2, inp, L.LkDir(lk)).value;
            TreeResSomeGmIndep(t1, p1.1, p2.1, inp, dir);
        }
      } else {
        TreeResSomeGmIndep(t1, gm1, gm2, inp, dir);
      }
  }

  /** Like `GroupFreeL`, but `Group` nodes ARE allowed: the image under
      `Translate` of a look-free RegElk body that MAY contain captures. Still
      no `LookaroundR` (bodies are look-free at L1/L3) and no `Backreference`
      -- a backreference is the one construct whose SUCCESS reads the group
      map, which is exactly what the lemmas below rule out. */
  ghost predicate GroupOkL(r: L.Regex)
    decreases r
  {
    match r
    case Epsilon => true
    case Character(_) => true
    case AnchorR(_) => true
    case Disjunction(r1, r2) => GroupOkL(r1) && GroupOkL(r2)
    case Sequence(r1, r2) => GroupOkL(r1) && GroupOkL(r2)
    case Quantified(_, _, _, r1) => GroupOkL(r1)
    case Group(_, r1) => GroupOkL(r1)
    case LookaroundR(_, _) => false
    case Backreference(_) => false
  }

  /** A group-free regex is in particular group-OK. */
  lemma GroupFreeIsGroupOk(r: L.Regex)
    requires GroupFreeL(r)
    ensures GroupOkL(r)
    decreases r
  {
    match r
    case Disjunction(r1, r2) => GroupFreeIsGroupOk(r1); GroupFreeIsGroupOk(r2);
    case Sequence(r1, r2) => GroupFreeIsGroupOk(r1); GroupFreeIsGroupOk(r2);
    case Quantified(_, _, _, r1) => GroupFreeIsGroupOk(r1);
    case _ =>
  }

  /** `GroupOkL` widened to admit `LookaroundR` too (L4, nesting). Still no
      `Backreference`: that is the ONLY construct whose success reads the group
      map, which is what makes the map-independence below true. */
  ghost predicate NoBackrefL(r: L.Regex)
    decreases r
  {
    match r
    case Epsilon => true
    case Character(_) => true
    case AnchorR(_) => true
    case Disjunction(r1, r2) => NoBackrefL(r1) && NoBackrefL(r2)
    case Sequence(r1, r2) => NoBackrefL(r1) && NoBackrefL(r2)
    case Quantified(_, _, _, r1) => NoBackrefL(r1)
    case Group(_, r1) => NoBackrefL(r1)
    case LookaroundR(_, r1) => NoBackrefL(r1)
    case Backreference(_) => false
  }

  ghost predicate NoBackrefActs(acts: LS.Actions) {
    forall i :: 0 <= i < |acts| ==>
      (acts[i].Acheck? || acts[i].Aclose? || (acts[i].Areg? && NoBackrefL(acts[i].r)))
  }

  lemma NoBackrefActsTail(acts: LS.Actions)
    requires |acts| > 0 && NoBackrefActs(acts)
    ensures NoBackrefActs(acts[1..])
  { forall i | 0 <= i < |acts[1..]| ensures acts[1..][i].Acheck? || acts[1..][i].Aclose?
      || (acts[1..][i].Areg? && NoBackrefL(acts[1..][i].r)) { assert acts[1..][i] == acts[i + 1]; } }

  lemma NoBackrefActsCons(a: LS.Action, acts: LS.Actions)
    requires NoBackrefActs(acts)
    requires a.Acheck? || a.Aclose? || (a.Areg? && NoBackrefL(a.r))
    ensures NoBackrefActs([a] + acts)
  { forall i | 0 <= i < |[a] + acts| ensures ([a] + acts)[i].Acheck? || ([a] + acts)[i].Aclose?
      || (([a] + acts)[i].Areg? && NoBackrefL(([a] + acts)[i].r)) {
      if i > 0 { assert ([a] + acts)[i] == acts[i - 1]; } } }

  /** Group-OK is in particular backreference-free. */
  lemma GroupOkIsNoBackref(r: L.Regex)
    requires GroupOkL(r)
    ensures NoBackrefL(r)
    decreases r
  {
    match r
    case Disjunction(r1, r2) => GroupOkIsNoBackref(r1); GroupOkIsNoBackref(r2);
    case Sequence(r1, r2) => GroupOkIsNoBackref(r1); GroupOkIsNoBackref(r2);
    case Quantified(_, _, _, r1) => GroupOkIsNoBackref(r1);
    case Group(_, r1) => GroupOkIsNoBackref(r1);
    case _ =>
  }

  lemma GroupOkActsIsNoBackref(acts: LS.Actions)
    requires GroupOkActs(acts)
    ensures NoBackrefActs(acts)
  { forall i | 0 <= i < |acts| && acts[i].Areg? ensures NoBackrefL(acts[i].r) {
      GroupOkIsNoBackref(acts[i].r); } }

  /** Action stacks the walk may carry: regexes are group-OK, and `Aclose`
      (pushed by a `Group`) is now permitted. */
  ghost predicate GroupOkActs(acts: LS.Actions) {
    forall i :: 0 <= i < |acts| ==>
      (acts[i].Acheck? || acts[i].Aclose? || (acts[i].Areg? && GroupOkL(acts[i].r)))
  }

  lemma GroupOkActsTail(acts: LS.Actions)
    requires |acts| > 0 && GroupOkActs(acts)
    ensures GroupOkActs(acts[1..])
  { forall i | 0 <= i < |acts[1..]| ensures acts[1..][i].Acheck? || acts[1..][i].Aclose?
      || (acts[1..][i].Areg? && GroupOkL(acts[1..][i].r)) { assert acts[1..][i] == acts[i + 1]; } }

  lemma GroupOkActsCons(a: LS.Action, acts: LS.Actions)
    requires GroupOkActs(acts)
    requires a.Acheck? || a.Aclose? || (a.Areg? && GroupOkL(a.r))
    ensures GroupOkActs([a] + acts)
  { forall i | 0 <= i < |[a] + acts| ensures ([a] + acts)[i].Acheck? || ([a] + acts)[i].Aclose?
      || (([a] + acts)[i].Areg? && GroupOkL(([a] + acts)[i].r)) {
      if i > 0 { assert ([a] + acts)[i] == acts[i - 1]; } } }

  /** The computed tree does not depend on the group map at all -- not merely
      its success, the WHOLE tree. Every node's payload carries only ids
      (`Open(gid)`, `Close(gid)`, `Reset(gidl)`), never the map itself, and
      the only construct whose control flow reads the map is `Backreference`,
      which `GroupOkL` excludes. */
  lemma ComputeTreeGroupOkGmIndep(rer: LW.RegExpRecord, act: LS.Actions, inp: LC.Input,
                                  gm1: LG.GroupMap, gm2: LG.GroupMap, dir: WP.Direction,
                                  fuel: nat)
    requires NoBackrefActs(act)
    ensures FS.ComputeTree(rer, act, inp, gm1, dir, fuel)
         == FS.ComputeTree(rer, act, inp, gm2, dir, fuel)
    decreases fuel
  {
    if fuel == 0 || |act| == 0 { return; }
    var f := fuel - 1;
    var cont := act[1..];
    NoBackrefActsTail(act);
    match act[0]
    case Acheck(strcheck) =>
      if SSx.IsStrictSuffix(inp, strcheck, dir) {
        ComputeTreeGroupOkGmIndep(rer, cont, inp, gm1, gm2, dir, f);
      }
    case Aclose(gid) =>
      ComputeTreeGroupOkGmIndep(rer, cont, inp, LG.GMClose(LC.Idx(inp), gid, gm1),
                                LG.GMClose(LC.Idx(inp), gid, gm2), dir, f);
    case Areg(r) =>
      match r
      case Epsilon => ComputeTreeGroupOkGmIndep(rer, cont, inp, gm1, gm2, dir, f);
      case Character(cd) =>
        match LC.ReadChar(rer, cd, inp, dir) {
          case None =>
          case Some(pair) => ComputeTreeGroupOkGmIndep(rer, cont, pair.1, gm1, gm2, dir, f);
        }
      case Disjunction(r1, r2) =>
        NoBackrefActsCons(LS.Areg(r1), cont);
        NoBackrefActsCons(LS.Areg(r2), cont);
        ComputeTreeGroupOkGmIndep(rer, [LS.Areg(r1)] + cont, inp, gm1, gm2, dir, f);
        ComputeTreeGroupOkGmIndep(rer, [LS.Areg(r2)] + cont, inp, gm1, gm2, dir, f);
      case Sequence(r1, r2) =>
        var na := LS.SeqList(r1, r2, dir) + cont;
        assert NoBackrefActs(na) by {
          if dir.Forward? {
            assert na == [LS.Areg(r1)] + ([LS.Areg(r2)] + cont);
            NoBackrefActsCons(LS.Areg(r2), cont);
            NoBackrefActsCons(LS.Areg(r1), [LS.Areg(r2)] + cont);
          } else {
            assert na == [LS.Areg(r2)] + ([LS.Areg(r1)] + cont);
            NoBackrefActsCons(LS.Areg(r1), cont);
            NoBackrefActsCons(LS.Areg(r2), [LS.Areg(r1)] + cont);
          }
        }
        ComputeTreeGroupOkGmIndep(rer, na, inp, gm1, gm2, dir, f);
      case Quantified(greedy, min, delta, r1) =>
        var gidl := L.DefGroups(r1);
        if min > 0 {
          var quant := L.Quantified(greedy, min - 1, delta, r1);
          var na := [LS.Areg(r1), LS.Areg(quant)] + cont;
          assert NoBackrefActs(na) by {
            assert na == [LS.Areg(r1)] + ([LS.Areg(quant)] + cont);
            NoBackrefActsCons(LS.Areg(quant), cont);
            NoBackrefActsCons(LS.Areg(r1), [LS.Areg(quant)] + cont);
          }
          // the Reset payload is `gidl`, which depends only on r1
          ComputeTreeGroupOkGmIndep(rer, na, inp, LG.GMReset(gidl, gm1),
                                    LG.GMReset(gidl, gm2), dir, f);
        } else if delta == LN.NN(0) {
          ComputeTreeGroupOkGmIndep(rer, cont, inp, gm1, gm2, dir, f);
        } else {
          var quant := L.Quantified(greedy, 0, FS.NoiPred(delta), r1);
          var na := [LS.Areg(r1), LS.Acheck(inp), LS.Areg(quant)] + cont;
          assert NoBackrefActs(na) by {
            assert na == [LS.Areg(r1)] + ([LS.Acheck(inp)] + ([LS.Areg(quant)] + cont));
            NoBackrefActsCons(LS.Areg(quant), cont);
            NoBackrefActsCons(LS.Acheck(inp), [LS.Areg(quant)] + cont);
            NoBackrefActsCons(LS.Areg(r1), [LS.Acheck(inp)] + ([LS.Areg(quant)] + cont));
          }
          ComputeTreeGroupOkGmIndep(rer, na, inp, LG.GMReset(gidl, gm1),
                                    LG.GMReset(gidl, gm2), dir, f);
          ComputeTreeGroupOkGmIndep(rer, cont, inp, gm1, gm2, dir, f);
        }
      case Group(gid, r1) =>
        var na := [LS.Areg(r1), LS.Aclose(gid)] + cont;
        assert NoBackrefActs(na) by {
          assert na == [LS.Areg(r1)] + ([LS.Aclose(gid)] + cont);
          NoBackrefActsCons(LS.Aclose(gid), cont);
          NoBackrefActsCons(LS.Areg(r1), [LS.Aclose(gid)] + cont);
        }
        ComputeTreeGroupOkGmIndep(rer, na, inp, LG.GMOpen(LC.Idx(inp), gid, gm1),
                                  LG.GMOpen(LC.Idx(inp), gid, gm2), dir, f);
      case LookaroundR(lk, r1) =>
        // the sub-walk's tree is map-independent by the IH; WHETHER the
        // lookaround passes is map-independent by TreeResSomeGmIndep; and the
        // map it hands the continuation (`gmlk`) differs between the two runs
        // but the IH says the continuation's tree does not depend on it
        NoBackrefActsCons(LS.Areg(r1), []);
        assert [LS.Areg(r1)] == [LS.Areg(r1)] + [];
        ComputeTreeGroupOkGmIndep(rer, [LS.Areg(r1)], inp, gm1, gm2, L.LkDir(lk), f);
        var o1 := FS.ComputeTree(rer, [LS.Areg(r1)], inp, gm1, L.LkDir(lk), f);
        if o1.Some? {
          var treelk := o1.value;
          TreeResSomeGmIndep(treelk, gm1, gm2, inp, L.LkDir(lk));
          match LS.LkResult(lk, treelk, gm1, inp) {
            case None =>
            case Some(gmlk1) =>
              var gmlk2 := LS.LkResult(lk, treelk, gm2, inp).value;
              ComputeTreeGroupOkGmIndep(rer, cont, inp, gmlk1, gmlk2, dir, f);
          }
        }
      case AnchorR(a) =>
        if LS.AnchorSatisfied(rer, a, inp) {
          ComputeTreeGroupOkGmIndep(rer, cont, inp, gm1, gm2, dir, f);
        }
      case Backreference(gid) =>    // excluded by GroupOkL
  }

  /** SUCCESS of a walk is group-map independent: the tree is the same
      (`ComputeTreeGroupOkGmIndep`) and reading a leaf out of a fixed tree
      never lets the map decide Some-vs-None (`TreeResSomeGmIndep`).

      This is what lets the span duality below carry captures: a `Group` node
      changes the map the walk RECORDS, never whether the walk succeeds. */
  lemma SuccActsGmIndep(rer: LW.RegExpRecord, acts: LS.Actions, inp: LC.Input,
                        gm1: LG.GroupMap, gm2: LG.GroupMap, dir: WP.Direction)
    requires NoBackrefActs(acts)
    ensures SuccActs(rer, acts, inp, gm1, dir) <==> SuccActs(rer, acts, inp, gm2, dir)
  {
    var fuel := FS.ActionsFuel(acts, inp, dir) + 1;
    FS.FunctionalTerminates(rer, acts, inp, gm1, dir, fuel);
    FS.FunctionalTerminates(rer, acts, inp, gm2, dir, fuel);
    ComputeTreeGroupOkGmIndep(rer, acts, inp, gm1, gm2, dir, fuel);
    FU.ComputeTrRw(rer, acts, inp, gm1, dir);
    FU.ComputeTrRw(rer, acts, inp, gm2, dir);
    assert FU.ComputeTr(rer, acts, inp, gm1, dir) == FU.ComputeTr(rer, acts, inp, gm2, dir);
    TreeResSomeGmIndep(FU.ComputeTr(rer, acts, inp, gm1, dir), gm1, gm2, inp, dir);
  }

  // NEXT STEP (L4, nesting): `MatchesL` now has a real `LookaroundR` case, and
  // the map-independence above already admits nested lookarounds. What remains
  // on the spec side is the `Bwd*` `LookaroundR` arm: a nested lookBEHIND is
  // zero-width, so the walk neither consumes nor moves -- it succeeds exactly
  // when the sub-walk of its body from the SAME position does, which is the
  // `MatchesL` clause. The engine side is the lid-induction: `FBuildLids`
  // counts DOWN from maxlook and `annotate` gives an outer lookaround a
  // SMALLER lid than its body's, so inner columns are always built first and
  // an outer build reads them already-correct. `FBuildOracleCorrect` is
  // ALREADY nesting-agnostic (it characterizes the bit operationally via
  // ReachesWrite); the look-free assumption to remove lives in
  // `OracleSpec.OracleColumnSpec`, whose `TranslateGroupFree` + `SpanDuality`
  // steps are what currently force a look-free body.
  //
  // NEXT STEP (L3): widen the `Bwd*` family from `GroupFreeL` to `GroupOkL`.
  // The Group case of `BwdComplete` is straightforward with the lemmas above
  // (push `Areg(r1), Aclose(gid)` under `GMOpen`, land back on `cont` with a
  // rewritten map that `SuccActsGmIndep` discards). What blocks a one-shot
  // widening is the QUANTIFIER proofs: `BwdCompleteQuant`/`BwdCompleteFree`/
  // `BwdSoundQuant` currently lean on `GroupFreeDefGroups` + `GMResetNil` to
  // treat a layer's `Reset` as a NO-OP and keep `gm` constant across
  // iterations. With groups present `DefGroups(r1)` is nonempty, so each layer
  // really resets and the recursion must thread `GMReset(DefGroups(r1), gm)`,
  // re-anchoring each recursive call's continuation hypothesis through
  // `SuccActsGmIndep`. Mechanical, ~6 sites, but not a signature change.

  // ===========================================================================
  // Backward-walk plumbing at InputAt positions
  // ===========================================================================

  /** `Reverse` seen from the other end: head of the reversal is the last
      element, tail of the reversal reverses the rest. */
  lemma ReverseSnocView<T>(s: seq<T>)
    requires |s| > 0
    ensures LC.Reverse(s) == [s[|s| - 1]] + LC.Reverse(s[..|s| - 1])
    decreases |s|
  {
    if |s| == 1 {
      assert s[..0] == [];
    } else {
      ReverseSnocView(s[1..]);
      assert s[1..][..|s| - 2] == s[..|s| - 1][1..];
      assert s[1..][|s[1..]| - 1] == s[|s| - 1];
      assert LC.Reverse(s[..|s| - 1]) == LC.Reverse(s[..|s| - 1][1..]) + [s[..|s| - 1][0]];
      assert s[..|s| - 1][0] == s[0];
    }
  }

  /** Peeling one character backward off `InputAt(str, j)` lands exactly on
      `InputAt(str, j - 1)` — the single fact the whole backward walk runs
      on. */
  lemma InputAtPeel(str: string, j: int)
    requires 0 < j <= |str|
    ensures var ia := T.InputAt(str, j);
      |ia.pref| > 0
      && ia.pref[0] == str[j - 1]
      && LC.Input([ia.pref[0]] + ia.next, ia.pref[1..]) == T.InputAt(str, j - 1)
  {
    var ia := T.InputAt(str, j);
    ReverseSnocView(str[..j]);
    assert str[..j][|str[..j]| - 1] == str[j - 1];
    assert str[..j][..j - 1] == str[..j - 1];
    assert ia.pref == [str[j - 1]] + LC.Reverse(str[..j - 1]);
    assert ia.pref[1..] == LC.Reverse(str[..j - 1]);
    assert [str[j - 1]] + str[j..] == str[j - 1..];
  }

  /** `AdvanceInputP` backward at an `InputAt` position steps to the previous
      position. */
  lemma AdvanceInputPBackAt(str: string, j: int)
    requires 0 < j <= |str|
    ensures LC.AdvanceInputP(T.InputAt(str, j), WP.Backward) == T.InputAt(str, j - 1)
  {
    InputAtPeel(str, j);
  }

  /** Reading backward at `InputAt(str, j)` under a matching descriptor
      yields the previous character and position. */
  lemma ReadCharBackAt(rer: LW.RegExpRecord, cd: LC.CharDescr, str: string, j: int)
    requires 0 < j <= |str|
    requires LC.CharMatch(rer, str[j - 1], cd)
    ensures LC.ReadChar(rer, cd, T.InputAt(str, j), WP.Backward)
         == Some((str[j - 1], T.InputAt(str, j - 1)))
  {
    InputAtPeel(str, j);
  }

  /** Backward strict-suffix at `InputAt` positions is just `mid < j`. */
  lemma StrictSuffixBackAt(str: string, mid: int, j: int)
    requires 0 <= mid < j <= |str|
    ensures SSx.IsStrictSuffix(T.InputAt(str, mid), T.InputAt(str, j), WP.Backward)
    decreases j - mid
  {
    InputAtPeel(str, j);
    var ia := T.InputAt(str, j);
    if mid == j - 1 {
      assert LC.Input([ia.pref[0]] + ia.next, ia.pref[1..]) == T.InputAt(str, mid);
    } else {
      StrictSuffixBackAt(str, mid, j - 1);
      var ib := T.InputAt(str, j - 1);
      assert SSx.StrictSuffixBackward(T.InputAt(str, mid), ib.next, ib.pref);
      assert [ia.pref[0]] + ia.next == ib.next && ia.pref[1..] == ib.pref;
    }
  }

  /** Updating with an empty `Reset` changes nothing. */
  lemma GMUpdateResetNil(idx: nat, gm: LG.GroupMap)
    ensures LG.GMUpdate(LG.Reset([]), idx, gm) == gm
  {
  }

  // ===========================================================================
  // Nonempty chains (what the Acheck progress guard admits)
  // ===========================================================================

  /** Chains whose every span consumes. */
  ghost predicate IterLNE(rer: LW.RegExpRecord, r: L.Regex, k: nat, str: string, i: int, j: int)
    decreases r, 2, k
  {
    if k == 0 then i == j
    else exists m: int {:trigger IterLNE(rer, r, k - 1, str, m, j)} ::
      i < m && MatchesL(rer, r, str, i, m) && IterLNE(rer, r, k - 1, str, m, j)
  }

  lemma IterLNEHead(rer: LW.RegExpRecord, r: L.Regex, k: nat, str: string, i: int, j: int)
    returns (m: int)
    requires k > 0
    requires IterLNE(rer, r, k, str, i, j)
    ensures i < m && MatchesL(rer, r, str, i, m) && IterLNE(rer, r, k - 1, str, m, j)
  {
    m :| i < m && MatchesL(rer, r, str, i, m) && IterLNE(rer, r, k - 1, str, m, j);
  }

  lemma IterLNECons(rer: LW.RegExpRecord, r: L.Regex, k: nat, str: string, i: int, m: int, j: int)
    requires i < m && MatchesL(rer, r, str, i, m)
    requires IterLNE(rer, r, k, str, m, j)
    ensures IterLNE(rer, r, k + 1, str, i, j)
  {
  }

  /** `IterLBounds` for nonempty chains. */
  lemma IterLNEBounds(rer: LW.RegExpRecord, r: L.Regex, k: nat, str: string, i: int, j: int)
    requires IterLNE(rer, r, k, str, i, j)
    ensures i <= j
    decreases r, 2, k
  {
    if k > 0 {
      var m := IterLNEHead(rer, r, k, str, i, j);
      IterLNEBounds(rer, r, k - 1, str, m, j);
    }
  }

  /** Empty iterations are droppable. */
  lemma IterLDropEmpty(rer: LW.RegExpRecord, r: L.Regex, k: nat, str: string, i: int, j: int)
    returns (k2: nat)
    requires IterL(rer, r, k, str, i, j)
    ensures k2 <= k && IterLNE(rer, r, k2, str, i, j)
    decreases k
  {
    if k == 0 { k2 := 0; return; }
    var m := IterLHead(rer, r, k, str, i, j);
    if m == i {
      k2 := IterLDropEmpty(rer, r, k - 1, str, m, j);
    } else {
      MatchesLBounds(rer, r, str, i, m);
      var kk := IterLDropEmpty(rer, r, k - 1, str, m, j);
      IterLNECons(rer, r, kk, str, i, m, j);
      k2 := kk + 1;
    }
  }

  /** Split a nonempty chain after its first `n` spans. */
  lemma IterLNESplit(rer: LW.RegExpRecord, r: L.Regex, k: nat, n: nat, str: string, i: int, j: int)
    returns (mid: int)
    requires IterLNE(rer, r, k, str, i, j)
    requires n <= k
    ensures IterLNE(rer, r, n, str, i, mid) && IterLNE(rer, r, k - n, str, mid, j)
    decreases n
  {
    if n == 0 { mid := i; return; }
    var m := IterLNEHead(rer, r, k, str, i, j);
    mid := IterLNESplit(rer, r, k - 1, n - 1, str, m, j);
    IterLNECons(rer, r, n - 1, str, i, m, mid);
  }

  // ===========================================================================
  // BwdComplete: a span match makes the backward walk succeed
  // ===========================================================================

  /** THE completeness direction: if `r` matches `[i, j)` and the
      continuation's backward walk succeeds from position `i`, then the walk
      of `[Areg(r)] + cont` from position `j` succeeds. Group-free `r` keeps
      the group map constant throughout. */
  lemma BwdComplete(rer: LW.RegExpRecord, r: L.Regex, cont: LS.Actions, str: string,
                    i: int, j: int, gm: LG.GroupMap)
    requires GroupFreeL(r)
    requires 0 <= i <= j <= |str|
    requires MatchesL(rer, r, str, i, j)
    requires SuccActs(rer, cont, T.InputAt(str, i), gm, WP.Backward)
    ensures SuccActs(rer, [LS.Areg(r)] + cont, T.InputAt(str, j), gm, WP.Backward)
    decreases r, 1, 0
  {
    var inp := T.InputAt(str, j);
    var acts := [LS.Areg(r)] + cont;
    FU.ComputeTrRw(rer, acts, inp, gm, WP.Backward);
    assert acts[0] == LS.Areg(r) && acts[1..] == cont;
    match r
    case Epsilon =>
      assert i == j;
    case Character(cd) =>
      assert j == i + 1 && LC.CharMatch(rer, str[i], cd);
      ReadCharBackAt(rer, cd, str, j);
      AdvanceInputPBackAt(str, j);
      var tc := FU.ComputeTr(rer, cont, T.InputAt(str, i), gm, WP.Backward);
      assert FU.ComputeTr(rer, acts, inp, gm, WP.Backward) == LT.Read(str[i], tc);
      assert LT.TreeRes(LT.Read(str[i], tc), gm, inp, WP.Backward)
          == LT.TreeRes(tc, gm, T.InputAt(str, i), WP.Backward);
    case AnchorR(a) =>
      assert i == j && LS.AnchorSatisfied(rer, a, inp);
    case Disjunction(r1, r2) =>
      assert MatchesL(rer, L.Disjunction(r1, r2), str, i, j);
      var t1 := FU.ComputeTr(rer, [LS.Areg(r1)] + cont, inp, gm, WP.Backward);
      var t2 := FU.ComputeTr(rer, [LS.Areg(r2)] + cont, inp, gm, WP.Backward);
      assert FU.ComputeTr(rer, acts, inp, gm, WP.Backward) == LT.Choice(t1, t2);
      if MatchesL(rer, r1, str, i, j) {
        BwdComplete(rer, r1, cont, str, i, j, gm);
        assert LT.TreeRes(t1, gm, inp, WP.Backward).Some?;
      } else {
        BwdComplete(rer, r2, cont, str, i, j, gm);
        assert LT.TreeRes(t2, gm, inp, WP.Backward).Some?;
      }
    case Sequence(r1, r2) =>
      assert MatchesL(rer, L.Sequence(r1, r2), str, i, j);
      assert exists m: int :: MatchesL(rer, r1, str, i, m) && MatchesL(rer, r2, str, m, j);
      var m: int :| MatchesL(rer, r1, str, i, m) && MatchesL(rer, r2, str, m, j);
      MatchesLBounds(rer, r1, str, i, m);
      MatchesLBounds(rer, r2, str, m, j);
      BwdComplete(rer, r1, cont, str, i, m, gm);
      BwdComplete(rer, r2, [LS.Areg(r1)] + cont, str, m, j, gm);
      assert LS.SeqList(r1, r2, WP.Backward) + cont == [LS.Areg(r2)] + ([LS.Areg(r1)] + cont);
    case Quantified(greedy, min, delta, r1) =>
      assert MatchesL(rer, L.Quantified(greedy, min, delta, r1), str, i, j);
      assert exists k: nat :: (min <= k
        && (match delta case Inf => true case NN(dx) => k <= min + dx)
        && IterL(rer, r1, k, str, i, j));
      var k: nat :| min <= k
        && (match delta case Inf => true case NN(dx) => k <= min + dx)
        && IterL(rer, r1, k, str, i, j);
      BwdCompleteQuant(rer, greedy, min, delta, r1, cont, str, i, j, gm, k);
    case Group(_, _) =>
    case LookaroundR(_, _) =>
    case Backreference(_) =>
  }

  /** `BwdComplete` for quantifiers: `k` admissible spans walk the
      quantifier's own unfolding — forced copies peel the RIGHTMOST span
      first (the action list is head-first regardless of direction), and
      the free layers take only consuming spans through the `Acheck`
      progress guard. */
  lemma BwdCompleteQuant(rer: LW.RegExpRecord, greedy: bool, min: nat, delta: LN.NoI,
                         r1: L.Regex, cont: LS.Actions, str: string,
                         i: int, j: int, gm: LG.GroupMap, k: nat)
    requires GroupFreeL(r1)
    requires 0 <= i <= j <= |str|
    requires min <= k
    requires match delta case Inf => true case NN(dx) => k <= min + dx
    requires IterL(rer, r1, k, str, i, j)
    requires SuccActs(rer, cont, T.InputAt(str, i), gm, WP.Backward)
    ensures SuccActs(rer, [LS.Areg(L.Quantified(greedy, min, delta, r1))] + cont,
                     T.InputAt(str, j), gm, WP.Backward)
    decreases r1, 3, k + min
  {
    var inp := T.InputAt(str, j);
    var q := L.Quantified(greedy, min, delta, r1);
    var acts := [LS.Areg(q)] + cont;
    FU.ComputeTrRw(rer, acts, inp, gm, WP.Backward);
    assert acts[0] == LS.Areg(q) && acts[1..] == cont;
    GroupFreeDefGroups(r1);
    GMResetNil(gm);
    if min > 0 {
      // peel the last span into the head copy; the rest recurse
      var mid := IterLSplit(rer, r1, k, k - 1, str, i, j);
      IterLBounds(rer, r1, k - 1, str, i, mid);
      var mm := IterLHead(rer, r1, k - (k - 1), str, mid, j);
      assert mm == j;
      MatchesLBounds(rer, r1, str, mid, j);
      var inner := [LS.Areg(L.Quantified(greedy, min - 1, delta, r1))] + cont;
      BwdCompleteQuant(rer, greedy, min - 1, delta, r1, cont, str, i, mid, gm, k - 1);
      BwdComplete(rer, r1, inner, str, mid, j, gm);
      assert [LS.Areg(r1), LS.Areg(L.Quantified(greedy, min - 1, delta, r1))] + cont
          == [LS.Areg(r1)] + inner;
      var titer := FU.ComputeTr(rer, [LS.Areg(r1)] + inner, inp, gm, WP.Backward);
      assert FU.ComputeTr(rer, acts, inp, gm, WP.Backward) == LT.GroupActionT(LG.Reset([]), titer);
      GMUpdateResetNil(LC.Idx(inp), gm);
      assert LT.TreeRes(LT.GroupActionT(LG.Reset([]), titer), gm, inp, WP.Backward)
          == LT.TreeRes(titer, gm, inp, WP.Backward);
    } else if delta == LN.NN(0) {
      assert k == 0;
    } else {
      var k2 := IterLDropEmpty(rer, r1, k, str, i, j);
      BwdCompleteFree(rer, greedy, delta, r1, cont, str, i, j, gm, k2);
    }
  }

  /** The free layers: a NONEMPTY chain of `k2` admissible spans takes the
      iterate branch `k2` times (each passes the `Acheck` strict-progress
      guard), then the skip branch. */
  lemma BwdCompleteFree(rer: LW.RegExpRecord, greedy: bool, delta: LN.NoI,
                        r1: L.Regex, cont: LS.Actions, str: string,
                        i: int, j: int, gm: LG.GroupMap, k2: nat)
    requires GroupFreeL(r1)
    requires 0 <= i <= j <= |str|
    requires delta != LN.NN(0) || k2 == 0
    requires match delta case Inf => true case NN(dx) => k2 <= dx
    requires IterLNE(rer, r1, k2, str, i, j)
    requires SuccActs(rer, cont, T.InputAt(str, i), gm, WP.Backward)
    ensures SuccActs(rer, [LS.Areg(L.Quantified(greedy, 0, delta, r1))] + cont,
                     T.InputAt(str, j), gm, WP.Backward)
    decreases r1, 2, k2
  {
    var inp := T.InputAt(str, j);
    var q := L.Quantified(greedy, 0, delta, r1);
    var acts := [LS.Areg(q)] + cont;
    FU.ComputeTrRw(rer, acts, inp, gm, WP.Backward);
    assert acts[0] == LS.Areg(q) && acts[1..] == cont;
    GroupFreeDefGroups(r1);
    GMResetNil(gm);
    if k2 == 0 {
      // i == j: the skip branch carries the continuation's success
      if delta == LN.NN(0) {
        return;
      }
      var tskip := FU.ComputeTr(rer, cont, inp, gm, WP.Backward);
      var titer := FU.ComputeTr(rer, [LS.Areg(r1), LS.Acheck(inp), LS.Areg(L.Quantified(greedy, 0, FS.NoiPred(delta), r1))] + cont,
                                inp, gm, WP.Backward);
      assert FU.ComputeTr(rer, acts, inp, gm, WP.Backward)
          == LT.GreedyChoice(greedy, LT.GroupActionT(LG.Reset([]), titer), tskip);
      assert LT.TreeRes(tskip, gm, inp, WP.Backward).Some?;
    } else {
      // nonempty chain: last span through this layer, the rest recurse
      var mid := IterLNESplit(rer, r1, k2, k2 - 1, str, i, j);
      IterLNEBounds(rer, r1, k2 - 1, str, i, mid);
      var mm := IterLNEHead(rer, r1, k2 - (k2 - 1), str, mid, j);
      assert mm == j && mid < j;
      var qpred := L.Quantified(greedy, 0, FS.NoiPred(delta), r1);
      var inner := [LS.Acheck(inp), LS.Areg(qpred)] + cont;
      // the guard passes at mid, and the smaller quantifier finishes there
      BwdCompleteFree(rer, greedy, FS.NoiPred(delta), r1, cont, str, i, mid, gm, k2 - 1);
      var inpMid := T.InputAt(str, mid);
      FU.ComputeTrRw(rer, inner, inpMid, gm, WP.Backward);
      assert inner[0] == LS.Acheck(inp) && inner[1..] == [LS.Areg(qpred)] + cont;
      StrictSuffixBackAt(str, mid, j);
      var tq := FU.ComputeTr(rer, [LS.Areg(qpred)] + cont, inpMid, gm, WP.Backward);
      assert FU.ComputeTr(rer, inner, inpMid, gm, WP.Backward) == LT.Progress(tq);
      assert SuccActs(rer, inner, inpMid, gm, WP.Backward);
      // the body's span rides on top
      BwdComplete(rer, r1, inner, str, mid, j, gm);
      assert [LS.Areg(r1), LS.Acheck(inp), LS.Areg(qpred)] + cont == [LS.Areg(r1)] + inner;
      var titer := FU.ComputeTr(rer, [LS.Areg(r1)] + inner, inp, gm, WP.Backward);
      var tskip := FU.ComputeTr(rer, cont, inp, gm, WP.Backward);
      assert FU.ComputeTr(rer, acts, inp, gm, WP.Backward)
          == LT.GreedyChoice(greedy, LT.GroupActionT(LG.Reset([]), titer), tskip);
      GMUpdateResetNil(LC.Idx(inp), gm);
      assert LT.TreeRes(LT.GroupActionT(LG.Reset([]), titer), gm, inp, WP.Backward)
          == LT.TreeRes(titer, gm, inp, WP.Backward);
      assert LT.TreeRes(titer, gm, inp, WP.Backward).Some?;
    }
  }

  /** The completeness half of the span duality, assembled: a body match
      ending at `cp` makes the backward walk of the body from `cp`
      succeed. */
  lemma SpanDualityComplete(rer: LW.RegExpRecord, r: L.Regex, str: string,
                            i: int, cp: int, gm: LG.GroupMap)
    requires GroupFreeL(r)
    requires 0 <= i <= cp <= |str|
    requires MatchesL(rer, r, str, i, cp)
    ensures SuccActs(rer, [LS.Areg(r)], T.InputAt(str, cp), gm, WP.Backward)
  {
    SuccActsNil(rer, T.InputAt(str, i), gm, WP.Backward);
    BwdComplete(rer, r, [], str, i, cp, gm);
    assert [LS.Areg(r)] + [] == [LS.Areg(r)];
  }

  // ===========================================================================
  // BwdSound: a successful backward walk yields a span match
  // ===========================================================================

  /** `Reverse` preserves length. */
  lemma ReverseLength<T>(s: seq<T>)
    ensures |LC.Reverse(s)| == |s|
    decreases |s|
  {
    if |s| > 0 { ReverseLength(s[1..]); }
  }

  /** `InputAt(str, p)` sits at index `p`. */
  lemma IdxInputAt(str: string, p: int)
    requires 0 <= p <= |str|
    ensures |T.InputAt(str, p).pref| == p && LC.Idx(T.InputAt(str, p)) == p
  {
    ReverseLength(str[..p]);
  }

  /** THE soundness direction: if the backward walk of `[Areg(r)] + cont`
      from position `j` succeeds, then `r` matches some span `[i, j)` and the
      continuation's walk succeeds from `i`. */
  lemma BwdSound(rer: LW.RegExpRecord, r: L.Regex, cont: LS.Actions, str: string,
                 j: int, gm: LG.GroupMap) returns (i: int)
    requires GroupFreeL(r)
    requires 0 <= j <= |str|
    requires SuccActs(rer, [LS.Areg(r)] + cont, T.InputAt(str, j), gm, WP.Backward)
    ensures 0 <= i <= j
    ensures MatchesL(rer, r, str, i, j)
    ensures SuccActs(rer, cont, T.InputAt(str, i), gm, WP.Backward)
    decreases r, 1, 0
  {
    var inp := T.InputAt(str, j);
    var acts := [LS.Areg(r)] + cont;
    FU.ComputeTrRw(rer, acts, inp, gm, WP.Backward);
    assert acts[0] == LS.Areg(r) && acts[1..] == cont;
    match r
    case Epsilon =>
      i := j;
    case Character(cd) =>
      if LC.ReadChar(rer, cd, inp, WP.Backward) == None {
        assert FU.ComputeTr(rer, acts, inp, gm, WP.Backward) == LT.Mismatch;
        assert false;
      }
      IdxInputAt(str, j);
      assert |inp.pref| == j && |inp.pref| > 0;
      InputAtPeel(str, j);
      assert LC.CharMatch(rer, str[j - 1], cd);
      ReadCharBackAt(rer, cd, str, j);
      AdvanceInputPBackAt(str, j);
      var tc := FU.ComputeTr(rer, cont, T.InputAt(str, j - 1), gm, WP.Backward);
      assert FU.ComputeTr(rer, acts, inp, gm, WP.Backward) == LT.Read(str[j - 1], tc);
      assert LT.TreeRes(LT.Read(str[j - 1], tc), gm, inp, WP.Backward)
          == LT.TreeRes(tc, gm, T.InputAt(str, j - 1), WP.Backward);
      i := j - 1;
    case AnchorR(a) =>
      if !LS.AnchorSatisfied(rer, a, inp) {
        assert FU.ComputeTr(rer, acts, inp, gm, WP.Backward) == LT.Mismatch;
        assert false;
      }
      i := j;
    case Disjunction(r1, r2) =>
      var t1 := FU.ComputeTr(rer, [LS.Areg(r1)] + cont, inp, gm, WP.Backward);
      var t2 := FU.ComputeTr(rer, [LS.Areg(r2)] + cont, inp, gm, WP.Backward);
      assert FU.ComputeTr(rer, acts, inp, gm, WP.Backward) == LT.Choice(t1, t2);
      assert LT.TreeRes(LT.Choice(t1, t2), gm, inp, WP.Backward)
          == LT.Seqop(LT.TreeRes(t1, gm, inp, WP.Backward), LT.TreeRes(t2, gm, inp, WP.Backward));
      if LT.TreeRes(t1, gm, inp, WP.Backward).Some? {
        i := BwdSound(rer, r1, cont, str, j, gm);
      } else {
        assert LT.TreeRes(t2, gm, inp, WP.Backward).Some?;
        i := BwdSound(rer, r2, cont, str, j, gm);
      }
    case Sequence(r1, r2) =>
      assert LS.SeqList(r1, r2, WP.Backward) + cont == [LS.Areg(r2)] + ([LS.Areg(r1)] + cont);
      var m := BwdSound(rer, r2, [LS.Areg(r1)] + cont, str, j, gm);
      i := BwdSound(rer, r1, cont, str, m, gm);
      assert MatchesL(rer, r1, str, i, m) && MatchesL(rer, r2, str, m, j);
    case Quantified(greedy, min, delta, r1) =>
      var k: nat;
      i, k := BwdSoundQuant(rer, greedy, min, delta, r1, cont, str, j, gm);
    case Group(_, _) =>
      i := j; assert false;
    case LookaroundR(_, _) =>
      i := j; assert false;
    case Backreference(_) =>
      i := j; assert false;
  }

  /** `BwdSound` for quantifiers: the walk's own unfolding peels the
      RIGHTMOST span per forced copy or free layer; free layers consume
      strictly (the `Acheck` guard), so the position founds the
      induction where `delta == Inf` gives no structural measure. */
  lemma BwdSoundQuant(rer: LW.RegExpRecord, greedy: bool, min: nat, delta: LN.NoI,
                      r1: L.Regex, cont: LS.Actions, str: string,
                      j: int, gm: LG.GroupMap) returns (i: int, k: nat)
    requires GroupFreeL(r1)
    requires 0 <= j <= |str|
    requires SuccActs(rer, [LS.Areg(L.Quantified(greedy, min, delta, r1))] + cont,
                      T.InputAt(str, j), gm, WP.Backward)
    ensures 0 <= i <= j
    ensures min <= k && (match delta case Inf => true case NN(dx) => k <= min + dx)
    ensures IterL(rer, r1, k, str, i, j)
    ensures SuccActs(rer, cont, T.InputAt(str, i), gm, WP.Backward)
    decreases r1, 3, min + j
  {
    var inp := T.InputAt(str, j);
    var q := L.Quantified(greedy, min, delta, r1);
    var acts := [LS.Areg(q)] + cont;
    FU.ComputeTrRw(rer, acts, inp, gm, WP.Backward);
    assert acts[0] == LS.Areg(q) && acts[1..] == cont;
    GroupFreeDefGroups(r1);
    GMResetNil(gm);
    GMUpdateResetNil(LC.Idx(inp), gm);
    if min > 0 {
      var inner := [LS.Areg(L.Quantified(greedy, min - 1, delta, r1))] + cont;
      assert [LS.Areg(r1), LS.Areg(L.Quantified(greedy, min - 1, delta, r1))] + cont
          == [LS.Areg(r1)] + inner;
      var titer := FU.ComputeTr(rer, [LS.Areg(r1)] + inner, inp, gm, WP.Backward);
      assert FU.ComputeTr(rer, acts, inp, gm, WP.Backward) == LT.GroupActionT(LG.Reset([]), titer);
      assert LT.TreeRes(LT.GroupActionT(LG.Reset([]), titer), gm, inp, WP.Backward)
          == LT.TreeRes(titer, gm, inp, WP.Backward);
      var m := BwdSound(rer, r1, inner, str, j, gm);
      var i2, k2 := BwdSoundQuant(rer, greedy, min - 1, delta, r1, cont, str, m, gm);
      i := i2;
      k := k2 + 1;
      IterLSnoc(rer, r1, k2, str, i2, m, j);
    } else if delta == LN.NN(0) {
      i := j;
      k := 0;
    } else {
      var qpred := L.Quantified(greedy, 0, FS.NoiPred(delta), r1);
      var inner := [LS.Acheck(inp), LS.Areg(qpred)] + cont;
      assert [LS.Areg(r1), LS.Acheck(inp), LS.Areg(qpred)] + cont == [LS.Areg(r1)] + inner;
      var titer := FU.ComputeTr(rer, [LS.Areg(r1)] + inner, inp, gm, WP.Backward);
      var tskip := FU.ComputeTr(rer, cont, inp, gm, WP.Backward);
      assert FU.ComputeTr(rer, acts, inp, gm, WP.Backward)
          == LT.GreedyChoice(greedy, LT.GroupActionT(LG.Reset([]), titer), tskip);
      var iterRes := LT.TreeRes(LT.GroupActionT(LG.Reset([]), titer), gm, inp, WP.Backward);
      var skipRes := LT.TreeRes(tskip, gm, inp, WP.Backward);
      assert iterRes.Some? || skipRes.Some? by {
        if greedy {
          assert LT.TreeRes(LT.GreedyChoice(greedy, LT.GroupActionT(LG.Reset([]), titer), tskip), gm, inp, WP.Backward)
              == LT.Seqop(iterRes, skipRes);
        } else {
          assert LT.TreeRes(LT.GreedyChoice(greedy, LT.GroupActionT(LG.Reset([]), titer), tskip), gm, inp, WP.Backward)
              == LT.Seqop(skipRes, iterRes);
        }
      }
      if skipRes.Some? {
        i := j;
        k := 0;
      } else {
        assert iterRes.Some?;
        assert LT.TreeRes(titer, gm, inp, WP.Backward).Some?;
        var m := BwdSound(rer, r1, inner, str, j, gm);
        // the Acheck guard forces strict progress: m < j
        var inpM := T.InputAt(str, m);
        FU.ComputeTrRw(rer, inner, inpM, gm, WP.Backward);
        assert inner[0] == LS.Acheck(inp) && inner[1..] == [LS.Areg(qpred)] + cont;
        if !SSx.IsStrictSuffix(inpM, inp, WP.Backward) {
          assert FU.ComputeTr(rer, inner, inpM, gm, WP.Backward) == LT.Mismatch;
          assert false;
        }
        SSx.SSLengthLt(inpM, inp, WP.Backward);
        IdxInputAt(str, m);
        IdxInputAt(str, j);
        assert m < j;
        var tq := FU.ComputeTr(rer, [LS.Areg(qpred)] + cont, inpM, gm, WP.Backward);
        assert FU.ComputeTr(rer, inner, inpM, gm, WP.Backward) == LT.Progress(tq);
        assert SuccActs(rer, [LS.Areg(qpred)] + cont, inpM, gm, WP.Backward);
        var i2, k2 := BwdSoundQuant(rer, greedy, 0, FS.NoiPred(delta), r1, cont, str, m, gm);
        i := i2;
        k := k2 + 1;
        IterLSnoc(rer, r1, k2, str, i2, m, j);
      }
    }
  }

  /** The soundness half of the span duality, assembled: a successful
      backward walk of the body from `cp` yields a body match ending at
      `cp`. */
  lemma SpanDualitySound(rer: LW.RegExpRecord, r: L.Regex, str: string,
                         cp: int, gm: LG.GroupMap) returns (i: int)
    requires GroupFreeL(r)
    requires 0 <= cp <= |str|
    requires SuccActs(rer, [LS.Areg(r)], T.InputAt(str, cp), gm, WP.Backward)
    ensures 0 <= i <= cp && MatchesL(rer, r, str, i, cp)
  {
    assert [LS.Areg(r)] + [] == [LS.Areg(r)];
    i := BwdSound(rer, r, [], str, cp, gm);
  }
}
