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
  import RE = RegElkRegex

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
        assert exists q: int {:trigger MatchesL(rer, RevL(r1), LC.Reverse(str), q, n - i)} ::
                 (MatchesL(rer, RevL(r2), LC.Reverse(str), n - j, q)
                  && MatchesL(rer, RevL(r1), LC.Reverse(str), q, n - i));
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
        assert exists k: nat {:trigger IterL(rer, r1, k, str, i, j)} ::
                 (min <= k
                  && (match delta case Inf => true case NN(dx) => k <= min + dx)
                  && IterL(rer, r1, k, str, i, j));
        var k: nat :| min <= k
          && (match delta case Inf => true case NN(dx) => k <= min + dx)
          && IterL(rer, r1, k, str, i, j);
        IterLReverse(rer, r1, k, str, i, j);
      }
      if MatchesL(rer, RevL(r), LC.Reverse(str), n - j, n - i) {
        assert RevL(r) == L.Quantified(g, min, delta, RevL(r1));
        assert MatchesL(rer, L.Quantified(g, min, delta, RevL(r1)), LC.Reverse(str),
                        n - j, n - i);
        assert exists k: nat {:trigger IterL(rer, RevL(r1), k, LC.Reverse(str), n - j, n - i)} ::
                 (min <= k
                  && (match delta case Inf => true case NN(dx) => k <= min + dx)
                  && IterL(rer, RevL(r1), k, LC.Reverse(str), n - j, n - i));
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
  // Reversal at the INPUT level: the four direction-sensitive primitives
  // ===========================================================================

  /** An input window with its two halves exchanged. Scanning `r` BACKWARD
      over `inp` is scanning `RevL(r)` FORWARD over `SwapInput(inp)` -- this
      is the whole reversal, expressed without ever mentioning a string. */
  function SwapInput(inp: LC.Input): LC.Input { LC.Input(inp.pref, inp.next) }

  lemma SwapInputInvolution(inp: LC.Input)
    ensures SwapInput(SwapInput(inp)) == inp
  {}

  /** `InputAtReverse`, restated as the swap. */
  lemma InputAtSwap(str: string, cp: int)
    requires 0 <= cp <= |str|
    ensures |LC.Reverse(str)| == |str|
    ensures T.InputAt(LC.Reverse(str), |str| - cp) == SwapInput(T.InputAt(str, cp))
  {
    ReverseLength(str);
    InputAtReverse(str, cp);
  }

  /** (1) Reading a character. Backward reads `pref[0]`; forward on the
      swapped window reads the SAME character and lands on the swapped
      result. */
  lemma ReadCharSwap(rer: LW.RegExpRecord, cd: LC.CharDescr, inp: LC.Input)
    ensures match LC.ReadChar(rer, cd, inp, WP.Backward)
            case None => LC.ReadChar(rer, cd, SwapInput(inp), WP.Forward).None?
            case Some(pair) =>
              LC.ReadChar(rer, cd, SwapInput(inp), WP.Forward)
                == Some((pair.0, SwapInput(pair.1)))
  {}

  /** (2) The strict-suffix progress guard. */
  lemma StrictSuffixSwapAux(inp: LC.Input, next: seq<char>, pref: seq<char>)
    ensures SSx.StrictSuffixBackward(inp, next, pref)
        <==> SSx.StrictSuffixForward(SwapInput(inp), pref, next)
    decreases |pref|
  {
    if |pref| == 0 { return; }
    if LC.Input([pref[0]] + next, pref[1..]) == inp {
      assert LC.Input(pref[1..], [pref[0]] + next) == SwapInput(inp);
    } else {
      assert LC.Input(pref[1..], [pref[0]] + next) != SwapInput(inp);
      StrictSuffixSwapAux(inp, [pref[0]] + next, pref[1..]);
    }
  }

  lemma IsStrictSuffixSwap(inp1: LC.Input, inp2: LC.Input)
    ensures SSx.IsStrictSuffix(inp1, inp2, WP.Backward)
        <==> SSx.IsStrictSuffix(SwapInput(inp1), SwapInput(inp2), WP.Forward)
  {
    StrictSuffixSwapAux(inp1, inp2.next, inp2.pref);
  }

  /** (3) Anchors, at the input level (the string-level form is
      `AnchorSatisfiedReverse`). */
  lemma AnchorSatisfiedSwap(rer: LW.RegExpRecord, a: L.Anchor, inp: LC.Input)
    ensures LS.AnchorSatisfied(rer, SwapAnchorL(a), SwapInput(inp))
        <==> LS.AnchorSatisfied(rer, a, inp)
  {}

  /** `RevL` permutes `DefGroups` (a Sequence swaps its two halves) but
      preserves its ELEMENTS. */
  lemma SetOfConcat(a: seq<LG.GroupId>, b: seq<LG.GroupId>)
    ensures forall g: LG.GroupId :: g in a + b <==> (g in a || g in b)
  {}

  lemma RevLDefGroupsSet(r: L.Regex)
    ensures forall g: LG.GroupId :: g in L.DefGroups(RevL(r)) <==> g in L.DefGroups(r)
    decreases r
  {
    match r
    case Disjunction(r1, r2) =>
      RevLDefGroupsSet(r1); RevLDefGroupsSet(r2);
      SetOfConcat(L.DefGroups(RevL(r1)), L.DefGroups(RevL(r2)));
      SetOfConcat(L.DefGroups(r1), L.DefGroups(r2));
    case Sequence(r1, r2) =>
      RevLDefGroupsSet(r1); RevLDefGroupsSet(r2);
      assert L.DefGroups(RevL(r)) == L.DefGroups(RevL(r2)) + L.DefGroups(RevL(r1));
      assert L.DefGroups(r) == L.DefGroups(r1) + L.DefGroups(r2);
      SetOfConcat(L.DefGroups(RevL(r2)), L.DefGroups(RevL(r1)));
      SetOfConcat(L.DefGroups(r1), L.DefGroups(r2));
    case Quantified(_, _, _, r1) => RevLDefGroupsSet(r1);
    case Group(gid, r1) =>
      RevLDefGroupsSet(r1);
      SetOfConcat([gid], L.DefGroups(RevL(r1)));
      SetOfConcat([gid], L.DefGroups(r1));
    case _ =>
  }

  /** ... and a `Reset` only ever reads those elements as a SET, so the
      permuted payload acts identically. */
  lemma GMResetPermute(gl1: LG.GroupSet, gl2: LG.GroupSet, gm: LG.GroupMap)
    requires forall g: LG.GroupId :: g in gl1 <==> g in gl2
    ensures LG.GMReset(gl1, gm) == LG.GMReset(gl2, gm)
  {
    assert (set g | g in gl1) == (set g | g in gl2);
  }

  /** The two combined: a quantifier layer's reset behaves the same either
      way round. */
  lemma RevLResetAgrees(r: L.Regex, gm: LG.GroupMap)
    ensures LG.GMReset(L.DefGroups(RevL(r)), gm) == LG.GMReset(L.DefGroups(r), gm)
  {
    RevLDefGroupsSet(r);
    GMResetPermute(L.DefGroups(RevL(r)), L.DefGroups(r), gm);
  }

  /** An action stack reversed for the other scanning direction: each regex
      reverses, each progress guard's recorded window swaps, and `Aclose` is
      direction-blind. */
  function RevActs(acts: LS.Actions): LS.Actions {
    seq(|acts|, i requires 0 <= i < |acts| =>
      match acts[i]
      case Areg(r) => LS.Areg(RevL(r))
      case Acheck(ip) => LS.Acheck(SwapInput(ip))
      case Aclose(g) => LS.Aclose(g))
  }

  lemma RevActsCons(a: LS.Action, acts: LS.Actions)
    ensures RevActs([a] + acts)
         == [(match a case Areg(r) => LS.Areg(RevL(r))
                      case Acheck(ip) => LS.Acheck(SwapInput(ip))
                      case Aclose(g) => LS.Aclose(g))] + RevActs(acts)
  {
    var lhs := RevActs([a] + acts);
    var rhs := [(match a case Areg(r) => LS.Areg(RevL(r))
                         case Acheck(ip) => LS.Acheck(SwapInput(ip))
                         case Aclose(g) => LS.Aclose(g))] + RevActs(acts);
    forall i | 0 <= i < |lhs| ensures lhs[i] == rhs[i] {}
  }

  lemma RevActsTail(acts: LS.Actions)
    requires |acts| > 0
    ensures RevActs(acts)[1..] == RevActs(acts[1..])
  {
    var lhs := RevActs(acts)[1..];
    var rhs := RevActs(acts[1..]);
    forall i | 0 <= i < |lhs| ensures lhs[i] == rhs[i] {}
  }

  /** The reversal keeps a stack backreference-free. */
  lemma RevActsNoBackref(acts: LS.Actions)
    requires NoBackrefActs(acts)
    ensures NoBackrefActs(RevActs(acts))
  {
    forall i | 0 <= i < |RevActs(acts)| && RevActs(acts)[i].Areg?
      ensures NoBackrefL(RevActs(acts)[i].r)
    {
      assert acts[i].Areg?;
      RevLNoBackref(acts[i].r);
    }
  }

  lemma RevLNoBackref(r: L.Regex)
    requires NoBackrefL(r)
    ensures NoBackrefL(RevL(r))
    decreases r
  {
    match r
    case Disjunction(r1, r2) => RevLNoBackref(r1); RevLNoBackref(r2);
    case Sequence(r1, r2) => RevLNoBackref(r1); RevLNoBackref(r2);
    case Quantified(_, _, _, r1) => RevLNoBackref(r1);
    case Group(_, r1) => RevLNoBackref(r1);
    case _ =>
  }

  /** The concatenation-order fact, as a lemma rather than a comment: the
      spec's BACKWARD `SeqList` is the reversal of its FORWARD one. This is
      the step that makes the whole reversal line up. */
  lemma SeqListReverse(r1: L.Regex, r2: L.Regex)
    ensures RevActs(LS.SeqList(r1, r2, WP.Backward))
         == LS.SeqList(RevL(r2), RevL(r1), WP.Forward)
  {
    assert LS.SeqList(r1, r2, WP.Backward) == [LS.Areg(r2), LS.Areg(r1)];
    assert LS.SeqList(RevL(r2), RevL(r1), WP.Forward)
        == [LS.Areg(RevL(r2)), LS.Areg(RevL(r1))];
    var lhs := RevActs([LS.Areg(r2), LS.Areg(r1)]);
    forall i | 0 <= i < |lhs|
      ensures lhs[i] == [LS.Areg(RevL(r2)), LS.Areg(RevL(r1))][i] {}
  }

  // ---------------------------------------------------------------------
  // The FUEL measures correspond too -- the same phenomenon as FFindMatch's
  // `decreases` lining up in Mirror.dfy. Without this the tree correspondence
  // would have to reconcile two different termination bounds.
  // ---------------------------------------------------------------------

  lemma CurrentStrSwap(inp: LC.Input)
    ensures LC.CurrentStr(SwapInput(inp), WP.Forward) == LC.CurrentStr(inp, WP.Backward)
    ensures LC.CurrentStr(SwapInput(inp), WP.Backward) == LC.CurrentStr(inp, WP.Forward)
  {}

  lemma MaxIterSwap(inp: LC.Input)
    ensures FS.MaxIter(SwapInput(inp), WP.Forward) == FS.MaxIter(inp, WP.Backward)
  {}

  /** Advancing one position commutes with the swap -- the `Acheck` guard's
      counterpart of `ReadCharSwap`. */
  lemma AdvanceInputSwap(inp: LC.Input)
    ensures match LC.AdvanceInput(inp, WP.Backward)
            case None => LC.AdvanceInput(SwapInput(inp), WP.Forward).None?
            case Some(ni) =>
              LC.AdvanceInput(SwapInput(inp), WP.Forward) == Some(SwapInput(ni))
  {}

  lemma RegexFuelReverse(r: L.Regex, inp: LC.Input)
    requires GroupOkL(r)
    ensures FS.RegexFuel(RevL(r), SwapInput(inp), WP.Forward)
         == FS.RegexFuel(r, inp, WP.Backward)
    decreases r
  {
    match r
    case Disjunction(r1, r2) =>
      RegexFuelReverse(r1, inp); RegexFuelReverse(r2, inp);
    case Sequence(r1, r2) =>
      RegexFuelReverse(r1, inp); RegexFuelReverse(r2, inp);
      assert RevL(r) == L.Sequence(RevL(r2), RevL(r1));
    case Quantified(b, min, delta, r1) =>
      RegexFuelReverse(r1, inp);
      MaxIterSwap(inp);
    case Group(_, r1) => RegexFuelReverse(r1, inp);
    case _ =>
  }

  lemma ActionsFuelReverse(acts: LS.Actions, inp: LC.Input)
    requires GroupOkActs(acts)
    ensures FS.ActionsFuel(RevActs(acts), SwapInput(inp), WP.Forward)
         == FS.ActionsFuel(acts, inp, WP.Backward)
    decreases |acts|
  {
    if |acts| == 0 {
      assert RevActs(acts) == [];
      return;
    }
    GroupOkActsTail(acts);
    RevActsTail(acts);
    assert RevActs(acts)[0] ==
      (match acts[0] case Areg(r) => LS.Areg(RevL(r))
                     case Acheck(ip) => LS.Acheck(SwapInput(ip))
                     case Aclose(g) => LS.Aclose(g));
    match acts[0]
    case Areg(r) =>
      RegexFuelReverse(r, inp);
      ActionsFuelReverse(acts[1..], inp);
    case Aclose(g) =>
      ActionsFuelReverse(acts[1..], inp);
    case Acheck(ip) =>
      AdvanceInputSwap(ip);
      match LC.AdvanceInput(ip, WP.Backward) {
        case None =>
        case Some(ni) => ActionsFuelReverse(acts[1..], ni);
      }
  }

  /* ---------------------------------------------------------------------
     (4) CONCATENATION ORDER -- and the reason a TREE-level reversal now
     looks tractable, where it previously looked risky.

       SeqList(r1, r2, Backward) == [Areg(r2), Areg(r1)]

     The spec ALREADY reverses concatenation order when scanning backward,
     which is exactly what `RevL` does structurally: RevL(Sequence(r1, r2))
     is Sequence(RevL(r2), RevL(r1)), whose FORWARD SeqList is
     [Areg(RevL(r2)), Areg(RevL(r1))]. The two action stacks correspond
     elementwise.

     Priority is decided by that stack order together with `Choice` ordering
     (Disjunction) and the greedy flag (Quantified), and `RevL` preserves
     both. So the objection that killed the tree-level route for captures --
     that leaf ORDER might not survive reversal -- appears not to apply.

     STATUS. Every ingredient the tree correspondence needs is now proven;
     only the assembly remains. In dependency order:

       (a) ReadCharSwap        -- consuming a character
       (b) IsStrictSuffixSwap  -- the empty-iteration progress guard
       (c) AnchorSatisfiedSwap -- anchors, via SwapAnchorL
       (d) SeqListReverse      -- concatenation order (the key one: the spec
                                  ALREADY reverses it going backward)
       (e) RevLResetAgrees     -- a quantifier layer's Reset permutes but
                                  acts identically
       (f) ActionsFuelReverse  -- the fuel measures correspond exactly, so
                                  the two runs terminate together
       (g) TreeResSomeGmIndep  -- the group map never decides success

     THE REMAINING LEMMA. Note it cannot be stated as tree EQUALITY, for the
     reason (e) exists: the Reset payload is a permuted sequence, so the two
     trees differ as values. The right shape is a structural equivalence

       TreeEquiv(t1, t2)  ==  equal except Reset payloads agree as SETS

     with ComputeTree producing TreeEquiv trees under RevActs + SwapInput,
     and TreeEquiv implying TreeRes agrees on Some-ness (using (g), since
     the recorded group POSITIONS also differ -- Idx(inp) is |inp.pref| and
     the swap exchanges the halves, so leaf maps correspond through the
     index mirror rather than being equal, exactly as Mirror.dfy's register
     banks do).

     WHAT IT BUYS. `SuccActs` correspondence between directions, hence the
     forward span duality (L2 item 4) for free from the existing Bwd*
     family, instead of porting ~300 lines by hand. It also unblocks L3's
     lookbehind capture pass, whose capture regex is reverse_regex(body) run
     Backward.

     No contradiction has turned up anywhere in this chain.
     --------------------------------------------------------------------- */

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
    requires GroupOkL(r)
    requires NoBackrefActs(cont)
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
      GroupOkIsNoBackref(r1);
      NoBackrefActsCons(LS.Areg(r1), cont);
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
    case Group(gid, r1) =>
      // ComputeTr([Areg(Group(gid,r1))]+cont, inp, gm) = GroupActionT(Open(gid),
      //   ComputeTr([Areg(r1), Aclose(gid)]+cont, inp, GMOpen(Idx(inp),gid,gm))).
      // TreeRes threads GMOpen; so the goal is exactly the body's span under
      // the opened map. The body match is MatchesL(r1) (group-transparent), and
      // cont resumes at the CLOSED map, which SuccActsGmIndep discards.
      assert MatchesL(rer, r1, str, i, j);            // MatchesL(Group) == MatchesL(r1)
      GroupOkIsNoBackref(r1);
      var gmO := LG.GMOpen(LC.Idx(inp), gid, gm);
      var acont := [LS.Aclose(gid)] + cont;
      NoBackrefActsCons(LS.Aclose(gid), cont);
      // [Aclose(gid)]+cont succeeds under gmO at position i
      var inpI := T.InputAt(str, i);
      IdxInputAt(str, i);
      var gmC := LG.GMClose(LC.Idx(inpI), gid, gmO);
      SuccActsGmIndep(rer, cont, inpI, gm, gmC, WP.Backward);
      FU.ComputeTrRw(rer, acont, inpI, gmO, WP.Backward);
      assert acont[0] == LS.Aclose(gid) && acont[1..] == cont;
      assert SuccActs(rer, acont, inpI, gmO, WP.Backward);
      BwdComplete(rer, r1, acont, str, i, j, gmO);
      // relate SuccActs([Areg(r1),Aclose(gid)]+cont, inp, gmO) to the goal
      assert [LS.Areg(r1)] + acont == [LS.Areg(r1), LS.Aclose(gid)] + cont;
      var titer := FU.ComputeTr(rer, [LS.Areg(r1), LS.Aclose(gid)] + cont, inp, gmO, WP.Backward);
      assert FU.ComputeTr(rer, acts, inp, gm, WP.Backward) == LT.GroupActionT(LG.Open(gid), titer);
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
    requires GroupOkL(r1)
    requires NoBackrefActs(cont)
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
    GroupOkIsNoBackref(r1);
    if min > 0 {
      // Each iteration RESETS the body's groups: the quantifier tree is
      // GroupActionT(Reset(DefGroups(r1)), titer), and titer is built under
      // GMReset(gidl, gm). So recurse under gm' and let the Reset node thread
      // the map back; cont's success shifts gm -> gm' via SuccActsGmIndep.
      var gidl := L.DefGroups(r1);
      var gm' := LG.GMReset(gidl, gm);
      SuccActsGmIndep(rer, cont, T.InputAt(str, i), gm, gm', WP.Backward);
      // peel the last span into the head copy; the rest recurse
      var mid := IterLSplit(rer, r1, k, k - 1, str, i, j);
      IterLBounds(rer, r1, k - 1, str, i, mid);
      var mm := IterLHead(rer, r1, k - (k - 1), str, mid, j);
      assert mm == j;
      MatchesLBounds(rer, r1, str, mid, j);
      var inner := [LS.Areg(L.Quantified(greedy, min - 1, delta, r1))] + cont;
      NoBackrefActsCons(LS.Areg(L.Quantified(greedy, min - 1, delta, r1)), cont);
      BwdCompleteQuant(rer, greedy, min - 1, delta, r1, cont, str, i, mid, gm', k - 1);
      BwdComplete(rer, r1, inner, str, mid, j, gm');
      assert [LS.Areg(r1), LS.Areg(L.Quantified(greedy, min - 1, delta, r1))] + cont
          == [LS.Areg(r1)] + inner;
      var titer := FU.ComputeTr(rer, [LS.Areg(r1)] + inner, inp, gm', WP.Backward);
      assert FU.ComputeTr(rer, acts, inp, gm, WP.Backward) == LT.GroupActionT(LG.Reset(gidl), titer);
      assert LT.TreeRes(LT.GroupActionT(LG.Reset(gidl), titer), gm, inp, WP.Backward)
          == LT.TreeRes(titer, gm', inp, WP.Backward);
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
    requires GroupOkL(r1)
    requires NoBackrefActs(cont)
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
    GroupOkIsNoBackref(r1);
    var gidl := L.DefGroups(r1);
    if k2 == 0 {
      // i == j: the skip branch carries the continuation's success (unaffected
      // by the iterate branch's Reset(gidl))
      if delta == LN.NN(0) {
        return;
      }
      var tskip := FU.ComputeTr(rer, cont, inp, gm, WP.Backward);
      var titer := FU.ComputeTr(rer, [LS.Areg(r1), LS.Acheck(inp), LS.Areg(L.Quantified(greedy, 0, FS.NoiPred(delta), r1))] + cont,
                                inp, LG.GMReset(gidl, gm), WP.Backward);
      assert FU.ComputeTr(rer, acts, inp, gm, WP.Backward)
          == LT.GreedyChoice(greedy, LT.GroupActionT(LG.Reset(gidl), titer), tskip);
      assert LT.TreeRes(tskip, gm, inp, WP.Backward).Some?;
    } else {
      // Each iteration resets DefGroups(r1); the iterate subtree is built under
      // gm' = GMReset(gidl, gm). Recurse under gm', shift cont via SuccActsGmIndep,
      // and the Reset node threads the map back.
      var gm' := LG.GMReset(gidl, gm);
      SuccActsGmIndep(rer, cont, T.InputAt(str, i), gm, gm', WP.Backward);
      // nonempty chain: last span through this layer, the rest recurse
      var mid := IterLNESplit(rer, r1, k2, k2 - 1, str, i, j);
      IterLNEBounds(rer, r1, k2 - 1, str, i, mid);
      var mm := IterLNEHead(rer, r1, k2 - (k2 - 1), str, mid, j);
      assert mm == j && mid < j;
      var qpred := L.Quantified(greedy, 0, FS.NoiPred(delta), r1);
      var inner := [LS.Acheck(inp), LS.Areg(qpred)] + cont;
      NoBackrefActsCons(LS.Areg(qpred), cont);
      NoBackrefActsCons(LS.Acheck(inp), [LS.Areg(qpred)] + cont);
      // the guard passes at mid, and the smaller quantifier finishes there
      BwdCompleteFree(rer, greedy, FS.NoiPred(delta), r1, cont, str, i, mid, gm', k2 - 1);
      var inpMid := T.InputAt(str, mid);
      FU.ComputeTrRw(rer, inner, inpMid, gm', WP.Backward);
      assert inner[0] == LS.Acheck(inp) && inner[1..] == [LS.Areg(qpred)] + cont;
      StrictSuffixBackAt(str, mid, j);
      var tq := FU.ComputeTr(rer, [LS.Areg(qpred)] + cont, inpMid, gm', WP.Backward);
      assert FU.ComputeTr(rer, inner, inpMid, gm', WP.Backward) == LT.Progress(tq);
      assert SuccActs(rer, inner, inpMid, gm', WP.Backward);
      // the body's span rides on top
      BwdComplete(rer, r1, inner, str, mid, j, gm');
      assert [LS.Areg(r1), LS.Acheck(inp), LS.Areg(qpred)] + cont == [LS.Areg(r1)] + inner;
      var titer := FU.ComputeTr(rer, [LS.Areg(r1)] + inner, inp, gm', WP.Backward);
      var tskip := FU.ComputeTr(rer, cont, inp, gm, WP.Backward);
      assert FU.ComputeTr(rer, acts, inp, gm, WP.Backward)
          == LT.GreedyChoice(greedy, LT.GroupActionT(LG.Reset(gidl), titer), tskip);
      assert LT.TreeRes(LT.GroupActionT(LG.Reset(gidl), titer), gm, inp, WP.Backward)
          == LT.TreeRes(titer, gm', inp, WP.Backward);
      assert LT.TreeRes(titer, gm', inp, WP.Backward).Some?;
    }
  }

  /** The completeness half of the span duality, assembled: a body match
      ending at `cp` makes the backward walk of the body from `cp`
      succeed. */
  lemma SpanDualityComplete(rer: LW.RegExpRecord, r: L.Regex, str: string,
                            i: int, cp: int, gm: LG.GroupMap)
    requires GroupOkL(r)
    requires 0 <= i <= cp <= |str|
    requires MatchesL(rer, r, str, i, cp)
    ensures SuccActs(rer, [LS.Areg(r)], T.InputAt(str, cp), gm, WP.Backward)
  {
    SuccActsNil(rer, T.InputAt(str, i), gm, WP.Backward);
    assert NoBackrefActs([]);
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
    requires GroupOkL(r)
    requires NoBackrefActs(cont)
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
      GroupOkIsNoBackref(r1);
      NoBackrefActsCons(LS.Areg(r1), cont);
      assert LS.SeqList(r1, r2, WP.Backward) + cont == [LS.Areg(r2)] + ([LS.Areg(r1)] + cont);
      var m := BwdSound(rer, r2, [LS.Areg(r1)] + cont, str, j, gm);
      i := BwdSound(rer, r1, cont, str, m, gm);
      assert MatchesL(rer, r1, str, i, m) && MatchesL(rer, r2, str, m, j);
    case Quantified(greedy, min, delta, r1) =>
      var k: nat;
      i, k := BwdSoundQuant(rer, greedy, min, delta, r1, cont, str, j, gm);
    case Group(gid, r1) =>
      // ComputeTr([Areg(Group(gid,r1))]+cont, inp, gm) = GroupActionT(Open(gid),
      //   ComputeTr([Areg(r1),Aclose(gid)]+cont, inp, gmO)); TreeRes threads GMOpen,
      //   so the body's backward walk under gmO succeeds. Recover its span (=
      //   MatchesL(Group)==MatchesL(r1)); cont resumes at the closed map, shifted
      //   back to gm by SuccActsGmIndep.
      GroupOkIsNoBackref(r1);
      var gmO := LG.GMOpen(LC.Idx(inp), gid, gm);
      var acont := [LS.Aclose(gid)] + cont;
      NoBackrefActsCons(LS.Aclose(gid), cont);
      var t' := FU.ComputeTr(rer, [LS.Areg(r1)] + acont, inp, gmO, WP.Backward);
      assert [LS.Areg(r1)] + acont == [LS.Areg(r1), LS.Aclose(gid)] + cont;
      assert FU.ComputeTr(rer, acts, inp, gm, WP.Backward) == LT.GroupActionT(LG.Open(gid), t');
      assert LT.TreeRes(LT.GroupActionT(LG.Open(gid), t'), gm, inp, WP.Backward)
          == LT.TreeRes(t', gmO, inp, WP.Backward);
      assert SuccActs(rer, [LS.Areg(r1)] + acont, inp, gmO, WP.Backward);
      var i2 := BwdSound(rer, r1, acont, str, j, gmO);
      // acont = [Aclose(gid)]+cont succeeds under gmO at i2  ->  cont at gmC  ->  cont at gm
      var inpI := T.InputAt(str, i2);
      IdxInputAt(str, i2);
      var gmC := LG.GMClose(LC.Idx(inpI), gid, gmO);
      FU.ComputeTrRw(rer, acont, inpI, gmO, WP.Backward);
      assert acont[0] == LS.Aclose(gid) && acont[1..] == cont;
      assert SuccActs(rer, cont, inpI, gmC, WP.Backward);
      SuccActsGmIndep(rer, cont, inpI, gmC, gm, WP.Backward);
      i := i2;
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
    requires GroupOkL(r1)
    requires NoBackrefActs(cont)
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
    GroupOkIsNoBackref(r1);
    var gidl := L.DefGroups(r1);
    if min > 0 {
      // the iterate subtree is built under gm' = GMReset(gidl, gm); recover the
      // body's span there, then shift cont's success back to gm.
      var gm' := LG.GMReset(gidl, gm);
      var inner := [LS.Areg(L.Quantified(greedy, min - 1, delta, r1))] + cont;
      NoBackrefActsCons(LS.Areg(L.Quantified(greedy, min - 1, delta, r1)), cont);
      assert [LS.Areg(r1), LS.Areg(L.Quantified(greedy, min - 1, delta, r1))] + cont
          == [LS.Areg(r1)] + inner;
      var titer := FU.ComputeTr(rer, [LS.Areg(r1)] + inner, inp, gm', WP.Backward);
      assert FU.ComputeTr(rer, acts, inp, gm, WP.Backward) == LT.GroupActionT(LG.Reset(gidl), titer);
      assert LT.TreeRes(LT.GroupActionT(LG.Reset(gidl), titer), gm, inp, WP.Backward)
          == LT.TreeRes(titer, gm', inp, WP.Backward);
      var m := BwdSound(rer, r1, inner, str, j, gm');
      var i2, k2 := BwdSoundQuant(rer, greedy, min - 1, delta, r1, cont, str, m, gm');
      i := i2;
      k := k2 + 1;
      IterLSnoc(rer, r1, k2, str, i2, m, j);
      SuccActsGmIndep(rer, cont, T.InputAt(str, i2), gm', gm, WP.Backward);
    } else if delta == LN.NN(0) {
      i := j;
      k := 0;
    } else {
      var gm' := LG.GMReset(gidl, gm);
      var qpred := L.Quantified(greedy, 0, FS.NoiPred(delta), r1);
      var inner := [LS.Acheck(inp), LS.Areg(qpred)] + cont;
      NoBackrefActsCons(LS.Areg(qpred), cont);
      NoBackrefActsCons(LS.Acheck(inp), [LS.Areg(qpred)] + cont);
      assert [LS.Areg(r1), LS.Acheck(inp), LS.Areg(qpred)] + cont == [LS.Areg(r1)] + inner;
      var titer := FU.ComputeTr(rer, [LS.Areg(r1)] + inner, inp, gm', WP.Backward);
      var tskip := FU.ComputeTr(rer, cont, inp, gm, WP.Backward);
      assert FU.ComputeTr(rer, acts, inp, gm, WP.Backward)
          == LT.GreedyChoice(greedy, LT.GroupActionT(LG.Reset(gidl), titer), tskip);
      var iterRes := LT.TreeRes(LT.GroupActionT(LG.Reset(gidl), titer), gm, inp, WP.Backward);
      var skipRes := LT.TreeRes(tskip, gm, inp, WP.Backward);
      assert iterRes.Some? || skipRes.Some? by {
        if greedy {
          assert LT.TreeRes(LT.GreedyChoice(greedy, LT.GroupActionT(LG.Reset(gidl), titer), tskip), gm, inp, WP.Backward)
              == LT.Seqop(iterRes, skipRes);
        } else {
          assert LT.TreeRes(LT.GreedyChoice(greedy, LT.GroupActionT(LG.Reset(gidl), titer), tskip), gm, inp, WP.Backward)
              == LT.Seqop(skipRes, iterRes);
        }
      }
      if skipRes.Some? {
        i := j;
        k := 0;
      } else {
        assert iterRes.Some?;
        assert LT.TreeRes(titer, gm', inp, WP.Backward).Some?;
        var m := BwdSound(rer, r1, inner, str, j, gm');
        // the Acheck guard forces strict progress: m < j
        var inpM := T.InputAt(str, m);
        FU.ComputeTrRw(rer, inner, inpM, gm', WP.Backward);
        assert inner[0] == LS.Acheck(inp) && inner[1..] == [LS.Areg(qpred)] + cont;
        if !SSx.IsStrictSuffix(inpM, inp, WP.Backward) {
          assert FU.ComputeTr(rer, inner, inpM, gm', WP.Backward) == LT.Mismatch;
          assert false;
        }
        SSx.SSLengthLt(inpM, inp, WP.Backward);
        IdxInputAt(str, m);
        IdxInputAt(str, j);
        assert m < j;
        var tq := FU.ComputeTr(rer, [LS.Areg(qpred)] + cont, inpM, gm', WP.Backward);
        assert FU.ComputeTr(rer, inner, inpM, gm', WP.Backward) == LT.Progress(tq);
        assert SuccActs(rer, [LS.Areg(qpred)] + cont, inpM, gm', WP.Backward);
        var i2, k2 := BwdSoundQuant(rer, greedy, 0, FS.NoiPred(delta), r1, cont, str, m, gm');
        i := i2;
        k := k2 + 1;
        IterLSnoc(rer, r1, k2, str, i2, m, j);
        SuccActsGmIndep(rer, cont, T.InputAt(str, i2), gm', gm, WP.Backward);
      }
    }
  }

  /** The soundness half of the span duality, assembled: a successful
      backward walk of the body from `cp` yields a body match ending at
      `cp`. */
  lemma SpanDualitySound(rer: LW.RegExpRecord, r: L.Regex, str: string,
                         cp: int, gm: LG.GroupMap) returns (i: int)
    requires GroupOkL(r)
    requires 0 <= cp <= |str|
    requires SuccActs(rer, [LS.Areg(r)], T.InputAt(str, cp), gm, WP.Backward)
    ensures 0 <= i <= cp && MatchesL(rer, r, str, i, cp)
  {
    assert [LS.Areg(r)] + [] == [LS.Areg(r)];
    assert NoBackrefActs([]);
    i := BwdSound(rer, r, [], str, cp, gm);
  }

  // ===========================================================================
  // THE DIRECTION CORRESPONDENCE
  // ===========================================================================

  /** `TreeRes` lifted over the fuel `Option`. */
  ghost function TResOpt(o: Option<LT.Tree>, gm: LG.GroupMap, inp: LC.Input,
                         dir: WP.Direction): Option<LT.Leaf>
  {
    match o case None => None case Some(t) => LT.TreeRes(t, gm, inp, dir)
  }

  /** Walking `acts` BACKWARD from `inp` succeeds exactly when walking the
      reversed stack FORWARD from the swapped window does.

      Stated on SUCCESS rather than on the trees, because the trees genuinely
      differ: a quantifier's `Reset` payload is permuted (RevLDefGroupsSet)
      and an `AnchorPass` payload is swapped. `TreeRes` reads the first
      set-wise and ignores the second, so neither difference reaches the
      answer. The recorded group maps also differ -- `Idx` is `|inp.pref|`
      and the swap exchanges the halves -- which is why the two maps are
      universally quantified here rather than shared. */
  lemma SuccReverse(rer: LW.RegExpRecord, acts: LS.Actions, inp: LC.Input,
                    gm1: LG.GroupMap, gm2: LG.GroupMap, fuel: nat)
    requires GroupOkActs(acts)
    // the two runs consume fuel in lockstep -- needed wherever a case pairs
    // two sub-results (Disjunction, the free quantifier layer), since there
    // `None` means "ran out", not "no match"
    ensures FS.ComputeTree(rer, acts, inp, gm1, WP.Backward, fuel).Some?
        <==> FS.ComputeTree(rer, RevActs(acts), SwapInput(inp), gm2, WP.Forward, fuel).Some?
    ensures TResOpt(FS.ComputeTree(rer, acts, inp, gm1, WP.Backward, fuel),
                    gm1, inp, WP.Backward).Some?
        <==> TResOpt(FS.ComputeTree(rer, RevActs(acts), SwapInput(inp), gm2,
                                    WP.Forward, fuel),
                     gm2, SwapInput(inp), WP.Forward).Some?
    decreases fuel
  {
    if fuel == 0 { return; }
    var f := fuel - 1;
    if |acts| == 0 { assert RevActs(acts) == []; return; }
    var cont := acts[1..];
    GroupOkActsTail(acts);
    RevActsTail(acts);
    RevActsCons(acts[0], cont);
    assert RevActs(acts) == [RevActs(acts)[0]] + RevActs(cont);
    var sinp := SwapInput(inp);

    match acts[0]
    case Acheck(strcheck) =>
      assert RevActs(acts)[0] == LS.Acheck(SwapInput(strcheck));
      IsStrictSuffixSwap(inp, strcheck);
      if SSx.IsStrictSuffix(inp, strcheck, WP.Backward) {
        SuccReverse(rer, cont, inp, gm1, gm2, f);
      }
    case Aclose(gid) =>
      assert RevActs(acts)[0] == LS.Aclose(gid);
      SuccReverse(rer, cont, inp, LG.GMClose(LC.Idx(inp), gid, gm1),
                  LG.GMClose(LC.Idx(sinp), gid, gm2), f);
    case Areg(r) =>
      assert RevActs(acts)[0] == LS.Areg(RevL(r));
      match r
      case Epsilon => SuccReverse(rer, cont, inp, gm1, gm2, f);
      case Character(cd) =>
        ReadCharSwap(rer, cd, inp);
        match LC.ReadChar(rer, cd, inp, WP.Backward) {
          case None =>
          case Some(pair) =>
            LC.AdvanceInputSuccess(inp, WP.Backward, pair.1);
            LC.AdvanceInputSuccess(sinp, WP.Forward, SwapInput(pair.1));
            SuccReverse(rer, cont, pair.1, gm1, gm2, f);
        }
      case Disjunction(r1, r2) =>
        GroupOkActsCons(LS.Areg(r1), cont);
        GroupOkActsCons(LS.Areg(r2), cont);
        RevActsCons(LS.Areg(r1), cont);
        RevActsCons(LS.Areg(r2), cont);
        SuccReverse(rer, [LS.Areg(r1)] + cont, inp, gm1, gm2, f);
        SuccReverse(rer, [LS.Areg(r2)] + cont, inp, gm1, gm2, f);
      case Sequence(r1, r2) =>
        var na := LS.SeqList(r1, r2, WP.Backward) + cont;
        assert na == [LS.Areg(r2)] + ([LS.Areg(r1)] + cont);
        assert GroupOkActs(na) by {
          GroupOkActsCons(LS.Areg(r1), cont);
          GroupOkActsCons(LS.Areg(r2), [LS.Areg(r1)] + cont);
        }
        RevActsCons(LS.Areg(r1), cont);
        RevActsCons(LS.Areg(r2), [LS.Areg(r1)] + cont);
        assert RevActs(na)
            == [LS.Areg(RevL(r2))] + ([LS.Areg(RevL(r1))] + RevActs(cont));
        assert LS.SeqList(RevL(r2), RevL(r1), WP.Forward) + RevActs(cont)
            == [LS.Areg(RevL(r2))] + ([LS.Areg(RevL(r1))] + RevActs(cont));
        SuccReverse(rer, na, inp, gm1, gm2, f);
      case Quantified(g, min, delta, r1) =>
        assert RevL(r) == L.Quantified(g, min, delta, RevL(r1));
        var gidl := L.DefGroups(r1);
        var gidl2 := L.DefGroups(RevL(r1));
        RevLResetAgrees(r1, gm1);
        if min > 0 {
          var q := L.Quantified(g, min - 1, delta, r1);
          var na := [LS.Areg(r1), LS.Areg(q)] + cont;
          assert na == [LS.Areg(r1)] + ([LS.Areg(q)] + cont);
          assert GroupOkActs(na) by {
            GroupOkActsCons(LS.Areg(q), cont);
            GroupOkActsCons(LS.Areg(r1), [LS.Areg(q)] + cont);
          }
          RevActsCons(LS.Areg(q), cont);
          RevActsCons(LS.Areg(r1), [LS.Areg(q)] + cont);
          assert RevL(q) == L.Quantified(g, min - 1, delta, RevL(r1));
          assert RevActs(na)
              == [LS.Areg(RevL(r1))] + ([LS.Areg(RevL(q))] + RevActs(cont));
          assert [LS.Areg(RevL(r1)), LS.Areg(RevL(q))] + RevActs(cont)
              == [LS.Areg(RevL(r1))] + ([LS.Areg(RevL(q))] + RevActs(cont));
          SuccReverse(rer, na, inp, LG.GMReset(gidl, gm1), LG.GMReset(gidl2, gm2), f);
        } else if delta == LN.NN(0) {
          SuccReverse(rer, cont, inp, gm1, gm2, f);
        } else {
          var q := L.Quantified(g, 0, FS.NoiPred(delta), r1);
          var na := [LS.Areg(r1), LS.Acheck(inp), LS.Areg(q)] + cont;
          assert na == [LS.Areg(r1)] + ([LS.Acheck(inp)] + ([LS.Areg(q)] + cont));
          assert GroupOkActs(na) by {
            GroupOkActsCons(LS.Areg(q), cont);
            GroupOkActsCons(LS.Acheck(inp), [LS.Areg(q)] + cont);
            GroupOkActsCons(LS.Areg(r1), [LS.Acheck(inp)] + ([LS.Areg(q)] + cont));
          }
          RevActsCons(LS.Areg(q), cont);
          RevActsCons(LS.Acheck(inp), [LS.Areg(q)] + cont);
          RevActsCons(LS.Areg(r1), [LS.Acheck(inp)] + ([LS.Areg(q)] + cont));
          assert RevL(q) == L.Quantified(g, 0, FS.NoiPred(delta), RevL(r1));
          assert RevActs(na)
              == [LS.Areg(RevL(r1))]
                 + ([LS.Acheck(SwapInput(inp))] + ([LS.Areg(RevL(q))] + RevActs(cont)));
          assert [LS.Areg(RevL(r1)), LS.Acheck(SwapInput(inp)), LS.Areg(RevL(q))]
                 + RevActs(cont)
              == [LS.Areg(RevL(r1))]
                 + ([LS.Acheck(SwapInput(inp))] + ([LS.Areg(RevL(q))] + RevActs(cont)));
          SuccReverse(rer, na, inp, LG.GMReset(gidl, gm1), LG.GMReset(gidl2, gm2), f);
          SuccReverse(rer, cont, inp, gm1, gm2, f);
          // spell the four sub-trees out; the outer node is a GreedyChoice of
          // the iterate branch (under its Reset) and the skip branch, ordered
          // by the SAME greedy flag on both sides
          var ib := FS.ComputeTree(rer, na, inp, LG.GMReset(gidl, gm1), WP.Backward, f);
          var sb := FS.ComputeTree(rer, cont, inp, gm1, WP.Backward, f);
          var if_ := FS.ComputeTree(rer, RevActs(na), sinp, LG.GMReset(gidl2, gm2),
                                    WP.Forward, f);
          var sf := FS.ComputeTree(rer, RevActs(cont), sinp, gm2, WP.Forward, f);
          assert ib.Some? <==> if_.Some?;
          assert sb.Some? <==> sf.Some?;
          if ib.Some? && sb.Some? {
            assert LT.TreeRes(LT.GroupActionT(LG.Reset(gidl), ib.value), gm1, inp,
                              WP.Backward)
                == LT.TreeRes(ib.value, LG.GMReset(gidl, gm1), inp, WP.Backward);
            assert LT.TreeRes(LT.GroupActionT(LG.Reset(gidl2), if_.value), gm2, sinp,
                              WP.Forward)
                == LT.TreeRes(if_.value, LG.GMReset(gidl2, gm2), sinp, WP.Forward);
          }
        }
      case Group(gid, r1) =>
        var na := [LS.Areg(r1), LS.Aclose(gid)] + cont;
        assert na == [LS.Areg(r1)] + ([LS.Aclose(gid)] + cont);
        assert GroupOkActs(na) by {
          GroupOkActsCons(LS.Aclose(gid), cont);
          GroupOkActsCons(LS.Areg(r1), [LS.Aclose(gid)] + cont);
        }
        RevActsCons(LS.Aclose(gid), cont);
        RevActsCons(LS.Areg(r1), [LS.Aclose(gid)] + cont);
        assert RevActs(na) == [LS.Areg(RevL(r1))] + ([LS.Aclose(gid)] + RevActs(cont));
        assert [LS.Areg(RevL(r1)), LS.Aclose(gid)] + RevActs(cont)
            == [LS.Areg(RevL(r1))] + ([LS.Aclose(gid)] + RevActs(cont));
        SuccReverse(rer, na, inp, LG.GMOpen(LC.Idx(inp), gid, gm1),
                    LG.GMOpen(LC.Idx(sinp), gid, gm2), f);
      case AnchorR(a) =>
        AnchorSatisfiedSwap(rer, a, inp);
        if LS.AnchorSatisfied(rer, a, inp) {
          SuccReverse(rer, cont, inp, gm1, gm2, f);
        }
      case LookaroundR(lk, r1) =>   // excluded by GroupOkL
      case Backreference(gid) =>    // excluded by GroupOkL
  }

  /** THE COROLLARY downstream consumes: walking BACKWARD succeeds exactly
      when walking the reversed stack FORWARD from the swapped window does.

      The two runs need the SAME fuel (ActionsFuelReverse), so one bound
      serves both. */
  lemma SuccActsReverse(rer: LW.RegExpRecord, acts: LS.Actions, inp: LC.Input,
                        gm1: LG.GroupMap, gm2: LG.GroupMap)
    requires GroupOkActs(acts)
    ensures SuccActs(rer, RevActs(acts), SwapInput(inp), gm2, WP.Forward)
        <==> SuccActs(rer, acts, inp, gm1, WP.Backward)
  {
    GroupOkActsIsNoBackref(acts);
    RevActsNoBackref(acts);
    var fb := FS.ActionsFuel(acts, inp, WP.Backward) + 1;
    var ff := FS.ActionsFuel(RevActs(acts), SwapInput(inp), WP.Forward) + 1;
    ActionsFuelReverse(acts, inp);
    assert fb == ff;
    FS.FunctionalTerminates(rer, acts, inp, gm1, WP.Backward, fb);
    FS.FunctionalTerminates(rer, RevActs(acts), SwapInput(inp), gm2, WP.Forward, ff);
    FU.ComputeTrRw(rer, acts, inp, gm1, WP.Backward);
    FU.ComputeTrRw(rer, RevActs(acts), SwapInput(inp), gm2, WP.Forward);
    SuccReverse(rer, acts, inp, gm1, gm2, fb);
  }

  // ===========================================================================
  // L2 item 4: the FORWARD span duality, for free from the backward one
  // ===========================================================================

  lemma RevLInvolution(r: L.Regex)
    ensures RevL(RevL(r)) == r
    decreases r
  {
    match r
    case Disjunction(r1, r2) => RevLInvolution(r1); RevLInvolution(r2);
    case Sequence(r1, r2) => RevLInvolution(r1); RevLInvolution(r2);
    case Quantified(_, _, _, r1) => RevLInvolution(r1);
    case Group(_, r1) => RevLInvolution(r1);
    case AnchorR(a) => assert SwapAnchorL(SwapAnchorL(a)) == a;
    case _ =>
  }

  lemma RevLGroupFree(r: L.Regex)
    requires GroupFreeL(r)
    ensures GroupFreeL(RevL(r))
    decreases r
  {
    match r
    case Disjunction(r1, r2) => RevLGroupFree(r1); RevLGroupFree(r2);
    case Sequence(r1, r2) => RevLGroupFree(r1); RevLGroupFree(r2);
    case Quantified(_, _, _, r1) => RevLGroupFree(r1);
    case _ =>
  }

  /** A single-regex stack reverses to a single-regex stack. */
  lemma RevActsSingleton(r: L.Regex)
    ensures RevActs([LS.Areg(r)]) == [LS.Areg(RevL(r))]
  {
    var lhs := RevActs([LS.Areg(r)]);
    forall i | 0 <= i < |lhs| ensures lhs[i] == [LS.Areg(RevL(r))][i] {}
  }

  /** Success of the FORWARD walk, expressed through the reversal. */
  lemma SuccActsForwardViaReverse(rer: LW.RegExpRecord, r: L.Regex, str: string,
                                  cp: int, gm: LG.GroupMap)
    requires GroupOkL(r)
    requires 0 <= cp <= |str|
    ensures |LC.Reverse(str)| == |str|
    ensures SuccActs(rer, [LS.Areg(r)], T.InputAt(str, cp), gm, WP.Forward)
        <==> SuccActs(rer, [LS.Areg(RevL(r))],
                      T.InputAt(LC.Reverse(str), |str| - cp), gm, WP.Backward)
  {
    ReverseLength(str);
    InputAtSwap(str, cp);
    RevLGroupOk(r);
    var acts := [LS.Areg(RevL(r))];
    assert GroupOkActs(acts) by {
      forall i | 0 <= i < |acts| && acts[i].Areg? ensures GroupOkL(acts[i].r) {}
    }
    RevActsSingleton(RevL(r));
    RevLInvolution(r);
    assert RevActs(acts) == [LS.Areg(r)];
    SwapInputInvolution(T.InputAt(str, cp));
    SuccActsReverse(rer, acts, T.InputAt(LC.Reverse(str), |str| - cp), gm, gm);
  }

  /** THE FORWARD COMPLETENESS half: a span makes the forward walk succeed. */
  lemma SpanDualityForwardComplete(rer: LW.RegExpRecord, r: L.Regex, str: string,
                                   i: int, j: int, gm: LG.GroupMap)
    requires GroupOkL(r)
    requires 0 <= i <= j <= |str|
    requires MatchesL(rer, r, str, i, j)
    ensures SuccActs(rer, [LS.Areg(r)], T.InputAt(str, i), gm, WP.Forward)
  {
    ReverseLength(str);
    MatchesLReverse(rer, r, str, i, j);
    RevLGroupOk(r);
    SpanDualityComplete(rer, RevL(r), LC.Reverse(str), |str| - j, |str| - i, gm);
    SuccActsForwardViaReverse(rer, r, str, i, gm);
  }

  /** THE FORWARD SOUNDNESS half: a successful forward walk yields a span. */
  lemma SpanDualityForwardSound(rer: LW.RegExpRecord, r: L.Regex, str: string,
                                cp: int, gm: LG.GroupMap) returns (j: int)
    requires GroupOkL(r)
    requires 0 <= cp <= |str|
    requires SuccActs(rer, [LS.Areg(r)], T.InputAt(str, cp), gm, WP.Forward)
    ensures cp <= j <= |str|
    ensures MatchesL(rer, r, str, cp, j)
  {
    ReverseLength(str);
    RevLGroupOk(r);
    SuccActsForwardViaReverse(rer, r, str, cp, gm);
    var m := SpanDualitySound(rer, RevL(r), LC.Reverse(str), |str| - cp, gm);
    // m is the START of the reversed span; mirror it back
    j := |str| - m;
    RevLInvolution(r);
    MatchesLReverse(rer, RevL(r), LC.Reverse(str), m, |str| - cp);
    assert MatchesL(rer, RevL(RevL(r)), LC.Reverse(LC.Reverse(str)),
                    |str| - (|str| - cp), |str| - m);
    FS.ReverseReverse(str);
  }

  // ===========================================================================
  // The reversal on the RegElk side, and its commutation with Translate
  // ===========================================================================

  function SwapAnchorRE(a: RE.anchor): RE.anchor {
    match a
    case BeginInput => RE.EndInput
    case EndInput => RE.BeginInput
    case WordBoundary => RE.WordBoundary
    case NonWordBoundary => RE.NonWordBoundary
  }

  /** `RevL` on the RegElk side: concatenation order flips and input anchors
      swap. Note this is `R.reverse_regex` PLUS the anchor swap -- the engine's
      own `reverse_regex` leaves anchors alone because backward EXECUTION
      handles them via its direction flag, whereas reversing the string makes
      the swap explicit. */
  function RevRE(r: RE.regex): RE.regex
    decreases r
  {
    match r
    case Re_empty => r
    case Re_character(_) => r
    case Re_anchor(a) => RE.Re_anchor(SwapAnchorRE(a))
    case Re_alt(r1, r2) => RE.Re_alt(RevRE(r1), RevRE(r2))
    case Re_con(r1, r2) => RE.Re_con(RevRE(r2), RevRE(r1))
    case Re_quant(n, q, qt, r1) => RE.Re_quant(n, q, qt, RevRE(r1))
    case Re_capture(c, r1) => RE.Re_capture(c, RevRE(r1))
    case Re_lookaround(l, lk, r1) => r
  }

  lemma RevRETransWf(r: RE.regex)
    requires T.TransWf(r)
    ensures T.TransWf(RevRE(r))
    decreases r
  {
    match r
    case Re_alt(r1, r2) => RevRETransWf(r1); RevRETransWf(r2);
    case Re_con(r1, r2) => RevRETransWf(r1); RevRETransWf(r2);
    case Re_quant(_, _, _, r1) => RevRETransWf(r1);
    case Re_capture(_, r1) => RevRETransWf(r1);
    case _ =>
  }

  /** The two reversals agree across the translation -- so a fact proved about
      `RevL` on the spec side transfers to `RevRE` on the engine side. */
  lemma TranslateRevRE(r: RE.regex)
    requires T.TransWf(r)
    ensures T.TransWf(RevRE(r))
    ensures T.Translate(RevRE(r)) == RevL(T.Translate(r))
    decreases r
  {
    RevRETransWf(r);
    match r
    case Re_alt(r1, r2) => TranslateRevRE(r1); TranslateRevRE(r2);
    case Re_con(r1, r2) => TranslateRevRE(r1); TranslateRevRE(r2);
    case Re_quant(_, _, _, r1) => TranslateRevRE(r1);
    case Re_capture(_, r1) => TranslateRevRE(r1);
    case Re_anchor(a) => assert T.TrAnchor(SwapAnchorRE(a)) == SwapAnchorL(T.TrAnchor(a));
    case _ =>
  }
}
