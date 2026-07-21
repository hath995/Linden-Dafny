// Pattern combinators with pre-proven fact bundles: every recursive-predicate-
// on-a-constant obligation a TypedCapture client faces (StarFragmentRaw,
// Latin1Wf, SimpleRaw, numCaptures, POnlyRaw) is one lemma call per building
// block; the con/capture skeleton on top unfolds at fuel 1.
include "ApiReasoning.dfy"

/** Building blocks for supported patterns — `Lit`, `Cap`, `Plus1`, the Perl
    classes — each with a fact bundle discharging the structural side
    conditions of `LindenRegexReasoning.TypedCapture`/`CaptureInRange`. */
module LindenRegexPatterns {
  import opened Std.Wrappers
  import R = RegElkRegex
  import RC = Charclasses
  import NR = LindenElkNfaRep
  import LW = WarblreRegExpRecord
  import LC = Chars
  import T = LindenElkTranslate
  import RD = LindenElkReduce
  import TR = LindenElkTransfer
  import CC = CaptureContent

  // ===========================================================================
  // Canned character predicates
  // ===========================================================================
  const DigitPred: char -> bool := c => '0' <= c <= '9'
  const HexPred: char -> bool := c => ('0' <= c <= '9') || ('a' <= c <= 'f')
  const WordPred: char -> bool :=
    c => ('0' <= c <= '9') || ('A' <= c <= 'Z') || c == '_' || ('a' <= c <= 'z')

  // ===========================================================================
  // Combinators
  // ===========================================================================

  /** A literal string (a `Raw_con` chain of single characters). */
  function Lit(s: string): R.raw_regex { RD.LitRe(s) }

  /** A capturing group. */
  function Cap(r: R.raw_regex): R.raw_regex { R.Raw_capture(r) }

  /** `r+` rewritten as `r r*` — the star-fragment encoding of one-or-more
      (the engine's `+` itself is outside the currently proven fragment). */
  function Plus1(r: R.raw_regex): R.raw_regex { R.Raw_con(r, R.raw_star(r)) }

  /** `^` — begin of input (anchors are in the proven fragment). */
  const Bol: R.raw_regex := R.Raw_anchor(R.BeginInput)
  /** `$` — end of input. */
  const Eol: R.raw_regex := R.Raw_anchor(R.EndInput)
  /** `\b` / `\B` — word boundary / non-boundary. */
  const Wb: R.raw_regex := R.Raw_anchor(R.WordBoundary)
  const NWb: R.raw_regex := R.Raw_anchor(R.NonWordBoundary)

  /** `^r$` — the whole-input form of `r`. */
  function Exact(r: R.raw_regex): R.raw_regex {
    R.Raw_con(Bol, R.Raw_con(r, Eol))
  }

  /** Fact bundle for anchors: in the fragment, no captures. */
  lemma AnchorFacts(a: R.anchor)
    ensures NR.AnchorFragmentRaw(R.Raw_anchor(a)) && T.Latin1Wf(R.Raw_anchor(a))
    ensures TR.AltRaw(R.Raw_anchor(a)) && RD.numCaptures(R.Raw_anchor(a)) == 0
  {
  }

  /** `\d` */
  const Digit: R.raw_regex := R.raw_group(RC.Digit)
  /** `\w` */
  const Word: R.raw_regex := R.raw_group(RC.Word)

  // ===========================================================================
  // Fact bundles
  // ===========================================================================

  /** Everything TypedCapture needs to know about a literal: fragment
      membership, well-formedness, simplicity, no captures. */
  lemma LitFacts(s: string)
    requires RD.AsciiLit(s)
    ensures NR.StarFragmentRaw(Lit(s))
    ensures T.Latin1Wf(Lit(s))
    ensures TR.SimpleRaw(Lit(s))
    ensures RD.numCaptures(Lit(s)) == 0
    decreases |s|
  {
    if |s| > 0 {
      assert RD.AsciiLit(s[1..]);
      LitFacts(s[1..]);
    }
  }

  /** A literal is `P`-only whenever `P` holds of each of its characters
      (used when a literal sits INSIDE a typed capture body). */
  lemma LitPOnly(rer: LW.RegExpRecord, s: string, P: char -> bool)
    requires !rer.ignoreCase && RD.AsciiLit(s)
    requires forall i :: 0 <= i < |s| ==> P(s[i])
    ensures TR.POnlyRaw(rer, Lit(s), P)
    decreases |s|
  {
    if |s| > 0 {
      CC.CdSingleOnly(rer, s[0], P);
      assert T.CharToCd(R.Char(s[0])) == LC.CdSingle(s[0]);
      assert RD.AsciiLit(s[1..]);
      LitPOnly(rer, s[1..], P);
    }
  }

  /** Everything TypedCapture needs about `\d`, including that it is
      digit-only. */
  lemma DigitFacts(rer: LW.RegExpRecord)
    requires !rer.ignoreCase
    ensures NR.StarFragmentRaw(Digit) && T.Latin1Wf(Digit)
    ensures TR.SimpleRaw(Digit) && RD.numCaptures(Digit) == 0
    ensures TR.POnlyRaw(rer, Digit, DigitPred)
  {
    assert RC.group_to_range(RC.Digit) == [(48, 57)];
    assert T.ValidBounds([(48, 57)]);
    TR.RangesToCdOnly(rer, [(48, 57)], DigitPred);
    assert T.CharToCd(R.Group(RC.Digit)) == T.RangesToCd([(48, 57)]);
  }

  /** Everything TypedCapture needs about `\w`, including that it is
      word-char-only. */
  lemma WordFacts(rer: LW.RegExpRecord)
    requires !rer.ignoreCase
    ensures NR.StarFragmentRaw(Word) && T.Latin1Wf(Word)
    ensures TR.SimpleRaw(Word) && RD.numCaptures(Word) == 0
    ensures TR.POnlyRaw(rer, Word, WordPred)
  {
    var rs := [(48, 57), (65, 90), (95, 95), (97, 122)];
    assert RC.group_to_range(RC.Word) == rs;
    assert T.ValidBounds(rs);
    TR.RangesToCdOnly(rer, rs, WordPred);
    assert T.CharToCd(R.Group(RC.Word)) == T.RangesToCd(rs);
  }

  /** `a|b`. Patterns using it take the `Alt` route: `TR.AltRaw`,
      `TR.RawGidContainerAlt`, `LR.TypedCaptureAlt` (conditional conclusions —
      an untaken arm leaves its groups unset). */
  function Or(a: R.raw_regex, b: R.raw_regex): R.raw_regex { R.Raw_alt(a, b) }

  /** Greedy option, encoded as `r | ε` to stay inside the proven star
      fragment (the engine's native `?` quantifier awaits fragment growth).
      NOTE: an optional CAPTURE is written `Opt(Cap(x))` — supported today via
      `TypedCaptureAlt` — not `Cap(x)` under a quantifier. */
  function Opt(r: R.raw_regex): R.raw_regex { R.Raw_alt(r, R.Raw_empty) }

  /** Fact bundle for `Or`. */
  lemma OrFacts(a: R.raw_regex, b: R.raw_regex)
    requires NR.StarFragmentRaw(a) && T.Latin1Wf(a) && TR.AltRaw(a)
    requires NR.StarFragmentRaw(b) && T.Latin1Wf(b) && TR.AltRaw(b)
    ensures NR.StarFragmentRaw(Or(a, b)) && T.Latin1Wf(Or(a, b)) && TR.AltRaw(Or(a, b))
    ensures RD.numCaptures(Or(a, b)) == RD.numCaptures(a) + RD.numCaptures(b)
  {
  }

  /** Fact bundle for `Opt`. */
  lemma OptFacts(r: R.raw_regex)
    requires NR.StarFragmentRaw(r) && T.Latin1Wf(r) && TR.AltRaw(r)
    ensures NR.StarFragmentRaw(Opt(r)) && T.Latin1Wf(Opt(r)) && TR.AltRaw(Opt(r))
    ensures RD.numCaptures(Opt(r)) == RD.numCaptures(r)
  {
  }

  /** `r{n}` as n-fold concatenation — fixed-width fields (dates `\d{4}`,
      zip codes, ...) inside the star fragment. */
  function Rep(n: nat, r: R.raw_regex): R.raw_regex
    decreases n
  {
    if n == 0 then R.Raw_empty else R.Raw_con(r, Rep(n - 1, r))
  }

  /** `Rep` preserves every structural fact of a capture-free argument. */
  lemma RepFacts(n: nat, r: R.raw_regex)
    requires NR.StarFragmentRaw(r) && T.Latin1Wf(r) && TR.SimpleRaw(r)
    requires RD.numCaptures(r) == 0
    ensures NR.StarFragmentRaw(Rep(n, r)) && T.Latin1Wf(Rep(n, r))
    ensures TR.SimpleRaw(Rep(n, r)) && RD.numCaptures(Rep(n, r)) == 0
    decreases n
  {
    if n > 0 { RepFacts(n - 1, r); }
  }

  /** `Rep` preserves `P`-onliness. */
  lemma RepPOnly(rer: LW.RegExpRecord, n: nat, r: R.raw_regex, P: char -> bool)
    requires TR.POnlyRaw(rer, r, P)
    ensures TR.POnlyRaw(rer, Rep(n, r), P)
    decreases n
  {
    if n > 0 { RepPOnly(rer, n - 1, r, P); }
  }

  /** `Plus1` preserves every structural fact of its argument. */
  lemma Plus1Facts(r: R.raw_regex)
    requires NR.StarFragmentRaw(r) && T.Latin1Wf(r) && TR.SimpleRaw(r)
    ensures NR.StarFragmentRaw(Plus1(r)) && T.Latin1Wf(Plus1(r)) && TR.SimpleRaw(Plus1(r))
    ensures RD.numCaptures(Plus1(r)) == 2 * RD.numCaptures(r)
  {
  }

  /** `Plus1` preserves `P`-onliness. */
  lemma Plus1POnly(rer: LW.RegExpRecord, r: R.raw_regex, P: char -> bool)
    requires TR.POnlyRaw(rer, r, P)
    ensures TR.POnlyRaw(rer, Plus1(r), P)
  {
  }
}
