// The reduction toolkit (digit-capture README, promotion item 3): a library of
// homomorphism lemmas that mechanize "prove SpecRegex(p) == E" — the fuel-wall
// workaround of characterizing `Translate . annotate` instead of evaluating it
// (annotate/Translate never collapse on a 30-node constant; see the README's
// "the wall"). Each TA_* lemma unfolds exactly one constructor with the
// (capture, lookaround, quantifier) counter threading made explicit, so a
// concrete pattern's reduction is a short ladder of lemma calls at fuel 1 —
// what ButtonATree.dfy assembled by hand, packaged once.
include "Spec.dfy"

/** The reduction toolkit: `TA` characterizes `Translate . annotate_regex` with
    counters; the per-constructor `TA_*` lemmas unfold it one level at a time;
    `SpecRegexE` caps the ladder off with the `.*?` prefix and group-0 wrap.
    Counter bookkeeping (`numCaptures`, `AnnotateCounters`, `AnnotateMaxGroup`,
    `NGroupsEq`) is promoted here from the digit-capture example. */
module LindenElkReduce {
  import opened Std.Wrappers
  import LC = Chars
  import L = Regex
  import LN = WarblreNumeric
  import R = RegElkRegex
  import RC = Charclasses
  import T = LindenElkTranslate
  import LES = LindenElkSpec

  // ===========================================================================
  // TA — the characterization function all reduction lemmas speak about
  // ===========================================================================

  // Opaque: users never unfold TA — they chain the TA_* lemmas below. The
  // ensures keeps the capture counter's monotonicity visible so chained
  // occurrences of TA in lemma statements stay well-formed without a reveal.
  /** `Translate . annotate_regex` with the counter state made explicit: the
      Linden translation of `ra` annotated from counters `(c, l, q)`, together
      with the next fresh counters. THE object every reduction lemma is stated
      about; opaque — use the `TA_*` lemmas, never unfold it. */
  ghost function {:opaque} TA(ra: R.raw_regex, c: int, l: int, q: int): (res: (L.Regex, int, int, int))
    requires T.Latin1Wf(ra) && c >= 0
    ensures res.1 >= c
  {
    T.AnnotateRegexWf(ra, c, l, q);
    var (ar, c2, l2, q2) := R.annotate_regex(ra, c, l, q);
    (T.Translate(ar), c2, l2, q2)
  }

  // ===========================================================================
  // The per-constructor homomorphism ladder
  // ===========================================================================

  /** `TA` on the empty pattern: `Epsilon`, counters unchanged. */
  lemma TA_Empty(c: int, l: int, q: int)
    requires c >= 0
    ensures TA(R.Raw_empty, c, l, q) == (L.Epsilon, c, l, q)
  {
    reveal TA();
  }

  /** `TA` on a character node: `Character(CharToCd(ch))`, counters unchanged. */
  lemma TA_Char(ch: R.character, c: int, l: int, q: int)
    requires T.CharacterWfL1(ch) && c >= 0
    ensures TA(R.Raw_character(ch), c, l, q) == (L.Character(T.CharToCd(ch)), c, l, q)
  {
    reveal TA();
  }

  /** `TA` on an anchor: `AnchorR(TrAnchor(a))`, counters unchanged. */
  lemma TA_Anchor(a: R.anchor, c: int, l: int, q: int)
    requires c >= 0
    ensures TA(R.Raw_anchor(a), c, l, q) == (L.AnchorR(T.TrAnchor(a)), c, l, q)
  {
    reveal TA();
  }

  /** `TA` is a homomorphism over concatenation: `Sequence` of the parts, with
      the counters threaded left to right. */
  lemma TA_Con(r1: R.raw_regex, r2: R.raw_regex, c: int, l: int, q: int)
    requires T.Latin1Wf(r1) && T.Latin1Wf(r2) && c >= 0
    ensures var (e1, c1, l1, q1) := TA(r1, c, l, q);
            var (e2, c2, l2, q2) := TA(r2, c1, l1, q1);
            TA(R.Raw_con(r1, r2), c, l, q) == (L.Sequence(e1, e2), c2, l2, q2)
  {
    reveal TA();
    T.AnnotateRegexWf(r1, c, l, q);
    var (ar1, c1, l1, q1) := R.annotate_regex(r1, c, l, q);
    T.AnnotateRegexWf(r2, c1, l1, q1);
  }

  /** `TA` is a homomorphism over alternation: `Disjunction` of the parts, with
      the counters threaded left to right. */
  lemma TA_Alt(r1: R.raw_regex, r2: R.raw_regex, c: int, l: int, q: int)
    requires T.Latin1Wf(r1) && T.Latin1Wf(r2) && c >= 0
    ensures var (e1, c1, l1, q1) := TA(r1, c, l, q);
            var (e2, c2, l2, q2) := TA(r2, c1, l1, q1);
            TA(R.Raw_alt(r1, r2), c, l, q) == (L.Disjunction(e1, e2), c2, l2, q2)
  {
    reveal TA();
    T.AnnotateRegexWf(r1, c, l, q);
    var (ar1, c1, l1, q1) := R.annotate_regex(r1, c, l, q);
    T.AnnotateRegexWf(r2, c1, l1, q1);
  }

  /** `TA` on a shorthand quantifier (`* *? + +? ? ??`): `Quantified` per the
      canonicalized count; the quantifier id is consumed (body annotated at
      `q + 1`) and then dropped by `Translate`. */
  lemma TA_Quant(qk: R.quantifier, r1: R.raw_regex, c: int, l: int, q: int)
    requires T.Latin1Wf(r1) && c >= 0
    ensures var cq := R.quant_canonicalize(qk);
            var (e1, c1, l1, q1) := TA(r1, c, l, q + 1);
            TA(R.Raw_quant(qk, r1), c, l, q)
              == (L.Quantified(cq.greedy, cq.min as nat, T.TrDelta(cq), e1), c1, l1, q1)
  {
    reveal TA();
    T.AnnotateRegexWf(r1, c, l, q + 1);
  }

  /** `TA` on a counted quantifier `{n,m}`: as `TA_Quant`, without
      canonicalization. */
  lemma TA_Count(cq: R.counted_quantifier, r1: R.raw_regex, c: int, l: int, q: int)
    requires T.QuantWf(cq) && T.Latin1Wf(r1) && c >= 0
    ensures var (e1, c1, l1, q1) := TA(r1, c, l, q + 1);
            TA(R.Raw_count(cq, r1), c, l, q)
              == (L.Quantified(cq.greedy, cq.min as nat, T.TrDelta(cq), e1), c1, l1, q1)
  {
    reveal TA();
    T.AnnotateRegexWf(r1, c, l, q + 1);
  }

  /** `TA` on a capture group: `Group(c, body)` — the group id IS the incoming
      capture counter, and the body is annotated with it bumped. */
  lemma TA_Cap(r1: R.raw_regex, c: int, l: int, q: int)
    requires T.Latin1Wf(r1) && c >= 0
    ensures var (e1, c1, l1, q1) := TA(r1, c + 1, l, q);
            TA(R.Raw_capture(r1), c, l, q) == (L.Group(c as nat, e1), c1, l1, q1)
  {
    reveal TA();
    T.AnnotateRegexWf(r1, c + 1, l, q);
  }

  /** `TA` on a lookaround: `LookaroundR(TrLookaround(lk), body)`; the
      lookaround id is consumed (body annotated at `l + 1`) and dropped. */
  lemma TA_Look(lk: R.lookaround, r1: R.raw_regex, c: int, l: int, q: int)
    requires T.Latin1Wf(r1) && c >= 0
    ensures var (e1, c1, l1, q1) := TA(r1, c, l + 1, q);
            TA(R.Raw_lookaround(lk, r1), c, l, q)
              == (L.LookaroundR(T.TrLookaround(lk), e1), c1, l1, q1)
  {
    reveal TA();
    T.AnnotateRegexWf(r1, c, l + 1, q);
  }

  // ===========================================================================
  // Counter bookkeeping (promoted verbatim from examples/digit-capture)
  // ===========================================================================

  /** The number of capturing groups (`Raw_capture` nodes) in a raw regex. */
  function numCaptures(ra: R.raw_regex): nat
    decreases ra
  {
    match ra
    case Raw_empty => 0
    case Raw_character(_) => 0
    case Raw_anchor(_) => 0
    case Raw_alt(r1, r2) => numCaptures(r1) + numCaptures(r2)
    case Raw_con(r1, r2) => numCaptures(r1) + numCaptures(r2)
    case Raw_quant(_, r1) => numCaptures(r1)
    case Raw_count(_, r1) => numCaptures(r1)
    case Raw_capture(r1) => 1 + numCaptures(r1)
    case Raw_lookaround(_, r1) => numCaptures(r1)
  }

  /** `annotate_regex` threads the capture counter, incrementing by exactly one
      per `Raw_capture` node — so the counter out is the counter in plus
      `numCaptures`. */
  lemma AnnotateCounters(ra: R.raw_regex, c: int, l: int, q: int)
    ensures R.annotate_regex(ra, c, l, q).1 == c + numCaptures(ra)
    decreases ra
  {
    match ra
    case Raw_alt(r1, r2) =>
      AnnotateCounters(r1, c, l, q);
      var (_, c1, l1, q1) := R.annotate_regex(r1, c, l, q);
      AnnotateCounters(r2, c1, l1, q1);
    case Raw_con(r1, r2) =>
      AnnotateCounters(r1, c, l, q);
      var (_, c1, l1, q1) := R.annotate_regex(r1, c, l, q);
      AnnotateCounters(r2, c1, l1, q1);
    case Raw_quant(_, r1) => AnnotateCounters(r1, c, l, q + 1);
    case Raw_count(_, r1) => AnnotateCounters(r1, c, l, q + 1);
    case Raw_capture(r1) => AnnotateCounters(r1, c + 1, l, q);
    case Raw_lookaround(_, r1) => AnnotateCounters(r1, c, l + 1, q);
    case Raw_empty =>
    case Raw_character(_) =>
    case Raw_anchor(_) =>
  }

  /** The largest capture id assigned in a subtree annotated starting at `c` is
      `c + numCaptures - 1` (or 0 if the subtree has no captures). */
  lemma AnnotateMaxGroup(ra: R.raw_regex, c: int, l: int, q: int)
    requires c >= 0
    ensures R.max_group(R.annotate_regex(ra, c, l, q).0)
         == (if numCaptures(ra) == 0 then 0 else c + numCaptures(ra) - 1)
    decreases ra
  {
    match ra
    case Raw_alt(r1, r2) =>
      AnnotateMaxGroup(r1, c, l, q);
      AnnotateCounters(r1, c, l, q);
      var (_, c1, l1, q1) := R.annotate_regex(r1, c, l, q);
      AnnotateMaxGroup(r2, c1, l1, q1);
    case Raw_con(r1, r2) =>
      AnnotateMaxGroup(r1, c, l, q);
      AnnotateCounters(r1, c, l, q);
      var (_, c1, l1, q1) := R.annotate_regex(r1, c, l, q);
      AnnotateMaxGroup(r2, c1, l1, q1);
    case Raw_quant(_, r1) => AnnotateMaxGroup(r1, c, l, q + 1);
    case Raw_count(_, r1) => AnnotateMaxGroup(r1, c, l, q + 1);
    case Raw_capture(r1) => AnnotateMaxGroup(r1, c + 1, l, q);
    case Raw_lookaround(_, r1) => AnnotateMaxGroup(r1, c, l + 1, q);
    case Raw_empty =>
    case Raw_character(_) =>
    case Raw_anchor(_) =>
  }

  /** `TA`'s capture counter out is the counter in plus `numCaptures` — the
      fact that lets a ladder compute every intermediate counter statically. */
  lemma TA_Counters(ra: R.raw_regex, c: int, l: int, q: int)
    requires T.Latin1Wf(ra) && c >= 0
    ensures TA(ra, c, l, q).1 == c + numCaptures(ra)
  {
    reveal TA();
    AnnotateCounters(ra, c, l, q);
  }

  /** The group count of any pattern, in closed form: group 0 (the whole-match
      wrap `annotate` adds) plus one per `Raw_capture` node. Subsumes the
      per-pattern `NGroups... == k` proofs the examples did by hand. */
  lemma NGroupsEq(raw: R.raw_regex)
    ensures LES.NGroups(raw) == 1 + numCaptures(raw)
  {
    AnnotateMaxGroup(R.Raw_capture(raw), 0, 1, 1);
    assert numCaptures(R.Raw_capture(raw)) == 1 + numCaptures(raw);
  }

  // ===========================================================================
  // Translation-shape facts: counter independence and defined groups
  // ===========================================================================

  /** The translated shape of a capture-free subpattern is independent of ALL
      counters (`Translate` drops quantifier/lookaround ids, and with no
      captures the capture counter is never consulted) — so such a subpattern
      has one canonical translation wherever it occurs. */
  lemma TA_CaptureFree(ra: R.raw_regex, c: int, l: int, q: int, c': int, l': int, q': int)
    requires T.Latin1Wf(ra) && numCaptures(ra) == 0 && c >= 0 && c' >= 0
    ensures TA(ra, c, l, q).0 == TA(ra, c', l', q').0
    decreases ra
  {
    match ra
    case Raw_empty =>
      TA_Empty(c, l, q); TA_Empty(c', l', q');
    case Raw_character(ch) =>
      TA_Char(ch, c, l, q); TA_Char(ch, c', l', q');
    case Raw_anchor(a) =>
      TA_Anchor(a, c, l, q); TA_Anchor(a, c', l', q');
    case Raw_con(r1, r2) =>
      TA_Con(r1, r2, c, l, q); TA_Con(r1, r2, c', l', q');
      TA_CaptureFree(r1, c, l, q, c', l', q');
      TA_Counters(r1, c, l, q); TA_Counters(r1, c', l', q');
      var (_, c1, l1, q1) := TA(r1, c, l, q);
      var (_, c1', l1', q1') := TA(r1, c', l', q');
      TA_CaptureFree(r2, c1, l1, q1, c1', l1', q1');
    case Raw_alt(r1, r2) =>
      TA_Alt(r1, r2, c, l, q); TA_Alt(r1, r2, c', l', q');
      TA_CaptureFree(r1, c, l, q, c', l', q');
      TA_Counters(r1, c, l, q); TA_Counters(r1, c', l', q');
      var (_, c1, l1, q1) := TA(r1, c, l, q);
      var (_, c1', l1', q1') := TA(r1, c', l', q');
      TA_CaptureFree(r2, c1, l1, q1, c1', l1', q1');
    case Raw_quant(qk, r1) =>
      TA_Quant(qk, r1, c, l, q); TA_Quant(qk, r1, c', l', q');
      TA_CaptureFree(r1, c, l, q + 1, c', l', q' + 1);
    case Raw_count(cq, r1) =>
      TA_Count(cq, r1, c, l, q); TA_Count(cq, r1, c', l', q');
      TA_CaptureFree(r1, c, l, q + 1, c', l', q' + 1);
    case Raw_capture(r1) =>
      assert numCaptures(ra) >= 1;
    case Raw_lookaround(lk, r1) =>
      TA_Look(lk, r1, c, l, q); TA_Look(lk, r1, c', l', q');
      TA_CaptureFree(r1, c, l + 1, q, c', l' + 1, q');
  }

  /** The groups defined by a translated subpattern annotated from `c` are
      exactly the contiguous block `[c, c + numCaptures)` — depth-first
      annotation assigns ids densely. The workhorse behind locating a target
      group inside a larger pattern. */
  lemma TA_DefGroups(ra: R.raw_regex, c: int, l: int, q: int, gid: nat)
    requires T.Latin1Wf(ra) && c >= 0
    ensures gid in L.DefGroups(TA(ra, c, l, q).0) <==> c <= gid < c + numCaptures(ra)
    decreases ra
  {
    match ra
    case Raw_empty =>
      TA_Empty(c, l, q);
    case Raw_character(ch) =>
      TA_Char(ch, c, l, q);
    case Raw_anchor(a) =>
      TA_Anchor(a, c, l, q);
    case Raw_con(r1, r2) =>
      TA_Con(r1, r2, c, l, q);
      TA_Counters(r1, c, l, q);
      var (e1, c1, l1, q1) := TA(r1, c, l, q);
      TA_DefGroups(r1, c, l, q, gid);
      TA_DefGroups(r2, c1, l1, q1, gid);
      TA_Counters(r2, c1, l1, q1);
    case Raw_alt(r1, r2) =>
      TA_Alt(r1, r2, c, l, q);
      TA_Counters(r1, c, l, q);
      var (e1, c1, l1, q1) := TA(r1, c, l, q);
      TA_DefGroups(r1, c, l, q, gid);
      TA_DefGroups(r2, c1, l1, q1, gid);
      TA_Counters(r2, c1, l1, q1);
    case Raw_quant(qk, r1) =>
      TA_Quant(qk, r1, c, l, q);
      TA_DefGroups(r1, c, l, q + 1, gid);
    case Raw_count(cq, r1) =>
      TA_Count(cq, r1, c, l, q);
      TA_DefGroups(r1, c, l, q + 1, gid);
    case Raw_capture(r1) =>
      TA_Cap(r1, c, l, q);
      TA_DefGroups(r1, c + 1, l, q, gid);
    case Raw_lookaround(lk, r1) =>
      TA_Look(lk, r1, c, l, q);
      TA_DefGroups(r1, c, l + 1, q, gid);
  }

  // ===========================================================================
  // String literals (generalizes the example's lit/LitT/TransAnnLit)
  // ===========================================================================

  /** A literal string as a concatenation of single-character regexes. */
  function LitRe(s: string): R.raw_regex
    decreases |s|
  {
    if |s| == 0 then R.Raw_empty
    else R.Raw_con(R.raw_char(s[0]), LitRe(s[1..]))
  }

  /** The translated shape of `LitRe(s)`: a chain of `CdSingle` characters. */
  function LitT(s: string): L.Regex
    decreases |s|
  {
    if |s| == 0 then L.Epsilon
    else L.Sequence(L.Character(LC.CdSingle(s[0])), LitT(s[1..]))
  }

  /** Every character of `s` is 7-bit ASCII (RegElk's `char_wf` domain). */
  predicate AsciiLit(s: string) {
    forall i :: 0 <= i < |s| ==> s[i] as int < 128
  }

  /** A literal is Latin-1 well-formed and capture-free. */
  lemma LitReFacts(s: string)
    requires AsciiLit(s)
    ensures T.Latin1Wf(LitRe(s)) && numCaptures(LitRe(s)) == 0
    decreases |s|
  {
    if |s| > 0 {
      assert AsciiLit(s[1..]);
      LitReFacts(s[1..]);
    }
  }

  /** The literal reduction, once and for all: `TA` maps `LitRe(s)` to
      `LitT(s)` with all counters fixed — by string induction, so no ladder
      step is ever needed inside a literal. */
  lemma TA_Lit(s: string, c: int, l: int, q: int)
    requires AsciiLit(s) && c >= 0
    ensures T.Latin1Wf(LitRe(s))
    ensures TA(LitRe(s), c, l, q) == (LitT(s), c, l, q)
    decreases |s|
  {
    LitReFacts(s);
    if |s| == 0 {
      TA_Empty(c, l, q);
    } else {
      assert AsciiLit(s[1..]);
      TA_Lit(s[1..], c, l, q);
      TA_Char(R.Char(s[0]), c, l, q);
      assert T.CharToCd(R.Char(s[0])) == LC.CdSingle(s[0]);
      TA_Con(R.raw_char(s[0]), LitRe(s[1..]), c, l, q);
      assert LitRe(s) == R.Raw_con(R.raw_char(s[0]), LitRe(s[1..]));
    }
  }

  /** A translated literal defines no groups. */
  lemma LitTNoGroups(s: string)
    ensures L.DefGroups(LitT(s)) == []
    decreases |s|
  {
    if |s| > 0 { LitTNoGroups(s[1..]); }
  }

  // ===========================================================================
  // Perl-class descriptors
  // ===========================================================================

  /** The concrete `CharDescr` that `\d` translates to. */
  const CdDigit: LC.CharDescr := LC.CdUnion(LC.CdRange('0', '9'), LC.CdEmpty)

  /** `CharToCd` of the `\d` group is exactly `CdDigit` — lets a ladder replace
      the symbolic `CharToCd(Group(Digit))` with concrete data. */
  lemma CdDigitEq()
    ensures T.CharToCd(R.Group(RC.Digit)) == CdDigit
  {
    assert RC.group_to_range(RC.Digit) == [(48, 57)];
    assert T.ValidBounds([(48, 57)]);
    assert CdDigit == T.RangesToCd([(48, 57)]);
  }

  // ===========================================================================
  // The capstone: SpecRegex(raw) == the .*? prefix + group-0 wrap around a
  // ladder-reduced body (generalizes the example's SpecRegexButtonA)
  // ===========================================================================

  /** The translated body of `raw` as it sits inside `SpecRegex`'s group-0
      wrap (a name for `TA(raw, 1, 1, 1).0`, matching `annotate`'s counters). */
  ghost function SpecBody(raw: R.raw_regex): L.Regex
    requires T.Latin1Wf(raw)
  {
    TA(raw, 1, 1, 1).0
  }

  /** THE reduction capstone: once a ladder has reduced `TA(raw, 1, 1, 1).0` to
      concrete data `body`, the full spec regex is that body under the group-0
      wrap and the lazy `.*?` search prefix. After this, `SpecRegex(raw)` is
      DATA — pattern-matching on it needs no fuel. */
  lemma SpecRegexE(raw: R.raw_regex, body: L.Regex)
    requires T.Latin1Wf(raw)
    requires TA(raw, 1, 1, 1).0 == body
    ensures LES.SpecRegex(raw)
         == L.Sequence(L.Quantified(false, 0, LN.Inf, L.Character(LC.CdAll)),
                       L.Group(0, body))
  {
    reveal TA();
    T.AnnotateWf(raw);
    T.AnnotateRegexWf(raw, 1, 1, 1);
    var ab := R.annotate_regex(raw, 1, 1, 1).0;
    assert T.Translate(ab) == body;
    // annotate(raw) is the group-0 wrap around the body annotated at (1, 1, 1)
    assert R.annotate(raw) == R.Re_capture(0, ab);
    // lazy_prefix prepends the non-greedy .*?
    var prefix := R.Re_quant(R.NonNullable, 0, R.CountedQuant(0, None, false), R.Re_character(R.Dot));
    var lp := R.lazy_prefix(R.annotate(raw));
    assert lp == R.Re_con(prefix, R.Re_capture(0, ab));
    assert T.Translate(prefix) == L.Quantified(false, 0, LN.Inf, L.Character(LC.CdAll));
    assert LES.SpecRegex(raw) == T.Translate(lp);
  }
}
