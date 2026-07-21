// Phase 1: AST translation RegElk -> Linden, with the ground-level semantic
// agreement lemmas (characters and anchors).
//
// Design decision (plan finding 4): every RegElk character is translated to
// the CharDescr that matches RegElk's ACTUAL behavior — CdSingle/CdAll plus
// CdUnion-of-CdRange chains built from the very range lists the RegElk
// compiler consumes (group_to_range / class_to_range / range_neg). We never
// use Linden's ECMAScript descriptors (CdDot/CdDigits/...), so the agreement
// lemmas hold for arbitrary Unicode input strings with no input restriction.
include "LindenImports.dfy"
include "RegElkImports.dfy"

/** Translates a well-formed, annotated RegElk `regex` (package `regex-engine`)
    into Linden's `Regex` AST, and proves the ground-level semantic agreement
    lemmas — `CharSemAgree` for characters, `AnchorSemAgree` for anchors — that
    every later layer of the equivalence proof builds on. */
module LindenElkTranslate {
  import opened Std.Wrappers
  import LW = WarblreRegExpRecord
  import WP = WarblrePrimitives
  import LC = Chars
  import LG = Groups
  import L = Regex
  import LN = WarblreNumeric
  import LS = Semantics
  import R = RegElkRegex
  import RC = Charclasses
  import RA = Anchors

  // ===========================================================================
  // Range-list shape predicates
  // ===========================================================================

  // Bounds usable as Dafny chars without hitting the surrogate gap.
  /** A range endpoint pair that fits in the Latin-1 domain (0..255) RegElk's
      compiler operates in, so it converts safely to a Dafny `char`. */
  predicate ValidBound(p: (int, int)) {
    0 <= p.0 <= 255 && 0 <= p.1 <= 255
  }
  /** Every pair in `rs` satisfies `ValidBound`. */
  predicate ValidBounds(rs: seq<(int, int)>) {
    forall i :: 0 <= i < |rs| ==> ValidBound(rs[i])
  }

  /** `rs` is sorted (non-strictly) by range start. */
  predicate SortedByStart(rs: seq<(int, int)>) {
    forall i, j :: 0 <= i < j < |rs| ==> rs[i].0 <= rs[j].0
  }

  // The shape of compiler-emitted range lists: well-formed bounded pairs,
  // strictly increasing with a gap of at least one code point between ranges.
  /** The exact shape every RegElk-compiler-emitted range list has: bounded,
      strictly-increasing starts with at least one unmatched code point
      between consecutive ranges. The structural invariant `class_to_range`,
      `range_negation`, and `build_range` are all proved to maintain. */
  predicate Canonical(rs: seq<(int, int)>) {
    (forall i :: 0 <= i < |rs| ==> 0 <= rs[i].0 <= rs[i].1 <= 255)
    && (forall i :: 0 <= i < |rs| - 1 ==> rs[i+1].0 > rs[i].1 + 1)
  }

  /** Under `Canonical`, range starts are strictly increasing, not merely sorted. */
  lemma CanonicalStartsIncrease(rs: seq<(int, int)>, i: int, j: int)
    requires Canonical(rs) && 0 <= i < j < |rs|
    ensures rs[i].0 < rs[j].0
    decreases j - i
  {
    if j == i + 1 {
      assert rs[j].0 > rs[i].1 + 1 >= rs[i].0;
    } else {
      CanonicalStartsIncrease(rs, i, j - 1);
      CanonicalStartsIncrease(rs, j - 1, j);
    }
  }

  /** A `Canonical` list is both `SortedByStart` and `ValidBounds` — the two
      weaker facts the char-matching lemmas actually consume. */
  lemma CanonicalSorted(rs: seq<(int, int)>)
    requires Canonical(rs)
    ensures SortedByStart(rs) && ValidBounds(rs)
  {
    forall i, j | 0 <= i < j < |rs| ensures rs[i].0 <= rs[j].0 {
      CanonicalStartsIncrease(rs, i, j);
    }
  }

  /** In a `SortedByStart` list, the head has the minimum start of any element. */
  lemma SortedHeadMin(rs: seq<(int, int)>)
    requires SortedByStart(rs) && |rs| > 0
    ensures forall p :: p in rs ==> rs[0].0 <= p.0
  {
    forall p | p in rs ensures rs[0].0 <= p.0 {
      var k :| 0 <= k < |rs| && rs[k] == p;
    }
  }

  // ===========================================================================
  // is_in_range agrees with "some range contains c" on sorted lists
  // ===========================================================================

  /** `RC.is_in_range` (RegElk's range-membership check) agrees with the plain
      existential "some range contains `c`" on any `SortedByStart` list — the
      bridge `RangesToCdMatch` needs to reason about `is_in_range` as a
      membership fact. */
  lemma IsInRangeIffExists(c: int, l: seq<(int, int)>)
    requires SortedByStart(l)
    ensures RC.is_in_range(c, l) <==> exists i :: 0 <= i < |l| && l[i].0 <= c <= l[i].1
    decreases |l|
  {
    if |l| == 0 {
    } else {
      var ch1, ch2 := l[0].0, l[0].1;
      assert forall k :: 0 <= k < |l[1..]| ==> l[1..][k] == l[k+1];
      assert SortedByStart(l[1..]);
      if c < ch1 {
        // sorted: every start is >= ch1 > c
        assert forall i :: 0 <= i < |l| ==> l[i].0 >= ch1;
      } else if ch1 <= c <= ch2 {
        assert l[0].0 <= c <= l[0].1;
      } else {
        IsInRangeIffExists(c, l[1..]);
        // c not in l[0] (c > ch2), so exists-over-l == exists-over-tail
        assert (exists i :: 0 <= i < |l| && l[i].0 <= c <= l[i].1)
           <==> (exists k :: 0 <= k < |l[1..]| && l[1..][k].0 <= c <= l[1..][k].1);
      }
    }
  }

  // ===========================================================================
  // RangesToCd: the CharDescr image of a range list, and its match agreement
  // ===========================================================================

  /** Turns a range list into the equivalent Linden `CharDescr`: a `CdUnion`
      chain of one `CdRange` per pair. */
  function RangesToCd(rs: seq<(int, int)>): LC.CharDescr
    requires ValidBounds(rs)
    decreases |rs|
  {
    if |rs| == 0 then LC.CdEmpty
    else LC.CdUnion(LC.CdRange(rs[0].0 as char, rs[0].1 as char), RangesToCd(rs[1..]))
  }

  // Under case-sensitive matching, ExistCanonicalized is plain membership.
  /** Under case-sensitive matching (`!rer.ignoreCase`), Warblre's
      `ExistCanonicalized` collapses to plain set membership, since
      canonicalization is then the identity. */
  lemma ExistCanonCS(rer: LW.RegExpRecord, s: WP.CharSet, c: char)
    requires !rer.ignoreCase
    ensures WP.ExistCanonicalized(rer, s, c) <==> c in s
  {
    if WP.ExistCanonicalized(rer, s, c) {
      var c0 :| c0 in s && WP.Canonicalize(rer, c0) == c;
      WP.CanonicalizeCaseSensitive(rer, c0);
    }
    if c in s {
      WP.CanonicalizeCaseSensitive(rer, c);
      assert c in s && WP.Canonicalize(rer, c) == c;
    }
  }

  /** THE range-to-`CharDescr` agreement: `RangesToCd(rs)` matches `ch` (via
      Linden's `CharMatch`) iff `ch` falls inside one of `rs`'s ranges — the
      fact `CharSemAgree` instantiates for every `Group`/`Class`/`NegClass`
      character node. */
  lemma RangesToCdMatch(rer: LW.RegExpRecord, ch: char, rs: seq<(int, int)>)
    requires !rer.ignoreCase && ValidBounds(rs)
    ensures LC.CharMatch(rer, ch, RangesToCd(rs))
        <==> exists i :: 0 <= i < |rs| && rs[i].0 <= ch as int <= rs[i].1
    decreases |rs|
  {
    WP.CanonicalizeCaseSensitive(rer, ch);
    if |rs| == 0 {
    } else {
      var lo, hi := rs[0].0 as char, rs[0].1 as char;
      // the CdRange head matches iff ch lies in [rs[0].0, rs[0].1]
      calc {
        LC.CharMatchPrime(rer, ch, LC.CdRange(lo, hi));
        WP.ExistCanonicalized(rer, WP.Range(WP.FromNumericValue(WP.NumericValue(lo)), WP.FromNumericValue(WP.NumericValue(hi))), ch);
        { assert WP.FromNumericValue(WP.NumericValue(lo)) == lo && WP.FromNumericValue(WP.NumericValue(hi)) == hi; }
        WP.ExistCanonicalized(rer, WP.Range(lo, hi), ch);
        { ExistCanonCS(rer, WP.Range(lo, hi), ch); }
        ch in WP.Range(lo, hi);
        lo <= ch <= hi;
        rs[0].0 <= ch as int <= rs[0].1;
      }
      assert forall k :: 0 <= k < |rs[1..]| ==> rs[1..][k] == rs[k+1];
      RangesToCdMatch(rer, ch, rs[1..]);
      assert LC.CharMatch(rer, ch, RangesToCd(rs))
         <==> LC.CharMatchPrime(rer, ch, LC.CdRange(lo, hi)) || LC.CharMatch(rer, ch, RangesToCd(rs[1..]));
    }
  }

  // ===========================================================================
  // Canonicality of the compiler-emitted range lists
  // ===========================================================================

  // range_negation of a canonical list is canonical (and bounded below by min).
  /** Negating a `Canonical` range list (RegElk's `range_negation`) yields
      another `Canonical` list, with every start bounded below by `min`. */
  lemma RangeNegationCanonical(l: seq<(int, int)>, min: int)
    requires Canonical(l)
    requires 0 <= min <= 255
    requires |l| > 0 ==> min <= l[0].0
    ensures var out := RC.range_negation(l, min);
      Canonical(out) && forall k :: 0 <= k < |out| ==> out[k].0 >= min
    decreases |l|
  {
    if |l| == 0 {
    } else {
      var r1, r2 := l[0].0, l[0].1;
      assert forall k :: 0 <= k < |l[1..]| ==> l[1..][k] == l[k+1];
      assert Canonical(l[1..]);
      if r2 == RC.max_char {
        // next == []
      } else {
        if |l| > 1 {
          assert l[1].0 > r2 + 1;  // canonical gap
        }
        RangeNegationCanonical(l[1..], RC.next_char(r2));
      }
      var next := if r2 == RC.max_char then [] else RC.range_negation(l[1..], RC.next_char(r2));
      if min < r1 {
        var out := [(min, RC.prev_char(r1))] + next;
        assert out[0] == (min, r1 - 1);
        if |next| > 0 {
          assert next[0].0 >= r2 + 1 > (r1 - 1) + 1;
        }
        assert forall k :: 1 <= k < |out| ==> out[k] == next[k-1];
      } else {
        // out == next; starts >= r2+1 >= min since min <= r1 <= r2
      }
    }
  }

  // The three Perl-class constants and their negations are canonical.
  /** The three Perl character-class groups (`\d \w \s`) and their negations
      (`\D \W \S`) all translate to `Canonical` range lists via `RC.group_to_range`. */
  lemma GroupToRangeCanonical(g: RC.char_group)
    ensures Canonical(RC.group_to_range(g))
  {
    assert Canonical(RC.digit);
    assert Canonical(RC.word);
    assert Canonical(RC.space);
    match g
    case Digit =>
    case Word =>
    case Space =>
    case NonDigit => RangeNegationCanonical(RC.digit, 0);
    case NonWord => RangeNegationCanonical(RC.word, 0);
    case NonSpace => RangeNegationCanonical(RC.space, 0);
  }

  // ----- class_to_range: flatten, sort, merge -----

  // Latin-1 well-formedness of a class: RegElk's own class_wf (literal chars
  // ASCII, range endpoints ordered) plus explicit-range upper bounds <= 255
  // (the engine's documented 0..255 domain; everything Parser.parse produces).
  /** Latin-1 well-formedness of a `char_class`: RegElk's own `class_wf`
      strengthened with the engine's documented 0..255 domain on explicit
      ranges — the precondition every translation/agreement lemma in this
      file assumes about parser-produced classes. */
  predicate ClassWfL1(cl: RC.char_class) {
    R.class_wf(cl)
    && forall i :: 0 <= i < |cl| ==> (cl[i].CRange? ==> cl[i].c2 as int <= 255)
  }

  /** Every pair in `rs` is a valid, ordered Latin-1 bound — a weaker,
      order-agnostic cousin of `Canonical` used as an intermediate invariant
      before a list has been sorted/merged. */
  predicate MemBounds(rs: seq<(int, int)>) {
    forall p :: p in rs ==> 0 <= p.0 <= p.1 <= 255
  }

  /** `Canonical` implies `MemBounds`. */
  lemma CanonicalMemBounds(rs: seq<(int, int)>)
    requires Canonical(rs)
    ensures MemBounds(rs)
  {
    forall p | p in rs ensures 0 <= p.0 <= p.1 <= 255 {
      var k :| 0 <= k < |rs| && rs[k] == p;
    }
  }

  /** Flattening a well-formed class (`RC.class_flatten`) preserves `MemBounds`. */
  lemma ClassFlattenWf(cl: RC.char_class)
    requires ClassWfL1(cl)
    ensures MemBounds(RC.class_flatten(cl))
    decreases |cl|
  {
    if |cl| == 0 {
    } else {
      assert R.class_elt_wf(cl[0]);
      assert forall k :: 0 <= k < |cl[1..]| ==> cl[1..][k] == cl[k+1];
      ClassFlattenWf(cl[1..]);
      match cl[0]
      case CChar(x) =>
      case CRange(c1, c2) =>
        assert cl[0].CRange? && cl[0].c2 as int <= 255;
      case CGroup(g) =>
        GroupToRangeCanonical(g);
        CanonicalMemBounds(RC.group_to_range(g));
    }
  }

  /** Inserting into a `SortedByStart` list (`RC.insert_range`) preserves the
      sort and adds exactly `x` as a multiset element. */
  lemma InsertRangeSorted(x: (int, int), l: seq<(int, int)>)
    requires SortedByStart(l)
    ensures var out := RC.insert_range(x, l);
      SortedByStart(out) && multiset(out) == multiset([x] + l)
    decreases |l|
  {
    if |l| == 0 {
    } else if x.0 <= l[0].0 {
      assert RC.insert_range(x, l) == [x] + l;
    } else {
      assert forall k :: 0 <= k < |l[1..]| ==> l[1..][k] == l[k+1];
      InsertRangeSorted(x, l[1..]);
      var rest := RC.insert_range(x, l[1..]);
      var out := [l[0]] + rest;
      assert multiset(rest) == multiset([x] + l[1..]);
      assert multiset(out) == multiset([x] + l) by {
        assert [x] + l == [x] + [l[0]] + l[1..];
      }
      // every element of rest is x or from l[1..]; both have start >= l[0].0
      forall i, j | 0 <= i < j < |out| ensures out[i].0 <= out[j].0 {
        if i == 0 {
          assert out[j] == rest[j-1];
          assert rest[j-1] in multiset(rest);
          assert rest[j-1] == x || rest[j-1] in l[1..];
          if rest[j-1] in l[1..] {
            var k :| 0 <= k < |l[1..]| && l[1..][k] == rest[j-1];
          }
        } else {
          assert out[i] == rest[i-1] && out[j] == rest[j-1];
        }
      }
    }
  }

  /** `RC.sort_ranges` produces a `SortedByStart` permutation of its input. */
  lemma SortRangesSorted(l: seq<(int, int)>)
    ensures var out := RC.sort_ranges(l);
      SortedByStart(out) && multiset(out) == multiset(l)
    decreases |l|
  {
    if |l| == 0 {
    } else {
      assert forall k :: 0 <= k < |l[1..]| ==> l[1..][k] == l[k+1];
      SortRangesSorted(l[1..]);
      InsertRangeSorted(l[0], RC.sort_ranges(l[1..]));
      assert multiset([l[0]] + RC.sort_ranges(l[1..])) == multiset([l[0]]) + multiset(l[1..]);
      assert l == [l[0]] + l[1..];
    }
  }

  /** `MemBounds` transfers across equal multisets. */
  lemma MultisetMemBounds(a: seq<(int, int)>, b: seq<(int, int)>)
    requires multiset(a) == multiset(b) && MemBounds(b)
    ensures MemBounds(a)
  {
    forall p | p in a ensures 0 <= p.0 <= p.1 <= 255 {
      assert p in multiset(a);
      assert p in b;
    }
  }

  /** `RC.build_range`'s merge pass turns a sorted, bounded list into a
      `Canonical` one, with the first output pair starting at `current.0`. */
  lemma BuildRangeCanonical(current: (int, int), next: seq<(int, int)>)
    requires 0 <= current.0 <= current.1 <= 255
    requires MemBounds(next)
    requires SortedByStart(next)
    requires forall p :: p in next ==> current.0 <= p.0
    ensures var out := RC.build_range(current, next);
      Canonical(out) && |out| > 0 && out[0].0 == current.0
    decreases |next|
  {
    var cstart, cend := current.0, current.1;
    if cend == RC.max_char || |next| == 0 {
      assert RC.build_range(current, next) == [current];
    } else {
      var nstart, nend := next[0].0, next[0].1;
      assert next[0] in next;
      assert forall k :: 0 <= k < |next[1..]| ==> next[1..][k] == next[k+1];
      assert forall p :: p in next[1..] ==> p in next;
      assert SortedByStart(next[1..]);
      if nstart > RC.next_char(cend) {
        // disjoint: emit current, continue from next[0]
        forall p | p in next[1..] ensures nstart <= p.0 {
          var k :| 0 <= k < |next[1..]| && next[1..][k] == p;
        }
        BuildRangeCanonical((nstart, nend), next[1..]);
        var rest := RC.build_range((nstart, nend), next[1..]);
        var out := [current] + rest;
        assert out[0] == current && (forall k :: 1 <= k < |out| ==> out[k] == rest[k-1]);
        assert rest[0].0 == nstart > cend + 1;
      } else {
        // overlap/adjacent: extend current
        var merged := (cstart, RC.char_max(cend, nend));
        forall p | p in next[1..] ensures merged.0 <= p.0 {
          assert p in next;
        }
        BuildRangeCanonical(merged, next[1..]);
      }
    }
  }

  /** Top-level canonicality result: `RC.class_to_range` of a well-formed
      class is always `Canonical` — chains the flatten/sort/build_range
      lemmas above into the fact `CharSemAgree` needs. */
  lemma ClassToRangeCanonical(cl: RC.char_class)
    requires ClassWfL1(cl)
    ensures Canonical(RC.class_to_range(cl))
  {
    ClassFlattenWf(cl);
    SortRangesSorted(RC.class_flatten(cl));
    var lsort := RC.sort_ranges(RC.class_flatten(cl));
    MultisetMemBounds(lsort, RC.class_flatten(cl));
    if |lsort| == 0 {
    } else {
      assert lsort[0] in lsort;
      SortedHeadMin(lsort);
      assert forall k :: 0 <= k < |lsort[1..]| ==> lsort[1..][k] == lsort[k+1];
      assert forall p :: p in lsort[1..] ==> p in lsort;
      forall p | p in lsort[1..] ensures lsort[0].0 <= p.0 {
        assert p in lsort;
      }
      BuildRangeCanonical(lsort[0], lsort[1..]);
    }
  }

  // ===========================================================================
  // Character translation and the character-level agreement lemma
  // ===========================================================================

  // Latin-1 well-formedness of a single character node.
  /** Latin-1 well-formedness of a single character node: literal chars and
      classes must respect the engine's 0..255 domain. */
  predicate CharacterWfL1(c: R.character) {
    match c
    case Char(ch) => R.char_wf(ch)
    case Dot => true
    case Group(_) => true
    case Class(cl) => ClassWfL1(cl)
    case NegClass(cl) => ClassWfL1(cl)
  }

  // The char_expectation the RegElk compiler emits for a character node
  // (factored out of Compiler.compile's Re_character case; Phase 4 proves the
  // compiler emits Consume(ExpectationOf(c)) by definition).
  /** The `char_expectation` RegElk's compiler emits for character node `c` —
      the ground truth `CharSemAgree` proves the translated `CharDescr`
      (`CharToCd(c)`) matches exactly. */
  function ExpectationOf(c: R.character): RC.char_expectation {
    match c
    case Char(ch) => RC.Single(ch)
    case Dot => RC.All
    case Group(g) => RC.Ranges(RC.group_to_range(g))
    case Class(cl) => RC.Ranges(RC.class_to_range(cl))
    case NegClass(cl) => RC.Ranges(RC.range_neg(RC.class_to_range(cl)))
  }

  /** Translates a RegElk character node to the Linden `CharDescr` that
      matches RegElk's actual runtime behavior (built from the compiler's own
      range lists, never Linden's ECMAScript descriptors), so the agreement
      holds unconditionally over arbitrary Unicode input. */
  function CharToCd(c: R.character): LC.CharDescr
    requires CharacterWfL1(c)
  {
    match c
    case Char(ch) => LC.CdSingle(ch)
    case Dot => LC.CdAll
    case Group(g) =>
      assert ValidBounds(RC.group_to_range(g)) by {
        GroupToRangeCanonical(g);
        CanonicalSorted(RC.group_to_range(g));
      }
      RangesToCd(RC.group_to_range(g))
    case Class(cl) =>
      assert ValidBounds(RC.class_to_range(cl)) by {
        ClassToRangeCanonical(cl);
        CanonicalSorted(RC.class_to_range(cl));
      }
      RangesToCd(RC.class_to_range(cl))
    case NegClass(cl) =>
      assert ValidBounds(RC.range_neg(RC.class_to_range(cl))) by {
        ClassToRangeCanonical(cl);
        RangeNegationCanonical(RC.class_to_range(cl), 0);
        CanonicalSorted(RC.range_neg(RC.class_to_range(cl)));
      }
      RangesToCd(RC.range_neg(RC.class_to_range(cl)))
  }

  // THE character-level agreement: RegElk's is_accepted on the compiler's
  // expectation agrees with Linden's CharMatch on the translated descriptor,
  // for EVERY char (full Unicode), under the fixed case-sensitive record.
  /** THE character-level agreement lemma: RegElk's `is_accepted` on
      `ExpectationOf(c)` agrees with Linden's `CharMatch` on `CharToCd(c)`,
      for every `char` and every character-node shape — grounds all later
      reasoning about `Read`/`Mismatch` tree nodes in the simulation proof. */
  lemma CharSemAgree(rer: LW.RegExpRecord, c: R.character, ch: char)
    requires !rer.ignoreCase && CharacterWfL1(c)
    ensures RC.is_accepted(Some(ch), ExpectationOf(c)) <==> LC.CharMatch(rer, ch, CharToCd(c))
  {
    match c
    case Char(e) =>
      WP.CanonicalizeCaseSensitive(rer, ch);
      WP.CanonicalizeCaseSensitive(rer, e);
    case Dot =>
    case Group(g) =>
      var rs := RC.group_to_range(g);
      GroupToRangeCanonical(g);
      CanonicalSorted(rs);
      IsInRangeIffExists(ch as int, rs);
      RangesToCdMatch(rer, ch, rs);
    case Class(cl) =>
      var rs := RC.class_to_range(cl);
      ClassToRangeCanonical(cl);
      CanonicalSorted(rs);
      IsInRangeIffExists(ch as int, rs);
      RangesToCdMatch(rer, ch, rs);
    case NegClass(cl) =>
      var rs := RC.range_neg(RC.class_to_range(cl));
      ClassToRangeCanonical(cl);
      RangeNegationCanonical(RC.class_to_range(cl), 0);
      CanonicalSorted(rs);
      IsInRangeIffExists(ch as int, rs);
      RangesToCdMatch(rer, ch, rs);
  }

  // ===========================================================================
  // Anchors
  // ===========================================================================

  /** Translates a RegElk anchor to its Linden counterpart. */
  function TrAnchor(a: R.anchor): L.Anchor {
    match a
    case BeginInput => L.BeginInput
    case EndInput => L.EndInput
    case WordBoundary => L.WordBoundary
    case NonWordBoundary => L.NonWordBoundary
  }

  /** Translates a RegElk lookaround flavor to its Linden counterpart. */
  function TrLookaround(lk: R.lookaround): L.Lookaround {
    match lk
    case Lookahead => L.LookAhead
    case NegLookahead => L.NegLookAhead
    case Lookbehind => L.LookBehind
    case NegLookbehind => L.NegLookBehind
  }

  // Linden input at string position cp.
  /** The Linden `Input` (remaining suffix, reversed prefix) at string
      position `cp`. */
  function InputAt(str: LC.String, cp: nat): LC.Input
    requires cp <= |str|
  {
    LC.Input(str[cp..], LC.Reverse(str[..cp]))
  }

  // RegElk char_context at string position cp. Going backward the roles of
  // prevchar/nextchar are mirrored (Anchors.dfy header note).
  /** RegElk's `char_context` at string position `cp`, scanning in direction
      `dir` (the prev/next roles are mirrored when scanning backward). */
  function CpContext(str: LC.String, cp: nat, dir: RA.direction): RA.char_context
    requires cp <= |str|
  {
    var before := if cp == 0 then None else Some(str[cp-1]);
    var after := if cp == |str| then None else Some(str[cp]);
    match dir
    case Forward => RA.CharContext(before, after)
    case Backward => RA.CharContext(after, before)
  }

  /** Basic length/head facts about `LC.Reverse`, used to relate `InputAt`'s
      reversed prefix back to raw string indexing. */
  lemma ReverseProps(s: LC.String)
    ensures |LC.Reverse(s)| == |s|
    ensures |s| > 0 ==> LC.Reverse(s)[0] == s[|s|-1]
  {
    if |s| == 0 {
    } else {
      ReverseProps(s[1..]);
    }
  }

  /** Linden's `WordChar` agrees with RegElk's `is_ascii_word_character`. */
  lemma WordCharIff(rer: LW.RegExpRecord, c: char)
    ensures LC.WordChar(rer, c) <==> RC.is_ascii_word_character(c)
  {
    assert LC.WordChar(rer, c) <==> c in WP.AsciiWordCharacters();
  }

  // THE anchor-level agreement: RegElk's is_satisfied on the position context
  // agrees with Linden's AnchorSatisfied at the same position, both directions,
  // under multiline=false.
  /** THE anchor-level agreement lemma: RegElk's `is_satisfied` at a position
      context agrees with Linden's `AnchorSatisfied` at the corresponding
      `Input`, in both scan directions, under `multiline=false`. */
  lemma AnchorSemAgree(rer: LW.RegExpRecord, a: R.anchor, str: LC.String, cp: nat, dir: RA.direction)
    requires !rer.multiline && cp <= |str|
    ensures RA.is_satisfied(a, CpContext(str, cp, dir), dir)
        <==> LS.AnchorSatisfied(rer, TrAnchor(a), InputAt(str, cp))
  {
    var inp := InputAt(str, cp);
    ReverseProps(str[..cp]);
    assert |inp.pref| == cp;
    assert |inp.next| == |str| - cp;
    if cp > 0 {
      assert inp.pref[0] == str[..cp][cp-1] == str[cp-1];
    }
    var ctx := CpContext(str, cp, dir);
    match a
    case BeginInput =>
      assert LS.AnchorSatisfied(rer, L.BeginInput, inp) <==> cp == 0;
    case EndInput =>
      assert LS.AnchorSatisfied(rer, L.EndInput, inp) <==> cp == |str|;
    case WordBoundary =>
      BoundaryAgree(rer, str, cp, dir);
    case NonWordBoundary =>
      BoundaryAgree(rer, str, cp, dir);
  }

  /** Word-boundary case of `AnchorSemAgree`: RegElk's `is_boundary` agrees
      with Linden's `IsBoundary` at the corresponding `Input`. */
  lemma BoundaryAgree(rer: LW.RegExpRecord, str: LC.String, cp: nat, dir: RA.direction)
    requires cp <= |str|
    ensures RA.is_boundary(CpContext(str, cp, dir)) <==> LS.IsBoundary(rer, InputAt(str, cp))
  {
    var inp := InputAt(str, cp);
    ReverseProps(str[..cp]);
    assert |inp.pref| == cp;
    assert |inp.next| == |str| - cp;
    if cp > 0 {
      assert inp.pref[0] == str[..cp][cp-1] == str[cp-1];
      WordCharIff(rer, str[cp-1]);
    }
    if cp < |str| {
      assert inp.next[0] == str[cp];
      WordCharIff(rer, str[cp]);
    }
  }

  // ===========================================================================
  // Regex translation
  // ===========================================================================

  // Latin-1 well-formedness of a raw regex: RegElk's regex_wf strengthened
  // with explicit-range bounds <= 255 and non-negative counted minima.
  // Strictly contains everything Parser.parse can produce.
  /** Latin-1 well-formedness of a raw (pre-annotation) regex: RegElk's
      `regex_wf` strengthened with the same 0..255/non-negative constraints
      as `CharacterWfL1` — holds of everything `Parser.parse` can produce. */
  predicate Latin1Wf(raw: R.raw_regex)
    decreases raw
  {
    match raw
    case Raw_empty => true
    case Raw_anchor(_) => true
    case Raw_character(c) => CharacterWfL1(c)
    case Raw_alt(r1, r2) => Latin1Wf(r1) && Latin1Wf(r2)
    case Raw_con(r1, r2) => Latin1Wf(r1) && Latin1Wf(r2)
    case Raw_quant(_, r1) => Latin1Wf(r1)
    case Raw_count(q, r1) => 0 <= q.min && (q.max.Some? ==> q.min <= q.max.value) && Latin1Wf(r1)
    case Raw_capture(r1) => Latin1Wf(r1)
    case Raw_lookaround(_, r1) => Latin1Wf(r1)
  }

  /** A `counted_quantifier`'s bounds are sane: non-negative `min`, and `max`
      (if present) at least `min`. */
  predicate QuantWf(q: R.counted_quantifier) {
    0 <= q.min && (q.max.Some? ==> q.min <= q.max.value)
  }

  // What the translation needs of an annotated regex.
  /** What `Translate` needs of an *annotated* regex — the well-formedness
      invariant threaded through the translation, preserved by `annotate`
      (see `AnnotateWf`). */
  predicate TransWf(re: R.regex)
    decreases re
  {
    match re
    case Re_empty => true
    case Re_character(c) => CharacterWfL1(c)
    case Re_alt(r1, r2) => TransWf(r1) && TransWf(r2)
    case Re_con(r1, r2) => TransWf(r1) && TransWf(r2)
    case Re_quant(_, _, q, r1) => QuantWf(q) && TransWf(r1)
    case Re_capture(cid, r1) => cid >= 0 && TransWf(r1)
    case Re_lookaround(_, _, r1) => TransWf(r1)
    case Re_anchor(_) => true
  }

  /** Translates a counted quantifier's upper bound to Linden's `NoI`
      (`Inf` when unbounded, `NN(max-min)` otherwise). */
  function TrDelta(q: R.counted_quantifier): LN.NoI
    requires QuantWf(q)
  {
    match q.max
    case None => LN.Inf
    case Some(m) => LN.NN((m - q.min) as nat)
  }

  // The translation. Quantifier/lookaround ids are dropped (Linden has none);
  // capture ids become Linden group ids unchanged.
  /** THE AST translation: maps a well-formed, annotated RegElk `regex` to
      its Linden `Regex`, dropping RegElk-only quantifier/lookaround ids and
      carrying capture ids through unchanged as Linden group ids. */
  function Translate(re: R.regex): L.Regex
    requires TransWf(re)
    decreases re
  {
    match re
    case Re_empty => L.Epsilon
    case Re_character(c) => L.Character(CharToCd(c))
    case Re_alt(r1, r2) => L.Disjunction(Translate(r1), Translate(r2))
    case Re_con(r1, r2) => L.Sequence(Translate(r1), Translate(r2))
    case Re_quant(_, _, q, r1) => L.Quantified(q.greedy, q.min as nat, TrDelta(q), Translate(r1))
    case Re_capture(cid, r1) => L.Group(cid as nat, Translate(r1))
    case Re_lookaround(_, lk, r1) => L.LookaroundR(TrLookaround(lk), Translate(r1))
    case Re_anchor(a) => L.AnchorR(TrAnchor(a))
  }

  // annotate preserves Latin-1 well-formedness into TransWf.
  /** `R.annotate_regex` preserves Latin-1 well-formedness into `TransWf`, and
      never decreases the running capture-id counter — the structural fact
      `AnnotateWf` packages for top-level use. */
  lemma AnnotateRegexWf(ra: R.raw_regex, c: int, l: int, q: int)
    requires Latin1Wf(ra) && c >= 0
    ensures var (re, c2, l2, q2) := R.annotate_regex(ra, c, l, q);
      TransWf(re) && c2 >= c
    decreases ra
  {
    match ra
    case Raw_empty =>
    case Raw_anchor(_) =>
    case Raw_character(_) =>
    case Raw_alt(r1, r2) =>
      AnnotateRegexWf(r1, c, l, q);
      var (_, c1, l1, q1) := R.annotate_regex(r1, c, l, q);
      AnnotateRegexWf(r2, c1, l1, q1);
    case Raw_con(r1, r2) =>
      AnnotateRegexWf(r1, c, l, q);
      var (_, c1, l1, q1) := R.annotate_regex(r1, c, l, q);
      AnnotateRegexWf(r2, c1, l1, q1);
    case Raw_quant(quant, r1) =>
      AnnotateRegexWf(r1, c, l, q + 1);
      assert QuantWf(R.quant_canonicalize(quant));
    case Raw_count(quant, r1) =>
      AnnotateRegexWf(r1, c, l, q + 1);
    case Raw_capture(r1) =>
      AnnotateRegexWf(r1, c + 1, l, q);
    case Raw_lookaround(_, r1) =>
      AnnotateRegexWf(r1, c, l + 1, q);
  }

  /** Top-level well-formedness bridge: a well-formed raw regex, once
      `annotate`d and wrapped by `lazy_prefix`, satisfies `TransWf` — the
      precondition `Translate` needs, discharged automatically wherever
      `SpecRegex` is constructed. */
  lemma AnnotateWf(raw: R.raw_regex)
    requires Latin1Wf(raw)
    ensures TransWf(R.annotate(raw))
    ensures TransWf(R.lazy_prefix(R.annotate(raw)))
  {
    AnnotateRegexWf(R.Raw_capture(raw), 0, 1, 1);
  }
}
