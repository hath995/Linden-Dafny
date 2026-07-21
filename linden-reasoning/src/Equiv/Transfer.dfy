// The raw-to-spec transfer layer: the fuel-wall BYPASS for the common case.
// Instead of reducing SpecRegex(p) to concrete data (Reduce.dfy's ladder, still
// available for bespoke L3 proofs), a client states three small TRANSPARENT
// predicates about their raw pattern — SimpleRaw, POnlyRaw, RawGidContainer —
// which unfold cheaply on concrete ASTs, and the lemmas here transfer them once
// and for all to the spec-side predicates CaptureContent's content theory
// needs (SimpleFragRe, POnly, GidContainer). No concrete Linden tree is ever
// written down.
include "Reduce.dfy"
include "CaptureContent.dfy"

/** Transfers structural facts about a raw RegElk pattern (simple fragment,
    P-only body, capture-group location) to the corresponding facts about
    `SpecRegex` of that pattern — the bridge that lets `ApiReasoning`'s
    `TypedCapture` run on preconditions a client can discharge by unfolding. */
module LindenElkTransfer {
  import opened Std.Wrappers
  import LC = Chars
  import L = Regex
  import LG = Groups
  import LN = WarblreNumeric
  import LW = WarblreRegExpRecord
  import R = RegElkRegex
  import RC = Charclasses
  import T = LindenElkTranslate
  import LES = LindenElkSpec
  import RD = LindenElkReduce
  import CC = CaptureContent

  // ===========================================================================
  // The raw-level predicates (transparent: clients unfold them on concrete
  // patterns, bottom-up along the con-spine)
  // ===========================================================================

  /** The raw image of `CC.SimpleFragRe`: no alternation, lookarounds, or
      anchors. (Alternation is the first planned lift — see the GUIDE.) */
  predicate SimpleRaw(ra: R.raw_regex)
    decreases ra
  {
    match ra
    case Raw_empty => true
    case Raw_character(_) => true
    case Raw_con(r1, r2) => SimpleRaw(r1) && SimpleRaw(r2)
    case Raw_quant(_, r1) => SimpleRaw(r1)
    case Raw_count(_, r1) => SimpleRaw(r1)
    case Raw_capture(r1) => SimpleRaw(r1)
    case Raw_alt(_, _) => false
    case Raw_lookaround(_, _) => false
    case Raw_anchor(_) => false
  }

  /** The raw image of `CC.POnly`: every character node's translated descriptor
      only matches `P`-characters, and the shape is capture-free
      Epsilon/Character/Sequence/Quantified. */
  ghost predicate POnlyRaw(rer: LW.RegExpRecord, ra: R.raw_regex, P: char -> bool)
    decreases ra
  {
    match ra
    case Raw_empty => true
    case Raw_character(ch) => T.CharacterWfL1(ch) && CC.CdOnly(rer, T.CharToCd(ch), P)
    case Raw_con(r1, r2) => POnlyRaw(rer, r1, P) && POnlyRaw(rer, r2, P)
    case Raw_quant(_, r1) => POnlyRaw(rer, r1, P)
    case Raw_count(_, r1) => POnlyRaw(rer, r1, P)
    case _ => false
  }

  /** The raw image of `CC.GidContainer`: descending from capture counter `c`
      (depth-first, matching `annotate`'s id assignment), the pattern holds the
      capture that gets id `gid` exactly once, with capture-free body `body`,
      never under a quantifier (whose per-iteration Reset would clear it). */
  ghost predicate RawGidContainer(ra: R.raw_regex, c: nat, gid: nat, body: R.raw_regex)
    decreases ra
  {
    match ra
    case Raw_capture(b) =>
      if gid == c then b == body && RD.numCaptures(b) == 0
      else c < gid && RawGidContainer(b, c + 1, gid, body)
    case Raw_con(r1, r2) =>
      if c <= gid < c + RD.numCaptures(r1) then RawGidContainer(r1, c, gid, body)
      else RawGidContainer(r2, c + RD.numCaptures(r1), gid, body)
    case _ => false
  }

  /** `RawGidContainer` pins `gid` inside the block of ids `ra` assigns, and
      the target body is capture-free. */
  lemma RawGidContainerBounds(ra: R.raw_regex, c: nat, gid: nat, body: R.raw_regex)
    requires RawGidContainer(ra, c, gid, body)
    ensures c <= gid < c + RD.numCaptures(ra)
    ensures RD.numCaptures(body) == 0
    decreases ra
  {
    match ra
    case Raw_capture(b) =>
      if gid != c { RawGidContainerBounds(b, c + 1, gid, body); }
    case Raw_con(r1, r2) =>
      if c <= gid < c + RD.numCaptures(r1) {
        RawGidContainerBounds(r1, c, gid, body);
      } else {
        RawGidContainerBounds(r2, c + RD.numCaptures(r1), gid, body);
      }
    case _ =>
  }

  /** The canonical translation of a capture-free subpattern (well-defined by
      `RD.TA_CaptureFree`: with no captures, the translated shape is counter-
      independent). */
  ghost function TrOf(ra: R.raw_regex): L.Regex
    requires T.Latin1Wf(ra)
  {
    RD.TA(ra, 0, 0, 0).0
  }

  // ===========================================================================
  // The transfer lemmas
  // ===========================================================================

  /** A simple raw pattern translates into the simple spec fragment. */
  lemma SimpleRawSpec(ra: R.raw_regex, c: int, l: int, q: int)
    requires T.Latin1Wf(ra) && SimpleRaw(ra) && c >= 0
    ensures CC.SimpleFragRe(RD.TA(ra, c, l, q).0)
    decreases ra
  {
    match ra
    case Raw_empty =>
      RD.TA_Empty(c, l, q);
    case Raw_character(ch) =>
      RD.TA_Char(ch, c, l, q);
    case Raw_con(r1, r2) =>
      RD.TA_Con(r1, r2, c, l, q);
      SimpleRawSpec(r1, c, l, q);
      var (e1, c1, l1, q1) := RD.TA(r1, c, l, q);
      SimpleRawSpec(r2, c1, l1, q1);
    case Raw_quant(qk, r1) =>
      RD.TA_Quant(qk, r1, c, l, q);
      SimpleRawSpec(r1, c, l, q + 1);
    case Raw_count(cq, r1) =>
      RD.TA_Count(cq, r1, c, l, q);
      SimpleRawSpec(r1, c, l, q + 1);
    case Raw_capture(r1) =>
      RD.TA_Cap(r1, c, l, q);
      SimpleRawSpec(r1, c + 1, l, q);
    case Raw_alt(_, _) =>
    case Raw_lookaround(_, _) =>
    case Raw_anchor(_) =>
  }

  /** A P-only raw pattern translates into a P-only spec regex. */
  lemma POnlyRawSpec(rer: LW.RegExpRecord, ra: R.raw_regex, P: char -> bool, c: int, l: int, q: int)
    requires T.Latin1Wf(ra) && POnlyRaw(rer, ra, P) && c >= 0
    ensures CC.POnly(rer, RD.TA(ra, c, l, q).0, P)
    decreases ra
  {
    match ra
    case Raw_empty =>
      RD.TA_Empty(c, l, q);
    case Raw_character(ch) =>
      RD.TA_Char(ch, c, l, q);
    case Raw_con(r1, r2) =>
      RD.TA_Con(r1, r2, c, l, q);
      POnlyRawSpec(rer, r1, P, c, l, q);
      var (e1, c1, l1, q1) := RD.TA(r1, c, l, q);
      POnlyRawSpec(rer, r2, P, c1, l1, q1);
    case Raw_quant(qk, r1) =>
      RD.TA_Quant(qk, r1, c, l, q);
      POnlyRawSpec(rer, r1, P, c, l, q + 1);
    case Raw_count(cq, r1) =>
      RD.TA_Count(cq, r1, c, l, q);
      POnlyRawSpec(rer, r1, P, c, l, q + 1);
    case _ =>
  }

  /** THE container transfer (the plan's hotspot): a raw-level capture location
      becomes a spec-level `GidContainer` for the canonical body translation,
      at any counter state that assigns the expected ids. */
  lemma RawGidContainerSpec(ra: R.raw_regex, c: nat, l: int, q: int, gid: nat, body: R.raw_regex)
    requires T.Latin1Wf(ra) && SimpleRaw(ra)
    requires RawGidContainer(ra, c, gid, body)
    ensures T.Latin1Wf(body)
    ensures CC.SimpleFragRe(RD.TA(ra, c as int, l, q).0)
    ensures CC.GidContainer(RD.TA(ra, c as int, l, q).0, gid, TrOf(body))
    decreases ra
  {
    SimpleRawSpec(ra, c as int, l, q);
    match ra
    case Raw_capture(b) =>
      RD.TA_Cap(b, c as int, l, q);
      var (eb, c1, l1, q1) := RD.TA(b, c as int + 1, l, q);
      if gid == c {
        // the target: its translated body IS the canonical translation
        RD.TA_CaptureFree(b, c as int + 1, l, q, 0, 0, 0);
        assert eb == TrOf(body);
        // and the body defines no groups (it is capture-free)
        RD.TA_DefGroups(body, 0, 0, 0, gid);
        assert gid !in L.DefGroups(TrOf(body));
      } else {
        // a wrapper capture: recurse; membership via the dense-id block
        RawGidContainerSpec(b, c + 1, l, q, gid, body);
        RawGidContainerBounds(b, c + 1, gid, body);
        RD.TA_DefGroups(b, c as int + 1, l, q, gid);
        assert gid in L.DefGroups(eb);
      }
    case Raw_con(r1, r2) =>
      RD.TA_Con(r1, r2, c as int, l, q);
      RD.TA_Counters(r1, c as int, l, q);
      var (e1, c1, l1, q1) := RD.TA(r1, c as int, l, q);
      assert c1 == c as int + RD.numCaptures(r1);
      RD.TA_DefGroups(r1, c as int, l, q, gid);
      RD.TA_DefGroups(r2, c1, l1, q1, gid);
      RD.TA_Counters(r2, c1, l1, q1);
      if c <= gid < c + RD.numCaptures(r1) {
        RawGidContainerSpec(r1, c, l, q, gid, body);
        assert gid in L.DefGroups(e1);
      } else {
        RawGidContainerBounds(r2, c + RD.numCaptures(r1), gid, body);
        RawGidContainerSpec(r2, c + RD.numCaptures(r1), l1, q1, gid, body);
        assert gid !in L.DefGroups(e1);
        assert gid in L.DefGroups(RD.TA(r2, c1, l1, q1).0);
      }
    case _ =>
  }

  // ===========================================================================
  // Whole-spec corollaries: the same facts about SpecRegex(raw) itself,
  // threading the .*? search prefix and the group-0 wrap
  // ===========================================================================

  /** `SpecRegex` of a simple pattern is in the simple spec fragment. */
  lemma SpecSimple(raw: R.raw_regex)
    requires T.Latin1Wf(raw) && SimpleRaw(raw)
    ensures CC.SimpleFragRe(LES.SpecRegex(raw))
  {
    RD.SpecRegexE(raw, RD.TA(raw, 1, 1, 1).0);
    SimpleRawSpec(raw, 1, 1, 1);
  }

  /** THE whole-spec container fact: a raw capture location (counted from 1,
      group 0 being the whole-match wrap) locates the group inside
      `SpecRegex(raw)` — `.*?` prefix and group-0 wrap included. */
  lemma SpecGidContainer(raw: R.raw_regex, gid: nat, body: R.raw_regex)
    requires T.Latin1Wf(raw) && SimpleRaw(raw)
    requires RawGidContainer(raw, 1, gid, body)
    ensures T.Latin1Wf(body)
    ensures CC.SimpleFragRe(LES.SpecRegex(raw))
    ensures CC.GidContainer(LES.SpecRegex(raw), gid, TrOf(body))
  {
    var bodyT := RD.TA(raw, 1, 1, 1).0;
    RD.SpecRegexE(raw, bodyT);
    SimpleRawSpec(raw, 1, 1, 1);
    RawGidContainerSpec(raw, 1, 1, 1, gid, body);
    RawGidContainerBounds(raw, 1, gid, body);
    RD.TA_DefGroups(raw, 1, 1, 1, gid);
    var prefix := L.Quantified(false, 0, LN.Inf, L.Character(LC.CdAll));
    assert LES.SpecRegex(raw) == L.Sequence(prefix, L.Group(0, bodyT));
    assert L.DefGroups(prefix) == [];
    assert gid >= 1;
    assert gid in L.DefGroups(bodyT);
    assert gid in L.DefGroups(L.Group(0, bodyT));
  }

  /** A range-list descriptor (what every RegElk `Group`/`Class`/`NegClass`
      translates to) only matches P-characters when every range is covered
      by P. (Engine-facing: `RangesToCd` mirrors RegElk's compiler ranges.) */
  lemma RangesToCdOnly(rer: LW.RegExpRecord, rs: seq<(int, int)>, P: char -> bool)
    requires !rer.ignoreCase && T.ValidBounds(rs)
    requires forall i :: 0 <= i < |rs| ==>
               forall c: char :: rs[i].0 <= c as int <= rs[i].1 ==> P(c)
    ensures CC.CdOnly(rer, T.RangesToCd(rs), P)
  {
    forall c: char | LC.CharMatch(rer, c, T.RangesToCd(rs))
      ensures P(c)
    {
      T.RangesToCdMatch(rer, c, rs);
      var i :| 0 <= i < |rs| && rs[i].0 <= c as int <= rs[i].1;
    }
  }

  // ===========================================================================
  // BRACKET CLASSES, coverage-style: prove a `[...]` class P-only WITHOUT ever
  // evaluating class_to_range on the concrete class. Coverage of the class's
  // elements is preserved through the compiler's flatten -> sort -> merge
  // pipeline, so the client's whole obligation is two index-based foralls over
  // the literal element list (see ClassPOnly / ClassWfFromElts).
  // ===========================================================================

  /** Every character inside any of `rs`'s ranges satisfies `P`. */
  ghost predicate RangesCovered(rs: seq<(int, int)>, P: char -> bool) {
    forall i :: 0 <= i < |rs| ==>
      forall c: char :: rs[i].0 <= c as int <= rs[i].1 ==> P(c)
  }

  /** Coverage of one bracket-class element by `P`. */
  ghost predicate ClassEltCovered(e: RC.char_class_elt, P: char -> bool) {
    match e
    case CChar(x) => P(x)
    case CRange(c1, c2) => forall c: char :: c1 <= c <= c2 ==> P(c)
    case CGroup(g) => RangesCovered(RC.group_to_range(g), P)
  }

  /** Coverage of a whole bracket class by `P` — the ONLY content obligation a
      client discharges (an index-based forall over the literal element list). */
  ghost predicate ClassCovered(cl: RC.char_class, P: char -> bool) {
    forall i :: 0 <= i < |cl| ==> ClassEltCovered(cl[i], P)
  }

  /** Coverage transfers across equal multisets (sorting is a permutation). */
  lemma CoveredPerm(a: seq<(int, int)>, b: seq<(int, int)>, P: char -> bool)
    requires multiset(a) == multiset(b) && RangesCovered(b, P)
    ensures RangesCovered(a, P)
  {
    forall i | 0 <= i < |a|
      ensures forall c: char :: a[i].0 <= c as int <= a[i].1 ==> P(c)
    {
      assert a[i] in multiset(a);
      assert a[i] in b;
      var j :| 0 <= j < |b| && b[j] == a[i];
    }
  }

  /** Flattening preserves coverage. */
  lemma FlattenCovered(cl: RC.char_class, P: char -> bool)
    requires ClassCovered(cl, P)
    ensures RangesCovered(RC.class_flatten(cl), P)
    decreases |cl|
  {
    if |cl| == 0 {
    } else {
      assert forall k :: 0 <= k < |cl[1..]| ==> cl[1..][k] == cl[k+1];
      FlattenCovered(cl[1..], P);
      var rest := RC.class_flatten(cl[1..]);
      match cl[0]
      case CChar(x) =>
        assert ClassEltCovered(cl[0], P);
        forall c: char | x as int <= c as int <= x as int ensures P(c) {
          assert c == x;
        }
        assert RC.class_flatten(cl) == [(x as int, x as int)] + rest;
      case CRange(c1, c2) =>
        assert ClassEltCovered(cl[0], P);
        forall c: char | c1 as int <= c as int <= c2 as int ensures P(c) {
          assert c1 <= c <= c2;
        }
        assert RC.class_flatten(cl) == [(c1 as int, c2 as int)] + rest;
      case CGroup(g) =>
        assert ClassEltCovered(cl[0], P);
        var grs := RC.group_to_range(g);
        assert RC.class_flatten(cl) == grs + rest;
        forall i | 0 <= i < |grs + rest|
          ensures forall c: char :: (grs + rest)[i].0 <= c as int <= (grs + rest)[i].1 ==> P(c)
        {
          if i < |grs| {
            assert (grs + rest)[i] == grs[i];
          } else {
            assert (grs + rest)[i] == rest[i - |grs|];
          }
        }
    }
  }

  /** The merge pass (`build_range`) preserves coverage: a merged range only
      covers points that some input range covered. */
  lemma BuildRangeCovered(current: (int, int), next: seq<(int, int)>, P: char -> bool)
    requires 0 <= current.0 <= current.1 <= 255
    requires T.MemBounds(next) && T.SortedByStart(next)
    requires forall p :: p in next ==> current.0 <= p.0
    requires forall c: char :: current.0 <= c as int <= current.1 ==> P(c)
    requires RangesCovered(next, P)
    ensures RangesCovered(RC.build_range(current, next), P)
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
      assert T.SortedByStart(next[1..]);
      assert RangesCovered(next[1..], P) by {
        forall i | 0 <= i < |next[1..]|
          ensures forall c: char :: next[1..][i].0 <= c as int <= next[1..][i].1 ==> P(c)
        {
          assert next[1..][i] == next[i+1];
        }
      }
      assert forall c: char :: nstart <= c as int <= nend ==> P(c);   // next[0] covered
      if nstart > RC.next_char(cend) {
        forall p | p in next[1..] ensures nstart <= p.0 {
          var k :| 0 <= k < |next[1..]| && next[1..][k] == p;
        }
        BuildRangeCovered((nstart, nend), next[1..], P);
        var rest := RC.build_range((nstart, nend), next[1..]);
        var out := [current] + rest;
        assert forall k :: 1 <= k < |out| ==> out[k] == rest[k-1];
        assert out[0] == current;
      } else {
        // overlap/adjacent: the merged range is covered by current + next[0]
        var merged := (cstart, RC.char_max(cend, nend));
        forall c: char | merged.0 <= c as int <= merged.1 ensures P(c) {
          if c as int <= cend {
            assert cstart <= c as int <= cend;
          } else {
            // nstart <= cend + 1 <= c as int, and c as int <= max(cend, nend) == nend here
            assert nstart <= c as int <= nend;
          }
        }
        forall p | p in next[1..] ensures merged.0 <= p.0 {
          assert p in next;
        }
        BuildRangeCovered(merged, next[1..], P);
      }
    }
  }

  /** Top-level coverage result: `class_to_range` of a covered class is
      covered — flatten/sort/merge never widen the matched set. */
  lemma ClassToRangeCovered(cl: RC.char_class, P: char -> bool)
    requires T.ClassWfL1(cl) && ClassCovered(cl, P)
    ensures RangesCovered(RC.class_to_range(cl), P)
  {
    T.ClassFlattenWf(cl);
    FlattenCovered(cl, P);
    T.SortRangesSorted(RC.class_flatten(cl));
    var lsort := RC.sort_ranges(RC.class_flatten(cl));
    T.MultisetMemBounds(lsort, RC.class_flatten(cl));
    CoveredPerm(lsort, RC.class_flatten(cl), P);
    if |lsort| == 0 {
    } else {
      assert lsort[0] in lsort;
      T.SortedHeadMin(lsort);
      assert forall k :: 0 <= k < |lsort[1..]| ==> lsort[1..][k] == lsort[k+1];
      assert forall p :: p in lsort[1..] ==> p in lsort;
      forall p | p in lsort[1..] ensures lsort[0].0 <= p.0 {
        assert p in lsort;
      }
      assert 0 <= lsort[0].0 <= lsort[0].1 <= 255 by {
        assert lsort[0] in lsort;
      }
      assert RangesCovered(lsort[1..], P) by {
        forall i | 0 <= i < |lsort[1..]|
          ensures forall c: char :: lsort[1..][i].0 <= c as int <= lsort[1..][i].1 ==> P(c)
        {
          assert lsort[1..][i] == lsort[i+1];
        }
      }
      assert forall c: char :: lsort[0].0 <= c as int <= lsort[0].1 ==> P(c);
      BuildRangeCovered(lsort[0], lsort[1..], P);
    }
  }

  /** Well-formedness of a class from element-wise facts — index-based, so a
      concrete class needs no recursion unrolling. */
  lemma ClassWfFromElts(cl: RC.char_class)
    requires forall i :: 0 <= i < |cl| ==> R.class_elt_wf(cl[i])
    requires forall i :: 0 <= i < |cl| ==> (cl[i].CRange? ==> cl[i].c2 as int <= 255)
    ensures T.ClassWfL1(cl)
    decreases |cl|
  {
    if |cl| > 0 {
      assert forall k :: 0 <= k < |cl[1..]| ==> cl[1..][k] == cl[k+1];
      ClassWfFromElts(cl[1..]);
    }
  }

  /** THE bracket-class discharge: a covered, well-formed class node is
      `P`-only — no `class_to_range` evaluation, no stepwise asserts. */
  lemma ClassPOnly(rer: LW.RegExpRecord, cl: RC.char_class, P: char -> bool)
    requires !rer.ignoreCase
    requires T.ClassWfL1(cl)
    requires ClassCovered(cl, P)
    ensures T.CharacterWfL1(R.Class(cl))
    ensures CC.CdOnly(rer, T.CharToCd(R.Class(cl)), P)
    ensures POnlyRaw(rer, R.raw_class(cl), P)
  {
    var rs := RC.class_to_range(cl);
    T.ClassToRangeCanonical(cl);
    T.CanonicalSorted(rs);
    ClassToRangeCovered(cl, P);
    RangesToCdOnly(rer, rs, P);
    assert T.CharToCd(R.Class(cl)) == T.RangesToCd(rs);
  }

  /** The canonical body translation of a P-only raw body is P-only. */
  lemma TrOfPOnly(rer: LW.RegExpRecord, body: R.raw_regex, P: char -> bool)
    requires T.Latin1Wf(body) && POnlyRaw(rer, body, P)
    ensures CC.POnly(rer, TrOf(body), P)
  {
    POnlyRawSpec(rer, body, P, 0, 0, 0);
  }

  // ===========================================================================
  // THE ALTERNATION LIFT (raw side): SimpleRaw/RawGidContainer extended with
  // Raw_alt, transferring to CC.AltFragRe/GidContainerAlt. The target group
  // may now sit inside ONE arm of an alternation — at the price of a
  // conditional conclusion (see ApiReasoning.TypedCaptureAlt).
  // ===========================================================================

  /** `SimpleRaw` plus alternation. */
  predicate AltRaw(ra: R.raw_regex)
    decreases ra
  {
    match ra
    case Raw_empty => true
    case Raw_character(_) => true
    case Raw_alt(r1, r2) => AltRaw(r1) && AltRaw(r2)
    case Raw_con(r1, r2) => AltRaw(r1) && AltRaw(r2)
    case Raw_quant(_, r1) => AltRaw(r1)
    case Raw_count(_, r1) => AltRaw(r1)
    case Raw_capture(r1) => AltRaw(r1)
    case Raw_lookaround(_, _) => false
    case Raw_anchor(_) => true
  }

  /** `RawGidContainer` plus alternation: the target may live in one arm. */
  ghost predicate RawGidContainerAlt(ra: R.raw_regex, c: nat, gid: nat, body: R.raw_regex)
    decreases ra
  {
    match ra
    case Raw_capture(b) =>
      if gid == c then b == body && RD.numCaptures(b) == 0
      else c < gid && RawGidContainerAlt(b, c + 1, gid, body)
    case Raw_con(r1, r2) =>
      if c <= gid < c + RD.numCaptures(r1) then RawGidContainerAlt(r1, c, gid, body)
      else RawGidContainerAlt(r2, c + RD.numCaptures(r1), gid, body)
    case Raw_alt(r1, r2) =>
      if c <= gid < c + RD.numCaptures(r1) then RawGidContainerAlt(r1, c, gid, body)
      else RawGidContainerAlt(r2, c + RD.numCaptures(r1), gid, body)
    case _ => false
  }

  lemma RawGidContainerAltBounds(ra: R.raw_regex, c: nat, gid: nat, body: R.raw_regex)
    requires RawGidContainerAlt(ra, c, gid, body)
    ensures c <= gid < c + RD.numCaptures(ra)
    ensures RD.numCaptures(body) == 0
    decreases ra
  {
    match ra
    case Raw_capture(b) =>
      if gid != c { RawGidContainerAltBounds(b, c + 1, gid, body); }
    case Raw_con(r1, r2) =>
      if c <= gid < c + RD.numCaptures(r1) {
        RawGidContainerAltBounds(r1, c, gid, body);
      } else {
        RawGidContainerAltBounds(r2, c + RD.numCaptures(r1), gid, body);
      }
    case Raw_alt(r1, r2) =>
      if c <= gid < c + RD.numCaptures(r1) {
        RawGidContainerAltBounds(r1, c, gid, body);
      } else {
        RawGidContainerAltBounds(r2, c + RD.numCaptures(r1), gid, body);
      }
    case _ =>
  }

  /** An alt-fragment raw pattern translates into the alt spec fragment. */
  lemma AltRawSpec(ra: R.raw_regex, c: int, l: int, q: int)
    requires T.Latin1Wf(ra) && AltRaw(ra) && c >= 0
    ensures CC.AltFragRe(RD.TA(ra, c, l, q).0)
    decreases ra
  {
    match ra
    case Raw_empty =>
      RD.TA_Empty(c, l, q);
    case Raw_character(ch) =>
      RD.TA_Char(ch, c, l, q);
    case Raw_alt(r1, r2) =>
      RD.TA_Alt(r1, r2, c, l, q);
      AltRawSpec(r1, c, l, q);
      var (e1, c1, l1, q1) := RD.TA(r1, c, l, q);
      AltRawSpec(r2, c1, l1, q1);
    case Raw_con(r1, r2) =>
      RD.TA_Con(r1, r2, c, l, q);
      AltRawSpec(r1, c, l, q);
      var (e1, c1, l1, q1) := RD.TA(r1, c, l, q);
      AltRawSpec(r2, c1, l1, q1);
    case Raw_quant(qk, r1) =>
      RD.TA_Quant(qk, r1, c, l, q);
      AltRawSpec(r1, c, l, q + 1);
    case Raw_count(cq, r1) =>
      RD.TA_Count(cq, r1, c, l, q);
      AltRawSpec(r1, c, l, q + 1);
    case Raw_capture(r1) =>
      RD.TA_Cap(r1, c, l, q);
      AltRawSpec(r1, c + 1, l, q);
    case Raw_lookaround(_, _) =>
    case Raw_anchor(a) =>
      RD.TA_Anchor(a, c, l, q);
  }

  /** The container transfer over the alternation fragment. */
  lemma RawGidContainerAltSpec(ra: R.raw_regex, c: nat, l: int, q: int, gid: nat, body: R.raw_regex)
    requires T.Latin1Wf(ra) && AltRaw(ra)
    requires RawGidContainerAlt(ra, c, gid, body)
    ensures T.Latin1Wf(body)
    ensures CC.AltFragRe(RD.TA(ra, c as int, l, q).0)
    ensures CC.GidContainerAlt(RD.TA(ra, c as int, l, q).0, gid, TrOf(body))
    decreases ra
  {
    AltRawSpec(ra, c as int, l, q);
    match ra
    case Raw_capture(b) =>
      RD.TA_Cap(b, c as int, l, q);
      var (eb, c1, l1, q1) := RD.TA(b, c as int + 1, l, q);
      if gid == c {
        RD.TA_CaptureFree(b, c as int + 1, l, q, 0, 0, 0);
        assert eb == TrOf(body);
        RD.TA_DefGroups(body, 0, 0, 0, gid);
        assert gid !in L.DefGroups(TrOf(body));
      } else {
        RawGidContainerAltSpec(b, c + 1, l, q, gid, body);
        RawGidContainerAltBounds(b, c + 1, gid, body);
        RD.TA_DefGroups(b, c as int + 1, l, q, gid);
        assert gid in L.DefGroups(eb);
      }
    case Raw_con(r1, r2) =>
      RD.TA_Con(r1, r2, c as int, l, q);
      RD.TA_Counters(r1, c as int, l, q);
      var (e1, c1, l1, q1) := RD.TA(r1, c as int, l, q);
      assert c1 == c as int + RD.numCaptures(r1);
      RD.TA_DefGroups(r1, c as int, l, q, gid);
      RD.TA_DefGroups(r2, c1, l1, q1, gid);
      RD.TA_Counters(r2, c1, l1, q1);
      if c <= gid < c + RD.numCaptures(r1) {
        RawGidContainerAltSpec(r1, c, l, q, gid, body);
        assert gid in L.DefGroups(e1);
      } else {
        RawGidContainerAltBounds(r2, c + RD.numCaptures(r1), gid, body);
        RawGidContainerAltSpec(r2, c + RD.numCaptures(r1), l1, q1, gid, body);
        assert gid !in L.DefGroups(e1);
        assert gid in L.DefGroups(RD.TA(r2, c1, l1, q1).0);
      }
    case Raw_alt(r1, r2) =>
      RD.TA_Alt(r1, r2, c as int, l, q);
      RD.TA_Counters(r1, c as int, l, q);
      var (e1, c1, l1, q1) := RD.TA(r1, c as int, l, q);
      assert c1 == c as int + RD.numCaptures(r1);
      RD.TA_DefGroups(r1, c as int, l, q, gid);
      RD.TA_DefGroups(r2, c1, l1, q1, gid);
      RD.TA_Counters(r2, c1, l1, q1);
      if c <= gid < c + RD.numCaptures(r1) {
        RawGidContainerAltSpec(r1, c, l, q, gid, body);
        assert gid in L.DefGroups(e1);
      } else {
        RawGidContainerAltBounds(r2, c + RD.numCaptures(r1), gid, body);
        RawGidContainerAltSpec(r2, c + RD.numCaptures(r1), l1, q1, gid, body);
        assert gid !in L.DefGroups(e1);
        assert gid in L.DefGroups(RD.TA(r2, c1, l1, q1).0);
      }
    case _ =>
  }

  /** Whole-spec alternation-fragment container fact (`.*?` prefix and group-0
      wrap included). */
  lemma SpecGidContainerAlt(raw: R.raw_regex, gid: nat, body: R.raw_regex)
    requires T.Latin1Wf(raw) && AltRaw(raw)
    requires RawGidContainerAlt(raw, 1, gid, body)
    ensures T.Latin1Wf(body)
    ensures CC.AltFragRe(LES.SpecRegex(raw))
    ensures CC.GidContainerAlt(LES.SpecRegex(raw), gid, TrOf(body))
  {
    var bodyT := RD.TA(raw, 1, 1, 1).0;
    RD.SpecRegexE(raw, bodyT);
    AltRawSpec(raw, 1, 1, 1);
    RawGidContainerAltSpec(raw, 1, 1, 1, gid, body);
    RawGidContainerAltBounds(raw, 1, gid, body);
    RD.TA_DefGroups(raw, 1, 1, 1, gid);
    var prefix := L.Quantified(false, 0, LN.Inf, L.Character(LC.CdAll));
    assert LES.SpecRegex(raw) == L.Sequence(prefix, L.Group(0, bodyT));
    assert L.DefGroups(prefix) == [];
    assert gid >= 1;
    assert gid in L.DefGroups(bodyT);
    assert gid in L.DefGroups(L.Group(0, bodyT));
  }

  // ===========================================================================
  // Structural conveniences
  // ===========================================================================

  /** A capture-free simple pattern is trivially `(c => true)`-only — the
      instantiation behind bounds-only conclusions (`CaptureInRange`). */
  lemma POnlyRawTrue(rer: LW.RegExpRecord, ra: R.raw_regex)
    requires T.Latin1Wf(ra) && SimpleRaw(ra) && RD.numCaptures(ra) == 0
    ensures POnlyRaw(rer, ra, c => true)
    decreases ra
  {
    match ra
    case Raw_con(r1, r2) => POnlyRawTrue(rer, r1); POnlyRawTrue(rer, r2);
    case Raw_quant(_, r1) => POnlyRawTrue(rer, r1);
    case Raw_count(_, r1) => POnlyRawTrue(rer, r1);
    case _ =>
  }

  /** The simple raw fragment embeds in the alternation raw fragment. */
  lemma SimpleRawIsAltRaw(ra: R.raw_regex)
    requires SimpleRaw(ra)
    ensures AltRaw(ra)
    decreases ra
  {
    match ra
    case Raw_con(r1, r2) => SimpleRawIsAltRaw(r1); SimpleRawIsAltRaw(r2);
    case Raw_quant(_, r1) => SimpleRawIsAltRaw(r1);
    case Raw_count(_, r1) => SimpleRawIsAltRaw(r1);
    case Raw_capture(r1) => SimpleRawIsAltRaw(r1);
    case _ =>
  }

  /** A simple-fragment container is an alternation-fragment container. */
  lemma RawGidContainerIsAlt(ra: R.raw_regex, c: nat, gid: nat, body: R.raw_regex)
    requires RawGidContainer(ra, c, gid, body)
    ensures RawGidContainerAlt(ra, c, gid, body)
    decreases ra
  {
    match ra
    case Raw_capture(b) =>
      if gid != c { RawGidContainerIsAlt(b, c + 1, gid, body); }
    case Raw_con(r1, r2) =>
      if c <= gid < c + RD.numCaptures(r1) {
        RawGidContainerIsAlt(r1, c, gid, body);
      } else {
        RawGidContainerIsAlt(r2, c + RD.numCaptures(r1), gid, body);
      }
    case _ =>
  }

  /** The container's target body inherits membership in the simple fragment. */
  lemma RawGidContainerSimple(ra: R.raw_regex, c: nat, gid: nat, body: R.raw_regex)
    requires SimpleRaw(ra) && RawGidContainer(ra, c, gid, body)
    ensures SimpleRaw(body)
    decreases ra
  {
    match ra
    case Raw_capture(b) =>
      if gid != c { RawGidContainerSimple(b, c + 1, gid, body); }
    case Raw_con(r1, r2) =>
      if c <= gid < c + RD.numCaptures(r1) {
        RawGidContainerSimple(r1, c, gid, body);
      } else {
        RawGidContainerSimple(r2, c + RD.numCaptures(r1), gid, body);
      }
    case _ =>
  }
}
