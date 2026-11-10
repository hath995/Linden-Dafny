// G5: CdnSound (package linden-equiv-cdn-sound; first proved by the W5 endgame
// subagent, see linden-equiv/endgame/W5-cdn.md).
//
// The CDN guard `CheckNullable(qid)` reads `cdn_get(table, qid)` where the table
// is `build_cdn_v(compile_cdns(re), cp, ov, ctx, dir)`. This module proves that
// the table means "the quantifier's body matches the EMPTY span at cp" in the
// kind-blind gated span predicate `OBV.MatchesV`:
//
//   CdnfSound  : interpret_cdn_v(compile_cdnf(r), cp, ov, t, ctx, dir)
//                  <==> MatchesV(r, str, ov, cp, cp)
//                under CdnWf(r), ctx == cp_context(cp, str, dir), and a table
//                hypothesis for the inner CDN pluses compile_cdnf reads.
//   CdnSound   : every eligible CDN plus `qid` of `re` has
//                  cdn_get(build_cdn_v(compile_cdns(re), …), qid)
//                    <==> MatchesV(body_of(qid), str, ov, cp, cp)
//                and no other id is in the table (QUnique + CdnWf).
//
// Checked against linden-equiv-oracle-bridge-v's deps + its .doo. No axioms.
module LindenElkCdnSound {
  import opened Std.Wrappers
  import R = RegElkRegex
  import C = Cdn
  import LOr = Oracle
  import LAnc = Anchors
  import AI = ArrayInterp
  import ORc = LindenElkOracleReach
  import OBV = LindenElkOracleBridgeV
  import T = LindenElkTranslate
  import CP = Compiler

  // ===========================================================================
  // Premises
  // ===========================================================================

  /** Quantifier bounds are sane and every stored nullability annotation is
      what `R.nullable` computes for the body (what `annotate_regex` writes).
      Exactly the quantifier part of `T.TransWf` (see `TransWfCdnWf`). */
  predicate CdnWf(r: R.regex)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => CdnWf(r1) && CdnWf(r2)
    case Re_con(r1, r2) => CdnWf(r1) && CdnWf(r2)
    case Re_quant(nul, _, q, r1) =>
      0 <= q.min && (q.max.Some? ==> q.min <= q.max.value) && nul == R.nullable(r1) && CdnWf(r1)
    case Re_capture(_, r1) => CdnWf(r1)
    case Re_lookaround(_, _, r1) => CdnWf(r1)
    case _ => true
  }

  lemma TransWfCdnWf(r: R.regex)
    requires T.TransWf(r)
    ensures CdnWf(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => TransWfCdnWf(r1); TransWfCdnWf(r2);
    case Re_con(r1, r2) => TransWfCdnWf(r1); TransWfCdnWf(r2);
    case Re_quant(_, _, _, r1) => TransWfCdnWf(r1);
    case Re_capture(_, r1) => TransWfCdnWf(r1);
    case Re_lookaround(_, _, r1) => TransWfCdnWf(r1);
    case _ =>
  }

  /** The quantifier shape `compile_cdns_rec` lists (a greedy, unbounded,
      `min > 0`, context-dependent-nullable plus). */
  predicate EligibleCdnPlus(nul: R.nullability, q: R.counted_quantifier) {
    nul == R.CDNullable && q.min > 0 && q.max == None && q.greedy
  }

  /** `t` is right at `cp` about every eligible CDN plus that `compile_cdnf(r)`
      can reach (it never looks below a lookaround). */
  ghost predicate TableOkLocal(r: R.regex, t: C.cdn_table, str: string, ov: LOr.OracleView, cp: int)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => TableOkLocal(r1, t, str, ov, cp) && TableOkLocal(r2, t, str, ov, cp)
    case Re_con(r1, r2) => TableOkLocal(r1, t, str, ov, cp) && TableOkLocal(r2, t, str, ov, cp)
    case Re_quant(nul, qid, q, r1) =>
      (EligibleCdnPlus(nul, q) ==> (C.cdn_get(t, qid) <==> OBV.MatchesV(r1, str, ov, cp, cp)))
      && TableOkLocal(r1, t, str, ov, cp)
    case Re_capture(_, r1) => TableOkLocal(r1, t, str, ov, cp)
    case _ => true
  }

  /** `t` is right at `cp` about EVERY eligible CDN plus of `r`, including those
      inside lookaround bodies (`compile_cdns_rec` lists those too). */
  ghost predicate TableOkAll(r: R.regex, t: C.cdn_table, str: string, ov: LOr.OracleView, cp: int)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => TableOkAll(r1, t, str, ov, cp) && TableOkAll(r2, t, str, ov, cp)
    case Re_con(r1, r2) => TableOkAll(r1, t, str, ov, cp) && TableOkAll(r2, t, str, ov, cp)
    case Re_quant(nul, qid, q, r1) =>
      (EligibleCdnPlus(nul, q) ==> (C.cdn_get(t, qid) <==> OBV.MatchesV(r1, str, ov, cp, cp)))
      && TableOkAll(r1, t, str, ov, cp)
    case Re_capture(_, r1) => TableOkAll(r1, t, str, ov, cp)
    case Re_lookaround(_, _, r1) => TableOkAll(r1, t, str, ov, cp)
    case _ => true
  }

  lemma TableOkAllLocal(r: R.regex, t: C.cdn_table, str: string, ov: LOr.OracleView, cp: int)
    requires TableOkAll(r, t, str, ov, cp)
    ensures TableOkLocal(r, t, str, ov, cp)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => TableOkAllLocal(r1, t, str, ov, cp); TableOkAllLocal(r2, t, str, ov, cp);
    case Re_con(r1, r2) => TableOkAllLocal(r1, t, str, ov, cp); TableOkAllLocal(r2, t, str, ov, cp);
    case Re_quant(_, _, _, r1) => TableOkAllLocal(r1, t, str, ov, cp);
    case Re_capture(_, r1) => TableOkAllLocal(r1, t, str, ov, cp);
    case _ =>
  }

  // ===========================================================================
  // Span facts at an empty span
  // ===========================================================================

  /** Anchors read the same under every scan direction, provided the context
      is the one that direction holds at `cp`. */
  lemma AnchorDirInvariant(a: R.anchor, str: string, cp: int, dir: LAnc.direction)
    ensures LAnc.is_satisfied(a, AI.cp_context(cp, str, dir), dir)
        == LAnc.is_satisfied(a, ORc.CtxAt(str, cp), LAnc.Forward)
  {
  }

  /** `k > 0` empty iterations exist iff the body matches the empty span. */
  lemma IterEmptyIntro(r1: R.regex, k: nat, str: string, ov: LOr.OracleView, cp: int)
    requires OBV.MatchesV(r1, str, ov, cp, cp)
    ensures OBV.MatchesIterV(r1, k, str, ov, cp, cp)
    decreases k
  {
    if k > 0 {
      IterEmptyIntro(r1, k - 1, str, ov, cp);
      assert OBV.MatchesV(r1, str, ov, cp, cp) && OBV.MatchesIterV(r1, k - 1, str, ov, cp, cp);
    }
  }

  lemma IterEmptyIff(r1: R.regex, k: nat, str: string, ov: LOr.OracleView, cp: int)
    requires k > 0
    ensures OBV.MatchesIterV(r1, k, str, ov, cp, cp) <==> OBV.MatchesV(r1, str, ov, cp, cp)
  {
    if OBV.MatchesIterV(r1, k, str, ov, cp, cp) {
      var m := OBV.MatchesIterVHead(r1, k, str, ov, cp, cp);
      OBV.MatchesVBounds(r1, str, ov, cp, m);
      OBV.MatchesIterVBounds(r1, k - 1, str, ov, m, cp);
      assert m == cp;
    }
    if OBV.MatchesV(r1, str, ov, cp, cp) {
      IterEmptyIntro(r1, k, str, ov, cp);
    }
  }

  /** One-step unfoldings, as lemmas: in statement context the library
      predicate does not unfold on a constructor argument (W5's probe, see
      linden-equiv/endgame/W5-cdn.md §4, surprise 5). */
  lemma QuantUnfold(nul: R.nullability, qid: R.quantid, q: R.counted_quantifier, r1: R.regex,
                    str: string, ov: LOr.OracleView, i: int, j: int)
    requires OBV.MatchesV(R.Re_quant(nul, qid, q, r1), str, ov, i, j)
    ensures exists k: nat :: q.min <= k && (q.max.Some? ==> k <= q.max.value)
                          && OBV.MatchesIterV(r1, k, str, ov, i, j)
  {}

  lemma ConUnfold(r1: R.regex, r2: R.regex, str: string, ov: LOr.OracleView, i: int, j: int)
    requires OBV.MatchesV(R.Re_con(r1, r2), str, ov, i, j)
    ensures exists m: int :: OBV.MatchesV(r1, str, ov, i, m) && OBV.MatchesV(r2, str, ov, m, j)
  {}

  /** A `min > 0` quantifier matches the empty span iff its body does
      (the fifth `Re_quant` arm of `compile_cdnf`, and the CDN-plus arm). */
  lemma QuantEmptyIff(nul: R.nullability, qid: R.quantid, q: R.counted_quantifier, r1: R.regex,
                      str: string, ov: LOr.OracleView, cp: int)
    requires 0 < q.min && (q.max.Some? ==> q.min <= q.max.value)
    ensures OBV.MatchesV(R.Re_quant(nul, qid, q, r1), str, ov, cp, cp)
        <==> OBV.MatchesV(r1, str, ov, cp, cp)
  {
    if OBV.MatchesV(R.Re_quant(nul, qid, q, r1), str, ov, cp, cp) {
      QuantUnfold(nul, qid, q, r1, str, ov, cp, cp);
      var k: nat :| q.min <= k && (q.max.Some? ==> k <= q.max.value)
                 && OBV.MatchesIterV(r1, k, str, ov, cp, cp);
      IterEmptyIff(r1, k, str, ov, cp);
    }
    if OBV.MatchesV(r1, str, ov, cp, cp) {
      var k: nat := q.min;
      IterEmptyIff(r1, k, str, ov, cp);
      assert q.min <= k && (q.max.Some? ==> k <= q.max.value) && OBV.MatchesIterV(r1, k, str, ov, cp, cp);
    }
  }

  /** An empty span of a concatenation splits only at `cp`. */
  lemma ConEmptyIff(r1: R.regex, r2: R.regex, str: string, ov: LOr.OracleView, cp: int)
    ensures OBV.MatchesV(R.Re_con(r1, r2), str, ov, cp, cp)
        <==> OBV.MatchesV(r1, str, ov, cp, cp) && OBV.MatchesV(r2, str, ov, cp, cp)
  {
    if OBV.MatchesV(R.Re_con(r1, r2), str, ov, cp, cp) {
      ConUnfold(r1, r2, str, ov, cp, cp);
      var m: int :| OBV.MatchesV(r1, str, ov, cp, m) && OBV.MatchesV(r2, str, ov, m, cp);
      OBV.MatchesVBounds(r1, str, ov, cp, m);
      OBV.MatchesVBounds(r2, str, ov, m, cp);
      assert m == cp;
    }
    if OBV.MatchesV(r1, str, ov, cp, cp) && OBV.MatchesV(r2, str, ov, cp, cp) {
      assert OBV.MatchesV(r1, str, ov, cp, cp) && OBV.MatchesV(r2, str, ov, cp, cp);
    }
  }

  /** Context-independent nullability really is context-independent. */
  lemma CINullableMatchesEmpty(r: R.regex, str: string, ov: LOr.OracleView, cp: int)
    requires CdnWf(r) && R.nullable(r) == R.CINullable
    ensures OBV.MatchesV(r, str, ov, cp, cp)
    decreases r
  {
    match r
    case Re_empty =>
    case Re_alt(r1, r2) =>
      if R.nullable(r1) == R.CINullable { CINullableMatchesEmpty(r1, str, ov, cp); }
      else { CINullableMatchesEmpty(r2, str, ov, cp); }
    case Re_con(r1, r2) =>
      CINullableMatchesEmpty(r1, str, ov, cp);
      CINullableMatchesEmpty(r2, str, ov, cp);
      ConEmptyIff(r1, r2, str, ov, cp);
    case Re_quant(nul, qid, q, r1) =>
      if q.min == 0 {
        var k: nat := 0;
        assert q.min <= k && (q.max.Some? ==> k <= q.max.value) && OBV.MatchesIterV(r1, k, str, ov, cp, cp);
      } else {
        CINullableMatchesEmpty(r1, str, ov, cp);
        QuantEmptyIff(nul, qid, q, r1, str, ov, cp);
      }
    case Re_capture(_, r1) => CINullableMatchesEmpty(r1, str, ov, cp);
  }

  /** Non-nullability means no empty span (the `CdnWf` twin of
      `OBV.NonNullableNoEmptyMatchV`, without its fragment premise). */
  lemma NonNullableNoEmpty(r: R.regex, str: string, ov: LOr.OracleView, cp: int)
    requires CdnWf(r) && R.nullable(r) == R.NonNullable
    ensures !OBV.MatchesV(r, str, ov, cp, cp)
    decreases r
  {
    match r
    case Re_character(_) =>
    case Re_alt(r1, r2) =>
      NonNullableNoEmpty(r1, str, ov, cp);
      NonNullableNoEmpty(r2, str, ov, cp);
    case Re_con(r1, r2) =>
      ConEmptyIff(r1, r2, str, ov, cp);
      if R.nullable(r1) == R.NonNullable { NonNullableNoEmpty(r1, str, ov, cp); }
      else { NonNullableNoEmpty(r2, str, ov, cp); }
    case Re_quant(nul, qid, q, r1) =>
      NonNullableNoEmpty(r1, str, ov, cp);
      QuantEmptyIff(nul, qid, q, r1, str, ov, cp);
    case Re_capture(_, r1) => NonNullableNoEmpty(r1, str, ov, cp);
  }

  // ===========================================================================
  // Task 1a: the single-formula theorem
  // ===========================================================================

  lemma CdnfSound(r: R.regex, str: string, ov: LOr.OracleView, cp: int,
                  t: C.cdn_table, ctx: LAnc.char_context, dir: LAnc.direction)
    requires CdnWf(r)
    requires ctx == AI.cp_context(cp, str, dir)
    requires TableOkLocal(r, t, str, ov, cp)
    ensures C.interpret_cdn_v(C.compile_cdnf(r), cp, ov, t, ctx, dir)
        <==> OBV.MatchesV(r, str, ov, cp, cp)
    decreases r
  {
    match r
    case Re_empty =>
    case Re_character(_) =>
    case Re_alt(r1, r2) =>
      CdnfSound(r1, str, ov, cp, t, ctx, dir);
      CdnfSound(r2, str, ov, cp, t, ctx, dir);
    case Re_con(r1, r2) =>
      CdnfSound(r1, str, ov, cp, t, ctx, dir);
      CdnfSound(r2, str, ov, cp, t, ctx, dir);
      ConEmptyIff(r1, r2, str, ov, cp);
    case Re_quant(nul, qid, q, r1) =>
      if q.min == 0 {
        var k: nat := 0;
        assert q.min <= k && (q.max.Some? ==> k <= q.max.value) && OBV.MatchesIterV(r1, k, str, ov, cp, cp);
      } else if nul == R.NonNullable {
        NonNullableNoEmpty(r, str, ov, cp);
      } else if nul == R.CINullable {
        CINullableMatchesEmpty(r, str, ov, cp);
      } else if q.max == None && q.greedy && nul == R.CDNullable {
        // the inner CDN plus is read from the table
        assert EligibleCdnPlus(nul, q);
        QuantEmptyIff(nul, qid, q, r1, str, ov, cp);
      } else {
        // fifth arm: min > 0, bounded or lazy, CDN body
        CdnfSound(r1, str, ov, cp, t, ctx, dir);
        QuantEmptyIff(nul, qid, q, r1, str, ov, cp);
      }
    case Re_capture(_, r1) => CdnfSound(r1, str, ov, cp, t, ctx, dir);
    case Re_lookaround(lid, la, r1) =>
    case Re_anchor(a) => AnchorDirInvariant(a, str, cp, dir);
  }

  // ===========================================================================
  // Task 1b: the table theorem
  // ===========================================================================

  /** Every quantifier id of `r` (looks included). */
  ghost function QIds(r: R.regex): set<int>
    decreases r
  {
    match r
    case Re_alt(r1, r2) => QIds(r1) + QIds(r2)
    case Re_con(r1, r2) => QIds(r1) + QIds(r2)
    case Re_quant(_, qid, _, r1) => {qid} + QIds(r1)
    case Re_capture(_, r1) => QIds(r1)
    case Re_lookaround(_, _, r1) => QIds(r1)
    case _ => {}
  }

  /** Quantifier ids are pairwise distinct (the `int` twin of `PIV.QuantUnique`,
      which lives in pike-inv-re, not a dependency of this leaf). */
  ghost predicate QUnique(r: R.regex)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => QUnique(r1) && QUnique(r2) && QIds(r1) !! QIds(r2)
    case Re_con(r1, r2) => QUnique(r1) && QUnique(r2) && QIds(r1) !! QIds(r2)
    case Re_quant(_, qid, _, r1) => qid !in QIds(r1) && QUnique(r1)
    case Re_capture(_, r1) => QUnique(r1)
    case Re_lookaround(_, _, r1) => QUnique(r1)
    case _ => true
  }

  /** The eligible CDN plus ids of `r` (looks included): exactly the ids
      `compile_cdns_rec` lists. */
  ghost function CdnQIds(r: R.regex): set<int>
    decreases r
  {
    match r
    case Re_alt(r1, r2) => CdnQIds(r1) + CdnQIds(r2)
    case Re_con(r1, r2) => CdnQIds(r1) + CdnQIds(r2)
    case Re_quant(nul, qid, q, r1) => (if EligibleCdnPlus(nul, q) then {qid} else {}) + CdnQIds(r1)
    case Re_capture(_, r1) => CdnQIds(r1)
    case Re_lookaround(_, _, r1) => CdnQIds(r1)
    case _ => {}
  }

  lemma CdnQIdsSub(r: R.regex)
    ensures CdnQIds(r) <= QIds(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => CdnQIdsSub(r1); CdnQIdsSub(r2);
    case Re_con(r1, r2) => CdnQIdsSub(r1); CdnQIdsSub(r2);
    case Re_quant(_, _, _, r1) => CdnQIdsSub(r1);
    case Re_capture(_, r1) => CdnQIdsSub(r1);
    case Re_lookaround(_, _, r1) => CdnQIdsSub(r1);
    case _ =>
  }

  /** `compile_cdns_rec` prepends its own list to the accumulator. */
  lemma CompileCdnsRecAppend(r: R.regex, c: C.cdns)
    ensures C.compile_cdns_rec(r, c) == C.compile_cdns_rec(r, []) + c
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      CompileCdnsRecAppend(r1, c);
      CompileCdnsRecAppend(r2, C.compile_cdns_rec(r1, c));
      CompileCdnsRecAppend(r2, C.compile_cdns_rec(r1, []));
    case Re_con(r1, r2) =>
      CompileCdnsRecAppend(r1, c);
      CompileCdnsRecAppend(r2, C.compile_cdns_rec(r1, c));
      CompileCdnsRecAppend(r2, C.compile_cdns_rec(r1, []));
    case Re_quant(nul, qid, q, r1) =>
      if nul == R.CDNullable && q.min > 0 && q.max == None && q.greedy {
        CompileCdnsRecAppend(r1, [(qid, C.compile_cdnf(r1))] + c);
        CompileCdnsRecAppend(r1, [(qid, C.compile_cdnf(r1))]);
      } else {
        CompileCdnsRecAppend(r1, c);
      }
    case Re_capture(_, r1) => CompileCdnsRecAppend(r1, c);
    case Re_lookaround(_, _, r1) => CompileCdnsRecAppend(r1, c);
    case _ =>
  }

  /** `build_cdn_rec_v` over a concatenated list is a sequential composition. */
  lemma BuildAppend(a: C.cdns, b: C.cdns, cp: int, ov: LOr.OracleView, ctx: LAnc.char_context,
                    dir: LAnc.direction, t: C.cdn_table)
    ensures C.build_cdn_rec_v(a + b, cp, ov, ctx, dir, t)
         == C.build_cdn_rec_v(b, cp, ov, ctx, dir, C.build_cdn_rec_v(a, cp, ov, ctx, dir, t))
    decreases |a|
  {
    if |a| == 0 {
      assert a + b == b;
    } else {
      assert (a + b)[0] == a[0];
      assert (a + b)[1..] == a[1..] + b;
      var eval := C.interpret_cdn_v(a[0].1, cp, ov, t, ctx, dir);
      var t' := if eval then C.cdn_set_true(t, a[0].0) else t;
      BuildAppend(a[1..], b, cp, ov, ctx, dir, t');
    }
  }

  /** Table entries agree on all of `r`'s quantifier ids ⇒ `TableOkAll` transfers. */
  lemma TableOkAllFrame(r: R.regex, t: C.cdn_table, t': C.cdn_table, str: string, ov: LOr.OracleView, cp: int)
    requires TableOkAll(r, t, str, ov, cp)
    requires forall q :: q in QIds(r) ==> (q in t <==> q in t')
    ensures TableOkAll(r, t', str, ov, cp)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => TableOkAllFrame(r1, t, t', str, ov, cp); TableOkAllFrame(r2, t, t', str, ov, cp);
    case Re_con(r1, r2) => TableOkAllFrame(r1, t, t', str, ov, cp); TableOkAllFrame(r2, t, t', str, ov, cp);
    case Re_quant(_, _, _, r1) => TableOkAllFrame(r1, t, t', str, ov, cp);
    case Re_capture(_, r1) => TableOkAllFrame(r1, t, t', str, ov, cp);
    case Re_lookaround(_, _, r1) => TableOkAllFrame(r1, t, t', str, ov, cp);
    case _ =>
  }

  /** The induction: building `r`'s list on a table that holds none of `r`'s
      ids yields a table that is right about every eligible CDN plus of `r`
      and adds only eligible ids of `r`. The `Re_quant` arm is where the list
      order matters: the body's entries are built before the plus's own
      formula is evaluated. */
  lemma BuildRecSound(r: R.regex, str: string, ov: LOr.OracleView, cp: int,
                      ctx: LAnc.char_context, dir: LAnc.direction, t: C.cdn_table)
    requires CdnWf(r) && QUnique(r)
    requires ctx == AI.cp_context(cp, str, dir)
    requires QIds(r) !! t
    ensures var t' := C.build_cdn_rec_v(C.compile_cdns_rec(r, []), cp, ov, ctx, dir, t);
            t <= t' && t' - t <= CdnQIds(r) && TableOkAll(r, t', str, ov, cp)
    decreases CP.rsize(r), 1
  {
    CdnQIdsSub(r);
    match r
    case Re_empty =>
    case Re_character(_) =>
    case Re_anchor(_) =>
    case Re_alt(r1, r2) =>
      BuildRecSoundPair(r1, r2, str, ov, cp, ctx, dir, t);
      assert C.compile_cdns_rec(r, []) == C.compile_cdns_rec(r2, C.compile_cdns_rec(r1, []));
    case Re_con(r1, r2) =>
      BuildRecSoundPair(r1, r2, str, ov, cp, ctx, dir, t);
      assert C.compile_cdns_rec(r, []) == C.compile_cdns_rec(r2, C.compile_cdns_rec(r1, []));
    case Re_capture(_, r1) =>
      BuildRecSound(r1, str, ov, cp, ctx, dir, t);
    case Re_lookaround(_, _, r1) =>
      BuildRecSound(r1, str, ov, cp, ctx, dir, t);
    case Re_quant(nul, qid, q, r1) =>
      CdnQIdsSub(r1);
      if EligibleCdnPlus(nul, q) {
        var f := C.compile_cdnf(r1);
        var l1 := C.compile_cdns_rec(r1, []);
        CompileCdnsRecAppend(r1, [(qid, f)]);
        assert C.compile_cdns_rec(r, []) == C.compile_cdns_rec(r1, [(qid, f)]) by {
          assert [(qid, f)] + [] == [(qid, f)];
        }
        assert C.compile_cdns_rec(r, []) == l1 + [(qid, f)];
        BuildAppend(l1, [(qid, f)], cp, ov, ctx, dir, t);
        BuildRecSound(r1, str, ov, cp, ctx, dir, t);
        var t1 := C.build_cdn_rec_v(l1, cp, ov, ctx, dir, t);
        TableOkAllLocal(r1, t1, str, ov, cp);
        CdnfSound(r1, str, ov, cp, t1, ctx, dir);
        var eval := C.interpret_cdn_v(f, cp, ov, t1, ctx, dir);
        var t2 := if eval then C.cdn_set_true(t1, qid) else t1;
        assert C.build_cdn_rec_v([(qid, f)], cp, ov, ctx, dir, t1)
            == C.build_cdn_rec_v([], cp, ov, ctx, dir, t2);
        assert qid !in t1;
        TableOkAllFrame(r1, t1, t2, str, ov, cp);
        assert C.cdn_get(t2, qid) <==> OBV.MatchesV(r1, str, ov, cp, cp);
      } else {
        BuildRecSound(r1, str, ov, cp, ctx, dir, t);
      }
  }

  /** The `Re_alt`/`Re_con` arm: `r2`'s entries are built on `r1`'s table. */
  lemma BuildRecSoundPair(r1: R.regex, r2: R.regex, str: string, ov: LOr.OracleView, cp: int,
                          ctx: LAnc.char_context, dir: LAnc.direction, t: C.cdn_table)
    requires CdnWf(r1) && QUnique(r1) && CdnWf(r2) && QUnique(r2) && QIds(r1) !! QIds(r2)
    requires ctx == AI.cp_context(cp, str, dir)
    requires (QIds(r1) + QIds(r2)) !! t
    ensures var t' := C.build_cdn_rec_v(C.compile_cdns_rec(r2, C.compile_cdns_rec(r1, [])), cp, ov, ctx, dir, t);
            t <= t' && t' - t <= CdnQIds(r1) + CdnQIds(r2)
            && TableOkAll(r1, t', str, ov, cp) && TableOkAll(r2, t', str, ov, cp)
    decreases 1 + CP.rsize(r1) + CP.rsize(r2), 0
  {
    CdnQIdsSub(r1); CdnQIdsSub(r2);
    var l1 := C.compile_cdns_rec(r1, []);
    var l2 := C.compile_cdns_rec(r2, []);
    CompileCdnsRecAppend(r2, l1);
    BuildAppend(l2, l1, cp, ov, ctx, dir, t);
    BuildRecSound(r2, str, ov, cp, ctx, dir, t);
    var t2 := C.build_cdn_rec_v(l2, cp, ov, ctx, dir, t);
    assert QIds(r1) !! t2;
    BuildRecSound(r1, str, ov, cp, ctx, dir, t2);
    var t3 := C.build_cdn_rec_v(l1, cp, ov, ctx, dir, t2);
    TableOkAllFrame(r2, t2, t3, str, ov, cp);
  }

  /** CdnSound, structural form: the whole table built at `cp` is right about
      every eligible CDN plus of `re` and holds nothing else. */
  lemma CdnSoundAll(re: R.regex, str: string, ov: LOr.OracleView, cp: int,
                    ctx: LAnc.char_context, dir: LAnc.direction)
    requires CdnWf(re) && QUnique(re)
    requires ctx == AI.cp_context(cp, str, dir)
    ensures var tb := C.build_cdn_v(C.compile_cdns(re), cp, ov, ctx, dir);
            tb <= CdnQIds(re) && TableOkAll(re, tb, str, ov, cp)
  {
    BuildRecSound(re, str, ov, cp, ctx, dir, C.init_cdn());
  }

  /** The body of eligible CDN plus `qid` in `re`. */
  ghost function CdnBody(re: R.regex, qid: int): R.regex
    requires qid in CdnQIds(re)
    decreases re
  {
    match re
    case Re_alt(r1, r2) => if qid in CdnQIds(r1) then CdnBody(r1, qid) else CdnBody(r2, qid)
    case Re_con(r1, r2) => if qid in CdnQIds(r1) then CdnBody(r1, qid) else CdnBody(r2, qid)
    case Re_quant(nul, q0, q, r1) =>
      if EligibleCdnPlus(nul, q) && q0 == qid then r1 else CdnBody(r1, qid)
    case Re_capture(_, r1) => CdnBody(r1, qid)
    case Re_lookaround(_, _, r1) => CdnBody(r1, qid)
  }

  lemma TableOkAllAt(re: R.regex, t: C.cdn_table, str: string, ov: LOr.OracleView, cp: int, qid: int)
    requires QUnique(re) && TableOkAll(re, t, str, ov, cp)
    requires qid in CdnQIds(re)
    ensures C.cdn_get(t, qid) <==> OBV.MatchesV(CdnBody(re, qid), str, ov, cp, cp)
    decreases re
  {
    CdnQIdsSub(re);
    match re
    case Re_alt(r1, r2) =>
      CdnQIdsSub(r1); CdnQIdsSub(r2);
      if qid in CdnQIds(r1) { TableOkAllAt(r1, t, str, ov, cp, qid); }
      else { TableOkAllAt(r2, t, str, ov, cp, qid); }
    case Re_con(r1, r2) =>
      CdnQIdsSub(r1); CdnQIdsSub(r2);
      if qid in CdnQIds(r1) { TableOkAllAt(r1, t, str, ov, cp, qid); }
      else { TableOkAllAt(r2, t, str, ov, cp, qid); }
    case Re_quant(nul, q0, q, r1) =>
      CdnQIdsSub(r1);
      if !(EligibleCdnPlus(nul, q) && q0 == qid) { TableOkAllAt(r1, t, str, ov, cp, qid); }
    case Re_capture(_, r1) => TableOkAllAt(r1, t, str, ov, cp, qid);
    case Re_lookaround(_, _, r1) => TableOkAllAt(r1, t, str, ov, cp, qid);
  }

  /** CdnSound, the plan's form:
        cdn_get(build_cdn_v(compile_cdns(re), cp, ov, ctx, dir), qid)
          <==> MatchesV(body_of(qid), str, ov, cp, cp)
      for every eligible CDN plus `qid` of `re`, and `false` for any other id. */
  lemma CdnSound(re: R.regex, str: string, ov: LOr.OracleView, cp: int,
                 ctx: LAnc.char_context, dir: LAnc.direction, qid: int)
    requires CdnWf(re) && QUnique(re)
    requires ctx == AI.cp_context(cp, str, dir)
    ensures qid in CdnQIds(re) ==>
              (C.cdn_get(C.build_cdn_v(C.compile_cdns(re), cp, ov, ctx, dir), qid)
               <==> OBV.MatchesV(CdnBody(re, qid), str, ov, cp, cp))
    ensures qid !in CdnQIds(re) ==> !C.cdn_get(C.build_cdn_v(C.compile_cdns(re), cp, ov, ctx, dir), qid)
  {
    CdnSoundAll(re, str, ov, cp, ctx, dir);
    if qid in CdnQIds(re) {
      TableOkAllAt(re, C.build_cdn_v(C.compile_cdns(re), cp, ov, ctx, dir), str, ov, cp, qid);
    }
  }

  // ===========================================================================
  // Engine-facing corollaries
  // ===========================================================================

  /** The guard of the CDN plus `Re_quant(CDN, qid, q, r1)` sitting anywhere in
      `re`, read off the table the engine builds at a step: it passes iff the
      quantifier's body matches the empty span at `cp`. */
  lemma CheckNullableMeaning(re: R.regex, str: string, ov: LOr.OracleView, cp: int,
                             dir: LAnc.direction, qid: int)
    requires CdnWf(re) && QUnique(re)
    requires qid in CdnQIds(re)
    ensures C.cdn_get(C.build_cdn_v(C.compile_cdns(re), cp, ov, AI.cp_context(cp, str, dir), dir), qid)
        <==> OBV.MatchesV(CdnBody(re, qid), str, ov, cp, cp)
  {
    CdnSound(re, str, ov, cp, AI.cp_context(cp, str, dir), dir, qid);
  }

  /** The oracle-build bytecode of a lookahead runs `reverse_regex(remove_capture(body))`
      backward but reads a table built from `compile_cdns(body)`. At an empty span the
      two regexes agree, so the entry still means "the reversed body is nullable here". */
  lemma EmptySpanReverse(r: R.regex, str: string, ov: LOr.OracleView, cp: int)
    requires CdnWf(r)
    ensures OBV.MatchesV(R.reverse_regex(r), str, ov, cp, cp) <==> OBV.MatchesV(r, str, ov, cp, cp)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => EmptySpanReverse(r1, str, ov, cp); EmptySpanReverse(r2, str, ov, cp);
    case Re_con(r1, r2) =>
      EmptySpanReverse(r1, str, ov, cp); EmptySpanReverse(r2, str, ov, cp);
      ConEmptyIff(r1, r2, str, ov, cp);
      ConEmptyIff(R.reverse_regex(r2), R.reverse_regex(r1), str, ov, cp);
    case Re_quant(nul, qid, q, r1) =>
      EmptySpanReverse(r1, str, ov, cp);
      if q.min == 0 {
        var k: nat := 0;
        assert q.min <= k && (q.max.Some? ==> k <= q.max.value) && OBV.MatchesIterV(r1, k, str, ov, cp, cp);
        assert q.min <= k && (q.max.Some? ==> k <= q.max.value)
            && OBV.MatchesIterV(R.reverse_regex(r1), k, str, ov, cp, cp);
      } else {
        QuantEmptyIff(nul, qid, q, r1, str, ov, cp);
        QuantEmptyIff(nul, qid, q, R.reverse_regex(r1), str, ov, cp);
      }
    case Re_capture(_, r1) => EmptySpanReverse(r1, str, ov, cp);
    case _ =>
  }

  lemma EmptySpanRemoveCapture(r: R.regex, str: string, ov: LOr.OracleView, cp: int)
    requires CdnWf(r)
    ensures OBV.MatchesV(R.remove_capture(r), str, ov, cp, cp) <==> OBV.MatchesV(r, str, ov, cp, cp)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => EmptySpanRemoveCapture(r1, str, ov, cp); EmptySpanRemoveCapture(r2, str, ov, cp);
    case Re_con(r1, r2) =>
      EmptySpanRemoveCapture(r1, str, ov, cp); EmptySpanRemoveCapture(r2, str, ov, cp);
      ConEmptyIff(r1, r2, str, ov, cp);
      ConEmptyIff(R.remove_capture(r1), R.remove_capture(r2), str, ov, cp);
    case Re_quant(nul, qid, q, r1) =>
      EmptySpanRemoveCapture(r1, str, ov, cp);
      if q.min == 0 {
        var k: nat := 0;
        assert q.min <= k && (q.max.Some? ==> k <= q.max.value) && OBV.MatchesIterV(r1, k, str, ov, cp, cp);
        assert q.min <= k && (q.max.Some? ==> k <= q.max.value)
            && OBV.MatchesIterV(R.remove_capture(r1), k, str, ov, cp, cp);
      } else {
        QuantEmptyIff(nul, qid, q, r1, str, ov, cp);
        QuantEmptyIff(nul, qid, q, R.remove_capture(r1), str, ov, cp);
      }
    case Re_capture(_, r1) => EmptySpanRemoveCapture(r1, str, ov, cp);
    case _ =>
  }

  // ===========================================================================
  // Task 2: the §8 falsifier — compile_cdns lists every referenced entry first
  // ===========================================================================

  /** The quantifier ids a formula reads from the table. */
  function Refs(f: C.cdn_formula): set<int>
    decreases f
  {
    match f
    case CDN_and(f1, f2) => Refs(f1) + Refs(f2)
    case CDN_or(f1, f2) => Refs(f1) + Refs(f2)
    case CDN_quant(q) => {q}
    case _ => {}
  }

  /** The ids a list sets. */
  function Ids(l: C.cdns): set<int>
    decreases |l|
  {
    if |l| == 0 then {} else {l[0].0} + Ids(l[1..])
  }

  lemma IdsAppend(a: C.cdns, b: C.cdns)
    ensures Ids(a + b) == Ids(a) + Ids(b)
    decreases |a|
  {
    if |a| == 0 { assert a + b == b; }
    else { assert (a + b)[1..] == a[1..] + b; IdsAppend(a[1..], b); }
  }

  lemma IdsIndex(l: C.cdns, q: int)
    requires q in Ids(l)
    ensures exists j :: 0 <= j < |l| && l[j].0 == q
    decreases |l|
  {
    if l[0].0 != q { IdsIndex(l[1..], q); var j :| 0 <= j < |l[1..]| && l[1..][j].0 == q; assert l[j + 1].0 == q; }
  }

  /** Every `CDN_quant(q)` in entry `i` names an entry `j < i`: the order
      `build_cdn_rec` needs (inner entries set before outer ones read them). */
  ghost predicate RefsEarlier(l: C.cdns) {
    forall i, q | 0 <= i < |l| && q in Refs(l[i].1) :: exists j :: 0 <= j < i && l[j].0 == q
  }

  /** `compile_cdnf` reads only eligible CDN pluses of `r` itself. */
  lemma RefsCompileCdnf(r: R.regex)
    requires CdnWf(r)
    ensures Refs(C.compile_cdnf(r)) <= CdnQIds(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => RefsCompileCdnf(r1); RefsCompileCdnf(r2);
    case Re_con(r1, r2) => RefsCompileCdnf(r1); RefsCompileCdnf(r2);
    case Re_quant(_, _, _, r1) => RefsCompileCdnf(r1);
    case Re_capture(_, r1) => RefsCompileCdnf(r1);
    case _ =>
  }

  lemma IdsCompileCdns(r: R.regex)
    ensures Ids(C.compile_cdns_rec(r, [])) == CdnQIds(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      IdsCompileCdns(r1); IdsCompileCdns(r2);
      CompileCdnsRecAppend(r2, C.compile_cdns_rec(r1, []));
      IdsAppend(C.compile_cdns_rec(r2, []), C.compile_cdns_rec(r1, []));
    case Re_con(r1, r2) =>
      IdsCompileCdns(r1); IdsCompileCdns(r2);
      CompileCdnsRecAppend(r2, C.compile_cdns_rec(r1, []));
      IdsAppend(C.compile_cdns_rec(r2, []), C.compile_cdns_rec(r1, []));
    case Re_quant(nul, qid, q, r1) =>
      IdsCompileCdns(r1);
      if EligibleCdnPlus(nul, q) {
        CompileCdnsRecAppend(r1, [(qid, C.compile_cdnf(r1))]);
        assert C.compile_cdns_rec(r, []) == C.compile_cdns_rec(r1, [(qid, C.compile_cdnf(r1))]) by {
          assert [(qid, C.compile_cdnf(r1))] + [] == [(qid, C.compile_cdnf(r1))];
        }
        IdsAppend(C.compile_cdns_rec(r1, []), [(qid, C.compile_cdnf(r1))]);
        assert Ids([(qid, C.compile_cdnf(r1))]) == {qid};
      }
    case Re_capture(_, r1) => IdsCompileCdns(r1);
    case Re_lookaround(_, _, r1) => IdsCompileCdns(r1);
    case _ =>
  }

  lemma RefsEarlierAppend(a: C.cdns, b: C.cdns)
    requires RefsEarlier(a) && RefsEarlier(b)
    ensures RefsEarlier(a + b)
  {
    var l := a + b;
    forall i, q | 0 <= i < |l| && q in Refs(l[i].1) ensures exists j :: 0 <= j < i && l[j].0 == q {
      if i < |a| {
        assert l[i] == a[i];
        var j :| 0 <= j < i && a[j].0 == q;
        assert l[j] == a[j];
      } else {
        assert l[i] == b[i - |a|];
        var j :| 0 <= j < i - |a| && b[j].0 == q;
        assert l[j + |a|] == b[j];
      }
    }
  }

  /** §8 falsifier, settled for every nesting: inner-first. */
  lemma CompileCdnsInnerFirst(r: R.regex)
    requires CdnWf(r)
    ensures RefsEarlier(C.compile_cdns_rec(r, []))
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      CompileCdnsInnerFirst(r1); CompileCdnsInnerFirst(r2);
      CompileCdnsRecAppend(r2, C.compile_cdns_rec(r1, []));
      RefsEarlierAppend(C.compile_cdns_rec(r2, []), C.compile_cdns_rec(r1, []));
    case Re_con(r1, r2) =>
      CompileCdnsInnerFirst(r1); CompileCdnsInnerFirst(r2);
      CompileCdnsRecAppend(r2, C.compile_cdns_rec(r1, []));
      RefsEarlierAppend(C.compile_cdns_rec(r2, []), C.compile_cdns_rec(r1, []));
    case Re_quant(nul, qid, q, r1) =>
      CompileCdnsInnerFirst(r1);
      if EligibleCdnPlus(nul, q) {
        var l1 := C.compile_cdns_rec(r1, []);
        var f := C.compile_cdnf(r1);
        CompileCdnsRecAppend(r1, [(qid, f)]);
        assert C.compile_cdns_rec(r, []) == C.compile_cdns_rec(r1, [(qid, f)]) by {
          assert [(qid, f)] + [] == [(qid, f)];
        }
        RefsCompileCdnf(r1);
        IdsCompileCdns(r1);
        var l := l1 + [(qid, f)];
        forall i, q2 | 0 <= i < |l| && q2 in Refs(l[i].1) ensures exists j :: 0 <= j < i && l[j].0 == q2 {
          if i < |l1| {
            assert l[i] == l1[i];
            var j :| 0 <= j < i && l1[j].0 == q2;
            assert l[j] == l1[j];
          } else {
            assert l[i] == (qid, f);
            assert q2 in Ids(l1);
            IdsIndex(l1, q2);
            var j :| 0 <= j < |l1| && l1[j].0 == q2;
            assert l[j] == l1[j];
          }
        }
      }
    case Re_capture(_, r1) => CompileCdnsInnerFirst(r1);
    case Re_lookaround(_, _, r1) => CompileCdnsInnerFirst(r1);
    case _ =>
  }

  // ----- concrete instances -----

  const plus1 := R.CountedQuant(1, None, true)

  /** `((\b)+|a)+`, annotated by hand (capture 0 around it, as `annotate` does). */
  const ex1: R.regex :=
    R.Re_capture(0, R.Re_quant(R.CDNullable, 1, plus1,
      R.Re_alt(R.Re_quant(R.CDNullable, 2, plus1, R.Re_anchor(R.WordBoundary)),
               R.Re_character(R.Char('a')))))

  lemma Ex1Annotate()
    ensures R.annotate(R.Raw_quant(R.Plus, R.Raw_alt(R.Raw_quant(R.Plus, R.Raw_anchor(R.WordBoundary)),
                                                     R.Raw_character(R.Char('a'))))) == ex1
  {}

  lemma Ex1()
    ensures C.compile_cdns(ex1) == [(2, C.CDN_anchor(R.WordBoundary)), (1, C.CDN_quant(2))]
  {}

  /** `((\b)+|((^)+)+)+`: CDN pluses nested inside both arms of an alternation,
      one of them two levels deep. */
  const ex2: R.regex :=
    R.Re_quant(R.CDNullable, 1, plus1,
      R.Re_alt(R.Re_quant(R.CDNullable, 2, plus1, R.Re_anchor(R.WordBoundary)),
               R.Re_quant(R.CDNullable, 3, plus1,
                 R.Re_quant(R.CDNullable, 4, plus1, R.Re_anchor(R.BeginInput)))))

  lemma Ex2()
    ensures C.compile_cdns(ex2) ==
      [(4, C.CDN_anchor(R.BeginInput)), (3, C.CDN_quant(4)),
       (2, C.CDN_anchor(R.WordBoundary)), (1, C.CDN_or(C.CDN_quant(2), C.CDN_quant(3)))]
  {}

  /** `(((\b)+){2,3})+`: the fifth `compile_cdnf` arm reads THROUGH a bounded
      quantifier (not listed) to the inner plus. */
  const ex3: R.regex :=
    R.Re_quant(R.CDNullable, 1, plus1,
      R.Re_quant(R.CDNullable, 2, R.CountedQuant(2, Some(3), true),
        R.Re_quant(R.CDNullable, 3, plus1, R.Re_anchor(R.WordBoundary))))

  lemma Ex3()
    ensures C.compile_cdns(ex3) == [(3, C.CDN_anchor(R.WordBoundary)), (1, C.CDN_quant(3))]
  {}

  /** `((?=(\b)+)|a)+`: a CDN plus inside a look body is listed in the OUTER
      list too (evaluated at the outer cp; never read by the outer bytecode). */
  const ex4: R.regex :=
    R.Re_quant(R.CDNullable, 1, plus1,
      R.Re_alt(R.Re_lookaround(1, R.Lookahead, R.Re_quant(R.CDNullable, 2, plus1, R.Re_anchor(R.WordBoundary))),
               R.Re_character(R.Char('a'))))

  lemma Ex4()
    ensures C.compile_cdns(ex4) == [(2, C.CDN_anchor(R.WordBoundary)), (1, C.CDN_look(1))]
  {}

  // ===========================================================================
  // G5b brick: the table reads the view only at cp, only in the columns of the
  // looks the formulas name (all inside the regex). So two views that agree on
  // those columns give the SAME table: the generalization the sweep's
  // `SameModCdn` independence (`AdvanceOvIndepAbove`) needs once look-body build
  // code may hold CheckNullable.
  // ===========================================================================

  function LookRefs(f: C.cdn_formula): set<int>
    decreases f
  {
    match f
    case CDN_and(f1, f2) => LookRefs(f1) + LookRefs(f2)
    case CDN_or(f1, f2) => LookRefs(f1) + LookRefs(f2)
    case CDN_look(l) => {l}
    case CDN_neglook(l) => {l}
    case _ => {}
  }

  /** Every lookaround id of `r`. */
  ghost function LIds(r: R.regex): set<int>
    decreases r
  {
    match r
    case Re_alt(r1, r2) => LIds(r1) + LIds(r2)
    case Re_con(r1, r2) => LIds(r1) + LIds(r2)
    case Re_quant(_, _, _, r1) => LIds(r1)
    case Re_capture(_, r1) => LIds(r1)
    case Re_lookaround(lid, _, r1) => {lid} + LIds(r1)
    case _ => {}
  }

  lemma LookRefsCompileCdnf(r: R.regex)
    ensures LookRefs(C.compile_cdnf(r)) <= LIds(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => LookRefsCompileCdnf(r1); LookRefsCompileCdnf(r2);
    case Re_con(r1, r2) => LookRefsCompileCdnf(r1); LookRefsCompileCdnf(r2);
    case Re_quant(_, _, _, r1) => LookRefsCompileCdnf(r1);
    case Re_capture(_, r1) => LookRefsCompileCdnf(r1);
    case _ =>
  }

  ghost predicate ListLookRefsIn(l: C.cdns, S: set<int>) {
    forall i | 0 <= i < |l| :: LookRefs(l[i].1) <= S
  }

  lemma ListLookRefsAppend(a: C.cdns, b: C.cdns, S: set<int>)
    requires ListLookRefsIn(a, S) && ListLookRefsIn(b, S)
    ensures ListLookRefsIn(a + b, S)
  {
    forall i | 0 <= i < |a + b| ensures LookRefs((a + b)[i].1) <= S {
      if i < |a| { assert (a + b)[i] == a[i]; } else { assert (a + b)[i] == b[i - |a|]; }
    }
  }

  lemma LookRefsCompileCdns(r: R.regex)
    ensures ListLookRefsIn(C.compile_cdns_rec(r, []), LIds(r))
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      LookRefsCompileCdns(r1); LookRefsCompileCdns(r2);
      CompileCdnsRecAppend(r2, C.compile_cdns_rec(r1, []));
      ListLookRefsAppend(C.compile_cdns_rec(r2, []), C.compile_cdns_rec(r1, []), LIds(r));
    case Re_con(r1, r2) =>
      LookRefsCompileCdns(r1); LookRefsCompileCdns(r2);
      CompileCdnsRecAppend(r2, C.compile_cdns_rec(r1, []));
      ListLookRefsAppend(C.compile_cdns_rec(r2, []), C.compile_cdns_rec(r1, []), LIds(r));
    case Re_quant(nul, qid, q, r1) =>
      LookRefsCompileCdns(r1);
      if EligibleCdnPlus(nul, q) {
        var f := C.compile_cdnf(r1);
        CompileCdnsRecAppend(r1, [(qid, f)]);
        assert C.compile_cdns_rec(r, []) == C.compile_cdns_rec(r1, [(qid, f)]) by {
          assert [(qid, f)] + [] == [(qid, f)];
        }
        LookRefsCompileCdnf(r1);
        ListLookRefsAppend(C.compile_cdns_rec(r1, []), [(qid, f)], LIds(r));
      }
    case Re_capture(_, r1) => LookRefsCompileCdns(r1);
    case Re_lookaround(_, _, r1) => LookRefsCompileCdns(r1);
    case _ =>
  }

  lemma InterpretAgree(f: C.cdn_formula, cp: int, ov1: LOr.OracleView, ov2: LOr.OracleView,
                       t: C.cdn_table, ctx: LAnc.char_context, dir: LAnc.direction)
    requires forall l | l in LookRefs(f) :: LOr.view_get_oracle(ov1, cp, l) == LOr.view_get_oracle(ov2, cp, l)
    ensures C.interpret_cdn_v(f, cp, ov1, t, ctx, dir) == C.interpret_cdn_v(f, cp, ov2, t, ctx, dir)
    decreases f
  {
    match f
    case CDN_and(f1, f2) => InterpretAgree(f1, cp, ov1, ov2, t, ctx, dir); InterpretAgree(f2, cp, ov1, ov2, t, ctx, dir);
    case CDN_or(f1, f2) => InterpretAgree(f1, cp, ov1, ov2, t, ctx, dir); InterpretAgree(f2, cp, ov1, ov2, t, ctx, dir);
    case _ =>
  }

  lemma BuildAgree(cs: C.cdns, cp: int, ov1: LOr.OracleView, ov2: LOr.OracleView,
                   ctx: LAnc.char_context, dir: LAnc.direction, t: C.cdn_table, S: set<int>)
    requires ListLookRefsIn(cs, S)
    requires forall l | l in S :: LOr.view_get_oracle(ov1, cp, l) == LOr.view_get_oracle(ov2, cp, l)
    ensures C.build_cdn_rec_v(cs, cp, ov1, ctx, dir, t) == C.build_cdn_rec_v(cs, cp, ov2, ctx, dir, t)
    decreases |cs|
  {
    if |cs| > 0 {
      assert LookRefs(cs[0].1) <= S;
      InterpretAgree(cs[0].1, cp, ov1, ov2, t, ctx, dir);
      var eval := C.interpret_cdn_v(cs[0].1, cp, ov1, t, ctx, dir);
      var t' := if eval then C.cdn_set_true(t, cs[0].0) else t;
      assert ListLookRefsIn(cs[1..], S) by {
        forall i | 0 <= i < |cs[1..]| ensures LookRefs(cs[1..][i].1) <= S { assert cs[1..][i] == cs[i + 1]; }
      }
      BuildAgree(cs[1..], cp, ov1, ov2, ctx, dir, t', S);
    }
  }

  /** The sweep form: views agreeing on every column above `k`, and a body whose
      looks all sit above `k` (`LidsWellNested`), build the same table. */
  lemma CdnTableAgreeAbove(body: R.regex, k: int, cp: int, ov1: LOr.OracleView, ov2: LOr.OracleView,
                           ctx: LAnc.char_context, dir: LAnc.direction)
    requires forall l | l in LIds(body) :: l > k
    requires forall l: int :: l > k ==> LOr.view_get_oracle(ov1, cp, l) == LOr.view_get_oracle(ov2, cp, l)
    ensures C.build_cdn_v(C.compile_cdns(body), cp, ov1, ctx, dir) == C.build_cdn_v(C.compile_cdns(body), cp, ov2, ctx, dir)
  {
    LookRefsCompileCdns(body);
    BuildAgree(C.compile_cdns(body), cp, ov1, ov2, ctx, dir, C.init_cdn(), LIds(body));
  }
}
