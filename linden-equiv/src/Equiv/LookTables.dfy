// Lookaround campaign (L1): per-lid table adherence for FCompileExtra.
//
// The main bytecode carries only CheckOracle(lid)/NegCheckOracle(lid); the
// lookaround's flavour, body, build bytecode (ends in WriteOracle(lid)) and
// capture bytecode live in FCompiled's five per-lid tables, filled by a fold
// (FCompileExtra) whose writes are bounds-guarded. This file gives the
// vocabulary that pins those tables against the MAIN ast's lid numbering:
//
//   LookIds/LookUnique   — the lid analogues of PikeInvRE's CapIds/CapUnique
//                          (annotate numbers lids by a monotonic counter,
//                          outer-before-inner: AnnotateLookUnique);
//   LookEntryOk          — one lid's row across the five tables holds exactly
//                          FCompileExtra's data for that lookaround;
//   LookTablesOk         — every lookaround subterm's row is correct;
//   FFullCompilationLookOk — the whole-pipeline corollary the oracle
//                          correctness theorem will consume.
//
// The fold's clobbering is tamed by LookUnique: disjoint sibling lid sets and
// lid-not-in-body mean each row is written once and framed thereafter.
include "RegElkImports.dfy"

/** Lookaround-table adherence: `FCompileExtra` fills the five per-lid tables
    exactly as the MAIN ast's lid numbering dictates. The lid analogue of the
    `CapUnique`/`QuantUnique` vocabulary, plus the fold-adherence theorem. */
module LindenElkLookTables {
  import opened Std.Wrappers
  import R = RegElkRegex
  import RB = Bytecode
  import CD = Cdn
  import CP = Compiler

  // ===========================================================================
  // Lid sets and uniqueness (the lid analogues of CapIds / CapUnique)
  // ===========================================================================

  /** The set of (non-negative) lookaround ids occurring in `r`. */
  ghost function LookIds(r: R.regex): set<nat>
    decreases r
  {
    match r
    case Re_empty => {}
    case Re_character(_) => {}
    case Re_anchor(_) => {}
    case Re_alt(r1, r2) => LookIds(r1) + LookIds(r2)
    case Re_con(r1, r2) => LookIds(r1) + LookIds(r2)
    case Re_quant(_, _, _, r1) => LookIds(r1)
    case Re_capture(_, r1) => LookIds(r1)
    case Re_lookaround(lid, _, r1) =>
      (if lid >= 0 then {lid as nat} else {}) + LookIds(r1)
  }

  /** Every lookaround id in `r` is non-negative and occurs exactly once —
      what `annotate`'s monotonic lid counter guarantees. */
  ghost predicate LookUnique(r: R.regex)
    decreases r
  {
    match r
    case Re_empty => true
    case Re_character(_) => true
    case Re_anchor(_) => true
    case Re_alt(r1, r2) => LookUnique(r1) && LookUnique(r2) && LookIds(r1) * LookIds(r2) == {}
    case Re_con(r1, r2) => LookUnique(r1) && LookUnique(r2) && LookIds(r1) * LookIds(r2) == {}
    case Re_quant(_, _, _, r1) => LookUnique(r1)
    case Re_capture(_, r1) => LookUnique(r1)
    case Re_lookaround(lid, _, r1) => lid >= 0 && (lid as nat) !in LookIds(r1) && LookUnique(r1)
  }

  /** `annotate_regex` assigns lookaround ids by a monotonic counter
      (outer-before-inner: the enclosing lookaround takes the CURRENT `l`, its
      body starts at `l + 1`), so lids are unique and lie in `[l, l')` — the
      lid analogue of `AnnotateCapUnique`. */
  lemma AnnotateLookUnique(ra: R.raw_regex, c: int, l: int, q: int)
    requires l >= 0
    ensures var res := R.annotate_regex(ra, c, l, q);
      l <= res.2 && LookUnique(res.0)
      && (forall x: nat :: x in LookIds(res.0) ==> l <= x < res.2)
    decreases ra
  {
    match ra
    case Raw_empty => case Raw_character(_) => case Raw_anchor(_) =>
    case Raw_alt(r1, r2) =>
      var (ar1, c1, l1, q1) := R.annotate_regex(r1, c, l, q);
      AnnotateLookUnique(r1, c, l, q);
      AnnotateLookUnique(r2, c1, l1, q1);
    case Raw_con(r1, r2) =>
      var (ar1, c1, l1, q1) := R.annotate_regex(r1, c, l, q);
      AnnotateLookUnique(r1, c, l, q);
      AnnotateLookUnique(r2, c1, l1, q1);
    case Raw_quant(quant, r1) => AnnotateLookUnique(r1, c, l, q + 1);
    case Raw_count(quant, r1) => AnnotateLookUnique(r1, c, l, q + 1);
    case Raw_capture(r1) => AnnotateLookUnique(r1, c + 1, l, q);
    case Raw_lookaround(look, r1) => AnnotateLookUnique(r1, c, l + 1, q);
  }

  /** What actually gets compiled — `lazy_prefix(annotate(raw))` — has unique
      look ids, all at least `1`, and the lazy prefix contributes none of them.
      The lid analogue of `PIV.SpecRegexQuantUnique`. */
  lemma SpecRegexLookUnique(raw: R.raw_regex)
    ensures LookUnique(R.annotate(raw))
    ensures LookUnique(R.lazy_prefix(R.annotate(raw)))
    ensures LookIds(R.lazy_prefix(R.annotate(raw))) == LookIds(R.annotate(raw))
    ensures forall x: nat :: x in LookIds(R.annotate(raw)) ==> 1 <= x
  {
    AnnotateLookUnique(R.Raw_capture(raw), 0, 1, 1);
    var ast := R.annotate(raw);
    var pre := R.Re_quant(R.NonNullable, 0, R.CountedQuant(0, None, false),
                          R.Re_character(R.Dot));
    assert R.lazy_prefix(ast) == R.Re_con(pre, ast);
    assert LookIds(pre) == {};
  }

  /** Every lid in `r` is bounded by `max_lookaround(r)` — so the
      `FFullCompilation` tables (length `max_lookaround(r) + 1`) have room for
      every row. */
  lemma LookIdsLeMax(r: R.regex)
    ensures forall x: nat :: x in LookIds(r) ==> x <= R.max_lookaround(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => LookIdsLeMax(r1); LookIdsLeMax(r2);
    case Re_con(r1, r2) => LookIdsLeMax(r1); LookIdsLeMax(r2);
    case Re_quant(_, _, _, r1) => LookIdsLeMax(r1);
    case Re_capture(_, r1) => LookIdsLeMax(r1);
    case Re_lookaround(_, _, r1) => LookIdsLeMax(r1);
    case _ =>
  }

  // ===========================================================================
  // Table adherence
  // ===========================================================================

  /** Row `lid` of the five per-lookaround tables holds exactly the data
      `FCompileExtra` computes for a `Re_lookaround(lid, la, body)` node. */
  ghost predicate LookEntryOk(fc: CP.FCompiled, lid: int, la: R.lookaround, body: R.regex) {
    0 <= lid < |fc.f_look_types| && 0 <= lid < |fc.f_look_ast|
    && 0 <= lid < |fc.f_look_cdns| && 0 <= lid < |fc.f_look_build_bc|
    && 0 <= lid < |fc.f_look_capture_bc|
    && fc.f_look_types[lid] == la
    && fc.f_look_ast[lid] == body
    && fc.f_look_cdns[lid] == CD.compile_cdns(body)
    && fc.f_look_build_bc[lid] == CP.compile_to_write(CP.oracle_regex(la, body), lid)
    && fc.f_look_capture_bc[lid] == CP.compile_to_bytecode(CP.capture_regex(la, body))
  }

  /** Every lookaround subterm of `r` has a correct row in `fc`'s tables. */
  ghost predicate LookTablesOk(r: R.regex, fc: CP.FCompiled)
    decreases r
  {
    match r
    case Re_empty => true
    case Re_character(_) => true
    case Re_anchor(_) => true
    case Re_alt(r1, r2) => LookTablesOk(r1, fc) && LookTablesOk(r2, fc)
    case Re_con(r1, r2) => LookTablesOk(r1, fc) && LookTablesOk(r2, fc)
    case Re_quant(_, _, _, r1) => LookTablesOk(r1, fc)
    case Re_capture(_, r1) => LookTablesOk(r1, fc)
    case Re_lookaround(lid, la, body) =>
      LookEntryOk(fc, lid, la, body) && LookTablesOk(body, fc)
  }

  /** The five look tables of `a` and `b` have the same lengths. */
  ghost predicate SameLookSizes(a: CP.FCompiled, b: CP.FCompiled) {
    |a.f_look_types| == |b.f_look_types|
    && |a.f_look_ast| == |b.f_look_ast|
    && |a.f_look_cdns| == |b.f_look_cdns|
    && |a.f_look_build_bc| == |b.f_look_build_bc|
    && |a.f_look_capture_bc| == |b.f_look_capture_bc|
  }

  /** The five look tables of `a` and `b` agree at row `i`. */
  ghost predicate AgreeAt(a: CP.FCompiled, b: CP.FCompiled, i: nat) {
    (i < |a.f_look_types| && i < |b.f_look_types| ==> a.f_look_types[i] == b.f_look_types[i])
    && (i < |a.f_look_ast| && i < |b.f_look_ast| ==> a.f_look_ast[i] == b.f_look_ast[i])
    && (i < |a.f_look_cdns| && i < |b.f_look_cdns| ==> a.f_look_cdns[i] == b.f_look_cdns[i])
    && (i < |a.f_look_build_bc| && i < |b.f_look_build_bc| ==> a.f_look_build_bc[i] == b.f_look_build_bc[i])
    && (i < |a.f_look_capture_bc| && i < |b.f_look_capture_bc| ==> a.f_look_capture_bc[i] == b.f_look_capture_bc[i])
  }

  /** `FCompileExtra` preserves the look-table lengths and touches look rows
      only at indices in `LookIds(r)` — the fold's frame. */
  lemma FCompileExtraLookFrame(r: R.regex, c: CP.FCompiled)
    ensures var c' := CP.FCompileExtra(r, c);
      SameLookSizes(c, c')
      && forall i: nat :: i !in LookIds(r) ==> AgreeAt(c, c', i)
    decreases r
  {
    match r
    case Re_empty => case Re_character(_) => case Re_anchor(_) =>
    case Re_alt(r1, r2) =>
      FCompileExtraLookFrame(r1, c);
      FCompileExtraLookFrame(r2, CP.FCompileExtra(r1, c));
    case Re_con(r1, r2) =>
      FCompileExtraLookFrame(r1, c);
      FCompileExtraLookFrame(r2, CP.FCompileExtra(r1, c));
    case Re_quant(nul, qid, quant, r1) =>
      var c1 := if quant.min > 0 && quant.max == None && nul != R.NonNullable && quant.greedy
                then c.(f_plus_bc := CP.upd(c.f_plus_bc, qid, CP.compile_reconstruct_nulled(r1)))
                else c;
      FCompileExtraLookFrame(r1, c1);
    case Re_capture(_, r1) =>
      FCompileExtraLookFrame(r1, c);
    case Re_lookaround(lid, la, body) =>
      var c1 := c.(f_look_types := CP.upd(c.f_look_types, lid, la));
      var c2 := c1.(f_look_cdns := CP.upd(c1.f_look_cdns, lid, CD.compile_cdns(body)));
      var c3 := c2.(f_look_ast := CP.upd(c2.f_look_ast, lid, body));
      var c4 := c3.(f_look_build_bc := CP.upd(c3.f_look_build_bc, lid, CP.compile_to_write(CP.oracle_regex(la, body), lid)));
      var c5 := c4.(f_look_capture_bc := CP.upd(c4.f_look_capture_bc, lid, CP.compile_to_bytecode(CP.capture_regex(la, body))));
      FCompileExtraLookFrame(body, c5);
  }

  /** Adherence only reads the rows at `LookIds(r)`, so it survives any update
      that leaves those rows (and the table lengths) alone. */
  lemma LookTablesOkFrame(r: R.regex, a: CP.FCompiled, b: CP.FCompiled)
    requires LookTablesOk(r, a)
    requires SameLookSizes(a, b)
    requires forall i: nat :: i in LookIds(r) ==> AgreeAt(a, b, i)
    ensures LookTablesOk(r, b)
    decreases r
  {
    match r
    case Re_empty => case Re_character(_) => case Re_anchor(_) =>
    case Re_alt(r1, r2) => LookTablesOkFrame(r1, a, b); LookTablesOkFrame(r2, a, b);
    case Re_con(r1, r2) => LookTablesOkFrame(r1, a, b); LookTablesOkFrame(r2, a, b);
    case Re_quant(_, _, _, r1) => LookTablesOkFrame(r1, a, b);
    case Re_capture(_, r1) => LookTablesOkFrame(r1, a, b);
    case Re_lookaround(lid, la, body) =>
      assert (lid as nat) in LookIds(r);
      LookTablesOkFrame(body, a, b);
  }

  /** The fold-adherence theorem: over a lid-unique regex whose ids all fit
      the tables, `FCompileExtra` produces correct rows for every lookaround
      subterm. Uniqueness tames the fold's clobbering — each row is written
      once (its own node) and framed by every later write. */
  lemma FCompileExtraLookOk(r: R.regex, c: CP.FCompiled)
    requires LookUnique(r)
    requires forall i: nat :: i in LookIds(r) ==>
      i < |c.f_look_types| && i < |c.f_look_ast| && i < |c.f_look_cdns|
      && i < |c.f_look_build_bc| && i < |c.f_look_capture_bc|
    ensures LookTablesOk(r, CP.FCompileExtra(r, c))
    decreases r
  {
    match r
    case Re_empty => case Re_character(_) => case Re_anchor(_) =>
    case Re_alt(r1, r2) =>
      var c1 := CP.FCompileExtra(r1, c);
      assert forall i: nat :: i in LookIds(r1) ==> i in LookIds(r);
      assert forall i: nat :: i in LookIds(r2) ==> i in LookIds(r);
      FCompileExtraLookOk(r1, c);
      FCompileExtraLookFrame(r1, c);
      assert forall i: nat :: i in LookIds(r2) ==>
        i < |c1.f_look_types| && i < |c1.f_look_ast| && i < |c1.f_look_cdns|
        && i < |c1.f_look_build_bc| && i < |c1.f_look_capture_bc|;
      FCompileExtraLookOk(r2, c1);
      FCompileExtraLookFrame(r2, c1);
      // r1's rows are outside LookIds(r2), so r2's fold frames them
      assert forall i: nat :: i in LookIds(r1) ==> i !in LookIds(r2);
      LookTablesOkFrame(r1, c1, CP.FCompileExtra(r2, c1));
    case Re_con(r1, r2) =>
      var c1 := CP.FCompileExtra(r1, c);
      assert forall i: nat :: i in LookIds(r1) ==> i in LookIds(r);
      assert forall i: nat :: i in LookIds(r2) ==> i in LookIds(r);
      FCompileExtraLookOk(r1, c);
      FCompileExtraLookFrame(r1, c);
      assert forall i: nat :: i in LookIds(r2) ==>
        i < |c1.f_look_types| && i < |c1.f_look_ast| && i < |c1.f_look_cdns|
        && i < |c1.f_look_build_bc| && i < |c1.f_look_capture_bc|;
      FCompileExtraLookOk(r2, c1);
      FCompileExtraLookFrame(r2, c1);
      assert forall i: nat :: i in LookIds(r1) ==> i !in LookIds(r2);
      LookTablesOkFrame(r1, c1, CP.FCompileExtra(r2, c1));
    case Re_quant(nul, qid, quant, r1) =>
      var c1 := if quant.min > 0 && quant.max == None && nul != R.NonNullable && quant.greedy
                then c.(f_plus_bc := CP.upd(c.f_plus_bc, qid, CP.compile_reconstruct_nulled(r1)))
                else c;
      assert forall i: nat :: i in LookIds(r1) ==> i in LookIds(r);
      assert SameLookSizes(c, c1);
      FCompileExtraLookOk(r1, c1);
    case Re_capture(_, r1) =>
      assert forall i: nat :: i in LookIds(r1) ==> i in LookIds(r);
      FCompileExtraLookOk(r1, c);
    case Re_lookaround(lid, la, body) =>
      var c1 := c.(f_look_types := CP.upd(c.f_look_types, lid, la));
      var c2 := c1.(f_look_cdns := CP.upd(c1.f_look_cdns, lid, CD.compile_cdns(body)));
      var c3 := c2.(f_look_ast := CP.upd(c2.f_look_ast, lid, body));
      var c4 := c3.(f_look_build_bc := CP.upd(c3.f_look_build_bc, lid, CP.compile_to_write(CP.oracle_regex(la, body), lid)));
      var c5 := c4.(f_look_capture_bc := CP.upd(c4.f_look_capture_bc, lid, CP.compile_to_bytecode(CP.capture_regex(la, body))));
      assert (lid as nat) in LookIds(r);
      assert lid < |c.f_look_types| && lid < |c.f_look_ast| && lid < |c.f_look_cdns|
          && lid < |c.f_look_build_bc| && lid < |c.f_look_capture_bc|;
      assert LookEntryOk(c5, lid, la, body);
      FCompileExtraLookOk(body, c5);
      FCompileExtraLookFrame(body, c5);
      // lid !in LookIds(body) (uniqueness), so the body's fold frames row lid
      assert AgreeAt(c5, CP.FCompileExtra(body, c5), lid as nat);
  }

  /** Whole-pipeline corollary: `FFullCompilation` of a lid-unique regex has
      correct per-lookaround tables — the fact the oracle-correctness theorem
      consumes. */
  lemma FFullCompilationLookOk(r: R.regex)
    requires LookUnique(r)
    ensures LookTablesOk(r, CP.FFullCompilation(r))
  {
    LookIdsLeMax(r);
    var maxlook := R.max_lookaround(r);
    var maxquant := R.max_quant(r);
    var nlook := if maxlook + 1 >= 0 then maxlook + 1 else 0;
    var nquant := if maxquant + 1 >= 0 then maxquant + 1 else 0;
    var seed := CP.FCompiled(r, CP.compile_to_bytecode(R.lazy_prefix(r)), CD.compile_cdns(r),
                             seq(nlook, i => R.Lookahead), seq(nlook, i => R.Re_empty),
                             seq(nlook, i => []), seq(nlook, i => []),
                             seq(nlook, i => []), seq(nquant, i => []));
    assert CP.FFullCompilation(r) == CP.FCompileExtra(r, seed);
    FCompileExtraLookOk(r, seed);
  }
}
