// Port of cdn.ml
// CDN (Context-Dependent Nullable) formulas: express when a regex is nullable
// at a given string position, so that context-dependent nullable eager pluses
// can be matched without bytecode duplication.
module Cdn {
  import opened Std.Wrappers
  import opened RegElkRegex
  import opened Oracle
  import opened Bytecode
  import opened Anchors

  // * CDN Table
  // a set of quantifier ids known to be nullable at the current cp
  // (OCaml `unit IntMap.t`).
  type cdn_table = set<int>

  function init_cdn(): cdn_table { {} }
  function cdn_set_true(cdn: cdn_table, qid: quantid): cdn_table { cdn + {qid} }
  function cdn_get(cdn: cdn_table, qid: quantid): bool { qid in cdn }

  // * CDN formulas
  datatype cdn_formula =
    | CDN_true
    | CDN_false
    | CDN_and(f1: cdn_formula, f2: cdn_formula)
    | CDN_or(o1: cdn_formula, o2: cdn_formula)
    | CDN_quant(cqid: quantid)
    | CDN_look(clid: lookid)
    | CDN_neglook(cnlid: lookid)
    | CDN_anchor(canc: anchor)

  // * Evaluating CDN formulas
  function interpret_cdn(f: cdn_formula, cp: int, o: oracle, t: cdn_table,
                         ctx: char_context, dir: direction): bool
    reads o
    decreases f
  {
    match f
    case CDN_true => true
    case CDN_false => false
    case CDN_and(f1, f2) =>
      interpret_cdn(f1, cp, o, t, ctx, dir) && interpret_cdn(f2, cp, o, t, ctx, dir)
    case CDN_or(f1, f2) =>
      interpret_cdn(f1, cp, o, t, ctx, dir) || interpret_cdn(f2, cp, o, t, ctx, dir)
    case CDN_quant(qid) => cdn_get(t, qid)
    case CDN_look(lid) => get_oracle(o, cp, lid)
    case CDN_neglook(lid) => !get_oracle(o, cp, lid)
    case CDN_anchor(a) => is_satisfied(a, ctx, dir)
  }

  // * Compiling to CDN formulas (minimizing as we build)
  function compile_cdnf(r: regex): cdn_formula
    decreases r
  {
    match r
    case Re_empty => CDN_true
    case Re_character(_) => CDN_false
    case Re_alt(r1, r2) =>
      var f1 := compile_cdnf(r1); var f2 := compile_cdnf(r2);
      (match (f1, f2)
       case (CDN_true, _) => CDN_true
       case (_, CDN_true) => CDN_true
       case (CDN_false, _) => f2
       case (_, CDN_false) => f1
       case (_, _) => CDN_or(f1, f2))
    case Re_con(r1, r2) =>
      var f1 := compile_cdnf(r1); var f2 := compile_cdnf(r2);
      (match (f1, f2)
       case (CDN_true, _) => f2
       case (_, CDN_true) => f1
       case (CDN_false, _) => CDN_false
       case (_, CDN_false) => CDN_false
       case (_, _) => CDN_and(f1, f2))
    case Re_quant(nul, qid, quant, r1) =>
      if quant.min == 0 then CDN_true            // can skip repetitions entirely
      else if nul == NonNullable then CDN_false  // min>0 and the body consumes
      else if nul == CINullable then CDN_true    // empty string via min reps
      else if quant.max == None && quant.greedy && nul == CDNullable then CDN_quant(qid)
      else compile_cdnf(r1)
    case Re_capture(cid, r1) => compile_cdnf(r1)
    case Re_lookaround(lid, look, r1) =>
      (match look
       case Lookahead => CDN_look(lid)
       case Lookbehind => CDN_look(lid)
       case NegLookahead => CDN_neglook(lid)
       case NegLookbehind => CDN_neglook(lid))
    case Re_anchor(a) => CDN_anchor(a)
  }

  // * Compiling all CDN formulas of a regex (single AST traversal)
  type cdns = seq<(quantid, cdn_formula)>

  function compile_cdns_rec(r: regex, c: cdns): cdns
    decreases r
  {
    match r
    case Re_empty => c
    case Re_character(_) => c
    case Re_anchor(_) => c
    case Re_alt(r1, r2) => compile_cdns_rec(r2, compile_cdns_rec(r1, c))
    case Re_con(r1, r2) => compile_cdns_rec(r2, compile_cdns_rec(r1, c))
    case Re_lookaround(_, _, r1) => compile_cdns_rec(r1, c)
    case Re_capture(_, r1) => compile_cdns_rec(r1, c)
    case Re_quant(nul, qid, quant, r1) =>
      if nul == CDNullable && quant.min > 0 && quant.max == None && quant.greedy
      then compile_cdns_rec(r1, [(qid, compile_cdnf(r1))] + c)
      else compile_cdns_rec(r1, c)
  }

  function compile_cdns(r: regex): cdns { compile_cdns_rec(r, []) }

  // * Building the CDN Table (done by the interpreter at each step)
  function build_cdn_rec(cs: cdns, cp: int, o: oracle, ctx: char_context,
                         dir: direction, table: cdn_table): cdn_table
    reads o
    decreases |cs|
  {
    if |cs| == 0 then table
    else
      var qid := cs[0].0; var formula := cs[0].1;
      var eval := interpret_cdn(formula, cp, o, table, ctx, dir);
      var table' := if eval then cdn_set_true(table, qid) else table;
      build_cdn_rec(cs[1..], cp, o, ctx, dir, table')
  }

  function build_cdn(cs: cdns, cp: int, o: oracle, ctx: char_context, dir: direction): cdn_table
    reads o
  {
    build_cdn_rec(cs, cp, o, ctx, dir, init_cdn())
  }

  // ----- Pure view-based evaluation (spec-only; used by the functional model
  // of the interpreter, which computes over OracleView) -----

  function interpret_cdn_v(f: cdn_formula, cp: int, ov: OracleView, t: cdn_table,
                           ctx: char_context, dir: direction): bool
    decreases f
  {
    match f
    case CDN_true => true
    case CDN_false => false
    case CDN_and(f1, f2) =>
      interpret_cdn_v(f1, cp, ov, t, ctx, dir) && interpret_cdn_v(f2, cp, ov, t, ctx, dir)
    case CDN_or(f1, f2) =>
      interpret_cdn_v(f1, cp, ov, t, ctx, dir) || interpret_cdn_v(f2, cp, ov, t, ctx, dir)
    case CDN_quant(qid) => cdn_get(t, qid)
    case CDN_look(lid) => view_get_oracle(ov, cp, lid)
    case CDN_neglook(lid) => !view_get_oracle(ov, cp, lid)
    case CDN_anchor(a) => is_satisfied(a, ctx, dir)
  }

  function build_cdn_rec_v(cs: cdns, cp: int, ov: OracleView, ctx: char_context,
                           dir: direction, table: cdn_table): cdn_table
    decreases |cs|
  {
    if |cs| == 0 then table
    else
      var qid := cs[0].0; var formula := cs[0].1;
      var eval := interpret_cdn_v(formula, cp, ov, table, ctx, dir);
      var table' := if eval then cdn_set_true(table, qid) else table;
      build_cdn_rec_v(cs[1..], cp, ov, ctx, dir, table')
  }

  function build_cdn_v(cs: cdns, cp: int, ov: OracleView, ctx: char_context, dir: direction): cdn_table {
    build_cdn_rec_v(cs, cp, ov, ctx, dir, init_cdn())
  }

  lemma InterpretCdnView(f: cdn_formula, cp: int, o: oracle, t: cdn_table,
                         ctx: char_context, dir: direction)
    ensures interpret_cdn(f, cp, o, t, ctx, dir) == interpret_cdn_v(f, cp, ViewOf(o), t, ctx, dir)
    decreases f
  {
    match f
    case CDN_look(lid) => GetOracleView(o, cp, lid);
    case CDN_neglook(lid) => GetOracleView(o, cp, lid);
    case CDN_and(f1, f2) =>
      InterpretCdnView(f1, cp, o, t, ctx, dir);
      InterpretCdnView(f2, cp, o, t, ctx, dir);
    case CDN_or(f1, f2) =>
      InterpretCdnView(f1, cp, o, t, ctx, dir);
      InterpretCdnView(f2, cp, o, t, ctx, dir);
    case _ =>
  }

  lemma BuildCdnRecView(cs: cdns, cp: int, o: oracle, ctx: char_context,
                        dir: direction, table: cdn_table)
    ensures build_cdn_rec(cs, cp, o, ctx, dir, table) == build_cdn_rec_v(cs, cp, ViewOf(o), ctx, dir, table)
    decreases |cs|
  {
    if |cs| == 0 {
    } else {
      InterpretCdnView(cs[0].1, cp, o, table, ctx, dir);
      var eval := interpret_cdn(cs[0].1, cp, o, table, ctx, dir);
      var table' := if eval then cdn_set_true(table, cs[0].0) else table;
      BuildCdnRecView(cs[1..], cp, o, ctx, dir, table');
    }
  }

  lemma BuildCdnView(cs: cdns, cp: int, o: oracle, ctx: char_context, dir: direction)
    ensures build_cdn(cs, cp, o, ctx, dir) == build_cdn_v(cs, cp, ViewOf(o), ctx, dir)
  {
    BuildCdnRecView(cs, cp, o, ctx, dir, init_cdn());
  }
}
