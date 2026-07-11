// Port of compiler.ml
// Compile an annotated regex to bytecode.
// NOTE: `fresh` is a reserved keyword in Dafny (the fresh(...) builtin), so the
// OCaml `fresh` label parameter is named `nextl` here.
module Compiler {
  import opened Std.Wrappers
  import opened Charclasses
  import opened RegElkRegex
  import opened Bytecode
  import opened Cdn

  // * Registers (2 per capture group: start and end)
  function start_reg(c: capture): Register { 2 * c }
  function end_reg(c: capture): Register { 2 * c + 1 }

  // * Compilation data-structure: a tree of instruction lists, flattened later.
  datatype treelist = Leaf(l: seq<instruction>) | Concat(t1: treelist, t2: treelist)

  // left-associative chain of Concats (OCaml `@@`)
  function chain(ts: seq<treelist>): treelist
    requires |ts| >= 1
    decreases |ts|
  {
    if |ts| == 1 then ts[0]
    else Concat(chain(ts[..|ts| - 1]), ts[|ts| - 1])
  }

  function tl_flatten(t: treelist, tail: seq<instruction>): seq<instruction>
    decreases t
  {
    match t
    case Leaf(l) => l + tail
    case Concat(a, b) => tl_flatten(a, tl_flatten(b, tail))
  }

  // * Compilation types
  datatype comp_type = Progress | ReconstructNulled

  // AST node count, used as the termination measure across compile/repeat_*.
  // Re_quant contributes 2 so repeat_min/optional (which re-compile the body)
  // have a strictly smaller measure than the enclosing compile call.
  function rsize(r: regex): nat
    decreases r
  {
    match r
    case Re_empty => 1
    case Re_character(_) => 1
    case Re_anchor(_) => 1
    case Re_alt(a, b) => 1 + rsize(a) + rsize(b)
    case Re_con(a, b) => 1 + rsize(a) + rsize(b)
    case Re_quant(_, _, _, r1) => 2 + rsize(r1)
    case Re_capture(_, r1) => 1 + rsize(r1)
    case Re_lookaround(_, _, r1) => 1 + rsize(r1)
  }

  // Recursively compiles a regex. `nextl` is the next available label.
  // Returns the code and the next fresh label.
  function compile(r: regex, nextl: Label, ctype: comp_type): (treelist, Label)
    decreases rsize(r), 0
  {
    match r
    case Re_empty => (Leaf([]), nextl)
    case Re_character(c) =>
      if ctype == ReconstructNulled then (Leaf([Bytecode.Fail]), nextl + 1)
      else
        (match c
         case Char(ch) => (Leaf([Consume(Single(ch))]), nextl + 1)
         case Dot => (Leaf([Consume(All)]), nextl + 1)
         case Group(g) => (Leaf([Consume(Ranges(group_to_range(g)))]), nextl + 1)
         case Class(cl) => (Leaf([Consume(Ranges(class_to_range(cl)))]), nextl + 1)
         case NegClass(cl) => (Leaf([Consume(Ranges(range_neg(class_to_range(cl))))]), nextl + 1))
    case Re_con(r1, r2) =>
      var (l1, f1) := compile(r1, nextl, ctype);
      var (l2, f2) := compile(r2, f1, ctype);
      (Concat(l1, l2), f2)
    case Re_alt(r1, r2) =>
      var (l1, f1) := compile(r1, nextl + 1, ctype);
      var (l2, f2) := compile(r2, f1 + 1, ctype);
      (chain([Leaf([Fork(nextl + 1, f1 + 1)]), l1, Leaf([Jmp(f2)]), l2]), f2)
    case Re_quant(nul, qid, quant, r1) =>
      if ctype == Progress then
        // particular case: non-nullable +, last repetition is the final loop
        if quant.min > 0 && quant.max == None && nul == NonNullable then
          var (min_code, min_f) := repeat_min(quant.min - 1, qid, r1, nextl, ctype);
          var (body_code, body_f) := compile(r1, min_f + 1, ctype);
          var fork := if quant.greedy then Fork(min_f, body_f + 1)
                      else Fork(body_f + 1, min_f);
          (chain([min_code, Leaf([SetQuantToClock(qid, false)]), body_code, Leaf([fork])]), body_f + 1)
        // particular case: greedy CIN +
        else if quant.min > 0 && quant.max == None && nul == CINullable && quant.greedy then
          var (min_code, min_f) := repeat_min(quant.min - 1, qid, r1, nextl, ctype);
          var (body_code, body_f) := compile(r1, min_f + 3, ctype);
          (chain([min_code,
                  Leaf([Fork(min_f + 1, body_f + 2), SetQuantToClock(qid, false), BeginLoop]),
                  body_code,
                  Leaf([EndLoop, Fork(min_f + 1, body_f + 3), SetQuantToClock(qid, true)])]),
           body_f + 3)
        // particular case: greedy CDN +
        else if quant.min > 0 && quant.max == None && nul == CDNullable && quant.greedy then
          var (min_code, min_f) := repeat_min(quant.min - 1, qid, r1, nextl, ctype);
          var (body_code, body_f) := compile(r1, min_f + 3, ctype);
          (chain([min_code,
                  Leaf([Fork(min_f + 1, body_f + 2), SetQuantToClock(qid, false), BeginLoop]),
                  body_code,
                  Leaf([EndLoop, Fork(min_f + 1, body_f + 4), CheckNullable(qid), SetQuantToClock(qid, true)])]),
           body_f + 4)
        // generic case
        else
          var (min_code, min_f) := repeat_min(quant.min, qid, r1, nextl, ctype);
          (match quant.max
           case None =>
             var (iter_code, iter_f) := compile(r1, min_f + 3, ctype);
             var fork := if quant.greedy then Fork(min_f + 1, iter_f + 2)
                         else Fork(iter_f + 2, min_f + 1);
             (chain([min_code,
                     Leaf([fork, SetQuantToClock(qid, false), BeginLoop]),
                     iter_code,
                     Leaf([EndLoop, Jmp(min_f)])]),
              iter_f + 2)
           case Some(mx) =>
             var (opt_code, opt_f) := repeat_optional(mx - quant.min, qid, r1, min_f, ctype, quant.greedy);
             (Concat(min_code, opt_code), opt_f))
      else // ReconstructNulled: only find the top-priority nullable path
        if quant.min == 0 then (Leaf([]), nextl)
        else if nul == NonNullable then (Leaf([Bytecode.Fail]), nextl + 1)
        else if quant.max == None && nul == CINullable && quant.greedy then
          (Leaf([SetQuantToClock(qid, true)]), nextl + 1)
        else if quant.max == None && nul == CDNullable && quant.greedy then
          (Leaf([CheckNullable(qid), SetQuantToClock(qid, true)]), nextl + 2)
        else
          var (l1, f1) := compile(r1, nextl + 1, ReconstructNulled);
          (Concat(Leaf([SetQuantToClock(qid, false)]), l1), f1)
    case Re_capture(cid, r1) =>
      var (l1, f1) := compile(r1, nextl + 1, ctype);
      (chain([Leaf([SetRegisterToCP(start_reg(cid))]), l1, Leaf([SetRegisterToCP(end_reg(cid))])]), f1 + 1)
    case Re_lookaround(lookid, looktype, r1) =>
      (match looktype
       case Lookahead => (Leaf([CheckOracle(lookid)]), nextl + 1)
       case Lookbehind => (Leaf([CheckOracle(lookid)]), nextl + 1)
       case NegLookahead => (Leaf([NegCheckOracle(lookid)]), nextl + 1)
       case NegLookbehind => (Leaf([NegCheckOracle(lookid)]), nextl + 1))
    case Re_anchor(a) => (Leaf([AnchorAssertion(a)]), nextl + 1)
  }

  // repeats body `min` times inside quantifier qid
  function repeat_min(min: int, qid: quantid, r: regex, nextl: Label, ctype: comp_type): (treelist, Label)
    decreases rsize(r) + 1, min
  {
    if min <= 0 then (Leaf([]), nextl)
    else
      var (body_code, new_f) := compile(r, nextl + 1, ctype);
      var (next_code, next_f) := repeat_min(min - 1, qid, r, new_f, ctype);
      (chain([Leaf([SetQuantToClock(qid, false)]), body_code, next_code]), next_f)
  }

  // repeats the optional max-min repetitions of a bounded quantifier
  function repeat_optional(nb: int, qid: quantid, r: regex, nextl: Label, ctype: comp_type, greedy: bool): (treelist, Label)
    decreases rsize(r) + 1, nb
  {
    if nb <= 0 then (Leaf([]), nextl)
    else
      var (body_code, new_f) := compile(r, nextl + 3, ctype);
      var (next_code, next_f) := repeat_optional(nb - 1, qid, r, new_f + 1, ctype, greedy);
      var fork := if greedy then Fork(nextl + 1, next_f) else Fork(next_f, nextl + 1);
      (chain([Leaf([fork, SetQuantToClock(qid, false), BeginLoop]), body_code, Leaf([EndLoop]), next_code]), next_f)
  }

  // adds an Accept at the end
  function compile_to_bytecode(r: regex): code {
    tl_flatten(compile(r, 0, Progress).0, [Accept])
  }

  // same but with a WriteOracle instead of Accept (l = the lookid being built)
  function compile_to_write(r: regex, l: lookid): code {
    tl_flatten(compile(r, 0, Progress).0, [WriteOracle(l)])
  }

  // bytecode for reconstructing missing groups from nulled + (recurses on nested +)
  function compile_reconstruct_nulled(r: regex): code {
    tl_flatten(compile(r, 0, ReconstructNulled).0, [Accept])
  }

  // * Fully Compiled Regexes (ahead-of-time compilation)
  class CompiledRegex {
    var main_ast: regex
    var main_bc: code
    var main_cdns: cdns
    var look_types: array<lookaround>
    var look_ast: array<regex>
    var look_cdns: array<cdns>
    var look_build_bc: array<code>
    var look_capture_bc: array<code>
    var plus_bc: array<code>

    constructor(ast: regex, bc: code, cdns_: cdns,
                lt: array<lookaround>, la: array<regex>, lc: array<cdns>,
                lb: array<code>, lcap: array<code>, pb: array<code>)
      ensures main_ast == ast && main_bc == bc && main_cdns == cdns_
      ensures look_types == lt && look_ast == la && look_cdns == lc
      ensures look_build_bc == lb && look_capture_bc == lcap && plus_bc == pb
    {
      main_ast := ast; main_bc := bc; main_cdns := cdns_;
      look_types := lt; look_ast := la; look_cdns := lc;
      look_build_bc := lb; look_capture_bc := lcap; plus_bc := pb;
    }
  }

  // the regex used when building the oracle
  function oracle_regex(looktype: lookaround, l: regex): regex {
    match looktype
    case Lookahead => lazy_prefix(reverse_regex(remove_capture(l)))
    case NegLookahead => lazy_prefix(reverse_regex(remove_capture(l)))
    case Lookbehind => lazy_prefix(remove_capture(l))
    case NegLookbehind => lazy_prefix(remove_capture(l))
  }

  // the regex used when reconstructing capture groups
  function capture_regex(looktype: lookaround, l: regex): regex {
    match looktype
    case Lookahead => l
    case Lookbehind => reverse_regex(l)
    case NegLookahead => Re_empty // no capture groups in negative lookarounds
    case NegLookbehind => Re_empty
  }

  // ----- Pure model of the compiled regex (spec-only; mirrors the arrays) -----
  datatype FCompiled = FCompiled(
    f_main_ast: regex, f_main_bc: code, f_main_cdns: cdns,
    f_look_types: seq<lookaround>, f_look_ast: seq<regex>, f_look_cdns: seq<cdns>,
    f_look_build_bc: seq<code>, f_look_capture_bc: seq<code>, f_plus_bc: seq<code>)

  function CrView(c: CompiledRegex): FCompiled
    reads c, c.look_types, c.look_ast, c.look_cdns, c.look_build_bc, c.look_capture_bc, c.plus_bc
  {
    FCompiled(c.main_ast, c.main_bc, c.main_cdns,
              c.look_types[..], c.look_ast[..], c.look_cdns[..],
              c.look_build_bc[..], c.look_capture_bc[..], c.plus_bc[..])
  }

  // bounds-guarded seq update, mirroring the guarded array writes
  function upd<T>(s: seq<T>, i: int, v: T): seq<T> {
    if 0 <= i < |s| then s[i := v] else s
  }

  // mirrors compile_extra_bytecode's sequential array writes
  function FCompileExtra(r: regex, c: FCompiled): FCompiled
    decreases r
  {
    match r
    case Re_empty => c
    case Re_character(_) => c
    case Re_anchor(_) => c
    case Re_capture(_, r1) => FCompileExtra(r1, c)
    case Re_alt(r1, r2) => FCompileExtra(r2, FCompileExtra(r1, c))
    case Re_con(r1, r2) => FCompileExtra(r2, FCompileExtra(r1, c))
    case Re_quant(nul, qid, quant, r1) =>
      var c1 := if quant.min > 0 && quant.max == None && nul != NonNullable && quant.greedy
                then c.(f_plus_bc := upd(c.f_plus_bc, qid, compile_reconstruct_nulled(r1)))
                else c;
      FCompileExtra(r1, c1)
    case Re_lookaround(lid, la, body) =>
      var c1 := c.(f_look_types := upd(c.f_look_types, lid, la));
      var c2 := c1.(f_look_cdns := upd(c1.f_look_cdns, lid, compile_cdns(body)));
      var c3 := c2.(f_look_ast := upd(c2.f_look_ast, lid, body));
      var c4 := c3.(f_look_build_bc := upd(c3.f_look_build_bc, lid, compile_to_write(oracle_regex(la, body), lid)));
      var c5 := c4.(f_look_capture_bc := upd(c4.f_look_capture_bc, lid, compile_to_bytecode(capture_regex(la, body))));
      FCompileExtra(body, c5)
  }

  function FFullCompilation(r: regex): FCompiled {
    var maxlook := max_lookaround(r);
    var maxquant := max_quant(r);
    var nlook := if maxlook + 1 >= 0 then maxlook + 1 else 0;
    var nquant := if maxquant + 1 >= 0 then maxquant + 1 else 0;
    FCompileExtra(r, FCompiled(r, compile_to_bytecode(lazy_prefix(r)), compile_cdns(r),
                               seq(nlook, i => Lookahead), seq(nlook, i => Re_empty),
                               seq(nlook, i => []), seq(nlook, i => []),
                               seq(nlook, i => []), seq(nquant, i => [])))
  }

  // recursively sets the two kinds of bytecode for each lookaround and nullable
  // plus. Table writes are bounds-guarded (memory-safe; in practice every
  // lid <= maxlook and qid <= maxquant so the guards always pass).
  method compile_extra_bytecode(r: regex, c: CompiledRegex)
    // the three code tables are distinct arrays (they are in full_compilation,
    // the only caller); needed so the writes mirror the pure model
    requires c.look_build_bc != c.look_capture_bc && c.look_build_bc != c.plus_bc
          && c.look_capture_bc != c.plus_bc
    modifies c.look_types, c.look_cdns, c.look_ast, c.look_build_bc, c.look_capture_bc, c.plus_bc
    ensures CrView(c) == FCompileExtra(r, old(CrView(c)))
    decreases r
  {
    match r
    case Re_empty =>
    case Re_character(_) =>
    case Re_anchor(_) =>
    case Re_capture(_, r1) => compile_extra_bytecode(r1, c);
    case Re_alt(r1, r2) => compile_extra_bytecode(r1, c); compile_extra_bytecode(r2, c);
    case Re_con(r1, r2) => compile_extra_bytecode(r1, c); compile_extra_bytecode(r2, c);
    case Re_quant(nul, qid, quant, r1) =>
      if quant.min > 0 && quant.max == None && nul != NonNullable && quant.greedy {
        var quant_code := compile_reconstruct_nulled(r1);
        if 0 <= qid < c.plus_bc.Length {
          c.plus_bc[qid] := quant_code;
        }
      }
      compile_extra_bytecode(r1, c);
    case Re_lookaround(lid, la, body) =>
      var build_reg := oracle_regex(la, body);
      var capture_reg := capture_regex(la, body);
      var build_code := compile_to_write(build_reg, lid);
      var capture_code := compile_to_bytecode(capture_reg);
      if 0 <= lid < c.look_types.Length { c.look_types[lid] := la; }
      if 0 <= lid < c.look_cdns.Length { c.look_cdns[lid] := compile_cdns(body); }
      if 0 <= lid < c.look_ast.Length { c.look_ast[lid] := body; }
      if 0 <= lid < c.look_build_bc.Length { c.look_build_bc[lid] := build_code; }
      if 0 <= lid < c.look_capture_bc.Length { c.look_capture_bc[lid] := capture_code; }
      compile_extra_bytecode(body, c);
  }

  method full_compilation(r: regex) returns (c: CompiledRegex)
    ensures fresh(c) && fresh(c.look_types) && fresh(c.look_ast) && fresh(c.look_cdns)
    ensures fresh(c.look_build_bc) && fresh(c.look_capture_bc) && fresh(c.plus_bc)
    ensures CrView(c) == FFullCompilation(r)
  {
    var maxlook := max_lookaround(r);
    var maxquant := max_quant(r);
    var nlook := if maxlook + 1 >= 0 then maxlook + 1 else 0;
    var nquant := if maxquant + 1 >= 0 then maxquant + 1 else 0;
    // explicit defaults (observationally identical to the previous auto-init:
    // the slots for id 0 are never read; OCaml's Array.make also requires an
    // explicit default). Makes the contents available to specifications.
    var looktypes := new lookaround[nlook](i => Lookahead);
    var lookcdns := new cdns[nlook](i => []);
    var lookast := new regex[nlook](i => Re_empty);
    var build_look := new code[nlook](i => []);
    var capture_look := new code[nlook](i => []);
    var plus_code := new code[nquant](i => []);
    var main_code := compile_to_bytecode(lazy_prefix(r));
    var main_cdns := compile_cdns(r);
    c := new CompiledRegex(r, main_code, main_cdns, looktypes, lookast, lookcdns,
                           build_look, capture_look, plus_code);
    assert looktypes[..] == seq(nlook, i => Lookahead);
    assert lookast[..] == seq(nlook, i => Re_empty);
    assert lookcdns[..] == seq(nlook, i => []);
    assert build_look[..] == seq(nlook, i => []);
    assert capture_look[..] == seq(nlook, i => []);
    assert plus_code[..] == seq(nquant, i => []);
    compile_extra_bytecode(r, c); // compile lookarounds, CIN & CDN
  }
}
