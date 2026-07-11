// OCaml-vs-Dafny cross-check.
//
// Reference outputs were captured by running the ORIGINAL OCaml RegElk engine
// (opam `linden` switch, OCaml 4.14.2) via a minimal driver that constructs the
// raw_regex AST directly and calls Interpreter(Map_Regs).full_match — see
// ../oracle_check.ml. These are the RAW capture arrays, INCLUDING the stale
// end-register that the capture-reset filter leaves behind (a group with
// start = -1 but end != -1). Asserting against them pins the Dafny port's
// bit-for-bit fidelity to the OCaml original (all three register engines),
// not merely agreement-up-to-normalization with JS.
//
// The first two cases are the metamorphic counterexample r? != (r|eps) for the
// lazy/nullable r = a*?: OCaml (like JS) gives (?:a*?)? -> [0,1] but
// (?:a*?|) -> [0,0]; the Dafny port must reproduce both exactly.
module OCamlCrossCheck {
  import opened Std.Wrappers
  import opened RegElkRegex
  import AI = ArrayInterp
  import LI = ListInterp
  import MI = MapInterp

  method checkAll(raw: raw_regex, s: string, ocaml: Option<seq<int>>) {
    var a := AI.full_match(raw, s);
    var l := LI.full_match(raw, s);
    var m := MI.full_match(raw, s);
    expect a == ocaml, "Array_Regs engine disagrees with OCaml reference";
    expect l == ocaml, "List_Regs engine disagrees with OCaml reference";
    expect m == ocaml, "Map_Regs engine disagrees with OCaml reference";
  }

  method {:test} ocaml_vs_dafny() {
    // (?:a*?)? on "aa"   -- OCaml: "0 1"   (greedy ? of a lazy star matches one 'a')
    checkAll(Raw_quant(QuestionMark, Raw_quant(LazyStar, raw_char('a'))), "aa", Some([0, 1]));
    // (?:a*?|) on "aa"   -- OCaml: "0 0"   (left lazy-star alternative matches empty)
    checkAll(Raw_alt(Raw_quant(LazyStar, raw_char('a')), Raw_empty), "aa", Some([0, 0]));
    // (a|a*) on "aa"     -- OCaml: "0 1 0 1"
    checkAll(Raw_capture(Raw_alt(raw_char('a'), Raw_quant(Star, raw_char('a')))), "aa",
             Some([0, 1, 0, 1]));
    // ((a)|(b))* on "ab" -- OCaml: "0 2 1 2 -1 1 1 2"  (group 2 reset: start -1, stale end 1)
    checkAll(Raw_quant(Star, Raw_capture(Raw_alt(Raw_capture(raw_char('a')), Raw_capture(raw_char('b'))))),
             "ab", Some([0, 2, 1, 2, -1, 1, 1, 2]));
    print "OCaml-vs-Dafny: all 3 Dafny engines reproduce the OCaml reference outputs exactly\n";
  }
}
