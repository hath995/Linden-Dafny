// Port of (a representative subset of) tests.ml's paper_tests.
// Expected capture arrays were generated from Node's RegExp engine (with the
// `d` indices flag), which RegElk faithfully replicates. Each case is run
// through all three register implementations (Array/List/Map), mirroring the
// way tests.native runs the suite for each REGS module.
//
// Capture array layout: index 2*i / 2*i+1 = start/end of group i; group 0 is
// the whole match; -1 = undefined. None = no match.
module Tests {
  import opened Std.Wrappers
  import opened Charclasses
  import opened RegElkRegex
  import AI = ArrayInterp
  import LI = ListInterp
  import MI = MapInterp
  import PA = Parser

  // RegElk's convention (interpreter.ml get_op/print_slice): a group is defined
  // iff its START register is >= 0; the END register may be left stale by the
  // capture-reset filter and is only read when the start is set. Normalize an
  // output to that convention so it can be compared against JS .exec results
  // (which report [-1,-1] for undefined groups).
  function normalize_arr(arr: seq<int>): seq<int> {
    seq(|arr|, j requires 0 <= j < |arr| =>
      if j % 2 == 0 then arr[j]                          // start register: keep
      else if arr[j - 1] < 0 then -1 else arr[j])        // end: -1 if its start is unset
  }
  function normalize(o: Option<seq<int>>): Option<seq<int>> {
    match o case None => None case Some(a) => Some(normalize_arr(a))
  }

  method check(raw: raw_regex, str: string, expected: Option<seq<int>>)
  {
    var a0 := AI.full_match(raw, str);
    var l0 := LI.full_match(raw, str);
    var m0 := MI.full_match(raw, str);
    var a := normalize(a0);
    var l := normalize(l0);
    var m := normalize(m0);
    if a != expected { print "ARRAY mismatch: ", a, " expected ", expected, "\n"; }
    if l != expected { print "LIST  mismatch: ", l, " expected ", expected, "\n"; }
    if m != expected { print "MAP   mismatch: ", m, " expected ", expected, "\n"; }
    expect a == expected;
    expect l == expected;
    expect m == expected;
  }

  method {:test} paper_tests()
  {
    // (a* )b  on "caabd"
    check(Raw_con(Raw_quant(Star, raw_char('a')), raw_char('b')), "caabd", Some([1, 4]));
    // (a|a* )  on "aa"
    check(Raw_capture(Raw_alt(raw_char('a'), Raw_quant(Star, raw_char('a')))), "aa", Some([0, 1, 0, 1]));
    // (?<=L)1  on "L1.2"
    check(Raw_con(Raw_lookaround(Lookbehind, raw_char('L')), raw_char('1')), "L1.2", Some([1, 2]));
    // (?<=L)1  on "v1.2"  (no match)
    check(Raw_con(Raw_lookaround(Lookbehind, raw_char('L')), raw_char('1')), "v1.2", None);
    // (?<=PLDI)[0-9]{2,4}  on "PLDI2024"
    check(Raw_con(Raw_lookaround(Lookbehind,
                    Raw_con(Raw_con(Raw_con(Raw_character(Char('P')), Raw_character(Char('L'))),
                                    Raw_character(Char('D'))), Raw_character(Char('I')))),
                  Raw_count(CountedQuant(2, Some(4), true), Raw_character(Class([CRange('0', '9')])))),
          "PLDI2024", Some([4, 8]));
    // (a|.)b  on "ab"
    check(Raw_con(Raw_capture(Raw_alt(Raw_character(Char('a')), Raw_character(Dot))), Raw_character(Char('b'))),
          "ab", Some([0, 2, 0, 1]));
    // (a+)*b  on "aaa"  (no match: no 'b')
    check(Raw_con(Raw_quant(Star, Raw_capture(Raw_quant(Plus, Raw_character(Char('a'))))), Raw_character(Char('b'))),
          "aaa", None);
    // (?=(c))  on "c"
    check(Raw_lookaround(Lookahead, Raw_capture(Raw_character(Char('c')))), "c", Some([0, 0, 0, 1]));
    // ((a)|(b))*  on "ab"  (capture reset)
    check(Raw_quant(Star, Raw_capture(Raw_alt(Raw_capture(Raw_character(Char('a'))),
                                              Raw_capture(Raw_character(Char('b')))))),
          "ab", Some([0, 2, 1, 2, -1, -1, 1, 2]));
    // (?:(?:a|)(?:|b))*  on "ab"
    check(Raw_quant(Star, Raw_con(Raw_alt(Raw_character(Char('a')), Raw_empty),
                                  Raw_alt(Raw_empty, Raw_character(Char('b'))))),
          "ab", Some([0, 2]));
    // (?:(a)*|(?:(b)|(c))* )*  on "abc"  (capture reset across alternatives)
    check(Raw_quant(Star, Raw_alt(Raw_quant(Star, Raw_capture(Raw_character(Char('a')))),
                                  Raw_quant(Star, Raw_alt(Raw_capture(Raw_character(Char('b'))),
                                                          Raw_capture(Raw_character(Char('c'))))))),
          "abc", Some([0, 3, -1, -1, -1, -1, 2, 3]));
    // abc(?<=ab(?<=b)c)  on "abc"  (nested lookbehind)
    check(Raw_con(Raw_con(Raw_con(Raw_character(Char('a')), Raw_character(Char('b'))), Raw_character(Char('c'))),
                  Raw_lookaround(Lookbehind,
                    Raw_con(Raw_con(Raw_con(Raw_character(Char('a')), Raw_character(Char('b'))),
                                    Raw_lookaround(Lookbehind, Raw_character(Char('b')))),
                            Raw_character(Char('c'))))),
          "abc", Some([0, 3]));
    // (?:a* )*(?=b)  on "aaaaaaaaaaaaaa"  (no match: lookahead 'b' fails)
    check(Raw_con(Raw_quant(Star, Raw_quant(Star, Raw_character(Char('a')))),
                  Raw_lookaround(Lookahead, Raw_character(Char('b')))),
          "aaaaaaaaaaaaaa", None);

    print "paper_tests: all cases passed across Array/List/Map engines\n";
  }

  // Parse a regex *string*, then match it, validating the Std.Parsers-based
  // parser together with the engine. Expected arrays come from Node's RegExp.
  method check_parse(restr: string, str: string, expected: Option<seq<int>>)
  {
    var past := PA.parse(restr);
    expect past.Some?, "parse failed for /" + restr + "/";
    var r := LI.full_match(past.value, str);
    var n := normalize(r);
    if n != expected { print "PARSE-MATCH mismatch /", restr, "/ on ", str, ": ", n, " expected ", expected, "\n"; }
    expect n == expected;
  }

  method {:test} parser_tests()
  {
    check_parse("a*b", "caabd", Some([1, 4]));
    check_parse("(a|a*)", "aa", Some([0, 1, 0, 1]));
    check_parse("(?<=L)1", "L1.2", Some([1, 2]));
    check_parse("(a|.)b", "ab", Some([0, 2, 0, 1]));
    check_parse("(?=(c))", "c", Some([0, 0, 0, 1]));
    check_parse("((a)|(b))*", "ab", Some([0, 2, 1, 2, -1, -1, 1, 2]));
    check_parse("(?<=PLDI)[0-9]{2,4}", "PLDI2024", Some([4, 8]));
    check_parse("\\d+", "ab123", Some([2, 5]));   // \d+
    check_parse("[a-c]+", "xabcy", Some([1, 4]));
    check_parse("a{2,3}", "aaaa", Some([0, 3]));
    check_parse("(?:ab)+", "ababx", Some([0, 4]));
    check_parse("[^0-9]+", "12ab34", Some([2, 4]));
    print "parser_tests: all parse+match cases passed\n";
  }
}
