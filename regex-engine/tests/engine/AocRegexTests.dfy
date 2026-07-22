// Ported from hath995/Dafny-AoC-template parser/regex.dfy (`test_ReMatch`),
// rewritten idiomatically for the RegElk engine.
//
// That file is a Thompson-NFA matcher with a verbose regex dialect — it spells
// digits as `(0|1|2|...|9)` and its `ReMatch` matches the *entire* string
// (the NFA is anchored at both ends and must consume all input). Here we:
//   - use idiomatic syntax: `\d` for digits, `\(` `\)` for literal parens;
//   - anchor with `^...$` to reproduce the full-string match semantics;
//   - report captures as substrings (like the source's `captures` seq), which
//     for a defined group g is s[start_g .. end_g], group 0 = whole match.
//
// Expected values were taken from Node's RegExp (matches RegElk). Each case is
// checked across all three register engines.
module AocRegexTests {
  import opened Std.Wrappers
  import opened RegElkRegex
  import AI = ArrayInterp
  import LI = ListInterp
  import MI = MapInterp
  import PA = Parser

  // group defined iff its start register >= 0; end may be stale (RegElk convention)
  function normalize_arr(arr: seq<int>): seq<int> {
    seq(|arr|, j requires 0 <= j < |arr| =>
      if j % 2 == 0 then arr[j] else if arr[j - 1] < 0 then -1 else arr[j])
  }
  function normalize(o: Option<seq<int>>): Option<seq<int>> {
    match o case None => None case Some(a) => Some(normalize_arr(a))
  }

  // substrings of the defined groups (0 = whole match), in order
  function extractCaps(arr: seq<int>, s: string, i: nat): seq<string>
    decreases |arr| - 2 * i
  {
    if 2 * i + 1 >= |arr| then []
    else
      var rest := extractCaps(arr, s, i + 1);
      if arr[2 * i] >= 0 then
        var st := arr[2 * i];
        var en := arr[2 * i + 1];
        var lo := if st <= en then st else en;     // lookbehind groups may reverse
        var hi := if st <= en then en else st;
        (if 0 <= lo <= hi <= |s| then [s[lo..hi]] else []) + rest
      else rest
  }

  // Parse `re`, match `s`, and return (matched?, captured substrings) —
  // mirroring the source's `captures: seq<string>`.
  method matchAndCapture(re: string, s: string) returns (matched: bool, caps: seq<string>)
  {
    var p := PA.parse(re);
    expect p.Some?, "parse failed for /" + re + "/";
    var raw := p.value;
    var a := AI.full_match(raw, s);
    var l := LI.full_match(raw, s);
    var m := MI.full_match(raw, s);
    expect normalize(a) == normalize(l) && normalize(m) == normalize(l),
           "engines disagree on /" + re + "/";
    match l {
      case None => matched := false; caps := [];
      case Some(arr) => matched := true; caps := extractCaps(arr, s, 0);
    }
  }

  method {:test} aoc_ReMatch_tests()
  {
    // "abc" matches "abc", not "abd"
    var m0, c0 := matchAndCapture("^abc$", "abc");
    expect m0 && c0 == ["abc"], "test 1 failed";
    var m1, c1 := matchAndCapture("^abc$", "abd");
    expect !m1, "test 2 failed";

    // a+(b|c)+ : whole + last (b|c) iteration
    var m2, c2 := matchAndCapture("^a+(b|c)+$", "aaaccc");
    expect m2 && c2 == ["aaaccc", "c"], "test 3 failed";

    // a+be*(c|d|f)g
    var m3, c3 := matchAndCapture("^a+be*(c|d|f)g$", "aabeefg");
    expect m3 && c3 == ["aabeefg", "f"], "test 4 failed";

    // two \d+ groups  (source: ((0|1|..|9)+),((0|1|..|9)+))
    var m4, c4 := matchAndCapture("^addxy (\\d+),(\\d+)$", "addxy 12,345");
    expect m4 && c4 == ["addxy 12,345", "12", "345"], "test 5 failed";

    // greedy .+ capture
    var m5, c5 := matchAndCapture("^add(.+)$", "addxy 12,355");
    expect m5 && c5 == ["addxy 12,355", "xy 12,355"], "test 6 failed";

    // literal parens via \( \)
    var m6, c6 := matchAndCapture("^add\\(.+,.+\\)$", "add(12,355)");
    expect m6 && c6 == ["add(12,355)"], "test 7 failed";

    // \((\d+),(\d+)\).+  on an AoC "mul" style line
    var m7, c7 := matchAndCapture(
      "^\\((\\d+),(\\d+)\\).+$",
      "(12,403)%&mul[3,7]!@^do_not_mul(5,5)+mul(32,64]then(mul(11,8)mul(8,5))");
    expect m7 && c7 == ["(12,403)%&mul[3,7]!@^do_not_mul(5,5)+mul(32,64]then(mul(11,8)mul(8,5))", "12", "403"],
           "test 8 failed";

    print "aoc_ReMatch_tests: all cases passed across Array/List/Map\n";
  }
}
