// Ported subset of tc39/test262 test/staging/sm/RegExp (SpiderMonkey staging).
// Originals are mirrored under test262/sm-RegExp/.
//
// Most of those 91 files exercise JavaScript RegExp *object* semantics that
// RegElk does not implement (flags g/i/m/u/y/s, lastIndex, .compile/.replace/
// .split, prototypes/descriptors/getters, unicode, named groups, backreferences).
// RegElk implements only the core matching algorithm (capture groups,
// non-capturing groups, lookarounds, anchors, character classes/\d\w\s,
// greedy/lazy/counted quantifiers, ASCII chars 0..255).
//
// This module ports the matching assertions that fall within that feature set.
// Each case is parsed with our Std.Parsers-based parser and matched by all three
// register engines. Expected capture-span arrays were derived from Node's
// RegExp (with the `d` indices flag), which RegElk replicates. Cases that used
// flags are taken at lastIndex 0 (where the single-match result is flag-independent).
// See test262/README.md for the full list of skipped files and why.
module Test262 {
  import opened Std.Wrappers
  import opened RegElkRegex
  import AI = ArrayInterp
  import LI = ListInterp
  import MI = MapInterp
  import PA = Parser

  // A group is defined iff its START register >= 0 (RegElk convention); the END
  // register may be left stale by the reset filter. Normalize to compare with JS.
  function normalize_arr(arr: seq<int>): seq<int> {
    seq(|arr|, j requires 0 <= j < |arr| =>
      if j % 2 == 0 then arr[j]
      else if arr[j - 1] < 0 then -1 else arr[j])
  }
  function normalize(o: Option<seq<int>>): Option<seq<int>> {
    match o case None => None case Some(a) => Some(normalize_arr(a))
  }

  method check(src: string, pat: string, str: string, expected: Option<seq<int>>)
  {
    var p := PA.parse(pat);
    expect p.Some?, "parse failed for /" + pat + "/ (" + src + ")";
    var a0 := AI.full_match(p.value, str);
    var l0 := LI.full_match(p.value, str);
    var m0 := MI.full_match(p.value, str);
    var a := normalize(a0);
    var l := normalize(l0);
    var m := normalize(m0);
    if a != expected || l != expected || m != expected {
      print src, ": /", pat, "/  got A=", a, " L=", l, " M=", m, " expected ", expected, "\n";
    }
    expect a == expected;
    expect l == expected;
    expect m == expected;
  }

  method {:test} sm_RegExp_tests()
  {
    // regress-yarr-regexp.js : greedy capture + greedy capture-zero
    check("regress-yarr-regexp", "((?:.)+)((?:.)*)", "a", Some([0, 1, 0, 1, 1, 1]));
    check("regress-yarr-regexp", "((?:.)+)((?:.)*)", "ab", Some([0, 2, 0, 2, 2, 2]));
    check("regress-yarr-regexp", "((?:.)+)((?:.)*)", "abc", Some([0, 3, 0, 3, 3, 3]));
    check("regress-yarr-regexp", "((?:)*?)a", "a", Some([0, 1, 0, 0]));
    check("regress-yarr-regexp", "((?:.)*?)a", "a", Some([0, 1, 0, 0]));
    check("regress-yarr-regexp", "a((?:.)*)", "a", Some([0, 1, 1, 1]));
    check("regress-yarr-regexp", "([A-Z])", "fooBar", Some([3, 4, 3, 4]));

    // empty-lookahead.js : /(?=)/.test('test') === true  (empty match at 0)
    check("empty-lookahead", "(?=)", "test", Some([0, 0]));

    // regress-613820-2.js : inner capture reset across quantified alternation
    check("regress-613820-2", "(?:(f)(o)(o)|(b)(a)(r))*", "foobar",
          Some([0, 6, -1, -1, -1, -1, -1, -1, 3, 4, 4, 5, 5, 6]));

    // exec.js : core .exec matching (flag/lastIndex side effects dropped)
    check("exec", "a", "ba", Some([1, 2]));
    check("exec", "abc", "abc-------abc", Some([0, 3]));
    check("exec", "abc()?", "abc-------abc", Some([0, 3, -1, -1]));
    check("exec", "abc", "cdefg", None);
    check("exec", "a(b)c", "00abcd", Some([2, 5, 3, 4]));
    check("exec", "abc", "00abc", Some([2, 5]));

    // match.js : /a/[Symbol.match]("abcAbcABC")[0] === "a"
    check("match", "a", "abcAbcABC", Some([0, 1]));

    // class-null.js : /([\0]+)/ (without the unsupported /u flag) on a NUL char
    check("class-null", "([\\0]+)", [0 as char], Some([0, 1, 0, 1]));
    check("class-null", "([\\0]+)", "0", None);

    print "test262 sm/RegExp: all portable matching cases passed across Array/List/Map\n";
  }
}
