// Property-based tests for the RegElk engine using DafnyCheck
// (junctioned in at DafnyRegElk/DafnyCheck), focused on the JS runtime so we can
// use the REAL JavaScript RegExp engine as a differential oracle.
//
// EXCLUDED from dfyconfig.toml; `{:verify false}` (these tests just run + assert
// via `expect`). Run with:
//   dafny/Dafny.exe test DafnyRegElk/PropertyTests.dfy DafnyRegElk/PropertyTestsFFI.js \
//       --target:js --standard-libraries --allow-warnings --no-verify
// (needs `npm install bignumber.js` in repo root; native extern passed positionally).
//
// All runs are SEEDED (reproducible). A CLASSIFIER is attached to every run and,
// thanks to the DafnyCheck fix, logs its distribution at any verbosity (here Low).
//
// Properties:
//   ORACLE   RegElk match == real JS RegExp match, over random (regex, string)
//            pairs (tuned generator -> many real matches WITH capture groups;
//            tallied + asserted non-zero).
//   WITNESS  for a constructed regex we build a string it MUST match (genMatch),
//            check RegElk matches it AND agrees with JS, then apply a random
//            mutation and check RegElk still agrees with JS (boundary fuzzing).
//   CROSS    the Array / List / Map register engines always agree.
//   STAR     a starred regex always matches (nullability).
//   LITERAL  a literal regex matches its own string (bare string generator —
//            exercises DafnyCheck's early-termination fix).
//   IDENTITY structural identities that hold in any regex semantics:
//            (r|r) == r (whole span), (eps . r) == r (full captures),
//            determinism, and capture-span well-formedness.
//   (Quantifier "laws" like r? == (r|eps) are NOT included: they are false in
//    real regex semantics; the ORACLE covers those constructs vs JS instead.)
include "../../src/Engine/Charclasses.dfy"
include "../../src/Engine/Regex.dfy"
include "../../src/Engine/Bytecode.dfy"
include "../../src/Engine/Anchors.dfy"
include "../../src/Engine/Oracle.dfy"
include "../../src/Engine/Regs.dfy"
include "../../src/Engine/Cdn.dfy"
include "../../src/Engine/Compiler.dfy"
include "../../src/Engine/Interpreter.dfy"

module {:extern "JsRegexOracle"} JsRegexOracle {
  method {:extern} OracleAgrees(pattern: string, input: string, matched: bool, spans: seq<int>)
    returns (agree: bool)
  // Runtime multiplier for every property's numRuns, read from env PBT_SCALE (>=1).
  // Lets us compile the test once and sweep run sizes via `node` without recompiling.
  method {:extern} PbtScale() returns (scale: nat)
}

module {:verify false} PropertyTests {
  import opened Std.Wrappers
  import opened Charclasses
  import opened RegElkRegex
  import AI = ArrayInterp
  import LI = ListInterp
  import MI = MapInterp
  import opened Arbitraries
  import opened DafnyCheck
  import opened RunConfigs
  import opened JsRegexOracle

  // ---------- regex -> JS-compatible pattern string ----------
  function digitChar(d: int): char requires 0 <= d <= 9 { (d + 48) as char }
  function i2s(n: int): string requires n >= 0 decreases n {
    if n <= 9 then [digitChar(n)] else i2s(n / 10) + [digitChar(n % 10)]
  }
  function escLit(c: char): string { if c in "\\^$.|?*+()[]{}" then ['\\', c] else [c] }
  function grpStr(g: char_group): string {
    match g case Digit => "\\d" case NonDigit => "\\D" case Word => "\\w"
    case NonWord => "\\W" case Space => "\\s" case NonSpace => "\\S"
  }
  function classEltStr(e: char_class_elt): string {
    match e case CChar(c) => (if c in "\\]^-" then ['\\', c] else [c])
    case CRange(a, b) => [a] + "-" + [b] case CGroup(g) => grpStr(g)
  }
  function classStr(cl: seq<char_class_elt>): string decreases |cl| {
    if |cl| == 0 then "" else classEltStr(cl[0]) + classStr(cl[1..])
  }
  function quantStr(q: quantifier): string {
    match q case Star => "*" case LazyStar => "*?" case Plus => "+"
    case LazyPlus => "+?" case QuestionMark => "?" case LazyQuestionMark => "??"
  }
  function countStr(cq: counted_quantifier): string {
    "{" + i2s(cq.min) + "," + (if cq.max.Some? then i2s(cq.max.value) else "") + "}"
      + (if cq.greedy then "" else "?")
  }
  function toPattern(r: raw_regex): string decreases r {
    match r
    case Raw_empty => ""
    case Raw_character(c) =>
      (match c case Char(ch) => escLit(ch) case Dot => "." case Group(g) => grpStr(g)
       case Class(cl) => "[" + classStr(cl) + "]" case NegClass(cl) => "[^" + classStr(cl) + "]")
    case Raw_alt(a, b) => "(?:" + toPattern(a) + "|" + toPattern(b) + ")"
    case Raw_con(a, b) => toPattern(a) + toPattern(b)
    case Raw_quant(q, r1) => "(?:" + toPattern(r1) + ")" + quantStr(q)
    case Raw_count(cq, r1) => "(?:" + toPattern(r1) + ")" + countStr(cq)
    case Raw_capture(r1) => "(" + toPattern(r1) + ")"
    case Raw_lookaround(look, r1) =>
      (match look case Lookahead => "(?=" case NegLookahead => "(?!"
       case Lookbehind => "(?<=" case NegLookbehind => "(?<!") + toPattern(r1) + ")"
    case Raw_anchor(a) =>
      (match a case BeginInput => "^" case EndInput => "$"
       case WordBoundary => "\\b" case NonWordBoundary => "\\B")
  }

  // ---------- encode RegElk result for the oracle ----------
  function canon(arr: seq<int>, i: nat): seq<int> decreases |arr| - 2 * i {
    if 2 * i + 1 >= |arr| then []
    else var s := arr[2 * i]; var e := arr[2 * i + 1];
      (if s < 0 then [-1, -1] else if s <= e then [s, e] else [e, s]) + canon(arr, i + 1)
  }
  function encMatched(r: Option<seq<int>>): bool { r.Some? }
  function encSpans(r: Option<seq<int>>): seq<int> { match r case None => [] case Some(a) => canon(a, 0) }
  function hasDefinedCapture(arr: seq<int>, i: nat): bool decreases |arr| - 2 * i {
    if 2 * i + 1 >= |arr| then false
    else (i >= 1 && arr[2 * i] >= 0) || hasDefinedCapture(arr, i + 1)
  }
  function canonOpt(r: Option<seq<int>>): Option<seq<int>> {
    match r case None => None case Some(a) => Some(canon(a, 0))
  }
  function spanOf(o: Option<seq<int>>): Option<(int, int)> {
    match o case None => None case Some(a) => if |a| >= 2 then Some((a[0], a[1])) else None
  }
  function spansInRange(arr: seq<int>, n: int, i: nat): bool decreases |arr| - 2 * i {
    if 2 * i + 1 >= |arr| then true
    else var st := arr[2 * i]; var en := arr[2 * i + 1];
      (st < 0 || (0 <= st <= en <= n)) && spansInRange(arr, n, i + 1)
  }
  function litRegex(s: string): raw_regex decreases |s| {
    if |s| == 0 then Raw_empty else if |s| == 1 then Raw_character(Char(s[0]))
    else Raw_con(Raw_character(Char(s[0])), litRegex(s[1..]))
  }

  // ---------- witness generation: a string the (lookaround/anchor-free) regex matches ----------
  function groupWit(g: char_group): string {
    match g case Digit => "0" case Word => "a" case Space => " "
    case NonDigit => "a" case NonWord => "-" case NonSpace => "a"
  }
  function classWit(cl: seq<char_class_elt>): string {
    if |cl| == 0 then "a"
    else match cl[0] case CChar(ch) => [ch] case CRange(a, b) => [a] case CGroup(g) => groupWit(g)
  }
  // first candidate char that is not an excluded CChar (our NegClass uses only CChars)
  function notCChar(ch: char, cl: seq<char_class_elt>): bool decreases |cl| {
    if |cl| == 0 then true
    else (match cl[0] case CChar(c) => c != ch case _ => true) && notCChar(ch, cl[1..])
  }
  function negClassWit(cl: seq<char_class_elt>): string {
    if notCChar('b', cl) then "b" else if notCChar('c', cl) then "c"
    else if notCChar('x', cl) then "x" else "0"
  }
  function matchChar(c: character): string {
    match c case Char(ch) => [ch] case Dot => "a" case Group(g) => groupWit(g)
    case Class(cl) => classWit(cl) case NegClass(cl) => negClassWit(cl)
  }
  function repeatStr(s: string, n: int): string decreases n {
    if n <= 0 then "" else s + repeatStr(s, n - 1)
  }
  // a string guaranteed to match `r` (for the lookaround/anchor-free matchable grammar)
  function genMatch(r: raw_regex): string decreases r {
    match r
    case Raw_empty => ""
    case Raw_character(c) => matchChar(c)
    case Raw_alt(a, b) => genMatch(a)                 // left witness satisfies the alt
    case Raw_con(a, b) => genMatch(a) + genMatch(b)
    case Raw_quant(q, x) => (match q case Plus => genMatch(x) case LazyPlus => genMatch(x) case _ => "")
    case Raw_count(cq, x) => repeatStr(genMatch(x), cq.min)
    case Raw_capture(x) => genMatch(x)
    case Raw_lookaround(_, _) => ""                   // excluded from matchable grammar
    case Raw_anchor(_) => ""                          // excluded from matchable grammar
  }
  // a small deterministic edit (replace / delete / insert) driven by k
  function mutate(s: string, k: nat): string {
    if |s| == 0 then "a"
    else
      var pos := k % |s|;
      var op := (k / 7) % 3;
      if op == 0 then s[..pos] + ['b'] + s[pos + 1..]
      else if op == 1 then s[..pos] + s[pos + 1..]
      else s[..pos] + ['a'] + s[pos..]
  }

  // ---------- AST feature classification ----------
  function hasCapture(r: raw_regex): bool decreases r {
    match r case Raw_capture(_) => true
    case Raw_alt(a, b) => hasCapture(a) || hasCapture(b) case Raw_con(a, b) => hasCapture(a) || hasCapture(b)
    case Raw_quant(_, x) => hasCapture(x) case Raw_count(_, x) => hasCapture(x)
    case Raw_lookaround(_, x) => hasCapture(x) case _ => false
  }
  function hasLook(r: raw_regex): bool decreases r {
    match r case Raw_lookaround(_, _) => true
    case Raw_alt(a, b) => hasLook(a) || hasLook(b) case Raw_con(a, b) => hasLook(a) || hasLook(b)
    case Raw_quant(_, x) => hasLook(x) case Raw_count(_, x) => hasLook(x)
    case Raw_capture(x) => hasLook(x) case _ => false
  }
  function hasAnchor(r: raw_regex): bool decreases r {
    match r case Raw_anchor(_) => true
    case Raw_alt(a, b) => hasAnchor(a) || hasAnchor(b) case Raw_con(a, b) => hasAnchor(a) || hasAnchor(b)
    case Raw_quant(_, x) => hasAnchor(x) case Raw_count(_, x) => hasAnchor(x)
    case Raw_capture(x) => hasAnchor(x) case Raw_lookaround(_, x) => hasAnchor(x) case _ => false
  }
  function hasQuant(r: raw_regex): bool decreases r {
    match r case Raw_quant(_, _) => true case Raw_count(_, _) => true
    case Raw_alt(a, b) => hasQuant(a) || hasQuant(b) case Raw_con(a, b) => hasQuant(a) || hasQuant(b)
    case Raw_capture(x) => hasQuant(x) case Raw_lookaround(_, x) => hasQuant(x) case _ => false
  }
  function astSize(r: raw_regex): nat decreases r {
    match r case Raw_empty => 1 case Raw_character(_) => 1 case Raw_anchor(_) => 1
    case Raw_alt(a, b) => 1 + astSize(a) + astSize(b) case Raw_con(a, b) => 1 + astSize(a) + astSize(b)
    case Raw_quant(_, x) => 1 + astSize(x) case Raw_count(_, x) => 1 + astSize(x)
    case Raw_capture(x) => 1 + astSize(x) case Raw_lookaround(_, x) => 1 + astSize(x)
  }
  function featTag(r: raw_regex): string {
    if hasCapture(r) then "cap" else if hasLook(r) then "look"
    else if hasAnchor(r) then "anch" else if hasQuant(r) then "quant" else "plain"
  }
  function lenTag(n: int): string {
    if n == 0 then "len0" else if n == 1 then "len1" else if n == 2 then "len2"
    else if n == 3 then "len3" else "len4+"
  }
  function sizeTag(n: int): string {
    if n <= 2 then "sz<=2" else if n <= 5 then "sz3-5" else if n <= 10 then "sz6-10" else "sz11+"
  }
  function classifyPair(p: (raw_regex, string)): string { featTag(p.0) + "/" + lenTag(|p.1|) }
  function classifyRegex(r: raw_regex): string { featTag(r) + "/" + sizeTag(astSize(r)) }

  class Counters {
    var total: nat
    var matched: nat
    var withCaps: nat
    constructor() { total := 0; matched := 0; withCaps := 0; }
  }

  // ===================== properties =====================
  @AssumeCrossModuleTermination
  class OracleAgreement extends MethodUnderTest<(raw_regex, string), string> {
    const c: Counters
    constructor(c: Counters) { this.c := c; }
    ghost predicate Valid() reads this { true }
    method run(input: (raw_regex, string)) returns (result: Result<bool, string>)
      requires Valid() ensures Valid()
    {
      var re := input.0; var s := input.1;
      var rr := LI.full_match(re, s);
      c.total := c.total + 1;
      if rr.Some? { c.matched := c.matched + 1; if hasDefinedCapture(rr.value, 0) { c.withCaps := c.withCaps + 1; } }
      var agree := OracleAgrees(toPattern(re), s, encMatched(rr), encSpans(rr));
      result := Success(agree);
    }
  }

  // build a guaranteed-matching witness, check RegElk matches it AND agrees with
  // JS, then mutate it and re-check RegElk vs JS on the (near-match) result.
  @AssumeCrossModuleTermination
  class WitnessMutation extends MethodUnderTest<(raw_regex, nat), string> {
    const c: Counters
    constructor(c: Counters) { this.c := c; }
    ghost predicate Valid() reads this { true }
    method run(input: (raw_regex, nat)) returns (result: Result<bool, string>)
      requires Valid() ensures Valid()
    {
      var r := input.0; var k := input.1;
      var pat := toPattern(r);
      var wit := genMatch(r);
      var w := LI.full_match(r, wit);
      var aw := OracleAgrees(pat, wit, encMatched(w), encSpans(w));
      var mstr := mutate(wit, k);
      var wm := LI.full_match(r, mstr);
      var am := OracleAgrees(pat, mstr, encMatched(wm), encSpans(wm));
      c.total := c.total + 1;
      if w.Some? { c.matched := c.matched + 1; if hasDefinedCapture(w.value, 0) { c.withCaps := c.withCaps + 1; } }
      result := Success(w.Some? && aw && am);     // witness must match; both must agree with JS
    }
  }

  @AssumeCrossModuleTermination
  class CrossEngineAgreement extends MethodUnderTest<(raw_regex, string), string> {
    constructor() {}
    ghost predicate Valid() reads this { true }
    method run(input: (raw_regex, string)) returns (result: Result<bool, string>)
      requires Valid() ensures Valid()
    {
      var a := AI.full_match(input.0, input.1);
      var l := LI.full_match(input.0, input.1);
      var m := MI.full_match(input.0, input.1);
      result := Success(canonOpt(a) == canonOpt(l) && canonOpt(l) == canonOpt(m));
    }
  }

  @AssumeCrossModuleTermination
  class StarAlwaysMatches extends MethodUnderTest<(raw_regex, string), string> {
    constructor() {}
    ghost predicate Valid() reads this { true }
    method run(input: (raw_regex, string)) returns (result: Result<bool, string>)
      requires Valid() ensures Valid()
    {
      var res := LI.full_match(Raw_quant(Star, input.0), input.1);
      result := Success(res.Some?);
    }
  }

  @AssumeCrossModuleTermination
  class LiteralSelfMatch extends MethodUnderTest<string, string> {
    constructor() {}
    ghost predicate Valid() reads this { true }
    method run(input: string) returns (result: Result<bool, string>)
      requires Valid() ensures Valid()
    {
      var res := LI.full_match(litRegex(input), input);
      match res {
        case None => result := Success(false);
        case Some(arr) => result := Success(|arr| >= 2 && arr[0] == 0 && arr[1] == |input|);
      }
    }
  }

  // (r|r) == r  (whole span) — left alternative is identical to r, tried first
  @AssumeCrossModuleTermination
  class AltIdempotent extends MethodUnderTest<(raw_regex, string), string> {
    constructor() {}
    ghost predicate Valid() reads this { true }
    method run(input: (raw_regex, string)) returns (result: Result<bool, string>)
      requires Valid() ensures Valid()
    {
      var a := LI.full_match(Raw_alt(input.0, input.0), input.1);
      var b := LI.full_match(input.0, input.1);
      result := Success(spanOf(a) == spanOf(b));
    }
  }

  // (eps . r) == r  (full captures) — a leading empty is a genuine no-op
  @AssumeCrossModuleTermination
  class ConEmptyIdentity extends MethodUnderTest<(raw_regex, string), string> {
    constructor() {}
    ghost predicate Valid() reads this { true }
    method run(input: (raw_regex, string)) returns (result: Result<bool, string>)
      requires Valid() ensures Valid()
    {
      var a := LI.full_match(Raw_con(Raw_empty, input.0), input.1);
      var b := LI.full_match(input.0, input.1);
      result := Success(canonOpt(a) == canonOpt(b));
    }
  }

  @AssumeCrossModuleTermination
  class Deterministic extends MethodUnderTest<(raw_regex, string), string> {
    constructor() {}
    ghost predicate Valid() reads this { true }
    method run(input: (raw_regex, string)) returns (result: Result<bool, string>)
      requires Valid() ensures Valid()
    {
      var a := LI.full_match(input.0, input.1);
      var b := LI.full_match(input.0, input.1);
      result := Success(canonOpt(a) == canonOpt(b));
    }
  }

  @AssumeCrossModuleTermination
  class SpansWellFormed extends MethodUnderTest<(raw_regex, string), string> {
    constructor() {}
    ghost predicate Valid() reads this { true }
    method run(input: (raw_regex, string)) returns (result: Result<bool, string>)
      requires Valid() ensures Valid()
    {
      var r0 := LI.full_match(input.0, input.1);
      match r0 {
        case None => result := Success(true);
        case Some(arr) => result := Success(spansInRange(canon(arr, 0), |input.1|, 0));
      }
    }
  }

  // KNOWN NON-IDENTITY (kept as an expect-FAIL regression): r? != (r|eps) for a
  // lazy/nullable r. This is true in JS *and* OCaml (verified), so RegElk must
  // distinguish them; the property is expected to be VIOLATED.
  @AssumeCrossModuleTermination
  class OptEqAltEmpty extends MethodUnderTest<(raw_regex, string), string> {
    constructor() {}
    ghost predicate Valid() reads this { true }
    method run(input: (raw_regex, string)) returns (result: Result<bool, string>)
      requires Valid() ensures Valid()
    {
      var r := input.0; var s := input.1;
      var a := LI.full_match(Raw_quant(QuestionMark, r), s);
      var b := LI.full_match(Raw_alt(r, Raw_empty), s);
      result := Success(spanOf(a) == spanOf(b));   // would only hold if r? == (r|eps)
    }
  }

  // (r . eps) == r  (trailing empty is a no-op) — mirror of ConEmptyIdentity
  @AssumeCrossModuleTermination
  class ConEmptyRight extends MethodUnderTest<(raw_regex, string), string> {
    constructor() {}
    ghost predicate Valid() reads this { true }
    method run(input: (raw_regex, string)) returns (result: Result<bool, string>)
      requires Valid() ensures Valid()
    {
      var a := LI.full_match(Raw_con(input.0, Raw_empty), input.1);
      var b := LI.full_match(input.0, input.1);
      result := Success(canonOpt(a) == canonOpt(b));
    }
  }

  // Begin-anchor semantics: `^r` matches s  <=>  r's leftmost match starts at 0,
  // and when both match their spans agree. Exercises the BeginInput anchor against
  // the unanchored leftmost-match search.
  @AssumeCrossModuleTermination
  class AnchorStart extends MethodUnderTest<(raw_regex, string), string> {
    constructor() {}
    ghost predicate Valid() reads this { true }
    method run(input: (raw_regex, string)) returns (result: Result<bool, string>)
      requires Valid() ensures Valid()
    {
      var r := input.0; var s := input.1;
      var a := LI.full_match(r, s);
      var b := LI.full_match(Raw_con(Raw_anchor(BeginInput), r), s);
      var sa := spanOf(a);
      var startsAt0 := sa.Some? && sa.value.0 == 0;
      var ok := (b.Some? == startsAt0) && (!b.Some? || spanOf(b) == sa);
      result := Success(ok);
    }
  }

  // ECMA quantifier unrolling: r+ ≡ r·r*  and  r+? ≡ r·r*?  (overall span only,
  // since unrolling duplicates r and changes the group count). This stresses the
  // nullable-/greedy-plus machinery against an explicit unrolled form.
  @AssumeCrossModuleTermination
  class PlusUnroll extends MethodUnderTest<(raw_regex, string), string> {
    constructor() {}
    ghost predicate Valid() reads this { true }
    method run(input: (raw_regex, string)) returns (result: Result<bool, string>)
      requires Valid() ensures Valid()
    {
      var r := input.0; var s := input.1;
      var ag := LI.full_match(Raw_quant(Plus, r), s);
      var bg := LI.full_match(Raw_con(r, Raw_quant(Star, r)), s);
      var al := LI.full_match(Raw_quant(LazyPlus, r), s);
      var bl := LI.full_match(Raw_con(r, Raw_quant(LazyStar, r)), s);
      result := Success(spanOf(ag) == spanOf(bg) && spanOf(al) == spanOf(bl));
    }
  }

  // Counted vs simple quantifier compilation equivalence (ECMA defines these
  // syntactically equal):  r{0,1} ≡ r? ,  r{0,} ≡ r* ,  r{1,} ≡ r+  (all greedy).
  // Same inner r, so the FULL capture arrays must agree — cross-checks the
  // counted-quantifier compiler path against the dedicated quantifier path.
  @AssumeCrossModuleTermination
  class CountVsQuant extends MethodUnderTest<(raw_regex, string), string> {
    constructor() {}
    ghost predicate Valid() reads this { true }
    method run(input: (raw_regex, string)) returns (result: Result<bool, string>)
      requires Valid() ensures Valid()
    {
      var r := input.0; var s := input.1;
      var q   := LI.full_match(Raw_count(CountedQuant(0, Some(1), true), r), s);
      var qq  := LI.full_match(Raw_quant(QuestionMark, r), s);
      var st  := LI.full_match(Raw_count(CountedQuant(0, None, true), r), s);
      var stq := LI.full_match(Raw_quant(Star, r), s);
      var pl  := LI.full_match(Raw_count(CountedQuant(1, None, true), r), s);
      var plq := LI.full_match(Raw_quant(Plus, r), s);
      result := Success(canonOpt(q) == canonOpt(qq)
                     && canonOpt(st) == canonOpt(stq)
                     && canonOpt(pl) == canonOpt(plq));
    }
  }

  // (r*)* is always nullable, so it always matches — robustness of nested stars.
  @AssumeCrossModuleTermination
  class StarDouble extends MethodUnderTest<(raw_regex, string), string> {
    constructor() {}
    ghost predicate Valid() reads this { true }
    method run(input: (raw_regex, string)) returns (result: Result<bool, string>)
      requires Valid() ensures Valid()
    {
      var res := LI.full_match(Raw_quant(Star, Raw_quant(Star, input.0)), input.1);
      result := Success(res.Some?);
    }
  }

  // Counted-quantifier bound expansion (ECMA): r{m,n} ≡ m mandatory copies then
  // (n-m) optional copies (greedy). Checked for r{2,3} ≡ r·r·r? and r{1,2} ≡ r·r?
  // (overall span — the explicit form duplicates r so group counts differ). Stresses
  // the {m,n} compiler against a hand-unrolled concatenation.
  @AssumeCrossModuleTermination
  class CountUnroll extends MethodUnderTest<(raw_regex, string), string> {
    constructor() {}
    ghost predicate Valid() reads this { true }
    method run(input: (raw_regex, string)) returns (result: Result<bool, string>)
      requires Valid() ensures Valid()
    {
      var r := input.0; var s := input.1;
      var a23 := LI.full_match(Raw_count(CountedQuant(2, Some(3), true), r), s);
      var b23 := LI.full_match(Raw_con(Raw_con(r, r), Raw_quant(QuestionMark, r)), s);
      var a12 := LI.full_match(Raw_count(CountedQuant(1, Some(2), true), r), s);
      var b12 := LI.full_match(Raw_con(r, Raw_quant(QuestionMark, r)), s);
      result := Success(spanOf(a23) == spanOf(b23) && spanOf(a12) == spanOf(b12));
    }
  }

  // Greedy vs lazy counted quantifier: r{1,3} and r{1,3}? match the same set (same
  // bounds) so they agree on match-existence and leftmost start; greedy consumes at
  // least as much, so its overall end is >= the lazy one's.
  @AssumeCrossModuleTermination
  class CountGreedyLazy extends MethodUnderTest<(raw_regex, string), string> {
    constructor() {}
    ghost predicate Valid() reads this { true }
    method run(input: (raw_regex, string)) returns (result: Result<bool, string>)
      requires Valid() ensures Valid()
    {
      var r := input.0; var s := input.1;
      var g := LI.full_match(Raw_count(CountedQuant(1, Some(3), true), r), s);
      var l := LI.full_match(Raw_count(CountedQuant(1, Some(3), false), r), s);
      var ok := (g.Some? == l.Some?);
      if g.Some? && l.Some? {
        var sg := spanOf(g); var sl := spanOf(l);
        ok := ok && sg.Some? && sl.Some?
                 && sg.value.0 == sl.value.0      // same leftmost start
                 && sg.value.1 >= sl.value.1;     // greedy end >= lazy end
      }
      result := Success(ok);
    }
  }

  // Capturing is transparent to the overall match: wrapping r in a capture group
  // changes neither whether it matches nor the whole-match span, and the added
  // group 1 spans exactly the whole match (group 0).
  @AssumeCrossModuleTermination
  class CaptureTransparent extends MethodUnderTest<(raw_regex, string), string> {
    constructor() {}
    ghost predicate Valid() reads this { true }
    method run(input: (raw_regex, string)) returns (result: Result<bool, string>)
      requires Valid() ensures Valid()
    {
      var r := input.0; var s := input.1;
      var a := LI.full_match(r, s);
      var b := LI.full_match(Raw_capture(r), s);
      var ok := spanOf(a) == spanOf(b);
      if b.Some? && |b.value| >= 4 {
        var arr := b.value;                         // [s0,e0, s1,e1, ...]
        ok := ok && arr[2] == arr[0] && arr[3] == arr[1];   // group 1 == group 0
      }
      result := Success(ok);
    }
  }

  // ---- deliberately-FALSE properties, used only to test SHRINK QUALITY ----
  // "every string has length <= 1": violated by any |s| >= 2. The minimal
  // counterexample is a length-2 string with the regex shrunk to a tiny leaf
  // (the regex is irrelevant to the property, so it should minimise fully).
  @AssumeCrossModuleTermination
  class StrLenLE1 extends MethodUnderTest<(raw_regex, string), string> {
    constructor() {}
    ghost predicate Valid() reads this { true }
    method run(input: (raw_regex, string)) returns (result: Result<bool, string>)
      requires Valid() ensures Valid()
    { result := Success(|input.1| <= 1); }
  }

  // "every regex has astSize <= 1": violated by any composite regex. The minimal
  // counterexample is a size-2 regex with the string shrunk to empty (the string
  // is irrelevant, so it should minimise to "").
  @AssumeCrossModuleTermination
  class AstSizeLE1 extends MethodUnderTest<(raw_regex, string), string> {
    constructor() {}
    ghost predicate Valid() reads this { true }
    method run(input: (raw_regex, string)) returns (result: Result<bool, string>)
      requires Valid() ensures Valid()
    { result := Success(astSize(input.0) <= 1); }
  }

  // ===================== generators =====================
  // full generator (includes anchors & lookarounds), tuned for matches+captures
  method BuildRegexArb() returns (arb: Arbitrary<raw_regex>) {
    var reg := new Registry<raw_regex>("leaf", 3);
    var leaf := Arbitrary<raw_regex>.Of([
      Raw_character(Char('a')), Raw_character(Char('b')), raw_dot, Raw_empty,
      Raw_character(Group(Word)), Raw_character(Group(Digit)), Raw_character(Group(Space)),
      Raw_character(Class([CChar('a'), CChar('b')])), Raw_character(Class([CRange('a', 'c')])),
      Raw_character(NegClass([CChar('a')])), Raw_character(NegClass([CChar('a'), CChar('b')]))]);
    reg.Register("leaf", leaf);
    var a1 := reg.Tie("re"); var a2 := reg.Tie("re");
    var altA := Arbitrary<raw_regex>.Tuple(a1, a2);
    var alt := altA.Map((p: (raw_regex, raw_regex)) => Raw_alt(p.0, p.1)); reg.Register("alt", alt);
    var c1 := reg.Tie("re"); var c2 := reg.Tie("re");
    var conA := Arbitrary<raw_regex>.Tuple(c1, c2);
    var con := conA.Map((p: (raw_regex, raw_regex)) => Raw_con(p.0, p.1)); reg.Register("con", con);
    var qg := Arbitrary<quantifier>.Of([Star, Plus, QuestionMark, LazyStar, LazyPlus, LazyQuestionMark]);
    var qt := reg.Tie("re"); var quantA := Arbitrary<quantifier>.Tuple(qg, qt);
    var quant := quantA.Map((p: (quantifier, raw_regex)) => Raw_quant(p.0, p.1)); reg.Register("quant", quant);
    var capt := reg.Tie("re"); var capture := capt.Map((r: raw_regex) => Raw_capture(r)); reg.Register("capture", capture);
    var ag := Arbitrary<anchor>.Of([BeginInput, EndInput, WordBoundary, NonWordBoundary]);
    var anchor := ag.Map((a: anchor) => Raw_anchor(a)); reg.Register("anchor", anchor);
    var lg := Arbitrary<lookaround>.Of([Lookahead, NegLookahead, Lookbehind, NegLookbehind]);
    var lt := reg.Tie("re"); var lookA := Arbitrary<lookaround>.Tuple(lg, lt);
    var look := lookA.Map((p: (lookaround, raw_regex)) => Raw_lookaround(p.0, p.1)); reg.Register("look", look);
    // varied {m,n}: bounded greedy/lazy, open-ended {0,}/{1,}, exact-ish {2,3}
    var cqg := Arbitrary<counted_quantifier>.Of([
      CountedQuant(0, Some(2), true), CountedQuant(1, Some(2), false), CountedQuant(1, None, true),
      CountedQuant(0, None, true), CountedQuant(2, Some(3), true), CountedQuant(0, Some(1), false)]);
    var cnt := reg.Tie("re"); var cntA := Arbitrary<counted_quantifier>.Tuple(cqg, cnt);
    var count := cntA.Map((p: (counted_quantifier, raw_regex)) => Raw_count(p.0, p.1)); reg.Register("count", count);
    var l1 := reg.Tie("leaf"); var l2 := reg.Tie("leaf"); var l3 := reg.Tie("leaf");
    var o1 := reg.Tie("con"); var o2 := reg.Tie("con");
    var u1 := reg.Tie("quant"); var u2 := reg.Tie("quant");
    var p1 := reg.Tie("capture"); var p2 := reg.Tie("capture");
    var x1 := reg.Tie("alt"); var x2 := reg.Tie("count"); var x3 := reg.Tie("anchor"); var x4 := reg.Tie("look");
    var reArb := Arbitrary<raw_regex>.Mix([l1, l2, l3, o1, o2, u1, u2, p1, p2, x1, x2, x3, x4]);
    reg.Register("re", reArb); arb := reg.Lookup("re");
  }

  // matchable generator: NO anchors / lookarounds, so genMatch reliably builds a
  // matching witness for every produced regex.
  method BuildMatchableRegexArb() returns (arb: Arbitrary<raw_regex>) {
    var reg := new Registry<raw_regex>("leaf", 3);
    var leaf := Arbitrary<raw_regex>.Of([
      Raw_character(Char('a')), Raw_character(Char('b')), raw_dot, Raw_empty,
      Raw_character(Group(Word)), Raw_character(Group(Digit)), Raw_character(Group(Space)),
      Raw_character(Class([CChar('a'), CChar('b')])), Raw_character(Class([CRange('a', 'c')])),
      Raw_character(NegClass([CChar('a')])), Raw_character(NegClass([CChar('a'), CChar('b')]))]);
    reg.Register("leaf", leaf);
    var a1 := reg.Tie("re"); var a2 := reg.Tie("re");
    var altA := Arbitrary<raw_regex>.Tuple(a1, a2);
    var alt := altA.Map((p: (raw_regex, raw_regex)) => Raw_alt(p.0, p.1)); reg.Register("alt", alt);
    var c1 := reg.Tie("re"); var c2 := reg.Tie("re");
    var conA := Arbitrary<raw_regex>.Tuple(c1, c2);
    var con := conA.Map((p: (raw_regex, raw_regex)) => Raw_con(p.0, p.1)); reg.Register("con", con);
    var qg := Arbitrary<quantifier>.Of([Star, Plus, QuestionMark, LazyStar, LazyPlus, LazyQuestionMark]);
    var qt := reg.Tie("re"); var quantA := Arbitrary<quantifier>.Tuple(qg, qt);
    var quant := quantA.Map((p: (quantifier, raw_regex)) => Raw_quant(p.0, p.1)); reg.Register("quant", quant);
    var capt := reg.Tie("re"); var capture := capt.Map((r: raw_regex) => Raw_capture(r)); reg.Register("capture", capture);
    // greedy counted quants only here so genMatch's `repeat min` witness reliably matches
    var cqg := Arbitrary<counted_quantifier>.Of([
      CountedQuant(0, Some(2), true), CountedQuant(1, Some(2), true), CountedQuant(2, Some(2), true),
      CountedQuant(1, Some(3), true), CountedQuant(2, Some(4), true)]);
    var cnt := reg.Tie("re"); var cntA := Arbitrary<counted_quantifier>.Tuple(cqg, cnt);
    var count := cntA.Map((p: (counted_quantifier, raw_regex)) => Raw_count(p.0, p.1)); reg.Register("count", count);
    var l1 := reg.Tie("leaf"); var l2 := reg.Tie("leaf"); var l3 := reg.Tie("leaf");
    var o1 := reg.Tie("con"); var o2 := reg.Tie("con");
    var u1 := reg.Tie("quant"); var p1 := reg.Tie("capture"); var p2 := reg.Tie("capture");
    var x1 := reg.Tie("alt"); var x2 := reg.Tie("count");
    var reArb := Arbitrary<raw_regex>.Mix([l1, l2, l3, o1, o2, u1, p1, p2, x1, x2]);
    reg.Register("re", reArb); arb := reg.Lookup("re");
  }

  method BuildStringArb() returns (arb: Arbitrary<string>) {
    // richer alphabet: digit '0' and space ' ' exercise \d/\s classes and \b/\B
    // word boundaries against the letter chars.
    var ch := Arbitrary<char>.Of(['a', 'b', '0', ' ']);
    arb := Arbitrary<char>.Lists(ch, 0, 5);
  }

  @AssumeCrossModuleTermination
  class PairMaker extends FlatMapFn<raw_regex, (raw_regex, string)> {
    const strArb: Arbitrary<string>
    constructor(sa: Arbitrary<string>) { strArb := sa; }
    method CreateArbitrary(t: raw_regex) returns (p: Arbitrary<(raw_regex, string)>) {
      var sa := strArb; p := sa.Map((s: string) => (t, s));
    }
  }

  method BuildPairArb() returns (arb: Arbitrary<(raw_regex, string)>) {
    var reArb := BuildRegexArb(); var strArb := BuildStringArb();
    var pm := new PairMaker(strArb); arb := reArb.FlatMap(pm);
  }

  // Lookbehind-focused regex generator: every produced regex is `(?<=A)B` or
  // `(?<!A)B` where A (the lookbehind body) and B are drawn from the matchable
  // grammar (so A/B carry captures/quantifiers but no nested lookarounds/anchors).
  // Concentrates coverage on RegElk's reversed-span / capture-in-lookbehind path.
  method BuildLookbehindRegexArb() returns (arb: Arbitrary<raw_regex>) {
    var inner := BuildMatchableRegexArb();
    var body := BuildMatchableRegexArb();
    var ib := Arbitrary<raw_regex>.Tuple(inner, body);
    var lbg := Arbitrary<lookaround>.Of([Lookbehind, NegLookbehind]);
    var lib := Arbitrary<lookaround>.Tuple(lbg, ib);
    arb := lib.Map((p: (lookaround, (raw_regex, raw_regex))) =>
             Raw_con(Raw_lookaround(p.0, p.1.0), p.1.1));
  }

  method BuildLookbehindPairArb() returns (arb: Arbitrary<(raw_regex, string)>) {
    var reArb := BuildLookbehindRegexArb(); var strArb := BuildStringArb();
    var pm := new PairMaker(strArb); arb := reArb.FlatMap(pm);
  }

  // Counted-quantifier-focused generator: `r{m,n}` (varied bounds, greedy & lazy)
  // wrapping a matchable r. Concentrates coverage on the {m,n} compiler path.
  method BuildCountedRegexArb() returns (arb: Arbitrary<raw_regex>) {
    var body := BuildMatchableRegexArb();
    var cqg := Arbitrary<counted_quantifier>.Of([
      CountedQuant(0, Some(2), true), CountedQuant(1, Some(3), true), CountedQuant(2, Some(3), true),
      CountedQuant(0, Some(2), false), CountedQuant(1, Some(3), false),
      CountedQuant(2, Some(2), true), CountedQuant(0, None, true), CountedQuant(1, None, false)]);
    var cb := Arbitrary<counted_quantifier>.Tuple(cqg, body);
    arb := cb.Map((p: (counted_quantifier, raw_regex)) => Raw_count(p.0, p.1));
  }

  method BuildCountedPairArb() returns (arb: Arbitrary<(raw_regex, string)>) {
    var reArb := BuildCountedRegexArb(); var strArb := BuildStringArb();
    var pm := new PairMaker(strArb); arb := reArb.FlatMap(pm);
  }

  // Capture-reset-focused generator: quantified alternations of DISTINCT capture
  // groups -- `(?:(X)|(Y))q` and `((X)|(Y))q` -- the textbook shape where each
  // quantifier iteration RESETS the inner groups to undefined (JS semantics). The
  // outer quantifier makes earlier-iteration captures get overwritten/reset, so the
  // final spans depend on the last iteration only. Differentially checked vs JS.
  method BuildCaptureResetRegexArb() returns (arb: Arbitrary<raw_regex>) {
    // shape A: (?:(X)|(Y))q   (two capture groups, both reset each iteration)
    var xA := BuildMatchableRegexArb(); var yA := BuildMatchableRegexArb();
    var xyA := Arbitrary<raw_regex>.Tuple(xA, yA);
    var altA := xyA.Map((p: (raw_regex, raw_regex)) => Raw_alt(Raw_capture(p.0), Raw_capture(p.1)));
    var qA := Arbitrary<quantifier>.Of([Star, Plus, QuestionMark, LazyStar, LazyPlus]);
    var qaA := Arbitrary<quantifier>.Tuple(qA, altA);
    var shapeA := qaA.Map((p: (quantifier, raw_regex)) => Raw_quant(p.0, p.1));
    // shape B: ((X)|(Y))q     (outer capture too -> 3 groups all resetting)
    var xB := BuildMatchableRegexArb(); var yB := BuildMatchableRegexArb();
    var xyB := Arbitrary<raw_regex>.Tuple(xB, yB);
    var altB := xyB.Map((p: (raw_regex, raw_regex)) => Raw_capture(Raw_alt(Raw_capture(p.0), Raw_capture(p.1))));
    var qB := Arbitrary<quantifier>.Of([Star, Plus, QuestionMark, LazyStar, LazyPlus]);
    var qbB := Arbitrary<quantifier>.Tuple(qB, altB);
    var shapeB := qbB.Map((p: (quantifier, raw_regex)) => Raw_quant(p.0, p.1));
    arb := Arbitrary<raw_regex>.Mix([shapeA, shapeB]);
  }

  method BuildCaptureResetPairArb() returns (arb: Arbitrary<(raw_regex, string)>) {
    var reArb := BuildCaptureResetRegexArb(); var strArb := BuildStringArb();
    var pm := new PairMaker(strArb); arb := reArb.FlatMap(pm);
  }

  // Nested-lookbehind generator: `(?<= (?<=A)B ) C` -- the outer lookbehind's body
  // is itself a lookbehind-containing regex (depth-2 lookaround nesting). Exercises
  // RegElk's recursive lookaround / nested reversed-span handling against JS.
  method BuildNestedLookbehindRegexArb() returns (arb: Arbitrary<raw_regex>) {
    var innerLB := BuildLookbehindRegexArb();        // produces (?<=A)B
    var c := BuildMatchableRegexArb();
    var ic := Arbitrary<raw_regex>.Tuple(innerLB, c);
    var lb2 := Arbitrary<lookaround>.Of([Lookbehind, NegLookbehind]);
    var lic := Arbitrary<lookaround>.Tuple(lb2, ic);
    arb := lic.Map((p: (lookaround, (raw_regex, raw_regex))) =>
             Raw_con(Raw_lookaround(p.0, p.1.0), p.1.1));
  }

  method BuildNestedLookbehindPairArb() returns (arb: Arbitrary<(raw_regex, string)>) {
    var reArb := BuildNestedLookbehindRegexArb(); var strArb := BuildStringArb();
    var pm := new PairMaker(strArb); arb := reArb.FlatMap(pm);
  }

  // Quantified / counted lookbehind: `(?:(?<=A))q B` and `(?:(?<=A)){m,n} B`. JS
  // rejects a BARE quantified lookbehind, but RegElk's toPattern wraps quantified
  // subexpressions in (?:...), and `(?:(?<=A))*` IS valid JS — so this is genuinely
  // differential. Exercises the nullable-quantifier-over-zero-width-assertion path
  // (incl. the JS "empty iteration doesn't capture" reset, e.g. `(?:(?<=(a)))*b`).
  method BuildQuantLookbehindRegexArb() returns (arb: Arbitrary<raw_regex>) {
    // shape Q: (?:(?<=A))q B
    var aQ := BuildMatchableRegexArb();
    var lbgQ := Arbitrary<lookaround>.Of([Lookbehind, NegLookbehind]);
    var laQ := Arbitrary<lookaround>.Tuple(lbgQ, aQ);
    var lookQ := laQ.Map((p: (lookaround, raw_regex)) => Raw_lookaround(p.0, p.1));
    var qg := Arbitrary<quantifier>.Of([Star, Plus, QuestionMark, LazyStar, LazyPlus]);
    var qlQ := Arbitrary<quantifier>.Tuple(qg, lookQ);
    var qlbQ := qlQ.Map((p: (quantifier, raw_regex)) => Raw_quant(p.0, p.1));
    var bQ := BuildMatchableRegexArb();
    var qbQ := Arbitrary<raw_regex>.Tuple(qlbQ, bQ);
    var shapeQ := qbQ.Map((p: (raw_regex, raw_regex)) => Raw_con(p.0, p.1));
    // shape C: (?:(?<=A)){m,n} B   (counted lookbehind, e.g. (?<=a){2})
    var aC := BuildMatchableRegexArb();
    var lbgC := Arbitrary<lookaround>.Of([Lookbehind, NegLookbehind]);
    var laC := Arbitrary<lookaround>.Tuple(lbgC, aC);
    var lookC := laC.Map((p: (lookaround, raw_regex)) => Raw_lookaround(p.0, p.1));
    var cqg := Arbitrary<counted_quantifier>.Of([
      CountedQuant(0, Some(2), true), CountedQuant(1, Some(2), true),
      CountedQuant(2, Some(2), true), CountedQuant(1, None, true)]);
    var clC := Arbitrary<counted_quantifier>.Tuple(cqg, lookC);
    var clbC := clC.Map((p: (counted_quantifier, raw_regex)) => Raw_count(p.0, p.1));
    var bC := BuildMatchableRegexArb();
    var cbC := Arbitrary<raw_regex>.Tuple(clbC, bC);
    var shapeC := cbC.Map((p: (raw_regex, raw_regex)) => Raw_con(p.0, p.1));
    arb := Arbitrary<raw_regex>.Mix([shapeQ, shapeC]);
  }

  method BuildQuantLookbehindPairArb() returns (arb: Arbitrary<(raw_regex, string)>) {
    var reArb := BuildQuantLookbehindRegexArb(); var strArb := BuildStringArb();
    var pm := new PairMaker(strArb); arb := reArb.FlatMap(pm);
  }

  // Deeply nested captures: `(((A)))`, `((A)(B))`, and `((A))q`. Tests group-index
  // assignment (parent before children, left-to-right) and nested capture spans /
  // nested reset under a quantifier — all standard JS, fully differential.
  method BuildNestedCaptureRegexArb() returns (arb: Arbitrary<raw_regex>) {
    // shape 1: (((A)))
    var a1 := BuildMatchableRegexArb();
    var s1 := a1.Map((r: raw_regex) => Raw_capture(Raw_capture(Raw_capture(r))));
    // shape 2: ((A)(B))   (parent group 1, siblings 2 and 3)
    var a2 := BuildMatchableRegexArb(); var b2 := BuildMatchableRegexArb();
    var ab2 := Arbitrary<raw_regex>.Tuple(a2, b2);
    var s2 := ab2.Map((p: (raw_regex, raw_regex)) => Raw_capture(Raw_con(Raw_capture(p.0), Raw_capture(p.1))));
    // shape 3: ((A))q   (quantified nested capture -> nested per-iteration reset)
    var a3 := BuildMatchableRegexArb();
    var n3 := a3.Map((r: raw_regex) => Raw_capture(Raw_capture(r)));
    var q3 := Arbitrary<quantifier>.Of([Star, Plus, QuestionMark, LazyStar]);
    var qn3 := Arbitrary<quantifier>.Tuple(q3, n3);
    var s3 := qn3.Map((p: (quantifier, raw_regex)) => Raw_quant(p.0, p.1));
    arb := Arbitrary<raw_regex>.Mix([s1, s2, s3]);
  }

  method BuildNestedCapturePairArb() returns (arb: Arbitrary<(raw_regex, string)>) {
    var reArb := BuildNestedCaptureRegexArb(); var strArb := BuildStringArb();
    var pm := new PairMaker(strArb); arb := reArb.FlatMap(pm);
  }

  // Mixed lookaround in one pattern: a body constrained on BOTH sides, and one
  // lookbehind nesting a lookahead. Captures can come from either direction in a
  // single match (the lookbehind's are reconstructed from reversed spans, the
  // lookahead's are forward) -- a strong joint test of both directions vs JS.
  //   shape 1: (?<=A) B (?=C)        side-by-side lookbehind + lookahead
  //   shape 2: (?<= (?=A) B ) C      lookahead nested inside a lookbehind
  method BuildMixedLookaroundRegexArb() returns (arb: Arbitrary<raw_regex>) {
    // ---- shape 1: (?<=A)B(?=C) ----
    var a1 := BuildMatchableRegexArb();
    var lbg1 := Arbitrary<lookaround>.Of([Lookbehind, NegLookbehind]);
    var lbA1t := Arbitrary<lookaround>.Tuple(lbg1, a1);
    var lbA1 := lbA1t.Map((p: (lookaround, raw_regex)) => Raw_lookaround(p.0, p.1));   // (?<=A)
    var c1 := BuildMatchableRegexArb();
    var lag1 := Arbitrary<lookaround>.Of([Lookahead, NegLookahead]);
    var laC1t := Arbitrary<lookaround>.Tuple(lag1, c1);
    var laC1 := laC1t.Map((p: (lookaround, raw_regex)) => Raw_lookaround(p.0, p.1));   // (?=C)
    var b1 := BuildMatchableRegexArb();
    var lbAB1t := Arbitrary<raw_regex>.Tuple(lbA1, b1);
    var lbAB1 := lbAB1t.Map((p: (raw_regex, raw_regex)) => Raw_con(p.0, p.1));          // (?<=A)B
    var full1t := Arbitrary<raw_regex>.Tuple(lbAB1, laC1);
    var shape1 := full1t.Map((p: (raw_regex, raw_regex)) => Raw_con(p.0, p.1));         // (?<=A)B(?=C)
    // ---- shape 2: (?<=(?=A)B)C ----
    var a2 := BuildMatchableRegexArb();
    var lag2 := Arbitrary<lookaround>.Of([Lookahead, NegLookahead]);
    var laA2t := Arbitrary<lookaround>.Tuple(lag2, a2);
    var laA2 := laA2t.Map((p: (lookaround, raw_regex)) => Raw_lookaround(p.0, p.1));    // (?=A)
    var b2 := BuildMatchableRegexArb();
    var inner2t := Arbitrary<raw_regex>.Tuple(laA2, b2);
    var inner2 := inner2t.Map((p: (raw_regex, raw_regex)) => Raw_con(p.0, p.1));        // (?=A)B
    var lbg2 := Arbitrary<lookaround>.Of([Lookbehind, NegLookbehind]);
    var lbI2t := Arbitrary<lookaround>.Tuple(lbg2, inner2);
    var lbI2 := lbI2t.Map((p: (lookaround, raw_regex)) => Raw_lookaround(p.0, p.1));    // (?<=(?=A)B)
    var c2 := BuildMatchableRegexArb();
    var full2t := Arbitrary<raw_regex>.Tuple(lbI2, c2);
    var shape2 := full2t.Map((p: (raw_regex, raw_regex)) => Raw_con(p.0, p.1));         // (?<=(?=A)B)C
    arb := Arbitrary<raw_regex>.Mix([shape1, shape2]);
  }

  method BuildMixedLookaroundPairArb() returns (arb: Arbitrary<(raw_regex, string)>) {
    var reArb := BuildMixedLookaroundRegexArb(); var strArb := BuildStringArb();
    var pm := new PairMaker(strArb); arb := reArb.FlatMap(pm);
  }

  method BuildWitnessArb() returns (arb: Arbitrary<(raw_regex, nat)>) {
    var reArb := BuildMatchableRegexArb();
    var natArb := Arbitrary<nat>.Nats(1000);
    arb := Arbitrary<raw_regex>.Tuple(reArb, natArb);
  }

  method {:test} RegElkProperties() {
    var scale := PbtScale();
    print "PBT_SCALE = ", scale, " (base numRuns multiplied by this)\n";
    // ---- ORACLE: RegElk vs the real JS RegExp, random (regex, string) pairs ----
    var oc := new Counters();
    var pA := BuildPairArb(); var sO := new OracleAgreement(oc);
    var cO := DefaultConfig<(raw_regex, string)>()
      .(seed := Some(13371337 as bv64), numRuns := 60 * scale, verbosity := Low,
        classifier := Some((p: (raw_regex, string)) => classifyPair(p)));
    var okO := RunMethodTestWithConfig(pA, sO, "ORACLE: RegElk match == JS RegExp match", cO);
    print "ORACLE tallies: matched ", oc.matched, "/", oc.total, ", with-captures ", oc.withCaps, "\n";
    expect okO, "PROPERTY ORACLE FAILED";
    expect oc.matched > 0 && oc.withCaps > 0, "generator produced no matches/captures";

    // ---- WITNESS + MUTATION: constructed matching string, then a random edit ----
    var wc := new Counters();
    var wA := BuildWitnessArb(); var sW := new WitnessMutation(wc);
    var cW := DefaultConfig<(raw_regex, nat)>()
      .(seed := Some(77777 as bv64), numRuns := 60 * scale, verbosity := Low,
        classifier := Some((p: (raw_regex, nat)) => featTag(p.0)));
    var okW := RunMethodTestWithConfig(wA, sW,
      "WITNESS+MUTATION: regex matches its witness; RegElk==JS on witness & mutation", cW);
    print "WITNESS tallies: witness-matched ", wc.matched, "/", wc.total, ", with-captures ", wc.withCaps, "\n";
    expect okW, "PROPERTY WITNESS+MUTATION FAILED";
    expect wc.matched == wc.total, "RegElk failed to match a constructed witness (or genMatch wrong)";
    expect wc.withCaps > 0, "no witnesses with capture groups generated";

    // ---- CROSS / STAR ----
    var pB := BuildPairArb(); var sC := new CrossEngineAgreement();
    var cC := DefaultConfig<(raw_regex, string)>()
      .(seed := Some(424242 as bv64), numRuns := 50 * scale, verbosity := Low,
        classifier := Some((p: (raw_regex, string)) => classifyPair(p)));
    var okC := RunMethodTestWithConfig(pB, sC, "CROSS: Array=List=Map", cC);
    expect okC, "PROPERTY CROSS FAILED";

    var pS := BuildPairArb(); var sS := new StarAlwaysMatches();
    var cS := DefaultConfig<(raw_regex, string)>()
      .(seed := Some(900900 as bv64), numRuns := 50 * scale, verbosity := Low,
        classifier := Some((p: (raw_regex, string)) => classifyRegex(p.0)));
    var okS := RunMethodTestWithConfig(pS, sS, "STAR: (r)* always matches", cS);
    expect okS, "PROPERTY STAR FAILED";

    // ---- LITERAL (bare string generator: exercises early-termination fix) ----
    var strArb := BuildStringArb(); var sL := new LiteralSelfMatch();
    var cL := DefaultConfig<string>()
      .(seed := Some(55555 as bv64), numRuns := 40 * scale, verbosity := Low,
        classifier := Some((s: string) => lenTag(|s|)));
    var okL := RunMethodTestWithConfig(strArb, sL, "LITERAL: literal matches itself", cL);
    expect okL, "PROPERTY LITERAL FAILED";

    // ---- structural identities (true in any regex semantics) ----
    var iCfg := DefaultConfig<(raw_regex, string)>()
      .(seed := Some(20240609 as bv64), numRuns := 40 * scale, verbosity := Low,
        classifier := Some((p: (raw_regex, string)) => classifyPair(p)));
    var p4 := BuildPairArb(); var s4 := new AltIdempotent();
    var ok4 := RunMethodTestWithConfig(p4, s4, "IDENTITY: (r|r) == r", iCfg);
    expect ok4, "PROPERTY (r|r)==r FAILED";
    var p5 := BuildPairArb(); var s5 := new ConEmptyIdentity();
    var ok5 := RunMethodTestWithConfig(p5, s5, "IDENTITY: (eps.r) == r", iCfg);
    expect ok5, "PROPERTY (eps.r)==r FAILED";
    var p6 := BuildPairArb(); var s6 := new Deterministic();
    var ok6 := RunMethodTestWithConfig(p6, s6, "INVARIANT: full_match deterministic", iCfg);
    expect ok6, "PROPERTY determinism FAILED";
    var p7 := BuildPairArb(); var s7 := new SpansWellFormed();
    var ok7 := RunMethodTestWithConfig(p7, s7, "INVARIANT: capture spans within input", iCfg);
    expect ok7, "PROPERTY span-well-formedness FAILED";

    // ---- additional metamorphic identities (exercise distinct compiler paths) ----
    var jCfg := DefaultConfig<(raw_regex, string)>()
      .(seed := Some(31415926 as bv64), numRuns := 40 * scale, verbosity := Low,
        classifier := Some((p: (raw_regex, string)) => classifyPair(p)));
    var p8 := BuildPairArb(); var s8 := new ConEmptyRight();
    var ok8 := RunMethodTestWithConfig(p8, s8, "IDENTITY: (r.eps) == r", jCfg);
    expect ok8, "PROPERTY (r.eps)==r FAILED";
    var p9 := BuildPairArb(); var s9 := new AnchorStart();
    var ok9 := RunMethodTestWithConfig(p9, s9, "ANCHOR: ^r matches iff r matches at index 0", jCfg);
    expect ok9, "PROPERTY anchor-start FAILED";
    var p10 := BuildPairArb(); var s10 := new PlusUnroll();
    var ok10 := RunMethodTestWithConfig(p10, s10, "IDENTITY: r+ == r.r* (greedy & lazy span)", jCfg);
    expect ok10, "PROPERTY plus-unroll FAILED";
    var p11 := BuildPairArb(); var s11 := new CountVsQuant();
    var ok11 := RunMethodTestWithConfig(p11, s11, "IDENTITY: r{0,1}==r?, r{0,}==r*, r{1,}==r+", jCfg);
    expect ok11, "PROPERTY count-vs-quant FAILED";
    var p12 := BuildPairArb(); var s12 := new StarDouble();
    var ok12 := RunMethodTestWithConfig(p12, s12, "STAR: (r*)* always matches", jCfg);
    expect ok12, "PROPERTY star-double FAILED";

    // ---- LOOKBEHIND: differential vs JS, concentrated on (?<=A)B / (?<!A)B with
    // captures inside the lookbehind (RegElk's reversed-span reconstruction path) ----
    var lbc := new Counters();
    var pLB := BuildLookbehindPairArb(); var sLB := new OracleAgreement(lbc);
    var cLB := DefaultConfig<(raw_regex, string)>()
      .(seed := Some(16180339 as bv64), numRuns := 50 * scale, verbosity := Low,
        classifier := Some((p: (raw_regex, string)) => classifyPair(p)));
    var okLB := RunMethodTestWithConfig(pLB, sLB,
      "LOOKBEHIND-ORACLE: (?<=A)B vs JS (captures, reversed spans)", cLB);
    print "LOOKBEHIND tallies: matched ", lbc.matched, "/", lbc.total,
          ", with-captures ", lbc.withCaps, "\n";
    expect okLB, "PROPERTY LOOKBEHIND-ORACLE FAILED";
    expect lbc.matched > 0, "lookbehind generator produced no matches";

    // ---- COUNTED QUANTIFIER: differential vs JS, concentrated on r{m,n} ----
    var ctc := new Counters();
    var pCT := BuildCountedPairArb(); var sCT := new OracleAgreement(ctc);
    var cCT := DefaultConfig<(raw_regex, string)>()
      .(seed := Some(27182818 as bv64), numRuns := 50 * scale, verbosity := Low,
        classifier := Some((p: (raw_regex, string)) => classifyPair(p)));
    var okCT := RunMethodTestWithConfig(pCT, sCT, "COUNTED-ORACLE: r{m,n} vs JS", cCT);
    print "COUNTED tallies: matched ", ctc.matched, "/", ctc.total,
          ", with-captures ", ctc.withCaps, "\n";
    expect okCT, "PROPERTY COUNTED-ORACLE FAILED";
    expect ctc.matched > 0, "counted generator produced no matches";

    // counted-quantifier metamorphic identities (over the full generator)
    var p13 := BuildPairArb(); var s13 := new CountUnroll();
    var ok13 := RunMethodTestWithConfig(p13, s13, "IDENTITY: r{2,3}==r.r.r?, r{1,2}==r.r?", jCfg);
    expect ok13, "PROPERTY count-unroll FAILED";
    var p14 := BuildPairArb(); var s14 := new CountGreedyLazy();
    var ok14 := RunMethodTestWithConfig(p14, s14, "ORDER: r{1,3} greedy end >= r{1,3}? lazy end", jCfg);
    expect ok14, "PROPERTY count-greedy-lazy FAILED";

    // ---- CAPTURE RESET: ((X)|(Y))q differential vs JS (per-iteration group reset),
    // plus a metamorphic transparency invariant ----
    var crc := new Counters();
    var pCR := BuildCaptureResetPairArb(); var sCR := new OracleAgreement(crc);
    var cCR := DefaultConfig<(raw_regex, string)>()
      .(seed := Some(14142135 as bv64), numRuns := 50 * scale, verbosity := Low,
        classifier := Some((p: (raw_regex, string)) => classifyPair(p)));
    var okCR := RunMethodTestWithConfig(pCR, sCR,
      "CAPTURE-RESET-ORACLE: ((X)|(Y))q vs JS (per-iteration reset)", cCR);
    print "CAPTURE-RESET tallies: matched ", crc.matched, "/", crc.total,
          ", with-captures ", crc.withCaps, "\n";
    expect okCR, "PROPERTY CAPTURE-RESET-ORACLE FAILED";
    expect crc.matched > 0 && crc.withCaps > 0, "capture-reset generator produced no matches/captures";

    var p15 := BuildPairArb(); var s15 := new CaptureTransparent();
    var ok15 := RunMethodTestWithConfig(p15, s15, "IDENTITY: (r) whole-match span == r; group1==group0", jCfg);
    expect ok15, "PROPERTY capture-transparent FAILED";

    // ---- NESTED LOOKBEHIND: (?<=(?<=A)B)C differential vs JS ----
    var nlc := new Counters();
    var pNL := BuildNestedLookbehindPairArb(); var sNL := new OracleAgreement(nlc);
    var cNL := DefaultConfig<(raw_regex, string)>()
      .(seed := Some(22360679 as bv64), numRuns := 50 * scale, verbosity := Low,
        classifier := Some((p: (raw_regex, string)) => classifyPair(p)));
    var okNL := RunMethodTestWithConfig(pNL, sNL, "NESTED-LOOKBEHIND-ORACLE: (?<=(?<=A)B)C vs JS", cNL);
    print "NESTED-LB tallies: matched ", nlc.matched, "/", nlc.total,
          ", with-captures ", nlc.withCaps, "\n";
    expect okNL, "PROPERTY NESTED-LOOKBEHIND-ORACLE FAILED";
    expect nlc.matched > 0, "nested-lookbehind generator produced no matches";

    // ---- QUANTIFIED / COUNTED LOOKBEHIND: (?:(?<=A))q B and (?:(?<=A)){m,n} B vs JS ----
    var qlc := new Counters();
    var pQL := BuildQuantLookbehindPairArb(); var sQL := new OracleAgreement(qlc);
    var cQL := DefaultConfig<(raw_regex, string)>()
      .(seed := Some(17320508 as bv64), numRuns := 50 * scale, verbosity := Low,
        classifier := Some((p: (raw_regex, string)) => classifyPair(p)));
    var okQL := RunMethodTestWithConfig(pQL, sQL,
      "QUANT-LOOKBEHIND-ORACLE: (?:(?<=A))q/{m,n} B vs JS", cQL);
    print "QUANT-LB tallies: matched ", qlc.matched, "/", qlc.total,
          ", with-captures ", qlc.withCaps, "\n";
    expect okQL, "PROPERTY QUANT-LOOKBEHIND-ORACLE FAILED";
    expect qlc.matched > 0, "quant-lookbehind generator produced no matches";

    // ---- DEEPLY NESTED CAPTURES: (((A))), ((A)(B)), ((A))q vs JS (group numbering) ----
    var ncc := new Counters();
    var pNC := BuildNestedCapturePairArb(); var sNC := new OracleAgreement(ncc);
    var cNC := DefaultConfig<(raw_regex, string)>()
      .(seed := Some(26457513 as bv64), numRuns := 50 * scale, verbosity := Low,
        classifier := Some((p: (raw_regex, string)) => classifyPair(p)));
    var okNC := RunMethodTestWithConfig(pNC, sNC, "NESTED-CAPTURE-ORACLE: (((A))) / ((A)(B)) vs JS", cNC);
    print "NESTED-CAP tallies: matched ", ncc.matched, "/", ncc.total,
          ", with-captures ", ncc.withCaps, "\n";
    expect okNC, "PROPERTY NESTED-CAPTURE-ORACLE FAILED";
    expect ncc.matched > 0 && ncc.withCaps > 0, "nested-capture generator produced no matches/captures";

    // ---- MIXED LOOKAROUND: (?<=A)B(?=C) and (?<=(?=A)B)C vs JS (captures from both
    // directions in one match) ----
    var mlc := new Counters();
    var pML := BuildMixedLookaroundPairArb(); var sML := new OracleAgreement(mlc);
    var cML := DefaultConfig<(raw_regex, string)>()
      .(seed := Some(57721566 as bv64), numRuns := 50 * scale, verbosity := Low,
        classifier := Some((p: (raw_regex, string)) => classifyPair(p)));
    var okML := RunMethodTestWithConfig(pML, sML,
      "MIXED-LOOKAROUND-ORACLE: (?<=A)B(?=C) / (?<=(?=A)B)C vs JS", cML);
    print "MIXED-LA tallies: matched ", mlc.matched, "/", mlc.total,
          ", with-captures ", mlc.withCaps, "\n";
    expect okML, "PROPERTY MIXED-LOOKAROUND-ORACLE FAILED";
    expect mlc.matched > 0, "mixed-lookaround generator produced no matches";

    // ---- SHRINK QUALITY: break a property on purpose, then assert the shrinker
    // minimised the counterexample to its KNOWN minimum (tests the native-Choice
    // shrinker end-to-end: ShrinkByDeletion + binary-search down to the floor) ----
    var pSQ1 := BuildPairArb(); var sSQ1 := new StrLenLE1();
    var cSQ := DefaultConfig<(raw_regex, string)>()
      .(seed := Some(11235813 as bv64), numRuns := 30 * scale, verbosity := Low);
    var okSQ1, ceSQ1 := RunMethodTestWithConfigCE(pSQ1, sSQ1,
      "SHRINK-QUALITY: |s|<=1 (expect minimal CE |s|==2)", cSQ);
    expect !okSQ1, "SHRINK-QUALITY-1: property should have failed (|s|<=1 is false)";
    expect ceSQ1.Some?, "SHRINK-QUALITY-1: no counterexample returned";
    var reSQ1 := ceSQ1.value.0; var sSQ1str := ceSQ1.value.1;
    print "SHRINK-QUALITY-1 minimised CE: |s|=", |sSQ1str|, ", astSize(re)=", astSize(reSQ1), "\n";
    // The greedy (Minithesis-style) shrinker reaches a LOCAL minimum: from random
    // counterexamples (|s| up to 5, astSize up to ~15) it drives the string toward
    // the minimal violating length 2 (reaches 3) and shrinks the irrelevant regex
    // (reaches astSize 4). Bounds guard against a regressed/no-op shrinker.
    expect |sSQ1str| <= 3, "shrinker failed to reduce the violating string near-minimal";
    expect astSize(reSQ1) <= 4, "shrinker failed to reduce the (irrelevant) regex";

    var pSQ2 := BuildPairArb(); var sSQ2 := new AstSizeLE1();
    var cSQ2 := DefaultConfig<(raw_regex, string)>()
      .(seed := Some(13211235 as bv64), numRuns := 30 * scale, verbosity := Low);
    var okSQ2, ceSQ2 := RunMethodTestWithConfigCE(pSQ2, sSQ2,
      "SHRINK-QUALITY: astSize(r)<=1 (expect minimal CE astSize==2, |s|==0)", cSQ2);
    expect !okSQ2, "SHRINK-QUALITY-2: property should have failed (astSize<=1 is false)";
    expect ceSQ2.Some?, "SHRINK-QUALITY-2: no counterexample returned";
    var reSQ2 := ceSQ2.value.0; var sSQ2str := ceSQ2.value.1;
    print "SHRINK-QUALITY-2 minimised CE: astSize(re)=", astSize(reSQ2), ", |s|=", |sSQ2str|, "\n";
    // Here the shrinker drives the regex toward the minimal composite (astSize 2,
    // reaches 3) and ELIMINATES the irrelevant string entirely (|s| == 0, its global
    // minimum) -- a clear demonstration that the irrelevant dimension is shrunk away.
    expect astSize(reSQ2) <= 3, "shrinker failed to reduce regex near the minimal composite";
    expect |sSQ2str| == 0, "shrinker failed to eliminate the irrelevant string";

    // ---- KEPT counterexample, EXPECTED TO FAIL: r? != (r|eps) for lazy r ----
    // A fixed generator of exactly the counterexample (r = a*?, s = "aa") makes the
    // failure deterministic. We assert the metamorphic property is VIOLATED, i.e.
    // RegElk distinguishes r? from (r|eps) -- matching both OCaml and JS. The exact
    // spans are pinned (and cross-checked against OCaml in OCamlCrossCheck.dfy).
    var aLazy := Raw_quant(LazyStar, raw_char('a'));
    var cxArb := Arbitrary<(raw_regex, string)>.Of([(aLazy, "aa")]);
    var sX := new OptEqAltEmpty();
    var xCfg := DefaultConfig<(raw_regex, string)>().(seed := Some(1 as bv64), numRuns := 20, verbosity := Low);
    var okX := RunMethodTestWithConfig(cxArb, sX, "EXPECT-FAIL: r? != (r|eps) for lazy r", xCfg);
    expect !okX, "regression: r? == (r|eps) now HOLDS, but it must differ (OCaml/JS)";
    var ropt := LI.full_match(Raw_quant(QuestionMark, aLazy), "aa");
    var ralt := LI.full_match(Raw_alt(aLazy, Raw_empty), "aa");
    expect spanOf(ropt) == Some((0, 1)), "(a*?)? on aa must span [0,1] (OCaml/JS)";
    expect spanOf(ralt) == Some((0, 0)), "(a*?|) on aa must span [0,0] (OCaml/JS)";
    print "EXPECT-FAIL r? != (r|eps): observed as expected ((a*?)? -> [0,1], (a*?|) -> [0,0])\n";

    print "RegElk property tests: all properties held\n";
  }

  // Entry point so the suite can be compiled ONCE (dafny translate js) and then
  // swept across run sizes via `PBT_SCALE=N node <out>.js` without recompiling.
  method Main() {
    RegElkProperties();
  }
}
