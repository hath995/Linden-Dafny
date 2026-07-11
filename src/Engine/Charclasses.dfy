// Port of charclasses.ml
// Representing classes of characters, including ranges and negated classes.
//
// NOTE: OCaml chars go 0..255; the engine only deals with the first 256 chars.
// Design choice for the Dafny port: range *bounds* are modelled as `int` (code
// points) rather than `char`, so range negation / construction is total integer
// arithmetic with no `int as char` validity proof obligations. Character
// literals (Single / CChar) and the consumed character stay as `char`.
module Charclasses {
  import opened Std.Wrappers

  // https://tc39.es/ecma262/#ASCII-word-characters
  predicate is_ascii_word_character(c: char) {
    var n := c as int;
    (n >= 65 && n <= 90) ||      // uppercase
    (n >= 97 && n <= 122) ||     // lowercase
    (n >= 48 && n <= 57) ||      // numbers
    (n == 95)                    // '_'
  }

  const min_char: int := 0
  const max_char: int := 255

  function prev_char(c: int): int { c - 1 }
  function next_char(c: int): int { c + 1 }
  function char_max(c1: int, c2: int): int { if c1 > c2 then c1 else c2 }

  // A range is a pair of inclusive code-point bounds.
  datatype char_expectation =
    | All                         // any character
    | Single(c: char)             // a particular character
    | Ranges(rs: seq<(int, int)>) // several ranges (expected ordered)

  // * Range Negation

  // ordered negation of an ordered list of ranges
  function range_negation(l: seq<(int, int)>, min: int): seq<(int, int)>
    decreases |l|
  {
    if |l| == 0 then [(min, max_char)]
    else
      var r1 := l[0].0;
      var r2 := l[0].1;
      var next := if r2 == max_char then [] else range_negation(l[1..], next_char(r2));
      if min < r1 then [(min, prev_char(r1))] + next
      else next
  }

  function range_neg(l: seq<(int, int)>): seq<(int, int)> {
    range_negation(l, min_char)
  }

  function negation(ce: char_expectation): char_expectation {
    match ce
    case All => Ranges([])
    case Single(x) => Ranges(range_neg([(x as int, x as int)]))
    case Ranges(l) => Ranges(range_neg(l))
  }

  // * Usual Ranges - stopped at 255

  const digit: seq<(int, int)> := [(48, 57)]                  // \d

  const word: seq<(int, int)> :=                              // \w
    [(48, 57), (65, 90), (95, 95), (97, 122)]

  const space: seq<(int, int)> :=                             // \s
    [(9, 13), (32, 32), (160, 160)]

  // * Character Groups (usual character classes)
  datatype char_group =
    | Digit     // \d
    | NonDigit  // \D
    | Word      // \w
    | NonWord   // \W
    | Space     // \s
    | NonSpace  // \S

  function group_to_range(g: char_group): seq<(int, int)> {
    match g
    case Digit => digit
    case NonDigit => range_neg(digit)
    case Word => word
    case NonWord => range_neg(word)
    case Space => space
    case NonSpace => range_neg(space)
  }

  // * Character Classes
  datatype char_class_elt =
    | CChar(c: char)
    | CRange(c1: char, c2: char)  // e.g. "a-e"
    | CGroup(g: char_group)       // e.g. "\w"

  // contents between [] or [^]; may be out of order
  type char_class = seq<char_class_elt>

  // flattening everything to a list of unordered ranges
  function class_flatten(c: char_class): seq<(int, int)>
    decreases |c|
  {
    if |c| == 0 then []
    else
      match c[0]
      case CChar(x) => [(x as int, x as int)] + class_flatten(c[1..])
      case CRange(c1, c2) => [(c1 as int, c2 as int)] + class_flatten(c[1..])
      case CGroup(g) => group_to_range(g) + class_flatten(c[1..])
  }

  // used by the parser: what happens when two elements are separated by a dash?
  // two characters -> a range; otherwise the dash is a literal '-'.
  function make_range(e1: char_class_elt, e2: char_class_elt): char_class {
    match (e1, e2)
    case (CChar(c1), CChar(c2)) => [CRange(c1, c2)]
    case _ => [e1, CChar('-'), e2]
  }

  // * Character Acceptance

  // the list is assumed ordered
  function is_in_range(c: int, l: seq<(int, int)>): bool
    decreases |l|
  {
    if |l| == 0 then false
    else
      var ch1 := l[0].0;
      var ch2 := l[0].1;
      if c < ch1 then false
      else if c >= ch1 && c <= ch2 then true
      else is_in_range(c, l[1..])
  }

  // is a read character accepted by an expectation?
  // (the OCaml `None -> failwith` is guarded by callers: we never consume a
  //  blocked thread without a character. Total here -> None means "not
  //  accepted", which is never the operative branch.)
  function is_accepted(read: Option<char>, ce: char_expectation): bool {
    match read
    case None => false
    case Some(r) =>
      match ce
      case All => true
      case Single(e) => r == e
      case Ranges(l) => is_in_range(r as int, l)
  }

  // * Range Construction

  // small total sort by range start (replaces OCaml List.sort)
  function insert_range(x: (int, int), l: seq<(int, int)>): seq<(int, int)>
    decreases |l|
  {
    if |l| == 0 then [x]
    else if x.0 <= l[0].0 then [x] + l
    else [l[0]] + insert_range(x, l[1..])
  }

  function sort_ranges(l: seq<(int, int)>): seq<(int, int)>
    decreases |l|
  {
    if |l| == 0 then []
    else insert_range(l[0], sort_ranges(l[1..]))
  }

  // assumes the list is ordered by first element, current has the smallest
  // first element, and each pair is well-formed (first <= second).
  function build_range(current: (int, int), next: seq<(int, int)>): seq<(int, int)>
    decreases |next|
  {
    var cstart := current.0;
    var cend := current.1;
    if cend == max_char then [current]
    else if |next| == 0 then [current]
    else
      var nstart := next[0].0;
      var nend := next[0].1;
      if nstart > next_char(cend) then
        // disjoint ranges
        [current] + build_range((nstart, nend), next[1..])
      else
        // extend from the end
        build_range((cstart, char_max(cend, nend)), next[1..])
  }

  function class_to_range(c: char_class): seq<(int, int)> {
    var lsort := sort_ranges(class_flatten(c));
    if |lsort| == 0 then []
    else build_range(lsort[0], lsort[1..])
  }
}
