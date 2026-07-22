// Port of regex.ml
// The type of regexes we match, including capture groups and lookarounds,
// plus annotation, nullability analysis, and AST manipulation helpers.
/** The regex AST (before/after annotation), plus nullability analysis and AST
    manipulation helpers. `raw_regex` is what the `Parser` produces; `annotate`
    turns it into a `regex` with unique ids for every capture group, lookaround,
    and quantifier, which is what the `Compiler` consumes. */
module RegElkRegex {
  import opened Std.Wrappers
  import opened Charclasses

  // * Quantifiers
  // all of these can be compiled for regex-linear matching, except LazyPlus
  /** The six ECMAScript quantifier shorthands: `*`, `*?`, `+`, `+?`, `?`, `??`.
      All but `LazyPlus` can be compiled for linear-time matching. */
  datatype quantifier =
    | Star | LazyStar | Plus | LazyPlus | QuestionMark | LazyQuestionMark

  // generic quantifier type, for (possibly non-linear) counted repetition.
  // max = None represents infinity.
  /** A general `{min,max}`-style counted repetition (`max = None` means
      unbounded), with a `greedy` flag; the canonical form every `quantifier`
      is reduced to. */
  datatype counted_quantifier = CountedQuant(min: int, max: Option<int>, greedy: bool)

  /** Converts a quantifier shorthand (`*`, `+`, `?`, ...) into its canonical
      `counted_quantifier`. */
  function quant_canonicalize(q: quantifier): counted_quantifier {
    match q
    case Star => CountedQuant(0, None, true)
    case LazyStar => CountedQuant(0, None, false)
    case Plus => CountedQuant(1, None, true)
    case LazyPlus => CountedQuant(1, None, false)
    case QuestionMark => CountedQuant(0, Some(1), true)
    case LazyQuestionMark => CountedQuant(0, Some(1), false)
  }

  // * Lookarounds
  /** The four lookaround flavours: `(?=…)`, `(?!…)`, `(?<=…)`, `(?<!…)`. */
  datatype lookaround = Lookahead | NegLookahead | Lookbehind | NegLookbehind

  // * Anchors (0-width assertions)
  /** Zero-width assertions: `$`, `^`, `\b`, `\B`. */
  datatype anchor = EndInput | BeginInput | WordBoundary | NonWordBoundary

  // * Character Characterizations
  /** A single-character pattern element: a literal `Char`, `Dot` (any
      character), a Perl `char_group` like `\w`, or a bracket `Class`/`NegClass`. */
  datatype character =
    | Char(c: char)            // a simple character
    | Dot                      // any character
    | Group(g: char_group)     // PERL character classes \s, \w...
    | Class(cl: char_class)    // a character class
    | NegClass(cl: char_class) // a negated character class

  // * Raw Regexes (before annotation)
  /** The unannotated regex AST produced by the `Parser`: capture groups,
      lookarounds, and quantifiers don't yet carry the unique ids that
      `annotate` assigns them.

      - `Raw_empty` — the empty pattern.
      - `Raw_character(rc)` — a single `character`.
      - `Raw_alt(ra1, ra2)` — `ra1 | ra2`.
      - `Raw_con(rc1, rc2)` — `rc1` followed by `rc2`.
      - `Raw_quant(rq, rqr)` — `rqr` repeated per quantifier shorthand `rq`.
      - `Raw_count(rcq, rcr)` — `rcr` repeated per general `{min,max}` count `rcq`.
      - `Raw_capture(rcap)` — a capturing group `( rcap )`.
      - `Raw_lookaround(rl, rlr)` — a lookaround `rl` around `rlr`.
      - `Raw_anchor(ranc)` — a zero-width anchor. */
  datatype raw_regex =
    | Raw_empty
    | Raw_character(rc: character)
    | Raw_alt(ra1: raw_regex, ra2: raw_regex)
    | Raw_con(rc1: raw_regex, rc2: raw_regex)
    | Raw_quant(rq: quantifier, rqr: raw_regex)
    | Raw_count(rcq: counted_quantifier, rcr: raw_regex)
    | Raw_capture(rcap: raw_regex)
    | Raw_lookaround(rl: lookaround, rlr: raw_regex)
    | Raw_anchor(ranc: anchor)

  // shortcuts for simpler ASTs
  /** A literal-character `raw_regex`. */
  function raw_char(x: char): raw_regex { Raw_character(Char(x)) }
  /** The `.` (any character) `raw_regex`. */
  const raw_dot: raw_regex := Raw_character(Dot)
  /** `r*` — greedy zero-or-more, as a `raw_regex`. */
  function raw_star(r: raw_regex): raw_regex { Raw_quant(Star, r) }
  /** `r+` — greedy one-or-more, as a `raw_regex`. */
  function raw_plus(r: raw_regex): raw_regex { Raw_quant(Plus, r) }
  /** `r?` — greedy optional, as a `raw_regex`. */
  function raw_qmark(r: raw_regex): raw_regex { Raw_quant(QuestionMark, r) }
  /** A Perl character-group (e.g. `\w`) `raw_regex`. */
  function raw_group(g: char_group): raw_regex { Raw_character(Group(g)) }
  /** A bracket class `[...]` `raw_regex`. */
  function raw_class(c: char_class): raw_regex { Raw_character(Class(c)) }
  /** A negated bracket class `[^...]` `raw_regex`. */
  function raw_neg_class(c: char_class): raw_regex { Raw_character(NegClass(c)) }

  // * Nullability: NonNullable / Context-Dependent / Context-Independent
  /** How a regex's ability to match the empty string can depend on context:
      `NonNullable` (never), `CDNullable` (context-dependent, e.g. an anchor
      or lookaround), or `CINullable` (always, regardless of context). */
  datatype nullability = NonNullable | CDNullable | CINullable

  // annotated identifiers
  /** A capture-group id, assigned by `annotate`. */
  type capture = int
  /** A lookaround id, assigned by `annotate`. */
  type lookid = int
  /** A quantifier id, assigned by `annotate`. */
  type quantid = int

  // * Annotated Regexes
  /** The annotated regex AST the `Compiler` consumes: like `raw_regex`, but
      every capture group (`Re_capture`), lookaround (`Re_lookaround`), and
      quantifier (`Re_quant`) carries a unique id, and each quantifier has been
      canonicalized to a `counted_quantifier` and cached its `nullability`.
      Produced from a `raw_regex` by `annotate`. */
  datatype regex =
    | Re_empty
    | Re_character(ec: character)
    | Re_alt(e1: regex, e2: regex)
    | Re_con(c1: regex, c2: regex)
    // each quantifier gets a unique id; all turned into counted quantifiers
    | Re_quant(qnul: nullability, qid: quantid, quant: counted_quantifier, qr: regex)
    | Re_capture(cid: capture, capr: regex)
    | Re_lookaround(lid: lookid, look: lookaround, lr: regex)
    | Re_anchor(anc: anchor)

  // * Computing Nullability
  /** Nullability of a disjunction `r1 | r2` given the nullability of each
      side. */
  function null_or(n1: nullability, n2: nullability): nullability {
    match n1
    case NonNullable => n2
    case CDNullable => (match n2 case CINullable => CINullable case _ => CDNullable)
    case CINullable => CINullable
  }

  /** Nullability of a concatenation `r1 r2` given the nullability of each
      part. */
  function null_and(n1: nullability, n2: nullability): nullability {
    match n1
    case NonNullable => NonNullable
    case CDNullable => (match n2 case NonNullable => NonNullable case _ => CDNullable)
    case CINullable => n2
  }

  /** Whether annotated regex `r` can match the empty string, and if so under
      what conditions (see `nullability`). */
  function nullable(r: regex): nullability
    decreases r
  {
    match r
    case Re_empty => CINullable
    case Re_character(_) => NonNullable
    case Re_alt(r1, r2) => null_or(nullable(r1), nullable(r2))
    case Re_con(r1, r2) => null_and(nullable(r1), nullable(r2))
    case Re_quant(_, _, q, r1) => if q.min == 0 then CINullable else nullable(r1)
    case Re_capture(_, r1) => nullable(r1)
    case Re_lookaround(_, _, _) => CDNullable
    case Re_anchor(_) => CDNullable
  }

  /** Same as `nullable`, computed directly on an unannotated `raw_regex`. */
  function raw_nullable(r: raw_regex): nullability
    decreases r
  {
    match r
    case Raw_empty => CINullable
    case Raw_character(_) => NonNullable
    case Raw_alt(r1, r2) => null_or(raw_nullable(r1), raw_nullable(r2))
    case Raw_con(r1, r2) => null_and(raw_nullable(r1), raw_nullable(r2))
    case Raw_quant(q, r1) =>
      (match q
       case Star => CINullable
       case LazyStar => CINullable
       case QuestionMark => CINullable
       case LazyQuestionMark => CINullable
       case Plus => raw_nullable(r1)
       case LazyPlus => raw_nullable(r1))
    case Raw_count(q, r1) => if q.min == 0 then CINullable else raw_nullable(r1)
    case Raw_capture(r1) => raw_nullable(r1)
    case Raw_lookaround(_, _) => CDNullable
    case Raw_anchor(_) => CDNullable
  }

  // * Annotating Regexes
  // adds identifiers for each capture group / lookaround / quantifier,
  // returning the next fresh ids; also canonicalizes every quantifier.
  /** Annotates `ra`, assigning fresh capture/lookaround/quantifier ids
      starting at `c`/`l`/`q` (depth-first, left to right) and canonicalizing
      every quantifier; returns the annotated `regex` along with the next
      fresh id of each kind. The workhorse behind `annotate`. */
  function annotate_regex(ra: raw_regex, c: capture, l: lookid, q: quantid)
    : (regex, capture, lookid, quantid)
    decreases ra
  {
    match ra
    case Raw_empty => (Re_empty, c, l, q)
    case Raw_character(r) => (Re_character(r), c, l, q)
    case Raw_alt(r1, r2) =>
      var (ar1, c1, l1, q1) := annotate_regex(r1, c, l, q);
      var (ar2, c2, l2, q2) := annotate_regex(r2, c1, l1, q1);
      (Re_alt(ar1, ar2), c2, l2, q2)
    case Raw_con(r1, r2) =>
      var (ar1, c1, l1, q1) := annotate_regex(r1, c, l, q);
      var (ar2, c2, l2, q2) := annotate_regex(r2, c1, l1, q1);
      (Re_con(ar1, ar2), c2, l2, q2)
    case Raw_quant(quant, r1) =>
      var (ar1, c1, l1, q1) := annotate_regex(r1, c, l, q + 1);
      (Re_quant(nullable(ar1), q, quant_canonicalize(quant), ar1), c1, l1, q1)
    case Raw_count(quant, r1) =>
      var (ar1, c1, l1, q1) := annotate_regex(r1, c, l, q + 1);
      (Re_quant(nullable(ar1), q, quant, ar1), c1, l1, q1)
    case Raw_capture(r1) =>
      var (ar1, c1, l1, q1) := annotate_regex(r1, c + 1, l, q);
      (Re_capture(c, ar1), c1, l1, q1)
    case Raw_lookaround(look, r1) =>
      var (ar1, c1, l1, q1) := annotate_regex(r1, c, l + 1, q);
      (Re_lookaround(l, look, ar1), c1, l1, q1)
    case Raw_anchor(a) => (Re_anchor(a), c, l, q)
  }

  // external capture group 0; lookarounds start at 1; quants start at 1.
  /** Annotates a parsed `raw_regex` into the `regex` the `Compiler` consumes,
      implicitly wrapping it in capture group 0 (the whole-match capture);
      lookaround and quantifier ids start at 1. */
  function annotate(ra: raw_regex): regex {
    annotate_regex(Raw_capture(ra), 0, 1, 1).0
  }

  // adds a .*? prefix so the match need not start at the beginning
  /** Prepends a non-greedy `.*?` to `r`, so the match is free to start
      anywhere in the input rather than only at position 0. */
  function lazy_prefix(r: regex): regex {
    Re_con(Re_quant(NonNullable, 0, CountedQuant(0, None, false), Re_character(Dot)), r)
  }

  // * Regex Manipulation

  // reversing a regex for backward execution (only concatenation is reversed)
  /** Reverses `r` for backward execution: swaps the order of every
      concatenation (`Re_con(r1, r2)` becomes `r2` then `r1`), leaving
      everything else structurally the same. Used to run lookbehinds. */
  function reverse_regex(r: regex): regex
    decreases r
  {
    match r
    case Re_empty => r
    case Re_character(_) => r
    case Re_alt(r1, r2) => Re_alt(reverse_regex(r1), reverse_regex(r2))
    case Re_con(r1, r2) => Re_con(reverse_regex(r2), reverse_regex(r1))
    case Re_quant(nul, qid, quant, r1) => Re_quant(nul, qid, quant, reverse_regex(r1))
    case Re_capture(cid, r1) => Re_capture(cid, reverse_regex(r1))
    case Re_lookaround(lid, look, r1) => Re_lookaround(lid, look, reverse_regex(r1))
    case Re_anchor(a) => Re_anchor(a)
  }

  // during oracle building we don't extract captures, so remove them
  /** Strips every `Re_capture` node out of `r` (dropping the group markers
      but keeping their content), since building the lookaround `Oracle`
      doesn't need capture information. */
  function remove_capture(r: regex): regex
    decreases r
  {
    match r
    case Re_empty => r
    case Re_character(_) => r
    case Re_anchor(_) => r
    case Re_alt(r1, r2) => Re_alt(remove_capture(r1), remove_capture(r2))
    case Re_con(r1, r2) => Re_con(remove_capture(r1), remove_capture(r2))
    case Re_quant(nul, qid, quant, r1) => Re_quant(nul, qid, quant, remove_capture(r1))
    case Re_capture(cid, r1) => remove_capture(r1) // removing the group entirely
    case Re_lookaround(lid, look, r1) => Re_lookaround(lid, look, remove_capture(r1))
  }

  // * Lookaround Manipulation
  /** Finds the `Re_lookaround` node in `r` with id `lid`, returning its body
      and `lookaround` flavour, or `None` if no such id occurs. */
  function get_lookaround(r: regex, lid: lookid): Option<(regex, lookaround)>
    decreases r
  {
    match r
    case Re_empty => None
    case Re_character(_) => None
    case Re_anchor(_) => None
    case Re_alt(r1, r2) =>
      (match get_lookaround(r1, lid) case Some(le) => Some(le) case None => get_lookaround(r2, lid))
    case Re_con(r1, r2) =>
      (match get_lookaround(r1, lid) case Some(le) => Some(le) case None => get_lookaround(r2, lid))
    case Re_quant(_, _, _, r1) => get_lookaround(r1, lid)
    case Re_capture(_, r1) => get_lookaround(r1, lid)
    case Re_lookaround(l, look, r1) =>
      if l == lid then Some((r1, look)) else get_lookaround(r1, lid)
  }

  // we should always find a lookaround in range
  /** Total variant of `get_lookaround`, for callers that already know `lid`
      occurs in `r` (as every id assigned by `annotate` does). */
  function get_look(r: regex, lid: lookid): (regex, lookaround)
    requires get_lookaround(r, lid).Some?
  {
    get_lookaround(r, lid).value
  }

  /** Finds the `Re_quant` node in `r` with id `qid`, returning its body and
      `counted_quantifier`, or `None` if no such id occurs. */
  function get_quantifier(r: regex, qid: quantid): Option<(regex, counted_quantifier)>
    decreases r
  {
    match r
    case Re_empty => None
    case Re_character(_) => None
    case Re_anchor(_) => None
    case Re_alt(r1, r2) =>
      (match get_quantifier(r1, qid) case Some(qr) => Some(qr) case None => get_quantifier(r2, qid))
    case Re_con(r1, r2) =>
      (match get_quantifier(r1, qid) case Some(qr) => Some(qr) case None => get_quantifier(r2, qid))
    case Re_lookaround(_, _, r1) => get_quantifier(r1, qid)
    case Re_capture(_, r1) => get_quantifier(r1, qid)
    case Re_quant(nul, id, quant, r1) =>
      if id == qid then Some((r1, quant)) else get_quantifier(r1, qid)
  }

  /** Total variant of `get_quantifier`, for callers that already know `qid`
      occurs in `r`. */
  function get_quant(r: regex, qid: quantid): (regex, counted_quantifier)
    requires get_quantifier(r, qid).Some?
  {
    get_quantifier(r, qid).value
  }

  function imax(a: int, b: int): int { if a > b then a else b }

  /** The largest lookaround id occurring in `r` (0 if it has none). */
  function max_lookaround(r: regex): lookid
    ensures max_lookaround(r) >= 0
    decreases r
  {
    match r
    case Re_empty => 0
    case Re_character(_) => 0
    case Re_anchor(_) => 0
    case Re_alt(r1, r2) => imax(max_lookaround(r1), max_lookaround(r2))
    case Re_con(r1, r2) => imax(max_lookaround(r1), max_lookaround(r2))
    case Re_quant(_, _, _, r1) => max_lookaround(r1)
    case Re_capture(_, r1) => max_lookaround(r1)
    case Re_lookaround(lid, look, r1) => imax(lid, max_lookaround(r1))
  }

  /** The largest capture-group id occurring in `r` (0 if it has none but the
      implicit whole-match group). */
  function max_group(r: regex): capture
    ensures max_group(r) >= 0
    decreases r
  {
    match r
    case Re_empty => 0
    case Re_character(_) => 0
    case Re_anchor(_) => 0
    case Re_alt(r1, r2) => imax(max_group(r1), max_group(r2))
    case Re_con(r1, r2) => imax(max_group(r1), max_group(r2))
    case Re_quant(_, _, _, r1) => max_group(r1)
    case Re_lookaround(_, _, r1) => max_group(r1)
    case Re_capture(cid, r1) => imax(cid, max_group(r1))
  }

  /** The largest quantifier id occurring in `r` (0 if it has none). */
  function max_quant(r: regex): quantid
    ensures max_quant(r) >= 0
    decreases r
  {
    match r
    case Re_empty => 0
    case Re_character(_) => 0
    case Re_anchor(_) => 0
    case Re_alt(r1, r2) => imax(max_quant(r1), max_quant(r2))
    case Re_con(r1, r2) => imax(max_quant(r1), max_quant(r2))
    case Re_lookaround(_, _, r1) => max_quant(r1)
    case Re_capture(_, r1) => max_quant(r1)
    case Re_quant(_, qid, _, r1) => imax(qid, max_quant(r1))
  }

  function reverse_seq<T>(s: seq<T>): seq<T>
    decreases |s|
  {
    if |s| == 0 then [] else reverse_seq(s[1..]) + [s[0]]
  }

  // nullable greedy plus quantifier ids (min>0, max=None, greedy)
  function nullable_plus_quantid'(r: regex, lq: seq<quantid>): seq<quantid>
    decreases r
  {
    match r
    case Re_empty => lq
    case Re_character(_) => lq
    case Re_anchor(_) => lq
    case Re_alt(r1, r2) => nullable_plus_quantid'(r2, nullable_plus_quantid'(r1, lq))
    case Re_con(r1, r2) => nullable_plus_quantid'(r2, nullable_plus_quantid'(r1, lq))
    case Re_lookaround(_, _, r1) => nullable_plus_quantid'(r1, lq)
    case Re_capture(_, r1) => nullable_plus_quantid'(r1, lq)
    case Re_quant(nul, qid, quant, r1) =>
      match nul
      case CDNullable =>
        if quant.min > 0 && quant.max == None && quant.greedy
        then nullable_plus_quantid'(r1, [qid] + lq)
        else nullable_plus_quantid'(r1, lq)
      case CINullable =>
        if quant.min > 0 && quant.max == None && quant.greedy
        then nullable_plus_quantid'(r1, [qid] + lq)
        else nullable_plus_quantid'(r1, lq)
      case NonNullable => nullable_plus_quantid'(r1, lq)
  }

  // ordered from lowest to highest
  /** The ids of every nullable, greedy, unbounded (`min>0, max=None`) `+`
      quantifier in `r`, ordered from lowest to highest id. */
  function nullable_plus_quantid(r: regex): seq<quantid> {
    reverse_seq(nullable_plus_quantid'(r, []))
  }

  // all CDN plus, ordered from highest to lowest
  function cdn_plus_list'(r: regex, lq: seq<quantid>): seq<quantid>
    decreases r
  {
    match r
    case Re_empty => lq
    case Re_character(_) => lq
    case Re_anchor(_) => lq
    case Re_alt(r1, r2) => cdn_plus_list'(r2, cdn_plus_list'(r1, lq))
    case Re_con(r1, r2) => cdn_plus_list'(r2, cdn_plus_list'(r1, lq))
    case Re_lookaround(_, _, r1) => cdn_plus_list'(r1, lq)
    case Re_capture(_, r1) => cdn_plus_list'(r1, lq)
    case Re_quant(nul, qid, quant, r1) =>
      if nul == CDNullable && quant.min > 0 && quant.max == None && quant.greedy
      then cdn_plus_list'(r1, [qid] + lq)
      else cdn_plus_list'(r1, lq)
  }

  /** The ids of every context-dependent-nullable (`CDNullable`), greedy,
      unbounded `+` quantifier in `r`, ordered from highest to lowest id. */
  function cdn_plus_list(r: regex): seq<quantid> {
    cdn_plus_list'(r, [])
  }

  // * Regex Well-Formedness
  predicate char_wf(c: char) { c as int < 128 }

  predicate class_elt_wf(e: char_class_elt) {
    match e
    case CChar(c) => char_wf(c)
    case CGroup(_) => true
    case CRange(c1, c2) => c1 <= c2
  }

  predicate class_wf(cl: char_class)
    decreases |cl|
  {
    if |cl| == 0 then true else class_elt_wf(cl[0]) && class_wf(cl[1..])
  }

  /** Well-formedness of a parsed `raw_regex`: every literal character is
      ASCII (`char_wf`), every counted repetition's range is non-empty
      (`min <= max`), and every character class's ranges are properly ordered. */
  predicate regex_wf(r: raw_regex)
    decreases r
  {
    match r
    case Raw_empty => true
    case Raw_anchor(_) => true
    case Raw_alt(r1, r2) => regex_wf(r1) && regex_wf(r2)
    case Raw_con(r1, r2) => regex_wf(r1) && regex_wf(r2)
    case Raw_quant(_, r1) => regex_wf(r1)
    case Raw_capture(r1) => regex_wf(r1)
    case Raw_lookaround(_, r1) => regex_wf(r1)
    case Raw_count(c, r1) =>
      var ok_range := (match c.max case None => true case Some(m) => c.min <= m);
      ok_range && regex_wf(r1)
    case Raw_character(c) =>
      match c
      case Char(ch) => char_wf(ch)
      case Dot => true
      case Group(_) => true
      case Class(cl) => class_wf(cl)
      case NegClass(cl) => class_wf(cl)
  }
}
