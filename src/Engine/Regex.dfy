// Port of regex.ml
// The type of regexes we match, including capture groups and lookarounds,
// plus annotation, nullability analysis, and AST manipulation helpers.
module RegElkRegex {
  import opened Std.Wrappers
  import opened Charclasses

  // * Quantifiers
  // all of these can be compiled for regex-linear matching, except LazyPlus
  datatype quantifier =
    | Star | LazyStar | Plus | LazyPlus | QuestionMark | LazyQuestionMark

  // generic quantifier type, for (possibly non-linear) counted repetition.
  // max = None represents infinity.
  datatype counted_quantifier = CountedQuant(min: int, max: Option<int>, greedy: bool)

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
  datatype lookaround = Lookahead | NegLookahead | Lookbehind | NegLookbehind

  // * Anchors (0-width assertions)
  datatype anchor = EndInput | BeginInput | WordBoundary | NonWordBoundary

  // * Character Characterizations
  datatype character =
    | Char(c: char)            // a simple character
    | Dot                      // any character
    | Group(g: char_group)     // PERL character classes \s, \w...
    | Class(cl: char_class)    // a character class
    | NegClass(cl: char_class) // a negated character class

  // * Raw Regexes (before annotation)
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
  function raw_char(x: char): raw_regex { Raw_character(Char(x)) }
  const raw_dot: raw_regex := Raw_character(Dot)
  function raw_star(r: raw_regex): raw_regex { Raw_quant(Star, r) }
  function raw_plus(r: raw_regex): raw_regex { Raw_quant(Plus, r) }
  function raw_qmark(r: raw_regex): raw_regex { Raw_quant(QuestionMark, r) }
  function raw_group(g: char_group): raw_regex { Raw_character(Group(g)) }
  function raw_class(c: char_class): raw_regex { Raw_character(Class(c)) }
  function raw_neg_class(c: char_class): raw_regex { Raw_character(NegClass(c)) }

  // * Nullability: NonNullable / Context-Dependent / Context-Independent
  datatype nullability = NonNullable | CDNullable | CINullable

  // annotated identifiers
  type capture = int
  type lookid = int
  type quantid = int

  // * Annotated Regexes
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
  function null_or(n1: nullability, n2: nullability): nullability {
    match n1
    case NonNullable => n2
    case CDNullable => (match n2 case CINullable => CINullable case _ => CDNullable)
    case CINullable => CINullable
  }

  function null_and(n1: nullability, n2: nullability): nullability {
    match n1
    case NonNullable => NonNullable
    case CDNullable => (match n2 case NonNullable => NonNullable case _ => CDNullable)
    case CINullable => n2
  }

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
  function annotate(ra: raw_regex): regex {
    annotate_regex(Raw_capture(ra), 0, 1, 1).0
  }

  // adds a .*? prefix so the match need not start at the beginning
  function lazy_prefix(r: regex): regex {
    Re_con(Re_quant(NonNullable, 0, CountedQuant(0, None, false), Re_character(Dot)), r)
  }

  // * Regex Manipulation

  // reversing a regex for backward execution (only concatenation is reversed)
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
  function get_look(r: regex, lid: lookid): (regex, lookaround)
    requires get_lookaround(r, lid).Some?
  {
    get_lookaround(r, lid).value
  }

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

  function get_quant(r: regex, qid: quantid): (regex, counted_quantifier)
    requires get_quantifier(r, qid).Some?
  {
    get_quantifier(r, qid).value
  }

  function imax(a: int, b: int): int { if a > b then a else b }

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
