// Port of parser_src/regex_lexer.mll + regex_parser.mly.
// An ECMA-262-style regex-string parser producing a raw_regex, built with the
// Dafny standard library's Std.Parsers combinators. The OCaml version is a
// menhir LR grammar over a lexer; here we parse the character stream directly
// with PEG-style combinators (ordered choice). The grammar's only recursion is
// through groups `( disjunction )`, so a single `Recursive` suffices.
//
// Limitations (mirroring the OCaml "Unsupported_*" exceptions, but here the
// unsupported escapes \x \u \k \p \P and \<digit> are parsed as identity escapes
// rather than raising; named groups / unicode / backrefs remain unsupported).
/** An ECMA-262-style regex-string parser, producing a `raw_regex` (the
    `RegElkRegex` AST before annotation), built with `Std.Parsers`
    PEG-style combinators; the only recursion is through parenthesized
    groups. Unsupported escapes (`\x`, `\u`, `\k`, `\p`, `\P`, `\<digit>`)
    are parsed as identity escapes rather than rejected; named groups,
    unicode, and backreferences remain unsupported. */
module Parser {
  import opened Std.Wrappers
  import opened Charclasses
  import opened RegElkRegex
  import SB = Std.Parsers.StringBuilders

  /** A parser combinator producing an `R` on success. */
  type P<R> = SB.B<R>

  /** A parser that matches exactly the character `c`. */
  function lit(c: char): P<char> {
    SB.CharTest((x: char) => x == c, [c])
  }

  // patterncharacter: any char that isn't a regex metacharacter
  /** Parses a single literal pattern character: anything that isn't one of
      the regex metacharacters `^$\.*+?()[]|`. */
  function pchar(): P<raw_regex> {
    SB.CharTest((c: char) => c !in "^$\\.*+?()[]|", "patternchar")
      .Map(c => Raw_character(Char(c)))
  }

  // escape sequence following a backslash in atom position
  /** Parses the escape sequence after a backslash in atom position: the
      `\d\D\s\S\w\W` character-group shorthands, the control escapes
      `\f\n\r\t\v\0`, or (as an identity escape) any other character
      literally. */
  function atomescapeP(): P<raw_regex> {
    SB.O([
      lit('d').Map(_ => Raw_character(Group(Digit))),
      lit('D').Map(_ => Raw_character(Group(NonDigit))),
      lit('s').Map(_ => Raw_character(Group(Space))),
      lit('S').Map(_ => Raw_character(Group(NonSpace))),
      lit('w').Map(_ => Raw_character(Group(Word))),
      lit('W').Map(_ => Raw_character(Group(NonWord))),
      lit('f').Map(_ => Raw_character(Char(12 as char))),
      lit('n').Map(_ => Raw_character(Char('\n'))),
      lit('r').Map(_ => Raw_character(Char('\r'))),
      lit('t').Map(_ => Raw_character(Char('\t'))),
      lit('v').Map(_ => Raw_character(Char(11 as char))),
      lit('0').Map(_ => Raw_character(Char(0 as char))),
      SB.CharTest((c: char) => true, "escaped char").Map(c => Raw_character(Char(c)))
    ])
  }

  // a class escape (after backslash, inside [ ])
  /** Parses a class escape (after `\` inside `[...]`): the `\d\D\s\S\w\W`
      group shorthands, the control escapes, or (as an identity escape) any
      other character as a literal `CChar`. */
  function classEsc(): P<char_class_elt> {
    lit('\\').ConcatKeepRight(SB.O([
      lit('d').Map(_ => CGroup(Digit)),
      lit('D').Map(_ => CGroup(NonDigit)),
      lit('s').Map(_ => CGroup(Space)),
      lit('S').Map(_ => CGroup(NonSpace)),
      lit('w').Map(_ => CGroup(Word)),
      lit('W').Map(_ => CGroup(NonWord)),
      lit('b').Map(_ => CChar(8 as char)),   // backspace
      lit('f').Map(_ => CChar(12 as char)),
      lit('n').Map(_ => CChar('\n')),
      lit('r').Map(_ => CChar('\r')),
      lit('t').Map(_ => CChar('\t')),
      lit('v').Map(_ => CChar(11 as char)),
      lit('0').Map(_ => CChar(0 as char)),
      SB.CharTest((c: char) => true, "escaped char").Map(c => CChar(c))
    ]))
  }

  // a class atom that is not a dash (\esc or a plain char other than ] \ -)
  /** Parses one bracket-class atom that isn't a bare `-`: either a
      `classEsc()` escape or any literal character other than `]`, `\`, `-`. */
  function catomND(): P<char_class_elt> {
    SB.O([
      classEsc(),
      SB.CharTest((c: char) => c != ']' && c != '\\' && c != '-', "classchar").Map(c => CChar(c))
    ])
  }

  function flatten(items: seq<char_class>): char_class
    decreases |items|
  {
    if |items| == 0 then [] else items[0] + flatten(items[1..])
  }

  /** Parses the contents of a bracket expression `[...]`/`[^...]`: a sequence
      of `catomND-catomND` ranges, lone atoms, or literal `-`s, flattened into
      a `char_class`. */
  function classcontents(): P<char_class> {
    var rangeItem := catomND().Concat(lit('-').ConcatKeepRight(catomND()))
                       .Map((p: (char_class_elt, char_class_elt)) => make_range(p.0, p.1));
    var atomItem := SB.O([
      catomND().Map((e: char_class_elt) => [e]),
      lit('-').Map(_ => [CChar('-')])
    ]);
    var item := SB.O([rangeItem.FailureResetsInput(), atomItem]);
    item.Rep().Map((items: seq<char_class>) => flatten(items))
  }

  /** Parses a full bracket expression, `[^...]` (negated) or `[...]` (plain),
      into a `Raw_character(NegClass ...)` / `Raw_character(Class ...)`. */
  function classParser(): P<raw_regex> {
    SB.O([
      SB.S("[^").ConcatKeepRight(classcontents()).ConcatKeepLeft(lit(']'))
        .Map((c: char_class) => Raw_character(NegClass(c))),
      lit('[').ConcatKeepRight(classcontents()).ConcatKeepLeft(lit(']'))
        .Map((c: char_class) => Raw_character(Class(c)))
    ])
  }

  // term-level anchors
  /** Parses a term-level zero-width anchor: `^`, `$`, `\b`, `\B`. */
  function anchors(): P<raw_regex> {
    SB.O([
      lit('^').Map(_ => Raw_anchor(BeginInput)),
      lit('$').Map(_ => Raw_anchor(EndInput)),
      SB.S("\\b").Map(_ => Raw_anchor(WordBoundary)),
      SB.S("\\B").Map(_ => Raw_anchor(NonWordBoundary))
    ])
  }

  /** Parses a general counted-repetition suffix `{n}`, `{n,}`, or `{n,m}`,
      with an optional trailing `?` for non-greedy. */
  function countedQuant(): P<counted_quantifier> {
    lit('{').ConcatKeepRight(SB.Nat)
      .Concat(lit(',').ConcatKeepRight(SB.Nat.Option()).Option())
      .ConcatKeepLeft(lit('}'))
      .Concat(lit('?').Option())
      .Map((p: ((nat, Option<Option<nat>>), Option<char>)) =>
        var mn := p.0.0;
        var commaOpt := p.0.1;
        var greedy := p.1.None?;
        match commaOpt
        case None => CountedQuant(mn, Some(mn), greedy)        // {n}
        case Some(None) => CountedQuant(mn, None, greedy)      // {n,}
        case Some(Some(mx)) => CountedQuant(mn, Some(mx), greedy)) // {n,mx}
  }

  // a quantifier suffix: a function transforming the preceding atom
  /** Parses any quantifier suffix (`*`, `*?`, `+`, `+?`, `?`, `??`, or a
      `countedQuant`) as a function that wraps a preceding atom in the
      corresponding `Raw_quant`/`Raw_count`. */
  function quantSuffix(): P<raw_regex -> raw_regex> {
    SB.O([
      SB.S("*?").Map(_ => (a: raw_regex) => Raw_quant(LazyStar, a)),
      lit('*').Map(_ => (a: raw_regex) => Raw_quant(Star, a)),
      SB.S("+?").Map(_ => (a: raw_regex) => Raw_quant(LazyPlus, a)),
      lit('+').Map(_ => (a: raw_regex) => Raw_quant(Plus, a)),
      SB.S("??").Map(_ => (a: raw_regex) => Raw_quant(LazyQuestionMark, a)),
      lit('?').Map(_ => (a: raw_regex) => Raw_quant(QuestionMark, a)),
      countedQuant().Map((cq: counted_quantifier) => (a: raw_regex) => Raw_count(cq, a))
    ])
  }

  /** Left-folds a sequence of terms into a right-nested `Raw_con` chain (or
      `Raw_empty` for an empty sequence) — how consecutive terms in an
      alternative are concatenated. */
  function foldcon(ts: seq<raw_regex>): raw_regex
    decreases |ts|
  {
    if |ts| == 0 then Raw_empty
    else if |ts| == 1 then ts[0]
    else Raw_con(foldcon(ts[..|ts| - 1]), ts[|ts| - 1])
  }

  /** Right-folds a sequence of alternatives into a `Raw_alt` chain (or
      `Raw_empty` for an empty sequence) — how `a|b|c` is built. */
  function foldalt(ts: seq<raw_regex>): raw_regex
    decreases |ts|
  {
    if |ts| == 0 then Raw_empty
    else if |ts| == 1 then ts[0]
    else Raw_alt(ts[0], foldalt(ts[1..]))
  }

  /** The full regex grammar: groups (plain, non-capturing `(?:...)`,
      lookarounds), atoms (`.`, escapes, classes, literal chars), quantifier
      suffixes, concatenation, and `|`-disjunction, tied together with a
      single `Recursive` for parenthesized groups. */
  function regexParser(): P<raw_regex> {
    SB.Recursive((disj: P<raw_regex>) =>
      var grp := SB.O([
        SB.S("(?:").ConcatKeepRight(disj).ConcatKeepLeft(lit(')')),
        lit('(').ConcatKeepRight(disj).ConcatKeepLeft(lit(')')).Map(d => Raw_capture(d))
      ]);
      var look := SB.O([
        SB.S("(?=").ConcatKeepRight(disj).ConcatKeepLeft(lit(')')).Map(d => Raw_lookaround(Lookahead, d)),
        SB.S("(?!").ConcatKeepRight(disj).ConcatKeepLeft(lit(')')).Map(d => Raw_lookaround(NegLookahead, d)),
        SB.S("(?<=").ConcatKeepRight(disj).ConcatKeepLeft(lit(')')).Map(d => Raw_lookaround(Lookbehind, d)),
        SB.S("(?<!").ConcatKeepRight(disj).ConcatKeepLeft(lit(')')).Map(d => Raw_lookaround(NegLookbehind, d))
      ]);
      var atom := SB.O([
        grp,
        lit('.').Map(_ => Raw_character(Dot)),
        lit('\\').ConcatKeepRight(atomescapeP()),
        classParser(),
        pchar()
      ]);
      var atomTerm := atom.Concat(quantSuffix().Option())
        .Map((p: (raw_regex, Option<raw_regex -> raw_regex>)) =>
          match p.1 case None => p.0 case Some(f) => f(p.0));
      var term := SB.O([anchors(), look, atomTerm]);
      var alternative := term.Rep().Map(foldcon);
      var disjunction := alternative.RepSep(lit('|')).Map(foldalt);
      disjunction
    ).End()
  }

  // top-level: parse a regex string into a raw_regex (None on parse failure)
  /** Parses regex string `s` into a `raw_regex`, or `None` if it doesn't
      match the grammar. The top-level entry point of this module. */
  function parse(s: string): Option<raw_regex> {
    var res := SB.Apply(regexParser(), s);
    if res.ParseSuccess? then Some(res.result) else None
  }
}
