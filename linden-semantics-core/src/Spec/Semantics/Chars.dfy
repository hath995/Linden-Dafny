// Mirror of Semantics/Chars.v.
// Characters and strings. In Coq this section is parameterized by `rer: RegExpRecord`; here `rer`
// is threaded as an explicit parameter to the functions that need it. String := seq<char>.

/** Characters, strings, and the current-position `Input`, plus reading a character against a
    `CharDescr` (the compiled form of a character class). The building blocks `Semantics.IsTree`
    uses to advance through the string. */
module Chars {
  import opened Std.Wrappers
  import opened WarblreRegExpRecord
  import opened WarblrePrimitives

  type String = seq<char>

  // ----- small seq helpers (Coq List.rev / firstn / skipn, total versions) -----
  function Reverse<T>(s: seq<T>): seq<T> {
    if |s| == 0 then [] else Reverse(s[1..]) + [s[0]]
  }
  // Coq List.firstn: truncates when n > |s|.
  /** The first `n` elements of `s`, or all of `s` if it's shorter than `n`. */
  function Take<T>(s: seq<T>, n: nat): seq<T> {
    if n <= |s| then s[..n] else s
  }
  // Coq List.skipn: empty when n > |s|.
  /** `s` with its first `n` elements dropped, or `[]` if it's shorter than `n`. */
  function Drop<T>(s: seq<T>, n: nat): seq<T> {
    if n <= |s| then s[n..] else []
  }

  // ----- input -----
  // Coq: Inductive input := Input (next: string) (pref: string).
  // `next` = chars still to read; `pref` = reversed list of already-read chars.
  /** The current scanning position within a string, as a zipper: `next` holds the characters
      still ahead, and `pref` holds the already-read characters in reverse order. Matching
      advances by moving one character between `next` and `pref` (see `AdvanceInput`). */
  datatype Input = Input(next: String, pref: String)

  // Coq: idx inp := length pref.
  /** The 0-based offset of `inp` into the original string (how many characters have been read). */
  function Idx(inp: Input): nat { |inp.pref| }

  // Coq: next_str
  function NextStr(i: Input): String { i.next }

  // Coq: current_str i dir
  /** The characters ahead of `i` in scanning direction `dir` — `next` when going `Forward`,
      `pref` when going `Backward`. */
  function CurrentStr(i: Input, dir: Direction): String {
    match dir case Forward => i.next case Backward => i.pref
  }

  // Coq: remaining_length inp dir
  /** How many characters remain to be read from `inp` in direction `dir`. */
  function RemainingLength(inp: Input, dir: Direction): nat {
    match dir case Forward => |inp.next| case Backward => |inp.pref|
  }

  // Coq: input_str i := rev pref ++ next
  /** Reconstructs the whole original string from `i` (already-read prefix, un-reversed, followed
      by what's left). */
  function InputStr(i: Input): String { Reverse(i.pref) + i.next }

  // Coq: substr inp startIdx endIdx := firstn (endIdx-startIdx) (skipn startIdx (input_str inp))
  /** The substring of `inp`'s original string from `startIdx` to `endIdx` (used to read back a
      capture group's text, e.g. for a `Backreference`). */
  function Substr(inp: Input, startIdx: nat, endIdx: nat): String {
    Take(Drop(InputStr(inp), startIdx), if endIdx >= startIdx then endIdx - startIdx else 0)
  }

  // Coq: init_input str := Input str []
  /** The starting `Input` for matching against `str`: nothing read yet. */
  function InitInput(str: String): Input { Input(str, []) }

  // Coq: Inductive input_compat: input -> string -> Prop.
  /** Whether `i` is a valid position within `str0` — i.e. `i`'s read and unread parts
      reassemble exactly into `str0`. */
  predicate InputCompat(i: Input, str0: String) {
    Reverse(i.pref) + i.next == str0
  }

  // ----- canonicalized membership -----
  // Coq: inb_canonicalized c l := inb (canonicalize c) (map canonicalize l).
  /** `l` with every character case-folded via `Canonicalize`. */
  function MapCanon(rer: RegExpRecord, l: seq<char>): seq<char> {
    if |l| == 0 then [] else [Canonicalize(rer, l[0])] + MapCanon(rer, l[1..])
  }
  /** Whether `c`'s canonical form occurs among `l`'s canonicalized characters — membership
      that respects the `i` flag. */
  predicate InbCanonicalized(rer: RegExpRecord, c: char, l: seq<char>) {
    Canonicalize(rer, c) in MapCanon(rer, l)
  }

  /** Without the `i` flag, canonicalizing every character of `l` changes nothing. */
  lemma MapCanonicalizeCaseSensitive(rer: RegExpRecord, l: seq<char>)
    requires !rer.ignoreCase
    ensures MapCanon(rer, l) == l
  {
    if |l| == 0 {
    } else {
      CanonicalizeCaseSensitive(rer, l[0]);
      MapCanonicalizeCaseSensitive(rer, l[1..]);
    }
  }

  /** Without the `i` flag, `InbCanonicalized` reduces to plain membership `c in l`. */
  lemma InbCanonicalizedCaseSensitive(rer: RegExpRecord, c: char, l: seq<char>)
    requires !rer.ignoreCase
    ensures InbCanonicalized(rer, c, l) <==> (c in l)
  {
    CanonicalizeCaseSensitive(rer, c);
    MapCanonicalizeCaseSensitive(rer, l);
  }

  // Coq: wordCharacters rer (naive: ascii word characters).
  function WordCharactersOf(rer: RegExpRecord): CharSet { WordCharacters(rer) }

  // Coq: word_char c := contains (wordCharacters rer) c.
  /** Whether `c` counts as a word character under `rer`'s flags — the test behind `\b`/`\B`. */
  predicate WordChar(rer: RegExpRecord, c: char) { Contains(WordCharactersOf(rer), c) }

  // ----- character descriptors -----
  // Coq: Inductive char_descr.
  /** The compiled form of a character class, as it appears in `Regex.Character(cd)`: a literal
      character, a built-in class (`\d`, `\s`, `\w`, `.`, a Unicode property), a negation
      (`CdInv`), a range (`CdRange`, e.g. `[a-z]`), or a union (`CdUnion`, e.g. `[a-zA-Z0-9]`).
      Matched against an actual character by `CharMatch`. */
  datatype CharDescr =
    | CdEmpty
    | CdDot
    | CdAll
    | CdSingle(c: char)
    | CdDigits
    | CdNonDigits
    | CdWhitespace
    | CdNonWhitespace
    | CdWordChar
    | CdNonWordChar
    | CdUnicodeProp(p: Property)
    | CdNonUnicodeProp(p: Property)
    | CdInv(cd: CharDescr)
    | CdRange(l: char, h: char)
    | CdUnion(cd1: CharDescr, cd2: CharDescr)

  // Coq: dot_matches dotAll c
  /** Whether `.` matches `c`: any character under `dotAll`, otherwise any character except a
      line terminator. */
  predicate DotMatches(rer: RegExpRecord, dotAll: bool, c: char) {
    if dotAll then ExistCanonicalized(rer, AllChars(), c)
    else ExistCanonicalized(rer, RemoveAll(AllChars(), LineTerminators()), c)
  }

  // Coq: Fixpoint char_match' ccan cd
  /** Whether the already-canonicalized character `ccan` matches descriptor `cd`, recursing
      through unions/negations/ranges. Called by `CharMatch`, which does the canonicalizing. */
  predicate CharMatchPrime(rer: RegExpRecord, ccan: char, cd: CharDescr)
    decreases cd
  {
    match cd
    case CdEmpty => false
    case CdDot => DotMatches(rer, rer.dotAll, ccan)
    case CdAll => true
    case CdSingle(c') => ccan == Canonicalize(rer, c')
    case CdDigits => ExistCanonicalized(rer, Digits(), ccan)
    case CdNonDigits => ExistCanonicalized(rer, RemoveAll(AllChars(), Digits()), ccan)
    case CdWhitespace => ExistCanonicalized(rer, Union(WhiteSpaces(), LineTerminators()), ccan)
    case CdNonWhitespace => ExistCanonicalized(rer, RemoveAll(AllChars(), Union(WhiteSpaces(), LineTerminators())), ccan)
    case CdWordChar => ExistCanonicalized(rer, WordCharactersOf(rer), ccan)
    case CdNonWordChar => ExistCanonicalized(rer, RemoveAll(AllChars(), WordCharactersOf(rer)), ccan)
    case CdUnicodeProp(p) => ExistCanonicalized(rer, FromList(CodePointsFor(p)), ccan)
    case CdNonUnicodeProp(p) => ExistCanonicalized(rer, RemoveAll(AllChars(), FromList(CodePointsFor(p))), ccan)
    case CdInv(cd') => !CharMatchPrime(rer, ccan, cd')
    case CdRange(l, h) =>
      var charSet := Range(FromNumericValue(NumericValue(l)), FromNumericValue(NumericValue(h)));
      ExistCanonicalized(rer, charSet, ccan)
    case CdUnion(cd1, cd2) => CharMatchPrime(rer, ccan, cd1) || CharMatchPrime(rer, ccan, cd2)
  }

  // Coq: char_match c cd := char_match' (canonicalize c) cd.
  /** Whether character `c` matches descriptor `cd` (case-folding `c` first per `rer`'s flags).
      The semantic meaning of `Regex.Character(cd)`. */
  predicate CharMatch(rer: RegExpRecord, c: char, cd: CharDescr) {
    CharMatchPrime(rer, Canonicalize(rer, c), cd)
  }

  /** `CdSingle(c2)` matches `c1` exactly when they canonicalize to the same character. */
  lemma SingleMatch(rer: RegExpRecord, c1: char, c2: char)
    ensures CharMatch(rer, c1, CdSingle(c2)) <==> Canonicalize(rer, c1) == Canonicalize(rer, c2)
  {}

  // ----- reading characters -----
  // Coq: read_char cd i dir : option (Character * input)
  /** Reads one character from `i` in direction `dir` if it matches `cd`, returning the character
      read and the advanced `Input`; `None` if there's nothing to read or it doesn't match.
      The primitive `Read` step of `Semantics.IsTree`. */
  function ReadChar(rer: RegExpRecord, cd: CharDescr, i: Input, dir: Direction): Option<(char, Input)> {
    match dir
    case Forward =>
      if |i.next| == 0 then None
      else if CharMatch(rer, i.next[0], cd)
           then Some((i.next[0], Input(i.next[1..], [i.next[0]] + i.pref)))
           else None
    case Backward =>
      if |i.pref| == 0 then None
      else if CharMatch(rer, i.pref[0], cd)
           then Some((i.pref[0], Input([i.pref[0]] + i.next, i.pref[1..])))
           else None
  }

  // Coq: Inductive ReadResult := CanRead | CannotRead.
  /** The outcome of `CheckRead`: whether a character can be read (input non-empty and matching)
      without actually reading it. */
  datatype ReadResult = CanRead | CannotRead

  // Coq: check_read cd i dir
  /** Whether a character matching `cd` could be read from `i` in direction `dir`, without
      producing the resulting `Input` (see `ReadChar`/`AdvanceInput` for that). */
  function CheckRead(rer: RegExpRecord, cd: CharDescr, i: Input, dir: Direction): ReadResult {
    match dir
    case Forward =>
      if |i.next| == 0 then CannotRead
      else if CharMatch(rer, i.next[0], cd) then CanRead else CannotRead
    case Backward =>
      if |i.pref| == 0 then CannotRead
      else if CharMatch(rer, i.pref[0], cd) then CanRead else CannotRead
  }

  // Coq: advance_input i dir : option input
  /** Moves `i` one character in direction `dir` (from `next` to `pref`, or vice versa);
      `None` if there is nothing left to move. */
  function AdvanceInput(i: Input, dir: Direction): Option<Input> {
    match dir
    case Forward =>
      if |i.next| == 0 then None
      else Some(Input(i.next[1..], [i.next[0]] + i.pref))
    case Backward =>
      if |i.pref| == 0 then None
      else Some(Input([i.pref[0]] + i.next, i.pref[1..]))
  }

  // Coq: advance_input' i dir
  /** Total version of `AdvanceInput`: advances `i` one character, or leaves it unchanged if
      there's nothing left to advance over. */
  function AdvanceInputP(i: Input, dir: Direction): Input {
    match AdvanceInput(i, dir) case Some(nextinp) => nextinp case None => i
  }

  /** When `AdvanceInput` succeeds, `AdvanceInputP` agrees with it. */
  lemma AdvanceInputSuccess(i: Input, dir: Direction, nexti: Input)
    requires AdvanceInput(i, dir) == Some(nexti)
    ensures AdvanceInputP(i, dir) == nexti
  {}

  // Coq: advance_input_n i n dir
  /** Advances `i` by `n` characters in direction `dir` in one step (used to jump straight to a
      captured group's end/start position). */
  function AdvanceInputN(i: Input, n: nat, dir: Direction): Input {
    match dir
    case Forward => Input(Drop(i.next, n), Reverse(Take(i.next, n)) + i.pref)
    case Backward => Input(Reverse(Take(i.pref, n)) + i.next, Drop(i.pref, n))
  }

  // Coq: can_read_correct
  /** `ReadChar` succeeds landing on `i2` exactly when `CheckRead` says `CanRead` and advancing
      `i1` lands on `i2` — i.e. `ReadChar` is `CheckRead` + `AdvanceInput` fused together. */
  lemma CanReadCorrect(i1: Input, rer: RegExpRecord, cd: CharDescr, dir: Direction, i2: Input)
    ensures (exists c :: ReadChar(rer, cd, i1, dir) == Some((c, i2)))
         <==> (CheckRead(rer, cd, i1, dir) == CanRead && AdvanceInput(i1, dir) == Some(i2))
  {
    if CheckRead(rer, cd, i1, dir) == CanRead && AdvanceInput(i1, dir) == Some(i2) {
      match dir
      case Forward => assert ReadChar(rer, cd, i1, dir) == Some((i1.next[0], i2));
      case Backward => assert ReadChar(rer, cd, i1, dir) == Some((i1.pref[0], i2));
    }
  }

  // Coq: read_char_success_advance
  /** Whenever `ReadChar` succeeds, its resulting `Input` is what `AdvanceInput` gives. */
  lemma ReadCharSuccessAdvance(rer: RegExpRecord, cd: CharDescr, inp: Input, dir: Direction, c: char, nextinp: Input)
    requires ReadChar(rer, cd, inp, dir) == Some((c, nextinp))
    ensures AdvanceInput(inp, dir) == Some(nextinp)
  {}

  // Coq: cannot_read_correct
  /** `ReadChar` fails exactly when `CheckRead` says `CannotRead`. */
  lemma CannotReadCorrect(i: Input, rer: RegExpRecord, cd: CharDescr, dir: Direction)
    ensures (ReadChar(rer, cd, i, dir) == None) <==> (CheckRead(rer, cd, i, dir) == CannotRead)
  {}

  // Coq: Inductive next_input i1 i2 dir := advance_input i1 dir = Some i2.
  /** Whether `i2` is exactly `i1` advanced by one character in direction `dir`. */
  predicate NextInput(i1: Input, i2: Input, dir: Direction) {
    AdvanceInput(i1, dir) == Some(i2)
  }
}
