// Mirror of the Warblre Character / CharSet / Property primitives that Linden uses
// (Warblre/spec/Parameters.v), concretized to Dafny's native `char` per the porting plan:
//   Character := char,  CharSet := set<char>,  String := seq<char>.
// Canonicalize is kept ABSTRACT (opaque function + the case-sensitivity law as an axiom) so the
// development stays faithful to Warblre's parameterization over the case-folding function, while
// every other primitive is concrete and the CharSet spec-lemmas come for free from native sets.
include "RegExpRecord.dfy"
include "Numeric.dfy"

/** ECMAScript's `Character`/`CharSet`/`Property` primitives, concretized to Dafny's native
    `char`, `set<char>`, and `seq<char>`. `Canonicalize` (case-folding) stays abstract behind
    an opaque function plus the case-sensitivity law, so the rest of the development remains
    faithful to Warblre's parameterization over case-folding. */
module WarblrePrimitives {
  import opened WarblreRegExpRecord
  import opened WarblreNumeric

  // Warblre's Direction (re-exported by Linden as Direction).
  /** The scanning direction: `Forward` for ordinary matching, `Backward` for lookbehinds
      (see `Regex.LkDir`). */
  datatype Direction = Forward | Backward

  // ----- Character (= Dafny char) -----

  // Coq: Character.numeric_value : type -> nat.
  function NumericValue(c: char): nat { c as int }

  // A nat is a valid Unicode scalar value (the domain of Dafny `char`).
  /** Whether `n` is a valid Unicode scalar value — i.e. a legal `char` code point
      (excludes the surrogate range `0xD800..0xDFFF`). */
  predicate ValidCodePoint(n: nat) { n < 0x110000 && !(0xD800 <= n <= 0xDFFF) }

  // Coq: Character.from_numeric_value : nat -> type.
  function FromNumericValue(n: nat): char requires ValidCodePoint(n) { n as char }

  // Coq: Character.canonicalize : RegExpRecord -> type -> type.
  // Concrete naive instance (the LindenInst "naive engine"): identity when case-sensitive, and a
  // simple ASCII upper-case fold under ignoreCase. Marked {:opaque} so the verifier still treats it
  // as an uninterpreted function (the abstract development is unchanged and only relies on the
  // case-sensitivity law below) while the compiler can EXECUTE it — this is what makes the engine
  // runnable for tests. `reveal Canonicalize()` exposes the body where (rarely) needed.
  /** Case-fold `c` under the regex's flags: identity unless `rer.ignoreCase`, in which case
      lower-case ASCII letters are mapped to upper-case. Kept `{:opaque}` so proofs treat it
      abstractly (via `CanonicalizeCaseSensitive`) while it still compiles and runs. */
  function {:opaque} Canonicalize(rer: RegExpRecord, c: char): char {
    if rer.ignoreCase && 'a' <= c <= 'z' then (c as int - 32) as char else c
  }

  // Coq: LindenParameters.canonicalize_casesenst — when ignoreCase = false, canonicalize is id.
  // Now a proved lemma (was an axiom) since Canonicalize has a concrete body.
  /** Without the `i` flag, `Canonicalize` is the identity. */
  lemma CanonicalizeCaseSensitive(rer: RegExpRecord, c: char)
    ensures !rer.ignoreCase ==> Canonicalize(rer, c) == c
  {
    reveal Canonicalize();
  }

  // ----- CharSet (= set<char>) -----
  // Native `set<char>` supplies the Warblre CharSet spec-lemmas (union_spec, contains_spec,
  // remove_all_spec, range_spec, ...) for free; these helpers just name the operations.
  /** A set of characters (e.g. a character class's contents), backed by Dafny's native `set`. */
  type CharSet = set<char>

  const EmptyCS: CharSet := {}
  function FromList(l: seq<char>): CharSet { set c | c in l }
  function Union(a: CharSet, b: CharSet): CharSet { a + b }
  function Singleton(c: char): CharSet { {c} }
  function RemoveAll(a: CharSet, b: CharSet): CharSet { a - b }
  function Size(s: CharSet): nat { |s| }
  predicate Contains(s: CharSet, c: char) { c in s }
  predicate IsEmpty(s: CharSet) { s == {} }
  function Filter(s: CharSet, f: char -> bool): CharSet { set c | c in s && f(c) }

  // Coq: CharSet.range l h — chars whose numeric value is within [l, h].
  /** The inclusive character range `[lo, hi]` (e.g. what `[a-z]` denotes). */
  function Range(lo: char, hi: char): CharSet { set c: char {:autotriggers false} | lo <= c <= hi }

  // Coq: CharSet.exist s f.  (Ghost-level; not compilable as written.)
  /** Whether some character in `s` satisfies `f`. */
  predicate Exist(s: CharSet, f: char -> bool) { exists c :: c in s && f(c) }

  // Coq: CharSet.exist_canonicalized rer s c.
  /** Whether `c` is the canonicalization (under `rer`'s flags) of some member of `s` — how a
      character class is matched under the `i` flag. */
  predicate ExistCanonicalized(rer: RegExpRecord, s: CharSet, c: char) {
    exists c0 :: c0 in s && Canonicalize(rer, c0) == c
  }

  // ----- Standard ECMAScript character classes (naive instance) -----
  // NOTE: refine exact membership against Semantics/Chars.v when porting that file.

  // Coq: Characters.all := from_list Character.all (the universe of characters).
  // Ghost-level universe of all chars (finite bounded type; triggerless but fine for specs).
  /** The set of every `char` — what `.` (with the `s`/`dotAll` flag) or a negated empty class
      denotes. */
  function AllChars(): CharSet { set c: char {:autotriggers false} | true }

  /** `[0-9]`, the character class matched by `\d`. */
  function Digits(): CharSet { Range('0', '9') }
  /** ASCII word characters `[A-Za-z0-9_]`, the class matched by `\w`. */
  function AsciiWordCharacters(): CharSet {
    Union(Union(Range('a', 'z'), Range('A', 'Z')), Union(Range('0', '9'), {'_'}))
  }
  /** The line-terminator characters (`\n`, `\r`, U+2028, U+2029) that anchor `^`/`$`
      matching under the `m` flag and that `.` excludes without `dotAll`. */
  function LineTerminators(): CharSet { {'\n', '\r', '\U{2028}', '\U{2029}'} }
  /** The whitespace characters matched by `\s` (includes `LineTerminators`). */
  function WhiteSpaces(): CharSet {
    {' ', '\t', '\U{000B}', '\U{000C}', '\U{00A0}', '\U{FEFF}'} + LineTerminators()
  }

  // Coq: Semantics.wordCharacters rer (returns a Result there; here we return the set directly).
  // The naive word-character set is the ASCII word characters; case-folding under ignoreCase is
  // handled at the use site via Canonicalize.
  /** The character set used for `\b`/`\B` word-boundary tests (here just the ASCII word
      characters; `ignoreCase` folding is applied at the use site). */
  function WordCharacters(rer: RegExpRecord): CharSet { AsciiWordCharacters() }

  // ----- Property (Unicode property) -----
  // Coq: Property.class { type; code_points_for: type -> list char }.
  // Model a property as the value carrying its code points.
  /** A Unicode property class (e.g. `\p{...}`), modeled as the set of code points it covers. */
  datatype Property = Property(codePoints: seq<char>)
  function CodePointsFor(p: Property): seq<char> { p.codePoints }
}
