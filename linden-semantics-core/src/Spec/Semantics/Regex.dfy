// Mirror of Semantics/Regex.v.
// Abstract syntax tree of JavaScript regexes (Linden's AST). Parameterized in Coq by
// LindenParameters; here the character type is concrete (char) via Chars/Primitives.
include "Chars.dfy"
include "Groups.dfy"

/** The abstract syntax of ECMAScript regular expressions.

    This is the surface language the whole development is about: every other
    module either builds a [Regex] value, gives it meaning (`Semantics.IsTree`),
    or proves something about that meaning. The character type is concrete
    (`char`) rather than parameterized. */
module Regex {
  import opened WarblrePrimitives  // Direction
  import opened WarblreNumeric     // NoI
  import opened Chars              // CharDescr
  import opened Groups             // GroupId

  // Coq: Inductive lookaround := LookAhead | LookBehind | NegLookAhead | NegLookBehind.
  /** The four lookaround flavours: `(?=…)`, `(?<=…)`, `(?!…)`, `(?<!…)`. */
  datatype Lookaround = LookAhead | LookBehind | NegLookAhead | NegLookBehind

  // Coq: lk_dir
  /** The scanning direction a lookaround matches in: lookaheads go `Forward`,
      lookbehinds go `Backward`. */
  function LkDir(lk: Lookaround): Direction {
    match lk
    case LookAhead => Forward
    case NegLookAhead => Forward
    case LookBehind => Backward
    case NegLookBehind => Backward
  }

  // Coq: positivity
  /** Whether a lookaround is *positive* (must match) or *negative* (must fail). */
  function Positivity(lk: Lookaround): bool {
    match lk
    case LookAhead => true
    case LookBehind => true
    case NegLookAhead => false
    case NegLookBehind => false
  }

  // Coq: Inductive anchor := BeginInput | EndInput | WordBoundary | NonWordBoundary.
  /** Zero-width assertions: `^`, `$`, `\b`, `\B`. */
  datatype Anchor = BeginInput | EndInput | WordBoundary | NonWordBoundary

  // Coq: Inductive regex.
  /** An ECMAScript regex.

      - `Epsilon` — the empty pattern (always matches, consuming nothing).
      - `Character(cd)` — a single character described by a class/literal `cd`.
      - `Disjunction(r1, r2)` — `r1 | r2`; `r1` has priority.
      - `Sequence(r1, r2)` — `r1` followed by `r2`.
      - `Quantified(greedy, min, delta, r1)` — `r1{min, min+delta}`; `delta` is a
        `NoI` so `Inf` gives `*`/`+`. `greedy` chooses iterate-first vs. skip-first.
      - `LookaroundR(lk, r)` — a lookahead/lookbehind around `r`.
      - `Group(id, r)` — a capturing group `( r )` recorded under `id`.
      - `AnchorR(a)` — a zero-width anchor.
      - `Backreference(id)` — `\id`, re-matches group `id`'s captured text. */
  datatype Regex =
    | Epsilon
    | Character(cd: CharDescr)
    | Disjunction(r1: Regex, r2: Regex)
    | Sequence(r1: Regex, r2: Regex)
    | Quantified(greedy: bool, min: nat, delta: NoI, r1: Regex)
    | LookaroundR(lk: Lookaround, r: Regex)
    | Group(id: GroupId, r: Regex)
    | AnchorR(a: Anchor)
    | Backreference(id: GroupId)

  // Coq: regex_eq_dec — free structural `==` in Dafny (dropped).

  function NatMax(a: nat, b: nat): nat { if a >= b then a else b }

  // Coq: Fixpoint def_groups r — all group ids defined in r (for reset).
  /** All capture-group ids that occur anywhere in `r`, in left-to-right order.
      Used by quantifiers to reset the groups inside one iteration before the
      next (ECMAScript resets per-iteration captures). */
  function DefGroups(r: Regex): seq<GroupId>
    decreases r
  {
    match r
    case Epsilon => []
    case Character(_) => []
    case Disjunction(r1, r2) => DefGroups(r1) + DefGroups(r2)
    case Sequence(r1, r2) => DefGroups(r1) + DefGroups(r2)
    case Quantified(_, _, _, r1) => DefGroups(r1)
    case LookaroundR(_, r0) => DefGroups(r0)
    case Group(id, r1) => [id] + DefGroups(r1)
    case AnchorR(_) => []
    case Backreference(_) => []
  }

  // Coq: Fixpoint max_group r
  /** The largest group id appearing in `r` (0 if it has no groups). */
  function MaxGroup(r: Regex): GroupId
    decreases r
  {
    match r
    case Epsilon => 0
    case Character(_) => 0
    case AnchorR(_) => 0
    case Backreference(_) => 0
    case Disjunction(r1, r2) => NatMax(MaxGroup(r1), MaxGroup(r2))
    case Sequence(r1, r2) => NatMax(MaxGroup(r1), MaxGroup(r2))
    case Quantified(_, _, _, r0) => MaxGroup(r0)
    case LookaroundR(_, r0) => MaxGroup(r0)
    case Group(id, r0) => NatMax(id, MaxGroup(r0))
  }

  // ----- common quantifiers -----
  /** `r*` — greedy zero-or-more. */
  function GreedyStar(r: Regex): Regex { Quantified(true, 0, Inf, r) }      // r*
  /** `r*?` — lazy zero-or-more. */
  function LazyStar(r: Regex): Regex { Quantified(false, 0, Inf, r) }       // r*?
  /** `r+` — greedy one-or-more. */
  function GreedyPlus(r: Regex): Regex { Quantified(true, 1, Inf, r) }      // r+
  /** `r+?` — lazy one-or-more. */
  function LazyPlus(r: Regex): Regex { Quantified(false, 1, Inf, r) }       // r+?
  /** `r?` — greedy optional. */
  function GreedyQMark(r: Regex): Regex { Quantified(true, 0, NN(1), r) }   // r?
  /** `r??` — lazy optional. */
  function LazyQMark(r: Regex): Regex { Quantified(false, 0, NN(1), r) }    // r??
}
