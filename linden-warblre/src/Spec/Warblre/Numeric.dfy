// Mirror of Warblre/spec/base/Numeric.v (the subset Linden uses).
// non_neg_integer := nat; NoI (non_neg_integer_or_inf) with add/sub/eqb/leqb.
/** Non-negative integers and "nat-or-infinity", used to bound quantifier repetitions
    (e.g. `r{2,5}` vs. `r{2,}`). */
module WarblreNumeric {

  // Coq: Definition non_neg_integer := nat.
  /** A non-negative integer (just `nat`), named for parity with Warblre. */
  type NonNegInt = nat

  // Coq: Inductive non_neg_integer_or_inf := N (n: non_neg_integer) | Inf.
  /** A `nat`, or `Inf` for unbounded. Used as the quantifier's `delta` in `Regex.Quantified`,
      so `NN(0)` gives an exact count and `Inf` gives `*`/`+`-style unboundedness. */
  datatype NoI = NN(n: nat) | Inf

  // Coq: NoI.add
  /** Addition, with `Inf` absorbing (`Inf + anything = Inf`). */
  function NoIAdd(l: NoI, r: NoI): NoI {
    match l
    case NN(a) => (match r case NN(b) => NN(a + b) case Inf => Inf)
    case Inf => Inf
  }

  // Coq: NoI.sub (Coq nat subtraction is truncated at 0).
  /** Subtract a `nat` from a `NoI`, truncating at 0 (never going negative); `Inf` stays `Inf`. */
  function NoISub(l: NoI, r: nat): NoI {
    match l
    case NN(a) => NN(if a >= r then a - r else 0)
    case Inf => Inf
  }

  // Coq: NoI.eqb. Structural equality suffices in Dafny.
  predicate NoIEqb(l: NoI, r: NoI) { l == r }

  // Coq: NoI.leqb (l <= r where l: nat, r: NoI).
  /** Whether the `nat` `l` is `<=` the `NoI` `r` (always true when `r` is `Inf`). */
  predicate NoILeqb(l: nat, r: NoI) {
    match r
    case NN(b) => l <= b
    case Inf => true
  }

  /** A `nat` is always `<=` its own `NN` wrapping. */
  lemma NoILeqbRefl(l: nat)
    ensures NoILeqb(l, NN(l))
  {}
}
