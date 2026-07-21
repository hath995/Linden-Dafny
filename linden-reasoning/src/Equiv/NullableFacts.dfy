// Phase +A: Linden-side nullability — the semantic meaning of the engine's
// `nullable() == NonNullable` annotation, on the translated AST.
//
// The compiler's "last repetition is the final loop" scheme for `+`/`{n,}`
// (Compiler.dfy:107-112) omits the BeginLoop/EndLoop empty-iteration guard,
// justified by the body being NonNullable: every successful pass through it
// consumes at least one character, so the guard could never fire. This file
// states that justification on the Linden side:
//   - `NonNullableL(r)` — the structural mirror of `nullable(re) == NonNullable`
//     over the translated regex;
//   - `TransNonNullable` — the annotation agreement through `Translate`.
// The downstream campaign (do-while representation) builds on these to erase
// always-passing `Acheck`s from star iteration lists.
include "Translate.dfy"

/** Linden-side nullability facts backing the `+`/`{n,}` do-while scheme:
    `NonNullableL` (the translated image of the engine's `NonNullable`
    annotation) and its agreement lemma through `Translate`. */
module LindenElkNullable {
  import opened Std.Wrappers
  import L = Regex
  import R = RegElkRegex
  import T = LindenElkTranslate

  /** `r` cannot match the empty string in ANY context: every successful path
      through `r` consumes at least one character. The structural mirror of
      the engine's `nullable(re) == NonNullable` (zero-width constructs —
      `Epsilon`, anchors, lookarounds, backreferences — are never
      NonNullable; a sequence consumes if EITHER part does; a disjunction
      only if BOTH branches do; a quantifier only if forced at least once
      with a consuming body). */
  predicate NonNullableL(r: L.Regex)
    decreases r
  {
    match r
    case Epsilon => false
    case Character(_) => true
    case Disjunction(r1, r2) => NonNullableL(r1) && NonNullableL(r2)
    case Sequence(r1, r2) => NonNullableL(r1) || NonNullableL(r2)
    case Quantified(greedy, min, delta, r1) => min > 0 && NonNullableL(r1)
    case Group(gid, r1) => NonNullableL(r1)
    case AnchorR(_) => false
    case LookaroundR(_, _) => false
    case Backreference(_) => false
  }

  /** The annotation agreement: whenever the engine computed `NonNullable`
      for an annotated regex, its translation satisfies `NonNullableL`. */
  lemma TransNonNullable(re: R.regex)
    requires T.TransWf(re)
    requires R.nullable(re) == R.NonNullable
    ensures NonNullableL(T.Translate(re))
    decreases re
  {
    match re
    case Re_empty =>
    case Re_character(_) =>
    case Re_alt(r1, r2) =>
      // null_or is NonNullable only when both sides are
      TransNonNullable(r1);
      TransNonNullable(r2);
    case Re_con(r1, r2) =>
      // null_and is NonNullable exactly when either side is
      if R.nullable(r1) == R.NonNullable {
        TransNonNullable(r1);
      } else {
        assert R.nullable(r2) == R.NonNullable;
        TransNonNullable(r2);
      }
    case Re_quant(nul, qid, q, r1) =>
      // min == 0 yields CINullable, so min > 0 and the body is NonNullable
      TransNonNullable(r1);
    case Re_capture(cid, r1) =>
      TransNonNullable(r1);
    case Re_lookaround(_, _, _) =>
      // CDNullable, never NonNullable: vacuous
    case Re_anchor(_) =>
      // CDNullable, never NonNullable: vacuous
  }
}
