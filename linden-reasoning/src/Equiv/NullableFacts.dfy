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

  /** `r` can match the empty string in EVERY context — the structural mirror
      of the engine's `nullable(re) == CINullable` over the translated regex
      (§2.5b: the discriminator of the compiler's CIN-GREEDY end-fork scheme).
      Anchors and lookarounds are context-DEPENDENT, so they are not CI; a
      disjunction is CI-nullable if either branch is (`null_or`), a sequence
      only if both parts are (`null_and`), a quantifier if its minimum is zero
      or its body is CI-nullable. */
  predicate CINullableL(r: L.Regex)
    decreases r
  {
    match r
    case Epsilon => true
    case Character(_) => false
    case Disjunction(r1, r2) => CINullableL(r1) || CINullableL(r2)
    case Sequence(r1, r2) => CINullableL(r1) && CINullableL(r2)
    case Quantified(greedy, min, delta, r1) => min == 0 || CINullableL(r1)
    case Group(gid, r1) => CINullableL(r1)
    case AnchorR(_) => false
    case LookaroundR(_, _) => false
    case Backreference(_) => false
  }

  /** CI-nullable excludes non-nullable: a regex that always matches empty
      cannot be one that never does. */
  lemma CINotNonNullableL(r: L.Regex)
    requires CINullableL(r)
    ensures !NonNullableL(r)
    decreases r
  {
    match r
    case Epsilon =>
    case Character(_) =>
    case Disjunction(r1, r2) =>
      if CINullableL(r1) { CINotNonNullableL(r1); } else { CINotNonNullableL(r2); }
    case Sequence(r1, r2) =>
      CINotNonNullableL(r1); CINotNonNullableL(r2);
    case Quantified(greedy, min, delta, r1) =>
      if min > 0 { CINotNonNullableL(r1); }
    case Group(gid, r1) =>
      CINotNonNullableL(r1);
    case AnchorR(_) =>
    case LookaroundR(_, _) =>
    case Backreference(_) =>
  }

  /** The annotation agreement for `CINullable`, BOTH ways: the engine computed
      `CINullable` iff the translation is CI-nullable. Plain structural
      induction — the two definitions are constructor-for-constructor mirrors
      (`null_or` is `CINullable` iff either side is; `null_and` iff both are). */
  lemma TransCINullable(re: R.regex)
    requires T.TransWf(re)
    ensures R.nullable(re) == R.CINullable <==> CINullableL(T.Translate(re))
    decreases re
  {
    match re
    case Re_empty =>
    case Re_character(_) =>
    case Re_alt(r1, r2) =>
      TransCINullable(r1);
      TransCINullable(r2);
    case Re_con(r1, r2) =>
      TransCINullable(r1);
      TransCINullable(r2);
    case Re_quant(nul, qid, q, r1) =>
      TransCINullable(r1);
    case Re_capture(cid, r1) =>
      TransCINullable(r1);
    case Re_lookaround(_, _, _) =>
    case Re_anchor(_) =>
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
