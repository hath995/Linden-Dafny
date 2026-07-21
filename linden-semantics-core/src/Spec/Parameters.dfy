// Mirror of Semantics/Parameters.v.
// In Coq, `LindenParameters` is a typeclass bundling Warblre's Character/CharSet/Property
// typeclasses plus the `canonicalize_casesenst` law. In this port those three types are fixed
// concretely in Warblre/Primitives.dfy (Character := char, CharSet := set<char>, Property carrying
// its code points) and `canonicalize` is the opaque function declared there. The only genuine
// "parameter law" is canonicalize_casesenst, re-stated here under the Linden name as a proved
// lemma (discharged from the Primitives axiom) so downstream files call it without touching the
// raw axiom.

/** Linden's parameters typeclass, instantiated concretely (see `Warblre/Primitives.dfy`);
    re-exports the case-sensitivity law under the Linden name. */
module LindenParameters {
  import opened WarblreRegExpRecord
  import opened WarblrePrimitives

  // Coq: LindenParameters.canonicalize_casesenst.
  /** Without the `i` flag, `Canonicalize` is the identity (restated from
      `CanonicalizeCaseSensitive` under the Linden parameters name). */
  lemma CanonicalizeCaseInsensitiveIsId(rer: RegExpRecord, c: char)
    requires !rer.ignoreCase
    ensures Canonicalize(rer, c) == c
  {
    CanonicalizeCaseSensitive(rer, c);
  }
}
