// Mirror of Semantics/Inst.v.
// The Coq file instantiates the LindenParameters typeclass using Warblre's naive engine. In this
// port the naive instantiation IS the concrete model already fixed in Warblre/Primitives.dfy
// (Character := char, CharSet := set<char>, canonicalize abstract with the case law). No separate
// instance object is required, so this module exists only for structural parity with the Rocq
// development and to document the correspondence.
include "Parameters.dfy"

/** Structural placeholder recording that `LindenParameters` *is* the naive-engine
    instantiation of Linden's parameters typeclass; carries no additional definitions. */
module LindenInst {
  import opened LindenParameters
}
