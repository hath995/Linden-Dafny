// Mirror of Engine/SeenSets.v.
// Memoization sets for PikeTree (seen trees) and PikeVM (seen (pc, LoopBool) pairs). The Coq dev
// parameterizes over abstract TSeen/VMSeen typeclasses with list instances (TSlist/VMSlist); here
// we use the concrete list (seq) instances directly and prove their axioms as lemmas. (Divergence:
// the development is no longer generic over arbitrary seen-set implementations — see PORTING_NOTES.)
include "NFA.dfy"
include "BooleanSemantics.dfy"

/** The memoization tables that make `PikeTree` and `PikeVM` linear-time: they record which
    subtrees / `(pc, LoopBool)` pairs have already been explored at the current input position,
    so a matcher never re-expands the same state twice. */
module SeenSets {
  import opened Tree
  import opened NFA            // Label
  import opened BooleanSemantics  // LoopBool

  // ----- TSeen: sets of seen trees (list instance) -----
  /** The set of `Tree` subtrees already explored by `PikeTree` at the current position. */
  type SeenTrees = seq<Tree>
  /** The empty seen-tree set, at the start of each input position. */
  const InitialSeenTrees: SeenTrees := []
  /** Record `t` as seen. */
  function AddSeenTrees(s: SeenTrees, t: Tree): SeenTrees { [t] + s }
  /** Has `t` already been explored? */
  predicate Inseen(s: SeenTrees, t: Tree) { t in s }

  /** Recording `t2` only affects membership of `t2` itself; all other membership is unchanged. */
  // Coq: in_add
  lemma InAdd(seen: SeenTrees, t1: Tree, t2: Tree)
    ensures Inseen(AddSeenTrees(seen, t2), t1) <==> (t1 == t2 || Inseen(seen, t1))
  {
    assert AddSeenTrees(seen, t2) == [t2] + seen;
  }

  /** Nothing has been seen yet at a fresh position. */
  // Coq: initial_nothing
  lemma InitialNothing(t: Tree)
    ensures !Inseen(InitialSeenTrees, t)
  {}

  // ----- VMSeen: sets of seen (pc, LoopBool) pairs (list instance) -----
  /** The set of `(pc, LoopBool)` keys `PikeVM` has already expanded at the current position —
      the dedup that underlies `Termination`'s linear-time bound. */
  type SeenPcs = seq<(Label, LoopBool)>
  /** The empty seen-key set, at the start of each input position. */
  const InitialSeenPcs: SeenPcs := []
  /** Record `(l, b)` as seen. */
  function AddSeenPcs(s: SeenPcs, l: Label, b: LoopBool): SeenPcs { [(l, b)] + s }
  /** Has key `(l, b)` already been expanded? */
  predicate Inseenpc(s: SeenPcs, l: Label, b: LoopBool) { (l, b) in s }

  /** Recording `(pc2, b2)` only affects membership of that key; all other membership is unchanged. */
  // Coq: inpc_add
  lemma InpcAdd(seen: SeenPcs, pc1: Label, b1: LoopBool, pc2: Label, b2: LoopBool)
    ensures Inseenpc(AddSeenPcs(seen, pc2, b2), pc1, b1) <==> ((pc1, b1) == (pc2, b2) || Inseenpc(seen, pc1, b1))
  {
    assert AddSeenPcs(seen, pc2, b2) == [(pc2, b2)] + seen;
  }

  /** Nothing has been seen yet at a fresh position. */
  // Coq: initial_nothing_pc
  lemma InitialNothingPc(pc: Label, b: LoopBool)
    ensures !Inseenpc(InitialSeenPcs, pc, b)
  {}
}
