// Mirror of Engine/Correctness.v.
// Top-level PikeVM correctness. The Warblre-relative theorems (pike_vm_warblre,
// pike_vm_same_warblre[_str0]) are OUT OF SCOPE (they depend on WarblreEquiv) and are omitted.
// In-scope endpoints: pike_vm_to_pike_tree (Thm 15) and pike_vm_correct (Thm 16), both PROVED here
// from the (axiomatized) simulation/invariant lemmas.
include "PikeEquiv.dfy"

/** The top-level correctness proof for the PikeVM: `PikeVmToPikeTree` (Theorem 15) shows the VM's
    small-step run simulates a `PikeTree` run, and `PikeVmCorrect` (Theorem 16) concludes the VM's
    final result equals `Tree.FirstLeaf`, the tree semantics' answer. Everything here is assembled
    from the (partly axiomatized) simulation machinery in `PikeEquiv`. */
module Correctness {
  import opened Std.Wrappers
  import opened WarblreRegExpRecord
  import opened WarblrePrimitives
  import opened Chars
  import opened Groups
  import opened Regex
  import opened Tree
  import opened Semantics       // IsTree, Areg
  import opened BooleanSemantics  // BoolTree, BooleanCorrect, CanExit
  import opened NFA             // Compilation, Code
  import opened PikeSubset
  import opened PikeTree
  import opened PikeVM
  import opened PikeEquiv

  // Coq: trc (transitive-reflexive closure), specialized to the two step relations.
  /** The transitive-reflexive closure of `PikeTree.PikeTreeStep`: `TrcPikeTree(x, y)` holds when `y`
      is reachable from `x` by zero or more small steps. */
  least predicate TrcPikeTree(x: PikeTreeState, y: PikeTreeState) {
    x == y || (exists z :: PikeTreeStep(x, z) && TrcPikeTree(z, y))
  }
  /** The transitive-reflexive closure of `PikeVM.PikeVmStep`: `TrcPikeVm(c, rer, x, y)` holds when
      `y` is reachable from `x` by zero or more small steps of the bytecode VM running `c`. */
  least predicate TrcPikeVm(c: Code, rer: RegExpRecord, x: PikeVmState, y: PikeVmState) {
    x == y || (exists z :: PikeVmStep(c, rer, x, z) && TrcPikeVm(c, rer, z, y))
  }

  // ===== Axiomatized (inductions over the trc least predicates). See PROGRESS.md. =====

  // Coq: vm_to_tree — the invariant is preserved through the VM trc (uses invariant_preservation).
  // (least lemmas can't have out-params, so the resulting PikeTree state is existentially quantified.)
  /** If the VM invariant `PikeEquiv.PikeInv` holds and the VM runs from `svm1` to `svm2`, some
      `PikeTree` run from `st1` reaches a state `st2` that is still `PikeInv`-related to `svm2`. This
      walks `PikeEquiv.InvariantPreservation` along the whole VM trace, skipping steps where the VM
      merely stutters (advances `pc` without the tree side moving). */
  least lemma VmToTree(rer: RegExpRecord, svm1: PikeVmState, st1: PikeTreeState, svm2: PikeVmState, code: Code)
    requires StutterWf(rer, code)
    requires PikeInv(rer, code, st1, svm1)
    requires TrcPikeVm(code, rer, svm1, svm2)
    ensures exists st2 :: TrcPikeTree(st1, st2) && PikeInv(rer, code, st2, svm2)
  {
    if svm1 == svm2 {
      assert TrcPikeTree(st1, st1) && PikeInv(rer, code, st1, svm2);  // witness st2 := st1
    } else {
      var svmmid :| PikeVmStep(code, rer, svm1, svmmid) && TrcPikeVm(code, rer, svmmid, svm2);
      InvariantPreservation(rer, code, st1, svm1, svmmid);
      if exists pts2 :: PikeTreeStep(st1, pts2) && PikeInv(rer, code, pts2, svmmid) {
        var pts2 :| PikeTreeStep(st1, pts2) && PikeInv(rer, code, pts2, svmmid);
        VmToTree(rer, svmmid, pts2, svm2, code);
        var st2 :| TrcPikeTree(pts2, st2) && PikeInv(rer, code, st2, svm2);
        assert TrcPikeTree(st1, st2) by { assert PikeTreeStep(st1, pts2) && TrcPikeTree(pts2, st2); }
      } else {
        VmToTree(rer, svmmid, st1, svm2, code);  // stutter: PikeInv(st1, svmmid) holds
      }
    }
  }

  // Coq: pike_tree_trc_correct (induction over the trc; uses pts_preservation)
  /** `PikeTree.Piketreeinv` is preserved along an entire `TrcPikeTree` run: if it holds at the start
      with target `result`, it still holds (with the same `result`) wherever the run ends up. Proved
      by walking `PikeTree.PtsPreservation` over the trace. */
  least lemma PikeTreeTrcCorrect(s1: PikeTreeState, s2: PikeTreeState, result: Option<Leaf>)
    requires Piketreeinv(s1, result)
    requires TrcPikeTree(s1, s2)
    ensures Piketreeinv(s2, result)
  {
    if s1 != s2 {
      var z :| PikeTreeStep(s1, z) && TrcPikeTree(z, s2);
      PtsPreservation(s1, z, result);
      PikeTreeTrcCorrect(z, s2, result);
    }
  }

  // ===== Proved theorems =====

  // Coq: pike_vm_to_pike_tree (Theorem 15)
  /** Theorem 15. If the compiled bytecode VM run for `r` on `inp` reaches final result `result`, then
      a `PikeTree` run over `tree` (the pike-subset tree for `r`) also reaches `result` — the VM's
      execution is simulated by the tree-walking algorithm it is meant to speed up. */
  lemma PikeVmToPikeTree(rer: RegExpRecord, r: Regex, inp: Input, tree: Tree, result: Option<Leaf>)
    requires PikeRegex(r)
    requires BoolTree(rer, [Areg(r)], inp, CanExit, tree)
    requires TrcPikeVm(Compilation(r), rer, PikeVmInitialState(inp), PVS_final(result))
    ensures TrcPikeTree(PikeTreeInitialState(tree, inp), PTS_final(result))
  {
    var code := Compilation(r);
    InitialPikeInv(rer, r, inp, tree, code);
    CompilationStutterWf(rer, r, code);
    VmToTree(rer, PikeVmInitialState(inp), PikeTreeInitialState(tree, inp), PVS_final(result), code);
    var st2 :| TrcPikeTree(PikeTreeInitialState(tree, inp), st2) && PikeInv(rer, code, st2, PVS_final(result));
    // PikeInv(code, st2, PVS_final(result)) forces st2 == PTS_final(result).
    assert st2.PTS_final? && st2.best == result;
  }

  // Coq: pike_vm_correct (Theorem 16) — the in-scope correctness endpoint.
  /** Theorem 16, the capstone correctness result: for a `PikeSubset.PikeRegex` `r` whose tree
      semantics tree is `tree`, if the bytecode VM's run reaches final `result`, then `result` is
      exactly `Tree.FirstLeaf(tree, inp)` — the same answer the backtracking tree semantics gives.
      Chains `BooleanSemantics.BooleanCorrect`, `PikeVmToPikeTree`, `PikeSubset.PikeActionsPikeTree`,
      `PikeTree.InitPiketreeInv`, and `PikeTreeTrcCorrect`. */
  lemma PikeVmCorrect(rer: RegExpRecord, r: Regex, inp: Input, tree: Tree, result: Option<Leaf>)
    requires PikeRegex(r)
    requires IsTree(rer, [Areg(r)], inp, Empty, Forward, tree)
    requires TrcPikeVm(Compilation(r), rer, PikeVmInitialState(inp), PVS_final(result))
    ensures result == FirstLeaf(tree, inp)
  {
    // is_tree -> bool_tree
    BooleanCorrect(rer, r, inp, tree);
    // bool_tree + vm trc -> tree trc to final
    PikeVmToPikeTree(rer, r, inp, tree, result);
    // tree is a pike subtree
    assert PikeActions([Areg(r)]);
    PikeActionsPikeTree(rer, [Areg(r)], inp, Empty, Forward, tree);
    // initial PikeTree invariant
    InitPiketreeInv(tree, inp);
    // invariant preserved to the final state
    PikeTreeTrcCorrect(PikeTreeInitialState(tree, inp), PTS_final(result), FirstLeaf(tree, inp));
    // Piketreeinv(PTS_final(result), FirstLeaf tree inp) forces result == FirstLeaf tree inp.
  }
}
