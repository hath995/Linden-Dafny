// Mirror of Semantics/ComputeIsTree.v.
// compute_tree yields trees that satisfy the inductive semantics is_tree.
include "FunctionalSemantics.dfy"

/** The bridge from the executable semantics back to the relational one: whatever
    `ComputeTree` computes is a valid tree under `Semantics.IsTree`. */
module ComputeIsTree {
  import opened Std.Wrappers
  import opened WarblreRegExpRecord
  import opened WarblreNumeric
  import opened WarblrePrimitives
  import opened Chars
  import opened Groups
  import opened Regex
  import opened Tree
  import SS = StrictSuffix
  import opened Semantics
  import opened FunctionalSemantics

  // Coq: compute_is_tree. Recursion on fuel mirroring ComputeTree; each branch establishes the body
  // of the IsTree least-predicate from the inductive hypothesis on sub-results.
  /** If `ComputeTree` produces `t` for this action stack/position, `t` is a genuine `IsTree`
      tree. Proved by recursion on `fuel`, mirroring `ComputeTree`'s own recursion structure. */
  lemma ComputeIsTreeThm(rer: RegExpRecord, act: Actions, inp: Input, gm: GroupMap, dir: Direction, fuel: nat, t: Tree)
    requires ComputeTree(rer, act, inp, gm, dir, fuel) == Some(t)
    ensures IsTree(rer, act, inp, gm, dir, t)
    decreases fuel
  {
    var f := fuel - 1;
    if |act| == 0 {
    } else {
      var cont := act[1..];
      match act[0]
      case Acheck(strcheck) =>
        if SS.IsStrictSuffix(inp, strcheck, dir) {
          var sub := ComputeTree(rer, cont, inp, gm, dir, f);
          if sub.Some? { ComputeIsTreeThm(rer, cont, inp, gm, dir, f, sub.value); }
        }
      case Aclose(gid) =>
        var gm' := GMClose(Idx(inp), gid, gm);
        var sub := ComputeTree(rer, cont, inp, gm', dir, f);
        if sub.Some? { ComputeIsTreeThm(rer, cont, inp, gm', dir, f, sub.value); }
      case Areg(r) =>
        match r
        case Epsilon =>
          ComputeIsTreeThm(rer, cont, inp, gm, dir, f, t);
        case Character(cd) => {
          match ReadChar(rer, cd, inp, dir) {
            case None =>
            case Some(pair) =>
              var sub := ComputeTree(rer, cont, pair.1, gm, dir, f);
              if sub.Some? { ComputeIsTreeThm(rer, cont, pair.1, gm, dir, f, sub.value); }
          }
        }
        case Disjunction(r1, r2) =>
          var s1 := ComputeTree(rer, [Areg(r1)] + cont, inp, gm, dir, f);
          var s2 := ComputeTree(rer, [Areg(r2)] + cont, inp, gm, dir, f);
          if s1.Some? { ComputeIsTreeThm(rer, [Areg(r1)] + cont, inp, gm, dir, f, s1.value); }
          if s2.Some? { ComputeIsTreeThm(rer, [Areg(r2)] + cont, inp, gm, dir, f, s2.value); }
        case Sequence(r1, r2) =>
          var na := SeqList(r1, r2, dir) + cont;
          var sub := ComputeTree(rer, na, inp, gm, dir, f);
          if sub.Some? { ComputeIsTreeThm(rer, na, inp, gm, dir, f, sub.value); }
        case Quantified(greedy, min, delta, r1) =>
          var gidl := DefGroups(r1);
          if min > 0 {
            var na := [Areg(r1), Areg(Quantified(greedy, min - 1, delta, r1))] + cont;
            var gm' := GMReset(gidl, gm);
            var sub := ComputeTree(rer, na, inp, gm', dir, f);
            if sub.Some? { ComputeIsTreeThm(rer, na, inp, gm', dir, f, sub.value); }
          } else if delta == NN(0) {
            ComputeIsTreeThm(rer, cont, inp, gm, dir, f, t);
          } else {
            var na := [Areg(r1), Acheck(inp), Areg(Quantified(greedy, 0, NoiPred(delta), r1))] + cont;
            var gm' := GMReset(gidl, gm);
            var siter := ComputeTree(rer, na, inp, gm', dir, f);
            var sskip := ComputeTree(rer, cont, inp, gm, dir, f);
            if siter.Some? { ComputeIsTreeThm(rer, na, inp, gm', dir, f, siter.value); }
            if sskip.Some? { ComputeIsTreeThm(rer, cont, inp, gm, dir, f, sskip.value); }
          }
        case Group(gid, r1) =>
          var na := [Areg(r1), Aclose(gid)] + cont;
          var gm' := GMOpen(Idx(inp), gid, gm);
          var sub := ComputeTree(rer, na, inp, gm', dir, f);
          if sub.Some? { ComputeIsTreeThm(rer, na, inp, gm', dir, f, sub.value); }
        case LookaroundR(lk, r1) =>
          var slk := ComputeTree(rer, [Areg(r1)], inp, gm, LkDir(lk), f);
          if slk.Some? {
            ComputeIsTreeThm(rer, [Areg(r1)], inp, gm, LkDir(lk), f, slk.value);
            match LkResult(lk, slk.value, gm, inp)
            case Some(gmlk) =>
              var sc := ComputeTree(rer, cont, inp, gmlk, dir, f);
              if sc.Some? { ComputeIsTreeThm(rer, cont, inp, gmlk, dir, f, sc.value); }
            case None =>
          }
        case AnchorR(a) =>
          if AnchorSatisfied(rer, a, inp) {
            var sub := ComputeTree(rer, cont, inp, gm, dir, f);
            if sub.Some? { ComputeIsTreeThm(rer, cont, inp, gm, dir, f, sub.value); }
          }
        case Backreference(gid) => {
          match ReadBackref(rer, gm, gid, inp, dir) {
            case None =>
            case Some(pair) =>
              var sub := ComputeTree(rer, cont, pair.1, gm, dir, f);
              if sub.Some? { ComputeIsTreeThm(rer, cont, pair.1, gm, dir, f, sub.value); }
          }
        }
    }
  }
}
