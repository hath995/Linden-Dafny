// Mirror of Engine/PikeSubset.v.
// The subset of regexes / actions / trees supported by the PikeVM engine.
// The Coq Ltac automation (invert_subset/pike_subset/in_subset) has no Dafny analog and is omitted.

/** The fragment of the full spec (`Regex`, `Action`, `Tree`) that the `PikeVM`/`PikeTree` linear-time
    engine actually supports: no lookarounds, anchors, backreferences, or bounded/lazy quantifiers other
    than unbounded star. Everything downstream of this module (`NFA`, `PikeVM`, `PikeTree`, `PikeEquiv`,
    `Correctness`) proves its results relative to this subset. */
module PikeSubset {
  import opened Std.Wrappers
  import opened WarblreRegExpRecord
  import opened WarblrePrimitives
  import opened WarblreNumeric
  import opened Chars
  import opened Groups
  import opened Regex
  import opened Tree
  import opened Semantics
  import SS = StrictSuffix
  import opened FunctionalSemantics
  import ComputeIsTree
  import opened FunctionalUtils

  /** Regexes the PikeVM can compile: `Epsilon`, `Character`, `Disjunction`, `Sequence`, `Group`, and
      only the unbounded-star form of `Quantified` (`min == 0, delta == Inf`). Excludes lookarounds,
      anchors, backreferences, and bounded/optional quantifiers. */
  // Coq: pike_regex (Epsilon, Character, Disjunction, Sequence, greedy/lazy star, Group).
  predicate PikeRegex(r: Regex)
    decreases r
  {
    match r
    case Epsilon => true
    case Character(_) => true
    case Disjunction(r1, r2) => PikeRegex(r1) && PikeRegex(r2)
    case Sequence(r1, r2) => PikeRegex(r1) && PikeRegex(r2)
    case Quantified(b, min, delta, r1) => PikeRegex(r1)
    case Group(_, r1) => PikeRegex(r1)
    case LookaroundR(_, _) => false
    case AnchorR(_) => true
    case Backreference(_) => false
  }

  /** An `Action` is in the pike fragment iff any `Areg` it carries is a `PikeRegex`; `Aclose`/`Acheck`
      (group-close, empty-loop guard) are always allowed. */
  // Coq: pike_action
  predicate PikeAction(a: Action) {
    match a case Areg(r) => PikeRegex(r) case Aclose(_) => true case Acheck(_) => true
  }

  /** An action stack (continuation) is in the pike fragment iff every action in it is. */
  // Coq: pike_actions
  predicate PikeActions(acts: Actions) {
    forall i :: 0 <= i < |acts| ==> PikeAction(acts[i])
  }

  /** The `Tree` shapes the pike fragment can produce: no `ReadBackRef`, `AnchorPass`, `LK`, or
      `LKFail` node anywhere in the tree. */
  // Coq: pike_subtree
  predicate PikeSubtree(t: Tree)
    decreases t
  {
    match t
    case Mismatch => true
    case Match => true
    case Choice(t1, t2) => PikeSubtree(t1) && PikeSubtree(t2)
    case Read(_, t1) => PikeSubtree(t1)
    case Progress(t1) => PikeSubtree(t1)
    case GroupActionT(_, t1) => PikeSubtree(t1)
    case ReadBackRef(_, _) => false
    case AnchorPass(_, t1) => PikeSubtree(t1)
    case LK(_, _, _) => false
    case LKFail(_, _) => false
  }

  /** A list of `(Tree, GroupMap)` pairs — e.g. `PikeTree`'s active/blocked queues — is pike iff every
      tree in it is a `PikeSubtree`. */
  // Coq: pike_list
  predicate PikeList(l: seq<(Tree, GroupMap)>) {
    forall i :: 0 <= i < |l| ==> PikeSubtree(l[i].0)
  }

  /** `PikeList` distributes over `cons`. */
  // Coq: pike_list_cons
  lemma PikeListCons(t: Tree, gm: GroupMap, l: seq<(Tree, GroupMap)>)
    ensures PikeList([(t, gm)] + l) <==> (PikeSubtree(t) && PikeList(l))
  {
    if PikeSubtree(t) && PikeList(l) {
      forall i | 0 <= i < |[(t, gm)] + l| ensures PikeSubtree(([(t, gm)] + l)[i].0) {
        if i == 0 {} else { assert ([(t, gm)] + l)[i] == l[i - 1]; }
      }
    }
    if PikeList([(t, gm)] + l) {
      assert ([(t, gm)] + l)[0] == (t, gm);
      forall i | 0 <= i < |l| ensures PikeSubtree(l[i].0) { assert ([(t, gm)] + l)[i + 1] == l[i]; }
    }
  }

  /** `PikeList` distributes over `+` (list append). */
  // Coq: pike_list_app
  lemma PikeListApp(l1: seq<(Tree, GroupMap)>, l2: seq<(Tree, GroupMap)>)
    ensures PikeList(l1 + l2) <==> (PikeList(l1) && PikeList(l2))
  {
    if PikeList(l1) && PikeList(l2) {
      forall i | 0 <= i < |l1 + l2| ensures PikeSubtree((l1 + l2)[i].0) {
        if i < |l1| { assert (l1 + l2)[i] == l1[i]; } else { assert (l1 + l2)[i] == l2[i - |l1|]; }
      }
    }
    if PikeList(l1 + l2) {
      forall i | 0 <= i < |l1| ensures PikeSubtree(l1[i].0) { assert (l1 + l2)[i] == l1[i]; }
      forall i | 0 <= i < |l2| ensures PikeSubtree(l2[i].0) { assert (l1 + l2)[i + |l1|] == l2[i]; }
    }
  }

  /** The empty list is trivially pike. */
  // Coq: pike_list_empty
  lemma PikeListEmpty()
    ensures PikeList([])
  {}

  /** A singleton list is pike iff its one tree is. */
  // Coq: pike_list_single
  lemma PikeListSingle(t: Tree, gm: GroupMap)
    requires PikeSubtree(t)
    ensures PikeList([(t, gm)])
  {}

  /** A two-element list is pike if both its trees are. */
  // Coq: pike_list_twice
  lemma PikeListTwice(t1: Tree, t2: Tree, gm1: GroupMap, gm2: GroupMap)
    requires PikeSubtree(t1) && PikeSubtree(t2)
    ensures PikeList([(t1, gm1), (t2, gm2)])
  {}

  /** `PikeActions` distributes over cons (helper for the fuel induction below). */
  // PikeActions distributes over cons/concat (helpers for the fuel induction).
  lemma PikeActionsConsIff(x: Action, cont: Actions)
    ensures PikeActions([x] + cont) <==> (PikeAction(x) && PikeActions(cont))
  {
    if PikeAction(x) && PikeActions(cont) {
      forall i | 0 <= i < |[x] + cont| ensures PikeAction(([x] + cont)[i]) {
        if i == 0 {} else { assert ([x] + cont)[i] == cont[i - 1]; }
      }
    }
    if PikeActions([x] + cont) {
      assert ([x] + cont)[0] == x;
      forall i | 0 <= i < |cont| ensures PikeAction(cont[i]) { assert ([x] + cont)[i + 1] == cont[i]; }
    }
  }

  /** The tail of a pike action stack is still pike. */
  lemma PikeActionsTail(acts: Actions)
    requires |acts| > 0 && PikeActions(acts)
    ensures PikeActions(acts[1..])
  {
    forall i | 0 <= i < |acts[1..]| ensures PikeAction(acts[1..][i]) { assert acts[1..][i] == acts[i + 1]; }
  }

  /** Running the fuel-driven reference interpreter (`ComputeTree`, mirroring `ComputeIsTree`) on a
      pike action stack always produces a `PikeSubtree` — the pike fragment never needs the tree
      shapes (`ReadBackRef`/`AnchorPass`/`LK`/`LKFail`) that only lookarounds/anchors/backrefs
      produce. Fuel-induction workhorse behind `PikeActionsPikeTree`. */
  // Fuel-induction version (mirrors ComputeIsTree): pike actions compute pike subtrees.
  lemma ComputePikeSubtree(rer: RegExpRecord, act: Actions, inp: Input, gm: GroupMap, dir: Direction, fuel: nat, t: Tree)
    requires PikeActions(act)
    requires ComputeTree(rer, act, inp, gm, dir, fuel) == Some(t)
    ensures PikeSubtree(t)
    decreases fuel
  {
    var f := fuel - 1;
    if |act| == 0 {
    } else {
      var cont := act[1..];
      PikeActionsTail(act);  // PikeActions(cont)
      assert act == [act[0]] + cont;
      PikeActionsConsIff(act[0], cont);  // PikeAction(act[0])
      match act[0]
      case Acheck(strcheck) =>
        if SS.IsStrictSuffix(inp, strcheck, dir) {
          var sub := ComputeTree(rer, cont, inp, gm, dir, f);
          if sub.Some? { ComputePikeSubtree(rer, cont, inp, gm, dir, f, sub.value); }
        }
      case Aclose(gid) =>
        var gm' := GMClose(Idx(inp), gid, gm);
        var sub := ComputeTree(rer, cont, inp, gm', dir, f);
        if sub.Some? { ComputePikeSubtree(rer, cont, inp, gm', dir, f, sub.value); }
      case Areg(r) =>
        assert PikeRegex(r);
        match r
        case Epsilon =>
          ComputePikeSubtree(rer, cont, inp, gm, dir, f, t);
        case Character(cd) => {
          match ReadChar(rer, cd, inp, dir) {
            case None =>
            case Some(pair) =>
              var sub := ComputeTree(rer, cont, pair.1, gm, dir, f);
              if sub.Some? { ComputePikeSubtree(rer, cont, pair.1, gm, dir, f, sub.value); }
          }
        }
        case Disjunction(r1, r2) =>
          PikeActionsConsIff(Areg(r1), cont);
          PikeActionsConsIff(Areg(r2), cont);
          var s1 := ComputeTree(rer, [Areg(r1)] + cont, inp, gm, dir, f);
          var s2 := ComputeTree(rer, [Areg(r2)] + cont, inp, gm, dir, f);
          if s1.Some? { ComputePikeSubtree(rer, [Areg(r1)] + cont, inp, gm, dir, f, s1.value); }
          if s2.Some? { ComputePikeSubtree(rer, [Areg(r2)] + cont, inp, gm, dir, f, s2.value); }
        case Sequence(r1, r2) =>
          var na := SeqList(r1, r2, dir) + cont;
          assert PikeActions(na) by {
            match dir
            case Forward =>
              assert na == [Areg(r1)] + ([Areg(r2)] + cont);
              PikeActionsConsIff(Areg(r2), cont);
              PikeActionsConsIff(Areg(r1), [Areg(r2)] + cont);
            case Backward =>
              assert na == [Areg(r2)] + ([Areg(r1)] + cont);
              PikeActionsConsIff(Areg(r1), cont);
              PikeActionsConsIff(Areg(r2), [Areg(r1)] + cont);
          }
          var sub := ComputeTree(rer, na, inp, gm, dir, f);
          if sub.Some? { ComputePikeSubtree(rer, na, inp, gm, dir, f, sub.value); }
        case Quantified(greedy, min, delta, r1) =>
          var gidl := DefGroups(r1);
          if min > 0 {
            // forced iteration: Reset then [body, Quantified(min-1)]
            var quant := Quantified(greedy, min - 1, delta, r1);
            var na := [Areg(r1), Areg(quant)] + cont;
            var gm' := GMReset(gidl, gm);
            assert PikeActions(na) by {
              assert na == [Areg(r1)] + ([Areg(quant)] + cont);
              assert PikeRegex(quant);
              PikeActionsConsIff(Areg(quant), cont);
              PikeActionsConsIff(Areg(r1), [Areg(quant)] + cont);
            }
            var sub := ComputeTree(rer, na, inp, gm', dir, f);
            if sub.Some? { ComputePikeSubtree(rer, na, inp, gm', dir, f, sub.value); }
          } else if delta == NN(0) {
            // spent: epsilon-continue
            var sub := ComputeTree(rer, cont, inp, gm, dir, f);
            if sub.Some? { ComputePikeSubtree(rer, cont, inp, gm, dir, f, sub.value); }
          } else {
            var na := [Areg(r1), Acheck(inp), Areg(Quantified(greedy, 0, NoiPred(delta), r1))] + cont;
            var gm' := GMReset(gidl, gm);
            assert PikeActions(na) by {
              assert na == [Areg(r1)] + ([Acheck(inp)] + ([Areg(Quantified(greedy, 0, NoiPred(delta), r1))] + cont));
              assert PikeRegex(Quantified(greedy, 0, NoiPred(delta), r1));
              PikeActionsConsIff(Areg(Quantified(greedy, 0, NoiPred(delta), r1)), cont);
              PikeActionsConsIff(Acheck(inp), [Areg(Quantified(greedy, 0, NoiPred(delta), r1))] + cont);
              PikeActionsConsIff(Areg(r1), [Acheck(inp)] + ([Areg(Quantified(greedy, 0, NoiPred(delta), r1))] + cont));
            }
            var siter := ComputeTree(rer, na, inp, gm', dir, f);
            var sskip := ComputeTree(rer, cont, inp, gm, dir, f);
            if siter.Some? { ComputePikeSubtree(rer, na, inp, gm', dir, f, siter.value); }
            if sskip.Some? { ComputePikeSubtree(rer, cont, inp, gm, dir, f, sskip.value); }
          }
        case Group(gid, r1) =>
          var na := [Areg(r1), Aclose(gid)] + cont;
          var gm' := GMOpen(Idx(inp), gid, gm);
          assert PikeActions(na) by {
            assert na == [Areg(r1)] + ([Aclose(gid)] + cont);
            PikeActionsConsIff(Aclose(gid), cont);
            PikeActionsConsIff(Areg(r1), [Aclose(gid)] + cont);
          }
          var sub := ComputeTree(rer, na, inp, gm', dir, f);
          if sub.Some? { ComputePikeSubtree(rer, na, inp, gm', dir, f, sub.value); }
        case LookaroundR(lk, r1) =>  // not pike: PikeRegex(r) is false, contradiction
        case AnchorR(a) =>
          // zero-width check: satisfied continues with cont unchanged, else Mismatch
          if AnchorSatisfied(rer, a, inp) {
            var sub := ComputeTree(rer, cont, inp, gm, dir, f);
            if sub.Some? { ComputePikeSubtree(rer, cont, inp, gm, dir, f, sub.value); }
          }
        case Backreference(gid) =>   // not pike
    }
  }

  /** The bridge from the relational reference semantics to the pike world: if `IsTree` relates a
      pike action stack `cont` to tree `t`, then `t` is a `PikeSubtree`. Proved by running
      `ComputeTree` (via `ComputeIsTree`'s equivalence) and applying `ComputePikeSubtree`. This is
      what lets `BooleanSemantics`/`TreeRep`/`PikeEquiv` assume every tree they see is pike-shaped. */
  // Coq: pike_actions_pike_tree — proved via the fuel induction + is_tree ⟺ compute_tr.
  lemma PikeActionsPikeTree(rer: RegExpRecord, cont: Actions, inp: Input, gm: GroupMap, dir: Direction, t: Tree)
    requires PikeActions(cont)
    requires IsTree(rer, cont, inp, gm, dir, t)
    ensures PikeSubtree(t)
  {
    var fuel := ActionsFuel(cont, inp, dir) + 1;
    FunctionalTerminates(rer, cont, inp, gm, dir, fuel);
    var opt := ComputeTree(rer, cont, inp, gm, dir, fuel);
    ComputeIsTree.ComputeIsTreeThm(rer, cont, inp, gm, dir, fuel, opt.value);
    IsTreeDeterm(rer, cont, inp, gm, dir, t, opt.value);
    ComputePikeSubtree(rer, cont, inp, gm, dir, fuel, opt.value);
  }
}
