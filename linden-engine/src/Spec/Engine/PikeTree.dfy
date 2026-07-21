// Mirror of Engine/PikeTree.v.
// The PikeTree algorithm: explores ordered tree branches in parallel with memoization, finding the
// first match. Step relation (nondeterministic: a seen tree MAY be skipped), the non-deterministic
// result relations (tree_nd/list_nd/state_nd), the invariant piketreeinv, and its preservation.

/** The **PikeTree** algorithm: a small-step machine that walks a `Tree` directly (rather than
    compiled bytecode), exploring branches in priority order with memoization of already-visited
    subtrees (`SeenTrees`). It sits between the tree semantics (`IsTree`/`TreeRes`) and the
    bytecode-level `PikeVM`, and its result-preservation invariant `Piketreeinv` is what `PikeVM`'s
    own correctness proof (`Correctness.dfy`) ultimately reduces to via `PikeEquiv`. */
module PikeTree {
  import opened Std.Wrappers
  import opened WarblrePrimitives
  import opened Chars
  import opened Groups
  import opened Tree
  import opened PikeSubset
  import opened SeenSets

  // Coq: step_result
  /** The outcome of stepping one `(Tree, GroupMap)` pair: `StepActive` gives the next pairs to
      explore, `StepMatch` signals a `Match` leaf, `StepBlocked` gives the subtree to resume once a
      character (`Read`) is consumed. `StepDead()` is `StepActive([])`, a dead branch. */
  datatype StepResult = StepActive(next: seq<(Tree, GroupMap)>) | StepMatch | StepBlocked(t: Tree)
  function StepDead(): StepResult { StepActive([]) }

  // Coq: tree_bfs_step
  /** One step of tree exploration at index `idx`: descends through `Choice` (both branches),
      `Progress`, and `GroupActionT` (updating `gm` via `GMUpdate`), reports `Match`/`Mismatch`
      directly, and blocks at `Read` (deferring its continuation to the next input position). */
  function TreeBfsStep(t: Tree, gm: GroupMap, idx: nat): StepResult {
    match t
    case Mismatch => StepDead()
    case ReadBackRef(_, _) => StepDead()
    case AnchorPass(_, t1) => StepActive([(t1, gm)])
    case LK(_, _, _) => StepDead()
    case LKFail(_, _) => StepDead()
    case Match => StepMatch
    case Choice(t1, t2) => StepActive([(t1, gm), (t2, gm)])
    case Read(c, t1) => StepBlocked(t1)
    case Progress(t1) => StepActive([(t1, gm)])
    case GroupActionT(a, t1) => StepActive([(t1, GMUpdate(a, idx, gm))])
  }

  // Coq: next_inp
  /** Advances `i` one position forward, discarding the possibility of running off the end (used
      where the caller already knows a `Read` succeeded). */
  function NextInp(i: Input): Input { AdvanceInputP(i, Forward) }

  /** `NextInp` agrees with `AdvanceInput` whenever the latter succeeds. */
  lemma AdvanceNext(i1: Input, i2: Input)
    requires AdvanceInput(i1, Forward) == Some(i2)
    ensures NextInp(i1) == i2
  {}

  // Coq: pike_tree_state
  /** The machine state: `PTS` tracks the current input position, the `active` worklist of
      `(Tree, GroupMap)` pairs still to step, the best `Match` found so far, threads `blocked` on a
      `Read` until the next character, and the `seen` set for memoization; `PTS_final` is the
      halted state carrying the answer. */
  datatype PikeTreeState =
    | PTS(inp: Input, active: seq<(Tree, GroupMap)>, best: Option<Leaf>, blocked: seq<(Tree, GroupMap)>, seen: SeenTrees)
    | PTS_final(best: Option<Leaf>)

  // Coq: pike_tree_step (nondeterministic relation: pts_skip overlaps the active rules when the head
  // tree has been seen).
  /** The nondeterministic step relation: `pts_skip` may (but need not) discard an already-`seen`
      head tree; the other rules (`pts_final`/`pts_nextchar`/`pts_active`/`pts_match`/`pts_blocked`)
      dispatch on `TreeBfsStep` of the active list's head, mirroring `PikeVmStep` one level up
      (tree-level instead of bytecode-level). */
  ghost predicate PikeTreeStep(s1: PikeTreeState, s2: PikeTreeState) {
    match s1
    case PTS_final(_) => false
    case PTS(inp, active, best, blocked, seen) =>
      // pts_skip
      (|active| > 0 && Inseen(seen, active[0].0) && s2 == PTS(inp, active[1..], best, blocked, seen))
      // pts_final
      || (|active| == 0 && |blocked| == 0 && s2 == PTS_final(best))
      // pts_nextchar
      || (|active| == 0 && |blocked| > 0 && s2 == PTS(NextInp(inp), blocked, best, [], InitialSeenTrees))
      // pts_active
      || (|active| > 0 &&
          (match TreeBfsStep(active[0].0, active[0].1, Idx(inp))
           case StepActive(na) => s2 == PTS(inp, na + active[1..], best, blocked, AddSeenTrees(seen, active[0].0))
           case _ => false))
      // pts_match
      || (|active| > 0 &&
          (match TreeBfsStep(active[0].0, active[0].1, Idx(inp))
           case StepMatch => s2 == PTS(inp, [], Some((inp, active[0].1)), blocked, AddSeenTrees(seen, active[0].0))
           case _ => false))
      // pts_blocked
      || (|active| > 0 &&
          (match TreeBfsStep(active[0].0, active[0].1, Idx(inp))
           case StepBlocked(newt) => s2 == PTS(inp, active[1..], best, blocked + [(newt, active[0].1)], AddSeenTrees(seen, active[0].0))
           case _ => false))
  }

  // Coq: pike_tree_initial_state
  /** The initial state for tree `t` on input `i`: one active thread `(t, Empty)`, nothing found,
      nothing blocked, nothing seen. */
  function PikeTreeInitialState(t: Tree, i: Input): PikeTreeState {
    PTS(i, [(t, Empty)], None, [], InitialSeenTrees)
  }

  // Coq: tree_nd — any possible result after skipping (or not) seen subtrees. Recursive on t.
  /** "Nondeterministic tree result": every possible outcome `res` obtainable by walking `t` and
      *optionally* skipping any subtree already in `seen` (the `tr_skip` disjunct). Because skipping
      is optional, `TreeNd` overapproximates what memoized execution can produce; `Piketreeinv` uses
      it to state that memoization never changes the *actual* answer even though it changes what
      could in principle happen along the way. */
  ghost predicate TreeNd(t: Tree, gm: GroupMap, inp: Input, seen: SeenTrees, res: Option<Leaf>)
    decreases t
  {
    (Inseen(seen, t) && res == None)  // tr_skip
    || (match t
        case Mismatch => res == None
        case Match => res == Some((inp, gm))
        case Choice(t1, t2) =>
          exists l1, l2 :: TreeNd(t1, gm, inp, seen, l1) && TreeNd(t2, gm, inp, seen, l2) && res == Seqop(l1, l2)
        case Read(c, t1) => TreeNd(t1, gm, NextInp(inp), seen, res)
        case Progress(t1) => TreeNd(t1, gm, inp, seen, res)
        case AnchorPass(_, t1) => TreeNd(t1, gm, inp, seen, res)
        case GroupActionT(act, t1) => TreeNd(t1, GMUpdate(act, Idx(inp), gm), inp, seen, res)
        case _ => false)
  }

  // Coq: list_result
  /** The combined `TreeRes` of a worklist, computed via `Seqop` (first non-`None` wins) — the
      priority-ordered result of a whole `active`/`blocked` list. */
  function ListResult(l: seq<(Tree, GroupMap)>, inp: Input): Option<Leaf> {
    SeqopList(l, (tgm: (Tree, GroupMap)) => TreeRes(tgm.0, tgm.1, inp, Forward))
  }

  /** `ListResult` unfolds on the head of a `(Tree, GroupMap)` list via `Seqop`. */
  lemma ListResultCons(t: Tree, gm: GroupMap, l: seq<(Tree, GroupMap)>, inp: Input)
    ensures ListResult([(t, gm)] + l, inp) == Seqop(TreeRes(t, gm, inp, Forward), ListResult(l, inp))
  {
    var f := (tgm: (Tree, GroupMap)) => TreeRes(tgm.0, tgm.1, inp, Forward);
    if TreeRes(t, gm, inp, Forward).Some? {
      SeqopListHeadSome((t, gm), l, f, TreeRes(t, gm, inp, Forward).value);
    } else {
      SeqopListHeadNone((t, gm), l, f);
    }
  }

  // Coq: list_nd
  /** The `TreeNd` analogue for a whole list: combines each element's nondeterministic result via
      `Seqop`, in order. */
  ghost predicate ListNd(l: seq<(Tree, GroupMap)>, inp: Input, seen: SeenTrees, res: Option<Leaf>)
    decreases l
  {
    if |l| == 0 then res == None  // tlr_nil
    else exists l1, l2 :: TreeNd(l[0].0, l[0].1, inp, seen, l1) && ListNd(l[1..], inp, seen, l2) && res == Seqop(l1, l2)
  }

  // Coq: state_nd
  /** The possible final results `rseq` of a whole machine state: the already-`blocked` list's
      `ListResult` (resolved at the *next* input), sequenced with the `active` list's `ListNd` and
      the running `best`. */
  ghost predicate StateNd(inp: Input, active: seq<(Tree, GroupMap)>, best: Option<Leaf>, blocked: seq<(Tree, GroupMap)>, seen: SeenTrees, rseq: Option<Leaf>) {
    exists r2 :: ListNd(active, inp, seen, r2) && rseq == Seqop(ListResult(blocked, NextInp(inp)), Seqop(r2, best))
  }

  // Coq: piketreeinv
  /** The central correctness invariant: for `PTS`, every possible nondeterministic outcome
      (`StateNd`) coincides with the fixed target `result`, and both worklists are `PikeList`
      (contain only nodes `PikeSubtree` can reach); for `PTS_final`, `best` simply *is* `result`.
      Established initially by `InitPiketreeInv` and preserved by `PtsPreservation`. */
  ghost predicate Piketreeinv(s: PikeTreeState, result: Option<Leaf>) {
    match s
    case PTS_final(best) => best == result
    case PTS(inp, active, best, blocked, seen) =>
      (forall res :: StateNd(inp, active, best, blocked, seen, res) ==> res == result)
      && PikeList(active) && PikeList(blocked)
  }

  // Coq: size
  /** A structural size on `Tree`, used as a decreasing measure in proofs about parent/child
      subtrees (e.g. `AddParentTree`) where `TreeSize` from `Tree.dfy` isn't the right shape. */
  function Size(t: Tree): nat
    decreases t
  {
    match t
    case Mismatch => 0
    case Match => 0
    case LKFail(_, _) => 0
    case Read(_, t1) => 1 + Size(t1)
    case Progress(t1) => 1 + Size(t1)
    case GroupActionT(_, t1) => 1 + Size(t1)
    case AnchorPass(_, t1) => 1 + Size(t1)
    case ReadBackRef(_, t1) => 1 + Size(t1)
    case Choice(t1, t2) => Size(t1) + Size(t2) + 1
    case LK(_, tlk, t1) => 1 + Size(t1)
  }

  // Coq: no_tree_result — = ResGroupMapIndep (proved in Tree.dfy).
  /** `TreeRes` failing is independent of the group map / input used — a `Mismatch`-shaped subtree
      stays a non-match regardless of context. */
  lemma NoTreeResult(t: Tree, gm1: GroupMap, gm2: GroupMap, inp1: Input, inp2: Input)
    requires TreeRes(t, gm1, inp1, Forward) == None
    ensures TreeRes(t, gm2, inp2, Forward) == None
  {
    ResGroupMapIndep(t, gm1, gm2, inp1, inp2, Forward, Forward);
  }

  // ===== Axiomatized (nd-result inductions + the two named theorems). See PROGRESS.md. =====

  // Coq: list_result_app
  /** `ListResult` distributes over list append via `Seqop`'s associativity. */
  lemma ListResultApp(l1: seq<(Tree, GroupMap)>, l2: seq<(Tree, GroupMap)>, inp: Input)
    ensures ListResult(l1 + l2, inp) == Seqop(ListResult(l1, inp), ListResult(l2, inp))
    decreases l1
  {
    if |l1| == 0 {
      assert l1 + l2 == l2;
      assert ListResult(l1, inp) == None;
    } else {
      var t := l1[0].0;
      var gm := l1[0].1;
      assert l1 == [(t, gm)] + l1[1..];
      assert l1 + l2 == [(t, gm)] + (l1[1..] + l2);
      ListResultCons(t, gm, l1[1..], inp);
      ListResultCons(t, gm, l1[1..] + l2, inp);
      ListResultApp(l1[1..], l2, inp);
      SeqopAssoc(TreeRes(t, gm, inp, Forward), ListResult(l1[1..], inp), ListResult(l2, inp));
    }
  }

  // Coq: tree_res_nd
  /** For any `PikeSubtree`, `TreeRes` is itself a valid `TreeNd` outcome (taking the "don't skip
      anything" branch throughout) — grounds the nondeterministic relation in the deterministic one. */
  lemma TreeResNd(t: Tree, gm: GroupMap, inp: Input, seen: SeenTrees)
    requires PikeSubtree(t)
    ensures TreeNd(t, gm, inp, seen, TreeRes(t, gm, inp, Forward))
    decreases t
  {
    match t
    case Mismatch =>
    case Match =>
    case Choice(t1, t2) =>
      TreeResNd(t1, gm, inp, seen);
      TreeResNd(t2, gm, inp, seen);
      assert TreeNd(t1, gm, inp, seen, TreeRes(t1, gm, inp, Forward));
      assert TreeNd(t2, gm, inp, seen, TreeRes(t2, gm, inp, Forward));
    case Read(c, t1) =>
      TreeResNd(t1, gm, NextInp(inp), seen);
    case Progress(t1) =>
      TreeResNd(t1, gm, inp, seen);
    case GroupActionT(a, t1) =>
      TreeResNd(t1, GMUpdate(a, Idx(inp), gm), inp, seen);
    case ReadBackRef(_, _) =>
    case AnchorPass(_, t1) =>
      TreeResNd(t1, gm, inp, seen);
    case LK(_, _, _) =>
    case LKFail(_, _) =>
  }

  // Coq: tree_nd_initial
  /** With the empty `InitialSeenTrees`, `TreeNd` has no skip option, so it collapses to exactly
      `TreeRes` — the converse of `TreeResNd` for the unmemoized initial state. */
  lemma TreeNdInitial(t: Tree, gm: GroupMap, inp: Input, res: Option<Leaf>)
    requires PikeSubtree(t)
    requires TreeNd(t, gm, inp, InitialSeenTrees, res)
    ensures res == TreeRes(t, gm, inp, Forward)
    decreases t
  {
    InitialNothing(t);  // skip disjunct cannot apply (nothing is in the initial seen set)
    match t
    case Mismatch =>
    case Match =>
    case Choice(t1, t2) =>
      var l1, l2 :| TreeNd(t1, gm, inp, InitialSeenTrees, l1) && TreeNd(t2, gm, inp, InitialSeenTrees, l2) && res == Seqop(l1, l2);
      TreeNdInitial(t1, gm, inp, l1);
      TreeNdInitial(t2, gm, inp, l2);
    case Read(c, t1) =>
      TreeNdInitial(t1, gm, NextInp(inp), res);
    case Progress(t1) =>
      TreeNdInitial(t1, gm, inp, res);
    case GroupActionT(a, t1) =>
      TreeNdInitial(t1, GMUpdate(a, Idx(inp), gm), inp, res);
    case ReadBackRef(_, _) =>
    case AnchorPass(_, _) =>
    case LK(_, _, _) =>
    case LKFail(_, _) =>
  }

  // Coq: list_result_nd
  /** List version of `TreeResNd`: a `PikeList` worklist's `ListResult` is a valid `ListNd` outcome. */
  lemma ListResultNd(active: seq<(Tree, GroupMap)>, inp: Input, seen: SeenTrees)
    requires PikeList(active)
    ensures ListNd(active, inp, seen, ListResult(active, inp))
    decreases active
  {
    if |active| == 0 {
      assert ListResult(active, inp) == None;
    } else {
      var t := active[0].0;
      var gm := active[0].1;
      assert active == [(t, gm)] + active[1..];
      assert PikeSubtree(t);
      assert PikeList(active[1..]) by {
        forall i | 0 <= i < |active[1..]| ensures PikeSubtree(active[1..][i].0) { assert active[1..][i] == active[i + 1]; }
      }
      TreeResNd(t, gm, inp, seen);
      ListResultNd(active[1..], inp, seen);
      ListResultCons(t, gm, active[1..], inp);
    }
  }

  // Coq: list_nd_initial
  /** List version of `TreeNdInitial`: with nothing yet seen, a `ListNd` outcome must be the
      worklist's `ListResult`. */
  lemma ListNdInitial(l: seq<(Tree, GroupMap)>, inp: Input, res: Option<Leaf>)
    requires PikeList(l)
    requires ListNd(l, inp, InitialSeenTrees, res)
    ensures res == ListResult(l, inp)
    decreases l
  {
    if |l| == 0 {
      assert ListResult(l, inp) == None;
    } else {
      var t := l[0].0;
      var gm := l[0].1;
      var l1, l2 :| TreeNd(t, gm, inp, InitialSeenTrees, l1) && ListNd(l[1..], inp, InitialSeenTrees, l2) && res == Seqop(l1, l2);
      assert l == [(t, gm)] + l[1..];
      assert PikeSubtree(t);
      assert PikeList(l[1..]) by {
        forall i | 0 <= i < |l[1..]| ensures PikeSubtree(l[1..][i].0) { assert l[1..][i] == l[i + 1]; }
      }
      TreeNdInitial(t, gm, inp, l1);
      ListNdInitial(l[1..], inp, l2);
      ListResultCons(t, gm, l[1..], inp);
    }
  }

  // Coq: no_tree_result_nd
  /** If `TreeNd` can yield `None` under some `(gm1, inp1)`, it can yield `None` under any other
      `(gm2, inp2)` too — the nondeterministic analogue of `NoTreeResult`. */
  lemma NoTreeResultNd(t: Tree, seen: SeenTrees, gm1: GroupMap, gm2: GroupMap, inp1: Input, inp2: Input)
    requires TreeNd(t, gm1, inp1, seen, None)
    ensures TreeNd(t, gm2, inp2, seen, None)
    decreases t
  {
    if Inseen(seen, t) {
      // skip disjunct holds for any gm/inp
    } else {
      match t
      case Mismatch =>
      case Match =>
      case Choice(t1, t2) =>
        var l1, l2 :| TreeNd(t1, gm1, inp1, seen, l1) && TreeNd(t2, gm1, inp1, seen, l2) && None == Seqop(l1, l2);
        assert l1 == None && l2 == None;
        NoTreeResultNd(t1, seen, gm1, gm2, inp1, inp2);
        NoTreeResultNd(t2, seen, gm1, gm2, inp1, inp2);
        assert TreeNd(t1, gm2, inp2, seen, None) && TreeNd(t2, gm2, inp2, seen, None);
      case Read(c, t1) =>
        NoTreeResultNd(t1, seen, gm1, gm2, NextInp(inp1), NextInp(inp2));
      case Progress(t1) =>
        NoTreeResultNd(t1, seen, gm1, gm2, inp1, inp2);
      case GroupActionT(a, t1) =>
        NoTreeResultNd(t1, seen, GMUpdate(a, Idx(inp1), gm1), GMUpdate(a, Idx(inp2), gm2), inp1, inp2);
      case ReadBackRef(_, _) =>
      case AnchorPass(_, _) =>
      case LK(_, _, _) =>
      case LKFail(_, _) =>
    }
  }

  // Coq: add_seen / list_add_seen
  /** Removing a *failed* tree (`TreeRes = None`) from the seen set doesn't change what `TreeNd` can
      produce: if `tseen` never matches, memoizing it couldn't have changed the outcome, so results
      valid with it `seen` are also valid without it. */
  lemma AddSeen(t: Tree, seen: SeenTrees, tseen: Tree, gm: GroupMap, inp: Input, res: Option<Leaf>)
    requires TreeRes(tseen, gm, inp, Forward) == None
    requires TreeNd(t, gm, inp, AddSeenTrees(seen, tseen), res)
    requires PikeSubtree(tseen)
    ensures TreeNd(t, gm, inp, seen, res)
    decreases t
  {
    if Inseen(AddSeenTrees(seen, tseen), t) && res == None {
      InAdd(seen, t, tseen);
      if t == tseen {
        TreeResNd(tseen, gm, inp, seen);  // TreeNd(tseen, gm, inp, seen, None) = TreeNd(t, gm, inp, seen, res)
      }
    } else {
      match t
      case Mismatch =>
      case Match =>
      case Choice(t1, t2) =>
        var l1, l2 :| TreeNd(t1, gm, inp, AddSeenTrees(seen, tseen), l1) && TreeNd(t2, gm, inp, AddSeenTrees(seen, tseen), l2) && res == Seqop(l1, l2);
        AddSeen(t1, seen, tseen, gm, inp, l1);
        AddSeen(t2, seen, tseen, gm, inp, l2);
      case Read(c, t1) =>
        NoTreeResult(tseen, gm, gm, inp, NextInp(inp));
        AddSeen(t1, seen, tseen, gm, NextInp(inp), res);
      case Progress(t1) =>
        AddSeen(t1, seen, tseen, gm, inp, res);
      case GroupActionT(a, t1) =>
        NoTreeResult(tseen, gm, GMUpdate(a, Idx(inp), gm), inp, inp);
        AddSeen(t1, seen, tseen, GMUpdate(a, Idx(inp), gm), inp, res);
      case ReadBackRef(_, _) =>
      case AnchorPass(_, _) =>
      case LK(_, _, _) =>
      case LKFail(_, _) =>
    }
  }

  /** List version of `AddSeen`. */
  lemma ListAddSeen(l: seq<(Tree, GroupMap)>, seen: SeenTrees, tseen: Tree, gm: GroupMap, inp: Input, res: Option<Leaf>)
    requires TreeRes(tseen, gm, inp, Forward) == None
    requires ListNd(l, inp, AddSeenTrees(seen, tseen), res)
    requires PikeSubtree(tseen)
    ensures ListNd(l, inp, seen, res)
    decreases l
  {
    if |l| == 0 {
    } else {
      var t := l[0].0;
      var gm0 := l[0].1;
      var l1, l2 :| TreeNd(t, gm0, inp, AddSeenTrees(seen, tseen), l1) && ListNd(l[1..], inp, AddSeenTrees(seen, tseen), l2) && res == Seqop(l1, l2);
      NoTreeResult(tseen, gm, gm0, inp, inp);  // TreeRes(tseen, gm0, inp, F) == None
      AddSeen(t, seen, tseen, gm0, inp, l1);
      ListAddSeen(l[1..], seen, tseen, gm, inp, l2);
    }
  }

  // Coq: add_seen_nd / list_add_seen_nd
  /** Like `AddSeen`, but the "failed" hypothesis is itself phrased as `TreeNd(tseen, ..., None)`
      (already-nondeterministic) rather than the deterministic `TreeRes`. */
  lemma AddSeenNd(t: Tree, seen: SeenTrees, tseen: Tree, gm: GroupMap, inp: Input, res: Option<Leaf>)
    requires TreeNd(tseen, gm, inp, seen, None)
    requires TreeNd(t, gm, inp, AddSeenTrees(seen, tseen), res)
    ensures TreeNd(t, gm, inp, seen, res)
    decreases t
  {
    if Inseen(AddSeenTrees(seen, tseen), t) && res == None {
      InAdd(seen, t, tseen);
      // t == tseen: TreeNd(tseen, gm, inp, seen, None) is the hypothesis; else Inseen(seen,t): skip
    } else {
      match t
      case Mismatch =>
      case Match =>
      case Choice(t1, t2) =>
        var l1, l2 :| TreeNd(t1, gm, inp, AddSeenTrees(seen, tseen), l1) && TreeNd(t2, gm, inp, AddSeenTrees(seen, tseen), l2) && res == Seqop(l1, l2);
        AddSeenNd(t1, seen, tseen, gm, inp, l1);
        AddSeenNd(t2, seen, tseen, gm, inp, l2);
      case Read(c, t1) =>
        NoTreeResultNd(tseen, seen, gm, gm, inp, NextInp(inp));
        AddSeenNd(t1, seen, tseen, gm, NextInp(inp), res);
      case Progress(t1) =>
        AddSeenNd(t1, seen, tseen, gm, inp, res);
      case GroupActionT(a, t1) =>
        NoTreeResultNd(tseen, seen, gm, GMUpdate(a, Idx(inp), gm), inp, inp);
        AddSeenNd(t1, seen, tseen, GMUpdate(a, Idx(inp), gm), inp, res);
      case ReadBackRef(_, _) =>
      case AnchorPass(_, _) =>
      case LK(_, _, _) =>
      case LKFail(_, _) =>
    }
  }

  /** List version of `AddSeenNd`. */
  lemma ListAddSeenNd(l: seq<(Tree, GroupMap)>, seen: SeenTrees, tseen: Tree, gm: GroupMap, inp: Input, res: Option<Leaf>)
    requires TreeNd(tseen, gm, inp, seen, None)
    requires ListNd(l, inp, AddSeenTrees(seen, tseen), res)
    ensures ListNd(l, inp, seen, res)
    decreases l
  {
    if |l| == 0 {
    } else {
      var t := l[0].0;
      var gm0 := l[0].1;
      var l1, l2 :| TreeNd(t, gm0, inp, AddSeenTrees(seen, tseen), l1) && ListNd(l[1..], inp, AddSeenTrees(seen, tseen), l2) && res == Seqop(l1, l2);
      NoTreeResultNd(tseen, seen, gm, gm0, inp, inp);  // TreeNd(tseen, gm0, inp, seen, None)
      AddSeenNd(t, seen, tseen, gm0, inp, l1);
      ListAddSeenNd(l[1..], seen, tseen, gm, inp, l2);
    }
  }

  // Coq: add_parent_tree
  /** A *strictly larger* tree (`Size(t) < Size(tseen)`) can never equal one of its own strict
      subtrees, so memoizing an ancestor `tseen` never spuriously triggers the skip case for a
      strictly-smaller descendant `t` — letting it be dropped from `seen` without changing `TreeNd`. */
  lemma AddParentTree(tseen: Tree, t: Tree, res: Option<Leaf>, seen: SeenTrees, gm: GroupMap, inp: Input)
    requires Size(t) < Size(tseen)
    requires TreeNd(t, gm, inp, AddSeenTrees(seen, tseen), res)
    ensures TreeNd(t, gm, inp, seen, res)
    decreases t
  {
    if Inseen(AddSeenTrees(seen, tseen), t) && res == None {
      InAdd(seen, t, tseen);
      // t == tseen would give Size(t) < Size(t), impossible; else Inseen(seen,t): skip
    } else {
      match t
      case Mismatch =>
      case Match =>
      case Choice(t1, t2) =>
        var l1, l2 :| TreeNd(t1, gm, inp, AddSeenTrees(seen, tseen), l1) && TreeNd(t2, gm, inp, AddSeenTrees(seen, tseen), l2) && res == Seqop(l1, l2);
        AddParentTree(tseen, t1, l1, seen, gm, inp);
        AddParentTree(tseen, t2, l2, seen, gm, inp);
      case Read(c, t1) =>
        AddParentTree(tseen, t1, res, seen, gm, NextInp(inp));
      case Progress(t1) =>
        AddParentTree(tseen, t1, res, seen, gm, inp);
      case GroupActionT(a, t1) =>
        AddParentTree(tseen, t1, res, seen, GMUpdate(a, Idx(inp), gm), inp);
      case ReadBackRef(_, _) =>
      case AnchorPass(_, _) =>
      case LK(_, _, _) =>
      case LKFail(_, _) =>
    }
  }

  // Coq: init_piketree_inv (Theorem 11)
  /** **Theorem 11.** The invariant holds at the very start: `Piketreeinv` for
      `PikeTreeInitialState(t, inp)` against target `FirstLeaf(t, inp)` — i.e. before any steps,
      the machine's eventual answer is exactly the highest-priority leaf of `t`. */
  lemma InitPiketreeInv(t: Tree, inp: Input)
    requires PikeSubtree(t)
    ensures Piketreeinv(PikeTreeInitialState(t, inp), FirstLeaf(t, inp))
  {
    var result := FirstLeaf(t, inp);
    assert PikeList([(t, Empty)]);
    forall res | StateNd(inp, [(t, Empty)], None, [], InitialSeenTrees, res)
      ensures res == result
    {
      var r2 :| ListNd([(t, Empty)], inp, InitialSeenTrees, r2)
                && res == Seqop(ListResult([], NextInp(inp)), Seqop(r2, None));
      assert ListResult([], NextInp(inp)) == None;
      assert ListResult([], inp) == None;
      SeqopNone(r2);
      assert res == r2;
      ListNdInitial([(t, Empty)], inp, r2);   // r2 == ListResult([(t,Empty)], inp)
      assert [(t, Empty)] + [] == [(t, Empty)];
      ListResultCons(t, Empty, [], inp);       // ListResult([(t,Empty)], inp) == Seqop(TreeRes(t,Empty,inp,F), None)
      SeqopNone(TreeRes(t, Empty, inp, Forward));
      assert r2 == TreeRes(t, Empty, inp, Forward);
      assert result == TreeRes(t, Empty, inp, Forward);
    }
  }

  // Helper: build a ListNd for (t,gm)::tail from a head TreeNd and a tail ListNd.
  /** Builds a `ListNd` for a list from a `TreeNd` fact about its head and a `ListNd` fact about
      its tail. */
  lemma ListNdCons(t: Tree, gm: GroupMap, tail: seq<(Tree, GroupMap)>, inp: Input, seen: SeenTrees, l1: Option<Leaf>, l2: Option<Leaf>)
    requires TreeNd(t, gm, inp, seen, l1)
    requires ListNd(tail, inp, seen, l2)
    ensures ListNd([(t, gm)] + tail, inp, seen, Seqop(l1, l2))
  {
    assert ([(t, gm)] + tail)[0] == (t, gm);
    assert ([(t, gm)] + tail)[1..] == tail;
  }

  // Coq: pts_preservation (Theorem 12)
  /** **Theorem 12.** Every `PikeTreeStep` preserves `Piketreeinv`: whatever `result` the invariant
      names before the step, it still names it after. Case-splits on which `PikeTreeStep` rule
      fired; the `pts_active`/`pts_blocked` cases delegate to `PtsActiveCase`/`PtsBlockedCase`. This
      is the tree-level analogue of what `PikeEquiv`/`Correctness` prove for the bytecode `PikeVM`. */
  lemma PtsPreservation(pts1: PikeTreeState, pts2: PikeTreeState, res: Option<Leaf>)
    requires PikeTreeStep(pts1, pts2)
    requires Piketreeinv(pts1, res)
    ensures Piketreeinv(pts2, res)
  {
    assert pts1.PTS?;
    var inp, active, best, blocked, seen := pts1.inp, pts1.active, pts1.best, pts1.blocked, pts1.seen;
    if |active| == 0 {
      if |blocked| == 0 {
        // pts_final: pts2 == PTS_final(best); goal best == res.
        assert ListNd([], inp, seen, None);
        assert ListResult([], NextInp(inp)) == None;
        assert StateNd(inp, active, best, blocked, seen, best);
        assert best == res;
      } else {
        // pts_nextchar: pts2 == PTS(NextInp(inp), blocked, best, [], InitialSeenTrees)
        forall r | StateNd(NextInp(inp), blocked, best, [], InitialSeenTrees, r) ensures r == res {
          var r2 :| ListNd(blocked, NextInp(inp), InitialSeenTrees, r2)
                    && r == Seqop(ListResult([], NextInp(NextInp(inp))), Seqop(r2, best));
          assert ListResult([], NextInp(NextInp(inp))) == None;
          ListNdInitial(blocked, NextInp(inp), r2);   // r2 == ListResult(blocked, NextInp(inp))
          assert ListNd([], inp, seen, None);
          assert StateNd(inp, active, best, blocked, seen, r);  // active == []
        }
      }
    } else {
      var t0, gm0 := active[0].0, active[0].1;
      PikeListCons(t0, gm0, active[1..]);   // PikeSubtree(t0) && PikeList(active[1..])
      assert active == [(t0, gm0)] + active[1..];
      if Inseen(seen, t0) && pts2 == PTS(inp, active[1..], best, blocked, seen) {
        // pts_skip
        forall r | StateNd(inp, active[1..], best, blocked, seen, r) ensures r == res {
          var r2 :| ListNd(active[1..], inp, seen, r2)
                    && r == Seqop(ListResult(blocked, NextInp(inp)), Seqop(r2, best));
          assert TreeNd(t0, gm0, inp, seen, None);   // tr_skip (Inseen)
          ListNdCons(t0, gm0, active[1..], inp, seen, None, r2);  // ListNd(active, inp, seen, Seqop(None,r2)=r2)
          assert StateNd(inp, active, best, blocked, seen, r);
        }
      } else {
        match TreeBfsStep(t0, gm0, Idx(inp)) {
          case StepMatch =>
            assert t0 == Match;
            assert pts2 == PTS(inp, [], Some((inp, gm0)), blocked, AddSeenTrees(seen, t0));
            forall r | StateNd(inp, [], Some((inp, gm0)), blocked, AddSeenTrees(seen, t0), r) ensures r == res {
              var r2 :| ListNd([], inp, AddSeenTrees(seen, t0), r2)
                        && r == Seqop(ListResult(blocked, NextInp(inp)), Seqop(r2, Some((inp, gm0))));
              // r2 == None
              ListResultNd(active[1..], inp, seen);   // ListNd(active[1..], inp, seen, ListResult(active[1..],inp))
              assert TreeNd(Match, gm0, inp, seen, Some((inp, gm0)));
              ListNdCons(t0, gm0, active[1..], inp, seen, Some((inp, gm0)), ListResult(active[1..], inp));
              // Seqop(Some,_) == Some((inp,gm0)); so ListNd(active, inp, seen, Some((inp,gm0)))
              assert StateNd(inp, active, best, blocked, seen, r);
            }
          case StepActive(na) =>
            assert pts2 == PTS(inp, na + active[1..], best, blocked, AddSeenTrees(seen, t0));
            PtsActiveCase(inp, active, best, blocked, seen, t0, gm0, na, res);
          case StepBlocked(newt) =>
            assert pts2 == PTS(inp, active[1..], best, blocked + [(newt, gm0)], AddSeenTrees(seen, t0));
            PtsBlockedCase(inp, active, best, blocked, seen, t0, gm0, newt, res);
        }
      }
    }
  }

  // The pts_active case (head expands to children na). Split out to bound verification cost.
  /** The `pts_active` case of `PtsPreservation`: when the active head expands via `StepActive`
      into children `na`, the invariant still holds after splicing `na` into the worklist and
      memoizing the head. */
  lemma PtsActiveCase(inp: Input, active: seq<(Tree, GroupMap)>, best: Option<Leaf>, blocked: seq<(Tree, GroupMap)>, seen: SeenTrees, t0: Tree, gm0: GroupMap, na: seq<(Tree, GroupMap)>, res: Option<Leaf>)
    requires |active| > 0 && active[0] == (t0, gm0)
    requires PikeSubtree(t0) && PikeList(active[1..]) && PikeList(blocked)
    requires forall r :: StateNd(inp, active, best, blocked, seen, r) ==> r == res
    requires TreeBfsStep(t0, gm0, Idx(inp)) == StepActive(na)
    ensures Piketreeinv(PTS(inp, na + active[1..], best, blocked, AddSeenTrees(seen, t0)), res)
  {
    assert active == [(t0, gm0)] + active[1..];
    var seen' := AddSeenTrees(seen, t0);
    var tail := active[1..];
    // PikeSubtree(t0) restricts t0 to Mismatch/Match/Choice/Read/Progress/GroupActionT;
    // StepActive arises only for Mismatch / Choice / Progress / GroupActionT.
    forall r | StateNd(inp, na + tail, best, blocked, seen', r) ensures r == res {
      var r2 :| ListNd(na + tail, inp, seen', r2)
                && r == Seqop(ListResult(blocked, NextInp(inp)), Seqop(r2, best));
      // Establish ListNd(active, inp, seen, r2): head t0 contributes l1 = tree_nd(t0), tail contributes lrest.
      match t0
      case Mismatch =>
        assert na == [];
        assert na + tail == tail;
        ListAddSeen(tail, seen, t0, gm0, inp, r2);   // ListNd(tail, inp, seen, r2)   (TreeRes(Mismatch)=None)
        assert TreeNd(t0, gm0, inp, seen, None);
        ListNdCons(t0, gm0, tail, inp, seen, None, r2);
        assert StateNd(inp, active, best, blocked, seen, r);
      case Progress(t1) =>
        assert na == [(t1, gm0)];
        assert na + tail == [(t1, gm0)] + tail;
        var l1, lrest :| TreeNd(t1, gm0, inp, seen', l1) && ListNd(tail, inp, seen', lrest) && r2 == Seqop(l1, lrest);
        AddParentTree(t0, t1, l1, seen, gm0, inp);    // TreeNd(t1, gm0, inp, seen, l1)
        assert TreeNd(t0, gm0, inp, seen, l1);        // tr_progress
        PtsActiveTail(t0, t1, tail, inp, seen, gm0, gm0, l1, lrest, r2);
        assert StateNd(inp, active, best, blocked, seen, r);
      case AnchorPass(a, t1) =>
        assert na == [(t1, gm0)];
        assert na + tail == [(t1, gm0)] + tail;
        var l1, lrest :| TreeNd(t1, gm0, inp, seen', l1) && ListNd(tail, inp, seen', lrest) && r2 == Seqop(l1, lrest);
        AddParentTree(t0, t1, l1, seen, gm0, inp);    // TreeNd(t1, gm0, inp, seen, l1)
        assert TreeNd(t0, gm0, inp, seen, l1);        // tr_anchorpass
        PtsActiveTail(t0, t1, tail, inp, seen, gm0, gm0, l1, lrest, r2);
        assert StateNd(inp, active, best, blocked, seen, r);
      case GroupActionT(a, t1) =>
        var gm1 := GMUpdate(a, Idx(inp), gm0);
        assert na == [(t1, gm1)];
        assert na + tail == [(t1, gm1)] + tail;
        var l1, lrest :| TreeNd(t1, gm1, inp, seen', l1) && ListNd(tail, inp, seen', lrest) && r2 == Seqop(l1, lrest);
        AddParentTree(t0, t1, l1, seen, gm1, inp);
        assert TreeNd(t0, gm0, inp, seen, l1);        // tr_groupaction
        PtsActiveTail(t0, t1, tail, inp, seen, gm1, gm0, l1, lrest, r2);
        assert StateNd(inp, active, best, blocked, seen, r);
      case Choice(t1, t2) =>
        assert na == [(t1, gm0), (t2, gm0)];
        assert na + tail == [(t1, gm0)] + ([(t2, gm0)] + tail);
        var la, lr1 :| TreeNd(t1, gm0, inp, seen', la) && ListNd([(t2, gm0)] + tail, inp, seen', lr1) && r2 == Seqop(la, lr1);
        var lb, lrest :| TreeNd(t2, gm0, inp, seen', lb) && ListNd(tail, inp, seen', lrest) && lr1 == Seqop(lb, lrest);
        AddParentTree(t0, t1, la, seen, gm0, inp);
        AddParentTree(t0, t2, lb, seen, gm0, inp);
        assert TreeNd(t0, gm0, inp, seen, Seqop(la, lb));   // tr_choice
        PtsActiveTailChoice(t0, t1, t2, tail, inp, seen, gm0, la, lb, lrest, r2);
        assert StateNd(inp, active, best, blocked, seen, r);
      case Match =>
        assert false;   // Match → StepMatch, not StepActive
      case Read(c, t1) =>
        assert false;   // Read → StepBlocked
    }
  }

  // For Progress/GroupAction: reconstruct ListNd(active, inp, seen, r2) from head l1 and tail lrest under seen'.
  /** Helper for `PtsActiveCase`'s `Progress`/`GroupActionT` branches: reconstructs a `ListNd` for
      the whole (head :: tail) list from a `TreeNd` fact about the head and a `ListNd` fact about
      the tail under the head's own membership in `seen`. */
  lemma PtsActiveTail(t0: Tree, t1: Tree, tail: seq<(Tree, GroupMap)>, inp: Input, seen: SeenTrees, gm1: GroupMap, gm0: GroupMap, l1: Option<Leaf>, lrest: Option<Leaf>, r2: Option<Leaf>)
    requires PikeList(tail)
    requires (t0.Progress? && t0.t == t1) || (t0.GroupActionT? && t0.t == t1)
          || (t0.AnchorPass? && t0.t == t1)
    requires TreeNd(t0, gm0, inp, seen, l1)
    requires ListNd(tail, inp, AddSeenTrees(seen, t0), lrest)
    requires r2 == Seqop(l1, lrest)
    ensures ListNd([(t0, gm0)] + tail, inp, seen, r2)
  {
    if l1.Some? {
      ListResultNd(tail, inp, seen);
      ListNdCons(t0, gm0, tail, inp, seen, l1, ListResult(tail, inp));   // Seqop(l1,_) == l1 == r2
    } else {
      ListAddSeenNd(tail, seen, t0, gm0, inp, lrest);                    // ListNd(tail, inp, seen, lrest)
      ListNdCons(t0, gm0, tail, inp, seen, l1, lrest);                   // Seqop(None,lrest) == lrest == r2
    }
  }

  /** The `PtsActiveTail` construction specialized to a `Choice` head, whose two children each
      contribute a nondeterministic result combined via `Seqop`. */
  lemma PtsActiveTailChoice(t0: Tree, t1: Tree, t2: Tree, tail: seq<(Tree, GroupMap)>, inp: Input, seen: SeenTrees, gm0: GroupMap, la: Option<Leaf>, lb: Option<Leaf>, lrest: Option<Leaf>, r2: Option<Leaf>)
    requires PikeList(tail) && t0 == Choice(t1, t2)
    requires TreeNd(t0, gm0, inp, seen, Seqop(la, lb))
    requires ListNd(tail, inp, AddSeenTrees(seen, t0), lrest)
    requires r2 == Seqop(Seqop(la, lb), lrest)
    ensures ListNd([(t0, gm0)] + tail, inp, seen, r2)
  {
    var l1 := Seqop(la, lb);
    if l1.Some? {
      ListResultNd(tail, inp, seen);
      ListNdCons(t0, gm0, tail, inp, seen, l1, ListResult(tail, inp));
    } else {
      ListAddSeenNd(tail, seen, t0, gm0, inp, lrest);
      ListNdCons(t0, gm0, tail, inp, seen, l1, lrest);
    }
  }

  // The pts_blocked case (head Read c t1 blocks; t1 enqueued at the next input).
  /** The `pts_blocked` case of `PtsPreservation`: when the active head is a `Read` that blocks,
      the invariant still holds after moving it (as `newt`) onto `blocked` and memoizing the
      original. */
  lemma PtsBlockedCase(inp: Input, active: seq<(Tree, GroupMap)>, best: Option<Leaf>, blocked: seq<(Tree, GroupMap)>, seen: SeenTrees, t0: Tree, gm0: GroupMap, newt: Tree, res: Option<Leaf>)
    requires |active| > 0 && active[0] == (t0, gm0)
    requires PikeSubtree(t0) && PikeList(active[1..]) && PikeList(blocked)
    requires forall r :: StateNd(inp, active, best, blocked, seen, r) ==> r == res
    requires TreeBfsStep(t0, gm0, Idx(inp)) == StepBlocked(newt)
    ensures Piketreeinv(PTS(inp, active[1..], best, blocked + [(newt, gm0)], AddSeenTrees(seen, t0)), res)
  {
    // StepBlocked arises only from Read; so t0 == Read(c, t1) and newt == t1.
    assert t0.Read? && newt == t0.t;
    var t1 := t0.t;
    assert active == [(t0, gm0)] + active[1..];
    var tail := active[1..];
    var seen' := AddSeenTrees(seen, t0);
    // PikeList(blocked + [(t1, gm0)])
    assert PikeSubtree(t1);
    PikeListSingle(t1, gm0);
    PikeListApp(blocked, [(t1, gm0)]);
    var B := TreeRes(t1, gm0, NextInp(inp), Forward);
    assert TreeRes(t0, gm0, inp, Forward) == B;   // TreeRes(Read c t1) advances the input
    forall r | StateNd(inp, tail, best, blocked + [(newt, gm0)], seen', r) ensures r == res {
      var r2 :| ListNd(tail, inp, seen', r2)
                && r == Seqop(ListResult(blocked + [(t1, gm0)], NextInp(inp)), Seqop(r2, best));
      ListResultApp(blocked, [(t1, gm0)], NextInp(inp));
      ListResultCons(t1, gm0, [], NextInp(inp));
      assert [(t1, gm0)] + [] == [(t1, gm0)];
      assert ListResult([], NextInp(inp)) == None;
      SeqopNone(B);
      assert ListResult([(t1, gm0)], NextInp(inp)) == B;
      assert ListResult(blocked + [(t1, gm0)], NextInp(inp)) == Seqop(ListResult(blocked, NextInp(inp)), B);
      TreeResNd(t0, gm0, inp, seen);   // TreeNd(t0, gm0, inp, seen, B)
      // reconstruct ListNd(active, inp, seen, r2old) with head value B
      var r2old;
      if B.Some? {
        ListResultNd(tail, inp, seen);
        ListNdCons(t0, gm0, tail, inp, seen, B, ListResult(tail, inp));
        r2old := Seqop(B, ListResult(tail, inp));
        assert r2old == B;
        assert Seqop(B, Seqop(r2, best)) == Seqop(r2old, best);
      } else {
        ListAddSeen(tail, seen, t0, gm0, inp, r2);   // TreeRes(t0)=B=None → ListNd(tail, inp, seen, r2)
        ListNdCons(t0, gm0, tail, inp, seen, B, r2);
        r2old := Seqop(B, r2);
        assert r2old == r2;
        assert Seqop(B, Seqop(r2, best)) == Seqop(r2old, best);
      }
      assert ListNd(active, inp, seen, r2old);
      // seqop rearrangement: r == Seqop(ListResult(blocked, NextInp inp), Seqop(r2old, best))
      SeqopAssoc(ListResult(blocked, NextInp(inp)), B, Seqop(r2, best));
      assert r == Seqop(ListResult(blocked, NextInp(inp)), Seqop(r2old, best));
      assert StateNd(inp, active, best, blocked, seen, r);
    }
  }
}
