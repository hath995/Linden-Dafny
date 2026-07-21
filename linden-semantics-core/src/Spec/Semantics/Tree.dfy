// Mirror of Semantics/Tree.v.
// Backtracking trees: all paths a backtracking engine could explore, branches ordered by priority.
include "Regex.dfy"

/** Backtracking trees — the meaning of a regex on an input, made explicit as data.

    A tree records every path a backtracking search could take; its leaves, read
    left-to-right, are the match attempts in ECMAScript priority order. `TreeRes`
    reads off the highest-priority result; `TreeLeaves` lists them all. */
module Tree {
  import opened Std.Wrappers
  import opened WarblrePrimitives  // Direction
  import opened Chars              // Input, advance_input', advance_input_n, init_input, Idx
  import opened Groups             // GroupAction, GroupMap, GMUpdate, Empty
  import opened Regex              // Lookaround, Anchor, positivity, lk_dir

  type String = seq<char>

  // ----- option chaining (Coq seqop) -----
  /** Left-biased choice on `Option`: `o1` if it is `Some`, else `o2`. This is how
      `Choice` priority is resolved when reading a result off a tree. */
  function Seqop<X>(o1: Option<X>, o2: Option<X>): Option<X> {
    match o1 case Some(_) => o1 case None => o2
  }

  lemma SeqopNone<X>(o1: Option<X>)
    ensures Seqop(o1, None) == o1
  {}

  lemma SeqopAssoc<X>(o1: Option<X>, o2: Option<X>, o3: Option<X>)
    ensures Seqop(o1, Seqop(o2, o3)) == Seqop(Seqop(o1, o2), o3)
  {}

  // Coq seqop_list := fold_left (fun y x => seqop y (f x)) l None.
  function SeqopFold<X, Y>(l: seq<X>, f: X -> Option<Y>, acc: Option<Y>): Option<Y>
    decreases |l|
  {
    if |l| == 0 then acc else SeqopFold(l[1..], f, Seqop(acc, f(l[0])))
  }
  function SeqopList<X, Y>(l: seq<X>, f: X -> Option<Y>): Option<Y> { SeqopFold(l, f, None) }

  lemma SeqopSome<X, Y>(l: seq<X>, f: X -> Option<Y>, r: Y)
    ensures SeqopFold(l, f, Some(r)) == Some(r)
  {
    if |l| == 0 {} else { SeqopSome(l[1..], f, r); }
  }

  lemma SeqopListHeadSome<X, Y>(h: X, l: seq<X>, f: X -> Option<Y>, r: Y)
    requires f(h) == Some(r)
    ensures SeqopList([h] + l, f) == Some(r)
  {
    assert ([h] + l)[1..] == l;
    SeqopSome(l, f, r);
  }

  lemma SeqopListHeadNone<X, Y>(h: X, l: seq<X>, f: X -> Option<Y>)
    requires f(h) == None
    ensures SeqopList([h] + l, f) == SeqopList(l, f)
  {
    assert ([h] + l)[1..] == l;
  }

  // ----- backtracking trees -----
  // Coq: Inductive tree. (`GroupAction` constructor renamed `GroupActionT` to avoid clashing with
  // the Groups.GroupAction datatype.)
  /** A backtracking tree. Interior nodes record what the search did; the leaves
      are `Match` (a path that succeeded) and `Mismatch` (a dead end).

      - `Choice(t1, t2)` — `t1` has priority over `t2` (greedy vs. lazy = order).
      - `Read` / `ReadBackRef` — consumed input (a char, or a backreference's text).
      - `Progress` — the empty-iteration guard marker.
      - `GroupActionT` — opened / closed / reset a capture group.
      - `AnchorPass` — a zero-width anchor was satisfied.
      - `LK` / `LKFail` — a lookaround that succeeded (`tlk` = its subtree) / failed. */
  datatype Tree =
    | Mismatch
    | Match
    | Choice(t1: Tree, t2: Tree)
    | Read(c: char, t: Tree)
    | ReadBackRef(str: String, t: Tree)
    | Progress(t: Tree)
    | AnchorPass(a: Anchor, t: Tree)
    | GroupActionT(g: GroupAction, t: Tree)
    | LK(lk: Lookaround, tlk: Tree, t: Tree)
    | LKFail(lk: Lookaround, tlk: Tree)

  // Coq: tree_eq_dec / tree_eqb — native `==` (dropped).

  function NatMax(a: nat, b: nat): nat { if a >= b then a else b }

  // Coq: max_gid_list / max_gid_groupaction / max_gid_tree
  function MaxGidList(gl: seq<GroupId>): nat {
    if |gl| == 0 then 0 else NatMax(gl[0], MaxGidList(gl[1..]))
  }
  function MaxGidGroupAction(act: GroupAction): nat {
    match act case Open(gid) => gid case Close(gid) => gid case Reset(gl) => MaxGidList(gl)
  }
  function MaxGidTree(t: Tree): nat
    decreases t
  {
    match t
    case Mismatch => 0
    case Match => 0
    case Choice(t1, t2) => NatMax(MaxGidTree(t1), MaxGidTree(t2))
    case Read(_, t0) => MaxGidTree(t0)
    case ReadBackRef(_, t0) => MaxGidTree(t0)
    case Progress(t0) => MaxGidTree(t0)
    case AnchorPass(_, t0) => MaxGidTree(t0)
    case GroupActionT(act, t0) => NatMax(MaxGidGroupAction(act), MaxGidTree(t0))
    case LK(_, tlk, t0) => NatMax(MaxGidTree(tlk), MaxGidTree(t0))
    case LKFail(_, tlk) => MaxGidTree(tlk)
  }

  // Coq: greedy_choice
  /** Order two branches by greediness: greedy tries `t1` (iterate) first, lazy
      tries `t2` (skip) first. This one choice is the whole of greedy-vs-lazy. */
  function GreedyChoice(greedy: bool, t1: Tree, t2: Tree): Tree {
    if greedy then Choice(t1, t2) else Choice(t2, t1)
  }

  // ----- tree results -----
  // Coq: leaf := (input * group_map).
  /** One match result: where matching ended (`Input`) together with the captures (`GroupMap`). */
  type Leaf = (Input, GroupMap)

  // Coq: advance_idx / advance_idx_n (backward uses truncated nat subtraction).
  function AdvanceIdx(idx: nat, dir: Direction): nat {
    match dir case Forward => idx + 1 case Backward => if idx >= 1 then idx - 1 else 0
  }
  function AdvanceIdxN(idx: nat, n: nat, dir: Direction): nat {
    match dir case Forward => idx + n case Backward => if idx >= n then idx - n else 0
  }

  // Coq: tree_res — highest-priority result.
  /** The highest-priority result of a tree: walks branches left-to-right (folding
      `Choice` with `Seqop`) and returns the first reachable `Match`. This is the
      match JavaScript returns; `None` means the whole tree fails. */
  function TreeRes(t: Tree, gm: GroupMap, inp: Input, dir: Direction): Option<Leaf>
    decreases t
  {
    match t
    case Mismatch => None
    case Match => Some((inp, gm))
    case Choice(t1, t2) => Seqop(TreeRes(t1, gm, inp, dir), TreeRes(t2, gm, inp, dir))
    case Read(c, t1) => TreeRes(t1, gm, AdvanceInputP(inp, dir), dir)
    case Progress(t1) => TreeRes(t1, gm, inp, dir)
    case GroupActionT(a, t1) => TreeRes(t1, GMUpdate(a, Idx(inp), gm), inp, dir)
    case LK(lk, tlk, t1) =>
      if Positivity(lk) then
        (match TreeRes(tlk, gm, inp, LkDir(lk))
         case None => None
         case Some(pair) => TreeRes(t1, pair.1, inp, dir))
      else
        (match TreeRes(tlk, gm, inp, LkDir(lk))
         case None => TreeRes(t1, gm, inp, dir)
         case Some(_) => None)
    case LKFail(_, _) => None
    case AnchorPass(_, t0) => TreeRes(t0, gm, inp, dir)
    case ReadBackRef(brStr, t0) => TreeRes(t0, gm, AdvanceInputN(inp, |brStr|, dir), dir)
  }

  // Coq: first_branch / first_leaf
  /** `TreeRes` taken from the very start of `str0` — the top-level match of a
      whole regex on a whole string. */
  function FirstBranch(t: Tree, str0: String): Option<Leaf> {
    TreeRes(t, Empty, InitInput(str0), Forward)
  }
  /** `TreeRes` taken from input position `inp` (empty captures, forward). */
  function FirstLeaf(t: Tree, inp: Input): Option<Leaf> {
    TreeRes(t, Empty, inp, Forward)
  }

  // Coq: tree_leaves — ordered list of all results.
  /** Every result of a tree, in priority order — the full backtracking search
      materialized as a sequence. `TreeRes` is its head. */
  function TreeLeaves(t: Tree, gm: GroupMap, inp: Input, dir: Direction): seq<Leaf>
    decreases t
  {
    match t
    case Mismatch => []
    case Match => [(inp, gm)]
    case Choice(t1, t2) => TreeLeaves(t1, gm, inp, dir) + TreeLeaves(t2, gm, inp, dir)
    case Read(c, t1) => TreeLeaves(t1, gm, AdvanceInputP(inp, dir), dir)
    case Progress(t1) => TreeLeaves(t1, gm, inp, dir)
    case GroupActionT(a, t1) => TreeLeaves(t1, GMUpdate(a, Idx(inp), gm), inp, dir)
    case LK(lk, tlk, t1) =>
      if Positivity(lk) then
        var sub := TreeLeaves(tlk, gm, inp, LkDir(lk));
        if |sub| == 0 then [] else TreeLeaves(t1, sub[0].1, inp, dir)
      else
        var sub := TreeLeaves(tlk, gm, inp, LkDir(lk));
        if |sub| == 0 then TreeLeaves(t1, gm, inp, dir) else []
    case LKFail(_, _) => []
    case AnchorPass(_, t0) => TreeLeaves(t0, gm, inp, dir)
    case ReadBackRef(brStr, t0) => TreeLeaves(t0, gm, AdvanceInputN(inp, |brStr|, dir), dir)
  }

  // Coq: hd_error
  function HdError<A>(l: seq<A>): Option<A> { if |l| == 0 then None else Some(l[0]) }

  lemma HdErrorApp<A>(l1: seq<A>, l2: seq<A>)
    ensures HdError(l1 + l2) == (match HdError(l1) case Some(h) => Some(h) case None => HdError(l2))
  {
    if |l1| == 0 { assert l1 + l2 == l2; } else { assert (l1 + l2)[0] == l1[0]; }
  }

  lemma HdErrorNoneNil<A>(l: seq<A>)
    ensures HdError(l) == None <==> l == []
  {}

  // Coq: first_tree_leaf — tree_res = hd_error of tree_leaves.
  /** The highest-priority result is the head of the leaf list:
      `TreeRes(t, …) == HdError(TreeLeaves(t, …))`. Ties `TreeRes` and
      `TreeLeaves` together. */
  lemma FirstTreeLeaf(t: Tree, gm: GroupMap, inp: Input, dir: Direction)
    ensures TreeRes(t, gm, inp, dir) == HdError(TreeLeaves(t, gm, inp, dir))
    decreases t
  {
    match t
    case Choice(t1, t2) =>
      FirstTreeLeaf(t1, gm, inp, dir);
      FirstTreeLeaf(t2, gm, inp, dir);
      HdErrorApp(TreeLeaves(t1, gm, inp, dir), TreeLeaves(t2, gm, inp, dir));
    case Read(c, t1) => FirstTreeLeaf(t1, gm, AdvanceInputP(inp, dir), dir);
    case Progress(t1) => FirstTreeLeaf(t1, gm, inp, dir);
    case GroupActionT(a, t1) => FirstTreeLeaf(t1, GMUpdate(a, Idx(inp), gm), inp, dir);
    case AnchorPass(_, t0) => FirstTreeLeaf(t0, gm, inp, dir);
    case ReadBackRef(brStr, t0) => FirstTreeLeaf(t0, gm, AdvanceInputN(inp, |brStr|, dir), dir);
    case LK(lk, tlk, t1) =>
      FirstTreeLeaf(tlk, gm, inp, LkDir(lk));
      if Positivity(lk) {
        var sub := TreeLeaves(tlk, gm, inp, LkDir(lk));
        if |sub| != 0 { FirstTreeLeaf(t1, sub[0].1, inp, dir); }
      } else {
        FirstTreeLeaf(t1, gm, inp, dir);
      }
    case _ =>
  }

  // Coq: leaves_group_map_indep — emptiness of leaves is independent of gm/inp/dir.
  /** Whether a tree has *no* leaves is purely structural: it does not depend on
      the group map, input position, or direction. */
  lemma LeavesGroupMapIndep(t: Tree, gm1: GroupMap, gm2: GroupMap, inp1: Input, inp2: Input, dir1: Direction, dir2: Direction)
    requires TreeLeaves(t, gm1, inp1, dir1) == []
    ensures TreeLeaves(t, gm2, inp2, dir2) == []
    decreases t
  {
    match t
    case Choice(t1, t2) =>
      assert TreeLeaves(t1, gm1, inp1, dir1) == [];
      assert TreeLeaves(t2, gm1, inp1, dir1) == [];
      LeavesGroupMapIndep(t1, gm1, gm2, inp1, inp2, dir1, dir2);
      LeavesGroupMapIndep(t2, gm1, gm2, inp1, inp2, dir1, dir2);
    case Read(c, t1) => LeavesGroupMapIndep(t1, gm1, gm2, AdvanceInputP(inp1, dir1), AdvanceInputP(inp2, dir2), dir1, dir2);
    case Progress(t1) => LeavesGroupMapIndep(t1, gm1, gm2, inp1, inp2, dir1, dir2);
    case GroupActionT(a, t1) => LeavesGroupMapIndep(t1, GMUpdate(a, Idx(inp1), gm1), GMUpdate(a, Idx(inp2), gm2), inp1, inp2, dir1, dir2);
    case AnchorPass(_, t0) => LeavesGroupMapIndep(t0, gm1, gm2, inp1, inp2, dir1, dir2);
    case ReadBackRef(brStr, t0) => LeavesGroupMapIndep(t0, gm1, gm2, AdvanceInputN(inp1, |brStr|, dir1), AdvanceInputN(inp2, |brStr|, dir2), dir1, dir2);
    case LK(lk, tlk, t1) =>
      var sub1 := TreeLeaves(tlk, gm1, inp1, LkDir(lk));
      var sub2 := TreeLeaves(tlk, gm2, inp2, LkDir(lk));
      if Positivity(lk) {
        // sub1 must be empty (else leaves come from t1 and could be nonempty only if t1 has leaves)
        if |sub1| == 0 {
          LeavesGroupMapIndep(tlk, gm1, gm2, inp1, inp2, LkDir(lk), LkDir(lk));
          assert |sub2| == 0;
        } else {
          // result == TreeLeaves(t1, sub1[0].1, inp1, dir1) == []
          if |sub2| == 0 {
            // sub2 empty -> result empty
          } else {
            LeavesGroupMapIndep(t1, sub1[0].1, sub2[0].1, inp1, inp2, dir1, dir2);
          }
        }
      } else {
        if |sub1| == 0 {
          // result == TreeLeaves(t1, gm1, inp1, dir1) == []
          LeavesGroupMapIndep(tlk, gm1, gm2, inp1, inp2, LkDir(lk), LkDir(lk));
          assert |sub2| == 0;
          LeavesGroupMapIndep(t1, gm1, gm2, inp1, inp2, dir1, dir2);
        } else {
          // result == [] already; need sub2 nonempty too so result stays []
          if |sub2| == 0 {
            // sub2 empty would make result = TreeLeaves(t1,...). Show contradiction: sub1 nonempty
            // but indep says emptiness transfers, so sub2 empty => sub1 empty, contradiction.
            LeavesGroupMapIndep(tlk, gm2, gm1, inp2, inp1, LkDir(lk), LkDir(lk));
            assert |sub1| == 0;
          }
        }
      }
    case _ =>
  }

  // Coq: res_group_map_indep
  /** Whether a tree *fails* (`TreeRes == None`) is independent of the group map,
      input, and direction — a corollary of `LeavesGroupMapIndep`. */
  lemma ResGroupMapIndep(t: Tree, gm1: GroupMap, gm2: GroupMap, inp1: Input, inp2: Input, dir1: Direction, dir2: Direction)
    requires TreeRes(t, gm1, inp1, dir1) == None
    ensures TreeRes(t, gm2, inp2, dir2) == None
  {
    FirstTreeLeaf(t, gm1, inp1, dir1);
    FirstTreeLeaf(t, gm2, inp2, dir2);
    HdErrorNoneNil(TreeLeaves(t, gm1, inp1, dir1));
    LeavesGroupMapIndep(t, gm1, gm2, inp1, inp2, dir1, dir2);
    HdErrorNoneNil(TreeLeaves(t, gm2, inp2, dir2));
  }
}
