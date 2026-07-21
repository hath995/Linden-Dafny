// Mirror of Rewriting/Equivalence.v.
// Leaves-equivalence of regexes and the proof that it permits rewriting under a context. The big
// theorems (leaves_concat, the three context-congruence theorems, observe_equivalence) are
// axiomatized — these are long structural inductions over is_tree / contexts. The setoid `≅` notation
// is dropped; `contextdir`'s Forward/Backward are renamed CtxForward/CtxBackward (clash with Direction).
include "../Semantics/FunctionalUtils.dfy"
include "LeavesEquivalence.dfy"
include "FlatMap.dfy"
include "../Properties/Monotony.dfy"

/** Leaves-equivalence of regexes (`TreeEquiv`/`TreeEquivDir`) and the congruence theorems that let
    you rewrite a sub-regex by an equivalent one anywhere inside a larger regex (`RegexCtx` plugging)
    without changing the observable match (`ObserveEquivalence`). This is the toolkit `Rewriting/`
    exists for. */
module Equivalence {
  import opened Std.Wrappers
  import opened WarblreRegExpRecord
  import opened WarblrePrimitives
  import opened WarblreNumeric
  import opened Chars
  import opened Groups
  import opened Regex
  import opened Tree
  import opened Semantics
  import opened FunctionalSemantics
  import opened ComputeIsTree
  import opened FunctionalUtils
  import opened LeavesEquivalence
  import opened FlatMap
  import Mono = Monotony
  import SS = StrictSuffix

  // Coq: observ_equiv
  /** Two regexes agree observably: from the empty input state, whenever both produce a tree,
      their first (highest-priority) leaf — the actual match result — is the same. */
  ghost predicate ObservEquiv(rer: RegExpRecord, r1: Regex, r2: Regex) {
    forall inp, t1, t2 ::
      IsTree(rer, [Areg(r1)], inp, Empty, Forward, t1) && IsTree(rer, [Areg(r2)], inp, Empty, Forward, t2)
      ==> FirstLeaf(t1, inp) == FirstLeaf(t2, inp)
  }

  // Coq: tree_equiv_tr_dir / tree_nequiv_tr_dir
  /** Two trees (for the same input/groups/direction) have equivalent leaf sequences, i.e. the
      same leaves up to reordering among equal-priority elements (see `LeavesEquiv`). */
  ghost predicate TreeEquivTrDir(i: Input, gm: GroupMap, dir: Direction, tr1: Tree, tr2: Tree) {
    LeavesEquiv([], TreeLeaves(tr1, gm, i, dir), TreeLeaves(tr2, gm, i, dir))
  }
  /** Two trees disagree on their highest-priority result — a witness that they are NOT equivalent. */
  ghost predicate TreeNequivTrDir(i: Input, gm: GroupMap, dir: Direction, tr1: Tree, tr2: Tree) {
    TreeRes(tr1, gm, i, dir) != TreeRes(tr2, gm, i, dir)
  }

  // Coq: actions_equiv_dir / actions_equiv_dir_cond / actions_equiv
  /** Two action stacks produce leaves-equivalent trees from every reachable input/groups state,
      scanning in direction `dir`. The workhorse equivalence used throughout this file's congruence
      proofs; `TreeEquivDir` is defined in terms of it. */
  ghost predicate ActionsEquivDir(rer: RegExpRecord, dir: Direction, acts1: Actions, acts2: Actions) {
    forall inp, gm, t1, t2 ::
      IsTree(rer, acts1, inp, gm, dir, t1) && IsTree(rer, acts2, inp, gm, dir, t2)
      ==> TreeEquivTrDir(inp, gm, dir, t1, t2)
  }
  /** `ActionsEquivDir`, restricted to leaves satisfying a predicate `P` — used when the two
      stacks are only known to agree on a subset of reachable leaves (e.g. position-bounded ones). */
  ghost predicate ActionsEquivDirCond(rer: RegExpRecord, dir: Direction, P: Leaf -> bool, acts1: Actions, acts2: Actions) {
    forall lf: Leaf :: P(lf) ==>
      forall t1, t2 ::
        IsTree(rer, acts1, lf.0, lf.1, dir, t1) && IsTree(rer, acts2, lf.0, lf.1, dir, t2)
        ==> TreeEquivTrDir(lf.0, lf.1, dir, t1, t2)
  }
  /** `ActionsEquivDir` in every scanning direction at once. */
  ghost predicate ActionsEquiv(rer: RegExpRecord, acts1: Actions, acts2: Actions) {
    forall dir :: ActionsEquivDir(rer, dir, acts1, acts2)
  }

  // Coq: tree_equiv_dir / tree_equiv (the regex equivalence `≅[rer][dir]` / `≅[rer]`)
  /** The regex equivalence `r1 ≅[rer][dir] r2`: same defined groups and leaves-equivalent trees
      when scanned in direction `dir`. This is the relation the congruence lemmas below (`SeqCongL`,
      `DisjCongR`, `QuantCong`, `GroupCong`, …) preserve when rewriting sub-regexes. */
  ghost predicate TreeEquivDir(rer: RegExpRecord, dir: Direction, r1: Regex, r2: Regex) {
    DefGroups(r1) == DefGroups(r2) && ActionsEquivDir(rer, dir, [Areg(r1)], [Areg(r2)])
  }
  /** `TreeEquivDir` in every scanning direction — the direction-independent regex equivalence
      `r1 ≅[rer] r2`. */
  ghost predicate TreeEquiv(rer: RegExpRecord, r1: Regex, r2: Regex) {
    forall dir :: TreeEquivDir(rer, dir, r1, r2)
  }

  // Coq: tree_nequiv_dir / tree_nequiv
  /** Witnessed non-equivalence of `r1`/`r2` in direction `dir`: some input/groups state gives
      trees whose highest-priority results differ. */
  ghost predicate TreeNequivDir(rer: RegExpRecord, dir: Direction, r1: Regex, r2: Regex) {
    exists i, gm, tr1, tr2 ::
      IsTree(rer, [Areg(r1)], i, gm, dir, tr1) && IsTree(rer, [Areg(r2)], i, gm, dir, tr2)
      && TreeNequivTrDir(i, gm, dir, tr1, tr2)
  }
  /** Witnessed non-equivalence of `r1`/`r2` in some scanning direction. */
  ghost predicate TreeNequiv(rer: RegExpRecord, r1: Regex, r2: Regex) {
    exists dir :: TreeNequivDir(rer, dir, r1, r2)
  }

  // ----- regex contexts -----
  // Coq: regex_ctx
  /** A regex with a single hole `CHole`, to be `PlugCtx`-filled with a sub-regex. Used to state
      "replacing the sub-regex at this position preserves equivalence" congruence theorems
      (`RegexEquivCtxSamedir`/`Forward`/`Backward`) uniformly over any position in a regex tree. */
  datatype RegexCtx =
    | CHole
    | CDisjunctionL(r1: Regex, c2: RegexCtx)
    | CDisjunctionR(c1: RegexCtx, r2: Regex)
    | CSequenceL(r1: Regex, c2: RegexCtx)
    | CSequenceR(c1: RegexCtx, r2: Regex)
    | CQuantified(greedy: bool, min: nat, delta: NoI, c1: RegexCtx)
    | CLookaround(lk: Lookaround, c1: RegexCtx)
    | CGroup(gid: GroupId, c1: RegexCtx)

  // Coq: plug_ctx
  /** Fill the hole of context `c` with regex `r`, producing a concrete regex. */
  function PlugCtx(c: RegexCtx, r: Regex): Regex
    decreases c
  {
    match c
    case CHole => r
    case CDisjunctionL(r1, c2) => Disjunction(r1, PlugCtx(c2, r))
    case CDisjunctionR(c1, r2) => Disjunction(PlugCtx(c1, r), r2)
    case CSequenceL(r1, c2) => Sequence(r1, PlugCtx(c2, r))
    case CSequenceR(c1, r2) => Sequence(PlugCtx(c1, r), r2)
    case CQuantified(greedy, min, delta, c1) => Quantified(greedy, min, delta, PlugCtx(c1, r))
    case CLookaround(lk, c1) => LookaroundR(lk, PlugCtx(c1, r))
    case CGroup(gid, c1) => Group(gid, PlugCtx(c1, r))
  }

  // Coq: contextdir (Forward/Backward renamed to avoid the Direction clash)
  /** The scanning direction forced on a context's hole: `CtxSame` if no lookaround sits between
      the hole and the top (the outer direction passes through unchanged), else the direction
      fixed by the innermost enclosing lookaround. */
  datatype ContextDir = CtxForward | CtxBackward | CtxSame

  // Coq: ctx_dir
  /** Computes `ctx`'s `ContextDir` by walking from the hole outward, taking the direction of the
      first lookaround encountered (if any). */
  function CtxDir(ctx: RegexCtx): ContextDir
    decreases ctx
  {
    match ctx
    case CHole => CtxSame
    case CDisjunctionL(_, c) => CtxDir(c)
    case CDisjunctionR(c, _) => CtxDir(c)
    case CSequenceL(_, c) => CtxDir(c)
    case CSequenceR(c, _) => CtxDir(c)
    case CQuantified(_, _, _, c) => CtxDir(c)
    case CGroup(_, c) => CtxDir(c)
    case CLookaround(lk, c) =>
      var overrideDir := match LkDir(lk) case Forward => CtxForward case Backward => CtxBackward;
      (match CtxDir(c) case CtxSame => overrideDir case d => d)
  }

  // Coq: act_from_leaf
  /** From leaf `l` (an input/groups pair), resuming action stack `act` produces exactly the
      leaves `mapped`. This is the per-leaf "continuation" relation that `LeavesConcat` shows
      appending actions amounts to flat-mapping over. */
  ghost predicate ActFromLeaf(rer: RegExpRecord, act: Actions, dir: Direction, l: Leaf, mapped: seq<Leaf>) {
    exists t :: IsTree(rer, act, l.0, l.1, dir, t) && mapped == TreeLeaves(t, l.1, l.0, dir)
  }

  // Named partial application of act_from_leaf as the flat-map function (a stable function value, so
  // FlatMapRel(.., ActFromLeafFn(rer, act2, dir), ..) means the same thing in the statement and proof).
  /** `ActFromLeaf` curried on `(rer, act2, dir)`, as a stable function value usable with
      `FlatMapRel`/`FlatMap`'s combinators. */
  ghost function ActFromLeafFn(rer: RegExpRecord, act2: Actions, dir: Direction): (Leaf, seq<Leaf>) -> bool {
    (l, mapped) => ActFromLeaf(rer, act2, dir, l, mapped)
  }

  // ===== Axiomatized theorems (long inductions over is_tree / contexts). See PROGRESS.md. =====

  // Coq: tree_equiv_compute_dir_iff (bridges is_tree and compute_tr definitions)
  /** `TreeEquivDir` restated in terms of `ComputeTr` instead of `IsTree` — lets equivalence
      proofs work with the executable function directly. */
  lemma TreeEquivComputeDirIff(rer: RegExpRecord, dir: Direction, r1: Regex, r2: Regex)
    ensures TreeEquivDir(rer, dir, r1, r2)
        <==> (DefGroups(r1) == DefGroups(r2)
              && forall i, gm :: TreeEquivTrDir(i, gm, dir, ComputeTr(rer, [Areg(r1)], i, gm, dir), ComputeTr(rer, [Areg(r2)], i, gm, dir)))
  {
    if TreeEquivDir(rer, dir, r1, r2) {
      forall i, gm
        ensures TreeEquivTrDir(i, gm, dir, ComputeTr(rer, [Areg(r1)], i, gm, dir), ComputeTr(rer, [Areg(r2)], i, gm, dir))
      {
        ComputeTrEqIsTree(rer, [Areg(r1)], i, gm, dir, ComputeTr(rer, [Areg(r1)], i, gm, dir));
        ComputeTrEqIsTree(rer, [Areg(r2)], i, gm, dir, ComputeTr(rer, [Areg(r2)], i, gm, dir));
      }
    }
    if DefGroups(r1) == DefGroups(r2)
       && (forall i, gm :: TreeEquivTrDir(i, gm, dir, ComputeTr(rer, [Areg(r1)], i, gm, dir), ComputeTr(rer, [Areg(r2)], i, gm, dir))) {
      forall inp, gm, t1, t2
        | IsTree(rer, [Areg(r1)], inp, gm, dir, t1) && IsTree(rer, [Areg(r2)], inp, gm, dir, t2)
        ensures TreeEquivTrDir(inp, gm, dir, t1, t2)
      {
        IsTreeEqComputeTr(rer, [Areg(r1)], inp, gm, dir, t1);   // t1 == ComputeTr(r1 ...)
        IsTreeEqComputeTr(rer, [Areg(r2)], inp, gm, dir, t2);   // t2 == ComputeTr(r2 ...)
      }
      assert ActionsEquivDir(rer, dir, [Areg(r1)], [Areg(r2)]);
    }
  }

  // Fuel-induction core of leaves_concat (mirrors ComputeTree; act2 and the flat-map function stay
  // fixed, the action list act1 is consumed in lockstep with act1+act2). The Choice/free-quantifier
  // cases combine the two sub-results with FlatMapApp.
  /** The fuel-driven induction that proves `LeavesConcat`: as `act1` is consumed running
      `act1 + act2`, the leaves of `act1`'s tree flat-mapped through `act2`'s continuations equal
      the leaves of the combined tree. One case per `Regex`/`Action` constructor, mirroring
      `ComputeTree`. */
  lemma LeavesConcatFuel(
      rer: RegExpRecord, act1: Actions, act2: Actions, inp: Input, gm: GroupMap, dir: Direction,
      fuel: nat, t1: Tree, tapp: Tree)
    requires fuel > ActionsFuel(act1, inp, dir)
    requires fuel > ActionsFuel(act1 + act2, inp, dir)
    requires ComputeTree(rer, act1, inp, gm, dir, fuel) == Some(t1)
    requires ComputeTree(rer, act1 + act2, inp, gm, dir, fuel) == Some(tapp)
    ensures FlatMapRel(TreeLeaves(t1, gm, inp, dir), ActFromLeafFn(rer, act2, dir), TreeLeaves(tapp, gm, inp, dir))
    decreases fuel
  {
    var f := fuel - 1;
    var ff := ActFromLeafFn(rer, act2, dir);
    if |act1| == 0 {
      assert act1 + act2 == act2;
      ComputeIsTreeThm(rer, act2, inp, gm, dir, fuel, tapp);   // IsTree(act2, inp, gm, dir, tapp)
      var lv := TreeLeaves(tapp, gm, inp, dir);
      assert ff((inp, gm), lv);                                 // witness t := tapp
      assert FlatMapRel([], ff, []);
      assert [(inp, gm)][0] == (inp, gm) && [(inp, gm)][1..] == [] && lv == lv + [];
      // FlatMapRel([(inp,gm)], ff, lv) by FM_cons
    } else {
      var cont := act1[1..];
      assert act1 == [act1[0]] + cont;
      assert act1 + act2 == [act1[0]] + (cont + act2);
      assert (act1 + act2)[0] == act1[0] && (act1 + act2)[1..] == cont + act2;
      match act1[0]
      case Acheck(strcheck) =>
        if SS.IsStrictSuffix(inp, strcheck, dir) {
          CheckTermination(cont, inp, strcheck, dir);
          CheckTermination(cont + act2, inp, strcheck, dir);
          var t1c := ComputeTree(rer, cont, inp, gm, dir, f).value;
          var tappc := ComputeTree(rer, cont + act2, inp, gm, dir, f).value;
          LeavesConcatFuel(rer, cont, act2, inp, gm, dir, f, t1c, tappc);
        } else {
          assert FlatMapRel([], ff, []);
        }
      case Aclose(gid) =>
        CloseTermination(cont, inp, dir, gid);
        CloseTermination(cont + act2, inp, dir, gid);
        var gmc := GMClose(Idx(inp), gid, gm);
        var t1c := ComputeTree(rer, cont, inp, gmc, dir, f).value;
        var tappc := ComputeTree(rer, cont + act2, inp, gmc, dir, f).value;
        LeavesConcatFuel(rer, cont, act2, inp, gmc, dir, f, t1c, tappc);
      case Areg(r) =>
        match r
        case Epsilon =>
          EpsilonTermination(cont, inp, dir);
          EpsilonTermination(cont + act2, inp, dir);
          var t1c := ComputeTree(rer, cont, inp, gm, dir, f).value;
          var tappc := ComputeTree(rer, cont + act2, inp, gm, dir, f).value;
          LeavesConcatFuel(rer, cont, act2, inp, gm, dir, f, t1c, tappc);
        case Character(cd) => {
          match ReadChar(rer, cd, inp, dir) {
            case Some(pair) =>
              CharacterTermination(rer, cont, inp, dir, cd, pair.0, pair.1);
              CharacterTermination(rer, cont + act2, inp, dir, cd, pair.0, pair.1);
              var t1c := ComputeTree(rer, cont, pair.1, gm, dir, f).value;
              var tappc := ComputeTree(rer, cont + act2, pair.1, gm, dir, f).value;
              LeavesConcatFuel(rer, cont, act2, pair.1, gm, dir, f, t1c, tappc);
            case None =>
              assert FlatMapRel([], ff, []);
          }
        }
        case Disjunction(r1, r2) =>
          DisjunctionLeftTermination(cont, inp, dir, r1, r2);
          DisjunctionRightTermination(cont, inp, dir, r1, r2);
          DisjunctionLeftTermination(cont + act2, inp, dir, r1, r2);
          DisjunctionRightTermination(cont + act2, inp, dir, r1, r2);
          assert ([Areg(r1)] + cont) + act2 == [Areg(r1)] + (cont + act2);
          assert ([Areg(r2)] + cont) + act2 == [Areg(r2)] + (cont + act2);
          var t1a := ComputeTree(rer, [Areg(r1)] + cont, inp, gm, dir, f).value;
          var t1b := ComputeTree(rer, [Areg(r2)] + cont, inp, gm, dir, f).value;
          var tappa := ComputeTree(rer, ([Areg(r1)] + cont) + act2, inp, gm, dir, f).value;
          var tappb := ComputeTree(rer, ([Areg(r2)] + cont) + act2, inp, gm, dir, f).value;
          LeavesConcatFuel(rer, [Areg(r1)] + cont, act2, inp, gm, dir, f, t1a, tappa);
          LeavesConcatFuel(rer, [Areg(r2)] + cont, act2, inp, gm, dir, f, t1b, tappb);
          FlatMapApp(TreeLeaves(t1a, gm, inp, dir), TreeLeaves(t1b, gm, inp, dir), ff,
                     TreeLeaves(tappa, gm, inp, dir), TreeLeaves(tappb, gm, inp, dir));
        case Sequence(r1, r2) =>
          SequenceTermination(cont, inp, dir, r1, r2);
          SequenceTermination(cont + act2, inp, dir, r1, r2);
          assert (SeqList(r1, r2, dir) + cont) + act2 == SeqList(r1, r2, dir) + (cont + act2);
          var t1c := ComputeTree(rer, SeqList(r1, r2, dir) + cont, inp, gm, dir, f).value;
          var tappc := ComputeTree(rer, (SeqList(r1, r2, dir) + cont) + act2, inp, gm, dir, f).value;
          LeavesConcatFuel(rer, SeqList(r1, r2, dir) + cont, act2, inp, gm, dir, f, t1c, tappc);
        case Quantified(greedy, min, delta, r1) =>
          var gidl := DefGroups(r1);
          if min > 0 {
            var qprev := Quantified(greedy, min - 1, delta, r1);
            QuantForcedTermination(cont, inp, dir, r1, min - 1, delta, greedy);
            QuantForcedTermination(cont + act2, inp, dir, r1, min - 1, delta, greedy);
            assert (min - 1) + 1 == min;
            assert ([Areg(r1), Areg(qprev)] + cont) + act2 == [Areg(r1), Areg(qprev)] + (cont + act2);
            var gmr := GMReset(gidl, gm);
            var t1c := ComputeTree(rer, [Areg(r1), Areg(qprev)] + cont, inp, gmr, dir, f).value;
            var tappc := ComputeTree(rer, ([Areg(r1), Areg(qprev)] + cont) + act2, inp, gmr, dir, f).value;
            LeavesConcatFuel(rer, [Areg(r1), Areg(qprev)] + cont, act2, inp, gmr, dir, f, t1c, tappc);
          } else if delta == NN(0) {
            QuantDoneTermination(cont, inp, dir, r1, greedy);
            QuantDoneTermination(cont + act2, inp, dir, r1, greedy);
            var t1c := ComputeTree(rer, cont, inp, gm, dir, f).value;
            var tappc := ComputeTree(rer, cont + act2, inp, gm, dir, f).value;
            LeavesConcatFuel(rer, cont, act2, inp, gm, dir, f, t1c, tappc);
          } else {
            var qnext := Quantified(greedy, 0, NoiPred(delta), r1);
            var il := [Areg(r1), Acheck(inp), Areg(qnext)] + cont;
            QuantFreeIterTermination(cont, inp, dir, r1, greedy, delta);
            QuantFreeIterTermination(cont + act2, inp, dir, r1, greedy, delta);
            QuantFreeSkipTermination(cont, inp, dir, r1, greedy, delta);
            QuantFreeSkipTermination(cont + act2, inp, dir, r1, greedy, delta);
            assert il + act2 == [Areg(r1), Acheck(inp), Areg(qnext)] + (cont + act2);
            var gmr := GMReset(gidl, gm);
            var t1iter := ComputeTree(rer, il, inp, gmr, dir, f).value;
            var t1skip := ComputeTree(rer, cont, inp, gm, dir, f).value;
            var tappiter := ComputeTree(rer, il + act2, inp, gmr, dir, f).value;
            var tappskip := ComputeTree(rer, cont + act2, inp, gm, dir, f).value;
            LeavesConcatFuel(rer, il, act2, inp, gmr, dir, f, t1iter, tappiter);
            LeavesConcatFuel(rer, cont, act2, inp, gm, dir, f, t1skip, tappskip);
            var XA := GroupActionT(Reset(gidl), t1iter);
            var YA := GroupActionT(Reset(gidl), tappiter);
            assert TreeLeaves(XA, gm, inp, dir) == TreeLeaves(t1iter, gmr, inp, dir);
            assert TreeLeaves(YA, gm, inp, dir) == TreeLeaves(tappiter, gmr, inp, dir);
            if greedy {
              FlatMapApp(TreeLeaves(XA, gm, inp, dir), TreeLeaves(t1skip, gm, inp, dir), ff,
                         TreeLeaves(YA, gm, inp, dir), TreeLeaves(tappskip, gm, inp, dir));
            } else {
              FlatMapApp(TreeLeaves(t1skip, gm, inp, dir), TreeLeaves(XA, gm, inp, dir), ff,
                         TreeLeaves(tappskip, gm, inp, dir), TreeLeaves(YA, gm, inp, dir));
            }
          }
        case Group(gid, r1) =>
          GroupTermination(cont, inp, dir, r1, gid);
          GroupTermination(cont + act2, inp, dir, r1, gid);
          assert ([Areg(r1), Aclose(gid)] + cont) + act2 == [Areg(r1), Aclose(gid)] + (cont + act2);
          var gmo := GMOpen(Idx(inp), gid, gm);
          var t1c := ComputeTree(rer, [Areg(r1), Aclose(gid)] + cont, inp, gmo, dir, f).value;
          var tappc := ComputeTree(rer, ([Areg(r1), Aclose(gid)] + cont) + act2, inp, gmo, dir, f).value;
          LeavesConcatFuel(rer, [Areg(r1), Aclose(gid)] + cont, act2, inp, gmo, dir, f, t1c, tappc);
        case LookaroundR(lk, r1) =>
          LkLkTermination(cont, inp, dir, lk, r1);                  // (body fuel — unused for leaves)
          var treelk := ComputeTree(rer, [Areg(r1)], inp, gm, LkDir(lk), f).value;
          match LkResult(lk, treelk, gm, inp) {
            case Some(gmlk) =>
              LkAfterTermination(cont, inp, dir, lk, r1);
              LkAfterTermination(cont + act2, inp, dir, lk, r1);
              var t1c := ComputeTree(rer, cont, inp, gmlk, dir, f).value;
              var tappc := ComputeTree(rer, cont + act2, inp, gmlk, dir, f).value;
              FirstTreeLeaf(treelk, gm, inp, LkDir(lk));   // connect TreeRes(treelk) and TreeLeaves(treelk)[0]
              if Positivity(lk) {
                var sub := TreeLeaves(treelk, gm, inp, LkDir(lk));
                if |sub| == 0 {
                  assert FlatMapRel([], ff, []);
                } else {
                  assert gmlk == sub[0].1;
                  LeavesConcatFuel(rer, cont, act2, inp, gmlk, dir, f, t1c, tappc);
                }
              } else {
                var sub := TreeLeaves(treelk, gm, inp, LkDir(lk));
                if |sub| == 0 {
                  assert gmlk == gm;
                  LeavesConcatFuel(rer, cont, act2, inp, gmlk, dir, f, t1c, tappc);
                } else {
                  assert FlatMapRel([], ff, []);
                }
              }
            case None =>
              assert FlatMapRel([], ff, []);   // both LKFail
          }
        case AnchorR(a) =>
          if AnchorSatisfied(rer, a, inp) {
            AnchorTermination(cont, inp, dir, a);
            AnchorTermination(cont + act2, inp, dir, a);
            var t1c := ComputeTree(rer, cont, inp, gm, dir, f).value;
            var tappc := ComputeTree(rer, cont + act2, inp, gm, dir, f).value;
            LeavesConcatFuel(rer, cont, act2, inp, gm, dir, f, t1c, tappc);
          } else {
            assert FlatMapRel([], ff, []);
          }
        case Backreference(gid) => {
          match ReadBackref(rer, gm, gid, inp, dir) {
            case Some(pair) =>
              BackrefTermination(rer, cont, inp, dir, gid, gm, pair.0, pair.1);
              BackrefTermination(rer, cont + act2, inp, dir, gid, gm, pair.0, pair.1);
              ReadBackrefSuccessAdvance(rer, gm, gid, inp, dir, pair.0, pair.1);   // pair.1 == AdvanceInputN(inp,|pair.0|,dir)
              var t1c := ComputeTree(rer, cont, pair.1, gm, dir, f).value;
              var tappc := ComputeTree(rer, cont + act2, pair.1, gm, dir, f).value;
              LeavesConcatFuel(rer, cont, act2, pair.1, gm, dir, f, t1c, tappc);
            case None =>
              assert FlatMapRel([], ff, []);
          }
        }
    }
  }

  // Coq: leaves_concat — appending actions corresponds to flat-mapping the leaves.
  /** Appending action stack `act2` after `act1` corresponds to flat-mapping `ActFromLeafFn(act2)`
      over `act1`'s leaves: `TreeLeaves(t1)` flat-mapped gives `TreeLeaves(tapp)`. The fuel-free,
      fuel-existentially-quantified wrapper around `LeavesConcatFuel`. */
  lemma LeavesConcat(rer: RegExpRecord, inp: Input, gm: GroupMap, dir: Direction, act1: Actions, act2: Actions, tapp: Tree, t1: Tree)
    requires IsTree(rer, act1 + act2, inp, gm, dir, tapp)
    requires IsTree(rer, act1, inp, gm, dir, t1)
    ensures FlatMapRel(TreeLeaves(t1, gm, inp, dir),
                       ActFromLeafFn(rer, act2, dir),
                       TreeLeaves(tapp, gm, inp, dir))
  {
    var fuel := ActionsFuel(act1, inp, dir) + ActionsFuel(act1 + act2, inp, dir) + 1;
    FunctionalTerminates(rer, act1, inp, gm, dir, fuel);
    FunctionalTerminates(rer, act1 + act2, inp, gm, dir, fuel);
    var t1' := ComputeTree(rer, act1, inp, gm, dir, fuel).value;
    var tapp' := ComputeTree(rer, act1 + act2, inp, gm, dir, fuel).value;
    ComputeIsTreeThm(rer, act1, inp, gm, dir, fuel, t1');
    ComputeIsTreeThm(rer, act1 + act2, inp, gm, dir, fuel, tapp');
    IsTreeDeterm(rer, act1, inp, gm, dir, t1, t1');
    IsTreeDeterm(rer, act1 + act2, inp, gm, dir, tapp, tapp');
    LeavesConcatFuel(rer, act1, act2, inp, gm, dir, fuel, t1', tapp');
  }

  // Coq: observe_equivalence (Theorem 8) — leaves-equivalence implies the observable (first-match)
  // behaviours agree, since the first leaf is the head of the (equivalent) leaf lists.
  /** The payoff theorem: `TreeEquivDir` (forward) implies `ObservEquiv` — leaves-equivalent
      regexes return the same match. This is why the congruence lemmas below are worth having:
      any rewrite they justify is observably transparent. */
  lemma ObserveEquivalence(rer: RegExpRecord, r1: Regex, r2: Regex)
    requires TreeEquivDir(rer, Forward, r1, r2)
    ensures ObservEquiv(rer, r1, r2)
  {
    forall inp, t1, t2
      | IsTree(rer, [Areg(r1)], inp, Empty, Forward, t1) && IsTree(rer, [Areg(r2)], inp, Empty, Forward, t2)
      ensures FirstLeaf(t1, inp) == FirstLeaf(t2, inp)
    {
      // ActionsEquivDir(rer, Forward, [Areg r1], [Areg r2]) at gm = Empty:
      assert TreeEquivTrDir(inp, Empty, Forward, t1, t2);
      // == LeavesEquiv([], TreeLeaves(t1, Empty, inp, Fwd), TreeLeaves(t2, Empty, inp, Fwd))
      EquivHead(TreeLeaves(t1, Empty, inp, Forward), TreeLeaves(t2, Empty, inp, Forward));
      FirstTreeLeaf(t1, Empty, inp, Forward);   // FirstLeaf == HdError(TreeLeaves)
      FirstTreeLeaf(t2, Empty, inp, Forward);
    }
  }

  // ===== Reusable action-equivalence congruence infrastructure (built on LeavesConcat + FlatMap). =====

  // act_from_leaf for a fixed action list is deterministic (the tree is unique by IsTreeDeterm).
  /** `ActFromLeafFn(rer, cont, dir)` is a deterministic (single-valued) relation, since the tree
      for a fixed action stack and leaf is unique (`IsTreeDeterm`). */
  lemma ActFromLeafDeterm(rer: RegExpRecord, dir: Direction, cont: Actions)
    ensures Determ(ActFromLeafFn(rer, cont, dir))
  {
    forall l, m1, m2 | ActFromLeafFn(rer, cont, dir)(l, m1) && ActFromLeafFn(rer, cont, dir)(l, m2)
      ensures m1 == m2
    {
      assert ActFromLeaf(rer, cont, dir, l, m1) && ActFromLeaf(rer, cont, dir, l, m2);
      var t1 :| IsTree(rer, cont, l.0, l.1, dir, t1) && m1 == TreeLeaves(t1, l.1, l.0, dir);
      var t2 :| IsTree(rer, cont, l.0, l.1, dir, t2) && m2 == TreeLeaves(t2, l.1, l.0, dir);
      IsTreeDeterm(rer, cont, l.0, l.1, dir, t1, t2);
    }
  }

  // If a1, a2 are leaves-equivalent action lists, their act_from_leaf functions are equivalent.
  /** If action stacks `a1`/`a2` are `ActionsEquivDir`-equivalent, their `ActFromLeafFn` values
      agree (as leaf-functions, `EquivLeaffuncts`) on every leaf. */
  lemma ActFromLeafEquiv(rer: RegExpRecord, dir: Direction, a1: Actions, a2: Actions)
    requires ActionsEquivDir(rer, dir, a1, a2)
    ensures EquivLeaffuncts(ActFromLeafFn(rer, a1, dir), ActFromLeafFn(rer, a2, dir))
  {
    forall lf, yf, yg | ActFromLeafFn(rer, a1, dir)(lf, yf) && ActFromLeafFn(rer, a2, dir)(lf, yg)
      ensures LeavesEquiv([], yf, yg)
    {
      assert ActFromLeaf(rer, a1, dir, lf, yf) && ActFromLeaf(rer, a2, dir, lf, yg);
      var t1 :| IsTree(rer, a1, lf.0, lf.1, dir, t1) && yf == TreeLeaves(t1, lf.1, lf.0, dir);
      var t2 :| IsTree(rer, a2, lf.0, lf.1, dir, t2) && yg == TreeLeaves(t2, lf.1, lf.0, dir);
      assert TreeEquivTrDir(lf.0, lf.1, dir, t1, t2);   // from ActionsEquivDir(a1, a2)
    }
  }

  /** `ActionsEquivDir` is reflexive: any action stack is equivalent to itself. */
  lemma ActionsEquivRefl(rer: RegExpRecord, dir: Direction, a: Actions)
    ensures ActionsEquivDir(rer, dir, a, a)
  {
    forall inp, gm, t1, t2 | IsTree(rer, a, inp, gm, dir, t1) && IsTree(rer, a, inp, gm, dir, t2)
      ensures TreeEquivTrDir(inp, gm, dir, t1, t2)
    {
      IsTreeDeterm(rer, a, inp, gm, dir, t1, t2);
      LeavesEquivRefl(TreeLeaves(t1, gm, inp, dir), []);
    }
  }

  /** `ActionsEquivDir` is transitive. */
  lemma ActionsEquivTrans(rer: RegExpRecord, dir: Direction, a: Actions, b: Actions, c: Actions)
    requires ActionsEquivDir(rer, dir, a, b)
    requires ActionsEquivDir(rer, dir, b, c)
    ensures ActionsEquivDir(rer, dir, a, c)
  {
    forall inp, gm, ta, tc | IsTree(rer, a, inp, gm, dir, ta) && IsTree(rer, c, inp, gm, dir, tc)
      ensures TreeEquivTrDir(inp, gm, dir, ta, tc)
    {
      ComputeTrIsTree(rer, b, inp, gm, dir);                 // IsTree(b, .., ComputeTr b)
      var tb := ComputeTr(rer, b, inp, gm, dir);
      assert TreeEquivTrDir(inp, gm, dir, ta, tb);           // from ActionsEquivDir(a, b)
      assert TreeEquivTrDir(inp, gm, dir, tb, tc);           // from ActionsEquivDir(b, c)
      LeavesEquivTrans(TreeLeaves(ta, gm, inp, dir), TreeLeaves(tb, gm, inp, dir), TreeLeaves(tc, gm, inp, dir), []);
    }
  }

  // Prefix congruence: prepending a common prefix preserves action-equivalence (FlatmapLeavesEquivR).
  /** Prepending a common prefix `pre` to two equivalent action stacks keeps them equivalent
      (`pre + a1 ≅ pre + a2`). */
  lemma ActionsEquivPrefix(rer: RegExpRecord, dir: Direction, pre: Actions, a1: Actions, a2: Actions)
    requires ActionsEquivDir(rer, dir, a1, a2)
    ensures ActionsEquivDir(rer, dir, pre + a1, pre + a2)
  {
    forall inp, gm, t1, t2 | IsTree(rer, pre + a1, inp, gm, dir, t1) && IsTree(rer, pre + a2, inp, gm, dir, t2)
      ensures TreeEquivTrDir(inp, gm, dir, t1, t2)
    {
      ComputeTrIsTree(rer, pre, inp, gm, dir);
      var tpre := ComputeTr(rer, pre, inp, gm, dir);
      LeavesConcat(rer, inp, gm, dir, pre, a1, t1, tpre);    // FlatMapRel(TreeLeaves tpre, AFL a1, TreeLeaves t1)
      LeavesConcat(rer, inp, gm, dir, pre, a2, t2, tpre);    // FlatMapRel(TreeLeaves tpre, AFL a2, TreeLeaves t2)
      ActFromLeafEquiv(rer, dir, a1, a2);
      FlatmapLeavesEquivR(TreeLeaves(tpre, gm, inp, dir), ActFromLeafFn(rer, a1, dir), ActFromLeafFn(rer, a2, dir),
                          TreeLeaves(t1, gm, inp, dir), TreeLeaves(t2, gm, inp, dir));
    }
  }

  // Suffix congruence: appending a common suffix preserves action-equivalence (FlatmapLeavesEquivL).
  /** Appending a common suffix `cont` to two equivalent action stacks keeps them equivalent
      (`a1 + cont ≅ a2 + cont`). */
  lemma ActionsEquivSuffix(rer: RegExpRecord, dir: Direction, a1: Actions, a2: Actions, cont: Actions)
    requires ActionsEquivDir(rer, dir, a1, a2)
    ensures ActionsEquivDir(rer, dir, a1 + cont, a2 + cont)
  {
    forall inp, gm, t1, t2 | IsTree(rer, a1 + cont, inp, gm, dir, t1) && IsTree(rer, a2 + cont, inp, gm, dir, t2)
      ensures TreeEquivTrDir(inp, gm, dir, t1, t2)
    {
      ComputeTrIsTree(rer, a1, inp, gm, dir);
      ComputeTrIsTree(rer, a2, inp, gm, dir);
      var ta1 := ComputeTr(rer, a1, inp, gm, dir);
      var ta2 := ComputeTr(rer, a2, inp, gm, dir);
      LeavesConcat(rer, inp, gm, dir, a1, cont, t1, ta1);    // FlatMapRel(TreeLeaves ta1, AFL cont, TreeLeaves t1)
      LeavesConcat(rer, inp, gm, dir, a2, cont, t2, ta2);
      assert TreeEquivTrDir(inp, gm, dir, ta1, ta2);         // from ActionsEquivDir(a1, a2)
      ActFromLeafDeterm(rer, dir, cont);
      FlatmapLeavesEquivL(TreeLeaves(ta1, gm, inp, dir), TreeLeaves(ta2, gm, inp, dir), ActFromLeafFn(rer, cont, dir),
                          TreeLeaves(t1, gm, inp, dir), TreeLeaves(t2, gm, inp, dir));
    }
  }

  // Two action lists with identical computed trees are action-equivalent.
  /** If two action stacks always compute the exact same tree (via `ComputeTr`), they're trivially
      `ActionsEquivDir`-equivalent — a shortcut for when the trees coincide, not just their leaves. */
  lemma ActionsEquivByComputeTr(rer: RegExpRecord, dir: Direction, a: Actions, b: Actions)
    requires forall inp, gm :: ComputeTr(rer, a, inp, gm, dir) == ComputeTr(rer, b, inp, gm, dir)
    ensures ActionsEquivDir(rer, dir, a, b)
  {
    forall inp, gm, ta, tb | IsTree(rer, a, inp, gm, dir, ta) && IsTree(rer, b, inp, gm, dir, tb)
      ensures TreeEquivTrDir(inp, gm, dir, ta, tb)
    {
      IsTreeEqComputeTr(rer, a, inp, gm, dir, ta);
      IsTreeEqComputeTr(rer, b, inp, gm, dir, tb);
      LeavesEquivRefl(TreeLeaves(ta, gm, inp, dir), []);
    }
  }

  // [Areg(Sequence r0 r')] and the flattened SeqList have the same tree (one-step ComputeTr unfold).
  /** `[Areg(Sequence(r0, rp))]` and its one-step unfolding `SeqList(r0, rp, dir)` are equivalent
      action stacks (in both directions) — they compute the same tree. */
  lemma SeqUnfoldEquiv(rer: RegExpRecord, dir: Direction, r0: Regex, rp: Regex)
    ensures ActionsEquivDir(rer, dir, [Areg(Sequence(r0, rp))], SeqList(r0, rp, dir))
    ensures ActionsEquivDir(rer, dir, SeqList(r0, rp, dir), [Areg(Sequence(r0, rp))])
  {
    forall inp, gm
      ensures ComputeTr(rer, [Areg(Sequence(r0, rp))], inp, gm, dir) == ComputeTr(rer, SeqList(r0, rp, dir), inp, gm, dir)
    {
      ComputeTrRw(rer, [Areg(Sequence(r0, rp))], inp, gm, dir);
      assert SeqList(r0, rp, dir) + [] == SeqList(r0, rp, dir);
    }
    ActionsEquivByComputeTr(rer, dir, [Areg(Sequence(r0, rp))], SeqList(r0, rp, dir));
    ActionsEquivByComputeTr(rer, dir, SeqList(r0, rp, dir), [Areg(Sequence(r0, rp))]);
  }

  // ----- per-constructor regex congruences -----
  /** `Sequence` congruence on the right: if `r1 ≅ r2` then `r0 r1 ≅ r0 r2`. */
  lemma SeqCongR(rer: RegExpRecord, dir: Direction, r0: Regex, r1: Regex, r2: Regex)
    requires TreeEquivDir(rer, dir, r1, r2)
    ensures TreeEquivDir(rer, dir, Sequence(r0, r1), Sequence(r0, r2))
  {
    assert DefGroups(r1) == DefGroups(r2);
    SeqUnfoldEquiv(rer, dir, r0, r1);
    SeqUnfoldEquiv(rer, dir, r0, r2);
    match dir {
      case Forward =>
        assert SeqList(r0, r1, dir) == [Areg(r0)] + [Areg(r1)] && SeqList(r0, r2, dir) == [Areg(r0)] + [Areg(r2)];
        ActionsEquivPrefix(rer, dir, [Areg(r0)], [Areg(r1)], [Areg(r2)]);
      case Backward =>
        assert SeqList(r0, r1, dir) == [Areg(r1)] + [Areg(r0)] && SeqList(r0, r2, dir) == [Areg(r2)] + [Areg(r0)];
        ActionsEquivSuffix(rer, dir, [Areg(r1)], [Areg(r2)], [Areg(r0)]);
    }
    ActionsEquivTrans(rer, dir, [Areg(Sequence(r0, r1))], SeqList(r0, r1, dir), SeqList(r0, r2, dir));
    ActionsEquivTrans(rer, dir, [Areg(Sequence(r0, r1))], SeqList(r0, r2, dir), [Areg(Sequence(r0, r2))]);
  }

  /** `Sequence` congruence on the left: if `r1 ≅ r2` then `r1 r0 ≅ r2 r0`. */
  lemma SeqCongL(rer: RegExpRecord, dir: Direction, r0: Regex, r1: Regex, r2: Regex)
    requires TreeEquivDir(rer, dir, r1, r2)
    ensures TreeEquivDir(rer, dir, Sequence(r1, r0), Sequence(r2, r0))
  {
    assert DefGroups(r1) == DefGroups(r2);
    SeqUnfoldEquiv(rer, dir, r1, r0);
    SeqUnfoldEquiv(rer, dir, r2, r0);
    match dir {
      case Forward =>
        assert SeqList(r1, r0, dir) == [Areg(r1)] + [Areg(r0)] && SeqList(r2, r0, dir) == [Areg(r2)] + [Areg(r0)];
        ActionsEquivSuffix(rer, dir, [Areg(r1)], [Areg(r2)], [Areg(r0)]);
      case Backward =>
        assert SeqList(r1, r0, dir) == [Areg(r0)] + [Areg(r1)] && SeqList(r2, r0, dir) == [Areg(r0)] + [Areg(r2)];
        ActionsEquivPrefix(rer, dir, [Areg(r0)], [Areg(r1)], [Areg(r2)]);
    }
    ActionsEquivTrans(rer, dir, [Areg(Sequence(r1, r0))], SeqList(r1, r0, dir), SeqList(r2, r0, dir));
    ActionsEquivTrans(rer, dir, [Areg(Sequence(r1, r0))], SeqList(r2, r0, dir), [Areg(Sequence(r2, r0))]);
  }

  /** `Disjunction` congruence on the right: if `r1 ≅ r2` then `r0|r1 ≅ r0|r2`. */
  lemma DisjCongR(rer: RegExpRecord, dir: Direction, r0: Regex, r1: Regex, r2: Regex)
    requires TreeEquivDir(rer, dir, r1, r2)
    ensures TreeEquivDir(rer, dir, Disjunction(r0, r1), Disjunction(r0, r2))
  {
    forall inp, gm, t1, t2 | IsTree(rer, [Areg(Disjunction(r0, r1))], inp, gm, dir, t1) && IsTree(rer, [Areg(Disjunction(r0, r2))], inp, gm, dir, t2)
      ensures TreeEquivTrDir(inp, gm, dir, t1, t2)
    {
      ComputeTrRw(rer, [Areg(Disjunction(r0, r1))], inp, gm, dir);
      ComputeTrRw(rer, [Areg(Disjunction(r0, r2))], inp, gm, dir);
      IsTreeEqComputeTr(rer, [Areg(Disjunction(r0, r1))], inp, gm, dir, t1);
      IsTreeEqComputeTr(rer, [Areg(Disjunction(r0, r2))], inp, gm, dir, t2);
      assert [Areg(r0)] + [] == [Areg(r0)] && [Areg(r1)] + [] == [Areg(r1)] && [Areg(r2)] + [] == [Areg(r2)];
      var ta := ComputeTr(rer, [Areg(r0)], inp, gm, dir);
      var tb1 := ComputeTr(rer, [Areg(r1)], inp, gm, dir);
      var tb2 := ComputeTr(rer, [Areg(r2)], inp, gm, dir);
      assert t1 == Choice(ta, tb1) && t2 == Choice(ta, tb2);
      ComputeTrIsTree(rer, [Areg(r1)], inp, gm, dir);
      ComputeTrIsTree(rer, [Areg(r2)], inp, gm, dir);
      assert TreeEquivTrDir(inp, gm, dir, tb1, tb2);
      LeavesEquivRefl(TreeLeaves(ta, gm, inp, dir), []);
      LeavesEquivApp(TreeLeaves(ta, gm, inp, dir), TreeLeaves(ta, gm, inp, dir), TreeLeaves(tb1, gm, inp, dir), TreeLeaves(tb2, gm, inp, dir));
    }
  }

  /** `Disjunction` congruence on the left: if `r1 ≅ r2` then `r1|r0 ≅ r2|r0`. */
  lemma DisjCongL(rer: RegExpRecord, dir: Direction, r0: Regex, r1: Regex, r2: Regex)
    requires TreeEquivDir(rer, dir, r1, r2)
    ensures TreeEquivDir(rer, dir, Disjunction(r1, r0), Disjunction(r2, r0))
  {
    forall inp, gm, t1, t2 | IsTree(rer, [Areg(Disjunction(r1, r0))], inp, gm, dir, t1) && IsTree(rer, [Areg(Disjunction(r2, r0))], inp, gm, dir, t2)
      ensures TreeEquivTrDir(inp, gm, dir, t1, t2)
    {
      ComputeTrRw(rer, [Areg(Disjunction(r1, r0))], inp, gm, dir);
      ComputeTrRw(rer, [Areg(Disjunction(r2, r0))], inp, gm, dir);
      IsTreeEqComputeTr(rer, [Areg(Disjunction(r1, r0))], inp, gm, dir, t1);
      IsTreeEqComputeTr(rer, [Areg(Disjunction(r2, r0))], inp, gm, dir, t2);
      assert [Areg(r0)] + [] == [Areg(r0)] && [Areg(r1)] + [] == [Areg(r1)] && [Areg(r2)] + [] == [Areg(r2)];
      var ta := ComputeTr(rer, [Areg(r0)], inp, gm, dir);
      var tb1 := ComputeTr(rer, [Areg(r1)], inp, gm, dir);
      var tb2 := ComputeTr(rer, [Areg(r2)], inp, gm, dir);
      assert t1 == Choice(tb1, ta) && t2 == Choice(tb2, ta);
      ComputeTrIsTree(rer, [Areg(r1)], inp, gm, dir);
      ComputeTrIsTree(rer, [Areg(r2)], inp, gm, dir);
      assert TreeEquivTrDir(inp, gm, dir, tb1, tb2);
      LeavesEquivRefl(TreeLeaves(ta, gm, inp, dir), []);
      LeavesEquivApp(TreeLeaves(tb1, gm, inp, dir), TreeLeaves(tb2, gm, inp, dir), TreeLeaves(ta, gm, inp, dir), TreeLeaves(ta, gm, inp, dir));
    }
  }

  /** `Group` congruence: if `r1 ≅ r2` then wrapping either in the same capturing group `gid`
      keeps them equivalent. */
  lemma GroupCong(rer: RegExpRecord, dir: Direction, gid: GroupId, r1: Regex, r2: Regex)
    requires TreeEquivDir(rer, dir, r1, r2)
    ensures TreeEquivDir(rer, dir, Group(gid, r1), Group(gid, r2))
  {
    ActionsEquivSuffix(rer, dir, [Areg(r1)], [Areg(r2)], [Aclose(gid)]);
    forall inp, gm, tg1, tg2 | IsTree(rer, [Areg(Group(gid, r1))], inp, gm, dir, tg1) && IsTree(rer, [Areg(Group(gid, r2))], inp, gm, dir, tg2)
      ensures TreeEquivTrDir(inp, gm, dir, tg1, tg2)
    {
      ComputeTrRw(rer, [Areg(Group(gid, r1))], inp, gm, dir);
      ComputeTrRw(rer, [Areg(Group(gid, r2))], inp, gm, dir);
      IsTreeEqComputeTr(rer, [Areg(Group(gid, r1))], inp, gm, dir, tg1);
      IsTreeEqComputeTr(rer, [Areg(Group(gid, r2))], inp, gm, dir, tg2);
      var gmo := GMOpen(Idx(inp), gid, gm);
      assert [Areg(r1), Aclose(gid)] + [] == [Areg(r1), Aclose(gid)] && [Areg(r2), Aclose(gid)] + [] == [Areg(r2), Aclose(gid)];
      assert [Areg(r1)] + [Aclose(gid)] == [Areg(r1), Aclose(gid)] && [Areg(r2)] + [Aclose(gid)] == [Areg(r2), Aclose(gid)];
      var tc1 := ComputeTr(rer, [Areg(r1), Aclose(gid)], inp, gmo, dir);
      var tc2 := ComputeTr(rer, [Areg(r2), Aclose(gid)], inp, gmo, dir);
      assert tg1 == GroupActionT(Open(gid), tc1) && tg2 == GroupActionT(Open(gid), tc2);
      assert GMUpdate(Open(gid), Idx(inp), gm) == gmo;
      ComputeTrIsTree(rer, [Areg(r1), Aclose(gid)], inp, gmo, dir);
      ComputeTrIsTree(rer, [Areg(r2), Aclose(gid)], inp, gmo, dir);
      assert TreeEquivTrDir(inp, gmo, dir, tc1, tc2);
    }
  }

  // ----- quantifier-body congruence (the well-founded-on-input loop unrolling) -----

  // The position-bound predicate used to restrict the flat-map congruence to the leaves actually
  // produced by the body (which, by monotony, never sit further back than the start).
  /** Whether leaf `lf` sits at or beyond `inp` in direction `dir` — i.e. hasn't overshot `inp`.
      By monotony (`Mono.TreeLeavesRemaining`), every leaf a quantifier body produces from `inp`
      satisfies this, which is what lets the quantifier congruence restrict its leaf-function
      equivalence hypothesis to just these leaves. */
  ghost function LeafBoundedBy(inp: Input, dir: Direction): Leaf -> bool {
    (lf: Leaf) => RemainingLength(lf.0, dir) <= RemainingLength(inp, dir)
  }

  // act_from_leaf is total, so the flat-map over any leaf list exists.
  /** `ActFromLeafFn(rer, K, dir)` is total: some flat-mapped result `FL` exists for any leaf list `L`. */
  lemma FlatMapActFromLeafExists(L: seq<Leaf>, rer: RegExpRecord, K: Actions, dir: Direction) returns (FL: seq<Leaf>)
    ensures FlatMapRel(L, ActFromLeafFn(rer, K, dir), FL)
    decreases L
  {
    if |L| == 0 {
      FL := [];
    } else {
      var rest := FlatMapActFromLeafExists(L[1..], rer, K, dir);
      ComputeTrIsTree(rer, K, L[0].0, L[0].1, dir);
      var ly := TreeLeaves(ComputeTr(rer, K, L[0].0, L[0].1, dir), L[0].1, L[0].0, dir);
      assert ActFromLeafFn(rer, K, dir)(L[0], ly);
      FL := ly + rest;
    }
  }

  // Composition: appending continuation K1/K2 after equivalent bodies r1/r2, where K1≅K2 on every
  // leaf the bodies can reach (the position-bounded leaves), preserves leaves-equivalence.
  /** If bodies `r1 ≅ r2` and continuations `K1`/`K2` agree on every leaf the bodies can reach
      (`LeafBoundedBy`), then `[Areg(r1)] + K1` and `[Areg(r2)] + K2` produce leaves-equivalent
      trees. The composition step used to unroll one quantifier iteration in `QuantCongAt`. */
  lemma QuantIterEquiv(rer: RegExpRecord, dir: Direction, r1: Regex, r2: Regex, K1: Actions, K2: Actions, inp: Input, gm: GroupMap)
    requires ActionsEquivDir(rer, dir, [Areg(r1)], [Areg(r2)])
    requires EquivLeaffunctsCond(ActFromLeafFn(rer, K1, dir), ActFromLeafFn(rer, K2, dir), LeafBoundedBy(inp, dir))
    ensures LeavesEquiv([], TreeLeaves(ComputeTr(rer, [Areg(r1)] + K1, inp, gm, dir), gm, inp, dir),
                            TreeLeaves(ComputeTr(rer, [Areg(r2)] + K2, inp, gm, dir), gm, inp, dir))
  {
    ComputeTrIsTree(rer, [Areg(r1)], inp, gm, dir);
    ComputeTrIsTree(rer, [Areg(r2)], inp, gm, dir);
    var tb1 := ComputeTr(rer, [Areg(r1)], inp, gm, dir);
    var tb2 := ComputeTr(rer, [Areg(r2)], inp, gm, dir);
    var L1 := TreeLeaves(tb1, gm, inp, dir);
    var L2 := TreeLeaves(tb2, gm, inp, dir);
    var t1 := ComputeTr(rer, [Areg(r1)] + K1, inp, gm, dir);
    var t2 := ComputeTr(rer, [Areg(r2)] + K2, inp, gm, dir);
    ComputeTrIsTree(rer, [Areg(r1)] + K1, inp, gm, dir);
    ComputeTrIsTree(rer, [Areg(r2)] + K2, inp, gm, dir);
    LeavesConcat(rer, inp, gm, dir, [Areg(r1)], K1, t1, tb1);   // FlatMapRel(L1, AFL K1, TreeLeaves t1)
    LeavesConcat(rer, inp, gm, dir, [Areg(r2)], K2, t2, tb2);   // FlatMapRel(L2, AFL K2, TreeLeaves t2)
    var FL2 := FlatMapActFromLeafExists(L2, rer, K1, dir);       // FlatMapRel(L2, AFL K1, FL2)
    assert TreeEquivTrDir(inp, gm, dir, tb1, tb2);               // L1 ≅ L2 from ActionsEquivDir
    ActFromLeafDeterm(rer, dir, K1);
    FlatmapLeavesEquivL(L1, L2, ActFromLeafFn(rer, K1, dir), TreeLeaves(t1, gm, inp, dir), FL2);   // TreeLeaves t1 ≅ FL2
    forall i | 0 <= i < |L2| ensures LeafBoundedBy(inp, dir)(L2[i]) {
      assert L2[i] in L2;
      Mono.TreeLeavesRemaining(tb2, gm, inp, dir, L2[i]);
    }
    FlatmapLeavesEquivRProp(L2, ActFromLeafFn(rer, K1, dir), ActFromLeafFn(rer, K2, dir), FL2, TreeLeaves(t2, gm, inp, dir), LeafBoundedBy(inp, dir));   // FL2 ≅ TreeLeaves t2
    LeavesEquivTrans(TreeLeaves(t1, gm, inp, dir), FL2, TreeLeaves(t2, gm, inp, dir), []);
  }

  // The quantifier-body congruence, positional form: induction on (remaining input, min).
  /** The core of `QuantCong`, at a fixed input/groups state: if `r1 ≅ r2`, the quantifiers
      `Quantified(greedy, min, delta, r1)` and `..r2` produce leaves-equivalent trees. Proved by
      induction on `(RemainingLength(inp, dir), min)`, unrolling one iteration at a time via
      `QuantIterEquiv` and the forced/free per-leaf lemmas below. */
  lemma QuantCongAt(rer: RegExpRecord, dir: Direction, greedy: bool, min: nat, delta: NoI, r1: Regex, r2: Regex, inp: Input, gm: GroupMap)
    requires TreeEquivDir(rer, dir, r1, r2)
    ensures LeavesEquiv([], TreeLeaves(ComputeTr(rer, [Areg(Quantified(greedy, min, delta, r1))], inp, gm, dir), gm, inp, dir),
                            TreeLeaves(ComputeTr(rer, [Areg(Quantified(greedy, min, delta, r2))], inp, gm, dir), gm, inp, dir))
    decreases RemainingLength(inp, dir), min, 2
  {
    ComputeTrRw(rer, [Areg(Quantified(greedy, min, delta, r1))], inp, gm, dir);
    ComputeTrRw(rer, [Areg(Quantified(greedy, min, delta, r2))], inp, gm, dir);
    var gidl := DefGroups(r1);
    assert DefGroups(r1) == DefGroups(r2);
    var t1 := ComputeTr(rer, [Areg(Quantified(greedy, min, delta, r1))], inp, gm, dir);
    var t2 := ComputeTr(rer, [Areg(Quantified(greedy, min, delta, r2))], inp, gm, dir);
    assert ActionsEquivDir(rer, dir, [Areg(r1)], [Areg(r2)]);
    if min > 0 {
      var K1 := [Areg(Quantified(greedy, min - 1, delta, r1))];
      var K2 := [Areg(Quantified(greedy, min - 1, delta, r2))];
      var gmr := GMReset(gidl, gm);
      forall lf, yf, yg | LeafBoundedBy(inp, dir)(lf) && ActFromLeafFn(rer, K1, dir)(lf, yf) && ActFromLeafFn(rer, K2, dir)(lf, yg)
        ensures LeavesEquiv([], yf, yg)
      {
        ForcedLeafEquiv(rer, dir, greedy, min, delta, r1, r2, inp, lf, yf, yg);
      }
      assert EquivLeaffunctsCond(ActFromLeafFn(rer, K1, dir), ActFromLeafFn(rer, K2, dir), LeafBoundedBy(inp, dir));
      QuantIterEquiv(rer, dir, r1, r2, K1, K2, inp, gmr);
      assert [Areg(r1), Areg(Quantified(greedy, min - 1, delta, r1))] + [] == [Areg(r1)] + K1;
      assert [Areg(r2), Areg(Quantified(greedy, min - 1, delta, r2))] + [] == [Areg(r2)] + K2;
      assert GMUpdate(Reset(gidl), Idx(inp), gm) == gmr && GMUpdate(Reset(DefGroups(r2)), Idx(inp), gm) == gmr;
      assert t1 == GroupActionT(Reset(gidl), ComputeTr(rer, [Areg(r1)] + K1, inp, gmr, dir));
      assert t2 == GroupActionT(Reset(DefGroups(r2)), ComputeTr(rer, [Areg(r2)] + K2, inp, gmr, dir));
      assert TreeLeaves(t1, gm, inp, dir) == TreeLeaves(ComputeTr(rer, [Areg(r1)] + K1, inp, gmr, dir), gmr, inp, dir);
      assert TreeLeaves(t2, gm, inp, dir) == TreeLeaves(ComputeTr(rer, [Areg(r2)] + K2, inp, gmr, dir), gmr, inp, dir);
    } else if delta == NN(0) {
      LeavesEquivRefl(TreeLeaves(t1, gm, inp, dir), []);   // both trees == ComputeTr([], ..) == Match
    } else {
      var K1 := [Acheck(inp), Areg(Quantified(greedy, 0, NoiPred(delta), r1))];
      var K2 := [Acheck(inp), Areg(Quantified(greedy, 0, NoiPred(delta), r2))];
      var gmr := GMReset(gidl, gm);
      forall lf, yf, yg | LeafBoundedBy(inp, dir)(lf) && ActFromLeafFn(rer, K1, dir)(lf, yf) && ActFromLeafFn(rer, K2, dir)(lf, yg)
        ensures LeavesEquiv([], yf, yg)
      {
        FreeLeafEquiv(rer, dir, greedy, delta, r1, r2, inp, lf, yf, yg);
      }
      assert EquivLeaffunctsCond(ActFromLeafFn(rer, K1, dir), ActFromLeafFn(rer, K2, dir), LeafBoundedBy(inp, dir));
      QuantIterEquiv(rer, dir, r1, r2, K1, K2, inp, gmr);
      // iter leaves of r1 ≅ r2; the skip branch ([(inp,gm)]) is identical, combine via LeavesEquivApp.
      var iter1 := ComputeTr(rer, [Areg(r1)] + K1, inp, gmr, dir);
      var iter2 := ComputeTr(rer, [Areg(r2)] + K2, inp, gmr, dir);
      var skip := ComputeTr(rer, [], inp, gm, dir);   // Match
      ComputeTrRw(rer, [], inp, gm, dir);
      assert [Areg(r1), Acheck(inp), Areg(Quantified(greedy, 0, NoiPred(delta), r1))] + [] == [Areg(r1)] + K1;
      assert [Areg(r2), Acheck(inp), Areg(Quantified(greedy, 0, NoiPred(delta), r2))] + [] == [Areg(r2)] + K2;
      var IL1 := TreeLeaves(iter1, gmr, inp, dir);
      var IL2 := TreeLeaves(iter2, gmr, inp, dir);
      var SL := TreeLeaves(skip, gm, inp, dir);
      assert GMUpdate(Reset(gidl), Idx(inp), gm) == gmr && GMUpdate(Reset(DefGroups(r2)), Idx(inp), gm) == gmr;
      assert t1 == GreedyChoice(greedy, GroupActionT(Reset(gidl), iter1), skip);
      assert t2 == GreedyChoice(greedy, GroupActionT(Reset(DefGroups(r2)), iter2), skip);
      assert TreeLeaves(GroupActionT(Reset(gidl), iter1), gm, inp, dir) == IL1;
      assert TreeLeaves(GroupActionT(Reset(DefGroups(r2)), iter2), gm, inp, dir) == IL2;
      LeavesEquivRefl(SL, []);
      if greedy {
        assert TreeLeaves(t1, gm, inp, dir) == IL1 + SL && TreeLeaves(t2, gm, inp, dir) == IL2 + SL;
        LeavesEquivApp(IL1, IL2, SL, SL);   // IL1+SL ≅ IL2+SL
      } else {
        assert TreeLeaves(t1, gm, inp, dir) == SL + IL1 && TreeLeaves(t2, gm, inp, dir) == SL + IL2;
        LeavesEquivApp(SL, SL, IL1, IL2);   // SL+IL1 ≅ SL+IL2
      }
    }
  }

  // The forced-iteration leaf equivalence: the continuation [Areg(Quant min-1 _)] is equivalent on
  // any bounded leaf, by the IH at min-1.
  /** The per-leaf equivalence hypothesis `QuantIterEquiv` needs for a forced iteration (`min > 0`):
      continuing with `Quantified(.., min-1, .., r1/r2)` agrees on any bounded leaf, by the
      induction hypothesis of `QuantCongAt` at `min - 1`. */
  lemma ForcedLeafEquiv(rer: RegExpRecord, dir: Direction, greedy: bool, min: nat, delta: NoI, r1: Regex, r2: Regex, inp: Input, lf: Leaf, yf: seq<Leaf>, yg: seq<Leaf>)
    requires min > 0
    requires TreeEquivDir(rer, dir, r1, r2)
    requires RemainingLength(lf.0, dir) <= RemainingLength(inp, dir)
    requires ActFromLeafFn(rer, [Areg(Quantified(greedy, min - 1, delta, r1))], dir)(lf, yf)
    requires ActFromLeafFn(rer, [Areg(Quantified(greedy, min - 1, delta, r2))], dir)(lf, yg)
    ensures LeavesEquiv([], yf, yg)
    decreases RemainingLength(inp, dir), min, 0
  {
    var K1 := [Areg(Quantified(greedy, min - 1, delta, r1))];
    var K2 := [Areg(Quantified(greedy, min - 1, delta, r2))];
    assert ActFromLeaf(rer, K1, dir, lf, yf) && ActFromLeaf(rer, K2, dir, lf, yg);
    var s1 :| IsTree(rer, K1, lf.0, lf.1, dir, s1) && yf == TreeLeaves(s1, lf.1, lf.0, dir);
    var s2 :| IsTree(rer, K2, lf.0, lf.1, dir, s2) && yg == TreeLeaves(s2, lf.1, lf.0, dir);
    ComputeTrIsTree(rer, K1, lf.0, lf.1, dir);
    ComputeTrIsTree(rer, K2, lf.0, lf.1, dir);
    IsTreeDeterm(rer, K1, lf.0, lf.1, dir, s1, ComputeTr(rer, K1, lf.0, lf.1, dir));
    IsTreeDeterm(rer, K2, lf.0, lf.1, dir, s2, ComputeTr(rer, K2, lf.0, lf.1, dir));
    QuantCongAt(rer, dir, greedy, min - 1, delta, r1, r2, lf.0, lf.1);
  }

  // The free-iteration leaf equivalence: the loop-progress check kills non-advancing leaves; on
  // advancing leaves the remaining input strictly decreases, so the IH applies.
  /** The per-leaf equivalence hypothesis `QuantIterEquiv` needs for a free iteration (unbounded
      repeat, `min == 0`): the `Acheck` progress guard kills non-advancing leaves outright (both
      sides empty), and on advancing leaves the remaining input strictly decreases, so
      `QuantCongAt`'s induction hypothesis applies. This is the empty-loop-guard reasoning
      the README calls out, specialized to equivalence proofs. */
  lemma FreeLeafEquiv(rer: RegExpRecord, dir: Direction, greedy: bool, delta: NoI, r1: Regex, r2: Regex, inp: Input, lf: Leaf, yf: seq<Leaf>, yg: seq<Leaf>)
    requires TreeEquivDir(rer, dir, r1, r2)
    requires RemainingLength(lf.0, dir) <= RemainingLength(inp, dir)
    requires ActFromLeafFn(rer, [Acheck(inp), Areg(Quantified(greedy, 0, NoiPred(delta), r1))], dir)(lf, yf)
    requires ActFromLeafFn(rer, [Acheck(inp), Areg(Quantified(greedy, 0, NoiPred(delta), r2))], dir)(lf, yg)
    ensures LeavesEquiv([], yf, yg)
    decreases RemainingLength(inp, dir), 0, 1
  {
    var K1 := [Acheck(inp), Areg(Quantified(greedy, 0, NoiPred(delta), r1))];
    var K2 := [Acheck(inp), Areg(Quantified(greedy, 0, NoiPred(delta), r2))];
    assert ActFromLeaf(rer, K1, dir, lf, yf) && ActFromLeaf(rer, K2, dir, lf, yg);
    var s1 :| IsTree(rer, K1, lf.0, lf.1, dir, s1) && yf == TreeLeaves(s1, lf.1, lf.0, dir);
    var s2 :| IsTree(rer, K2, lf.0, lf.1, dir, s2) && yg == TreeLeaves(s2, lf.1, lf.0, dir);
    ComputeTrIsTree(rer, K1, lf.0, lf.1, dir);
    ComputeTrIsTree(rer, K2, lf.0, lf.1, dir);
    IsTreeDeterm(rer, K1, lf.0, lf.1, dir, s1, ComputeTr(rer, K1, lf.0, lf.1, dir));
    IsTreeDeterm(rer, K2, lf.0, lf.1, dir, s2, ComputeTr(rer, K2, lf.0, lf.1, dir));
    ComputeTrRw(rer, K1, lf.0, lf.1, dir);
    ComputeTrRw(rer, K2, lf.0, lf.1, dir);
    if SS.IsStrictSuffix(lf.0, inp, dir) {
      SS.SSLengthLt(lf.0, inp, dir);   // RemainingLength(lf.0) < RemainingLength(inp)
      var QK1 := [Areg(Quantified(greedy, 0, NoiPred(delta), r1))];
      var QK2 := [Areg(Quantified(greedy, 0, NoiPred(delta), r2))];
      assert K1 == [Acheck(inp)] + QK1 && K2 == [Acheck(inp)] + QK2;
      // Acheck passes: ComputeTr(K1) == Progress(ComputeTr(QK1)); leaves of Progress(x) == leaves of x.
      assert ComputeTr(rer, K1, lf.0, lf.1, dir) == Progress(ComputeTr(rer, QK1, lf.0, lf.1, dir));
      assert ComputeTr(rer, K2, lf.0, lf.1, dir) == Progress(ComputeTr(rer, QK2, lf.0, lf.1, dir));
      assert yf == TreeLeaves(ComputeTr(rer, QK1, lf.0, lf.1, dir), lf.1, lf.0, dir);
      assert yg == TreeLeaves(ComputeTr(rer, QK2, lf.0, lf.1, dir), lf.1, lf.0, dir);
      QuantCongAt(rer, dir, greedy, 0, NoiPred(delta), r1, r2, lf.0, lf.1);
    } else {
      // Acheck(inp) fails: both trees are Mismatch, yf == yg == []
      assert ComputeTr(rer, K1, lf.0, lf.1, dir) == Mismatch;
      assert ComputeTr(rer, K2, lf.0, lf.1, dir) == Mismatch;
      assert yf == [] && yg == [];
    }
  }

  // The quantifier-body congruence (Theorem ingredient): replacing a quantifier's body by a
  // leaves-equivalent regex preserves equivalence. Discharged via the positional QuantCongAt.
  /** `Quantified` congruence: if `r1 ≅ r2` then `Quantified(greedy, min, delta, r1) ≅ ..r2`
      (same `greedy`/`min`/`delta`). Discharged via `QuantCongAt`. */
  lemma QuantCong(rer: RegExpRecord, dir: Direction, greedy: bool, min: nat, delta: NoI, r1: Regex, r2: Regex)
    requires TreeEquivDir(rer, dir, r1, r2)
    ensures TreeEquivDir(rer, dir, Quantified(greedy, min, delta, r1), Quantified(greedy, min, delta, r2))
  {
    assert DefGroups(r1) == DefGroups(r2);
    forall inp, gm, ta, tb | IsTree(rer, [Areg(Quantified(greedy, min, delta, r1))], inp, gm, dir, ta) && IsTree(rer, [Areg(Quantified(greedy, min, delta, r2))], inp, gm, dir, tb)
      ensures TreeEquivTrDir(inp, gm, dir, ta, tb)
    {
      IsTreeEqComputeTr(rer, [Areg(Quantified(greedy, min, delta, r1))], inp, gm, dir, ta);
      IsTreeEqComputeTr(rer, [Areg(Quantified(greedy, min, delta, r2))], inp, gm, dir, tb);
      QuantCongAt(rer, dir, greedy, min, delta, r1, r2, inp, gm);
    }
  }

  // Coq: regex_equiv_ctx_samedir (Theorem 5) — induction on the (lookaround-free) context spine.
  /** Theorem 5: plugging equivalent regexes into the same lookaround-free context (`CtxDir(ctx)
      == CtxSame`) yields equivalent results — the general form of the per-constructor congruences
      above, composed along a context. Proved by induction on `ctx`. */
  lemma RegexEquivCtxSamedir(rer: RegExpRecord, r1: Regex, r2: Regex, dir: Direction, ctx: RegexCtx)
    requires TreeEquivDir(rer, dir, r1, r2)
    requires CtxDir(ctx) == CtxSame
    ensures TreeEquivDir(rer, dir, PlugCtx(ctx, r1), PlugCtx(ctx, r2))
    decreases ctx
  {
    match ctx
    case CHole =>
    case CDisjunctionL(r0, c2) =>
      RegexEquivCtxSamedir(rer, r1, r2, dir, c2);
      DisjCongR(rer, dir, r0, PlugCtx(c2, r1), PlugCtx(c2, r2));
    case CDisjunctionR(c1, r0) =>
      RegexEquivCtxSamedir(rer, r1, r2, dir, c1);
      DisjCongL(rer, dir, r0, PlugCtx(c1, r1), PlugCtx(c1, r2));
    case CSequenceL(r0, c2) =>
      RegexEquivCtxSamedir(rer, r1, r2, dir, c2);
      SeqCongR(rer, dir, r0, PlugCtx(c2, r1), PlugCtx(c2, r2));
    case CSequenceR(c1, r0) =>
      RegexEquivCtxSamedir(rer, r1, r2, dir, c1);
      SeqCongL(rer, dir, r0, PlugCtx(c1, r1), PlugCtx(c1, r2));
    case CQuantified(greedy, min, delta, c1) =>
      RegexEquivCtxSamedir(rer, r1, r2, dir, c1);
      QuantCong(rer, dir, greedy, min, delta, PlugCtx(c1, r1), PlugCtx(c1, r2));
    case CGroup(gid, c1) =>
      RegexEquivCtxSamedir(rer, r1, r2, dir, c1);
      GroupCong(rer, dir, gid, PlugCtx(c1, r1), PlugCtx(c1, r2));
    case CLookaround(lk, c1) =>
      assert CtxDir(ctx) != CtxSame;   // a lookaround always sets a concrete direction
  }

  // Lookaround congruence: replacing a lookaround's body by a regex equivalent in the lookaround's
  // OWN direction makes the lookarounds equivalent in ALL outer directions. In fact the leaves are
  // EQUAL: a top-level lookaround consumes nothing, so its only leaf is determined by the body's first
  // result, which agrees by EquivHead.
  /** Lookaround congruence: if the bodies are equivalent in the lookaround's own scanning
      direction (`LkDir(lk)`), the lookarounds are equivalent in every outer direction — a
      lookaround only ever depends on its body's first (highest-priority) result. */
  lemma LkCong(rer: RegExpRecord, lk: Lookaround, b1: Regex, b2: Regex)
    requires TreeEquivDir(rer, LkDir(lk), b1, b2)
    ensures TreeEquiv(rer, LookaroundR(lk, b1), LookaroundR(lk, b2))
  {
    assert DefGroups(b1) == DefGroups(b2);
    forall dir
      ensures TreeEquivDir(rer, dir, LookaroundR(lk, b1), LookaroundR(lk, b2))
    {
      forall inp, gm, t1, t2 | IsTree(rer, [Areg(LookaroundR(lk, b1))], inp, gm, dir, t1) && IsTree(rer, [Areg(LookaroundR(lk, b2))], inp, gm, dir, t2)
        ensures TreeEquivTrDir(inp, gm, dir, t1, t2)
      {
        var d := LkDir(lk);
        ComputeTrIsTree(rer, [Areg(b1)], inp, gm, d);
        ComputeTrIsTree(rer, [Areg(b2)], inp, gm, d);
        var tl1 := ComputeTr(rer, [Areg(b1)], inp, gm, d);
        var tl2 := ComputeTr(rer, [Areg(b2)], inp, gm, d);
        assert TreeEquivTrDir(inp, gm, d, tl1, tl2);           // body leaves equiv
        EquivHead(TreeLeaves(tl1, gm, inp, d), TreeLeaves(tl2, gm, inp, d));   // HdError equal
        FirstTreeLeaf(tl1, gm, inp, d);
        FirstTreeLeaf(tl2, gm, inp, d);                        // TreeRes(tl1) == TreeRes(tl2)
        HdErrorNoneNil(TreeLeaves(tl1, gm, inp, d));
        HdErrorNoneNil(TreeLeaves(tl2, gm, inp, d));
        ComputeTrRw(rer, [Areg(LookaroundR(lk, b1))], inp, gm, dir);
        ComputeTrRw(rer, [Areg(LookaroundR(lk, b2))], inp, gm, dir);
        IsTreeEqComputeTr(rer, [Areg(LookaroundR(lk, b1))], inp, gm, dir, t1);
        IsTreeEqComputeTr(rer, [Areg(LookaroundR(lk, b2))], inp, gm, dir, t2);
        assert LkResult(lk, tl1, gm, inp) == LkResult(lk, tl2, gm, inp);   // depends only on TreeRes(tl)
        assert TreeLeaves(t1, gm, inp, dir) == TreeLeaves(t2, gm, inp, dir);
        LeavesEquivRefl(TreeLeaves(t1, gm, inp, dir), []);
      }
    }
  }

  // Coq: regex_equiv_ctx_forward (Theorem 6) — the hole sits inside a forward lookaround, so
  // equivalence in the forward direction lifts to all outer directions.
  /** Theorem 6: when the context's hole sits inside a forward-scanning lookaround (`CtxDir(ctx)
      == CtxForward`), forward equivalence of `r1`/`r2` lifts to full (all-directions) equivalence
      of the plugged results. Proved by induction on `ctx`, bottoming out at `LkCong`. */
  lemma RegexEquivCtxForward(rer: RegExpRecord, r1: Regex, r2: Regex, ctx: RegexCtx)
    requires TreeEquivDir(rer, Forward, r1, r2)
    requires CtxDir(ctx) == CtxForward
    ensures TreeEquiv(rer, PlugCtx(ctx, r1), PlugCtx(ctx, r2))
    decreases ctx
  {
    match ctx
    case CHole =>
      assert false;   // CtxDir(CHole) == CtxSame
    case CDisjunctionL(r0, c2) =>
      RegexEquivCtxForward(rer, r1, r2, c2);
      forall dir ensures TreeEquivDir(rer, dir, PlugCtx(ctx, r1), PlugCtx(ctx, r2)) { DisjCongR(rer, dir, r0, PlugCtx(c2, r1), PlugCtx(c2, r2)); }
    case CDisjunctionR(c1, r0) =>
      RegexEquivCtxForward(rer, r1, r2, c1);
      forall dir ensures TreeEquivDir(rer, dir, PlugCtx(ctx, r1), PlugCtx(ctx, r2)) { DisjCongL(rer, dir, r0, PlugCtx(c1, r1), PlugCtx(c1, r2)); }
    case CSequenceL(r0, c2) =>
      RegexEquivCtxForward(rer, r1, r2, c2);
      forall dir ensures TreeEquivDir(rer, dir, PlugCtx(ctx, r1), PlugCtx(ctx, r2)) { SeqCongR(rer, dir, r0, PlugCtx(c2, r1), PlugCtx(c2, r2)); }
    case CSequenceR(c1, r0) =>
      RegexEquivCtxForward(rer, r1, r2, c1);
      forall dir ensures TreeEquivDir(rer, dir, PlugCtx(ctx, r1), PlugCtx(ctx, r2)) { SeqCongL(rer, dir, r0, PlugCtx(c1, r1), PlugCtx(c1, r2)); }
    case CQuantified(greedy, min, delta, c1) =>
      RegexEquivCtxForward(rer, r1, r2, c1);
      forall dir ensures TreeEquivDir(rer, dir, PlugCtx(ctx, r1), PlugCtx(ctx, r2)) { QuantCong(rer, dir, greedy, min, delta, PlugCtx(c1, r1), PlugCtx(c1, r2)); }
    case CGroup(gid, c1) =>
      RegexEquivCtxForward(rer, r1, r2, c1);
      forall dir ensures TreeEquivDir(rer, dir, PlugCtx(ctx, r1), PlugCtx(ctx, r2)) { GroupCong(rer, dir, gid, PlugCtx(c1, r1), PlugCtx(c1, r2)); }
    case CLookaround(lk, c1) =>
      if CtxDir(c1) == CtxSame {
        assert LkDir(lk) == Forward;
        RegexEquivCtxSamedir(rer, r1, r2, Forward, c1);   // TreeEquivDir(Forward, plug(c1,r1), plug(c1,r2))
        LkCong(rer, lk, PlugCtx(c1, r1), PlugCtx(c1, r2));
      } else {
        RegexEquivCtxForward(rer, r1, r2, c1);            // TreeEquiv ⊇ TreeEquivDir(LkDir(lk), ..)
        LkCong(rer, lk, PlugCtx(c1, r1), PlugCtx(c1, r2));
      }
  }

  // Coq: regex_equiv_ctx_backward (Theorem 7) — symmetric to Theorem 6.
  /** Theorem 7: the backward-scanning counterpart of `RegexEquivCtxForward` — when the context's
      hole sits inside a backward-scanning lookaround, backward equivalence lifts to full
      equivalence of the plugged results. */
  lemma RegexEquivCtxBackward(rer: RegExpRecord, r1: Regex, r2: Regex, ctx: RegexCtx)
    requires TreeEquivDir(rer, Backward, r1, r2)
    requires CtxDir(ctx) == CtxBackward
    ensures TreeEquiv(rer, PlugCtx(ctx, r1), PlugCtx(ctx, r2))
    decreases ctx
  {
    match ctx
    case CHole =>
      assert false;
    case CDisjunctionL(r0, c2) =>
      RegexEquivCtxBackward(rer, r1, r2, c2);
      forall dir ensures TreeEquivDir(rer, dir, PlugCtx(ctx, r1), PlugCtx(ctx, r2)) { DisjCongR(rer, dir, r0, PlugCtx(c2, r1), PlugCtx(c2, r2)); }
    case CDisjunctionR(c1, r0) =>
      RegexEquivCtxBackward(rer, r1, r2, c1);
      forall dir ensures TreeEquivDir(rer, dir, PlugCtx(ctx, r1), PlugCtx(ctx, r2)) { DisjCongL(rer, dir, r0, PlugCtx(c1, r1), PlugCtx(c1, r2)); }
    case CSequenceL(r0, c2) =>
      RegexEquivCtxBackward(rer, r1, r2, c2);
      forall dir ensures TreeEquivDir(rer, dir, PlugCtx(ctx, r1), PlugCtx(ctx, r2)) { SeqCongR(rer, dir, r0, PlugCtx(c2, r1), PlugCtx(c2, r2)); }
    case CSequenceR(c1, r0) =>
      RegexEquivCtxBackward(rer, r1, r2, c1);
      forall dir ensures TreeEquivDir(rer, dir, PlugCtx(ctx, r1), PlugCtx(ctx, r2)) { SeqCongL(rer, dir, r0, PlugCtx(c1, r1), PlugCtx(c1, r2)); }
    case CQuantified(greedy, min, delta, c1) =>
      RegexEquivCtxBackward(rer, r1, r2, c1);
      forall dir ensures TreeEquivDir(rer, dir, PlugCtx(ctx, r1), PlugCtx(ctx, r2)) { QuantCong(rer, dir, greedy, min, delta, PlugCtx(c1, r1), PlugCtx(c1, r2)); }
    case CGroup(gid, c1) =>
      RegexEquivCtxBackward(rer, r1, r2, c1);
      forall dir ensures TreeEquivDir(rer, dir, PlugCtx(ctx, r1), PlugCtx(ctx, r2)) { GroupCong(rer, dir, gid, PlugCtx(c1, r1), PlugCtx(c1, r2)); }
    case CLookaround(lk, c1) =>
      if CtxDir(c1) == CtxSame {
        assert LkDir(lk) == Backward;
        RegexEquivCtxSamedir(rer, r1, r2, Backward, c1);
        LkCong(rer, lk, PlugCtx(c1, r1), PlugCtx(c1, r2));
      } else {
        RegexEquivCtxBackward(rer, r1, r2, c1);
        LkCong(rer, lk, PlugCtx(c1, r1), PlugCtx(c1, r2));
      }
  }
}
