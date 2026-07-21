// Mirror of Semantics/FunctionalUtils.v.
// Utilities around the functional semantics: compute_tr (compute_tree with sufficient fuel) and the
// bridging lemmas to is_tree. The Coq Ltac automation (compute_tr_step/simpl/cbv) has no Dafny
// analog and is omitted.
include "ComputeIsTree.dfy"

/** `ComputeTr`, the fuel-free way to compute the tree for an action stack/position, and the
    lemmas connecting it to `IsTree`: it always yields a valid tree (`ComputeTrIsTree`), it's
    the *only* one (`IsTreeEqComputeTr`), and it unfolds one construct at a time
    (`ComputeTrRw`/`ComputeTrUnfold`). This is what makes the reference semantics executable. */
module FunctionalUtils {
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
  import opened ComputeIsTree

  // Coq: compute_tr
  /** Computes the tree for action stack `act` at position `inp` — `ComputeTree` run with
      exactly enough fuel (`ActionsFuel(act, inp, dir) + 1`) that it always terminates
      successfully, so this function needs no fuel parameter of its own. */
  function ComputeTr(rer: RegExpRecord, act: Actions, inp: Input, gm: GroupMap, dir: Direction): Tree {
    match ComputeTree(rer, act, inp, gm, dir, ActionsFuel(act, inp, dir) + 1)
    case Some(tr) => tr
    case None => Mismatch
  }

  // Coq: compute_tr_is_tree
  /** `ComputeTr` always yields a valid `IsTree` tree. */
  lemma ComputeTrIsTree(rer: RegExpRecord, act: Actions, inp: Input, gm: GroupMap, dir: Direction)
    ensures IsTree(rer, act, inp, gm, dir, ComputeTr(rer, act, inp, gm, dir))
  {
    var fuel := ActionsFuel(act, inp, dir) + 1;
    FunctionalTerminates(rer, act, inp, gm, dir, fuel);
    var opt := ComputeTree(rer, act, inp, gm, dir, fuel);
    assert opt.Some? && ComputeTr(rer, act, inp, gm, dir) == opt.value;
    ComputeIsTreeThm(rer, act, inp, gm, dir, fuel, opt.value);
  }

  // Coq: is_tree_eq_compute_tr
  /** Any `IsTree` tree for this action stack/position must equal `ComputeTr`'s result — i.e.
      `ComputeTr` computes *the* (unique, per `IsTreeDeterm`) tree. */
  lemma IsTreeEqComputeTr(rer: RegExpRecord, act: Actions, inp: Input, gm: GroupMap, dir: Direction, tr: Tree)
    requires IsTree(rer, act, inp, gm, dir, tr)
    ensures tr == ComputeTr(rer, act, inp, gm, dir)
  {
    ComputeTrIsTree(rer, act, inp, gm, dir);
    IsTreeDeterm(rer, act, inp, gm, dir, tr, ComputeTr(rer, act, inp, gm, dir));
  }

  // Coq: compute_tr_eq_is_tree
  /** Converse direction: if `tr` equals `ComputeTr`'s result, then `tr` satisfies `IsTree`. */
  lemma ComputeTrEqIsTree(rer: RegExpRecord, act: Actions, inp: Input, gm: GroupMap, dir: Direction, tr: Tree)
    requires tr == ComputeTr(rer, act, inp, gm, dir)
    ensures IsTree(rer, act, inp, gm, dir, tr)
  {
    ComputeTrIsTree(rer, act, inp, gm, dir);
  }

  // Coq: compute_tr_ind
  /** To prove a property `P` of every `IsTree` tree for this stack/position, it suffices to
      prove `P` of `ComputeTr`'s result (since that's the only tree there is). */
  lemma ComputeTrInd(rer: RegExpRecord, act: Actions, inp: Input, gm: GroupMap, dir: Direction, P: Tree -> bool, tr: Tree)
    requires P(ComputeTr(rer, act, inp, gm, dir))
    requires IsTree(rer, act, inp, gm, dir, tr)
    ensures P(tr)
  {
    IsTreeEqComputeTr(rer, act, inp, gm, dir, tr);
  }

  // Coq: compute_tr_unfold — one-step unfolding of compute_tr.
  /** `ComputeTr`'s definition unrolled by one action/regex construct, expressed purely in terms
      of recursive `ComputeTr` calls (no fuel bookkeeping visible). Proved equal to `ComputeTr`
      itself by `ComputeTrRw`; used to reason about `ComputeTr` construct-by-construct. */
  function ComputeTrUnfold(rer: RegExpRecord, act: Actions, inp: Input, gm: GroupMap, dir: Direction): Tree {
    if |act| == 0 then Match
    else
      var cont := act[1..];
      match act[0]
      case Acheck(strcheck) =>
        if SS.IsStrictSuffix(inp, strcheck, dir) then Progress(ComputeTr(rer, cont, inp, gm, dir))
        else Mismatch
      case Aclose(gid) =>
        GroupActionT(Close(gid), ComputeTr(rer, cont, inp, GMClose(Idx(inp), gid, gm), dir))
      case Areg(r) =>
        match r
        case Epsilon => ComputeTr(rer, cont, inp, gm, dir)
        case Character(cd) =>
          (match ReadChar(rer, cd, inp, dir)
           case Some(pair) => Read(pair.0, ComputeTr(rer, cont, pair.1, gm, dir))
           case None => Mismatch)
        case Disjunction(r1, r2) =>
          Choice(ComputeTr(rer, [Areg(r1)] + cont, inp, gm, dir), ComputeTr(rer, [Areg(r2)] + cont, inp, gm, dir))
        case Sequence(r1, r2) =>
          ComputeTr(rer, SeqList(r1, r2, dir) + cont, inp, gm, dir)
        case Quantified(greedy, min, delta, r1) =>
          var gidl := DefGroups(r1);
          if min > 0 then
            GroupActionT(Reset(gidl), ComputeTr(rer, [Areg(r1), Areg(Quantified(greedy, min - 1, delta, r1))] + cont, inp, GMReset(gidl, gm), dir))
          else if delta == NN(0) then
            ComputeTr(rer, cont, inp, gm, dir)
          else
            var titer := ComputeTr(rer, [Areg(r1), Acheck(inp), Areg(Quantified(greedy, 0, NoiPred(delta), r1))] + cont, inp, GMReset(gidl, gm), dir);
            var tskip := ComputeTr(rer, cont, inp, gm, dir);
            GreedyChoice(greedy, GroupActionT(Reset(gidl), titer), tskip)
        case Group(gid, r1) =>
          GroupActionT(Open(gid), ComputeTr(rer, [Areg(r1), Aclose(gid)] + cont, inp, GMOpen(Idx(inp), gid, gm), dir))
        case LookaroundR(lk, r1) =>
          var treelk := ComputeTr(rer, [Areg(r1)], inp, gm, LkDir(lk));
          (match LkResult(lk, treelk, gm, inp)
           case Some(gmlk) => LK(lk, treelk, ComputeTr(rer, cont, inp, gmlk, dir))
           case None => LKFail(lk, treelk))
        case AnchorR(a) =>
          if AnchorSatisfied(rer, a, inp) then AnchorPass(a, ComputeTr(rer, cont, inp, gm, dir))
          else Mismatch
        case Backreference(gid) =>
          (match ReadBackref(rer, gm, gid, inp, dir)
           case Some(pair) => ReadBackRef(pair.0, ComputeTr(rer, cont, pair.1, gm, dir))
           case None => Mismatch)
  }

  // For any sufficient fuel, ComputeTree yields exactly Some(ComputeTr ...) (fuel irrelevance +
  // termination). This is the bridge that lets ComputeTrRw replace ComputeTree-subcalls with ComputeTr.
  /** Any fuel beyond `ActionsFuel(act, inp, dir)` makes `ComputeTree` agree with `ComputeTr`. */
  lemma SubComputeTr(rer: RegExpRecord, act: Actions, inp: Input, gm: GroupMap, dir: Direction, fuel: nat)
    requires fuel > ActionsFuel(act, inp, dir)
    ensures ComputeTree(rer, act, inp, gm, dir, fuel) == Some(ComputeTr(rer, act, inp, gm, dir))
  {
    var g := ActionsFuel(act, inp, dir) + 1;
    FunctionalTerminates(rer, act, inp, gm, dir, g);
    ComputeTreeFuelIrrelevance(rer, act, inp, gm, dir, fuel, g);
  }

  // Coq: compute_tr_rw — one-step unfolding equation. ComputeTr(act) == ComputeTree(act, F) with
  // F = ActionsFuel(act)+1; unfold one step and replace each ComputeTree-subcall by ComputeTr via
  // SubComputeTr (each subcall's fuel f = ActionsFuel(act) is sufficient by the termination lemma).
  /** `ComputeTr` equals its one-step unfolding `ComputeTrUnfold` — the key rewrite rule for
      reasoning about `ComputeTr` construct-by-construct instead of via its fuel-based definition. */
  lemma ComputeTrRw(rer: RegExpRecord, act: Actions, inp: Input, gm: GroupMap, dir: Direction)
    ensures ComputeTr(rer, act, inp, gm, dir) == ComputeTrUnfold(rer, act, inp, gm, dir)
  {
    var F := ActionsFuel(act, inp, dir) + 1;
    FunctionalTerminates(rer, act, inp, gm, dir, F);
    if |act| == 0 {
      return;
    }
    var cont := act[1..];
    var f := F - 1;   // == ActionsFuel(act, inp, dir)
    assert act == [act[0]] + cont;
    match act[0]
    case Acheck(strcheck) =>
      assert act == [Acheck(strcheck)] + cont;
      if SS.IsStrictSuffix(inp, strcheck, dir) {
        CheckTermination(cont, inp, strcheck, dir);
        SubComputeTr(rer, cont, inp, gm, dir, f);
      }
    case Aclose(gid) =>
      assert act == [Aclose(gid)] + cont;
      CloseTermination(cont, inp, dir, gid);
      SubComputeTr(rer, cont, inp, GMClose(Idx(inp), gid, gm), dir, f);
    case Areg(r) =>
      match r
      case Epsilon =>
        assert act == [Areg(Epsilon)] + cont;
        EpsilonTermination(cont, inp, dir);
        SubComputeTr(rer, cont, inp, gm, dir, f);
      case Character(cd) =>
        assert act == [Areg(Character(cd))] + cont;
        match ReadChar(rer, cd, inp, dir) {
          case Some(pair) =>
            CharacterTermination(rer, cont, inp, dir, cd, pair.0, pair.1);
            SubComputeTr(rer, cont, pair.1, gm, dir, f);
          case None =>
        }
      case Disjunction(r1, r2) =>
        assert act == [Areg(Disjunction(r1, r2))] + cont;
        DisjunctionLeftTermination(cont, inp, dir, r1, r2);
        DisjunctionRightTermination(cont, inp, dir, r1, r2);
        SubComputeTr(rer, [Areg(r1)] + cont, inp, gm, dir, f);
        SubComputeTr(rer, [Areg(r2)] + cont, inp, gm, dir, f);
      case Sequence(r1, r2) =>
        assert act == [Areg(Sequence(r1, r2))] + cont;
        SequenceTermination(cont, inp, dir, r1, r2);
        SubComputeTr(rer, SeqList(r1, r2, dir) + cont, inp, gm, dir, f);
      case Quantified(greedy, min, delta, r1) =>
        assert act == [Areg(Quantified(greedy, min, delta, r1))] + cont;
        var gidl := DefGroups(r1);
        if min > 0 {
          QuantForcedTermination(cont, inp, dir, r1, min - 1, delta, greedy);
          assert (min - 1) + 1 == min;
          SubComputeTr(rer, [Areg(r1), Areg(Quantified(greedy, min - 1, delta, r1))] + cont, inp, GMReset(gidl, gm), dir, f);
        } else if delta == NN(0) {
          QuantDoneTermination(cont, inp, dir, r1, greedy);
          SubComputeTr(rer, cont, inp, gm, dir, f);
        } else {
          QuantFreeIterTermination(cont, inp, dir, r1, greedy, delta);
          QuantFreeSkipTermination(cont, inp, dir, r1, greedy, delta);
          SubComputeTr(rer, [Areg(r1), Acheck(inp), Areg(Quantified(greedy, 0, NoiPred(delta), r1))] + cont, inp, GMReset(gidl, gm), dir, f);
          SubComputeTr(rer, cont, inp, gm, dir, f);
        }
      case Group(gid, r1) =>
        assert act == [Areg(Group(gid, r1))] + cont;
        GroupTermination(cont, inp, dir, r1, gid);
        SubComputeTr(rer, [Areg(r1), Aclose(gid)] + cont, inp, GMOpen(Idx(inp), gid, gm), dir, f);
      case LookaroundR(lk, r1) =>
        assert act == [Areg(LookaroundR(lk, r1))] + cont;
        LkLkTermination(cont, inp, dir, lk, r1);
        SubComputeTr(rer, [Areg(r1)], inp, gm, LkDir(lk), f);
        var treelk := ComputeTr(rer, [Areg(r1)], inp, gm, LkDir(lk));
        match LkResult(lk, treelk, gm, inp) {
          case Some(gmlk) =>
            LkAfterTermination(cont, inp, dir, lk, r1);
            SubComputeTr(rer, cont, inp, gmlk, dir, f);
          case None =>
        }
      case AnchorR(a) =>
        assert act == [Areg(AnchorR(a))] + cont;
        if AnchorSatisfied(rer, a, inp) {
          AnchorTermination(cont, inp, dir, a);
          SubComputeTr(rer, cont, inp, gm, dir, f);
        }
      case Backreference(gid) =>
        assert act == [Areg(Backreference(gid))] + cont;
        match ReadBackref(rer, gm, gid, inp, dir) {
          case Some(pair) =>
            BackrefTermination(rer, cont, inp, dir, gid, gm, pair.0, pair.1);
            SubComputeTr(rer, cont, pair.1, gm, dir, f);
          case None =>
        }
  }
}
