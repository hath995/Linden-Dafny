// A Warblre-style "strictly nullable" static analysis and its soundness, for the Linden tree
// semantics. Warblre (props/StrictlyNullable.v) defines a syntactic under-approximation of "this
// regex, if it matches, always matches the empty string" and proves it sound. We port the analysis
// to Linden's `Regex` and prove the analogue over the tree semantics: if `StrictlyNullable r`, then
// every leaf of r's backtracking tree sits at the START position (it consumes no characters).
//
// The proof is a fuel induction mirroring `ComputeTree` (same shape as ComputeBoolTree): strict
// nullability propagates through the action list (a lookaround body is evaluated separately and does
// not move the top-level position; the loop-progress `Acheck` is itself a strictly-nullable action),
// so each recursive ComputeTree call stays within the strictly-nullable fragment.
include "../Semantics/FunctionalUtils.dfy"

/** A syntactic under-approximation of "this regex, if it matches, always matches the empty
    string" (`StrictlyNullable`), proved sound over the tree semantics: if `StrictlyNullable(r)`
    holds, every leaf of `r`'s backtracking tree sits at the starting position, i.e. `r` consumes
    no characters. Ported from Warblre's `props/StrictlyNullable.v`. */
module StrictlyNullable {
  import opened Std.Wrappers
  import opened WarblreRegExpRecord
  import opened WarblreNumeric
  import opened WarblrePrimitives
  import opened Chars
  import opened Groups
  import opened Regex
  import opened Tree
  import opened Semantics
  import opened FunctionalSemantics
  import opened FunctionalUtils
  import SS = StrictSuffix

  // Coq: strictly_nullable (Warblre props/StrictlyNullable.v).
  /** Syntactic check: `r` can never consume a character. `LookaroundR` and `AnchorR` are always
      nullable (they're zero-width by construction); `Character` and `Backreference` never are;
      the connectives require all sub-regexes to be nullable. */
  predicate StrictlyNullable(r: Regex)
    decreases r
  {
    match r
    case Epsilon => true
    case LookaroundR(_, _) => true              // lookarounds consume nothing (body irrelevant)
    case AnchorR(_) => true                     // anchors consume nothing
    case Character(_) => false
    case Backreference(_) => false              // a backref can match a non-empty string
    case Disjunction(r1, r2) => StrictlyNullable(r1) && StrictlyNullable(r2)
    case Sequence(r1, r2) => StrictlyNullable(r1) && StrictlyNullable(r2)
    case Quantified(_, _, _, r1) => StrictlyNullable(r1)
    case Group(_, r1) => StrictlyNullable(r1)
  }

  /** Lifts `StrictlyNullable` to a single `Action`: an `Areg(r)` counts iff `r` is strictly
      nullable; `Acheck`/`Aclose` never consume input either, so they always count. */
  predicate SNAction(a: Action) {
    match a case Areg(r) => StrictlyNullable(r) case Acheck(_) => true case Aclose(_) => true
  }
  /** An action stack where every action is `SNAction` — the invariant `SNComputeTree`
      maintains as it walks the stack. */
  predicate SNActions(act: Actions) {
    forall i :: 0 <= i < |act| ==> SNAction(act[i])
  }

  lemma SNActionsTail(act: Actions)
    requires |act| > 0 && SNActions(act)
    ensures SNActions(act[1..])
  {
    forall i | 0 <= i < |act[1..]| ensures SNAction(act[1..][i]) { assert act[1..][i] == act[i + 1]; }
  }

  lemma SNActionsCons(a: Action, cont: Actions)
    requires SNAction(a) && SNActions(cont)
    ensures SNActions([a] + cont)
  {
    forall i | 0 <= i < |[a] + cont| ensures SNAction(([a] + cont)[i]) {
      if i == 0 { assert ([a] + cont)[0] == a; } else { assert ([a] + cont)[i] == cont[i - 1]; }
    }
  }

  lemma SNSeqList(r1: Regex, r2: Regex, dir: Direction, cont: Actions)
    requires StrictlyNullable(r1) && StrictlyNullable(r2) && SNActions(cont)
    ensures SNActions(SeqList(r1, r2, dir) + cont)
  {
    match dir
    case Forward =>
      assert SeqList(r1, r2, dir) + cont == [Areg(r1)] + ([Areg(r2)] + cont);
      SNActionsCons(Areg(r2), cont);
      SNActionsCons(Areg(r1), [Areg(r2)] + cont);
    case Backward =>
      assert SeqList(r1, r2, dir) + cont == [Areg(r2)] + ([Areg(r1)] + cont);
      SNActionsCons(Areg(r1), cont);
      SNActionsCons(Areg(r2), [Areg(r1)] + cont);
  }

  // MAIN: a strictly-nullable action list yields only leaves at the start position.
  /** MAIN LEMMA: if the action stack `act` is strictly nullable (`SNActions`), the tree
      `ComputeTree` computes for it has its highest-priority leaf at the starting position `inp`
      — a strictly-nullable stack cannot advance the input. Proved by fuel induction mirroring
      `ComputeTree`'s own recursion. */
  lemma SNComputeTree(rer: RegExpRecord, act: Actions, inp: Input, gm: GroupMap, dir: Direction, fuel: nat, t: Tree, inp2: Input, gm2: GroupMap)
    requires SNActions(act)
    requires ComputeTree(rer, act, inp, gm, dir, fuel) == Some(t)
    requires TreeRes(t, gm, inp, dir) == Some((inp2, gm2))
    ensures inp2 == inp
    decreases fuel
  {
    var f := fuel - 1;
    if |act| == 0 {
      // t == Match, TreeRes(Match, gm, inp, dir) == Some((inp, gm))
    } else {
      var cont := act[1..];
      SNActionsTail(act);
      assert act == [act[0]] + cont;
      match act[0]
      case Acheck(strcheck) =>
        if SS.IsStrictSuffix(inp, strcheck, dir) {
          var tcont := ComputeTree(rer, cont, inp, gm, dir, f).value;
          SNComputeTree(rer, cont, inp, gm, dir, f, tcont, inp2, gm2);
        }
      case Aclose(gid) =>
        var gmc := GMClose(Idx(inp), gid, gm);
        var tcont := ComputeTree(rer, cont, inp, gmc, dir, f).value;
        SNComputeTree(rer, cont, inp, gmc, dir, f, tcont, inp2, gm2);
      case Areg(r) =>
        assert StrictlyNullable(r);
        match r
        case Epsilon =>
          var tc := ComputeTree(rer, cont, inp, gm, dir, f).value;
          SNComputeTree(rer, cont, inp, gm, dir, f, tc, inp2, gm2);
        case Character(cd) =>
          assert false;   // StrictlyNullable(Character) is false
        case Disjunction(r1, r2) =>
          var l1 := [Areg(r1)] + cont;
          var l2 := [Areg(r2)] + cont;
          SNActionsCons(Areg(r1), cont);
          SNActionsCons(Areg(r2), cont);
          var t1 := ComputeTree(rer, l1, inp, gm, dir, f).value;
          var t2 := ComputeTree(rer, l2, inp, gm, dir, f).value;
          if TreeRes(t1, gm, inp, dir).Some? {
            SNComputeTree(rer, l1, inp, gm, dir, f, t1, inp2, gm2);
          } else {
            SNComputeTree(rer, l2, inp, gm, dir, f, t2, inp2, gm2);
          }
        case Sequence(r1, r2) =>
          var na := SeqList(r1, r2, dir) + cont;
          SNSeqList(r1, r2, dir, cont);
          var tc := ComputeTree(rer, na, inp, gm, dir, f).value;
          SNComputeTree(rer, na, inp, gm, dir, f, tc, inp2, gm2);
        case Quantified(greedy, min, delta, r1) =>
          var gidl := DefGroups(r1);
          assert StrictlyNullable(r1);
          if min > 0 {
            var qprev := Quantified(greedy, min - 1, delta, r1);
            var iter := [Areg(r1), Areg(qprev)] + cont;
            assert iter == [Areg(r1)] + ([Areg(qprev)] + cont);
            SNActionsCons(Areg(qprev), cont);
            SNActionsCons(Areg(r1), [Areg(qprev)] + cont);
            var titer := ComputeTree(rer, iter, inp, GMReset(gidl, gm), dir, f).value;
            SNComputeTree(rer, iter, inp, GMReset(gidl, gm), dir, f, titer, inp2, gm2);
          } else if delta == NN(0) {
            var tc := ComputeTree(rer, cont, inp, gm, dir, f).value;
            SNComputeTree(rer, cont, inp, gm, dir, f, tc, inp2, gm2);
          } else {
            var qnext := Quantified(greedy, 0, NoiPred(delta), r1);
            var iter := [Areg(r1), Acheck(inp), Areg(qnext)] + cont;
            assert iter == [Areg(r1)] + ([Acheck(inp)] + ([Areg(qnext)] + cont));
            SNActionsCons(Areg(qnext), cont);
            SNActionsCons(Acheck(inp), [Areg(qnext)] + cont);
            SNActionsCons(Areg(r1), [Acheck(inp)] + ([Areg(qnext)] + cont));
            var titer := ComputeTree(rer, iter, inp, GMReset(gidl, gm), dir, f).value;
            var tskip := ComputeTree(rer, cont, inp, gm, dir, f).value;
            var A := GroupActionT(Reset(gidl), titer);
            // t == GreedyChoice(greedy, A, tskip); TreeRes is the first Some of the two, in greedy order.
            if TreeRes(A, gm, inp, dir).Some? {
              assert TreeRes(A, gm, inp, dir) == TreeRes(titer, GMReset(gidl, gm), inp, dir);
              SNComputeTree(rer, iter, inp, GMReset(gidl, gm), dir, f, titer,
                            TreeRes(A, gm, inp, dir).value.0, TreeRes(A, gm, inp, dir).value.1);
              assert TreeRes(A, gm, inp, dir).value.0 == inp;
            }
            if TreeRes(tskip, gm, inp, dir).Some? {
              SNComputeTree(rer, cont, inp, gm, dir, f, tskip,
                            TreeRes(tskip, gm, inp, dir).value.0, TreeRes(tskip, gm, inp, dir).value.1);
              assert TreeRes(tskip, gm, inp, dir).value.0 == inp;
            }
          }
        case Group(gid, r1) =>
          var na := [Areg(r1), Aclose(gid)] + cont;
          assert na == [Areg(r1)] + ([Aclose(gid)] + cont);
          SNActionsCons(Aclose(gid), cont);
          SNActionsCons(Areg(r1), [Aclose(gid)] + cont);
          var gmo := GMOpen(Idx(inp), gid, gm);
          var tcont := ComputeTree(rer, na, inp, gmo, dir, f).value;
          SNComputeTree(rer, na, inp, gmo, dir, f, tcont, inp2, gm2);
        case LookaroundR(lk, r1) =>
          var treelk := ComputeTree(rer, [Areg(r1)], inp, gm, LkDir(lk), f).value;
          match LkResult(lk, treelk, gm, inp) {
            case Some(gmlk) =>
              // t == LK(lk, treelk, tcont); the top-level position comes from tcont at inp.
              var tcont := ComputeTree(rer, cont, inp, gmlk, dir, f).value;
              assert TreeRes(tcont, gmlk, inp, dir) == Some((inp2, gm2));
              SNComputeTree(rer, cont, inp, gmlk, dir, f, tcont, inp2, gm2);
            case None =>
              // t == LKFail(lk, treelk); TreeRes(LKFail) == None: vacuous
          }
        case AnchorR(a) =>
          if AnchorSatisfied(rer, a, inp) {
            var tcont := ComputeTree(rer, cont, inp, gm, dir, f).value;
            SNComputeTree(rer, cont, inp, gm, dir, f, tcont, inp2, gm2);
          }
        case Backreference(gid) =>
          assert false;   // StrictlyNullable(Backreference) is false
    }
  }

  // Soundness, stated semantically over is_tree: if r is strictly nullable, any match leaf is at
  // the start position (the regex consumes no characters).
  /** Soundness of `StrictlyNullable`, stated over the relational `IsTree` semantics rather than
      `ComputeTree`: if `r` is strictly nullable, its match's end position always equals its
      start — `r` consumes no characters. */
  lemma StrictlyNullableSound(rer: RegExpRecord, r: Regex, inp: Input, gm: GroupMap, dir: Direction, t: Tree, inp2: Input, gm2: GroupMap)
    requires StrictlyNullable(r)
    requires IsTree(rer, [Areg(r)], inp, gm, dir, t)
    requires TreeRes(t, gm, inp, dir) == Some((inp2, gm2))
    ensures inp2 == inp
  {
    var fuel := ActionsFuel([Areg(r)], inp, dir) + 1;
    FunctionalTerminates(rer, [Areg(r)], inp, gm, dir, fuel);
    var tprime := ComputeTree(rer, [Areg(r)], inp, gm, dir, fuel).value;
    IsTreeEqComputeTr(rer, [Areg(r)], inp, gm, dir, t);   // t == ComputeTr(...) == tprime
    assert t == tprime;
    assert SNActions([Areg(r)]);
    SNComputeTree(rer, [Areg(r)], inp, gm, dir, fuel, tprime, inp2, gm2);
  }
}
