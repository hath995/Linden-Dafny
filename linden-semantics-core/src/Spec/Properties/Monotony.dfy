// A Warblre-style "monotony / progress" property for the Linden tree semantics.
// Warblre proves (Match.monotony) that a successful match never moves backwards: the result's end
// index is >= the start in the search direction. Here we prove the analogous, in fact STRONGER,
// purely structural fact about the backtracking tree: every leaf produced by `TreeRes` sits at the
// start position or at a STRICT SUFFIX of it (i.e. the search only ever advances in direction dir).
// This holds for ALL trees, so it specializes to any is_tree result.
include "../Semantics/Tree.dfy"
include "../Semantics/StrictSuffix.dfy"

/** The tree semantics only ever moves forward: every leaf a backtracking tree can produce sits
    at the start position or a `StrictSuffix.StrictSuffix` of it. This is a purely structural
    fact about `Tree`, so it specializes to any `IsTree` result — it is Linden's (stronger)
    analogue of Warblre's `Match.monotony`. */
module Monotony {
  import opened Std.Wrappers
  import opened WarblrePrimitives  // Direction, Forward, Backward
  import opened Chars              // Input, Take, Drop, Reverse, AdvanceInput*, Idx
  import opened Groups             // GroupMap
  import opened Regex              // Positivity, LkDir, Lookaround
  import opened Tree               // Tree, Leaf, TreeRes, GMUpdate via Groups
  import SS = StrictSuffix

  // ----- small reverse / take-drop helpers -----
  lemma ReverseLength(s: seq<char>)
    ensures |Reverse(s)| == |s|
    decreases s
  {
    if |s| != 0 { ReverseLength(s[1..]); }
  }

  lemma ReverseReverse(s: seq<char>)
    ensures Reverse(Reverse(s)) == s
    decreases s
  {
    if |s| != 0 {
      assert Reverse(s) == Reverse(s[1..]) + [s[0]];
      SS.ReverseSnoc(Reverse(s[1..]), s[0]);
      ReverseReverse(s[1..]);
      assert s == [s[0]] + s[1..];
    }
  }

  lemma TakeDropApp<T>(s: seq<T>, n: nat)
    ensures Take(s, n) + Drop(s, n) == s
  {
    if n <= |s| {
      assert Take(s, n) == s[..n] && Drop(s, n) == s[n..];
    } else {
      assert Take(s, n) == s && Drop(s, n) == [];
    }
  }

  // Advancing by ANY number of characters lands on the start or a strict suffix.
  /** Advancing the input by any number `n` of characters (`AdvanceInputN`) either leaves it
      unchanged (`n` characters weren't available) or lands on a strict suffix. */
  lemma AdvanceInputNProgress(inp: Input, n: nat, dir: Direction)
    ensures AdvanceInputN(inp, n, dir) == inp || SS.StrictSuffix(AdvanceInputN(inp, n, dir), inp, dir)
  {
    var r := AdvanceInputN(inp, n, dir);
    match dir
    case Forward =>
      var diff := Take(inp.next, n);
      TakeDropApp(inp.next, n);           // inp.next == Take + Drop
      assert r.next == Drop(inp.next, n) && r.pref == Reverse(diff) + inp.pref;
      if diff == [] {
        assert r == inp;
      } else {
        assert inp.next == diff + r.next;
        SS.SSFwdDiff(r.next, r.pref, inp.next, inp.pref);   // witness diff
        assert r == Input(r.next, r.pref) && inp == Input(inp.next, inp.pref);
      }
    case Backward =>
      var take := Take(inp.pref, n);
      TakeDropApp(inp.pref, n);
      assert r.next == Reverse(take) + inp.next && r.pref == Drop(inp.pref, n);
      if take == [] {
        assert r == inp;
      } else {
        var d := Reverse(take);
        ReverseLength(take);
        ReverseReverse(take);             // Reverse(d) == take
        assert d != [] && r.next == d + inp.next && inp.pref == Reverse(d) + r.pref;
        SS.SSBwdDiff(r.next, r.pref, inp.next, inp.pref);   // witness d
        assert r == Input(r.next, r.pref) && inp == Input(inp.next, inp.pref);
      }
  }

  // MAIN: every leaf of a backtracking tree is the start position or a strict suffix of it.
  /** MAIN LEMMA: the highest-priority leaf (`TreeRes`) of a tree rooted at `inp` sits at `inp`
      itself or a strict suffix of it in direction `dir` — matching never moves backwards. */
  lemma TreeResMonotony(t: Tree, gm: GroupMap, inp: Input, dir: Direction, inp2: Input, gm2: GroupMap)
    requires TreeRes(t, gm, inp, dir) == Some((inp2, gm2))
    ensures inp2 == inp || SS.StrictSuffix(inp2, inp, dir)
    decreases t
  {
    match t
    case Match =>
      // TreeRes(Match) == Some((inp, gm)) ⟹ inp2 == inp
    case Mismatch =>            // TreeRes == None: vacuous
    case Choice(t1, t2) =>
      if TreeRes(t1, gm, inp, dir).Some? {
        TreeResMonotony(t1, gm, inp, dir, inp2, gm2);
      } else {
        TreeResMonotony(t2, gm, inp, dir, inp2, gm2);
      }
    case Progress(t1) =>
      TreeResMonotony(t1, gm, inp, dir, inp2, gm2);
    case AnchorPass(_, t0) =>
      TreeResMonotony(t0, gm, inp, dir, inp2, gm2);
    case GroupActionT(a, t1) =>
      TreeResMonotony(t1, GMUpdate(a, Idx(inp), gm), inp, dir, inp2, gm2);
    case Read(c, t1) =>
      var nexti := AdvanceInputP(inp, dir);
      TreeResMonotony(t1, gm, nexti, dir, inp2, gm2);   // inp2 == nexti || SS(inp2, nexti)
      if AdvanceInput(inp, dir).Some? {
        var ni := AdvanceInput(inp, dir).value;
        assert nexti == ni;
        SS.ReadSuffix(inp, dir, ni);                     // SS(ni, inp, dir)
        if inp2 != nexti { SS.StrictSuffixTrans(inp2, nexti, inp, dir); }
      } else {
        assert nexti == inp;
      }
    case ReadBackRef(brStr, t0) =>
      var nexti := AdvanceInputN(inp, |brStr|, dir);
      TreeResMonotony(t0, gm, nexti, dir, inp2, gm2);    // inp2 == nexti || SS(inp2, nexti)
      AdvanceInputNProgress(inp, |brStr|, dir);          // nexti == inp || SS(nexti, inp)
      if nexti != inp && inp2 != nexti {
        SS.StrictSuffixTrans(inp2, nexti, inp, dir);
      }
    case LK(lk, tlk, t1) =>
      if Positivity(lk) {
        var sub := TreeRes(tlk, gm, inp, LkDir(lk));
        if sub.Some? {
          TreeResMonotony(t1, sub.value.1, inp, dir, inp2, gm2);
        }
      } else {
        var sub := TreeRes(tlk, gm, inp, LkDir(lk));
        if sub.None? {
          TreeResMonotony(t1, gm, inp, dir, inp2, gm2);
        }
      }
    case LKFail(_, _) =>       // TreeRes == None: vacuous
  }

  // Every leaf in the full leaf list (not just the first) is at the start or a strict suffix.
  /** The same guarantee as `TreeResMonotony`, but for *every* leaf `l` in `TreeLeaves`
      (not just the first / highest-priority one). */
  lemma TreeLeavesMonotony(t: Tree, gm: GroupMap, inp: Input, dir: Direction, l: Leaf)
    requires l in TreeLeaves(t, gm, inp, dir)
    ensures l.0 == inp || SS.StrictSuffix(l.0, inp, dir)
    decreases t
  {
    match t
    case Match =>
    case Mismatch =>
    case Choice(t1, t2) =>
      if l in TreeLeaves(t1, gm, inp, dir) {
        TreeLeavesMonotony(t1, gm, inp, dir, l);
      } else {
        TreeLeavesMonotony(t2, gm, inp, dir, l);
      }
    case Progress(t1) =>
      TreeLeavesMonotony(t1, gm, inp, dir, l);
    case AnchorPass(_, t0) =>
      TreeLeavesMonotony(t0, gm, inp, dir, l);
    case GroupActionT(a, t1) =>
      TreeLeavesMonotony(t1, GMUpdate(a, Idx(inp), gm), inp, dir, l);
    case Read(c, t1) =>
      var nexti := AdvanceInputP(inp, dir);
      TreeLeavesMonotony(t1, gm, nexti, dir, l);
      if AdvanceInput(inp, dir).Some? {
        var ni := AdvanceInput(inp, dir).value;
        assert nexti == ni;
        SS.ReadSuffix(inp, dir, ni);
        if l.0 != nexti { SS.StrictSuffixTrans(l.0, nexti, inp, dir); }
      } else {
        assert nexti == inp;
      }
    case ReadBackRef(brStr, t0) =>
      var nexti := AdvanceInputN(inp, |brStr|, dir);
      TreeLeavesMonotony(t0, gm, nexti, dir, l);
      AdvanceInputNProgress(inp, |brStr|, dir);
      if nexti != inp && l.0 != nexti {
        SS.StrictSuffixTrans(l.0, nexti, inp, dir);
      }
    case LK(lk, tlk, t1) =>
      if Positivity(lk) {
        var sub := TreeRes(tlk, gm, inp, LkDir(lk));
        if TreeLeaves(tlk, gm, inp, LkDir(lk)) != [] {
          TreeLeavesMonotony(t1, TreeLeaves(tlk, gm, inp, LkDir(lk))[0].1, inp, dir, l);
        }
      } else {
        if TreeLeaves(tlk, gm, inp, LkDir(lk)) == [] {
          TreeLeavesMonotony(t1, gm, inp, dir, l);
        }
      }
    case LKFail(_, _) =>
  }

  // Consequence: leaf positions never have more remaining input than the start.
  /** Consequence of `TreeLeavesMonotony`: any leaf's remaining input (`RemainingLength`) is no
      longer than the start's — leaves never have *more* input left than where matching began. */
  lemma TreeLeavesRemaining(t: Tree, gm: GroupMap, inp: Input, dir: Direction, l: Leaf)
    requires l in TreeLeaves(t, gm, inp, dir)
    ensures RemainingLength(l.0, dir) <= RemainingLength(inp, dir)
  {
    TreeLeavesMonotony(t, gm, inp, dir, l);
    if l.0 != inp {
      SS.SSLengthLt(l.0, inp, dir);
    }
  }

  // Corollary (Warblre's `monotony'`): a forward match's end index never precedes the start.
  /** Warblre's `monotony'`: for a `Forward` match, the end index (`Idx`) is never smaller than
      the start index — a successful forward match never appears to move backwards. */
  lemma ForwardMatchAdvances(t: Tree, gm: GroupMap, inp: Input, inp2: Input, gm2: GroupMap)
    requires TreeRes(t, gm, inp, Forward) == Some((inp2, gm2))
    ensures Idx(inp) <= Idx(inp2)
  {
    TreeResMonotony(t, gm, inp, Forward, inp2, gm2);
    if inp2 != inp {
      assert inp2 == Input(inp2.next, inp2.pref) && inp == Input(inp.next, inp.pref);
      SS.SSFwdDiff(inp2.next, inp2.pref, inp.next, inp.pref);
      var d :| d != [] && inp.next == d + inp2.next && inp2.pref == Reverse(d) + inp.pref;
      ReverseLength(d);   // |inp2.pref| == |d| + |inp.pref| >= |inp.pref|
    }
  }
}
