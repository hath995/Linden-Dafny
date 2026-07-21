// Mirror of Rewriting/LeavesEquivalence.v.
// Equivalence of ordered leaf lists up to removing lower-priority duplicates. The Coq eqb machinery
// (input_eqb/gm_eqb/leaf_eqb) collapses to native `==`; `is_seen` is `in`. `leaves_equiv` is
// structurally recursive on the lists, so it is a plain recursive predicate. The setoid
// `Add Relation` has no Dafny analog and is dropped.
include "../Semantics/Tree.dfy"

/** Equivalence of ordered leaf lists up to removing lower-priority duplicates — the notion
    the `Rewriting` layer uses to prove two (sub)trees yield the same match. `LeavesEquiv` is the
    central relation; `EquivNodup` characterizes it via `FilterLeaves`. */
module LeavesEquivalence {
  import opened Chars
  import opened Groups
  import opened Tree

  /** An `(Input, GroupMap)` pair, the same shape as `Leaf`, used for the `seen` accumulator. */
  type Pair = (Input, GroupMap)  // an (input, group_map), same as Leaf

  // Coq: is_seen
  predicate IsSeen(inpgm: Pair, l: seq<Pair>) { inpgm in l }

  lemma IsSeenSpec(inpgm: Pair, l: seq<Pair>)
    ensures IsSeen(inpgm, l) <==> inpgm in l
  {}

  // Coq: filter_leaves — deduplicate l given an accumulator of already-seen leaves.
  /** Deduplicates `l` left to right against an accumulator `seen` of already-encountered
      leaves: the first occurrence of each leaf survives, later ones are dropped. */
  function FilterLeaves(l: seq<Leaf>, seen: seq<Pair>): seq<Leaf>
    decreases l
  {
    if |l| == 0 then []
    else if l[0] in seen then FilterLeaves(l[1..], seen)
    else [l[0]] + FilterLeaves(l[1..], [l[0]] + seen)
  }

  // Coq: leaves_equiv — equivalent up to removing duplicates already in `seen`.
  /** Two leaf lists are equivalent relative to an already-`seen` set: once duplicates of
      `seen` (and of each other) are dropped, they denote the same sequence of new leaves.
      This is the leaf-preservation notion regex rewrites must satisfy; see `EquivNodup` for
      the equivalent characterization via `FilterLeaves`. */
  predicate LeavesEquiv(seen: seq<Pair>, l1: seq<Leaf>, l2: seq<Leaf>)
    decreases |l1| + |l2|
  {
    (|l1| == 0 && |l2| == 0)  // equiv_nil
    || (|l1| > 0 && l1[0] in seen && LeavesEquiv(seen, l1[1..], l2))  // equiv_seen_left
    || (|l2| > 0 && l2[0] in seen && LeavesEquiv(seen, l1, l2[1..]))  // equiv_seen_right
    || (|l1| > 0 && |l2| > 0 && l1[0] == l2[0] && !(l1[0] in seen) && LeavesEquiv([l1[0]] + seen, l1[1..], l2[1..]))  // equiv_cons
  }

  // Coq: leaves_equiv_refl
  /** `LeavesEquiv` is reflexive: any list is equivalent to itself. */
  lemma LeavesEquivRefl(l: seq<Leaf>, seen: seq<Pair>)
    ensures LeavesEquiv(seen, l, l)
    decreases l
  {
    if |l| != 0 {
      if l[0] in seen {
        LeavesEquivRefl(l[1..], seen);
        assert LeavesEquiv(seen, l[1..], l);  // equiv_seen_left on the right-built version
      } else {
        LeavesEquivRefl(l[1..], [l[0]] + seen);
      }
    }
  }

  // Coq: leaves_equiv_comm
  /** `LeavesEquiv` is symmetric. */
  lemma LeavesEquivComm(l1: seq<Leaf>, l2: seq<Leaf>, seen: seq<Pair>)
    requires LeavesEquiv(seen, l1, l2)
    ensures LeavesEquiv(seen, l2, l1)
    decreases |l1| + |l2|
  {
    if |l1| == 0 && |l2| == 0 {
    } else if |l1| > 0 && l1[0] in seen && LeavesEquiv(seen, l1[1..], l2) {
      LeavesEquivComm(l1[1..], l2, seen);
    } else if |l2| > 0 && l2[0] in seen && LeavesEquiv(seen, l1, l2[1..]) {
      LeavesEquivComm(l1, l2[1..], seen);
    } else {
      LeavesEquivComm(l1[1..], l2[1..], [l1[0]] + seen);
    }
  }

  // Coq: equiv_head
  /** Leaf lists equivalent with an empty `seen` set have the same first element — so
      `LeavesEquiv([], l1, l2)` implies `l1` and `l2` give the same highest-priority result
      (`HdError`). */
  lemma EquivHead(l1: seq<Leaf>, l2: seq<Leaf>)
    requires LeavesEquiv([], l1, l2)
    ensures HdError(l1) == HdError(l2)
  {}

  // Coq: leaves_equiv_trans (via equiv_nodup)
  /** `LeavesEquiv` is transitive (for a fixed `seen` set), via the `FilterLeaves`
      characterization in `EquivNodup`. */
  lemma LeavesEquivTrans(l1: seq<Leaf>, l2: seq<Leaf>, l3: seq<Leaf>, seen: seq<Pair>)
    requires LeavesEquiv(seen, l1, l2)
    requires LeavesEquiv(seen, l2, l3)
    ensures LeavesEquiv(seen, l1, l3)
  {
    EquivNodup(l1, l2, seen);
    EquivNodup(l2, l3, seen);
    EquivNodup(l1, l3, seen);
  }

  // ===== Discharged: inductions over leaves_equiv / filter_leaves. =====

  // ----- filter_leaves helpers -----
  // FilterLeaves depends on `seen` only through its membership set.
  /** `FilterLeaves` depends on `seen` only through its membership set: swapping `seen` for
      a list with the same elements doesn't change the result. */
  lemma FilterLeavesSeenExt(l: seq<Leaf>, s1: seq<Pair>, s2: seq<Pair>)
    requires forall x :: x in s1 <==> x in s2
    ensures FilterLeaves(l, s1) == FilterLeaves(l, s2)
    decreases l
  {
    if |l| != 0 {
      if l[0] in s1 {
        FilterLeavesSeenExt(l[1..], s1, s2);
      } else {
        FilterLeavesSeenExt(l[1..], [l[0]] + s1, [l[0]] + s2);
      }
    }
  }

  // x survives filtering iff it occurs and is not already seen.
  /** A leaf survives `FilterLeaves` iff it occurs in `l` and was not already in `seen`. */
  lemma FilterLeavesMembership(l: seq<Leaf>, seen: seq<Pair>, x: Leaf)
    ensures x in FilterLeaves(l, seen) <==> (x in l && x !in seen)
    decreases l
  {
    if |l| != 0 {
      if l[0] in seen {
        FilterLeavesMembership(l[1..], seen, x);
      } else {
        FilterLeavesMembership(l[1..], [l[0]] + seen, x);
      }
    }
  }

  // A prefix entirely contained in `seen` is dropped by filtering.
  /** A prefix entirely contained in `seen` contributes nothing: filtering `pre + l` is the
      same as filtering `l` alone. */
  lemma FilterLeavesPrefixSeen(pre: seq<Leaf>, l: seq<Leaf>, seen: seq<Pair>)
    requires forall x :: x in pre ==> x in seen
    ensures FilterLeaves(pre + l, seen) == FilterLeaves(l, seen)
    decreases pre
  {
    if |pre| == 0 {
      assert pre + l == l;
    } else {
      assert (pre + l)[0] == pre[0] && (pre + l)[1..] == pre[1..] + l;
      FilterLeavesPrefixSeen(pre[1..], l, seen);
    }
  }

  // The accumulated seen-set after filtering a prefix.
  /** The seen-set accumulated after `FilterLeaves` has walked all of `l` starting from
      `seen`. */
  function SeenAfter(l: seq<Leaf>, seen: seq<Pair>): seq<Pair>
    decreases l
  {
    if |l| == 0 then seen
    else if l[0] in seen then SeenAfter(l[1..], seen)
    else SeenAfter(l[1..], [l[0]] + seen)
  }

  /** `SeenAfter(l, seen)` contains exactly the elements of `seen` together with those of `l`. */
  lemma SeenAfterMembership(l: seq<Leaf>, seen: seq<Pair>, x: Pair)
    ensures x in SeenAfter(l, seen) <==> (x in seen || x in l)
    decreases l
  {
    if |l| != 0 {
      if l[0] in seen { SeenAfterMembership(l[1..], seen, x); }
      else { SeenAfterMembership(l[1..], [l[0]] + seen, x); }
    }
  }

  /** Filtering a concatenation splits: filter the first part, then filter the second part
      against the seen-set accumulated by the first (`SeenAfter`). */
  lemma FilterLeavesApp(a: seq<Leaf>, b: seq<Leaf>, seen: seq<Pair>)
    ensures FilterLeaves(a + b, seen) == FilterLeaves(a, seen) + FilterLeaves(b, SeenAfter(a, seen))
    decreases a
  {
    if |a| == 0 {
      assert a + b == b;
    } else {
      assert (a + b)[0] == a[0] && (a + b)[1..] == a[1..] + b;
      if a[0] in seen {
        FilterLeavesApp(a[1..], b, seen);
      } else {
        FilterLeavesApp(a[1..], b, [a[0]] + seen);
      }
    }
  }

  // leaves_equiv depends on `seen` only through its membership set.
  /** `LeavesEquiv` depends on `seen` only through its membership set. */
  lemma LeavesEquivSeenExt(l1: seq<Leaf>, l2: seq<Leaf>, s1: seq<Pair>, s2: seq<Pair>)
    requires forall x :: x in s1 <==> x in s2
    requires LeavesEquiv(s1, l1, l2)
    ensures LeavesEquiv(s2, l1, l2)
    decreases |l1| + |l2|
  {
    if |l1| == 0 && |l2| == 0 {
    } else if |l1| > 0 && l1[0] in s1 && LeavesEquiv(s1, l1[1..], l2) {
      LeavesEquivSeenExt(l1[1..], l2, s1, s2);
    } else if |l2| > 0 && l2[0] in s1 && LeavesEquiv(s1, l1, l2[1..]) {
      LeavesEquivSeenExt(l1, l2[1..], s1, s2);
    } else {
      LeavesEquivSeenExt(l1[1..], l2[1..], [l1[0]] + s1, [l1[0]] + s2);
    }
  }

  // Coq: equiv_nodup — the key characterization.
  /** The key characterization: `LeavesEquiv(seen, l1, l2)` holds exactly when deduplicating
      both lists against `seen` (`FilterLeaves`) yields the same sequence. */
  lemma EquivNodup(l1: seq<Leaf>, l2: seq<Leaf>, seen: seq<Pair>)
    ensures LeavesEquiv(seen, l1, l2) <==> FilterLeaves(l1, seen) == FilterLeaves(l2, seen)
    decreases |l1| + |l2|
  {
    if LeavesEquiv(seen, l1, l2) {
      if |l1| == 0 && |l2| == 0 {
      } else if |l1| > 0 && l1[0] in seen && LeavesEquiv(seen, l1[1..], l2) {
        EquivNodup(l1[1..], l2, seen);
      } else if |l2| > 0 && l2[0] in seen && LeavesEquiv(seen, l1, l2[1..]) {
        EquivNodup(l1, l2[1..], seen);
      } else {
        assert |l1| > 0 && |l2| > 0 && l1[0] == l2[0] && !(l1[0] in seen) && LeavesEquiv([l1[0]] + seen, l1[1..], l2[1..]);
        EquivNodup(l1[1..], l2[1..], [l1[0]] + seen);
      }
    }
    if FilterLeaves(l1, seen) == FilterLeaves(l2, seen) {
      if |l1| == 0 && |l2| == 0 {
      } else if |l1| > 0 && l1[0] in seen {
        EquivNodup(l1[1..], l2, seen);   // FilterLeaves(l1,seen)==FilterLeaves(l1[1..],seen)
      } else if |l2| > 0 && l2[0] in seen {
        EquivNodup(l1, l2[1..], seen);
      } else if |l1| > 0 && |l2| > 0 {
        // both heads not in seen ⟹ heads equal and tails equiv
        assert l1[0] !in seen && l2[0] !in seen;
        assert FilterLeaves(l1, seen) == [l1[0]] + FilterLeaves(l1[1..], [l1[0]] + seen);
        assert FilterLeaves(l2, seen) == [l2[0]] + FilterLeaves(l2[1..], [l2[0]] + seen);
        assert [l1[0]] + FilterLeaves(l1[1..], [l1[0]] + seen) == [l2[0]] + FilterLeaves(l2[1..], [l2[0]] + seen);
        assert ([l1[0]] + FilterLeaves(l1[1..], [l1[0]] + seen))[0] == l1[0];
        assert ([l2[0]] + FilterLeaves(l2[1..], [l2[0]] + seen))[0] == l2[0];
        assert l1[0] == l2[0];
        assert ([l1[0]] + FilterLeaves(l1[1..], [l1[0]] + seen))[1..] == FilterLeaves(l1[1..], [l1[0]] + seen);
        assert ([l2[0]] + FilterLeaves(l2[1..], [l2[0]] + seen))[1..] == FilterLeaves(l2[1..], [l2[0]] + seen);
        assert FilterLeaves(l1[1..], [l1[0]] + seen) == FilterLeaves(l2[1..], [l1[0]] + seen);
        EquivNodup(l1[1..], l2[1..], [l1[0]] + seen);
      } else if |l1| == 0 {
        // |l2| > 0 with l2[0] not in seen ⟹ FilterLeaves(l2,seen) nonempty != [] : vacuous
        assert |l2| > 0 && l2[0] !in seen;
        assert FilterLeaves(l1, seen) == [];
        assert FilterLeaves(l2, seen) == [l2[0]] + FilterLeaves(l2[1..], [l2[0]] + seen);
        assert false;
      } else {
        assert |l1| > 0 && l1[0] !in seen && |l2| == 0;
        assert FilterLeaves(l2, seen) == [];
        assert FilterLeaves(l1, seen) == [l1[0]] + FilterLeaves(l1[1..], [l1[0]] + seen);
        assert false;
      }
    }
  }

  // Coq: equiv_remove_left
  /** An already-`seen` leaf can be dropped from the front of `l1` without affecting
      equivalence with `l2`. */
  lemma EquivRemoveLeft(l1: seq<Leaf>, l2: seq<Leaf>, inp: Input, gm: GroupMap, seen: seq<Pair>)
    requires (inp, gm) in seen
    requires LeavesEquiv(seen, [(inp, gm)] + l1, l2)
    ensures LeavesEquiv(seen, l1, l2)
  {
    EquivNodup([(inp, gm)] + l1, l2, seen);
    assert ([(inp, gm)] + l1)[0] == (inp, gm) && ([(inp, gm)] + l1)[1..] == l1;
    EquivNodup(l1, l2, seen);
  }

  // Coq: leaves_equiv_monotony
  /** Equivalence is preserved when the `seen` set grows: any superset of a witnessing
      seen-set still witnesses equivalence. */
  lemma LeavesEquivMonotony(l1: seq<Leaf>, l2: seq<Leaf>, seen1: seq<Pair>, seen2: seq<Pair>)
    requires forall x :: x in seen1 ==> x in seen2
    requires LeavesEquiv(seen1, l1, l2)
    ensures LeavesEquiv(seen2, l1, l2)
    decreases |l1| + |l2|
  {
    if |l1| == 0 && |l2| == 0 {
    } else if |l1| > 0 && l1[0] in seen1 && LeavesEquiv(seen1, l1[1..], l2) {
      LeavesEquivMonotony(l1[1..], l2, seen1, seen2);
    } else if |l2| > 0 && l2[0] in seen1 && LeavesEquiv(seen1, l1, l2[1..]) {
      LeavesEquivMonotony(l1, l2[1..], seen1, seen2);
    } else {
      // equiv_cons under seen1: heads equal, head not in seen1
      LeavesEquivMonotony(l1[1..], l2[1..], [l1[0]] + seen1, [l1[0]] + seen2);
      // now LeavesEquiv([l1[0]]+seen2, l1[1..], l2[1..])
      if l1[0] in seen2 {
        // membership of [l1[0]]+seen2 equals seen2
        LeavesEquivSeenExt(l1[1..], l2[1..], [l1[0]] + seen2, seen2);
        // drop l2[0]==l1[0] (in seen2), then l1[0]
        assert LeavesEquiv(seen2, l1[1..], l2);     // equiv_seen_right on l2[0]
        assert LeavesEquiv(seen2, l1, l2);          // equiv_seen_left on l1[0]
      }
      // else: equiv_cons under seen2 directly
    }
  }

  // Coq: equiv_cons'
  /** Prepending the same leaf `(inp, gm)` to both lists preserves equivalence, moving that
      leaf into the `seen` set. */
  lemma EquivConsP(seen: seq<Pair>, inp: Input, gm: GroupMap, l1: seq<Leaf>, l2: seq<Leaf>)
    requires LeavesEquiv([(inp, gm)] + seen, l1, l2)
    ensures LeavesEquiv(seen, [(inp, gm)] + l1, [(inp, gm)] + l2)
  {
    var h := (inp, gm);
    EquivNodup(l1, l2, [h] + seen);   // FilterLeaves(l1,[h]+seen)==FilterLeaves(l2,[h]+seen)
    assert ([h] + l1)[0] == h && ([h] + l1)[1..] == l1;
    assert ([h] + l2)[0] == h && ([h] + l2)[1..] == l2;
    if h in seen {
      // FilterLeaves([h]+l1,seen)==FilterLeaves(l1,seen); and [h]+seen ~ seen membership-wise
      LeavesEquivSeenExt(l1, l2, [h] + seen, seen);
      EquivNodup(l1, l2, seen);
      EquivNodup([h] + l1, [h] + l2, seen);
    } else {
      // FilterLeaves([h]+l1,seen)==[h]+FilterLeaves(l1,[h]+seen)
      EquivNodup([h] + l1, [h] + l2, seen);
    }
  }

  // Coq: leaves_equiv_subseen
  /** Prepending part of the seen-set itself (`subseen`) onto `l1` doesn't disturb
      equivalence with `l2`. */
  lemma LeavesEquivSubseen(l1: seq<Leaf>, l2: seq<Leaf>, seen: seq<Pair>, subseen: seq<Pair>)
    requires forall x :: x in subseen ==> x in seen
    requires LeavesEquiv(seen, l1, l2)
    ensures LeavesEquiv(seen, subseen + l1, l2)
  {
    EquivNodup(l1, l2, seen);
    FilterLeavesPrefixSeen(subseen, l1, seen);
    EquivNodup(subseen + l1, l2, seen);
  }

  // Coq: leaves_equiv_app2
  /** Equivalence composes under concatenation: if `p1 ~ p2` and, with `p1` folded into
      `seen`, `l1 ~ l2`, then the concatenations `p1+l1 ~ p2+l2`. */
  lemma LeavesEquivApp2(seen: seq<Pair>, p1: seq<Leaf>, p2: seq<Leaf>, l1: seq<Leaf>, l2: seq<Leaf>)
    requires LeavesEquiv(seen, p1, p2)
    requires LeavesEquiv(p1 + seen, l1, l2)
    ensures LeavesEquiv(seen, p1 + l1, p2 + l2)
  {
    EquivNodup(p1, p2, seen);          // FilterLeaves(p1,seen)==FilterLeaves(p2,seen)
    EquivNodup(l1, l2, p1 + seen);     // FilterLeaves(l1,p1+seen)==FilterLeaves(l2,p1+seen)
    FilterLeavesApp(p1, l1, seen);
    FilterLeavesApp(p2, l2, seen);
    // SeenAfter(p1,seen) and SeenAfter(p2,seen) both have membership == (p1+seen)
    forall x ensures x in SeenAfter(p1, seen) <==> x in (p1 + seen) {
      SeenAfterMembership(p1, seen, x);
    }
    FilterLeavesSeenExt(l1, SeenAfter(p1, seen), p1 + seen);
    forall x ensures x in SeenAfter(p2, seen) <==> x in (p1 + seen) {
      SeenAfterMembership(p2, seen, x);
      FilterLeavesMembership(p1, seen, x);
      FilterLeavesMembership(p2, seen, x);
      assert (x in FilterLeaves(p1, seen)) == (x in FilterLeaves(p2, seen));
    }
    FilterLeavesSeenExt(l2, SeenAfter(p2, seen), p1 + seen);
    EquivNodup(p1 + l1, p2 + l2, seen);
  }

  // Coq: leaves_equiv_app
  /** Concatenating two independently-equivalent pairs of leaf lists (each equivalent with
      an empty `seen` set) preserves equivalence. */
  lemma LeavesEquivApp(p1: seq<Leaf>, p2: seq<Leaf>, l1: seq<Leaf>, l2: seq<Leaf>)
    requires LeavesEquiv([], p1, p2)
    requires LeavesEquiv([], l1, l2)
    ensures LeavesEquiv([], p1 + l1, p2 + l2)
  {
    LeavesEquivMonotony(l1, l2, [], p1);   // LeavesEquiv(p1, l1, l2)
    assert p1 + [] == p1;
    LeavesEquivApp2([], p1, p2, l1, l2);
  }
}
