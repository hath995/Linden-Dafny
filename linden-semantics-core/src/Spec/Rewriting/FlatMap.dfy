// Mirror of Rewriting/FlatMap.v.
// Propositional flat_map and lemmas relating it to leaves_equiv. FlatMap is parameterized by a
// higher-order relation f: (X, seq<Y>) -> bool. The lemmas (inductions over FlatMap / leaves_equiv)
// are axiomatized; they support the equivalence proofs.
include "LeavesEquivalence.dfy"

/** A propositional flat-map relation over leaf-producing relations, and the lemmas
    connecting it to `LeavesEquiv` — the toolkit for showing that mapping an
    equivalence-preserving, per-element relation over equivalent leaf lists yields
    equivalent results. */
module FlatMap {
  import opened Chars
  import opened Groups
  import opened Tree
  import opened LeavesEquivalence

  // Coq: FlatMap lbase f lmapped.
  /** `lmapped` is obtained by relating each element of `lbase` to a chunk of output values
      via `f` and concatenating the chunks in order — a relational flat-map. */
  ghost predicate FlatMapRel<X(!new), Y(!new)>(lbase: seq<X>, f: (X, seq<Y>) -> bool, lmapped: seq<Y>)
    decreases lbase
  {
    (|lbase| == 0 && lmapped == [])  // FM_nil
    || (|lbase| > 0 && exists ly: seq<Y>, rest: seq<Y> ::
          f(lbase[0], ly) && FlatMapRel(lbase[1..], f, rest) && lmapped == ly + rest)  // FM_cons
  }

  // Coq: determ
  /** Whether `f` relates each input to at most one output — determinism. */
  ghost predicate Determ<A(!new), B(!new)>(f: (A, seq<B>) -> bool) {
    forall x, y1, y2 :: f(x, y1) && f(x, y2) ==> y1 == y2
  }

  // Coq: equiv_leaffuncts
  /** Two leaf-producing relations `f`, `g` agree up to `LeavesEquiv` on every leaf they're
      both given — i.e. `f` and `g` can be swapped in a flat-map without changing the
      equivalence class of the result. */
  ghost predicate EquivLeaffuncts(f: (Leaf, seq<Leaf>) -> bool, g: (Leaf, seq<Leaf>) -> bool) {
    forall lf, yf, yg :: f(lf, yf) && g(lf, yg) ==> LeavesEquiv([], yf, yg)
  }

  // Coq: equiv_leaffuncts_cond
  /** Like `EquivLeaffuncts`, but the agreement between `f` and `g` is only required on
      leaves satisfying `P`. */
  ghost predicate EquivLeaffunctsCond(f: (Leaf, seq<Leaf>) -> bool, g: (Leaf, seq<Leaf>) -> bool, P: Leaf -> bool) {
    forall l :: P(l) ==> forall yf, yg :: f(l, yf) && g(l, yg) ==> LeavesEquiv([], yf, yg)
  }

  // ===== Discharged: inductions over FlatMap / leaves_equiv. =====

  // Coq: FlatMap_app
  /** `FlatMapRel` distributes over concatenation of the base list. */
  lemma FlatMapApp<X(!new), Y(!new)>(lbase1: seq<X>, lbase2: seq<X>, f: (X, seq<Y>) -> bool, lmapped1: seq<Y>, lmapped2: seq<Y>)
    requires FlatMapRel(lbase1, f, lmapped1)
    requires FlatMapRel(lbase2, f, lmapped2)
    ensures FlatMapRel(lbase1 + lbase2, f, lmapped1 + lmapped2)
    decreases lbase1
  {
    if |lbase1| == 0 {
      assert lbase1 + lbase2 == lbase2;
      assert lmapped1 + lmapped2 == lmapped2;
    } else {
      var ly, rest :| f(lbase1[0], ly) && FlatMapRel(lbase1[1..], f, rest) && lmapped1 == ly + rest;
      FlatMapApp(lbase1[1..], lbase2, f, rest, lmapped2);   // FlatMapRel(lbase1[1..]+lbase2, f, rest+lmapped2)
      assert FlatMapRel(lbase1 + lbase2, f, lmapped1 + lmapped2) by {
        var concat := lbase1 + lbase2;
        var tail := rest + lmapped2;
        assert |concat| > 0;
        assert concat[0] == lbase1[0];
        assert concat[1..] == lbase1[1..] + lbase2;
        assert f(concat[0], ly);
        assert FlatMapRel(concat[1..], f, tail);
        assert lmapped1 + lmapped2 == ly + tail;
        assert exists ly': seq<Y>, rest': seq<Y> :: f(concat[0], ly') && FlatMapRel(concat[1..], f, rest') && lmapped1 + lmapped2 == ly' + rest';
      }
    }
  }

  // The image of a member leaf is a subset (membership-wise) of the flat-mapped list.
  /** For a `Determ`inistic `f`, the chunk `ye` that `f` produces for a member `e` of `lst`
      is entirely contained (membership-wise) in the overall flat-mapped result `flst`. */
  lemma FlatMapImageSubset(lst: seq<Leaf>, f: (Leaf, seq<Leaf>) -> bool, flst: seq<Leaf>, e: Leaf, ye: seq<Leaf>)
    requires Determ(f)
    requires e in lst
    requires f(e, ye)
    requires FlatMapRel(lst, f, flst)
    ensures forall x :: x in ye ==> x in flst
    decreases lst
  {
    var ly, rest :| f(lst[0], ly) && FlatMapRel(lst[1..], f, rest) && flst == ly + rest;
    if e == lst[0] {
      assert ye == ly;   // Determ
    } else {
      assert e in lst[1..];
      FlatMapImageSubset(lst[1..], f, rest, e, ye);
    }
  }

  // Coq: flatmap_leaves_equiv_l_seen
  /** Inductive workhorse for `FlatmapLeavesEquivL`: threads a `seen`/`fseen` accumulator
      through the flat-map of two `LeavesEquiv`-related base lists. */
  lemma FlatmapLeavesEquivLSeen(l1: seq<Leaf>, l2: seq<Leaf>, seen: seq<Pair>, f: (Leaf, seq<Leaf>) -> bool, fseen: seq<Leaf>, fl1: seq<Leaf>, fl2: seq<Leaf>)
    requires Determ(f)
    requires LeavesEquiv(seen, l1, l2)
    requires FlatMapRel(l1, f, fl1)
    requires FlatMapRel(l2, f, fl2)
    requires FlatMapRel(seen, f, fseen)
    ensures LeavesEquiv(fseen, fl1, fl2)
    decreases |l1| + |l2|
  {
    if |l1| == 0 && |l2| == 0 {
      assert fl1 == [] && fl2 == [];
    } else if |l1| > 0 && l1[0] in seen && LeavesEquiv(seen, l1[1..], l2) {
      var ly1, rest1 :| f(l1[0], ly1) && FlatMapRel(l1[1..], f, rest1) && fl1 == ly1 + rest1;
      FlatmapLeavesEquivLSeen(l1[1..], l2, seen, f, fseen, rest1, fl2);
      FlatMapImageSubset(seen, f, fseen, l1[0], ly1);   // ly1 ⊆ fseen
      LeavesEquivSubseen(rest1, fl2, fseen, ly1);        // LeavesEquiv(fseen, ly1+rest1, fl2)
    } else if |l2| > 0 && l2[0] in seen && LeavesEquiv(seen, l1, l2[1..]) {
      var ly2, rest2 :| f(l2[0], ly2) && FlatMapRel(l2[1..], f, rest2) && fl2 == ly2 + rest2;
      FlatmapLeavesEquivLSeen(l1, l2[1..], seen, f, fseen, fl1, rest2);   // LeavesEquiv(fseen, fl1, rest2)
      FlatMapImageSubset(seen, f, fseen, l2[0], ly2);
      LeavesEquivComm(fl1, rest2, fseen);                 // LeavesEquiv(fseen, rest2, fl1)
      LeavesEquivSubseen(rest2, fl1, fseen, ly2);         // LeavesEquiv(fseen, ly2+rest2, fl1)
      LeavesEquivComm(ly2 + rest2, fl1, fseen);           // LeavesEquiv(fseen, fl1, ly2+rest2)
    } else {
      // equiv_cons: l1[0]==l2[0], l1[0] !in seen, LeavesEquiv([l1[0]]+seen, l1[1..], l2[1..])
      var ly1, rest1 :| f(l1[0], ly1) && FlatMapRel(l1[1..], f, rest1) && fl1 == ly1 + rest1;
      var ly2, rest2 :| f(l2[0], ly2) && FlatMapRel(l2[1..], f, rest2) && fl2 == ly2 + rest2;
      assert l1[0] == l2[0];
      assert ly1 == ly2;   // Determ
      var emp: seq<Leaf> := [];
      assert FlatMapRel([l1[0]], f, ly1) by {
        assert FlatMapRel(emp, f, emp);
        assert [l1[0]][0] == l1[0] && [l1[0]][1..] == emp;
        assert ly1 == ly1 + emp;
      }
      FlatMapApp([l1[0]], seen, f, ly1, fseen);   // FlatMapRel([l1[0]]+seen, f, ly1+fseen)
      FlatmapLeavesEquivLSeen(l1[1..], l2[1..], [l1[0]] + seen, f, ly1 + fseen, rest1, rest2);
      LeavesEquivRefl(ly1, fseen);                 // LeavesEquiv(fseen, ly1, ly1)
      LeavesEquivApp2(fseen, ly1, ly1, rest1, rest2);   // LeavesEquiv(fseen, ly1+rest1, ly1+rest2)
    }
  }

  // Coq: flatmap_leaves_equiv_l
  /** Flat-mapping a deterministic relation `f` over two `LeavesEquiv`-related leaf lists
      yields `LeavesEquiv`-related results: flat-map preserves leaf-equivalence in its base
      list argument. */
  lemma FlatmapLeavesEquivL(leaves1: seq<Leaf>, leaves2: seq<Leaf>, f: (Leaf, seq<Leaf>) -> bool, leavesf1: seq<Leaf>, leavesf2: seq<Leaf>)
    requires Determ(f)
    requires LeavesEquiv([], leaves1, leaves2)
    requires FlatMapRel(leaves1, f, leavesf1)
    requires FlatMapRel(leaves2, f, leavesf2)
    ensures LeavesEquiv([], leavesf1, leavesf2)
  {
    assert FlatMapRel([], f, []);   // FM_nil
    FlatmapLeavesEquivLSeen(leaves1, leaves2, [], f, [], leavesf1, leavesf2);
  }

  // Coq: flatmap_leaves_equiv_r
  /** Flat-mapping two relations `f`, `g` that are `EquivLeaffuncts`-agreeing, over the
      *same* base list, yields `LeavesEquiv`-related results: flat-map preserves
      leaf-equivalence in its relation argument. */
  lemma FlatmapLeavesEquivR(leaves: seq<Leaf>, f: (Leaf, seq<Leaf>) -> bool, g: (Leaf, seq<Leaf>) -> bool, leavesf: seq<Leaf>, leavesg: seq<Leaf>)
    requires EquivLeaffuncts(f, g)
    requires FlatMapRel(leaves, f, leavesf)
    requires FlatMapRel(leaves, g, leavesg)
    ensures LeavesEquiv([], leavesf, leavesg)
    decreases leaves
  {
    if |leaves| == 0 {
    } else {
      var lyf, restf :| f(leaves[0], lyf) && FlatMapRel(leaves[1..], f, restf) && leavesf == lyf + restf;
      var lyg, restg :| g(leaves[0], lyg) && FlatMapRel(leaves[1..], g, restg) && leavesg == lyg + restg;
      assert LeavesEquiv([], lyf, lyg);   // EquivLeaffuncts at leaves[0]
      FlatmapLeavesEquivR(leaves[1..], f, g, restf, restg);
      LeavesEquivApp(lyf, lyg, restf, restg);
    }
  }

  // Coq: flatmap_leaves_equiv_r_prop
  /** Like `FlatmapLeavesEquivR`, but `f`/`g` only need to agree (`EquivLeaffunctsCond`) on
      leaves satisfying `P`, given every element of `l` satisfies `P`. */
  lemma FlatmapLeavesEquivRProp(l: seq<Leaf>, f: (Leaf, seq<Leaf>) -> bool, g: (Leaf, seq<Leaf>) -> bool, fl: seq<Leaf>, gl: seq<Leaf>, P: Leaf -> bool)
    requires EquivLeaffunctsCond(f, g, P)
    requires forall i :: 0 <= i < |l| ==> P(l[i])
    requires FlatMapRel(l, f, fl)
    requires FlatMapRel(l, g, gl)
    ensures LeavesEquiv([], fl, gl)
    decreases l
  {
    if |l| == 0 {
    } else {
      var lyf, restf :| f(l[0], lyf) && FlatMapRel(l[1..], f, restf) && fl == lyf + restf;
      var lyg, restg :| g(l[0], lyg) && FlatMapRel(l[1..], g, restg) && gl == lyg + restg;
      assert P(l[0]);
      assert LeavesEquiv([], lyf, lyg);   // EquivLeaffunctsCond at l[0]
      forall i | 0 <= i < |l[1..]| ensures P(l[1..][i]) { assert l[1..][i] == l[i + 1]; }
      FlatmapLeavesEquivRProp(l[1..], f, g, restf, restg, P);
      LeavesEquivApp(lyf, lyg, restf, restg);
    }
  }
}
