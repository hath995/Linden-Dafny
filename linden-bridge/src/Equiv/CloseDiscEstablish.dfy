// L3b item 4, step 1b: discharge `TreeResMirror`'s `CloseDisc` hypothesis for
// real backtracking trees. `CloseDisc(t, {})` — every Close in `t` fires on a
// currently-open group — holds for `ComputeTr` of a group-OK stack whose group
// ids are unique.
//
// THE INVARIANT THAT SURVIVES QUANTIFIERS. The naive "defined groups are
// distinct / disjoint from the open set" invariant is FALSE under a capturing
// quantifier: the residual `Areg(Quantified(min-1,..,r1))` left on the stack
// re-declares `DefGroups(r1)` while the current iteration's copies of those
// groups are still open. The fix: relate each `Areg` head's `DefGroups` to the
// pending CLOSES *below it* on the stack (`HeadsFreshOfCloses`), never to other
// defs. A quantifier unfold pushes `Areg`s, never `Aclose`s, so the pending
// closes do not grow — and the invariant is preserved. The same fact gives
// exactly the freshness each ComputeTree case needs.

include "TreeResMirror.dfy"

module LindenCloseDisc {
  import opened Std.Wrappers
  import WP = WarblrePrimitives
  import LC = Chars
  import LG = Groups
  import L = Regex
  import LN = WarblreNumeric
  import LS = Semantics
  import LT = Tree
  import LW = WarblreRegExpRecord
  import FS = FunctionalSemantics
  import FU = FunctionalUtils
  import SD = LindenSpanDuality
  import TRM = LindenTreeResMirror

  // ===========================================================================
  // The stack invariant
  // ===========================================================================

  /** The pending `Aclose` gids of a stack, in order. */
  ghost function ClosesActs(acts: LS.Actions): seq<LG.GroupId>
    decreases |acts|
  {
    if |acts| == 0 then []
    else (if acts[0].Aclose? then [acts[0].gid] else []) + ClosesActs(acts[1..])
  }

  ghost function ClosesSet(acts: LS.Actions): set<LG.GroupId> {
    set g | g in ClosesActs(acts)
  }

  ghost predicate NoDupG(s: seq<LG.GroupId>) {
    forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
  }

  /** Each `Areg` head's defined groups are disjoint from the `Aclose`s below
      it — quantifier-stable (unfolds add no closes). */
  ghost predicate HeadsFreshOfCloses(acts: LS.Actions)
    decreases |acts|
  {
    if |acts| == 0 then true
    else (acts[0].Areg? ==>
            forall g :: g in L.DefGroups(acts[0].r) ==> g !in ClosesActs(acts[1..]))
         && HeadsFreshOfCloses(acts[1..])
  }

  /** Each `Areg` head defines dup-free groups. */
  ghost predicate HeadsNoDupDefs(acts: LS.Actions)
    decreases |acts|
  {
    if |acts| == 0 then true
    else (acts[0].Areg? ==> NoDupG(L.DefGroups(acts[0].r)))
         && HeadsNoDupDefs(acts[1..])
  }

  ghost predicate StackInv(acts: LS.Actions) {
    && NoDupG(ClosesActs(acts))
    && HeadsFreshOfCloses(acts)
    && HeadsNoDupDefs(acts)
    && SD.GroupOkActs(acts)
  }

  // ===========================================================================
  // Stack plumbing
  // ===========================================================================

  lemma ClosesActsAppend(xs: LS.Actions, ys: LS.Actions)
    ensures ClosesActs(xs + ys) == ClosesActs(xs) + ClosesActs(ys)
    decreases |xs|
  {
    if |xs| == 0 {
      assert xs + ys == ys;
    } else {
      assert (xs + ys)[0] == xs[0];
      assert (xs + ys)[1..] == xs[1..] + ys;
      ClosesActsAppend(xs[1..], ys);
    }
  }

  /** `ClosesActs` of a head that is not an `Aclose` equals that of the tail. */
  lemma ClosesActsConsNonClose(a: LS.Action, cont: LS.Actions)
    requires !a.Aclose?
    ensures ClosesActs([a] + cont) == ClosesActs(cont)
  {
    assert ([a] + cont)[0] == a;
    assert ([a] + cont)[1..] == cont;
  }

  lemma ClosesActsConsClose(gid: LG.GroupId, cont: LS.Actions)
    ensures ClosesActs([LS.Aclose(gid)] + cont) == [gid] + ClosesActs(cont)
  {
    assert ([LS.Aclose(gid)] + cont)[0] == LS.Aclose(gid);
    assert ([LS.Aclose(gid)] + cont)[1..] == cont;
  }

  // ===========================================================================
  // Invariant preservation across the ComputeTree stack transformations
  // ===========================================================================

  lemma StackInvTail(acts: LS.Actions)
    requires |acts| > 0 && StackInv(acts)
    ensures StackInv(acts[1..])
  {
    SD.GroupOkActsTail(acts);
    assert acts == [acts[0]] + acts[1..];
    if acts[0].Aclose? {
      assert acts[0] == LS.Aclose(acts[0].gid);
      ClosesActsConsClose(acts[0].gid, acts[1..]);
      NoDupGTail(acts[0].gid, ClosesActs(acts[1..]));
    } else {
      ClosesActsConsNonClose(acts[0], acts[1..]);
    }
  }

  /** Prepending a group-OK `Areg`/`Acheck` whose defs avoid the current closes. */
  lemma StackInvConsFront(a: LS.Action, cont: LS.Actions)
    requires StackInv(cont)
    requires a.Acheck? || (a.Areg? && SD.GroupOkL(a.r)
                           && NoDupG(L.DefGroups(a.r))
                           && (forall g :: g in L.DefGroups(a.r) ==> g !in ClosesActs(cont)))
    ensures StackInv([a] + cont)
  {
    ClosesActsConsNonClose(a, cont);
    assert ([a] + cont)[1..] == cont;
    SD.GroupOkActsCons(a, cont);
  }

  /** The `Group(gid,r1)` expansion: `[Areg(Group(gid,r1))]+cont` →
      `[Areg(r1), Aclose(gid)]+cont`. */
  lemma StackInvGroup(gid: LG.GroupId, r1: L.Regex, cont: LS.Actions)
    requires StackInv([LS.Areg(L.Group(gid, r1))] + cont)
    ensures StackInv([LS.Areg(r1), LS.Aclose(gid)] + cont)
  {
    var acts := [LS.Areg(L.Group(gid, r1))] + cont;
    assert acts[0] == LS.Areg(L.Group(gid, r1)) && acts[1..] == cont;
    StackInvTail(acts);                     // StackInv(cont)
    assert L.DefGroups(L.Group(gid, r1)) == [gid] + L.DefGroups(r1);
    // head facts from StackInv(acts)
    assert NoDupG([gid] + L.DefGroups(r1));                        // HeadsNoDupDefs
    NoDupGTail(gid, L.DefGroups(r1));                              // gid∉DefGroups(r1), NoDupG(DefGroups(r1))
    assert NoDupG(L.DefGroups(r1));
    assert gid !in L.DefGroups(r1);
    assert forall g :: g in [gid] + L.DefGroups(r1) ==> g !in ClosesActs(cont);  // HeadsFresh
    assert gid !in ClosesActs(cont);
    assert forall g :: g in L.DefGroups(r1) ==> g !in ClosesActs(cont);
    assert SD.GroupOkActs(acts) && 0 < |acts| && acts[0].Areg? && acts[0].r == L.Group(gid, r1);
    assert SD.GroupOkL(L.Group(gid, r1));   // GroupOkActs(acts) at head
    assert SD.GroupOkL(r1);                 // == GroupOkL(Group(gid,r1)) by defn

    var mid := [LS.Aclose(gid)] + cont;
    // StackInv(mid)
    ClosesActsConsClose(gid, cont);
    assert ClosesActs(mid) == [gid] + ClosesActs(cont);
    NoDupGPrepend(gid, ClosesActs(cont));
    assert NoDupG(ClosesActs(mid));
    assert mid[0] == LS.Aclose(gid) && mid[1..] == cont;
    assert HeadsFreshOfCloses(mid);
    assert HeadsNoDupDefs(mid);
    SD.GroupOkActsCons(LS.Aclose(gid), cont);
    assert StackInv(mid);

    // now prepend Areg(r1); its defs must avoid ClosesActs(mid) = [gid]+ClosesActs(cont)
    forall g | g in L.DefGroups(r1) ensures g !in ClosesActs(mid) {
      assert g != gid;
      assert g !in ClosesActs(cont);
    }
    StackInvConsFront(LS.Areg(r1), mid);
    assert [LS.Areg(r1)] + mid == [LS.Areg(r1), LS.Aclose(gid)] + cont;
  }

  /** A prefix of group-OK `Areg`/`Acheck` heads whose defs are all inside
      `DefGroups(rSrc)` (so they avoid the closes because `rSrc`'s defs do),
      each dup-free — the common shape of the quantifier / sequence / disjunction
      expansions. Proved by front-consing. */
  lemma StackInvConsRegAvoid(r: L.Regex, cont: LS.Actions)
    requires StackInv(cont)
    requires SD.GroupOkL(r) && NoDupG(L.DefGroups(r))
    requires forall g :: g in L.DefGroups(r) ==> g !in ClosesActs(cont)
    ensures StackInv([LS.Areg(r)] + cont)
  {
    StackInvConsFront(LS.Areg(r), cont);
  }

  // ===========================================================================
  // NoDup helpers
  // ===========================================================================

  lemma NoDupGTail(x: LG.GroupId, b: seq<LG.GroupId>)
    requires NoDupG([x] + b)
    ensures NoDupG(b)
    ensures x !in b
  {
    forall i, j | 0 <= i < j < |b| ensures b[i] != b[j] {
      assert ([x] + b)[i + 1] == b[i] && ([x] + b)[j + 1] == b[j];
    }
    forall k | 0 <= k < |b| ensures b[k] != x {
      assert ([x] + b)[0] == x && ([x] + b)[k + 1] == b[k];
    }
  }

  lemma NoDupGPrepend(x: LG.GroupId, b: seq<LG.GroupId>)
    requires NoDupG(b)
    requires x !in b
    ensures NoDupG([x] + b)
  {
    forall i, j | 0 <= i < j < |[x] + b| ensures ([x] + b)[i] != ([x] + b)[j] {
      if i == 0 {
        assert ([x] + b)[i] == x && ([x] + b)[j] == b[j - 1] && b[j - 1] in b;
      } else {
        assert ([x] + b)[i] == b[i - 1] && ([x] + b)[j] == b[j - 1];
      }
    }
  }

  // ===========================================================================
  // THE ESTABLISHMENT (fueled)
  // ===========================================================================

  lemma CloseDiscCT(rer: LW.RegExpRecord, acts: LS.Actions, inp: LC.Input,
                    gm: LG.GroupMap, dir: WP.Direction, fuel: nat)
    requires StackInv(acts)
    ensures var o := FS.ComputeTree(rer, acts, inp, gm, dir, fuel);
            o.Some? ==> TRM.CloseDisc(o.value, ClosesSet(acts))
    decreases fuel
  {
    if fuel == 0 { return; }
    var f := fuel - 1;
    if |acts| == 0 { return; }
    var cont := acts[1..];
    var O := ClosesSet(acts);
    match acts[0]
    case Acheck(strcheck) =>
      ClosesActsConsNonClose(acts[0], cont);
      assert acts == [acts[0]] + cont;
      assert ClosesSet(acts) == ClosesSet(cont);
      if SD.SSx.IsStrictSuffix(inp, strcheck, dir) {
        StackInvTail(acts);
        CloseDiscCT(rer, cont, inp, gm, dir, f);
      }
    case Aclose(gid) =>
      ClosesActsConsClose(gid, cont);
      assert acts == [LS.Aclose(gid)] + cont;
      assert ClosesActs(acts) == [gid] + ClosesActs(cont);
      NoDupGTail(gid, ClosesActs(cont));
      assert gid !in ClosesActs(cont);
      StackInvTail(acts);
      CloseDiscCT(rer, cont, inp, LG.GMClose(LC.Idx(inp), gid, gm), dir, f);
      var sub := FS.ComputeTree(rer, cont, inp, LG.GMClose(LC.Idx(inp), gid, gm), dir, f);
      if sub.Some? {
        assert gid in O;
        assert O - {gid} == ClosesSet(cont);
        assert TRM.CloseDisc(LT.GroupActionT(LG.Close(gid), sub.value), O);
      }
    case Areg(r) =>
      assert acts == [LS.Areg(r)] + cont;
      ClosesActsConsNonClose(acts[0], cont);
      assert ClosesSet(acts) == ClosesSet(cont);
      SD.GroupOkActsTail(acts);
      assert SD.GroupOkActs(cont);
      // head facts
      assert SD.GroupOkL(r);
      assert NoDupG(L.DefGroups(r));
      assert forall g :: g in L.DefGroups(r) ==> g !in ClosesActs(cont);
      match r
      case Epsilon =>
        StackInvTail(acts);
        CloseDiscCT(rer, cont, inp, gm, dir, f);
      case Character(cd) =>
        match LC.ReadChar(rer, cd, inp, dir) {
          case Some(pair) =>
            StackInvTail(acts);
            CloseDiscCT(rer, cont, pair.1, gm, dir, f);
          case None =>
        }
      case Disjunction(r1, r2) =>
        assert L.DefGroups(r) == L.DefGroups(r1) + L.DefGroups(r2);
        DefGroupsConcatAvoid(r1, r2, cont);
        DefGroupsConcatNoDup(r1, r2);
        StackInvTail(acts);
        StackInvConsRegAvoid(r1, cont);
        StackInvConsRegAvoid(r2, cont);
        CloseDiscCT(rer, [LS.Areg(r1)] + cont, inp, gm, dir, f);
        CloseDiscCT(rer, [LS.Areg(r2)] + cont, inp, gm, dir, f);
        assert ClosesSet([LS.Areg(r1)] + cont) == ClosesSet(cont) by { ClosesActsConsNonClose(LS.Areg(r1), cont); }
        assert ClosesSet([LS.Areg(r2)] + cont) == ClosesSet(cont) by { ClosesActsConsNonClose(LS.Areg(r2), cont); }
      case Sequence(r1, r2) =>
        assert L.DefGroups(r) == L.DefGroups(r1) + L.DefGroups(r2);
        StackInvTail(acts);
        SeqListStackInv(r1, r2, dir, cont);
        CloseDiscCT(rer, LS.SeqList(r1, r2, dir) + cont, inp, gm, dir, f);
      case Quantified(greedy, min, delta, r1) =>
        var gidl := L.DefGroups(r1);
        assert L.DefGroups(r) == gidl;
        assert forall g :: g in gidl ==> g !in ClosesActs(cont);
        assert (set g | g in gidl) * O == {};
        StackInvTail(acts);
        if min > 0 {
          var q1 := L.Quantified(greedy, min - 1, delta, r1);
          QuantStackInv(greedy, min, delta, r1, cont);
          CloseDiscCT(rer, [LS.Areg(r1), LS.Areg(q1)] + cont, inp, LG.GMReset(gidl, gm), dir, f);
          var titer := FS.ComputeTree(rer, [LS.Areg(r1), LS.Areg(q1)] + cont, inp, LG.GMReset(gidl, gm), dir, f);
          if titer.Some? {
            assert ClosesSet([LS.Areg(r1), LS.Areg(q1)] + cont) == O by { QuantClosesSet(r1, q1, cont); }
            assert O - (set g | g in gidl) == O;
            assert TRM.CloseDisc(LT.GroupActionT(LG.Reset(gidl), titer.value), O);
          }
        } else if delta == LN.NN(0) {
          CloseDiscCT(rer, cont, inp, gm, dir, f);
        } else {
          var q0 := L.Quantified(greedy, 0, FS.NoiPred(delta), r1);
          QuantFreeStackInv(greedy, delta, r1, inp, cont);
          CloseDiscCT(rer, [LS.Areg(r1), LS.Acheck(inp), LS.Areg(q0)] + cont, inp, LG.GMReset(gidl, gm), dir, f);
          CloseDiscCT(rer, cont, inp, gm, dir, f);
          var titer := FS.ComputeTree(rer, [LS.Areg(r1), LS.Acheck(inp), LS.Areg(q0)] + cont, inp, LG.GMReset(gidl, gm), dir, f);
          var tskip := FS.ComputeTree(rer, cont, inp, gm, dir, f);
          if titer.Some? && tskip.Some? {
            assert ClosesSet([LS.Areg(r1), LS.Acheck(inp), LS.Areg(q0)] + cont) == O by { QuantFreeClosesSet(r1, q0, inp, cont); }
            assert O - (set g | g in gidl) == O;
            assert TRM.CloseDisc(LT.GroupActionT(LG.Reset(gidl), titer.value), O);
            assert TRM.CloseDisc(tskip.value, O);
            assert TRM.CloseDisc(LT.GreedyChoice(greedy, LT.GroupActionT(LG.Reset(gidl), titer.value), tskip.value), O);
          }
        }
      case Group(gid, r1) =>
        StackInvGroup(gid, r1, cont);
        CloseDiscCT(rer, [LS.Areg(r1), LS.Aclose(gid)] + cont, inp, LG.GMOpen(LC.Idx(inp), gid, gm), dir, f);
        var sub := FS.ComputeTree(rer, [LS.Areg(r1), LS.Aclose(gid)] + cont, inp, LG.GMOpen(LC.Idx(inp), gid, gm), dir, f);
        if sub.Some? {
          assert ClosesSet([LS.Areg(r1), LS.Aclose(gid)] + cont) == O + {gid} by { GroupClosesSet(r1, gid, cont); }
          assert TRM.CloseDisc(LT.GroupActionT(LG.Open(gid), sub.value), O);
        }
      case AnchorR(a) =>
        if LS.AnchorSatisfied(rer, a, inp) {
          StackInvTail(acts);
          CloseDiscCT(rer, cont, inp, gm, dir, f);
        }
      case LookaroundR(lk, r1) =>
        assert SD.GroupOkL(r);
        assert false;
      case Backreference(gid) =>
        assert SD.GroupOkL(r);
        assert false;
  }

  // ===========================================================================
  // DefGroups / ClosesSet arithmetic used above
  // ===========================================================================

  lemma DefGroupsConcatAvoid(r1: L.Regex, r2: L.Regex, cont: LS.Actions)
    requires forall g :: g in L.DefGroups(r1) + L.DefGroups(r2) ==> g !in ClosesActs(cont)
    ensures forall g :: g in L.DefGroups(r1) ==> g !in ClosesActs(cont)
    ensures forall g :: g in L.DefGroups(r2) ==> g !in ClosesActs(cont)
  {}

  lemma DefGroupsConcatNoDup(r1: L.Regex, r2: L.Regex)
    requires NoDupG(L.DefGroups(r1) + L.DefGroups(r2))
    ensures NoDupG(L.DefGroups(r1))
    ensures NoDupG(L.DefGroups(r2))
  {
    var a := L.DefGroups(r1);
    var b := L.DefGroups(r2);
    forall i, j | 0 <= i < j < |a| ensures a[i] != a[j] {
      assert (a + b)[i] == a[i] && (a + b)[j] == a[j];
    }
    forall i, j | 0 <= i < j < |b| ensures b[i] != b[j] {
      assert (a + b)[i + |a|] == b[i] && (a + b)[j + |a|] == b[j];
    }
  }

  lemma SeqListStackInv(r1: L.Regex, r2: L.Regex, dir: WP.Direction, cont: LS.Actions)
    requires StackInv(cont)
    requires SD.GroupOkL(r1) && SD.GroupOkL(r2)
    requires NoDupG(L.DefGroups(r1) + L.DefGroups(r2))
    requires forall g :: g in L.DefGroups(r1) + L.DefGroups(r2) ==> g !in ClosesActs(cont)
    ensures StackInv(LS.SeqList(r1, r2, dir) + cont)
  {
    DefGroupsConcatNoDup(r1, r2);
    DefGroupsConcatAvoid(r1, r2, cont);
    match dir {
      case Forward =>
        assert LS.SeqList(r1, r2, dir) == [LS.Areg(r1), LS.Areg(r2)];
        StackInvConsRegAvoid(r2, cont);
        assert ClosesActs([LS.Areg(r2)] + cont) == ClosesActs(cont) by { ClosesActsConsNonClose(LS.Areg(r2), cont); }
        StackInvConsRegAvoid(r1, [LS.Areg(r2)] + cont);
        assert [LS.Areg(r1)] + ([LS.Areg(r2)] + cont) == [LS.Areg(r1), LS.Areg(r2)] + cont;
      case Backward =>
        assert LS.SeqList(r1, r2, dir) == [LS.Areg(r2), LS.Areg(r1)];
        StackInvConsRegAvoid(r1, cont);
        assert ClosesActs([LS.Areg(r1)] + cont) == ClosesActs(cont) by { ClosesActsConsNonClose(LS.Areg(r1), cont); }
        StackInvConsRegAvoid(r2, [LS.Areg(r1)] + cont);
        assert [LS.Areg(r2)] + ([LS.Areg(r1)] + cont) == [LS.Areg(r2), LS.Areg(r1)] + cont;
    }
  }

  lemma QuantStackInv(greedy: bool, min: nat, delta: LN.NoI, r1: L.Regex, cont: LS.Actions)
    requires StackInv(cont)
    requires SD.GroupOkL(r1) && NoDupG(L.DefGroups(r1))
    requires forall g :: g in L.DefGroups(r1) ==> g !in ClosesActs(cont)
    ensures StackInv([LS.Areg(r1), LS.Areg(L.Quantified(greedy, min - 1, delta, r1))] + cont)
    requires min > 0
  {
    var q1 := L.Quantified(greedy, min - 1, delta, r1);
    assert L.DefGroups(q1) == L.DefGroups(r1);
    assert SD.GroupOkL(q1);
    StackInvConsRegAvoid(q1, cont);
    assert ClosesActs([LS.Areg(q1)] + cont) == ClosesActs(cont) by { ClosesActsConsNonClose(LS.Areg(q1), cont); }
    StackInvConsRegAvoid(r1, [LS.Areg(q1)] + cont);
    assert [LS.Areg(r1)] + ([LS.Areg(q1)] + cont) == [LS.Areg(r1), LS.Areg(q1)] + cont;
  }

  lemma QuantFreeStackInv(greedy: bool, delta: LN.NoI, r1: L.Regex, inpc: LC.Input, cont: LS.Actions)
    requires StackInv(cont)
    requires SD.GroupOkL(r1) && NoDupG(L.DefGroups(r1))
    requires forall g :: g in L.DefGroups(r1) ==> g !in ClosesActs(cont)
    ensures StackInv([LS.Areg(r1), LS.Acheck(inpc), LS.Areg(L.Quantified(greedy, 0, FS.NoiPred(delta), r1))] + cont)
  {
    var q0 := L.Quantified(greedy, 0, FS.NoiPred(delta), r1);
    assert L.DefGroups(q0) == L.DefGroups(r1);
    assert SD.GroupOkL(q0);
    StackInvConsRegAvoid(q0, cont);
    var s1 := [LS.Areg(q0)] + cont;
    assert ClosesActs(s1) == ClosesActs(cont) by { ClosesActsConsNonClose(LS.Areg(q0), cont); }
    StackInvConsFront(LS.Acheck(inpc), s1);
    var s2 := [LS.Acheck(inpc)] + s1;
    assert ClosesActs(s2) == ClosesActs(cont) by { ClosesActsConsNonClose(LS.Acheck(inpc), s1); }
    StackInvConsRegAvoid(r1, s2);
    assert [LS.Areg(r1)] + s2 == [LS.Areg(r1), LS.Acheck(inpc), LS.Areg(q0)] + cont;
  }

  lemma GroupClosesSet(r1: L.Regex, gid: LG.GroupId, cont: LS.Actions)
    ensures ClosesSet([LS.Areg(r1), LS.Aclose(gid)] + cont)
         == ClosesSet(cont) + {gid}
  {
    assert [LS.Areg(r1), LS.Aclose(gid)] + cont == [LS.Areg(r1)] + ([LS.Aclose(gid)] + cont);
    ClosesActsConsNonClose(LS.Areg(r1), [LS.Aclose(gid)] + cont);
    ClosesActsConsClose(gid, cont);
    assert ClosesActs([LS.Areg(r1), LS.Aclose(gid)] + cont) == [gid] + ClosesActs(cont);
  }

  lemma QuantClosesSet(r1: L.Regex, q1: L.Regex, cont: LS.Actions)
    ensures ClosesSet([LS.Areg(r1), LS.Areg(q1)] + cont) == ClosesSet(cont)
  {
    assert [LS.Areg(r1), LS.Areg(q1)] + cont == [LS.Areg(r1)] + ([LS.Areg(q1)] + cont);
    ClosesActsConsNonClose(LS.Areg(r1), [LS.Areg(q1)] + cont);
    ClosesActsConsNonClose(LS.Areg(q1), cont);
  }

  lemma QuantFreeClosesSet(r1: L.Regex, q0: L.Regex, inpc: LC.Input, cont: LS.Actions)
    ensures ClosesSet([LS.Areg(r1), LS.Acheck(inpc), LS.Areg(q0)] + cont) == ClosesSet(cont)
  {
    assert [LS.Areg(r1), LS.Acheck(inpc), LS.Areg(q0)] + cont
        == [LS.Areg(r1)] + ([LS.Acheck(inpc)] + ([LS.Areg(q0)] + cont));
    ClosesActsConsNonClose(LS.Areg(r1), [LS.Acheck(inpc)] + ([LS.Areg(q0)] + cont));
    ClosesActsConsNonClose(LS.Acheck(inpc), [LS.Areg(q0)] + cont);
    ClosesActsConsNonClose(LS.Areg(q0), cont);
  }

  // ===========================================================================
  // Fuel-free wrapper + the body corollary
  // ===========================================================================

  lemma CloseDiscComputeTr(rer: LW.RegExpRecord, acts: LS.Actions, inp: LC.Input,
                           gm: LG.GroupMap, dir: WP.Direction)
    requires StackInv(acts)
    ensures TRM.CloseDisc(FU.ComputeTr(rer, acts, inp, gm, dir), ClosesSet(acts))
  {
    var fuel := FS.ActionsFuel(acts, inp, dir) + 1;
    FS.FunctionalTerminates(rer, acts, inp, gm, dir, fuel);
    CloseDiscCT(rer, acts, inp, gm, dir, fuel);
  }

  /** The call-site corollary: the tree of a single group-OK, unique-id regex
      from a fresh stack satisfies `CloseDisc` at the empty open set — exactly
      `TreeResMirror`'s hypothesis. */
  lemma CloseDiscBody(rer: LW.RegExpRecord, r: L.Regex, inp: LC.Input,
                      gm: LG.GroupMap, dir: WP.Direction)
    requires SD.GroupOkL(r) && NoDupG(L.DefGroups(r))
    ensures TRM.CloseDisc(FU.ComputeTr(rer, [LS.Areg(r)], inp, gm, dir), {})
  {
    assert ClosesActs([LS.Areg(r)]) == [] by { ClosesActsConsNonClose(LS.Areg(r), []); }
    assert forall g :: g in L.DefGroups(r) ==> g !in ClosesActs([LS.Areg(r)][1..]);
    assert HeadsFreshOfCloses([LS.Areg(r)]);
    assert HeadsNoDupDefs([LS.Areg(r)]);
    assert SD.GroupOkActs([LS.Areg(r)]) by { SD.GroupOkActsCons(LS.Areg(r), []); }
    assert StackInv([LS.Areg(r)]);
    assert ClosesSet([LS.Areg(r)]) == {};
    CloseDiscComputeTr(rer, [LS.Areg(r)], inp, gm, dir);
  }
}
