// Phase +B: the check-insertion equivalence — inserting an always-passing
// Acheck into an action list preserves the computed tree up to Progress
// nodes, hence preserves leaves.
//
// This is the semantic core of the do-while campaign (ROADMAP.md §1): the
// compiler's `+` scheme omits the empty-iteration guard, so the engine's
// backward fork must consume `Progress(Choice(...))` uniformly. We get that
// uniformity by relating the engine to trees of CHECKED action lists (an
// `Acheck` inserted after the last forced body) and bridging back to the
// standard spec tree with the lemmas here: the inserted check always passes
// because a NonNullable component precedes it (`NullableFacts`), and
// `Progress` is a definitional pass-through in `TreeLeaves`.

include "EntryLk.dfy"

/** The check-insertion equivalence over the functional tree semantics
    (`ComputeTree`): fuel monotonicity, the leaves-agreement relation, and
    the guarded insertion lemma. */
module LindenElkCheckErase {
  import opened Std.Wrappers
  import LC = Chars
  import LG = Groups
  import LT = Tree
  import LS = Semantics
  import FS = FunctionalSemantics
  import SS = StrictSuffix
  import WP = WarblrePrimitives
  import LW = WarblreRegExpRecord
  import L = Regex
  import LN = WarblreNumeric
  import PS = PikeSubset
  import EL = LindenElkEntryLk
  import BS = BooleanSemantics
  import NN = LindenElkNullable

  /** `ComputeTree` is fuel-monotone: a result obtained at fuel `f` is stable
      under any larger fuel. */
  lemma ComputeTreeFuelMono(rer: LW.RegExpRecord, act: LS.Actions, inp: LC.Input,
                            gm: LG.GroupMap, dir: WP.Direction, f: nat, f': nat)
    requires f <= f'
    requires FS.ComputeTree(rer, act, inp, gm, dir, f).Some?
    ensures FS.ComputeTree(rer, act, inp, gm, dir, f') == FS.ComputeTree(rer, act, inp, gm, dir, f)
    decreases f
  {
    if |act| == 0 {
    } else {
      var cont := act[1..];
      match act[0]
      case Acheck(strcheck) =>
        if SS.IsStrictSuffix(inp, strcheck, dir) {
          ComputeTreeFuelMono(rer, cont, inp, gm, dir, f - 1, f' - 1);
        }
      case Aclose(gid) =>
        ComputeTreeFuelMono(rer, cont, inp, LG.GMClose(LC.Idx(inp), gid, gm), dir, f - 1, f' - 1);
      case Areg(r) =>
        match r
        case Epsilon =>
          ComputeTreeFuelMono(rer, cont, inp, gm, dir, f - 1, f' - 1);
        case Character(cd) =>
          match LC.ReadChar(rer, cd, inp, dir) {
            case Some(pair) =>
              ComputeTreeFuelMono(rer, cont, pair.1, gm, dir, f - 1, f' - 1);
            case None =>
          }
        case Disjunction(r1, r2) =>
          ComputeTreeFuelMono(rer, [LS.Areg(r1)] + cont, inp, gm, dir, f - 1, f' - 1);
          ComputeTreeFuelMono(rer, [LS.Areg(r2)] + cont, inp, gm, dir, f - 1, f' - 1);
        case Sequence(r1, r2) =>
          ComputeTreeFuelMono(rer, LS.SeqList(r1, r2, dir) + cont, inp, gm, dir, f - 1, f' - 1);
        case Quantified(greedy, min, delta, r1) =>
          var gidl := L.DefGroups(r1);
          if min > 0 {
            ComputeTreeFuelMono(rer, [LS.Areg(r1), LS.Areg(L.Quantified(greedy, min - 1, delta, r1))] + cont,
                                inp, LG.GMReset(gidl, gm), dir, f - 1, f' - 1);
          } else if delta == LN.NN(0) {
            ComputeTreeFuelMono(rer, cont, inp, gm, dir, f - 1, f' - 1);
          } else {
            ComputeTreeFuelMono(rer, [LS.Areg(r1), LS.Acheck(inp), LS.Areg(L.Quantified(greedy, 0, FS.NoiPred(delta), r1))] + cont,
                                inp, LG.GMReset(gidl, gm), dir, f - 1, f' - 1);
            ComputeTreeFuelMono(rer, cont, inp, gm, dir, f - 1, f' - 1);
          }
        case Group(gid, r1) =>
          ComputeTreeFuelMono(rer, [LS.Areg(r1), LS.Aclose(gid)] + cont, inp, LG.GMOpen(LC.Idx(inp), gid, gm), dir, f - 1, f' - 1);
        case LookaroundR(lk, r1) =>
          ComputeTreeFuelMono(rer, [LS.Areg(r1)], inp, gm, L.LkDir(lk), f - 1, f' - 1);
          var treelk := FS.ComputeTree(rer, [LS.Areg(r1)], inp, gm, L.LkDir(lk), f - 1).value;
          match LS.LkResult(lk, treelk, gm, inp) {
            case Some(gmlk) =>
              ComputeTreeFuelMono(rer, cont, inp, gmlk, dir, f - 1, f' - 1);
            case None =>
          }
        case AnchorR(a) =>
          if LS.AnchorSatisfied(rer, a, inp) {
            ComputeTreeFuelMono(rer, cont, inp, gm, dir, f - 1, f' - 1);
          }
        case Backreference(gid) =>
          match LS.ReadBackref(rer, gm, gid, inp, dir) {
            case Some(pair) =>
              ComputeTreeFuelMono(rer, cont, pair.1, gm, dir, f - 1, f' - 1);
            case None =>
          }
    }
  }

  // ===========================================================================
  // The Progress-blind tree measure
  // ===========================================================================

  /** Tree size counting `Progress` nodes as zero — the measure under which
      check insertion is size-preserving (`BoolCheckInsert` only ever adds
      `Progress` nodes), so the downstream construction can recurse on a
      checked subtree where `TreeSize` would tie. */
  function PSize(t: LT.Tree): nat
    decreases t
  {
    match t
    case Mismatch => 1
    case Match => 1
    case Choice(t1, t2) => 1 + PSize(t1) + PSize(t2)
    case Read(_, t0) => 1 + PSize(t0)
    case ReadBackRef(_, t0) => 1 + PSize(t0)
    case Progress(t0) => PSize(t0)
    case AnchorPass(_, t0) => 1 + PSize(t0)
    case GroupActionT(_, t0) => 1 + PSize(t0)
    case LK(_, tlk, t0) => 1 + PSize(tlk) + PSize(t0)
    case LKFail(_, tlk) => 1 + PSize(tlk)
  }

  // ===========================================================================
  // Leaves agreement and its congruences
  // ===========================================================================

  /** `t1` and `t2` denote the same leaf sequences at every group map, input,
      and direction — the sense in which inserting a passing `Acheck` (whose
      `Progress` node is a `TreeLeaves` pass-through) changes nothing. */
  ghost predicate LeavesAgree(t1: LT.Tree, t2: LT.Tree) {
    forall gm: LG.GroupMap, inp: LC.Input, dir: WP.Direction ::
      LT.TreeLeaves(t1, gm, inp, dir) == LT.TreeLeaves(t2, gm, inp, dir)
  }

  lemma LAProgressPass(t: LT.Tree)
    ensures LeavesAgree(LT.Progress(t), t)
  {}

  lemma LACongProgress(a: LT.Tree, b: LT.Tree)
    requires LeavesAgree(a, b)
    ensures LeavesAgree(LT.Progress(a), LT.Progress(b))
  {}

  lemma LACongRead(c: char, a: LT.Tree, b: LT.Tree)
    requires LeavesAgree(a, b)
    ensures LeavesAgree(LT.Read(c, a), LT.Read(c, b))
  {}

  lemma LACongGroup(g: LG.GroupAction, a: LT.Tree, b: LT.Tree)
    requires LeavesAgree(a, b)
    ensures LeavesAgree(LT.GroupActionT(g, a), LT.GroupActionT(g, b))
  {}

  /** A gate is a congruence for leaf agreement when both sides carry the SAME
      body subtree: the verdict and the map handed to the continuation are read
      off that subtree, so they coincide. */
  lemma LACongLK(lk: L.Lookaround, tlk: LT.Tree, a: LT.Tree, b: LT.Tree)
    requires LeavesAgree(a, b)
    ensures LeavesAgree(LT.LK(lk, tlk, a), LT.LK(lk, tlk, b))
  {}

  lemma LACongAnchor(an: L.Anchor, a: LT.Tree, b: LT.Tree)
    requires LeavesAgree(a, b)
    ensures LeavesAgree(LT.AnchorPass(an, a), LT.AnchorPass(an, b))
  {}

  lemma LACongChoice(a1: LT.Tree, b1: LT.Tree, a2: LT.Tree, b2: LT.Tree)
    requires LeavesAgree(a1, b1) && LeavesAgree(a2, b2)
    ensures LeavesAgree(LT.Choice(a1, a2), LT.Choice(b1, b2))
  {}

  /** Leaves-agreeing trees have the same highest-priority result — the
      single hop `MainTheorem` takes from the checked tree the simulation ran
      on back to the spec tree. */
  lemma LAFirstLeaf(t1: LT.Tree, t2: LT.Tree, inp: LC.Input)
    requires LeavesAgree(t1, t2)
    ensures LT.FirstLeaf(t1, inp) == LT.FirstLeaf(t2, inp)
  {
    LT.FirstTreeLeaf(t1, LG.Empty, inp, WP.Forward);
    LT.FirstTreeLeaf(t2, LG.Empty, inp, WP.Forward);
  }

  // ===========================================================================
  // The insertion guard and its bookkeeping
  // ===========================================================================

  /** Some `Areg` element of `pre` is NonNullable: any walk that gets past it
      must have consumed at least one character. */
  ghost predicate ConsumesBeforeAreg(pre: LS.Actions) {
    exists i :: 0 <= i < |pre| && pre[i].Areg? && NN.NonNullableL(pre[i].r)
  }

  /** `a` is at or past `b`: equal, or a strict suffix in direction `dir`. */
  ghost predicate AtOrPast(a: LC.Input, b: LC.Input, dir: WP.Direction) {
    a == b || SS.IsStrictSuffix(a, b, dir)
  }

  /** Every `Acheck` recorded in `pre` records a position at or past `chk`,
      so passing any of them certifies progress past `chk` too. */
  ghost predicate ChecksAtOrPast(pre: LS.Actions, chk: LC.Input, dir: WP.Direction) {
    forall i :: 0 <= i < |pre| && pre[i].Acheck? ==> AtOrPast(pre[i].inp, chk, dir)
  }

  lemma ConsumesTailC(pre: LS.Actions)
    requires |pre| > 0 && ConsumesBeforeAreg(pre)
    requires !(pre[0].Areg? && NN.NonNullableL(pre[0].r))
    ensures ConsumesBeforeAreg(pre[1..])
  {
    var i :| 0 <= i < |pre| && pre[i].Areg? && NN.NonNullableL(pre[i].r);
    assert i > 0;
    assert pre[1..][i - 1] == pre[i];
  }

  lemma ConsumesPrepend(xs: LS.Actions, ys: LS.Actions)
    requires ConsumesBeforeAreg(ys)
    ensures ConsumesBeforeAreg(xs + ys)
  {
    var i :| 0 <= i < |ys| && ys[i].Areg? && NN.NonNullableL(ys[i].r);
    assert (xs + ys)[|xs| + i] == ys[i];
  }

  lemma AtOrPastTrans(a: LC.Input, b: LC.Input, c: LC.Input, dir: WP.Direction)
    requires AtOrPast(a, b, dir) && AtOrPast(b, c, dir)
    ensures AtOrPast(a, c, dir)
  {
    if a != b && b != c {
      SS.StrictSuffixTrans(a, b, c, dir);
    }
  }

  // ===========================================================================
  // The insertion lemma
  // ===========================================================================

  /** THE check-insertion lemma: inserting `Acheck(chk)` between `pre` and
      `rest` cannot change the outcome — the check always passes when reached,
      because either the walk has already moved strictly past `chk`
      (`IsStrictSuffix`), or a NonNullable element of `pre` still guarantees
      it will before the check is consumed. The checked tree computes with one
      extra fuel (the check is one extra step) and denotes the same leaves.
      Restricted to the pike subset (`pre` free of lookarounds and
      backreferences), which is all the engine pipeline ever builds. */
  lemma CheckInsert(rer: LW.RegExpRecord, pre: LS.Actions, chk: LC.Input, rest: LS.Actions,
                    inp: LC.Input, gm: LG.GroupMap, dir: WP.Direction, fuel: nat)
    requires PS.PikeActions(pre)
    requires AtOrPast(inp, chk, dir)
    requires ConsumesBeforeAreg(pre) || SS.IsStrictSuffix(inp, chk, dir)
    requires ChecksAtOrPast(pre, chk, dir)
    requires FS.ComputeTree(rer, pre + rest, inp, gm, dir, fuel).Some?
    ensures FS.ComputeTree(rer, pre + [LS.Acheck(chk)] + rest, inp, gm, dir, fuel + 1).Some?
    ensures LeavesAgree(FS.ComputeTree(rer, pre + [LS.Acheck(chk)] + rest, inp, gm, dir, fuel + 1).value,
                        FS.ComputeTree(rer, pre + rest, inp, gm, dir, fuel).value)
    decreases fuel
  {
    var stdList := pre + rest;
    var chkList := pre + [LS.Acheck(chk)] + rest;
    var std := FS.ComputeTree(rer, stdList, inp, gm, dir, fuel);
    if |pre| == 0 {
      // base: the check is the head; the guard forces it to pass
      assert !ConsumesBeforeAreg(pre);
      assert SS.IsStrictSuffix(inp, chk, dir);
      assert stdList == rest;
      assert chkList == [LS.Acheck(chk)] + rest;
      assert chkList[0] == LS.Acheck(chk) && chkList[1..] == rest;
      assert FS.ComputeTree(rer, chkList, inp, gm, dir, fuel + 1)
          == Some(LT.Progress(std.value));
      LAProgressPass(std.value);
    } else {
      assert stdList[0] == pre[0] && stdList[1..] == pre[1..] + rest;
      assert chkList[0] == pre[0] && chkList[1..] == pre[1..] + [LS.Acheck(chk)] + rest;
      assert PS.PikeAction(pre[0]);
      assert PS.PikeActions(pre[1..]) by {
        forall i | 0 <= i < |pre[1..]| ensures PS.PikeAction(pre[1..][i]) {
          assert pre[1..][i] == pre[i + 1];
        }
      }
      assert ChecksAtOrPast(pre[1..], chk, dir) by {
        forall i | 0 <= i < |pre[1..]| && pre[1..][i].Acheck?
          ensures AtOrPast(pre[1..][i].inp, chk, dir)
        {
          assert pre[1..][i] == pre[i + 1];
        }
      }
      var f := fuel - 1;
      match pre[0]
      case Acheck(c2) =>
        if SS.IsStrictSuffix(inp, c2, dir) {
          // passing a recorded check certifies progress past chk too
          assert AtOrPast(c2, chk, dir);
          assert SS.IsStrictSuffix(inp, chk, dir) by {
            if c2 != chk {
              assert SS.IsStrictSuffix(c2, chk, dir);
              SS.StrictSuffixTrans(inp, c2, chk, dir);
            }
          }
          CheckInsert(rer, pre[1..], chk, rest, inp, gm, dir, f);
          var sa := FS.ComputeTree(rer, pre[1..] + [LS.Acheck(chk)] + rest, inp, gm, dir, f + 1);
          var sb := FS.ComputeTree(rer, pre[1..] + rest, inp, gm, dir, f);
          LACongProgress(sa.value, sb.value);
        }
        // failing kills both sides identically (Mismatch)
      case Aclose(gid) =>
        if ConsumesBeforeAreg(pre) { ConsumesTailC(pre); }
        CheckInsert(rer, pre[1..], chk, rest, inp, LG.GMClose(LC.Idx(inp), gid, gm), dir, f);
        var sa := FS.ComputeTree(rer, pre[1..] + [LS.Acheck(chk)] + rest, inp, LG.GMClose(LC.Idx(inp), gid, gm), dir, f + 1);
        var sb := FS.ComputeTree(rer, pre[1..] + rest, inp, LG.GMClose(LC.Idx(inp), gid, gm), dir, f);
        LACongGroup(LG.Close(gid), sa.value, sb.value);
      case Areg(r) =>
        assert PS.PikeRegex(r);
        match r
        case Epsilon =>
          if ConsumesBeforeAreg(pre) { ConsumesTailC(pre); }
          CheckInsert(rer, pre[1..], chk, rest, inp, gm, dir, f);
        case Character(cd) =>
          match LC.ReadChar(rer, cd, inp, dir) {
            case Some(pair) =>
              // reading strictly advances: the guard flips to the suffix disjunct
              SS.ReadCharSuffix(inp, dir, pair.1, cd, pair.0, rer);
              assert SS.StrictSuffix(pair.1, inp, dir);
              assert SS.IsStrictSuffix(pair.1, chk, dir) by {
                if inp != chk { SS.StrictSuffixTrans(pair.1, inp, chk, dir); }
              }
              CheckInsert(rer, pre[1..], chk, rest, pair.1, gm, dir, f);
              var sa := FS.ComputeTree(rer, pre[1..] + [LS.Acheck(chk)] + rest, pair.1, gm, dir, f + 1);
              var sb := FS.ComputeTree(rer, pre[1..] + rest, pair.1, gm, dir, f);
              LACongRead(pair.0, sa.value, sb.value);
            case None =>
              // both Mismatch
          }
        case Disjunction(r1, r2) =>
          var pa := [LS.Areg(r1)] + pre[1..];
          var pb := [LS.Areg(r2)] + pre[1..];
          assert pa + rest == [LS.Areg(r1)] + (pre[1..] + rest);
          assert pb + rest == [LS.Areg(r2)] + (pre[1..] + rest);
          assert pa + [LS.Acheck(chk)] + rest == [LS.Areg(r1)] + (pre[1..] + [LS.Acheck(chk)] + rest);
          assert pb + [LS.Acheck(chk)] + rest == [LS.Areg(r2)] + (pre[1..] + [LS.Acheck(chk)] + rest);
          assert PS.PikeActions(pa) by {
            forall i | 0 <= i < |pa| ensures PS.PikeAction(pa[i]) { if i > 0 { assert pa[i] == pre[i]; } }
          }
          assert PS.PikeActions(pb) by {
            forall i | 0 <= i < |pb| ensures PS.PikeAction(pb[i]) { if i > 0 { assert pb[i] == pre[i]; } }
          }
          assert ChecksAtOrPast(pa, chk, dir) by {
            forall i | 0 <= i < |pa| && pa[i].Acheck? ensures AtOrPast(pa[i].inp, chk, dir) { assert i > 0; assert pa[i] == pre[i]; }
          }
          assert ChecksAtOrPast(pb, chk, dir) by {
            forall i | 0 <= i < |pb| && pb[i].Acheck? ensures AtOrPast(pb[i].inp, chk, dir) { assert i > 0; assert pb[i] == pre[i]; }
          }
          if ConsumesBeforeAreg(pre) {
            if pre[0].Areg? && NN.NonNullableL(pre[0].r) {
              // both branches inherit a NonNullable head
              assert ConsumesBeforeAreg(pa) by { assert pa[0] == LS.Areg(r1); }
              assert ConsumesBeforeAreg(pb) by { assert pb[0] == LS.Areg(r2); }
            } else {
              ConsumesTailC(pre);
              ConsumesPrepend([LS.Areg(r1)], pre[1..]);
              ConsumesPrepend([LS.Areg(r2)], pre[1..]);
            }
          }
          CheckInsert(rer, pa, chk, rest, inp, gm, dir, f);
          CheckInsert(rer, pb, chk, rest, inp, gm, dir, f);
          var sa1 := FS.ComputeTree(rer, pa + [LS.Acheck(chk)] + rest, inp, gm, dir, f + 1);
          var sb1 := FS.ComputeTree(rer, pa + rest, inp, gm, dir, f);
          var sa2 := FS.ComputeTree(rer, pb + [LS.Acheck(chk)] + rest, inp, gm, dir, f + 1);
          var sb2 := FS.ComputeTree(rer, pb + rest, inp, gm, dir, f);
          LACongChoice(sa1.value, sb1.value, sa2.value, sb2.value);
        case Sequence(r1, r2) =>
          var sl := LS.SeqList(r1, r2, dir);
          var pn := sl + pre[1..];
          assert pn + rest == sl + (pre[1..] + rest);
          assert pn + [LS.Acheck(chk)] + rest == sl + (pre[1..] + [LS.Acheck(chk)] + rest);
          assert PS.PikeActions(pn) by {
            forall i | 0 <= i < |pn| ensures PS.PikeAction(pn[i]) {
              if i >= |sl| { assert pn[i] == pre[i - |sl| + 1]; }
            }
          }
          assert ChecksAtOrPast(pn, chk, dir) by {
            forall i | 0 <= i < |pn| && pn[i].Acheck? ensures AtOrPast(pn[i].inp, chk, dir) {
              assert i >= |sl|; assert pn[i] == pre[i - |sl| + 1];
            }
          }
          if ConsumesBeforeAreg(pre) {
            if pre[0].Areg? && NN.NonNullableL(pre[0].r) {
              // one of the two parts is NonNullable; both are in sl
              if NN.NonNullableL(r1) {
                assert ConsumesBeforeAreg(pn) by {
                  var k := if dir == WP.Forward then 0 else 1;
                  assert pn[k] == LS.Areg(r1);
                }
              } else {
                assert ConsumesBeforeAreg(pn) by {
                  var k := if dir == WP.Forward then 1 else 0;
                  assert pn[k] == LS.Areg(r2);
                }
              }
            } else {
              ConsumesTailC(pre);
              ConsumesPrepend(sl, pre[1..]);
            }
          }
          CheckInsert(rer, pn, chk, rest, inp, gm, dir, f);
        case Quantified(greedy, min, delta, r1) =>
          var gidl := L.DefGroups(r1);
          if min > 0 {
            var q1 := L.Quantified(greedy, min - 1, delta, r1);
            var pn := [LS.Areg(r1), LS.Areg(q1)] + pre[1..];
            assert pn + rest == [LS.Areg(r1), LS.Areg(q1)] + (pre[1..] + rest);
            assert pn + [LS.Acheck(chk)] + rest == [LS.Areg(r1), LS.Areg(q1)] + (pre[1..] + [LS.Acheck(chk)] + rest);
            assert PS.PikeActions(pn) by {
              forall i | 0 <= i < |pn| ensures PS.PikeAction(pn[i]) {
                if i >= 2 { assert pn[i] == pre[i - 1]; }
              }
            }
            assert ChecksAtOrPast(pn, chk, dir) by {
              forall i | 0 <= i < |pn| && pn[i].Acheck? ensures AtOrPast(pn[i].inp, chk, dir) {
                assert i >= 2; assert pn[i] == pre[i - 1];
              }
            }
            if ConsumesBeforeAreg(pre) {
              if pre[0].Areg? && NN.NonNullableL(pre[0].r) {
                assert ConsumesBeforeAreg(pn) by { assert pn[0] == LS.Areg(r1); }
              } else {
                ConsumesTailC(pre);
                ConsumesPrepend([LS.Areg(r1), LS.Areg(q1)], pre[1..]);
              }
            }
            CheckInsert(rer, pn, chk, rest, inp, LG.GMReset(gidl, gm), dir, f);
            var sa := FS.ComputeTree(rer, pn + [LS.Acheck(chk)] + rest, inp, LG.GMReset(gidl, gm), dir, f + 1);
            var sb := FS.ComputeTree(rer, pn + rest, inp, LG.GMReset(gidl, gm), dir, f);
            LACongGroup(LG.Reset(gidl), sa.value, sb.value);
          } else if delta == LN.NN(0) {
            if ConsumesBeforeAreg(pre) { ConsumesTailC(pre); }
            CheckInsert(rer, pre[1..], chk, rest, inp, gm, dir, f);
          } else {
            var q0 := L.Quantified(greedy, 0, FS.NoiPred(delta), r1);
            var pi := [LS.Areg(r1), LS.Acheck(inp), LS.Areg(q0)] + pre[1..];
            assert pi + rest == [LS.Areg(r1), LS.Acheck(inp), LS.Areg(q0)] + (pre[1..] + rest);
            assert pi + [LS.Acheck(chk)] + rest == [LS.Areg(r1), LS.Acheck(inp), LS.Areg(q0)] + (pre[1..] + [LS.Acheck(chk)] + rest);
            assert PS.PikeActions(pi) by {
              forall i | 0 <= i < |pi| ensures PS.PikeAction(pi[i]) {
                if i >= 3 { assert pi[i] == pre[i - 2]; }
              }
            }
            assert ChecksAtOrPast(pi, chk, dir) by {
              forall i | 0 <= i < |pi| && pi[i].Acheck? ensures AtOrPast(pi[i].inp, chk, dir) {
                if i >= 3 { assert pi[i] == pre[i - 2]; } else { assert i == 1; assert pi[1].inp == inp; }
              }
            }
            if ConsumesBeforeAreg(pre) {
              // min == 0: pre[0] cannot be the witness
              ConsumesTailC(pre);
              ConsumesPrepend([LS.Areg(r1), LS.Acheck(inp), LS.Areg(q0)], pre[1..]);
            }
            CheckInsert(rer, pi, chk, rest, inp, LG.GMReset(gidl, gm), dir, f);
            CheckInsert(rer, pre[1..], chk, rest, inp, gm, dir, f);
            var ia := FS.ComputeTree(rer, pi + [LS.Acheck(chk)] + rest, inp, LG.GMReset(gidl, gm), dir, f + 1);
            var ib := FS.ComputeTree(rer, pi + rest, inp, LG.GMReset(gidl, gm), dir, f);
            var ka := FS.ComputeTree(rer, pre[1..] + [LS.Acheck(chk)] + rest, inp, gm, dir, f + 1);
            var kb := FS.ComputeTree(rer, pre[1..] + rest, inp, gm, dir, f);
            LACongGroup(LG.Reset(gidl), ia.value, ib.value);
            if greedy {
              LACongChoice(LT.GroupActionT(LG.Reset(gidl), ia.value), LT.GroupActionT(LG.Reset(gidl), ib.value), ka.value, kb.value);
            } else {
              LACongChoice(ka.value, kb.value, LT.GroupActionT(LG.Reset(gidl), ia.value), LT.GroupActionT(LG.Reset(gidl), ib.value));
            }
          }
        case Group(gid, r1) =>
          var pn := [LS.Areg(r1), LS.Aclose(gid)] + pre[1..];
          assert pn + rest == [LS.Areg(r1), LS.Aclose(gid)] + (pre[1..] + rest);
          assert pn + [LS.Acheck(chk)] + rest == [LS.Areg(r1), LS.Aclose(gid)] + (pre[1..] + [LS.Acheck(chk)] + rest);
          assert PS.PikeActions(pn) by {
            forall i | 0 <= i < |pn| ensures PS.PikeAction(pn[i]) {
              if i >= 2 { assert pn[i] == pre[i - 1]; }
            }
          }
          assert ChecksAtOrPast(pn, chk, dir) by {
            forall i | 0 <= i < |pn| && pn[i].Acheck? ensures AtOrPast(pn[i].inp, chk, dir) {
              assert i >= 2; assert pn[i] == pre[i - 1];
            }
          }
          if ConsumesBeforeAreg(pre) {
            if pre[0].Areg? && NN.NonNullableL(pre[0].r) {
              assert ConsumesBeforeAreg(pn) by { assert pn[0] == LS.Areg(r1); }
            } else {
              ConsumesTailC(pre);
              ConsumesPrepend([LS.Areg(r1), LS.Aclose(gid)], pre[1..]);
            }
          }
          CheckInsert(rer, pn, chk, rest, inp, LG.GMOpen(LC.Idx(inp), gid, gm), dir, f);
          var sa := FS.ComputeTree(rer, pn + [LS.Acheck(chk)] + rest, inp, LG.GMOpen(LC.Idx(inp), gid, gm), dir, f + 1);
          var sb := FS.ComputeTree(rer, pn + rest, inp, LG.GMOpen(LC.Idx(inp), gid, gm), dir, f);
          LACongGroup(LG.Open(gid), sa.value, sb.value);
        case AnchorR(a) =>
          if LS.AnchorSatisfied(rer, a, inp) {
            if ConsumesBeforeAreg(pre) { ConsumesTailC(pre); }
            CheckInsert(rer, pre[1..], chk, rest, inp, gm, dir, f);
            var sa := FS.ComputeTree(rer, pre[1..] + [LS.Acheck(chk)] + rest, inp, gm, dir, f + 1);
            var sb := FS.ComputeTree(rer, pre[1..] + rest, inp, gm, dir, f);
            LACongAnchor(a, sa.value, sb.value);
          }
          // else both Mismatch
        case LookaroundR(_, _) =>
          assert false;   // not pike
        case Backreference(_) =>
          assert false;   // not pike
    }
  }

  // ===========================================================================
  // The insertion lemma, boolean layer
  // ===========================================================================

  /** Some `Acheck` element sits in `pre` (once passed, the flag is `CanExit`
      onward; if failed, both trees die identically). */
  ghost predicate AcheckIn(pre: LS.Actions) {
    exists i :: 0 <= i < |pre| && pre[i].Acheck?
  }

  lemma AcheckInTail(pre: LS.Actions)
    requires |pre| > 0 && AcheckIn(pre) && !pre[0].Acheck?
    ensures AcheckIn(pre[1..])
  {
    var i :| 0 <= i < |pre| && pre[i].Acheck?;
    assert i > 0;
    assert pre[1..][i - 1] == pre[i];
  }

  lemma AcheckInPrepend(xs: LS.Actions, ys: LS.Actions)
    requires AcheckIn(ys)
    ensures AcheckIn(xs + ys)
  {
    var i :| 0 <= i < |ys| && ys[i].Acheck?;
    assert (xs + ys)[|xs| + i] == ys[i];
  }

  /** THE boolean-layer check-insertion lemma: `BoolTree`'s `Acheck` rule
      consults only the flag, never the recorded input, so the insertion is
      justified by the flag alone — it is `CanExit` when the check is reached,
      because a NonNullable element of `pre` (or an earlier check) forces a
      read first, or the flag was already set. The inserted node is a
      `Progress` pass-through: leaves agree. */
  lemma BoolCheckInsert(rer: LW.RegExpRecord, pre: LS.Actions, chk: LC.Input, rest: LS.Actions,
                       inp: LC.Input, b: BS.LoopBool, t: LT.Tree) returns (tstar: LT.Tree)
    requires EL.PikeLkActions(pre)
    requires ConsumesBeforeAreg(pre) || AcheckIn(pre) || b == BS.CanExit
    requires EL.BoolTreeLk(rer, pre + rest, inp, b, t)
    ensures EL.BoolTreeLk(rer, pre + [LS.Acheck(chk)] + rest, inp, b, tstar)
    ensures LeavesAgree(tstar, t)
    ensures PSize(tstar) == PSize(t)
    decreases LS.TreeSize(t), LS.ActionsRegexSize(pre)
  {
    if |pre| == 0 {
      assert !ConsumesBeforeAreg(pre) && !AcheckIn(pre);
      assert b == BS.CanExit;
      assert pre + rest == rest;
      assert pre + [LS.Acheck(chk)] + rest == [LS.Acheck(chk)] + rest;
      assert ([LS.Acheck(chk)] + rest)[0] == LS.Acheck(chk)
          && ([LS.Acheck(chk)] + rest)[1..] == rest;
      tstar := LT.Progress(t);
      LAProgressPass(t);
    } else {
      assert (pre + rest)[0] == pre[0] && (pre + rest)[1..] == pre[1..] + rest;
      assert (pre + [LS.Acheck(chk)] + rest)[0] == pre[0]
          && (pre + [LS.Acheck(chk)] + rest)[1..] == pre[1..] + [LS.Acheck(chk)] + rest;
      assert EL.PikeLkAction(pre[0]);
      assert EL.PikeLkActions(pre[1..]) by {
        forall i | 0 <= i < |pre[1..]| ensures EL.PikeLkAction(pre[1..][i]) {
          assert pre[1..][i] == pre[i + 1];
        }
      }
      match pre[0]
      case Acheck(c2) =>
        if b == BS.CanExit {
          match t {
            case Progress(tc) =>
              var sub := BoolCheckInsert(rer, pre[1..], chk, rest, inp, BS.CanExit, tc);
              tstar := LT.Progress(sub);
              LACongProgress(sub, tc);
            case _ =>
          }
        } else {
          // check fails on both sides identically
          tstar := LT.Mismatch;
        }
      case Aclose(gid) =>
        match t {
          case GroupActionT(g, tc) =>
            if ConsumesBeforeAreg(pre) { ConsumesTailC(pre); }
            if AcheckIn(pre) && !(ConsumesBeforeAreg(pre[1..]) || b == BS.CanExit) { AcheckInTail(pre); }
            var sub := BoolCheckInsert(rer, pre[1..], chk, rest, inp, b, tc);
            tstar := LT.GroupActionT(g, sub);
            LACongGroup(g, sub, tc);
          case _ =>
        }
      case Areg(r) =>
        assert EL.PikeLkRegex(r);
        match r
        case Epsilon =>
          if ConsumesBeforeAreg(pre) { ConsumesTailC(pre); }
          if AcheckIn(pre) && !(ConsumesBeforeAreg(pre[1..]) || b == BS.CanExit) { AcheckInTail(pre); }
          tstar := BoolCheckInsert(rer, pre[1..], chk, rest, inp, b, t);
        case Character(cd) =>
          match LC.ReadChar(rer, cd, inp, WP.Forward) {
            case Some(pair) =>
              match t {
                case Read(c, tc) =>
                  var sub := BoolCheckInsert(rer, pre[1..], chk, rest, pair.1, BS.CanExit, tc);
                  tstar := LT.Read(c, sub);
                  LACongRead(c, sub, tc);
                case _ =>
              }
            case None =>
              tstar := LT.Mismatch;
          }
        case Disjunction(r1, r2) =>
          match t {
            case Choice(ta, tb) =>
              var pa := [LS.Areg(r1)] + pre[1..];
              var pb := [LS.Areg(r2)] + pre[1..];
              assert pa + rest == [LS.Areg(r1)] + (pre[1..] + rest);
              assert pb + rest == [LS.Areg(r2)] + (pre[1..] + rest);
              assert pa + [LS.Acheck(chk)] + rest == [LS.Areg(r1)] + (pre[1..] + [LS.Acheck(chk)] + rest);
              assert pb + [LS.Acheck(chk)] + rest == [LS.Areg(r2)] + (pre[1..] + [LS.Acheck(chk)] + rest);
              assert EL.PikeLkActions(pa) by {
                forall i | 0 <= i < |pa| ensures EL.PikeLkAction(pa[i]) { if i > 0 { assert pa[i] == pre[i]; } }
              }
              assert EL.PikeLkActions(pb) by {
                forall i | 0 <= i < |pb| ensures EL.PikeLkAction(pb[i]) { if i > 0 { assert pb[i] == pre[i]; } }
              }
              if ConsumesBeforeAreg(pre) && !(pre[0].Areg? && NN.NonNullableL(pre[0].r)) {
                ConsumesTailC(pre);
                ConsumesPrepend([LS.Areg(r1)], pre[1..]);
                ConsumesPrepend([LS.Areg(r2)], pre[1..]);
              }
              if ConsumesBeforeAreg(pre) && pre[0].Areg? && NN.NonNullableL(pre[0].r) {
                assert ConsumesBeforeAreg(pa) by { assert pa[0] == LS.Areg(r1); }
                assert ConsumesBeforeAreg(pb) by { assert pb[0] == LS.Areg(r2); }
              }
              if AcheckIn(pre) && !(ConsumesBeforeAreg(pre) || b == BS.CanExit) {
                AcheckInTail(pre);
                AcheckInPrepend([LS.Areg(r1)], pre[1..]);
                AcheckInPrepend([LS.Areg(r2)], pre[1..]);
              }
              var sa := BoolCheckInsert(rer, pa, chk, rest, inp, b, ta);
              var sb := BoolCheckInsert(rer, pb, chk, rest, inp, b, tb);
              tstar := LT.Choice(sa, sb);
              LACongChoice(sa, ta, sb, tb);
            case _ =>
          }
        case Sequence(r1, r2) =>
          var pn := [LS.Areg(r1), LS.Areg(r2)] + pre[1..];
          assert pn + rest == [LS.Areg(r1), LS.Areg(r2)] + (pre[1..] + rest);
          assert pn + [LS.Acheck(chk)] + rest == [LS.Areg(r1), LS.Areg(r2)] + (pre[1..] + [LS.Acheck(chk)] + rest);
          assert EL.PikeLkActions(pn) by {
            forall i | 0 <= i < |pn| ensures EL.PikeLkAction(pn[i]) {
              if i >= 2 { assert pn[i] == pre[i - 1]; }
            }
          }
          if ConsumesBeforeAreg(pre) && !(pre[0].Areg? && NN.NonNullableL(pre[0].r)) {
            ConsumesTailC(pre);
            ConsumesPrepend([LS.Areg(r1), LS.Areg(r2)], pre[1..]);
          }
          if ConsumesBeforeAreg(pre) && pre[0].Areg? && NN.NonNullableL(pre[0].r) {
            if NN.NonNullableL(r1) {
              assert ConsumesBeforeAreg(pn) by { assert pn[0] == LS.Areg(r1); }
            } else {
              assert ConsumesBeforeAreg(pn) by { assert pn[1] == LS.Areg(r2); }
            }
          }
          if AcheckIn(pre) && !(ConsumesBeforeAreg(pre) || b == BS.CanExit) {
            AcheckInTail(pre);
            AcheckInPrepend([LS.Areg(r1), LS.Areg(r2)], pre[1..]);
          }
          assert pre == [pre[0]] + pre[1..];
          assert LS.ActionsRegexSize(pn) < LS.ActionsRegexSize(pre);
          tstar := BoolCheckInsert(rer, pn, chk, rest, inp, b, t);
        case Quantified(greedy, min, delta, r1) =>
          var gidl := L.DefGroups(r1);
          if min > 0 {
            match t {
              case GroupActionT(g, tc) =>
                var q1 := L.Quantified(greedy, min - 1, delta, r1);
                var pn := [LS.Areg(r1), LS.Areg(q1)] + pre[1..];
                assert pn + rest == [LS.Areg(r1), LS.Areg(q1)] + (pre[1..] + rest);
                assert pn + [LS.Acheck(chk)] + rest == [LS.Areg(r1), LS.Areg(q1)] + (pre[1..] + [LS.Acheck(chk)] + rest);
                assert EL.PikeLkActions(pn) by {
                  forall i | 0 <= i < |pn| ensures EL.PikeLkAction(pn[i]) {
                    if i >= 2 { assert pn[i] == pre[i - 1]; }
                  }
                }
                if ConsumesBeforeAreg(pre) && !(pre[0].Areg? && NN.NonNullableL(pre[0].r)) {
                  ConsumesTailC(pre);
                  ConsumesPrepend([LS.Areg(r1), LS.Areg(q1)], pre[1..]);
                }
                if ConsumesBeforeAreg(pre) && pre[0].Areg? && NN.NonNullableL(pre[0].r) {
                  assert ConsumesBeforeAreg(pn) by { assert pn[0] == LS.Areg(r1); }
                }
                if AcheckIn(pre) && !(ConsumesBeforeAreg(pre) || b == BS.CanExit) {
                  AcheckInTail(pre);
                  AcheckInPrepend([LS.Areg(r1), LS.Areg(q1)], pre[1..]);
                }
                var sub := BoolCheckInsert(rer, pn, chk, rest, inp, b, tc);
                tstar := LT.GroupActionT(g, sub);
                LACongGroup(g, sub, tc);
              case _ =>
            }
          } else if delta == LN.NN(0) {
            if ConsumesBeforeAreg(pre) { ConsumesTailC(pre); }
            if AcheckIn(pre) && !(ConsumesBeforeAreg(pre[1..]) || b == BS.CanExit) { AcheckInTail(pre); }
            tstar := BoolCheckInsert(rer, pre[1..], chk, rest, inp, b, t);
          } else {
            match t {
              case Choice(ta, tb) =>
                var itert := if greedy then ta else tb;
                var skipt := if greedy then tb else ta;
                match itert {
                  case GroupActionT(g, ti) =>
                    var q0 := L.Quantified(greedy, 0, FS.NoiPred(delta), r1);
                    var pi := [LS.Areg(r1), LS.Acheck(inp), LS.Areg(q0)] + pre[1..];
                    assert pi + rest == [LS.Areg(r1), LS.Acheck(inp), LS.Areg(q0)] + (pre[1..] + rest);
                    assert pi + [LS.Acheck(chk)] + rest == [LS.Areg(r1), LS.Acheck(inp), LS.Areg(q0)] + (pre[1..] + [LS.Acheck(chk)] + rest);
                    assert EL.PikeLkActions(pi) by {
                      forall i | 0 <= i < |pi| ensures EL.PikeLkAction(pi[i]) {
                        if i >= 3 { assert pi[i] == pre[i - 2]; }
                      }
                    }
                    assert AcheckIn(pi) by { assert pi[1].Acheck?; }
                    assert LS.TreeSize(ti) < LS.TreeSize(t);
                    var si := BoolCheckInsert(rer, pi, chk, rest, inp, BS.CannotExit, ti);
                    // skip branch
                    if ConsumesBeforeAreg(pre) { ConsumesTailC(pre); }
                    if AcheckIn(pre) && !(ConsumesBeforeAreg(pre[1..]) || b == BS.CanExit) { AcheckInTail(pre); }
                    assert LS.TreeSize(skipt) < LS.TreeSize(t);
                    var ss := BoolCheckInsert(rer, pre[1..], chk, rest, inp, b, skipt);
                    var istar := LT.GroupActionT(g, si);
                    LACongGroup(g, si, ti);
                    if greedy {
                      tstar := LT.Choice(istar, ss);
                      LACongChoice(istar, itert, ss, skipt);
                    } else {
                      tstar := LT.Choice(ss, istar);
                      LACongChoice(ss, skipt, istar, itert);
                    }
                  case _ =>
                }
              case _ =>
            }
          }
        case Group(gid, r1) =>
          match t {
            case GroupActionT(g, tc) =>
              var pn := [LS.Areg(r1), LS.Aclose(gid)] + pre[1..];
              assert pn + rest == [LS.Areg(r1), LS.Aclose(gid)] + (pre[1..] + rest);
              assert pn + [LS.Acheck(chk)] + rest == [LS.Areg(r1), LS.Aclose(gid)] + (pre[1..] + [LS.Acheck(chk)] + rest);
              assert EL.PikeLkActions(pn) by {
                forall i | 0 <= i < |pn| ensures EL.PikeLkAction(pn[i]) {
                  if i >= 2 { assert pn[i] == pre[i - 1]; }
                }
              }
              if ConsumesBeforeAreg(pre) && !(pre[0].Areg? && NN.NonNullableL(pre[0].r)) {
                ConsumesTailC(pre);
                ConsumesPrepend([LS.Areg(r1), LS.Aclose(gid)], pre[1..]);
              }
              if ConsumesBeforeAreg(pre) && pre[0].Areg? && NN.NonNullableL(pre[0].r) {
                assert ConsumesBeforeAreg(pn) by { assert pn[0] == LS.Areg(r1); }
              }
              if AcheckIn(pre) && !(ConsumesBeforeAreg(pre) || b == BS.CanExit) {
                AcheckInTail(pre);
                AcheckInPrepend([LS.Areg(r1), LS.Aclose(gid)], pre[1..]);
              }
              var sub := BoolCheckInsert(rer, pn, chk, rest, inp, b, tc);
              tstar := LT.GroupActionT(g, sub);
              LACongGroup(g, sub, tc);
            case _ =>
          }
        case AnchorR(a) =>
          if LS.AnchorSatisfied(rer, a, inp) {
            match t {
              case AnchorPass(a2, tc) =>
                if ConsumesBeforeAreg(pre) { ConsumesTailC(pre); }
                if AcheckIn(pre) && !(ConsumesBeforeAreg(pre[1..]) || b == BS.CanExit) { AcheckInTail(pre); }
                var sub := BoolCheckInsert(rer, pre[1..], chk, rest, inp, b, tc);
                tstar := LT.AnchorPass(a2, sub);
                LACongAnchor(a2, sub, tc);
              case _ =>
            }
          } else {
            tstar := LT.Mismatch;
          }
        case LookaroundR(lk, r1) =>
          // the gate is zero-width: rebuild it around the continuation's
          // inserted-check tree. Both sides carry the SAME body subtree, so
          // LACongLK gives the leaf agreement.
          match t {
            case LK(lk2, tlk, tc) =>
              if ConsumesBeforeAreg(pre) { ConsumesTailC(pre); }
              if AcheckIn(pre) && !(ConsumesBeforeAreg(pre[1..]) || b == BS.CanExit) { AcheckInTail(pre); }
              var sub := BoolCheckInsert(rer, pre[1..], chk, rest, inp, b, tc);
              tstar := LT.LK(lk2, tlk, sub);
              LACongLK(lk2, tlk, sub, tc);
            case LKFail(lk2, tlk) =>
              tstar := t;
            case _ =>
          }
        case Backreference(_) =>
          assert false;   // not pike
    }
  }

  // ===========================================================================
  // The flag lift, boolean layer
  // ===========================================================================

  /** Every `Acheck` in `acts` is preceded by some NonNullable `Areg`: any walk
      that surfaces a check must have consumed a character first, so the two
      loop-flag values are indistinguishable along the whole list (the flags
      converge at the first read, before any check can be consulted). */
  ghost predicate ShieldedActs(acts: LS.Actions) {
    forall i :: 0 <= i < |acts| && acts[i].Acheck? ==>
      exists j :: 0 <= j < i && acts[j].Areg? && NN.NonNullableL(acts[j].r)
  }

  /** Peeling a head that is not itself a NonNullable `Areg` keeps every
      remaining `Acheck` shielded. */
  lemma ShieldedTail(acts: LS.Actions)
    requires |acts| > 0 && ShieldedActs(acts)
    requires !(acts[0].Areg? && NN.NonNullableL(acts[0].r))
    ensures ShieldedActs(acts[1..])
  {
    var tail := acts[1..];
    forall i | 0 <= i < |tail| && tail[i].Acheck?
      ensures exists j :: 0 <= j < i && tail[j].Areg? && NN.NonNullableL(tail[j].r)
    {
      assert tail[i] == acts[i + 1];
      var j :| 0 <= j < i + 1 && acts[j].Areg? && NN.NonNullableL(acts[j].r);
      assert j > 0;
      assert tail[j - 1] == acts[j];
    }
  }

  /** Replacing the head by check-free `parts` keeps the list shielded, as
      long as a NonNullable head is replaced by parts containing a NonNullable
      element (the null_and/null_or tables guarantee one exists for every
      expansion the walk performs). */
  lemma ShieldedCons(parts: LS.Actions, acts: LS.Actions)
    requires |acts| > 0 && ShieldedActs(acts)
    requires forall p :: 0 <= p < |parts| ==> !parts[p].Acheck?
    requires (acts[0].Areg? && NN.NonNullableL(acts[0].r)) ==>
               exists p :: 0 <= p < |parts| && parts[p].Areg? && NN.NonNullableL(parts[p].r)
    ensures ShieldedActs(parts + acts[1..])
  {
    var xs := parts + acts[1..];
    forall i | 0 <= i < |xs| && xs[i].Acheck?
      ensures exists j :: 0 <= j < i && xs[j].Areg? && NN.NonNullableL(xs[j].r)
    {
      assert i >= |parts|;
      assert xs[i] == acts[1..][i - |parts|];
      assert acts[1..][i - |parts|] == acts[i - |parts| + 1];
      var j :| 0 <= j < i - |parts| + 1 && acts[j].Areg? && NN.NonNullableL(acts[j].r);
      if j == 0 {
        var p :| 0 <= p < |parts| && parts[p].Areg? && NN.NonNullableL(parts[p].r);
        assert xs[p] == parts[p];
        assert p < i;
      } else {
        assert xs[|parts| + j - 1] == acts[1..][j - 1] == acts[j];
        assert |parts| + j - 1 < i;
      }
    }
  }

  /** THE flag-lift lemma: for a shielded action list, the `CannotExit`
      derivation is also a `CanExit` derivation of the SAME tree. The two
      walks can only differ at an `Acheck` consultation, and a shielded list
      cannot surface one before a read: the shield's NonNullable element must
      be traversed first, its completion forces a `Read`, and both flags are
      `CanExit` from that point on (the post-read sub-derivations are shared
      verbatim, so the induction stops at every `Character`). Free-iteration
      subtrees are pushed at `CannotExit` by BOTH derivations and are likewise
      shared without recursion. */
  lemma BoolFlagLift(rer: LW.RegExpRecord, acts: LS.Actions, inp: LC.Input, t: LT.Tree)
    requires EL.PikeLkActions(acts)
    requires ShieldedActs(acts)
    requires EL.BoolTreeLk(rer, acts, inp, BS.CannotExit, t)
    ensures EL.BoolTreeLk(rer, acts, inp, BS.CanExit, t)
    decreases LS.TreeSize(t), LS.ActionsRegexSize(acts)
  {
    if |acts| == 0 { return; }
    var cont := acts[1..];
    EL.PikeLkActionsTail(acts);
    assert acts == [acts[0]] + cont;
    match acts[0]
    case Acheck(strcheck) =>
      // a shielded list cannot have an Acheck at its head
      var j :| 0 <= j < 0 && acts[j].Areg? && NN.NonNullableL(acts[j].r);
    case Aclose(gid) =>
      match t {
        case GroupActionT(g, tc) =>
          ShieldedTail(acts);
          BoolFlagLift(rer, cont, inp, tc);
        case _ =>
      }
    case Areg(r) =>
      assert EL.PikeLkRegex(r);
      match r
      case Epsilon =>
        ShieldedTail(acts);
        assert LS.ActionsRegexSize(cont) < LS.ActionsRegexSize(acts);
        BoolFlagLift(rer, cont, inp, t);
      case Character(cd) =>
        // the flags converge at the read: the sub-derivation is shared
        match LC.ReadChar(rer, cd, inp, WP.Forward) {
          case None =>
          case Some(pair) =>
        }
      case Disjunction(r1, r2) =>
        match t {
          case Choice(ta, tb) =>
            var la := [LS.Areg(r1)] + cont;
            var lb := [LS.Areg(r2)] + cont;
            EL.PikeLkActionsConsIff(LS.Areg(r1), cont);
            EL.PikeLkActionsConsIff(LS.Areg(r2), cont);
            assert NN.NonNullableL(r) ==> NN.NonNullableL(r1) && NN.NonNullableL(r2);
            ShieldedCons([LS.Areg(r1)], acts);
            ShieldedCons([LS.Areg(r2)], acts);
            BoolFlagLift(rer, la, inp, ta);
            BoolFlagLift(rer, lb, inp, tb);
          case _ =>
        }
      case Sequence(r1, r2) =>
        var ln := [LS.Areg(r1), LS.Areg(r2)] + cont;
        EL.PikeLkActionsConsIff(LS.Areg(r2), cont);
        EL.PikeLkActionsConsIff(LS.Areg(r1), [LS.Areg(r2)] + cont);
        assert ln == [LS.Areg(r1)] + ([LS.Areg(r2)] + cont);
        var sparts := [LS.Areg(r1), LS.Areg(r2)];
        if NN.NonNullableL(r) {
          if NN.NonNullableL(r1) {
            assert sparts[0].Areg? && NN.NonNullableL(sparts[0].r);
          } else {
            assert NN.NonNullableL(r2);
            assert sparts[1].Areg? && NN.NonNullableL(sparts[1].r);
          }
        }
        ShieldedCons(sparts, acts);
        assert LS.ActionsRegexSize(ln) < LS.ActionsRegexSize(acts);
        BoolFlagLift(rer, ln, inp, t);
      case Quantified(greedy, min, delta, r1) =>
        var gidl := L.DefGroups(r1);
        if min > 0 {
          match t {
            case GroupActionT(g, tc) =>
              var q1 := L.Quantified(greedy, min - 1, delta, r1);
              var ln := [LS.Areg(r1), LS.Areg(q1)] + cont;
              EL.PikeLkActionsConsIff(LS.Areg(q1), cont);
              EL.PikeLkActionsConsIff(LS.Areg(r1), [LS.Areg(q1)] + cont);
              assert ln == [LS.Areg(r1)] + ([LS.Areg(q1)] + cont);
              assert NN.NonNullableL(r) ==> NN.NonNullableL(r1);
              ShieldedCons([LS.Areg(r1), LS.Areg(q1)], acts);
              assert LS.TreeSize(tc) < LS.TreeSize(t);
              BoolFlagLift(rer, ln, inp, tc);
            case _ =>
          }
        } else if delta == LN.NN(0) {
          ShieldedTail(acts);
          assert LS.ActionsRegexSize(cont) < LS.ActionsRegexSize(acts);
          BoolFlagLift(rer, cont, inp, t);
        } else {
          match t {
            case Choice(ta, tb) =>
              var itert := if greedy then ta else tb;
              var skipt := if greedy then tb else ta;
              match itert {
                case GroupActionT(g, ti) =>
                  // iteration subtree: pushed at CannotExit by both
                  // derivations — shared verbatim, no recursion.
                  ShieldedTail(acts);
                  assert LS.TreeSize(skipt) < LS.TreeSize(t);
                  BoolFlagLift(rer, cont, inp, skipt);
                case _ =>
              }
            case _ =>
          }
        }
      case Group(gid, r1) =>
        match t {
          case GroupActionT(g, tc) =>
            var ln := [LS.Areg(r1), LS.Aclose(gid)] + cont;
            EL.PikeLkActionsConsIff(LS.Aclose(gid), cont);
            EL.PikeLkActionsConsIff(LS.Areg(r1), [LS.Aclose(gid)] + cont);
            assert ln == [LS.Areg(r1)] + ([LS.Aclose(gid)] + cont);
            assert NN.NonNullableL(r) ==> NN.NonNullableL(r1);
            ShieldedCons([LS.Areg(r1), LS.Aclose(gid)], acts);
            assert LS.TreeSize(tc) < LS.TreeSize(t);
            BoolFlagLift(rer, ln, inp, tc);
          case _ =>
        }
      case AnchorR(a) =>
        if LS.AnchorSatisfied(rer, a, inp) {
          match t {
            case AnchorPass(a2, tc) =>
              ShieldedTail(acts);
              BoolFlagLift(rer, cont, inp, tc);
            case _ =>
          }
        }
      case LookaroundR(lk, r1) =>
        // the gate does not read the loop flag; lift under it
        match t {
          case LK(lk2, tlk, tc) =>
            ShieldedTail(acts);
            BoolFlagLift(rer, cont, inp, tc);
          case _ =>
        }
      case Backreference(_) =>
  }
}
