// G1(b) consumer (W3): FlipClosed's L5 closedness ladder with
// the lookbehind-body scope (`L5PosLooksL`: positive lookbehind ==> GroupOkLB
// body) DROPPED. The backward arm uses the generic flip mirror
// (`G.ComputeTrReverseG` / `G.TreeResMirrorG`) and the scope-free ladder
// hypothesis `ClosedBelowAny` at the flipped instance, which may itself hold
// positive lookbehinds. The ladder body (`FirstLeafClosedRecAuxAny`) is
// generated from FlipClosed.dfy:485-841 by gen_closed.py.
//
// The two `assert {:split_here} true;` lines at the head of the look case's
// `LkDir` arms are W3's FlipClosedG2 variant (W3-G1b.md §2.3a): 32.5 M
// resources for the ladder instead of 872 M unsplit.
//
// First verified against flip-closed's deps + flip-closed's own .doo, with
// FlipMirrorG.dfy as a co-source (see W3-G1b.md).

module LindenElkFlipClosedG {
  import opened Std.Wrappers
  import M = LindenElkMain
  import FM = LindenElkFlipMirror
  import FD = LindenElkFlipDisc
  import FR = LindenElkFlipRev
  import FC = LindenElkFlipClosed
  import TML = LindenElkTreeMirrorLk
  import TRM = LindenTreeResMirror
  import SD = LindenSpanDuality
  import EL = LindenElkEntryLk
  import NUL = LindenElkNullable
  import LFS = FunctionalSemantics
  import BS = BooleanSemantics
  import CD = LindenCloseDisc
  import LW = WarblreRegExpRecord
  import LT = Tree
  import LG = Groups
  import LS = Semantics
  import LC = Chars
  import FU = FunctionalUtils
  import WP = WarblrePrimitives
  import L = Regex
  import LL = LindenElkLookLeaves
  import LN = WarblreNumeric
  import G = LindenElkFlipMirrorG

  /** The fragment's own regex predicate already excludes backreferences, so the
      generic mirror needs NO extra premise anywhere `PikeLkRegexRec` holds. */
  lemma PikeLkIsNoBackref(r: L.Regex)
    requires EL.PikeLkRegexRec(r)
    ensures SD.NoBackrefL(r)
    decreases r
  {
    match r
    case Disjunction(r1, r2) => PikeLkIsNoBackref(r1); PikeLkIsNoBackref(r2);
    case Sequence(r1, r2) => PikeLkIsNoBackref(r1); PikeLkIsNoBackref(r2);
    case Quantified(_, _, _, r1) => PikeLkIsNoBackref(r1);
    case Group(_, r1) => PikeLkIsNoBackref(r1);
    case LookaroundR(_, r1) => PikeLkIsNoBackref(r1);
    case _ =>
  }

  /** `ClosedBelowL5` with the L5 scope dropped: ANY look nesting. */
  ghost predicate ClosedBelowAny(rer: LW.RegExpRecord, D: nat) {
    forall acts: LS.Actions, inp: LC.Input, b: BS.LoopBool, t: LT.Tree, gm: LG.GroupMap, leaf: LT.Leaf ::
      (D > 0 && M.NestDepthActsLe(acts, D - 1)
       && EL.BoolTreeLk(rer, acts, inp, b, t)
       && EL.PikeLkActionsRec(acts)
       && M.OpenOf(gm) <= M.PendingCloses(acts)
       && LT.TreeRes(t, gm, inp, WP.Forward) == Some(leaf)
       && M.LkClosedInGm(gm, acts)
       && M.OuterLkDisjoint(acts)
       && M.NoDupRegsActs(acts)
       && TRM.GmInBounds(gm, |inp.pref| + |inp.next|))
      ==> M.ClosedGm(leaf.1)
  }

  /** INSTANCE: the scope-free hypothesis implies the scoped one. */
  lemma ClosedBelowAnyImpliesL5(rer: LW.RegExpRecord, D: nat)
    requires ClosedBelowAny(rer, D)
    ensures FC.ClosedBelowL5(rer, D)
  {}

  /** Forward arm, scope-free (`FC.BodyLeafClosedFromBelowL5` minus `L5PosLooksL`). */
  lemma BodyLeafClosedFromBelowAny(rer: LW.RegExpRecord, lk: L.Lookaround, r1: L.Regex,
                                   tlk: LT.Tree, inp: LC.Input, gmR: LG.GroupMap,
                                   subR0: LT.Leaf, D: nat)
    requires L.Positivity(lk) && L.LkDir(lk) == WP.Forward
    requires EL.PikeLkRegexRec(r1)
    requires tlk == FU.ComputeTr(rer, [LS.Areg(r1)], inp, LG.Empty, WP.Forward)
    requires LT.TreeRes(tlk, gmR, inp, WP.Forward) == Some(subR0)
    requires forall g :: g in gmR ==> gmR[g].endIdx.Some?
    requires M.NoDupSeq(L.DefGroups(r1))
    requires TRM.GmInBounds(gmR, |inp.pref| + |inp.next|)
    requires D > 0 && M.NestDepthL(r1) <= D - 1
    requires ClosedBelowAny(rer, D)
    ensures M.ClosedGm(subR0.1)
  {
    assert EL.PikeLkActionsRec([LS.Areg(r1)]) by {
      assert [LS.Areg(r1)] == [LS.Areg(r1)] + [];
      assert EL.PikeLkActionsRec([]);
      EL.PikeLkActionsRecConsIff(LS.Areg(r1), []);
    }
    var fuel := LFS.ActionsFuel([LS.Areg(r1)], inp, WP.Forward) + 1;
    LFS.FunctionalTerminates(rer, [LS.Areg(r1)], inp, LG.Empty, WP.Forward, fuel);
    assert LFS.ComputeTree(rer, [LS.Areg(r1)], inp, LG.Empty, WP.Forward, fuel) == Some(tlk);
    var b0 := BS.CannotExit;
    assert BS.BoolEncoding(b0, inp, [LS.Areg(r1)]);
    EL.ComputeBoolTreeLkRec(rer, [LS.Areg(r1)], inp, LG.Empty, b0, fuel, tlk);
    assert EL.BoolTreeLk(rer, [LS.Areg(r1)], inp, b0, tlk);
    assert M.NestDepthActsLe([LS.Areg(r1)], D - 1);
    assert M.OpenOf(gmR) == {} by {
      forall g | g in M.OpenOf(gmR) ensures false { assert gmR[g].endIdx.Some?; }
    }
    assert M.OpenOf(gmR) <= M.PendingCloses([LS.Areg(r1)]);
    assert M.LkClosedInGm(gmR, [LS.Areg(r1)]) by {
      forall g | g in gmR && g in M.LkBodyGroupsActs([LS.Areg(r1)]) ensures gmR[g].endIdx.Some? { }
    }
    assert M.OuterLkDisjoint([LS.Areg(r1)]) by {
      M.OuterDefsActsCons(LS.Areg(r1), []); M.LkBodyGroupsActsCons(LS.Areg(r1), []);
      M.OuterLkFromNoDup(r1);
    }
    assert M.NoDupRegsActs([LS.Areg(r1)]);
  }

  /** Backward arm, generic (`FC.BackBodyLeafClosedFromBelow` with `GroupOkLB(r1)`
      dropped): the generic mirror sends the backward body walk to the flipped
      body's forward walk, which is a `ClosedBelowAny` instance whatever looks it
      holds (no `FwdPosActsL` needed). */
  lemma BackBodyLeafClosedFromBelowG(
      rer: LW.RegExpRecord, lk: L.Lookaround, r1: L.Regex,
      tlk: LT.Tree, inp: LC.Input, gmR: LG.GroupMap, subR0: LT.Leaf, D: nat)
    requires L.Positivity(lk) && L.LkDir(lk) == WP.Backward
    requires EL.PikeLkRegexRec(r1)
    requires tlk == FU.ComputeTr(rer, [LS.Areg(r1)], inp, LG.Empty, WP.Backward)
    requires LT.TreeRes(tlk, gmR, inp, WP.Backward) == Some(subR0)
    requires forall g :: g in gmR ==> gmR[g].endIdx.Some?
    requires M.NoDupSeq(L.DefGroups(r1))
    requires TRM.GmInBounds(gmR, |inp.pref| + |inp.next|)
    requires D > 0 && M.NestDepthL(r1) <= D - 1
    requires ClosedBelowAny(rer, D)
    ensures M.ClosedGm(subR0.1)
  {
    var n: nat := |inp.pref| + |inp.next|;
    var inpF := SD.SwapInput(inp);
    assert |inpF.pref| + |inpF.next| == n;
    var rF := FM.FlipRevL(r1);
    var actsB := [LS.Areg(r1)];
    var actsF := [LS.Areg(rF)];
    assert FM.FlipRevActs(actsB) == actsF;
    var tF := FU.ComputeTr(rer, actsF, inpF, LG.Empty, WP.Forward);

    // ---- generic F1: related trees; the backward tree is close-disciplined ----
    PikeLkIsNoBackref(r1);
    assert SD.NoBackrefActs(actsB);
    assert G.OppDir(WP.Backward) == WP.Forward;
    G.ComputeTrReverseG(rer, actsB, inp, LG.Empty, LG.Empty, WP.Backward);
    assert G.TreeMirrorRelG(tlk, tF);
    assert CD.NoDupG(L.DefGroups(r1));
    FD.ComputeTrCloseDiscF(rer, r1, inp, LG.Empty, WP.Backward);
    assert FM.CloseDiscF(tlk, {});
    assert TRM.OpenSubset(gmR, {});

    // ---- generic value fold from gmR ----
    var gmF := TRM.MirrorGm(gmR, n);
    FC.MirrorGmClosedIff(gmR, n);
    G.TreeResMirrorG(tlk, tF, gmR, inp, WP.Backward, n, {});
    var rb := LT.TreeRes(tlk, gmR, inp, WP.Backward);
    var rf := LT.TreeRes(tF, gmF, inpF, WP.Forward);
    assert rb == Some(subR0);
    assert rf.Some? && TRM.GmInBounds(subR0.1, n) && rf.value.1 == TRM.MirrorGm(subR0.1, n);

    // ---- the flipped instance is a ClosedBelowAny instance (no FwdPos) ----
    FC.FlipRevLPikeLkRec(r1);
    assert EL.PikeLkActionsRec(actsF) by {
      assert actsF == actsF + [];
      assert EL.PikeLkActionsRec([]);
      EL.PikeLkActionsRecConsIff(LS.Areg(rF), []);
    }
    var fuel := LFS.ActionsFuel(actsF, inpF, WP.Forward) + 1;
    LFS.FunctionalTerminates(rer, actsF, inpF, LG.Empty, WP.Forward, fuel);
    assert LFS.ComputeTree(rer, actsF, inpF, LG.Empty, WP.Forward, fuel) == Some(tF);
    var b0 := BS.CannotExit;
    assert BS.BoolEncoding(b0, inpF, actsF);
    EL.ComputeBoolTreeLkRec(rer, actsF, inpF, LG.Empty, b0, fuel, tF);
    assert EL.BoolTreeLk(rer, actsF, inpF, b0, tF);
    FC.NestDepthFlipRevL(r1);
    assert M.NestDepthActsLe(actsF, D - 1);
    assert M.ClosedGm(gmF);
    assert M.OpenOf(gmF) == {} by {
      forall g | g in M.OpenOf(gmF) ensures false { assert gmF[g].endIdx.Some?; }
    }
    assert M.OpenOf(gmF) <= M.PendingCloses(actsF);
    assert M.LkClosedInGm(gmF, actsF) by {
      forall g | g in gmF && g in M.LkBodyGroupsActs(actsF) ensures gmF[g].endIdx.Some? { }
    }
    FC.NoDupSeqFlipRevL(r1);
    assert M.OuterLkDisjoint(actsF) by {
      M.OuterDefsActsCons(LS.Areg(rF), []); M.LkBodyGroupsActsCons(LS.Areg(rF), []);
      M.OuterLkFromNoDup(rF);
    }
    assert M.NoDupRegsActs(actsF);
    assert TRM.GmInBounds(gmF, n);
    assert LT.TreeRes(tF, gmF, inpF, WP.Forward) == Some(rf.value);

    assert M.ClosedGm(rf.value.1);
    FC.MirrorGmClosedIff(subR0.1, n);
    assert M.ClosedGm(subR0.1);
  }

  least lemma FirstLeafClosedRecAuxAny(rer: LW.RegExpRecord, acts: LS.Actions, inp: LC.Input,
                                    b: BS.LoopBool, t: LT.Tree, gm: LG.GroupMap, leaf: LT.Leaf, D: nat)
    requires EL.BoolTreeLk(rer, acts, inp, b, t)
    requires EL.PikeLkActionsRec(acts)
    requires M.NestDepthActsLe(acts, D)
    requires ClosedBelowAny(rer, D)
    requires M.OpenOf(gm) <= M.PendingCloses(acts)
    requires LT.TreeRes(t, gm, inp, WP.Forward) == Some(leaf)
    requires M.LkClosedInGm(gm, acts)
    requires M.OuterLkDisjoint(acts)
    requires M.NoDupRegsActs(acts)
    requires TRM.GmInBounds(gm, |inp.pref| + |inp.next|)
    ensures M.ClosedGm(leaf.1)
{
    var n := |inp.pref| + |inp.next|;
    if |acts| == 0 {
      assert t == LT.Match;
      assert leaf.1 == gm;
      assert M.PendingCloses(acts) == {};
      forall g | g in gm ensures gm[g].endIdx.Some? {
        if gm[g].endIdx.None? { assert g in M.OpenOf(gm); }
      }
    } else {
      var cont := acts[1..];
      assert forall i :: 0 <= i < |cont| ==> cont[i] == acts[i + 1];
      assert M.PendingCloses(cont) <= M.PendingCloses(acts);
      assert M.NoDupRegsActs(cont) by { forall i | 0 <= i < |cont| ensures cont[i].Areg? ==> M.NoDupSeq(L.DefGroups(cont[i].r)) { assert cont[i] == acts[i + 1]; } }
      match acts[0]
      case Acheck(strcheck) =>
        if b == BS.CanExit {
          assert t.Progress?;
          assert M.PendingCloses(acts) == M.PendingCloses(cont);
          M.TailInv(gm, gm, acts);
          FirstLeafClosedRecAuxAny(rer, cont, inp, BS.CanExit, t.t, gm, leaf, D);
        } else {
          assert t == LT.Mismatch;
          assert false;
        }
      case Aclose(gid) =>
        assert t.GroupActionT? && t.g == LG.Close(gid);
        var gm2 := LG.GMUpdate(t.g, LC.Idx(inp), gm);
        assert gm2 == LG.GMClose(LC.Idx(inp), gid, gm);
        assert M.OpenOf(gm2) <= M.PendingCloses(cont) by {
          forall g | g in M.OpenOf(gm2) ensures g in M.PendingCloses(cont) {
            assert g != gid;
            assert g in M.OpenOf(gm);
            assert g in M.PendingCloses(acts);
            var i :| 0 <= i < |acts| && acts[i].Aclose? && acts[i].gid == g;
            assert i != 0;
            assert cont[i - 1] == acts[i];
          }
        }
        // GMClose keeps the domain, closes gid, and leaves every other group as-is.
        assert forall g :: g in gm2 ==> g in gm && (gm2[g].endIdx.Some? || gm2[g] == gm[g]);
        assert TRM.GmInBounds(gm2, n) by { assert LC.Idx(inp) <= n; }
        M.TailInv(gm, gm2, acts);
        FirstLeafClosedRecAuxAny(rer, cont, inp, b, t.t, gm2, leaf, D);
      case Areg(r) =>
        match r
        case Epsilon =>
          assert M.PendingCloses(acts) == M.PendingCloses(cont);
          M.TailInv(gm, gm, acts);
          FirstLeafClosedRecAuxAny(rer, cont, inp, b, t, gm, leaf, D);
        case Character(cd) =>
          if LC.ReadChar(rer, cd, inp, WP.Forward).None? {
            assert t == LT.Mismatch;
            assert false;
          } else {
            var pair := LC.ReadChar(rer, cd, inp, WP.Forward).value;
            assert t.Read?;
            assert pair.1 == LC.AdvanceInputP(inp, WP.Forward);
            assert |pair.1.pref| + |pair.1.next| == n;   // advance preserves total length
            assert M.PendingCloses(acts) == M.PendingCloses(cont);
            M.TailInv(gm, gm, acts);
            FirstLeafClosedRecAuxAny(rer, cont, pair.1, BS.CanExit, t.t, gm, leaf, D);
          }
        case Disjunction(r1, r2) =>
          assert t.Choice?;
          var acts1 := [LS.Areg(r1)] + cont;
          var acts2 := [LS.Areg(r2)] + cont;
          assert M.PendingCloses(acts1) == M.PendingCloses(cont) == M.PendingCloses(acts2) by {
            assert forall i :: 0 <= i < |cont| ==> acts1[i + 1] == cont[i] && acts2[i + 1] == cont[i];
          }
          assert M.PendingCloses(acts) == M.PendingCloses(cont);
          M.LkBodyGroupsActsCons(LS.Areg(r), cont); M.LkBodyGroupsActsCons(LS.Areg(r1), cont); M.LkBodyGroupsActsCons(LS.Areg(r2), cont);
          M.OuterDefsActsCons(LS.Areg(r), cont); M.OuterDefsActsCons(LS.Areg(r1), cont); M.OuterDefsActsCons(LS.Areg(r2), cont);
          assert LL.LkBodyGroups(r) == LL.LkBodyGroups(r1) + LL.LkBodyGroups(r2);
          assert M.DefGroupsOutsideLooksL(r) == M.DefGroupsOutsideLooksL(r1) + M.DefGroupsOutsideLooksL(r2);
          assert M.NoDupSeq(L.DefGroups(r)) && L.DefGroups(r) == L.DefGroups(r1) + L.DefGroups(r2);
          M.NoDupConcat(L.DefGroups(r1), L.DefGroups(r2));
          assert M.NoDupRegsActs(acts1) by { forall i | 0 <= i < |acts1| ensures acts1[i].Areg? ==> M.NoDupSeq(L.DefGroups(acts1[i].r)) { if i == 0 {} else { assert acts1[i] == cont[i - 1]; } } }
          assert M.NoDupRegsActs(acts2) by { forall i | 0 <= i < |acts2| ensures acts2[i].Areg? ==> M.NoDupSeq(L.DefGroups(acts2[i].r)) { if i == 0 {} else { assert acts2[i] == cont[i - 1]; } } }
          if LT.TreeRes(t.t1, gm, inp, WP.Forward).Some? {
            M.SubInv(gm, gm, acts1, acts);
            FirstLeafClosedRecAuxAny(rer, acts1, inp, b, t.t1, gm, leaf, D);
          } else {
            M.SubInv(gm, gm, acts2, acts);
            FirstLeafClosedRecAuxAny(rer, acts2, inp, b, t.t2, gm, leaf, D);
          }
        case Sequence(r1, r2) =>
          var acts1 := [LS.Areg(r1), LS.Areg(r2)] + cont;
          assert M.PendingCloses(acts1) == M.PendingCloses(cont) by {
            assert forall i :: 0 <= i < |cont| ==> acts1[i + 2] == cont[i];
          }
          assert M.PendingCloses(acts) == M.PendingCloses(cont);
          assert acts1 == [LS.Areg(r1)] + ([LS.Areg(r2)] + cont);
          M.LkBodyGroupsActsCons(LS.Areg(r), cont); M.LkBodyGroupsActsCons(LS.Areg(r1), [LS.Areg(r2)] + cont); M.LkBodyGroupsActsCons(LS.Areg(r2), cont);
          M.OuterDefsActsCons(LS.Areg(r), cont); M.OuterDefsActsCons(LS.Areg(r1), [LS.Areg(r2)] + cont); M.OuterDefsActsCons(LS.Areg(r2), cont);
          assert LL.LkBodyGroups(r) == LL.LkBodyGroups(r1) + LL.LkBodyGroups(r2);
          assert M.DefGroupsOutsideLooksL(r) == M.DefGroupsOutsideLooksL(r1) + M.DefGroupsOutsideLooksL(r2);
          assert M.NoDupSeq(L.DefGroups(r)) && L.DefGroups(r) == L.DefGroups(r1) + L.DefGroups(r2);
          M.NoDupConcat(L.DefGroups(r1), L.DefGroups(r2));
          assert M.NoDupRegsActs(acts1) by { forall i | 0 <= i < |acts1| ensures acts1[i].Areg? ==> M.NoDupSeq(L.DefGroups(acts1[i].r)) { if i < 2 {} else { assert acts1[i] == cont[i - 2]; } } }
          M.SubInv(gm, gm, acts1, acts);
          FirstLeafClosedRecAuxAny(rer, acts1, inp, b, t, gm, leaf, D);
        case Quantified(greedy, min, delta, r1) =>
          var gidl := L.DefGroups(r1);
          if min > 0 {
            assert t.GroupActionT? && t.g == LG.Reset(gidl);
            var gm2 := LG.GMUpdate(t.g, LC.Idx(inp), gm);
            assert gm2 == LG.GMReset(gidl, gm);
            assert M.OpenOf(gm2) <= M.OpenOf(gm);
            assert forall g :: g in gm2 ==> g in gm && gm2[g] == gm[g];
            var q' := L.Quantified(greedy, min - 1, delta, r1);
            var acts1 := [LS.Areg(r1), LS.Areg(q')] + cont;
            assert M.PendingCloses(acts1) == M.PendingCloses(cont) by {
              assert forall i :: 0 <= i < |cont| ==> acts1[i + 2] == cont[i];
            }
            assert M.PendingCloses(acts) == M.PendingCloses(cont);
            assert M.NoDupSeq(L.DefGroups(r)) && L.DefGroups(r) == L.DefGroups(r1) && L.DefGroups(q') == L.DefGroups(r1);
            assert M.NoDupRegsActs(acts1) by { forall i | 0 <= i < |acts1| ensures acts1[i].Areg? ==> M.NoDupSeq(L.DefGroups(acts1[i].r)) { if i < 2 {} else { assert acts1[i] == cont[i - 2]; } } }
            assert TRM.GmInBounds(gm2, n);   // GMReset only shrinks the domain
            M.QuantSubInv(gm, gm2, r, r1, q', cont, acts, acts1);
            FirstLeafClosedRecAuxAny(rer, acts1, inp, b, t.t, gm2, leaf, D);
          } else if delta == LN.NN(0) {
            assert M.PendingCloses(acts) == M.PendingCloses(cont);
            M.TailInv(gm, gm, acts);
            FirstLeafClosedRecAuxAny(rer, cont, inp, b, t, gm, leaf, D);
          } else {
            assert t.Choice?;
            var itert := if greedy then t.t1 else t.t2;
            var skipt := if greedy then t.t2 else t.t1;
            assert itert.GroupActionT? && itert.g == LG.Reset(gidl);
            assert M.PendingCloses(acts) == M.PendingCloses(cont);
            // Seqop picks t.t1 first: split on which branch the leaf came from.
            if LT.TreeRes(t.t1, gm, inp, WP.Forward).Some? {
              if greedy {
                var gm2 := LG.GMUpdate(itert.g, LC.Idx(inp), gm);
                assert gm2 == LG.GMReset(gidl, gm);
                assert M.OpenOf(gm2) <= M.OpenOf(gm);
                assert forall g :: g in gm2 ==> g in gm && gm2[g] == gm[g];
                var q'' := L.Quantified(greedy, 0, LFS.NoiPred(delta), r1);
                var acts1 := [LS.Areg(r1), LS.Acheck(inp), LS.Areg(q'')] + cont;
                assert M.PendingCloses(acts1) == M.PendingCloses(cont) by {
                  assert forall i :: 0 <= i < |cont| ==> acts1[i + 3] == cont[i];
                }
                assert M.NoDupSeq(L.DefGroups(r)) && L.DefGroups(r) == L.DefGroups(r1) && L.DefGroups(q'') == L.DefGroups(r1);
                assert M.NoDupRegsActs(acts1) by { forall i | 0 <= i < |acts1| ensures acts1[i].Areg? ==> M.NoDupSeq(L.DefGroups(acts1[i].r)) { if i < 3 {} else { assert acts1[i] == cont[i - 3]; } } }
                assert TRM.GmInBounds(gm2, n);
                M.QuantSubInvCheck(gm, gm2, r, r1, q'', inp, cont, acts, acts1);
                FirstLeafClosedRecAuxAny(rer, acts1, inp, BS.CannotExit, itert.t, gm2, leaf, D);
              } else {
                M.TailInv(gm, gm, acts);
                FirstLeafClosedRecAuxAny(rer, cont, inp, b, skipt, gm, leaf, D);
              }
            } else {
              if greedy {
                M.TailInv(gm, gm, acts);
                FirstLeafClosedRecAuxAny(rer, cont, inp, b, skipt, gm, leaf, D);
              } else {
                var gm2 := LG.GMUpdate(itert.g, LC.Idx(inp), gm);
                assert gm2 == LG.GMReset(gidl, gm);
                assert M.OpenOf(gm2) <= M.OpenOf(gm);
                assert forall g :: g in gm2 ==> g in gm && gm2[g] == gm[g];
                var q'' := L.Quantified(greedy, 0, LFS.NoiPred(delta), r1);
                var acts1 := [LS.Areg(r1), LS.Acheck(inp), LS.Areg(q'')] + cont;
                assert M.PendingCloses(acts1) == M.PendingCloses(cont) by {
                  assert forall i :: 0 <= i < |cont| ==> acts1[i + 3] == cont[i];
                }
                assert M.NoDupSeq(L.DefGroups(r)) && L.DefGroups(r) == L.DefGroups(r1) && L.DefGroups(q'') == L.DefGroups(r1);
                assert M.NoDupRegsActs(acts1) by { forall i | 0 <= i < |acts1| ensures acts1[i].Areg? ==> M.NoDupSeq(L.DefGroups(acts1[i].r)) { if i < 3 {} else { assert acts1[i] == cont[i - 3]; } } }
                assert TRM.GmInBounds(gm2, n);
                M.QuantSubInvCheck(gm, gm2, r, r1, q'', inp, cont, acts, acts1);
                FirstLeafClosedRecAuxAny(rer, acts1, inp, BS.CannotExit, itert.t, gm2, leaf, D);
              }
            }
          }
        case Group(gid, r1) =>
          assert t.GroupActionT? && t.g == LG.Open(gid);
          var gm2 := LG.GMUpdate(t.g, LC.Idx(inp), gm);
          assert gm2 == LG.GMOpen(LC.Idx(inp), gid, gm);
          var acts1 := [LS.Areg(r1), LS.Aclose(gid)] + cont;
          assert gid in M.PendingCloses(acts1) by { assert acts1[1].Aclose? && acts1[1].gid == gid; }
          assert M.OpenOf(gm2) <= M.PendingCloses(acts1) by {
            forall g | g in M.OpenOf(gm2) ensures g in M.PendingCloses(acts1) {
              if g != gid {
                assert g in M.OpenOf(gm);
                assert g in M.PendingCloses(acts);
                var i :| 0 <= i < |acts| && acts[i].Aclose? && acts[i].gid == g;
                assert i != 0;
                assert acts1[i + 1] == cont[i - 1] == acts[i];
              }
            }
          }
          // gid is an OUTER group ⇒ gid ∉ M.LkBodyGroupsActs; the Group rewrite keeps
          // the same look groups and shrinks outer defs, so both invariants thread.
          assert acts1 == [LS.Areg(r1)] + ([LS.Aclose(gid)] + cont);
          M.LkBodyGroupsActsCons(LS.Areg(r), cont); M.LkBodyGroupsActsCons(LS.Areg(r1), [LS.Aclose(gid)] + cont); M.LkBodyGroupsActsCons(LS.Aclose(gid), cont);
          M.OuterDefsActsCons(LS.Areg(r), cont); M.OuterDefsActsCons(LS.Areg(r1), [LS.Aclose(gid)] + cont); M.OuterDefsActsCons(LS.Aclose(gid), cont);
          assert L.DefGroups(r) == [gid] + L.DefGroups(r1);
          assert gid in M.OuterDefsActs(acts) && gid !in M.LkBodyGroupsActs(acts);   // M.OuterLkDisjoint
          assert M.LkBodyGroupsActs(acts1) == M.LkBodyGroupsActs(acts);
          assert M.LkClosedInGm(gm2, acts1) by {
            forall g | g in gm2 && g in M.LkBodyGroupsActs(acts1) ensures gm2[g].endIdx.Some? {
              assert g != gid; assert g in gm && g in M.LkBodyGroupsActs(acts);
            }
          }
          assert M.OuterLkDisjoint(acts1);
          assert M.NoDupSeq(L.DefGroups(r)) && L.DefGroups(r) == [gid] + L.DefGroups(r1);
          M.NoDupTailSeq([gid], L.DefGroups(r1));   // drop the leading [gid] ⇒ M.NoDupSeq(DefGroups(r1))
          assert M.NoDupRegsActs(acts1) by { forall i | 0 <= i < |acts1| ensures acts1[i].Areg? ==> M.NoDupSeq(L.DefGroups(acts1[i].r)) { if i < 2 {} else { assert acts1[i] == cont[i - 2]; } } }
          assert TRM.GmInBounds(gm2, n) by { assert LC.Idx(inp) <= n; }
          FirstLeafClosedRecAuxAny(rer, acts1, inp, b, t.t, gm2, leaf, D);
        case AnchorR(a) =>
          if LS.AnchorSatisfied(rer, a, inp) {
            assert t.AnchorPass?;
            assert M.PendingCloses(acts) == M.PendingCloses(cont);
            M.TailInv(gm, gm, acts);
            FirstLeafClosedRecAuxAny(rer, cont, inp, b, t.t, gm, leaf, D);
          } else {
            assert t == LT.Mismatch;
            assert false;
          }
        case LookaroundR(lk, r1) =>
          // The gate: fold the body first-leaf in (positive) or thread gm (negative).
          var S := (set g | g in L.DefGroups(r1));
          match t {
            case LK(lk2, tlk, tc) =>
              assert M.PendingCloses(acts) == M.PendingCloses(cont);
              assert EL.LkGateOk(rer, lk, r1, inp, tlk, true) && EL.BoolTreeLk(rer, cont, inp, b, tc);
              assert tlk == FU.ComputeTr(rer, [LS.Areg(r1)], inp, LG.Empty, L.LkDir(lk));
              var dir := L.LkDir(lk);
              M.LkBodyGroupsActsCons(LS.Areg(r), cont); M.OuterDefsActsCons(LS.Areg(r), cont);
              assert L.DefGroups(r) == L.DefGroups(r1);
              assert LL.LkBodyGroups(r) == S + LL.LkBodyGroups(r1);
              assert S <= M.LkBodyGroupsActs(acts);
              assert M.LkBodyGroupsActs(cont) <= M.LkBodyGroupsActs(acts);
              assert M.OuterDefsActs(cont) <= M.OuterDefsActs(acts);
              assert M.OuterLkDisjoint(cont);
              if L.Positivity(lk) {
                assert EL.PikeLkRegexRec(r1);                   // Rec: positive body recurses
                assert forall g :: g in gm && g in S ==> gm[g].endIdx.Some? by {
                  forall g | g in gm && g in S ensures gm[g].endIdx.Some? { assert g in M.LkBodyGroupsActs(acts); }
                }
                var sub := LT.TreeLeaves(tlk, gm, inp, dir);
                LT.FirstTreeLeaf(tlk, gm, inp, dir);
                assert |sub| > 0;                               // else TreeRes(t, ..) would be None
                assert M.NoDupSeq(L.DefGroups(r1)) by { assert M.NoDupSeq(L.DefGroups(r)); }
                // ---- the STRATIFIED body-leaf closedness at the S-restriction ----
                var gmR := map g | g in gm && g in S :: gm[g];
                assert M.OpenOf(gmR) == {} by {
                  forall g | g in gmR ensures gmR[g].endIdx.Some? { assert g in gm && g in S; }
                }
                var subR := LT.TreeLeaves(tlk, gmR, inp, dir);
                assert LL.GmAgreeInside(gm, gmR, S) by {
                  forall g | g in S ensures (g in gm <==> g in gmR) && (g in gm ==> gm[g] == gmR[g]) {}
                }
                LL.TreeLeavesFrameInside(tlk, gm, gmR, inp, dir, S);
                assert |sub| == |subR|;
                LT.FirstTreeLeaf(tlk, gmR, inp, dir);
                assert LT.TreeRes(tlk, gmR, inp, dir) == Some(subR[0]);
                // the body instance sits strictly below D
                assert acts[0].Areg? && acts[0].r == r;
                assert M.NestDepthL(r) <= D;                     // M.NestDepthActsLe at index 0
                assert M.NestDepthL(r1) < M.NestDepthL(r);
                // the body-walk confinement (hoisted: all following blocks read it)
                assert LL.DefGroupsIn(r1, S);
                LL.ComputeTrConfinedRec(rer, r1, inp, LG.Empty, dir, S);
                LL.GmConfinedLeavesRec(tlk, gm, inp, dir, S);
                assert LL.GmAgreeOutside(sub[0].1, gm, S);
                assert LL.GmAgreeInside(sub[0].1, subR[0].1, S);   // TreeLeavesFrameInside at 0
                assert TRM.GmInBounds(gmR, n) by {
                  assert forall g :: g in gmR ==> g in gm && gmR[g] == gm[g];
                }
                assert forall g :: g in gmR ==> gmR[g].endIdx.Some? by {
                  forall g | g in gmR ensures gmR[g].endIdx.Some? { assert g in gm && g in S; }
                }
                if dir == WP.Forward {
                  assert {:split_here} true;
                  BodyLeafClosedFromBelowAny(rer, lk, r1, tlk, inp, gmR, subR[0], D);
                } else {
                  assert {:split_here} true;
                  // ANY body: the generic flip mirror + the scope-free hypothesis.
                  assert dir == WP.Backward;
                  BackBodyLeafClosedFromBelowG(rer, lk, r1, tlk, inp, gmR, subR[0], D);
                }
                assert M.ClosedGm(subR[0].1);                     // ClosedBelow at the body instance
                // frames: S-agreement moves closedness; off-S the leaf equals gm
                assert forall g :: g in M.OpenOf(sub[0].1) ==> g in M.OpenOf(gm) by {
                  forall g | g in M.OpenOf(sub[0].1) ensures g in M.OpenOf(gm) {
                    if g in S {
                      assert g in subR[0].1 && subR[0].1[g].endIdx.Some?;
                      assert false;
                    }
                  }
                }
                assert forall g :: g in sub[0].1 ==> g in gm || g in S by {
                  forall g | g in sub[0].1 ensures g in gm || g in S {
                    if g !in S { }
                  }
                }
                assert TRM.GmInBounds(sub[0].1, n) by { M.TreeLeavesInBounds(tlk, gm, inp, dir, n); }
                assert M.OpenOf(sub[0].1) <= M.PendingCloses(cont) by {
                  forall g | g in M.OpenOf(sub[0].1) ensures g in M.PendingCloses(cont) {
                    assert g in M.OpenOf(gm);
                    assert g in M.PendingCloses(acts);
                    var i :| 0 <= i < |acts| && acts[i].Aclose? && acts[i].gid == g;
                    assert i != 0;
                    assert cont[i - 1] == acts[i];
                  }
                }
                assert LT.TreeRes(tc, sub[0].1, inp, WP.Forward) == Some(leaf);  // LK positive unfold
                assert M.LkClosedInGm(sub[0].1, cont) by {
                  forall g | g in sub[0].1 && g in M.LkBodyGroupsActs(cont) ensures sub[0].1[g].endIdx.Some? {
                    if g in S {
                      assert LL.GmAgreeInside(sub[0].1, subR[0].1, S);
                      assert g in subR[0].1 && subR[0].1[g].endIdx.Some?;
                    } else {
                      assert g in gm;
                      assert g in M.LkBodyGroupsActs(acts);
                    }
                  }
                }
                FirstLeafClosedRecAuxAny(rer, cont, inp, b, tc, sub[0].1, leaf, D);
              } else {
                assert LT.TreeRes(tc, gm, inp, WP.Forward) == Some(leaf);        // LK negative unfold
                assert M.LkClosedInGm(gm, cont) by {
                  forall g | g in gm && g in M.LkBodyGroupsActs(cont) ensures gm[g].endIdx.Some? { assert g in M.LkBodyGroupsActs(acts); }
                }
                assert M.PendingCloses(acts) == M.PendingCloses(cont);
                M.TailInv(gm, gm, acts);
                FirstLeafClosedRecAuxAny(rer, cont, inp, b, tc, gm, leaf, D);
              }
            case LKFail(lk2, tlk) =>
              assert false;                    // LKFail has no leaves
            case _ =>
          }
        case Backreference(_) =>
          assert false;
    }
  }

  /** The stratification ladder: closedness holds below every depth bound. */
  lemma ClosedBelowAllAny(rer: LW.RegExpRecord, D: nat)
    ensures ClosedBelowAny(rer, D)
    decreases D
  {
    if D == 0 {
    } else {
      ClosedBelowAllAny(rer, D - 1);
      forall acts: LS.Actions, inp: LC.Input, b: BS.LoopBool, t: LT.Tree, gm: LG.GroupMap, leaf: LT.Leaf |
        M.NestDepthActsLe(acts, D - 1)
        && EL.BoolTreeLk(rer, acts, inp, b, t)
        && EL.PikeLkActionsRec(acts)
        && M.OpenOf(gm) <= M.PendingCloses(acts)
        && LT.TreeRes(t, gm, inp, WP.Forward) == Some(leaf)
        && M.LkClosedInGm(gm, acts)
        && M.OuterLkDisjoint(acts)
        && M.NoDupRegsActs(acts)
        && TRM.GmInBounds(gm, |inp.pref| + |inp.next|)
        ensures M.ClosedGm(leaf.1)
      {
        FirstLeafClosedRecAuxAny(rer, acts, inp, b, t, gm, leaf, D - 1);
      }
    }
  }

  /** THE depth-k first-leaf closedness (the L4 extraction feed). */

  lemma FirstLeafClosedRecAny(rer: LW.RegExpRecord, acts: LS.Actions, inp: LC.Input,
                           b: BS.LoopBool, t: LT.Tree, gm: LG.GroupMap, leaf: LT.Leaf, D: nat)
    requires EL.BoolTreeLk(rer, acts, inp, b, t)
    requires EL.PikeLkActionsRec(acts)
    requires M.NestDepthActsLe(acts, D)
    requires M.OpenOf(gm) <= M.PendingCloses(acts)
    requires LT.TreeRes(t, gm, inp, WP.Forward) == Some(leaf)
    requires M.LkClosedInGm(gm, acts)
    requires M.OuterLkDisjoint(acts)
    requires M.NoDupRegsActs(acts)
    requires TRM.GmInBounds(gm, |inp.pref| + |inp.next|)
    ensures M.ClosedGm(leaf.1)
  {
    ClosedBelowAllAny(rer, D);
    FirstLeafClosedRecAuxAny(rer, acts, inp, b, t, gm, leaf, D);
  }
}
