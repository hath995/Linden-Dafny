// G5a rung A: the priority theorem for a greedy nullable plus whose skip arm is GUARDED (the CDN scheme).
//
// CDN layout (Compiler.dfy:122-130): head fork `Fork(iter, e1+2)`, then `e1+2: CheckNullable(qid)`,
// `e1+3: SetQuantToClock(qid, true)`, continuation at `e1+4`. Under `tr_cdn` the skip arm represents
//   * guard true  (FirstEmptyPath Some): `tr_stamp`'s tree, i.e. the CIN skip arm `Reset(gidl); Chain(p, tcont)`;
//   * guard false (FirstEmptyPath None): `Mismatch`.
// `CdnPlusPrioritySome` is `NP.CinPlusPriority` with `NUL.CINullableL(r1)` replaced by its only use,
// `FirstEmptyPathL(rer, r1, inp).Some?` (generated from that lemma by G5a1-P1a-cdn-priority.py.txt).
// `CdnPlusPriorityNone` is the new case: no leaf of `r1`'s tree sits at `inp`, so every `Acheck(inp)` chunk is a
// pass-through and the spec tree's leaves ARE the iteration arm's leaves (exact equality, no `S` slack).
// Neither needs a nullability premise: the CIN theorem is the `Some` case (`CinIsSomeCase`).
module LindenElkCdnPriority {
  import opened Std.Wrappers
  import LW = WarblreRegExpRecord
  import WP = WarblrePrimitives
  import LC = Chars
  import LG = Groups
  import L = Regex
  import LN = WarblreNumeric
  import LS = Semantics
  import LT = Tree
  import BS = BooleanSemantics
  import FS = FunctionalSemantics
  import FU = FunctionalUtils
  import SS = StrictSuffix
  import NUL = LindenElkNullable
  import EQ = Equivalence
  import FM = FlatMap
  import EL = LindenElkEntryLk
  import CE = LindenElkCheckErase
  import LL = LindenElkLookLeaves
  import NP = LindenElkNulledPlus
  import NB = LindenElkNulledPlusBool

  // ===========================================================================
  // The Some case: `NP.CinPlusPriority` with the CINullable premise weakened to its only use.
  // ===========================================================================

  lemma CdnPlusPrioritySome(rer: LW.RegExpRecord, r1: L.Regex, cont: LS.Actions, inp: LC.Input, gm: LG.GroupMap,
                            S: set<LG.GroupId>, tplus: LT.Tree, titer: LT.Tree, tcont: LT.Tree)
    requires EL.PikeLkRegexRec(r1) && EL.PikeLkActionsRec(cont)
    requires LL.LkBodiesInS(r1, S)   // (F-c) the continuation's looks are NOT constrained: the theorem runs at S = {}
    requires NP.FirstEmptyPathL(rer, r1, inp).Some?
    requires LS.IsTree(rer, [LS.Areg(L.Quantified(true, 1, LN.Inf, r1))] + cont, inp, gm, WP.Forward, tplus)
    requires LS.IsTree(rer, [LS.Areg(r1), LS.Acheck(inp), LS.Areg(L.Quantified(true, 0, LN.Inf, r1))] + cont,
                       inp, LG.GMReset(L.DefGroups(r1), gm), WP.Forward, titer)
    requires LS.IsTree(rer, cont, inp, gm, WP.Forward, tcont)
    ensures var gidl := L.DefGroups(r1);
            var p := NP.FirstEmptyPathL(rer, r1, inp).value;
            var tcin := LT.Choice(LT.GroupActionT(LG.Reset(gidl), titer),
                                  LT.GroupActionT(LG.Reset(gidl), NP.Chain(p, tcont)));
            var rc := LT.TreeRes(tcin, gm, inp, WP.Forward);
            var rp := LT.TreeRes(tplus, gm, inp, WP.Forward);
            (rc.Some? <==> rp.Some?)
            && (rc.Some? ==> rc.value.0 == rp.value.0 && LL.GmAgreeOutside(rc.value.1, rp.value.1, S))
  {
    var gidl := L.DefGroups(r1);
    var Gset := set g | g in gidl;
    var gm' := LG.GMReset(gidl, gm);
    var idx := LC.Idx(inp);
    var Q1 := L.Quantified(true, 1, LN.Inf, r1);
    var Q0 := L.Quantified(true, 0, LN.Inf, r1);
    EL.CinHeadIntro(true, 0, LN.Inf, r1);   // (G5a-1 3-L0c)
    var A := [LS.Areg(r1)];
    var rest := [LS.Areg(Q0)] + cont;
    var chk := [LS.Acheck(inp)] + rest;
    var iterActs := [LS.Areg(r1), LS.Acheck(inp), LS.Areg(Q0)] + cont;
    assert iterActs == A + chk;
    var plusActs := [LS.Areg(Q1)] + cont;
    assert plusActs[0] == LS.Areg(Q1) && plusActs[1..] == cont;

    // ---- the spec tree: Reset; tc with tc the tree of A + rest at gm' ----
    assert tplus.GroupActionT? && tplus.g == LG.Reset(gidl);
    var tc := tplus.t;
    assert LS.IsTree(rer, [LS.Areg(r1), LS.Areg(L.Quantified(true, 0, LN.Inf, r1))] + cont, inp, gm', WP.Forward, tc);
    assert [LS.Areg(r1), LS.Areg(Q0)] + cont == A + rest;
    var Lplus := LT.TreeLeaves(tc, gm', inp, WP.Forward);
    assert LT.TreeLeaves(tplus, gm, inp, WP.Forward) == Lplus;

    assert {:split_here} true;
    // ---- fragment facts for the sub-stacks ----
    EL.PikeLkActionsRecConsIff(LS.Areg(r1), []);
    assert EL.PikeLkActionsRec(A);
    EL.PikeLkActionsRecConsIff(LS.Areg(Q0), cont);
    assert EL.PikeLkActionsRec(rest);
    LL.LkActsInSCons(LS.Areg(r1), [], S);
    assert LL.LkActsInS(A, S);

    // ---- the first empty path of r1 ----
    assert A == [LS.Areg(r1)] + [];
    var p := NP.FirstEmptyPathL(rer, r1, inp).value;
    var gmP := NP.ApplyPath(p, idx, gm');
    assert NP.ActsGroupsIn(A, Gset) by {
      forall i | 0 <= i < |A| ensures (A[i].Areg? ==> forall g :: g in L.DefGroups(A[i].r) ==> g in Gset) && (A[i].Aclose? ==> A[i].gid in Gset) {}
    }
    NP.PathActionsIn(rer, A, inp, Gset);
    NP.ApplyPathOutside(p, idx, gm', Gset);
    NP.GMResetAgree(gidl, gmP, gm');
    assert LG.GMReset(gidl, gm') == gm';
    assert LG.GMReset(gidl, gmP) == gm';

    assert {:split_here} true;
    // ---- r1's own tree and its leaves at gm' ----
    var tr1 := FU.ComputeTr(rer, A, inp, gm', WP.Forward);
    FU.ComputeTrIsTree(rer, A, inp, gm', WP.Forward);
    var ls := LT.TreeLeaves(tr1, gm', inp, WP.Forward);
    NP.EmptyLeavesA(rer, A, inp, gm', S, tr1);
    NP.FirstAtSpec(ls, inp);
    var e := NP.FirstAt(ls, inp).value;
    var gme := ls[e].1;
    assert LL.GmAgreeOutside(gme, gmP, S);

    assert {:split_here} true;
    // ---- the two flat-maps over r1's leaves ----
    var frest := EQ.ActFromLeafFn(rer, rest, WP.Forward);
    var fchk := EQ.ActFromLeafFn(rer, chk, WP.Forward);
    EQ.ActFromLeafDeterm(rer, WP.Forward, rest);
    EQ.ActFromLeafDeterm(rer, WP.Forward, chk);
    EQ.LeavesConcat(rer, inp, gm', WP.Forward, A, rest, tc, tr1);
    assert FM.FlatMapRel(ls, frest, Lplus);
    var I := LT.TreeLeaves(titer, gm', inp, WP.Forward);
    EQ.LeavesConcat(rer, inp, gm', WP.Forward, A, chk, titer, tr1);
    assert FM.FlatMapRel(ls, fchk, I);

    assert {:split_here} true;
    // ---- split both at the first empty leaf ----
    var pre := ls[..e];
    var post := ls[e + 1..];
    assert ls == pre + ([ls[e]] + post);
    NP.FlatMapSplit(pre, [ls[e]] + post, frest, Lplus);
    var R1: seq<LT.Leaf>, R23: seq<LT.Leaf> :| FM.FlatMapRel(pre, frest, R1) && FM.FlatMapRel([ls[e]] + post, frest, R23) && Lplus == R1 + R23;
    NP.FlatMapSplit([ls[e]], post, frest, R23);
    var R2: seq<LT.Leaf>, R3: seq<LT.Leaf> :| FM.FlatMapRel([ls[e]], frest, R2) && FM.FlatMapRel(post, frest, R3) && R23 == R2 + R3;
    NP.FlatMapSplit(pre, [ls[e]] + post, fchk, I);
    var I1: seq<LT.Leaf>, I23: seq<LT.Leaf> :| FM.FlatMapRel(pre, fchk, I1) && FM.FlatMapRel([ls[e]] + post, fchk, I23) && I == I1 + I23;
    NP.FlatMapSplit([ls[e]], post, fchk, I23);
    var I2: seq<LT.Leaf>, I3: seq<LT.Leaf> :| FM.FlatMapRel([ls[e]], fchk, I2) && FM.FlatMapRel(post, fchk, I3) && I23 == I2 + I3;
    // singleton flat-maps are single chunks
    assert frest(ls[e], R2) by {
      var ly, rst :| frest(([ls[e]])[0], ly) && FM.FlatMapRel(([ls[e]])[1..], frest, rst) && R2 == ly + rst;
      assert rst == [];
    }
    assert fchk(ls[e], I2) by {
      var ly, rst :| fchk(([ls[e]])[0], ly) && FM.FlatMapRel(([ls[e]])[1..], fchk, rst) && I2 == ly + rst;
      assert rst == [];
    }

    assert {:split_here} true;
    // ---- the consuming prefix agrees chunk by chunk ----
    forall i, y | 0 <= i < |pre| && fchk(pre[i], y) ensures frest(pre[i], y) {
      assert pre[i] == ls[i] && ls[i].0 != inp;
      NP.ChkChunk(rer, rest, inp, ls[i], y);
    }
    NP.FlatMapEqOn(pre, frest, fchk, R1, I1);
    assert R1 == I1;
    // ---- the empty leaf's check chunk is empty ----
    NP.ChkChunk(rer, rest, inp, ls[e], I2);
    assert I2 == [];
    assert I2 + I3 == I3;
    assert I23 == I3;
    assert I == I1 + I3;
    assert {:split_here} true;
    // ---- the empty leaf's rest chunk: I (up to S) then the continuation ----
    NP.EmptyLeafChunk(rer, r1, cont, inp, ls[e], R2, titer, tcont, gm', gm);
    var IE := LT.TreeLeaves(titer, LG.GMReset(gidl, gme), inp, WP.Forward);
    var CE' := LT.TreeLeaves(tcont, gme, inp, WP.Forward);
    assert R2 == IE + CE';
    var C := LT.TreeLeaves(tcont, gmP, inp, WP.Forward);
    // the frame facts, stated as the instances the head comparison needs
    assert |IE| == |I| && |CE'| == |C| by {
      LL.GMUpdateAgreeOutside(LG.Reset(gidl), idx, gme, gmP, S);
      LL.TreeLeavesFrameOutside(titer, LG.GMReset(gidl, gme), gm', inp, WP.Forward, S);
      LL.TreeLeavesFrameOutside(tcont, gme, gmP, inp, WP.Forward, S);
    }
    assert |IE| > 0 ==> IE[0].0 == I[0].0 && LL.GmAgreeOutside(IE[0].1, I[0].1, S) by {
      LL.GMUpdateAgreeOutside(LG.Reset(gidl), idx, gme, gmP, S);
      LL.TreeLeavesFrameOutside(titer, LG.GMReset(gidl, gme), gm', inp, WP.Forward, S);
    }
    assert |CE'| > 0 ==> CE'[0].0 == C[0].0 && LL.GmAgreeOutside(CE'[0].1, C[0].1, S) by {
      LL.TreeLeavesFrameOutside(tcont, gme, gmP, inp, WP.Forward, S);
    }

    assert {:split_here} true;
    // ---- the engine shape's leaves ----
    var tcin := LT.Choice(LT.GroupActionT(LG.Reset(gidl), titer), LT.GroupActionT(LG.Reset(gidl), NP.Chain(p, tcont)));
    var Lcin := LT.TreeLeaves(tcin, gm, inp, WP.Forward);
    assert Lcin == I + C by {
      NP.ChainLeaves(p, tcont, gm', inp);
      assert LG.GMUpdate(LG.Reset(gidl), idx, gm) == gm';
      assert LT.TreeLeaves(LT.GroupActionT(LG.Reset(gidl), titer), gm, inp, WP.Forward) == I;
      assert LT.TreeLeaves(LT.GroupActionT(LG.Reset(gidl), NP.Chain(p, tcont)), gm, inp, WP.Forward)
          == LT.TreeLeaves(NP.Chain(p, tcont), gm', inp, WP.Forward);
      assert LT.TreeLeaves(NP.Chain(p, tcont), gm', inp, WP.Forward) == C;
    }

    assert {:split_here} true;
    // ---- heads ----
    var rc := LT.TreeRes(tcin, gm, inp, WP.Forward);
    var rp := LT.TreeRes(tplus, gm, inp, WP.Forward);
    assert rc == LT.HdError(Lcin) && rp == LT.HdError(Lplus) by {
      LT.FirstTreeLeaf(tcin, gm, inp, WP.Forward);
      LT.FirstTreeLeaf(tplus, gm, inp, WP.Forward);
    }
    assert {:split_here} true;   // (P1a) W14: this section was one 179 M batch
    assert R23 == R2 + R3 && R1 == I1;
    assert Lplus == I1 + (R2 + R3);
    assert (I1 + I3) + C == I1 + (I3 + C);
    assert Lcin == I1 + (I3 + C);
    assert {:split_here} true;
    if |I1| > 0 {
      assert Lplus[0] == I1[0] && Lcin[0] == I1[0];
      LL.GmAgreeOutsideRefl(I1[0].1, S);
    } else {
      assert Lplus == R2 + R3;
      assert Lcin == I3 + C;
      assert I == I3;
      assert |R2| == |I3 + C|;
      assert {:split_here} true;
      if |R2| > 0 {
        assert Lplus[0] == R2[0];
        assert Lcin[0] == (I3 + C)[0];
        if |IE| > 0 {
          assert R2[0] == IE[0] && (I3 + C)[0] == I3[0] && I3[0] == I[0];
        } else {
          assert R2[0] == CE'[0] && (I3 + C)[0] == C[0];
        }
      } else {
        assert |I3| == 0 && |C| == 0 && |IE| == 0 && |CE'| == 0;
        assert Lcin == [];
        assert {:split_here} true;
        // every remaining chunk is empty
        NP.FlatMapEmptyChunks(post, fchk);
        forall i, y | 0 <= i < |post| && frest(post[i], y) ensures y == [] {
          var l := post[i];
          assert l == ls[e + 1 + i];
          if l.0 != inp {
            NP.ChkChunk(rer, rest, inp, l, y);
            assert fchk(l, y);
          } else {
            NP.EmptyLeafChunk(rer, r1, cont, inp, l, y, titer, tcont, gm', gm);
            NP.TreeLeavesLenIndep(titer, LG.GMReset(gidl, l.1), gm', inp);
            NP.TreeLeavesLenIndep(tcont, l.1, gmP, inp);
          }
        }
        NP.FlatMapAllEmpty(post, frest, R3);
        assert Lplus == [];
      }
    }
  }

  // ===========================================================================
  // The None case: the guard is false, the engine's skip arm is `Mismatch`, and the spec's forced iteration
  // has no empty leaf at `inp`.
  // ===========================================================================

  /** The engine tree of a guarded greedy plus whose guard failed. */
  ghost function CdnDeadTree(gidl: seq<LG.GroupId>, titer: LT.Tree): LT.Tree {
    LT.Choice(LT.GroupActionT(LG.Reset(gidl), titer), LT.Mismatch)
  }

  /** No empty path of `r1` at `inp`: every leaf of `r1`'s tree is strictly past `inp`, so the iteration's
      `Acheck(inp)` passes every chunk, and the spec's forced-iteration tree has EXACTLY the iteration arm's
      leaves. */
  lemma CdnPlusPriorityNone(rer: LW.RegExpRecord, r1: L.Regex, cont: LS.Actions, inp: LC.Input, gm: LG.GroupMap,
                            S: set<LG.GroupId>, tplus: LT.Tree, titer: LT.Tree)
    requires EL.PikeLkRegexRec(r1) && EL.PikeLkActionsRec(cont)
    requires LL.LkBodiesInS(r1, S)
    requires NP.FirstEmptyPathL(rer, r1, inp).None?
    requires LS.IsTree(rer, [LS.Areg(L.Quantified(true, 1, LN.Inf, r1))] + cont, inp, gm, WP.Forward, tplus)
    requires LS.IsTree(rer, [LS.Areg(r1), LS.Acheck(inp), LS.Areg(L.Quantified(true, 0, LN.Inf, r1))] + cont,
                       inp, LG.GMReset(L.DefGroups(r1), gm), WP.Forward, titer)
    ensures var tdead := CdnDeadTree(L.DefGroups(r1), titer);
            LT.TreeLeaves(tdead, gm, inp, WP.Forward) == LT.TreeLeaves(tplus, gm, inp, WP.Forward)
            && LT.TreeRes(tdead, gm, inp, WP.Forward) == LT.TreeRes(tplus, gm, inp, WP.Forward)
  {
    var gidl := L.DefGroups(r1);
    var gm' := LG.GMReset(gidl, gm);
    var idx := LC.Idx(inp);
    var Q1 := L.Quantified(true, 1, LN.Inf, r1);
    var Q0 := L.Quantified(true, 0, LN.Inf, r1);
    var A := [LS.Areg(r1)];
    var rest := [LS.Areg(Q0)] + cont;
    var chk := [LS.Acheck(inp)] + rest;
    var iterActs := [LS.Areg(r1), LS.Acheck(inp), LS.Areg(Q0)] + cont;
    assert iterActs == A + chk;
    var plusActs := [LS.Areg(Q1)] + cont;
    assert plusActs[0] == LS.Areg(Q1) && plusActs[1..] == cont;

    // ---- the spec tree: Reset; tc ----
    assert tplus.GroupActionT? && tplus.g == LG.Reset(gidl);
    var tc := tplus.t;
    assert [LS.Areg(r1), LS.Areg(Q0)] + cont == A + rest;
    assert LS.IsTree(rer, A + rest, inp, gm', WP.Forward, tc);
    var Lplus := LT.TreeLeaves(tc, gm', inp, WP.Forward);
    assert LT.TreeLeaves(tplus, gm, inp, WP.Forward) == Lplus;

    assert {:split_here} true;
    // ---- r1's leaves: none sits at inp ----
    EL.PikeLkActionsRecConsIff(LS.Areg(r1), []);
    assert EL.PikeLkActionsRec(A);
    LL.LkActsInSCons(LS.Areg(r1), [], S);
    assert LL.LkActsInS(A, S);
    assert A == [LS.Areg(r1)] + [];
    var tr1 := FU.ComputeTr(rer, A, inp, gm', WP.Forward);
    FU.ComputeTrIsTree(rer, A, inp, gm', WP.Forward);
    var ls := LT.TreeLeaves(tr1, gm', inp, WP.Forward);
    NP.EmptyLeavesA(rer, A, inp, gm', S, tr1);
    NP.FirstAtSpec(ls, inp);
    assert NP.FirstAt(ls, inp).None?;
    assert forall i :: 0 <= i < |ls| ==> SS.StrictSuffix(ls[i].0, inp, WP.Forward);

    assert {:split_here} true;
    // ---- both flat-maps, chunk by chunk ----
    var frest := EQ.ActFromLeafFn(rer, rest, WP.Forward);
    var fchk := EQ.ActFromLeafFn(rer, chk, WP.Forward);
    EQ.ActFromLeafDeterm(rer, WP.Forward, rest);
    EQ.ActFromLeafDeterm(rer, WP.Forward, chk);
    EQ.LeavesConcat(rer, inp, gm', WP.Forward, A, rest, tc, tr1);
    assert FM.FlatMapRel(ls, frest, Lplus);
    var I := LT.TreeLeaves(titer, gm', inp, WP.Forward);
    EQ.LeavesConcat(rer, inp, gm', WP.Forward, A, chk, titer, tr1);
    assert FM.FlatMapRel(ls, fchk, I);
    forall i, y | 0 <= i < |ls| && fchk(ls[i], y) ensures frest(ls[i], y) {
      NP.ChkChunk(rer, rest, inp, ls[i], y);
    }
    NP.FlatMapEqOn(ls, frest, fchk, Lplus, I);
    assert Lplus == I;

    assert {:split_here} true;
    // ---- the engine shape's leaves ----
    var tdead := CdnDeadTree(gidl, titer);
    assert LG.GMUpdate(LG.Reset(gidl), idx, gm) == gm';
    assert LT.TreeLeaves(LT.GroupActionT(LG.Reset(gidl), titer), gm, inp, WP.Forward) == I;
    assert LT.TreeLeaves(LT.Mismatch, gm, inp, WP.Forward) == [];
    assert LT.TreeLeaves(tdead, gm, inp, WP.Forward) == I + [];
    assert I + [] == I;
    LT.FirstTreeLeaf(tdead, gm, inp, WP.Forward);
    LT.FirstTreeLeaf(tplus, gm, inp, WP.Forward);
  }

  // ===========================================================================
  // Rung A, one statement: the engine's skip arm is decided by the guard.
  // ===========================================================================

  /** The engine tree of a guarded greedy plus: the CIN shape when the guard passes, the dead shape when it
      does not. */
  ghost function CdnTree(rer: LW.RegExpRecord, r1: L.Regex, inp: LC.Input, titer: LT.Tree, tcont: LT.Tree): LT.Tree {
    var gidl := L.DefGroups(r1);
    match NP.FirstEmptyPathL(rer, r1, inp)
    case Some(p) => LT.Choice(LT.GroupActionT(LG.Reset(gidl), titer), LT.GroupActionT(LG.Reset(gidl), NP.Chain(p, tcont)))
    case None => CdnDeadTree(gidl, titer)
  }

  lemma CdnPlusPriority(rer: LW.RegExpRecord, r1: L.Regex, cont: LS.Actions, inp: LC.Input, gm: LG.GroupMap,
                        S: set<LG.GroupId>, tplus: LT.Tree, titer: LT.Tree, tcont: LT.Tree)
    requires EL.PikeLkRegexRec(r1) && EL.PikeLkActionsRec(cont)
    requires LL.LkBodiesInS(r1, S)
    requires LS.IsTree(rer, [LS.Areg(L.Quantified(true, 1, LN.Inf, r1))] + cont, inp, gm, WP.Forward, tplus)
    requires LS.IsTree(rer, [LS.Areg(r1), LS.Acheck(inp), LS.Areg(L.Quantified(true, 0, LN.Inf, r1))] + cont,
                       inp, LG.GMReset(L.DefGroups(r1), gm), WP.Forward, titer)
    requires LS.IsTree(rer, cont, inp, gm, WP.Forward, tcont)
    ensures var rc := LT.TreeRes(CdnTree(rer, r1, inp, titer, tcont), gm, inp, WP.Forward);
            var rp := LT.TreeRes(tplus, gm, inp, WP.Forward);
            (rc.Some? <==> rp.Some?)
            && (rc.Some? ==> rc.value.0 == rp.value.0 && LL.GmAgreeOutside(rc.value.1, rp.value.1, S))
  {
    if NP.FirstEmptyPathL(rer, r1, inp).Some? {
      CdnPlusPrioritySome(rer, r1, cont, inp, gm, S, tplus, titer, tcont);
    } else {
      CdnPlusPriorityNone(rer, r1, cont, inp, gm, S, tplus, titer);
      var rp := LT.TreeRes(tplus, gm, inp, WP.Forward);
      if rp.Some? { LL.GmAgreeOutsideRefl(rp.value.1, S); }
    }
  }

  /** The CIN theorem is the Some case (CINullable gives an empty path everywhere). */
  lemma CinIsSomeCase(rer: LW.RegExpRecord, r1: L.Regex, inp: LC.Input)
    requires NUL.CINullableL(r1)
    ensures NP.FirstEmptyPathL(rer, r1, inp).Some?
  {
    assert NP.FirstEmptyPathA(rer, [], inp) == Some([]);
    NP.CINullableEmptyPathA(rer, r1, [], inp);
    assert [LS.Areg(r1)] + [] == [LS.Areg(r1)];
  }

  // ===========================================================================
  // The BoolTreeLk form the constructions consume (machine A's `ATR_QuantCin…`, cin-walk's head lemma).
  // ===========================================================================

  lemma CdnPlusPriorityBool(rer: LW.RegExpRecord, r1: L.Regex, cont: LS.Actions, inp: LC.Input, b: BS.LoopBool,
                            S: set<LG.GroupId>, t: LT.Tree, ti: LT.Tree, tcont: LT.Tree)
    requires EL.PikeLkRegexRec(r1) && EL.PikeLkActionsRec(cont)
    requires EL.CinHeadL(true, 1, LN.Inf, r1)   // the plus head's atom: the caller's fragment of the quantifier
    requires LL.LkBodiesInS(r1, S)
    requires NB.EncOk(cont, inp, b)
    requires EL.BoolTreeLk(rer, [LS.Areg(L.Quantified(true, 1, LN.Inf, r1))] + cont, inp, b, t)
    requires EL.BoolTreeLk(rer, [LS.Areg(r1), LS.Acheck(inp), LS.Areg(L.Quantified(true, 0, LN.Inf, r1))] + cont, inp, BS.CannotExit, ti)
    requires EL.BoolTreeLk(rer, cont, inp, b, tcont)
    ensures NP.ResAgreeAtOutside(CdnTree(rer, r1, inp, ti, tcont), t, inp, S)
  {
    var gidl := L.DefGroups(r1);
    var plus := L.Quantified(true, 1, LN.Inf, r1);
    var star := L.Quantified(true, 0, LN.Inf, r1);
    EL.PikeLkRecQuantZero(true, LN.Inf, r1);    // the star's head: vacuous at min == 0
    var pacts := [LS.Areg(plus)] + cont;
    var ia := [LS.Areg(r1), LS.Acheck(inp), LS.Areg(star)] + cont;
    assert EL.PikeLkRegexRec(plus) && EL.PikeLkRegexRec(star);
    assert EL.PikeLkActionRec(LS.Areg(plus)) && EL.PikeLkActionRec(LS.Areg(star))
        && EL.PikeLkActionRec(LS.Areg(r1)) && EL.PikeLkActionRec(LS.Acheck(inp));
    EL.PikeLkActionsRecConsIff(LS.Areg(plus), cont);
    EL.PikeLkActionsRecConsIff(LS.Areg(star), cont);
    EL.PikeLkActionsRecConsIff(LS.Acheck(inp), [LS.Areg(star)] + cont);
    EL.PikeLkActionsRecConsIff(LS.Areg(r1), [LS.Acheck(inp)] + ([LS.Areg(star)] + cont));
    assert ia == [LS.Areg(r1)] + ([LS.Acheck(inp)] + ([LS.Areg(star)] + cont));
    assert EL.PikeLkActionsRec(pacts) && EL.PikeLkActionsRec(ia);
    NB.EncOkConsPlus(plus, cont, inp, b);
    NB.EncOkEncodable(cont, inp, b);
    NB.EncOkIter(r1, star, cont, inp);
    assert {:split_here} true;
    var tcdn := CdnTree(rer, r1, inp, ti, tcont);
    forall gm: LG.GroupMap
      ensures var rc := LT.TreeRes(tcdn, gm, inp, WP.Forward);
              var rp := LT.TreeRes(t, gm, inp, WP.Forward);
              (rc.Some? <==> rp.Some?)
              && (rc.Some? ==> rc.value.0 == rp.value.0 && LL.GmAgreeOutside(rc.value.1, rp.value.1, S))
    {
      NB.EncTreeIsTree(rer, pacts, inp, b, t, gm);
      NB.EncTreeIsTree(rer, ia, inp, BS.CannotExit, ti, LG.GMReset(gidl, gm));
      NB.EncTreeIsTree(rer, cont, inp, b, tcont, gm);
      CdnPlusPriority(rer, r1, cont, inp, gm, S, t, ti, tcont);
    }
  }

  /** The None case on its own, WITHOUT a continuation tree: when the guard fails the constructions have no
      `tcont` to offer (the Some case reads it off the spec tree along the empty path, and there is none). */
  lemma CdnPlusPriorityBoolNone(rer: LW.RegExpRecord, r1: L.Regex, cont: LS.Actions, inp: LC.Input, b: BS.LoopBool,
                                S: set<LG.GroupId>, t: LT.Tree, ti: LT.Tree)
    requires EL.PikeLkRegexRec(r1) && EL.PikeLkActionsRec(cont)
    requires EL.CinHeadL(true, 1, LN.Inf, r1)
    requires LL.LkBodiesInS(r1, S)
    requires NB.EncOk(cont, inp, b)
    requires NP.FirstEmptyPathL(rer, r1, inp).None?
    requires EL.BoolTreeLk(rer, [LS.Areg(L.Quantified(true, 1, LN.Inf, r1))] + cont, inp, b, t)
    requires EL.BoolTreeLk(rer, [LS.Areg(r1), LS.Acheck(inp), LS.Areg(L.Quantified(true, 0, LN.Inf, r1))] + cont, inp, BS.CannotExit, ti)
    ensures NP.ResAgreeAtOutside(CdnDeadTree(L.DefGroups(r1), ti), t, inp, S)
  {
    var gidl := L.DefGroups(r1);
    var plus := L.Quantified(true, 1, LN.Inf, r1);
    var star := L.Quantified(true, 0, LN.Inf, r1);
    EL.PikeLkRecQuantZero(true, LN.Inf, r1);
    var pacts := [LS.Areg(plus)] + cont;
    var ia := [LS.Areg(r1), LS.Acheck(inp), LS.Areg(star)] + cont;
    assert EL.PikeLkRegexRec(plus) && EL.PikeLkRegexRec(star);
    assert EL.PikeLkActionRec(LS.Areg(plus)) && EL.PikeLkActionRec(LS.Areg(star))
        && EL.PikeLkActionRec(LS.Areg(r1)) && EL.PikeLkActionRec(LS.Acheck(inp));
    EL.PikeLkActionsRecConsIff(LS.Areg(plus), cont);
    EL.PikeLkActionsRecConsIff(LS.Areg(star), cont);
    EL.PikeLkActionsRecConsIff(LS.Acheck(inp), [LS.Areg(star)] + cont);
    EL.PikeLkActionsRecConsIff(LS.Areg(r1), [LS.Acheck(inp)] + ([LS.Areg(star)] + cont));
    assert ia == [LS.Areg(r1)] + ([LS.Acheck(inp)] + ([LS.Areg(star)] + cont));
    assert EL.PikeLkActionsRec(pacts) && EL.PikeLkActionsRec(ia);
    NB.EncOkConsPlus(plus, cont, inp, b);
    NB.EncOkEncodable(cont, inp, b);
    NB.EncOkIter(r1, star, cont, inp);
    assert {:split_here} true;
    var tdead := CdnDeadTree(gidl, ti);
    forall gm: LG.GroupMap
      ensures var rc := LT.TreeRes(tdead, gm, inp, WP.Forward);
              var rp := LT.TreeRes(t, gm, inp, WP.Forward);
              (rc.Some? <==> rp.Some?)
              && (rc.Some? ==> rc.value.0 == rp.value.0 && LL.GmAgreeOutside(rc.value.1, rp.value.1, S))
    {
      NB.EncTreeIsTree(rer, pacts, inp, b, t, gm);
      NB.EncTreeIsTree(rer, ia, inp, BS.CannotExit, ti, LG.GMReset(gidl, gm));
      CdnPlusPriorityNone(rer, r1, cont, inp, gm, S, t, ti);
      var rp := LT.TreeRes(t, gm, inp, WP.Forward);
      if rp.Some? { LL.GmAgreeOutsideRefl(rp.value.1, S); }
    }
  }
}
