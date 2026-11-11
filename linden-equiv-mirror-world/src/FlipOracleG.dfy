// G1(b) follow-ons (W3): the direction-generic F2 tie and the
// mirror-oracle transport WITHOUT `QmBodiesLBOk`.
//
// First verified against flip-oracle's deps + flip-oracle's own .doo, with
// FlipMirrorG.dfy as a co-source (see W3-G1b.md).

module LindenElkFlipOracleG {
  import opened Std.Wrappers
  import LW = WarblreRegExpRecord
  import WP = WarblrePrimitives
  import LC = Chars
  import LG = Groups
  import L = Regex
  import LS = Semantics
  import LT = Tree
  import FU = FunctionalUtils
  import SSx = StrictSuffix
  import SD = LindenSpanDuality
  import NUL = LindenElkNullable
  import CD = LindenCloseDisc
  import LOr = Oracle
  import AR = LindenElkActionsRep
  import LL = LindenElkLookLeaves
  import TR = LindenElkTreeRep
  import MIR = LindenElkMirror
  import T = LindenElkTranslate
  import OE = LindenElkOracleEntry
  import EL = LindenElkEntryLk
  import TRM = LindenTreeResMirror
  import FR = LindenElkFlipRev
  import FM = LindenElkFlipMirror
  import FD = LindenElkFlipDisc
  import FO = LindenElkFlipOracle
  import G = LindenElkFlipMirrorG

  // ===========================================================================
  // F2, generic: the Someness tie (all the oracle needs) — NoBackrefL ONLY
  // ===========================================================================

  /** A body's walk in `dir` succeeds iff its flip-reversal's walk in
      `OppDir(dir)` over the swapped window succeeds. No fragment premise but
      backreference-freedom: no close discipline, no dup-free gids, no
      negative-body or nulled-plus restriction. */
  lemma BodySomeTieFlipG(rer: LW.RegExpRecord, tr: L.Regex, inp: LC.Input, dir: WP.Direction)
    requires SD.NoBackrefL(tr)
    ensures LT.TreeRes(FU.ComputeTr(rer, [LS.Areg(tr)], inp, LG.Empty, dir), LG.Empty, inp, dir).Some?
        <==> LT.TreeRes(FU.ComputeTr(rer, [LS.Areg(FM.FlipRevL(tr))], SD.SwapInput(inp), LG.Empty,
                                     G.OppDir(dir)),
                        LG.Empty, SD.SwapInput(inp), G.OppDir(dir)).Some?
  {
    var tB := FU.ComputeTr(rer, [LS.Areg(tr)], inp, LG.Empty, dir);
    var tF := FU.ComputeTr(rer, [LS.Areg(FM.FlipRevL(tr))], SD.SwapInput(inp), LG.Empty, G.OppDir(dir));
    assert SD.NoBackrefActs([LS.Areg(tr)]);
    G.ComputeTrReverseG(rer, [LS.Areg(tr)], inp, LG.Empty, LG.Empty, dir);
    assert FM.FlipRevActs([LS.Areg(tr)]) == [LS.Areg(FM.FlipRevL(tr))];
    assert G.TreeMirrorRelG(tB, tF);
    G.TreeResSomeMirrorG(tB, tF, LG.Empty, LG.Empty, inp, dir);
  }

  // ===========================================================================
  // F2, generic: the VALUE tie (BackBodyGmTieFlip without the LB pin)
  // ===========================================================================

  /** `FD.GroupOkLBNegFreePikeLk` with `GroupOkLB` weakened to `NoBackrefL`:
      `PikeLkRegexRec` admits either look direction already. */
  lemma NoBackrefNegFreePikeLk(tr: L.Regex)
    requires SD.NoBackrefL(tr)
    requires NUL.NoNulledPlusL(tr)
    ensures EL.PikeLkRegexRec(tr)
    decreases tr
  {
    match tr
    case Disjunction(r1, r2) => NoBackrefNegFreePikeLk(r1); NoBackrefNegFreePikeLk(r2);
    case Sequence(r1, r2) => NoBackrefNegFreePikeLk(r1); NoBackrefNegFreePikeLk(r2);
    case Quantified(_, _, _, r1) => NoBackrefNegFreePikeLk(r1);
    case Group(_, r1) => NoBackrefNegFreePikeLk(r1);
    case LookaroundR(lk, r1) =>
      NoBackrefNegFreePikeLk(r1);
    case _ =>
  }

  lemma BodyGmTieFlipG(rer: LW.RegExpRecord, tr: L.Regex, inp: LC.Input, n: nat, dir: WP.Direction)
    requires SD.NoBackrefL(tr)
    requires NUL.NoNulledPlusL(tr)   // §2.5b interim (only to reach PikeLkRegexRec)
    requires CD.NoDupG(L.DefGroups(tr))
    requires n == |inp.pref| + |inp.next|
    ensures var tB := FU.ComputeTr(rer, [LS.Areg(tr)], inp, LG.Empty, dir);
            var tF := FU.ComputeTr(rer, [LS.Areg(FM.FlipRevL(tr))], SD.SwapInput(inp),
                                   LG.Empty, G.OppDir(dir));
            var rb := LT.TreeRes(tB, LG.Empty, inp, dir);
            var rf := LT.TreeRes(tF, LG.Empty, SD.SwapInput(inp), G.OppDir(dir));
            && (rb.None? <==> rf.None?)
            && (rb.Some? ==>
                  && rf.Some?
                  && rf.value.0 == SD.SwapInput(rb.value.0)
                  && TRM.GmInBounds(rb.value.1, n)
                  && rf.value.1 == TRM.MirrorGm(rb.value.1, n))
  {
    var tB := FU.ComputeTr(rer, [LS.Areg(tr)], inp, LG.Empty, dir);
    var tF := FU.ComputeTr(rer, [LS.Areg(FM.FlipRevL(tr))], SD.SwapInput(inp),
                           LG.Empty, G.OppDir(dir));
    assert SD.NoBackrefActs([LS.Areg(tr)]);
    G.ComputeTrReverseG(rer, [LS.Areg(tr)], inp, LG.Empty, LG.Empty, dir);
    assert FM.FlipRevActs([LS.Areg(tr)]) == [LS.Areg(FM.FlipRevL(tr))];
    assert G.TreeMirrorRelG(tB, tF);
    NoBackrefNegFreePikeLk(tr);
    FD.ComputeTrCloseDiscF(rer, tr, inp, LG.Empty, dir);
    assert TRM.GmInBounds(LG.Empty, n);
    assert TRM.OpenSubset(LG.Empty, {});
    assert TRM.MirrorGm(LG.Empty, n) == LG.Empty;
    G.TreeResMirrorG(tB, tF, LG.Empty, inp, dir, n, {});
  }

  /** INSTANCE: `FD.BackBodyGmTieFlip`'s exact statement, from the generic tie. */
  lemma BackBodyGmTieFlipViaG(rer: LW.RegExpRecord, tr: L.Regex, inp: LC.Input, n: nat)
    requires SD.GroupOkLB(tr)
    requires NUL.NoNulledPlusL(tr)
    requires CD.NoDupG(L.DefGroups(tr))
    requires n == |inp.pref| + |inp.next|
    ensures var tB := FU.ComputeTr(rer, [LS.Areg(tr)], inp, LG.Empty, WP.Backward);
            var tF := FU.ComputeTr(rer, [LS.Areg(FM.FlipRevL(tr))], SD.SwapInput(inp),
                                   LG.Empty, WP.Forward);
            var rb := LT.TreeRes(tB, LG.Empty, inp, WP.Backward);
            var rf := LT.TreeRes(tF, LG.Empty, SD.SwapInput(inp), WP.Forward);
            && (rb.None? <==> rf.None?)
            && (rb.Some? ==>
                  && rf.Some?
                  && rf.value.0 == SD.SwapInput(rb.value.0)
                  && TRM.GmInBounds(rb.value.1, n)
                  && rf.value.1 == TRM.MirrorGm(rb.value.1, n))
  {
    SD.GroupOkLBIsNoBackref(tr);
    assert G.OppDir(WP.Backward) == WP.Forward;
    BodyGmTieFlipG(rer, tr, inp, n, WP.Backward);
  }

  /** W2's own direction helper, copied verbatim (W2Keystone.dfy:59) — a
      DIFFERENT function symbol from `G.OppDir`, same definition.
      (W2Keystone.dfy is the W2 endgame subagent's scratch keystone, see
      linden-equiv/endgame/W2-two-roots.md; it took `HbSome` / `HbVal` as two
      bodiless hypothesis lemmas, which `HbSomeDischarged` / `HbValDischarged`
      below prove with the same statements.) */
  function OppDirW2(d: WP.Direction): WP.Direction {
    match d
    case Forward => WP.Backward
    case Backward => WP.Forward
  }

  /** W2's hypothesis `HbSome` (W2Keystone.dfy:73), statement verbatim with W2's
      `OppDir`, PROVED for BOTH directions. The bridge is one definitional step:
      `OppDirW2(dir) == G.OppDir(dir)`. */
  lemma HbSomeDischarged(rer: LW.RegExpRecord, tr: L.Regex, inp: LC.Input, dir: WP.Direction)
    requires SD.NoBackrefL(tr)
    ensures LT.TreeRes(FU.ComputeTr(rer, [LS.Areg(tr)], inp, LG.Empty, dir),
                       LG.Empty, inp, dir).Some?
        <==> LT.TreeRes(FU.ComputeTr(rer, [LS.Areg(FM.FlipRevL(tr))], SD.SwapInput(inp),
                                     LG.Empty, OppDirW2(dir)),
                        LG.Empty, SD.SwapInput(inp), OppDirW2(dir)).Some?
  {
    assert OppDirW2(dir) == G.OppDir(dir);
    BodySomeTieFlipG(rer, tr, inp, dir);
  }

  /** W2's hypothesis `HbVal` (W2Keystone.dfy:85), statement verbatim, PROVED.
      (W2's `HbSome` is `BodySomeTieFlipG` verbatim: W2's `OppDir` has the same
      definition as `G.OppDir`.) */
  lemma HbValDischarged(rer: LW.RegExpRecord, tr: L.Regex, inp: LC.Input, n: nat)
    requires SD.NoBackrefL(tr)
    requires NUL.NoNulledPlusL(tr)
    requires CD.NoDupG(L.DefGroups(tr))
    requires n == |inp.pref| + |inp.next|
    ensures var tB := FU.ComputeTr(rer, [LS.Areg(tr)], inp, LG.Empty, WP.Backward);
            var tF := FU.ComputeTr(rer, [LS.Areg(FM.FlipRevL(tr))], SD.SwapInput(inp),
                                   LG.Empty, WP.Forward);
            var rb := LT.TreeRes(tB, LG.Empty, inp, WP.Backward);
            var rf := LT.TreeRes(tF, LG.Empty, SD.SwapInput(inp), WP.Forward);
            && (rb.None? <==> rf.None?)
            && (rb.Some? ==>
                  && rf.Some?
                  && rf.value.0 == SD.SwapInput(rb.value.0)
                  && TRM.GmInBounds(rb.value.1, n)
                  && rf.value.1 == TRM.MirrorGm(rb.value.1, n))
  {
    assert G.OppDir(WP.Backward) == WP.Forward;
    BodyGmTieFlipG(rer, tr, inp, n, WP.Backward);
  }

  // ===========================================================================
  // F3, generic: the mirror-oracle transport, mixed kinds, NoBackrefL only
  // ===========================================================================

  /** The generic per-row scope: backreference-free bodies. Nothing else. */
  ghost predicate QmBodiesNoBackref(qm: AR.QMap) {
    forall lid: int :: lid in qm.looks ==> SD.NoBackrefL(qm.looks[lid].1)
  }

  lemma QmBodiesLBOkNoBackref(qm: AR.QMap)
    requires FO.QmBodiesLBOk(qm)
    ensures QmBodiesNoBackref(qm)
  {
    reveal FO.QmBodiesLBOk();
    forall lid: int | lid in qm.looks ensures SD.NoBackrefL(qm.looks[lid].1) {
      SD.GroupOkLBIsNoBackref(qm.looks[lid].1);
    }
  }

  lemma MirrorOracleOkAtCpG(rer: LW.RegExpRecord, qm: AR.QMap, qm2: AR.QMap,
                            str: string, k: nat)
    requires |qm.ov| == |str| + 1
    requires qm2.ov == MIR.MirrorView(qm.ov, |str|)
    requires FO.FlipQmTie(qm, qm2) && QmBodiesNoBackref(qm)
    requires k <= |str|
    requires LL.OracleOkAt(rer, qm, T.InputAt(str, |str| - k))
    ensures |LC.Reverse(str)| == |str|
    ensures LL.OracleOkAt(rer, qm2, T.InputAt(LC.Reverse(str), k))
  {
    hide *;
    reveal LL.OracleOkAt, FO.FlipQmTie, QmBodiesNoBackref, TR.CpOf, T.InputAt, SD.SwapInput, MIR.Mirror;
    var n := |str|;
    var cp := n - k;
    LS.ReverseLength(str);
    var rstr := LC.Reverse(str);
    var inp := T.InputAt(str, cp);
    var inp2 := T.InputAt(rstr, k);
    SD.InputAtSwap(str, cp);
    assert inp2 == SD.SwapInput(inp);
    T.ReverseProps(str[..cp]);
    assert TR.CpOf(inp) == cp;
    T.ReverseProps(rstr[..k]);
    assert TR.CpOf(inp2) == k;
    assert {:split_here} true;
    forall lid: int, lk2: L.Lookaround, r12: L.Regex
      | lid in qm2.looks && qm2.looks[lid] == (lk2, r12)
      ensures LOr.view_get_oracle(qm2.ov, TR.CpOf(inp2), lid)
          <==> LT.TreeRes(FU.ComputeTr(rer, [LS.Areg(r12)], inp2, LG.Empty, L.LkDir(lk2)),
                          LG.Empty, inp2, L.LkDir(lk2)).Some?
    {
      assert lid in qm.looks;
      var lk := qm.looks[lid].0;
      var r1 := qm.looks[lid].1;
      assert lk2 == FR.FlipLk(lk) && r12 == FM.FlipRevL(r1);
      // ANY kind: the flipped row walks the opposite direction
      G.FlipLkDirPos(lk);
      var ld := L.LkDir(lk);
      assert L.LkDir(lk2) == G.OppDir(ld);
      MIR.MirrorViewGet(qm.ov, n, cp, lid);
      assert LOr.view_get_oracle(qm2.ov, k, lid) == LOr.view_get_oracle(qm.ov, cp, lid);
      LL.OracleOkAtGet(rer, qm, inp, lid, lk, r1);
      assert SD.NoBackrefL(r1);
      assert {:split_here} true;
      BodySomeTieFlipG(rer, r1, inp, ld);
    }
  }

  /** `FO.MirrorOracleColsOk` with `QmBodiesLBOk` replaced by `QmBodiesNoBackref`:
      the flipped table's columns are correct over the reversed string, for a
      table of MIXED look kinds. */
  lemma MirrorOracleColsOkG(rer: LW.RegExpRecord, qm: AR.QMap, qm2: AR.QMap, str: string)
    requires |qm.ov| == |str| + 1
    requires qm2.ov == MIR.MirrorView(qm.ov, |str|)
    requires FO.FlipQmTie(qm, qm2) && QmBodiesNoBackref(qm)
    requires OE.OracleColsOk(rer, qm, str)
    ensures OE.OracleColsOk(rer, qm2, LC.Reverse(str))
  {
    LS.ReverseLength(str);
    var rstr := LC.Reverse(str);
    forall k: int | 0 <= k <= |rstr|
      ensures LL.OracleOkAt(rer, qm2, T.InputAt(rstr, k))
    {
      assert LL.OracleOkAt(rer, qm, T.InputAt(str, |str| - k));
      MirrorOracleOkAtCpG(rer, qm, qm2, str, k as nat);
    }
  }

  /** INSTANCE: the one-way original's call shape. */
  lemma MirrorOracleColsOkViaG(rer: LW.RegExpRecord, qm: AR.QMap, qm2: AR.QMap, str: string)
    requires |qm.ov| == |str| + 1
    requires qm2.ov == MIR.MirrorView(qm.ov, |str|)
    requires FO.FlipQmTie(qm, qm2) && FO.QmBodiesLBOk(qm)
    requires OE.OracleColsOk(rer, qm, str)
    ensures OE.OracleColsOk(rer, qm2, LC.Reverse(str))
  {
    QmBodiesLBOkNoBackref(qm);
    MirrorOracleColsOkG(rer, qm, qm2, str);
  }
}
