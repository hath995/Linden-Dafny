// L5 CAPTURES — BRICK F3: the MIRROR-ORACLE transport (non-circular).
//
// The forward keystone applied to the FLIP-reversed body needs its oracle
// premise: the mirrored view `MirrorView(ov, n)` must be CORRECT for the
// flipped looks-map over `Reverse(str)`. This was exactly the crux that sank
// the old route (B5's `MirrorOracleOk` needed the no-flip tree mirror, which
// needed the mirror-oracle — circular, and the mirror was vacuous anyway).
//
// With the flip it is a straight composition, per look id:
//   bit of MirrorView at (k, lid)
//     == bit of ov at (n-k, lid)                        [`MirrorViewGet`]
//     <==> body's BACKWARD walk at n-k succeeds          [original `OracleOkAt`]
//     <==> FlipRevL(body)'s FORWARD walk at k succeeds   [`BackBodyGmTieFlip`
//                                                         None-iff — F2,
//                                                         oracle-free]
// which is precisely `OracleOkAt` for the flipped entry (its `LkDir` is
// Forward). No induction, no circularity.
//
// Deliverables: `MirrorOracleColsOk` (whole-view column correctness over the
// reversed string) and `ColsOkToSuffix` (columns => the `OracleOkSuffix` form
// the keystone consumes, at any starting position).
/** F3: `MirrorView(ov)` is a correct oracle for the FLIPPED looks-map. */
module LindenElkFlipOracle {
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
  import CD = LindenCloseDisc
  import LOr = Oracle
  import AR = LindenElkActionsRep
  import LL = LindenElkLookLeaves
  import TR = LindenElkTreeRep
  import MIR = LindenElkMirror
  import T = LindenElkTranslate
  import OE = LindenElkOracleEntry
  import FR = LindenElkFlipRev
  import FM = LindenElkFlipMirror
  import FD = LindenElkFlipDisc

  // ===========================================================================
  // The flipped looks-map
  // ===========================================================================

  /** `qm2`'s table is exactly `qm`'s with each entry kind-flipped and its body
      flip-reversed (same lids — the flip and the reversal both keep them). */
  ghost predicate FlipQmTie(qm: AR.QMap, qm2: AR.QMap) {
    (forall lid: int :: lid in qm2.looks <==> lid in qm.looks)
    && (forall lid: int :: lid in qm.looks ==>
          qm2.looks[lid] == (FR.FlipLk(qm.looks[lid].0), FM.FlipRevL(qm.looks[lid].1)))
  }

  /** The v1 scope, per table entry: lookbehind-flavoured, `GroupOkLB` body,
      group-free negative sub-bodies, dup-free gids. */
  ghost predicate QmBodiesLBOk(qm: AR.QMap) {
    forall lid: int :: lid in qm.looks ==>
      && (qm.looks[lid].0.LookBehind? || qm.looks[lid].0.NegLookBehind?)
      && SD.GroupOkLB(qm.looks[lid].1)
      && FD.NegBodiesGroupFree(qm.looks[lid].1)
      && CD.NoDupG(L.DefGroups(qm.looks[lid].1))
  }

  // ===========================================================================
  // The per-position transport
  // ===========================================================================

  /** One mirrored column: the flipped table's `OracleOkAt` at position `k` of
      the REVERSED string, from the original's at position `n-k`. */
  lemma MirrorOracleOkAtCp(rer: LW.RegExpRecord, qm: AR.QMap, qm2: AR.QMap,
                           str: string, k: nat)
    requires |qm.ov| == |str| + 1
    requires qm2.ov == MIR.MirrorView(qm.ov, |str|)
    requires FlipQmTie(qm, qm2) && QmBodiesLBOk(qm)
    requires k <= |str|
    requires LL.OracleOkAt(rer, qm, T.InputAt(str, |str| - k))
    ensures |LC.Reverse(str)| == |str|
    ensures LL.OracleOkAt(rer, qm2, T.InputAt(LC.Reverse(str), k))
  {
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
    assert n == |inp.pref| + |inp.next|;
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
      assert L.LkDir(lk) == WP.Backward && L.LkDir(lk2) == WP.Forward;
      // the mirrored bit IS the original bit
      MIR.MirrorViewGet(qm.ov, n, cp, lid);
      assert LOr.view_get_oracle(qm2.ov, k, lid) == LOr.view_get_oracle(qm.ov, cp, lid);
      // the original bit is the backward walk
      LL.OracleOkAtGet(rer, qm, inp, lid, lk, r1);
      // the backward walk is the flipped forward walk (F2, oracle-free)
      FD.BackBodyGmTieFlip(rer, r1, inp, n);
    }
  }

  /** Whole-view transport: the flipped table's columns are correct over the
      REVERSED string wherever the original's are over `str`. */
  lemma MirrorOracleColsOk(rer: LW.RegExpRecord, qm: AR.QMap, qm2: AR.QMap, str: string)
    requires |qm.ov| == |str| + 1
    requires qm2.ov == MIR.MirrorView(qm.ov, |str|)
    requires FlipQmTie(qm, qm2) && QmBodiesLBOk(qm)
    requires OE.OracleColsOk(rer, qm, str)
    ensures OE.OracleColsOk(rer, qm2, LC.Reverse(str))
  {
    LS.ReverseLength(str);
    var rstr := LC.Reverse(str);
    forall k: int | 0 <= k <= |rstr|
      ensures LL.OracleOkAt(rer, qm2, T.InputAt(rstr, k))
    {
      assert LL.OracleOkAt(rer, qm, T.InputAt(str, |str| - k));
      MirrorOracleOkAtCp(rer, qm, qm2, str, k as nat);
    }
  }

  // ===========================================================================
  // Columns => the Suffix form the keystone consumes
  // ===========================================================================

  /** Per-column correctness gives `OracleOkSuffix` from ANY starting position:
      every input the forward walk can reach from `InputAt(str, cp)` is itself
      a string position (`SuffixIsInputAt`), and each has a correct column. */
  lemma ColsOkToSuffix(rer: LW.RegExpRecord, qm: AR.QMap, str: string, cp: nat)
    requires cp <= |str|
    requires OE.OracleColsOk(rer, qm, str)
    ensures LL.OracleOkSuffix(rer, qm, T.InputAt(str, cp))
  {
    var inp0 := T.InputAt(str, cp);
    forall inp: LC.Input | inp == inp0 || SSx.IsStrictSuffix(inp, inp0, WP.Forward)
      ensures LL.OracleOkAt(rer, qm, inp)
    {
      if inp == inp0 {
        assert LL.OracleOkAt(rer, qm, T.InputAt(str, cp));
      } else {
        assert SSx.StrictSuffixForward(inp, inp0.next, inp0.pref);
        OE.SuffixIsInputAt(str, cp, inp);
        var m: nat :| cp < m <= |str| && inp == T.InputAt(str, m);
        assert LL.OracleOkAt(rer, qm, T.InputAt(str, m));
      }
    }
  }
}
