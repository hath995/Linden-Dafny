// G3b spec side (W8): the first empty path of `r` at `cp` vs the first empty
// path of `FXR(r)` at `n - cp`, and the stamp readout through the mirror.
//
// Package linden-equiv-stamp-mirror; first verified against
// linden-equiv-flip-statics's deps + its own .doo (linden-equiv/endgame/W8-G3b-stamp-mirror.md).
//
// Shape of the result:
//   * the PATHS are not mirror images as sequences (SeqLevelCon / SeqLevelQuant
//     below are concrete witnesses);
//   * their EFFECTS on a group map are: an empty path at `c` is a "patch"
//     (clear C, pin D at (c, c)), the patch of `FXR(r)` at `n - cp` has the SAME
//     (D, C) as the patch of `r` at `cp` (EmptyEffMirror), and a patch commutes
//     with `MirrorGm` (PatchMirror);
//   * so `StampApply` commutes with the mirror (StampApplyMirror), under
//     `TransWf` + `CapUnique` of the quantifier body and the ov / qcp / bodies
//     relation of the mirrored world.
module LindenElkStampMirror {
  import opened Std.Wrappers
  import LC = Chars
  import LG = Groups
  import L = Regex
  import R = RegElkRegex
  import RA = Anchors
  import LOr = Oracle
  import AI = ArrayInterp
  import T = LindenElkTranslate
  import AR = LindenElkActionsRep
  import TR = LindenElkTreeRep
  import NP = LindenElkNulledPlus
  import PIV = LindenElkPikeInv
  import MIR = LindenElkMirror
  import TRM = LindenTreeResMirror
  import SD = LindenSpanDuality
  import FR = LindenElkFlipRev
  import FM = LindenElkFlipMirror
  import FST = LindenElkFlipStatics
  import LBV = LindenLookBehindValue
  import BGM = LindenBackGmMirror
  import AReg = Array_Regs

  // ===========================================================================
  // 1. The closed form of an empty path's effect
  // ===========================================================================

  /** Every group of `D` pinned to the empty range at `c`. */
  ghost function Pin(D: set<nat>, c: nat): LG.GroupMap {
    map g | g in D :: LG.Range(c, Some(c))
  }

  /** Clear `C`, then pin `D` at `c`. */
  ghost function Patch(gm: LG.GroupMap, C: set<nat>, D: set<nat>, c: nat): LG.GroupMap {
    (gm - C) + Pin(D, c)
  }

  /** The (defined, cleared) group sets of the first empty path, computed on the
      regex with `FirstEmptyPathR`'s case split (same choices, no action order). */
  ghost function EmptyEff(qm: AR.QMap, re: R.regex, inp: LC.Input): Option<(set<nat>, set<nat>)>
    decreases re
  {
    match re
    case Re_empty => Some(({}, {}))
    case Re_character(_) => None
    case Re_anchor(a) => if RA.is_satisfied(a, TR.CtxOf(inp), RA.Forward) then Some(({}, {})) else None
    case Re_alt(r1, r2) =>
      if EmptyEff(qm, r1, inp).Some? then EmptyEff(qm, r1, inp) else EmptyEff(qm, r2, inp)
    case Re_con(r1, r2) =>
      var e1 := EmptyEff(qm, r1, inp);
      var e2 := EmptyEff(qm, r2, inp);
      if e1.Some? && e2.Some? then Some((e1.value.0 + e2.value.0, e1.value.1 + e2.value.1)) else None
    case Re_quant(nul, qid, q, r1) =>
      if q.min == 0 then Some(({}, {}))
      else
        var e1 := EmptyEff(qm, r1, inp);
        if e1.Some? then Some((e1.value.0, PIV.CapIds(r1) - e1.value.0)) else None
    case Re_capture(cid, r1) =>
      var e1 := EmptyEff(qm, r1, inp);
      if e1.Some? then Some((e1.value.0 + (if cid >= 0 then {cid as nat} else {}), e1.value.1)) else None
    case Re_lookaround(lid, lk, r1) =>
      var bit := LOr.view_get_oracle(qm.ov, TR.CpOf(inp), lid);
      if (if AR.PositiveL(T.TrLookaround(lk)) then bit else !bit) then Some(({}, {})) else None
  }

  lemma ApplyPathAppend(a: seq<LG.GroupAction>, b: seq<LG.GroupAction>, c: nat, gm: LG.GroupMap)
    ensures NP.ApplyPath(a + b, c, gm) == NP.ApplyPath(b, c, NP.ApplyPath(a, c, gm))
    decreases |a|
  {
    if |a| == 0 {
      assert a + b == b;
    } else {
      assert (a + b)[0] == a[0];
      assert (a + b)[1..] == a[1..] + b;
      ApplyPathAppend(a[1..], b, c, LG.GMUpdate(a[0], c, gm));
    }
  }

  lemma PatchEmpty(gm: LG.GroupMap, c: nat)
    ensures Patch(gm, {}, {}, c) == gm
  {
    var p := Patch(gm, {}, {}, c);
    assert forall g :: g in p <==> g in gm;
    assert forall g :: g in p ==> p[g] == gm[g];
  }

  lemma PatchCompose(gm: LG.GroupMap, C1: set<nat>, D1: set<nat>, C2: set<nat>, D2: set<nat>, c: nat)
    requires D1 * C2 == {}
    ensures Patch(Patch(gm, C1, D1, c), C2, D2, c) == Patch(gm, C1 + C2, D1 + D2, c)
  {
    var lhs := Patch(Patch(gm, C1, D1, c), C2, D2, c);
    var rhs := Patch(gm, C1 + C2, D1 + D2, c);
    forall g: nat ensures (g in lhs <==> g in rhs) && (g in lhs ==> lhs[g] == rhs[g]) {
      assert g !in D1 * C2;
    }
  }

  /** One forced iteration: reset the body's groups, then the body's patch. */
  lemma PatchAfterReset(gm: LG.GroupMap, X: set<nat>, C1: set<nat>, D1: set<nat>, c: nat)
    requires C1 <= X && D1 <= X
    ensures Patch(gm - X, C1, D1, c) == Patch(gm, X - D1, D1, c)
  {
    var lhs := Patch(gm - X, C1, D1, c);
    var rhs := Patch(gm, X - D1, D1, c);
    forall g ensures (g in lhs <==> g in rhs) && (g in lhs ==> lhs[g] == rhs[g]) {}
  }

  lemma PatchIdem(gm: LG.GroupMap, S: set<nat>, D: set<nat>, c: nat)
    ensures Patch(Patch(gm, S, D, c), S, D, c) == Patch(gm, S, D, c)
  {
    var lhs := Patch(Patch(gm, S, D, c), S, D, c);
    var rhs := Patch(gm, S, D, c);
    forall g ensures (g in lhs <==> g in rhs) && (g in lhs ==> lhs[g] == rhs[g]) {}
  }

  /** `k >= 1` forced iterations of `[Reset(DG)] + p1`, where `p1`'s effect is
      the patch `(C1, D1)` inside `X == set(DG)`. */
  lemma RepeatEff(k: nat, DG: LG.GroupSet, p1: seq<LG.GroupAction>, X: set<nat>,
                  C1: set<nat>, D1: set<nat>, c: nat, gm: LG.GroupMap)
    requires k >= 1
    requires forall g: nat :: g in DG <==> g in X
    requires C1 <= X && D1 <= X
    requires forall gm': LG.GroupMap :: NP.ApplyPath(p1, c, gm') == Patch(gm', C1, D1, c)
    ensures NP.ApplyPath(TR.RepeatPath(k, [LG.Reset(DG)] + p1), c, gm) == Patch(gm, X - D1, D1, c)
    decreases k
  {
    var q := [LG.Reset(DG)] + p1;
    assert TR.RepeatPath(k, q) == q + TR.RepeatPath(k - 1, q);
    ApplyPathAppend(q, TR.RepeatPath(k - 1, q), c, gm);
    // one iteration
    assert q[0] == LG.Reset(DG) && q[1..] == p1;
    assert NP.ApplyPath(q, c, gm) == NP.ApplyPath(p1, c, LG.GMUpdate(LG.Reset(DG), c, gm));
    assert LG.GMUpdate(LG.Reset(DG), c, gm) == gm - X by {
      assert (set g | g in DG) == X;
    }
    PatchAfterReset(gm, X, C1, D1, c);
    var gm1 := Patch(gm, X - D1, D1, c);
    assert NP.ApplyPath(q, c, gm) == gm1;
    if k == 1 {
      assert TR.RepeatPath(0, q) == [];
    } else {
      RepeatEff(k - 1, DG, p1, X, C1, D1, c, gm1);
      PatchIdem(gm, X - D1, D1, c);
    }
  }

  /** THE closed form: the first empty path exists iff `EmptyEff` does, and
      applying it at `c` is the patch `EmptyEff` names. */
  lemma EmptyEffPath(qm: AR.QMap, re: R.regex, inp: LC.Input, c: nat, gm: LG.GroupMap)
    requires T.TransWf(re) && PIV.CapUnique(re)
    ensures TR.FirstEmptyPathR(qm, re, inp).Some? <==> EmptyEff(qm, re, inp).Some?
    ensures EmptyEff(qm, re, inp).Some? ==>
      var e := EmptyEff(qm, re, inp).value;
      e.0 <= PIV.CapIds(re) && e.1 <= PIV.CapIds(re) && e.0 * e.1 == {}
      && NP.ApplyPath(TR.FirstEmptyPathR(qm, re, inp).value, c, gm) == Patch(gm, e.1, e.0, c)
    decreases re
  {
    match re
    case Re_empty => PatchEmpty(gm, c);
    case Re_character(_) =>
    case Re_anchor(_) => PatchEmpty(gm, c);
    case Re_lookaround(_, _, _) => PatchEmpty(gm, c);
    case Re_alt(r1, r2) =>
      EmptyEffPath(qm, r1, inp, c, gm);
      EmptyEffPath(qm, r2, inp, c, gm);
    case Re_con(r1, r2) =>
      EmptyEffPath(qm, r1, inp, c, gm);
      if EmptyEff(qm, r1, inp).Some? && EmptyEff(qm, r2, inp).Some? {
        var p1 := TR.FirstEmptyPathR(qm, r1, inp).value;
        var e1 := EmptyEff(qm, r1, inp).value;
        var gm1 := NP.ApplyPath(p1, c, gm);
        EmptyEffPath(qm, r2, inp, c, gm1);
        var p2 := TR.FirstEmptyPathR(qm, r2, inp).value;
        var e2 := EmptyEff(qm, r2, inp).value;
        ApplyPathAppend(p1, p2, c, gm);
        assert e1.0 * e2.1 == {} by {
          assert PIV.CapIds(r1) * PIV.CapIds(r2) == {};
        }
        assert e2.0 * e1.1 == {} by {
          assert PIV.CapIds(r1) * PIV.CapIds(r2) == {};
        }
        PatchCompose(gm, e1.1, e1.0, e2.1, e2.0, c);
      } else {
        EmptyEffPath(qm, r2, inp, c, gm);
      }
    case Re_quant(nul, qid, q, r1) =>
      if q.min != 0 {
        EmptyEffPath(qm, r1, inp, c, gm);
        if EmptyEff(qm, r1, inp).Some? {
          var p1 := TR.FirstEmptyPathR(qm, r1, inp).value;
          var e1 := EmptyEff(qm, r1, inp).value;
          forall gm': LG.GroupMap
            ensures NP.ApplyPath(p1, c, gm') == Patch(gm', e1.1, e1.0, c)
          { EmptyEffPath(qm, r1, inp, c, gm'); }
          var DG := L.DefGroups(T.Translate(r1));
          PIV.DefGroupsCapIds(r1);
          RepeatEff(q.min as nat, DG, p1, PIV.CapIds(r1), e1.1, e1.0, c, gm);
        }
      } else {
        PatchEmpty(gm, c);
      }
    case Re_capture(cid, r1) =>
      var g: nat := cid as nat;
      var gm0 := LG.GMOpen(c, g, gm);
      EmptyEffPath(qm, r1, inp, c, gm0);
      if EmptyEff(qm, r1, inp).Some? {
        var p1 := TR.FirstEmptyPathR(qm, r1, inp).value;
        var e1 := EmptyEff(qm, r1, inp).value;
        var path := [LG.Open(g)] + p1 + [LG.Close(g)];
        assert TR.FirstEmptyPathR(qm, re, inp).value == path;
        ApplyPathAppend([LG.Open(g)] + p1, [LG.Close(g)], c, gm);
        ApplyPathAppend([LG.Open(g)], p1, c, gm);
        assert NP.ApplyPath([LG.Open(g)], c, gm) == gm0 by {
          assert [LG.Open(g)][1..] == [];
        }
        var gm1 := NP.ApplyPath(p1, c, gm0);
        assert gm1 == Patch(gm0, e1.1, e1.0, c);
        assert g !in e1.0 && g !in e1.1;
        assert g in gm1 && gm1[g] == LG.Range(c, None);
        assert NP.ApplyPath([LG.Close(g)], c, gm1) == LG.GMClose(c, g, gm1) by {
          assert [LG.Close(g)][1..] == [];
        }
        var lhs := LG.GMClose(c, g, gm1);
        var rhs := Patch(gm, e1.1, e1.0 + {g}, c);
        forall h ensures (h in lhs <==> h in rhs) && (h in lhs ==> lhs[h] == rhs[h]) {}
        assert lhs == rhs;
      }
  }

  // ===========================================================================
  // 2. FXR leaves the effect unchanged (alternatives keep their order;
  //    concatenation's union is commutative; quantifier/capture sets are
  //    FXR-invariant; anchors and oracle bits read the mirrored position)
  // ===========================================================================

  lemma CapIdsFXR(r: R.regex)
    ensures PIV.CapIds(FST.FXR(r)) == PIV.CapIds(r)
  {
    FST.XRevIsRevRENested(r);
    LBV.CapIdsRevRE(r);
    FST.FlipCapIds(FST.XRV(r));
  }

  lemma CapUniqueFXR(r: R.regex)
    requires PIV.CapUnique(r)
    ensures PIV.CapUnique(FST.FXR(r))
  {
    FST.XRevIsRevRENested(r);
    LBV.CapUniqueRevRE(r);
    FST.FlipCapUnique(FST.XRV(r));
  }

  lemma AnchorSwapCtx(a: R.anchor, inp: LC.Input)
    ensures RA.is_satisfied(MIR.SwapAnchor(a), TR.CtxOf(SD.SwapInput(inp)), RA.Forward)
        <==> RA.is_satisfied(a, TR.CtxOf(inp), RA.Forward)
  {}

  lemma EmptyEffMirror(qm: AR.QMap, qm': AR.QMap, re: R.regex, str: string, cp: nat)
    requires cp <= |str| && |qm.ov| == |str| + 1
    requires qm'.ov == MIR.MirrorView(qm.ov, |str|)
    ensures |LC.Reverse(str)| == |str|
    ensures EmptyEff(qm', FST.FXR(re), T.InputAt(LC.Reverse(str), |str| - cp))
         == EmptyEff(qm, re, T.InputAt(str, cp))
    decreases re
  {
    var n := |str|;
    SD.InputAtSwap(str, cp);
    var inp := T.InputAt(str, cp);
    var inp' := T.InputAt(LC.Reverse(str), n - cp);
    assert inp' == SD.SwapInput(inp);
    match re
    case Re_empty =>
    case Re_character(_) =>
    case Re_anchor(a) =>
      assert FST.FXR(re) == R.Re_anchor(MIR.SwapAnchor(a));
      AnchorSwapCtx(a, inp);
    case Re_alt(r1, r2) =>
      assert FST.FXR(re) == R.Re_alt(FST.FXR(r1), FST.FXR(r2));
      EmptyEffMirror(qm, qm', r1, str, cp);
      EmptyEffMirror(qm, qm', r2, str, cp);
    case Re_con(r1, r2) =>
      assert FST.FXR(re) == R.Re_con(FST.FXR(r2), FST.FXR(r1));
      EmptyEffMirror(qm, qm', r1, str, cp);
      EmptyEffMirror(qm, qm', r2, str, cp);
      var e1 := EmptyEff(qm, r1, inp);
      var e2 := EmptyEff(qm, r2, inp);
      if e1.Some? && e2.Some? {
        assert e2.value.0 + e1.value.0 == e1.value.0 + e2.value.0;
        assert e2.value.1 + e1.value.1 == e1.value.1 + e2.value.1;
      }
    case Re_quant(nul, qid, q, r1) =>
      assert FST.FXR(re) == R.Re_quant(nul, qid, q, FST.FXR(r1));
      EmptyEffMirror(qm, qm', r1, str, cp);
      CapIdsFXR(r1);
    case Re_capture(cid, r1) =>
      assert FST.FXR(re) == R.Re_capture(cid, FST.FXR(r1));
      EmptyEffMirror(qm, qm', r1, str, cp);
    case Re_lookaround(lid, lk, r1) =>
      assert FST.FXR(re) == R.Re_lookaround(lid, FR.FlipLkRE(lk), FST.FXR(r1));
      SD.IdxInputAt(str, cp);
      assert TR.CpOf(inp) == cp;
      assert TR.CpOf(inp') == n - cp by {
        assert inp'.pref == inp.next == str[cp..];
      }
      MIR.MirrorViewGet(qm.ov, n, cp, lid);
      assert AR.PositiveL(T.TrLookaround(FR.FlipLkRE(lk))) == AR.PositiveL(T.TrLookaround(lk));
  }

  // ===========================================================================
  // 3. A patch commutes with the (ordered) group-map mirror
  // ===========================================================================

  lemma PatchMirror(gm: LG.GroupMap, C: set<nat>, D: set<nat>, c: nat, n: nat)
    requires c <= n && TRM.GmInBounds(gm, n)
    ensures TRM.GmInBounds(Patch(gm, C, D, c), n)
    ensures TRM.MirrorGm(Patch(gm, C, D, c), n) == Patch(TRM.MirrorGm(gm, n), C, D, n - c)
  {
    var p := Patch(gm, C, D, c);
    assert TRM.GmInBounds(p, n);
    var lhs := TRM.MirrorGm(p, n);
    var rhs := Patch(TRM.MirrorGm(gm, n), C, D, n - c);
    forall h ensures (h in lhs <==> h in rhs) && (h in lhs ==> lhs[h] == rhs[h]) {}
  }

  // ===========================================================================
  // 4. THE MIRROR LEMMA (path level, effect form)
  // ===========================================================================

  lemma FirstEmptyPathMirror(qm: AR.QMap, qm': AR.QMap, re: R.regex, str: string, cp: nat, gm: LG.GroupMap)
    requires T.TransWf(re) && PIV.CapUnique(re)
    requires cp <= |str| && |qm.ov| == |str| + 1
    requires qm'.ov == MIR.MirrorView(qm.ov, |str|)
    requires TRM.GmInBounds(gm, |str|)
    ensures T.TransWf(FST.FXR(re)) && |LC.Reverse(str)| == |str|
    ensures var n := |str|;
            var p := TR.FirstEmptyPathR(qm, re, T.InputAt(str, cp));
            var p' := TR.FirstEmptyPathR(qm', FST.FXR(re), T.InputAt(LC.Reverse(str), n - cp));
            (p.Some? <==> p'.Some?)
            && (p.Some? ==>
                  TRM.GmInBounds(NP.ApplyPath(p.value, cp, gm), n)
                  && TRM.MirrorGm(NP.ApplyPath(p.value, cp, gm), n)
                     == NP.ApplyPath(p'.value, n - cp, TRM.MirrorGm(gm, n)))
  {
    var n := |str|;
    FST.TranslateFlipXRev(re);
    CapUniqueFXR(re);
    SD.ReverseLength(str);
    var inp := T.InputAt(str, cp);
    var inp' := T.InputAt(LC.Reverse(str), n - cp);
    EmptyEffMirror(qm, qm', re, str, cp);
    EmptyEffPath(qm, re, inp, cp, gm);
    var gmM := TRM.MirrorGm(gm, n);
    EmptyEffPath(qm', FST.FXR(re), inp', n - cp, gmM);
    if EmptyEff(qm, re, inp).Some? {
      var e := EmptyEff(qm, re, inp).value;
      PatchMirror(gm, e.1, e.0, cp, n);
    }
  }

  // ===========================================================================
  // 5. StampApply commutes with the mirror
  // ===========================================================================

  lemma StampApplyMirror(qm: AR.QMap, qm': AR.QMap, str: string, qid: nat,
                         qcp: seq<int>, qcp': seq<int>, r1: R.regex, gm: LG.GroupMap)
    requires T.TransWf(r1) && PIV.CapUnique(r1)
    requires (qid as int) in qm.bodies && qm.bodies[qid as int] == r1
    requires (qid as int) in qm'.bodies && qm'.bodies[qid as int] == FST.FXR(r1)
    requires |qm.ov| == |str| + 1 && qm'.ov == MIR.MirrorView(qm.ov, |str|)
    requires AI.get_idx(qcp', qid) == MIR.MirrorCpVal(AI.get_idx(qcp, qid), |str|)
    requires TRM.GmInBounds(gm, |str|)
    ensures T.TransWf(FST.FXR(r1)) && |LC.Reverse(str)| == |str|
    ensures TRM.GmInBounds(PIV.StampApply(qm, str, qid, qcp, r1, gm), |str|)
    ensures TRM.MirrorGm(PIV.StampApply(qm, str, qid, qcp, r1, gm), |str|)
         == PIV.StampApply(qm', LC.Reverse(str), qid, qcp', FST.FXR(r1), TRM.MirrorGm(gm, |str|))
  {
    var n := |str|;
    FST.TranslateFlipXRev(r1);
    SD.ReverseLength(str);
    var rstr := LC.Reverse(str);
    var v := AI.get_idx(qcp, qid);
    if 0 <= v <= n {
      assert PIV.StampReady(qm, str, qid, qcp);
      assert PIV.StampReady(qm', rstr, qid, qcp');
      var cp: nat := v as nat;
      assert PIV.StampCp(qcp, qid) == cp;
      assert PIV.StampCp(qcp', qid) == n - cp;
      var DG := L.DefGroups(T.Translate(r1));
      var DG' := L.DefGroups(T.Translate(FST.FXR(r1)));
      FM.FlipRevLDefGroupsSet(T.Translate(r1));
      assert forall g :: g in DG <==> g in DG';
      TRM.GMResetMirror(gm, DG, DG', n);
      var gmR := LG.GMReset(DG, gm);
      FirstEmptyPathMirror(qm, qm', r1, str, cp, gmR);
    } else {
      assert !PIV.StampReady(qm, str, qid, qcp);
      assert !PIV.StampReady(qm', rstr, qid, qcp');
    }
  }

  // ===========================================================================
  // 6. Falsifiers of the SEQUENCE-level statement (why the lemma is effect-level)
  // ===========================================================================

  /** Sequence reversal with Open/Close swapped: the naive "mirror of a path". */
  function RevSwap(p: seq<LG.GroupAction>): seq<LG.GroupAction>
    decreases |p|
  {
    if |p| == 0 then []
    else RevSwap(p[1..]) + [match p[0]
                             case Open(g) => LG.Close(g)
                             case Close(g) => LG.Open(g)
                             case Reset(gl) => LG.Reset(gl)]
  }

  /** `()()`: the mirrored path is a different sequence (r2's actions first). */
  lemma SeqLevelCon(qm: AR.QMap, qm': AR.QMap, str: string)
    ensures var re := R.Re_con(R.Re_capture(1, R.Re_empty), R.Re_capture(2, R.Re_empty));
            T.TransWf(re) && T.TransWf(FST.FXR(re)) && |LC.Reverse(str)| == |str|
            && TR.FirstEmptyPathR(qm, re, T.InputAt(str, 0))
               == Some([LG.Open(1), LG.Close(1), LG.Open(2), LG.Close(2)])
            && TR.FirstEmptyPathR(qm', FST.FXR(re), T.InputAt(LC.Reverse(str), |str|))
               == Some([LG.Open(2), LG.Close(2), LG.Open(1), LG.Close(1)])
  {
    SD.ReverseLength(str);
    var c1 := R.Re_capture(1, R.Re_empty);
    var c2 := R.Re_capture(2, R.Re_empty);
    var re := R.Re_con(c1, c2);
    assert FST.FXR(c1) == c1;
    assert FST.FXR(c2) == c2;
    assert FST.FXR(re) == R.Re_con(c2, c1);
    var i := T.InputAt(str, 0);
    var i' := T.InputAt(LC.Reverse(str), |str|);
    assert TR.FirstEmptyPathR(qm, R.Re_empty, i) == Some([]);
    assert TR.FirstEmptyPathR(qm', R.Re_empty, i') == Some([]);
    assert TR.FirstEmptyPathR(qm, c1, i) == Some([LG.Open(1)] + [] + [LG.Close(1)]);
    assert TR.FirstEmptyPathR(qm, c2, i) == Some([LG.Open(2)] + [] + [LG.Close(2)]);
    assert TR.FirstEmptyPathR(qm', c1, i') == Some([LG.Open(1)] + [] + [LG.Close(1)]);
    assert TR.FirstEmptyPathR(qm', c2, i') == Some([LG.Open(2)] + [] + [LG.Close(2)]);
    assert [LG.Open(1)] + [] + [LG.Close(1)] == [LG.Open(1), LG.Close(1)];
    assert [LG.Open(2)] + [] + [LG.Close(2)] == [LG.Open(2), LG.Close(2)];
    assert TR.FirstEmptyPathR(qm, re, i)
        == Some(TR.FirstEmptyPathR(qm, c1, i).value + TR.FirstEmptyPathR(qm, c2, i).value);
    assert TR.FirstEmptyPathR(qm', FST.FXR(re), i')
        == Some(TR.FirstEmptyPathR(qm', c2, i').value + TR.FirstEmptyPathR(qm', c1, i').value);
    assert [LG.Open(1), LG.Close(1)] + [LG.Open(2), LG.Close(2)]
        == [LG.Open(1), LG.Close(1), LG.Open(2), LG.Close(2)];
    assert [LG.Open(2), LG.Close(2)] + [LG.Open(1), LG.Close(1)]
        == [LG.Open(2), LG.Close(2), LG.Open(1), LG.Close(1)];
  }

  /** `(?:())+` (min 1): the mirrored path equals the original, and is NOT the
      reversal; the reversal even has a different effect (it clears group 1). */
  lemma SeqLevelQuant(qm: AR.QMap, qm': AR.QMap, str: string, gm: LG.GroupMap)
    ensures var body := R.Re_capture(1, R.Re_empty);
            var re := R.Re_quant(R.CINullable, 0, R.CountedQuant(1, None, true), body);
            var p := [LG.Reset([1]), LG.Open(1), LG.Close(1)];
            T.TransWf(re) && T.TransWf(FST.FXR(re)) && |LC.Reverse(str)| == |str|
            && TR.FirstEmptyPathR(qm, re, T.InputAt(str, 0)) == Some(p)
            && TR.FirstEmptyPathR(qm', FST.FXR(re), T.InputAt(LC.Reverse(str), |str|)) == Some(p)
            && RevSwap(p) == [LG.Open(1), LG.Close(1), LG.Reset([1])]
            && 1 in NP.ApplyPath(p, 0, gm)
            && 1 !in NP.ApplyPath(RevSwap(p), 0, gm)
  {
    SD.ReverseLength(str);
    var body := R.Re_capture(1, R.Re_empty);
    var re := R.Re_quant(R.CINullable, 0, R.CountedQuant(1, None, true), body);
    assert FST.FXR(re) == re;
    assert T.Translate(body) == L.Group(1, L.Epsilon);
    assert L.DefGroups(T.Translate(body)) == [1];
    var p := [LG.Reset([1]), LG.Open(1), LG.Close(1)];
    var i := T.InputAt(str, 0);
    var i' := T.InputAt(LC.Reverse(str), |str|);
    assert TR.FirstEmptyPathR(qm, R.Re_empty, i) == Some([]);
    assert TR.FirstEmptyPathR(qm', R.Re_empty, i') == Some([]);
    assert TR.FirstEmptyPathR(qm, body, i) == Some([LG.Open(1)] + [] + [LG.Close(1)]);
    assert TR.FirstEmptyPathR(qm', body, i') == Some([LG.Open(1)] + [] + [LG.Close(1)]);
    assert [LG.Open(1)] + [] + [LG.Close(1)] == [LG.Open(1), LG.Close(1)];
    assert [LG.Reset([1])] + [LG.Open(1), LG.Close(1)] == p;
    assert TR.RepeatPath(1, p) == p + TR.RepeatPath(0, p);
    assert TR.RepeatPath(1, p) == p;
    assert TR.FirstEmptyPathR(qm, re, i)
        == Some(TR.RepeatPath(1, [LG.Reset(L.DefGroups(T.Translate(body)))] + TR.FirstEmptyPathR(qm, body, i).value));
    assert TR.FirstEmptyPathR(qm', re, i')
        == Some(TR.RepeatPath(1, [LG.Reset(L.DefGroups(T.Translate(body)))] + TR.FirstEmptyPathR(qm', body, i').value));
    assert p[1..] == [LG.Open(1), LG.Close(1)];
    assert p[1..][1..] == [LG.Close(1)];
    assert p[1..][1..][1..] == [];
    assert RevSwap(p[1..][1..]) == [LG.Open(1)];
    assert RevSwap(p[1..]) == [LG.Open(1), LG.Close(1)];
    assert RevSwap(p) == [LG.Open(1), LG.Close(1), LG.Reset([1])];
    // effects at 0
    var g1 := LG.GMReset([1], gm);
    var g2 := LG.GMOpen(0, 1, g1);
    var g3 := LG.GMClose(0, 1, g2);
    assert NP.ApplyPath(p, 0, gm) == NP.ApplyPath(p[1..], 0, g1);
    assert NP.ApplyPath(p[1..], 0, g1) == NP.ApplyPath(p[1..][1..], 0, g2);
    assert NP.ApplyPath(p[1..][1..], 0, g2) == NP.ApplyPath(p[1..][1..][1..], 0, g3);
    assert NP.ApplyPath(p, 0, gm) == g3;
    assert 1 in g3;
    var q := RevSwap(p);
    var h1 := LG.GMOpen(0, 1, gm);
    var h2 := LG.GMClose(0, 1, h1);
    var h3 := LG.GMReset([1], h2);
    assert q[1..] == [LG.Close(1), LG.Reset([1])];
    assert q[1..][1..] == [LG.Reset([1])];
    assert q[1..][1..][1..] == [];
    assert NP.ApplyPath(q, 0, gm) == NP.ApplyPath(q[1..], 0, h1);
    assert NP.ApplyPath(q[1..], 0, h1) == NP.ApplyPath(q[1..][1..], 0, h2);
    assert NP.ApplyPath(q[1..][1..], 0, h2) == NP.ApplyPath(q[1..][1..][1..], 0, h3);
    assert NP.ApplyPath(q, 0, gm) == h3;
    assert 1 !in h3;
  }

  /** `CapUnique` is load-bearing: `()(?:(^)|){1}` with BOTH groups numbered 1,
      at cp 1 of "a". Real path: define 1, then the quantifier's Reset clears it.
      FXR path at 0 of the reversal: Reset first, then define. Effects differ. */
  lemma CapUniqueNeeded(qm: AR.QMap, qm': AR.QMap, gm: LG.GroupMap, gm': LG.GroupMap)
    ensures var alt := R.Re_alt(R.Re_capture(1, R.Re_anchor(R.BeginInput)), R.Re_empty);
            var re := R.Re_con(R.Re_capture(1, R.Re_empty),
                               R.Re_quant(R.CINullable, 0, R.CountedQuant(1, Some(1), true), alt));
            var str := "a";
            T.TransWf(re) && !PIV.CapUnique(re) && T.TransWf(FST.FXR(re)) && |LC.Reverse(str)| == 1
            && TR.FirstEmptyPathR(qm, re, T.InputAt(str, 1)) == Some([LG.Open(1), LG.Close(1), LG.Reset([1])])
            && TR.FirstEmptyPathR(qm', FST.FXR(re), T.InputAt(LC.Reverse(str), 0))
               == Some([LG.Reset([1]), LG.Open(1), LG.Close(1)])
            && 1 !in NP.ApplyPath([LG.Open(1), LG.Close(1), LG.Reset([1])], 1, gm)
            && 1 in NP.ApplyPath([LG.Reset([1]), LG.Open(1), LG.Close(1)], 0, gm')
  {
    var c1 := R.Re_capture(1, R.Re_empty);
    var alt := R.Re_alt(R.Re_capture(1, R.Re_anchor(R.BeginInput)), R.Re_empty);
    var q := R.Re_quant(R.CINullable, 0, R.CountedQuant(1, Some(1), true), alt);
    var re := R.Re_con(c1, q);
    var str := "a";
    SD.ReverseLength(str);
    assert LC.Reverse(str) == "a" by {
      assert LC.Reverse(str[1..]) == [];
    }
    assert PIV.CapIds(c1) * PIV.CapIds(q) == {1};
    var altF := R.Re_alt(R.Re_capture(1, R.Re_anchor(R.EndInput)), R.Re_empty);
    assert FST.FXR(alt) == altF;
    assert FST.FXR(q) == R.Re_quant(R.CINullable, 0, R.CountedQuant(1, Some(1), true), altF);
    assert FST.FXR(c1) == c1;
    var i := T.InputAt(str, 1);
    var i' := T.InputAt(LC.Reverse(str), 0);
    assert i.pref == "a" && i.next == "" by { assert LC.Reverse(str[..1]) == "a" by { assert LC.Reverse(str[..1][1..]) == []; } }
    assert i'.pref == "" && i'.next == "a";
    assert TR.CtxOf(i) == RA.CharContext(Some('a'), None);
    assert TR.CtxOf(i') == RA.CharContext(None, Some('a'));
    // real side
    assert TR.FirstEmptyPathR(qm, R.Re_anchor(R.BeginInput), i) == None;
    assert TR.FirstEmptyPathR(qm, R.Re_capture(1, R.Re_anchor(R.BeginInput)), i) == None;
    assert TR.FirstEmptyPathR(qm, R.Re_empty, i) == Some([]);
    assert TR.FirstEmptyPathR(qm, alt, i) == Some([]);
    assert T.Translate(alt) == L.Disjunction(L.Group(1, L.AnchorR(T.TrAnchor(R.BeginInput))), L.Epsilon);
    assert L.DefGroups(T.Translate(alt)) == [1];
    assert TR.RepeatPath(1, [LG.Reset([1])]) == [LG.Reset([1])] + TR.RepeatPath(0, [LG.Reset([1])]);
    assert [LG.Reset([1])] + [] == [LG.Reset([1])];
    assert TR.FirstEmptyPathR(qm, q, i) == Some([LG.Reset([1])]);
    assert TR.FirstEmptyPathR(qm, c1, i) == Some([LG.Open(1)] + [] + [LG.Close(1)]);
    assert [LG.Open(1)] + [] + [LG.Close(1)] + [LG.Reset([1])] == [LG.Open(1), LG.Close(1), LG.Reset([1])];
    // mirror side
    assert TR.FirstEmptyPathR(qm', R.Re_anchor(R.EndInput), i') == None;
    assert TR.FirstEmptyPathR(qm', R.Re_capture(1, R.Re_anchor(R.EndInput)), i') == None;
    assert TR.FirstEmptyPathR(qm', R.Re_empty, i') == Some([]);
    assert TR.FirstEmptyPathR(qm', altF, i') == Some([]);
    assert T.Translate(altF) == L.Disjunction(L.Group(1, L.AnchorR(T.TrAnchor(R.EndInput))), L.Epsilon);
    assert L.DefGroups(T.Translate(altF)) == [1];
    assert TR.FirstEmptyPathR(qm', FST.FXR(q), i') == Some([LG.Reset([1])]);
    assert TR.FirstEmptyPathR(qm', c1, i') == Some([LG.Open(1)] + [] + [LG.Close(1)]);
    assert [LG.Reset([1])] + ([LG.Open(1)] + [] + [LG.Close(1)]) == [LG.Reset([1]), LG.Open(1), LG.Close(1)];
    // effects
    var p := [LG.Open(1), LG.Close(1), LG.Reset([1])];
    var g1 := LG.GMOpen(1, 1, gm);
    var g2 := LG.GMClose(1, 1, g1);
    var g3 := LG.GMReset([1], g2);
    assert p[1..] == [LG.Close(1), LG.Reset([1])] && p[1..][1..] == [LG.Reset([1])] && p[1..][1..][1..] == [];
    assert NP.ApplyPath(p, 1, gm) == NP.ApplyPath(p[1..], 1, g1);
    assert NP.ApplyPath(p[1..], 1, g1) == NP.ApplyPath(p[1..][1..], 1, g2);
    assert NP.ApplyPath(p[1..][1..], 1, g2) == NP.ApplyPath(p[1..][1..][1..], 1, g3);
    assert 1 !in g3;
    var p' := [LG.Reset([1]), LG.Open(1), LG.Close(1)];
    var h1 := LG.GMReset([1], gm');
    var h2 := LG.GMOpen(0, 1, h1);
    var h3 := LG.GMClose(0, 1, h2);
    assert p'[1..] == [LG.Open(1), LG.Close(1)] && p'[1..][1..] == [LG.Close(1)] && p'[1..][1..][1..] == [];
    assert NP.ApplyPath(p', 0, gm') == NP.ApplyPath(p'[1..], 0, h1);
    assert NP.ApplyPath(p'[1..], 0, h1) == NP.ApplyPath(p'[1..][1..], 0, h2);
    assert NP.ApplyPath(p'[1..][1..], 0, h2) == NP.ApplyPath(p'[1..][1..][1..], 0, h3);
    assert 1 in h3;
  }

  // ===========================================================================
  // 7. LiveStampsGm / GmOfLiveR through the mirror
  // ===========================================================================

  /** An effect: clear `.0`, then overlay `.1`. */
  ghost function ApplyEff(e: (set<nat>, LG.GroupMap), gm: LG.GroupMap): LG.GroupMap {
    (gm - e.0) + e.1
  }

  ghost function SeqEff(e1: (set<nat>, LG.GroupMap), e2: (set<nat>, LG.GroupMap)): (set<nat>, LG.GroupMap) {
    (e1.0 + e2.0, (e1.1 - e2.0) + e2.1)
  }

  /** Overlay keys inside the cleared set, overlay ranges empty and in bounds. */
  ghost predicate EffOk(e: (set<nat>, LG.GroupMap), X: set<nat>, n: nat) {
    e.0 <= X
    && (forall g :: g in e.1 ==> g in e.0)
    && TRM.GmInBounds(e.1, n)
    && (forall g :: g in e.1 ==> e.1[g].endIdx == Some(e.1[g].startIdx))
  }

  ghost function StampEff(qm: AR.QMap, str: string, qid: nat, qcp: seq<int>, r1: R.regex): (set<nat>, LG.GroupMap)
  {
    if PIV.StampReady(qm, str, qid, qcp) then
      var cp := PIV.StampCp(qcp, qid);
      var e := EmptyEff(qm, qm.bodies[qid as int], T.InputAt(str, cp));
      if e.Some? then (PIV.CapIds(r1), Pin(e.value.0, cp)) else ({}, map[])
    else ({}, map[])
  }

  ghost function LiveEff(r: R.regex, qm: AR.QMap, str: string, qc: seq<int>, qcp: seq<int>, mx: int): (set<nat>, LG.GroupMap)
    decreases r
  {
    match r
    case Re_empty => ({}, map[])
    case Re_character(_) => ({}, map[])
    case Re_anchor(_) => ({}, map[])
    case Re_alt(r1, r2) => SeqEff(LiveEff(r1, qm, str, qc, qcp, mx), LiveEff(r2, qm, str, qc, qcp, mx))
    case Re_con(r1, r2) => SeqEff(LiveEff(r1, qm, str, qc, qcp, mx), LiveEff(r2, qm, str, qc, qcp, mx))
    case Re_quant(nul, qid, q, r1) =>
      var qv := AI.get_idx(qc, qid);
      if qv < mx then ({}, map[])
      else if qid >= 0 && AI.get_idx(qcp, qid) >= 0 then StampEff(qm, str, qid as nat, qcp, r1)
      else LiveEff(r1, qm, str, qc, qcp, qv)
    case Re_capture(cid, r1) => LiveEff(r1, qm, str, qc, qcp, mx)
    case Re_lookaround(_, _, _) => ({}, map[])
  }

  /** The QMap knows every (outside-looks) quantifier body of `r`. */
  ghost predicate BodiesOk(r: R.regex, qm: AR.QMap)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => BodiesOk(r1, qm) && BodiesOk(r2, qm)
    case Re_con(r1, r2) => BodiesOk(r1, qm) && BodiesOk(r2, qm)
    case Re_quant(_, qid, _, r1) =>
      (qid >= 0 ==> qid in qm.bodies && qm.bodies[qid] == r1) && BodiesOk(r1, qm)
    case Re_capture(_, r1) => BodiesOk(r1, qm)
    case _ => true
  }

  /** The mirrored QMap knows `FXR` of every such body. */
  ghost predicate BodiesFXR(r: R.regex, qm': AR.QMap)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => BodiesFXR(r1, qm') && BodiesFXR(r2, qm')
    case Re_con(r1, r2) => BodiesFXR(r1, qm') && BodiesFXR(r2, qm')
    case Re_quant(_, qid, _, r1) =>
      (qid >= 0 ==> qid in qm'.bodies && qm'.bodies[qid] == FST.FXR(r1)) && BodiesFXR(r1, qm')
    case Re_capture(_, r1) => BodiesFXR(r1, qm')
    case _ => true
  }

  lemma BodiesFXROk(r: R.regex, qm': AR.QMap)
    requires BodiesFXR(r, qm')
    ensures BodiesOk(FST.FXR(r), qm')
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      assert FST.FXR(r) == R.Re_alt(FST.FXR(r1), FST.FXR(r2));
      BodiesFXROk(r1, qm'); BodiesFXROk(r2, qm');
    case Re_con(r1, r2) =>
      assert FST.FXR(r) == R.Re_con(FST.FXR(r2), FST.FXR(r1));
      BodiesFXROk(r1, qm'); BodiesFXROk(r2, qm');
    case Re_quant(nul, qid, q, r1) =>
      assert FST.FXR(r) == R.Re_quant(nul, qid, q, FST.FXR(r1));
      BodiesFXROk(r1, qm');
    case Re_capture(cid, r1) =>
      assert FST.FXR(r) == R.Re_capture(cid, FST.FXR(r1));
      BodiesFXROk(r1, qm');
    case Re_lookaround(lid, lk, r1) =>
      assert FST.FXR(r) == R.Re_lookaround(lid, FR.FlipLkRE(lk), FST.FXR(r1));
    case Re_anchor(a) =>
      assert FST.FXR(r) == R.Re_anchor(MIR.SwapAnchor(a));
    case _ =>
  }

  /** The converse direction: a QMap that knows FXR(r)'s bodies knows `FXR` of r's. */
  lemma BodiesFXRFromOk(r: R.regex, qm': AR.QMap)
    requires BodiesOk(FST.FXR(r), qm')
    ensures BodiesFXR(r, qm')
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      assert FST.FXR(r) == R.Re_alt(FST.FXR(r1), FST.FXR(r2));
      BodiesFXRFromOk(r1, qm'); BodiesFXRFromOk(r2, qm');
    case Re_con(r1, r2) =>
      assert FST.FXR(r) == R.Re_con(FST.FXR(r2), FST.FXR(r1));
      BodiesFXRFromOk(r1, qm'); BodiesFXRFromOk(r2, qm');
    case Re_quant(nul, qid, q, r1) =>
      assert FST.FXR(r) == R.Re_quant(nul, qid, q, FST.FXR(r1));
      BodiesFXRFromOk(r1, qm');
    case Re_capture(cid, r1) =>
      assert FST.FXR(r) == R.Re_capture(cid, FST.FXR(r1));
      BodiesFXRFromOk(r1, qm');
    case _ =>
  }

  lemma BodiesOkOfQid(r: R.regex, qm: AR.QMap)
    requires PIV.QuantUnique(r)
    requires forall q: nat :: q in PIV.QuantIds(r) ==>
               (q as int) in qm.bodies && qm.bodies[q as int] == PIV.QidBody(r, q)
    ensures BodiesOk(r, qm)
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      forall q: nat | q in PIV.QuantIds(r1)
        ensures (q as int) in qm.bodies && qm.bodies[q as int] == PIV.QidBody(r1, q)
      { assert PIV.QidBody(r, q) == PIV.QidBody(r1, q); }
      forall q: nat | q in PIV.QuantIds(r2)
        ensures (q as int) in qm.bodies && qm.bodies[q as int] == PIV.QidBody(r2, q)
      {
        assert q !in PIV.QuantIds(r1) * PIV.QuantIds(r2);
        assert PIV.QidBody(r, q) == PIV.QidBody(r2, q);
      }
      BodiesOkOfQid(r1, qm); BodiesOkOfQid(r2, qm);
    case Re_con(r1, r2) =>
      forall q: nat | q in PIV.QuantIds(r1)
        ensures (q as int) in qm.bodies && qm.bodies[q as int] == PIV.QidBody(r1, q)
      { assert PIV.QidBody(r, q) == PIV.QidBody(r1, q); }
      forall q: nat | q in PIV.QuantIds(r2)
        ensures (q as int) in qm.bodies && qm.bodies[q as int] == PIV.QidBody(r2, q)
      {
        assert q !in PIV.QuantIds(r1) * PIV.QuantIds(r2);
        assert PIV.QidBody(r, q) == PIV.QidBody(r2, q);
      }
      BodiesOkOfQid(r1, qm); BodiesOkOfQid(r2, qm);
    case Re_quant(nul, qid0, q0, r1) =>
      assert (qid0 as nat) in PIV.QuantIds(r);
      assert PIV.QidBody(r, qid0 as nat) == r1;
      forall q: nat | q in PIV.QuantIds(r1)
        ensures (q as int) in qm.bodies && qm.bodies[q as int] == PIV.QidBody(r1, q)
      {
        assert q != qid0 as nat;
        assert PIV.QidBody(r, q) == PIV.QidBody(r1, q);
      }
      BodiesOkOfQid(r1, qm);
    case Re_capture(_, r1) =>
      forall q: nat | q in PIV.QuantIds(r1)
        ensures (q as int) in qm.bodies && qm.bodies[q as int] == PIV.QidBody(r1, q)
      { assert PIV.QidBody(r, q) == PIV.QidBody(r1, q); }
      BodiesOkOfQid(r1, qm);
    case _ =>
  }

  /** `BodiesOk` from the standard table invariant (`QmapOk`) + `QuantUnique`. */
  lemma BodiesOkOfQmapOk(re: R.regex, qm: AR.QMap)
    requires T.TransWf(re) && AR.QmapOk(re, qm) && PIV.QuantUnique(re)
    ensures BodiesOk(re, qm)
  {
    forall q: nat | q in PIV.QuantIds(re)
      ensures (q as int) in qm.bodies && qm.bodies[q as int] == PIV.QidBody(re, q)
    { PIV.QmapOkBodyAtQid(re, qm, q); }
    BodiesOkOfQid(re, qm);
  }

  lemma ApplyEffNone(gm: LG.GroupMap)
    ensures ApplyEff(({}, map[]), gm) == gm
  {
    var p := ApplyEff(({}, map[]), gm);
    assert forall g :: g in p <==> g in gm;
  }

  lemma SeqEffApply(e1: (set<nat>, LG.GroupMap), e2: (set<nat>, LG.GroupMap), gm: LG.GroupMap)
    ensures ApplyEff(e2, ApplyEff(e1, gm)) == ApplyEff(SeqEff(e1, e2), gm)
  {
    var lhs := ApplyEff(e2, ApplyEff(e1, gm));
    var rhs := ApplyEff(SeqEff(e1, e2), gm);
    forall h ensures (h in lhs <==> h in rhs) && (h in lhs ==> lhs[h] == rhs[h]) {}
  }

  lemma StampEffClosed(qm: AR.QMap, str: string, qid: nat, qcp: seq<int>, r1: R.regex, gm: LG.GroupMap)
    requires T.TransWf(r1) && PIV.CapUnique(r1)
    requires (qid as int) in qm.bodies && qm.bodies[qid as int] == r1
    ensures EffOk(StampEff(qm, str, qid, qcp, r1), PIV.CapIds(r1), |str|)
    ensures PIV.StampApply(qm, str, qid, qcp, r1, gm) == ApplyEff(StampEff(qm, str, qid, qcp, r1), gm)
  {
    if PIV.StampReady(qm, str, qid, qcp) {
      var cp := PIV.StampCp(qcp, qid);
      var inp := T.InputAt(str, cp);
      var X := PIV.CapIds(r1);
      var DG := L.DefGroups(T.Translate(r1));
      PIV.DefGroupsCapIds(r1);
      var gmR := LG.GMReset(DG, gm);
      assert gmR == gm - X by { assert (set g | g in DG) == X; }
      EmptyEffPath(qm, r1, inp, cp, gmR);
      if EmptyEff(qm, r1, inp).Some? {
        var e := EmptyEff(qm, r1, inp).value;
        var lhs := Patch(gmR, e.1, e.0, cp);
        var rhs := ApplyEff((X, Pin(e.0, cp)), gm);
        forall h ensures (h in lhs <==> h in rhs) && (h in lhs ==> lhs[h] == rhs[h]) {}
        assert lhs == rhs;
      } else {
        ApplyEffNone(gm);
      }
    } else {
      ApplyEffNone(gm);
    }
  }

  lemma LiveEffClosed(r: R.regex, qm: AR.QMap, str: string, qc: seq<int>, qcp: seq<int>, mx: int, gm: LG.GroupMap)
    requires T.TransWf(r) && PIV.CapUnique(r) && BodiesOk(r, qm)
    ensures EffOk(LiveEff(r, qm, str, qc, qcp, mx), PIV.CapIds(r), |str|)
    ensures PIV.LiveStampsGm(r, qm, str, qc, qcp, mx, gm) == ApplyEff(LiveEff(r, qm, str, qc, qcp, mx), gm)
    decreases r
  {
    match r
    case Re_empty => ApplyEffNone(gm);
    case Re_character(_) => ApplyEffNone(gm);
    case Re_anchor(_) => ApplyEffNone(gm);
    case Re_lookaround(_, _, _) => ApplyEffNone(gm);
    case Re_alt(r1, r2) =>
      LiveEffClosed(r1, qm, str, qc, qcp, mx, gm);
      var gm1 := PIV.LiveStampsGm(r1, qm, str, qc, qcp, mx, gm);
      LiveEffClosed(r2, qm, str, qc, qcp, mx, gm1);
      SeqEffApply(LiveEff(r1, qm, str, qc, qcp, mx), LiveEff(r2, qm, str, qc, qcp, mx), gm);
    case Re_con(r1, r2) =>
      LiveEffClosed(r1, qm, str, qc, qcp, mx, gm);
      var gm1 := PIV.LiveStampsGm(r1, qm, str, qc, qcp, mx, gm);
      LiveEffClosed(r2, qm, str, qc, qcp, mx, gm1);
      SeqEffApply(LiveEff(r1, qm, str, qc, qcp, mx), LiveEff(r2, qm, str, qc, qcp, mx), gm);
    case Re_quant(nul, qid, q, r1) =>
      var qv := AI.get_idx(qc, qid);
      if qv < mx {
        ApplyEffNone(gm);
      } else if qid >= 0 && AI.get_idx(qcp, qid) >= 0 {
        StampEffClosed(qm, str, qid as nat, qcp, r1, gm);
      } else {
        LiveEffClosed(r1, qm, str, qc, qcp, qv, gm);
      }
    case Re_capture(cid, r1) =>
      LiveEffClosed(r1, qm, str, qc, qcp, mx, gm);
  }

  lemma PinMirror(D: set<nat>, c: nat, n: nat)
    requires c <= n
    ensures TRM.GmInBounds(Pin(D, c), n)
    ensures TRM.MirrorGm(Pin(D, c), n) == Pin(D, n - c)
  {
    var lhs := TRM.MirrorGm(Pin(D, c), n);
    var rhs := Pin(D, n - c);
    forall h ensures (h in lhs <==> h in rhs) && (h in lhs ==> lhs[h] == rhs[h]) {}
  }

  lemma MirrorGmEmpty(n: nat)
    ensures TRM.GmInBounds(map[], n) && TRM.MirrorGm(map[], n) == map[]
  {
    var m: LG.GroupMap := map[];
    assert forall h :: h !in TRM.MirrorGm(m, n);
  }

  lemma StampEffMirror(qm: AR.QMap, qm': AR.QMap, str: string, qid: nat, qcp: seq<int>, qcp': seq<int>, r1: R.regex)
    requires T.TransWf(r1) && PIV.CapUnique(r1)
    requires (qid as int) in qm.bodies && qm.bodies[qid as int] == r1
    requires (qid as int) in qm'.bodies && qm'.bodies[qid as int] == FST.FXR(r1)
    requires |qm.ov| == |str| + 1 && qm'.ov == MIR.MirrorView(qm.ov, |str|)
    requires AI.get_idx(qcp', qid) == MIR.MirrorCpVal(AI.get_idx(qcp, qid), |str|)
    ensures |LC.Reverse(str)| == |str|
    ensures TRM.GmInBounds(StampEff(qm, str, qid, qcp, r1).1, |str|)
    ensures StampEff(qm', LC.Reverse(str), qid, qcp', FST.FXR(r1))
         == (StampEff(qm, str, qid, qcp, r1).0, TRM.MirrorGm(StampEff(qm, str, qid, qcp, r1).1, |str|))
  {
    var n := |str|;
    FST.TranslateFlipXRev(r1);
    SD.ReverseLength(str);
    var rstr := LC.Reverse(str);
    StampEffClosed(qm, str, qid, qcp, r1, map[]);
    MirrorGmEmpty(n);
    var v := AI.get_idx(qcp, qid);
    if 0 <= v <= n {
      assert PIV.StampReady(qm, str, qid, qcp);
      assert PIV.StampReady(qm', rstr, qid, qcp');
      var cp: nat := v as nat;
      assert PIV.StampCp(qcp, qid) == cp;
      assert PIV.StampCp(qcp', qid) == n - cp;
      EmptyEffMirror(qm, qm', r1, str, cp);
      CapIdsFXR(r1);
      var e := EmptyEff(qm, r1, T.InputAt(str, cp));
      if e.Some? { PinMirror(e.value.0, cp, n); }
    } else {
      assert !PIV.StampReady(qm, str, qid, qcp);
      assert !PIV.StampReady(qm', rstr, qid, qcp');
    }
  }

  lemma SeqEffMirror(e1: (set<nat>, LG.GroupMap), e2: (set<nat>, LG.GroupMap), n: nat)
    requires TRM.GmInBounds(e1.1, n) && TRM.GmInBounds(e2.1, n)
    ensures TRM.GmInBounds(SeqEff(e1, e2).1, n)
    ensures SeqEff((e1.0, TRM.MirrorGm(e1.1, n)), (e2.0, TRM.MirrorGm(e2.1, n)))
         == (SeqEff(e1, e2).0, TRM.MirrorGm(SeqEff(e1, e2).1, n))
  {
    var m := SeqEff(e1, e2).1;
    assert TRM.GmInBounds(m, n);
    var lhs := SeqEff((e1.0, TRM.MirrorGm(e1.1, n)), (e2.0, TRM.MirrorGm(e2.1, n))).1;
    var rhs := TRM.MirrorGm(m, n);
    forall h ensures (h in lhs <==> h in rhs) && (h in lhs ==> lhs[h] == rhs[h]) {}
    assert lhs == rhs;
  }

  /** The concatenation swap: disjoint effects commute. */
  lemma SeqEffSwap(e1: (set<nat>, LG.GroupMap), e2: (set<nat>, LG.GroupMap), n: nat)
    requires TRM.GmInBounds(e1.1, n) && TRM.GmInBounds(e2.1, n)
    requires e1.0 * e2.0 == {}
    requires forall g :: g in e1.1 ==> g in e1.0
    requires forall g :: g in e2.1 ==> g in e2.0
    ensures TRM.GmInBounds(SeqEff(e1, e2).1, n)
    ensures SeqEff((e2.0, TRM.MirrorGm(e2.1, n)), (e1.0, TRM.MirrorGm(e1.1, n)))
         == (SeqEff(e1, e2).0, TRM.MirrorGm(SeqEff(e1, e2).1, n))
  {
    var m := SeqEff(e1, e2).1;
    assert TRM.GmInBounds(m, n);
    var lhs := SeqEff((e2.0, TRM.MirrorGm(e2.1, n)), (e1.0, TRM.MirrorGm(e1.1, n)));
    var rhs := (SeqEff(e1, e2).0, TRM.MirrorGm(m, n));
    assert lhs.0 == rhs.0;
    forall h: nat ensures (h in lhs.1 <==> h in rhs.1) && (h in lhs.1 ==> lhs.1[h] == rhs.1[h]) {
      assert h !in e1.0 * e2.0;
    }
    assert lhs.1 == rhs.1;
  }

  lemma LiveEffMirror(r: R.regex, qm: AR.QMap, qm': AR.QMap, str: string, qc: seq<int>,
                      qcp: seq<int>, qcp': seq<int>, mx: int)
    requires T.TransWf(r) && PIV.CapUnique(r) && BodiesOk(r, qm) && BodiesFXR(r, qm')
    requires |qm.ov| == |str| + 1 && qm'.ov == MIR.MirrorView(qm.ov, |str|)
    requires forall k :: AI.get_idx(qcp, k) <= |str|
    requires forall k :: AI.get_idx(qcp', k) == MIR.MirrorCpVal(AI.get_idx(qcp, k), |str|)
    ensures |LC.Reverse(str)| == |str|
    ensures EffOk(LiveEff(r, qm, str, qc, qcp, mx), PIV.CapIds(r), |str|)
    ensures LiveEff(FST.FXR(r), qm', LC.Reverse(str), qc, qcp', mx)
         == (LiveEff(r, qm, str, qc, qcp, mx).0, TRM.MirrorGm(LiveEff(r, qm, str, qc, qcp, mx).1, |str|))
    decreases r
  {
    var n := |str|;
    SD.ReverseLength(str);
    var rstr := LC.Reverse(str);
    LiveEffClosed(r, qm, str, qc, qcp, mx, map[]);
    MirrorGmEmpty(n);
    match r
    case Re_empty =>
    case Re_character(_) =>
    case Re_anchor(a) =>
      assert FST.FXR(r) == R.Re_anchor(MIR.SwapAnchor(a));
    case Re_lookaround(lid, lk, r1) =>
      assert FST.FXR(r) == R.Re_lookaround(lid, FR.FlipLkRE(lk), FST.FXR(r1));
    case Re_alt(r1, r2) =>
      assert FST.FXR(r) == R.Re_alt(FST.FXR(r1), FST.FXR(r2));
      LiveEffMirror(r1, qm, qm', str, qc, qcp, qcp', mx);
      LiveEffMirror(r2, qm, qm', str, qc, qcp, qcp', mx);
      SeqEffMirror(LiveEff(r1, qm, str, qc, qcp, mx), LiveEff(r2, qm, str, qc, qcp, mx), n);
    case Re_con(r1, r2) =>
      assert FST.FXR(r) == R.Re_con(FST.FXR(r2), FST.FXR(r1));
      LiveEffMirror(r1, qm, qm', str, qc, qcp, qcp', mx);
      LiveEffMirror(r2, qm, qm', str, qc, qcp, qcp', mx);
      var e1 := LiveEff(r1, qm, str, qc, qcp, mx);
      var e2 := LiveEff(r2, qm, str, qc, qcp, mx);
      assert e1.0 * e2.0 == {} by {
        assert PIV.CapIds(r1) * PIV.CapIds(r2) == {};
      }
      SeqEffSwap(e1, e2, n);
    case Re_quant(nul, qid, q, r1) =>
      assert FST.FXR(r) == R.Re_quant(nul, qid, q, FST.FXR(r1));
      var qv := AI.get_idx(qc, qid);
      if qv < mx {
      } else if qid >= 0 && AI.get_idx(qcp, qid) >= 0 {
        assert AI.get_idx(qcp', qid) >= 0;
        StampEffMirror(qm, qm', str, qid as nat, qcp, qcp', r1);
      } else {
        assert !(qid >= 0 && AI.get_idx(qcp', qid) >= 0);
        LiveEffMirror(r1, qm, qm', str, qc, qcp, qcp', qv);
      }
    case Re_capture(cid, r1) =>
      assert FST.FXR(r) == R.Re_capture(cid, FST.FXR(r1));
      LiveEffMirror(r1, qm, qm', str, qc, qcp, qcp', mx);
  }

  /** LiveStampsGm commutes with the ordered mirror. */
  lemma LiveStampsGmMirror(r: R.regex, qm: AR.QMap, qm': AR.QMap, str: string, qc: seq<int>,
                           qcp: seq<int>, qcp': seq<int>, mx: int, gm: LG.GroupMap)
    requires T.TransWf(r) && PIV.CapUnique(r) && BodiesOk(r, qm) && BodiesFXR(r, qm')
    requires |qm.ov| == |str| + 1 && qm'.ov == MIR.MirrorView(qm.ov, |str|)
    requires forall k :: AI.get_idx(qcp, k) <= |str|
    requires forall k :: AI.get_idx(qcp', k) == MIR.MirrorCpVal(AI.get_idx(qcp, k), |str|)
    requires TRM.GmInBounds(gm, |str|)
    ensures T.TransWf(FST.FXR(r)) && |LC.Reverse(str)| == |str|
    ensures TRM.GmInBounds(PIV.LiveStampsGm(r, qm, str, qc, qcp, mx, gm), |str|)
    ensures TRM.MirrorGm(PIV.LiveStampsGm(r, qm, str, qc, qcp, mx, gm), |str|)
         == PIV.LiveStampsGm(FST.FXR(r), qm', LC.Reverse(str), qc, qcp', mx, TRM.MirrorGm(gm, |str|))
  {
    var n := |str|;
    FST.TranslateFlipXRev(r);
    CapUniqueFXR(r);
    BodiesFXROk(r, qm');
    SD.ReverseLength(str);
    var rstr := LC.Reverse(str);
    LiveEffClosed(r, qm, str, qc, qcp, mx, gm);
    LiveEffMirror(r, qm, qm', str, qc, qcp, qcp', mx);
    var gmM := TRM.MirrorGm(gm, n);
    LiveEffClosed(FST.FXR(r), qm', rstr, qc, qcp', mx, gmM);
    var e := LiveEff(r, qm, str, qc, qcp, mx);
    var lhs0 := ApplyEff(e, gm);
    assert TRM.GmInBounds(lhs0, n);
    var lhs := TRM.MirrorGm(lhs0, n);
    var rhs := ApplyEff((e.0, TRM.MirrorGm(e.1, n)), gmM);
    forall h ensures (h in lhs <==> h in rhs) && (h in lhs ==> lhs[h] == rhs[h]) {}
    assert lhs == rhs;
  }

  // ---------------------------------------------------------------------------
  // GmOfLiveR: the reconstruction-aware readout of the real backward replay
  // (registers = MirrorRegs of the mirrored forward run's) is the RAW mirror
  // (BGM.RawMirrorGm, the engine's positional readout quirk) of the mirrored
  // forward run's GmOfLiveR on FXR(body).
  // ---------------------------------------------------------------------------

  /** Raw mirror of an effect application whose overlay is the ordered mirror of
      empty ranges. */
  lemma RawApplyEff(e: (set<nat>, LG.GroupMap), G: LG.GroupMap, X: set<nat>, n: nat)
    requires EffOk(e, X, n) && BGM.GmLeN(G, n)
    ensures TRM.GmInBounds(e.1, n)
    ensures BGM.GmLeN(ApplyEff((e.0, TRM.MirrorGm(e.1, n)), G), n)
    ensures BGM.RawMirrorGm(ApplyEff((e.0, TRM.MirrorGm(e.1, n)), G), n)
         == ApplyEff(e, BGM.RawMirrorGm(G, n))
  {
    var m' := TRM.MirrorGm(e.1, n);
    var a := ApplyEff((e.0, m'), G);
    assert BGM.GmLeN(a, n);
    var lhs := BGM.RawMirrorGm(a, n);
    var rhs := ApplyEff(e, BGM.RawMirrorGm(G, n));
    forall h ensures (h in lhs <==> h in rhs) && (h in lhs ==> lhs[h] == rhs[h]) {
      if h in e.1 {
        assert e.1[h].endIdx == Some(e.1[h].startIdx);
      }
    }
    assert lhs == rhs;
  }

  lemma GmOfLiveRMirror(body: R.regex, qm: AR.QMap, qm': AR.QMap, str: string,
                        cap: AReg.Regs, look: AReg.Regs, quant: AReg.Regs)
    requires T.TransWf(body) && PIV.CapUnique(body) && BodiesOk(body, qm) && BodiesFXR(body, qm')
    requires |qm.ov| == |str| + 1 && qm'.ov == MIR.MirrorView(qm.ov, |str|)
    requires forall k :: AI.get_idx(AReg.as_arrays(cap).0, k) <= |str|
    requires forall k :: AI.get_idx(quant.a_cp, k) <= |str|     // `BanksIn` on the quant bank
    ensures T.TransWf(FST.FXR(body)) && |LC.Reverse(str)| == |str|
    ensures BGM.GmLeN(PIV.GmOfLiveR(FST.FXR(body), qm', LC.Reverse(str), cap, look, quant), |str|)
    ensures PIV.GmOfLiveR(body, qm, str, MIR.MirrorRegs(cap, |str|), MIR.MirrorRegs(look, |str|),
                          MIR.MirrorRegs(quant, |str|))
         == BGM.RawMirrorGm(PIV.GmOfLiveR(FST.FXR(body), qm', LC.Reverse(str), cap, look, quant), |str|)
  {
    var n := |str|;
    FST.TranslateFlipXRev(body);
    CapUniqueFXR(body);
    BodiesFXROk(body, qm');
    SD.ReverseLength(str);
    var rstr := LC.Reverse(str);
    var capB := MIR.MirrorRegs(cap, n);
    var lookB := MIR.MirrorRegs(look, n);
    var quantB := MIR.MirrorRegs(quant, n);
    // the GmOfLive part
    PIV.GmOfLiveClkCong(body, capB, lookB, look, quantB, quant);
    BGM.GmOfLiveMirror(body, cap, look, quant, n);
    FST.GmOfLiveFXR(body, cap, look, quant);
    var G := PIV.GmOfLive(FST.FXR(body), cap, look, quant);
    assert PIV.GmOfLive(body, capB, lookB, quantB) == BGM.RawMirrorGm(G, n);
    // the stamp part: real side reads quantB.a_cp, mirror side quant.a_cp
    var qc := quant.a_clk;
    assert quantB.a_clk == qc;
    var qcpB := quantB.a_cp;
    var qcpF := quant.a_cp;
    forall k ensures AI.get_idx(qcpB, k) <= n {}
    forall k ensures AI.get_idx(qcpF, k) == MIR.MirrorCpVal(AI.get_idx(qcpB, k), n) {}
    LiveEffClosed(body, qm, str, qc, qcpB, -1, BGM.RawMirrorGm(G, n));
    LiveEffMirror(body, qm, qm', str, qc, qcpB, qcpF, -1);
    LiveEffClosed(FST.FXR(body), qm', rstr, qc, qcpF, -1, G);
    var e := LiveEff(body, qm, str, qc, qcpB, -1);
    RawApplyEff(e, G, PIV.CapIds(body), n);
  }

  /** The same, from the standard table invariants (what the call site has:
      `QmapOk` of the row body for the real table, of `FXR(body)` for the
      mirrored one, e.g. `FK.FlipXRevStaticOkNested`'s `qm''`). */
  lemma GmOfLiveRMirrorQ(body: R.regex, qm: AR.QMap, qm': AR.QMap, str: string,
                         cap: AReg.Regs, look: AReg.Regs, quant: AReg.Regs)
    requires T.TransWf(body) && PIV.CapUnique(body) && PIV.QuantUnique(body)
    requires AR.QmapOk(body, qm)
    requires T.TransWf(FST.FXR(body)) && AR.QmapOk(FST.FXR(body), qm')
    requires |qm.ov| == |str| + 1 && qm'.ov == MIR.MirrorView(qm.ov, |str|)
    requires forall k :: AI.get_idx(AReg.as_arrays(cap).0, k) <= |str|
    requires forall k :: AI.get_idx(quant.a_cp, k) <= |str|
    ensures |LC.Reverse(str)| == |str|
    ensures BGM.GmLeN(PIV.GmOfLiveR(FST.FXR(body), qm', LC.Reverse(str), cap, look, quant), |str|)
    ensures PIV.GmOfLiveR(body, qm, str, MIR.MirrorRegs(cap, |str|), MIR.MirrorRegs(look, |str|),
                          MIR.MirrorRegs(quant, |str|))
         == BGM.RawMirrorGm(PIV.GmOfLiveR(FST.FXR(body), qm', LC.Reverse(str), cap, look, quant), |str|)
  {
    BodiesOkOfQmapOk(body, qm);
    FST.XRevIsRevRENested(body);
    LBV.QuantUniqueRevRE(body);
    FST.FlipQuantUnique(FST.XRV(body));
    BodiesOkOfQmapOk(FST.FXR(body), qm');
    BodiesFXRFromOk(body, qm');
    GmOfLiveRMirror(body, qm, qm', str, cap, look, quant);
  }

  // ===========================================================================
  // 8. Anti-vacuity: the hypotheses of the three top lemmas are satisfiable
  //    (a live stamp at cp 0 on the CIN plus `(?:())+`, str = "")
  // ===========================================================================

  lemma Witness()
  {
    var body1 := R.Re_capture(1, R.Re_empty);
    var body := R.Re_quant(R.CINullable, 0, R.CountedQuant(1, None, true), body1);
    assert T.TransWf(body) && PIV.CapUnique(body);
    var ov: LOr.OracleView := [[]];
    var qm := AR.QMap(map[], map[], ov, map[0 := body1]);
    var qm' := AR.QMap(map[], map[], MIR.MirrorView(ov, 0), map[0 := FST.FXR(body1)]);
    assert BodiesOk(body, qm) && BodiesFXR(body, qm');
    var cap := AReg.init_regs(4);
    var look := AReg.init_regs(0);
    var quant := AReg.ARegs([0], [0]);
    assert forall k :: AI.get_idx(AReg.as_arrays(cap).0, k) <= 0;
    assert forall k :: AI.get_idx(quant.a_cp, k) <= 0;
    GmOfLiveRMirror(body, qm, qm', "", cap, look, quant);
    FirstEmptyPathMirror(qm, qm', body1, "", 0, map[]);
    assert AI.get_idx([0], 0) == MIR.MirrorCpVal(AI.get_idx([0], 0), 0);
    StampApplyMirror(qm, qm', "", 0, [0], [0], body1, map[]);
  }
}
