// (G5b-2, N2) The mirrored CDN table of a lookbehind row (from the W14 probe 4, `endgame/W14-G5a-first.md`).
//
// The flip tower relates a Backward run of `reverse_regex(body)` with the cdn list `cs` to a Forward run of
// `FXR(body)` over `Reverse(str)` with `MIR.SwapAnchorsCdns(cs)` (`BV.BackwardReplayMirrorNested`), while
// `FG.MirrorTables` pins the mirrored row's list to `compile_cdns(FXR(body))`. The two lists differ in order
// (`reverse_regex` swaps `Re_con`), but the TABLES they build agree at every position (`CdnTableMirror`),
// so the runs agree (`FFindMatchTableCong`), and the forward row's guard soundness at `FXR(body)` (N1) carries
// over to the swapped list (`GuardsOkRunFlip`).
/** (G5b-2) The mirrored CDN table of a lookbehind row: table equality, run congruence, guard soundness. */
module LindenElkCdnMirror {
  import opened Std.Wrappers
  import R = RegElkRegex
  import RB = Bytecode
  import CP = Compiler
  import C = Cdn
  import LOr = Oracle
  import LAnc = Anchors
  import AI = ArrayInterp
  import LC = Chars
  import ORc = LindenElkOracleReach
  import OBV = LindenElkOracleBridgeV
  import MIR = LindenElkMirror
  import FR = LindenElkFlipRev
  import FST = LindenElkFlipStatics
  import CS = LindenElkCdnSound
  import CG = LindenElkCdnGuards
  import CM = LindenElkClockMono
  import NR = LindenElkNfaRep
  import T = LindenElkTranslate
  import AR = LindenElkActionsRep
  import PIV = LindenElkPikeInv
  import PSM = LindenElkPikeSim

  // ===========================================================================
  // FXR, one constructor at a time
  // ===========================================================================

  lemma FXRShape(r: R.regex)
    ensures match r
      case Re_empty => FST.FXR(r) == r
      case Re_character(_) => FST.FXR(r) == r
      case Re_anchor(a) => FST.FXR(r) == R.Re_anchor(MIR.SwapAnchor(a))
      case Re_alt(r1, r2) => FST.FXR(r) == R.Re_alt(FST.FXR(r1), FST.FXR(r2))
      case Re_con(r1, r2) => FST.FXR(r) == R.Re_con(FST.FXR(r2), FST.FXR(r1))
      case Re_quant(nul, qid, q, r1) => FST.FXR(r) == R.Re_quant(nul, qid, q, FST.FXR(r1))
      case Re_capture(cid, r1) => FST.FXR(r) == R.Re_capture(cid, FST.FXR(r1))
      case Re_lookaround(lid, la, r1) => FST.FXR(r) == R.Re_lookaround(lid, FR.FlipLkRE(la), FST.FXR(r1))
  {}

  // ===========================================================================
  // Structure FXR keeps
  // ===========================================================================

  lemma NullableFXR(r: R.regex)
    ensures R.nullable(FST.FXR(r)) == R.nullable(r)
    decreases r
  {
    FXRShape(r);
    match r
    case Re_alt(r1, r2) => NullableFXR(r1); NullableFXR(r2);
    case Re_con(r1, r2) => NullableFXR(r1); NullableFXR(r2);   // null_and commutes
    case Re_quant(_, _, _, r1) => NullableFXR(r1);
    case Re_capture(_, r1) => NullableFXR(r1);
    case Re_lookaround(_, _, r1) =>
    case _ =>
  }

  lemma CdnWfFXR(r: R.regex)
    requires CS.CdnWf(r)
    ensures CS.CdnWf(FST.FXR(r))
    decreases r
  {
    FXRShape(r);
    match r
    case Re_alt(r1, r2) => CdnWfFXR(r1); CdnWfFXR(r2);
    case Re_con(r1, r2) => CdnWfFXR(r1); CdnWfFXR(r2);
    case Re_quant(_, _, _, r1) => CdnWfFXR(r1); NullableFXR(r1);
    case Re_capture(_, r1) => CdnWfFXR(r1);
    case Re_lookaround(_, _, r1) => CdnWfFXR(r1);
    case _ =>
  }

  lemma QIdsFXR(r: R.regex)
    ensures CS.QIds(FST.FXR(r)) == CS.QIds(r)
    ensures CS.CdnQIds(FST.FXR(r)) == CS.CdnQIds(r)
    decreases r
  {
    FXRShape(r);
    match r
    case Re_alt(r1, r2) => QIdsFXR(r1); QIdsFXR(r2);
    case Re_con(r1, r2) => QIdsFXR(r1); QIdsFXR(r2);
    case Re_quant(_, _, _, r1) => QIdsFXR(r1);
    case Re_capture(_, r1) => QIdsFXR(r1);
    case Re_lookaround(_, _, r1) => QIdsFXR(r1);
    case _ =>
  }

  lemma QUniqueFXR(r: R.regex)
    requires CS.QUnique(r)
    ensures CS.QUnique(FST.FXR(r))
    decreases r
  {
    FXRShape(r);
    match r
    case Re_alt(r1, r2) => QUniqueFXR(r1); QUniqueFXR(r2); QIdsFXR(r1); QIdsFXR(r2);
    case Re_con(r1, r2) => QUniqueFXR(r1); QUniqueFXR(r2); QIdsFXR(r1); QIdsFXR(r2);
    case Re_quant(_, _, _, r1) => QUniqueFXR(r1); QIdsFXR(r1);
    case Re_capture(_, r1) => QUniqueFXR(r1);
    case Re_lookaround(_, _, r1) => QUniqueFXR(r1);
    case _ =>
  }

  /** The mirrored plus's body is the mirror of the plus's body (needs QUnique: `Re_con` swaps the sides
      `CdnBody` searches first). */
  lemma CdnBodyFXR(r: R.regex, qid: int)
    requires CS.QUnique(r) && qid in CS.CdnQIds(r)
    ensures qid in CS.CdnQIds(FST.FXR(r))
    ensures CS.CdnBody(FST.FXR(r), qid) == FST.FXR(CS.CdnBody(r, qid))
    decreases r
  {
    FXRShape(r);
    QIdsFXR(r);
    match r
    case Re_alt(r1, r2) =>
      QIdsFXR(r1); QIdsFXR(r2);
      if qid in CS.CdnQIds(r1) { CdnBodyFXR(r1, qid); } else { CdnBodyFXR(r2, qid); }
    case Re_con(r1, r2) =>
      QIdsFXR(r1); QIdsFXR(r2); CS.CdnQIdsSub(r1); CS.CdnQIdsSub(r2);
      if qid in CS.CdnQIds(r1) {
        assert qid !in CS.CdnQIds(r2);
        CdnBodyFXR(r1, qid);
      } else {
        CdnBodyFXR(r2, qid);
      }
    case Re_quant(nul, q0, q, r1) =>
      QIdsFXR(r1);
      if !(CS.EligibleCdnPlus(nul, q) && q0 == qid) { CdnBodyFXR(r1, qid); }
    case Re_capture(_, r1) => QIdsFXR(r1); CdnBodyFXR(r1, qid);
    case Re_lookaround(_, _, r1) => QIdsFXR(r1); CdnBodyFXR(r1, qid);
  }

  lemma CdnWfCdnBody(r: R.regex, qid: int)
    requires CS.CdnWf(r) && qid in CS.CdnQIds(r)
    ensures CS.CdnWf(CS.CdnBody(r, qid))
    decreases r
  {
    match r
    case Re_alt(r1, r2) => if qid in CS.CdnQIds(r1) { CdnWfCdnBody(r1, qid); } else { CdnWfCdnBody(r2, qid); }
    case Re_con(r1, r2) => if qid in CS.CdnQIds(r1) { CdnWfCdnBody(r1, qid); } else { CdnWfCdnBody(r2, qid); }
    case Re_quant(nul, q0, q, r1) => if !(CS.EligibleCdnPlus(nul, q) && q0 == qid) { CdnWfCdnBody(r1, qid); }
    case Re_capture(_, r1) => CdnWfCdnBody(r1, qid);
    case Re_lookaround(_, _, r1) => CdnWfCdnBody(r1, qid);
  }

  // ===========================================================================
  // The empty-span mirror
  // ===========================================================================

  /** An anchor reads the same at `cp` of `str` as its swap at `n - cp` of the reversed string (both through
      the kind-blind `CtxAt`). */
  lemma AnchorMirror(a: R.anchor, str: string, cp: int)
    ensures LAnc.is_satisfied(MIR.SwapAnchor(a), ORc.CtxAt(LC.Reverse(str), MIR.Mirror(cp, |str|)), LAnc.Forward)
        <==> LAnc.is_satisfied(a, ORc.CtxAt(str, cp), LAnc.Forward)
  {
    var ctx := AI.cp_context(cp, str, LAnc.Backward);
    MIR.CpContextMirror(str, cp);
    assert ORc.CtxAt(LC.Reverse(str), MIR.Mirror(cp, |str|)) == ctx;
    MIR.IsSatisfiedMirror(a, ctx);
    CS.AnchorDirInvariant(a, str, cp, LAnc.Backward);
  }

  lemma EmptySpanMirror(b: R.regex, str: string, ov: LOr.OracleView, cp: int)
    requires CS.CdnWf(b)
    requires |ov| == |str| + 1
    ensures OBV.MatchesV(FST.FXR(b), LC.Reverse(str), MIR.MirrorView(ov, |str|),
                         MIR.Mirror(cp, |str|), MIR.Mirror(cp, |str|))
        <==> OBV.MatchesV(b, str, ov, cp, cp)
    decreases b
  {
    var n := |str|;
    var rstr := LC.Reverse(str);
    var ov' := MIR.MirrorView(ov, n);
    var m := MIR.Mirror(cp, n);
    FXRShape(b);
    match b
    case Re_empty =>
    case Re_character(_) =>
    case Re_anchor(a) => AnchorMirror(a, str, cp);
    case Re_alt(r1, r2) =>
      EmptySpanMirror(r1, str, ov, cp);
      EmptySpanMirror(r2, str, ov, cp);
    case Re_con(r1, r2) =>
      EmptySpanMirror(r1, str, ov, cp);
      EmptySpanMirror(r2, str, ov, cp);
      CS.ConEmptyIff(r1, r2, str, ov, cp);
      CS.ConEmptyIff(FST.FXR(r2), FST.FXR(r1), rstr, ov', m);
    case Re_quant(nul, qid, q, r1) =>
      if q.min == 0 {
        var k: nat := 0;
        assert q.min <= k && (q.max.Some? ==> k <= q.max.value) && OBV.MatchesIterV(r1, k, str, ov, cp, cp);
        assert q.min <= k && (q.max.Some? ==> k <= q.max.value)
            && OBV.MatchesIterV(FST.FXR(r1), k, rstr, ov', m, m);
      } else {
        EmptySpanMirror(r1, str, ov, cp);
        CS.QuantEmptyIff(nul, qid, q, r1, str, ov, cp);
        CS.QuantEmptyIff(nul, qid, q, FST.FXR(r1), rstr, ov', m);
      }
    case Re_capture(_, r1) => EmptySpanMirror(r1, str, ov, cp);
    case Re_lookaround(lid, la, r1) =>
      MIR.MirrorViewGet(ov, n, cp, lid);
  }

  // ===========================================================================
  // The table-level tie
  // ===========================================================================

  /** The mirrored world's table (built from `compile_cdns(FXR b)`, as `MirrorTables` pins it) equals the real
      Backward run's table, and hence the table the flip keystones' `SwapAnchorsCdns` run builds. Equality
      of `set<int>`s: the same bit for every qid. */
  lemma CdnTableMirror(b: R.regex, str: string, ov: LOr.OracleView, cp: int)
    requires CS.CdnWf(b) && CS.QUnique(b)
    requires |ov| == |str| + 1
    ensures var n := |str|;
            var m := MIR.Mirror(cp, n);
            var ctxF := AI.cp_context(m, LC.Reverse(str), LAnc.Forward);
            var tF := C.build_cdn_v(C.compile_cdns(FST.FXR(b)), m, MIR.MirrorView(ov, n), ctxF, LAnc.Forward);
            var tB := C.build_cdn_v(C.compile_cdns(b), cp, ov, AI.cp_context(cp, str, LAnc.Backward), LAnc.Backward);
            var tS := C.build_cdn_v(MIR.SwapAnchorsCdns(C.compile_cdns(b)), m, MIR.MirrorView(ov, n), ctxF, LAnc.Forward);
            tF == tB && tB == tS
  {
    var n := |str|;
    var rstr := LC.Reverse(str);
    var m := MIR.Mirror(cp, n);
    var ov' := MIR.MirrorView(ov, n);
    var ctxB := AI.cp_context(cp, str, LAnc.Backward);
    var ctxF := AI.cp_context(m, rstr, LAnc.Forward);
    MIR.CpContextMirror(str, cp);
    assert ctxF == ctxB;
    MIR.ReverseLen(str);
    var fb := FST.FXR(b);
    CdnWfFXR(b); QUniqueFXR(b); QIdsFXR(b);
    var tF := C.build_cdn_v(C.compile_cdns(fb), m, ov', ctxF, LAnc.Forward);
    var tB := C.build_cdn_v(C.compile_cdns(b), cp, ov, ctxB, LAnc.Backward);
    CS.CdnSoundAll(fb, rstr, ov', m, ctxF, LAnc.Forward);
    CS.CdnSoundAll(b, str, ov, cp, ctxB, LAnc.Backward);
    forall qid ensures qid in tF <==> qid in tB {
      CS.CdnSound(fb, rstr, ov', m, ctxF, LAnc.Forward, qid);
      CS.CdnSound(b, str, ov, cp, ctxB, LAnc.Backward, qid);
      if qid in CS.CdnQIds(b) {
        CdnBodyFXR(b, qid);
        CdnWfCdnBody(b, qid);
        EmptySpanMirror(CS.CdnBody(b, qid), str, ov, cp);
      }
    }
    assert tF == tB;
    MIR.BuildCdnMirror(C.compile_cdns(b), cp, ov, n, ctxB);
  }

  /** `CdnTableMirror` on the mirrored side only, at every mirrored position: the swapped list and the
      flipped body's own list build the same table. */
  lemma CdnTableSwapFXR(b: R.regex, str: string, ov: LOr.OracleView, m: int)
    requires T.TransWf(b) && PIV.QuantUnique(b)
    requires |ov| == |str| + 1 && 0 <= m <= |str|
    ensures var ctxF := AI.cp_context(m, LC.Reverse(str), LAnc.Forward);
            C.build_cdn_v(MIR.SwapAnchorsCdns(C.compile_cdns(b)), m, MIR.MirrorView(ov, |str|), ctxF, LAnc.Forward)
            == C.build_cdn_v(C.compile_cdns(FST.FXR(b)), m, MIR.MirrorView(ov, |str|), ctxF, LAnc.Forward)
  {
    var n := |str|;
    CS.TransWfCdnWf(b);
    CG.QUniqueOfQuantUnique(b);
    CdnTableMirror(b, str, ov, n - m);
    assert MIR.Mirror(n - m, n) == m;
  }

  // ===========================================================================
  // Run congruence: equal tables at every position, equal run
  // ===========================================================================

  /** One engine run of write-free code, under two cdn lists that build the same table at every position
      (against the run's own view and the position's context), is the same run. */
  lemma FFindMatchTableCong(c: RB.code, str: string, s: AI.VmState, ov: LOr.OracleView, dir: LAnc.direction,
                            cdnA: C.cdns, cdnB: C.cdns)
    requires |s.processed.true_set| == RB.size(c) && |s.processed.false_set| == RB.size(c)
    requires s.context == AI.cp_context(s.cp, str, dir)
    requires 0 <= s.cp <= |str|
    requires CM.NoWriteOracleCode(c)
    requires forall cp: int :: 0 <= cp <= |str| ==>
               C.build_cdn_v(cdnA, cp, ov, AI.cp_context(cp, str, dir), dir)
               == C.build_cdn_v(cdnB, cp, ov, AI.cp_context(cp, str, dir), dir)
    ensures dir.Forward? ==> s.context.nextchar == AI.get_char(str, s.cp)
    ensures dir.Backward? ==> s.context.nextchar == AI.get_char(str, s.cp - 1)
    ensures AI.FFindMatch(c, str, s, ov, dir, cdnA) == AI.FFindMatch(c, str, s, ov, dir, cdnB)
    decreases if dir.Forward? then |str| - s.cp else s.cp
  {
    assert dir.Forward? ==> s.context.nextchar == AI.get_char(str, s.cp);
    assert dir.Backward? ==> s.context.nextchar == AI.get_char(str, s.cp - 1);
    var s0 := s.(cdn := C.build_cdn_v(cdnA, s.cp, ov, s.context, dir));
    assert s0 == s.(cdn := C.build_cdn_v(cdnB, s.cp, ov, s.context, dir));
    var (s1, ov1) := AI.FAdvanceEpsilon(c, s0, ov, dir);
    CM.FAdvanceEpsilonOvStable(c, s0, ov, dir);
    assert ov1 == ov;
    if |s1.blocked| == 0 { return; }
    match s1.context.nextchar {
      case None =>
      case Some(_) =>
        var s2 := AI.FConsume(s1);
        var s3 := s2.(processed := AI.init_bpcset(RB.size(c)), isblocked := AI.init_pcset(RB.size(c)),
                      cdn := C.init_cdn(), cp := AI.incr_cp(s2.cp, dir));
        var newchar := AI.get_char(str, s3.cp - AI.cp_offset(dir));
        var s4 := s3.(context := LAnc.update_context(s3.context, newchar));
        assert s1.cp == s.cp && s1.context == s.context;   // engine postconditions
        if dir.Forward? {
          assert s.cp < |str| by {
            if s.cp >= |str| { assert AI.get_char(str, s.cp) == None; }
          }
          assert s4.cp == s.cp + 1;
        } else {
          assert s.cp > 0 by {
            if s.cp <= 0 { assert AI.get_char(str, s.cp - 1) == None; }
          }
          assert s4.cp == s.cp - 1;
        }
        assert s4.context == AI.cp_context(s4.cp, str, dir);
        FFindMatchTableCong(c, str, s4, ov1, dir, cdnA, cdnB);
    }
  }

  // ===========================================================================
  // Guard soundness of the swapped list (N2 + N1)
  // ===========================================================================

  /** The run premise of the mirrored lookbehind row: the anchor-swapped ORIGINAL-body list is guard-sound for
      the flipped body's code, because it builds the flipped body's own table at every position. */
  lemma GuardsOkRunFlip(qmF: AR.QMap, body: R.regex, bcF: RB.code, endlF: nat, str: string, ov: LOr.OracleView)
    requires T.TransWf(body) && PIV.QuantUnique(body)
    requires PSM.StaticCoreCdnRE(qmF, FST.FXR(body), bcF, endlF)
    requires |ov| == |str| + 1 && qmF.ov == MIR.MirrorView(ov, |str|)
    ensures PSM.GuardsOkRun(qmF, bcF, MIR.SwapAnchorsCdns(C.compile_cdns(body)), MIR.MirrorView(ov, |str|),
                            LC.Reverse(str))
  {
    var n := |str|;
    MIR.ReverseLen(str);
    var rstr := LC.Reverse(str);
    var ovF := MIR.MirrorView(ov, n);
    var csF := C.compile_cdns(FST.FXR(body));
    var csS := MIR.SwapAnchorsCdns(C.compile_cdns(body));
    CG.GuardsOkRunRow(qmF, FST.FXR(body), bcF, endlF, rstr, ovF);
    assert PSM.GuardsOkRun(qmF, bcF, csF, ovF, rstr);
    forall m: int ensures PSM.GuardsOkAt(qmF, bcF, PSM.CdnAt(csS, ovF, rstr, m), rstr, m) {
      if 0 <= m <= n {
        CdnTableSwapFXR(body, str, ov, m);
        assert PSM.CdnAt(csS, ovF, rstr, m) == PSM.CdnAt(csF, ovF, rstr, m);
        assert PSM.GuardsOkAt(qmF, bcF, PSM.CdnAt(csF, ovF, rstr, m), rstr, m);
      } else {
        reveal PSM.GuardsOkAt();
      }
    }
  }
}
