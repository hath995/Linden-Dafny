// W13 (2026-11-10): the three G3b probes W8 §7 left open.
//   P1  sibling-order blindness of FinalReadout's register premises under FXR
//       (BestLiveRE = StampLiveOk + LooksCapUnset; Covers; OnlyCapIdsSet;
//       WfRegs; ThreadRegsWf; StampsLocal) across `raB == MirrorThread(rfF)`.
//   P2  RegsFinalOk: (a) transport across the mirror, (b) a direction-generic
//       twin of FV.FFindMatchRegsFinal.
//   P3  FV.FFindMatchRegsFinal instantiated at the mirrored row entry
//       (FXR(body), Reverse(str), MirrorRegs(init banks)); and the composed
//       row-level statement over W1's RowTieLB.
// Scratch only; no `assume`, no `{:axiom}`, no isolation.
module LindenElkBackRowResidue {
  import opened Std.Wrappers
  import R = RegElkRegex
  import RB = Bytecode
  import CP = Compiler
  import AI = ArrayInterp
  import AReg = Array_Regs
  import LOr = Oracle
  import LAnc = Anchors
  import LCdn = Cdn
  import LC = Chars
  import T = LindenElkTranslate
  import NR = LindenElkNfaRep
  import AR = LindenElkActionsRep
  import PIV = LindenElkPikeInv
  import MIR = LindenElkMirror
  import FR = LindenElkFlipRev
  import FST = LindenElkFlipStatics
  import SL = LindenElkStampLive
  import PSM = LindenElkPikeSim
  import NRC = LindenElkNulledRecon
  import NRR = LindenElkNulledReconRegs
  import NRO = LindenElkNulledReconReadout
  import FV = LindenElkFinalVm
  import FRD = LindenElkFinalReadout
  import CM = LindenElkClockMono

  // ===========================================================================
  // 0. FXR's shape, one constructor at a time.
  // ===========================================================================

  lemma FXRAlt(a: R.regex, b: R.regex)
    ensures FST.FXR(R.Re_alt(a, b)) == R.Re_alt(FST.FXR(a), FST.FXR(b)) {}
  lemma FXRCon(a: R.regex, b: R.regex)
    ensures FST.FXR(R.Re_con(a, b)) == R.Re_con(FST.FXR(b), FST.FXR(a)) {}
  lemma FXRQuant(nul: R.nullability, qid: R.quantid, q: R.counted_quantifier, a: R.regex)
    ensures FST.FXR(R.Re_quant(nul, qid, q, a)) == R.Re_quant(nul, qid, q, FST.FXR(a)) {}
  lemma FXRCap(cid: R.capture, a: R.regex)
    ensures FST.FXR(R.Re_capture(cid, a)) == R.Re_capture(cid, FST.FXR(a)) {}
  lemma FXRLook(lid: R.lookid, la: R.lookaround, a: R.regex)
    ensures FST.FXR(R.Re_lookaround(lid, la, a)) == R.Re_lookaround(lid, FR.FlipLkRE(la), FST.FXR(a)) {}
  lemma FXRAnchor(x: R.anchor)
    ensures FST.FXR(R.Re_anchor(x)) == R.Re_anchor(MIR.SwapAnchor(x)) {}

  // ===========================================================================
  // 1. Id sets are FXR-invariant (no premise).
  // ===========================================================================

  lemma IdsFXR(r: R.regex)
    ensures PIV.QuantIds(FST.FXR(r)) == PIV.QuantIds(r)
    ensures PIV.CapIds(FST.FXR(r)) == PIV.CapIds(r)
    ensures PIV.QuantIdsOutsideLooks(FST.FXR(r)) == PIV.QuantIdsOutsideLooks(r)
    ensures PIV.CapIdsInLooks(FST.FXR(r)) == PIV.CapIdsInLooks(r)
    ensures NRR.LookIds(FST.FXR(r)) == NRR.LookIds(r)
    decreases r
  {
    match r
    case Re_alt(a, b) => FXRAlt(a, b); IdsFXR(a); IdsFXR(b);
    case Re_con(a, b) => FXRCon(a, b); IdsFXR(a); IdsFXR(b);
    case Re_quant(nul, qid, q, a) => FXRQuant(nul, qid, q, a); IdsFXR(a);
    case Re_capture(cid, a) => FXRCap(cid, a); IdsFXR(a);
    case Re_lookaround(lid, la, a) => FXRLook(lid, la, a); IdsFXR(a);
    case Re_anchor(x) => FXRAnchor(x);
    case Re_empty =>
    case Re_character(_) =>
  }

  lemma QuantUniqueFXR(r: R.regex)
    requires PIV.QuantUnique(r)
    ensures PIV.QuantUnique(FST.FXR(r))
    decreases r
  {
    match r
    case Re_alt(a, b) => FXRAlt(a, b); IdsFXR(a); IdsFXR(b); QuantUniqueFXR(a); QuantUniqueFXR(b);
    case Re_con(a, b) => FXRCon(a, b); IdsFXR(a); IdsFXR(b); QuantUniqueFXR(a); QuantUniqueFXR(b);
    case Re_quant(nul, qid, q, a) => FXRQuant(nul, qid, q, a); IdsFXR(a); QuantUniqueFXR(a);
    case Re_capture(cid, a) => FXRCap(cid, a); QuantUniqueFXR(a);
    case Re_lookaround(lid, la, a) => FXRLook(lid, la, a); QuantUniqueFXR(a);
    case Re_anchor(x) => FXRAnchor(x);
    case Re_empty =>
    case Re_character(_) =>
  }

  // ===========================================================================
  // 2. The path predicates: a Re_con is DESCENDED (to the child holding q),
  //    never compared across siblings, so under QuantUnique the swap is
  //    invisible. Thresholds (mx) come from ANCESTOR clocks only.
  // ===========================================================================

  lemma PathsFXR(r: R.regex, cc: seq<int>, qc: seq<int>, mx: int, q: nat)
    requires PIV.QuantUnique(r) && q in PIV.QuantIds(r)
    ensures q in PIV.QuantIds(FST.FXR(r))
    ensures PIV.QidBody(FST.FXR(r), q) == FST.FXR(PIV.QidBody(r, q))
    ensures PIV.QChainFresh(FST.FXR(r), qc, mx, q) == PIV.QChainFresh(r, qc, mx, q)
    ensures PIV.PathPresentQ(FST.FXR(r), cc, qc, mx, q) == PIV.PathPresentQ(r, cc, qc, mx, q)
    ensures NRR.QidCinPlus(FST.FXR(r), q) == NRR.QidCinPlus(r, q)
    decreases r
  {
    IdsFXR(r);
    match r
    case Re_alt(a, b) =>
      FXRAlt(a, b); IdsFXR(a); IdsFXR(b);
      if q in PIV.QuantIds(a) { PathsFXR(a, cc, qc, mx, q); } else { PathsFXR(b, cc, qc, mx, q); }
    case Re_con(a, b) =>
      FXRCon(a, b); IdsFXR(a); IdsFXR(b);
      assert PIV.QuantIds(a) * PIV.QuantIds(b) == {};
      if q in PIV.QuantIds(a) {
        assert q !in PIV.QuantIds(b) by { assert q !in PIV.QuantIds(a) * PIV.QuantIds(b); }
        PathsFXR(a, cc, qc, mx, q);
      } else {
        PathsFXR(b, cc, qc, mx, q);
      }
    case Re_quant(nul, qid0, qq, a) =>
      FXRQuant(nul, qid0, qq, a);
      if qid0 >= 0 && (qid0 as nat) == q {
      } else {
        assert q in PIV.QuantIds(a);
        PathsFXR(a, cc, qc, AI.get_idx(qc, qid0), q);
      }
    case Re_capture(cid, a) => FXRCap(cid, a); PathsFXR(a, cc, qc, mx, q);
    case Re_lookaround(lid, la, a) =>
      FXRLook(lid, la, a); PathsFXR(a, cc, qc, mx, q); PathsFXR(a, cc, qc, -1, q);
    case Re_empty =>
    case Re_character(_) =>
    case Re_anchor(_) =>
  }

  lemma CinQidsFXR(r: R.regex)
    requires PIV.QuantUnique(r)
    ensures FRD.CinQids(FST.FXR(r)) == FRD.CinQids(r)
  {
    IdsFXR(r);
    forall x | x in FRD.CinQids(FST.FXR(r)) ensures x in FRD.CinQids(r) {
      var q: nat :| q in PIV.QuantIds(FST.FXR(r)) && NRR.QidCinPlus(FST.FXR(r), q) && q as int == x;
      PathsFXR(r, [], [], -1, q);
    }
    forall x | x in FRD.CinQids(r) ensures x in FRD.CinQids(FST.FXR(r)) {
      var q: nat :| q in PIV.QuantIds(r) && NRR.QidCinPlus(r, q) && q as int == x;
      PathsFXR(r, [], [], -1, q);
    }
  }

  lemma BodyStaleFXR(b: R.regex, cc: seq<int>, qc: seq<int>, K: int)
    ensures SL.BodyStale(FST.FXR(b), cc, qc, K) == SL.BodyStale(b, cc, qc, K)
  { IdsFXR(b); }

  lemma RegsStaleFXR(b: R.regex, rg: NRC.Regs3, K: int)
    ensures NRR.RegsStale(FST.FXR(b), rg, K) == NRR.RegsStale(b, rg, K)
  { IdsFXR(b); }

  // ===========================================================================
  // 3. StampLiveOk / LooksCapUnset / BestLiveRE.
  // ===========================================================================

  /** Same banks, regex flipped: equal (QuantUnique only). */
  lemma StampLiveOkFXR(re: R.regex, cc: seq<int>, qc: seq<int>, qcp: seq<int>)
    requires PIV.QuantUnique(re)
    ensures SL.StampLiveOk(FST.FXR(re), cc, qc, qcp) <==> SL.StampLiveOk(re, cc, qc, qcp)
  {
    IdsFXR(re);
    forall q: nat | q in PIV.QuantIds(re)
      ensures PIV.QidBody(FST.FXR(re), q) == FST.FXR(PIV.QidBody(re, q))
      ensures PIV.QChainFresh(FST.FXR(re), qc, -1, q) == PIV.QChainFresh(re, qc, -1, q)
      ensures PIV.PathPresentQ(FST.FXR(re), cc, qc, -1, q) == PIV.PathPresentQ(re, cc, qc, -1, q)
      ensures SL.BodyStale(PIV.QidBody(FST.FXR(re), q), cc, qc, AI.get_idx(qc, q))
              == SL.BodyStale(PIV.QidBody(re, q), cc, qc, AI.get_idx(qc, q))
    {
      PathsFXR(re, cc, qc, -1, q);
      BodyStaleFXR(PIV.QidBody(re, q), cc, qc, AI.get_idx(qc, q));
    }
    reveal SL.StampLiveOk;
  }

  /** The stamp array is read only through its SIGN. */
  lemma StampLiveOkSignCong(re: R.regex, cc: seq<int>, qc: seq<int>, p1: seq<int>, p2: seq<int>)
    requires forall k: int :: (AI.get_idx(p1, k) >= 0) == (AI.get_idx(p2, k) >= 0)
    ensures SL.StampLiveOk(re, cc, qc, p1) <==> SL.StampLiveOk(re, cc, qc, p2)
  { reveal SL.StampLiveOk; }

  lemma LooksCapUnsetFXR(re: R.regex, cc: seq<int>)
    ensures PIV.LooksCapUnset(FST.FXR(re), cc) <==> PIV.LooksCapUnset(re, cc)
  { IdsFXR(re); }

  /** Pointwise read of a mirrored bank. */
  lemma MirrorGetIdx(r: AReg.Regs, n: nat, k: int)
    ensures AI.get_idx(MIR.MirrorRegs(r, n).a_cp, k) == MIR.MirrorCpVal(AI.get_idx(r.a_cp, k), n)
    ensures |MIR.MirrorRegs(r, n).a_cp| == |r.a_cp| && MIR.MirrorRegs(r, n).a_clk == r.a_clk
  {}

  /** On a bank bounded by `n`, the mirror keeps every SIGN and the bound. */
  lemma MirrorSign(r: AReg.Regs, n: nat)
    requires forall k: int :: AI.get_idx(r.a_cp, k) <= n
    ensures forall k: int :: (AI.get_idx(MIR.MirrorRegs(r, n).a_cp, k) >= 0) == (AI.get_idx(r.a_cp, k) >= 0)
    ensures forall k: int :: AI.get_idx(MIR.MirrorRegs(r, n).a_cp, k) <= n
    ensures forall k: int :: AI.get_idx(r.a_cp, k) >= -1 ==> AI.get_idx(MIR.MirrorRegs(r, n).a_cp, k) >= -1
  {
    forall k: int ensures (AI.get_idx(MIR.MirrorRegs(r, n).a_cp, k) >= 0) == (AI.get_idx(r.a_cp, k) >= 0)
                     && AI.get_idx(MIR.MirrorRegs(r, n).a_cp, k) <= n
                     && (AI.get_idx(r.a_cp, k) >= -1 ==> AI.get_idx(MIR.MirrorRegs(r, n).a_cp, k) >= -1)
    { MirrorGetIdx(r, n, k); }
  }

  /** P1 HEADLINE: BestLiveRE of the mirrored forward winner on FXR(body) IS
      BestLiveRE of its mirror on body. Premises: QuantUnique(body) and the
      quant-bank bound `a_cp <= n` (W1's FFindMatchCpsIn, or RegsFinalOk). */
  lemma BestLiveREMirror(body: R.regex, t: AI.Thread, n: nat)
    requires PIV.QuantUnique(body)
    requires forall k: int :: AI.get_idx(t.quant_regs.a_cp, k) <= n
    ensures PSM.BestLiveRE(FST.FXR(body), t) <==> PSM.BestLiveRE(body, MIR.MirrorThread(t, n))
  {
    var tB := MIR.MirrorThread(t, n);
    assert tB.capture_regs.a_clk == t.capture_regs.a_clk;
    assert tB.quant_regs.a_clk == t.quant_regs.a_clk;
    MirrorSign(t.quant_regs, n);
    StampLiveOkFXR(body, t.capture_regs.a_clk, t.quant_regs.a_clk, t.quant_regs.a_cp);
    StampLiveOkSignCong(body, t.capture_regs.a_clk, t.quant_regs.a_clk, t.quant_regs.a_cp, tB.quant_regs.a_cp);
    LooksCapUnsetFXR(body, t.capture_regs.a_clk);
    reveal PSM.BestLiveRE;
  }

  // ===========================================================================
  // 4. The other FinalReadout register premises.
  // ===========================================================================

  function Rg(t: AI.Thread): NRC.Regs3 { (t.capture_regs, t.look_regs, t.quant_regs) }

  lemma CoversWfMirror(body: R.regex, t: AI.Thread, n: nat)
    ensures NRR.Covers(FST.FXR(body), Rg(t)) <==> NRR.Covers(body, Rg(MIR.MirrorThread(t, n)))
    ensures NRR.WfRegs(Rg(t)) <==> NRR.WfRegs(Rg(MIR.MirrorThread(t, n)))
  {
    IdsFXR(body);
    MirrorGetIdx(t.capture_regs, n, 0); MirrorGetIdx(t.look_regs, n, 0); MirrorGetIdx(t.quant_regs, n, 0);
  }

  lemma OnlyCapIdsSetMirror(body: R.regex, t: AI.Thread, n: nat)
    requires forall k: int :: AI.get_idx(t.capture_regs.a_cp, k) <= n
    ensures NRO.OnlyCapIdsSet(FST.FXR(body), Rg(t)) <==> NRO.OnlyCapIdsSet(body, Rg(MIR.MirrorThread(t, n)))
  {
    IdsFXR(body);
    MirrorSign(t.capture_regs, n);
  }

  lemma ThreadRegsWfMirror(t: AI.Thread, n: nat, ncap: int, nlook: int, nquant: int)
    requires forall k: int :: AI.get_idx(t.capture_regs.a_cp, k) <= n
    ensures CM.ThreadRegsWf(t, ncap, nlook, nquant) <==> CM.ThreadRegsWf(MIR.MirrorThread(t, n), ncap, nlook, nquant)
  {
    var c := t.capture_regs;
    var cB := MIR.MirrorRegs(c, n);
    MirrorSign(c, n);
    forall k: int ensures AI.get_idx(cB.a_cp, k) >= -1 <==> AI.get_idx(c.a_cp, k) >= -1 {
      MirrorGetIdx(c, n, k);
    }
    MirrorGetIdx(t.capture_regs, n, 0); MirrorGetIdx(t.look_regs, n, 0); MirrorGetIdx(t.quant_regs, n, 0);
    assert PIV.CapRegWf(c) <==> PIV.CapRegWf(cB);
  }

  /** StampsLocal (derived INSIDE FinalReadout, not a premise) transports too;
      the real side's body map comes from the real table's QmapOk (as
      FinalReadout itself derives it), the mirrored table is not consulted. */
  lemma StampsLocalMirror(qm: AR.QMap, qm': AR.QMap, body: R.regex, str: string, rstr: string,
                          t: AI.Thread, n: nat)
    requires PIV.QuantUnique(body) && |str| == n && |rstr| == n
    requires T.TransWf(body) && AR.QmapOk(body, qm)
    requires forall k: int :: AI.get_idx(t.quant_regs.a_cp, k) <= n
    requires NRO.StampsLocal(qm', FST.FXR(body), rstr, Rg(t), -1)
    ensures NRO.StampsLocal(qm, body, str, Rg(MIR.MirrorThread(t, n)), -1)
  {
    var tB := MIR.MirrorThread(t, n);
    IdsFXR(body);
    MirrorSign(t.quant_regs, n);
    forall q: nat | q in PIV.QuantIds(body) && AI.get_idx(Rg(tB).2.a_cp, q) >= 0
      ensures NRR.QidCinPlus(body, q)
              && 0 <= AI.get_idx(Rg(tB).2.a_cp, q) <= |str|
              && (q as int) in qm.bodies && qm.bodies[q as int] == PIV.QidBody(body, q)
              && (PIV.QChainFresh(body, Rg(tB).2.a_clk, -1, q) ==>
                    PIV.PathPresentQ(body, Rg(tB).0.a_clk, Rg(tB).2.a_clk, -1, q)
                    && NRR.RegsStale(PIV.QidBody(body, q), Rg(tB), AI.get_idx(Rg(tB).2.a_clk, q)))
    {
      PathsFXR(body, t.capture_regs.a_clk, t.quant_regs.a_clk, -1, q);
      PIV.QmapOkBodyAtQid(body, qm, q);
      assert AI.get_idx(t.quant_regs.a_cp, q) >= 0;
      RegsStaleFXR(PIV.QidBody(body, q), Rg(t), AI.get_idx(t.quant_regs.a_clk, q));
      assert NRR.RegsStale(PIV.QidBody(body, q), Rg(tB), AI.get_idx(Rg(tB).2.a_clk, q))
         == NRR.RegsStale(PIV.QidBody(body, q), Rg(t), AI.get_idx(t.quant_regs.a_clk, q));
      MirrorGetIdx(t.quant_regs, n, q);
    }
  }

  // ===========================================================================
  // 5. P2(a): RegsFinalOk across the mirror. Needs the CAPTURE bound (the
  //    quant half is self-bounding); `RegsFinalOkMirrorNeedsCapBound` shows
  //    the capture bound cannot be dropped.
  // ===========================================================================

  lemma RegsFinalOkMirror(t: AI.Thread, n: nat, Q: set<int>)
    requires forall k: int :: AI.get_idx(t.capture_regs.a_cp, k) <= n
    requires FV.RegsFinalOk(t, n, Q)
    ensures FV.RegsFinalOk(MIR.MirrorThread(t, n), n, Q)
  {
    var tB := MIR.MirrorThread(t, n);
    MirrorSign(t.capture_regs, n);
    forall q: int | AI.get_idx(tB.quant_regs.a_cp, q) >= 0
      ensures AI.get_idx(tB.quant_regs.a_cp, q) <= n && q in Q
    {
      MirrorGetIdx(t.quant_regs, n, q);
    }
    assert tB.capture_regs.a_clk == t.capture_regs.a_clk && tB.quant_regs.a_clk == t.quant_regs.a_clk;
  }

  /** Both bounds give the converse as well (the mirror is an involution there). */
  lemma RegsFinalOkMirrorIff(t: AI.Thread, n: nat, Q: set<int>)
    requires forall k: int :: AI.get_idx(t.capture_regs.a_cp, k) <= n
    requires forall k: int :: AI.get_idx(t.quant_regs.a_cp, k) <= n
    ensures FV.RegsFinalOk(MIR.MirrorThread(t, n), n, Q) <==> FV.RegsFinalOk(t, n, Q)
  {
    var tB := MIR.MirrorThread(t, n);
    MirrorSign(t.capture_regs, n);
    MirrorSign(t.quant_regs, n);
    if FV.RegsFinalOk(tB, n, Q) {
      forall q: int | AI.get_idx(t.quant_regs.a_cp, q) >= 0
        ensures AI.get_idx(t.quant_regs.a_cp, q) <= n && q in Q
      {
        MirrorGetIdx(t.quant_regs, n, q);
      }
    }
    if FV.RegsFinalOk(t, n, Q) { RegsFinalOkMirror(t, n, Q); }
  }

  lemma RegsFinalOkMirrorNeedsCapBound()
    ensures var t := AI.Thread(0, AReg.ARegs([1], [0]), AReg.ARegs([], []), AReg.ARegs([], []), false);
            FV.RegsFinalOk(t, 0, {}) && !FV.RegsFinalOk(MIR.MirrorThread(t, 0), 0, {})
  {
    var t := AI.Thread(0, AReg.ARegs([1], [0]), AReg.ARegs([], []), AReg.ARegs([], []), false);
    var tB := MIR.MirrorThread(t, 0);
    assert tB.capture_regs.a_cp == [-1];
    assert AI.get_idx(tB.capture_regs.a_clk, 0) == 0 && AI.get_idx(tB.capture_regs.a_cp, 0) == -1;
    forall k: int ensures AI.get_idx(t.capture_regs.a_clk, k) < 0 <==> AI.get_idx(t.capture_regs.a_cp, k) < 0 {}
  }

  // ===========================================================================
  // 6. P2(b): the direction-generic twin of FV.FFindMatchRegsFinal. Only the
  //    termination measure and the cp bookkeeping change; the per-phase
  //    lemmas FV.FAdvanceEpsilonRegsFinal / FV.FConsumeRegsFinal already take
  //    any `dir`.
  // ===========================================================================

  lemma FFindMatchRegsFinalAny(c: RB.code, str: string, s: AI.VmState, ov: LOr.OracleView,
                               dir: LAnc.direction, cdn: LCdn.cdns, Q: set<int>)
    requires |s.processed.true_set| == RB.size(c) && |s.processed.false_set| == RB.size(c)
    requires FV.TrueStampsIn(c, Q)
    requires dir.Forward? ==> s.context.nextchar == AI.get_char(str, s.cp)
    requires dir.Backward? ==> s.context.nextchar == AI.get_char(str, s.cp - 1)
    requires 0 <= s.cp <= |str| && s.clock >= 0
    requires FV.VmRegsFinalOk(s, |str|, Q)
    ensures var r := AI.FFindMatch(c, str, s, ov, dir, cdn).0;
      r.Some? ==> FV.RegsFinalOk(r.value, |str|, Q)
    decreases if dir.Forward? then |str| - s.cp else s.cp
  {
    var s0 := s.(cdn := LCdn.build_cdn_v(cdn, s.cp, ov, s.context, dir));
    assert FV.VmRegsFinalOk(s0, |str|, Q);
    var (s1, ov1) := AI.FAdvanceEpsilon(c, s0, ov, dir);
    FV.FAdvanceEpsilonRegsFinal(c, s0, ov, dir, |str|, Q);
    CM.FAdvanceEpsilonClockGrows(c, s0, ov, dir);
    assert FV.VmRegsFinalOk(s1, |str|, Q);
    if |s1.blocked| == 0 { return; }
    match s1.context.nextchar {
      case None =>
      case Some(_) =>
        var s2 := AI.FConsume(s1);
        FV.FConsumeRegsFinal(s1, |str|, Q);
        CM.FConsumeClockSame(s1);
        var s3 := s2.(processed := AI.init_bpcset(RB.size(c)), isblocked := AI.init_pcset(RB.size(c)),
                      cdn := LCdn.init_cdn(), cp := AI.incr_cp(s2.cp, dir));
        var newchar := AI.get_char(str, s3.cp - AI.cp_offset(dir));
        var s4 := s3.(context := LAnc.update_context(s3.context, newchar));
        if dir.Forward? {
          assert s.cp < |str|;
          assert s4.cp == s.cp + 1;
        } else {
          assert s.cp > 0;
          assert s4.cp == s.cp - 1;
        }
        assert FV.VmRegsFinalOk(s4, |str|, Q);
        FFindMatchRegsFinalAny(c, str, s4, ov1, dir, cdn, Q);
    }
  }

  // ===========================================================================
  // 7. P3: the true-stamp inventories (Q = CinQids(body)) of the two codes.
  // ===========================================================================

  /** Mirror world: compile(FXR(body)). */
  lemma FXRTrueStampsCin(body: R.regex)
    requires NR.NestedFragmentRE(body) && PIV.QuantUnique(body)
    ensures FV.TrueStampsIn(CP.compile_to_bytecode(FST.FXR(body)), FRD.CinQids(body))
  {
    FST.XRVNestedFragment(body);
    FST.FlipNestedFragment(FST.XRV(body));
    assert NR.NestedFragmentRE(FST.FXR(body));
    QuantUniqueFXR(body);
    CinQidsFXR(body);
    var endl := FST.FXRCompileFacts(body);
    FRD.NestedNoCdnPlus(FST.FXR(body));   // (G5a) TrueStampsInCin's premise
    FRD.TrueStampsInCin(FST.FXR(body), CP.compile_to_bytecode(FST.FXR(body)), endl);
  }

  lemma RevIds(r: R.regex)
    ensures PIV.QuantIds(R.reverse_regex(r)) == PIV.QuantIds(r)
    decreases r
  {
    match r
    case Re_alt(a, b) => RevIds(a); RevIds(b);
    case Re_con(a, b) => RevIds(a); RevIds(b);
    case Re_quant(_, _, _, a) => RevIds(a);
    case Re_capture(_, a) => RevIds(a);
    case Re_lookaround(_, _, a) => RevIds(a);
    case _ =>
  }

  lemma RevQuantUnique(r: R.regex)
    requires PIV.QuantUnique(r)
    ensures PIV.QuantUnique(R.reverse_regex(r))
    decreases r
  {
    match r
    case Re_alt(a, b) => RevIds(a); RevIds(b); RevQuantUnique(a); RevQuantUnique(b);
    case Re_con(a, b) => RevIds(a); RevIds(b); RevQuantUnique(a); RevQuantUnique(b);
    case Re_quant(_, _, _, a) => RevIds(a); RevQuantUnique(a);
    case Re_capture(_, a) => RevQuantUnique(a);
    case Re_lookaround(_, _, a) => RevQuantUnique(a);
    case _ =>
  }

  lemma RevCinPlus(r: R.regex, q: nat)
    requires PIV.QuantUnique(r) && q in PIV.QuantIds(r)
    ensures q in PIV.QuantIds(R.reverse_regex(r))
    ensures NRR.QidCinPlus(R.reverse_regex(r), q) == NRR.QidCinPlus(r, q)
    decreases r
  {
    RevIds(r);
    match r
    case Re_alt(a, b) =>
      RevIds(a); RevIds(b);
      if q in PIV.QuantIds(a) { RevCinPlus(a, q); } else { RevCinPlus(b, q); }
    case Re_con(a, b) =>
      RevIds(a); RevIds(b);
      assert PIV.QuantIds(a) * PIV.QuantIds(b) == {};
      if q in PIV.QuantIds(a) {
        assert q !in PIV.QuantIds(b) by { assert q !in PIV.QuantIds(a) * PIV.QuantIds(b); }
        RevCinPlus(a, q);
      } else {
        RevCinPlus(b, q);
      }
    case Re_quant(_, qid0, _, a) =>
      if qid0 >= 0 && (qid0 as nat) == q {} else { RevCinPlus(a, q); }
    case Re_capture(_, a) => RevCinPlus(a, q);
    case Re_lookaround(_, _, a) => RevCinPlus(a, q);
    case _ =>
  }

  lemma RevCinQids(r: R.regex)
    requires PIV.QuantUnique(r)
    ensures FRD.CinQids(R.reverse_regex(r)) == FRD.CinQids(r)
  {
    RevIds(r);
    forall x | x in FRD.CinQids(R.reverse_regex(r)) ensures x in FRD.CinQids(r) {
      var q: nat :| q in PIV.QuantIds(R.reverse_regex(r)) && NRR.QidCinPlus(R.reverse_regex(r), q) && q as int == x;
      RevCinPlus(r, q);
    }
    forall x | x in FRD.CinQids(r) ensures x in FRD.CinQids(R.reverse_regex(r)) {
      var q: nat :| q in PIV.QuantIds(r) && NRR.QidCinPlus(r, q) && q as int == x;
      RevCinPlus(r, q);
    }
  }

  /** Real world: compile(reverse_regex(body)), the lookbehind capture code. */
  lemma RevTrueStampsCin(body: R.regex)
    requires NR.NestedFragmentRE(body) && PIV.QuantUnique(body)
    ensures FV.TrueStampsIn(CP.compile_to_bytecode(R.reverse_regex(body)), FRD.CinQids(body))
  {
    var rb := R.reverse_regex(body);
    NR.ReverseNestedFragmentRE(body);
    NR.CompileToBytecodeRepNested(rb);
    var next := CP.compile(rb, 0, CP.Progress).1;
    RevQuantUnique(body);
    RevCinQids(body);
    FRD.NestedNoCdnPlus(rb);   // (G5a) TrueStampsInCin's premise
    FRD.TrueStampsInCin(rb, CP.compile_to_bytecode(rb), next as nat);
  }

  // ===========================================================================
  // 8. P3: the instantiations.
  // ===========================================================================

  /** (a) FV.FFindMatchRegsFinal AS IS (Forward) at FXR(body) / Reverse(str) /
      MirrorRegs(entry banks), entry banks = the fresh row's init banks (the
      run LBEngineLeafFlip and W1's RowTieLB name). The entry premise holds. */
  lemma MirrorRowEntryRegsFinal(body: R.regex, str: string, cp: nat, ov: LOr.OracleView, cdns: LCdn.cdns,
                                ncap: int, nlook: int, nquant: int)
    requires cp <= |str| && |ov| == |str| + 1
    requires NR.NestedFragmentRE(body) && PIV.QuantUnique(body)
    ensures |LC.Reverse(str)| == |str|
    ensures var n := |str|; var rstr := LC.Reverse(str); var mcp := n - cp;
      var bcF := CP.compile_to_bytecode(FST.FXR(body));
      var sF := AI.FInitState(bcF, mcp, MIR.MirrorRegs(AReg.init_regs(ncap), n),
                              MIR.MirrorRegs(AReg.init_regs(nlook), n), MIR.MirrorRegs(AReg.init_regs(nquant), n),
                              0, AI.cp_context(mcp, rstr, LAnc.Forward));
      FV.VmRegsFinalOk(sF, n, FRD.CinQids(body))
      && (var rfF := AI.FFindMatch(bcF, rstr, sF, MIR.MirrorView(ov, n), LAnc.Forward, cdns).0;
          rfF.Some? ==> FV.RegsFinalOk(rfF.value, n, FRD.CinQids(body)))
  {
    var n := |str|;
    MIR.ReverseLen(str);
    var rstr := LC.Reverse(str);
    var mcp := n - cp;
    var Q := FRD.CinQids(body);
    FXRTrueStampsCin(body);
    var bcF := CP.compile_to_bytecode(FST.FXR(body));
    MIR.MirrorInitRegs(ncap, n); MIR.MirrorInitRegs(nlook, n); MIR.MirrorInitRegs(nquant, n);
    FV.RegsFinalOkInit(ncap, nlook, nquant, n, Q);
    var sF := AI.FInitState(bcF, mcp, AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant),
                            0, AI.cp_context(mcp, rstr, LAnc.Forward));
    assert FV.VmRegsFinalOk(sF, n, Q) by {
      assert sF.active == [AI.init_thread(AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant))];
    }
    FV.FFindMatchRegsFinal(bcF, rstr, sF, MIR.MirrorView(ov, n), LAnc.Forward, cdns, Q);
  }

  /** (b) The twin, directly on the REAL backward fresh run: no mirror, no bound. */
  lemma BackRowEntryRegsFinal(body: R.regex, str: string, cp: nat, ov: LOr.OracleView, cdns: LCdn.cdns,
                              ncap: int, nlook: int, nquant: int)
    requires cp <= |str|
    requires NR.NestedFragmentRE(body) && PIV.QuantUnique(body)
    ensures var bcB := CP.compile_to_bytecode(R.reverse_regex(body));
      var sB := AI.FInitState(bcB, cp, AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant),
                              0, AI.cp_context(cp, str, LAnc.Backward));
      FV.VmRegsFinalOk(sB, |str|, FRD.CinQids(body))
      && (var raB := AI.FFindMatch(bcB, str, sB, ov, LAnc.Backward, cdns).0;
          raB.Some? ==> FV.RegsFinalOk(raB.value, |str|, FRD.CinQids(body)))
  {
    var Q := FRD.CinQids(body);
    RevTrueStampsCin(body);
    var bcB := CP.compile_to_bytecode(R.reverse_regex(body));
    FV.RegsFinalOkInit(ncap, nlook, nquant, |str|, Q);
    var sB := AI.FInitState(bcB, cp, AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant),
                            0, AI.cp_context(cp, str, LAnc.Backward));
    assert FV.VmRegsFinalOk(sB, |str|, Q) by {
      assert sB.active == [AI.init_thread(AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant))];
    }
    FFindMatchRegsFinalAny(bcB, str, sB, ov, LAnc.Backward, cdns, Q);
  }

  /** The same entry premise for RUNNING banks reduces to RegsFinalOk of the
      entry thread on the real side plus the capture bound (P2(a) on the entry
      thread); with the loop's `qt.a_cp < 0` it needs no Q choice. */
  lemma MirrorEntryRunning(cap: AReg.Regs, lk: AReg.Regs, qt: AReg.Regs, n: nat, Q: set<int>)
    requires forall k: int :: AI.get_idx(cap.a_cp, k) <= n
    requires FV.RegsFinalOk(AI.init_thread(cap, lk, qt), n, Q)
    ensures FV.RegsFinalOk(AI.init_thread(MIR.MirrorRegs(cap, n), MIR.MirrorRegs(lk, n), MIR.MirrorRegs(qt, n)), n, Q)
  {
    var t := AI.init_thread(cap, lk, qt);
    RegsFinalOkMirror(t, n, Q);
    assert MIR.MirrorThread(t, n)
        == AI.init_thread(MIR.MirrorRegs(cap, n), MIR.MirrorRegs(lk, n), MIR.MirrorRegs(qt, n));
  }
}

// =============================================================================
// 9. The composed row-level statement over W1's per-row tie (MirrorWorld.dfy,
//    passed as a library source): at a lookbehind row, EVERY register premise
//    of FinalReadout at the real backward fresh winner raB is equivalent to the
//    same premise on FXR(body) at the mirrored forward fresh winner rfF.
// =============================================================================
module LindenElkBackRowPremises {
  import opened Std.Wrappers
  import R = RegElkRegex
  import CP = Compiler
  import AI = ArrayInterp
  import AReg = Array_Regs
  import LOr = Oracle
  import LC = Chars
  import PIV = LindenElkPikeInv
  import MIR = LindenElkMirror
  import FST = LindenElkFlipStatics
  import PSM = LindenElkPikeSim
  import NRR = LindenElkNulledReconRegs
  import NRO = LindenElkNulledReconReadout
  import FV = LindenElkFinalVm
  import CM = LindenElkClockMono
  import M = LindenElkMain
  import FG = LindenElkFlipGate
  import MW = LindenElkMirrorWorld
  import W = LindenElkBackRowResidue

  lemma CpsInBound(r: AReg.Regs, n: nat)
    requires MW.CpsIn(r, n)
    ensures forall k: int :: AI.get_idx(r.a_cp, k) <= n
  {}

  lemma CpsInMirror(r: AReg.Regs, n: nat)
    requires MW.CpsIn(r, n)
    ensures MW.CpsIn(MIR.MirrorRegs(r, n), n)
  {}

  lemma RowPremisesLB(crv: CP.FCompiled, str: string, l: int, lk: AReg.Regs, ov: LOr.OracleView,
                      ncap: int, nlook: int, nquant: int, Q: set<int>)
    requires |crv.f_look_types| == |crv.f_look_ast|
    requires MW.RowOk(crv, l) && crv.f_look_types[l] == R.Lookbehind
    requires |ov| == |str| + 1
    requires AReg.get_cp(lk, l).Some? && CM.LookCpsLE(lk, |str|)
    requires PIV.QuantUnique(crv.f_look_ast[l])
    ensures var n := |str|; var body := crv.f_look_ast[l];
      var raB := M.FreshBodyMatch(crv, str, l, lk, ov, ncap, nlook, nquant);
      var rfF := M.FreshBodyMatch(FG.MirrorTables(crv), LC.Reverse(str), l, MIR.MirrorRegs(lk, n),
                                  MIR.MirrorView(ov, n), ncap, nlook, nquant);
      (raB.Some? <==> rfF.Some?)
      && (raB.Some? ==>
            raB.value == MIR.MirrorThread(rfF.value, n)
            && (PSM.BestLiveRE(FST.FXR(body), rfF.value) <==> PSM.BestLiveRE(body, raB.value))
            && (NRR.Covers(FST.FXR(body), W.Rg(rfF.value)) <==> NRR.Covers(body, W.Rg(raB.value)))
            && (NRR.WfRegs(W.Rg(rfF.value)) <==> NRR.WfRegs(W.Rg(raB.value)))
            && (NRO.OnlyCapIdsSet(FST.FXR(body), W.Rg(rfF.value)) <==> NRO.OnlyCapIdsSet(body, W.Rg(raB.value)))
            && (CM.ThreadRegsWf(rfF.value, ncap, nlook, nquant) <==> CM.ThreadRegsWf(raB.value, ncap, nlook, nquant))
            && (FV.RegsFinalOk(rfF.value, n, Q) <==> FV.RegsFinalOk(raB.value, n, Q)))
  {
    var n := |str|;
    var body := crv.f_look_ast[l];
    MW.RowTieLB(crv, str, l, lk, ov, ncap, nlook, nquant);
    var raB := M.FreshBodyMatch(crv, str, l, lk, ov, ncap, nlook, nquant);
    var rfF := M.FreshBodyMatch(FG.MirrorTables(crv), LC.Reverse(str), l, MIR.MirrorRegs(lk, n),
                                MIR.MirrorView(ov, n), ncap, nlook, nquant);
    assert rfF == MW.MirrorOpt(raB, n);
    if raB.Some? {
      assert AReg.get_cp(lk, l).value <= |str| by {
        assert AI.get_idx(lk.a_cp, l) <= |str|;
      }
      MW.FreshBodyMatchCpsIn(crv, str, l, lk, ov, ncap, nlook, nquant);
      var tB := raB.value;
      var tF := rfF.value;
      assert tF == MIR.MirrorThread(tB, n);
      MW.MirrorThreadInvol(tB, n);
      assert tB == MIR.MirrorThread(tF, n);
      CpsInMirror(tB.capture_regs, n); CpsInMirror(tB.quant_regs, n);
      CpsInBound(tF.capture_regs, n); CpsInBound(tF.quant_regs, n);
      W.BestLiveREMirror(body, tF, n);
      W.CoversWfMirror(body, tF, n);
      W.OnlyCapIdsSetMirror(body, tF, n);
      W.ThreadRegsWfMirror(tF, n, ncap, nlook, nquant);
      W.RegsFinalOkMirrorIff(tF, n, Q);
    }
  }
}
