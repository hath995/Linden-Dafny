// L3b item 4, step 2 (the engine-side GmOfLive commutation): the capture-reset
// filter commutes with the position mirror `v |-> n - v`.
//
// `filter_capture` decides every reset by comparing CLOCKS (never positions)
// and its only write to the capture array is `-1` (via `filter_all` / the
// stale-start reset). `MirrorRegs` remaps POSITIONS and leaves clocks alone,
// and `MirrorCpVal(-1) == -1`. So filtering the mirrored bank yields the mirror
// of the filtered bank — the register-level half of reconciling the backward
// replay's `GmOfLive` with the forward `RevRE`-run's, before `LiveRange` reads
// out (where the reversed-lookbehind-span orientation then enters).

include "BackValue.dfy"
include "PikeInvRE.dfy"

module LindenBackGmMirror {
  import opened Std.Wrappers
  import R = RegElkRegex
  import CP = Compiler
  import AI = ArrayInterp
  import AReg = Array_Regs
  import MIR = LindenElkMirror
  import SD = LindenSpanDuality
  import BV = LindenElkBackValue
  import PIV = LindenElkPikeInv
  import LG = Groups

  /** The pointwise position mirror on a raw register array. */
  function MirrorArr(a: seq<int>, n: int): seq<int> {
    seq(|a|, i requires 0 <= i < |a| => MIR.MirrorCpVal(a[i], n))
  }

  lemma MirrorArrLen(a: seq<int>, n: int)
    ensures |MirrorArr(a, n)| == |a|
  {}

  /** Writing `-1` commutes with the mirror (`MirrorCpVal(-1) == -1`). */
  lemma MirrorArrSetNeg(a: seq<int>, k: int, n: int)
    ensures AI.set_idx(MirrorArr(a, n), k, -1) == MirrorArr(AI.set_idx(a, k, -1), n)
  {
    var lhs := AI.set_idx(MirrorArr(a, n), k, -1);
    var rhs := MirrorArr(AI.set_idx(a, k, -1), n);
    assert |lhs| == |a| && |rhs| == |a|;
    forall i | 0 <= i < |a| ensures lhs[i] == rhs[i] {
      if i == k {
        assert MIR.MirrorCpVal(-1, n) == -1;
      }
    }
  }

  /** `filter_all` only writes `-1` (to start registers), so it commutes with
      the mirror. */
  lemma FilterAllMirror(r: R.regex, a: seq<int>, n: int)
    ensures AI.filter_all(r, MirrorArr(a, n)) == MirrorArr(AI.filter_all(r, a), n)
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      FilterAllMirror(r1, a, n);
      FilterAllMirror(r2, AI.filter_all(r1, a), n);
    case Re_con(r1, r2) =>
      FilterAllMirror(r1, a, n);
      FilterAllMirror(r2, AI.filter_all(r1, a), n);
    case Re_quant(_, _, _, r1) => FilterAllMirror(r1, a, n);
    case Re_capture(cid, r1) =>
      MirrorArrSetNeg(a, CP.start_reg(cid), n);
      FilterAllMirror(r1, AI.set_idx(a, CP.start_reg(cid), -1), n);
    case Re_lookaround(_, _, r1) => FilterAllMirror(r1, a, n);
    case _ =>
  }

  /** THE COMMUTATION: `filter_capture` on the mirrored bank is the mirror of
      `filter_capture` on the bank — the branch decisions read only the
      (unmirrored) clocks, and the only writes are `-1`. */
  lemma FilterCaptureMirror(r: R.regex, a: seq<int>, cc: seq<int>, lc: seq<int>,
                            qc: seq<int>, mc: int, n: int)
    ensures AI.filter_capture(r, MirrorArr(a, n), cc, lc, qc, mc)
         == MirrorArr(AI.filter_capture(r, a, cc, lc, qc, mc), n)
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      FilterCaptureMirror(r1, a, cc, lc, qc, mc, n);
      FilterCaptureMirror(r2, AI.filter_capture(r1, a, cc, lc, qc, mc), cc, lc, qc, mc, n);
    case Re_con(r1, r2) =>
      FilterCaptureMirror(r1, a, cc, lc, qc, mc, n);
      FilterCaptureMirror(r2, AI.filter_capture(r1, a, cc, lc, qc, mc), cc, lc, qc, mc, n);
    case Re_quant(nul, qid, quant, r1) =>
      var quant_val := AI.get_idx(qc, qid);
      if quant_val < mc {
        FilterAllMirror(r1, a, n);
      } else {
        FilterCaptureMirror(r1, a, cc, lc, qc, quant_val, n);
      }
    case Re_capture(cid, r1) =>
      var start := AI.get_idx(cc, CP.start_reg(cid));
      if start < 0 {
        FilterAllMirror(r1, a, n);
      } else if start < mc {
        MirrorArrSetNeg(a, CP.start_reg(cid), n);
        FilterAllMirror(r1, AI.set_idx(a, CP.start_reg(cid), -1), n);
      } else {
        FilterCaptureMirror(r1, a, cc, lc, qc, mc, n);
      }
    case Re_lookaround(lid, l, r1) =>
      var look_val := AI.get_idx(lc, lid);
      if look_val < 0 {
        FilterAllMirror(r1, a, n);
      } else if look_val < mc {
        FilterAllMirror(r1, a, n);
      } else {
        FilterCaptureMirror(r1, a, cc, lc, qc, -1, n);
      }
    case _ =>
  }

  /** Lifted to `filter_reset`: filtering the mirrored capture bank (clocks and
      the look/quant banks unchanged) is the mirror of the filtered bank.
      `MirrorRegs` keeps `a_clk`, so the clock arrays that drive every reset
      decision are identical on both sides. */
  lemma FilterResetMirror(r: R.regex, cap: AReg.Regs, look: AReg.Regs, quant: AReg.Regs,
                          mc: int, n: int)
    ensures AI.filter_reset(r, MIR.MirrorRegs(cap, n), look, quant, mc)
         == MirrorArr(AI.filter_reset(r, cap, look, quant, mc), n)
  {
    var cr := AReg.as_arrays(cap).0;
    var cc := AReg.as_arrays(cap).1;
    assert MIR.MirrorRegs(cap, n).a_cp == MirrorArr(cr, n);
    assert AReg.as_arrays(MIR.MirrorRegs(cap, n)) == (MirrorArr(cr, n), cc);
    FilterCaptureMirror(r, cr, cc, AReg.as_arrays(look).1, AReg.as_arrays(quant).1, mc, n);
  }

  // ===========================================================================
  // The reversed-span (raw) range mirror, and GmOfLive commutation
  // ===========================================================================

  /** `MirrorCpVal` preserves sign for in-bounds values. */
  lemma MirrorCpValSign(v: int, n: nat)
    requires v <= n
    ensures MIR.MirrorCpVal(v, n) >= 0 <==> v >= 0
  {}

  /** `get_idx` commutes with the array mirror (out-of-range gives `-1` on both,
      `MirrorCpVal(-1) == -1`). */
  lemma GetIdxMirror(f: seq<int>, k: int, n: int)
    ensures AI.get_idx(MirrorArr(f, n), k) == MIR.MirrorCpVal(AI.get_idx(f, k), n)
  {
    assert |MirrorArr(f, n)| == |f|;
    if 0 <= k < |f| {
    } else {
      assert MIR.MirrorCpVal(-1, n) == -1;
    }
  }

  /** `filter_all` keeps every register `<= n` (it only writes `-1 <= n`). */
  lemma FilterAllLeN(r: R.regex, a: seq<int>, n: nat)
    requires forall i :: AI.get_idx(a, i) <= n
    ensures forall i :: AI.get_idx(AI.filter_all(r, a), i) <= n
    decreases r
  {
    match r
    case Re_alt(r1, r2) => FilterAllLeN(r1, a, n); FilterAllLeN(r2, AI.filter_all(r1, a), n);
    case Re_con(r1, r2) => FilterAllLeN(r1, a, n); FilterAllLeN(r2, AI.filter_all(r1, a), n);
    case Re_quant(_, _, _, r1) => FilterAllLeN(r1, a, n);
    case Re_capture(cid, r1) =>
      SetIdxLeN(a, CP.start_reg(cid), n);
      FilterAllLeN(r1, AI.set_idx(a, CP.start_reg(cid), -1), n);
    case Re_lookaround(_, _, r1) => FilterAllLeN(r1, a, n);
    case _ =>
  }

  lemma SetIdxLeN(a: seq<int>, k: int, n: nat)
    requires forall i :: AI.get_idx(a, i) <= n
    ensures forall i :: AI.get_idx(AI.set_idx(a, k, -1), i) <= n
  {
    var b := AI.set_idx(a, k, -1);
    forall i ensures AI.get_idx(b, i) <= n {
      if 0 <= i < |b| && i != k {
        assert AI.get_idx(b, i) == AI.get_idx(a, i);
      }
    }
  }

  /** `filter_capture` keeps every register `<= n`. */
  lemma FilterCaptureLeN(r: R.regex, a: seq<int>, cc: seq<int>, lc: seq<int>,
                         qc: seq<int>, mc: int, n: nat)
    requires forall i :: AI.get_idx(a, i) <= n
    ensures forall i :: AI.get_idx(AI.filter_capture(r, a, cc, lc, qc, mc), i) <= n
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      FilterCaptureLeN(r1, a, cc, lc, qc, mc, n);
      FilterCaptureLeN(r2, AI.filter_capture(r1, a, cc, lc, qc, mc), cc, lc, qc, mc, n);
    case Re_con(r1, r2) =>
      FilterCaptureLeN(r1, a, cc, lc, qc, mc, n);
      FilterCaptureLeN(r2, AI.filter_capture(r1, a, cc, lc, qc, mc), cc, lc, qc, mc, n);
    case Re_quant(nul, qid, quant, r1) =>
      var quant_val := AI.get_idx(qc, qid);
      if quant_val < mc { FilterAllLeN(r1, a, n); }
      else { FilterCaptureLeN(r1, a, cc, lc, qc, quant_val, n); }
    case Re_capture(cid, r1) =>
      var start := AI.get_idx(cc, CP.start_reg(cid));
      if start < 0 { FilterAllLeN(r1, a, n); }
      else if start < mc { SetIdxLeN(a, CP.start_reg(cid), n); FilterAllLeN(r1, AI.set_idx(a, CP.start_reg(cid), -1), n); }
      else { FilterCaptureLeN(r1, a, cc, lc, qc, mc, n); }
    case Re_lookaround(lid, l, r1) =>
      var look_val := AI.get_idx(lc, lid);
      if look_val < 0 { FilterAllLeN(r1, a, n); }
      else if look_val < mc { FilterAllLeN(r1, a, n); }
      else { FilterCaptureLeN(r1, a, cc, lc, qc, -1, n); }
    case _ =>
  }

  /** The engine's RAW readout mirror: `LiveRange`/`RangeFromArr` read
      `start_reg`/`end_reg` POSITIONALLY, so over mirrored caps a closed group
      reads out REVERSED — `Range(s, Some e) |-> Range(n-s, Some(n-e))`. This is
      the reversed-lookbehind-span quirk; the ordered spec mirror (`MirrorRange`)
      is `Range(n-e, Some(n-s))`, reconciled by the widened `NormalizeArr`. */
  function RawMirrorRange(rg: LG.Range, n: nat): LG.Range
    requires rg.startIdx <= n
    requires rg.endIdx.Some? ==> rg.endIdx.value <= n
  {
    match rg.endIdx
    case None => LG.Range(n - rg.startIdx, None)
    case Some(e) => LG.Range(n - rg.startIdx, Some(n - e))
  }

  ghost predicate GmLeN(gm: LG.GroupMap, n: nat) {
    forall g :: g in gm ==>
      gm[g].startIdx <= n && (gm[g].endIdx.Some? ==> gm[g].endIdx.value <= n)
  }

  ghost function RawMirrorGm(gm: LG.GroupMap, n: nat): LG.GroupMap
    requires GmLeN(gm, n)
  {
    map g | g in gm :: RawMirrorRange(gm[g], n)
  }

  /** One group's `LiveRange` over the mirrored array is the raw-mirror of its
      `LiveRange` over the array. */
  lemma LiveRangeMirror(f: seq<int>, cc: seq<int>, gid: nat, n: nat)
    requires AI.get_idx(f, CP.start_reg(gid)) >= 0
    requires AI.get_idx(f, CP.start_reg(gid)) <= n
    requires AI.get_idx(f, CP.end_reg(gid)) <= n
    ensures AI.get_idx(MirrorArr(f, n), CP.start_reg(gid)) >= 0
    ensures PIV.LiveRange(MirrorArr(f, n), cc, gid)
         == RawMirrorRange(PIV.LiveRange(f, cc, gid), n)
  {
    GetIdxMirror(f, CP.start_reg(gid), n);
    GetIdxMirror(f, CP.end_reg(gid), n);
    MirrorCpValSign(AI.get_idx(f, CP.end_reg(gid)), n);
    assert AI.get_idx(MirrorArr(f, n), CP.start_reg(gid)) == n - AI.get_idx(f, CP.start_reg(gid));
  }

  /** THE STEP-2 PAYOFF: the backward replay's `GmOfLive` (over the mirrored
      capture bank) is the raw-span mirror of the forward run's `GmOfLive` —
      same domain, each range reversed-span-mirrored. Clocks (hence the reset
      shape and the present-set) are identical because `MirrorRegs` keeps
      `a_clk`; only the positions reflect. */
  lemma GmOfLiveMirror(body: R.regex, cap: AReg.Regs, look: AReg.Regs, quant: AReg.Regs, n: nat)
    requires forall k :: AI.get_idx(AReg.as_arrays(cap).0, k) <= n
    ensures GmLeN(PIV.GmOfLive(body, cap, look, quant), n)
    ensures PIV.GmOfLive(body, MIR.MirrorRegs(cap, n), look, quant)
         == RawMirrorGm(PIV.GmOfLive(body, cap, look, quant), n)
  {
    var cr := AReg.as_arrays(cap).0;
    var cc := AReg.as_arrays(cap).1;
    var f := AI.filter_reset(body, cap, look, quant, -1);
    var f_L := AI.filter_reset(body, MIR.MirrorRegs(cap, n), look, quant, -1);
    assert f == AI.filter_capture(body, cr, cc, AReg.as_arrays(look).1, AReg.as_arrays(quant).1, -1);
    FilterResetMirror(body, cap, look, quant, -1, n);
    assert f_L == MirrorArr(f, n);
    FilterCaptureLeN(body, cr, cc, AReg.as_arrays(look).1, AReg.as_arrays(quant).1, -1, n);
    assert forall k :: AI.get_idx(f, k) <= n;
    assert AReg.as_arrays(MIR.MirrorRegs(cap, n)).1 == cc;

    var g0 := PIV.GmOfLive(body, cap, look, quant);
    var gL := PIV.GmOfLive(body, MIR.MirrorRegs(cap, n), look, quant);

    // bounds on g0's ranges (present start >= 0, and everything <= n)
    forall g | g in g0
      ensures g0[g].startIdx <= n && (g0[g].endIdx.Some? ==> g0[g].endIdx.value <= n)
    {
    }
    assert GmLeN(g0, n);

    // domain agreement + per-gid raw-mirror value
    forall gid: nat | 0 <= gid < |f_L|
      ensures (AI.get_idx(f_L, CP.start_reg(gid)) >= 0) <==> (AI.get_idx(f, CP.start_reg(gid)) >= 0)
    {
      GetIdxMirror(f, CP.start_reg(gid), n);
      MirrorCpValSign(AI.get_idx(f, CP.start_reg(gid)), n);
    }
    assert |f_L| == |f|;

    forall gid: nat | gid in g0
      ensures gid in gL && gL[gid] == RawMirrorRange(g0[gid], n)
    {
      LiveRangeMirror(f, cc, gid, n);
    }
    forall gid: nat | gid in gL
      ensures gid in g0
    {
      GetIdxMirror(f, CP.start_reg(gid), n);
      MirrorCpValSign(AI.get_idx(f, CP.start_reg(gid)), n);
    }
    assert gL == RawMirrorGm(g0, n);
  }
}
