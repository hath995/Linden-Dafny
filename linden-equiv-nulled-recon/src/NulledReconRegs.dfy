// §2.5b STAGE 2, RUNG E (register side) — reading the reconstructed registers.
//
// After a live stamp's reconstruction (`FNulledPlus` at the stamp: the null
// interpreter over the body's ReconstructNulled code, then `FNulledChildren`
// for the nested stamps it re-set at the same position), `filter_capture` at
// the stamp's clock reads the body's groups as EXACTLY the groups of the first
// empty path, each spanning `[cp, cp)` (`EngineReadout`). The induction pushes
// every write outside a subterm into the subterm's initial registers
// (`ApplyWrites` is pointwise), so it never has to commute a write past the
// recursive reconstruction.
module LindenElkNulledReconRegs {
  import opened Std.Wrappers
  import R = RegElkRegex
  import RB = Bytecode
  import CP = Compiler
  import AI = ArrayInterp
  import AReg = Array_Regs
  import LOr = Oracle
  import RA = Anchors
  import LCdn = Cdn
  import T = LindenElkTranslate
  import NUL = LindenElkNullable
  import NR = LindenElkNfaRep
  import AR = LindenElkActionsRep
  import TR = LindenElkTreeRep
  import LC = Chars
  import LG = Groups
  import L = Regex
  import PIV = LindenElkPikeInv
  import NRC = LindenElkNulledRecon

  type Regs3 = NRC.Regs3

  /** The first / second subterm of a node (the node itself for leaves). */
  ghost function L1(r: R.regex): R.regex {
    match r
    case Re_alt(a, _) => a
    case Re_con(a, _) => a
    case Re_quant(_, _, _, a) => a
    case Re_capture(_, a) => a
    case Re_lookaround(_, _, a) => a
    case _ => r
  }
  ghost function L2(r: R.regex): R.regex {
    match r
    case Re_alt(_, b) => b
    case Re_con(_, b) => b
    case _ => r
  }

  // ===========================================================================
  // 1. Register sets of a regex; sizes; staleness.
  // ===========================================================================

  ghost function LookIds(r: R.regex): set<nat>
    decreases r
  {
    match r
    case Re_empty => {}
    case Re_character(_) => {}
    case Re_anchor(_) => {}
    case Re_alt(r1, r2) => LookIds(r1) + LookIds(r2)
    case Re_con(r1, r2) => LookIds(r1) + LookIds(r2)
    case Re_quant(_, _, _, r1) => LookIds(r1)
    case Re_capture(_, r1) => LookIds(r1)
    case Re_lookaround(lid, _, r1) => (if lid >= 0 then {lid as nat} else {}) + LookIds(r1)
  }

  /** The registers of `r`, as raw (int) keys — no well-formedness needed. */
  ghost function CapRegsOf(r: R.regex): set<int>
    decreases r
  {
    match r
    case Re_empty => {}
    case Re_character(_) => {}
    case Re_anchor(_) => {}
    case Re_alt(r1, r2) => CapRegsOf(r1) + CapRegsOf(r2)
    case Re_con(r1, r2) => CapRegsOf(r1) + CapRegsOf(r2)
    case Re_quant(_, _, _, r1) => CapRegsOf(r1)
    case Re_capture(cid, r1) => {CP.start_reg(cid), CP.end_reg(cid)} + CapRegsOf(r1)
    case Re_lookaround(_, _, r1) => CapRegsOf(r1)
  }
  ghost function QuantRegsOf(r: R.regex): set<int>
    decreases r
  {
    match r
    case Re_empty => {}
    case Re_character(_) => {}
    case Re_anchor(_) => {}
    case Re_alt(r1, r2) => QuantRegsOf(r1) + QuantRegsOf(r2)
    case Re_con(r1, r2) => QuantRegsOf(r1) + QuantRegsOf(r2)
    case Re_quant(_, qid, _, r1) => {qid} + QuantRegsOf(r1)
    case Re_capture(_, r1) => QuantRegsOf(r1)
    case Re_lookaround(_, _, r1) => QuantRegsOf(r1)
  }
  ghost function LookRegsOf(r: R.regex): set<int>
    decreases r
  {
    match r
    case Re_empty => {}
    case Re_character(_) => {}
    case Re_anchor(_) => {}
    case Re_alt(r1, r2) => LookRegsOf(r1) + LookRegsOf(r2)
    case Re_con(r1, r2) => LookRegsOf(r1) + LookRegsOf(r2)
    case Re_quant(_, _, _, r1) => LookRegsOf(r1)
    case Re_capture(_, r1) => LookRegsOf(r1)
    case Re_lookaround(lid, _, r1) => {lid} + LookRegsOf(r1)
  }

  /** `a` and `b` agree (value and clock) on every capture register outside
      `Sc`, every look register outside `Sl`, every quant register outside `Sq`. */
  ghost predicate AgreeOutside(a: Regs3, b: Regs3, Sc: set<int>, Sl: set<int>, Sq: set<int>) {
    (forall k: int :: k !in Sc ==> AI.get_idx(a.0.a_cp, k) == AI.get_idx(b.0.a_cp, k) && AI.get_idx(a.0.a_clk, k) == AI.get_idx(b.0.a_clk, k))
    && (forall k: int :: k !in Sl ==> AI.get_idx(a.1.a_cp, k) == AI.get_idx(b.1.a_cp, k) && AI.get_idx(a.1.a_clk, k) == AI.get_idx(b.1.a_clk, k))
    && (forall k: int :: k !in Sq ==> AI.get_idx(a.2.a_cp, k) == AI.get_idx(b.2.a_cp, k) && AI.get_idx(a.2.a_clk, k) == AI.get_idx(b.2.a_clk, k))
  }

  ghost predicate Sized3(a: Regs3, b: Regs3) {
    |a.0.a_cp| == |b.0.a_cp| && |a.0.a_clk| == |b.0.a_clk|
    && |a.1.a_cp| == |b.1.a_cp| && |a.1.a_clk| == |b.1.a_clk|
    && |a.2.a_cp| == |b.2.a_cp| && |a.2.a_clk| == |b.2.a_clk|
  }

  ghost predicate WfRegs(rg: Regs3) {
    |rg.0.a_cp| == |rg.0.a_clk| && |rg.1.a_cp| == |rg.1.a_clk| && |rg.2.a_cp| == |rg.2.a_clk|
  }

  /** Every register of `r` is in range. */
  ghost predicate Covers(r: R.regex, rg: Regs3) {
    (forall c: nat :: c in PIV.CapIds(r) ==> CP.end_reg(c) < |rg.0.a_cp|)
    && (forall l: nat :: l in LookIds(r) ==> l < |rg.1.a_cp|)
    && (forall q: nat :: q in PIV.QuantIds(r) ==> q < |rg.2.a_cp|)
  }

  /** Every capture/quant clock of `r` is below `K`. */
  ghost predicate RegsStale(r: R.regex, rg: Regs3, K: int) {
    (forall c: nat :: c in PIV.CapIds(r) ==> AI.get_idx(rg.0.a_clk, CP.start_reg(c)) < K && AI.get_idx(rg.0.a_clk, CP.end_reg(c)) < K)
    && (forall q: nat :: q in PIV.QuantIds(r) ==> AI.get_idx(rg.2.a_clk, q) < K)
  }

  /** An unset start CLOCK means an unset start VALUE (the register bank invariant). */
  ghost predicate CapValWf(rg: Regs3) {
    forall k: int :: AI.get_idx(rg.0.a_clk, k) < 0 <==> AI.get_idx(rg.0.a_cp, k) < 0
  }


  lemma CoversChild(r: R.regex, rg: Regs3)
    requires Covers(r, rg)
    ensures r.Re_alt? || r.Re_con? ==> Covers(L1(r), rg) && Covers(L2(r), rg)
    ensures r.Re_quant? || r.Re_capture? || r.Re_lookaround? ==> Covers(L1(r), rg)
  {
    match r
    case Re_alt(r1, r2) =>
      assert PIV.CapIds(r1) <= PIV.CapIds(r) && PIV.CapIds(r2) <= PIV.CapIds(r);
      assert LookIds(r1) <= LookIds(r) && LookIds(r2) <= LookIds(r);
      assert PIV.QuantIds(r1) <= PIV.QuantIds(r) && PIV.QuantIds(r2) <= PIV.QuantIds(r);
    case Re_con(r1, r2) =>
      assert PIV.CapIds(r1) <= PIV.CapIds(r) && PIV.CapIds(r2) <= PIV.CapIds(r);
      assert LookIds(r1) <= LookIds(r) && LookIds(r2) <= LookIds(r);
      assert PIV.QuantIds(r1) <= PIV.QuantIds(r) && PIV.QuantIds(r2) <= PIV.QuantIds(r);
    case Re_quant(_, _, _, r1) =>
      assert PIV.CapIds(r1) <= PIV.CapIds(r) && LookIds(r1) <= LookIds(r) && PIV.QuantIds(r1) <= PIV.QuantIds(r);
    case Re_capture(_, r1) =>
      assert PIV.CapIds(r1) <= PIV.CapIds(r) && LookIds(r1) <= LookIds(r) && PIV.QuantIds(r1) <= PIV.QuantIds(r);
    case Re_lookaround(_, _, r1) =>
      assert PIV.CapIds(r1) <= PIV.CapIds(r) && LookIds(r1) <= LookIds(r) && PIV.QuantIds(r1) <= PIV.QuantIds(r);
    case _ =>
  }

  lemma ApplyWritesSingle(w: NRC.Write, cp: int, k: int, rg: Regs3)
    ensures NRC.ApplyWrites([w], cp, [k], rg) == NRC.ApplyWrite(w, cp, k, rg)
  {
    var ws := [w]; var clks := [k];
    assert ws[1..] == [] && clks[1..] == [];
    assert NRC.ApplyWrites([], cp, [], NRC.ApplyWrite(w, cp, k, rg)) == NRC.ApplyWrite(w, cp, k, rg);
  }

  lemma SingletonTargets(w: NRC.Write)
    ensures w.WCap? ==> CapTargets([w]) == {w.reg} && LookTargets([w]) == {} && QuantTargets([w]) == {}
    ensures w.WLook? ==> LookTargets([w]) == {w.lid} && CapTargets([w]) == {} && QuantTargets([w]) == {}
    ensures w.WQuant? ==> QuantTargets([w]) == {w.qid} && CapTargets([w]) == {} && LookTargets([w]) == {}
  {
    var ws := [w];
    forall k ensures (k in CapTargets(ws) <==> (w.WCap? && k == w.reg)) {
      if k in CapTargets(ws) { var i :| 0 <= i < |ws| && ws[i].WCap? && ws[i].reg == k; assert i == 0; }
      if w.WCap? && k == w.reg { assert ws[0].WCap? && ws[0].reg == k; }
    }
    forall k ensures (k in LookTargets(ws) <==> (w.WLook? && k == w.lid)) {
      if k in LookTargets(ws) { var i :| 0 <= i < |ws| && ws[i].WLook? && ws[i].lid == k; assert i == 0; }
      if w.WLook? && k == w.lid { assert ws[0].WLook? && ws[0].lid == k; }
    }
    forall k ensures (k in QuantTargets(ws) <==> (w.WQuant? && k == w.qid)) {
      if k in QuantTargets(ws) { var i :| 0 <= i < |ws| && ws[i].WQuant? && ws[i].qid == k; assert i == 0; }
      if w.WQuant? && k == w.qid { assert ws[0].WQuant? && ws[0].qid == k; }
    }
  }

  /** `filter_capture` is pointwise in the value array. */
  lemma FilterCrPointwise(r: R.regex, X: seq<int>, Y: seq<int>, cc: seq<int>, lc: seq<int>, qc: seq<int>, M: int, j: int)
    requires AI.get_idx(X, j) == AI.get_idx(Y, j)
    ensures AI.get_idx(AI.filter_capture(r, X, cc, lc, qc, M), j) == AI.get_idx(AI.filter_capture(r, Y, cc, lc, qc, M), j)
    decreases r
  {
    match r
    case Re_empty =>
    case Re_character(_) =>
    case Re_anchor(_) =>
    case Re_alt(r1, r2) =>
      FilterCrPointwise(r1, X, Y, cc, lc, qc, M, j);
      FilterCrPointwise(r2, AI.filter_capture(r1, X, cc, lc, qc, M), AI.filter_capture(r1, Y, cc, lc, qc, M), cc, lc, qc, M, j);
    case Re_con(r1, r2) =>
      FilterCrPointwise(r1, X, Y, cc, lc, qc, M, j);
      FilterCrPointwise(r2, AI.filter_capture(r1, X, cc, lc, qc, M), AI.filter_capture(r1, Y, cc, lc, qc, M), cc, lc, qc, M, j);
    case Re_quant(_, qid, _, r1) =>
      var qv := AI.get_idx(qc, qid);
      if qv < M { PIV.FilterAllCrPointwise(r1, X, Y, j); } else { FilterCrPointwise(r1, X, Y, cc, lc, qc, qv, j); }
    case Re_capture(cid, r1) =>
      var start := AI.get_idx(cc, CP.start_reg(cid));
      if start < 0 { PIV.FilterAllCrPointwise(r1, X, Y, j); }
      else if start < M {
        assert AI.get_idx(AI.set_idx(X, CP.start_reg(cid), -1), j) == AI.get_idx(AI.set_idx(Y, CP.start_reg(cid), -1), j);
        PIV.FilterAllCrPointwise(r1, AI.set_idx(X, CP.start_reg(cid), -1), AI.set_idx(Y, CP.start_reg(cid), -1), j);
      } else { FilterCrPointwise(r1, X, Y, cc, lc, qc, M, j); }
    case Re_lookaround(lid, _, r1) =>
      var lv := AI.get_idx(lc, lid);
      if lv < 0 || lv < M { PIV.FilterAllCrPointwise(r1, X, Y, j); } else { FilterCrPointwise(r1, X, Y, cc, lc, qc, -1, j); }
  }

  /** Lookaround ids are pairwise distinct across `r` (the look analog of `QuantUnique`). */
  ghost predicate LookUnique(r: R.regex)
    decreases r
  {
    match r
    case Re_empty => true
    case Re_character(_) => true
    case Re_anchor(_) => true
    case Re_alt(r1, r2) => LookUnique(r1) && LookUnique(r2) && LookRegsOf(r1) * LookRegsOf(r2) == {}
    case Re_con(r1, r2) => LookUnique(r1) && LookUnique(r2) && LookRegsOf(r1) * LookRegsOf(r2) == {}
    case Re_quant(_, _, _, r1) => LookUnique(r1)
    case Re_capture(_, r1) => LookUnique(r1)
    case Re_lookaround(lid, _, r1) => lid !in LookRegsOf(r1) && LookUnique(r1)
  }

  /** Registers of one side of an alt/con are untouched by writes inside the other side. */
  lemma SubAgree(r: R.regex, a: Regs3, b: Regs3)
    requires (r.Re_alt? || r.Re_con?) && PIV.CapUnique(r) && PIV.QuantUnique(r)
    requires AgreeOutside(b, a, InnerCapRegs(L2(r)), InnerLookRegs(L2(r)), InnerQuantRegs(L2(r)))
             || AgreeOutside(b, a, CapRegsOf(L2(r)), LookRegsOf(L2(r)), QuantRegsOf(L2(r)))
    ensures forall k: int :: k in CapRegsOf(L1(r)) ==> AI.get_idx(b.0.a_cp, k) == AI.get_idx(a.0.a_cp, k) && AI.get_idx(b.0.a_clk, k) == AI.get_idx(a.0.a_clk, k)
    ensures forall k: int :: k in QuantRegsOf(L1(r)) ==> AI.get_idx(b.2.a_cp, k) == AI.get_idx(a.2.a_cp, k) && AI.get_idx(b.2.a_clk, k) == AI.get_idx(a.2.a_clk, k)
  {
    DisjointRegs(r);
    InnerSub(L2(r));
  }

  /** The mirror image: the second side's registers are untouched by writes inside the first. */
  lemma SubAgree2(r: R.regex, a: Regs3, b: Regs3)
    requires (r.Re_alt? || r.Re_con?) && PIV.CapUnique(r) && PIV.QuantUnique(r)
    requires AgreeOutside(b, a, InnerCapRegs(L1(r)), InnerLookRegs(L1(r)), InnerQuantRegs(L1(r)))
             || AgreeOutside(b, a, CapRegsOf(L1(r)), LookRegsOf(L1(r)), QuantRegsOf(L1(r)))
    ensures forall k: int :: k in CapRegsOf(L2(r)) ==> AI.get_idx(b.0.a_cp, k) == AI.get_idx(a.0.a_cp, k) && AI.get_idx(b.0.a_clk, k) == AI.get_idx(a.0.a_clk, k)
    ensures forall k: int :: k in QuantRegsOf(L2(r)) ==> AI.get_idx(b.2.a_cp, k) == AI.get_idx(a.2.a_cp, k) && AI.get_idx(b.2.a_clk, k) == AI.get_idx(a.2.a_clk, k)
  {
    DisjointRegs(r);
    InnerSub(L1(r));
  }

  lemma AgreeOutsideRefl(a: Regs3, Sc: set<int>, Sl: set<int>, Sq: set<int>)
    ensures AgreeOutside(a, a, Sc, Sl, Sq)
  {}

  lemma AgreeOutsideTrans(a: Regs3, b: Regs3, c: Regs3, Sc: set<int>, Sl: set<int>, Sq: set<int>)
    requires AgreeOutside(a, b, Sc, Sl, Sq) && AgreeOutside(b, c, Sc, Sl, Sq)
    ensures AgreeOutside(a, c, Sc, Sl, Sq)
  {}

  lemma AgreeOutsideWeaken(a: Regs3, b: Regs3, Sc: set<int>, Sl: set<int>, Sq: set<int>, Sc': set<int>, Sl': set<int>, Sq': set<int>)
    requires AgreeOutside(a, b, Sc, Sl, Sq) && Sc <= Sc' && Sl <= Sl' && Sq <= Sq'
    ensures AgreeOutside(a, b, Sc', Sl', Sq')
  {}

  // ===========================================================================
  // 2. `ApplyWrites` is pointwise; the writes of `NulledWrites` target the
  //    regex's own registers.
  // ===========================================================================

  ghost function CapTargets(ws: seq<NRC.Write>): set<int> { set i | 0 <= i < |ws| && ws[i].WCap? :: ws[i].reg }
  ghost function LookTargets(ws: seq<NRC.Write>): set<int> { set i | 0 <= i < |ws| && ws[i].WLook? :: ws[i].lid }
  ghost function QuantTargets(ws: seq<NRC.Write>): set<int> { set i | 0 <= i < |ws| && ws[i].WQuant? :: ws[i].qid }

  lemma TargetsTail(ws: seq<NRC.Write>)
    requires |ws| > 0
    ensures CapTargets(ws[1..]) <= CapTargets(ws) && LookTargets(ws[1..]) <= LookTargets(ws) && QuantTargets(ws[1..]) <= QuantTargets(ws)
    ensures ws[0].WCap? ==> ws[0].reg in CapTargets(ws)
    ensures ws[0].WLook? ==> ws[0].lid in LookTargets(ws)
    ensures ws[0].WQuant? ==> ws[0].qid in QuantTargets(ws)
  {
    forall k | k in CapTargets(ws[1..]) ensures k in CapTargets(ws) {
      var i :| 0 <= i < |ws[1..]| && ws[1..][i].WCap? && ws[1..][i].reg == k;
      assert ws[i + 1] == ws[1..][i];
    }
    forall k | k in LookTargets(ws[1..]) ensures k in LookTargets(ws) {
      var i :| 0 <= i < |ws[1..]| && ws[1..][i].WLook? && ws[1..][i].lid == k;
      assert ws[i + 1] == ws[1..][i];
    }
    forall k | k in QuantTargets(ws[1..]) ensures k in QuantTargets(ws) {
      var i :| 0 <= i < |ws[1..]| && ws[1..][i].WQuant? && ws[1..][i].qid == k;
      assert ws[i + 1] == ws[1..][i];
    }
  }

  lemma TargetsApp(a: seq<NRC.Write>, b: seq<NRC.Write>)
    ensures CapTargets(a + b) == CapTargets(a) + CapTargets(b)
    ensures LookTargets(a + b) == LookTargets(a) + LookTargets(b)
    ensures QuantTargets(a + b) == QuantTargets(a) + QuantTargets(b)
  {
    forall k ensures k in CapTargets(a + b) <==> k in CapTargets(a) + CapTargets(b) {
      if k in CapTargets(a + b) {
        var i :| 0 <= i < |a + b| && (a + b)[i].WCap? && (a + b)[i].reg == k;
        if i < |a| { assert (a + b)[i] == a[i]; } else { assert (a + b)[i] == b[i - |a|]; }
      }
      if k in CapTargets(a) { var i :| 0 <= i < |a| && a[i].WCap? && a[i].reg == k; assert (a + b)[i] == a[i]; }
      if k in CapTargets(b) { var i :| 0 <= i < |b| && b[i].WCap? && b[i].reg == k; assert (a + b)[|a| + i] == b[i]; }
    }
    forall k ensures k in LookTargets(a + b) <==> k in LookTargets(a) + LookTargets(b) {
      if k in LookTargets(a + b) {
        var i :| 0 <= i < |a + b| && (a + b)[i].WLook? && (a + b)[i].lid == k;
        if i < |a| { assert (a + b)[i] == a[i]; } else { assert (a + b)[i] == b[i - |a|]; }
      }
      if k in LookTargets(a) { var i :| 0 <= i < |a| && a[i].WLook? && a[i].lid == k; assert (a + b)[i] == a[i]; }
      if k in LookTargets(b) { var i :| 0 <= i < |b| && b[i].WLook? && b[i].lid == k; assert (a + b)[|a| + i] == b[i]; }
    }
    forall k ensures k in QuantTargets(a + b) <==> k in QuantTargets(a) + QuantTargets(b) {
      if k in QuantTargets(a + b) {
        var i :| 0 <= i < |a + b| && (a + b)[i].WQuant? && (a + b)[i].qid == k;
        if i < |a| { assert (a + b)[i] == a[i]; } else { assert (a + b)[i] == b[i - |a|]; }
      }
      if k in QuantTargets(a) { var i :| 0 <= i < |a| && a[i].WQuant? && a[i].qid == k; assert (a + b)[i] == a[i]; }
      if k in QuantTargets(b) { var i :| 0 <= i < |b| && b[i].WQuant? && b[i].qid == k; assert (a + b)[|a| + i] == b[i]; }
    }
  }

  /** Sizes are preserved, and registers outside the targets are untouched. */
  lemma ApplyWritesFrame(ws: seq<NRC.Write>, cp: int, clks: seq<int>, rg: Regs3)
    requires |clks| == |ws|
    ensures Sized3(NRC.ApplyWrites(ws, cp, clks, rg), rg)
    ensures AgreeOutside(NRC.ApplyWrites(ws, cp, clks, rg), rg, CapTargets(ws), LookTargets(ws), QuantTargets(ws))
    decreases |ws|
  {
    if |ws| > 0 {
      var rg1 := NRC.ApplyWrite(ws[0], cp, clks[0], rg);
      TargetsTail(ws);
      ApplyWritesFrame(ws[1..], cp, clks[1..], rg1);
      AgreeOutsideWeaken(NRC.ApplyWrites(ws, cp, clks, rg), rg1, CapTargets(ws[1..]), LookTargets(ws[1..]), QuantTargets(ws[1..]),
                         CapTargets(ws), LookTargets(ws), QuantTargets(ws));
      assert AgreeOutside(rg1, rg, CapTargets(ws), LookTargets(ws), QuantTargets(ws));
      AgreeOutsideTrans(NRC.ApplyWrites(ws, cp, clks, rg), rg1, rg, CapTargets(ws), LookTargets(ws), QuantTargets(ws));
    }
  }

  /** Writes at non-negative clocks and positions keep the value/clock bank invariant. */
  lemma ApplyWritesCapValWf(ws: seq<NRC.Write>, cp: int, clks: seq<int>, rg: Regs3)
    requires |clks| == |ws| && cp >= 0 && forall i :: 0 <= i < |clks| ==> clks[i] >= 0
    requires CapValWf(rg)
    ensures CapValWf(NRC.ApplyWrites(ws, cp, clks, rg))
    decreases |ws|
  {
    if |ws| > 0 {
      var rg1 := NRC.ApplyWrite(ws[0], cp, clks[0], rg);
      assert CapValWf(rg1);
      ApplyWritesCapValWf(ws[1..], cp, clks[1..], rg1);
    }
  }

  /** On the targets, the result does not depend on the initial registers
      (same sizes assumed, so every write lands). */
  /** The write targets land (in range) in `a`. */
  ghost predicate TargetsInRange(ws: seq<NRC.Write>, a: Regs3) {
    (forall k: int :: k in CapTargets(ws) && k >= 0 ==> k < |a.0.a_cp| && k < |a.0.a_clk|)
    && (forall k: int :: k in LookTargets(ws) && k >= 0 ==> k < |a.1.a_cp| && k < |a.1.a_clk|)
    && (forall k: int :: k in QuantTargets(ws) && k >= 0 ==> k < |a.2.a_cp| && k < |a.2.a_clk|)
  }

  /** The first empty path's writes land in a bank covering the regex. */
  lemma TargetsInRangeFromCovers(qm: AR.QMap, r: R.regex, inp: LC.Input, rg: Regs3)
    requires PIV.CapUnique(r) && PIV.QuantUnique(r) && Covers(r, rg) && WfRegs(rg)
    requires NRC.NulledWrites(qm, r, inp).Some?
    ensures TargetsInRange(NRC.NulledWrites(qm, r, inp).value, rg)
  {
    var ws := NRC.NulledWrites(qm, r, inp).value;
    NulledWritesTargets(qm, r, inp);
    CapRegsOfChar(r);
    QuantRegsOfChar(r);
    LookRegsOfChar(r);
    forall k: int | k in CapTargets(ws) && k >= 0 ensures k < |rg.0.a_cp| && k < |rg.0.a_clk| {
      var c: nat :| c in PIV.CapIds(r) && (k == CP.start_reg(c) || k == CP.end_reg(c));
    }
    forall k: int | k in QuantTargets(ws) && k >= 0 ensures k < |rg.2.a_cp| && k < |rg.2.a_clk| {
      assert (k as nat) in PIV.QuantIds(r);
    }
    forall k: int | k in LookTargets(ws) && k >= 0 ensures k < |rg.1.a_cp| && k < |rg.1.a_clk| {
      assert (k as nat) in LookIds(r);
    }
  }

  lemma LookRegsOfChar(r: R.regex)
    ensures forall k: int :: k in LookRegsOf(r) && k >= 0 ==> (k as nat) in LookIds(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => LookRegsOfChar(r1); LookRegsOfChar(r2);
    case Re_con(r1, r2) => LookRegsOfChar(r1); LookRegsOfChar(r2);
    case Re_quant(_, _, _, r1) => LookRegsOfChar(r1);
    case Re_capture(_, r1) => LookRegsOfChar(r1);
    case Re_lookaround(_, _, r1) => LookRegsOfChar(r1);
    case _ =>
  }

  lemma ApplyWritesOnTargets(ws: seq<NRC.Write>, cp: int, clks: seq<int>, a: Regs3, b: Regs3)
    requires |clks| == |ws|
    requires Sized3(a, b) && TargetsInRange(ws, a)
    ensures var ra := NRC.ApplyWrites(ws, cp, clks, a);
            var rb := NRC.ApplyWrites(ws, cp, clks, b);
            (forall k: int :: k in CapTargets(ws) ==> AI.get_idx(ra.0.a_cp, k) == AI.get_idx(rb.0.a_cp, k) && AI.get_idx(ra.0.a_clk, k) == AI.get_idx(rb.0.a_clk, k))
            && (forall k: int :: k in LookTargets(ws) ==> AI.get_idx(ra.1.a_cp, k) == AI.get_idx(rb.1.a_cp, k) && AI.get_idx(ra.1.a_clk, k) == AI.get_idx(rb.1.a_clk, k))
            && (forall k: int :: k in QuantTargets(ws) ==> AI.get_idx(ra.2.a_cp, k) == AI.get_idx(rb.2.a_cp, k) && AI.get_idx(ra.2.a_clk, k) == AI.get_idx(rb.2.a_clk, k))
    decreases |ws|
  {
    if |ws| > 0 {
      var a1 := NRC.ApplyWrite(ws[0], cp, clks[0], a);
      var b1 := NRC.ApplyWrite(ws[0], cp, clks[0], b);
      TargetsTail(ws);
      assert Sized3(a1, a) && Sized3(b1, b);
      assert TargetsInRange(ws[1..], a1);
      ApplyWritesOnTargets(ws[1..], cp, clks[1..], a1, b1);
      ApplyWritesFrame(ws[1..], cp, clks[1..], a1);
      ApplyWritesFrame(ws[1..], cp, clks[1..], b1);
      var ra := NRC.ApplyWrites(ws, cp, clks, a);
      var rb := NRC.ApplyWrites(ws, cp, clks, b);
      assert ra == NRC.ApplyWrites(ws[1..], cp, clks[1..], a1);
      assert rb == NRC.ApplyWrites(ws[1..], cp, clks[1..], b1);
      // the head write's target: either rewritten by the tail (then equal by IH)
      // or untouched by the tail (then equal to the head write on both sides).
      match ws[0]
      case WCap(reg) =>
        if reg !in CapTargets(ws[1..]) {
          if reg >= 0 {
            assert reg < |a.0.a_cp| && reg < |a.0.a_clk|;
            assert AI.get_idx(a1.0.a_cp, reg) == cp && AI.get_idx(b1.0.a_cp, reg) == cp;
            assert AI.get_idx(a1.0.a_clk, reg) == clks[0] && AI.get_idx(b1.0.a_clk, reg) == clks[0];
          } else {
            assert AI.get_idx(a1.0.a_cp, reg) == -1 && AI.get_idx(b1.0.a_cp, reg) == -1;
            assert AI.get_idx(a1.0.a_clk, reg) == -1 && AI.get_idx(b1.0.a_clk, reg) == -1;
          }
          assert AI.get_idx(ra.0.a_cp, reg) == AI.get_idx(a1.0.a_cp, reg);
          assert AI.get_idx(rb.0.a_cp, reg) == AI.get_idx(b1.0.a_cp, reg);
          assert AI.get_idx(ra.0.a_clk, reg) == AI.get_idx(a1.0.a_clk, reg);
          assert AI.get_idx(rb.0.a_clk, reg) == AI.get_idx(b1.0.a_clk, reg);
        }
        forall k: int | k in CapTargets(ws)
          ensures AI.get_idx(ra.0.a_cp, k) == AI.get_idx(rb.0.a_cp, k) && AI.get_idx(ra.0.a_clk, k) == AI.get_idx(rb.0.a_clk, k)
        {
          if k in CapTargets(ws[1..]) {
          } else {
            assert k == reg by {
              var i :| 0 <= i < |ws| && ws[i].WCap? && ws[i].reg == k;
              if i > 0 { assert ws[1..][i - 1] == ws[i]; assert k in CapTargets(ws[1..]); }
            }
          }
        }
      case WLook(l) =>
        if l !in LookTargets(ws[1..]) {
          if l >= 0 {
            assert l < |a.1.a_cp| && l < |a.1.a_clk|;
            assert AI.get_idx(a1.1.a_cp, l) == cp && AI.get_idx(b1.1.a_cp, l) == cp;
            assert AI.get_idx(a1.1.a_clk, l) == clks[0] && AI.get_idx(b1.1.a_clk, l) == clks[0];
          } else {
            assert AI.get_idx(a1.1.a_cp, l) == -1 && AI.get_idx(b1.1.a_cp, l) == -1;
            assert AI.get_idx(a1.1.a_clk, l) == -1 && AI.get_idx(b1.1.a_clk, l) == -1;
          }
          assert AI.get_idx(ra.1.a_cp, l) == AI.get_idx(a1.1.a_cp, l);
          assert AI.get_idx(rb.1.a_cp, l) == AI.get_idx(b1.1.a_cp, l);
          assert AI.get_idx(ra.1.a_clk, l) == AI.get_idx(a1.1.a_clk, l);
          assert AI.get_idx(rb.1.a_clk, l) == AI.get_idx(b1.1.a_clk, l);
        }
        forall k: int | k in LookTargets(ws)
          ensures AI.get_idx(ra.1.a_cp, k) == AI.get_idx(rb.1.a_cp, k) && AI.get_idx(ra.1.a_clk, k) == AI.get_idx(rb.1.a_clk, k)
        {
          if k in LookTargets(ws[1..]) {
          } else {
            assert k == l by {
              var i :| 0 <= i < |ws| && ws[i].WLook? && ws[i].lid == k;
              if i > 0 { assert ws[1..][i - 1] == ws[i]; assert k in LookTargets(ws[1..]); }
            }
          }
        }
      case WQuant(q, bq) =>
        if q !in QuantTargets(ws[1..]) {
          if q >= 0 {
            assert q < |a.2.a_cp| && q < |a.2.a_clk|;
            assert AI.get_idx(a1.2.a_cp, q) == AI.get_idx(b1.2.a_cp, q);
            assert AI.get_idx(a1.2.a_clk, q) == clks[0] && AI.get_idx(b1.2.a_clk, q) == clks[0];
          } else {
            assert AI.get_idx(a1.2.a_cp, q) == -1 && AI.get_idx(b1.2.a_cp, q) == -1;
            assert AI.get_idx(a1.2.a_clk, q) == -1 && AI.get_idx(b1.2.a_clk, q) == -1;
          }
          assert AI.get_idx(ra.2.a_cp, q) == AI.get_idx(a1.2.a_cp, q);
          assert AI.get_idx(rb.2.a_cp, q) == AI.get_idx(b1.2.a_cp, q);
          assert AI.get_idx(ra.2.a_clk, q) == AI.get_idx(a1.2.a_clk, q);
          assert AI.get_idx(rb.2.a_clk, q) == AI.get_idx(b1.2.a_clk, q);
        }
        forall k: int | k in QuantTargets(ws)
          ensures AI.get_idx(ra.2.a_cp, k) == AI.get_idx(rb.2.a_cp, k) && AI.get_idx(ra.2.a_clk, k) == AI.get_idx(rb.2.a_clk, k)
        {
          if k in QuantTargets(ws[1..]) {
          } else {
            assert k == q by {
              var i :| 0 <= i < |ws| && ws[i].WQuant? && ws[i].qid == k;
              if i > 0 { assert ws[1..][i - 1] == ws[i]; assert k in QuantTargets(ws[1..]); }
            }
          }
        }
    }
  }

  /** Same targets from two initial banks that agree outside the targets: the
      results are equal (pointwise on every register). */
  lemma ApplyWritesMerge(ws: seq<NRC.Write>, cp: int, clks: seq<int>, a: Regs3, b: Regs3)
    requires |clks| == |ws|
    requires Sized3(a, b) && WfRegs(a) && WfRegs(b) && TargetsInRange(ws, a)
    requires AgreeOutside(a, b, CapTargets(ws), LookTargets(ws), QuantTargets(ws))
    ensures NRC.ApplyWrites(ws, cp, clks, a) == NRC.ApplyWrites(ws, cp, clks, b)
  {
    var ra := NRC.ApplyWrites(ws, cp, clks, a);
    var rb := NRC.ApplyWrites(ws, cp, clks, b);
    ApplyWritesFrame(ws, cp, clks, a);
    ApplyWritesFrame(ws, cp, clks, b);
    ApplyWritesOnTargets(ws, cp, clks, a, b);
    assert Sized3(ra, rb);
    SeqExt(ra.0.a_cp, rb.0.a_cp); SeqExt(ra.0.a_clk, rb.0.a_clk);
    SeqExt(ra.1.a_cp, rb.1.a_cp); SeqExt(ra.1.a_clk, rb.1.a_clk);
    SeqExt(ra.2.a_cp, rb.2.a_cp); SeqExt(ra.2.a_clk, rb.2.a_clk);
  }

  lemma SeqExt(x: seq<int>, y: seq<int>)
    requires |x| == |y|
    requires forall k: int :: AI.get_idx(x, k) == AI.get_idx(y, k)
    ensures x == y
  {
    forall i | 0 <= i < |x| ensures x[i] == y[i] { assert AI.get_idx(x, i) == x[i] && AI.get_idx(y, i) == y[i]; }
  }

  /** The writes of the first empty path target the regex's own registers. */
  lemma NulledWritesTargets(qm: AR.QMap, re: R.regex, inp: LC.Input)
    requires NRC.NulledWrites(qm, re, inp).Some?
    ensures var ws := NRC.NulledWrites(qm, re, inp).value;
            CapTargets(ws) <= CapRegsOf(re) && LookTargets(ws) <= LookRegsOf(re) && QuantTargets(ws) <= QuantRegsOf(re)
    decreases re
  {
    var ws := NRC.NulledWrites(qm, re, inp).value;
    match re
    case Re_empty => assert ws == [];
    case Re_character(_) =>
    case Re_anchor(_) => assert ws == [];
    case Re_alt(r1, r2) =>
      if NRC.NulledWrites(qm, r1, inp).Some? { NulledWritesTargets(qm, r1, inp); }
      else { NulledWritesTargets(qm, r2, inp); }
    case Re_con(r1, r2) =>
      NulledWritesTargets(qm, r1, inp);
      NulledWritesTargets(qm, r2, inp);
      TargetsApp(NRC.NulledWrites(qm, r1, inp).value, NRC.NulledWrites(qm, r2, inp).value);
    case Re_quant(nul, qid, q, r1) =>
      if q.min == 0 {
        assert ws == [];
      } else if nul == R.NonNullable {
      } else if q.max == None && nul == R.CINullable && q.greedy {
        assert ws == [NRC.WQuant(qid, true)];
        forall k | k in QuantTargets(ws) ensures k in QuantRegsOf(re) { assert k == qid; }
        assert CapTargets(ws) == {} && LookTargets(ws) == {};
      } else if q.max == None && nul == R.CDNullable && q.greedy {
      } else {
        NulledWritesTargets(qm, r1, inp);
        var w1 := NRC.NulledWrites(qm, r1, inp).value;
        TargetsApp([NRC.WQuant(qid, false)], w1);
        forall k | k in QuantTargets([NRC.WQuant(qid, false)]) ensures k in QuantRegsOf(re) { assert k == qid; }
        assert CapTargets([NRC.WQuant(qid, false)]) == {} && LookTargets([NRC.WQuant(qid, false)]) == {};
      }
    case Re_capture(cid, r1) =>
      NulledWritesTargets(qm, r1, inp);
      var w1 := NRC.NulledWrites(qm, r1, inp).value;
      TargetsApp([NRC.WCap(CP.start_reg(cid))] + w1, [NRC.WCap(CP.end_reg(cid))]);
      TargetsApp([NRC.WCap(CP.start_reg(cid))], w1);
      forall k | k in CapTargets([NRC.WCap(CP.start_reg(cid))]) ensures k in CapRegsOf(re) { assert k == CP.start_reg(cid); }
      forall k | k in CapTargets([NRC.WCap(CP.end_reg(cid))]) ensures k in CapRegsOf(re) { assert k == CP.end_reg(cid); }
      assert LookTargets([NRC.WCap(CP.start_reg(cid))]) == {} && QuantTargets([NRC.WCap(CP.start_reg(cid))]) == {};
      assert LookTargets([NRC.WCap(CP.end_reg(cid))]) == {} && QuantTargets([NRC.WCap(CP.end_reg(cid))]) == {};
    case Re_lookaround(lid, la, _) =>
      if NRC.PositiveLk(la) {
        assert ws == [NRC.WLook(lid)];
        forall k | k in LookTargets(ws) ensures k in LookRegsOf(re) { assert k == lid; }
        assert CapTargets(ws) == {} && QuantTargets(ws) == {};
      } else {
        assert ws == [];
      }
  }


  /** The first empty path never writes a look-body capture's start register. */
  lemma NulledWritesLookCapsFree(qm: AR.QMap, re: R.regex, inp: LC.Input)
    requires PIV.CapUnique(re)
    requires NRC.NulledWrites(qm, re, inp).Some?
    ensures forall c: nat :: c in PIV.CapIdsInLooks(re) ==> CP.start_reg(c) !in CapTargets(NRC.NulledWrites(qm, re, inp).value)
    decreases re
  {
    var ws := NRC.NulledWrites(qm, re, inp).value;
    match re
    case Re_empty =>
    case Re_character(_) =>
    case Re_anchor(_) =>
    case Re_lookaround(lid, la, _) =>
      assert CapTargets(ws) == {} by { if NRC.PositiveLk(la) { assert ws == [NRC.WLook(lid)]; } else { assert ws == []; } }
    case Re_alt(r1, r2) =>
      if NRC.NulledWrites(qm, r1, inp).Some? { NulledWritesLookCapsFree(qm, r1, inp); NulledWritesTargets(qm, r1, inp); LookCapsNotInOther(re, r1, r2); }
      else { NulledWritesLookCapsFree(qm, r2, inp); NulledWritesTargets(qm, r2, inp); LookCapsNotInOther(re, r2, r1); }
    case Re_con(r1, r2) =>
      NulledWritesLookCapsFree(qm, r1, inp); NulledWritesLookCapsFree(qm, r2, inp);
      NulledWritesTargets(qm, r1, inp); NulledWritesTargets(qm, r2, inp);
      TargetsApp(NRC.NulledWrites(qm, r1, inp).value, NRC.NulledWrites(qm, r2, inp).value);
      LookCapsNotInOther(re, r1, r2); LookCapsNotInOther(re, r2, r1);
    case Re_quant(nul, qid, q, r1) =>
      if q.min == 0 { assert ws == []; }
      else if nul == R.NonNullable { }
      else if q.max == None && nul == R.CINullable && q.greedy { assert ws == [NRC.WQuant(qid, true)]; assert CapTargets(ws) == {}; }
      else if q.max == None && nul == R.CDNullable && q.greedy { }
      else {
        NulledWritesLookCapsFree(qm, r1, inp);
        var w1 := NRC.NulledWrites(qm, r1, inp).value;
        TargetsApp([NRC.WQuant(qid, false)], w1);
        assert CapTargets([NRC.WQuant(qid, false)]) == {};
      }
    case Re_capture(cid, r1) =>
      NulledWritesLookCapsFree(qm, r1, inp);
      var w1 := NRC.NulledWrites(qm, r1, inp).value;
      TargetsApp([NRC.WCap(CP.start_reg(cid))] + w1, [NRC.WCap(CP.end_reg(cid))]);
      TargetsApp([NRC.WCap(CP.start_reg(cid))], w1);
      SingletonTargets(NRC.WCap(CP.start_reg(cid))); SingletonTargets(NRC.WCap(CP.end_reg(cid)));
      CapIdsInLooksSub(r1);
      forall c: nat | c in PIV.CapIdsInLooks(re) ensures CP.start_reg(c) !in CapTargets(ws) {
        assert c in PIV.CapIds(r1) && c != cid as nat;
      }
  }

  /** A look-body capture of one side of an alt/con has its start register outside the other side's. */
  lemma LookCapsNotInOther(re: R.regex, a: R.regex, b: R.regex)
    requires (re.Re_alt? || re.Re_con?) && PIV.CapUnique(re) && ((a == L1(re) && b == L2(re)) || (a == L2(re) && b == L1(re)))
    ensures forall c: nat :: c in PIV.CapIdsInLooks(b) ==> CP.start_reg(c) !in CapRegsOf(a)
  {
    CapRegsOfChar(a);
    CapIdsInLooksSub(b);
    forall c: nat | c in PIV.CapIdsInLooks(b) ensures CP.start_reg(c) !in CapRegsOf(a) {
      if CP.start_reg(c) in CapRegsOf(a) {
        var c': nat :| c' in PIV.CapIds(a) && (CP.start_reg(c) == CP.start_reg(c') || CP.start_reg(c) == CP.end_reg(c'));
        assert c == c';
        assert c in PIV.CapIds(L1(re)) * PIV.CapIds(L2(re));
      }
    }
  }

  /** `FNulledChildren` keeps look-body captures absent. */
  lemma FNulledChildrenLookCapsAbsent(qm: AR.QMap, r: R.regex, cdnt: LCdn.cdn_table, cp: nat, rg: Regs3,
                                      plus_bcv: seq<RB.code>, str: string, ov: LOr.OracleView)
    requires PIV.CapUnique(r) && PIV.QuantUnique(r) && NRC.NoCdnPlusRE(r) && PlusTableOk(r, plus_bcv)
    requires WfRegs(rg) && CapValWf(rg) && ov == qm.ov && cp <= |str|
    requires LookCapsAbsent(r, rg)
    ensures LookCapsAbsent(r, FC(r, cdnt, cp, rg, plus_bcv, str, ov))
    decreases r, 1
  {
    var rg2 := FC(r, cdnt, cp, rg, plus_bcv, str, ov);
    FNulledChildrenFrame(qm, r, cdnt, cp, rg, plus_bcv, str, ov);
    match r
    case Re_empty =>
    case Re_character(_) =>
    case Re_anchor(_) =>
    case Re_lookaround(_, _, _) =>
    case Re_capture(_, r1) =>
      PlusTableOkChildren(r, plus_bcv);
      FNulledChildrenLookCapsAbsent(qm, r1, cdnt, cp, rg, plus_bcv, str, ov);
    case Re_alt(r1, r2) =>
      PlusTableOkChildren(r, plus_bcv);
      FNulledChildrenLookCapsAbsent(qm, r1, cdnt, cp, rg, plus_bcv, str, ov);
      var rgA := FC(r1, cdnt, cp, rg, plus_bcv, str, ov);
      FNulledChildrenFrame(qm, r1, cdnt, cp, rg, plus_bcv, str, ov);
      SubAgree2(r, rg, rgA);
      CapIdsInLooksSub(r2); CapRegsOfChar(r2);
      assert LookCapsAbsent(r2, rgA) by {
        forall c: nat | c in PIV.CapIdsInLooks(r2) ensures AI.get_idx(rgA.0.a_cp, CP.start_reg(c)) < 0 { assert CP.start_reg(c) in CapRegsOf(r2); }
      }
      FNulledChildrenLookCapsAbsent(qm, r2, cdnt, cp, rgA, plus_bcv, str, ov);
      FNulledChildrenFrame(qm, r2, cdnt, cp, rgA, plus_bcv, str, ov);
      assert rg2 == FC(r2, cdnt, cp, rgA, plus_bcv, str, ov);
      SubAgree(r, rgA, rg2);
      CapIdsInLooksSub(r1); CapRegsOfChar(r1);
      forall c: nat | c in PIV.CapIdsInLooks(r) ensures AI.get_idx(rg2.0.a_cp, CP.start_reg(c)) < 0 {
        if c in PIV.CapIdsInLooks(r1) { assert CP.start_reg(c) in CapRegsOf(r1); }
      }
    case Re_con(r1, r2) =>
      PlusTableOkChildren(r, plus_bcv);
      FNulledChildrenLookCapsAbsent(qm, r1, cdnt, cp, rg, plus_bcv, str, ov);
      var rgA := FC(r1, cdnt, cp, rg, plus_bcv, str, ov);
      FNulledChildrenFrame(qm, r1, cdnt, cp, rg, plus_bcv, str, ov);
      SubAgree2(r, rg, rgA);
      CapIdsInLooksSub(r2); CapRegsOfChar(r2);
      assert LookCapsAbsent(r2, rgA) by {
        forall c: nat | c in PIV.CapIdsInLooks(r2) ensures AI.get_idx(rgA.0.a_cp, CP.start_reg(c)) < 0 { assert CP.start_reg(c) in CapRegsOf(r2); }
      }
      FNulledChildrenLookCapsAbsent(qm, r2, cdnt, cp, rgA, plus_bcv, str, ov);
      FNulledChildrenFrame(qm, r2, cdnt, cp, rgA, plus_bcv, str, ov);
      assert rg2 == FC(r2, cdnt, cp, rgA, plus_bcv, str, ov);
      SubAgree(r, rgA, rg2);
      CapIdsInLooksSub(r1); CapRegsOfChar(r1);
      forall c: nat | c in PIV.CapIdsInLooks(r) ensures AI.get_idx(rg2.0.a_cp, CP.start_reg(c)) < 0 {
        if c in PIV.CapIdsInLooks(r1) { assert CP.start_reg(c) in CapRegsOf(r1); }
      }
    case Re_quant(nul, qid, q, body) =>
      PlusTableOkChildren(r, plus_bcv);
      match AReg.get_cp(rg.2, qid) {
        case None => FNulledChildrenLookCapsAbsent(qm, body, cdnt, cp, rg, plus_bcv, str, ov);
        case Some(start_cp) =>
          if start_cp == cp {
            var start_clock := AI.opt_int(AReg.get_clock(rg.2, qid));
            var code := AI.get_code_v(plus_bcv, qid);
            ReconAtLookCapsAbsent(qm, r, body, qid, code, cdnt, cp, rg, start_clock, plus_bcv, str, ov);
          }
      }
  }

  lemma ReconAtLookCapsAbsent(qm: AR.QMap, r: R.regex, body: R.regex, qid: int, code: RB.code, cdnt: LCdn.cdn_table, cp: nat, rg: Regs3,
                              start_clock: int, plus_bcv: seq<RB.code>, str: string, ov: LOr.OracleView)
    requires r.Re_quant? && L1(r) == body && r.qid == qid && qid >= 0
    requires PIV.CapUnique(r) && PIV.QuantUnique(r) && NRC.NoCdnPlusRE(r) && PlusTableOk(r, plus_bcv)
    requires code == AI.get_code_v(plus_bcv, qid)
    requires WfRegs(rg) && CapValWf(rg) && ov == qm.ov && cp <= |str| && start_clock >= -1
    requires LookCapsAbsent(body, rg)
    ensures LookCapsAbsent(body, ReconAt(code, body, cdnt, cp, rg, start_clock, plus_bcv, str, ov).0)
    decreases r, 0
  {
    var (rg2, ov2) := ReconAt(code, body, cdnt, cp, rg, start_clock, plus_bcv, str, ov);
    var ctx := AI.cp_context(cp, str, RA.Forward);
    var inits := AI.FInitState(code, cp, rg.0, rg.1, rg.2, start_clock, ctx).(cdn := cdnt);
    var (result, _, ov1) := AI.FNullInterp(code, inits, ov, RA.Forward);
    var rg1 := match result case None => rg case Some(w) => (w.capture_regs, w.look_regs, w.quant_regs);
    PlusTableOkChildren(r, plus_bcv);
    var inp := T.InputAt(str, cp);
    CpOfInputAt(str, cp);
    assert LookCapsAbsent(body, rg1) by {
      if QidCinPlus(r, qid as nat) {
        assert inits == AI.FInitState(code, TR.CpOf(inp) as int, rg.0, rg.1, rg.2, start_clock, TR.CtxOf(inp)).(cdn := inits.cdn);
        NRC.NullInterpNulled(qm, body, inp, inits, ov, rg.0, rg.1, rg.2, start_clock);
        if result.Some? {
          var ws := NRC.NulledWrites(qm, body, inp).value;
          var C := AI.FNullInterp(code, inits, ov, RA.Forward).1.clock;
          var clks: seq<int> :| |clks| == |ws| && NRC.Incr(clks) && NRC.ClksIn(clks, start_clock, C)
                                  && NRC.RegsOf(result.value) == NRC.ApplyWrites(ws, cp, clks, rg);
          ApplyWritesFrame(ws, cp, clks, rg);
          NulledWritesLookCapsFree(qm, body, inp);
        }
      } else {
        NullInterpEmptyCode(inits, ov);
      }
    }
    ReconAtRegs1(qm, r, body, qid, code, cdnt, cp, rg, start_clock, plus_bcv, str, ov);
    FNulledChildrenLookCapsAbsent(qm, body, cdnt, cp, rg1, plus_bcv, str, ov1);
    assert ov1 == ov;
  }

  /** The intermediate bank of `ReconAt` (after the null interpreter) is well-formed. */
  lemma ReconAtRegs1(qm: AR.QMap, r: R.regex, body: R.regex, qid: int, code: RB.code, cdnt: LCdn.cdn_table, cp: nat, rg: Regs3,
                     start_clock: int, plus_bcv: seq<RB.code>, str: string, ov: LOr.OracleView)
    requires r.Re_quant? && L1(r) == body && r.qid == qid && qid >= 0
    requires PIV.QuantUnique(r) && NRC.NoCdnPlusRE(r) && PlusTableOk(r, plus_bcv)
    requires code == AI.get_code_v(plus_bcv, qid)
    requires WfRegs(rg) && CapValWf(rg) && ov == qm.ov && cp <= |str| && start_clock >= -1
    ensures var ctx := AI.cp_context(cp, str, RA.Forward);
            var inits := AI.FInitState(code, cp, rg.0, rg.1, rg.2, start_clock, ctx).(cdn := cdnt);
            var (result, _, ov1) := AI.FNullInterp(code, inits, ov, RA.Forward);
            var rg1 := match result case None => rg case Some(w) => (w.capture_regs, w.look_regs, w.quant_regs);
            WfRegs(rg1) && CapValWf(rg1) && Sized3(rg1, rg) && ov1 == ov
  {
    var ctx := AI.cp_context(cp, str, RA.Forward);
    var inits := AI.FInitState(code, cp, rg.0, rg.1, rg.2, start_clock, ctx).(cdn := cdnt);
    var (result, _, ov1) := AI.FNullInterp(code, inits, ov, RA.Forward);
    var inp := T.InputAt(str, cp);
    CpOfInputAt(str, cp);
    PlusTableOkChildren(r, plus_bcv);
    if QidCinPlus(r, qid as nat) {
      assert inits == AI.FInitState(code, TR.CpOf(inp) as int, rg.0, rg.1, rg.2, start_clock, TR.CtxOf(inp)).(cdn := inits.cdn);
      NRC.NullInterpNulled(qm, body, inp, inits, ov, rg.0, rg.1, rg.2, start_clock);
      if result.Some? {
        var ws := NRC.NulledWrites(qm, body, inp).value;
        var C := AI.FNullInterp(code, inits, ov, RA.Forward).1.clock;
        var clks: seq<int> :| |clks| == |ws| && NRC.Incr(clks) && NRC.ClksIn(clks, start_clock, C)
                                && NRC.RegsOf(result.value) == NRC.ApplyWrites(ws, cp, clks, rg);
        ApplyWritesFrame(ws, cp, clks, rg);
        ApplyWritesCapValWf(ws, cp, clks, rg);
      }
    } else {
      NullInterpEmptyCode(inits, ov);
    }
  }

  // ===========================================================================
  // 3. Small `filter_capture` algebra (pointwise, no fragment hypotheses).
  // ===========================================================================

  /** `filter_capture` only ever rewrites START registers of the regex's own
      captures; every other slot passes through. */
  lemma FilterKeepsNonStart(r: R.regex, cr: seq<int>, cc: seq<int>, lc: seq<int>, qc: seq<int>, mx: int, j: int)
    requires forall c: nat :: c in PIV.CapIds(r) ==> CP.start_reg(c) != j
    ensures AI.get_idx(AI.filter_capture(r, cr, cc, lc, qc, mx), j) == AI.get_idx(cr, j)
    decreases r
  {
    match r
    case Re_empty =>
    case Re_character(_) =>
    case Re_anchor(_) =>
    case Re_alt(r1, r2) =>
      FilterKeepsNonStart(r1, cr, cc, lc, qc, mx, j);
      FilterKeepsNonStart(r2, AI.filter_capture(r1, cr, cc, lc, qc, mx), cc, lc, qc, mx, j);
    case Re_con(r1, r2) =>
      FilterKeepsNonStart(r1, cr, cc, lc, qc, mx, j);
      FilterKeepsNonStart(r2, AI.filter_capture(r1, cr, cc, lc, qc, mx), cc, lc, qc, mx, j);
    case Re_quant(_, qid, _, r1) =>
      var qv := AI.get_idx(qc, qid);
      if qv < mx { FilterAllKeepsNonStart(r1, cr, j); } else { FilterKeepsNonStart(r1, cr, cc, lc, qc, qv, j); }
    case Re_capture(cid, r1) =>
      var start := AI.get_idx(cc, CP.start_reg(cid));
      if start < 0 { FilterAllKeepsNonStart(r1, cr, j); }
      else if start < mx { FilterAllKeepsNonStart(r1, AI.set_idx(cr, CP.start_reg(cid), -1), j); }
      else { FilterKeepsNonStart(r1, cr, cc, lc, qc, mx, j); }
    case Re_lookaround(lid, _, r1) =>
      var lv := AI.get_idx(lc, lid);
      if lv < 0 || lv < mx { FilterAllKeepsNonStart(r1, cr, j); } else { FilterKeepsNonStart(r1, cr, cc, lc, qc, -1, j); }
  }

  lemma FilterAllKeepsNonStart(r: R.regex, cr: seq<int>, j: int)
    requires forall c: nat :: c in PIV.CapIds(r) ==> CP.start_reg(c) != j
    ensures AI.get_idx(AI.filter_all(r, cr), j) == AI.get_idx(cr, j)
    decreases r
  {
    match r
    case Re_empty =>
    case Re_character(_) =>
    case Re_anchor(_) =>
    case Re_alt(r1, r2) => FilterAllKeepsNonStart(r1, cr, j); FilterAllKeepsNonStart(r2, AI.filter_all(r1, cr), j);
    case Re_con(r1, r2) => FilterAllKeepsNonStart(r1, cr, j); FilterAllKeepsNonStart(r2, AI.filter_all(r1, cr), j);
    case Re_quant(_, _, _, r1) => FilterAllKeepsNonStart(r1, cr, j);
    case Re_capture(cid, r1) => FilterAllKeepsNonStart(r1, AI.set_idx(cr, CP.start_reg(cid), -1), j);
    case Re_lookaround(_, _, r1) => FilterAllKeepsNonStart(r1, cr, j);
  }

  /** The value `filter_capture` leaves at the start register of an
      outside-look capture `c` depends only on that slot, the start clocks of
      `r`'s captures and the clocks of `r`'s quantifiers. */
  lemma FilterAtStartDep(r: R.regex, A: seq<int>, B: seq<int>, ccA: seq<int>, ccB: seq<int>,
                         lcA: seq<int>, lcB: seq<int>, qcA: seq<int>, qcB: seq<int>, mx: int, c: nat)
    requires c in PIV.CapIds(r) && c !in PIV.CapIdsInLooks(r)
    requires AI.get_idx(A, CP.start_reg(c)) == AI.get_idx(B, CP.start_reg(c))
    requires forall c': nat :: c' in PIV.CapIds(r) ==> AI.get_idx(ccA, CP.start_reg(c')) == AI.get_idx(ccB, CP.start_reg(c'))
    requires forall q: nat :: q in PIV.QuantIds(r) ==> AI.get_idx(qcA, q) == AI.get_idx(qcB, q)
    ensures AI.get_idx(AI.filter_capture(r, A, ccA, lcA, qcA, mx), CP.start_reg(c))
         == AI.get_idx(AI.filter_capture(r, B, ccB, lcB, qcB, mx), CP.start_reg(c))
    decreases r
  {
    var j := CP.start_reg(c);
    match r
    case Re_empty =>
    case Re_character(_) =>
    case Re_anchor(_) =>
    case Re_alt(r1, r2) =>
      var A1 := AI.filter_capture(r1, A, ccA, lcA, qcA, mx);
      var B1 := AI.filter_capture(r1, B, ccB, lcB, qcB, mx);
      if c in PIV.CapIds(r1) {
        FilterAtStartDep(r1, A, B, ccA, ccB, lcA, lcB, qcA, qcB, mx, c);
        if c in PIV.CapIds(r2) {
          FilterAtStartDep(r2, A1, B1, ccA, ccB, lcA, lcB, qcA, qcB, mx, c);
        } else {
          FilterKeepsNonStart(r2, A1, ccA, lcA, qcA, mx, j);
          FilterKeepsNonStart(r2, B1, ccB, lcB, qcB, mx, j);
        }
      } else {
        FilterKeepsNonStart(r1, A, ccA, lcA, qcA, mx, j);
        FilterKeepsNonStart(r1, B, ccB, lcB, qcB, mx, j);
        FilterAtStartDep(r2, A1, B1, ccA, ccB, lcA, lcB, qcA, qcB, mx, c);
      }
    case Re_con(r1, r2) =>
      var A1 := AI.filter_capture(r1, A, ccA, lcA, qcA, mx);
      var B1 := AI.filter_capture(r1, B, ccB, lcB, qcB, mx);
      if c in PIV.CapIds(r1) {
        FilterAtStartDep(r1, A, B, ccA, ccB, lcA, lcB, qcA, qcB, mx, c);
        if c in PIV.CapIds(r2) {
          FilterAtStartDep(r2, A1, B1, ccA, ccB, lcA, lcB, qcA, qcB, mx, c);
        } else {
          FilterKeepsNonStart(r2, A1, ccA, lcA, qcA, mx, j);
          FilterKeepsNonStart(r2, B1, ccB, lcB, qcB, mx, j);
        }
      } else {
        FilterKeepsNonStart(r1, A, ccA, lcA, qcA, mx, j);
        FilterKeepsNonStart(r1, B, ccB, lcB, qcB, mx, j);
        FilterAtStartDep(r2, A1, B1, ccA, ccB, lcA, lcB, qcA, qcB, mx, c);
      }
    case Re_quant(_, qid, _, r1) =>
      var qv := AI.get_idx(qcA, qid);
      assert qid >= 0 ==> AI.get_idx(qcB, qid) == qv;
      if qid < 0 {
        // an out-of-range quant clock reads -1 on both sides
        assert AI.get_idx(qcA, qid) == -1 && AI.get_idx(qcB, qid) == -1;
      }
      if qv < mx {
        PIV.FilterAllCrPointwise(r1, A, B, j);
      } else {
        FilterAtStartDep(r1, A, B, ccA, ccB, lcA, lcB, qcA, qcB, qv, c);
      }
    case Re_capture(cid, r1) =>
      var start := AI.get_idx(ccA, CP.start_reg(cid));
      if cid >= 0 { assert (cid as nat) in PIV.CapIds(r); assert AI.get_idx(ccB, CP.start_reg(cid)) == start; }
      if cid < 0 {
        assert start == -1 && AI.get_idx(ccB, CP.start_reg(cid)) == -1 by { assert CP.start_reg(cid) < 0; }
      }
      if start < 0 {
        PIV.FilterAllCrPointwise(r1, A, B, j);
      } else if start < mx {
        assert AI.get_idx(AI.set_idx(A, CP.start_reg(cid), -1), j) == AI.get_idx(AI.set_idx(B, CP.start_reg(cid), -1), j);
        PIV.FilterAllCrPointwise(r1, AI.set_idx(A, CP.start_reg(cid), -1), AI.set_idx(B, CP.start_reg(cid), -1), j);
      } else {
        if c == cid as nat {
          assert c !in PIV.CapIds(r1) || true;
          if c in PIV.CapIds(r1) {
            FilterAtStartDep(r1, A, B, ccA, ccB, lcA, lcB, qcA, qcB, mx, c);
          } else {
            FilterKeepsNonStart(r1, A, ccA, lcA, qcA, mx, j);
            FilterKeepsNonStart(r1, B, ccB, lcB, qcB, mx, j);
          }
        } else {
          FilterAtStartDep(r1, A, B, ccA, ccB, lcA, lcB, qcA, qcB, mx, c);
        }
      }
    case Re_lookaround(lid, _, r1) =>
      // c is outside the look body: both branches keep its start slot.
      assert c !in PIV.CapIds(r1);
      var lvA := AI.get_idx(lcA, lid);
      var lvB := AI.get_idx(lcB, lid);
      if lvA < 0 || lvA < mx { FilterAllKeepsNonStart(r1, A, j); } else { FilterKeepsNonStart(r1, A, ccA, lcA, qcA, -1, j); }
      if lvB < 0 || lvB < mx { FilterAllKeepsNonStart(r1, B, j); } else { FilterKeepsNonStart(r1, B, ccB, lcB, qcB, -1, j); }
  }

  // ===========================================================================
  // 4. The reconstruction context and `FNulledChildren`'s frame.
  // ===========================================================================

  /** Whether `qid`'s quantifier node in `r` is a CIN-greedy `+`. */
  ghost predicate QidCinPlus(r: R.regex, qid: nat)
    requires qid in PIV.QuantIds(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => if qid in PIV.QuantIds(r1) then QidCinPlus(r1, qid) else QidCinPlus(r2, qid)
    case Re_con(r1, r2) => if qid in PIV.QuantIds(r1) then QidCinPlus(r1, qid) else QidCinPlus(r2, qid)
    case Re_quant(nul, qid0, q, r1) =>
      if qid0 >= 0 && (qid0 as nat) == qid then (q.min != 0 && q.max == None && nul == R.CINullable && q.greedy)
      else QidCinPlus(r1, qid)
    case Re_capture(cid, r1) => QidCinPlus(r1, qid)
    case Re_lookaround(lid, l, r1) => QidCinPlus(r1, qid)
  }

  /** The per-quantifier reconstruction table: the canonical ReconstructNulled
      code of a CIN-greedy `+`'s body, empty for every other quantifier. */
  ghost predicate PlusTableOk(r: R.regex, plus_bcv: seq<RB.code>) {
    forall q: nat :: q in PIV.QuantIds(r) ==>
      AI.get_code_v(plus_bcv, q as int)
        == (if QidCinPlus(r, q) then CP.compile_reconstruct_nulled(PIV.QidBody(r, q)) else [])
  }

  /** Under `QuantUnique`, the table condition passes to the immediate subterms. */
  lemma PlusTableOkChildren(r: R.regex, plus_bcv: seq<RB.code>)
    requires PIV.QuantUnique(r) && PlusTableOk(r, plus_bcv)
    ensures r.Re_alt? || r.Re_con? ==> PlusTableOk(L1(r), plus_bcv) && PlusTableOk(L2(r), plus_bcv)
    ensures r.Re_quant? ==> PlusTableOk(L1(r), plus_bcv)
    ensures r.Re_capture? ==> PlusTableOk(L1(r), plus_bcv)
    ensures r.Re_lookaround? ==> PlusTableOk(L1(r), plus_bcv)
  {
    match r
    case Re_alt(r1, r2) =>
      forall q: nat | q in PIV.QuantIds(r1) ensures AI.get_code_v(plus_bcv, q as int) == (if QidCinPlus(r1, q) then CP.compile_reconstruct_nulled(PIV.QidBody(r1, q)) else []) {
        assert q in PIV.QuantIds(r);
      }
      forall q: nat | q in PIV.QuantIds(r2) ensures AI.get_code_v(plus_bcv, q as int) == (if QidCinPlus(r2, q) then CP.compile_reconstruct_nulled(PIV.QidBody(r2, q)) else []) {
        assert PIV.QuantIds(r1) * PIV.QuantIds(r2) == {};
        assert q in PIV.QuantIds(r) && q !in PIV.QuantIds(r1);
        assert PIV.QidBody(r, q) == PIV.QidBody(r2, q) && QidCinPlus(r, q) == QidCinPlus(r2, q);
      }
    case Re_con(r1, r2) =>
      forall q: nat | q in PIV.QuantIds(r1) ensures AI.get_code_v(plus_bcv, q as int) == (if QidCinPlus(r1, q) then CP.compile_reconstruct_nulled(PIV.QidBody(r1, q)) else []) {
        assert q in PIV.QuantIds(r);
      }
      forall q: nat | q in PIV.QuantIds(r2) ensures AI.get_code_v(plus_bcv, q as int) == (if QidCinPlus(r2, q) then CP.compile_reconstruct_nulled(PIV.QidBody(r2, q)) else []) {
        assert PIV.QuantIds(r1) * PIV.QuantIds(r2) == {};
        assert q in PIV.QuantIds(r) && q !in PIV.QuantIds(r1);
        assert PIV.QidBody(r, q) == PIV.QidBody(r2, q) && QidCinPlus(r, q) == QidCinPlus(r2, q);
      }
    case Re_quant(nul, qid0, qq, r1) =>
      forall q: nat | q in PIV.QuantIds(r1) ensures AI.get_code_v(plus_bcv, q as int) == (if QidCinPlus(r1, q) then CP.compile_reconstruct_nulled(PIV.QidBody(r1, q)) else []) {
        assert q in PIV.QuantIds(r) && (qid0 as nat) != q;
      }
    case Re_capture(_, r1) =>
      forall q: nat | q in PIV.QuantIds(r1) ensures AI.get_code_v(plus_bcv, q as int) == (if QidCinPlus(r1, q) then CP.compile_reconstruct_nulled(PIV.QidBody(r1, q)) else []) {
        assert q in PIV.QuantIds(r);
      }
    case Re_lookaround(_, _, r1) =>
      forall q: nat | q in PIV.QuantIds(r1) ensures AI.get_code_v(plus_bcv, q as int) == (if QidCinPlus(r1, q) then CP.compile_reconstruct_nulled(PIV.QidBody(r1, q)) else []) {
        assert q in PIV.QuantIds(r);
      }
    case Re_empty =>
    case Re_character(_) =>
    case Re_anchor(_) =>
  }

  lemma CpOfInputAt(str: string, cp: nat)
    requires cp <= |str|
    ensures TR.CpOf(T.InputAt(str, cp)) == cp
    ensures TR.CtxOf(T.InputAt(str, cp)) == AI.cp_context(cp, str, RA.Forward)
  {
    var inp := T.InputAt(str, cp);
    T.ReverseProps(str[..cp]);
    assert |inp.pref| == cp;
    if cp > 0 { assert inp.pref[0] == str[..cp][cp - 1] == str[cp - 1]; }
    if cp < |str| { assert inp.next[0] == str[cp]; }
  }

  /** The null interpreter over the EMPTY code finds nothing and changes nothing. */
  lemma NullInterpEmptyCode(s0: AI.VmState, ov: LOr.OracleView)
    requires |s0.processed.true_set| == 0 && |s0.processed.false_set| == 0
    requires |s0.active| == 1 && s0.bestmatch == None
    ensures AI.FNullInterp([], s0, ov, RA.Forward).0 == None
    ensures AI.FNullInterp([], s0, ov, RA.Forward).2 == ov
  {
    var t := s0.active[0];
    assert s0.active == [t] + [];
    assert !AI.bpc_mem(s0.processed, t.pc, t.exit_allowed);
    assert RB.get_instr([], t.pc) == RB.Fail;
    NRC.StepFail([], s0, ov, RA.Forward, t, []);
    var s1 := NRC.Bump(s0, t).(active := []);
    assert AI.FAdvanceEpsilon([], s1, ov, RA.Forward) == (s1, ov);
  }

  /** The registers `FNulledChildren` hands back, as a triple. */
  ghost function FC(r: R.regex, cdnt: LCdn.cdn_table, cp: int, rg: Regs3, plus_bcv: seq<RB.code>, str: string, ov: LOr.OracleView): Regs3 {
    var (c, l, q, _) := AI.FNulledChildren(r, cdnt, cp, rg.0, rg.1, rg.2, plus_bcv, str, ov, RA.Forward);
    (c, l, q)
  }
  ghost function FCov(r: R.regex, cdnt: LCdn.cdn_table, cp: int, rg: Regs3, plus_bcv: seq<RB.code>, str: string, ov: LOr.OracleView): LOr.OracleView {
    AI.FNulledChildren(r, cdnt, cp, rg.0, rg.1, rg.2, plus_bcv, str, ov, RA.Forward).3
  }

  /** One nested reconstruction at `cp`: the null interpreter over `code` from
      the quantifier's clock, then the children. Mirrors the `Some(start_cp)`
      branch of `FNulledChildren` with `start_cp == cp`. */
  ghost function ReconAt(code: RB.code, body: R.regex, cdnt: LCdn.cdn_table, cp: int, rg: Regs3, start_clock: int,
                         plus_bcv: seq<RB.code>, str: string, ov: LOr.OracleView): (Regs3, LOr.OracleView)
  {
    var ctx := AI.cp_context(cp, str, RA.Forward);
    var inits0 := AI.FInitState(code, cp, rg.0, rg.1, rg.2, start_clock, ctx);
    var inits := inits0.(cdn := cdnt);
    var (result, _, ov1) := AI.FNullInterp(code, inits, ov, RA.Forward);
    var rg1 := match result case None => rg case Some(w) => (w.capture_regs, w.look_regs, w.quant_regs);
    var (c2, l2, q2, ov2) := AI.FNulledChildren(body, cdnt, cp, rg1.0, rg1.1, rg1.2, plus_bcv, str, ov1, RA.Forward);
    ((c2, l2, q2), ov2)
  }

  /** The registers of the body's nodes strictly inside `r` (never a top-level
      node's own registers): what `FNulledChildren` may touch. */
  ghost function InnerCapRegs(r: R.regex): set<int>
    decreases r
  {
    match r
    case Re_empty => {}
    case Re_character(_) => {}
    case Re_anchor(_) => {}
    case Re_alt(r1, r2) => InnerCapRegs(r1) + InnerCapRegs(r2)
    case Re_con(r1, r2) => InnerCapRegs(r1) + InnerCapRegs(r2)
    case Re_quant(_, _, _, r1) => CapRegsOf(r1)
    case Re_capture(_, r1) => InnerCapRegs(r1)
    case Re_lookaround(_, _, _) => {}
  }
  ghost function InnerLookRegs(r: R.regex): set<int>
    decreases r
  {
    match r
    case Re_empty => {}
    case Re_character(_) => {}
    case Re_anchor(_) => {}
    case Re_alt(r1, r2) => InnerLookRegs(r1) + InnerLookRegs(r2)
    case Re_con(r1, r2) => InnerLookRegs(r1) + InnerLookRegs(r2)
    case Re_quant(_, _, _, r1) => LookRegsOf(r1)
    case Re_capture(_, r1) => InnerLookRegs(r1)
    case Re_lookaround(_, _, _) => {}
  }
  ghost function InnerQuantRegs(r: R.regex): set<int>
    decreases r
  {
    match r
    case Re_empty => {}
    case Re_character(_) => {}
    case Re_anchor(_) => {}
    case Re_alt(r1, r2) => InnerQuantRegs(r1) + InnerQuantRegs(r2)
    case Re_con(r1, r2) => InnerQuantRegs(r1) + InnerQuantRegs(r2)
    case Re_quant(_, _, _, r1) => QuantRegsOf(r1)
    case Re_capture(_, r1) => InnerQuantRegs(r1)
    case Re_lookaround(_, _, _) => {}
  }

  lemma InnerSub(r: R.regex)
    ensures InnerCapRegs(r) <= CapRegsOf(r) && InnerLookRegs(r) <= LookRegsOf(r) && InnerQuantRegs(r) <= QuantRegsOf(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => InnerSub(r1); InnerSub(r2);
    case Re_con(r1, r2) => InnerSub(r1); InnerSub(r2);
    case Re_capture(_, r1) => InnerSub(r1);
    case _ =>
  }

  /** The frame of `FNulledChildren`: the oracle view is unchanged, sizes are
      kept, and only registers strictly inside quantifier bodies of `r` move. */
  lemma FNulledChildrenFrame(qm: AR.QMap, r: R.regex, cdnt: LCdn.cdn_table, cp: nat, rg: Regs3,
                             plus_bcv: seq<RB.code>, str: string, ov: LOr.OracleView)
    requires PIV.QuantUnique(r) && NRC.NoCdnPlusRE(r) && PlusTableOk(r, plus_bcv)
    requires WfRegs(rg) && CapValWf(rg) && ov == qm.ov && cp <= |str|
    ensures FCov(r, cdnt, cp, rg, plus_bcv, str, ov) == ov
    ensures var rg2 := FC(r, cdnt, cp, rg, plus_bcv, str, ov);
            WfRegs(rg2) && Sized3(rg2, rg) && CapValWf(rg2)
            && AgreeOutside(rg2, rg, InnerCapRegs(r), InnerLookRegs(r), InnerQuantRegs(r))
    decreases r, 1
  {
    var rg2 := FC(r, cdnt, cp, rg, plus_bcv, str, ov);
    match r
    case Re_empty =>
    case Re_character(_) =>
    case Re_anchor(_) =>
    case Re_lookaround(_, _, _) =>
    case Re_capture(_, r1) =>
      PlusTableOkChildren(r, plus_bcv);
      FNulledChildrenFrame(qm, r1, cdnt, cp, rg, plus_bcv, str, ov);
    case Re_alt(r1, r2) =>
      PlusTableOkChildren(r, plus_bcv);
      FNulledChildrenFrame(qm, r1, cdnt, cp, rg, plus_bcv, str, ov);
      var rgA := FC(r1, cdnt, cp, rg, plus_bcv, str, ov);
      FNulledChildrenFrame(qm, r2, cdnt, cp, rgA, plus_bcv, str, ov);
      assert rg2 == FC(r2, cdnt, cp, rgA, plus_bcv, str, ov);
      AgreeOutsideWeaken(rg2, rgA, InnerCapRegs(r2), InnerLookRegs(r2), InnerQuantRegs(r2), InnerCapRegs(r), InnerLookRegs(r), InnerQuantRegs(r));
      AgreeOutsideWeaken(rgA, rg, InnerCapRegs(r1), InnerLookRegs(r1), InnerQuantRegs(r1), InnerCapRegs(r), InnerLookRegs(r), InnerQuantRegs(r));
      AgreeOutsideTrans(rg2, rgA, rg, InnerCapRegs(r), InnerLookRegs(r), InnerQuantRegs(r));
    case Re_con(r1, r2) =>
      PlusTableOkChildren(r, plus_bcv);
      FNulledChildrenFrame(qm, r1, cdnt, cp, rg, plus_bcv, str, ov);
      var rgA := FC(r1, cdnt, cp, rg, plus_bcv, str, ov);
      FNulledChildrenFrame(qm, r2, cdnt, cp, rgA, plus_bcv, str, ov);
      assert rg2 == FC(r2, cdnt, cp, rgA, plus_bcv, str, ov);
      AgreeOutsideWeaken(rg2, rgA, InnerCapRegs(r2), InnerLookRegs(r2), InnerQuantRegs(r2), InnerCapRegs(r), InnerLookRegs(r), InnerQuantRegs(r));
      AgreeOutsideWeaken(rgA, rg, InnerCapRegs(r1), InnerLookRegs(r1), InnerQuantRegs(r1), InnerCapRegs(r), InnerLookRegs(r), InnerQuantRegs(r));
      AgreeOutsideTrans(rg2, rgA, rg, InnerCapRegs(r), InnerLookRegs(r), InnerQuantRegs(r));
    case Re_quant(nul, qid, q, body) =>
      PlusTableOkChildren(r, plus_bcv);
      InnerSub(body);
      match AReg.get_cp(rg.2, qid) {
        case None =>
          FNulledChildrenFrame(qm, body, cdnt, cp, rg, plus_bcv, str, ov);
          AgreeOutsideWeaken(rg2, rg, InnerCapRegs(body), InnerLookRegs(body), InnerQuantRegs(body), CapRegsOf(body), LookRegsOf(body), QuantRegsOf(body));
        case Some(start_cp) =>
          if start_cp == cp {
            var start_clock := AI.opt_int(AReg.get_clock(rg.2, qid));
            assert start_clock >= -1;
            var code := AI.get_code_v(plus_bcv, qid);
            var (rgR, ovR) := ReconAt(code, body, cdnt, cp, rg, start_clock, plus_bcv, str, ov);
            assert rg2 == rgR && FCov(r, cdnt, cp, rg, plus_bcv, str, ov) == ovR;
            ReconAtFrame(qm, r, body, qid, code, cdnt, cp, rg, start_clock, plus_bcv, str, ov);
          } else {
            AgreeOutsideRefl(rg, InnerCapRegs(r), InnerLookRegs(r), InnerQuantRegs(r));
          }
      }
  }

  /** The frame of one nested reconstruction: the null interpreter's writes and
      the children's writes all land inside the body. */
  lemma ReconAtFrame(qm: AR.QMap, r: R.regex, body: R.regex, qid: int, code: RB.code, cdnt: LCdn.cdn_table, cp: nat, rg: Regs3,
                     start_clock: int, plus_bcv: seq<RB.code>, str: string, ov: LOr.OracleView)
    requires r.Re_quant? && L1(r) == body && r.qid == qid && qid >= 0
    requires PIV.QuantUnique(r) && NRC.NoCdnPlusRE(r) && PlusTableOk(r, plus_bcv)
    requires code == AI.get_code_v(plus_bcv, qid)
    requires WfRegs(rg) && CapValWf(rg) && ov == qm.ov && cp <= |str| && start_clock >= -1
    ensures var (rg2, ov2) := ReconAt(code, body, cdnt, cp, rg, start_clock, plus_bcv, str, ov);
            ov2 == ov && WfRegs(rg2) && Sized3(rg2, rg) && CapValWf(rg2)
            && AgreeOutside(rg2, rg, CapRegsOf(body), LookRegsOf(body), QuantRegsOf(body))
    decreases r, 0
  {
    var (rg2, ov2) := ReconAt(code, body, cdnt, cp, rg, start_clock, plus_bcv, str, ov);
    var ctx := AI.cp_context(cp, str, RA.Forward);
    var inits0 := AI.FInitState(code, cp, rg.0, rg.1, rg.2, start_clock, ctx);
    var inits := inits0.(cdn := cdnt);
    var (result, _, ov1) := AI.FNullInterp(code, inits, ov, RA.Forward);
    var rg1 := match result case None => rg case Some(w) => (w.capture_regs, w.look_regs, w.quant_regs);
    PlusTableOkChildren(r, plus_bcv);
    assert (qid as nat) in PIV.QuantIds(r) && PIV.QidBody(r, qid as nat) == body;
    var inp := T.InputAt(str, cp);
    CpOfInputAt(str, cp);
    if QidCinPlus(r, qid as nat) {
      assert code == CP.compile_reconstruct_nulled(body);
      assert inits == AI.FInitState(code, TR.CpOf(inp) as int, rg.0, rg.1, rg.2, start_clock, TR.CtxOf(inp)).(cdn := inits.cdn);
      NRC.NullInterpNulled(qm, body, inp, inits, ov, rg.0, rg.1, rg.2, start_clock);
      assert ov1 == ov;
      if result.Some? {
        var ws := NRC.NulledWrites(qm, body, inp).value;
        var C := AI.FNullInterp(code, inits, ov, RA.Forward).1.clock;
        assert NRC.RegsFrom(NRC.RegsOf(result.value), ws, cp, rg, start_clock, C);
        var clks: seq<int> :| |clks| == |ws| && NRC.Incr(clks) && NRC.ClksIn(clks, start_clock, C)
                                && NRC.RegsOf(result.value) == NRC.ApplyWrites(ws, cp, clks, rg);
        ApplyWritesFrame(ws, cp, clks, rg);
        ApplyWritesCapValWf(ws, cp, clks, rg);
        NulledWritesTargets(qm, body, inp);
        AgreeOutsideWeaken(rg1, rg, CapTargets(ws), LookTargets(ws), QuantTargets(ws), CapRegsOf(body), LookRegsOf(body), QuantRegsOf(body));
      } else {
        AgreeOutsideRefl(rg, CapRegsOf(body), LookRegsOf(body), QuantRegsOf(body));
      }
    } else {
      assert code == [];
      NullInterpEmptyCode(inits, ov);
      assert result.None? && ov1 == ov;
      AgreeOutsideRefl(rg, CapRegsOf(body), LookRegsOf(body), QuantRegsOf(body));
    }
    assert WfRegs(rg1) && Sized3(rg1, rg) && CapValWf(rg1);
    FNulledChildrenFrame(qm, body, cdnt, cp, rg1, plus_bcv, str, ov1);
    InnerSub(body);
    AgreeOutsideWeaken(rg2, rg1, InnerCapRegs(body), InnerLookRegs(body), InnerQuantRegs(body), CapRegsOf(body), LookRegsOf(body), QuantRegsOf(body));
    AgreeOutsideTrans(rg2, rg1, rg, CapRegsOf(body), LookRegsOf(body), QuantRegsOf(body));
  }

  // ===========================================================================
  // 5. The groups on the first empty path (the structural set both readouts
  //    meet on), and the reset scope of the forced quantifiers on it.
  // ===========================================================================

  ghost function PathGroupsR(qm: AR.QMap, re: R.regex, inp: LC.Input): set<nat>
    requires T.TransWf(re)
    decreases re
  {
    match re
    case Re_empty => {}
    case Re_character(_) => {}
    case Re_anchor(_) => {}
    case Re_alt(r1, r2) =>
      if TR.FirstEmptyPathR(qm, r1, inp).Some? then PathGroupsR(qm, r1, inp) else PathGroupsR(qm, r2, inp)
    case Re_con(r1, r2) => PathGroupsR(qm, r1, inp) + PathGroupsR(qm, r2, inp)
    case Re_quant(nul, qid, q, r1) => if q.min == 0 then {} else PathGroupsR(qm, r1, inp)
    case Re_capture(cid, r1) => (if cid >= 0 then {cid as nat} else {}) + PathGroupsR(qm, r1, inp)
    case Re_lookaround(_, _, _) => {}
  }

  ghost function ResetGroupsR(qm: AR.QMap, re: R.regex, inp: LC.Input): set<nat>
    requires T.TransWf(re)
    decreases re
  {
    match re
    case Re_empty => {}
    case Re_character(_) => {}
    case Re_anchor(_) => {}
    case Re_alt(r1, r2) =>
      if TR.FirstEmptyPathR(qm, r1, inp).Some? then ResetGroupsR(qm, r1, inp) else ResetGroupsR(qm, r2, inp)
    case Re_con(r1, r2) => ResetGroupsR(qm, r1, inp) + ResetGroupsR(qm, r2, inp)
    case Re_quant(nul, qid, q, r1) => if q.min == 0 then {} else PIV.CapIds(r1)
    case Re_capture(cid, r1) => ResetGroupsR(qm, r1, inp)
    case Re_lookaround(_, _, _) => {}
  }

  lemma PathGroupsInCapIds(qm: AR.QMap, re: R.regex, inp: LC.Input)
    requires T.TransWf(re)
    ensures PathGroupsR(qm, re, inp) <= PIV.CapIds(re)
    ensures ResetGroupsR(qm, re, inp) <= PIV.CapIds(re)
    decreases re
  {
    match re
    case Re_empty =>
    case Re_character(_) =>
    case Re_anchor(_) =>
    case Re_alt(r1, r2) => PathGroupsInCapIds(qm, r1, inp); PathGroupsInCapIds(qm, r2, inp);
    case Re_con(r1, r2) => PathGroupsInCapIds(qm, r1, inp); PathGroupsInCapIds(qm, r2, inp);
    case Re_quant(nul, qid, q, r1) => PathGroupsInCapIds(qm, r1, inp);
    case Re_capture(cid, r1) => PathGroupsInCapIds(qm, r1, inp);
    case Re_lookaround(_, _, _) =>
  }

  /** `NulledWrites` and `FirstEmptyPathR` succeed together (CDN plus excluded;
      the annotation is the engine's nullability). */
  lemma NulledWritesIffPath(qm: AR.QMap, re: R.regex, inp: LC.Input)
    requires T.TransWf(re) && NRC.NoCdnPlusRE(re)
    ensures NRC.NulledWrites(qm, re, inp).Some? <==> TR.FirstEmptyPathR(qm, re, inp).Some?
    decreases re
  {
    match re
    case Re_empty =>
    case Re_character(_) =>
    case Re_anchor(_) =>
    case Re_lookaround(_, _, _) =>
    case Re_alt(r1, r2) => NulledWritesIffPath(qm, r1, inp); NulledWritesIffPath(qm, r2, inp);
    case Re_con(r1, r2) => NulledWritesIffPath(qm, r1, inp); NulledWritesIffPath(qm, r2, inp);
    case Re_capture(_, r1) => NulledWritesIffPath(qm, r1, inp);
    case Re_quant(nul, qid, q, r1) =>
      NulledWritesIffPath(qm, r1, inp);
      if q.min == 0 {
      } else if nul == R.NonNullable {
        NUL.TransNonNullable(r1);
        NonNullableNoPath(qm, r1, inp);
      } else if q.max == None && nul == R.CINullable && q.greedy {
        NUL.TransCINullable(r1);
        CINullablePath(qm, r1, inp);
      } else if q.max == None && nul == R.CDNullable && q.greedy {
        assert false;
      } else {
      }
  }

  lemma NonNullableNoPath(qm: AR.QMap, re: R.regex, inp: LC.Input)
    requires T.TransWf(re) && NUL.NonNullableL(T.Translate(re))
    ensures TR.FirstEmptyPathR(qm, re, inp).None?
    decreases re
  {
    match re
    case Re_empty =>
    case Re_character(_) =>
    case Re_anchor(_) =>
    case Re_lookaround(_, _, _) =>
    case Re_alt(r1, r2) => NonNullableNoPath(qm, r1, inp); NonNullableNoPath(qm, r2, inp);
    case Re_con(r1, r2) =>
      if NUL.NonNullableL(T.Translate(r1)) { NonNullableNoPath(qm, r1, inp); } else { NonNullableNoPath(qm, r2, inp); }
    case Re_capture(_, r1) => NonNullableNoPath(qm, r1, inp);
    case Re_quant(nul, qid, q, r1) => NonNullableNoPath(qm, r1, inp);
  }

  lemma CINullablePath(qm: AR.QMap, re: R.regex, inp: LC.Input)
    requires T.TransWf(re) && NUL.CINullableL(T.Translate(re))
    ensures TR.FirstEmptyPathR(qm, re, inp).Some?
    decreases re
  {
    match re
    case Re_empty =>
    case Re_character(_) =>
    case Re_anchor(_) =>
    case Re_lookaround(_, _, _) =>
    case Re_alt(r1, r2) =>
      if NUL.CINullableL(T.Translate(r1)) { CINullablePath(qm, r1, inp); } else { CINullablePath(qm, r2, inp); }
    case Re_con(r1, r2) => CINullablePath(qm, r1, inp); CINullablePath(qm, r2, inp);
    case Re_capture(_, r1) => CINullablePath(qm, r1, inp);
    case Re_quant(nul, qid, q, r1) => if q.min != 0 { CINullablePath(qm, r1, inp); }
  }

  // ===========================================================================
  // 6. Off-path subtrees stay hidden: with every capture/quant clock of `r`
  //    below `K`, `FNulledChildren` (which may re-run stale stamps at this
  //    position) leaves every capture of `r` absent under `filter_capture` at
  //    `K` — a re-run stamp's writes sit under its own stale quant node.
  // ===========================================================================

  ghost predicate LookCapsAbsent(r: R.regex, rg: Regs3) {
    forall c: nat :: c in PIV.CapIdsInLooks(r) ==> AI.get_idx(rg.0.a_cp, CP.start_reg(c)) < 0
  }

  lemma FilterHiddenAfterChildren(qm: AR.QMap, r: R.regex, cdnt: LCdn.cdn_table, cp: nat, rg: Regs3, K: int,
                                  plus_bcv: seq<RB.code>, str: string, ov: LOr.OracleView)
    requires PIV.CapUnique(r) && PIV.QuantUnique(r) && NRC.NoCdnPlusRE(r) && PlusTableOk(r, plus_bcv)
    requires WfRegs(rg) && CapValWf(rg) && ov == qm.ov && cp <= |str|
    requires RegsStale(r, rg, K) && LookCapsAbsent(r, rg)
    ensures var rg2 := FC(r, cdnt, cp, rg, plus_bcv, str, ov);
            forall c: nat :: c in PIV.CapIds(r) ==>
              AI.get_idx(AI.filter_capture(r, rg2.0.a_cp, rg2.0.a_clk, rg2.1.a_clk, rg2.2.a_clk, K), CP.start_reg(c)) < 0
    decreases r
  {
    var rg2 := FC(r, cdnt, cp, rg, plus_bcv, str, ov);
    FNulledChildrenFrame(qm, r, cdnt, cp, rg, plus_bcv, str, ov);
    var cr := rg2.0.a_cp; var cc := rg2.0.a_clk; var lc := rg2.1.a_clk; var qc := rg2.2.a_clk;
    match r
    case Re_empty =>
    case Re_character(_) =>
    case Re_anchor(_) =>
    case Re_lookaround(lid, _, r1) =>
      // the look body's captures are absent already and stay so
      forall c: nat | c in PIV.CapIds(r) ensures AI.get_idx(AI.filter_capture(r, cr, cc, lc, qc, K), CP.start_reg(c)) < 0 {
        assert c in PIV.CapIdsInLooks(r);
        assert AI.get_idx(cr, CP.start_reg(c)) < 0;
        PIV.FilterCaptureNeg(r, cr, cc, lc, qc, K, CP.start_reg(c));
      }
    case Re_capture(cid, r1) =>
      // cid's own start clock is untouched (< K): the whole subtree is cleared
      var sr := CP.start_reg(cid);
      assert AI.get_idx(cc, sr) == AI.get_idx(rg.0.a_clk, sr) by {
        InnerSub(r1);
        assert sr !in CapRegsOf(r1) by { CapRegsOfOwn(r); }
      }
      assert AI.get_idx(cc, sr) < K;
      forall c: nat | c in PIV.CapIds(r) ensures AI.get_idx(AI.filter_capture(r, cr, cc, lc, qc, K), CP.start_reg(c)) < 0 {
        if AI.get_idx(cc, sr) < 0 {
          if c == cid as nat { PIV.FilterAllNeg(r1, cr, sr); assert AI.get_idx(cr, sr) < 0 by { CapUnsetValue(rg2, sr); } }
          else { PIV.FilterAllClearsStart(r1, cr, c); }
        } else {
          var Z := AI.set_idx(cr, sr, -1);
          if c == cid as nat { PIV.FilterAllNeg(r1, Z, sr); }
          else { PIV.FilterAllClearsStart(r1, Z, c); }
        }
      }
    case Re_quant(nul, qid, q, r1) =>
      // qid's own clock is untouched (< K): filter_all clears the body
      assert AI.get_idx(qc, qid) == AI.get_idx(rg.2.a_clk, qid) by {
        InnerSub(r1);
        assert qid !in QuantRegsOf(r1) by { QuantRegsOfOwn(r); }
      }
      assert qid >= 0 && (qid as nat) in PIV.QuantIds(r);
      assert AI.get_idx(qc, qid) < K;
      forall c: nat | c in PIV.CapIds(r) ensures AI.get_idx(AI.filter_capture(r, cr, cc, lc, qc, K), CP.start_reg(c)) < 0 {
        PIV.FilterAllClearsStart(r1, cr, c);
      }
    case Re_alt(r1, r2) =>
      PlusTableOkChildren(r, plus_bcv);
      var rgA := FC(r1, cdnt, cp, rg, plus_bcv, str, ov);
      FNulledChildrenFrame(qm, r1, cdnt, cp, rg, plus_bcv, str, ov);
      FNulledChildrenFrame(qm, r2, cdnt, cp, rgA, plus_bcv, str, ov);
      assert rg2 == FC(r2, cdnt, cp, rgA, plus_bcv, str, ov);
      RegsStaleSplit(r, rg, K);
      InnerSub(r1); InnerSub(r2);
      DisjointRegs(r);
      SubAgree2(r, rg, rgA);
      assert RegsStale(r2, rgA, K) && LookCapsAbsent(r2, rgA) by { StaleFrame(r2, rg, rgA, K); }
      assert LookCapsAbsent(r, rg2) by { FNulledChildrenLookCapsAbsent(qm, r, cdnt, cp, rg, plus_bcv, str, ov); }
      FilterHiddenAfterChildren(qm, r1, cdnt, cp, rg, K, plus_bcv, str, ov);
      FilterHiddenAfterChildren(qm, r2, cdnt, cp, rgA, K, plus_bcv, str, ov);
      var f1A := AI.filter_capture(r1, rgA.0.a_cp, rgA.0.a_clk, rgA.1.a_clk, rgA.2.a_clk, K);
      var f1 := AI.filter_capture(r1, cr, cc, lc, qc, K);
      forall c: nat | c in PIV.CapIds(r) ensures AI.get_idx(AI.filter_capture(r, cr, cc, lc, qc, K), CP.start_reg(c)) < 0 {
        var j := CP.start_reg(c);
        if c in PIV.CapIds(r1) {
          assert c !in PIV.CapIds(r2);
          FilterKeepsNonStart(r2, f1, cc, lc, qc, K, j);
          // f1 at j equals f1A at j: rg2 and rgA agree on r1's registers
          if c in PIV.CapIdsInLooks(r1) {
            assert AI.get_idx(cr, j) < 0;
            PIV.FilterCaptureNeg(r1, cr, cc, lc, qc, K, j);
          } else {
            SubAgree(r, rgA, rg2);
            CapRegsOfChar(r1); QuantRegsOfChar(r1);
            FilterAtStartDep(r1, cr, rgA.0.a_cp, cc, rgA.0.a_clk, lc, rgA.1.a_clk, qc, rgA.2.a_clk, K, c);
          }
        } else {
          assert c in PIV.CapIds(r2);
          FilterKeepsNonStart(r1, cr, cc, lc, qc, K, j);
          var f2 := AI.filter_capture(r2, cr, cc, lc, qc, K);
          if c in PIV.CapIdsInLooks(r2) {
            assert AI.get_idx(cr, j) < 0;
            PIV.FilterCaptureNeg(r2, f1, cc, lc, qc, K, j);
          } else {
            FilterAtStartDep(r2, f1, cr, cc, cc, lc, lc, qc, qc, K, c);
          }
        }
      }
    case Re_con(r1, r2) =>
      PlusTableOkChildren(r, plus_bcv);
      var rgA := FC(r1, cdnt, cp, rg, plus_bcv, str, ov);
      FNulledChildrenFrame(qm, r1, cdnt, cp, rg, plus_bcv, str, ov);
      FNulledChildrenFrame(qm, r2, cdnt, cp, rgA, plus_bcv, str, ov);
      assert rg2 == FC(r2, cdnt, cp, rgA, plus_bcv, str, ov);
      RegsStaleSplit(r, rg, K);
      InnerSub(r1); InnerSub(r2);
      DisjointRegs(r);
      SubAgree2(r, rg, rgA);
      assert RegsStale(r2, rgA, K) && LookCapsAbsent(r2, rgA) by { StaleFrame(r2, rg, rgA, K); }
      assert LookCapsAbsent(r, rg2) by { FNulledChildrenLookCapsAbsent(qm, r, cdnt, cp, rg, plus_bcv, str, ov); }
      FilterHiddenAfterChildren(qm, r1, cdnt, cp, rg, K, plus_bcv, str, ov);
      FilterHiddenAfterChildren(qm, r2, cdnt, cp, rgA, K, plus_bcv, str, ov);
      var f1 := AI.filter_capture(r1, cr, cc, lc, qc, K);
      forall c: nat | c in PIV.CapIds(r) ensures AI.get_idx(AI.filter_capture(r, cr, cc, lc, qc, K), CP.start_reg(c)) < 0 {
        var j := CP.start_reg(c);
        if c in PIV.CapIds(r1) {
          assert c !in PIV.CapIds(r2);
          FilterKeepsNonStart(r2, f1, cc, lc, qc, K, j);
          if c in PIV.CapIdsInLooks(r1) {
            assert AI.get_idx(cr, j) < 0;
            PIV.FilterCaptureNeg(r1, cr, cc, lc, qc, K, j);
          } else {
            SubAgree(r, rgA, rg2);
            CapRegsOfChar(r1); QuantRegsOfChar(r1);
            FilterAtStartDep(r1, cr, rgA.0.a_cp, cc, rgA.0.a_clk, lc, rgA.1.a_clk, qc, rgA.2.a_clk, K, c);
          }
        } else {
          assert c in PIV.CapIds(r2);
          FilterKeepsNonStart(r1, cr, cc, lc, qc, K, j);
          if c in PIV.CapIdsInLooks(r2) {
            assert AI.get_idx(cr, j) < 0;
            PIV.FilterCaptureNeg(r2, f1, cc, lc, qc, K, j);
          } else {
            FilterAtStartDep(r2, f1, cr, cc, cc, lc, lc, qc, qc, K, c);
          }
        }
      }
  }

  // ---- small structural facts used above ----

  /** A capture node's own registers are not among its body's. */
  lemma CapRegsOfOwn(r: R.regex)
    requires r.Re_capture? && PIV.CapUnique(r)
    ensures CP.start_reg(r.cid) !in CapRegsOf(L1(r)) && CP.end_reg(r.cid) !in CapRegsOf(L1(r))
  {
    CapRegsOfChar(L1(r));
    assert (r.cid as nat) !in PIV.CapIds(L1(r));
  }

  /** `CapRegsOf` is exactly the start/end registers of `CapIds` (ids >= 0 under `CapUnique`). */
  lemma CapRegsOfChar(r: R.regex)
    requires PIV.CapUnique(r)
    ensures forall k: int :: k in CapRegsOf(r) <==> (exists c: nat :: c in PIV.CapIds(r) && (k == CP.start_reg(c) || k == CP.end_reg(c)))
    decreases r
  {
    match r
    case Re_alt(r1, r2) => CapRegsOfChar(r1); CapRegsOfChar(r2);
    case Re_con(r1, r2) => CapRegsOfChar(r1); CapRegsOfChar(r2);
    case Re_quant(_, _, _, r1) => CapRegsOfChar(r1);
    case Re_capture(cid, r1) => CapRegsOfChar(r1);
    case Re_lookaround(_, _, r1) => CapRegsOfChar(r1);
    case _ =>
  }

  lemma QuantRegsOfOwn(r: R.regex)
    requires r.Re_quant? && PIV.QuantUnique(r)
    ensures r.qid !in QuantRegsOf(L1(r))
  {
    QuantRegsOfChar(L1(r));
  }

  lemma QuantRegsOfChar(r: R.regex)
    requires PIV.QuantUnique(r)
    ensures forall k: int :: k in QuantRegsOf(r) <==> (k >= 0 && (k as nat) in PIV.QuantIds(r))
    decreases r
  {
    match r
    case Re_alt(r1, r2) => QuantRegsOfChar(r1); QuantRegsOfChar(r2);
    case Re_con(r1, r2) => QuantRegsOfChar(r1); QuantRegsOfChar(r2);
    case Re_quant(_, _, _, r1) => QuantRegsOfChar(r1);
    case Re_capture(_, r1) => QuantRegsOfChar(r1);
    case Re_lookaround(_, _, r1) => QuantRegsOfChar(r1);
    case _ =>
  }

  /** The two sides of an alt/con own disjoint registers. */
  lemma DisjointRegs(r: R.regex)
    requires (r.Re_alt? || r.Re_con?) && PIV.CapUnique(r) && PIV.QuantUnique(r)
    ensures CapRegsOf(L1(r)) * CapRegsOf(L2(r)) == {}
    ensures QuantRegsOf(L1(r)) * QuantRegsOf(L2(r)) == {}
  {
    CapRegsOfChar(L1(r)); CapRegsOfChar(L2(r));
    QuantRegsOfChar(L1(r)); QuantRegsOfChar(L2(r));
    forall k | k in CapRegsOf(L1(r)) ensures k !in CapRegsOf(L2(r)) {
      var c1: nat :| c1 in PIV.CapIds(L1(r)) && (k == CP.start_reg(c1) || k == CP.end_reg(c1));
      if k in CapRegsOf(L2(r)) {
        var c2: nat :| c2 in PIV.CapIds(L2(r)) && (k == CP.start_reg(c2) || k == CP.end_reg(c2));
        assert CP.start_reg(c1) == 2 * c1 && CP.end_reg(c1) == 2 * c1 + 1 && CP.start_reg(c2) == 2 * c2 && CP.end_reg(c2) == 2 * c2 + 1;
        assert c1 == c2;
        assert c1 in PIV.CapIds(L1(r)) * PIV.CapIds(L2(r));
        assert false;
      }
    }
    forall k | k in QuantRegsOf(L1(r)) ensures k !in QuantRegsOf(L2(r)) {
      assert k >= 0 && (k as nat) in PIV.QuantIds(L1(r));
      if k in QuantRegsOf(L2(r)) { assert (k as nat) in PIV.QuantIds(L1(r)) * PIV.QuantIds(L2(r)); assert false; }
    }
  }

  lemma RegsStaleSplit(r: R.regex, rg: Regs3, K: int)
    requires (r.Re_alt? || r.Re_con?) && RegsStale(r, rg, K) && LookCapsAbsent(r, rg)
    ensures RegsStale(L1(r), rg, K) && RegsStale(L2(r), rg, K) && LookCapsAbsent(L1(r), rg) && LookCapsAbsent(L2(r), rg)
  {}

  /** Staleness and absence transfer to registers that agree on the subterm's own. */
  lemma StaleFrame(r: R.regex, rg: Regs3, rg': Regs3, K: int)
    requires PIV.CapUnique(r) && PIV.QuantUnique(r)
    requires RegsStale(r, rg, K) && LookCapsAbsent(r, rg)
    requires forall k: int :: k in CapRegsOf(r) ==> AI.get_idx(rg'.0.a_cp, k) == AI.get_idx(rg.0.a_cp, k) && AI.get_idx(rg'.0.a_clk, k) == AI.get_idx(rg.0.a_clk, k)
    requires forall k: int :: k in QuantRegsOf(r) ==> AI.get_idx(rg'.2.a_clk, k) == AI.get_idx(rg.2.a_clk, k)
    ensures RegsStale(r, rg', K) && LookCapsAbsent(r, rg')
  {
    CapRegsOfChar(r);
    QuantRegsOfChar(r);
    forall c: nat | c in PIV.CapIds(r) ensures AI.get_idx(rg'.0.a_clk, CP.start_reg(c)) < K && AI.get_idx(rg'.0.a_clk, CP.end_reg(c)) < K {
      assert CP.start_reg(c) in CapRegsOf(r) && CP.end_reg(c) in CapRegsOf(r);
    }
    forall q: nat | q in PIV.QuantIds(r) ensures AI.get_idx(rg'.2.a_clk, q) < K {
      assert (q as int) in QuantRegsOf(r);
    }
    forall c: nat | c in PIV.CapIdsInLooks(r) ensures AI.get_idx(rg'.0.a_cp, CP.start_reg(c)) < 0 {
      CapIdsInLooksSub(r);
      assert CP.start_reg(c) in CapRegsOf(r);
    }
  }

  lemma CapIdsInLooksSub(r: R.regex)
    ensures PIV.CapIdsInLooks(r) <= PIV.CapIds(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => CapIdsInLooksSub(r1); CapIdsInLooksSub(r2);
    case Re_con(r1, r2) => CapIdsInLooksSub(r1); CapIdsInLooksSub(r2);
    case Re_quant(_, _, _, r1) => CapIdsInLooksSub(r1);
    case Re_capture(_, r1) => CapIdsInLooksSub(r1);
    case Re_lookaround(_, _, r1) =>
    case _ =>
  }

  lemma CapUnsetValue(rg: Regs3, k: int)
    requires CapValWf(rg) && AI.get_idx(rg.0.a_clk, k) < 0
    ensures AI.get_idx(rg.0.a_cp, k) < 0
  {}


  // ===========================================================================
  // 7. THE ENGINE-SIDE READOUT (R2): after the first empty path's writes (at
  //    clocks above `K`) and the children's reconstruction at the same
  //    position, `filter_capture` at `K` reads exactly the path's groups, each
  //    as `[cp, cp)`.
  // ===========================================================================

  /** What the filtered registers say about one capture. */
  ghost predicate ReadsAs(f: seq<int>, rg: Regs3, c: nat, cp: nat, present: bool) {
    (AI.get_idx(f, CP.start_reg(c)) >= 0 <==> present)
    && (present ==> AI.get_idx(f, CP.start_reg(c)) == cp as int
                    && AI.get_idx(rg.0.a_cp, CP.end_reg(c)) == cp as int
                    && AI.get_idx(rg.0.a_clk, CP.end_reg(c)) >= AI.get_idx(rg.0.a_clk, CP.start_reg(c)))
  }

  ghost function Filt(r: R.regex, rg: Regs3, K: int): seq<int> {
    AI.filter_capture(r, rg.0.a_cp, rg.0.a_clk, rg.1.a_clk, rg.2.a_clk, K)
  }

  /** The hypotheses shared by the readout lemmas. */
  ghost predicate ReadoutCtx(qm: AR.QMap, r: R.regex, plus_bcv: seq<RB.code>, ov: LOr.OracleView, str: string, cp: nat) {
    T.TransWf(r) && PIV.CapUnique(r) && PIV.QuantUnique(r) && LookUnique(r) && NRC.NoCdnPlusRE(r) && PlusTableOk(r, plus_bcv)
    && ov == qm.ov && cp <= |str|
  }

  ghost predicate RegsCtx(r: R.regex, rg: Regs3, K: int) {
    WfRegs(rg) && CapValWf(rg) && Covers(r, rg) && RegsStale(r, rg, K) && LookCapsAbsent(r, rg)
  }

  lemma EngineReadout(qm: AR.QMap, r: R.regex, cdnt: LCdn.cdn_table, cp: nat, rg0: Regs3, K: int, clks: seq<int>,
                      plus_bcv: seq<RB.code>, str: string, ov: LOr.OracleView)
    requires ReadoutCtx(qm, r, plus_bcv, ov, str, cp)
    requires RegsCtx(r, rg0, K)
    requires NRC.NulledWrites(qm, r, T.InputAt(str, cp)).Some?
    requires var ws := NRC.NulledWrites(qm, r, T.InputAt(str, cp)).value;
             |clks| == |ws| && NRC.Incr(clks) && (forall i :: 0 <= i < |clks| ==> clks[i] > K) && K >= -1
    ensures var inp := T.InputAt(str, cp);
            var ws := NRC.NulledWrites(qm, r, inp).value;
            var rg1 := NRC.ApplyWrites(ws, cp as int, clks, rg0);
            var rg2 := FC(r, cdnt, cp as int, rg1, plus_bcv, str, ov);
            FCov(r, cdnt, cp as int, rg1, plus_bcv, str, ov) == ov
            && WfRegs(rg2) && Sized3(rg2, rg0) && CapValWf(rg2) && LookCapsAbsent(r, rg2)
            && AgreeOutside(rg2, rg0, CapRegsOf(r), LookRegsOf(r), QuantRegsOf(r))
            && (forall c: nat :: c in PIV.CapIds(r) ==> ReadsAs(Filt(r, rg2, K), rg2, c, cp, c in PathGroupsR(qm, r, inp)))
    decreases r
  {
    var inp := T.InputAt(str, cp);
    var ws := NRC.NulledWrites(qm, r, inp).value;
    var rg1 := NRC.ApplyWrites(ws, cp as int, clks, rg0);
    var rg2 := FC(r, cdnt, cp as int, rg1, plus_bcv, str, ov);
    ApplyWritesFrame(ws, cp as int, clks, rg0);
    ApplyWritesCapValWf(ws, cp as int, clks, rg0);
    NulledWritesTargets(qm, r, inp);
    AgreeOutsideWeaken(rg1, rg0, CapTargets(ws), LookTargets(ws), QuantTargets(ws), CapRegsOf(r), LookRegsOf(r), QuantRegsOf(r));
    FNulledChildrenFrame(qm, r, cdnt, cp, rg1, plus_bcv, str, ov);
    InnerSub(r);
    AgreeOutsideWeaken(rg2, rg1, InnerCapRegs(r), InnerLookRegs(r), InnerQuantRegs(r), CapRegsOf(r), LookRegsOf(r), QuantRegsOf(r));
    AgreeOutsideTrans(rg2, rg1, rg0, CapRegsOf(r), LookRegsOf(r), QuantRegsOf(r));
    assert LookCapsAbsent(r, rg2) by {
      NulledWritesLookCapsFree(qm, r, inp);
      assert LookCapsAbsent(r, rg1);
      FNulledChildrenLookCapsAbsent(qm, r, cdnt, cp, rg1, plus_bcv, str, ov);
    }
    match r {
      case Re_empty =>
      case Re_character(_) =>
      case Re_anchor(_) =>
      case Re_lookaround(_, _, _) =>
        forall c: nat | c in PIV.CapIds(r) ensures ReadsAs(Filt(r, rg2, K), rg2, c, cp, c in PathGroupsR(qm, r, inp)) {
          assert c in PIV.CapIdsInLooks(r);
          PIV.FilterCaptureNeg(r, rg2.0.a_cp, rg2.0.a_clk, rg2.1.a_clk, rg2.2.a_clk, K, CP.start_reg(c));
        }
      case Re_capture(cid, r1) =>
        assert {:split_here} true;
        EngineReadoutCapture(qm, r, cdnt, cp, rg0, K, clks, plus_bcv, str, ov);
      case Re_quant(nul, qid, q, r1) =>
        assert {:split_here} true;
        EngineReadoutQuant(qm, r, cdnt, cp, rg0, K, clks, plus_bcv, str, ov);
      case Re_alt(r1, r2) =>
        assert {:split_here} true;
        EngineReadoutAlt(qm, r, cdnt, cp, rg0, K, clks, plus_bcv, str, ov);
      case Re_con(r1, r2) =>
        assert {:split_here} true;
        EngineReadoutCon(qm, r, cdnt, cp, rg0, K, clks, plus_bcv, str, ov);
    }
  }

  lemma LookCapsAbsentKept(r: R.regex, a: Regs3, b: Regs3)
    requires LookCapsAbsent(r, a)
    requires forall c: nat :: c in PIV.CapIdsInLooks(r) ==> AI.get_idx(b.0.a_cp, CP.start_reg(c)) == AI.get_idx(a.0.a_cp, CP.start_reg(c))
    ensures LookCapsAbsent(r, b)
  {}

  // ---- the capture arm ----
  lemma EngineReadoutCapture(qm: AR.QMap, r: R.regex, cdnt: LCdn.cdn_table, cp: nat, rg0: Regs3, K: int, clks: seq<int>,
                             plus_bcv: seq<RB.code>, str: string, ov: LOr.OracleView)
    requires r.Re_capture?
    requires ReadoutCtx(qm, r, plus_bcv, ov, str, cp)
    requires RegsCtx(r, rg0, K)
    requires NRC.NulledWrites(qm, r, T.InputAt(str, cp)).Some?
    requires var ws := NRC.NulledWrites(qm, r, T.InputAt(str, cp)).value;
             |clks| == |ws| && NRC.Incr(clks) && (forall i :: 0 <= i < |clks| ==> clks[i] > K) && K >= -1
    ensures var inp := T.InputAt(str, cp);
            var ws := NRC.NulledWrites(qm, r, inp).value;
            var rg1 := NRC.ApplyWrites(ws, cp as int, clks, rg0);
            var rg2 := FC(r, cdnt, cp as int, rg1, plus_bcv, str, ov);
            forall c: nat :: c in PIV.CapIds(r) ==> ReadsAs(Filt(r, rg2, K), rg2, c, cp, c in PathGroupsR(qm, r, inp))
    decreases r, 0
  {
    var cid := r.cid; var r1 := L1(r);
    var inp := T.InputAt(str, cp);
    var ws := NRC.NulledWrites(qm, r, inp).value;
    var w1 := NRC.NulledWrites(qm, r1, inp).value;
    var sr := CP.start_reg(cid); var er := CP.end_reg(cid);
    assert ws == [NRC.WCap(sr)] + w1 + [NRC.WCap(er)];
    var n1 := |w1|;
    assert |clks| == n1 + 2;
    var ks := clks[0]; var ke := clks[n1 + 1]; var clks1 := clks[1..n1 + 1];
    assert clks == [ks] + clks1 + [ke];
    var cpi := cp as int;
    // rg1 = end-write ∘ W1 ∘ start-write; push the end write into the initial bank
    var rgS := NRC.ApplyWrite(NRC.WCap(sr), cpi, ks, rg0);
    var rgSE := NRC.ApplyWrite(NRC.WCap(er), cpi, ke, rgS);
    var rg1 := NRC.ApplyWrites(ws, cpi, clks, rg0);
    ApplyWritesSplit3(w1, sr, er, cpi, ks, clks1, ke, rg0);
    assert rg1 == NRC.ApplyWrite(NRC.WCap(er), cpi, ke, NRC.ApplyWrites(w1, cpi, clks1, rgS));
    NulledWritesTargets(qm, r1, inp);
    CapRegsOfOwn(r);
    assert er !in CapTargets(w1) && sr !in CapTargets(w1);
    ApplyWritesOutsideCommute(w1, cpi, clks1, rgS, er, ke);
    assert rg1 == NRC.ApplyWrites(w1, cpi, clks1, rgSE);
    // the inner readout at threshold K from rgSE
    PlusTableOkChildren(r, plus_bcv);
    CapUniqueChild(r);
    assert RegsCtx(r1, rgSE, K) by {
      assert Sized3(rgSE, rg0) && WfRegs(rgSE) && CapValWf(rgSE) by {
        assert ks >= 0 && ke >= 0 && cpi >= 0;
        ApplyWritesSingle(NRC.WCap(sr), cpi, ks, rg0);
        ApplyWritesSingle(NRC.WCap(er), cpi, ke, rgS);
        ApplyWritesFrame([NRC.WCap(sr)], cpi, [ks], rg0);
        ApplyWritesCapValWf([NRC.WCap(sr)], cpi, [ks], rg0);
        ApplyWritesFrame([NRC.WCap(er)], cpi, [ke], rgS);
        ApplyWritesCapValWf([NRC.WCap(er)], cpi, [ke], rgS);
      }
      RegsCtxCaptureInner(r, rg0, rgS, rgSE, K, ks, ke);
    }
    assert NRC.Incr(clks1) && forall i :: 0 <= i < |clks1| ==> clks1[i] > K by {
      forall i, j | 0 <= i < j < |clks1| ensures clks1[i] < clks1[j] { assert clks1[i] == clks[i + 1] && clks1[j] == clks[j + 1]; }
      forall i | 0 <= i < |clks1| ensures clks1[i] > K { assert clks1[i] == clks[i + 1]; }
    }
    EngineReadout(qm, r1, cdnt, cp, rgSE, K, clks1, plus_bcv, str, ov);
    var rg2 := FC(r, cdnt, cpi, rg1, plus_bcv, str, ov);
    assert rg2 == FC(r1, cdnt, cpi, rg1, plus_bcv, str, ov);
    // cid's own registers survive the inner run
    assert AI.get_idx(rg2.0.a_clk, sr) == ks && AI.get_idx(rg2.0.a_cp, sr) == cpi
        && AI.get_idx(rg2.0.a_clk, er) == ke && AI.get_idx(rg2.0.a_cp, er) == cpi by {
      assert sr !in CapRegsOf(r1) && er !in CapRegsOf(r1);
      assert sr < |rg0.0.a_cp| && er < |rg0.0.a_cp| by { assert (cid as nat) in PIV.CapIds(r); }
      assert AI.get_idx(rgSE.0.a_clk, sr) == ks && AI.get_idx(rgSE.0.a_cp, sr) == cpi;
      assert AI.get_idx(rgSE.0.a_clk, er) == ke && AI.get_idx(rgSE.0.a_cp, er) == cpi;
    }
    var f := Filt(r, rg2, K);
    // present branch: start clock ks > K
    assert ks > K && ks >= 0;
    assert f == AI.filter_capture(r1, rg2.0.a_cp, rg2.0.a_clk, rg2.1.a_clk, rg2.2.a_clk, K);
    forall c: nat | c in PIV.CapIds(r) ensures ReadsAs(f, rg2, c, cp, c in PathGroupsR(qm, r, inp)) {
      if c == cid as nat {
        FilterKeepsNonStart(r1, rg2.0.a_cp, rg2.0.a_clk, rg2.1.a_clk, rg2.2.a_clk, K, sr);
        assert ks <= ke by { assert ks == clks[0] && ke == clks[n1 + 1]; }
      } else {
        assert c in PIV.CapIds(r1);
        assert c in PathGroupsR(qm, r, inp) <==> c in PathGroupsR(qm, r1, inp);
      }
    }
  }

  lemma CapUniqueChild(r: R.regex)
    requires PIV.CapUnique(r) && PIV.QuantUnique(r) && T.TransWf(r) && NRC.NoCdnPlusRE(r)
    ensures r.Re_alt? || r.Re_con? ==> PIV.CapUnique(L1(r)) && PIV.QuantUnique(L1(r)) && T.TransWf(L1(r)) && NRC.NoCdnPlusRE(L1(r))
                                       && PIV.CapUnique(L2(r)) && PIV.QuantUnique(L2(r)) && T.TransWf(L2(r)) && NRC.NoCdnPlusRE(L2(r))
    ensures r.Re_quant? || r.Re_capture? || r.Re_lookaround? ==> PIV.CapUnique(L1(r)) && PIV.QuantUnique(L1(r)) && T.TransWf(L1(r)) && NRC.NoCdnPlusRE(L1(r))
    ensures LookUnique(r) ==> (r.Re_alt? || r.Re_con? ==> LookUnique(L1(r)) && LookUnique(L2(r)))
    ensures LookUnique(r) ==> (r.Re_quant? || r.Re_capture? || r.Re_lookaround? ==> LookUnique(L1(r)))
  {}

  /** The register context for a capture's body after its start/end writes. */
  lemma RegsCtxCaptureInner(r: R.regex, rg0: Regs3, rgS: Regs3, rgSE: Regs3, K: int, ks: int, ke: int)
    requires r.Re_capture? && PIV.CapUnique(r)
    requires RegsCtx(r, rg0, K)
    requires Sized3(rgSE, rg0) && WfRegs(rgSE) && CapValWf(rgSE)
    requires forall k: int :: k != CP.start_reg(r.cid) && k != CP.end_reg(r.cid) ==>
               AI.get_idx(rgSE.0.a_cp, k) == AI.get_idx(rg0.0.a_cp, k) && AI.get_idx(rgSE.0.a_clk, k) == AI.get_idx(rg0.0.a_clk, k)
    requires rgSE.2 == rg0.2
    ensures RegsCtx(L1(r), rgSE, K)
  {
    var r1 := L1(r);
    CapRegsOfChar(r1);
    assert (r.cid as nat) !in PIV.CapIds(r1);
    CoversChild(r, rg0);
    CoversSized(r1, rg0, rgSE);
    forall c: nat | c in PIV.CapIds(r1) ensures AI.get_idx(rgSE.0.a_clk, CP.start_reg(c)) < K && AI.get_idx(rgSE.0.a_clk, CP.end_reg(c)) < K {
      assert c != r.cid as nat;
      assert CP.start_reg(c) != CP.start_reg(r.cid) && CP.start_reg(c) != CP.end_reg(r.cid);
      assert CP.end_reg(c) != CP.start_reg(r.cid) && CP.end_reg(c) != CP.end_reg(r.cid);
    }
    forall q: nat | q in PIV.QuantIds(r1) ensures AI.get_idx(rgSE.2.a_clk, q) < K { assert q in PIV.QuantIds(r); }
    CapIdsInLooksSub(r1);
    forall c: nat | c in PIV.CapIdsInLooks(r1) ensures AI.get_idx(rgSE.0.a_cp, CP.start_reg(c)) < 0 {
      assert c != r.cid as nat;
      assert c in PIV.CapIdsInLooks(r);
      assert CP.start_reg(c) != CP.start_reg(r.cid) && CP.start_reg(c) != CP.end_reg(r.cid);
    }
  }

  /** `[a] + w + [b]` with clocks `[ka] + cl + [kb]` applies as a, then w, then b. */
  lemma ApplyWritesSplit3(w: seq<NRC.Write>, sr: int, er: int, cp: int, ka: int, cl: seq<int>, kb: int, rg: Regs3)
    requires |cl| == |w|
    ensures NRC.ApplyWrites([NRC.WCap(sr)] + w + [NRC.WCap(er)], cp, [ka] + cl + [kb], rg)
         == NRC.ApplyWrite(NRC.WCap(er), cp, kb, NRC.ApplyWrites(w, cp, cl, NRC.ApplyWrite(NRC.WCap(sr), cp, ka, rg)))
  {
    var ws := [NRC.WCap(sr)] + w + [NRC.WCap(er)];
    var clks := [ka] + cl + [kb];
    assert ws[0] == NRC.WCap(sr) && ws[1..] == w + [NRC.WCap(er)];
    assert clks[0] == ka && clks[1..] == cl + [kb];
    var rgS := NRC.ApplyWrite(NRC.WCap(sr), cp, ka, rg);
    NRC.ApplyWritesSnoc(w, NRC.WCap(er), cp, cl, kb, rgS);
  }

  /** A write to a register no later write touches commutes to the front. */
  lemma ApplyWritesOutsideCommute(w: seq<NRC.Write>, cp: int, cl: seq<int>, rg: Regs3, er: int, kb: int)
    requires |cl| == |w| && er !in CapTargets(w)
    ensures NRC.ApplyWrite(NRC.WCap(er), cp, kb, NRC.ApplyWrites(w, cp, cl, rg))
         == NRC.ApplyWrites(w, cp, cl, NRC.ApplyWrite(NRC.WCap(er), cp, kb, rg))
    decreases |w|
  {
    if |w| > 0 {
      TargetsTail(w);
      var rg1 := NRC.ApplyWrite(w[0], cp, cl[0], rg);
      var rgE := NRC.ApplyWrite(NRC.WCap(er), cp, kb, rg);
      assert NRC.ApplyWrite(w[0], cp, cl[0], rgE) == NRC.ApplyWrite(NRC.WCap(er), cp, kb, rg1) by {
        match w[0]
        case WCap(reg) =>
          assert reg != er;
          SetRegCommute(rg.0, reg, cp, cl[0], er, kb);
        case WLook(_) =>
        case WQuant(_, _) =>
      }
      ApplyWritesOutsideCommute(w[1..], cp, cl[1..], rg1, er, kb);
    }
  }

  lemma SetRegCommute(a: AReg.Regs, k1: int, cp: int, c1: int, k2: int, c2: int)
    requires k1 != k2
    ensures AReg.set_reg(AReg.set_reg(a, k1, Some(cp), c1), k2, Some(cp), c2)
         == AReg.set_reg(AReg.set_reg(a, k2, Some(cp), c2), k1, Some(cp), c1)
  {}

  // ---- the quantifier arm ----
  lemma EngineReadoutQuant(qm: AR.QMap, r: R.regex, cdnt: LCdn.cdn_table, cp: nat, rg0: Regs3, K: int, clks: seq<int>,
                           plus_bcv: seq<RB.code>, str: string, ov: LOr.OracleView)
    requires r.Re_quant?
    requires ReadoutCtx(qm, r, plus_bcv, ov, str, cp)
    requires RegsCtx(r, rg0, K)
    requires NRC.NulledWrites(qm, r, T.InputAt(str, cp)).Some?
    requires var ws := NRC.NulledWrites(qm, r, T.InputAt(str, cp)).value;
             |clks| == |ws| && NRC.Incr(clks) && (forall i :: 0 <= i < |clks| ==> clks[i] > K) && K >= -1
    ensures var inp := T.InputAt(str, cp);
            var ws := NRC.NulledWrites(qm, r, inp).value;
            var rg1 := NRC.ApplyWrites(ws, cp as int, clks, rg0);
            var rg2 := FC(r, cdnt, cp as int, rg1, plus_bcv, str, ov);
            forall c: nat :: c in PIV.CapIds(r) ==> ReadsAs(Filt(r, rg2, K), rg2, c, cp, c in PathGroupsR(qm, r, inp))
    decreases r, 0
  {
    var nul := r.qnul; var qid := r.qid; var q := r.quant; var r1 := L1(r);
    var inp := T.InputAt(str, cp);
    var ws := NRC.NulledWrites(qm, r, inp).value;
    var cpi := cp as int;
    var rg1 := NRC.ApplyWrites(ws, cpi, clks, rg0);
    var rg2 := FC(r, cdnt, cpi, rg1, plus_bcv, str, ov);
    assert qid >= 0 && (qid as nat) in PIV.QuantIds(r);
    PlusTableOkChildren(r, plus_bcv);
    CapUniqueChild(r);
    QuantRegsOfOwn(r);
    InnerSub(r1);
    if q.min == 0 {
      // no write; the quant node is stale (< K): the body is cleared
      assert ws == [];
      assert rg1 == rg0;
      FNulledChildrenFrame(qm, r, cdnt, cp, rg1, plus_bcv, str, ov);
      assert AI.get_idx(rg2.2.a_clk, qid) == AI.get_idx(rg0.2.a_clk, qid) < K;
      forall c: nat | c in PIV.CapIds(r) ensures ReadsAs(Filt(r, rg2, K), rg2, c, cp, c in PathGroupsR(qm, r, inp)) {
        PIV.FilterAllClearsStart(r1, rg2.0.a_cp, c);
      }
    } else if nul == R.NonNullable {
      assert false;
    } else if q.max == None && nul == R.CINullable && q.greedy {
      // the nested stamp: rg1 stamps qid at (cp, k); the children run its reconstruction
      assert ws == [NRC.WQuant(qid, true)];
      var k := clks[0];
      assert |clks| == 1 && ws == [NRC.WQuant(qid, true)] && clks == [k];
      ApplyWritesSingle(NRC.WQuant(qid, true), cpi, k, rg0);
      assert rg1 == NRC.ApplyWrite(NRC.WQuant(qid, true), cpi, k, rg0);
      assert rg1.2 == AReg.set_reg(rg0.2, qid, Some(cpi), k) && rg1.0 == rg0.0 && rg1.1 == rg0.1;
      assert qid < |rg0.2.a_cp| && |rg0.2.a_cp| == |rg0.2.a_clk|;
      assert AReg.get_cp(rg1.2, qid) == Some(cpi) && AI.opt_int(AReg.get_clock(rg1.2, qid)) == k;
      var code := AI.get_code_v(plus_bcv, qid);
      assert QidCinPlus(r, qid as nat) && PIV.QidBody(r, qid as nat) == r1;
      assert code == CP.compile_reconstruct_nulled(r1);
      var (rgR, ovR) := ReconAt(code, r1, cdnt, cpi, rg1, k, plus_bcv, str, ov);
      assert rg2 == rgR;
      // unfold ReconAt: the null interpreter accepts (r1 is CI-nullable) with NulledWrites(r1)
      var ctx := AI.cp_context(cpi, str, RA.Forward);
      var inits := AI.FInitState(code, cpi, rg1.0, rg1.1, rg1.2, k, ctx).(cdn := cdnt);
      var (result, sF, ov1) := AI.FNullInterp(code, inits, ov, RA.Forward);
      CpOfInputAt(str, cp);
      assert inits == AI.FInitState(code, TR.CpOf(inp) as int, rg1.0, rg1.1, rg1.2, k, TR.CtxOf(inp)).(cdn := inits.cdn);
      NRC.NullInterpNulled(qm, r1, inp, inits, ov, rg1.0, rg1.1, rg1.2, k);
      NUL.TransCINullable(r1);
      CINullablePath(qm, r1, inp);
      NulledWritesIffPath(qm, r1, inp);
      assert result.Some? && ov1 == ov;
      var w1 := NRC.NulledWrites(qm, r1, inp).value;
      assert NRC.RegsFrom(NRC.RegsOf(result.value), w1, cpi, rg1, k, sF.clock);
      var clks1: seq<int> :| |clks1| == |w1| && NRC.Incr(clks1) && NRC.ClksIn(clks1, k, sF.clock)
                              && NRC.RegsOf(result.value) == NRC.ApplyWrites(w1, cpi, clks1, rg1);
      var rgW := NRC.ApplyWrites(w1, cpi, clks1, rg1);
      assert rg2 == FC(r1, cdnt, cpi, rgW, plus_bcv, str, ov);
      // the body's readout at threshold k from rg1 (its registers are rg0's, all < K < k)
      assert RegsCtx(r1, rg1, k) by { RegsCtxQuantInner(r, rg0, rg1, K, k); }
      assert forall i :: 0 <= i < |clks1| ==> clks1[i] > k;
      EngineReadout(qm, r1, cdnt, cp, rg1, k, clks1, plus_bcv, str, ov);
      // qid's clock survives the body's run: k >= K, present branch at K
      assert AI.get_idx(rg2.2.a_clk, qid) == k by {
        assert qid !in QuantRegsOf(r1);
        assert AI.get_idx(rg1.2.a_clk, qid) == k;
      }
      assert k >= K;
      assert Filt(r, rg2, K) == AI.filter_capture(r1, rg2.0.a_cp, rg2.0.a_clk, rg2.1.a_clk, rg2.2.a_clk, k);
      forall c: nat | c in PIV.CapIds(r) ensures ReadsAs(Filt(r, rg2, K), rg2, c, cp, c in PathGroupsR(qm, r, inp)) {
        assert c in PathGroupsR(qm, r, inp) <==> c in PathGroupsR(qm, r1, inp);
      }
    } else if q.max == None && nul == R.CDNullable && q.greedy {
      assert false;
    } else {
      // the generic forced quantifier: one clock-mark, then the body's writes
      var w1 := NRC.NulledWrites(qm, r1, inp).value;
      assert ws == [NRC.WQuant(qid, false)] + w1;
      var k := clks[0];
      var clks1 := clks[1..];
      assert ws[0] == NRC.WQuant(qid, false) && ws[1..] == w1 && clks[0] == k && clks[1..] == clks1;
      var rgM := NRC.ApplyWrite(NRC.WQuant(qid, false), cpi, k, rg0);
      assert rg1 == NRC.ApplyWrites(w1, cpi, clks1, rgM);
      assert AReg.get_cp(rgM.2, qid) == None;
      // the children skip the mark (a_cp None) and recurse into the body
      NulledWritesTargets(qm, r1, inp);
      assert qid !in QuantTargets(w1) by { QuantRegsOfChar(r1); }
      ApplyWritesFrame(w1, cpi, clks1, rgM);
      assert AReg.get_cp(rg1.2, qid) == None by {
        assert AI.get_idx(rg1.2.a_cp, qid) == AI.get_idx(rgM.2.a_cp, qid) == -1;
      }
      assert rg2 == FC(r1, cdnt, cpi, rg1, plus_bcv, str, ov);
      assert RegsCtx(r1, rgM, k) by { RegsCtxQuantInner(r, rg0, rgM, K, k); }
      assert NRC.Incr(clks1) && forall i :: 0 <= i < |clks1| ==> clks1[i] > k by {
        forall i, j | 0 <= i < j < |clks1| ensures clks1[i] < clks1[j] { assert clks1[i] == clks[i + 1] && clks1[j] == clks[j + 1]; }
        forall i | 0 <= i < |clks1| ensures clks1[i] > k { assert clks1[i] == clks[i + 1] && clks[0] < clks[i + 1]; }
      }
      EngineReadout(qm, r1, cdnt, cp, rgM, k, clks1, plus_bcv, str, ov);
      assert AI.get_idx(rg2.2.a_clk, qid) == k by {
        assert qid !in QuantRegsOf(r1);
        assert AI.get_idx(rgM.2.a_clk, qid) == k;
        assert AI.get_idx(rg1.2.a_clk, qid) == k;
      }
      assert k >= K;
      assert Filt(r, rg2, K) == AI.filter_capture(r1, rg2.0.a_cp, rg2.0.a_clk, rg2.1.a_clk, rg2.2.a_clk, k);
      forall c: nat | c in PIV.CapIds(r) ensures ReadsAs(Filt(r, rg2, K), rg2, c, cp, c in PathGroupsR(qm, r, inp)) {
        assert c in PathGroupsR(qm, r, inp) <==> c in PathGroupsR(qm, r1, inp);
      }
    }
  }

  /** The register context for a quantifier's body at the quantifier's fresh clock `k`. */
  lemma RegsCtxQuantInner(r: R.regex, rg0: Regs3, rgQ: Regs3, K: int, k: int)
    requires r.Re_quant? && PIV.QuantUnique(r) && PIV.CapUnique(r)
    requires RegsCtx(r, rg0, K) && K < k
    requires Sized3(rgQ, rg0) && WfRegs(rgQ) && CapValWf(rgQ)
    requires rgQ.0 == rg0.0 && rgQ.1 == rg0.1
    requires forall j: int :: j != r.qid ==> AI.get_idx(rgQ.2.a_clk, j) == AI.get_idx(rg0.2.a_clk, j)
    ensures RegsCtx(L1(r), rgQ, k)
  {
    CoversChild(r, rg0);
    CoversSized(L1(r), rg0, rgQ);
    assert PIV.CapIdsInLooks(L1(r)) == PIV.CapIdsInLooks(r);
    forall q: nat | q in PIV.QuantIds(L1(r)) ensures AI.get_idx(rgQ.2.a_clk, q) < k {
      assert q != r.qid as nat;
      assert AI.get_idx(rg0.2.a_clk, q) < K;
    }
    forall c: nat | c in PIV.CapIds(L1(r)) ensures AI.get_idx(rgQ.0.a_clk, CP.start_reg(c)) < k && AI.get_idx(rgQ.0.a_clk, CP.end_reg(c)) < k {
      assert c in PIV.CapIds(r);
    }
  }

  // ---- the alternation arm ----
  lemma EngineReadoutAlt(qm: AR.QMap, r: R.regex, cdnt: LCdn.cdn_table, cp: nat, rg0: Regs3, K: int, clks: seq<int>,
                         plus_bcv: seq<RB.code>, str: string, ov: LOr.OracleView)
    requires r.Re_alt?
    requires ReadoutCtx(qm, r, plus_bcv, ov, str, cp)
    requires RegsCtx(r, rg0, K)
    requires NRC.NulledWrites(qm, r, T.InputAt(str, cp)).Some?
    requires var ws := NRC.NulledWrites(qm, r, T.InputAt(str, cp)).value;
             |clks| == |ws| && NRC.Incr(clks) && (forall i :: 0 <= i < |clks| ==> clks[i] > K) && K >= -1
    ensures var inp := T.InputAt(str, cp);
            var ws := NRC.NulledWrites(qm, r, inp).value;
            var rg1 := NRC.ApplyWrites(ws, cp as int, clks, rg0);
            var rg2 := FC(r, cdnt, cp as int, rg1, plus_bcv, str, ov);
            forall c: nat :: c in PIV.CapIds(r) ==> ReadsAs(Filt(r, rg2, K), rg2, c, cp, c in PathGroupsR(qm, r, inp))
    decreases r, 0
  {
    var r1 := L1(r); var r2 := L2(r);
    var inp := T.InputAt(str, cp);
    var ws := NRC.NulledWrites(qm, r, inp).value;
    var cpi := cp as int;
    var rg1 := NRC.ApplyWrites(ws, cpi, clks, rg0);
    ApplyWritesFrame(ws, cpi, clks, rg0);
    ApplyWritesCapValWf(ws, cpi, clks, rg0);
    PlusTableOkChildren(r, plus_bcv);
    CapUniqueChild(r);
    DisjointRegs(r);
    RegsStaleSplit(r, rg0, K);
    CoversChild(r, rg0);
    InnerSub(r1); InnerSub(r2);
    FNulledChildrenFrame(qm, r1, cdnt, cp, rg1, plus_bcv, str, ov);
    var rgA := FC(r1, cdnt, cpi, rg1, plus_bcv, str, ov);
    var rg2 := FC(r, cdnt, cpi, rg1, plus_bcv, str, ov);
    assert rg2 == FC(r2, cdnt, cpi, rgA, plus_bcv, str, ov);
    NulledWritesIffPath(qm, r1, inp);
    NulledWritesIffPath(qm, r2, inp);
    var f1 := AI.filter_capture(r1, rg2.0.a_cp, rg2.0.a_clk, rg2.1.a_clk, rg2.2.a_clk, K);
    assert Filt(r, rg2, K) == AI.filter_capture(r2, f1, rg2.0.a_clk, rg2.1.a_clk, rg2.2.a_clk, K);
    if NRC.NulledWrites(qm, r1, inp).Some? {
      assert {:split_here} true;
      // ON r1: readout of r1; r2 stays hidden
      assert ws == NRC.NulledWrites(qm, r1, inp).value;
      assert PathGroupsR(qm, r, inp) == PathGroupsR(qm, r1, inp);
      EngineReadout(qm, r1, cdnt, cp, rg0, K, clks, plus_bcv, str, ov);
      // rgA agrees with rg0 on r2's registers
      ApplyWritesFrame(ws, cpi, clks, rg0);
      NulledWritesTargets(qm, r1, inp);
      FNulledChildrenFrame(qm, r1, cdnt, cp, rg1, plus_bcv, str, ov);
      assert RegsCtx(r2, rgA, K) by {
        AgreeOutsideWeaken(rg1, rg0, CapTargets(ws), LookTargets(ws), QuantTargets(ws), CapRegsOf(r1), LookRegsOf(r1), QuantRegsOf(r1));
        AgreeOutsideWeaken(rgA, rg1, InnerCapRegs(r1), InnerLookRegs(r1), InnerQuantRegs(r1), CapRegsOf(r1), LookRegsOf(r1), QuantRegsOf(r1));
        AgreeOutsideTrans(rgA, rg1, rg0, CapRegsOf(r1), LookRegsOf(r1), QuantRegsOf(r1));
        SubAgree2(r, rg0, rgA);
        StaleFrame(r2, rg0, rgA, K);
        CoversSized(r2, rg0, rgA);
      }
      FilterHiddenAfterChildren(qm, r2, cdnt, cp, rgA, K, plus_bcv, str, ov);
      FNulledChildrenFrame(qm, r2, cdnt, cp, rgA, plus_bcv, str, ov);
      assert {:split_here} true;
      SubAgree(r, rgA, rg2);
      assert LookCapsAbsent(r, rg2) by {
        NulledWritesLookCapsFree(qm, r, inp);
        FNulledChildrenLookCapsAbsent(qm, r, cdnt, cp, rg1, plus_bcv, str, ov);
      }
      forall c: nat | c in PIV.CapIds(r) ensures ReadsAs(Filt(r, rg2, K), rg2, c, cp, c in PathGroupsR(qm, r, inp)) {
        var j := CP.start_reg(c);
        if c in PIV.CapIds(r1) {
          assert c !in PIV.CapIds(r2);
          FilterKeepsNonStart(r2, f1, rg2.0.a_clk, rg2.1.a_clk, rg2.2.a_clk, K, j);
          // f1 at j == the r1 readout on rgA (rg2 agrees with rgA on r1's registers)
          ReadsAsTransfer(r1, rgA, rg2, K, c, cp, c in PathGroupsR(qm, r1, inp));
        } else {
          PathGroupsInCapIds(qm, r1, inp);
          assert c in PIV.CapIds(r2) && c !in PathGroupsR(qm, r1, inp);
          FilterKeepsNonStart(r1, rg2.0.a_cp, rg2.0.a_clk, rg2.1.a_clk, rg2.2.a_clk, K, j);
          var f2 := AI.filter_capture(r2, rg2.0.a_cp, rg2.0.a_clk, rg2.1.a_clk, rg2.2.a_clk, K);
          if c in PIV.CapIdsInLooks(r2) {
            PIV.FilterCaptureNeg(r2, f1, rg2.0.a_clk, rg2.1.a_clk, rg2.2.a_clk, K, j);
          } else {
            FilterAtStartDep(r2, f1, rg2.0.a_cp, rg2.0.a_clk, rg2.0.a_clk, rg2.1.a_clk, rg2.1.a_clk, rg2.2.a_clk, rg2.2.a_clk, K, c);
          }
        }
      }
    } else {
      assert {:split_here} true;
      // ON r2: r1 (no empty path) stays hidden; readout of r2 from rgA
      assert ws == NRC.NulledWrites(qm, r2, inp).value;
      assert PathGroupsR(qm, r, inp) == PathGroupsR(qm, r2, inp);
      ApplyWritesFrame(ws, cpi, clks, rg0);
      NulledWritesTargets(qm, r2, inp);
      // r1's registers in rg1 are rg0's: hidden after its children
      assert RegsCtx(r1, rg1, K) by {
        AgreeOutsideWeaken(rg1, rg0, CapTargets(ws), LookTargets(ws), QuantTargets(ws), CapRegsOf(r2), LookRegsOf(r2), QuantRegsOf(r2));
        StaleFrame(r1, rg0, rg1, K);
        CoversSized(r1, rg0, rg1);
        ApplyWritesCapValWf(ws, cpi, clks, rg0);
      }
      FilterHiddenAfterChildren(qm, r1, cdnt, cp, rg1, K, plus_bcv, str, ov);
      FNulledChildrenFrame(qm, r1, cdnt, cp, rg1, plus_bcv, str, ov);
      // r2's readout from rg0' := rg1 with r1's children applied = ApplyWrites(ws, rgB) where rgB := rgA with ws undone
      // (ApplyWrites is pointwise: build rgB from rgA outside the targets and rg0 on them)
      var rgB := MergeOn(rgA, rg0, CapTargets(ws), LookTargets(ws), QuantTargets(ws));
      assert NRC.ApplyWrites(ws, cpi, clks, rgB) == rgA by {
        TargetsInRangeFromCovers(qm, r2, inp, rg0);
        MergeOnApply(ws, cpi, clks, rg0, rgA, rgB, r1, r2);
      }
      assert RegsCtx(r2, rgB, K) by {
        SubAgree2(r, rg1, rgA);
        RegsCtxMerge(r, rg0, rg1, rgA, rgB, K, ws);
      }
      EngineReadout(qm, r2, cdnt, cp, rgB, K, clks, plus_bcv, str, ov);
      assert rg2 == FC(r2, cdnt, cpi, NRC.ApplyWrites(ws, cpi, clks, rgB), plus_bcv, str, ov);
      assert {:split_here} true;
      FNulledChildrenFrame(qm, r2, cdnt, cp, rgA, plus_bcv, str, ov);
      SubAgree(r, rgA, rg2);
      assert LookCapsAbsent(r, rg2) by {
        NulledWritesLookCapsFree(qm, r, inp);
        FNulledChildrenLookCapsAbsent(qm, r, cdnt, cp, rg1, plus_bcv, str, ov);
      }
      forall c: nat | c in PIV.CapIds(r) ensures ReadsAs(Filt(r, rg2, K), rg2, c, cp, c in PathGroupsR(qm, r, inp)) {
        var j := CP.start_reg(c);
        if c in PIV.CapIds(r1) {
          PathGroupsInCapIds(qm, r2, inp);
          assert PIV.CapIds(r1) * PIV.CapIds(r2) == {};
          assert c !in PIV.CapIds(r2) && c !in PathGroupsR(qm, r2, inp);
          FilterKeepsNonStart(r2, f1, rg2.0.a_clk, rg2.1.a_clk, rg2.2.a_clk, K, j);
          if c in PIV.CapIdsInLooks(r1) {
            PIV.FilterCaptureNeg(r1, rg2.0.a_cp, rg2.0.a_clk, rg2.1.a_clk, rg2.2.a_clk, K, j);
          } else {
            CapRegsOfChar(r1); QuantRegsOfChar(r1);
            assert forall c': nat :: c' in PIV.CapIds(r1) ==> CP.start_reg(c') in CapRegsOf(r1);
            assert forall q: nat :: q in PIV.QuantIds(r1) ==> (q as int) in QuantRegsOf(r1);
            FilterAtStartDep(r1, rg2.0.a_cp, rgA.0.a_cp, rg2.0.a_clk, rgA.0.a_clk, rg2.1.a_clk, rgA.1.a_clk, rg2.2.a_clk, rgA.2.a_clk, K, c);
          }
        } else {
          assert c in PIV.CapIds(r2);
          FilterKeepsNonStart(r1, rg2.0.a_cp, rg2.0.a_clk, rg2.1.a_clk, rg2.2.a_clk, K, j);
          if c in PIV.CapIdsInLooks(r2) {
            PIV.FilterCaptureNeg(r2, f1, rg2.0.a_clk, rg2.1.a_clk, rg2.2.a_clk, K, j);
            PIV.FilterCaptureNeg(r2, rg2.0.a_cp, rg2.0.a_clk, rg2.1.a_clk, rg2.2.a_clk, K, j);
          } else {
            FilterAtStartDep(r2, f1, rg2.0.a_cp, rg2.0.a_clk, rg2.0.a_clk, rg2.1.a_clk, rg2.1.a_clk, rg2.2.a_clk, rg2.2.a_clk, K, c);
          }
        }
      }
    }
  }

  // ---- the concatenation arm ----
  lemma EngineReadoutCon(qm: AR.QMap, r: R.regex, cdnt: LCdn.cdn_table, cp: nat, rg0: Regs3, K: int, clks: seq<int>,
                         plus_bcv: seq<RB.code>, str: string, ov: LOr.OracleView)
    requires r.Re_con?
    requires ReadoutCtx(qm, r, plus_bcv, ov, str, cp)
    requires RegsCtx(r, rg0, K)
    requires NRC.NulledWrites(qm, r, T.InputAt(str, cp)).Some?
    requires var ws := NRC.NulledWrites(qm, r, T.InputAt(str, cp)).value;
             |clks| == |ws| && NRC.Incr(clks) && (forall i :: 0 <= i < |clks| ==> clks[i] > K) && K >= -1
    ensures var inp := T.InputAt(str, cp);
            var ws := NRC.NulledWrites(qm, r, inp).value;
            var rg1 := NRC.ApplyWrites(ws, cp as int, clks, rg0);
            var rg2 := FC(r, cdnt, cp as int, rg1, plus_bcv, str, ov);
            forall c: nat :: c in PIV.CapIds(r) ==> ReadsAs(Filt(r, rg2, K), rg2, c, cp, c in PathGroupsR(qm, r, inp))
    decreases r, 0
  {
    var r1 := L1(r); var r2 := L2(r);
    var inp := T.InputAt(str, cp);
    var ws := NRC.NulledWrites(qm, r, inp).value;
    var w1 := NRC.NulledWrites(qm, r1, inp).value;
    var w2 := NRC.NulledWrites(qm, r2, inp).value;
    assert ws == w1 + w2;
    var n1 := |w1|;
    var cl1 := clks[..n1]; var cl2 := clks[n1..];
    assert clks == cl1 + cl2;
    var cpi := cp as int;
    var rg1 := NRC.ApplyWrites(ws, cpi, clks, rg0);
    ApplyWritesApp(w1, w2, cpi, cl1, cl2, rg0);
    var rgX := NRC.ApplyWrites(w1, cpi, cl1, rg0);
    assert rg1 == NRC.ApplyWrites(w2, cpi, cl2, rgX);
    ApplyWritesFrame(ws, cpi, clks, rg0);
    ApplyWritesCapValWf(ws, cpi, clks, rg0);
    PlusTableOkChildren(r, plus_bcv);
    CapUniqueChild(r);
    DisjointRegs(r);
    RegsStaleSplit(r, rg0, K);
    CoversChild(r, rg0);
    InnerSub(r1); InnerSub(r2);
    NulledWritesTargets(qm, r1, inp);
    NulledWritesTargets(qm, r2, inp);
    TargetsApp(w1, w2);
    assert CapTargets(w1) * CapTargets(w2) == {} && LookTargets(w1) * LookTargets(w2) == {} && QuantTargets(w1) * QuantTargets(w2) == {} by {
      assert LookRegsOf(r1) * LookRegsOf(r2) == {};
    }
    FNulledChildrenFrame(qm, r1, cdnt, cp, rg1, plus_bcv, str, ov);
    var rgA := FC(r1, cdnt, cpi, rg1, plus_bcv, str, ov);
    var rg2 := FC(r, cdnt, cpi, rg1, plus_bcv, str, ov);
    assert rg2 == FC(r2, cdnt, cpi, rgA, plus_bcv, str, ov);
    assert NRC.Incr(cl1) && NRC.Incr(cl2) && (forall i :: 0 <= i < |cl1| ==> cl1[i] > K) && (forall i :: 0 <= i < |cl2| ==> cl2[i] > K) by {
      forall i, j | 0 <= i < j < |cl2| ensures cl2[i] < cl2[j] { assert cl2[i] == clks[n1 + i] && cl2[j] == clks[n1 + j]; }
      forall i | 0 <= i < |cl2| ensures cl2[i] > K { assert cl2[i] == clks[n1 + i]; }
    }
    assert {:split_here} true;
    // (1) r1's readout from rg0a := rg0 with w2 applied (w2 touches r2's registers only)
    var rg0a := NRC.ApplyWrites(w2, cpi, cl2, rg0);
    ApplyWritesFrame(w2, cpi, cl2, rg0);
    ApplyWritesFrame(w1, cpi, cl1, rg0);
    assert rg1 == NRC.ApplyWrites(w1, cpi, cl1, rg0a) by { ApplyWritesDisjointCommute(w1, w2, cpi, cl1, cl2, rg0); }
    assert RegsCtx(r1, rg0a, K) by {
      AgreeOutsideWeaken(rg0a, rg0, CapTargets(w2), LookTargets(w2), QuantTargets(w2), CapRegsOf(r2), LookRegsOf(r2), QuantRegsOf(r2));
      SubAgree(r, rg0, rg0a);
      StaleFrame(r1, rg0, rg0a, K);
      CoversSized(r1, rg0, rg0a);
      ApplyWritesCapValWf(w2, cpi, cl2, rg0);
    }
    EngineReadout(qm, r1, cdnt, cp, rg0a, K, cl1, plus_bcv, str, ov);
    assert {:split_here} true;
    // (2) r2's readout: rgA = ApplyWrites(w2, rgB) with rgB := rgA outside w2's targets, rg0 on them
    SubAgree2(r, rg1, rgA);
    var rgB := MergeOn(rgA, rg0, CapTargets(w2), LookTargets(w2), QuantTargets(w2));
    assert NRC.ApplyWrites(w2, cpi, cl2, rgB) == rgA by {
      TargetsInRangeFromCovers(qm, r2, inp, rg0);
      MergeOnApplyCon(w1, w2, cpi, cl1, cl2, rg0, rg1, rgA, rgB, r1, r2);
    }
    assert RegsCtx(r2, rgB, K) by {
      forall k: int | k in CapRegsOf(r2) && k !in CapTargets(w2) ensures AI.get_idx(rgA.0.a_cp, k) == AI.get_idx(rg0.0.a_cp, k) && AI.get_idx(rgA.0.a_clk, k) == AI.get_idx(rg0.0.a_clk, k) {
        assert k !in CapTargets(w1) by { if k in CapTargets(w1) { assert k in CapRegsOf(r1) * CapRegsOf(r2); } }
      }
      forall k: int | k in QuantRegsOf(r2) && k !in QuantTargets(w2) ensures AI.get_idx(rgA.2.a_clk, k) == AI.get_idx(rg0.2.a_clk, k) {
        assert k !in QuantTargets(w1) by { if k in QuantTargets(w1) { assert k in QuantRegsOf(r1) * QuantRegsOf(r2); } }
      }
      RegsCtxMergeCon(r, rg0, rg1, rgA, rgB, K, w1, w2);
    }
    EngineReadout(qm, r2, cdnt, cp, rgB, K, cl2, plus_bcv, str, ov);
    assert rg2 == FC(r2, cdnt, cpi, NRC.ApplyWrites(w2, cpi, cl2, rgB), plus_bcv, str, ov);
    assert {:split_here} true;
    FNulledChildrenFrame(qm, r2, cdnt, cp, rgA, plus_bcv, str, ov);
    SubAgree(r, rgA, rg2);
    assert LookCapsAbsent(r, rg2) by {
      NulledWritesLookCapsFree(qm, r, inp);
      FNulledChildrenLookCapsAbsent(qm, r, cdnt, cp, rg1, plus_bcv, str, ov);
    }
    AgreeOutsideWeaken(rg2, rgA, InnerCapRegs(r2), InnerLookRegs(r2), InnerQuantRegs(r2), CapRegsOf(r2), LookRegsOf(r2), QuantRegsOf(r2));
    var f1 := AI.filter_capture(r1, rg2.0.a_cp, rg2.0.a_clk, rg2.1.a_clk, rg2.2.a_clk, K);
    assert Filt(r, rg2, K) == AI.filter_capture(r2, f1, rg2.0.a_clk, rg2.1.a_clk, rg2.2.a_clk, K);
    forall c: nat | c in PIV.CapIds(r) ensures ReadsAs(Filt(r, rg2, K), rg2, c, cp, c in PathGroupsR(qm, r, inp)) {
      var j := CP.start_reg(c);
      if c in PIV.CapIds(r1) {
        assert c !in PIV.CapIds(r2);
        assert c in PathGroupsR(qm, r, inp) <==> c in PathGroupsR(qm, r1, inp) by { PathGroupsInCapIds(qm, r2, inp); }
        FilterKeepsNonStart(r2, f1, rg2.0.a_clk, rg2.1.a_clk, rg2.2.a_clk, K, j);
        ReadsAsTransfer(r1, rgA, rg2, K, c, cp, c in PathGroupsR(qm, r1, inp));
      } else {
        assert c in PIV.CapIds(r2);
        assert c in PathGroupsR(qm, r, inp) <==> c in PathGroupsR(qm, r2, inp) by { PathGroupsInCapIds(qm, r1, inp); }
        FilterKeepsNonStart(r1, rg2.0.a_cp, rg2.0.a_clk, rg2.1.a_clk, rg2.2.a_clk, K, j);
        if c in PIV.CapIdsInLooks(r2) {
          PIV.FilterCaptureNeg(r2, f1, rg2.0.a_clk, rg2.1.a_clk, rg2.2.a_clk, K, j);
          PIV.FilterCaptureNeg(r2, rg2.0.a_cp, rg2.0.a_clk, rg2.1.a_clk, rg2.2.a_clk, K, j);
        } else {
          FilterAtStartDep(r2, f1, rg2.0.a_cp, rg2.0.a_clk, rg2.0.a_clk, rg2.1.a_clk, rg2.1.a_clk, rg2.2.a_clk, rg2.2.a_clk, K, c);
        }
      }
    }
  }

  // ---- helpers for the alt/con arms ----

  /** A readout on `r`'s registers transfers to a bank that agrees with it on them. */
  lemma ReadsAsTransfer(r: R.regex, a: Regs3, b: Regs3, K: int, c: nat, cp: nat, present: bool)
    requires PIV.CapUnique(r) && PIV.QuantUnique(r) && c in PIV.CapIds(r)
    requires ReadsAs(Filt(r, a, K), a, c, cp, present)
    requires forall k: int :: k in CapRegsOf(r) ==> AI.get_idx(b.0.a_cp, k) == AI.get_idx(a.0.a_cp, k) && AI.get_idx(b.0.a_clk, k) == AI.get_idx(a.0.a_clk, k)
    requires forall k: int :: k in QuantRegsOf(r) ==> AI.get_idx(b.2.a_clk, k) == AI.get_idx(a.2.a_clk, k)
    requires c in PIV.CapIdsInLooks(r) ==> AI.get_idx(a.0.a_cp, CP.start_reg(c)) < 0
    ensures ReadsAs(Filt(r, b, K), b, c, cp, present)
  {
    CapRegsOfChar(r);
    QuantRegsOfChar(r);
    var j := CP.start_reg(c);
    assert j in CapRegsOf(r) && CP.end_reg(c) in CapRegsOf(r);
    if c in PIV.CapIdsInLooks(r) {
      PIV.FilterCaptureNeg(r, a.0.a_cp, a.0.a_clk, a.1.a_clk, a.2.a_clk, K, j);
      PIV.FilterCaptureNeg(r, b.0.a_cp, b.0.a_clk, b.1.a_clk, b.2.a_clk, K, j);
    } else {
      FilterAtStartDep(r, a.0.a_cp, b.0.a_cp, a.0.a_clk, b.0.a_clk, a.1.a_clk, b.1.a_clk, a.2.a_clk, b.2.a_clk, K, c);
    }
  }

  lemma CoversSized(r: R.regex, a: Regs3, b: Regs3)
    requires Covers(r, a) && Sized3(b, a)
    ensures Covers(r, b)
  {}

  /** `a` outside the targets, `b` on them. */
  ghost function MergeOn(a: Regs3, b: Regs3, Sc: set<int>, Sl: set<int>, Sq: set<int>): Regs3
    requires Sized3(a, b)
  {
    (AReg.ARegs(seq(|a.0.a_cp|, i requires 0 <= i < |a.0.a_cp| => if i in Sc then b.0.a_cp[i] else a.0.a_cp[i]),
                seq(|a.0.a_clk|, i requires 0 <= i < |a.0.a_clk| => if i in Sc then b.0.a_clk[i] else a.0.a_clk[i])),
     AReg.ARegs(seq(|a.1.a_cp|, i requires 0 <= i < |a.1.a_cp| => if i in Sl then b.1.a_cp[i] else a.1.a_cp[i]),
                seq(|a.1.a_clk|, i requires 0 <= i < |a.1.a_clk| => if i in Sl then b.1.a_clk[i] else a.1.a_clk[i])),
     AReg.ARegs(seq(|a.2.a_cp|, i requires 0 <= i < |a.2.a_cp| => if i in Sq then b.2.a_cp[i] else a.2.a_cp[i]),
                seq(|a.2.a_clk|, i requires 0 <= i < |a.2.a_clk| => if i in Sq then b.2.a_clk[i] else a.2.a_clk[i])))
  }

  lemma MergeOnFacts(a: Regs3, b: Regs3, Sc: set<int>, Sl: set<int>, Sq: set<int>)
    requires Sized3(a, b)
    ensures var m := MergeOn(a, b, Sc, Sl, Sq);
            Sized3(m, a) && AgreeOutside(m, a, Sc, Sl, Sq)
            && (forall k: int :: k in Sc ==> AI.get_idx(m.0.a_cp, k) == AI.get_idx(b.0.a_cp, k) && AI.get_idx(m.0.a_clk, k) == AI.get_idx(b.0.a_clk, k))
            && (forall k: int :: k in Sl ==> AI.get_idx(m.1.a_cp, k) == AI.get_idx(b.1.a_cp, k) && AI.get_idx(m.1.a_clk, k) == AI.get_idx(b.1.a_clk, k))
            && (forall k: int :: k in Sq ==> AI.get_idx(m.2.a_cp, k) == AI.get_idx(b.2.a_cp, k) && AI.get_idx(m.2.a_clk, k) == AI.get_idx(b.2.a_clk, k))
  {}

  /** Applying `ws` to the merge reproduces `rgA` when `rgA` already carries `ws`
      (on the targets) and is `rgA` elsewhere. */
  lemma MergeOnApply(ws: seq<NRC.Write>, cp: int, clks: seq<int>, rg0: Regs3, rgA: Regs3, rgB: Regs3, r1: R.regex, r2: R.regex)
    requires |clks| == |ws| && Sized3(rgA, rg0) && WfRegs(rg0) && WfRegs(rgA) && TargetsInRange(ws, rg0)
    requires rgB == MergeOn(rgA, rg0, CapTargets(ws), LookTargets(ws), QuantTargets(ws))
    requires var rg1 := NRC.ApplyWrites(ws, cp, clks, rg0);
             (forall k: int :: k in CapTargets(ws) ==> AI.get_idx(rgA.0.a_cp, k) == AI.get_idx(rg1.0.a_cp, k) && AI.get_idx(rgA.0.a_clk, k) == AI.get_idx(rg1.0.a_clk, k))
             && (forall k: int :: k in LookTargets(ws) ==> AI.get_idx(rgA.1.a_cp, k) == AI.get_idx(rg1.1.a_cp, k) && AI.get_idx(rgA.1.a_clk, k) == AI.get_idx(rg1.1.a_clk, k))
             && (forall k: int :: k in QuantTargets(ws) ==> AI.get_idx(rgA.2.a_cp, k) == AI.get_idx(rg1.2.a_cp, k) && AI.get_idx(rgA.2.a_clk, k) == AI.get_idx(rg1.2.a_clk, k))
    ensures NRC.ApplyWrites(ws, cp, clks, rgB) == rgA
  {
    MergeOnFacts(rgA, rg0, CapTargets(ws), LookTargets(ws), QuantTargets(ws));
    var rgB' := NRC.ApplyWrites(ws, cp, clks, rgB);
    var rg1 := NRC.ApplyWrites(ws, cp, clks, rg0);
    ApplyWritesFrame(ws, cp, clks, rgB);
    assert TargetsInRange(ws, rgB);
    ApplyWritesOnTargets(ws, cp, clks, rgB, rg0);
    assert Sized3(rgB', rgA);
    SeqExt(rgB'.0.a_cp, rgA.0.a_cp); SeqExt(rgB'.0.a_clk, rgA.0.a_clk);
    SeqExt(rgB'.1.a_cp, rgA.1.a_cp); SeqExt(rgB'.1.a_clk, rgA.1.a_clk);
    SeqExt(rgB'.2.a_cp, rgA.2.a_cp); SeqExt(rgB'.2.a_clk, rgA.2.a_clk);
  }

  lemma MergeOnApplyCon(w1: seq<NRC.Write>, w2: seq<NRC.Write>, cp: int, cl1: seq<int>, cl2: seq<int>,
                        rg0: Regs3, rg1: Regs3, rgA: Regs3, rgB: Regs3, r1: R.regex, r2: R.regex)
    requires |cl1| == |w1| && |cl2| == |w2| && WfRegs(rg0) && TargetsInRange(w2, rg0)
    requires rg1 == NRC.ApplyWrites(w2, cp, cl2, NRC.ApplyWrites(w1, cp, cl1, rg0))
    requires Sized3(rgA, rg0) && WfRegs(rgA)
    requires AgreeOutside(rgA, rg1, InnerCapRegs(r1), InnerLookRegs(r1), InnerQuantRegs(r1))
    requires CapTargets(w2) * CapRegsOf(r1) == {} && LookTargets(w2) * LookRegsOf(r1) == {} && QuantTargets(w2) * QuantRegsOf(r1) == {}
    requires InnerCapRegs(r1) <= CapRegsOf(r1) && InnerLookRegs(r1) <= LookRegsOf(r1) && InnerQuantRegs(r1) <= QuantRegsOf(r1)
    requires rgB == MergeOn(rgA, rg0, CapTargets(w2), LookTargets(w2), QuantTargets(w2))
    ensures NRC.ApplyWrites(w2, cp, cl2, rgB) == rgA
  {
    var rgX := NRC.ApplyWrites(w1, cp, cl1, rg0);
    ApplyWritesFrame(w1, cp, cl1, rg0);
    ApplyWritesFrame(w2, cp, cl2, rgX);
    assert TargetsInRange(w2, rgX);
    ApplyWritesOnTargets(w2, cp, cl2, rgX, rg0);
    var rg1' := NRC.ApplyWrites(w2, cp, cl2, rg0);
    ApplyWritesFrame(w2, cp, cl2, rg0);
    // on w2's targets rgA == rg1 == ApplyWrites(w2, rg0)
    MergeOnApply(w2, cp, cl2, rg0, rgA, rgB, r1, r2);
  }

  lemma RegsCtxMerge(r: R.regex, rg0: Regs3, rg1: Regs3, rgA: Regs3, rgB: Regs3, K: int, ws: seq<NRC.Write>)
    requires r.Re_alt? && PIV.CapUnique(r) && PIV.QuantUnique(r)
    requires RegsCtx(r, rg0, K)
    requires Sized3(rgA, rg0) && WfRegs(rgA) && CapValWf(rgA)
    requires rgB == MergeOn(rgA, rg0, CapTargets(ws), LookTargets(ws), QuantTargets(ws))
    requires forall k: int :: k in CapRegsOf(L2(r)) ==> AI.get_idx(rgA.0.a_cp, k) == AI.get_idx(rg1.0.a_cp, k) && AI.get_idx(rgA.0.a_clk, k) == AI.get_idx(rg1.0.a_clk, k)
    requires forall k: int :: k in QuantRegsOf(L2(r)) ==> AI.get_idx(rgA.2.a_cp, k) == AI.get_idx(rg1.2.a_cp, k) && AI.get_idx(rgA.2.a_clk, k) == AI.get_idx(rg1.2.a_clk, k)
    requires AgreeOutside(rg1, rg0, CapTargets(ws), LookTargets(ws), QuantTargets(ws))
    ensures RegsCtx(L2(r), rgB, K)
  {
    MergeOnFacts(rgA, rg0, CapTargets(ws), LookTargets(ws), QuantTargets(ws));
    RegsStaleSplit(r, rg0, K);
    forall k: int | k in CapRegsOf(L2(r))
      ensures AI.get_idx(rgB.0.a_cp, k) == AI.get_idx(rg0.0.a_cp, k) && AI.get_idx(rgB.0.a_clk, k) == AI.get_idx(rg0.0.a_clk, k)
    { if k in CapTargets(ws) { } else { } }
    forall k: int | k in QuantRegsOf(L2(r)) ensures AI.get_idx(rgB.2.a_clk, k) == AI.get_idx(rg0.2.a_clk, k)
    { if k in QuantTargets(ws) { } else { } }
    StaleFrame(L2(r), rg0, rgB, K);
    CoversChild(r, rg0);
    CoversSized(L2(r), rg0, rgB);
    assert CapValWf(rgB) by {
      forall k: int | AI.get_idx(rgB.0.a_clk, k) < 0 ensures AI.get_idx(rgB.0.a_cp, k) < 0 { if k in CapTargets(ws) { } else { } }
      forall k: int | AI.get_idx(rgB.0.a_cp, k) < 0 ensures AI.get_idx(rgB.0.a_clk, k) < 0 { if k in CapTargets(ws) { } else { } }
    }
  }

  lemma RegsCtxMergeCon(r: R.regex, rg0: Regs3, rg1: Regs3, rgA: Regs3, rgB: Regs3, K: int, w1: seq<NRC.Write>, w2: seq<NRC.Write>)
    requires r.Re_con? && PIV.CapUnique(r) && PIV.QuantUnique(r)
    requires RegsCtx(r, rg0, K)
    requires Sized3(rgA, rg0) && WfRegs(rgA) && CapValWf(rgA)
    requires rgB == MergeOn(rgA, rg0, CapTargets(w2), LookTargets(w2), QuantTargets(w2))
    requires forall k: int :: k in CapRegsOf(L2(r)) && k !in CapTargets(w2) ==> AI.get_idx(rgA.0.a_cp, k) == AI.get_idx(rg0.0.a_cp, k) && AI.get_idx(rgA.0.a_clk, k) == AI.get_idx(rg0.0.a_clk, k)
    requires forall k: int :: k in QuantRegsOf(L2(r)) && k !in QuantTargets(w2) ==> AI.get_idx(rgA.2.a_clk, k) == AI.get_idx(rg0.2.a_clk, k)
    ensures RegsCtx(L2(r), rgB, K)
  {
    MergeOnFacts(rgA, rg0, CapTargets(w2), LookTargets(w2), QuantTargets(w2));
    RegsStaleSplit(r, rg0, K);
    forall k: int | k in CapRegsOf(L2(r))
      ensures AI.get_idx(rgB.0.a_cp, k) == AI.get_idx(rg0.0.a_cp, k) && AI.get_idx(rgB.0.a_clk, k) == AI.get_idx(rg0.0.a_clk, k)
    {}
    forall k: int | k in QuantRegsOf(L2(r)) ensures AI.get_idx(rgB.2.a_clk, k) == AI.get_idx(rg0.2.a_clk, k) {}
    StaleFrame(L2(r), rg0, rgB, K);
    CoversChild(r, rg0);
    CoversSized(L2(r), rg0, rgB);
    assert CapValWf(rgB) by {
      forall k: int | AI.get_idx(rgB.0.a_clk, k) < 0 ensures AI.get_idx(rgB.0.a_cp, k) < 0 { if k in CapTargets(w2) { } else { } }
      forall k: int | AI.get_idx(rgB.0.a_cp, k) < 0 ensures AI.get_idx(rgB.0.a_clk, k) < 0 { if k in CapTargets(w2) { } else { } }
    }
  }

  lemma ApplyWritesApp(a: seq<NRC.Write>, b: seq<NRC.Write>, cp: int, ca: seq<int>, cb: seq<int>, rg: Regs3)
    requires |ca| == |a| && |cb| == |b|
    ensures NRC.ApplyWrites(a + b, cp, ca + cb, rg) == NRC.ApplyWrites(b, cp, cb, NRC.ApplyWrites(a, cp, ca, rg))
    decreases |a|
  {
    if |a| == 0 {
      assert a + b == b && ca + cb == cb;
    } else {
      assert (a + b)[0] == a[0] && (a + b)[1..] == a[1..] + b;
      assert (ca + cb)[0] == ca[0] && (ca + cb)[1..] == ca[1..] + cb;
      ApplyWritesApp(a[1..], b, cp, ca[1..], cb, NRC.ApplyWrite(a[0], cp, ca[0], rg));
    }
  }

  /** Writes to disjoint register sets commute. */
  lemma ApplyWritesDisjointCommute(w1: seq<NRC.Write>, w2: seq<NRC.Write>, cp: int, cl1: seq<int>, cl2: seq<int>, rg: Regs3)
    requires |cl1| == |w1| && |cl2| == |w2|
    requires CapTargets(w1) * CapTargets(w2) == {} && LookTargets(w1) * LookTargets(w2) == {} && QuantTargets(w1) * QuantTargets(w2) == {}
    ensures NRC.ApplyWrites(w2, cp, cl2, NRC.ApplyWrites(w1, cp, cl1, rg)) == NRC.ApplyWrites(w1, cp, cl1, NRC.ApplyWrites(w2, cp, cl2, rg))
    decreases |w1|
  {
    if |w1| > 0 {
      TargetsTail(w1);
      var rgH := NRC.ApplyWrite(w1[0], cp, cl1[0], rg);
      // one write commutes with all of w2
      assert w1[0].WCap? ==> w1[0].reg in CapTargets(w1);
      assert w1[0].WLook? ==> w1[0].lid in LookTargets(w1);
      assert w1[0].WQuant? ==> w1[0].qid in QuantTargets(w1);
      assert w1[0].WCap? ==> w1[0].reg !in CapTargets(w2) by { if w1[0].WCap? && w1[0].reg in CapTargets(w2) { assert w1[0].reg in CapTargets(w1) * CapTargets(w2); } }
      assert w1[0].WLook? ==> w1[0].lid !in LookTargets(w2) by { if w1[0].WLook? && w1[0].lid in LookTargets(w2) { assert w1[0].lid in LookTargets(w1) * LookTargets(w2); } }
      assert w1[0].WQuant? ==> w1[0].qid !in QuantTargets(w2) by { if w1[0].WQuant? && w1[0].qid in QuantTargets(w2) { assert w1[0].qid in QuantTargets(w1) * QuantTargets(w2); } }
      ApplyWriteCommuteAll(w1[0], cl1[0], w2, cp, cl2, rg);
      ApplyWritesDisjointCommute(w1[1..], w2, cp, cl1[1..], cl2, rgH);
    }
  }

  lemma ApplyWriteCommuteAll(w: NRC.Write, k: int, ws: seq<NRC.Write>, cp: int, cl: seq<int>, rg: Regs3)
    requires |cl| == |ws|
    requires w.WCap? ==> w.reg !in CapTargets(ws)
    requires w.WLook? ==> w.lid !in LookTargets(ws)
    requires w.WQuant? ==> w.qid !in QuantTargets(ws)
    ensures NRC.ApplyWrites(ws, cp, cl, NRC.ApplyWrite(w, cp, k, rg)) == NRC.ApplyWrite(w, cp, k, NRC.ApplyWrites(ws, cp, cl, rg))
    decreases |ws|
  {
    if |ws| > 0 {
      TargetsTail(ws);
      var rg1 := NRC.ApplyWrite(ws[0], cp, cl[0], rg);
      assert NRC.ApplyWrite(ws[0], cp, cl[0], NRC.ApplyWrite(w, cp, k, rg)) == NRC.ApplyWrite(w, cp, k, rg1) by {
        match (w, ws[0])
        case (WCap(a), WCap(b)) => SetRegCommute(rg.0, a, cp, k, b, cl[0]);
        case (WLook(a), WLook(b)) => SetRegCommute(rg.1, a, cp, k, b, cl[0]);
        case (WQuant(a, ba), WQuant(b, bb)) => SetRegCommuteQ(rg.2, a, ba, cp, k, b, bb, cl[0]);
        case _ =>
      }
      ApplyWriteCommuteAll(w, k, ws[1..], cp, cl[1..], rg1);
    }
  }

  lemma SetRegCommuteQ(a: AReg.Regs, k1: int, b1: bool, cp: int, c1: int, k2: int, b2: bool, c2: int)
    requires k1 != k2
    ensures AReg.set_reg(AReg.set_reg(a, k1, if b1 then Some(cp) else None, c1), k2, if b2 then Some(cp) else None, c2)
         == AReg.set_reg(AReg.set_reg(a, k2, if b2 then Some(cp) else None, c2), k1, if b1 then Some(cp) else None, c1)
  {}
}
