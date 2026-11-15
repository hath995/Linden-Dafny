// (G4a) The look and quant banks of the reconstructed winner: what `M.WinRegsOk` asks of them, carried through
// `FReconstructPlus` as register invariants (design: linden-equiv/endgame/G4a-design.md).
//
// The replay code `compile_reconstruct_nulled(body)` never emits a look body (a look node is one gate), so it
// gates only on lids DIRECTLY in `body` and writes only quantifiers outside looks. The one-step facts are
// ClockMono's (`FAdvanceEpsilon*`); this module lifts them through `FNulledPlus`/`FNulledChildren` in the shape
// of `LB.FNulledPlusLookSetIn`.
module LindenElkReconBank {
  import opened Std.Wrappers
  import R = RegElkRegex
  import RB = Bytecode
  import CP = Compiler
  import AI = ArrayInterp
  import AReg = Array_Regs
  import LOr = Oracle
  import LAnc = Anchors
  import LCdn = Cdn
  import CM = LindenElkClockMono
  import LB = LindenElkLookBank
  import PIV = LindenElkPikeInv
  import LTB = LindenElkLookTables
  import M = LindenElkMain
  import NRR = LindenElkNulledReconRegs

  // =========================================================================
  // 1. The shape of the replay code.
  // =========================================================================

  /** Look gates name lids in `DL`, quant writes name ids in `QO`, and nothing writes the oracle. */
  ghost predicate ShapeOk(c: RB.code, DL: set<int>, QO: set<int>) {
    forall pc: nat :: pc < |c| ==>
      (c[pc].CheckOracle? ==> c[pc].col in DL) && (c[pc].NegCheckOracle? ==> c[pc].ncl in DL)
      && (c[pc].SetQuantToClock? ==> c[pc].sq in QO) && !c[pc].WriteOracle?
  }

  ghost predicate TLShape(t: CP.treelist, DL: set<int>, QO: set<int>)
    decreases t
  {
    match t
    case Leaf(l) => forall i | 0 <= i < |l| ::
      (l[i].CheckOracle? ==> l[i].col in DL) && (l[i].NegCheckOracle? ==> l[i].ncl in DL)
      && (l[i].SetQuantToClock? ==> l[i].sq in QO) && !l[i].WriteOracle?
    case Concat(a, b) => TLShape(a, DL, QO) && TLShape(b, DL, QO)
  }

  lemma FlattenShape(t: CP.treelist, tail: RB.code, DL: set<int>, QO: set<int>)
    requires TLShape(t, DL, QO) && ShapeOk(tail, DL, QO)
    ensures ShapeOk(CP.tl_flatten(t, tail), DL, QO)
    decreases t
  {
    match t
    case Leaf(l) =>
      var f := l + tail;
      forall pc: nat | pc < |f|
        ensures (f[pc].CheckOracle? ==> f[pc].col in DL) && (f[pc].NegCheckOracle? ==> f[pc].ncl in DL)
                && (f[pc].SetQuantToClock? ==> f[pc].sq in QO) && !f[pc].WriteOracle?
      {
        if pc < |l| { assert f[pc] == l[pc]; } else { assert f[pc] == tail[pc - |l|]; }
      }
    case Concat(a, b) =>
      FlattenShape(b, tail, DL, QO);
      FlattenShape(a, CP.tl_flatten(b, tail), DL, QO);
  }

  lemma Chain3Shape(DL: set<int>, QO: set<int>, a: CP.treelist, b: CP.treelist, d: CP.treelist)
    requires TLShape(a, DL, QO) && TLShape(b, DL, QO) && TLShape(d, DL, QO)
    ensures TLShape(CP.chain([a, b, d]), DL, QO)
  {
    LB.Chain3(a, b, d);
    assert TLShape(CP.Concat(a, b), DL, QO);
  }

  lemma Chain4Shape(DL: set<int>, QO: set<int>, a: CP.treelist, b: CP.treelist, d: CP.treelist, e: CP.treelist)
    requires TLShape(a, DL, QO) && TLShape(b, DL, QO) && TLShape(d, DL, QO) && TLShape(e, DL, QO)
    ensures TLShape(CP.chain([a, b, d, e]), DL, QO)
  {
    LB.Chain4(a, b, d, e);
    assert TLShape(CP.Concat(a, b), DL, QO);
    assert TLShape(CP.Concat(CP.Concat(a, b), d), DL, QO);
  }

  /** The ReconstructNulled compiler gates only at `r`'s direct lids and writes only `r`'s outside-look qids. */
  lemma CompileShapeRN(r: R.regex, nextl: RB.Label, DL: set<int>, QO: set<int>)
    requires LTB.LookUnique(r) && PIV.QuantUnique(r)
    requires forall l: nat :: l in M.DirectLookIds(r) ==> (l as int) in DL
    requires forall q: nat :: q in PIV.QuantIdsOutsideLooks(r) ==> (q as int) in QO
    ensures TLShape(CP.compile(r, nextl, CP.ReconstructNulled).0, DL, QO)
    decreases CP.rsize(r), 0
  {
    match r
    case Re_empty =>
    case Re_character(c) =>
    case Re_anchor(a) =>
    case Re_lookaround(lookid, looktype, r1) =>
      assert lookid >= 0 && (lookid as nat) in M.DirectLookIds(r);
    case Re_capture(cid, r1) =>
    assert M.DirectLookIds(r1) <= M.DirectLookIds(r) && PIV.QuantIdsOutsideLooks(r1) <= PIV.QuantIdsOutsideLooks(r);
      var (l1, f1) := CP.compile(r1, nextl + 1, CP.ReconstructNulled);
      CompileShapeRN(r1, nextl + 1, DL, QO);
      Chain3Shape(DL, QO, CP.Leaf([RB.SetRegisterToCP(CP.start_reg(cid))]), l1, CP.Leaf([RB.SetRegisterToCP(CP.end_reg(cid))]));
    case Re_con(r1, r2) =>
    assert M.DirectLookIds(r1) <= M.DirectLookIds(r) && PIV.QuantIdsOutsideLooks(r1) <= PIV.QuantIdsOutsideLooks(r);
    assert M.DirectLookIds(r2) <= M.DirectLookIds(r) && PIV.QuantIdsOutsideLooks(r2) <= PIV.QuantIdsOutsideLooks(r);
      var (l1, f1) := CP.compile(r1, nextl, CP.ReconstructNulled);
      CompileShapeRN(r1, nextl, DL, QO);
      CompileShapeRN(r2, f1, DL, QO);
    case Re_alt(r1, r2) =>
    assert M.DirectLookIds(r1) <= M.DirectLookIds(r) && PIV.QuantIdsOutsideLooks(r1) <= PIV.QuantIdsOutsideLooks(r);
    assert M.DirectLookIds(r2) <= M.DirectLookIds(r) && PIV.QuantIdsOutsideLooks(r2) <= PIV.QuantIdsOutsideLooks(r);
      var (l1, f1) := CP.compile(r1, nextl + 1, CP.ReconstructNulled);
      var (l2, f2) := CP.compile(r2, f1 + 1, CP.ReconstructNulled);
      CompileShapeRN(r1, nextl + 1, DL, QO);
      CompileShapeRN(r2, f1 + 1, DL, QO);
      var lf := CP.Leaf([RB.Fork(nextl + 1, f1 + 1)]);
      var lj := CP.Leaf([RB.Jmp(f2)]);
      assert TLShape(lf, DL, QO) && TLShape(lj, DL, QO);
      Chain4Shape(DL, QO, lf, l1, lj, l2);
    case Re_quant(nul, qid, quant, r1) =>
      assert qid >= 0 && (qid as nat) in PIV.QuantIdsOutsideLooks(r);
      if quant.min == 0 {
      } else if nul == R.NonNullable {
      } else if quant.max == None && nul == R.CINullable && quant.greedy {
      } else if quant.max == None && nul == R.CDNullable && quant.greedy {
      } else {
      assert M.DirectLookIds(r1) <= M.DirectLookIds(r) && PIV.QuantIdsOutsideLooks(r1) <= PIV.QuantIdsOutsideLooks(r);
        CompileShapeRN(r1, nextl + 1, DL, QO);
        var (l1, f1) := CP.compile(r1, nextl + 1, CP.ReconstructNulled);
        assert TLShape(CP.Leaf([RB.SetQuantToClock(qid, false)]), DL, QO);
      }
  }

  lemma ReconCodeShape(r: R.regex, DL: set<int>, QO: set<int>)
    requires LTB.LookUnique(r) && PIV.QuantUnique(r)
    requires forall l: nat :: l in M.DirectLookIds(r) ==> (l as int) in DL
    requires forall q: nat :: q in PIV.QuantIdsOutsideLooks(r) ==> (q as int) in QO
    ensures ShapeOk(CP.compile_reconstruct_nulled(r), DL, QO)
  {
    CompileShapeRN(r, 0, DL, QO);
    FlattenShape(CP.compile(r, 0, CP.ReconstructNulled).0, [RB.Accept], DL, QO);
  }

  lemma ShapeOkCM(c: RB.code, DL: set<int>, QO: set<int>)
    requires ShapeOk(c, DL, QO)
    ensures CM.LookChecksInside(c, DL) && CM.QuantWritesInside(c, QO) && CM.NoWriteOracleCode(c)
  {}

  /** A body outside looks has its direct lids and outside-look qids among the regex's. */
  lemma QidBodyOuter(r: R.regex, q: nat)
    requires q in PIV.QuantIdsOutsideLooks(r) && PIV.QuantUnique(r) && LTB.LookUnique(r)
    ensures q in PIV.QuantIds(r)
    ensures M.DirectLookIds(PIV.QidBody(r, q)) <= M.DirectLookIds(r)
    ensures PIV.QuantIdsOutsideLooks(PIV.QidBody(r, q)) <= PIV.QuantIdsOutsideLooks(r)
    ensures PIV.QuantUnique(PIV.QidBody(r, q)) && LTB.LookUnique(PIV.QidBody(r, q))
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      PIV.QuantIdsSplit(r1); PIV.QuantIdsSplit(r2);
      if q in PIV.QuantIdsOutsideLooks(r1) { QidBodyOuter(r1, q); }
      else {
        QidBodyOuter(r2, q);
        assert q !in PIV.QuantIds(r1) by { if q in PIV.QuantIds(r1) { assert q in PIV.QuantIds(r1) * PIV.QuantIds(r2); } }
      }
    case Re_con(r1, r2) =>
      PIV.QuantIdsSplit(r1); PIV.QuantIdsSplit(r2);
      if q in PIV.QuantIdsOutsideLooks(r1) { QidBodyOuter(r1, q); }
      else {
        QidBodyOuter(r2, q);
        assert q !in PIV.QuantIds(r1) by { if q in PIV.QuantIds(r1) { assert q in PIV.QuantIds(r1) * PIV.QuantIds(r2); } }
      }
    case Re_quant(nul, qid0, quant, r1) =>
      if qid0 >= 0 && (qid0 as nat) == q {
      } else {
        QidBodyOuter(r1, q);
      }
    case Re_capture(_, r1) => QidBodyOuter(r1, q);
  }

  // =========================================================================
  // 2. The bank invariant through one null run.
  // =========================================================================

  /** What `M.WinRegsOk` asks of the look and quant banks, minus `LookSetIn` (LookBank has it) and `LookCpsLE`
      (it follows from the oracle half). */
  ghost predicate BankOk(lk: AReg.Regs, qt: AReg.Regs, ov: LOr.OracleView,
                         lk0: AReg.Regs, DL: set<int>, qt0: AReg.Regs, QO: set<int>) {
    CM.LookCpsOracleTrue(lk, ov) && CM.LookClkSetWithCp(lk) && CM.LookCpSetWithClk(lk)
    && CM.RegsAgreeOutside(lk, lk0, DL) && CM.RegsAgreeOutside(qt, qt0, QO)
  }

  /** `CM.FAdvanceEpsilonLookClkSet` from a clock `>= -1`: a null run starts at the stamp's clock, which is
      `opt_int(get_clock(..)) >= -1`, and its look writes stamp `s.clock + 1 >= 0`. */
  lemma FAdvanceEpsilonLookClkSetM1(c: RB.code, s: AI.VmState, ov: LOr.OracleView, dir: LAnc.direction)
    requires |s.processed.true_set| == RB.size(c) && |s.processed.false_set| == RB.size(c)
    requires s.clock >= -1
    requires CM.VmLookClkSet(s)
    ensures CM.VmLookClkSet(AI.FAdvanceEpsilon(c, s, ov, dir).0)
    decreases AI.unprocessed(s.processed), |s.active|
  {
    if |s.active| == 0 { return; }
    var t := s.active[0];
    var ac := s.active[1..];
    assert t in s.active;
    assert forall x | x in ac :: x in s.active;
    if AI.bpc_mem(s.processed, t.pc, t.exit_allowed) {
      FAdvanceEpsilonLookClkSetM1(c, s.(active := ac), ov, dir);
      return;
    }
    var b0 := s.processed;
    var s1 := s.(clock := s.clock + 1, processed := AI.bpc_add(b0, t.pc, t.exit_allowed));
    assert AI.unprocessed(s1.processed) <= AI.unprocessed(b0)
        && (0 <= t.pc < RB.size(c) ==> AI.unprocessed(s1.processed) < AI.unprocessed(b0))
      by { AI.UnprocessedAdd(b0, t.pc, t.exit_allowed); }
    match RB.get_instr(c, t.pc) {
      case Consume(ce) =>
        var (nb, ni) := AI.add_thread(t, ce, s1.blocked, s1.isblocked);
        var s2 := s1.(blocked := nb, isblocked := ni, active := ac);
        assert CM.VmLookClkSet(s2) by {
          forall tb | tb in nb ensures CM.LookClkSetWithCp(tb.0.look_regs) {
            assert tb == (t, ce) || tb in s1.blocked;
          }
        }
        FAdvanceEpsilonLookClkSetM1(c, s2, ov, dir);
      case Accept =>
      case Jmp(x) =>
        FAdvanceEpsilonLookClkSetM1(c, s1.(active := [t.(pc := x)] + ac), ov, dir);
      case Fork(x, y) =>
        var newt := AI.Thread(x, t.capture_regs, t.look_regs, t.quant_regs, t.exit_allowed);
        FAdvanceEpsilonLookClkSetM1(c, s1.(active := [newt, t.(pc := y)] + ac), ov, dir);
      case SetRegisterToCP(reg) =>
        var t2 := t.(capture_regs := AReg.set_reg(t.capture_regs, reg, Some(s1.cp), s1.clock), pc := t.pc + 1);
        FAdvanceEpsilonLookClkSetM1(c, s1.(active := [t2] + ac), ov, dir);
      case SetQuantToClock(q, bq) =>
        var ocp := if bq then Some(s1.cp) else None;
        var t2 := t.(quant_regs := AReg.set_reg(t.quant_regs, q, ocp, s1.clock), pc := t.pc + 1);
        FAdvanceEpsilonLookClkSetM1(c, s1.(active := [t2] + ac), ov, dir);
      case CheckOracle(l) =>
        if LOr.view_get_oracle(ov, s1.cp, l) {
          var t2 := t.(pc := t.pc + 1, look_regs := AReg.set_reg(t.look_regs, l, Some(s1.cp), s1.clock));
          assert CM.LookClkSetWithCp(t.look_regs);
          CM.SetRegLookClkSet(t.look_regs, l, s1.cp, s1.clock);   // s1.clock == s.clock + 1 >= 0
          FAdvanceEpsilonLookClkSetM1(c, s1.(active := [t2] + ac), ov, dir);
        } else {
          FAdvanceEpsilonLookClkSetM1(c, s1.(active := ac), ov, dir);
        }
      case NegCheckOracle(l) =>
        if LOr.view_get_oracle(ov, s1.cp, l) {
          FAdvanceEpsilonLookClkSetM1(c, s1.(active := ac), ov, dir);
        } else {
          FAdvanceEpsilonLookClkSetM1(c, s1.(active := [t.(pc := t.pc + 1)] + ac), ov, dir);
        }
      case WriteOracle(l) =>
        FAdvanceEpsilonLookClkSetM1(c, s1.(active := ac), LOr.view_set_oracle(ov, s1.cp, l), dir);
      case BeginLoop =>
        FAdvanceEpsilonLookClkSetM1(c, s1.(active := [t.(exit_allowed := false, pc := t.pc + 1)] + ac), ov, dir);
      case EndLoop =>
        if t.exit_allowed {
          FAdvanceEpsilonLookClkSetM1(c, s1.(active := [t.(pc := t.pc + 1)] + ac), ov, dir);
        } else {
          FAdvanceEpsilonLookClkSetM1(c, s1.(active := ac), ov, dir);
        }
      case CheckNullable(qid) =>
        if LCdn.cdn_get(s1.cdn, qid) {
          FAdvanceEpsilonLookClkSetM1(c, s1.(active := [t.(pc := t.pc + 1)] + ac), ov, dir);
        } else {
          FAdvanceEpsilonLookClkSetM1(c, s1.(active := ac), ov, dir);
        }
      case AnchorAssertion(a) =>
        if LAnc.is_satisfied(a, s1.context, dir) {
          FAdvanceEpsilonLookClkSetM1(c, s1.(active := [t.(pc := t.pc + 1)] + ac), ov, dir);
        } else {
          FAdvanceEpsilonLookClkSetM1(c, s1.(active := ac), ov, dir);
        }
      case Fail =>
        FAdvanceEpsilonLookClkSetM1(c, s1.(active := ac), ov, dir);
    }
  }

  /** One null run keeps the bank invariant and the oracle view. */
  lemma FNullInterpBank(c: RB.code, inits: AI.VmState, ov: LOr.OracleView, dir: LAnc.direction,
                        lk0: AReg.Regs, DL: set<int>, qt0: AReg.Regs, QO: set<int>)
    requires |inits.processed.true_set| == RB.size(c) && |inits.processed.false_set| == RB.size(c)
    requires ShapeOk(c, DL, QO)
    requires inits.cp >= 0 && inits.clock >= -1
    requires |inits.active| == 1 && inits.blocked == [] && inits.bestmatch.None?
    requires BankOk(inits.active[0].look_regs, inits.active[0].quant_regs, ov, lk0, DL, qt0, QO)
    ensures AI.FNullInterp(c, inits, ov, dir).2 == ov
    ensures var r := AI.FNullInterp(c, inits, ov, dir).0;
            r.Some? ==> BankOk(r.value.look_regs, r.value.quant_regs, ov, lk0, DL, qt0, QO)
  {
    ShapeOkCM(c, DL, QO);
    var t := inits.active[0];
    assert forall x | x in inits.active :: x == t;
    assert CM.VmLookOracleTrue(inits, ov);
    assert CM.VmLookClkSet(inits);
    assert CM.VmLookCpSet(inits);
    assert CM.VmLooksAgree(inits, lk0, DL);
    assert CM.VmQuantsAgree(inits, qt0, QO);
    CM.FAdvanceEpsilonLookOracleTrue(c, inits, ov, dir);
    FAdvanceEpsilonLookClkSetM1(c, inits, ov, dir);
    CM.FAdvanceEpsilonLookCpSet(c, inits, ov, dir);
    CM.FAdvanceEpsilonLookFrame(c, inits, ov, dir, lk0, DL);
    CM.FAdvanceEpsilonQuantFrame(c, inits, ov, dir, qt0, QO);
    CM.FAdvanceEpsilonOvStable(c, inits, ov, dir);
  }

  // =========================================================================
  // 3. Through the reconstruction.
  // =========================================================================

  /** Every replay code the reconstruction of `reg` may run has the shape. */
  ghost predicate PlusShapes(reg: R.regex, plus: seq<RB.code>, DL: set<int>, QO: set<int>) {
    forall q: nat :: q in PIV.QuantIdsOutsideLooks(reg) ==> ShapeOk(AI.get_code_v(plus, q as int), DL, QO)
  }

  lemma FNulledPlusBank(reg: R.regex, cap: AReg.Regs, lk: AReg.Regs, qt: AReg.Regs,
                        plus: seq<RB.code>, str: string, ov: LOr.OracleView, dir: LAnc.direction,
                        lk0: AReg.Regs, DL: set<int>, qt0: AReg.Regs, QO: set<int>)
    requires PlusShapes(reg, plus, DL, QO)
    requires BankOk(lk, qt, ov, lk0, DL, qt0, QO)
    ensures var res := AI.FNulledPlus(reg, cap, lk, qt, plus, str, ov, dir);
            res.3 == ov && BankOk(res.1, res.2, ov, lk0, DL, qt0, QO)
    decreases reg, 1
  {
    match reg
    case Re_empty =>
    case Re_character(_) =>
    case Re_anchor(_) =>
    case Re_lookaround(_, _, _) =>
    case Re_capture(_, r1) =>
      assert PIV.QuantIdsOutsideLooks(r1) <= PIV.QuantIdsOutsideLooks(reg);
      FNulledPlusBank(r1, cap, lk, qt, plus, str, ov, dir, lk0, DL, qt0, QO);
    case Re_alt(r1, r2) =>
      assert PIV.QuantIdsOutsideLooks(r1) <= PIV.QuantIdsOutsideLooks(reg) && PIV.QuantIdsOutsideLooks(r2) <= PIV.QuantIdsOutsideLooks(reg);
      var (c1, l1, q1, ov1) := AI.FNulledPlus(r1, cap, lk, qt, plus, str, ov, dir);
      FNulledPlusBank(r1, cap, lk, qt, plus, str, ov, dir, lk0, DL, qt0, QO);
      FNulledPlusBank(r2, c1, l1, q1, plus, str, ov1, dir, lk0, DL, qt0, QO);
    case Re_con(r1, r2) =>
      assert PIV.QuantIdsOutsideLooks(r1) <= PIV.QuantIdsOutsideLooks(reg) && PIV.QuantIdsOutsideLooks(r2) <= PIV.QuantIdsOutsideLooks(reg);
      var (c1, l1, q1, ov1) := AI.FNulledPlus(r1, cap, lk, qt, plus, str, ov, dir);
      FNulledPlusBank(r1, cap, lk, qt, plus, str, ov, dir, lk0, DL, qt0, QO);
      FNulledPlusBank(r2, c1, l1, q1, plus, str, ov1, dir, lk0, DL, qt0, QO);
    case Re_quant(nul, qid, quanttype, body) =>
      assert PIV.QuantIdsOutsideLooks(body) <= PIV.QuantIdsOutsideLooks(reg);
      match AReg.get_cp(qt, qid) {
        case None =>
          FNulledPlusBank(body, cap, lk, qt, plus, str, ov, dir, lk0, DL, qt0, QO);
        case Some(start_cp) =>
          var start_clock := AI.opt_int(AReg.get_clock(qt, qid));
          var bytecode := AI.get_code_v(plus, qid);
          var ctx := AI.cp_context(start_cp, str, dir);
          var inits0 := AI.FInitState(bytecode, start_cp, cap, lk, qt, start_clock, ctx);
          var subcdn := LCdn.compile_cdns(body);
          var subtable := LCdn.build_cdn_v(subcdn, start_cp, ov, ctx, dir);
          var inits := inits0.(cdn := subtable);
          assert qid >= 0 && (qid as nat) in PIV.QuantIdsOutsideLooks(reg);
          assert start_cp >= 0 && start_clock >= -1;
          FNullInterpBank(bytecode, inits, ov, dir, lk0, DL, qt0, QO);
          var (result, _, ov1) := AI.FNullInterp(bytecode, inits, ov, dir);
          var (ncap, nlk, nqt) := match result
                                  case None => (cap, lk, qt)
                                  case Some(w) => (w.capture_regs, w.look_regs, w.quant_regs);
          assert BankOk(nlk, nqt, ov, lk0, DL, qt0, QO);
          FNulledChildrenBank(body, subtable, start_cp, ncap, nlk, nqt, plus, str, ov1, dir, lk0, DL, qt0, QO);
      }
  }

  lemma FNulledChildrenBank(reg: R.regex, cdnt: LCdn.cdn_table, cp: int, cap: AReg.Regs, lk: AReg.Regs, qt: AReg.Regs,
                            plus: seq<RB.code>, str: string, ov: LOr.OracleView, dir: LAnc.direction,
                            lk0: AReg.Regs, DL: set<int>, qt0: AReg.Regs, QO: set<int>)
    requires PlusShapes(reg, plus, DL, QO)
    requires BankOk(lk, qt, ov, lk0, DL, qt0, QO)
    ensures var res := AI.FNulledChildren(reg, cdnt, cp, cap, lk, qt, plus, str, ov, dir);
            res.3 == ov && BankOk(res.1, res.2, ov, lk0, DL, qt0, QO)
    decreases reg, 0
  {
    match reg
    case Re_empty =>
    case Re_character(_) =>
    case Re_anchor(_) =>
    case Re_lookaround(_, _, _) =>
    case Re_capture(_, r1) =>
      assert PIV.QuantIdsOutsideLooks(r1) <= PIV.QuantIdsOutsideLooks(reg);
      FNulledChildrenBank(r1, cdnt, cp, cap, lk, qt, plus, str, ov, dir, lk0, DL, qt0, QO);
    case Re_alt(r1, r2) =>
      assert PIV.QuantIdsOutsideLooks(r1) <= PIV.QuantIdsOutsideLooks(reg) && PIV.QuantIdsOutsideLooks(r2) <= PIV.QuantIdsOutsideLooks(reg);
      var (c1, l1, q1, ov1) := AI.FNulledChildren(r1, cdnt, cp, cap, lk, qt, plus, str, ov, dir);
      FNulledChildrenBank(r1, cdnt, cp, cap, lk, qt, plus, str, ov, dir, lk0, DL, qt0, QO);
      FNulledChildrenBank(r2, cdnt, cp, c1, l1, q1, plus, str, ov1, dir, lk0, DL, qt0, QO);
    case Re_con(r1, r2) =>
      assert PIV.QuantIdsOutsideLooks(r1) <= PIV.QuantIdsOutsideLooks(reg) && PIV.QuantIdsOutsideLooks(r2) <= PIV.QuantIdsOutsideLooks(reg);
      var (c1, l1, q1, ov1) := AI.FNulledChildren(r1, cdnt, cp, cap, lk, qt, plus, str, ov, dir);
      FNulledChildrenBank(r1, cdnt, cp, cap, lk, qt, plus, str, ov, dir, lk0, DL, qt0, QO);
      FNulledChildrenBank(r2, cdnt, cp, c1, l1, q1, plus, str, ov1, dir, lk0, DL, qt0, QO);
    case Re_quant(nul, qid, quanttype, body) =>
      assert PIV.QuantIdsOutsideLooks(body) <= PIV.QuantIdsOutsideLooks(reg);
      match AReg.get_cp(qt, qid) {
        case None =>
          FNulledChildrenBank(body, cdnt, cp, cap, lk, qt, plus, str, ov, dir, lk0, DL, qt0, QO);
        case Some(start_cp) =>
          if start_cp == cp {
            var start_clock := AI.opt_int(AReg.get_clock(qt, qid));
            var bytecode := AI.get_code_v(plus, qid);
            var ctx := AI.cp_context(cp, str, dir);
            var inits0 := AI.FInitState(bytecode, cp, cap, lk, qt, start_clock, ctx);
            var inits := inits0.(cdn := cdnt);
            assert qid >= 0 && (qid as nat) in PIV.QuantIdsOutsideLooks(reg);
            assert start_cp >= 0 && start_clock >= -1;
            FNullInterpBank(bytecode, inits, ov, dir, lk0, DL, qt0, QO);
            var (result, _, ov1) := AI.FNullInterp(bytecode, inits, ov, dir);
            var (ncap, nlk, nqt) := match result
                                    case None => (cap, lk, qt)
                                    case Some(w) => (w.capture_regs, w.look_regs, w.quant_regs);
            assert BankOk(nlk, nqt, ov, lk0, DL, qt0, QO);
            FNulledChildrenBank(body, cdnt, cp, ncap, nlk, nqt, plus, str, ov1, dir, lk0, DL, qt0, QO);
          }
      }
  }

  /** The top regex's plus table: every replay code the reconstruction of `ast` runs has the shape, at the
      direct lids and the outside-look qids of `re = lazy_prefix(ast)`. */
  lemma PlusShapesTop(ast: R.regex, plus: seq<RB.code>)
    requires LTB.LookUnique(R.lazy_prefix(ast)) && PIV.QuantUnique(R.lazy_prefix(ast))
    requires NRR.PlusTableOkS(R.lazy_prefix(ast), plus)
    ensures PlusShapes(ast, plus, M.DirectLidSet(R.lazy_prefix(ast)), M.QIdsOuter(R.lazy_prefix(ast)))
  {
    var re := R.lazy_prefix(ast);
    var pre := R.Re_quant(R.NonNullable, 0, R.CountedQuant(0, None, false), R.Re_character(R.Dot));
    assert re == R.Re_con(pre, ast);
    var DL := M.DirectLidSet(re);
    var QO := M.QIdsOuter(re);
    forall q: nat | q in PIV.QuantIdsOutsideLooks(ast) ensures ShapeOk(AI.get_code_v(plus, q as int), DL, QO) {
      assert q in PIV.QuantIdsOutsideLooks(re);
      QidBodyOuter(re, q);
      if NRR.QidStampPlus(re, q) {
        var b := PIV.QidBody(re, q);
        assert AI.get_code_v(plus, q as int) == CP.compile_reconstruct_nulled(b);
        forall l: nat | l in M.DirectLookIds(b) ensures (l as int) in DL {
          assert l in M.DirectLookIds(re);
        }
        forall q2: nat | q2 in PIV.QuantIdsOutsideLooks(b) ensures (q2 as int) in QO {
          assert q2 in PIV.QuantIdsOutsideLooks(re);
        }
        ReconCodeShape(b, DL, QO);
      } else {
        assert AI.get_code_v(plus, q as int) == [];
      }
    }
  }

  /** THE BANK AT THE RECONSTRUCTED WINNER. */
  lemma ReconBank(ast: R.regex, str: string, th: AI.Thread, ov: LOr.OracleView, nlook: int, nquant: int)
    requires LTB.LookUnique(R.lazy_prefix(ast)) && PIV.QuantUnique(R.lazy_prefix(ast))
    requires NRR.PlusTableOkS(R.lazy_prefix(ast), CP.FFullCompilation(ast).f_plus_bc)
    requires BankOk(th.look_regs, th.quant_regs, ov, AReg.init_regs(nlook), M.DirectLidSet(R.lazy_prefix(ast)),
                    AReg.init_regs(nquant), M.QIdsOuter(R.lazy_prefix(ast)))
    ensures var rp := AI.FReconstructPlus(th, ast, CP.FFullCompilation(ast).f_plus_bc, str, ov, LAnc.Forward);
            rp.1 == ov
            && BankOk(rp.0.look_regs, rp.0.quant_regs, ov, AReg.init_regs(nlook), M.DirectLidSet(R.lazy_prefix(ast)),
                      AReg.init_regs(nquant), M.QIdsOuter(R.lazy_prefix(ast)))
  {
    var plus := CP.FFullCompilation(ast).f_plus_bc;
    PlusShapesTop(ast, plus);
    FNulledPlusBank(ast, th.capture_regs, th.look_regs, th.quant_regs, plus, str, ov, LAnc.Forward,
                    AReg.init_regs(nlook), M.DirectLidSet(R.lazy_prefix(ast)),
                    AReg.init_regs(nquant), M.QIdsOuter(R.lazy_prefix(ast)));
  }

  /** `LookCpsLE` from the oracle half: `view_get_oracle` is false out of range. */
  lemma OracleTrueCpsLE(lk: AReg.Regs, ov: LOr.OracleView, n: int)
    requires CM.LookCpsOracleTrue(lk, ov) && |ov| == n + 1
    ensures CM.LookCpsLE(lk, n)
  {
    forall l: int ensures AI.get_idx(lk.a_cp, l) <= n {
      if AI.get_idx(lk.a_cp, l) >= 0 {
        assert LOr.view_get_oracle(ov, AI.get_idx(lk.a_cp, l), l);
      }
    }
  }
}
