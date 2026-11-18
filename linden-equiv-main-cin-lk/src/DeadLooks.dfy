// G4b-2 (transport plan §3) — THE DEAD-STAMP FIX.
//
// At the top regex the reconstructed winner `rp = FReconstructPlus(best)` replays DEAD stamps too: it writes
// look records at top lids that are not present (`NI.LookPathPresent`). The converse carrier's dominance
// premise (`NI.LookPathDom`) would hold there, while the engine (rightly) filters the lid's groups. The fix
// is a synthetic winner whose look CLOCK at those lids is lowered to `0` (the position is kept):
//   §1  `QClkPosT`: a set quant position carries a clock `>= 1` (every write stamps `s.clock + 1`, and a run
//       starts at clock `>= 0`), through `AI.FFindMatch` in either direction.
//   §2  `LowerDeadLookClks` and its facts.
//   §3  `LowerDeadNotDom`: a lowered lid sits under a stamped host whose clock is `>= 1 > 0`, so its
//       dominance fails (`NI.LookPathDomOnPathBreaksCdn`).
//   §4  `M.WinRegsOk` / `MC.WinRegsOkG` survive the lowering (they read look positions; clocks only through
//       `CM.LookClkSetWithCp` / `CM.LookCpSetWithClk`).
//   §5  The engine never reads a look clock before `filter_reset` (a copy of `QCI` for the relation "same
//       threads up to look clocks on `D`"), and `filter_capture` never reads the clock of a non-present top
//       lid (it sits under a `filter_all`): the answer is unchanged.
module LindenElkDeadLooks {
  import opened Std.Wrappers
  import R = RegElkRegex
  import RB = Bytecode
  import CP = Compiler
  import AI = ArrayInterp
  import AReg = Array_Regs
  import LOr = Oracle
  import LAnc = Anchors
  import LCdn = Cdn
  import RC = Charclasses
  import NR = LindenElkNfaRep
  import T = LindenElkTranslate
  import PIV = LindenElkPikeInv
  import CM = LindenElkClockMono
  import M = LindenElkMain
  import LTB = LindenElkLookTables
  import NI = LindenElkNestInv
  import ELk = LindenElkEmptyLooks
  import LR = LindenElkLookRecord
  import LB = LindenElkLookBank
  import MC = LindenElkMainCinLk

  // ===========================================================================
  // 1. A set quant position carries a clock >= 1
  // ===========================================================================

  /** Every quant register is unset (position and clock) or carries a clock `>= 1`; so a set position
      implies a clock `>= 1`. */
  ghost predicate QClkPosR(q: AReg.Regs) {
    forall k: int {:trigger AI.get_idx(q.a_clk, k)} ::
      (AI.get_idx(q.a_clk, k) == -1 && AI.get_idx(q.a_cp, k) < 0) || AI.get_idx(q.a_clk, k) >= 1
  }

  ghost predicate QClkPosT(t: AI.Thread) { QClkPosR(t.quant_regs) }

  ghost predicate VmQClkPos(s: AI.VmState) {
    (forall t | t in s.active :: QClkPosT(t))
    && (forall tb | tb in s.blocked :: QClkPosT(tb.0))
    && (s.bestmatch.Some? ==> QClkPosT(s.bestmatch.value))
  }

  /** What the consumers read. */
  lemma QClkPosSet(t: AI.Thread, k: int)
    requires QClkPosT(t) && AI.get_idx(t.quant_regs.a_cp, k) >= 0
    ensures AI.get_idx(t.quant_regs.a_clk, k) >= 1
  {
    assert (AI.get_idx(t.quant_regs.a_clk, k) == -1 && AI.get_idx(t.quant_regs.a_cp, k) < 0) || AI.get_idx(t.quant_regs.a_clk, k) >= 1;
  }

  /** Fresh registers. */
  lemma QClkPosInit(cap: AReg.Regs, look: AReg.Regs, nquant: int)
    ensures QClkPosT(AI.init_thread(cap, look, AReg.init_regs(nquant)))
  {
    var q := AReg.init_regs(nquant);
    forall k: int ensures AI.get_idx(q.a_clk, k) == -1 && AI.get_idx(q.a_cp, k) < 0 {
      if 0 <= k < |q.a_cp| { assert q.a_cp[k] == -1; }
      if 0 <= k < |q.a_clk| { assert q.a_clk[k] == -1; }
    }
  }

  lemma QClkPosInitState(c: RB.code, cp: int, cap: AReg.Regs, look: AReg.Regs, nquant: int, clk: int, ctx: LAnc.char_context)
    ensures VmQClkPos(AI.FInitState(c, cp, cap, look, AReg.init_regs(nquant), clk, ctx))
  {
    var s := AI.FInitState(c, cp, cap, look, AReg.init_regs(nquant), clk, ctx);
    QClkPosInit(cap, look, nquant);
    forall t0 | t0 in s.active ensures QClkPosT(t0) { assert t0 == AI.init_thread(cap, look, AReg.init_regs(nquant)); }
  }

  /** The quant write stamps a clock `>= 1`. */
  lemma QClkPosWrite(q: AReg.Regs, k: int, ocp: Option<int>, clk: int)
    requires QClkPosR(q) && clk >= 1
    ensures QClkPosR(AReg.set_reg(q, k, ocp, clk))
  {
    var q2 := AReg.set_reg(q, k, ocp, clk);
    forall j: int
      ensures (AI.get_idx(q2.a_clk, j) == -1 && AI.get_idx(q2.a_cp, j) < 0) || AI.get_idx(q2.a_clk, j) >= 1
    {
      assert (AI.get_idx(q.a_clk, j) == -1 && AI.get_idx(q.a_cp, j) < 0) || AI.get_idx(q.a_clk, j) >= 1;
      if j != k {
        CM.SetRegOtherIdx(q, k, ocp, clk, j);
      } else if 0 <= k < |q.a_cp| && 0 <= k < |q.a_clk| {
        assert q2.a_clk == q.a_clk[k := clk];
      } else {
        assert q2 == q;
      }
    }
  }

  /** An epsilon phase keeps the invariant. */
  lemma FAdvanceEpsilonQClkPos(c: RB.code, s: AI.VmState, ov: LOr.OracleView, dir: LAnc.direction)
    requires |s.processed.true_set| == RB.size(c) && |s.processed.false_set| == RB.size(c)
    requires s.clock >= 0
    requires VmQClkPos(s)
    ensures VmQClkPos(AI.FAdvanceEpsilon(c, s, ov, dir).0)
    decreases AI.unprocessed(s.processed), |s.active|
  {
    if |s.active| == 0 { return; }
    var t := s.active[0];
    var ac := s.active[1..];
    assert t in s.active;
    assert forall x | x in ac :: x in s.active;
    if AI.bpc_mem(s.processed, t.pc, t.exit_allowed) {
      FAdvanceEpsilonQClkPos(c, s.(active := ac), ov, dir);
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
        assert VmQClkPos(s2) by {
          forall tb | tb in nb ensures QClkPosT(tb.0) {
            assert tb == (t, ce) || tb in s1.blocked;
          }
        }
        FAdvanceEpsilonQClkPos(c, s2, ov, dir);
      case Accept =>
      case Jmp(x) =>
        FAdvanceEpsilonQClkPos(c, s1.(active := [t.(pc := x)] + ac), ov, dir);
      case Fork(x, y) =>
        var newt := AI.Thread(x, t.capture_regs, t.look_regs, t.quant_regs, t.exit_allowed);
        FAdvanceEpsilonQClkPos(c, s1.(active := [newt, t.(pc := y)] + ac), ov, dir);
      case SetRegisterToCP(reg) =>
        var t2 := t.(capture_regs := AReg.set_reg(t.capture_regs, reg, Some(s1.cp), s1.clock), pc := t.pc + 1);
        FAdvanceEpsilonQClkPos(c, s1.(active := [t2] + ac), ov, dir);
      case SetQuantToClock(q, bq) =>
        var ocp := if bq then Some(s1.cp) else None;
        var t2 := t.(quant_regs := AReg.set_reg(t.quant_regs, q, ocp, s1.clock), pc := t.pc + 1);
        QClkPosWrite(t.quant_regs, q, ocp, s1.clock);
        assert QClkPosT(t2);
        FAdvanceEpsilonQClkPos(c, s1.(active := [t2] + ac), ov, dir);
      case CheckOracle(l) =>
        if LOr.view_get_oracle(ov, s1.cp, l) {
          var t2 := t.(pc := t.pc + 1, look_regs := AReg.set_reg(t.look_regs, l, Some(s1.cp), s1.clock));
          FAdvanceEpsilonQClkPos(c, s1.(active := [t2] + ac), ov, dir);
        } else {
          FAdvanceEpsilonQClkPos(c, s1.(active := ac), ov, dir);
        }
      case NegCheckOracle(l) =>
        if LOr.view_get_oracle(ov, s1.cp, l) {
          FAdvanceEpsilonQClkPos(c, s1.(active := ac), ov, dir);
        } else {
          FAdvanceEpsilonQClkPos(c, s1.(active := [t.(pc := t.pc + 1)] + ac), ov, dir);
        }
      case WriteOracle(l) =>
        FAdvanceEpsilonQClkPos(c, s1.(active := ac), LOr.view_set_oracle(ov, s1.cp, l), dir);
      case BeginLoop =>
        FAdvanceEpsilonQClkPos(c, s1.(active := [t.(exit_allowed := false, pc := t.pc + 1)] + ac), ov, dir);
      case EndLoop =>
        if t.exit_allowed {
          FAdvanceEpsilonQClkPos(c, s1.(active := [t.(pc := t.pc + 1)] + ac), ov, dir);
        } else {
          FAdvanceEpsilonQClkPos(c, s1.(active := ac), ov, dir);
        }
      case CheckNullable(qid) =>
        if LCdn.cdn_get(s1.cdn, qid) {
          FAdvanceEpsilonQClkPos(c, s1.(active := [t.(pc := t.pc + 1)] + ac), ov, dir);
        } else {
          FAdvanceEpsilonQClkPos(c, s1.(active := ac), ov, dir);
        }
      case AnchorAssertion(a) =>
        if LAnc.is_satisfied(a, s1.context, dir) {
          FAdvanceEpsilonQClkPos(c, s1.(active := [t.(pc := t.pc + 1)] + ac), ov, dir);
        } else {
          FAdvanceEpsilonQClkPos(c, s1.(active := ac), ov, dir);
        }
      case Fail =>
        FAdvanceEpsilonQClkPos(c, s1.(active := ac), ov, dir);
    }
  }

  /** The consume phase moves blocked threads to active, registers untouched. */
  lemma FConsumeQClkPos(s: AI.VmState)
    requires VmQClkPos(s)
    ensures VmQClkPos(AI.FConsume(s))
    decreases |s.blocked|
  {
    if |s.blocked| == 0 { return; }
    var t := s.blocked[0].0;
    var ce := s.blocked[0].1;
    var s1 := s.(blocked := s.blocked[1..]);
    assert VmQClkPos(s1) by {
      forall tb | tb in s1.blocked ensures QClkPosT(tb.0) { assert tb in s.blocked; }
    }
    var s2 := if RC.is_accepted(s1.context.nextchar, ce)
              then s1.(active := [t.(exit_allowed := true, pc := t.pc + 1)] + s1.active)
              else s1;
    assert VmQClkPos(s2) by {
      assert s.blocked[0] in s.blocked;
      assert QClkPosT(t);
      forall t2 | t2 in s2.active ensures QClkPosT(t2) {
        if t2 != t.(exit_allowed := true, pc := t.pc + 1) { assert t2 in s1.active; }
      }
    }
    FConsumeQClkPos(s2);
  }

  /** THE VM INVARIANT: the winner of a search (either direction) started at a clock `>= 0`. */
  lemma FFindMatchQClkPos(c: RB.code, str: string, s: AI.VmState, ov: LOr.OracleView,
                          dir: LAnc.direction, cdn: LCdn.cdns)
    requires |s.processed.true_set| == RB.size(c) && |s.processed.false_set| == RB.size(c)
    requires dir.Forward? ==> s.context.nextchar == AI.get_char(str, s.cp)
    requires dir.Backward? ==> s.context.nextchar == AI.get_char(str, s.cp - 1)
    requires s.clock >= 0
    requires VmQClkPos(s)
    ensures var r := AI.FFindMatch(c, str, s, ov, dir, cdn).0;
      r.Some? ==> QClkPosT(r.value)
    decreases if dir.Forward? then |str| - s.cp else s.cp
  {
    var s0 := s.(cdn := LCdn.build_cdn_v(cdn, s.cp, ov, s.context, dir));
    assert VmQClkPos(s0);
    var (s1, ov1) := AI.FAdvanceEpsilon(c, s0, ov, dir);
    FAdvanceEpsilonQClkPos(c, s0, ov, dir);
    CM.FAdvanceEpsilonClockGrows(c, s0, ov, dir);
    assert VmQClkPos(s1);
    if |s1.blocked| == 0 { return; }
    match s1.context.nextchar {
      case None =>
      case Some(_) =>
        var s2 := AI.FConsume(s1);
        FConsumeQClkPos(s1);
        CM.FConsumeClockSame(s1);
        var s3 := s2.(processed := AI.init_bpcset(RB.size(c)), isblocked := AI.init_pcset(RB.size(c)),
                      cdn := LCdn.init_cdn(), cp := AI.incr_cp(s2.cp, dir));
        var newchar := AI.get_char(str, s3.cp - AI.cp_offset(dir));
        var s4 := s3.(context := LAnc.update_context(s3.context, newchar));
        assert VmQClkPos(s4);
        FFindMatchQClkPos(c, str, s4, ov1, dir, cdn);
    }
  }

  /** The run from a fresh quant bank at clock `0` (the main search, a look row's search). */
  lemma FFindMatchQClkPosInit(c: RB.code, str: string, ov: LOr.OracleView, dir: LAnc.direction, cdn: LCdn.cdns,
                              cp: int, cap: AReg.Regs, look: AReg.Regs, nquant: int)
    ensures var r := AI.FFindMatch(c, str, AI.FInitState(c, cp, cap, look, AReg.init_regs(nquant), 0, AI.cp_context(cp, str, dir)),
                                   ov, dir, cdn).0;
      r.Some? ==> QClkPosT(r.value)
  {
    var ctx := AI.cp_context(cp, str, dir);
    QClkPosInitState(c, cp, cap, look, nquant, 0, ctx);
    FFindMatchQClkPos(c, str, AI.FInitState(c, cp, cap, look, AReg.init_regs(nquant), 0, ctx), ov, dir, cdn);
  }

  // ===========================================================================
  // 2. The lowering
  // ===========================================================================

  /** A DEAD-WRITTEN top lid of thread `th`: a top lid the reconstruction may have re-set (`ELk.LooksQE`),
      recorded, and not present. */
  ghost predicate DeadLid(re: R.regex, Q: set<int>, th: AI.Thread, l: int) {
    l >= 0 && (l as nat) in NI.TopLookIds(re) && (l as nat) in LTB.LookIds(re) && l in ELk.LooksQE(re, Q)
    && AI.get_idx(th.look_regs.a_cp, l) >= 0
    && !NI.LookPathPresent(re, th.capture_regs.a_clk, th.quant_regs.a_clk, -1, l as nat)
  }

  /** The look CLOCK of every dead-written top lid lowered to `0`; everything else untouched. */
  ghost function LowerDeadLookClks(re: R.regex, Q: set<int>, th: AI.Thread): AI.Thread {
    var lk := th.look_regs;
    th.(look_regs := AReg.ARegs(lk.a_cp, seq(|lk.a_clk|, i requires 0 <= i < |lk.a_clk| => if DeadLid(re, Q, th, i) then 0 else lk.a_clk[i])))
  }

  lemma LowerDeadLookClksFacts(re: R.regex, Q: set<int>, th: AI.Thread)
    ensures var th1 := LowerDeadLookClks(re, Q, th);
            th1.pc == th.pc && th1.capture_regs == th.capture_regs && th1.quant_regs == th.quant_regs
            && th1.exit_allowed == th.exit_allowed
            && th1.look_regs.a_cp == th.look_regs.a_cp
            && |th1.look_regs.a_clk| == |th.look_regs.a_clk|
            && (forall l: int {:trigger AI.get_idx(th1.look_regs.a_clk, l)} :: !DeadLid(re, Q, th, l) ==>
                  AI.get_idx(th1.look_regs.a_clk, l) == AI.get_idx(th.look_regs.a_clk, l))
            && (forall l: int {:trigger AI.get_idx(th1.look_regs.a_clk, l)} :: DeadLid(re, Q, th, l) ==>
                  AI.get_idx(th1.look_regs.a_clk, l) <= 0
                  && (l < |th.look_regs.a_clk| ==> AI.get_idx(th1.look_regs.a_clk, l) == 0))
            && (forall l: int {:trigger AReg.get_cp(th1.look_regs, l)} :: AReg.get_cp(th1.look_regs, l) == AReg.get_cp(th.look_regs, l))
  {}

  /** The lowering reads the look positions and the capture/quant clocks only: it commutes with clearing
      quant positions (`rp0 = ClearQuantCps(LowerDeadLookClks(rp))`). */
  lemma LowerClearCommute(re: R.regex, Q: set<int>, th: AI.Thread, D: set<int>)
    ensures MC.ClearQuantCps(LowerDeadLookClks(re, Q, th), D) == LowerDeadLookClks(re, Q, MC.ClearQuantCps(th, D))
  {
    var a := MC.ClearQuantCps(LowerDeadLookClks(re, Q, th), D);
    var thc := MC.ClearQuantCps(th, D);
    var b := LowerDeadLookClks(re, Q, thc);
    MC.ClearQuantCpsFacts(th, D);
    forall l: int ensures DeadLid(re, Q, thc, l) == DeadLid(re, Q, th, l) {}
    assert a.look_regs.a_clk == b.look_regs.a_clk by {
      forall i | 0 <= i < |th.look_regs.a_clk| ensures a.look_regs.a_clk[i] == b.look_regs.a_clk[i] {
        assert DeadLid(re, Q, thc, i) == DeadLid(re, Q, th, i);
      }
    }
    assert a.look_regs == b.look_regs;
    assert a.quant_regs == b.quant_regs;
  }

  // ===========================================================================
  // 3. A lowered lid is not dominant
  // ===========================================================================

  /** THE DOM-KILL. `Q` is the winner's stamp set, the winner's set stamps carry clocks `>= 1` (§1) and the
      replay only raised quant clocks (`ELk.QClkGe`): every non-present top lid of `ELk.LooksQE(re, Q)` has
      a stamped host with clock `>= 1`, above the lowered look clock. */
  lemma LowerDeadNotDom(re: R.regex, Q: set<int>, best: AI.Thread, th0: AI.Thread)
    requires NR.NestedFragmentCdnRE(re) && LTB.LookUnique(re) && PIV.QuantUnique(re)
    requires Q == ELk.StampSet(best.quant_regs.a_cp)
    requires QClkPosT(best)
    requires ELk.QClkGe(th0.quant_regs, best.quant_regs.a_clk)
    requires CM.LookCpSetWithClk(th0.look_regs)
    ensures forall l: nat {:trigger NI.LookPathDom(re, AI.get_idx(LowerDeadLookClks(re, Q, th0).look_regs.a_clk, l), th0.quant_regs.a_clk, l)} ::
              l in NI.TopLookIds(re) && l in LTB.LookIds(re) && (l as int) in ELk.LooksQE(re, Q)
              && !NI.LookPathPresent(re, th0.capture_regs.a_clk, th0.quant_regs.a_clk, -1, l)
              ==> !NI.LookPathDom(re, AI.get_idx(LowerDeadLookClks(re, Q, th0).look_regs.a_clk, l), th0.quant_regs.a_clk, l)
  {
    var th1 := LowerDeadLookClks(re, Q, th0);
    LowerDeadLookClksFacts(re, Q, th0);
    forall l: nat | l in NI.TopLookIds(re) && l in LTB.LookIds(re) && (l as int) in ELk.LooksQE(re, Q)
                    && !NI.LookPathPresent(re, th0.capture_regs.a_clk, th0.quant_regs.a_clk, -1, l)
      ensures !NI.LookPathDom(re, AI.get_idx(th1.look_regs.a_clk, l), th0.quant_regs.a_clk, l)
    {
      var L := AI.get_idx(th1.look_regs.a_clk, l);
      assert L <= 0 by {
        if !DeadLid(re, Q, th0, l) {
          assert AI.get_idx(th0.look_regs.a_cp, l) < 0;
          assert L == AI.get_idx(th0.look_regs.a_clk, l);
        }
      }
      var q := LR.LooksQEUnderStamp(re, Q, l);
      assert AI.get_idx(best.quant_regs.a_cp, q) >= 0;
      QClkPosSet(best, q);
      assert AI.get_idx(th0.quant_regs.a_clk, q) >= AI.get_idx(best.quant_regs.a_clk, q);
      NI.LookPathDomOnPathBreaksCdn(re, L, th0.quant_regs.a_clk, l, q);
    }
  }

  // ===========================================================================
  // 4. The endpoint's register facts survive the lowering
  // ===========================================================================

  /** The look-bank clauses the two `WinRegsOk`s read. */
  lemma LowerLookBank(re: R.regex, Q: set<int>, th: AI.Thread, nlook: int, ov: LOr.OracleView, ub: int, P: set<int>, DL: set<int>)
    requires |th.look_regs.a_cp| == nlook && |th.look_regs.a_clk| == nlook
    requires CM.LookCpsLE(th.look_regs, ub)
    requires CM.RegsAgreeOutside(th.look_regs, AReg.init_regs(nlook), DL)
    requires CM.LookClkSetWithCp(th.look_regs) && CM.LookCpSetWithClk(th.look_regs)
    requires CM.LookCpsOracleTrue(th.look_regs, ov)
    requires forall l: int {:trigger l in P} :: (AI.get_idx(th.look_regs.a_cp, l) >= 0 || AI.get_idx(th.look_regs.a_clk, l) >= 0) ==> l in P
    ensures var lk1 := LowerDeadLookClks(re, Q, th).look_regs;
            |lk1.a_cp| == nlook && |lk1.a_clk| == nlook
            && CM.LookCpsLE(lk1, ub)
            && CM.RegsAgreeOutside(lk1, AReg.init_regs(nlook), DL)
            && CM.LookClkSetWithCp(lk1) && CM.LookCpSetWithClk(lk1)
            && CM.LookCpsOracleTrue(lk1, ov)
            && (forall l: int {:trigger l in P} :: (AI.get_idx(lk1.a_cp, l) >= 0 || AI.get_idx(lk1.a_clk, l) >= 0) ==> l in P)
  {
    var lk := th.look_regs;
    var lk1 := LowerDeadLookClks(re, Q, th).look_regs;
    LowerDeadLookClksFacts(re, Q, th);
    var ini := AReg.init_regs(nlook);
    forall k: int | k !in DL
      ensures AI.get_idx(lk1.a_cp, k) == AI.get_idx(ini.a_cp, k) && AI.get_idx(lk1.a_clk, k) == AI.get_idx(ini.a_clk, k)
    {
      assert AI.get_idx(lk.a_cp, k) == AI.get_idx(ini.a_cp, k) && AI.get_idx(lk.a_clk, k) == AI.get_idx(ini.a_clk, k);
      if 0 <= k < |ini.a_cp| { assert ini.a_cp[k] == -1; }
      assert AI.get_idx(ini.a_cp, k) == -1;
      assert !DeadLid(re, Q, th, k);
    }
    forall l: int | AI.get_idx(lk1.a_cp, l) >= 0 ensures AI.get_idx(lk1.a_clk, l) >= 0 {
      if DeadLid(re, Q, th, l) { assert 0 <= l < |lk.a_clk|; }
    }
    forall l: int | AI.get_idx(lk1.a_clk, l) >= 0 ensures AI.get_idx(lk1.a_cp, l) >= 0 {
      if !DeadLid(re, Q, th, l) { assert AI.get_idx(lk.a_clk, l) >= 0; }
    }
    forall l: int | AI.get_idx(lk1.a_cp, l) >= 0 || AI.get_idx(lk1.a_clk, l) >= 0 ensures l in P {
      if !DeadLid(re, Q, th, l) { assert AI.get_idx(lk.a_clk, l) == AI.get_idx(lk1.a_clk, l); }
      assert AI.get_idx(lk.a_cp, l) >= 0 || AI.get_idx(lk.a_clk, l) >= 0;
    }
  }

  /** `M.WinRegsOk` reads look positions, and look clocks only through `LookClkSetWithCp`/`LookCpSetWithClk`. */
  lemma WinRegsOkLowerLookClk(ast: R.regex, re: R.regex, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
                              th: AI.Thread, Q: set<int>, ncap: int, nlook: int, nquant: int)
    requires M.WinRegsOk(ast, re, crv, str, ov, th, ncap, nlook, nquant)
    ensures M.WinRegsOk(ast, re, crv, str, ov, LowerDeadLookClks(re, Q, th), ncap, nlook, nquant)
  {
    reveal M.WinRegsOk();
    var th1 := LowerDeadLookClks(re, Q, th);
    LowerDeadLookClksFacts(re, Q, th);
    LowerLookBank(re, Q, th, nlook, ov, |str|, LB.PosLookIds(re), M.DirectLidSet(re));
    assert forall l: int :: AReg.get_cp(th1.look_regs, l) == AReg.get_cp(th.look_regs, l);
  }

  /** The gate-free twin. */
  lemma WinRegsOkGLowerLookClk(ast: R.regex, re: R.regex, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
                               th: AI.Thread, Q: set<int>, ncap: int, nlook: int, nquant: int)
    requires MC.WinRegsOkG(ast, re, crv, str, ov, th, ncap, nlook, nquant)
    ensures MC.WinRegsOkG(ast, re, crv, str, ov, LowerDeadLookClks(re, Q, th), ncap, nlook, nquant)
  {
    reveal MC.WinRegsOkG();
    var th1 := LowerDeadLookClks(re, Q, th);
    LowerDeadLookClksFacts(re, Q, th);
    LowerLookBank(re, Q, th, nlook, ov, |str|, LB.PosLookIds(re), M.DirectLidSet(re));
    assert forall l: int :: AReg.get_cp(th1.look_regs, l) == AReg.get_cp(th.look_regs, l);
  }

  /** At the synthetic winner `rp0 = ClearQuantCps(LowerDeadLookClks(rp))`. */
  lemma WinRegsOkRp0(ast: R.regex, re: R.regex, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
                     rp: AI.Thread, Q: set<int>, ncap: int, nlook: int, nquant: int)
    requires M.WinRegsOk(ast, re, crv, str, ov, MC.ClearQuantCps(rp, M.QIdsOuter(re)), ncap, nlook, nquant)
    ensures M.WinRegsOk(ast, re, crv, str, ov, MC.ClearQuantCps(LowerDeadLookClks(re, Q, rp), M.QIdsOuter(re)), ncap, nlook, nquant)
  {
    LowerClearCommute(re, Q, rp, M.QIdsOuter(re));
    WinRegsOkLowerLookClk(ast, re, crv, str, ov, MC.ClearQuantCps(rp, M.QIdsOuter(re)), Q, ncap, nlook, nquant);
  }

  // ===========================================================================
  // 5. The answer is unchanged
  // ===========================================================================

  // ---- 5.1 the relation: same threads up to look clocks on `D` ----

  ghost predicate LAgree(k1: AReg.Regs, k2: AReg.Regs, D: set<int>) {
    k1.a_cp == k2.a_cp && |k1.a_clk| == |k2.a_clk|
    && forall k :: 0 <= k < |k1.a_clk| && k !in D ==> k1.a_clk[k] == k2.a_clk[k]
  }

  ghost predicate TAgree(t1: AI.Thread, t2: AI.Thread, D: set<int>) {
    t1.pc == t2.pc && t1.capture_regs == t2.capture_regs && t1.quant_regs == t2.quant_regs
    && t1.exit_allowed == t2.exit_allowed && LAgree(t1.look_regs, t2.look_regs, D)
  }

  ghost predicate ListAgree(a: seq<AI.Thread>, b: seq<AI.Thread>, D: set<int>) {
    |a| == |b| && forall i :: 0 <= i < |a| ==> TAgree(a[i], b[i], D)
  }

  ghost predicate BListAgree(a: seq<(AI.Thread, RC.char_expectation)>, b: seq<(AI.Thread, RC.char_expectation)>, D: set<int>) {
    |a| == |b| && forall i :: 0 <= i < |a| ==> TAgree(a[i].0, b[i].0, D) && a[i].1 == b[i].1
  }

  ghost predicate OptAgree(a: Option<AI.Thread>, b: Option<AI.Thread>, D: set<int>) {
    (a.None? <==> b.None?) && (a.Some? ==> TAgree(a.value, b.value, D))
  }

  ghost predicate SAgree(s1: AI.VmState, s2: AI.VmState, D: set<int>) {
    ListAgree(s1.active, s2.active, D) && BListAgree(s1.blocked, s2.blocked, D)
    && OptAgree(s1.bestmatch, s2.bestmatch, D)
    && s1.cp == s2.cp && s1.clock == s2.clock && s1.processed == s2.processed
    && s1.isblocked == s2.isblocked && s1.cdn == s2.cdn && s1.context == s2.context
  }

  /** The SAME write keeps the banks agreeing. */
  lemma LAgreeSet(k1: AReg.Regs, k2: AReg.Regs, k: int, cp: Option<int>, clk: int, D: set<int>)
    requires LAgree(k1, k2, D)
    ensures LAgree(AReg.set_reg(k1, k, cp, clk), AReg.set_reg(k2, k, cp, clk), D)
  {}

  lemma LAgreeGetCp(k1: AReg.Regs, k2: AReg.Regs, k: int, D: set<int>)
    requires LAgree(k1, k2, D)
    ensures AReg.get_cp(k1, k) == AReg.get_cp(k2, k)
  {}

  // ---- 5.2 the VM (a copy of `QCI`'s, the look bank in the quant bank's role) ----

  lemma ListAgreeCons(t1: AI.Thread, t2: AI.Thread, a: seq<AI.Thread>, b: seq<AI.Thread>, D: set<int>)
    requires TAgree(t1, t2, D) && ListAgree(a, b, D)
    ensures ListAgree([t1] + a, [t2] + b, D)
  {
    forall i | 0 <= i < |[t1] + a| ensures TAgree(([t1] + a)[i], ([t2] + b)[i], D) {
      if i > 0 { assert ([t1] + a)[i] == a[i - 1] && ([t2] + b)[i] == b[i - 1]; }
    }
  }

  lemma ListAgreeTail(a: seq<AI.Thread>, b: seq<AI.Thread>, D: set<int>)
    requires |a| > 0 && ListAgree(a, b, D)
    ensures TAgree(a[0], b[0], D) && ListAgree(a[1..], b[1..], D)
  {
    forall i | 0 <= i < |a[1..]| ensures TAgree(a[1..][i], b[1..][i], D) {
      assert a[1..][i] == a[i + 1] && b[1..][i] == b[i + 1];
    }
  }

  // ===========================================================================
  // The VM
  // ===========================================================================

  lemma FAdvanceEpsilonAgree(c: RB.code, s1: AI.VmState, s2: AI.VmState, ov: LOr.OracleView,
                             dir: LAnc.direction, D: set<int>)
    requires |s1.processed.true_set| == RB.size(c) && |s1.processed.false_set| == RB.size(c)
    requires SAgree(s1, s2, D)
    ensures SAgree(AI.FAdvanceEpsilon(c, s1, ov, dir).0, AI.FAdvanceEpsilon(c, s2, ov, dir).0, D)
    ensures AI.FAdvanceEpsilon(c, s1, ov, dir).1 == AI.FAdvanceEpsilon(c, s2, ov, dir).1
    decreases AI.unprocessed(s1.processed), |s1.active|
  {
    if |s1.active| == 0 { return; }
    var t := s1.active[0];
    var u := s2.active[0];
    var ac := s1.active[1..];
    var bc := s2.active[1..];
    ListAgreeTail(s1.active, s2.active, D);
    assert TAgree(t, u, D) && ListAgree(ac, bc, D);
    if AI.bpc_mem(s1.processed, t.pc, t.exit_allowed) {
      FAdvanceEpsilonAgree(c, s1.(active := ac), s2.(active := bc), ov, dir, D);
      return;
    }
    var b0 := s1.processed;
    var x1 := s1.(clock := s1.clock + 1, processed := AI.bpc_add(b0, t.pc, t.exit_allowed));
    var x2 := s2.(clock := s2.clock + 1, processed := AI.bpc_add(b0, u.pc, u.exit_allowed));
    assert AI.unprocessed(x1.processed) <= AI.unprocessed(b0)
        && (0 <= t.pc < RB.size(c) ==> AI.unprocessed(x1.processed) < AI.unprocessed(b0))
      by { AI.UnprocessedAdd(b0, t.pc, t.exit_allowed); }
    match RB.get_instr(c, t.pc) {
      case Consume(ce) =>
        assert {:split_here} true;   // (G4b-2, pack) one batch per instruction arm
        var (nb1, ni1) := AI.add_thread(t, ce, x1.blocked, x1.isblocked);
        var (nb2, ni2) := AI.add_thread(u, ce, x2.blocked, x2.isblocked);
        assert ni1 == ni2;
        assert BListAgree(nb1, nb2, D) by {
          if !AI.pc_mem(x1.isblocked, t.pc) {
            forall i | 0 <= i < |nb1| ensures TAgree(nb1[i].0, nb2[i].0, D) && nb1[i].1 == nb2[i].1 {
              if i > 0 { assert nb1[i] == x1.blocked[i - 1] && nb2[i] == x2.blocked[i - 1]; }
            }
          }
        }
        FAdvanceEpsilonAgree(c, x1.(blocked := nb1, isblocked := ni1, active := ac),
                             x2.(blocked := nb2, isblocked := ni2, active := bc), ov, dir, D);
      case Accept =>
      case Jmp(x) =>
        assert {:split_here} true;   // (G4b-2, pack) one batch per instruction arm
        ListAgreeCons(t.(pc := x), u.(pc := x), ac, bc, D);
        FAdvanceEpsilonAgree(c, x1.(active := [t.(pc := x)] + ac), x2.(active := [u.(pc := x)] + bc), ov, dir, D);
      case Fork(x, y) =>
        assert {:split_here} true;   // (G4b-2, pack) one batch per instruction arm
        var n1 := AI.Thread(x, t.capture_regs, t.look_regs, t.quant_regs, t.exit_allowed);
        var n2 := AI.Thread(x, u.capture_regs, u.look_regs, u.quant_regs, u.exit_allowed);
        ListAgreeCons(t.(pc := y), u.(pc := y), ac, bc, D);
        ListAgreeCons(n1, n2, [t.(pc := y)] + ac, [u.(pc := y)] + bc, D);
        assert [n1, t.(pc := y)] + ac == [n1] + ([t.(pc := y)] + ac);
        assert [n2, u.(pc := y)] + bc == [n2] + ([u.(pc := y)] + bc);
        FAdvanceEpsilonAgree(c, x1.(active := [n1, t.(pc := y)] + ac), x2.(active := [n2, u.(pc := y)] + bc), ov, dir, D);
      case SetRegisterToCP(reg) =>
        assert {:split_here} true;   // (G4b-2, pack) one batch per instruction arm
        var t2 := t.(capture_regs := AReg.set_reg(t.capture_regs, reg, Some(x1.cp), x1.clock), pc := t.pc + 1);
        var u2 := u.(capture_regs := AReg.set_reg(u.capture_regs, reg, Some(x2.cp), x2.clock), pc := u.pc + 1);
        ListAgreeCons(t2, u2, ac, bc, D);
        FAdvanceEpsilonAgree(c, x1.(active := [t2] + ac), x2.(active := [u2] + bc), ov, dir, D);
      case SetQuantToClock(q, bq) =>
        assert {:split_here} true;   // (G4b-2, pack) one batch per instruction arm
        var ocp := if bq then Some(x1.cp) else None;
        var t2 := t.(quant_regs := AReg.set_reg(t.quant_regs, q, ocp, x1.clock), pc := t.pc + 1);
        var u2 := u.(quant_regs := AReg.set_reg(u.quant_regs, q, ocp, x2.clock), pc := u.pc + 1);
        ListAgreeCons(t2, u2, ac, bc, D);
        FAdvanceEpsilonAgree(c, x1.(active := [t2] + ac), x2.(active := [u2] + bc), ov, dir, D);
      case CheckOracle(l) =>
        assert {:split_here} true;   // (G4b-2, pack) one batch per instruction arm
        if LOr.view_get_oracle(ov, x1.cp, l) {
          var t2 := t.(pc := t.pc + 1, look_regs := AReg.set_reg(t.look_regs, l, Some(x1.cp), x1.clock));
          var u2 := u.(pc := u.pc + 1, look_regs := AReg.set_reg(u.look_regs, l, Some(x2.cp), x2.clock));
          LAgreeSet(t.look_regs, u.look_regs, l, Some(x1.cp), x1.clock, D);
          ListAgreeCons(t2, u2, ac, bc, D);
          FAdvanceEpsilonAgree(c, x1.(active := [t2] + ac), x2.(active := [u2] + bc), ov, dir, D);
        } else {
          FAdvanceEpsilonAgree(c, x1.(active := ac), x2.(active := bc), ov, dir, D);
        }
      case NegCheckOracle(l) =>
        assert {:split_here} true;   // (G4b-2, pack) one batch per instruction arm
        if LOr.view_get_oracle(ov, x1.cp, l) {
          FAdvanceEpsilonAgree(c, x1.(active := ac), x2.(active := bc), ov, dir, D);
        } else {
          ListAgreeCons(t.(pc := t.pc + 1), u.(pc := u.pc + 1), ac, bc, D);
          FAdvanceEpsilonAgree(c, x1.(active := [t.(pc := t.pc + 1)] + ac), x2.(active := [u.(pc := u.pc + 1)] + bc), ov, dir, D);
        }
      case WriteOracle(l) =>
        assert {:split_here} true;   // (G4b-2, pack) one batch per instruction arm
        FAdvanceEpsilonAgree(c, x1.(active := ac), x2.(active := bc), LOr.view_set_oracle(ov, x1.cp, l), dir, D);
      case BeginLoop =>
        assert {:split_here} true;   // (G4b-2, pack) one batch per instruction arm
        var t2 := t.(exit_allowed := false, pc := t.pc + 1);
        var u2 := u.(exit_allowed := false, pc := u.pc + 1);
        ListAgreeCons(t2, u2, ac, bc, D);
        FAdvanceEpsilonAgree(c, x1.(active := [t2] + ac), x2.(active := [u2] + bc), ov, dir, D);
      case EndLoop =>
        assert {:split_here} true;   // (G4b-2, pack) one batch per instruction arm
        if t.exit_allowed {
          ListAgreeCons(t.(pc := t.pc + 1), u.(pc := u.pc + 1), ac, bc, D);
          FAdvanceEpsilonAgree(c, x1.(active := [t.(pc := t.pc + 1)] + ac), x2.(active := [u.(pc := u.pc + 1)] + bc), ov, dir, D);
        } else {
          FAdvanceEpsilonAgree(c, x1.(active := ac), x2.(active := bc), ov, dir, D);
        }
      case CheckNullable(qid) =>
        assert {:split_here} true;   // (G4b-2, pack) one batch per instruction arm
        if LCdn.cdn_get(x1.cdn, qid) {
          ListAgreeCons(t.(pc := t.pc + 1), u.(pc := u.pc + 1), ac, bc, D);
          FAdvanceEpsilonAgree(c, x1.(active := [t.(pc := t.pc + 1)] + ac), x2.(active := [u.(pc := u.pc + 1)] + bc), ov, dir, D);
        } else {
          FAdvanceEpsilonAgree(c, x1.(active := ac), x2.(active := bc), ov, dir, D);
        }
      case AnchorAssertion(a) =>
        assert {:split_here} true;   // (G4b-2, pack) one batch per instruction arm
        if LAnc.is_satisfied(a, x1.context, dir) {
          ListAgreeCons(t.(pc := t.pc + 1), u.(pc := u.pc + 1), ac, bc, D);
          FAdvanceEpsilonAgree(c, x1.(active := [t.(pc := t.pc + 1)] + ac), x2.(active := [u.(pc := u.pc + 1)] + bc), ov, dir, D);
        } else {
          FAdvanceEpsilonAgree(c, x1.(active := ac), x2.(active := bc), ov, dir, D);
        }
      case Fail =>
        assert {:split_here} true;   // (G4b-2, pack) one batch per instruction arm
        FAdvanceEpsilonAgree(c, x1.(active := ac), x2.(active := bc), ov, dir, D);
    }
  }

  lemma FConsumeAgree(s1: AI.VmState, s2: AI.VmState, D: set<int>)
    requires SAgree(s1, s2, D)
    ensures SAgree(AI.FConsume(s1), AI.FConsume(s2), D)
    decreases |s1.blocked|
  {
    if |s1.blocked| == 0 { return; }
    var t := s1.blocked[0].0;
    var u := s2.blocked[0].0;
    var ce := s1.blocked[0].1;
    var y1 := s1.(blocked := s1.blocked[1..]);
    var y2 := s2.(blocked := s2.blocked[1..]);
    assert BListAgree(y1.blocked, y2.blocked, D) by {
      forall i | 0 <= i < |y1.blocked| ensures TAgree(y1.blocked[i].0, y2.blocked[i].0, D) && y1.blocked[i].1 == y2.blocked[i].1 {
        assert y1.blocked[i] == s1.blocked[i + 1] && y2.blocked[i] == s2.blocked[i + 1];
      }
    }
    assert TAgree(t, u, D) && s2.blocked[0].1 == ce;
    if RC.is_accepted(y1.context.nextchar, ce) {
      ListAgreeCons(t.(exit_allowed := true, pc := t.pc + 1), u.(exit_allowed := true, pc := u.pc + 1), y1.active, y2.active, D);
      FConsumeAgree(y1.(active := [t.(exit_allowed := true, pc := t.pc + 1)] + y1.active),
                    y2.(active := [u.(exit_allowed := true, pc := u.pc + 1)] + y2.active), D);
    } else {
      FConsumeAgree(y1, y2, D);
    }
  }

  lemma FFindMatchAgree(c: RB.code, str: string, s1: AI.VmState, s2: AI.VmState, ov: LOr.OracleView,
                        dir: LAnc.direction, cdn: LCdn.cdns, D: set<int>)
    requires |s1.processed.true_set| == RB.size(c) && |s1.processed.false_set| == RB.size(c)
    requires dir.Forward? ==> s1.context.nextchar == AI.get_char(str, s1.cp)
    requires dir.Backward? ==> s1.context.nextchar == AI.get_char(str, s1.cp - 1)
    requires SAgree(s1, s2, D)
    ensures OptAgree(AI.FFindMatch(c, str, s1, ov, dir, cdn).0, AI.FFindMatch(c, str, s2, ov, dir, cdn).0, D)
    ensures AI.FFindMatch(c, str, s1, ov, dir, cdn).1 == AI.FFindMatch(c, str, s2, ov, dir, cdn).1
    decreases if dir.Forward? then |str| - s1.cp else s1.cp
  {
    var z1 := s1.(cdn := LCdn.build_cdn_v(cdn, s1.cp, ov, s1.context, dir));
    var z2 := s2.(cdn := LCdn.build_cdn_v(cdn, s2.cp, ov, s2.context, dir));
    assert SAgree(z1, z2, D);
    FAdvanceEpsilonAgree(c, z1, z2, ov, dir, D);
    var (a1, ov1) := AI.FAdvanceEpsilon(c, z1, ov, dir);
    var (a2, ov2) := AI.FAdvanceEpsilon(c, z2, ov, dir);
    if |a1.blocked| == 0 { return; }
    match a1.context.nextchar {
      case None =>
      case Some(_) =>
        FConsumeAgree(a1, a2, D);
        var b1 := AI.FConsume(a1);
        var b2 := AI.FConsume(a2);
        var c1 := b1.(processed := AI.init_bpcset(RB.size(c)), isblocked := AI.init_pcset(RB.size(c)),
                      cdn := LCdn.init_cdn(), cp := AI.incr_cp(b1.cp, dir));
        var c2 := b2.(processed := AI.init_bpcset(RB.size(c)), isblocked := AI.init_pcset(RB.size(c)),
                      cdn := LCdn.init_cdn(), cp := AI.incr_cp(b2.cp, dir));
        var newchar := AI.get_char(str, c1.cp - AI.cp_offset(dir));
        var d1 := c1.(context := LAnc.update_context(c1.context, newchar));
        var d2 := c2.(context := LAnc.update_context(c2.context, newchar));
        assert SAgree(d1, d2, D);
        FFindMatchAgree(c, str, d1, d2, ov1, dir, cdn, D);
    }
  }


  lemma FInitStateAgree(c: RB.code, cp: int, cap: AReg.Regs, ka: AReg.Regs, kb: AReg.Regs, qt: AReg.Regs,
                        clk: int, ctx: LAnc.char_context, D: set<int>)
    requires LAgree(ka, kb, D)
    ensures SAgree(AI.FInitState(c, cp, cap, ka, qt, clk, ctx), AI.FInitState(c, cp, cap, kb, qt, clk, ctx), D)
  {
    var s1 := AI.FInitState(c, cp, cap, ka, qt, clk, ctx);
    var s2 := AI.FInitState(c, cp, cap, kb, qt, clk, ctx);
    assert TAgree(s1.active[0], s2.active[0], D);
  }

  // ---- 5.3 the reconstruction and the look loop: no look clock is ever read ----

  lemma FNulledPlusAgree(reg: R.regex, cap: AReg.Regs, ka: AReg.Regs, kb: AReg.Regs, qt: AReg.Regs,
                         plus_bcv: seq<RB.code>, str: string, ov: LOr.OracleView, dir: LAnc.direction, D: set<int>)
    requires LAgree(ka, kb, D)
    ensures var r1 := AI.FNulledPlus(reg, cap, ka, qt, plus_bcv, str, ov, dir);
            var r2 := AI.FNulledPlus(reg, cap, kb, qt, plus_bcv, str, ov, dir);
            r1.0 == r2.0 && LAgree(r1.1, r2.1, D) && r1.2 == r2.2 && r1.3 == r2.3
    decreases reg, 1
  {
    match reg
    case Re_empty =>
    case Re_character(_) =>
    case Re_anchor(_) =>
    case Re_lookaround(_, _, _) =>
    case Re_capture(_, r1) => FNulledPlusAgree(r1, cap, ka, kb, qt, plus_bcv, str, ov, dir, D);
    case Re_alt(r1, r2) =>
      FNulledPlusAgree(r1, cap, ka, kb, qt, plus_bcv, str, ov, dir, D);
      var (c1, l1, x1, o1) := AI.FNulledPlus(r1, cap, ka, qt, plus_bcv, str, ov, dir);
      var (c2, l2, x2, o2) := AI.FNulledPlus(r1, cap, kb, qt, plus_bcv, str, ov, dir);
      FNulledPlusAgree(r2, c1, l1, l2, x1, plus_bcv, str, o1, dir, D);
    case Re_con(r1, r2) =>
      FNulledPlusAgree(r1, cap, ka, kb, qt, plus_bcv, str, ov, dir, D);
      var (c1, l1, x1, o1) := AI.FNulledPlus(r1, cap, ka, qt, plus_bcv, str, ov, dir);
      var (c2, l2, x2, o2) := AI.FNulledPlus(r1, cap, kb, qt, plus_bcv, str, ov, dir);
      FNulledPlusAgree(r2, c1, l1, l2, x1, plus_bcv, str, o1, dir, D);
    case Re_quant(nul, qid, quanttype, body) =>
      match AReg.get_cp(qt, qid) {
        case None => FNulledPlusAgree(body, cap, ka, kb, qt, plus_bcv, str, ov, dir, D);
        case Some(start_cp) =>
          var start_clock := AI.opt_int(AReg.get_clock(qt, qid));
          var bytecode := AI.get_code_v(plus_bcv, qid);
          var ctx := AI.cp_context(start_cp, str, dir);
          var subcdn := LCdn.compile_cdns(body);
          var subtable := LCdn.build_cdn_v(subcdn, start_cp, ov, ctx, dir);
          var i1 := AI.FInitState(bytecode, start_cp, cap, ka, qt, start_clock, ctx).(cdn := subtable);
          var i2 := AI.FInitState(bytecode, start_cp, cap, kb, qt, start_clock, ctx).(cdn := subtable);
          FInitStateAgree(bytecode, start_cp, cap, ka, kb, qt, start_clock, ctx, D);
          assert SAgree(i1, i2, D);
          FAdvanceEpsilonAgree(bytecode, i1, i2, ov, dir, D);
          var (res1, _, ova) := AI.FNullInterp(bytecode, i1, ov, dir);
          var (res2, _, ovb) := AI.FNullInterp(bytecode, i2, ov, dir);
          assert OptAgree(res1, res2, D) && ova == ovb;
          var (nc1, nl1, nq1) := match res1 case None => (cap, ka, qt) case Some(w) => (w.capture_regs, w.look_regs, w.quant_regs);
          var (nc2, nl2, nq2) := match res2 case None => (cap, kb, qt) case Some(w) => (w.capture_regs, w.look_regs, w.quant_regs);
          assert nc1 == nc2 && LAgree(nl1, nl2, D) && nq1 == nq2;
          FNulledChildrenAgree(body, subtable, start_cp, nc1, nl1, nl2, nq1, plus_bcv, str, ova, dir, D);
      }
  }

  lemma FNulledChildrenAgree(reg: R.regex, cdnt: LCdn.cdn_table, cp: int, cap: AReg.Regs, ka: AReg.Regs, kb: AReg.Regs,
                             qt: AReg.Regs, plus_bcv: seq<RB.code>, str: string,
                             ov: LOr.OracleView, dir: LAnc.direction, D: set<int>)
    requires LAgree(ka, kb, D)
    ensures var r1 := AI.FNulledChildren(reg, cdnt, cp, cap, ka, qt, plus_bcv, str, ov, dir);
            var r2 := AI.FNulledChildren(reg, cdnt, cp, cap, kb, qt, plus_bcv, str, ov, dir);
            r1.0 == r2.0 && LAgree(r1.1, r2.1, D) && r1.2 == r2.2 && r1.3 == r2.3
    decreases reg, 0
  {
    match reg
    case Re_empty =>
    case Re_character(_) =>
    case Re_anchor(_) =>
    case Re_lookaround(_, _, _) =>
    case Re_capture(_, r1) => FNulledChildrenAgree(r1, cdnt, cp, cap, ka, kb, qt, plus_bcv, str, ov, dir, D);
    case Re_alt(r1, r2) =>
      FNulledChildrenAgree(r1, cdnt, cp, cap, ka, kb, qt, plus_bcv, str, ov, dir, D);
      var (c1, l1, x1, o1) := AI.FNulledChildren(r1, cdnt, cp, cap, ka, qt, plus_bcv, str, ov, dir);
      var (c2, l2, x2, o2) := AI.FNulledChildren(r1, cdnt, cp, cap, kb, qt, plus_bcv, str, ov, dir);
      FNulledChildrenAgree(r2, cdnt, cp, c1, l1, l2, x1, plus_bcv, str, o1, dir, D);
    case Re_con(r1, r2) =>
      FNulledChildrenAgree(r1, cdnt, cp, cap, ka, kb, qt, plus_bcv, str, ov, dir, D);
      var (c1, l1, x1, o1) := AI.FNulledChildren(r1, cdnt, cp, cap, ka, qt, plus_bcv, str, ov, dir);
      var (c2, l2, x2, o2) := AI.FNulledChildren(r1, cdnt, cp, cap, kb, qt, plus_bcv, str, ov, dir);
      FNulledChildrenAgree(r2, cdnt, cp, c1, l1, l2, x1, plus_bcv, str, o1, dir, D);
    case Re_quant(nul, qid, quanttype, body) =>
      match AReg.get_cp(qt, qid) {
        case None => FNulledChildrenAgree(body, cdnt, cp, cap, ka, kb, qt, plus_bcv, str, ov, dir, D);
        case Some(start_cp) =>
          if start_cp == cp {
            var start_clock := AI.opt_int(AReg.get_clock(qt, qid));
            var bytecode := AI.get_code_v(plus_bcv, qid);
            var ctx := AI.cp_context(cp, str, dir);
            var i1 := AI.FInitState(bytecode, cp, cap, ka, qt, start_clock, ctx).(cdn := cdnt);
            var i2 := AI.FInitState(bytecode, cp, cap, kb, qt, start_clock, ctx).(cdn := cdnt);
            FInitStateAgree(bytecode, cp, cap, ka, kb, qt, start_clock, ctx, D);
            assert SAgree(i1, i2, D);
            FAdvanceEpsilonAgree(bytecode, i1, i2, ov, dir, D);
            var (res1, _, ova) := AI.FNullInterp(bytecode, i1, ov, dir);
            var (res2, _, ovb) := AI.FNullInterp(bytecode, i2, ov, dir);
            assert OptAgree(res1, res2, D) && ova == ovb;
            var (nc1, nl1, nq1) := match res1 case None => (cap, ka, qt) case Some(w) => (w.capture_regs, w.look_regs, w.quant_regs);
            var (nc2, nl2, nq2) := match res2 case None => (cap, kb, qt) case Some(w) => (w.capture_regs, w.look_regs, w.quant_regs);
            assert nc1 == nc2 && LAgree(nl1, nl2, D) && nq1 == nq2;
            FNulledChildrenAgree(body, cdnt, cp, nc1, nl1, nl2, nq1, plus_bcv, str, ova, dir, D);
          }
      }
  }

  lemma FFindMatchPlusAgree(c: RB.code, ast: R.regex, plus_bcv: seq<RB.code>, str: string, ov: LOr.OracleView,
                            dir: LAnc.direction, start_cp: int, cap: AReg.Regs, ka: AReg.Regs, kb: AReg.Regs,
                            qt: AReg.Regs, clk: int, cdn: LCdn.cdns, D: set<int>)
    requires LAgree(ka, kb, D)
    ensures OptAgree(AI.FFindMatchPlus(c, ast, plus_bcv, str, ov, dir, start_cp, cap, ka, qt, clk, cdn).0,
                     AI.FFindMatchPlus(c, ast, plus_bcv, str, ov, dir, start_cp, cap, kb, qt, clk, cdn).0, D)
    ensures AI.FFindMatchPlus(c, ast, plus_bcv, str, ov, dir, start_cp, cap, ka, qt, clk, cdn).1
         == AI.FFindMatchPlus(c, ast, plus_bcv, str, ov, dir, start_cp, cap, kb, qt, clk, cdn).1
  {
    var ctx := AI.cp_context(start_cp, str, dir);
    var i1 := AI.FInitState(c, start_cp, cap, ka, qt, clk, ctx);
    var i2 := AI.FInitState(c, start_cp, cap, kb, qt, clk, ctx);
    FInitStateAgree(c, start_cp, cap, ka, kb, qt, clk, ctx, D);
    FFindMatchAgree(c, str, i1, i2, ov, dir, cdn, D);
    var (res1, ova) := AI.FFindMatch(c, str, i1, ov, dir, cdn);
    var (res2, ovb) := AI.FFindMatch(c, str, i2, ov, dir, cdn);
    if res1.Some? {
      var w1 := res1.value;
      var w2 := res2.value;
      FNulledPlusAgree(ast, w1.capture_regs, w1.look_regs, w2.look_regs, w1.quant_regs, plus_bcv, str, ova, dir, D);
    }
  }

  /** THE LOOK LOOP reads look positions only (`FLookLoopLookClkIrrel`): no side condition. */
  lemma FLookLoopLookClkIrrel(crv: CP.FCompiled, str: string, lid: int, maxlook: int,
                              cap: AReg.Regs, ka: AReg.Regs, kb: AReg.Regs, qt: AReg.Regs, ov: LOr.OracleView, D: set<int>)
    requires LAgree(ka, kb, D)
    ensures var r1 := AI.FLookLoop(crv, str, lid, maxlook, cap, ka, qt, ov);
            var r2 := AI.FLookLoop(crv, str, lid, maxlook, cap, kb, qt, ov);
            r1.0 == r2.0 && LAgree(r1.1, r2.1, D) && r1.2 == r2.2 && r1.3 == r2.3
    decreases maxlook - lid
  {
    if lid > maxlook { return; }
    var next := lid + 1;
    LAgreeGetCp(ka, kb, lid, D);
    match AReg.get_cp(ka, lid) {
      case None => FLookLoopLookClkIrrel(crv, str, next, maxlook, cap, ka, kb, qt, ov, D);
      case Some(cp) =>
        var looktype := if 0 <= lid < |crv.f_look_types| then crv.f_look_types[lid] else R.Lookahead;
        if AI.capture_type(looktype) {
          var bytecode := AI.get_code_v(crv.f_look_capture_bc, lid);
          var dir := AI.capture_direction(looktype);
          var lookcdn := if 0 <= lid < |crv.f_look_cdns| then crv.f_look_cdns[lid] else [];
          var lookast := if 0 <= lid < |crv.f_look_ast| then crv.f_look_ast[lid] else R.Re_empty;
          FFindMatchPlusAgree(bytecode, lookast, crv.f_plus_bc, str, ov, dir, cp, cap, ka, kb, qt, 0, lookcdn, D);
          var (res1, ova) := AI.FFindMatchPlus(bytecode, lookast, crv.f_plus_bc, str, ov, dir, cp, cap, ka, qt, 0, lookcdn);
          var (res2, ovb) := AI.FFindMatchPlus(bytecode, lookast, crv.f_plus_bc, str, ov, dir, cp, cap, kb, qt, 0, lookcdn);
          var (nc1, nl1, nq1) := match res1 case None => (cap, ka, qt) case Some(t) => (t.capture_regs, t.look_regs, t.quant_regs);
          var (nc2, nl2, nq2) := match res2 case None => (cap, kb, qt) case Some(t) => (t.capture_regs, t.look_regs, t.quant_regs);
          assert nc1 == nc2 && LAgree(nl1, nl2, D) && nq1 == nq2 && ova == ovb;
          FLookLoopLookClkIrrel(crv, str, next, maxlook, nc1, nl1, nl2, nq1, ova, D);
        } else {
          FLookLoopLookClkIrrel(crv, str, next, maxlook, cap, ka, kb, qt, ov, D);
        }
    }
  }

  // ---- 5.4 `filter_capture` never reads the clock of a non-present top lid ----

  /** Two look-clock arrays that differ only at top lids of `r` whose path is not present: the descent to
      such a lid crosses a failing quant/capture test (`LookPathPresent`'s clauses are `filter_capture`'s),
      so the lid sits under a `filter_all`. */
  lemma FilterCaptureLookClkDead(r: R.regex, cr: seq<int>, cc: seq<int>, lc1: seq<int>, lc2: seq<int>,
                                 qc: seq<int>, mx: int)
    requires LTB.LookUnique(r)
    requires forall l: nat {:trigger AI.get_idx(lc1, l)} :: AI.get_idx(lc1, l) != AI.get_idx(lc2, l) ==>
               l !in LTB.LookIds(r) || (l in NI.TopLookIds(r) && !NI.LookPathPresent(r, cc, qc, mx, l))
    ensures AI.filter_capture(r, cr, cc, lc1, qc, mx) == AI.filter_capture(r, cr, cc, lc2, qc, mx)
    decreases r
  {
    match r
    case Re_empty =>
    case Re_character(_) =>
    case Re_anchor(_) =>
    case Re_alt(r1, r2) =>
      FilterCaptureDeadSides(r, cc, lc1, lc2, qc, mx);
      FilterCaptureLookClkDead(r1, cr, cc, lc1, lc2, qc, mx);
      var c1 := AI.filter_capture(r1, cr, cc, lc1, qc, mx);
      FilterCaptureLookClkDead(r2, c1, cc, lc1, lc2, qc, mx);
    case Re_con(r1, r2) =>
      FilterCaptureDeadSides(r, cc, lc1, lc2, qc, mx);
      FilterCaptureLookClkDead(r1, cr, cc, lc1, lc2, qc, mx);
      var c1 := AI.filter_capture(r1, cr, cc, lc1, qc, mx);
      FilterCaptureLookClkDead(r2, c1, cc, lc1, lc2, qc, mx);
    case Re_quant(nul, qid, quant, r1) =>
      var qv := AI.get_idx(qc, qid);
      if qv >= mx {
        forall l: nat | AI.get_idx(lc1, l) != AI.get_idx(lc2, l)
          ensures l !in LTB.LookIds(r1) || (l in NI.TopLookIds(r1) && !NI.LookPathPresent(r1, cc, qc, qv, l))
        {
          if l in LTB.LookIds(r1) {
            assert l in LTB.LookIds(r) && l in NI.TopLookIds(r) && !NI.LookPathPresent(r, cc, qc, mx, l);
          }
        }
        FilterCaptureLookClkDead(r1, cr, cc, lc1, lc2, qc, qv);
      }
    case Re_capture(cid, r1) =>
      var start := AI.get_idx(cc, CP.start_reg(cid));
      if start >= 0 && start >= mx {
        forall l: nat | AI.get_idx(lc1, l) != AI.get_idx(lc2, l)
          ensures l !in LTB.LookIds(r1) || (l in NI.TopLookIds(r1) && !NI.LookPathPresent(r1, cc, qc, mx, l))
        {
          if l in LTB.LookIds(r1) {
            assert l in LTB.LookIds(r) && l in NI.TopLookIds(r) && !NI.LookPathPresent(r, cc, qc, mx, l);
          }
        }
        FilterCaptureLookClkDead(r1, cr, cc, lc1, lc2, qc, mx);
      }
    case Re_lookaround(lid, la, r1) =>
      assert lid >= 0 && (lid as nat) in LTB.LookIds(r);
      assert AI.get_idx(lc1, lid) == AI.get_idx(lc2, lid) by {
        if AI.get_idx(lc1, lid as nat) != AI.get_idx(lc2, lid as nat) {
          assert NI.LookPathPresent(r, cc, qc, mx, lid as nat);
        }
      }
      forall l: nat | AI.get_idx(lc1, l) != AI.get_idx(lc2, l)
        ensures l !in LTB.LookIds(r1) || (l in NI.TopLookIds(r1) && !NI.LookPathPresent(r1, cc, qc, -1, l))
      {
        if l in LTB.LookIds(r1) {
          assert l in LTB.LookIds(r) && l != (lid as nat);
          assert l !in NI.TopLookIds(r);
        }
      }
      FilterCaptureLookClkDead(r1, cr, cc, lc1, lc2, qc, -1);
  }

  /** The two sides of a binary node inherit the hypothesis (`LookUnique`: a top lid of one side is no lid
      of the other). */
  lemma FilterCaptureDeadSides(r: R.regex, cc: seq<int>, lc1: seq<int>, lc2: seq<int>, qc: seq<int>, mx: int)
    requires r.Re_alt? || r.Re_con?
    requires LTB.LookUnique(r)
    requires forall l: nat {:trigger AI.get_idx(lc1, l)} :: AI.get_idx(lc1, l) != AI.get_idx(lc2, l) ==>
               l !in LTB.LookIds(r) || (l in NI.TopLookIds(r) && !NI.LookPathPresent(r, cc, qc, mx, l))
    ensures var r1 := if r.Re_alt? then r.e1 else r.c1;
            forall l: nat {:trigger AI.get_idx(lc1, l)} :: AI.get_idx(lc1, l) != AI.get_idx(lc2, l) ==>
               l !in LTB.LookIds(r1) || (l in NI.TopLookIds(r1) && !NI.LookPathPresent(r1, cc, qc, mx, l))
    ensures var r2 := if r.Re_alt? then r.e2 else r.c2;
            forall l: nat {:trigger AI.get_idx(lc1, l)} :: AI.get_idx(lc1, l) != AI.get_idx(lc2, l) ==>
               l !in LTB.LookIds(r2) || (l in NI.TopLookIds(r2) && !NI.LookPathPresent(r2, cc, qc, mx, l))
  {
    var r1 := if r.Re_alt? then r.e1 else r.c1;
    var r2 := if r.Re_alt? then r.e2 else r.c2;
    assert LTB.LookIds(r1) * LTB.LookIds(r2) == {};
    NI.TopLookIdsIn(r1); NI.TopLookIdsIn(r2);
    forall l: nat | AI.get_idx(lc1, l) != AI.get_idx(lc2, l)
      ensures l !in LTB.LookIds(r1) || (l in NI.TopLookIds(r1) && !NI.LookPathPresent(r1, cc, qc, mx, l))
      ensures l !in LTB.LookIds(r2) || (l in NI.TopLookIds(r2) && !NI.LookPathPresent(r2, cc, qc, mx, l))
    {
      if l in LTB.LookIds(r1) {
        assert l !in LTB.LookIds(r2) by { if l in LTB.LookIds(r2) { assert l in LTB.LookIds(r1) * LTB.LookIds(r2); } }
        assert l in LTB.LookIds(r) && l in NI.TopLookIds(r) && !NI.LookPathPresent(r, cc, qc, mx, l);
      } else if l in LTB.LookIds(r2) {
        assert l in LTB.LookIds(r) && l in NI.TopLookIds(r) && !NI.LookPathPresent(r, cc, qc, mx, l);
      }
    }
  }

  // ---- 5.5 the answer ----

  /** THE ANSWER at a thread with the endpoint's register facts: lowering the dead-written look clocks
      changes neither the look loop's capture/quant banks and look positions nor `filter_reset`. The look
      loop keeps the capture/quant clocks that decide a top lid's presence (`M.CaptureFrameO`,
      `M.QuantFrameO`), so the lid is still not present when `filter_capture` walks to it. */
  lemma AnswerLowered(ast: R.regex, re: R.regex, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
                      th: AI.Thread, Q: set<int>, ncap: int, nlook: int, nquant: int)
    requires crv == CP.FFullCompilation(ast) && re == R.lazy_prefix(ast)
    requires M.LookBodiesPlusGateRE(re)
    requires T.TransWf(re) && NR.NestedFragmentCdnRE(re)
    requires PIV.CapUnique(re) && PIV.QuantUnique(re) && LTB.LookUnique(re)
    requires LTB.LookTablesOk(re, crv) && LTB.LidsWellNested(re)
    requires forall x: nat :: x in LTB.LookIds(re) ==> 1 <= x <= R.max_lookaround(ast)
    requires ncap >= 0 && nlook >= 0 && nquant >= 0
    requires M.WinRegsOk(ast, re, crv, str, ov, th, ncap, nlook, nquant)
    ensures var th1 := LowerDeadLookClks(re, Q, th);
            var r1 := AI.FLookLoop(crv, str, 1, R.max_lookaround(ast), th.capture_regs, th.look_regs, th.quant_regs, ov);
            var r2 := AI.FLookLoop(crv, str, 1, R.max_lookaround(ast), th1.capture_regs, th1.look_regs, th1.quant_regs, ov);
            AI.filter_reset(ast, r1.0, r1.1, r1.2, -1) == AI.filter_reset(ast, r2.0, r2.1, r2.2, -1)
            && r1.0 == r2.0 && r1.1.a_cp == r2.1.a_cp && r1.2 == r2.2 && r1.3 == r2.3
  {
    hide M.LookBodiesPlusGateRE, T.TransWf, NR.NestedFragmentCdnRE, LTB.LookTablesOk, LTB.LidsWellNested;
    var maxlook := R.max_lookaround(ast);
    var th1 := LowerDeadLookClks(re, Q, th);
    LowerDeadLookClksFacts(re, Q, th);
    var D := set l: int | 0 <= l < |th.look_regs.a_clk| && DeadLid(re, Q, th, l);
    assert LAgree(th.look_regs, th1.look_regs, D) by {
      forall k | 0 <= k < |th.look_regs.a_clk| && k !in D ensures th.look_regs.a_clk[k] == th1.look_regs.a_clk[k] {
        assert !DeadLid(re, Q, th, k);
        assert AI.get_idx(th1.look_regs.a_clk, k) == AI.get_idx(th.look_regs.a_clk, k);
      }
    }
    FLookLoopLookClkIrrel(crv, str, 1, maxlook, th.capture_regs, th.look_regs, th1.look_regs, th.quant_regs, ov, D);
    var r1 := AI.FLookLoop(crv, str, 1, maxlook, th.capture_regs, th.look_regs, th.quant_regs, ov);
    var r2 := AI.FLookLoop(crv, str, 1, maxlook, th1.capture_regs, th1.look_regs, th1.quant_regs, ov);
    assert r1.0 == r2.0 && LAgree(r1.1, r2.1, D) && r1.2 == r2.2 && r1.3 == r2.3;
    assert {:split_here} true;
    // the look loop's frames at `th`
    M.EndpointValueOkRegsCdn(ast, re, crv, str, ov, th, ncap, nlook, nquant);
    M.EndpointQuantValueOkRegsCdn(ast, re, crv, str, ov, th, ncap, nlook, nquant);
    assert M.CaptureFrameO(re, r1.0, th.capture_regs) && M.QuantFrameO(re, r1.2, th.quant_regs);
    assert {:split_here} true;
    DeadStaysDead(ast, re, Q, th, r1.0, r1.2);
    assert {:split_here} true;
    assert LTB.LookUnique(ast) by { assert re == R.Re_con(re.c1, ast); }
    forall l: nat | AI.get_idx(r1.1.a_clk, l) != AI.get_idx(r2.1.a_clk, l)
      ensures l !in LTB.LookIds(ast) || (l in NI.TopLookIds(ast) && !NI.LookPathPresent(ast, r1.0.a_clk, r1.2.a_clk, -1, l))
    {
      assert (l as int) in D;
      assert DeadLid(re, Q, th, l);
    }
    FilterCaptureLookClkDead(ast, r1.0.a_cp, r1.0.a_clk, r1.1.a_clk, r2.1.a_clk, r1.2.a_clk, -1);
  }

  /** A dead lid of `th` is a non-present top lid of `ast` at any banks that keep `th`'s outside-look
      capture and quant clocks. */
  lemma DeadStaysDead(ast: R.regex, re: R.regex, Q: set<int>, th: AI.Thread, res0: AReg.Regs, res2: AReg.Regs)
    requires re == R.lazy_prefix(ast)
    requires NR.NestedFragmentCdnRE(re) && PIV.CapUnique(re) && LTB.LookUnique(re)
    requires M.CaptureFrameO(re, res0, th.capture_regs) && M.QuantFrameO(re, res2, th.quant_regs)
    ensures forall l: int {:trigger DeadLid(re, Q, th, l)} :: DeadLid(re, Q, th, l) ==>
              (l as nat) in LTB.LookIds(ast) && (l as nat) in NI.TopLookIds(ast)
              && !NI.LookPathPresent(ast, res0.a_clk, res2.a_clk, -1, l as nat)
  {
    reveal M.CaptureFrameO(), M.QuantFrameO();
    var pre := re.c1;
    assert re == R.Re_con(pre, ast);
    assert LTB.LookIds(pre) == {} && NI.TopLookIds(pre) == {};
    PIV.CapIdsLooksDisjoint(re);
    PIV.CaptureRegsSetDisjoint(PIV.CapIdsOutsideLooks(re), PIV.CapIdsInLooks(re));
    forall c: nat | c in PIV.CapIdsOutsideLooks(re)
      ensures AI.get_idx(th.capture_regs.a_clk, CP.start_reg(c as int)) == AI.get_idx(res0.a_clk, CP.start_reg(c as int))
    {
      var k := CP.start_reg(c as int);
      assert k in PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(re));
      assert k !in PIV.CaptureRegsSet(PIV.CapIdsInLooks(re)) by {
        if k in PIV.CaptureRegsSet(PIV.CapIdsInLooks(re)) {
          assert k in PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(re)) * PIV.CaptureRegsSet(PIV.CapIdsInLooks(re));
        }
      }
    }
    forall l: int | DeadLid(re, Q, th, l)
      ensures (l as nat) in LTB.LookIds(ast) && (l as nat) in NI.TopLookIds(ast)
              && !NI.LookPathPresent(ast, res0.a_clk, res2.a_clk, -1, l as nat)
    {
      var ln: nat := l;
      NI.LookPathPresentAgreeTopCdn(re, th.capture_regs.a_clk, th.quant_regs.a_clk, res0.a_clk, res2.a_clk, -1, ln);
      assert !NI.LookPathPresent(re, res0.a_clk, res2.a_clk, -1, ln);
      assert ln !in LTB.LookIds(pre);
      assert NI.LookPathPresent(re, res0.a_clk, res2.a_clk, -1, ln) == NI.LookPathPresent(ast, res0.a_clk, res2.a_clk, -1, ln);
    }
  }

  /** THE ANSWER at the synthetic winner `rp0 = ClearQuantCps(LowerDeadLookClks(rp), QIdsOuter(re))` — the
      twin of `MC.AnswerSynthetic`: the engine's answer is read off `rp0` exactly. */
  lemma AnswerSyntheticLowered(ast: R.regex, re: R.regex, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
                               rp: AI.Thread, Q: set<int>, ncap: int, nlook: int, nquant: int)
    requires crv == CP.FFullCompilation(ast) && re == R.lazy_prefix(ast)
    requires M.LookBodiesPlusGateRE(re)
    requires T.TransWf(re) && NR.NestedFragmentCdnRE(re)
    requires PIV.CapUnique(re) && PIV.QuantUnique(re) && LTB.LookUnique(re)
    requires LTB.LookTablesOk(re, crv) && LTB.LidsWellNested(re)
    requires forall x: nat :: x in LTB.LookIds(re) ==> 1 <= x <= R.max_lookaround(ast)
    requires ncap >= 0 && nlook >= 0 && nquant >= 0
    requires M.WinRegsOk(ast, re, crv, str, ov, MC.ClearQuantCps(rp, M.QIdsOuter(re)), ncap, nlook, nquant)
    ensures var rp0 := MC.ClearQuantCps(LowerDeadLookClks(re, Q, rp), M.QIdsOuter(re));
            var r1 := AI.FLookLoop(crv, str, 1, R.max_lookaround(ast), rp.capture_regs, rp.look_regs, rp.quant_regs, ov);
            var r2 := AI.FLookLoop(crv, str, 1, R.max_lookaround(ast), rp0.capture_regs, rp0.look_regs, rp0.quant_regs, ov);
            AI.filter_reset(ast, r1.0, r1.1, r1.2, -1) == AI.filter_reset(ast, r2.0, r2.1, r2.2, -1)
            && r1.0 == r2.0 && r1.1.a_cp == r2.1.a_cp && r1.3 == r2.3 && r1.2.a_clk == r2.2.a_clk
  {
    hide M.LookBodiesPlusGateRE, T.TransWf, NR.NestedFragmentCdnRE, LTB.LookTablesOk, LTB.LidsWellNested;
    var Dq := M.QIdsOuter(re);
    var rpc := MC.ClearQuantCps(rp, Dq);
    MC.AnswerSynthetic(ast, re, crv, str, ov, rp);
    AnswerLowered(ast, re, crv, str, ov, rpc, Q, ncap, nlook, nquant);
    LowerClearCommute(re, Q, rp, Dq);
  }
}
