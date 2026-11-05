// §2.5b STAGE 2, RUNG F (F-b, VM half) — the register facts of the best
// thread that hold of EVERY thread of a run, by a parallel induction on
// `FFindMatch` (it does not touch the simulation invariant; the shape is
// `CM.FFindMatchLookCpOk`'s):
//   * every SET quant cp was written by a TRUE stamp (`SetQuantToClock(q,
//     true)` — the only write of a nonnegative quant cp) whose qid is in a
//     given set `Q` (the caller's code inventory: the CIN-greedy pluses), at a
//     position `<= ub` (the forward scan keeps `cp <= |str|`);
//   * a capture register's value is set exactly when its clock is
//     (`NRR.CapValWf`): the only capture write records `(cp, clock)` with both
//     nonnegative.
// Under the interim gate `Q == {}` and the first fact is `M.QuantRegsFinal`'s
// value half; rung G retires that one.
module LindenElkFinalVm {
  import opened Std.Wrappers
  import AI = ArrayInterp
  import AReg = Array_Regs
  import RB = Bytecode
  import LOr = Oracle
  import LAnc = Anchors
  import LCdn = Cdn
  import RC = Charclasses
  import NR = LindenElkNfaRep
  import CM = LindenElkClockMono

  /** Every true stamp in `c` is on a qid in `Q`. */
  ghost predicate TrueStampsIn(c: RB.code, Q: set<int>) {
    forall pc: nat, q: int :: NR.GetPcRE(c, pc) == Some(RB.SetQuantToClock(q, true)) ==> q in Q
  }

  /** A thread's quant cps are true-stamp records inside `[0, ub]`, and its
      capture values are set exactly with their clocks. */
  ghost predicate RegsFinalOk(t: AI.Thread, ub: int, Q: set<int>) {
    (forall q: int :: AI.get_idx(t.quant_regs.a_cp, q) >= 0 ==> AI.get_idx(t.quant_regs.a_cp, q) <= ub && q in Q)
    && (forall k: int :: AI.get_idx(t.capture_regs.a_clk, k) < 0 <==> AI.get_idx(t.capture_regs.a_cp, k) < 0)
    // quant clocks never drop below the initial `-1` (`M.QuantRegsFinal`'s clock half)
    && (forall q: int :: AI.get_idx(t.quant_regs.a_clk, q) >= -1)
  }

  ghost predicate VmRegsFinalOk(s: AI.VmState, ub: int, Q: set<int>) {
    (forall t | t in s.active :: RegsFinalOk(t, ub, Q))
    && (forall tb | tb in s.blocked :: RegsFinalOk(tb.0, ub, Q))
    && (s.bestmatch.Some? ==> RegsFinalOk(s.bestmatch.value, ub, Q))
  }

  /** Fresh registers (every slot `-1`). */
  lemma RegsFinalOkInit(ncap: int, nlook: int, nquant: int, ub: int, Q: set<int>)
    ensures RegsFinalOk(AI.init_thread(AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant)), ub, Q)
  {
    var t := AI.init_thread(AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant));
    forall q: int ensures AI.get_idx(t.quant_regs.a_cp, q) < 0 && AI.get_idx(t.quant_regs.a_clk, q) == -1 {
      if 0 <= q < |t.quant_regs.a_cp| { assert t.quant_regs.a_cp[q] == -1; }
      if 0 <= q < |t.quant_regs.a_clk| { assert t.quant_regs.a_clk[q] == -1; }
    }
    forall k: int ensures AI.get_idx(t.capture_regs.a_clk, k) < 0 && AI.get_idx(t.capture_regs.a_cp, k) < 0 {
      if 0 <= k < |t.capture_regs.a_clk| { assert t.capture_regs.a_clk[k] == -1; }
      if 0 <= k < |t.capture_regs.a_cp| { assert t.capture_regs.a_cp[k] == -1; }
    }
  }

  /** The capture write `(cp, clk)`, both nonnegative. */
  lemma RegsFinalCapWrite(t: AI.Thread, reg: int, cp: int, clk: int, ub: int, Q: set<int>)
    requires RegsFinalOk(t, ub, Q)
    requires cp >= 0 && clk >= 0
    ensures RegsFinalOk(t.(capture_regs := AReg.set_reg(t.capture_regs, reg, Some(cp), clk)), ub, Q)
  {
    var r := t.capture_regs;
    var r2 := AReg.set_reg(r, reg, Some(cp), clk);
    forall k: int ensures AI.get_idx(r2.a_clk, k) < 0 <==> AI.get_idx(r2.a_cp, k) < 0 {
      if k != reg {
        CM.SetRegOtherIdx(r, reg, Some(cp), clk, k);
      } else if 0 <= reg < |r.a_cp| && 0 <= reg < |r.a_clk| {
        assert r2.a_cp == r.a_cp[reg := cp] && r2.a_clk == r.a_clk[reg := clk];
      } else {
        assert r2 == r;
      }
    }
  }

  /** The quant write: a mark records `-1`; a true stamp records `cp <= ub` on
      a qid of `Q`. */
  lemma RegsFinalQuantWrite(t: AI.Thread, q: int, bq: bool, cp: int, clk: int, ub: int, Q: set<int>)
    requires RegsFinalOk(t, ub, Q)
    requires clk >= -1
    requires bq ==> cp <= ub && q in Q
    ensures RegsFinalOk(t.(quant_regs := AReg.set_reg(t.quant_regs, q, if bq then Some(cp) else None, clk)), ub, Q)
  {
    var ocp := if bq then Some(cp) else None;
    var r := t.quant_regs;
    var r2 := AReg.set_reg(r, q, ocp, clk);
    forall k: int | AI.get_idx(r2.a_cp, k) >= 0 ensures AI.get_idx(r2.a_cp, k) <= ub && k in Q {
      if k != q {
        CM.SetRegOtherIdx(r, q, ocp, clk, k);
      } else if 0 <= q < |r.a_cp| && 0 <= q < |r.a_clk| {
        assert r2.a_cp == r.a_cp[q := if bq then cp else -1];
        assert bq;
      } else {
        assert r2 == r;
      }
    }
    forall k: int ensures AI.get_idx(r2.a_clk, k) >= -1 {
      if k != q {
        CM.SetRegOtherIdx(r, q, ocp, clk, k);
      } else if 0 <= q < |r.a_cp| && 0 <= q < |r.a_clk| {
        assert r2.a_clk == r.a_clk[q := clk];
      } else {
        assert r2 == r;
      }
    }
  }

  /** An epsilon phase keeps every thread's final-register facts. */
  lemma FAdvanceEpsilonRegsFinal(c: RB.code, s: AI.VmState, ov: LOr.OracleView,
                                 dir: LAnc.direction, ub: int, Q: set<int>)
    requires |s.processed.true_set| == RB.size(c) && |s.processed.false_set| == RB.size(c)
    requires TrueStampsIn(c, Q)
    requires 0 <= s.cp <= ub && s.clock >= 0
    requires VmRegsFinalOk(s, ub, Q)
    ensures VmRegsFinalOk(AI.FAdvanceEpsilon(c, s, ov, dir).0, ub, Q)
    decreases AI.unprocessed(s.processed), |s.active|
  {
    if |s.active| == 0 { return; }
    var t := s.active[0];
    var ac := s.active[1..];
    assert t in s.active;
    assert forall x | x in ac :: x in s.active;
    if AI.bpc_mem(s.processed, t.pc, t.exit_allowed) {
      FAdvanceEpsilonRegsFinal(c, s.(active := ac), ov, dir, ub, Q);
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
        assert VmRegsFinalOk(s2, ub, Q) by {
          forall tb | tb in nb ensures RegsFinalOk(tb.0, ub, Q) {
            assert tb == (t, ce) || tb in s1.blocked;
          }
        }
        FAdvanceEpsilonRegsFinal(c, s2, ov, dir, ub, Q);
      case Accept =>
      case Jmp(x) =>
        FAdvanceEpsilonRegsFinal(c, s1.(active := [t.(pc := x)] + ac), ov, dir, ub, Q);
      case Fork(x, y) =>
        var newt := AI.Thread(x, t.capture_regs, t.look_regs, t.quant_regs, t.exit_allowed);
        FAdvanceEpsilonRegsFinal(c, s1.(active := [newt, t.(pc := y)] + ac), ov, dir, ub, Q);
      case SetRegisterToCP(reg) =>
        var t2 := t.(capture_regs := AReg.set_reg(t.capture_regs, reg, Some(s1.cp), s1.clock), pc := t.pc + 1);
        RegsFinalCapWrite(t, reg, s1.cp, s1.clock, ub, Q);
        assert RegsFinalOk(t2, ub, Q);
        FAdvanceEpsilonRegsFinal(c, s1.(active := [t2] + ac), ov, dir, ub, Q);
      case SetQuantToClock(q, bq) =>
        var ocp := if bq then Some(s1.cp) else None;
        var t2 := t.(quant_regs := AReg.set_reg(t.quant_regs, q, ocp, s1.clock), pc := t.pc + 1);
        assert bq ==> q in Q by {
          if bq {
            assert 0 <= t.pc < |c|;
            assert NR.GetPcRE(c, t.pc as nat) == Some(RB.SetQuantToClock(q, true));
          }
        }
        RegsFinalQuantWrite(t, q, bq, s1.cp, s1.clock, ub, Q);
        assert RegsFinalOk(t2, ub, Q);
        FAdvanceEpsilonRegsFinal(c, s1.(active := [t2] + ac), ov, dir, ub, Q);
      case CheckOracle(l) =>
        if LOr.view_get_oracle(ov, s1.cp, l) {
          var t2 := t.(pc := t.pc + 1, look_regs := AReg.set_reg(t.look_regs, l, Some(s1.cp), s1.clock));
          FAdvanceEpsilonRegsFinal(c, s1.(active := [t2] + ac), ov, dir, ub, Q);
        } else {
          FAdvanceEpsilonRegsFinal(c, s1.(active := ac), ov, dir, ub, Q);
        }
      case NegCheckOracle(l) =>
        if LOr.view_get_oracle(ov, s1.cp, l) {
          FAdvanceEpsilonRegsFinal(c, s1.(active := ac), ov, dir, ub, Q);
        } else {
          FAdvanceEpsilonRegsFinal(c, s1.(active := [t.(pc := t.pc + 1)] + ac), ov, dir, ub, Q);
        }
      case WriteOracle(l) =>
        FAdvanceEpsilonRegsFinal(c, s1.(active := ac), LOr.view_set_oracle(ov, s1.cp, l), dir, ub, Q);
      case BeginLoop =>
        FAdvanceEpsilonRegsFinal(c, s1.(active := [t.(exit_allowed := false, pc := t.pc + 1)] + ac), ov, dir, ub, Q);
      case EndLoop =>
        if t.exit_allowed {
          FAdvanceEpsilonRegsFinal(c, s1.(active := [t.(pc := t.pc + 1)] + ac), ov, dir, ub, Q);
        } else {
          FAdvanceEpsilonRegsFinal(c, s1.(active := ac), ov, dir, ub, Q);
        }
      case CheckNullable(qid) =>
        if LCdn.cdn_get(s1.cdn, qid) {
          FAdvanceEpsilonRegsFinal(c, s1.(active := [t.(pc := t.pc + 1)] + ac), ov, dir, ub, Q);
        } else {
          FAdvanceEpsilonRegsFinal(c, s1.(active := ac), ov, dir, ub, Q);
        }
      case AnchorAssertion(a) =>
        if LAnc.is_satisfied(a, s1.context, dir) {
          FAdvanceEpsilonRegsFinal(c, s1.(active := [t.(pc := t.pc + 1)] + ac), ov, dir, ub, Q);
        } else {
          FAdvanceEpsilonRegsFinal(c, s1.(active := ac), ov, dir, ub, Q);
        }
      case Fail =>
        FAdvanceEpsilonRegsFinal(c, s1.(active := ac), ov, dir, ub, Q);
    }
  }

  /** The consume phase moves blocked threads to active, registers untouched. */
  lemma FConsumeRegsFinal(s: AI.VmState, ub: int, Q: set<int>)
    requires VmRegsFinalOk(s, ub, Q)
    ensures VmRegsFinalOk(AI.FConsume(s), ub, Q)
    decreases |s.blocked|
  {
    if |s.blocked| == 0 { return; }
    var t := s.blocked[0].0;
    var ce := s.blocked[0].1;
    var s1 := s.(blocked := s.blocked[1..]);
    assert VmRegsFinalOk(s1, ub, Q) by {
      forall tb | tb in s1.blocked ensures RegsFinalOk(tb.0, ub, Q) { assert tb in s.blocked; }
    }
    var s2 := if RC.is_accepted(s1.context.nextchar, ce)
              then s1.(active := [t.(exit_allowed := true, pc := t.pc + 1)] + s1.active)
              else s1;
    assert VmRegsFinalOk(s2, ub, Q) by {
      assert s.blocked[0] in s.blocked;
      assert RegsFinalOk(t, ub, Q);
      forall t2 | t2 in s2.active ensures RegsFinalOk(t2, ub, Q) {
        if t2 != t.(exit_allowed := true, pc := t.pc + 1) { assert t2 in s1.active; }
      }
    }
    FConsumeRegsFinal(s2, ub, Q);
  }

  /** THE VM HALF: a whole forward search's winning thread has true-stamp
      quant cps inside the string and well-formed capture values. */
  lemma FFindMatchRegsFinal(c: RB.code, str: string, s: AI.VmState, ov: LOr.OracleView,
                            dir: LAnc.direction, cdn: LCdn.cdns, Q: set<int>)
    requires |s.processed.true_set| == RB.size(c) && |s.processed.false_set| == RB.size(c)
    requires dir == LAnc.Forward
    requires TrueStampsIn(c, Q)
    requires s.context.nextchar == AI.get_char(str, s.cp)
    requires 0 <= s.cp <= |str| && s.clock >= 0
    requires VmRegsFinalOk(s, |str|, Q)
    ensures var r := AI.FFindMatch(c, str, s, ov, dir, cdn).0;
      r.Some? ==> RegsFinalOk(r.value, |str|, Q)
    decreases |str| - s.cp
  {
    var s0 := s.(cdn := LCdn.build_cdn_v(cdn, s.cp, ov, s.context, dir));
    assert VmRegsFinalOk(s0, |str|, Q);
    var (s1, ov1) := AI.FAdvanceEpsilon(c, s0, ov, dir);
    FAdvanceEpsilonRegsFinal(c, s0, ov, dir, |str|, Q);
    CM.FAdvanceEpsilonClockGrows(c, s0, ov, dir);
    assert VmRegsFinalOk(s1, |str|, Q);
    if |s1.blocked| == 0 { return; }
    match s1.context.nextchar {
      case None =>
      case Some(_) =>
        assert s.cp < |str|;
        var s2 := AI.FConsume(s1);
        FConsumeRegsFinal(s1, |str|, Q);
        CM.FConsumeClockSame(s1);
        var s3 := s2.(processed := AI.init_bpcset(RB.size(c)), isblocked := AI.init_pcset(RB.size(c)),
                      cdn := LCdn.init_cdn(), cp := AI.incr_cp(s2.cp, dir));
        var newchar := AI.get_char(str, s3.cp - AI.cp_offset(dir));
        var s4 := s3.(context := LAnc.update_context(s3.context, newchar));
        assert s4.cp == s.cp + 1 <= |str|;
        assert VmRegsFinalOk(s4, |str|, Q);
        FFindMatchRegsFinal(c, str, s4, ov1, dir, cdn, Q);
    }
  }
}
