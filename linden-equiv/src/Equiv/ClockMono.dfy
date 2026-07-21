// Clock-monotonicity backbone for the PikeInvRE preservation induction.
//
// FAdvanceEpsilon stamps every register write with the post-increment clock
// (s1.clock = s.clock + 1) and simultaneously advances the state clock to that
// same value. So the honest global bound is: every register clock is <= the
// state's clock. This file proves FAdvanceEpsilon preserves that bound and never
// decreases the clock -- the foundation for the per-iteration staleness argument
// (prior-iteration subgroup clocks sit strictly below the current star stamp).
//
// This is a self-contained property of the imported RegElk interpreter, proved
// by structural induction mirroring FAdvanceEpsilon's own recursion.
include "PikeInvRE.dfy"

/** The clock-monotonicity backbone for `PikeInvRE`'s preservation induction:
    proves three families of invariants are preserved by the VM's stepping
    operations (`FAdvanceEpsilon`, `FConsume`, `FInitState`) — every register
    clock stays `<=` the state's global clock (`VmClocksLE`), register arrays
    keep fixed, well-formed shapes (`VmRegsWf`), and every stored capture
    value stays `<=` the current `cp` (`VmCapsLE`). Proved by structural
    induction mirroring `FAdvanceEpsilon`'s own recursion. */
module LindenElkClockMono {
  import opened Std.Wrappers
  import AI = ArrayInterp
  import AReg = Array_Regs
  import RB = Bytecode
  import LOr = Oracle
  import LAnc = Anchors
  import LCdn = Cdn
  import RC = Charclasses
  import PIV = LindenElkPikeInv

  // Every clock stored in `regs` is at most C. Note: because get_idx yields -1
  // for out-of-range indices, RegsClocksLE(regs, C) already forces C >= -1.
  /** Every clock slot in `regs` (capture, look, or quant) is at most `C`. */
  ghost predicate RegsClocksLE(regs: AReg.ARegs, C: int) {
    forall k :: AI.get_idx(regs.a_clk, k) <= C
  }

  /** `RegsClocksLE` holds of a thread's capture, look, and quant registers. */
  ghost predicate ThreadClocksLE(t: AI.Thread, C: int) {
    RegsClocksLE(t.capture_regs, C) && RegsClocksLE(t.look_regs, C) && RegsClocksLE(t.quant_regs, C)
  }

  /** `ThreadClocksLE` bounded by the state's own `clock`, for every active and
      blocked thread and for `bestmatch`. */
  ghost predicate VmClocksLE(s: AI.VmState) {
    (forall t | t in s.active :: ThreadClocksLE(t, s.clock))
    && (forall tb | tb in s.blocked :: ThreadClocksLE(tb.0, s.clock))
    && (s.bestmatch.Some? ==> ThreadClocksLE(s.bestmatch.value, s.clock))
  }

  /** `ThreadClocksLE` is monotone: any bound that holds also holds for every
      larger bound. */
  lemma ThreadClocksLEMono(t: AI.Thread, C: int, D: int)
    requires ThreadClocksLE(t, C) && C <= D
    ensures ThreadClocksLE(t, D)
  {}

  // set_reg overwrites one clock slot with `clk` and leaves the rest; if the old
  // clocks and the new stamp are both <= C, so are all resulting clocks.
  /** `AReg.set_reg` preserves `RegsClocksLE(_, C)` when the newly stamped
      clock is itself `<= C`. */
  lemma RegsClocksLESet(regs: AReg.ARegs, k: int, cp: Option<int>, clk: int, C: int)
    requires RegsClocksLE(regs, C) && clk <= C
    ensures RegsClocksLE(AReg.set_reg(regs, k, cp, clk), C)
  {
    var r' := AReg.set_reg(regs, k, cp, clk);
    forall j ensures AI.get_idx(r'.a_clk, j) <= C {
      if 0 <= k < |regs.a_cp| && 0 <= k < |regs.a_clk| {
        assert |r'.a_clk| == |regs.a_clk|;
        if j == k {
          assert AI.get_idx(r'.a_clk, j) == clk;
        } else {
          assert AI.get_idx(r'.a_clk, j) == AI.get_idx(regs.a_clk, j);
        }
      } else {
        assert r' == regs;
      }
    }
  }

  // Blocked-list and bestmatch clocks lift from the state bound to any larger C.
  /** Lifts a state's blocked-thread and `bestmatch` clock bounds from
      `s.clock` up to any larger `C`. */
  lemma TailLE(s: AI.VmState, C: int)
    requires VmClocksLE(s) && s.clock <= C
    ensures forall tb | tb in s.blocked :: ThreadClocksLE(tb.0, C)
    ensures s.bestmatch.Some? ==> ThreadClocksLE(s.bestmatch.value, C)
  {
    forall tb | tb in s.blocked ensures ThreadClocksLE(tb.0, C) {
      ThreadClocksLEMono(tb.0, s.clock, C);
    }
    if s.bestmatch.Some? { ThreadClocksLEMono(s.bestmatch.value, s.clock, C); }
  }

  // The clock-monotonicity backbone.
  /** `FAdvanceEpsilon` never decreases the state's clock and preserves
      `VmClocksLE`: structural induction over the epsilon-closure fuel, one
      case per bytecode instruction. */
  lemma FAdvanceEpsilonClocksLE(c: RB.code, s: AI.VmState, ov: LOr.OracleView, dir: LAnc.direction)
    requires |s.processed.true_set| == RB.size(c) && |s.processed.false_set| == RB.size(c)
    requires VmClocksLE(s)
    ensures var r := AI.FAdvanceEpsilon(c, s, ov, dir).0;
      r.clock >= s.clock && VmClocksLE(r)
    decreases AI.unprocessed(s.processed), |s.active|
  {
    if |s.active| == 0 {
      return;                       // FAdvanceEpsilon returns (s, ov)
    }
    var t := s.active[0];
    var ac := s.active[1..];
    assert t in s.active;
    assert forall x | x in ac :: x in s.active;
    var i := RB.get_instr(c, t.pc);

    if AI.bpc_mem(s.processed, t.pc, t.exit_allowed) {
      var s' := s.(active := ac);
      assert VmClocksLE(s');
      FAdvanceEpsilonClocksLE(c, s', ov, dir);
      return;
    }

    var b0 := s.processed;
    var s1 := s.(clock := s.clock + 1, processed := AI.bpc_add(b0, t.pc, t.exit_allowed));
    // Mirror FAdvanceEpsilon's own termination witness so recursive lemma calls
    // whose active list does not shrink (Jmp/Fork/register writes) still decrease.
    assert AI.unprocessed(s1.processed) <= AI.unprocessed(b0)
        && (0 <= t.pc < RB.size(c) ==> AI.unprocessed(s1.processed) < AI.unprocessed(b0))
      by { AI.UnprocessedAdd(b0, t.pc, t.exit_allowed); }
    assert s.clock <= s1.clock;
    assert ThreadClocksLE(t, s1.clock) by { ThreadClocksLEMono(t, s.clock, s1.clock); }
    TailLE(s, s1.clock);

    match i {
      case Consume(ce) =>
        var (nb, ni) := AI.add_thread(t, ce, s1.blocked, s1.isblocked);
        var s' := s1.(blocked := nb, isblocked := ni, active := ac);
        assert 0 <= t.pc < |c|;
        assert VmClocksLE(s') by {
          forall t2 | t2 in s'.active ensures ThreadClocksLE(t2, s'.clock) {
            assert t2 in s.active;
            ThreadClocksLEMono(t2, s.clock, s'.clock);
          }
          forall tb | tb in s'.blocked ensures ThreadClocksLE(tb.0, s'.clock) {
            // nb is either s1.blocked (== s.blocked) or [(t,ce)] + s1.blocked
            assert tb == (t, ce) || tb in s.blocked;
          }
        }
        FAdvanceEpsilonClocksLE(c, s', ov, dir);

      case Accept =>
        // FAdvanceEpsilon returns (s1.(active := [], bestmatch := Some(t)), ov).
        assert ThreadClocksLE(t, s1.clock);

      case Jmp(x) =>
        var s' := s1.(active := [t.(pc := x)] + ac);
        assert 0 <= t.pc < |c|;
        assert VmClocksLE(s') by {
          forall t2 | t2 in s'.active ensures ThreadClocksLE(t2, s'.clock) {
            if t2 == t.(pc := x) { assert ThreadClocksLE(t2, s'.clock); }
            else { assert t2 in s.active; ThreadClocksLEMono(t2, s.clock, s'.clock); }
          }
        }
        FAdvanceEpsilonClocksLE(c, s', ov, dir);

      case Fork(x, y) =>
        var newt := AI.Thread(x, t.capture_regs, t.look_regs, t.quant_regs, t.exit_allowed);
        var s' := s1.(active := [newt, t.(pc := y)] + ac);
        assert 0 <= t.pc < |c|;
        assert VmClocksLE(s') by {
          forall t2 | t2 in s'.active ensures ThreadClocksLE(t2, s'.clock) {
            if t2 == newt || t2 == t.(pc := y) { assert ThreadClocksLE(t2, s'.clock); }
            else { assert t2 in s.active; ThreadClocksLEMono(t2, s.clock, s'.clock); }
          }
        }
        FAdvanceEpsilonClocksLE(c, s', ov, dir);

      case SetRegisterToCP(reg) =>
        var t' := t.(capture_regs := AReg.set_reg(t.capture_regs, reg, Some(s1.cp), s1.clock), pc := t.pc + 1);
        var s' := s1.(active := [t'] + ac);
        assert 0 <= t.pc < |c|;
        assert ThreadClocksLE(t', s1.clock) by {
          RegsClocksLESet(t.capture_regs, reg, Some(s1.cp), s1.clock, s1.clock);
        }
        assert VmClocksLE(s') by {
          forall t2 | t2 in s'.active ensures ThreadClocksLE(t2, s'.clock) {
            if t2 == t' { assert ThreadClocksLE(t2, s'.clock); }
            else { assert t2 in s.active; ThreadClocksLEMono(t2, s.clock, s'.clock); }
          }
        }
        FAdvanceEpsilonClocksLE(c, s', ov, dir);

      case SetQuantToClock(q, bq) =>
        var ocp := if bq then Some(s1.cp) else None;
        var t' := t.(quant_regs := AReg.set_reg(t.quant_regs, q, ocp, s1.clock), pc := t.pc + 1);
        var s' := s1.(active := [t'] + ac);
        assert 0 <= t.pc < |c|;
        assert ThreadClocksLE(t', s1.clock) by {
          RegsClocksLESet(t.quant_regs, q, ocp, s1.clock, s1.clock);
        }
        assert VmClocksLE(s') by {
          forall t2 | t2 in s'.active ensures ThreadClocksLE(t2, s'.clock) {
            if t2 == t' { assert ThreadClocksLE(t2, s'.clock); }
            else { assert t2 in s.active; ThreadClocksLEMono(t2, s.clock, s'.clock); }
          }
        }
        FAdvanceEpsilonClocksLE(c, s', ov, dir);

      case CheckOracle(l) =>
        assert 0 <= t.pc < |c|;
        if LOr.view_get_oracle(ov, s1.cp, l) {
          var t' := t.(pc := t.pc + 1, look_regs := AReg.set_reg(t.look_regs, l, Some(s1.cp), s1.clock));
          var s' := s1.(active := [t'] + ac);
          assert ThreadClocksLE(t', s1.clock) by {
            RegsClocksLESet(t.look_regs, l, Some(s1.cp), s1.clock, s1.clock);
          }
          assert VmClocksLE(s') by {
            forall t2 | t2 in s'.active ensures ThreadClocksLE(t2, s'.clock) {
              if t2 == t' { assert ThreadClocksLE(t2, s'.clock); }
              else { assert t2 in s.active; ThreadClocksLEMono(t2, s.clock, s'.clock); }
            }
          }
          FAdvanceEpsilonClocksLE(c, s', ov, dir);
        } else {
          var s' := s1.(active := ac);
          assert VmClocksLE(s') by {
            forall t2 | t2 in s'.active ensures ThreadClocksLE(t2, s'.clock) {
              assert t2 in s.active; ThreadClocksLEMono(t2, s.clock, s'.clock);
            }
          }
          FAdvanceEpsilonClocksLE(c, s', ov, dir);
        }

      case NegCheckOracle(l) =>
        assert 0 <= t.pc < |c|;
        if LOr.view_get_oracle(ov, s1.cp, l) {
          var s' := s1.(active := ac);
          assert VmClocksLE(s') by {
            forall t2 | t2 in s'.active ensures ThreadClocksLE(t2, s'.clock) {
              assert t2 in s.active; ThreadClocksLEMono(t2, s.clock, s'.clock);
            }
          }
          FAdvanceEpsilonClocksLE(c, s', ov, dir);
        } else {
          var s' := s1.(active := [t.(pc := t.pc + 1)] + ac);
          assert VmClocksLE(s') by {
            forall t2 | t2 in s'.active ensures ThreadClocksLE(t2, s'.clock) {
              if t2 == t.(pc := t.pc + 1) { assert ThreadClocksLE(t2, s'.clock); }
              else { assert t2 in s.active; ThreadClocksLEMono(t2, s.clock, s'.clock); }
            }
          }
          FAdvanceEpsilonClocksLE(c, s', ov, dir);
        }

      case WriteOracle(l) =>
        var s' := s1.(active := ac);
        assert 0 <= t.pc < |c|;
        assert VmClocksLE(s') by {
          forall t2 | t2 in s'.active ensures ThreadClocksLE(t2, s'.clock) {
            assert t2 in s.active; ThreadClocksLEMono(t2, s.clock, s'.clock);
          }
        }
        FAdvanceEpsilonClocksLE(c, s', LOr.view_set_oracle(ov, s1.cp, l), dir);

      case BeginLoop =>
        var s' := s1.(active := [t.(exit_allowed := false, pc := t.pc + 1)] + ac);
        assert 0 <= t.pc < |c|;
        assert VmClocksLE(s') by {
          forall t2 | t2 in s'.active ensures ThreadClocksLE(t2, s'.clock) {
            if t2 == t.(exit_allowed := false, pc := t.pc + 1) { assert ThreadClocksLE(t2, s'.clock); }
            else { assert t2 in s.active; ThreadClocksLEMono(t2, s.clock, s'.clock); }
          }
        }
        FAdvanceEpsilonClocksLE(c, s', ov, dir);

      case EndLoop =>
        assert 0 <= t.pc < |c|;
        if t.exit_allowed {
          var s' := s1.(active := [t.(pc := t.pc + 1)] + ac);
          assert VmClocksLE(s') by {
            forall t2 | t2 in s'.active ensures ThreadClocksLE(t2, s'.clock) {
              if t2 == t.(pc := t.pc + 1) { assert ThreadClocksLE(t2, s'.clock); }
              else { assert t2 in s.active; ThreadClocksLEMono(t2, s.clock, s'.clock); }
            }
          }
          FAdvanceEpsilonClocksLE(c, s', ov, dir);
        } else {
          var s' := s1.(active := ac);
          assert VmClocksLE(s') by {
            forall t2 | t2 in s'.active ensures ThreadClocksLE(t2, s'.clock) {
              assert t2 in s.active; ThreadClocksLEMono(t2, s.clock, s'.clock);
            }
          }
          FAdvanceEpsilonClocksLE(c, s', ov, dir);
        }

      case CheckNullable(qid) =>
        assert 0 <= t.pc < |c|;
        if LCdn.cdn_get(s1.cdn, qid) {
          var s' := s1.(active := [t.(pc := t.pc + 1)] + ac);
          assert VmClocksLE(s') by {
            forall t2 | t2 in s'.active ensures ThreadClocksLE(t2, s'.clock) {
              if t2 == t.(pc := t.pc + 1) { assert ThreadClocksLE(t2, s'.clock); }
              else { assert t2 in s.active; ThreadClocksLEMono(t2, s.clock, s'.clock); }
            }
          }
          FAdvanceEpsilonClocksLE(c, s', ov, dir);
        } else {
          var s' := s1.(active := ac);
          assert VmClocksLE(s') by {
            forall t2 | t2 in s'.active ensures ThreadClocksLE(t2, s'.clock) {
              assert t2 in s.active; ThreadClocksLEMono(t2, s.clock, s'.clock);
            }
          }
          FAdvanceEpsilonClocksLE(c, s', ov, dir);
        }

      case AnchorAssertion(a) =>
        assert 0 <= t.pc < |c|;
        if LAnc.is_satisfied(a, s1.context, dir) {
          var s' := s1.(active := [t.(pc := t.pc + 1)] + ac);
          assert VmClocksLE(s') by {
            forall t2 | t2 in s'.active ensures ThreadClocksLE(t2, s'.clock) {
              if t2 == t.(pc := t.pc + 1) { assert ThreadClocksLE(t2, s'.clock); }
              else { assert t2 in s.active; ThreadClocksLEMono(t2, s.clock, s'.clock); }
            }
          }
          FAdvanceEpsilonClocksLE(c, s', ov, dir);
        } else {
          var s' := s1.(active := ac);
          assert VmClocksLE(s') by {
            forall t2 | t2 in s'.active ensures ThreadClocksLE(t2, s'.clock) {
              assert t2 in s.active; ThreadClocksLEMono(t2, s.clock, s'.clock);
            }
          }
          FAdvanceEpsilonClocksLE(c, s', ov, dir);
        }

      case Fail =>
        var s' := s1.(active := ac);
        assert VmClocksLE(s') by {
          forall t2 | t2 in s'.active ensures ThreadClocksLE(t2, s'.clock) {
            assert t2 in s.active; ThreadClocksLEMono(t2, s.clock, s'.clock);
          }
        }
        FAdvanceEpsilonClocksLE(c, s', ov, dir);
    }
  }

  // FConsume moves matched blocked threads into the active list for the next
  // input position without touching the clock, so it preserves the bound.
  /** `FConsume` preserves `VmClocksLE` and leaves `s.clock` unchanged. */
  lemma FConsumeClocksLE(s: AI.VmState)
    requires VmClocksLE(s)
    ensures var r := AI.FConsume(s); r.clock == s.clock && VmClocksLE(r)
    decreases |s.blocked|
  {
    if |s.blocked| == 0 { return; }
    var t := s.blocked[0].0;
    var ce := s.blocked[0].1;
    var s1 := s.(blocked := s.blocked[1..]);
    assert s.blocked[0] in s.blocked;
    assert forall x | x in s1.blocked :: x in s.blocked;
    var s2 := if RC.is_accepted(s1.context.nextchar, ce)
              then s1.(active := [t.(exit_allowed := true, pc := t.pc + 1)] + s1.active)
              else s1;
    assert VmClocksLE(s2) by {
      assert s2.clock == s.clock;
      forall t2 | t2 in s2.active ensures ThreadClocksLE(t2, s2.clock) {
        if t2 == t.(exit_allowed := true, pc := t.pc + 1) {
          assert ThreadClocksLE(t, s.clock);      // t == s.blocked[0].0
        } else {
          assert t2 in s.active;
        }
      }
      forall tb | tb in s2.blocked ensures ThreadClocksLE(tb.0, s2.clock) {
        assert tb in s.blocked;
      }
      if s2.bestmatch.Some? { assert ThreadClocksLE(s2.bestmatch.value, s2.clock); }
    }
    FConsumeClocksLE(s2);
  }

  // init_regs stores -1 everywhere, so it meets any bound C >= -1.
  /** Fresh `AReg.init_regs` satisfies `RegsClocksLE` against any `C >= -1`. */
  lemma RegsClocksLEInit(n: int, C: int)
    requires C >= -1
    ensures RegsClocksLE(AReg.init_regs(n), C)
  {
    var r := AReg.init_regs(n);
    forall k ensures AI.get_idx(r.a_clk, k) <= C {
      if 0 <= k < |r.a_clk| { assert r.a_clk[k] == -1; }
    }
  }

  // The search-entry state (one thread, no blocked, no bestmatch) meets the
  // bound whenever its seed registers do -- the base case that grounds the
  // clock backbone at the start of a match attempt.
  /** `AI.FInitState` satisfies `VmClocksLE` whenever its seed registers do —
      the base case grounding the clock backbone at the start of a match. */
  lemma FInitStateClocksLE(c: RB.code, initcp: int, initcap: AReg.ARegs, initlook: AReg.ARegs,
                           initquant: AReg.ARegs, initclk: int, initctx: LAnc.char_context)
    requires RegsClocksLE(initcap, initclk) && RegsClocksLE(initlook, initclk)
          && RegsClocksLE(initquant, initclk)
    ensures VmClocksLE(AI.FInitState(c, initcp, initcap, initlook, initquant, initclk, initctx))
  {
    var s := AI.FInitState(c, initcp, initcap, initlook, initquant, initclk, initctx);
    assert s.active == [AI.init_thread(initcap, initlook, initquant)];
    forall t | t in s.active ensures ThreadClocksLE(t, s.clock) {
      assert t == AI.init_thread(initcap, initlook, initquant);
    }
  }

  // ===========================================================================
  // Register well-formedness backbone: register-array lengths are fixed for the
  // whole run and capture registers stay CapRegWf (values >= -1, unset clock =>
  // unset value). Discharges the length/range and consistency hypotheses of the
  // gm-effect discharge lemmas (GmOfLive{Open,Reset}Full, GmOfLiveClose).
  // ===========================================================================

  /** A thread's register arrays have the expected fixed lengths (`ncap`,
      `nlook`, `nquant`) and its capture registers are `PIV.CapRegWf`. */
  ghost predicate ThreadRegsWf(t: AI.Thread, ncap: int, nlook: int, nquant: int) {
    PIV.CapRegWf(t.capture_regs)
    && |t.capture_regs.a_cp| == ncap && |t.capture_regs.a_clk| == ncap
    && |t.look_regs.a_cp| == nlook && |t.look_regs.a_clk| == nlook
    && |t.quant_regs.a_cp| == nquant && |t.quant_regs.a_clk| == nquant
  }

  /** `ThreadRegsWf` for every active and blocked thread and for `bestmatch`. */
  ghost predicate VmRegsWf(s: AI.VmState, ncap: int, nlook: int, nquant: int) {
    (forall t | t in s.active :: ThreadRegsWf(t, ncap, nlook, nquant))
    && (forall tb | tb in s.blocked :: ThreadRegsWf(tb.0, ncap, nlook, nquant))
    && (s.bestmatch.Some? ==> ThreadRegsWf(s.bestmatch.value, ncap, nlook, nquant))
  }

  // set_reg never changes array lengths (in-range single update or identity).
  /** `AReg.set_reg` never changes a register array's `a_cp`/`a_clk` lengths. */
  lemma SetRegLens(r: AReg.ARegs, k: int, cp: Option<int>, clk: int)
    ensures |AReg.set_reg(r, k, cp, clk).a_cp| == |r.a_cp|
    ensures |AReg.set_reg(r, k, cp, clk).a_clk| == |r.a_clk|
  {}

  /** `FAdvanceEpsilon` preserves `VmRegsWf`, in lock-step with
      `FAdvanceEpsilonClocksLE`'s induction over the epsilon-closure fuel. */
  lemma FAdvanceEpsilonRegsWf(c: RB.code, s: AI.VmState, ov: LOr.OracleView, dir: LAnc.direction,
                              ncap: int, nlook: int, nquant: int)
    requires |s.processed.true_set| == RB.size(c) && |s.processed.false_set| == RB.size(c)
    requires s.cp >= 0 && s.clock >= 0
    requires VmRegsWf(s, ncap, nlook, nquant)
    ensures VmRegsWf(AI.FAdvanceEpsilon(c, s, ov, dir).0, ncap, nlook, nquant)
    decreases AI.unprocessed(s.processed), |s.active|
  {
    if |s.active| == 0 { return; }
    var t := s.active[0];
    var ac := s.active[1..];
    assert t in s.active;
    assert forall x | x in ac :: x in s.active;
    var i := RB.get_instr(c, t.pc);

    if AI.bpc_mem(s.processed, t.pc, t.exit_allowed) {
      FAdvanceEpsilonRegsWf(c, s.(active := ac), ov, dir, ncap, nlook, nquant);
      return;
    }

    var b0 := s.processed;
    var s1 := s.(clock := s.clock + 1, processed := AI.bpc_add(b0, t.pc, t.exit_allowed));
    assert AI.unprocessed(s1.processed) <= AI.unprocessed(b0)
        && (0 <= t.pc < RB.size(c) ==> AI.unprocessed(s1.processed) < AI.unprocessed(b0))
      by { AI.UnprocessedAdd(b0, t.pc, t.exit_allowed); }

    match i {
      case Consume(ce) =>
        var (nb, ni) := AI.add_thread(t, ce, s1.blocked, s1.isblocked);
        var s' := s1.(blocked := nb, isblocked := ni, active := ac);
        assert 0 <= t.pc < |c|;
        assert VmRegsWf(s', ncap, nlook, nquant) by {
          forall tb | tb in s'.blocked ensures ThreadRegsWf(tb.0, ncap, nlook, nquant) {
            assert tb == (t, ce) || tb in s.blocked;
          }
        }
        FAdvanceEpsilonRegsWf(c, s', ov, dir, ncap, nlook, nquant);

      case Accept =>
        // Returns (s1.(active := [], bestmatch := Some(t)), ov).
        assert ThreadRegsWf(t, ncap, nlook, nquant);

      case Jmp(x) =>
        var s' := s1.(active := [t.(pc := x)] + ac);
        assert 0 <= t.pc < |c|;
        assert VmRegsWf(s', ncap, nlook, nquant) by {
          forall t2 | t2 in s'.active ensures ThreadRegsWf(t2, ncap, nlook, nquant) {
            if t2 != t.(pc := x) { assert t2 in s.active; }
          }
        }
        FAdvanceEpsilonRegsWf(c, s', ov, dir, ncap, nlook, nquant);

      case Fork(x, y) =>
        var newt := AI.Thread(x, t.capture_regs, t.look_regs, t.quant_regs, t.exit_allowed);
        var s' := s1.(active := [newt, t.(pc := y)] + ac);
        assert 0 <= t.pc < |c|;
        assert VmRegsWf(s', ncap, nlook, nquant) by {
          forall t2 | t2 in s'.active ensures ThreadRegsWf(t2, ncap, nlook, nquant) {
            if t2 != newt && t2 != t.(pc := y) { assert t2 in s.active; }
          }
        }
        FAdvanceEpsilonRegsWf(c, s', ov, dir, ncap, nlook, nquant);

      case SetRegisterToCP(reg) =>
        var t' := t.(capture_regs := AReg.set_reg(t.capture_regs, reg, Some(s1.cp), s1.clock), pc := t.pc + 1);
        var s' := s1.(active := [t'] + ac);
        assert 0 <= t.pc < |c|;
        assert ThreadRegsWf(t', ncap, nlook, nquant) by {
          PIV.CapRegWfSet(t.capture_regs, reg, s1.cp, s1.clock);
          SetRegLens(t.capture_regs, reg, Some(s1.cp), s1.clock);
        }
        assert VmRegsWf(s', ncap, nlook, nquant) by {
          forall t2 | t2 in s'.active ensures ThreadRegsWf(t2, ncap, nlook, nquant) {
            if t2 != t' { assert t2 in s.active; }
          }
        }
        FAdvanceEpsilonRegsWf(c, s', ov, dir, ncap, nlook, nquant);

      case SetQuantToClock(q, bq) =>
        var ocp := if bq then Some(s1.cp) else None;
        var t' := t.(quant_regs := AReg.set_reg(t.quant_regs, q, ocp, s1.clock), pc := t.pc + 1);
        var s' := s1.(active := [t'] + ac);
        assert 0 <= t.pc < |c|;
        assert ThreadRegsWf(t', ncap, nlook, nquant) by {
          SetRegLens(t.quant_regs, q, ocp, s1.clock);
        }
        assert VmRegsWf(s', ncap, nlook, nquant) by {
          forall t2 | t2 in s'.active ensures ThreadRegsWf(t2, ncap, nlook, nquant) {
            if t2 != t' { assert t2 in s.active; }
          }
        }
        FAdvanceEpsilonRegsWf(c, s', ov, dir, ncap, nlook, nquant);

      case CheckOracle(l) =>
        assert 0 <= t.pc < |c|;
        if LOr.view_get_oracle(ov, s1.cp, l) {
          var t' := t.(pc := t.pc + 1, look_regs := AReg.set_reg(t.look_regs, l, Some(s1.cp), s1.clock));
          var s' := s1.(active := [t'] + ac);
          assert ThreadRegsWf(t', ncap, nlook, nquant) by {
            SetRegLens(t.look_regs, l, Some(s1.cp), s1.clock);
          }
          assert VmRegsWf(s', ncap, nlook, nquant) by {
            forall t2 | t2 in s'.active ensures ThreadRegsWf(t2, ncap, nlook, nquant) {
              if t2 != t' { assert t2 in s.active; }
            }
          }
          FAdvanceEpsilonRegsWf(c, s', ov, dir, ncap, nlook, nquant);
        } else {
          var s' := s1.(active := ac);
          assert VmRegsWf(s', ncap, nlook, nquant);
          FAdvanceEpsilonRegsWf(c, s', ov, dir, ncap, nlook, nquant);
        }

      case NegCheckOracle(l) =>
        assert 0 <= t.pc < |c|;
        if LOr.view_get_oracle(ov, s1.cp, l) {
          var s' := s1.(active := ac);
          assert VmRegsWf(s', ncap, nlook, nquant);
          FAdvanceEpsilonRegsWf(c, s', ov, dir, ncap, nlook, nquant);
        } else {
          var s' := s1.(active := [t.(pc := t.pc + 1)] + ac);
          assert VmRegsWf(s', ncap, nlook, nquant) by {
            forall t2 | t2 in s'.active ensures ThreadRegsWf(t2, ncap, nlook, nquant) {
              if t2 != t.(pc := t.pc + 1) { assert t2 in s.active; }
            }
          }
          FAdvanceEpsilonRegsWf(c, s', ov, dir, ncap, nlook, nquant);
        }

      case WriteOracle(l) =>
        var s' := s1.(active := ac);
        assert 0 <= t.pc < |c|;
        assert VmRegsWf(s', ncap, nlook, nquant);
        FAdvanceEpsilonRegsWf(c, s', LOr.view_set_oracle(ov, s1.cp, l), dir, ncap, nlook, nquant);

      case BeginLoop =>
        var s' := s1.(active := [t.(exit_allowed := false, pc := t.pc + 1)] + ac);
        assert 0 <= t.pc < |c|;
        assert VmRegsWf(s', ncap, nlook, nquant) by {
          forall t2 | t2 in s'.active ensures ThreadRegsWf(t2, ncap, nlook, nquant) {
            if t2 != t.(exit_allowed := false, pc := t.pc + 1) { assert t2 in s.active; }
          }
        }
        FAdvanceEpsilonRegsWf(c, s', ov, dir, ncap, nlook, nquant);

      case EndLoop =>
        assert 0 <= t.pc < |c|;
        if t.exit_allowed {
          var s' := s1.(active := [t.(pc := t.pc + 1)] + ac);
          assert VmRegsWf(s', ncap, nlook, nquant) by {
            forall t2 | t2 in s'.active ensures ThreadRegsWf(t2, ncap, nlook, nquant) {
              if t2 != t.(pc := t.pc + 1) { assert t2 in s.active; }
            }
          }
          FAdvanceEpsilonRegsWf(c, s', ov, dir, ncap, nlook, nquant);
        } else {
          var s' := s1.(active := ac);
          assert VmRegsWf(s', ncap, nlook, nquant);
          FAdvanceEpsilonRegsWf(c, s', ov, dir, ncap, nlook, nquant);
        }

      case CheckNullable(qid) =>
        assert 0 <= t.pc < |c|;
        if LCdn.cdn_get(s1.cdn, qid) {
          var s' := s1.(active := [t.(pc := t.pc + 1)] + ac);
          assert VmRegsWf(s', ncap, nlook, nquant) by {
            forall t2 | t2 in s'.active ensures ThreadRegsWf(t2, ncap, nlook, nquant) {
              if t2 != t.(pc := t.pc + 1) { assert t2 in s.active; }
            }
          }
          FAdvanceEpsilonRegsWf(c, s', ov, dir, ncap, nlook, nquant);
        } else {
          var s' := s1.(active := ac);
          assert VmRegsWf(s', ncap, nlook, nquant);
          FAdvanceEpsilonRegsWf(c, s', ov, dir, ncap, nlook, nquant);
        }

      case AnchorAssertion(a) =>
        assert 0 <= t.pc < |c|;
        if LAnc.is_satisfied(a, s1.context, dir) {
          var s' := s1.(active := [t.(pc := t.pc + 1)] + ac);
          assert VmRegsWf(s', ncap, nlook, nquant) by {
            forall t2 | t2 in s'.active ensures ThreadRegsWf(t2, ncap, nlook, nquant) {
              if t2 != t.(pc := t.pc + 1) { assert t2 in s.active; }
            }
          }
          FAdvanceEpsilonRegsWf(c, s', ov, dir, ncap, nlook, nquant);
        } else {
          var s' := s1.(active := ac);
          assert VmRegsWf(s', ncap, nlook, nquant);
          FAdvanceEpsilonRegsWf(c, s', ov, dir, ncap, nlook, nquant);
        }

      case Fail =>
        var s' := s1.(active := ac);
        assert VmRegsWf(s', ncap, nlook, nquant);
        FAdvanceEpsilonRegsWf(c, s', ov, dir, ncap, nlook, nquant);
    }
  }

  /** `FConsume` preserves `VmRegsWf`. */
  lemma FConsumeRegsWf(s: AI.VmState, ncap: int, nlook: int, nquant: int)
    requires VmRegsWf(s, ncap, nlook, nquant)
    ensures VmRegsWf(AI.FConsume(s), ncap, nlook, nquant)
    decreases |s.blocked|
  {
    if |s.blocked| == 0 { return; }
    var t := s.blocked[0].0;
    var ce := s.blocked[0].1;
    var s1 := s.(blocked := s.blocked[1..]);
    assert s.blocked[0] in s.blocked;
    assert forall x | x in s1.blocked :: x in s.blocked;
    var s2 := if RC.is_accepted(s1.context.nextchar, ce)
              then s1.(active := [t.(exit_allowed := true, pc := t.pc + 1)] + s1.active)
              else s1;
    assert VmRegsWf(s2, ncap, nlook, nquant) by {
      forall t2 | t2 in s2.active ensures ThreadRegsWf(t2, ncap, nlook, nquant) {
        if t2 != t.(exit_allowed := true, pc := t.pc + 1) { assert t2 in s.active; }
        else { assert ThreadRegsWf(t, ncap, nlook, nquant); }
      }
      forall tb | tb in s2.blocked ensures ThreadRegsWf(tb.0, ncap, nlook, nquant) {
        assert tb in s.blocked;
      }
    }
    FConsumeRegsWf(s2, ncap, nlook, nquant);
  }

  // Grounding at the search-entry state: fresh init_regs are CapRegWf with the
  // requested lengths (n >= 0).
  /** `AI.FInitState` over fresh `AReg.init_regs` satisfies `VmRegsWf` — the
      base case grounding the well-formedness backbone. */
  lemma FInitStateRegsWf(c: RB.code, initcp: int, ncap: int, nlook: int, nquant: int,
                         initclk: int, initctx: LAnc.char_context)
    requires ncap >= 0 && nlook >= 0 && nquant >= 0
    ensures VmRegsWf(AI.FInitState(c, initcp, AReg.init_regs(ncap), AReg.init_regs(nlook),
                                   AReg.init_regs(nquant), initclk, initctx),
                     ncap, nlook, nquant)
  {
    var s := AI.FInitState(c, initcp, AReg.init_regs(ncap), AReg.init_regs(nlook),
                           AReg.init_regs(nquant), initclk, initctx);
    PIV.CapRegWfInit(ncap);
    var th := AI.init_thread(AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant));
    assert ThreadRegsWf(th, ncap, nlook, nquant);
    assert s.active == [th];
    forall t | t in s.active ensures ThreadRegsWf(t, ncap, nlook, nquant) {
      assert t == th;
    }
  }

  // ===========================================================================
  // Capture-VALUE bound: every stored capture code point is <= the state's cp.
  // SetRegisterToCP stores exactly s.cp, and cp only advances between epsilon
  // phases -- so a group's recorded start position never exceeds the current
  // position. Discharges GMClose's `startIdx <= currIdx` guard (and rules out
  // its backward-lookaround swap branch) in the Close case of the simulation.
  // ===========================================================================

  /** Every capture value stored in `regs` (`a_cp`) is at most `B`. */
  ghost predicate RegsValsLE(regs: AReg.ARegs, B: int) {
    forall k :: AI.get_idx(regs.a_cp, k) <= B
  }

  /** `RegsValsLE` against the state's own `cp`, for every active and blocked
      thread's capture registers and for `bestmatch`. */
  ghost predicate VmCapsLE(s: AI.VmState) {
    (forall t | t in s.active :: RegsValsLE(t.capture_regs, s.cp))
    && (forall tb | tb in s.blocked :: RegsValsLE(tb.0.capture_regs, s.cp))
    && (s.bestmatch.Some? ==> RegsValsLE(s.bestmatch.value.capture_regs, s.cp))
  }

  /** `AReg.set_reg` preserves `RegsValsLE(_, B)` when the newly stored
      capture value is itself `<= B`. */
  lemma RegsValsLESet(regs: AReg.ARegs, k: int, cp: int, clk: int, B: int)
    requires RegsValsLE(regs, B) && cp <= B
    ensures RegsValsLE(AReg.set_reg(regs, k, Some(cp), clk), B)
  {
    var r' := AReg.set_reg(regs, k, Some(cp), clk);
    forall j ensures AI.get_idx(r'.a_cp, j) <= B {
      if 0 <= k < |regs.a_cp| && 0 <= k < |regs.a_clk| {
        if j == k { assert AI.get_idx(r'.a_cp, j) == cp; }
        else { assert AI.get_idx(r'.a_cp, j) == AI.get_idx(regs.a_cp, j); }
      } else {
        assert r' == regs;
      }
    }
  }

  /** `FAdvanceEpsilon` preserves `VmCapsLE`: `SetRegisterToCP` stores exactly
      `s.cp`, and `cp` only advances between epsilon phases, so a group's
      recorded position never exceeds the current one. */
  lemma FAdvanceEpsilonCapsLE(c: RB.code, s: AI.VmState, ov: LOr.OracleView, dir: LAnc.direction)
    requires |s.processed.true_set| == RB.size(c) && |s.processed.false_set| == RB.size(c)
    requires s.cp >= -1
    requires VmCapsLE(s)
    ensures VmCapsLE(AI.FAdvanceEpsilon(c, s, ov, dir).0)
    decreases AI.unprocessed(s.processed), |s.active|
  {
    if |s.active| == 0 { return; }
    var t := s.active[0];
    var ac := s.active[1..];
    assert t in s.active;
    assert forall x | x in ac :: x in s.active;
    var i := RB.get_instr(c, t.pc);

    if AI.bpc_mem(s.processed, t.pc, t.exit_allowed) {
      FAdvanceEpsilonCapsLE(c, s.(active := ac), ov, dir);
      return;
    }

    var b0 := s.processed;
    var s1 := s.(clock := s.clock + 1, processed := AI.bpc_add(b0, t.pc, t.exit_allowed));
    assert AI.unprocessed(s1.processed) <= AI.unprocessed(b0)
        && (0 <= t.pc < RB.size(c) ==> AI.unprocessed(s1.processed) < AI.unprocessed(b0))
      by { AI.UnprocessedAdd(b0, t.pc, t.exit_allowed); }
    assert s1.cp == s.cp;

    match i {
      case Consume(ce) =>
        var (nb, ni) := AI.add_thread(t, ce, s1.blocked, s1.isblocked);
        var s' := s1.(blocked := nb, isblocked := ni, active := ac);
        assert 0 <= t.pc < |c|;
        assert VmCapsLE(s') by {
          forall tb | tb in s'.blocked ensures RegsValsLE(tb.0.capture_regs, s'.cp) {
            assert tb == (t, ce) || tb in s.blocked;
          }
        }
        FAdvanceEpsilonCapsLE(c, s', ov, dir);

      case Accept =>
        assert RegsValsLE(t.capture_regs, s1.cp);

      case Jmp(x) =>
        var s' := s1.(active := [t.(pc := x)] + ac);
        assert 0 <= t.pc < |c|;
        assert VmCapsLE(s') by {
          forall t2 | t2 in s'.active ensures RegsValsLE(t2.capture_regs, s'.cp) {
            if t2 != t.(pc := x) { assert t2 in s.active; }
          }
        }
        FAdvanceEpsilonCapsLE(c, s', ov, dir);

      case Fork(x, y) =>
        var newt := AI.Thread(x, t.capture_regs, t.look_regs, t.quant_regs, t.exit_allowed);
        var s' := s1.(active := [newt, t.(pc := y)] + ac);
        assert 0 <= t.pc < |c|;
        assert VmCapsLE(s') by {
          forall t2 | t2 in s'.active ensures RegsValsLE(t2.capture_regs, s'.cp) {
            if t2 != newt && t2 != t.(pc := y) { assert t2 in s.active; }
          }
        }
        FAdvanceEpsilonCapsLE(c, s', ov, dir);

      case SetRegisterToCP(reg) =>
        var t' := t.(capture_regs := AReg.set_reg(t.capture_regs, reg, Some(s1.cp), s1.clock), pc := t.pc + 1);
        var s' := s1.(active := [t'] + ac);
        assert 0 <= t.pc < |c|;
        assert RegsValsLE(t'.capture_regs, s1.cp) by {
          RegsValsLESet(t.capture_regs, reg, s1.cp, s1.clock, s1.cp);
        }
        assert VmCapsLE(s') by {
          forall t2 | t2 in s'.active ensures RegsValsLE(t2.capture_regs, s'.cp) {
            if t2 != t' { assert t2 in s.active; }
          }
        }
        FAdvanceEpsilonCapsLE(c, s', ov, dir);

      case SetQuantToClock(q, bq) =>
        var ocp := if bq then Some(s1.cp) else None;
        var t' := t.(quant_regs := AReg.set_reg(t.quant_regs, q, ocp, s1.clock), pc := t.pc + 1);
        var s' := s1.(active := [t'] + ac);
        assert 0 <= t.pc < |c|;
        assert VmCapsLE(s') by {
          forall t2 | t2 in s'.active ensures RegsValsLE(t2.capture_regs, s'.cp) {
            if t2 != t' { assert t2 in s.active; }
          }
        }
        FAdvanceEpsilonCapsLE(c, s', ov, dir);

      case CheckOracle(l) =>
        assert 0 <= t.pc < |c|;
        if LOr.view_get_oracle(ov, s1.cp, l) {
          var t' := t.(pc := t.pc + 1, look_regs := AReg.set_reg(t.look_regs, l, Some(s1.cp), s1.clock));
          var s' := s1.(active := [t'] + ac);
          assert VmCapsLE(s') by {
            forall t2 | t2 in s'.active ensures RegsValsLE(t2.capture_regs, s'.cp) {
              if t2 != t' { assert t2 in s.active; }
            }
          }
          FAdvanceEpsilonCapsLE(c, s', ov, dir);
        } else {
          var s' := s1.(active := ac);
          assert VmCapsLE(s');
          FAdvanceEpsilonCapsLE(c, s', ov, dir);
        }

      case NegCheckOracle(l) =>
        assert 0 <= t.pc < |c|;
        if LOr.view_get_oracle(ov, s1.cp, l) {
          var s' := s1.(active := ac);
          assert VmCapsLE(s');
          FAdvanceEpsilonCapsLE(c, s', ov, dir);
        } else {
          var s' := s1.(active := [t.(pc := t.pc + 1)] + ac);
          assert VmCapsLE(s') by {
            forall t2 | t2 in s'.active ensures RegsValsLE(t2.capture_regs, s'.cp) {
              if t2 != t.(pc := t.pc + 1) { assert t2 in s.active; }
            }
          }
          FAdvanceEpsilonCapsLE(c, s', ov, dir);
        }

      case WriteOracle(l) =>
        var s' := s1.(active := ac);
        assert 0 <= t.pc < |c|;
        assert VmCapsLE(s');
        FAdvanceEpsilonCapsLE(c, s', LOr.view_set_oracle(ov, s1.cp, l), dir);

      case BeginLoop =>
        var s' := s1.(active := [t.(exit_allowed := false, pc := t.pc + 1)] + ac);
        assert 0 <= t.pc < |c|;
        assert VmCapsLE(s') by {
          forall t2 | t2 in s'.active ensures RegsValsLE(t2.capture_regs, s'.cp) {
            if t2 != t.(exit_allowed := false, pc := t.pc + 1) { assert t2 in s.active; }
          }
        }
        FAdvanceEpsilonCapsLE(c, s', ov, dir);

      case EndLoop =>
        assert 0 <= t.pc < |c|;
        if t.exit_allowed {
          var s' := s1.(active := [t.(pc := t.pc + 1)] + ac);
          assert VmCapsLE(s') by {
            forall t2 | t2 in s'.active ensures RegsValsLE(t2.capture_regs, s'.cp) {
              if t2 != t.(pc := t.pc + 1) { assert t2 in s.active; }
            }
          }
          FAdvanceEpsilonCapsLE(c, s', ov, dir);
        } else {
          var s' := s1.(active := ac);
          assert VmCapsLE(s');
          FAdvanceEpsilonCapsLE(c, s', ov, dir);
        }

      case CheckNullable(qid) =>
        assert 0 <= t.pc < |c|;
        if LCdn.cdn_get(s1.cdn, qid) {
          var s' := s1.(active := [t.(pc := t.pc + 1)] + ac);
          assert VmCapsLE(s') by {
            forall t2 | t2 in s'.active ensures RegsValsLE(t2.capture_regs, s'.cp) {
              if t2 != t.(pc := t.pc + 1) { assert t2 in s.active; }
            }
          }
          FAdvanceEpsilonCapsLE(c, s', ov, dir);
        } else {
          var s' := s1.(active := ac);
          assert VmCapsLE(s');
          FAdvanceEpsilonCapsLE(c, s', ov, dir);
        }

      case AnchorAssertion(a) =>
        assert 0 <= t.pc < |c|;
        if LAnc.is_satisfied(a, s1.context, dir) {
          var s' := s1.(active := [t.(pc := t.pc + 1)] + ac);
          assert VmCapsLE(s') by {
            forall t2 | t2 in s'.active ensures RegsValsLE(t2.capture_regs, s'.cp) {
              if t2 != t.(pc := t.pc + 1) { assert t2 in s.active; }
            }
          }
          FAdvanceEpsilonCapsLE(c, s', ov, dir);
        } else {
          var s' := s1.(active := ac);
          assert VmCapsLE(s');
          FAdvanceEpsilonCapsLE(c, s', ov, dir);
        }

      case Fail =>
        var s' := s1.(active := ac);
        assert VmCapsLE(s');
        FAdvanceEpsilonCapsLE(c, s', ov, dir);
    }
  }

  /** `FConsume` preserves `VmCapsLE`. */
  lemma FConsumeCapsLE(s: AI.VmState)
    requires VmCapsLE(s)
    ensures VmCapsLE(AI.FConsume(s))
    decreases |s.blocked|
  {
    if |s.blocked| == 0 { return; }
    var t := s.blocked[0].0;
    var ce := s.blocked[0].1;
    var s1 := s.(blocked := s.blocked[1..]);
    assert s.blocked[0] in s.blocked;
    assert forall x | x in s1.blocked :: x in s.blocked;
    var s2 := if RC.is_accepted(s1.context.nextchar, ce)
              then s1.(active := [t.(exit_allowed := true, pc := t.pc + 1)] + s1.active)
              else s1;
    assert VmCapsLE(s2) by {
      forall t2 | t2 in s2.active ensures RegsValsLE(t2.capture_regs, s2.cp) {
        if t2 != t.(exit_allowed := true, pc := t.pc + 1) { assert t2 in s.active; }
        else { assert RegsValsLE(t.capture_regs, s.cp); }
      }
      forall tb | tb in s2.blocked ensures RegsValsLE(tb.0.capture_regs, s2.cp) {
        assert tb in s.blocked;
      }
    }
    FConsumeCapsLE(s2);
  }

  // Advancing cp (FFindMatch's per-position increment) only weakens the bound.
  /** Bumping a state's `cp` upward (with everything else unchanged) preserves
      `VmCapsLE` — the per-position increment `FFindMatch` performs. */
  lemma VmCapsLEAdvance(s: AI.VmState, s': AI.VmState)
    requires VmCapsLE(s)
    requires s'.cp >= s.cp
    requires s'.active == s.active && s'.blocked == s.blocked && s'.bestmatch == s.bestmatch
    ensures VmCapsLE(s')
  {}

  /** `AI.FInitState` over fresh `AReg.init_regs` satisfies `VmCapsLE` — the
      base case grounding the capture-value bound. */
  lemma FInitStateCapsLE(c: RB.code, initcp: int, ncap: int, nlook: int, nquant: int,
                         initclk: int, initctx: LAnc.char_context)
    requires initcp >= -1
    ensures VmCapsLE(AI.FInitState(c, initcp, AReg.init_regs(ncap), AReg.init_regs(nlook),
                                   AReg.init_regs(nquant), initclk, initctx))
  {
    var s := AI.FInitState(c, initcp, AReg.init_regs(ncap), AReg.init_regs(nlook),
                           AReg.init_regs(nquant), initclk, initctx);
    var th := AI.init_thread(AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant));
    assert RegsValsLE(th.capture_regs, initcp) by {
      var r := AReg.init_regs(ncap);
      forall k ensures AI.get_idx(r.a_cp, k) <= initcp {
        if 0 <= k < |r.a_cp| { assert r.a_cp[k] == -1; }
      }
    }
    assert s.active == [th];
    forall t | t in s.active ensures RegsValsLE(t.capture_regs, s.cp) {
      assert t == th;
    }
  }
}
