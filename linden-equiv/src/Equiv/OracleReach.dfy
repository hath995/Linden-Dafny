// Lookaround campaign (L1), oracle theorem part C2: the configuration graph
// of a build sweep.
//
// For classified build code (no oracle reads, no CheckNullable — see
// CompileToWriteClassified), an executing thread's CONTROL FLOW depends only
// on (pc, exit_allowed, cp): registers are written but never read, and every
// branch tests either the instruction payload, the exit flag, the anchor
// context at cp, or the consumed character. So the run explores exactly the
// reachable part of a register-free configuration graph, and the Pike
// processed-set dedup — which drops duplicate (pc, exit_allowed) threads,
// losing only their registers — preserves reachability.
//
// ReachF is that graph's reachability predicate for a FORWARD run started at
// pc 0 (the shape of every L1 lookbehind build pass: FBuildLids runs
// compile_to_write(lazy_prefix(body), lid) forward from init_cp = 0). The
// oracle-correctness characterization to be proved against it:
//
//   view_get_oracle(ov', cp, lid) == view_get_oracle(ov, cp, lid)
//     || exists pc, eb :: ReachF(c, str, 0, pc, eb, cp)
//                         && get_instr(c, pc) == WriteOracle(lid)
//
// (soundness: every write comes from a live thread, whose config is
// reachable; completeness: the sweep processes every reachable config —
// the Pike worklist argument at existence level, next up).
include "OracleSweep.dfy"

/** The register-free configuration graph of a (Forward) build sweep:
    epsilon and consume edges over configurations `(pc, exit_allowed, cp)`,
    and its reachability predicate `ReachF`. */
module LindenElkOracleReach {
  import opened Std.Wrappers
  import AI = ArrayInterp
  import RB = Bytecode
  import LOr = Oracle
  import LAnc = Anchors
  import LCdn = Cdn
  import AReg = Array_Regs
  import RC = Charclasses
  import OS = LindenElkOracleSweep

  /** The character context a Forward run holds at position `cp`. */
  function CtxAt(str: string, cp: int): LAnc.char_context {
    AI.cp_context(cp, str, LAnc.Forward)
  }

  /** One epsilon edge at position `cp`: configuration `(pc, eb)` steps to
      `(pc2, eb2)` without consuming. Mirrors `FAdvanceEpsilon`'s cases for
      classified code; oracle and cdn instructions have no edges (the sweep
      lemmas exclude them), and `Accept`/`WriteOracle`/`Fail`/failed checks
      are terminal. */
  ghost predicate EpsEdge(c: RB.code, str: string, cp: int, pc: nat, eb: bool, pc2: nat, eb2: bool) {
    match RB.get_instr(c, pc)
    case Jmp(x) => x >= 0 && pc2 == x && eb2 == eb
    case Fork(x, y) => ((x >= 0 && pc2 == x) || (y >= 0 && pc2 == y)) && eb2 == eb
    case SetRegisterToCP(_) => pc2 == pc + 1 && eb2 == eb
    case SetQuantToClock(_, _) => pc2 == pc + 1 && eb2 == eb
    case BeginLoop => pc2 == pc + 1 && eb2 == false
    case EndLoop => eb && pc2 == pc + 1 && eb2 == eb
    case AnchorAssertion(a) =>
      LAnc.is_satisfied(a, CtxAt(str, cp), LAnc.Forward) && pc2 == pc + 1 && eb2 == eb
    case _ => false
  }

  /** The consume edge out of `(pc, eb)` at position `cp`: the blocked thread
      survives iff the character at `cp` meets its expectation; its successor
      is `(pc + 1, true)` at `cp + 1` (consuming re-arms the exit flag). */
  ghost predicate ConsumeEdge(c: RB.code, str: string, cp: int, pc: nat) {
    match RB.get_instr(c, pc)
    case Consume(ce) => RC.is_accepted(AI.get_char(str, cp), ce)
    case _ => false
  }

  /** Reachable configurations of the Forward run of `c` over `str` started
      at pc 0, position `cp0`, with the initial thread's cleared exit flag
      (`init_thread` starts `exit_allowed == false`). */
  least predicate ReachF(c: RB.code, str: string, cp0: int, pc: nat, eb: bool, cp: int) {
    (pc == 0 && eb == false && cp == cp0)
    || (exists pc1: nat, eb1: bool ::
          ReachF(c, str, cp0, pc1, eb1, cp) && EpsEdge(c, str, cp, pc1, eb1, pc, eb))
    || (eb == true && pc > 0
        && (ReachF(c, str, cp0, pc - 1, false, cp - 1) || ReachF(c, str, cp0, pc - 1, true, cp - 1))
        && ConsumeEdge(c, str, cp - 1, pc - 1))
  }

  /** The target of the sweep characterization: some reachable configuration
      at `cp` sits on a `WriteOracle(lid)` — the abstract statement of "the
      build sweep records a bit at `cp`". */
  ghost predicate ReachesWrite(c: RB.code, str: string, cp0: int, lid: int, cp: int) {
    exists pc: nat, eb: bool ::
      ReachF(c, str, cp0, pc, eb, cp) && RB.get_instr(c, pc) == RB.WriteOracle(lid)
  }

  /** Reachability only visits positions at or after the start (Forward run) —
      a sanity bound used to keep cp arithmetic honest downstream. */
  least lemma ReachFGeStart(c: RB.code, str: string, cp0: int, pc: nat, eb: bool, cp: int)
    requires ReachF(c, str, cp0, pc, eb, cp)
    ensures cp >= cp0
  {
  }

  // ===========================================================================
  // Soundness: every bit the sweep writes comes from a reachable WriteOracle
  // ===========================================================================

  /** Every active thread's configuration is reachable (threads at negative
      pcs read `Fail` and die without stepping, so they carry no claim). */
  ghost predicate ActiveOk(c: RB.code, str: string, cp0: int, ts: seq<AI.Thread>, cp: int) {
    forall j :: 0 <= j < |ts| ==>
      (ts[j].pc >= 0 ==> ReachF(c, str, cp0, ts[j].pc, ts[j].exit_allowed, cp))
  }

  /** Every blocked entry sits, reachably, on the `Consume` it recorded —
      exactly what the consume edge needs. */
  ghost predicate BlockedOk(c: RB.code, str: string, cp0: int, bs: seq<(AI.Thread, RC.char_expectation)>, cp: int) {
    forall j :: 0 <= j < |bs| ==>
      bs[j].0.pc >= 0
      && ReachF(c, str, cp0, bs[j].0.pc, bs[j].0.exit_allowed, cp)
      && RB.get_instr(c, bs[j].0.pc) == RB.Consume(bs[j].1)
  }

  /** One epsilon closure over classified code: the blocked frontier stays
      config-sound, untouched columns stay untouched, and every bit added in
      column `lid` is testified by a reachable `WriteOracle(lid)` at the
      closure's position. */
  lemma AdvanceReachSound(c: RB.code, str: string, cp0: int, s: AI.VmState, ov: LOr.OracleView, lid: int)
    requires |s.processed.true_set| == RB.size(c) && |s.processed.false_set| == RB.size(c)
    requires OS.NoOracleReads(c) && OS.NoCheckNullable(c) && OS.WritesOnlyLid(c, lid)
    requires s.context == CtxAt(str, s.cp)
    requires ActiveOk(c, str, cp0, s.active, s.cp)
    requires BlockedOk(c, str, cp0, s.blocked, s.cp)
    ensures var (s', ov') := AI.FAdvanceEpsilon(c, s, ov, LAnc.Forward);
      s'.active == []
      && BlockedOk(c, str, cp0, s'.blocked, s.cp)
      && (forall cp2: int :: LOr.view_get_oracle(ov', cp2, lid) ==>
            LOr.view_get_oracle(ov, cp2, lid) || ReachesWrite(c, str, cp0, lid, cp2))
      && (forall cp2: int, l2: int :: l2 != lid ==>
            LOr.view_get_oracle(ov', cp2, l2) == LOr.view_get_oracle(ov, cp2, l2))
    decreases AI.unprocessed(s.processed), |s.active|
  {
    if |s.active| == 0 { return; }
    var t := s.active[0];
    var ac := s.active[1..];
    var i := RB.get_instr(c, t.pc);
    if AI.bpc_mem(s.processed, t.pc, t.exit_allowed) {
      AdvanceReachSound(c, str, cp0, s.(active := ac), ov, lid);
      return;
    }
    var b0 := s.processed;
    var s1 := s.(clock := s.clock + 1, processed := AI.bpc_add(b0, t.pc, t.exit_allowed));
    AI.UnprocessedAdd(b0, t.pc, t.exit_allowed);
    // in every case below where `i` names a real instruction, t.pc is in
    // range (out-of-range fetch reads Fail), so ReachF(t.pc, ...) is on hand
    match i
    case Consume(ce) =>
      var (nb, ni) := AI.add_thread(t, ce, s1.blocked, s1.isblocked);
      assert BlockedOk(c, str, cp0, nb, s.cp);
      AdvanceReachSound(c, str, cp0, s1.(blocked := nb, isblocked := ni, active := ac), ov, lid);
    case Accept =>
    case Jmp(x) =>
      assert x >= 0 ==> ReachF(c, str, cp0, x, t.exit_allowed, s.cp) by {
        if x >= 0 { assert EpsEdge(c, str, s.cp, t.pc, t.exit_allowed, x, t.exit_allowed); }
      }
      AdvanceReachSound(c, str, cp0, s1.(active := [t.(pc := x)] + ac), ov, lid);
    case Fork(x, y) =>
      var newt := AI.Thread(x, t.capture_regs, t.look_regs, t.quant_regs, t.exit_allowed);
      assert x >= 0 ==> ReachF(c, str, cp0, x, t.exit_allowed, s.cp) by {
        if x >= 0 { assert EpsEdge(c, str, s.cp, t.pc, t.exit_allowed, x, t.exit_allowed); }
      }
      assert y >= 0 ==> ReachF(c, str, cp0, y, t.exit_allowed, s.cp) by {
        if y >= 0 { assert EpsEdge(c, str, s.cp, t.pc, t.exit_allowed, y, t.exit_allowed); }
      }
      AdvanceReachSound(c, str, cp0, s1.(active := [newt, t.(pc := y)] + ac), ov, lid);
    case SetRegisterToCP(reg) =>
      var t' := t.(capture_regs := AReg.set_reg(t.capture_regs, reg, Some(s1.cp), s1.clock), pc := t.pc + 1);
      assert EpsEdge(c, str, s.cp, t.pc, t.exit_allowed, t.pc + 1, t.exit_allowed);
      AdvanceReachSound(c, str, cp0, s1.(active := [t'] + ac), ov, lid);
    case SetQuantToClock(q, b) =>
      var ocp := if b then Some(s1.cp) else None;
      var t' := t.(quant_regs := AReg.set_reg(t.quant_regs, q, ocp, s1.clock), pc := t.pc + 1);
      assert EpsEdge(c, str, s.cp, t.pc, t.exit_allowed, t.pc + 1, t.exit_allowed);
      AdvanceReachSound(c, str, cp0, s1.(active := [t'] + ac), ov, lid);
    case CheckOracle(l) =>
      assert 0 <= t.pc < |c| && c[t.pc].CheckOracle?;
      assert false;
    case NegCheckOracle(l) =>
      assert 0 <= t.pc < |c| && c[t.pc].NegCheckOracle?;
      assert false;
    case WriteOracle(l) =>
      assert 0 <= t.pc < |c| && c[t.pc] == RB.WriteOracle(l);
      assert l == lid;
      assert ReachesWrite(c, str, cp0, lid, s.cp) by {
        assert ReachF(c, str, cp0, t.pc, t.exit_allowed, s.cp)
            && RB.get_instr(c, t.pc) == RB.WriteOracle(lid);
      }
      OS.ViewSetFacts(ov, s1.cp, l);
      AdvanceReachSound(c, str, cp0, s1.(active := ac), LOr.view_set_oracle(ov, s1.cp, l), lid);
    case BeginLoop =>
      assert EpsEdge(c, str, s.cp, t.pc, t.exit_allowed, t.pc + 1, false);
      AdvanceReachSound(c, str, cp0, s1.(active := [t.(exit_allowed := false, pc := t.pc + 1)] + ac), ov, lid);
    case EndLoop =>
      if t.exit_allowed {
        assert EpsEdge(c, str, s.cp, t.pc, t.exit_allowed, t.pc + 1, t.exit_allowed);
        AdvanceReachSound(c, str, cp0, s1.(active := [t.(pc := t.pc + 1)] + ac), ov, lid);
      } else {
        AdvanceReachSound(c, str, cp0, s1.(active := ac), ov, lid);
      }
    case CheckNullable(qid) =>
      assert 0 <= t.pc < |c| && c[t.pc].CheckNullable?;
      assert false;
    case AnchorAssertion(a) =>
      if LAnc.is_satisfied(a, s1.context, LAnc.Forward) {
        assert EpsEdge(c, str, s.cp, t.pc, t.exit_allowed, t.pc + 1, t.exit_allowed);
        AdvanceReachSound(c, str, cp0, s1.(active := [t.(pc := t.pc + 1)] + ac), ov, lid);
      } else {
        AdvanceReachSound(c, str, cp0, s1.(active := ac), ov, lid);
      }
    case Fail =>
      AdvanceReachSound(c, str, cp0, s1.(active := ac), ov, lid);
  }

  /** `FConsume` reactivates only blocked threads whose `Consume` accepts the
      character at `cp` — exactly the consume edge, so the new active list is
      config-sound at `cp + 1`. */
  lemma FConsumeReach(c: RB.code, str: string, cp0: int, s: AI.VmState)
    requires s.context.nextchar == AI.get_char(str, s.cp)
    requires BlockedOk(c, str, cp0, s.blocked, s.cp)
    requires ActiveOk(c, str, cp0, s.active, s.cp + 1)
    ensures AI.FConsume(s).blocked == []
    ensures ActiveOk(c, str, cp0, AI.FConsume(s).active, s.cp + 1)
    decreases |s.blocked|
  {
    if |s.blocked| == 0 { return; }
    var t := s.blocked[0].0;
    var ce := s.blocked[0].1;
    var s1 := s.(blocked := s.blocked[1..]);
    if RC.is_accepted(s1.context.nextchar, ce) {
      assert ConsumeEdge(c, str, s.cp, t.pc);
      assert ReachF(c, str, cp0, t.pc + 1, true, s.cp + 1);
      FConsumeReach(c, str, cp0, s1.(active := [t.(exit_allowed := true, pc := t.pc + 1)] + s1.active));
    } else {
      FConsumeReach(c, str, cp0, s1);
    }
  }

  /** A whole classified Forward run: untouched columns stay untouched, and
      every bit it adds in column `lid` is testified by a reachable
      `WriteOracle(lid)` at the recorded position. */
  lemma FindMatchReachSound(c: RB.code, str: string, cp0: int, s: AI.VmState, ov: LOr.OracleView,
                            cdn: LCdn.cdns, lid: int)
    requires |s.processed.true_set| == RB.size(c) && |s.processed.false_set| == RB.size(c)
    requires s.context.nextchar == AI.get_char(str, s.cp)
    requires OS.NoOracleReads(c) && OS.NoCheckNullable(c) && OS.WritesOnlyLid(c, lid)
    requires s.context == CtxAt(str, s.cp)
    requires ActiveOk(c, str, cp0, s.active, s.cp)
    requires BlockedOk(c, str, cp0, s.blocked, s.cp)
    ensures var (_, ov') := AI.FFindMatch(c, str, s, ov, LAnc.Forward, cdn);
      (forall cp2: int :: LOr.view_get_oracle(ov', cp2, lid) ==>
         LOr.view_get_oracle(ov, cp2, lid) || ReachesWrite(c, str, cp0, lid, cp2))
      && (forall cp2: int, l2: int :: l2 != lid ==>
            LOr.view_get_oracle(ov', cp2, l2) == LOr.view_get_oracle(ov, cp2, l2))
    decreases |str| - s.cp
  {
    var s0 := s.(cdn := LCdn.build_cdn_v(cdn, s.cp, ov, s.context, LAnc.Forward));
    var (s1, ov1) := AI.FAdvanceEpsilon(c, s0, ov, LAnc.Forward);
    AdvanceReachSound(c, str, cp0, s0, ov, lid);
    if |s1.blocked| == 0 { return; }
    match s1.context.nextchar
    case None =>
    case Some(_) =>
      var s2 := AI.FConsume(s1);
      FConsumeReach(c, str, cp0, s1);
      var s3 := s2.(processed := AI.init_bpcset(RB.size(c)), isblocked := AI.init_pcset(RB.size(c)),
                    cdn := LCdn.init_cdn(), cp := AI.incr_cp(s2.cp, LAnc.Forward));
      var newchar := AI.get_char(str, s3.cp - AI.cp_offset(LAnc.Forward));
      var s4 := s3.(context := LAnc.update_context(s3.context, newchar));
      assert s4.context == CtxAt(str, s4.cp);
      assert BlockedOk(c, str, cp0, s4.blocked, s4.cp);
      FindMatchReachSound(c, str, cp0, s4, ov1, cdn, lid);
  }
}
