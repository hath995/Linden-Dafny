// L4 depth-k, nested ORACLE ENTRY, rung V4: the ACCEPT-RUN characterization.
//
//   FFindMatch(compile_to_bytecode(body), str, init@cp, ov, Forward, cdn).0.Some?
//     <==>  exists j :: MatchesV(body, str, ov, cp, j)
//
// — the engine-side truth of a NESTED body run against a partial view, the leg
// that lets the (already-green) sim tower's tree correspondence meet the V1/V2
// span bridges. Two halves:
//
//   SOUNDNESS  (result Some ==> a V-reachable Accept ==> a MatchesV span):
//   clone of `AdvanceReachSoundV`/`FindMatchReachSoundV` with the reference
//   view = the running view (nested body code has NO WriteOracle, so the view
//   never changes — `NoOracleWrites`), and the `Accept` case producing the
//   reachable-Accept witness instead of being dead.
//
//   COMPLETENESS (a MatchesV span ==> result Some): `MatchesVToPath` (cp0
//   generalized) makes the Accept config V-reachable; the run-completeness
//   clone (`AdvanceAcceptCompleteV`/`FindMatchAcceptCompleteV`) shows a
//   None-result run processes EVERY reachable config — the `NoAccept`
//   hypothesis of the sweep version replaced by the run's own None result
//   (a closure that returns `bestmatch == None` never met an Accept, so it
//   never early-exited). Reuses `ClosureInvV` and its step lemmas at floor
//   `k == 0` (gate lids are >= 1; the write conjunct is vacuous).
//
// The single-block program invariant `BodyProgInvV` (entry fixed at `cp`,
// no dot-star zone) converts reachable Accepts back to `MatchesV` spans.

/** V4 of the nested oracle entry: the Accept-run characterization
    `AcceptRunCharacterizationV`. */
module LindenElkOracleAcceptV {
  import opened Std.Wrappers
  import R = RegElkRegex
  import RB = Bytecode
  import CP = Compiler
  import AI = ArrayInterp
  import AReg = Array_Regs
  import LOr = Oracle
  import LAnc = Anchors
  import RC = Charclasses
  import LCdn = Cdn
  import T = LindenElkTranslate
  import NR = LindenElkNfaRep
  import LTB = LindenElkLookTables
  import ORc = LindenElkOracleReach
  import OS = LindenElkOracleSweep
  import OB = LindenElkOracleBridge
  import OBV = LindenElkOracleBridgeV
  import ODV = LindenElkOracleDecompV

  // ===========================================================================
  // Classification
  // ===========================================================================

  /** No `WriteOracle` anywhere in `c` — a compiled nested BODY (search form)
      satisfies this: gates read, nothing writes. */
  ghost predicate NoOracleWrites(c: RB.code) {
    forall pc :: 0 <= pc < |c| ==> !c[pc].WriteOracle?
  }

  /** Some Accept instruction is V-reachable at position `cp`. */
  ghost predicate AcceptReachableAtV(c: RB.code, str: string, ov: LOr.OracleView, cp0: int, cp: int) {
    exists pc: nat, eb: bool ::
      ORc.ReachFV(c, str, ov, cp0, pc, eb, cp) && RB.get_instr(c, pc).Accept?
  }

  lemma AcceptReachableAtVIntro(c: RB.code, str: string, ov: LOr.OracleView, cp0: int, cp: int, pc: nat, eb: bool)
    requires ORc.ReachFV(c, str, ov, cp0, pc, eb, cp) && RB.get_instr(c, pc).Accept?
    ensures AcceptReachableAtV(c, str, ov, cp0, cp)
  {
  }

  lemma AcceptReachableAtVInv(c: RB.code, str: string, ov: LOr.OracleView, cp0: int, cp: int)
    returns (pc: nat, eb: bool)
    requires AcceptReachableAtV(c, str, ov, cp0, cp)
    ensures ORc.ReachFV(c, str, ov, cp0, pc, eb, cp) && RB.get_instr(c, pc).Accept?
  {
    pc, eb :| ORc.ReachFV(c, str, ov, cp0, pc, eb, cp) && RB.get_instr(c, pc).Accept?;
  }

  // ===========================================================================
  // SOUNDNESS: a Some result testifies a V-reachable Accept
  // ===========================================================================

  /** One closure: if it produces a match that was not already there, the
      accepting thread's config is V-reachable at this position — and the
      view never changes (`NoOracleWrites`). */
  lemma AdvanceAcceptSoundV(c: RB.code, str: string, cp0: int, s: AI.VmState, ov: LOr.OracleView)
    requires |s.processed.true_set| == RB.size(c) && |s.processed.false_set| == RB.size(c)
    requires OS.NoCheckNullable(c) && NoOracleWrites(c)
    requires s.context == ORc.CtxAt(str, s.cp)
    requires ORc.ActiveOkV(c, str, ov, cp0, s.active, s.cp)
    requires ORc.BlockedOkV(c, str, ov, cp0, s.blocked, s.cp)
    ensures var (s', ov') := AI.FAdvanceEpsilon(c, s, ov, LAnc.Forward);
            ov' == ov
            && s'.active == []
            && ORc.BlockedOkV(c, str, ov, cp0, s'.blocked, s.cp)
            && (s'.bestmatch.Some? ==> s.bestmatch.Some? || AcceptReachableAtV(c, str, ov, cp0, s.cp))
    decreases AI.unprocessed(s.processed), |s.active|
  {
    if |s.active| == 0 { return; }
    var t := s.active[0];
    var ac := s.active[1..];
    var i := RB.get_instr(c, t.pc);
    if AI.bpc_mem(s.processed, t.pc, t.exit_allowed) {
      AdvanceAcceptSoundV(c, str, cp0, s.(active := ac), ov);
      return;
    }
    var b0 := s.processed;
    var s1 := s.(clock := s.clock + 1, processed := AI.bpc_add(b0, t.pc, t.exit_allowed));
    AI.UnprocessedAdd(b0, t.pc, t.exit_allowed);
    match i
    case Consume(ce) =>
      var (nb, ni) := AI.add_thread(t, ce, s1.blocked, s1.isblocked);
      assert ORc.BlockedOkV(c, str, ov, cp0, nb, s.cp);
      AdvanceAcceptSoundV(c, str, cp0, s1.(blocked := nb, isblocked := ni, active := ac), ov);
    case Accept =>
      // the accepting thread is in range (else get_instr would be Fail)
      assert 0 <= t.pc < |c| && c[t.pc].Accept?;
      assert ORc.ReachFV(c, str, ov, cp0, t.pc, t.exit_allowed, s.cp);
      AcceptReachableAtVIntro(c, str, ov, cp0, s.cp, t.pc, t.exit_allowed);
    case Jmp(x) =>
      assert x >= 0 ==> ORc.ReachFV(c, str, ov, cp0, x, t.exit_allowed, s.cp) by {
        if x >= 0 { assert ORc.EpsEdgeV(c, str, ov, s.cp, t.pc, t.exit_allowed, x, t.exit_allowed); }
      }
      AdvanceAcceptSoundV(c, str, cp0, s1.(active := [t.(pc := x)] + ac), ov);
    case Fork(x, y) =>
      var newt := AI.Thread(x, t.capture_regs, t.look_regs, t.quant_regs, t.exit_allowed);
      assert x >= 0 ==> ORc.ReachFV(c, str, ov, cp0, x, t.exit_allowed, s.cp) by {
        if x >= 0 { assert ORc.EpsEdgeV(c, str, ov, s.cp, t.pc, t.exit_allowed, x, t.exit_allowed); }
      }
      assert y >= 0 ==> ORc.ReachFV(c, str, ov, cp0, y, t.exit_allowed, s.cp) by {
        if y >= 0 { assert ORc.EpsEdgeV(c, str, ov, s.cp, t.pc, t.exit_allowed, y, t.exit_allowed); }
      }
      AdvanceAcceptSoundV(c, str, cp0, s1.(active := [newt, t.(pc := y)] + ac), ov);
    case SetRegisterToCP(reg) =>
      var t' := t.(capture_regs := AReg.set_reg(t.capture_regs, reg, Some(s1.cp), s1.clock), pc := t.pc + 1);
      assert ORc.EpsEdgeV(c, str, ov, s.cp, t.pc, t.exit_allowed, t.pc + 1, t.exit_allowed);
      AdvanceAcceptSoundV(c, str, cp0, s1.(active := [t'] + ac), ov);
    case SetQuantToClock(q, b) =>
      var ocp := if b then Some(s1.cp) else None;
      var t' := t.(quant_regs := AReg.set_reg(t.quant_regs, q, ocp, s1.clock), pc := t.pc + 1);
      assert ORc.EpsEdgeV(c, str, ov, s.cp, t.pc, t.exit_allowed, t.pc + 1, t.exit_allowed);
      AdvanceAcceptSoundV(c, str, cp0, s1.(active := [t'] + ac), ov);
    case CheckOracle(l) =>
      if LOr.view_get_oracle(ov, s1.cp, l) {
        var t' := t.(pc := t.pc + 1, look_regs := AReg.set_reg(t.look_regs, l, Some(s1.cp), s1.clock));
        assert ORc.EpsEdgeV(c, str, ov, s.cp, t.pc, t.exit_allowed, t.pc + 1, t.exit_allowed);
        assert ORc.ReachFV(c, str, ov, cp0, t.pc + 1, t.exit_allowed, s.cp);
        AdvanceAcceptSoundV(c, str, cp0, s1.(active := [t'] + ac), ov);
      } else {
        AdvanceAcceptSoundV(c, str, cp0, s1.(active := ac), ov);
      }
    case NegCheckOracle(l) =>
      if LOr.view_get_oracle(ov, s1.cp, l) {
        AdvanceAcceptSoundV(c, str, cp0, s1.(active := ac), ov);
      } else {
        assert ORc.EpsEdgeV(c, str, ov, s.cp, t.pc, t.exit_allowed, t.pc + 1, t.exit_allowed);
        assert ORc.ReachFV(c, str, ov, cp0, t.pc + 1, t.exit_allowed, s.cp);
        AdvanceAcceptSoundV(c, str, cp0, s1.(active := [t.(pc := t.pc + 1)] + ac), ov);
      }
    case WriteOracle(l) =>
      assert 0 <= t.pc < |c| && c[t.pc].WriteOracle?;
      assert false;
    case BeginLoop =>
      assert ORc.EpsEdgeV(c, str, ov, s.cp, t.pc, t.exit_allowed, t.pc + 1, false);
      AdvanceAcceptSoundV(c, str, cp0, s1.(active := [t.(exit_allowed := false, pc := t.pc + 1)] + ac), ov);
    case EndLoop =>
      if t.exit_allowed {
        assert ORc.EpsEdgeV(c, str, ov, s.cp, t.pc, t.exit_allowed, t.pc + 1, t.exit_allowed);
        AdvanceAcceptSoundV(c, str, cp0, s1.(active := [t.(pc := t.pc + 1)] + ac), ov);
      } else {
        AdvanceAcceptSoundV(c, str, cp0, s1.(active := ac), ov);
      }
    case CheckNullable(qid) =>
      assert 0 <= t.pc < |c| && c[t.pc].CheckNullable?;
      assert false;
    case AnchorAssertion(a) =>
      if LAnc.is_satisfied(a, s1.context, LAnc.Forward) {
        assert ORc.EpsEdgeV(c, str, ov, s.cp, t.pc, t.exit_allowed, t.pc + 1, t.exit_allowed);
        AdvanceAcceptSoundV(c, str, cp0, s1.(active := [t.(pc := t.pc + 1)] + ac), ov);
      } else {
        AdvanceAcceptSoundV(c, str, cp0, s1.(active := ac), ov);
      }
    case Fail =>
      AdvanceAcceptSoundV(c, str, cp0, s1.(active := ac), ov);
  }

  /** Whole run: a Some result testifies a V-reachable Accept at SOME position
      at or after the entry. */
  lemma FindMatchAcceptSoundV(c: RB.code, str: string, cp0: int, s: AI.VmState,
                              ov: LOr.OracleView, cdn: LCdn.cdns)
    requires |s.processed.true_set| == RB.size(c) && |s.processed.false_set| == RB.size(c)
    requires s.context.nextchar == AI.get_char(str, s.cp)
    requires OS.NoCheckNullable(c) && NoOracleWrites(c)
    requires s.context == ORc.CtxAt(str, s.cp)
    requires ORc.ActiveOkV(c, str, ov, cp0, s.active, s.cp)
    requires ORc.BlockedOkV(c, str, ov, cp0, s.blocked, s.cp)
    ensures var (m, ov') := AI.FFindMatch(c, str, s, ov, LAnc.Forward, cdn);
            m.Some? ==> s.bestmatch.Some?
                        || exists cp2: int :: s.cp <= cp2 && AcceptReachableAtV(c, str, ov, cp0, cp2)
    decreases |str| - s.cp
  {
    var s0 := s.(cdn := LCdn.build_cdn_v(cdn, s.cp, ov, s.context, LAnc.Forward));
    var (s1, ov1) := AI.FAdvanceEpsilon(c, s0, ov, LAnc.Forward);
    AdvanceAcceptSoundV(c, str, cp0, s0, ov);
    assert ov1 == ov;
    assert s1.bestmatch.Some? ==> s.bestmatch.Some? || AcceptReachableAtV(c, str, ov, cp0, s.cp);
    if |s1.blocked| == 0 { return; }
    match s1.context.nextchar
    case None =>
    case Some(_) =>
      var s2 := AI.FConsume(s1);
      ORc.FConsumeReachV(c, str, ov, cp0, s1);
      var s3 := s2.(processed := AI.init_bpcset(RB.size(c)), isblocked := AI.init_pcset(RB.size(c)),
      cdn := LCdn.init_cdn(), cp := AI.incr_cp(s2.cp, LAnc.Forward));
      var newchar := AI.get_char(str, s3.cp - AI.cp_offset(LAnc.Forward));
      var s4 := s3.(context := LAnc.update_context(s3.context, newchar));
      assert s4.cp == s.cp + 1;
      assert s4.context == ORc.CtxAt(str, s4.cp);
      assert s4.bestmatch == s1.bestmatch;
      assert ORc.ActiveOkV(c, str, ov, cp0, s4.active, s4.cp);
      assert ORc.BlockedOkV(c, str, ov, cp0, s4.blocked, s4.cp);
      FindMatchAcceptSoundV(c, str, cp0, s4, ov, cdn);
      var (m, _) := AI.FFindMatch(c, str, s4, ov1, LAnc.Forward, cdn);
      if m.Some? {
        if s4.bestmatch.Some? {
          assert s.bestmatch.Some? || AcceptReachableAtV(c, str, ov, cp0, s.cp);
        } else {
          var cp2: int :| s4.cp <= cp2 && AcceptReachableAtV(c, str, ov, cp0, cp2);
          assert s.cp <= cp2;
        }
      }
  }

  // ===========================================================================
  // COMPLETENESS: a None-result run processes every reachable config, and
  // none of them is an Accept
  // ===========================================================================

  /** One closure over gate-aware, write-free code: if the result carries NO
      match, the closure ran to exhaustion (exactly the `NoAccept` behaviour),
      processed everything queued, kept the invariant — and processed no
      Accept. Floor `k == 0`: gate lids are `>= 1`, the write conjunct of
      `ClosureInvV` is vacuous. */
  lemma AdvanceAcceptCompleteV(c: RB.code, str: string, s: AI.VmState, ov: LOr.OracleView)
    requires |s.processed.true_set| == RB.size(c) && |s.processed.false_set| == RB.size(c)
    requires OS.AllGatesAbove(c, 0) && OS.NoCheckNullable(c) && NoOracleWrites(c)
    requires s.context == ORc.CtxAt(str, s.cp)
    requires ORc.ClosureInvV(c, 0, str, s, ov, ov)
    requires forall pc: nat, eb: bool ::
               ORc.InProc(s, pc, eb) && pc < RB.size(c) ==> !RB.get_instr(c, pc).Accept?
    ensures var (s', ov') := AI.FAdvanceEpsilon(c, s, ov, LAnc.Forward);
            ov' == ov
            && s'.cp == s.cp
            && (s'.bestmatch.None? ==>
                  s'.bestmatch == s.bestmatch
                  && s'.active == []
                  && (forall pc: nat, eb: bool ::
                        ORc.InProc(s, pc, eb) || (ORc.InActive(s, pc, eb) && pc < RB.size(c)) ==> ORc.InProc(s', pc, eb))
                  && ORc.ClosureInvV(c, 0, str, s', ov, ov)
                  && (forall pc: nat, eb: bool ::
                        ORc.InProc(s', pc, eb) && pc < RB.size(c) ==> !RB.get_instr(c, pc).Accept?))
    decreases AI.unprocessed(s.processed), |s.active|
  {
    if |s.active| == 0 { return; }
    var t := s.active[0];
    var ac := s.active[1..];
    var i := RB.get_instr(c, t.pc);
    if AI.bpc_mem(s.processed, t.pc, t.exit_allowed) {
      ORc.ClosureInvSkipV(c, 0, str, s, ov, ov);
      forall pc: nat, eb: bool | ORc.InProc(s.(active := ac), pc, eb) && pc < RB.size(c)
        ensures !RB.get_instr(c, pc).Accept?
      {
        assert ORc.InProc(s, pc, eb);
      }
      AdvanceAcceptCompleteV(c, str, s.(active := ac), ov);
      return;
    }
    var b0 := s.processed;
    var s1 := s.(clock := s.clock + 1, processed := AI.bpc_add(b0, t.pc, t.exit_allowed));
    AI.UnprocessedAdd(b0, t.pc, t.exit_allowed);
    // the newly processed head is not an Accept in every branch that recurses,
    // so the no-processed-Accept forall extends by BpcAddMem
    match i
    case Accept =>
    // the closure returns bestmatch Some — the None-guarded ensures is vacuous
    case Consume(ce) =>
      var (nb, ni) := AI.add_thread(t, ce, s1.blocked, s1.isblocked);
      ORc.ClosureInvConsumeV(c, 0, str, s, ov, ov, ce);
      var sr := s1.(blocked := nb, isblocked := ni, active := ac);
      NoAcceptProcExtend(c, s, sr, t.pc, t.exit_allowed);
      AdvanceAcceptCompleteV(c, str, sr, ov);
    case Jmp(x) =>
      var sr := s1.(active := [t.(pc := x)] + ac);
      assert x >= 0 ==> sr.active[0] == t.(pc := x);
      ORc.ClosureInvStepV(c, 0, str, s, ov, ov, t.pc, t.exit_allowed, [t.(pc := x)], sr);
      NoAcceptProcExtend(c, s, sr, t.pc, t.exit_allowed);
      AdvanceAcceptCompleteV(c, str, sr, ov);
    case Fork(x, y) =>
      var newt := AI.Thread(x, t.capture_regs, t.look_regs, t.quant_regs, t.exit_allowed);
      var sr := s1.(active := [newt, t.(pc := y)] + ac);
      assert x >= 0 ==> sr.active[0] == newt;
      assert y >= 0 ==> sr.active[1] == t.(pc := y);
      ORc.ClosureInvStepV(c, 0, str, s, ov, ov, t.pc, t.exit_allowed, [newt, t.(pc := y)], sr);
      NoAcceptProcExtend(c, s, sr, t.pc, t.exit_allowed);
      AdvanceAcceptCompleteV(c, str, sr, ov);
    case SetRegisterToCP(reg) =>
      var t' := t.(capture_regs := AReg.set_reg(t.capture_regs, reg, Some(s1.cp), s1.clock), pc := t.pc + 1);
      var sr := s1.(active := [t'] + ac);
      assert sr.active[0] == t';
      ORc.ClosureInvStepV(c, 0, str, s, ov, ov, t.pc, t.exit_allowed, [t'], sr);
      NoAcceptProcExtend(c, s, sr, t.pc, t.exit_allowed);
      AdvanceAcceptCompleteV(c, str, sr, ov);
    case SetQuantToClock(q, b) =>
      var ocp := if b then Some(s1.cp) else None;
      var t' := t.(quant_regs := AReg.set_reg(t.quant_regs, q, ocp, s1.clock), pc := t.pc + 1);
      var sr := s1.(active := [t'] + ac);
      assert sr.active[0] == t';
      ORc.ClosureInvStepV(c, 0, str, s, ov, ov, t.pc, t.exit_allowed, [t'], sr);
      NoAcceptProcExtend(c, s, sr, t.pc, t.exit_allowed);
      AdvanceAcceptCompleteV(c, str, sr, ov);
    case CheckOracle(l) =>
      assert 0 <= t.pc < |c| && c[t.pc].CheckOracle? && c[t.pc].col == l;
      if LOr.view_get_oracle(ov, s1.cp, l) {
        var t' := t.(pc := t.pc + 1, look_regs := AReg.set_reg(t.look_regs, l, Some(s1.cp), s1.clock));
        var sr := s1.(active := [t'] + ac);
        assert sr.active[0] == t';
        ORc.ClosureInvStepV(c, 0, str, s, ov, ov, t.pc, t.exit_allowed, [t'], sr);
        NoAcceptProcExtend(c, s, sr, t.pc, t.exit_allowed);
        AdvanceAcceptCompleteV(c, str, sr, ov);
      } else {
        var sr := s1.(active := ac);
        ORc.ClosureInvStepV(c, 0, str, s, ov, ov, t.pc, t.exit_allowed, [], sr);
        NoAcceptProcExtend(c, s, sr, t.pc, t.exit_allowed);
        AdvanceAcceptCompleteV(c, str, sr, ov);
      }
    case NegCheckOracle(l) =>
      assert 0 <= t.pc < |c| && c[t.pc].NegCheckOracle? && c[t.pc].ncl == l;
      if LOr.view_get_oracle(ov, s1.cp, l) {
        var sr := s1.(active := ac);
        ORc.ClosureInvStepV(c, 0, str, s, ov, ov, t.pc, t.exit_allowed, [], sr);
        NoAcceptProcExtend(c, s, sr, t.pc, t.exit_allowed);
        AdvanceAcceptCompleteV(c, str, sr, ov);
      } else {
        var sr := s1.(active := [t.(pc := t.pc + 1)] + ac);
        assert sr.active[0] == t.(pc := t.pc + 1);
        ORc.ClosureInvStepV(c, 0, str, s, ov, ov, t.pc, t.exit_allowed, [t.(pc := t.pc + 1)], sr);
        NoAcceptProcExtend(c, s, sr, t.pc, t.exit_allowed);
        AdvanceAcceptCompleteV(c, str, sr, ov);
      }
    case WriteOracle(l) =>
      assert 0 <= t.pc < |c| && c[t.pc].WriteOracle?;
      assert false;
    case BeginLoop =>
      var sr := s1.(active := [t.(exit_allowed := false, pc := t.pc + 1)] + ac);
      assert sr.active[0] == t.(exit_allowed := false, pc := t.pc + 1);
      ORc.ClosureInvStepV(c, 0, str, s, ov, ov, t.pc, t.exit_allowed, [t.(exit_allowed := false, pc := t.pc + 1)], sr);
      NoAcceptProcExtend(c, s, sr, t.pc, t.exit_allowed);
      AdvanceAcceptCompleteV(c, str, sr, ov);
    case EndLoop =>
      if t.exit_allowed {
        var sr := s1.(active := [t.(pc := t.pc + 1)] + ac);
        assert sr.active[0] == t.(pc := t.pc + 1);
        ORc.ClosureInvStepV(c, 0, str, s, ov, ov, t.pc, t.exit_allowed, [t.(pc := t.pc + 1)], sr);
        NoAcceptProcExtend(c, s, sr, t.pc, t.exit_allowed);
        AdvanceAcceptCompleteV(c, str, sr, ov);
      } else {
        var sr := s1.(active := ac);
        ORc.ClosureInvStepV(c, 0, str, s, ov, ov, t.pc, t.exit_allowed, [], sr);
        NoAcceptProcExtend(c, s, sr, t.pc, t.exit_allowed);
        AdvanceAcceptCompleteV(c, str, sr, ov);
      }
    case CheckNullable(qid) =>
      assert 0 <= t.pc < |c| && c[t.pc].CheckNullable?;
      assert false;
    case AnchorAssertion(a) =>
      if LAnc.is_satisfied(a, s1.context, LAnc.Forward) {
        var sr := s1.(active := [t.(pc := t.pc + 1)] + ac);
        assert sr.active[0] == t.(pc := t.pc + 1);
        ORc.ClosureInvStepV(c, 0, str, s, ov, ov, t.pc, t.exit_allowed, [t.(pc := t.pc + 1)], sr);
        NoAcceptProcExtend(c, s, sr, t.pc, t.exit_allowed);
        AdvanceAcceptCompleteV(c, str, sr, ov);
      } else {
        var sr := s1.(active := ac);
        ORc.ClosureInvStepV(c, 0, str, s, ov, ov, t.pc, t.exit_allowed, [], sr);
        NoAcceptProcExtend(c, s, sr, t.pc, t.exit_allowed);
        AdvanceAcceptCompleteV(c, str, sr, ov);
      }
    case Fail =>
      var sr := s1.(active := ac);
      forall pc: nat, eb: bool, pc2: nat, eb2: bool
        | ORc.InProc(sr, pc, eb) && pc2 < RB.size(c) && ORc.EpsEdgeV(c, str, ov, sr.cp, pc, eb, pc2, eb2)
        ensures ORc.InProc(sr, pc2, eb2) || ORc.InActive(sr, pc2, eb2)
      {
        ORc.BpcAddMem(b0, t.pc, t.exit_allowed, pc, eb);
        if pc != t.pc || eb != t.exit_allowed {
          assert ORc.InProc(s, pc, eb);
          ORc.BpcAddMem(b0, t.pc, t.exit_allowed, pc2, eb2);
          if ORc.InActive(s, pc2, eb2) && !ORc.InProc(s, pc2, eb2) { ORc.ActiveHeadTail(s, pc2, eb2); }
        }
      }
      forall pc: nat, eb: bool | ORc.InProc(sr, pc, eb) && RB.get_instr(c, pc).Consume?
        ensures ORc.HasBlockedEntry(c, sr.blocked, pc)
      {
        ORc.BpcAddMem(b0, t.pc, t.exit_allowed, pc, eb);
        assert ORc.InProc(s, pc, eb);
      }
      forall q: int | AI.pc_mem(sr.isblocked, q)
        ensures ORc.HasBlockedEntry(c, sr.blocked, q)
      {
        assert AI.pc_mem(s.isblocked, q);
      }
      NoAcceptProcExtend(c, s, sr, t.pc, t.exit_allowed);
      AdvanceAcceptCompleteV(c, str, sr, ov);
  }

  /** Adding a non-Accept head to the processed set keeps the
      no-processed-Accept forall (helper for `AdvanceAcceptCompleteV`). */
  lemma NoAcceptProcExtend(c: RB.code, s: AI.VmState, sr: AI.VmState, hpc: int, heb: bool)
    requires forall pc: nat, eb: bool ::
               ORc.InProc(s, pc, eb) && pc < RB.size(c) ==> !RB.get_instr(c, pc).Accept?
    requires sr.processed == AI.bpc_add(s.processed, hpc, heb)
    requires !RB.get_instr(c, hpc).Accept?
    ensures forall pc: nat, eb: bool ::
              ORc.InProc(sr, pc, eb) && pc < RB.size(c) ==> !RB.get_instr(c, pc).Accept?
  {
    forall pc: nat, eb: bool | ORc.InProc(sr, pc, eb) && pc < RB.size(c)
      ensures !RB.get_instr(c, pc).Accept?
    {
      ORc.BpcAddMem(s.processed, hpc, heb, pc, eb);
      if pc != hpc || eb != heb {
        assert ORc.InProc(s, pc, eb);
      }
    }
  }

  /** `bestmatch` is monotone: a run entered with a match in hand returns Some. */
  lemma FFindMatchBestmatchSome(c: RB.code, str: string, s: AI.VmState, ov: LOr.OracleView, cdn: LCdn.cdns)
    requires |s.processed.true_set| == RB.size(c) && |s.processed.false_set| == RB.size(c)
    requires s.context.nextchar == AI.get_char(str, s.cp)
    requires s.bestmatch.Some?
    ensures AI.FFindMatch(c, str, s, ov, LAnc.Forward, cdn).0.Some?
    decreases |str| - s.cp
  {
    var s0 := s.(cdn := LCdn.build_cdn_v(cdn, s.cp, ov, s.context, LAnc.Forward));
    var (s1, ov1) := AI.FAdvanceEpsilon(c, s0, ov, LAnc.Forward);
    FAdvanceBestmatchMono(c, s0, ov);
    if |s1.blocked| == 0 { return; }
    match s1.context.nextchar
    case None =>
    case Some(_) =>
      var s2 := AI.FConsume(s1);
      var s3 := s2.(processed := AI.init_bpcset(RB.size(c)), isblocked := AI.init_pcset(RB.size(c)),
      cdn := LCdn.init_cdn(), cp := AI.incr_cp(s2.cp, LAnc.Forward));
      var newchar := AI.get_char(str, s3.cp - AI.cp_offset(LAnc.Forward));
      var s4 := s3.(context := LAnc.update_context(s3.context, newchar));
      FFindMatchBestmatchSome(c, str, s4, ov1, cdn);
  }

  /** One closure never CLEARS `bestmatch`. */
  lemma FAdvanceBestmatchMono(c: RB.code, s: AI.VmState, ov: LOr.OracleView)
    requires |s.processed.true_set| == RB.size(c) && |s.processed.false_set| == RB.size(c)
    ensures var (s', _) := AI.FAdvanceEpsilon(c, s, ov, LAnc.Forward);
            s.bestmatch.Some? ==> s'.bestmatch.Some?
    decreases AI.unprocessed(s.processed), |s.active|
  {
    if |s.active| == 0 { return; }
    var t := s.active[0];
    var ac := s.active[1..];
    var i := RB.get_instr(c, t.pc);
    if AI.bpc_mem(s.processed, t.pc, t.exit_allowed) {
      FAdvanceBestmatchMono(c, s.(active := ac), ov);
      return;
    }
    var b0 := s.processed;
    var s1 := s.(clock := s.clock + 1, processed := AI.bpc_add(b0, t.pc, t.exit_allowed));
    AI.UnprocessedAdd(b0, t.pc, t.exit_allowed);
    match i
    case Consume(ce) =>
      var (nb, ni) := AI.add_thread(t, ce, s1.blocked, s1.isblocked);
      FAdvanceBestmatchMono(c, s1.(blocked := nb, isblocked := ni, active := ac), ov);
    case Accept =>
    case Jmp(x) => FAdvanceBestmatchMono(c, s1.(active := [t.(pc := x)] + ac), ov);
    case Fork(x, y) =>
      var newt := AI.Thread(x, t.capture_regs, t.look_regs, t.quant_regs, t.exit_allowed);
      FAdvanceBestmatchMono(c, s1.(active := [newt, t.(pc := y)] + ac), ov);
    case SetRegisterToCP(reg) =>
      var t' := t.(capture_regs := AReg.set_reg(t.capture_regs, reg, Some(s1.cp), s1.clock), pc := t.pc + 1);
      FAdvanceBestmatchMono(c, s1.(active := [t'] + ac), ov);
    case SetQuantToClock(q, b) =>
      var ocp := if b then Some(s1.cp) else None;
      var t' := t.(quant_regs := AReg.set_reg(t.quant_regs, q, ocp, s1.clock), pc := t.pc + 1);
      FAdvanceBestmatchMono(c, s1.(active := [t'] + ac), ov);
    case CheckOracle(l) =>
      if LOr.view_get_oracle(ov, s1.cp, l) {
        var t' := t.(pc := t.pc + 1, look_regs := AReg.set_reg(t.look_regs, l, Some(s1.cp), s1.clock));
        FAdvanceBestmatchMono(c, s1.(active := [t'] + ac), ov);
      } else {
        FAdvanceBestmatchMono(c, s1.(active := ac), ov);
      }
    case NegCheckOracle(l) =>
      if LOr.view_get_oracle(ov, s1.cp, l) {
        FAdvanceBestmatchMono(c, s1.(active := ac), ov);
      } else {
        FAdvanceBestmatchMono(c, s1.(active := [t.(pc := t.pc + 1)] + ac), ov);
      }
    case WriteOracle(l) =>
      FAdvanceBestmatchMono(c, s1.(active := ac), LOr.view_set_oracle(ov, s1.cp, l));
    case BeginLoop =>
      FAdvanceBestmatchMono(c, s1.(active := [t.(exit_allowed := false, pc := t.pc + 1)] + ac), ov);
    case EndLoop =>
      if t.exit_allowed {
        FAdvanceBestmatchMono(c, s1.(active := [t.(pc := t.pc + 1)] + ac), ov);
      } else {
        FAdvanceBestmatchMono(c, s1.(active := ac), ov);
      }
    case CheckNullable(qid) =>
      if LCdn.cdn_get(s1.cdn, qid) {
        FAdvanceBestmatchMono(c, s1.(active := [t.(pc := t.pc + 1)] + ac), ov);
      } else {
        FAdvanceBestmatchMono(c, s1.(active := ac), ov);
      }
    case AnchorAssertion(a) =>
      if LAnc.is_satisfied(a, s1.context, LAnc.Forward) {
        FAdvanceBestmatchMono(c, s1.(active := [t.(pc := t.pc + 1)] + ac), ov);
      } else {
        FAdvanceBestmatchMono(c, s1.(active := ac), ov);
      }
    case Fail =>
      FAdvanceBestmatchMono(c, s1.(active := ac), ov);
  }

  /** Whole run, completeness: a None result means NO config V-reachable at any
      position from the entry onward is an Accept. */
  lemma FindMatchAcceptCompleteV(c: RB.code, str: string, cp0: int, s: AI.VmState,
                                 ov: LOr.OracleView, cdn: LCdn.cdns)
    requires |s.processed.true_set| == RB.size(c) && |s.processed.false_set| == RB.size(c)
    requires s.context.nextchar == AI.get_char(str, s.cp)
    requires OS.AllGatesAbove(c, 0) && OS.NoCheckNullable(c) && NoOracleWrites(c)
    requires s.context == ORc.CtxAt(str, s.cp)
    requires s.processed == AI.init_bpcset(RB.size(c))
    requires s.isblocked == AI.init_pcset(RB.size(c))
    requires s.blocked == []
    requires s.bestmatch.None?
    requires 0 <= cp0 <= s.cp <= |str|
    requires forall pc: nat, eb: bool ::
               ORc.EntryConfigV(c, str, ov, cp0, pc, eb, s.cp) && pc < RB.size(c) ==> ORc.InActive(s, pc, eb)
    ensures var (m, ov') := AI.FFindMatch(c, str, s, ov, LAnc.Forward, cdn);
            m.None? ==> forall cp2: int, pc: nat, eb: bool ::
                ORc.ReachFV(c, str, ov, cp0, pc, eb, cp2) && pc < RB.size(c) && s.cp <= cp2
                ==> !RB.get_instr(c, pc).Accept?
    decreases |str| - s.cp
  {
    var s0 := s.(cdn := LCdn.build_cdn_v(cdn, s.cp, ov, s.context, LAnc.Forward));
    var (s1, ov1) := AI.FAdvanceEpsilon(c, s0, ov, LAnc.Forward);
    assert ORc.ClosureInvV(c, 0, str, s0, ov, ov);   // processed/isblocked empty, blocked == []
    assert forall pc: nat, eb: bool ::
        ORc.InProc(s0, pc, eb) && pc < RB.size(c) ==> !RB.get_instr(c, pc).Accept?;
    AdvanceAcceptCompleteV(c, str, s0, ov);
    var (m, ovf) := AI.FFindMatch(c, str, s, ov, LAnc.Forward, cdn);
    if m.Some? { return; }
    // a Some closure result would have propagated to a Some run result
    assert s1.bestmatch.None? by {
      if s1.bestmatch.Some? {
        if |s1.blocked| == 0 {
          assert m == s1.bestmatch;
        } else {
          match s1.context.nextchar
          case None =>
    assert m == s1.bestmatch;
          case Some(_) =>
            var s2 := AI.FConsume(s1);
            var s3 := s2.(processed := AI.init_bpcset(RB.size(c)), isblocked := AI.init_pcset(RB.size(c)),
            cdn := LCdn.init_cdn(), cp := AI.incr_cp(s2.cp, LAnc.Forward));
            var newchar := AI.get_char(str, s3.cp - AI.cp_offset(LAnc.Forward));
            var s4 := s3.(context := LAnc.update_context(s3.context, newchar));
            FFindMatchBestmatchSome(c, str, s4, ov1, cdn);
        }
        assert false;
      }
    }
    // the closure ran to exhaustion: everything reachable AT s.cp is processed
    // and no processed config is an Accept
    assert s1.active == [];
    assert ORc.ClosureInvV(c, 0, str, s1, ov, ov);
    assert ov1 == ov;
    assert forall p: nat, e: bool ::
        ORc.EntryConfigV(c, str, ov, cp0, p, e, s.cp) && p < RB.size(c) ==> ORc.InProc(s1, p, e);
    assert forall p: nat, e: bool, p2: nat, e2: bool ::
        ORc.InProc(s1, p, e) && p2 < RB.size(c) && ORc.EpsEdgeV(c, str, ov, s.cp, p, e, p2, e2) ==> ORc.InProc(s1, p2, e2);
    forall pc: nat, eb: bool | ORc.ReachFV(c, str, ov, cp0, pc, eb, s.cp) && pc < RB.size(c)
      ensures !RB.get_instr(c, pc).Accept?
    {
      ORc.ReachInProcV(c, str, ov, cp0, pc, eb, s.cp, s1);
    }
    if |s1.blocked| == 0 {
      // nothing consumed out of s.cp: nothing is reachable beyond it
      forall cp2: int, pc: nat, eb: bool
        | ORc.ReachFV(c, str, ov, cp0, pc, eb, cp2) && pc < RB.size(c) && s.cp <= cp2
        ensures !RB.get_instr(c, pc).Accept?
      {
        if cp2 > s.cp {
          ORc.ReachBeyondNeedsConsumeV(c, str, ov, cp0, s.cp, pc, eb, cp2);
          var p: nat, e: bool :| ORc.ReachFV(c, str, ov, cp0, p, e, s.cp) && ORc.ConsumeEdge(c, str, s.cp, p);
          assert 0 <= p < RB.size(c) by {
            if !(p < RB.size(c)) { assert RB.get_instr(c, p) == RB.Fail; }
          }
          ORc.ReachInProcV(c, str, ov, cp0, p, e, s.cp, s1);
          assert RB.get_instr(c, p).Consume?;
          assert ORc.HasBlockedEntry(c, s1.blocked, p);   // Inv2 — but s1.blocked == []
          assert false;
        }
      }
      return;
    }
    match s1.context.nextchar
    case None =>
      forall cp2: int, pc: nat, eb: bool
        | ORc.ReachFV(c, str, ov, cp0, pc, eb, cp2) && pc < RB.size(c) && s.cp <= cp2
        ensures !RB.get_instr(c, pc).Accept?
      {
        if cp2 > s.cp {
          ORc.ReachFVLeEnd(c, str, ov, cp0, pc, eb, cp2);   // cp2 <= |str|
          assert AI.get_char(str, s.cp) == None;             // nextchar None ==> s.cp >= |str|
          assert false;                                      // cp2 > s.cp >= |str| >= cp2
        }
      }
    case Some(_) =>
      var s2 := AI.FConsume(s1);
      var s3 := s2.(processed := AI.init_bpcset(RB.size(c)), isblocked := AI.init_pcset(RB.size(c)),
      cdn := LCdn.init_cdn(), cp := AI.incr_cp(s2.cp, LAnc.Forward));
      var newchar := AI.get_char(str, s3.cp - AI.cp_offset(LAnc.Forward));
      var s4 := s3.(context := LAnc.update_context(s3.context, newchar));
      ORc.FConsumeReachComplete(s1);
      ORc.FConsumeDrainsBlocked(s1);
      assert s4.blocked == [];
      assert s4.cp == s.cp + 1;
      assert s4.context == ORc.CtxAt(str, s4.cp);
      assert s4.bestmatch == s1.bestmatch && s4.bestmatch.None?;
      // entries of s4.cp are covered by s4.active
      forall pc: nat, eb: bool | ORc.EntryConfigV(c, str, ov, cp0, pc, eb, s4.cp) && pc < RB.size(c)
        ensures ORc.InActive(s4, pc, eb)
      {
        assert eb == true && pc > 0
               && (ORc.ReachFV(c, str, ov, cp0, pc - 1, false, s.cp) || ORc.ReachFV(c, str, ov, cp0, pc - 1, true, s.cp))
               && ORc.ConsumeEdge(c, str, s.cp, pc - 1);
        var e' :| (e' == false || e' == true) && ORc.ReachFV(c, str, ov, cp0, pc - 1, e', s.cp);
        var q: nat := pc - 1;
        assert 0 <= q < RB.size(c) by {
          if !(q < RB.size(c)) { assert RB.get_instr(c, q) == RB.Fail; }
        }
        ORc.ReachInProcV(c, str, ov, cp0, q, e', s.cp, s1);
        assert RB.get_instr(c, q).Consume?;
        assert ORc.HasBlockedEntry(c, s1.blocked, q);
        var j :| 0 <= j < |s1.blocked| && s1.blocked[j].0.pc == q
                 && RB.get_instr(c, q) == RB.Consume(s1.blocked[j].1);
        assert RC.is_accepted(s1.context.nextchar, s1.blocked[j].1);   // ConsumeEdge(s.cp, q)
        assert exists kk :: (0 <= kk < |AI.FConsume(s1).active|
                             && AI.FConsume(s1).active[kk].pc == s1.blocked[j].0.pc + 1
                             && AI.FConsume(s1).active[kk].exit_allowed);
        var kk :| 0 <= kk < |AI.FConsume(s1).active|
                  && AI.FConsume(s1).active[kk].pc == q + 1 && AI.FConsume(s1).active[kk].exit_allowed;
        assert s4.active == AI.FConsume(s1).active;
        assert s4.active[kk].pc == pc && s4.active[kk].exit_allowed == eb;
      }
      FindMatchAcceptCompleteV(c, str, cp0, s4, ov, cdn);
      assert AI.FFindMatch(c, str, s4, ov1, LAnc.Forward, cdn).0 == m;
  }

  // ===========================================================================
  // The single-block program invariant: reachable configs of an Accept-
  // terminated body program are mid-parse or done
  // ===========================================================================

  /** Every V-reachable configuration of `compile_to_bytecode(body)` started
      at `(pc 0, cp0)` is a mid-parse state of the body block entered at `cp0`,
      or the Accept with a completed span. */
  least lemma BodyProgInvV(body: R.regex, code: RB.code, next: nat, str: string, ov: LOr.OracleView,
                           cp0: int, pc: nat, eb: bool, cp: int)
    requires NR.NfaRepRE(body, code, 0, next)
    requires NR.GetPcRE(code, next) == Some(RB.Accept)
    requires ORc.ReachFV(code, str, ov, cp0, pc, eb, cp)
    ensures ODV.InBlockV(body, code, 0, next, str, ov, cp0, pc, cp)
            || (pc == next && OBV.MatchesV(body, str, ov, cp0, cp))
  {
    if pc == 0 && eb == false && cp == cp0 {
      ODV.BlockEntryV(body, code, 0, next, str, ov, cp0);
      if 0 == next {
        ODV.BlockEmptyV(body, code, 0, str, ov, cp0);
      }
    } else if exists pc1: nat, eb1: bool ::
        ORc.ReachFV(code, str, ov, cp0, pc1, eb1, cp) && ORc.EpsEdgeV(code, str, ov, cp, pc1, eb1, pc, eb) {
      var pc1: nat, eb1: bool :|
        ORc.ReachFV(code, str, ov, cp0, pc1, eb1, cp) && ORc.EpsEdgeV(code, str, ov, cp, pc1, eb1, pc, eb);
      BodyProgInvV(body, code, next, str, ov, cp0, pc1, eb1, cp);
      assert ODV.AnyEdgeV(code, str, ov, pc1, eb1, cp, pc, eb, cp);
      if ODV.InBlockV(body, code, 0, next, str, ov, cp0, pc1, cp) {
        ODV.BlockStepV(body, code, 0, next, str, ov, cp0, pc1, eb1, cp, pc, eb, cp);
      } else {
        // the Accept has no outgoing edges
        OB.GetPcInstr(code, next, RB.Accept);
        assert false;
      }
    } else {
      assert eb == true && pc > 0 && ORc.ConsumeEdge(code, str, cp - 1, pc - 1);
      var eb1: bool :| (eb1 == false || eb1 == true)
                       && ORc.ReachFV(code, str, ov, cp0, pc - 1, eb1, cp - 1);
      BodyProgInvV(body, code, next, str, ov, cp0, pc - 1, eb1, cp - 1);
      assert ODV.AnyEdgeV(code, str, ov, pc - 1, eb1, cp - 1, pc, eb, cp);
      if ODV.InBlockV(body, code, 0, next, str, ov, cp0, pc - 1, cp - 1) {
        ODV.BlockStepV(body, code, 0, next, str, ov, cp0, pc - 1, eb1, cp - 1, pc, eb, cp);
      } else {
        OB.GetPcInstr(code, next, RB.Accept);
        assert false;
      }
    }
  }

  // ===========================================================================
  // Classification of the compiled body program
  // ===========================================================================

  /** The compiled nested body program classifies: no CheckNullable, no
      WriteOracle, and every gate reads a column `>= 1`. */
  lemma BodyCodeClassified(body: R.regex)
    requires NR.NestedFragmentRE(body)
    requires LTB.LookUnique(body)
    requires forall x: nat :: x in LTB.LookIds(body) ==> 1 <= x
    ensures var code := CP.compile_to_bytecode(body);
            var next := CP.compile(body, 0, CP.Progress).1;
            next >= 0 && NR.NfaRepRE(body, code, 0, next as nat)
            && NR.GetPcRE(code, next as nat) == Some(RB.Accept)
            && |code| == next + 1
            && OS.NoCheckNullable(code) && NoOracleWrites(code) && OS.AllGatesAbove(code, 0)
  {
    NR.CompileToBytecodeRepNested(body);
    var code := CP.compile_to_bytecode(body);
    var next := CP.compile(body, 0, CP.Progress).1;
    forall pc: nat | 0 <= pc < |code|
      ensures !code[pc].CheckNullable? && !code[pc].WriteOracle?
              && (code[pc].CheckOracle? ==> code[pc].col > 0)
              && (code[pc].NegCheckOracle? ==> code[pc].ncl > 0)
    {
      assert NR.GetPcRE(code, pc) == Some(code[pc]);
      if pc < next as nat {
        NR.NoWriteInstrNestedRE(body, code, 0, next as nat, pc);
        assert forall x: nat :: x in LTB.LookIds(body) ==> x > 0;
        NR.GatesAboveInstrRE(body, code, 0, next as nat, 0, pc);
      } else {
        assert pc == next as nat;
        assert code[pc] == RB.Accept;
      }
    }
  }

  // ===========================================================================
  // THE ACCEPT-RUN CHARACTERIZATION
  // ===========================================================================

  /** THE V4 capstone: a nested body's Forward run from `cp` against the view
      `ov` returns Some EXACTLY when the body has a gated span from `cp`. */
  lemma AcceptRunCharacterizationV(body: R.regex, str: string, ov: LOr.OracleView, cp: int,
                                   cdn: LCdn.cdns, initcap: AReg.Regs, initlook: AReg.Regs,
                                   initquant: AReg.Regs, initclk: int)
    requires NR.NestedFragmentRE(body)
    requires LTB.LookUnique(body)
    requires forall x: nat :: x in LTB.LookIds(body) ==> 1 <= x
    requires 0 <= cp <= |str|
    ensures var code := CP.compile_to_bytecode(body);
            var s := AI.FInitState(code, cp, initcap, initlook, initquant, initclk,
                                   AI.cp_context(cp, str, LAnc.Forward));
            AI.FFindMatch(code, str, s, ov, LAnc.Forward, cdn).0.Some?
            <==> exists j: int :: OBV.MatchesV(body, str, ov, cp, j)
  {
    BodyCodeClassified(body);
    var code := CP.compile_to_bytecode(body);
    var next := CP.compile(body, 0, CP.Progress).1;
    var s := AI.FInitState(code, cp, initcap, initlook, initquant, initclk,
                           AI.cp_context(cp, str, LAnc.Forward));
    assert s.context == ORc.CtxAt(str, cp);
    assert s.context.nextchar == AI.get_char(str, cp);
    assert s.active == [AI.init_thread(initcap, initlook, initquant)];
    assert s.active[0].pc == 0 && s.active[0].exit_allowed == false;
    assert ORc.ReachFV(code, str, ov, cp, 0, false, cp);
    assert ORc.ActiveOkV(code, str, ov, cp, s.active, cp);
    assert ORc.BlockedOkV(code, str, ov, cp, s.blocked, cp);
    var (m, ovf) := AI.FFindMatch(code, str, s, ov, LAnc.Forward, cdn);

    if m.Some? {
      // soundness: a reachable Accept, decomposed to a MatchesV span
      FindMatchAcceptSoundV(code, str, cp, s, ov, cdn);
      assert s.bestmatch.None?;
      var cp2: int :| cp <= cp2 && AcceptReachableAtV(code, str, ov, cp, cp2);
      var pc, eb := AcceptReachableAtVInv(code, str, ov, cp, cp2);
      // pin the Accept's pc to `next`
      assert pc == next as nat by {
        if pc < next as nat {
          NR.NoWriteInstrNestedRE(body, code, 0, next as nat, pc);
          assert NR.GetPcRE(code, pc) == Some(code[pc]);
          assert false;
        } else if pc > next as nat {
          assert RB.get_instr(code, pc) == RB.Fail;
          assert false;
        }
      }
      BodyProgInvV(body, code, next as nat, str, ov, cp, pc, eb, cp2);
      if ODV.InBlockV(body, code, 0, next as nat, str, ov, cp, pc, cp2) {
        ODV.InBlockVRange(body, code, 0, next as nat, str, ov, cp, pc, cp2);
        assert false;
      }
      assert OBV.MatchesV(body, str, ov, cp, cp2);
    }

    if exists j: int :: OBV.MatchesV(body, str, ov, cp, j) {
      var j: int :| OBV.MatchesV(body, str, ov, cp, j);
      OBV.MatchesVBounds(body, str, ov, cp, j);
      // completeness: the span reaches the Accept, so a None result is absurd
      OBV.MatchesVToPath(body, code, 0, next as nat, str, ov, cp, cp, j, false);
      OB.GetPcInstr(code, next as nat, RB.Accept);
      assert ORc.ReachFV(code, str, ov, cp, next as nat, if j > cp then true else false, j);
      if m.None? {
        // entry coverage at the initial position: only the base config
        forall pc: nat, eb: bool | ORc.EntryConfigV(code, str, ov, cp, pc, eb, cp) && pc < RB.size(code)
          ensures ORc.InActive(s, pc, eb)
        {
          if !(pc == 0 && eb == false) {
            var e' :| (e' == false || e' == true) && ORc.ReachFV(code, str, ov, cp, pc - 1, e', cp - 1);
            ORc.ReachFVGeStart(code, str, ov, cp, pc - 1, e', cp - 1);
            assert false;
          }
          assert s.active[0].pc == 0 && s.active[0].exit_allowed == false;
        }
        FindMatchAcceptCompleteV(code, str, cp, s, ov, cdn);
        assert next as nat < RB.size(code);
        assert cp <= j;
        assert !RB.get_instr(code, next as nat).Accept?;
        assert false;
      }
    }
  }
}
