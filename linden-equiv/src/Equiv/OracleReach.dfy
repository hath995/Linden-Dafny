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

  // ===========================================================================
  // Completeness: the sweep processes every reachable configuration
  // (the Pike worklist argument, at existence level)
  // ===========================================================================

  /** Config `(pc, eb)` is already processed in `s` (in-range pcs only —
      `bpc_mem` is false out of range). */
  ghost predicate InProc(s: AI.VmState, pc: nat, eb: bool) {
    AI.bpc_mem(s.processed, pc, eb)
  }

  /** Config `(pc, eb)` is carried by some active thread of `s` (a thread at a
      negative pc can never match a `nat` pc, so those carry no config). */
  ghost predicate InActive(s: AI.VmState, pc: nat, eb: bool) {
    exists j :: 0 <= j < |s.active| && s.active[j].pc == pc && s.active[j].exit_allowed == eb
  }

  /** The worklist invariant carried across one epsilon closure at `s.cp`:
      (1) every in-range `EpsEdge`-successor of a processed config is itself
      processed or still active (the frontier is `EpsEdge`-closed into P ∪ A);
      (2) every processed `Consume` config has a blocked entry at its pc with
      its expectation (`add_thread` keeps the first per pc — same instruction,
      same expectation); (3) every processed `WriteOracle(lid)` config already
      has its bit set at `s.cp`. */
  /** `blocked` holds an entry at pc `q` recording the `Consume` there — the
      shape both the consume edge and `add_thread`'s per-pc dedup rely on.
      Taken over the sequence directly, so it frames trivially across a state
      update that leaves `blocked` unchanged. */
  ghost predicate HasBlockedEntry(c: RB.code, blocked: seq<(AI.Thread, RC.char_expectation)>, q: int) {
    exists j :: 0 <= j < |blocked| && blocked[j].0.pc == q
                && RB.get_instr(c, q) == RB.Consume(blocked[j].1)
  }

  ghost predicate ClosureInv(c: RB.code, str: string, s: AI.VmState, ov: LOr.OracleView, lid: int) {
    (forall pc: nat, eb: bool, pc2: nat, eb2: bool ::
        InProc(s, pc, eb) && pc2 < RB.size(c) && EpsEdge(c, str, s.cp, pc, eb, pc2, eb2)
          ==> InProc(s, pc2, eb2) || InActive(s, pc2, eb2))
    && (forall pc: nat, eb: bool ::
        InProc(s, pc, eb) && RB.get_instr(c, pc).Consume? ==> HasBlockedEntry(c, s.blocked, pc))
    && (forall q: int :: AI.pc_mem(s.isblocked, q) ==> HasBlockedEntry(c, s.blocked, q))
    && (forall pc: nat, eb: bool ::
        InProc(s, pc, eb) && RB.get_instr(c, pc) == RB.WriteOracle(lid)
          ==> LOr.view_get_oracle(ov, s.cp, lid))
  }

  /** `bpc_add` marks exactly the in-range pair `(q, qeb)` and nothing else. */
  lemma BpcAddMem(b: AI.Bpcset, q: int, qeb: bool, pc: nat, eb: bool)
    ensures AI.bpc_mem(AI.bpc_add(b, q, qeb), pc, eb)
         == (AI.bpc_mem(b, pc, eb)
             || (pc == q && eb == qeb && 0 <= q < (if qeb then |b.true_set| else |b.false_set|)))
  {
  }

  /** A config active in `s` is either the head's config or is active in the
      tail `s.active[1..]` — the case-split the drop branches need. */
  lemma ActiveHeadTail(s: AI.VmState, pc: nat, eb: bool)
    requires |s.active| > 0 && InActive(s, pc, eb)
    ensures (s.active[0].pc == pc && s.active[0].exit_allowed == eb)
         || InActive(s.(active := s.active[1..]), pc, eb)
  {
    var j :| 0 <= j < |s.active| && s.active[j].pc == pc && s.active[j].exit_allowed == eb;
    if j != 0 {
      assert s.(active := s.active[1..]).active[j - 1] == s.active[j];
    }
  }

  /** `pc_add` marks exactly the in-range label `q0` and nothing else. */
  lemma PcAddMem(pcs: AI.pcset, q0: int, q: int)
    ensures AI.pc_mem(AI.pc_add(pcs, q0), q) == ((q == q0 && 0 <= q0 < |pcs|) || AI.pc_mem(pcs, q))
  {
  }

  /** Prepending an entry to `blocked` preserves a blocked entry at `q`. */
  lemma BlockedPrependPreserves(c: RB.code, blocked: seq<(AI.Thread, RC.char_expectation)>,
                                x: (AI.Thread, RC.char_expectation), q: int)
    requires HasBlockedEntry(c, blocked, q)
    ensures HasBlockedEntry(c, [x] + blocked, q)
  {
    var j :| 0 <= j < |blocked| && blocked[j].0.pc == q && RB.get_instr(c, q) == RB.Consume(blocked[j].1);
    assert ([x] + blocked)[j + 1] == blocked[j];
  }

  /** Dropping an already-processed (skip) head preserves the closure
      invariant: the head's config stays in P, compensating the lost active
      witness. */
  lemma ClosureInvSkip(c: RB.code, str: string, s: AI.VmState, ov: LOr.OracleView, lid: int)
    requires |s.active| > 0
    requires AI.bpc_mem(s.processed, s.active[0].pc, s.active[0].exit_allowed)
    requires ClosureInv(c, str, s, ov, lid)
    ensures ClosureInv(c, str, s.(active := s.active[1..]), ov, lid)
  {
    var sr := s.(active := s.active[1..]);
    forall pc: nat, eb: bool, pc2: nat, eb2: bool
      | InProc(sr, pc, eb) && pc2 < RB.size(c) && EpsEdge(c, str, sr.cp, pc, eb, pc2, eb2)
      ensures InProc(sr, pc2, eb2) || InActive(sr, pc2, eb2)
    {
      assert InProc(s, pc, eb);
      if InActive(s, pc2, eb2) && !InProc(s, pc2, eb2) {
        ActiveHeadTail(s, pc2, eb2);
      }
    }
    // Inv2/Inv3/Inv4: processed/blocked/isblocked/ov/cp unchanged, nudge the quantifiers.
    forall pc: nat, eb: bool | InProc(sr, pc, eb) && RB.get_instr(c, pc).Consume?
      ensures HasBlockedEntry(c, sr.blocked, pc)
    {
      assert InProc(s, pc, eb);
    }
    forall q: int | AI.pc_mem(sr.isblocked, q)
      ensures HasBlockedEntry(c, sr.blocked, q)
    {
      assert AI.pc_mem(s.isblocked, q);
    }
    forall pc: nat, eb: bool | InProc(sr, pc, eb) && RB.get_instr(c, pc) == RB.WriteOracle(lid)
      ensures LOr.view_get_oracle(ov, sr.cp, lid)
    {
      assert InProc(s, pc, eb);
    }
  }

  /** Processing a `Consume` head: `blocked`/`isblocked` gain (or already hold)
      the head's entry, and the head has no epsilon successor, so the closure
      invariant is preserved. */
  lemma ClosureInvConsume(c: RB.code, str: string, s: AI.VmState, ov: LOr.OracleView, lid: int,
                          ce: RC.char_expectation)
    requires |s.active| > 0
    requires |s.processed.true_set| == RB.size(c) && |s.processed.false_set| == RB.size(c)
    requires !AI.bpc_mem(s.processed, s.active[0].pc, s.active[0].exit_allowed)
    requires RB.get_instr(c, s.active[0].pc) == RB.Consume(ce)
    requires ClosureInv(c, str, s, ov, lid)
    ensures
      var t := s.active[0];
      var s1 := s.(clock := s.clock + 1, processed := AI.bpc_add(s.processed, t.pc, t.exit_allowed));
      var r := AI.add_thread(t, ce, s1.blocked, s1.isblocked);
      ClosureInv(c, str, s1.(blocked := r.0, isblocked := r.1, active := s.active[1..]), ov, lid)
  {
    var t := s.active[0];
    var s1 := s.(clock := s.clock + 1, processed := AI.bpc_add(s.processed, t.pc, t.exit_allowed));
    var (nb, ni) := AI.add_thread(t, ce, s1.blocked, s1.isblocked);
    var sr := s1.(blocked := nb, isblocked := ni, active := s.active[1..]);
    assert 0 <= t.pc < RB.size(c);
    assert s1.blocked == s.blocked && s1.isblocked == s.isblocked;
    // Inv1: EpsEdge-closed. The new config (t.pc, eb) is a Consume (no EpsEdge).
    forall pc: nat, eb: bool, pc2: nat, eb2: bool
      | InProc(sr, pc, eb) && pc2 < RB.size(c) && EpsEdge(c, str, sr.cp, pc, eb, pc2, eb2)
      ensures InProc(sr, pc2, eb2) || InActive(sr, pc2, eb2)
    {
      BpcAddMem(s.processed, t.pc, t.exit_allowed, pc, eb);
      assert InProc(s, pc, eb);   // pc == t.pc would give i == Consume, no EpsEdge
      BpcAddMem(s.processed, t.pc, t.exit_allowed, pc2, eb2);
      if InActive(s, pc2, eb2) && !InProc(s, pc2, eb2) {
        ActiveHeadTail(s, pc2, eb2);
      }
    }
    // Inv2: every processed Consume config has a blocked entry (sr.blocked == nb).
    forall pc: nat, eb: bool | InProc(sr, pc, eb) && RB.get_instr(c, pc).Consume?
      ensures HasBlockedEntry(c, nb, pc)
    {
      BpcAddMem(s.processed, t.pc, t.exit_allowed, pc, eb);
      if pc == t.pc {
        if AI.pc_mem(s1.isblocked, t.pc) {
          assert nb == s.blocked && AI.pc_mem(s.isblocked, t.pc);   // Inv4(s) gives the entry
        } else {
          assert nb == [(t, ce)] + s.blocked && nb[0] == (t, ce);   // fresh entry at index 0
        }
      } else {
        assert InProc(s, pc, eb);
        assert HasBlockedEntry(c, s.blocked, pc);                    // Inv2(s)
        if !AI.pc_mem(s1.isblocked, t.pc) {
          assert nb == [(t, ce)] + s.blocked;
          BlockedPrependPreserves(c, s.blocked, (t, ce), pc);
        }
      }
    }
    // Inv4: every isblocked label has a blocked entry (sr.isblocked == ni).
    forall q: int | AI.pc_mem(ni, q)
      ensures HasBlockedEntry(c, nb, q)
    {
      if AI.pc_mem(s1.isblocked, t.pc) {
        assert ni == s.isblocked && nb == s.blocked;                 // Inv4(s)
      } else {
        PcAddMem(s.isblocked, t.pc, q);
        assert nb == [(t, ce)] + s.blocked;
        if q == t.pc {
          assert nb[0] == (t, ce);
        } else {
          BlockedPrependPreserves(c, s.blocked, (t, ce), q);
        }
      }
    }
    // Inv3 (WriteOracle): the new config (t.pc) is a Consume, not a WriteOracle.
    forall pc: nat, eb: bool | InProc(sr, pc, eb) && RB.get_instr(c, pc) == RB.WriteOracle(lid)
      ensures LOr.view_get_oracle(ov, sr.cp, lid)
    {
      BpcAddMem(s.processed, t.pc, t.exit_allowed, pc, eb);
      assert InProc(s, pc, eb);
    }
  }

  /** Processing an in-range non-`Consume`, non-`WriteOracle(lid)` head whose
      in-range epsilon successors are all queued (`pre`) or kept (the tail):
      `blocked`/`isblocked`/`ov` are untouched, so the closure invariant is
      preserved. Covers `Jmp`/`Fork`/`Set*`/`BeginLoop`/`EndLoop`/`Anchor`
      (and their drop branches, with `pre == []`). */
  lemma ClosureInvStep(c: RB.code, str: string, s: AI.VmState, ov: LOr.OracleView, lid: int,
                       hpc: nat, heb: bool, pre: seq<AI.Thread>, sr: AI.VmState)
    requires |s.active| > 0
    requires |s.processed.true_set| == RB.size(c) && |s.processed.false_set| == RB.size(c)
    requires ClosureInv(c, str, s, ov, lid)
    requires s.active[0].pc == hpc && s.active[0].exit_allowed == heb
    requires sr.cp == s.cp && sr.blocked == s.blocked && sr.isblocked == s.isblocked
    requires sr.active == pre + s.active[1..]
    requires sr.processed == AI.bpc_add(s.processed, hpc, heb)
    requires !RB.get_instr(c, hpc).Consume? && RB.get_instr(c, hpc) != RB.WriteOracle(lid)
    requires forall pc2: nat, eb2: bool ::
        pc2 < RB.size(c) && EpsEdge(c, str, s.cp, hpc, heb, pc2, eb2)
          ==> InProc(sr, pc2, eb2) || InActive(sr, pc2, eb2)
    ensures ClosureInv(c, str, sr, ov, lid)
  {
    var ac := s.active[1..];
    forall pc: nat, eb: bool, pc2: nat, eb2: bool
      | InProc(sr, pc, eb) && pc2 < RB.size(c) && EpsEdge(c, str, sr.cp, pc, eb, pc2, eb2)
      ensures InProc(sr, pc2, eb2) || InActive(sr, pc2, eb2)
    {
      BpcAddMem(s.processed, hpc, heb, pc, eb);
      if pc == hpc && eb == heb {
        assert EpsEdge(c, str, s.cp, hpc, heb, pc2, eb2);
      } else {
        assert InProc(s, pc, eb);
        BpcAddMem(s.processed, hpc, heb, pc2, eb2);
        if InActive(s, pc2, eb2) && !InProc(s, pc2, eb2) {
          ActiveHeadTail(s, pc2, eb2);
          if !(s.active[0].pc == pc2 && s.active[0].exit_allowed == eb2) {
            var j :| 0 <= j < |ac| && ac[j].pc == pc2 && ac[j].exit_allowed == eb2;
            assert sr.active[|pre| + j] == ac[j];
          }
        }
      }
    }
    forall pc: nat, eb: bool | InProc(sr, pc, eb) && RB.get_instr(c, pc).Consume?
      ensures HasBlockedEntry(c, sr.blocked, pc)
    {
      BpcAddMem(s.processed, hpc, heb, pc, eb);
      assert InProc(s, pc, eb);
    }
    forall q: int | AI.pc_mem(sr.isblocked, q)
      ensures HasBlockedEntry(c, sr.blocked, q)
    {
      assert AI.pc_mem(s.isblocked, q);
    }
    forall pc: nat, eb: bool | InProc(sr, pc, eb) && RB.get_instr(c, pc) == RB.WriteOracle(lid)
      ensures LOr.view_get_oracle(ov, sr.cp, lid)
    {
      BpcAddMem(s.processed, hpc, heb, pc, eb);
      assert InProc(s, pc, eb);
    }
  }

  /** One epsilon closure over classified `NoAccept` code processes every
      queued configuration: P grows to cover P ∪ (in-range) A, the closure ends
      with `active == []`, and the invariant is re-established of the result —
      so `s'.processed` is `EpsEdge`-closed, every processed `Consume` sits in
      `s'.blocked`, and every processed `WriteOracle(lid)`'s bit is set. */
  lemma AdvanceReachComplete(c: RB.code, str: string, s: AI.VmState, ov: LOr.OracleView, lid: int)
    requires |s.processed.true_set| == RB.size(c) && |s.processed.false_set| == RB.size(c)
    requires OS.NoOracleReads(c) && OS.NoCheckNullable(c) && OS.WritesOnlyLid(c, lid) && OS.NoAccept(c)
    requires s.context == CtxAt(str, s.cp)
    requires 0 <= s.cp < |ov| && 0 <= lid < |ov[s.cp]|
    requires ClosureInv(c, str, s, ov, lid)
    ensures var (s', ov') := AI.FAdvanceEpsilon(c, s, ov, LAnc.Forward);
      s'.active == []
      && s'.cp == s.cp
      && (forall pc: nat, eb: bool ::
            InProc(s, pc, eb) || (InActive(s, pc, eb) && pc < RB.size(c)) ==> InProc(s', pc, eb))
      && ClosureInv(c, str, s', ov', lid)
    decreases AI.unprocessed(s.processed), |s.active|
  {
    if |s.active| == 0 { return; }
    var t := s.active[0];
    var ac := s.active[1..];
    var i := RB.get_instr(c, t.pc);
    if AI.bpc_mem(s.processed, t.pc, t.exit_allowed) {
      ClosureInvSkip(c, str, s, ov, lid);
      AdvanceReachComplete(c, str, s.(active := ac), ov, lid);
      return;
    }
    var b0 := s.processed;
    var s1 := s.(clock := s.clock + 1, processed := AI.bpc_add(b0, t.pc, t.exit_allowed));
    AI.UnprocessedAdd(b0, t.pc, t.exit_allowed);
    match i
    case Consume(ce) =>
      var (nb, ni) := AI.add_thread(t, ce, s1.blocked, s1.isblocked);
      ClosureInvConsume(c, str, s, ov, lid, ce);
      AdvanceReachComplete(c, str, s1.(blocked := nb, isblocked := ni, active := ac), ov, lid);
    case Accept =>
      assert 0 <= t.pc < |c| && c[t.pc].Accept?;
      assert false;
    case Jmp(x) =>
      var sr := s1.(active := [t.(pc := x)] + ac);
      assert x >= 0 ==> sr.active[0] == t.(pc := x);
      ClosureInvStep(c, str, s, ov, lid, t.pc, t.exit_allowed, [t.(pc := x)], sr);
      AdvanceReachComplete(c, str, sr, ov, lid);
    case Fork(x, y) =>
      var newt := AI.Thread(x, t.capture_regs, t.look_regs, t.quant_regs, t.exit_allowed);
      var sr := s1.(active := [newt, t.(pc := y)] + ac);
      assert x >= 0 ==> sr.active[0] == newt;
      assert y >= 0 ==> sr.active[1] == t.(pc := y);
      ClosureInvStep(c, str, s, ov, lid, t.pc, t.exit_allowed, [newt, t.(pc := y)], sr);
      AdvanceReachComplete(c, str, sr, ov, lid);
    case SetRegisterToCP(reg) =>
      var t' := t.(capture_regs := AReg.set_reg(t.capture_regs, reg, Some(s1.cp), s1.clock), pc := t.pc + 1);
      var sr := s1.(active := [t'] + ac);
      assert sr.active[0] == t';
      ClosureInvStep(c, str, s, ov, lid, t.pc, t.exit_allowed, [t'], sr);
      AdvanceReachComplete(c, str, sr, ov, lid);
    case SetQuantToClock(q, b) =>
      var ocp := if b then Some(s1.cp) else None;
      var t' := t.(quant_regs := AReg.set_reg(t.quant_regs, q, ocp, s1.clock), pc := t.pc + 1);
      var sr := s1.(active := [t'] + ac);
      assert sr.active[0] == t';
      ClosureInvStep(c, str, s, ov, lid, t.pc, t.exit_allowed, [t'], sr);
      AdvanceReachComplete(c, str, sr, ov, lid);
    case CheckOracle(l) =>
      assert 0 <= t.pc < |c| && c[t.pc].CheckOracle?;
      assert false;
    case NegCheckOracle(l) =>
      assert 0 <= t.pc < |c| && c[t.pc].NegCheckOracle?;
      assert false;
    case WriteOracle(l) =>
      assert 0 <= t.pc < |c| && c[t.pc] == RB.WriteOracle(l);
      assert l == lid;
      OS.ViewSetFacts(ov, s1.cp, l);
      var ov' := LOr.view_set_oracle(ov, s1.cp, l);
      var sr := s1.(active := ac);
      assert LOr.view_get_oracle(ov', s.cp, lid);   // the freshly recorded bit (in range by requires)
      forall pc: nat, eb: bool, pc2: nat, eb2: bool
        | InProc(sr, pc, eb) && pc2 < RB.size(c) && EpsEdge(c, str, sr.cp, pc, eb, pc2, eb2)
        ensures InProc(sr, pc2, eb2) || InActive(sr, pc2, eb2)
      {
        BpcAddMem(b0, t.pc, t.exit_allowed, pc, eb);
        if pc != t.pc || eb != t.exit_allowed {
          assert InProc(s, pc, eb);
          BpcAddMem(b0, t.pc, t.exit_allowed, pc2, eb2);
          if InActive(s, pc2, eb2) && !InProc(s, pc2, eb2) { ActiveHeadTail(s, pc2, eb2); }
        }
      }
      forall pc: nat, eb: bool | InProc(sr, pc, eb) && RB.get_instr(c, pc).Consume?
        ensures HasBlockedEntry(c, sr.blocked, pc)
      {
        BpcAddMem(b0, t.pc, t.exit_allowed, pc, eb);
        assert InProc(s, pc, eb);
      }
      forall q: int | AI.pc_mem(sr.isblocked, q)
        ensures HasBlockedEntry(c, sr.blocked, q)
      {
        assert AI.pc_mem(s.isblocked, q);
      }
      AdvanceReachComplete(c, str, sr, ov', lid);
    case BeginLoop =>
      var sr := s1.(active := [t.(exit_allowed := false, pc := t.pc + 1)] + ac);
      assert sr.active[0] == t.(exit_allowed := false, pc := t.pc + 1);
      ClosureInvStep(c, str, s, ov, lid, t.pc, t.exit_allowed, [t.(exit_allowed := false, pc := t.pc + 1)], sr);
      AdvanceReachComplete(c, str, sr, ov, lid);
    case EndLoop =>
      if t.exit_allowed {
        var sr := s1.(active := [t.(pc := t.pc + 1)] + ac);
        assert sr.active[0] == t.(pc := t.pc + 1);
        ClosureInvStep(c, str, s, ov, lid, t.pc, t.exit_allowed, [t.(pc := t.pc + 1)], sr);
        AdvanceReachComplete(c, str, sr, ov, lid);
      } else {
        var sr := s1.(active := ac);
        ClosureInvStep(c, str, s, ov, lid, t.pc, t.exit_allowed, [], sr);
        AdvanceReachComplete(c, str, sr, ov, lid);
      }
    case CheckNullable(qid) =>
      assert 0 <= t.pc < |c| && c[t.pc].CheckNullable?;
      assert false;
    case AnchorAssertion(a) =>
      if LAnc.is_satisfied(a, s1.context, LAnc.Forward) {
        var sr := s1.(active := [t.(pc := t.pc + 1)] + ac);
        assert sr.active[0] == t.(pc := t.pc + 1);
        ClosureInvStep(c, str, s, ov, lid, t.pc, t.exit_allowed, [t.(pc := t.pc + 1)], sr);
        AdvanceReachComplete(c, str, sr, ov, lid);
      } else {
        var sr := s1.(active := ac);
        ClosureInvStep(c, str, s, ov, lid, t.pc, t.exit_allowed, [], sr);
        AdvanceReachComplete(c, str, sr, ov, lid);
      }
    case Fail =>
      var sr := s1.(active := ac);
      forall pc: nat, eb: bool, pc2: nat, eb2: bool
        | InProc(sr, pc, eb) && pc2 < RB.size(c) && EpsEdge(c, str, sr.cp, pc, eb, pc2, eb2)
        ensures InProc(sr, pc2, eb2) || InActive(sr, pc2, eb2)
      {
        BpcAddMem(b0, t.pc, t.exit_allowed, pc, eb);
        if pc != t.pc || eb != t.exit_allowed {
          assert InProc(s, pc, eb);
          BpcAddMem(b0, t.pc, t.exit_allowed, pc2, eb2);
          if InActive(s, pc2, eb2) && !InProc(s, pc2, eb2) { ActiveHeadTail(s, pc2, eb2); }
        }
      }
      forall pc: nat, eb: bool | InProc(sr, pc, eb) && RB.get_instr(c, pc).Consume?
        ensures HasBlockedEntry(c, sr.blocked, pc)
      {
        BpcAddMem(b0, t.pc, t.exit_allowed, pc, eb);
        assert InProc(s, pc, eb);
      }
      forall q: int | AI.pc_mem(sr.isblocked, q)
        ensures HasBlockedEntry(c, sr.blocked, q)
      {
        assert AI.pc_mem(s.isblocked, q);
      }
      forall pc: nat, eb: bool | InProc(sr, pc, eb) && RB.get_instr(c, pc) == RB.WriteOracle(lid)
        ensures LOr.view_get_oracle(ov, sr.cp, lid)
      {
        BpcAddMem(b0, t.pc, t.exit_allowed, pc, eb);
        assert InProc(s, pc, eb);
      }
      AdvanceReachComplete(c, str, sr, ov, lid);
  }

  /** `FConsume` only prepends to `active`, so any config present survives. */
  lemma FConsumeKeepsActive(s: AI.VmState, pc: int, eb: bool)
    requires exists k :: 0 <= k < |s.active| && s.active[k].pc == pc && s.active[k].exit_allowed == eb
    ensures exists k :: 0 <= k < |AI.FConsume(s).active|
                        && AI.FConsume(s).active[k].pc == pc && AI.FConsume(s).active[k].exit_allowed == eb
    decreases |s.blocked|
  {
    if |s.blocked| == 0 { assert AI.FConsume(s) == s; return; }
    var t := s.blocked[0].0;
    var ce := s.blocked[0].1;
    var s1 := s.(blocked := s.blocked[1..]);
    var k :| 0 <= k < |s.active| && s.active[k].pc == pc && s.active[k].exit_allowed == eb;
    if RC.is_accepted(s1.context.nextchar, ce) {
      var s2 := s1.(active := [t.(exit_allowed := true, pc := t.pc + 1)] + s1.active);
      assert s2.active[k + 1] == s.active[k];
      FConsumeKeepsActive(s2, pc, eb);
      assert AI.FConsume(s) == AI.FConsume(s2);
    } else {
      assert s1.active[k] == s.active[k];
      FConsumeKeepsActive(s1, pc, eb);
      assert AI.FConsume(s) == AI.FConsume(s1);
    }
  }

  /** `FConsume` reactivates EVERY blocked entry whose expectation accepts the
      character at `cp` (it dedups nothing): each accepted entry at pc `p`
      yields an active thread at `(p + 1, exit_allowed := true)` — the consume
      edge's successor. The existence counterpart of `FConsumeReach`. */
  lemma FConsumeReachComplete(s: AI.VmState)
    ensures forall j :: 0 <= j < |s.blocked| && RC.is_accepted(s.context.nextchar, s.blocked[j].1)
      ==> exists k :: 0 <= k < |AI.FConsume(s).active|
                      && AI.FConsume(s).active[k].pc == s.blocked[j].0.pc + 1
                      && AI.FConsume(s).active[k].exit_allowed
    decreases |s.blocked|
  {
    if |s.blocked| == 0 { assert AI.FConsume(s) == s; return; }
    var t := s.blocked[0].0;
    var ce := s.blocked[0].1;
    var s1 := s.(blocked := s.blocked[1..]);
    if RC.is_accepted(s1.context.nextchar, ce) {
      var newthr := t.(exit_allowed := true, pc := t.pc + 1);
      var s2 := s1.(active := [newthr] + s1.active);
      FConsumeReachComplete(s2);
      assert s2.active[0] == newthr;
      FConsumeKeepsActive(s2, t.pc + 1, true);
      assert AI.FConsume(s) == AI.FConsume(s2);
      forall j | 0 <= j < |s.blocked| && RC.is_accepted(s.context.nextchar, s.blocked[j].1)
        ensures exists k :: 0 <= k < |AI.FConsume(s).active|
                            && AI.FConsume(s).active[k].pc == s.blocked[j].0.pc + 1
                            && AI.FConsume(s).active[k].exit_allowed
      {
        if j >= 1 { assert s2.blocked[j - 1] == s.blocked[j]; }
      }
    } else {
      FConsumeReachComplete(s1);
      assert AI.FConsume(s) == AI.FConsume(s1);
      forall j | 0 <= j < |s.blocked| && RC.is_accepted(s.context.nextchar, s.blocked[j].1)
        ensures exists k :: 0 <= k < |AI.FConsume(s).active|
                            && AI.FConsume(s).active[k].pc == s.blocked[j].0.pc + 1
                            && AI.FConsume(s).active[k].exit_allowed
      {
        assert j >= 1;
        assert s1.blocked[j - 1] == s.blocked[j];
      }
    }
  }
}
