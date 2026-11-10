// G2: the look-bank invariant "a set look record is positive" (package
// linden-equiv-look-bank; first proved by the W7 endgame subagent, see
// linden-equiv/endgame/W7-G2-probe.md).
//
// Fragment-agnostic: nothing here assumes NestedFragmentRE, CaptureFreeRE, or
// any shape of a negative body. The only engine fact used is that the sole
// writer of `look_regs` is `CheckOracle(l)` (FAdvanceEpsilon's CheckOracle arm),
// and the only compiler fact is that `compile` emits `CheckOracle(lid)` only for
// a POSITIVE `Re_lookaround(lid, Lookahead|Lookbehind, _)` node.
module LindenElkLookBank {
  import opened Std.Wrappers
  import AI = ArrayInterp
  import AReg = Array_Regs
  import RB = Bytecode
  import LOr = Oracle
  import LAnc = Anchors
  import LCdn = Cdn
  import RC = Charclasses
  import CP = Compiler
  import R = RegElkRegex
  import LTB = LindenElkLookTables
  import CM = LindenElkClockMono

  // ===========================================================================
  // 1. The invariant and the code-shape condition
  // ===========================================================================

  /** Every look record that is set (cp or clock `>= 0`) sits at a lid in `P`. */
  ghost predicate LookSetIn(lk: AReg.Regs, P: set<int>) {
    forall l: int :: (AI.get_idx(lk.a_cp, l) >= 0 || AI.get_idx(lk.a_clk, l) >= 0) ==> l in P
  }

  /** Every `CheckOracle` gate of `c` names a lid in `P` (NegCheckOracle is free). */
  ghost predicate ChecksIn(c: RB.code, P: set<int>) {
    forall pc: nat :: pc < |c| ==> (c[pc].CheckOracle? ==> c[pc].col in P)
  }

  ghost predicate VmLookSetIn(s: AI.VmState, P: set<int>) {
    (forall t | t in s.active :: LookSetIn(t.look_regs, P))
    && (forall tb | tb in s.blocked :: LookSetIn(tb.0.look_regs, P))
    && (s.bestmatch.Some? ==> LookSetIn(s.bestmatch.value.look_regs, P))
  }

  /** `get_cp(lk, l).Some?` is the `a_cp >= 0` reading of the invariant. */
  lemma GetCpSomeIdx(lk: AReg.Regs, l: int)
    ensures AReg.get_cp(lk, l).Some? <==> AI.get_idx(lk.a_cp, l) >= 0
    ensures AReg.get_clock(lk, l).Some? <==> AI.get_idx(lk.a_clk, l) >= 0
  {}

  lemma SetRegLookSetIn(lk: AReg.Regs, l: int, cp: Option<int>, clk: int, P: set<int>)
    requires LookSetIn(lk, P) && l in P
    ensures LookSetIn(AReg.set_reg(lk, l, cp, clk), P)
  {
    var r2 := AReg.set_reg(lk, l, cp, clk);
    forall k: int | AI.get_idx(r2.a_cp, k) >= 0 || AI.get_idx(r2.a_clk, k) >= 0
      ensures k in P
    {
      if k != l {
        CM.SetRegOtherIdx(lk, l, cp, clk, k);
      }
    }
  }

  lemma InitRegsLookSetIn(n: int, P: set<int>)
    ensures LookSetIn(AReg.init_regs(n), P)
  {}

  // ===========================================================================
  // 2. Preservation by FAdvanceEpsilon / FConsume / FFindMatch (both directions)
  // ===========================================================================

  lemma FAdvanceEpsilonLookSetIn(c: RB.code, s: AI.VmState, ov: LOr.OracleView,
                                 dir: LAnc.direction, P: set<int>)
    requires |s.processed.true_set| == RB.size(c) && |s.processed.false_set| == RB.size(c)
    requires ChecksIn(c, P)
    requires VmLookSetIn(s, P)
    ensures VmLookSetIn(AI.FAdvanceEpsilon(c, s, ov, dir).0, P)
    decreases AI.unprocessed(s.processed), |s.active|
  {
    if |s.active| == 0 { return; }
    var t := s.active[0];
    var ac := s.active[1..];
    assert t in s.active;
    assert forall x | x in ac :: x in s.active;
    if AI.bpc_mem(s.processed, t.pc, t.exit_allowed) {
      FAdvanceEpsilonLookSetIn(c, s.(active := ac), ov, dir, P);
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
        assert VmLookSetIn(s2, P) by {
          forall tb | tb in nb ensures LookSetIn(tb.0.look_regs, P) {
            assert tb == (t, ce) || tb in s1.blocked;
          }
        }
        FAdvanceEpsilonLookSetIn(c, s2, ov, dir, P);
      case Accept =>
      case Jmp(x) =>
        FAdvanceEpsilonLookSetIn(c, s1.(active := [t.(pc := x)] + ac), ov, dir, P);
      case Fork(x, y) =>
        var newt := AI.Thread(x, t.capture_regs, t.look_regs, t.quant_regs, t.exit_allowed);
        FAdvanceEpsilonLookSetIn(c, s1.(active := [newt, t.(pc := y)] + ac), ov, dir, P);
      case SetRegisterToCP(reg) =>
        var t2 := t.(capture_regs := AReg.set_reg(t.capture_regs, reg, Some(s1.cp), s1.clock), pc := t.pc + 1);
        FAdvanceEpsilonLookSetIn(c, s1.(active := [t2] + ac), ov, dir, P);
      case SetQuantToClock(q, bq) =>
        var ocp := if bq then Some(s1.cp) else None;
        var t2 := t.(quant_regs := AReg.set_reg(t.quant_regs, q, ocp, s1.clock), pc := t.pc + 1);
        FAdvanceEpsilonLookSetIn(c, s1.(active := [t2] + ac), ov, dir, P);
      case CheckOracle(l) =>
        if LOr.view_get_oracle(ov, s1.cp, l) {
          var t2 := t.(pc := t.pc + 1, look_regs := AReg.set_reg(t.look_regs, l, Some(s1.cp), s1.clock));
          assert 0 <= t.pc < |c|;
          assert l in P;                                      // ChecksIn
          SetRegLookSetIn(t.look_regs, l, Some(s1.cp), s1.clock, P);
          FAdvanceEpsilonLookSetIn(c, s1.(active := [t2] + ac), ov, dir, P);
        } else {
          FAdvanceEpsilonLookSetIn(c, s1.(active := ac), ov, dir, P);
        }
      case NegCheckOracle(l) =>
        if LOr.view_get_oracle(ov, s1.cp, l) {
          FAdvanceEpsilonLookSetIn(c, s1.(active := ac), ov, dir, P);
        } else {
          FAdvanceEpsilonLookSetIn(c, s1.(active := [t.(pc := t.pc + 1)] + ac), ov, dir, P);
        }
      case WriteOracle(l) =>
        FAdvanceEpsilonLookSetIn(c, s1.(active := ac), LOr.view_set_oracle(ov, s1.cp, l), dir, P);
      case BeginLoop =>
        FAdvanceEpsilonLookSetIn(c, s1.(active := [t.(exit_allowed := false, pc := t.pc + 1)] + ac), ov, dir, P);
      case EndLoop =>
        if t.exit_allowed {
          FAdvanceEpsilonLookSetIn(c, s1.(active := [t.(pc := t.pc + 1)] + ac), ov, dir, P);
        } else {
          FAdvanceEpsilonLookSetIn(c, s1.(active := ac), ov, dir, P);
        }
      case CheckNullable(qid) =>
        if LCdn.cdn_get(s1.cdn, qid) {
          FAdvanceEpsilonLookSetIn(c, s1.(active := [t.(pc := t.pc + 1)] + ac), ov, dir, P);
        } else {
          FAdvanceEpsilonLookSetIn(c, s1.(active := ac), ov, dir, P);
        }
      case AnchorAssertion(a) =>
        if LAnc.is_satisfied(a, s1.context, dir) {
          FAdvanceEpsilonLookSetIn(c, s1.(active := [t.(pc := t.pc + 1)] + ac), ov, dir, P);
        } else {
          FAdvanceEpsilonLookSetIn(c, s1.(active := ac), ov, dir, P);
        }
      case Fail =>
        FAdvanceEpsilonLookSetIn(c, s1.(active := ac), ov, dir, P);
    }
  }

  lemma FConsumeLookSetIn(s: AI.VmState, P: set<int>)
    requires VmLookSetIn(s, P)
    ensures VmLookSetIn(AI.FConsume(s), P)
    decreases |s.blocked|
  {
    if |s.blocked| == 0 { return; }
    var t := s.blocked[0].0;
    var ce := s.blocked[0].1;
    var s1 := s.(blocked := s.blocked[1..]);
    assert VmLookSetIn(s1, P) by {
      forall tb | tb in s1.blocked ensures LookSetIn(tb.0.look_regs, P) { assert tb in s.blocked; }
    }
    var s2 := if RC.is_accepted(s1.context.nextchar, ce)
              then s1.(active := [t.(exit_allowed := true, pc := t.pc + 1)] + s1.active)
              else s1;
    assert VmLookSetIn(s2, P) by {
      assert s.blocked[0] in s.blocked;
      assert LookSetIn(t.look_regs, P);
      forall t2 | t2 in s2.active ensures LookSetIn(t2.look_regs, P) {
        if t2 != t.(exit_allowed := true, pc := t.pc + 1) { assert t2 in s1.active; }
      }
    }
    FConsumeLookSetIn(s2, P);
  }

  /** THE engine fact, both directions: a whole search over code whose only
      look writes are `CheckOracle(l)`, `l in P`, returns a winner whose every
      set look record is at a lid in `P`. */
  lemma FFindMatchLookSetIn(c: RB.code, str: string, s: AI.VmState, ov: LOr.OracleView,
                            dir: LAnc.direction, cdn: LCdn.cdns, P: set<int>)
    requires |s.processed.true_set| == RB.size(c) && |s.processed.false_set| == RB.size(c)
    requires dir.Forward? ==> s.context.nextchar == AI.get_char(str, s.cp)
    requires dir.Backward? ==> s.context.nextchar == AI.get_char(str, s.cp - 1)
    requires ChecksIn(c, P)
    requires VmLookSetIn(s, P)
    ensures var r := AI.FFindMatch(c, str, s, ov, dir, cdn).0;
      r.Some? ==> LookSetIn(r.value.look_regs, P)
    decreases if dir.Forward? then |str| - s.cp else s.cp
  {
    var s0 := s.(cdn := LCdn.build_cdn_v(cdn, s.cp, ov, s.context, dir));
    assert VmLookSetIn(s0, P);
    var (s1, ov1) := AI.FAdvanceEpsilon(c, s0, ov, dir);
    FAdvanceEpsilonLookSetIn(c, s0, ov, dir, P);
    assert VmLookSetIn(s1, P);
    if |s1.blocked| == 0 { return; }
    match s1.context.nextchar {
      case None =>
      case Some(_) =>
        var s2 := AI.FConsume(s1);
        FConsumeLookSetIn(s1, P);
        var s3 := s2.(processed := AI.init_bpcset(RB.size(c)), isblocked := AI.init_pcset(RB.size(c)),
                      cdn := LCdn.init_cdn(), cp := AI.incr_cp(s2.cp, dir));
        var newchar := AI.get_char(str, s3.cp - AI.cp_offset(dir));
        var s4 := s3.(context := LAnc.update_context(s3.context, newchar));
        assert VmLookSetIn(s4, P);
        FFindMatchLookSetIn(c, str, s4, ov1, dir, cdn, P);
    }
  }

  // ===========================================================================
  // 3. FReconstructPlus (FNulledPlus / FNulledChildren), FFindMatchPlus, FLookLoop
  // ===========================================================================

  ghost predicate PlusChecksIn(plus_bcv: seq<RB.code>, P: set<int>) {
    forall q | 0 <= q < |plus_bcv| :: ChecksIn(plus_bcv[q], P)
  }

  lemma GetCodeVChecksIn(plus_bcv: seq<RB.code>, q: int, P: set<int>)
    requires PlusChecksIn(plus_bcv, P)
    ensures ChecksIn(AI.get_code_v(plus_bcv, q), P)
  {}

  lemma FNullInterpLookSetIn(bytecode: RB.code, inits: AI.VmState, ov: LOr.OracleView,
                             dir: LAnc.direction, P: set<int>)
    requires |inits.processed.true_set| == RB.size(bytecode) && |inits.processed.false_set| == RB.size(bytecode)
    requires ChecksIn(bytecode, P)
    requires VmLookSetIn(inits, P)
    ensures var r := AI.FNullInterp(bytecode, inits, ov, dir).0;
      r.Some? ==> LookSetIn(r.value.look_regs, P)
  {
    FAdvanceEpsilonLookSetIn(bytecode, inits, ov, dir, P);
  }

  lemma FNulledPlusLookSetIn(reg: R.regex, cap: AReg.Regs, lk: AReg.Regs, qt: AReg.Regs,
                             plus_bcv: seq<RB.code>, str: string, ov: LOr.OracleView,
                             dir: LAnc.direction, P: set<int>)
    requires PlusChecksIn(plus_bcv, P)
    requires LookSetIn(lk, P)
    ensures LookSetIn(AI.FNulledPlus(reg, cap, lk, qt, plus_bcv, str, ov, dir).1, P)
    decreases reg, 1
  {
    match reg
    case Re_empty =>
    case Re_character(_) =>
    case Re_anchor(_) =>
    case Re_lookaround(_, _, _) =>
    case Re_capture(_, r1) =>
      FNulledPlusLookSetIn(r1, cap, lk, qt, plus_bcv, str, ov, dir, P);
    case Re_alt(r1, r2) =>
      var (c1, l1, q1, ov1) := AI.FNulledPlus(r1, cap, lk, qt, plus_bcv, str, ov, dir);
      FNulledPlusLookSetIn(r1, cap, lk, qt, plus_bcv, str, ov, dir, P);
      FNulledPlusLookSetIn(r2, c1, l1, q1, plus_bcv, str, ov1, dir, P);
    case Re_con(r1, r2) =>
      var (c1, l1, q1, ov1) := AI.FNulledPlus(r1, cap, lk, qt, plus_bcv, str, ov, dir);
      FNulledPlusLookSetIn(r1, cap, lk, qt, plus_bcv, str, ov, dir, P);
      FNulledPlusLookSetIn(r2, c1, l1, q1, plus_bcv, str, ov1, dir, P);
    case Re_quant(nul, qid, quanttype, body) =>
      match AReg.get_cp(qt, qid) {
        case None =>
          FNulledPlusLookSetIn(body, cap, lk, qt, plus_bcv, str, ov, dir, P);
        case Some(start_cp) =>
          var start_clock := AI.opt_int(AReg.get_clock(qt, qid));
          var bytecode := AI.get_code_v(plus_bcv, qid);
          var ctx := AI.cp_context(start_cp, str, dir);
          var inits0 := AI.FInitState(bytecode, start_cp, cap, lk, qt, start_clock, ctx);
          var subcdn := LCdn.compile_cdns(body);
          var subtable := LCdn.build_cdn_v(subcdn, start_cp, ov, ctx, dir);
          var inits := inits0.(cdn := subtable);
          GetCodeVChecksIn(plus_bcv, qid, P);
          assert VmLookSetIn(inits, P);
          FNullInterpLookSetIn(bytecode, inits, ov, dir, P);
          var (result, _, ov1) := AI.FNullInterp(bytecode, inits, ov, dir);
          var (ncap, nlk, nqt) := match result
                                  case None => (cap, lk, qt)
                                  case Some(w) => (w.capture_regs, w.look_regs, w.quant_regs);
          assert LookSetIn(nlk, P);
          FNulledChildrenLookSetIn(body, subtable, start_cp, ncap, nlk, nqt, plus_bcv, str, ov1, dir, P);
      }
  }

  lemma FNulledChildrenLookSetIn(reg: R.regex, cdnt: LCdn.cdn_table, cp: int, cap: AReg.Regs,
                                 lk: AReg.Regs, qt: AReg.Regs, plus_bcv: seq<RB.code>, str: string,
                                 ov: LOr.OracleView, dir: LAnc.direction, P: set<int>)
    requires PlusChecksIn(plus_bcv, P)
    requires LookSetIn(lk, P)
    ensures LookSetIn(AI.FNulledChildren(reg, cdnt, cp, cap, lk, qt, plus_bcv, str, ov, dir).1, P)
    decreases reg, 0
  {
    match reg
    case Re_empty =>
    case Re_character(_) =>
    case Re_anchor(_) =>
    case Re_lookaround(_, _, _) =>
    case Re_capture(_, r1) =>
      FNulledChildrenLookSetIn(r1, cdnt, cp, cap, lk, qt, plus_bcv, str, ov, dir, P);
    case Re_alt(r1, r2) =>
      var (c1, l1, q1, ov1) := AI.FNulledChildren(r1, cdnt, cp, cap, lk, qt, plus_bcv, str, ov, dir);
      FNulledChildrenLookSetIn(r1, cdnt, cp, cap, lk, qt, plus_bcv, str, ov, dir, P);
      FNulledChildrenLookSetIn(r2, cdnt, cp, c1, l1, q1, plus_bcv, str, ov1, dir, P);
    case Re_con(r1, r2) =>
      var (c1, l1, q1, ov1) := AI.FNulledChildren(r1, cdnt, cp, cap, lk, qt, plus_bcv, str, ov, dir);
      FNulledChildrenLookSetIn(r1, cdnt, cp, cap, lk, qt, plus_bcv, str, ov, dir, P);
      FNulledChildrenLookSetIn(r2, cdnt, cp, c1, l1, q1, plus_bcv, str, ov1, dir, P);
    case Re_quant(nul, qid, quanttype, body) =>
      match AReg.get_cp(qt, qid) {
        case None =>
          FNulledChildrenLookSetIn(body, cdnt, cp, cap, lk, qt, plus_bcv, str, ov, dir, P);
        case Some(start_cp) =>
          if start_cp == cp {
            var start_clock := AI.opt_int(AReg.get_clock(qt, qid));
            var bytecode := AI.get_code_v(plus_bcv, qid);
            var ctx := AI.cp_context(cp, str, dir);
            var inits0 := AI.FInitState(bytecode, cp, cap, lk, qt, start_clock, ctx);
            var inits := inits0.(cdn := cdnt);
            GetCodeVChecksIn(plus_bcv, qid, P);
            assert VmLookSetIn(inits, P);
            FNullInterpLookSetIn(bytecode, inits, ov, dir, P);
            var (result, _, ov1) := AI.FNullInterp(bytecode, inits, ov, dir);
            var (ncap, nlk, nqt) := match result
                                    case None => (cap, lk, qt)
                                    case Some(w) => (w.capture_regs, w.look_regs, w.quant_regs);
            assert LookSetIn(nlk, P);
            FNulledChildrenLookSetIn(body, cdnt, cp, ncap, nlk, nqt, plus_bcv, str, ov1, dir, P);
          }
      }
  }

  lemma FReconstructPlusLookSetIn(thread: AI.Thread, ast: R.regex, plus_bcv: seq<RB.code>,
                                  str: string, ov: LOr.OracleView, dir: LAnc.direction, P: set<int>)
    requires PlusChecksIn(plus_bcv, P)
    requires LookSetIn(thread.look_regs, P)
    ensures LookSetIn(AI.FReconstructPlus(thread, ast, plus_bcv, str, ov, dir).0.look_regs, P)
  {
    FNulledPlusLookSetIn(ast, thread.capture_regs, thread.look_regs, thread.quant_regs, plus_bcv, str, ov, dir, P);
  }

  lemma FFindMatchPlusLookSetIn(c: RB.code, ast: R.regex, plus_bcv: seq<RB.code>, str: string,
                                ov: LOr.OracleView, dir: LAnc.direction, start_cp: int,
                                capture: AReg.Regs, look: AReg.Regs, quant: AReg.Regs,
                                start_clock: int, cdn: LCdn.cdns, P: set<int>)
    requires ChecksIn(c, P) && PlusChecksIn(plus_bcv, P)
    requires LookSetIn(look, P)
    ensures var r := AI.FFindMatchPlus(c, ast, plus_bcv, str, ov, dir, start_cp, capture, look,
                                       quant, start_clock, cdn).0;
      r.Some? ==> LookSetIn(r.value.look_regs, P)
  {
    var inits := AI.FInitState(c, start_cp, capture, look, quant, start_clock,
                               AI.cp_context(start_cp, str, dir));
    assert VmLookSetIn(inits, P);
    FFindMatchLookSetIn(c, str, inits, ov, dir, cdn, P);
    var (result, ov1) := AI.FFindMatch(c, str, inits, ov, dir, cdn);
    if result.Some? {
      FReconstructPlusLookSetIn(result.value, ast, plus_bcv, str, ov1, dir, P);
    }
  }

  /** The compiled tables a run can execute: main pass, every look's capture
      replay, every nulled-plus reconstruction. (The oracle-BUILD bytecode is
      excluded on purpose: FBuildLids discards its threads.) */
  ghost predicate CrvChecksIn(crv: CP.FCompiled, P: set<int>) {
    ChecksIn(crv.f_main_bc, P)
    && (forall i | 0 <= i < |crv.f_look_capture_bc| :: ChecksIn(crv.f_look_capture_bc[i], P))
    && PlusChecksIn(crv.f_plus_bc, P)
  }

  lemma FLookLoopLookSetIn(crv: CP.FCompiled, str: string, lid: int, maxlook: int,
                           cap: AReg.Regs, lk: AReg.Regs, qt: AReg.Regs, ov: LOr.OracleView,
                           P: set<int>)
    requires CrvChecksIn(crv, P)
    requires LookSetIn(lk, P)
    ensures LookSetIn(AI.FLookLoop(crv, str, lid, maxlook, cap, lk, qt, ov).1, P)
    decreases maxlook - lid
  {
    if lid > maxlook { return; }
    var next := lid + 1;
    match AReg.get_cp(lk, lid) {
      case None =>
        FLookLoopLookSetIn(crv, str, next, maxlook, cap, lk, qt, ov, P);
      case Some(cp) =>
        var looktype := if 0 <= lid < |crv.f_look_types| then crv.f_look_types[lid] else R.Lookahead;
        if AI.capture_type(looktype) {
          var bytecode := AI.get_code_v(crv.f_look_capture_bc, lid);
          var dir := AI.capture_direction(looktype);
          var lookcdn := if 0 <= lid < |crv.f_look_cdns| then crv.f_look_cdns[lid] else [];
          var lookast := if 0 <= lid < |crv.f_look_ast| then crv.f_look_ast[lid] else R.Re_empty;
          assert ChecksIn(bytecode, P);
          FFindMatchPlusLookSetIn(bytecode, lookast, crv.f_plus_bc, str, ov, dir, cp, cap, lk, qt, 0, lookcdn, P);
          var (result, ov1) := AI.FFindMatchPlus(bytecode, lookast, crv.f_plus_bc, str, ov, dir,
                                                 cp, cap, lk, qt, 0, lookcdn);
          var (ncap, nlk, nqt) := match result
                                  case None => (cap, lk, qt)
                                  case Some(t) => (t.capture_regs, t.look_regs, t.quant_regs);
          assert LookSetIn(nlk, P);
          FLookLoopLookSetIn(crv, str, next, maxlook, ncap, nlk, nqt, ov1, P);
        } else {
          FLookLoopLookSetIn(crv, str, next, maxlook, cap, lk, qt, ov, P);
        }
    }
  }

  // ===========================================================================
  // 4. Code shape: compile emits CheckOracle only for POSITIVE look nodes
  //    (fragment-agnostic: no NfaRepRE, no NestedFragmentRE)
  // ===========================================================================

  /** The lids of `r`'s POSITIVE lookaround nodes (any depth). */
  ghost function PosLookIds(r: R.regex): set<int>
    decreases r
  {
    match r
    case Re_empty => {}
    case Re_character(_) => {}
    case Re_anchor(_) => {}
    case Re_alt(r1, r2) => PosLookIds(r1) + PosLookIds(r2)
    case Re_con(r1, r2) => PosLookIds(r1) + PosLookIds(r2)
    case Re_quant(_, _, _, r1) => PosLookIds(r1)
    case Re_capture(_, r1) => PosLookIds(r1)
    case Re_lookaround(lid, la, r1) =>
      (if la.Lookahead? || la.Lookbehind? then {lid} else {}) + PosLookIds(r1)
  }

  ghost predicate TLChecksIn(t: CP.treelist, P: set<int>)
    decreases t
  {
    match t
    case Leaf(l) => forall i | 0 <= i < |l| :: l[i].CheckOracle? ==> l[i].col in P
    case Concat(a, b) => TLChecksIn(a, P) && TLChecksIn(b, P)
  }

  lemma FlattenChecksIn(t: CP.treelist, tail: RB.code, P: set<int>)
    requires TLChecksIn(t, P) && ChecksIn(tail, P)
    ensures ChecksIn(CP.tl_flatten(t, tail), P)
    decreases t
  {
    match t
    case Leaf(l) =>
      var f := l + tail;
      forall pc: nat | pc < |f| ensures (f[pc].CheckOracle? ==> f[pc].col in P) {
        if pc < |l| { assert f[pc] == l[pc]; } else { assert f[pc] == tail[pc - |l|]; }
      }
    case Concat(a, b) =>
      FlattenChecksIn(b, tail, P);
      FlattenChecksIn(a, CP.tl_flatten(b, tail), P);
  }

  lemma Chain2(a: CP.treelist, b: CP.treelist)
    ensures CP.chain([a, b]) == CP.Concat(a, b)
  {
    assert [a, b][..1] == [a];
  }

  lemma Chain3(a: CP.treelist, b: CP.treelist, d: CP.treelist)
    ensures CP.chain([a, b, d]) == CP.Concat(CP.Concat(a, b), d)
  {
    assert [a, b, d][..2] == [a, b];
    Chain2(a, b);
  }

  lemma Chain4(a: CP.treelist, b: CP.treelist, d: CP.treelist, e: CP.treelist)
    ensures CP.chain([a, b, d, e]) == CP.Concat(CP.Concat(CP.Concat(a, b), d), e)
  {
    assert [a, b, d, e][..3] == [a, b, d];
    Chain3(a, b, d);
  }

  lemma Chain3Checks(P: set<int>, a: CP.treelist, b: CP.treelist, d: CP.treelist)
    requires TLChecksIn(a, P) && TLChecksIn(b, P) && TLChecksIn(d, P)
    ensures TLChecksIn(CP.chain([a, b, d]), P)
  {
    Chain3(a, b, d);
    assert TLChecksIn(CP.Concat(a, b), P);
  }

  lemma Chain4Checks(P: set<int>, a: CP.treelist, b: CP.treelist, d: CP.treelist, e: CP.treelist)
    requires TLChecksIn(a, P) && TLChecksIn(b, P) && TLChecksIn(d, P) && TLChecksIn(e, P)
    ensures TLChecksIn(CP.chain([a, b, d, e]), P)
  {
    Chain4(a, b, d, e);
    assert TLChecksIn(CP.Concat(a, b), P);
    assert TLChecksIn(CP.Concat(CP.Concat(a, b), d), P);
  }

  lemma CompileChecksIn(r: R.regex, nextl: RB.Label, ctype: CP.comp_type, P: set<int>)
    requires PosLookIds(r) <= P
    ensures TLChecksIn(CP.compile(r, nextl, ctype).0, P)
    decreases CP.rsize(r), 0
  {
    match r
    case Re_empty =>
    case Re_character(c) =>
    case Re_anchor(a) =>
    case Re_lookaround(lookid, looktype, r1) =>
    case Re_capture(cid, r1) =>
      var (l1, f1) := CP.compile(r1, nextl + 1, ctype);
      CompileChecksIn(r1, nextl + 1, ctype, P);
      Chain3Checks(P, CP.Leaf([RB.SetRegisterToCP(CP.start_reg(cid))]), l1, CP.Leaf([RB.SetRegisterToCP(CP.end_reg(cid))]));
    case Re_con(r1, r2) =>
      var (l1, f1) := CP.compile(r1, nextl, ctype);
      CompileChecksIn(r1, nextl, ctype, P);
      CompileChecksIn(r2, f1, ctype, P);
    case Re_alt(r1, r2) =>
      var (l1, f1) := CP.compile(r1, nextl + 1, ctype);
      var (l2, f2) := CP.compile(r2, f1 + 1, ctype);
      CompileChecksIn(r1, nextl + 1, ctype, P);
      CompileChecksIn(r2, f1 + 1, ctype, P);
      Chain4Checks(P, CP.Leaf([RB.Fork(nextl + 1, f1 + 1)]), l1, CP.Leaf([RB.Jmp(f2)]), l2);
      var lf := CP.Leaf([RB.Fork(nextl + 1, f1 + 1)]);
      var lj := CP.Leaf([RB.Jmp(f2)]);
      assert TLChecksIn(lf, P) && TLChecksIn(lj, P);
      assert TLChecksIn(CP.Concat(lf, l1), P);
      assert TLChecksIn(CP.Concat(CP.Concat(lf, l1), lj), P);
    case Re_quant(nul, qid, quant, r1) =>
      if ctype == CP.Progress {
        if quant.min > 0 && quant.max == None && nul == R.NonNullable {
          var (min_code, min_f) := CP.repeat_min(quant.min - 1, qid, r1, nextl, ctype);
          var (body_code, body_f) := CP.compile(r1, min_f + 1, ctype);
          var fork := if quant.greedy then RB.Fork(min_f, body_f + 1) else RB.Fork(body_f + 1, min_f);
          RepeatMinChecksIn(quant.min - 1, qid, r1, nextl, ctype, P);
          CompileChecksIn(r1, min_f + 1, ctype, P);
          Chain4Checks(P, min_code, CP.Leaf([RB.SetQuantToClock(qid, false)]), body_code, CP.Leaf([fork]));
        } else if quant.min > 0 && quant.max == None && nul == R.CINullable && quant.greedy {
          var (min_code, min_f) := CP.repeat_min(quant.min - 1, qid, r1, nextl, ctype);
          var (body_code, body_f) := CP.compile(r1, min_f + 3, ctype);
          RepeatMinChecksIn(quant.min - 1, qid, r1, nextl, ctype, P);
          CompileChecksIn(r1, min_f + 3, ctype, P);
          Chain4Checks(P, min_code,
                 CP.Leaf([RB.Fork(min_f + 1, body_f + 2), RB.SetQuantToClock(qid, false), RB.BeginLoop]),
                 body_code,
                 CP.Leaf([RB.EndLoop, RB.Fork(min_f + 1, body_f + 3), RB.SetQuantToClock(qid, true)]));
        } else if quant.min > 0 && quant.max == None && nul == R.CDNullable && quant.greedy {
          var (min_code, min_f) := CP.repeat_min(quant.min - 1, qid, r1, nextl, ctype);
          var (body_code, body_f) := CP.compile(r1, min_f + 3, ctype);
          RepeatMinChecksIn(quant.min - 1, qid, r1, nextl, ctype, P);
          CompileChecksIn(r1, min_f + 3, ctype, P);
          Chain4Checks(P, min_code,
                 CP.Leaf([RB.Fork(min_f + 1, body_f + 2), RB.SetQuantToClock(qid, false), RB.BeginLoop]),
                 body_code,
                 CP.Leaf([RB.EndLoop, RB.Fork(min_f + 1, body_f + 4), RB.CheckNullable(qid), RB.SetQuantToClock(qid, true)]));
        } else {
          var (min_code, min_f) := CP.repeat_min(quant.min, qid, r1, nextl, ctype);
          RepeatMinChecksIn(quant.min, qid, r1, nextl, ctype, P);
          match quant.max {
            case None =>
              var (iter_code, iter_f) := CP.compile(r1, min_f + 3, ctype);
              CompileChecksIn(r1, min_f + 3, ctype, P);
              var fork := if quant.greedy then RB.Fork(min_f + 1, iter_f + 2) else RB.Fork(iter_f + 2, min_f + 1);
              Chain4Checks(P, min_code, CP.Leaf([fork, RB.SetQuantToClock(qid, false), RB.BeginLoop]),
                     iter_code, CP.Leaf([RB.EndLoop, RB.Jmp(min_f)]));
            case Some(mx) =>
              RepeatOptChecksIn(mx - quant.min, qid, r1, min_f, ctype, quant.greedy, P);
          }
        }
      } else {
        if quant.min == 0 {
        } else if nul == R.NonNullable {
        } else if quant.max == None && nul == R.CINullable && quant.greedy {
        } else if quant.max == None && nul == R.CDNullable && quant.greedy {
        } else {
          CompileChecksIn(r1, nextl + 1, CP.ReconstructNulled, P);
        }
      }
  }

  lemma RepeatMinChecksIn(min: int, qid: R.quantid, r: R.regex, nextl: RB.Label, ctype: CP.comp_type, P: set<int>)
    requires PosLookIds(r) <= P
    ensures TLChecksIn(CP.repeat_min(min, qid, r, nextl, ctype).0, P)
    decreases CP.rsize(r) + 1, min
  {
    if min <= 0 { return; }
    var (body_code, new_f) := CP.compile(r, nextl + 1, ctype);
    var (next_code, next_f) := CP.repeat_min(min - 1, qid, r, new_f, ctype);
    CompileChecksIn(r, nextl + 1, ctype, P);
    RepeatMinChecksIn(min - 1, qid, r, new_f, ctype, P);
    Chain3Checks(P, CP.Leaf([RB.SetQuantToClock(qid, false)]), body_code, next_code);
  }

  lemma RepeatOptChecksIn(nb: int, qid: R.quantid, r: R.regex, nextl: RB.Label, ctype: CP.comp_type,
                          greedy: bool, P: set<int>)
    requires PosLookIds(r) <= P
    ensures TLChecksIn(CP.repeat_optional(nb, qid, r, nextl, ctype, greedy).0, P)
    decreases CP.rsize(r) + 1, nb
  {
    if nb <= 0 { return; }
    var (body_code, new_f) := CP.compile(r, nextl + 3, ctype);
    var (next_code, next_f) := CP.repeat_optional(nb - 1, qid, r, new_f + 1, ctype, greedy);
    CompileChecksIn(r, nextl + 3, ctype, P);
    RepeatOptChecksIn(nb - 1, qid, r, new_f + 1, ctype, greedy, P);
    var fork := if greedy then RB.Fork(nextl + 1, next_f) else RB.Fork(next_f, nextl + 1);
    Chain4Checks(P, CP.Leaf([fork, RB.SetQuantToClock(qid, false), RB.BeginLoop]), body_code, CP.Leaf([RB.EndLoop]), next_code);
    var lh := CP.Leaf([fork, RB.SetQuantToClock(qid, false), RB.BeginLoop]);
    var le := CP.Leaf([RB.EndLoop]);
    assert TLChecksIn(lh, P) && TLChecksIn(le, P);
    assert TLChecksIn(CP.Concat(lh, body_code), P);
    assert TLChecksIn(CP.Concat(CP.Concat(lh, body_code), le), P);
  }

  lemma CompileToBytecodeChecksIn(r: R.regex, P: set<int>)
    requires PosLookIds(r) <= P
    ensures ChecksIn(CP.compile_to_bytecode(r), P)
  {
    CompileChecksIn(r, 0, CP.Progress, P);
    FlattenChecksIn(CP.compile(r, 0, CP.Progress).0, [RB.Accept], P);
  }

  lemma CompileReconstructChecksIn(r: R.regex, P: set<int>)
    requires PosLookIds(r) <= P
    ensures ChecksIn(CP.compile_reconstruct_nulled(r), P)
  {
    CompileChecksIn(r, 0, CP.ReconstructNulled, P);
    FlattenChecksIn(CP.compile(r, 0, CP.ReconstructNulled).0, [RB.Accept], P);
  }

  lemma ReversePosLookIds(r: R.regex)
    ensures PosLookIds(R.reverse_regex(r)) == PosLookIds(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => ReversePosLookIds(r1); ReversePosLookIds(r2);
    case Re_con(r1, r2) => ReversePosLookIds(r1); ReversePosLookIds(r2);
    case Re_quant(_, _, _, r1) => ReversePosLookIds(r1);
    case Re_capture(_, r1) => ReversePosLookIds(r1);
    case Re_lookaround(_, _, r1) => ReversePosLookIds(r1);
    case _ =>
  }

  lemma CaptureRegexPosLookIds(la: R.lookaround, body: R.regex)
    ensures PosLookIds(CP.capture_regex(la, body)) <= PosLookIds(body)
  {
    ReversePosLookIds(body);
  }

  lemma UpdChecksIn(s: seq<RB.code>, i: int, v: RB.code, P: set<int>)
    requires forall j | 0 <= j < |s| :: ChecksIn(s[j], P)
    requires ChecksIn(v, P)
    ensures forall j | 0 <= j < |CP.upd(s, i, v)| :: ChecksIn(CP.upd(s, i, v)[j], P)
  {}

  lemma FCompileExtraChecksIn(r: R.regex, c: CP.FCompiled, P: set<int>)
    requires PosLookIds(r) <= P
    requires CrvChecksIn(c, P)
    ensures CrvChecksIn(CP.FCompileExtra(r, c), P)
    decreases r
  {
    match r
    case Re_empty =>
    case Re_character(_) =>
    case Re_anchor(_) =>
    case Re_capture(_, r1) => FCompileExtraChecksIn(r1, c, P);
    case Re_alt(r1, r2) =>
      FCompileExtraChecksIn(r1, c, P);
      FCompileExtraChecksIn(r2, CP.FCompileExtra(r1, c), P);
    case Re_con(r1, r2) =>
      FCompileExtraChecksIn(r1, c, P);
      FCompileExtraChecksIn(r2, CP.FCompileExtra(r1, c), P);
    case Re_quant(nul, qid, quant, r1) =>
      var c1 := if quant.min > 0 && quant.max == None && nul != R.NonNullable && quant.greedy
                then c.(f_plus_bc := CP.upd(c.f_plus_bc, qid, CP.compile_reconstruct_nulled(r1)))
                else c;
      CompileReconstructChecksIn(r1, P);
      UpdChecksIn(c.f_plus_bc, qid, CP.compile_reconstruct_nulled(r1), P);
      assert CrvChecksIn(c1, P);
      FCompileExtraChecksIn(r1, c1, P);
    case Re_lookaround(lid, la, body) =>
      var c1 := c.(f_look_types := CP.upd(c.f_look_types, lid, la));
      var c2 := c1.(f_look_cdns := CP.upd(c1.f_look_cdns, lid, LCdn.compile_cdns(body)));
      var c3 := c2.(f_look_ast := CP.upd(c2.f_look_ast, lid, body));
      var c4 := c3.(f_look_build_bc := CP.upd(c3.f_look_build_bc, lid, CP.compile_to_write(CP.oracle_regex(la, body), lid)));
      var capc := CP.compile_to_bytecode(CP.capture_regex(la, body));
      var c5 := c4.(f_look_capture_bc := CP.upd(c4.f_look_capture_bc, lid, capc));
      CaptureRegexPosLookIds(la, body);
      CompileToBytecodeChecksIn(CP.capture_regex(la, body), P);
      UpdChecksIn(c4.f_look_capture_bc, lid, capc, P);
      assert CrvChecksIn(c5, P);
      assert CP.FCompileExtra(r, c) == CP.FCompileExtra(body, c5);
      FCompileExtraChecksIn(body, c5, P);
  }

  /** The whole-pipeline code-shape fact: every table a run executes gates
      `CheckOracle` only on a POSITIVE lid of `r`. No fragment hypothesis. */
  lemma FFullCompilationChecksPos(r: R.regex)
    ensures CrvChecksIn(CP.FFullCompilation(r), PosLookIds(r))
  {
    var P := PosLookIds(r);
    var maxlook := R.max_lookaround(r);
    var maxquant := R.max_quant(r);
    var nlook := if maxlook + 1 >= 0 then maxlook + 1 else 0;
    var nquant := if maxquant + 1 >= 0 then maxquant + 1 else 0;
    var c0 := CP.FCompiled(r, CP.compile_to_bytecode(R.lazy_prefix(r)), LCdn.compile_cdns(r),
                           seq(nlook, i => R.Lookahead), seq(nlook, i => R.Re_empty),
                           seq(nlook, i => []), seq(nlook, i => []),
                           seq(nlook, i => []), seq(nquant, i => []));
    assert PosLookIds(R.lazy_prefix(r)) == P;
    CompileToBytecodeChecksIn(R.lazy_prefix(r), P);
    assert CrvChecksIn(c0, P);
    FCompileExtraChecksIn(r, c0, P);
    assert CP.FFullCompilation(r) == CP.FCompileExtra(r, c0);
  }

  // ===========================================================================
  // 5. The tie from a lid to its row kind: LookTablesOk
  // ===========================================================================

  lemma PosLookIdsTyped(r: R.regex, fc: CP.FCompiled)
    requires LTB.LookTablesOk(r, fc)
    ensures forall l | l in PosLookIds(r) :: 0 <= l < |fc.f_look_types| && AI.capture_type(fc.f_look_types[l])
    decreases r
  {
    match r
    case Re_alt(r1, r2) => PosLookIdsTyped(r1, fc); PosLookIdsTyped(r2, fc);
    case Re_con(r1, r2) => PosLookIdsTyped(r1, fc); PosLookIdsTyped(r2, fc);
    case Re_quant(_, _, _, r1) => PosLookIdsTyped(r1, fc);
    case Re_capture(_, r1) => PosLookIdsTyped(r1, fc);
    case Re_lookaround(lid, la, body) => PosLookIdsTyped(body, fc);
    case _ =>
  }

  /** A NEGATIVE look node's lid is not in `PosLookIds(r)` — under LookTablesOk
      its row says negative, which no positive node could share. */
  lemma NegLidNotPos(r: R.regex, fc: CP.FCompiled, lid: int)
    requires LTB.LookTablesOk(r, fc)
    requires 0 <= lid < |fc.f_look_types| && !AI.capture_type(fc.f_look_types[lid])
    ensures lid !in PosLookIds(r)
  {
    PosLookIdsTyped(r, fc);
  }

  // ===========================================================================
  // 6. End to end: the readout's look bank, at FBuildCapture's FLookLoop
  // ===========================================================================

  /** Every set look record (cp or clock) of `lk` sits at a POSITIVE row of `crv`. */
  ghost predicate LookPosTyped(lk: AReg.Regs, crv: CP.FCompiled) {
    forall l: int :: (AReg.get_cp(lk, l).Some? || AReg.get_clock(lk, l).Some?) ==>
      0 <= l < |crv.f_look_types| && AI.capture_type(crv.f_look_types[l])
  }

  lemma LookSetInTyped(lk: AReg.Regs, P: set<int>, crv: CP.FCompiled)
    requires LookSetIn(lk, P)
    requires forall l | l in P :: 0 <= l < |crv.f_look_types| && AI.capture_type(crv.f_look_types[l])
    ensures LookPosTyped(lk, crv)
  {
    forall l: int | AReg.get_cp(lk, l).Some? || AReg.get_clock(lk, l).Some?
      ensures 0 <= l < |crv.f_look_types| && AI.capture_type(crv.f_look_types[l])
    {
      GetCpSomeIdx(lk, l);
      assert l in P;
    }
  }

  /** The readout corollary: under LookPosTyped, a NEGATIVE row's look clock (what
      `filter_capture` reads through `R.as_arrays`) is `-1`-like, so
      `filter_capture` takes its `look_val < 0 ==> filter_all(r1, ..)` branch. */
  lemma NegLidUnset(lk: AReg.Regs, crv: CP.FCompiled, lid: int)
    requires LookPosTyped(lk, crv)
    requires 0 <= lid < |crv.f_look_types| && !AI.capture_type(crv.f_look_types[lid])
    ensures AI.get_idx(AReg.as_arrays(lk).1, lid) < 0
    ensures AI.get_idx(lk.a_cp, lid) < 0
  {
    GetCpSomeIdx(lk, lid);
  }

  /** FBuildCapture's two look-bank stages (main FFindMatchPlus, then FLookLoop)
      preserve LookSetIn, for ANY compiled record whose executed tables gate
      CheckOracle only inside `P`. */
  lemma BuildCaptureLookSetInGen(crv: CP.FCompiled, P: set<int>, str: string, ov: LOr.OracleView,
                                 max_look: int, cap0: AReg.Regs, lk0: AReg.Regs, qt0: AReg.Regs)
    requires CrvChecksIn(crv, P)
    requires LookSetIn(lk0, P)
    ensures var res := AI.FFindMatchPlus(crv.f_main_bc, crv.f_main_ast, crv.f_plus_bc, str, ov,
                                         LAnc.Forward, 0, cap0, lk0, qt0, 0, crv.f_main_cdns);
      res.0.Some? ==>
        LookSetIn(AI.FLookLoop(crv, str, 1, max_look, res.0.value.capture_regs,
                               res.0.value.look_regs, res.0.value.quant_regs, res.1).1, P)
  {
    FFindMatchPlusLookSetIn(crv.f_main_bc, crv.f_main_ast, crv.f_plus_bc, str, ov, LAnc.Forward, 0,
                            cap0, lk0, qt0, 0, crv.f_main_cdns, P);
    var res := AI.FFindMatchPlus(crv.f_main_bc, crv.f_main_ast, crv.f_plus_bc, str, ov,
                                 LAnc.Forward, 0, cap0, lk0, qt0, 0, crv.f_main_cdns);
    if res.0.Some? {
      var th := res.0.value;
      FLookLoopLookSetIn(crv, str, 1, max_look, th.capture_regs, th.look_regs, th.quant_regs, res.1, P);
    }
  }

  /** The same, at any compiled record `crv` whose executed tables gate only on
      positive lids of `r` and whose rows agree with `r` (LookTablesOk). */
  lemma BuildCaptureLookBankPosAt(r: R.regex, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
                                  max_look: int, cap0: AReg.Regs, qt0: AReg.Regs)
    requires CrvChecksIn(crv, PosLookIds(r))
    requires LTB.LookTablesOk(r, crv)
    ensures var res := AI.FFindMatchPlus(crv.f_main_bc, crv.f_main_ast, crv.f_plus_bc, str, ov,
                                         LAnc.Forward, 0, cap0, AReg.init_regs(max_look + 1), qt0,
                                         0, crv.f_main_cdns);
      res.0.Some? ==>
        LookPosTyped(AI.FLookLoop(crv, str, 1, max_look, res.0.value.capture_regs,
                                  res.0.value.look_regs, res.0.value.quant_regs, res.1).1, crv)
  {
    var P := PosLookIds(r);
    PosLookIdsTyped(r, crv);
    InitRegsLookSetIn(max_look + 1, P);
    BuildCaptureLookSetInGen(crv, P, str, ov, max_look, cap0, AReg.init_regs(max_look + 1), qt0);
    var res := AI.FFindMatchPlus(crv.f_main_bc, crv.f_main_ast, crv.f_plus_bc, str, ov,
                                 LAnc.Forward, 0, cap0, AReg.init_regs(max_look + 1), qt0,
                                 0, crv.f_main_cdns);
    if res.0.Some? {
      LookSetInTyped(AI.FLookLoop(crv, str, 1, max_look, res.0.value.capture_regs,
                                  res.0.value.look_regs, res.0.value.quant_regs, res.1).1, P, crv);
    }
  }

  /** In FBuildCapture of `FFullCompilation(r)` (exactly its register sizes):
      after the main FFindMatchPlus AND the FLookLoop replay, every set look
      record (cp or clock) is at a POSITIVE row. With `NegLidUnset`, a negative
      lid's clock is `< 0` and `filter_capture` takes `filter_all` there. */
  lemma BuildCaptureLookBankPos(r: R.regex, crv: CP.FCompiled, str: string, ov: LOr.OracleView)
    requires crv == CP.FFullCompilation(r)
    requires LTB.LookTablesOk(r, crv)
    ensures var max_look := R.max_lookaround(crv.f_main_ast);
      var res := AI.FFindMatchPlus(crv.f_main_bc, crv.f_main_ast, crv.f_plus_bc, str, ov,
                                   LAnc.Forward, 0, AReg.init_regs(2 * R.max_group(crv.f_main_ast) + 2),
                                   AReg.init_regs(max_look + 1), AReg.init_regs(R.max_quant(crv.f_main_ast) + 1),
                                   0, crv.f_main_cdns);
      res.0.Some? ==>
        LookPosTyped(AI.FLookLoop(crv, str, 1, max_look, res.0.value.capture_regs,
                                  res.0.value.look_regs, res.0.value.quant_regs, res.1).1, crv)
  {
    hide *;
    FFullCompilationChecksPos(r);
    BuildCaptureLookBankPosAt(r, crv, str, ov, R.max_lookaround(crv.f_main_ast),
                              AReg.init_regs(2 * R.max_group(crv.f_main_ast) + 2),
                              AReg.init_regs(R.max_quant(crv.f_main_ast) + 1));
  }
}
