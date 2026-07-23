// Lookaround campaign (L1), oracle theorem part C1: sweep-level frame and
// independence facts for the oracle-build runs.
//
// A build pass (FBuildLids iteration) runs FFindMatch over
// compile_to_write(oracle_regex(la, body), lid) — code that, for L1's
// look-free bodies, contains NO oracle reads (CheckOracle/NegCheckOracle) and
// NO CheckNullable (plus-fragment bodies exclude the nullable-plus schemes),
// and whose ONLY WriteOracle is the final WriteOracle(lid). This file proves
// the three consequences the oracle-correctness theorem is assembled from:
//
//   1. Monotone + column frame (AdvanceOracleFrame / FindMatchOracleFrame):
//      a run only ADDS bits, only in column `lid`, and — per epsilon
//      closure — only at the CURRENT cp. So FBuildLids' per-lid runs cannot
//      disturb each other's columns, and the lid-induction over nesting
//      degenerates to per-lid independence for non-nested lookarounds.
//
//   2. Oracle independence (AdvanceOvIndep / FindMatchOvIndep): with no
//      oracle reads and no CheckNullable, the THREAD evolution (and hence
//      bestmatch, and the positions written) is the same against any two
//      oracle views — the cdn table may differ arbitrarily (it is only ever
//      consulted by CheckNullable). So each column of FBuildOracle is a
//      function of (build bytecode, str) alone, characterizable against the
//      pristine view.
//
// Proofs are structural inductions mirroring FAdvanceEpsilon's own recursion,
// in the style of ClockMono.
include "RegElkImports.dfy"

/** Sweep-level frame/independence facts for oracle-build runs: a build pass
    only adds bits, only in its own lid column, only at the current cp per
    closure; and with no oracle-reading or cdn-reading instructions its thread
    evolution and written positions are independent of the oracle view. */
module LindenElkOracleSweep {
  import opened Std.Wrappers
  import AI = ArrayInterp
  import RB = Bytecode
  import LOr = Oracle
  import LAnc = Anchors
  import LCdn = Cdn
  import RC = Charclasses
  import AReg = Array_Regs

  // ===========================================================================
  // Code classification
  // ===========================================================================

  /** No oracle-consulting instruction anywhere in `c` — compiled look-free
      bodies satisfy this. */
  ghost predicate NoOracleReads(c: RB.code) {
    forall pc :: 0 <= pc < |c| ==> !c[pc].CheckOracle? && !c[pc].NegCheckOracle?
  }

  /** No `CheckNullable` anywhere in `c` — compiled plus-fragment bodies
      satisfy this (the fragment excludes the nullable-plus schemes), making
      the run's behaviour independent of the cdn table. */
  ghost predicate NoCheckNullable(c: RB.code) {
    forall pc :: 0 <= pc < |c| ==> !c[pc].CheckNullable?
  }

  /** Every `WriteOracle` in `c` writes column `lid` — `compile_to_write`'s
      output over a look-free body has exactly one, the final recorder. */
  ghost predicate WritesOnlyLid(c: RB.code, lid: int) {
    forall pc :: 0 <= pc < |c| ==> (c[pc].WriteOracle? ==> c[pc].wol == lid)
  }

  // ===========================================================================
  // Oracle-view plumbing
  // ===========================================================================

  /** `a` and `b` have identical row structure (so in-range tests agree). */
  ghost predicate SameShape(a: LOr.OracleView, b: LOr.OracleView) {
    |a| == |b| && forall i :: 0 <= i < |a| ==> |a[i]| == |b[i]|
  }

  /** Every bit of `a` is a bit of `b`. */
  ghost predicate Submap(a: LOr.OracleView, b: LOr.OracleView) {
    forall cp: int, l: int :: LOr.view_get_oracle(a, cp, l) ==> LOr.view_get_oracle(b, cp, l)
  }

  /** `view_set_oracle` adds exactly the in-range bit `(cp, l)` and preserves
      the view's shape. */
  lemma ViewSetFacts(ov: LOr.OracleView, cp: int, l: int)
    ensures var ov' := LOr.view_set_oracle(ov, cp, l);
      SameShape(ov, ov')
      && (forall cp2: int, l2: int ::
            LOr.view_get_oracle(ov', cp2, l2)
            == (LOr.view_get_oracle(ov, cp2, l2)
                || (cp2 == cp && l2 == l && 0 <= cp < |ov| && 0 <= l < |ov[cp]|)))
  {}

  // ===========================================================================
  // 1. Monotone + column frame + per-closure cp-locality
  // ===========================================================================

  /** One epsilon closure only ADDS bits, only in column `lid`, and only at
      the closure's (fixed) current `cp`. */
  lemma AdvanceOracleFrame(c: RB.code, s: AI.VmState, ov: LOr.OracleView, dir: LAnc.direction, lid: int)
    requires |s.processed.true_set| == RB.size(c) && |s.processed.false_set| == RB.size(c)
    requires WritesOnlyLid(c, lid)
    ensures var (s', ov') := AI.FAdvanceEpsilon(c, s, ov, dir);
      SameShape(ov, ov') && Submap(ov, ov')
      && (forall cp2: int, l2: int :: l2 != lid ==>
            LOr.view_get_oracle(ov', cp2, l2) == LOr.view_get_oracle(ov, cp2, l2))
      && (forall cp2: int :: cp2 != s.cp ==>
            LOr.view_get_oracle(ov', cp2, lid) == LOr.view_get_oracle(ov, cp2, lid))
    decreases AI.unprocessed(s.processed), |s.active|
  {
    if |s.active| == 0 { return; }
    var t := s.active[0];
    var ac := s.active[1..];
    var i := RB.get_instr(c, t.pc);
    if AI.bpc_mem(s.processed, t.pc, t.exit_allowed) {
      AdvanceOracleFrame(c, s.(active := ac), ov, dir, lid);
      return;
    }
    var b0 := s.processed;
    var s1 := s.(clock := s.clock + 1, processed := AI.bpc_add(b0, t.pc, t.exit_allowed));
    AI.UnprocessedAdd(b0, t.pc, t.exit_allowed);
    match i
    case Consume(ce) =>
      var (nb, ni) := AI.add_thread(t, ce, s1.blocked, s1.isblocked);
      AdvanceOracleFrame(c, s1.(blocked := nb, isblocked := ni, active := ac), ov, dir, lid);
    case Accept =>
    case Jmp(x) =>
      AdvanceOracleFrame(c, s1.(active := [t.(pc := x)] + ac), ov, dir, lid);
    case Fork(x, y) =>
      var newt := AI.Thread(x, t.capture_regs, t.look_regs, t.quant_regs, t.exit_allowed);
      AdvanceOracleFrame(c, s1.(active := [newt, t.(pc := y)] + ac), ov, dir, lid);
    case SetRegisterToCP(reg) =>
      var t' := t.(capture_regs := AReg.set_reg(t.capture_regs, reg, Some(s1.cp), s1.clock), pc := t.pc + 1);
      AdvanceOracleFrame(c, s1.(active := [t'] + ac), ov, dir, lid);
    case SetQuantToClock(q, b) =>
      var ocp := if b then Some(s1.cp) else None;
      var t' := t.(quant_regs := AReg.set_reg(t.quant_regs, q, ocp, s1.clock), pc := t.pc + 1);
      AdvanceOracleFrame(c, s1.(active := [t'] + ac), ov, dir, lid);
    case CheckOracle(l) =>
      if LOr.view_get_oracle(ov, s1.cp, l) {
        var t' := t.(pc := t.pc + 1, look_regs := AReg.set_reg(t.look_regs, l, Some(s1.cp), s1.clock));
        AdvanceOracleFrame(c, s1.(active := [t'] + ac), ov, dir, lid);
      } else {
        AdvanceOracleFrame(c, s1.(active := ac), ov, dir, lid);
      }
    case NegCheckOracle(l) =>
      if LOr.view_get_oracle(ov, s1.cp, l) {
        AdvanceOracleFrame(c, s1.(active := ac), ov, dir, lid);
      } else {
        AdvanceOracleFrame(c, s1.(active := [t.(pc := t.pc + 1)] + ac), ov, dir, lid);
      }
    case WriteOracle(l) =>
      // in-range pc (out-of-range reads Fail), so l == lid by WritesOnlyLid
      assert 0 <= t.pc < |c| && c[t.pc] == RB.WriteOracle(l);
      ViewSetFacts(ov, s1.cp, l);
      AdvanceOracleFrame(c, s1.(active := ac), LOr.view_set_oracle(ov, s1.cp, l), dir, lid);
    case BeginLoop =>
      AdvanceOracleFrame(c, s1.(active := [t.(exit_allowed := false, pc := t.pc + 1)] + ac), ov, dir, lid);
    case EndLoop =>
      if t.exit_allowed {
        AdvanceOracleFrame(c, s1.(active := [t.(pc := t.pc + 1)] + ac), ov, dir, lid);
      } else {
        AdvanceOracleFrame(c, s1.(active := ac), ov, dir, lid);
      }
    case CheckNullable(qid) =>
      if LCdn.cdn_get(s1.cdn, qid) {
        AdvanceOracleFrame(c, s1.(active := [t.(pc := t.pc + 1)] + ac), ov, dir, lid);
      } else {
        AdvanceOracleFrame(c, s1.(active := ac), ov, dir, lid);
      }
    case AnchorAssertion(a) =>
      if LAnc.is_satisfied(a, s1.context, dir) {
        AdvanceOracleFrame(c, s1.(active := [t.(pc := t.pc + 1)] + ac), ov, dir, lid);
      } else {
        AdvanceOracleFrame(c, s1.(active := ac), ov, dir, lid);
      }
    case Fail =>
      AdvanceOracleFrame(c, s1.(active := ac), ov, dir, lid);
  }

  /** A whole build run only ADDS bits, and only in column `lid`. */
  lemma FindMatchOracleFrame(c: RB.code, str: string, s: AI.VmState, ov: LOr.OracleView,
                             dir: LAnc.direction, cdn: LCdn.cdns, lid: int)
    requires |s.processed.true_set| == RB.size(c) && |s.processed.false_set| == RB.size(c)
    requires dir.Forward? ==> s.context.nextchar == AI.get_char(str, s.cp)
    requires dir.Backward? ==> s.context.nextchar == AI.get_char(str, s.cp - 1)
    requires WritesOnlyLid(c, lid)
    ensures var (_, ov') := AI.FFindMatch(c, str, s, ov, dir, cdn);
      SameShape(ov, ov') && Submap(ov, ov')
      && (forall cp2: int, l2: int :: l2 != lid ==>
            LOr.view_get_oracle(ov', cp2, l2) == LOr.view_get_oracle(ov, cp2, l2))
    decreases if dir.Forward? then |str| - s.cp else s.cp
  {
    var s0 := s.(cdn := LCdn.build_cdn_v(cdn, s.cp, ov, s.context, dir));
    var (s1, ov1) := AI.FAdvanceEpsilon(c, s0, ov, dir);
    AdvanceOracleFrame(c, s0, ov, dir, lid);
    if |s1.blocked| == 0 { return; }
    match s1.context.nextchar
    case None =>
    case Some(_) =>
      var s2 := AI.FConsume(s1);
      var s3 := s2.(processed := AI.init_bpcset(RB.size(c)), isblocked := AI.init_pcset(RB.size(c)),
                    cdn := LCdn.init_cdn(), cp := AI.incr_cp(s2.cp, dir));
      var newchar := AI.get_char(str, s3.cp - AI.cp_offset(dir));
      var s4 := s3.(context := LAnc.update_context(s3.context, newchar));
      FindMatchOracleFrame(c, str, s4, ov1, dir, cdn, lid);
  }

  // ===========================================================================
  // 2. Oracle independence of the thread evolution and written positions
  // ===========================================================================

  /** `s1` and `s2` agree on everything the step function reads except the cdn
      table (only ever consulted by `CheckNullable`, which the build code
      lacks). */
  ghost predicate SameModCdn(s1: AI.VmState, s2: AI.VmState) {
    s1.cp == s2.cp && s1.active == s2.active && s1.processed == s2.processed
    && s1.blocked == s2.blocked && s1.isblocked == s2.isblocked
    && s1.bestmatch == s2.bestmatch && s1.context == s2.context && s1.clock == s2.clock
  }

  /** `a1/a2` and `b1/b2` agree at cell `(cp, l)` — the relational invariant
      the independence lemmas preserve: two runs make the same write calls, so
      any cell on which the input views agree still agrees on the outputs.
      (Bitwise-NEW-bits equality would be false at cells where the inputs
      already differ.) */
  ghost predicate CellAgree(a: LOr.OracleView, b: LOr.OracleView, cp: int, l: int) {
    LOr.view_get_oracle(a, cp, l) == LOr.view_get_oracle(b, cp, l)
  }

  /** With no oracle reads and no `CheckNullable`, one epsilon closure evolves
      the threads identically against any two oracle views (of equal shape),
      making the same write calls — so cellwise agreement of the views is
      preserved. */
  lemma AdvanceOvIndep(c: RB.code, s1: AI.VmState, s2: AI.VmState,
                       ov1: LOr.OracleView, ov2: LOr.OracleView, dir: LAnc.direction)
    requires |s1.processed.true_set| == RB.size(c) && |s1.processed.false_set| == RB.size(c)
    requires NoOracleReads(c) && NoCheckNullable(c)
    requires SameModCdn(s1, s2)
    requires SameShape(ov1, ov2)
    ensures var (s1', ov1') := AI.FAdvanceEpsilon(c, s1, ov1, dir);
            var (s2', ov2') := AI.FAdvanceEpsilon(c, s2, ov2, dir);
      SameModCdn(s1', s2') && s1'.cdn == s1.cdn && s2'.cdn == s2.cdn
      && SameShape(ov1, ov1') && SameShape(ov2, ov2')
      && (forall cp2: int, l2: int :: CellAgree(ov1, ov2, cp2, l2) ==> CellAgree(ov1', ov2', cp2, l2))
    decreases AI.unprocessed(s1.processed), |s1.active|
  {
    if |s1.active| == 0 { return; }
    var t := s1.active[0];
    var ac := s1.active[1..];
    var i := RB.get_instr(c, t.pc);
    if AI.bpc_mem(s1.processed, t.pc, t.exit_allowed) {
      AdvanceOvIndep(c, s1.(active := ac), s2.(active := ac), ov1, ov2, dir);
      return;
    }
    var b0 := s1.processed;
    var s1a := s1.(clock := s1.clock + 1, processed := AI.bpc_add(b0, t.pc, t.exit_allowed));
    var s2a := s2.(clock := s2.clock + 1, processed := AI.bpc_add(b0, t.pc, t.exit_allowed));
    AI.UnprocessedAdd(b0, t.pc, t.exit_allowed);
    match i
    case Consume(ce) =>
      var (nb, ni) := AI.add_thread(t, ce, s1a.blocked, s1a.isblocked);
      AdvanceOvIndep(c, s1a.(blocked := nb, isblocked := ni, active := ac),
                     s2a.(blocked := nb, isblocked := ni, active := ac), ov1, ov2, dir);
    case Accept =>
    case Jmp(x) =>
      AdvanceOvIndep(c, s1a.(active := [t.(pc := x)] + ac), s2a.(active := [t.(pc := x)] + ac), ov1, ov2, dir);
    case Fork(x, y) =>
      var newt := AI.Thread(x, t.capture_regs, t.look_regs, t.quant_regs, t.exit_allowed);
      AdvanceOvIndep(c, s1a.(active := [newt, t.(pc := y)] + ac),
                     s2a.(active := [newt, t.(pc := y)] + ac), ov1, ov2, dir);
    case SetRegisterToCP(reg) =>
      var t' := t.(capture_regs := AReg.set_reg(t.capture_regs, reg, Some(s1a.cp), s1a.clock), pc := t.pc + 1);
      AdvanceOvIndep(c, s1a.(active := [t'] + ac), s2a.(active := [t'] + ac), ov1, ov2, dir);
    case SetQuantToClock(q, b) =>
      var ocp := if b then Some(s1a.cp) else None;
      var t' := t.(quant_regs := AReg.set_reg(t.quant_regs, q, ocp, s1a.clock), pc := t.pc + 1);
      AdvanceOvIndep(c, s1a.(active := [t'] + ac), s2a.(active := [t'] + ac), ov1, ov2, dir);
    case CheckOracle(l) =>
      assert 0 <= t.pc < |c| && c[t.pc].CheckOracle?;
      assert false;
    case NegCheckOracle(l) =>
      assert 0 <= t.pc < |c| && c[t.pc].NegCheckOracle?;
      assert false;
    case WriteOracle(l) =>
      ViewSetFacts(ov1, s1a.cp, l);
      ViewSetFacts(ov2, s2a.cp, l);
      // in-range tests at the written cell agree by SameShape
      assert 0 <= s1a.cp < |ov1| ==> |ov1[s1a.cp]| == |ov2[s1a.cp]|;
      AdvanceOvIndep(c, s1a.(active := ac), s2a.(active := ac),
                     LOr.view_set_oracle(ov1, s1a.cp, l), LOr.view_set_oracle(ov2, s2a.cp, l), dir);
    case BeginLoop =>
      AdvanceOvIndep(c, s1a.(active := [t.(exit_allowed := false, pc := t.pc + 1)] + ac),
                     s2a.(active := [t.(exit_allowed := false, pc := t.pc + 1)] + ac), ov1, ov2, dir);
    case EndLoop =>
      if t.exit_allowed {
        AdvanceOvIndep(c, s1a.(active := [t.(pc := t.pc + 1)] + ac),
                       s2a.(active := [t.(pc := t.pc + 1)] + ac), ov1, ov2, dir);
      } else {
        AdvanceOvIndep(c, s1a.(active := ac), s2a.(active := ac), ov1, ov2, dir);
      }
    case CheckNullable(qid) =>
      assert 0 <= t.pc < |c| && c[t.pc].CheckNullable?;
      assert false;
    case AnchorAssertion(a) =>
      if LAnc.is_satisfied(a, s1a.context, dir) {
        AdvanceOvIndep(c, s1a.(active := [t.(pc := t.pc + 1)] + ac),
                       s2a.(active := [t.(pc := t.pc + 1)] + ac), ov1, ov2, dir);
      } else {
        AdvanceOvIndep(c, s1a.(active := ac), s2a.(active := ac), ov1, ov2, dir);
      }
    case Fail =>
      AdvanceOvIndep(c, s1a.(active := ac), s2a.(active := ac), ov1, ov2, dir);
  }

  /** With no oracle reads and no `CheckNullable`, a whole build run returns
      the same result thread and preserves cellwise agreement of the views —
      so each `FBuildOracle` column is a function of the build bytecode and
      the string alone (transfer any run to the pristine view on the cells
      where they start equal). */
  lemma FindMatchOvIndep(c: RB.code, str: string, s1: AI.VmState, s2: AI.VmState,
                         ov1: LOr.OracleView, ov2: LOr.OracleView,
                         dir: LAnc.direction, cdn1: LCdn.cdns, cdn2: LCdn.cdns)
    requires |s1.processed.true_set| == RB.size(c) && |s1.processed.false_set| == RB.size(c)
    requires dir.Forward? ==> s1.context.nextchar == AI.get_char(str, s1.cp)
    requires dir.Backward? ==> s1.context.nextchar == AI.get_char(str, s1.cp - 1)
    requires NoOracleReads(c) && NoCheckNullable(c)
    requires SameModCdn(s1, s2)
    requires SameShape(ov1, ov2)
    ensures var (r1, ov1') := AI.FFindMatch(c, str, s1, ov1, dir, cdn1);
            var (r2, ov2') := AI.FFindMatch(c, str, s2, ov2, dir, cdn2);
      r1 == r2
      && SameShape(ov1, ov1') && SameShape(ov2, ov2')
      && (forall cp2: int, l2: int :: CellAgree(ov1, ov2, cp2, l2) ==> CellAgree(ov1', ov2', cp2, l2))
    decreases if dir.Forward? then |str| - s1.cp else s1.cp
  {
    var s10 := s1.(cdn := LCdn.build_cdn_v(cdn1, s1.cp, ov1, s1.context, dir));
    var s20 := s2.(cdn := LCdn.build_cdn_v(cdn2, s2.cp, ov2, s2.context, dir));
    var (s1', ov1') := AI.FAdvanceEpsilon(c, s10, ov1, dir);
    var (s2', ov2') := AI.FAdvanceEpsilon(c, s20, ov2, dir);
    AdvanceOvIndep(c, s10, s20, ov1, ov2, dir);
    if |s1'.blocked| == 0 { return; }
    match s1'.context.nextchar
    case None =>
    case Some(_) =>
      var s12 := AI.FConsume(s1');
      var s22 := AI.FConsume(s2');
      FConsumeSameModCdn(s1', s2');
      var s13 := s12.(processed := AI.init_bpcset(RB.size(c)), isblocked := AI.init_pcset(RB.size(c)),
                      cdn := LCdn.init_cdn(), cp := AI.incr_cp(s12.cp, dir));
      var s23 := s22.(processed := AI.init_bpcset(RB.size(c)), isblocked := AI.init_pcset(RB.size(c)),
                      cdn := LCdn.init_cdn(), cp := AI.incr_cp(s22.cp, dir));
      var newchar := AI.get_char(str, s13.cp - AI.cp_offset(dir));
      var s14 := s13.(context := LAnc.update_context(s13.context, newchar));
      var s24 := s23.(context := LAnc.update_context(s23.context, newchar));
      FindMatchOvIndep(c, str, s14, s24, ov1', ov2', dir, cdn1, cdn2);
  }

  /** `FConsume` preserves `SameModCdn` (it never reads the cdn table). */
  lemma FConsumeSameModCdn(s1: AI.VmState, s2: AI.VmState)
    requires SameModCdn(s1, s2)
    ensures SameModCdn(AI.FConsume(s1), AI.FConsume(s2))
    decreases |s1.blocked|
  {
    if |s1.blocked| == 0 { return; }
    var t := s1.blocked[0].0;
    var ce := s1.blocked[0].1;
    var s11 := s1.(blocked := s1.blocked[1..]);
    var s21 := s2.(blocked := s2.blocked[1..]);
    if RC.is_accepted(s11.context.nextchar, ce) {
      FConsumeSameModCdn(s11.(active := [t.(exit_allowed := true, pc := t.pc + 1)] + s11.active),
                         s21.(active := [t.(exit_allowed := true, pc := t.pc + 1)] + s21.active));
    } else {
      FConsumeSameModCdn(s11, s21);
    }
  }

  /** A run against ANY code never clears a bit and never changes the view's
      shape — monotonicity without side conditions, for composing NewBit
      across steps. */
  lemma MonoAny(c: RB.code, str: string, s: AI.VmState, ov: LOr.OracleView,
                dir: LAnc.direction, cdn: LCdn.cdns)
    requires |s.processed.true_set| == RB.size(c) && |s.processed.false_set| == RB.size(c)
    requires dir.Forward? ==> s.context.nextchar == AI.get_char(str, s.cp)
    requires dir.Backward? ==> s.context.nextchar == AI.get_char(str, s.cp - 1)
    ensures var (_, ov') := AI.FFindMatch(c, str, s, ov, dir, cdn);
      SameShape(ov, ov') && Submap(ov, ov')
    decreases if dir.Forward? then |str| - s.cp else s.cp
  {
    var s0 := s.(cdn := LCdn.build_cdn_v(cdn, s.cp, ov, s.context, dir));
    var (s1, ov1) := AI.FAdvanceEpsilon(c, s0, ov, dir);
    AdvanceMonoAny(c, s0, ov, dir);
    if |s1.blocked| == 0 { return; }
    match s1.context.nextchar
    case None =>
    case Some(_) =>
      var s2 := AI.FConsume(s1);
      var s3 := s2.(processed := AI.init_bpcset(RB.size(c)), isblocked := AI.init_pcset(RB.size(c)),
                    cdn := LCdn.init_cdn(), cp := AI.incr_cp(s2.cp, dir));
      var newchar := AI.get_char(str, s3.cp - AI.cp_offset(dir));
      var s4 := s3.(context := LAnc.update_context(s3.context, newchar));
      MonoAny(c, str, s4, ov1, dir, cdn);
  }

  /** One closure against ANY code never clears a bit and never changes the
      view's shape. */
  lemma AdvanceMonoAny(c: RB.code, s: AI.VmState, ov: LOr.OracleView, dir: LAnc.direction)
    requires |s.processed.true_set| == RB.size(c) && |s.processed.false_set| == RB.size(c)
    ensures var (s', ov') := AI.FAdvanceEpsilon(c, s, ov, dir);
      SameShape(ov, ov') && Submap(ov, ov')
    decreases AI.unprocessed(s.processed), |s.active|
  {
    if |s.active| == 0 { return; }
    var t := s.active[0];
    var ac := s.active[1..];
    var i := RB.get_instr(c, t.pc);
    if AI.bpc_mem(s.processed, t.pc, t.exit_allowed) {
      AdvanceMonoAny(c, s.(active := ac), ov, dir);
      return;
    }
    var b0 := s.processed;
    var s1 := s.(clock := s.clock + 1, processed := AI.bpc_add(b0, t.pc, t.exit_allowed));
    AI.UnprocessedAdd(b0, t.pc, t.exit_allowed);
    match i
    case Consume(ce) =>
      var (nb, ni) := AI.add_thread(t, ce, s1.blocked, s1.isblocked);
      AdvanceMonoAny(c, s1.(blocked := nb, isblocked := ni, active := ac), ov, dir);
    case Accept =>
    case Jmp(x) =>
      AdvanceMonoAny(c, s1.(active := [t.(pc := x)] + ac), ov, dir);
    case Fork(x, y) =>
      var newt := AI.Thread(x, t.capture_regs, t.look_regs, t.quant_regs, t.exit_allowed);
      AdvanceMonoAny(c, s1.(active := [newt, t.(pc := y)] + ac), ov, dir);
    case SetRegisterToCP(reg) =>
      var t' := t.(capture_regs := AReg.set_reg(t.capture_regs, reg, Some(s1.cp), s1.clock), pc := t.pc + 1);
      AdvanceMonoAny(c, s1.(active := [t'] + ac), ov, dir);
    case SetQuantToClock(q, b) =>
      var ocp := if b then Some(s1.cp) else None;
      var t' := t.(quant_regs := AReg.set_reg(t.quant_regs, q, ocp, s1.clock), pc := t.pc + 1);
      AdvanceMonoAny(c, s1.(active := [t'] + ac), ov, dir);
    case CheckOracle(l) =>
      if LOr.view_get_oracle(ov, s1.cp, l) {
        var t' := t.(pc := t.pc + 1, look_regs := AReg.set_reg(t.look_regs, l, Some(s1.cp), s1.clock));
        AdvanceMonoAny(c, s1.(active := [t'] + ac), ov, dir);
      } else {
        AdvanceMonoAny(c, s1.(active := ac), ov, dir);
      }
    case NegCheckOracle(l) =>
      if LOr.view_get_oracle(ov, s1.cp, l) {
        AdvanceMonoAny(c, s1.(active := ac), ov, dir);
      } else {
        AdvanceMonoAny(c, s1.(active := [t.(pc := t.pc + 1)] + ac), ov, dir);
      }
    case WriteOracle(l) =>
      ViewSetFacts(ov, s1.cp, l);
      AdvanceMonoAny(c, s1.(active := ac), LOr.view_set_oracle(ov, s1.cp, l), dir);
    case BeginLoop =>
      AdvanceMonoAny(c, s1.(active := [t.(exit_allowed := false, pc := t.pc + 1)] + ac), ov, dir);
    case EndLoop =>
      if t.exit_allowed {
        AdvanceMonoAny(c, s1.(active := [t.(pc := t.pc + 1)] + ac), ov, dir);
      } else {
        AdvanceMonoAny(c, s1.(active := ac), ov, dir);
      }
    case CheckNullable(qid) =>
      if LCdn.cdn_get(s1.cdn, qid) {
        AdvanceMonoAny(c, s1.(active := [t.(pc := t.pc + 1)] + ac), ov, dir);
      } else {
        AdvanceMonoAny(c, s1.(active := ac), ov, dir);
      }
    case AnchorAssertion(a) =>
      if LAnc.is_satisfied(a, s1.context, dir) {
        AdvanceMonoAny(c, s1.(active := [t.(pc := t.pc + 1)] + ac), ov, dir);
      } else {
        AdvanceMonoAny(c, s1.(active := ac), ov, dir);
      }
    case Fail =>
      AdvanceMonoAny(c, s1.(active := ac), ov, dir);
  }
}
