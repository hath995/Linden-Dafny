// §2.5b rung F-c (c6): the engine never READS a quant register's VALUE except
// in the nulled-plus reconstruction, and there only for the quantifiers of the
// regex it walks. So two register banks whose quant banks agree on clocks
// everywhere and on values outside a set `D` drive the VM, the null
// interpreter, the reconstruction of a regex without quantifiers in `D`, the
// lookaround capture loop (look bodies without quantifiers in `D`) and
// `filter_reset` to agreeing results. The final readout uses it with
// `D = CinQids(re)` to clear the CIN stamps' values before the look loop.
module LindenElkQuantCpIrrel {
  import opened Std.Wrappers
  import AI = ArrayInterp
  import AReg = Array_Regs
  import RB = Bytecode
  import LOr = Oracle
  import LAnc = Anchors
  import LCdn = Cdn
  import RC = Charclasses
  import R = RegElkRegex
  import CP = Compiler
  import PIV = LindenElkPikeInv

  // ===========================================================================
  // The relation
  // ===========================================================================

  ghost predicate QAgree(q1: AReg.Regs, q2: AReg.Regs, D: set<int>) {
    |q1.a_cp| == |q2.a_cp| && q1.a_clk == q2.a_clk
    && forall k :: 0 <= k < |q1.a_cp| && k !in D ==> q1.a_cp[k] == q2.a_cp[k]
  }

  ghost predicate TAgree(t1: AI.Thread, t2: AI.Thread, D: set<int>) {
    t1.pc == t2.pc && t1.capture_regs == t2.capture_regs && t1.look_regs == t2.look_regs
    && t1.exit_allowed == t2.exit_allowed && QAgree(t1.quant_regs, t2.quant_regs, D)
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

  lemma QAgreeRefl(q: AReg.Regs, D: set<int>)
    ensures QAgree(q, q, D)
  {}

  /** The SAME write keeps the banks agreeing. */
  lemma QAgreeSet(q1: AReg.Regs, q2: AReg.Regs, k: int, cp: Option<int>, clk: int, D: set<int>)
    requires QAgree(q1, q2, D)
    ensures QAgree(AReg.set_reg(q1, k, cp, clk), AReg.set_reg(q2, k, cp, clk), D)
  {}

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
        ListAgreeCons(t.(pc := x), u.(pc := x), ac, bc, D);
        FAdvanceEpsilonAgree(c, x1.(active := [t.(pc := x)] + ac), x2.(active := [u.(pc := x)] + bc), ov, dir, D);
      case Fork(x, y) =>
        var n1 := AI.Thread(x, t.capture_regs, t.look_regs, t.quant_regs, t.exit_allowed);
        var n2 := AI.Thread(x, u.capture_regs, u.look_regs, u.quant_regs, u.exit_allowed);
        ListAgreeCons(t.(pc := y), u.(pc := y), ac, bc, D);
        ListAgreeCons(n1, n2, [t.(pc := y)] + ac, [u.(pc := y)] + bc, D);
        assert [n1, t.(pc := y)] + ac == [n1] + ([t.(pc := y)] + ac);
        assert [n2, u.(pc := y)] + bc == [n2] + ([u.(pc := y)] + bc);
        FAdvanceEpsilonAgree(c, x1.(active := [n1, t.(pc := y)] + ac), x2.(active := [n2, u.(pc := y)] + bc), ov, dir, D);
      case SetRegisterToCP(reg) =>
        var t2 := t.(capture_regs := AReg.set_reg(t.capture_regs, reg, Some(x1.cp), x1.clock), pc := t.pc + 1);
        var u2 := u.(capture_regs := AReg.set_reg(u.capture_regs, reg, Some(x2.cp), x2.clock), pc := u.pc + 1);
        ListAgreeCons(t2, u2, ac, bc, D);
        FAdvanceEpsilonAgree(c, x1.(active := [t2] + ac), x2.(active := [u2] + bc), ov, dir, D);
      case SetQuantToClock(q, bq) =>
        var ocp := if bq then Some(x1.cp) else None;
        var t2 := t.(quant_regs := AReg.set_reg(t.quant_regs, q, ocp, x1.clock), pc := t.pc + 1);
        var u2 := u.(quant_regs := AReg.set_reg(u.quant_regs, q, ocp, x2.clock), pc := u.pc + 1);
        QAgreeSet(t.quant_regs, u.quant_regs, q, ocp, x1.clock, D);
        ListAgreeCons(t2, u2, ac, bc, D);
        FAdvanceEpsilonAgree(c, x1.(active := [t2] + ac), x2.(active := [u2] + bc), ov, dir, D);
      case CheckOracle(l) =>
        if LOr.view_get_oracle(ov, x1.cp, l) {
          var t2 := t.(pc := t.pc + 1, look_regs := AReg.set_reg(t.look_regs, l, Some(x1.cp), x1.clock));
          var u2 := u.(pc := u.pc + 1, look_regs := AReg.set_reg(u.look_regs, l, Some(x2.cp), x2.clock));
          ListAgreeCons(t2, u2, ac, bc, D);
          FAdvanceEpsilonAgree(c, x1.(active := [t2] + ac), x2.(active := [u2] + bc), ov, dir, D);
        } else {
          FAdvanceEpsilonAgree(c, x1.(active := ac), x2.(active := bc), ov, dir, D);
        }
      case NegCheckOracle(l) =>
        if LOr.view_get_oracle(ov, x1.cp, l) {
          FAdvanceEpsilonAgree(c, x1.(active := ac), x2.(active := bc), ov, dir, D);
        } else {
          ListAgreeCons(t.(pc := t.pc + 1), u.(pc := u.pc + 1), ac, bc, D);
          FAdvanceEpsilonAgree(c, x1.(active := [t.(pc := t.pc + 1)] + ac), x2.(active := [u.(pc := u.pc + 1)] + bc), ov, dir, D);
        }
      case WriteOracle(l) =>
        FAdvanceEpsilonAgree(c, x1.(active := ac), x2.(active := bc), LOr.view_set_oracle(ov, x1.cp, l), dir, D);
      case BeginLoop =>
        var t2 := t.(exit_allowed := false, pc := t.pc + 1);
        var u2 := u.(exit_allowed := false, pc := u.pc + 1);
        ListAgreeCons(t2, u2, ac, bc, D);
        FAdvanceEpsilonAgree(c, x1.(active := [t2] + ac), x2.(active := [u2] + bc), ov, dir, D);
      case EndLoop =>
        if t.exit_allowed {
          ListAgreeCons(t.(pc := t.pc + 1), u.(pc := u.pc + 1), ac, bc, D);
          FAdvanceEpsilonAgree(c, x1.(active := [t.(pc := t.pc + 1)] + ac), x2.(active := [u.(pc := u.pc + 1)] + bc), ov, dir, D);
        } else {
          FAdvanceEpsilonAgree(c, x1.(active := ac), x2.(active := bc), ov, dir, D);
        }
      case CheckNullable(qid) =>
        if LCdn.cdn_get(x1.cdn, qid) {
          ListAgreeCons(t.(pc := t.pc + 1), u.(pc := u.pc + 1), ac, bc, D);
          FAdvanceEpsilonAgree(c, x1.(active := [t.(pc := t.pc + 1)] + ac), x2.(active := [u.(pc := u.pc + 1)] + bc), ov, dir, D);
        } else {
          FAdvanceEpsilonAgree(c, x1.(active := ac), x2.(active := bc), ov, dir, D);
        }
      case AnchorAssertion(a) =>
        if LAnc.is_satisfied(a, x1.context, dir) {
          ListAgreeCons(t.(pc := t.pc + 1), u.(pc := u.pc + 1), ac, bc, D);
          FAdvanceEpsilonAgree(c, x1.(active := [t.(pc := t.pc + 1)] + ac), x2.(active := [u.(pc := u.pc + 1)] + bc), ov, dir, D);
        } else {
          FAdvanceEpsilonAgree(c, x1.(active := ac), x2.(active := bc), ov, dir, D);
        }
      case Fail =>
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

  lemma FInitStateAgree(c: RB.code, cp: int, cap: AReg.Regs, lk: AReg.Regs, q1: AReg.Regs, q2: AReg.Regs,
                        clk: int, ctx: LAnc.char_context, D: set<int>)
    requires QAgree(q1, q2, D)
    ensures SAgree(AI.FInitState(c, cp, cap, lk, q1, clk, ctx), AI.FInitState(c, cp, cap, lk, q2, clk, ctx), D)
  {
    var s1 := AI.FInitState(c, cp, cap, lk, q1, clk, ctx);
    var s2 := AI.FInitState(c, cp, cap, lk, q2, clk, ctx);
    assert TAgree(s1.active[0], s2.active[0], D);
  }

  // ===========================================================================
  // The reconstruction and the look loop
  // ===========================================================================

  /** The quantifier ids `FNulledPlus` consults when walking `r`. */
  ghost function QidsOf(r: R.regex): set<int>
    decreases r
  {
    match r
    case Re_capture(_, r1) => QidsOf(r1)
    case Re_alt(r1, r2) => QidsOf(r1) + QidsOf(r2)
    case Re_con(r1, r2) => QidsOf(r1) + QidsOf(r2)
    case Re_quant(_, qid, _, body) => {qid} + QidsOf(body)
    case _ => {}
  }

  lemma GetCpAgree(q1: AReg.Regs, q2: AReg.Regs, k: int, D: set<int>)
    requires QAgree(q1, q2, D) && k !in D
    ensures AReg.get_cp(q1, k) == AReg.get_cp(q2, k) && AReg.get_clock(q1, k) == AReg.get_clock(q2, k)
  {}

  lemma FNulledPlusAgree(reg: R.regex, cap: AReg.Regs, lk: AReg.Regs, q1: AReg.Regs, q2: AReg.Regs,
                         plus_bcv: seq<RB.code>, str: string, ov: LOr.OracleView, dir: LAnc.direction, D: set<int>)
    requires QAgree(q1, q2, D)
    requires QidsOf(reg) * D == {}
    ensures var r1 := AI.FNulledPlus(reg, cap, lk, q1, plus_bcv, str, ov, dir);
            var r2 := AI.FNulledPlus(reg, cap, lk, q2, plus_bcv, str, ov, dir);
            r1.0 == r2.0 && r1.1 == r2.1 && QAgree(r1.2, r2.2, D) && r1.3 == r2.3
    decreases reg, 1
  {
    match reg
    case Re_empty =>
    case Re_character(_) =>
    case Re_anchor(_) =>
    case Re_lookaround(_, _, _) =>
    case Re_capture(_, r1) => FNulledPlusAgree(r1, cap, lk, q1, q2, plus_bcv, str, ov, dir, D);
    case Re_alt(r1, r2) =>
      FNulledPlusAgree(r1, cap, lk, q1, q2, plus_bcv, str, ov, dir, D);
      var (c1, l1, x1, o1) := AI.FNulledPlus(r1, cap, lk, q1, plus_bcv, str, ov, dir);
      var (c2, l2, x2, o2) := AI.FNulledPlus(r1, cap, lk, q2, plus_bcv, str, ov, dir);
      FNulledPlusAgree(r2, c1, l1, x1, x2, plus_bcv, str, o1, dir, D);
    case Re_con(r1, r2) =>
      FNulledPlusAgree(r1, cap, lk, q1, q2, plus_bcv, str, ov, dir, D);
      var (c1, l1, x1, o1) := AI.FNulledPlus(r1, cap, lk, q1, plus_bcv, str, ov, dir);
      var (c2, l2, x2, o2) := AI.FNulledPlus(r1, cap, lk, q2, plus_bcv, str, ov, dir);
      FNulledPlusAgree(r2, c1, l1, x1, x2, plus_bcv, str, o1, dir, D);
    case Re_quant(nul, qid, quanttype, body) =>
      assert (qid as int) in QidsOf(reg);
      assert (qid as int) !in D by { if (qid as int) in D { assert (qid as int) in QidsOf(reg) * D; } }
      GetCpAgree(q1, q2, qid, D);
      match AReg.get_cp(q1, qid) {
        case None => FNulledPlusAgree(body, cap, lk, q1, q2, plus_bcv, str, ov, dir, D);
        case Some(start_cp) =>
          var start_clock := AI.opt_int(AReg.get_clock(q1, qid));
          var bytecode := AI.get_code_v(plus_bcv, qid);
          var ctx := AI.cp_context(start_cp, str, dir);
          var subcdn := LCdn.compile_cdns(body);
          var subtable := LCdn.build_cdn_v(subcdn, start_cp, ov, ctx, dir);
          var i1 := AI.FInitState(bytecode, start_cp, cap, lk, q1, start_clock, ctx).(cdn := subtable);
          var i2 := AI.FInitState(bytecode, start_cp, cap, lk, q2, start_clock, ctx).(cdn := subtable);
          FInitStateAgree(bytecode, start_cp, cap, lk, q1, q2, start_clock, ctx, D);
          assert SAgree(i1, i2, D);
          FAdvanceEpsilonAgree(bytecode, i1, i2, ov, dir, D);
          var (res1, _, ova) := AI.FNullInterp(bytecode, i1, ov, dir);
          var (res2, _, ovb) := AI.FNullInterp(bytecode, i2, ov, dir);
          assert OptAgree(res1, res2, D) && ova == ovb;
          var (nc1, nl1, nq1) := match res1 case None => (cap, lk, q1) case Some(w) => (w.capture_regs, w.look_regs, w.quant_regs);
          var (nc2, nl2, nq2) := match res2 case None => (cap, lk, q2) case Some(w) => (w.capture_regs, w.look_regs, w.quant_regs);
          assert nc1 == nc2 && nl1 == nl2 && QAgree(nq1, nq2, D);
          FNulledChildrenAgree(body, subtable, start_cp, nc1, nl1, nq1, nq2, plus_bcv, str, ova, dir, D);
      }
  }

  lemma FNulledChildrenAgree(reg: R.regex, cdnt: LCdn.cdn_table, cp: int, cap: AReg.Regs, lk: AReg.Regs,
                             q1: AReg.Regs, q2: AReg.Regs, plus_bcv: seq<RB.code>, str: string,
                             ov: LOr.OracleView, dir: LAnc.direction, D: set<int>)
    requires QAgree(q1, q2, D)
    requires QidsOf(reg) * D == {}
    ensures var r1 := AI.FNulledChildren(reg, cdnt, cp, cap, lk, q1, plus_bcv, str, ov, dir);
            var r2 := AI.FNulledChildren(reg, cdnt, cp, cap, lk, q2, plus_bcv, str, ov, dir);
            r1.0 == r2.0 && r1.1 == r2.1 && QAgree(r1.2, r2.2, D) && r1.3 == r2.3
    decreases reg, 0
  {
    match reg
    case Re_empty =>
    case Re_character(_) =>
    case Re_anchor(_) =>
    case Re_lookaround(_, _, _) =>
    case Re_capture(_, r1) => FNulledChildrenAgree(r1, cdnt, cp, cap, lk, q1, q2, plus_bcv, str, ov, dir, D);
    case Re_alt(r1, r2) =>
      FNulledChildrenAgree(r1, cdnt, cp, cap, lk, q1, q2, plus_bcv, str, ov, dir, D);
      var (c1, l1, x1, o1) := AI.FNulledChildren(r1, cdnt, cp, cap, lk, q1, plus_bcv, str, ov, dir);
      var (c2, l2, x2, o2) := AI.FNulledChildren(r1, cdnt, cp, cap, lk, q2, plus_bcv, str, ov, dir);
      FNulledChildrenAgree(r2, cdnt, cp, c1, l1, x1, x2, plus_bcv, str, o1, dir, D);
    case Re_con(r1, r2) =>
      FNulledChildrenAgree(r1, cdnt, cp, cap, lk, q1, q2, plus_bcv, str, ov, dir, D);
      var (c1, l1, x1, o1) := AI.FNulledChildren(r1, cdnt, cp, cap, lk, q1, plus_bcv, str, ov, dir);
      var (c2, l2, x2, o2) := AI.FNulledChildren(r1, cdnt, cp, cap, lk, q2, plus_bcv, str, ov, dir);
      FNulledChildrenAgree(r2, cdnt, cp, c1, l1, x1, x2, plus_bcv, str, o1, dir, D);
    case Re_quant(nul, qid, quanttype, body) =>
      assert (qid as int) in QidsOf(reg);
      assert (qid as int) !in D by { if (qid as int) in D { assert (qid as int) in QidsOf(reg) * D; } }
      GetCpAgree(q1, q2, qid, D);
      match AReg.get_cp(q1, qid) {
        case None => FNulledChildrenAgree(body, cdnt, cp, cap, lk, q1, q2, plus_bcv, str, ov, dir, D);
        case Some(start_cp) =>
          if start_cp == cp {
            var start_clock := AI.opt_int(AReg.get_clock(q1, qid));
            var bytecode := AI.get_code_v(plus_bcv, qid);
            var ctx := AI.cp_context(cp, str, dir);
            var i1 := AI.FInitState(bytecode, cp, cap, lk, q1, start_clock, ctx).(cdn := cdnt);
            var i2 := AI.FInitState(bytecode, cp, cap, lk, q2, start_clock, ctx).(cdn := cdnt);
            FInitStateAgree(bytecode, cp, cap, lk, q1, q2, start_clock, ctx, D);
            assert SAgree(i1, i2, D);
            FAdvanceEpsilonAgree(bytecode, i1, i2, ov, dir, D);
            var (res1, _, ova) := AI.FNullInterp(bytecode, i1, ov, dir);
            var (res2, _, ovb) := AI.FNullInterp(bytecode, i2, ov, dir);
            assert OptAgree(res1, res2, D) && ova == ovb;
            var (nc1, nl1, nq1) := match res1 case None => (cap, lk, q1) case Some(w) => (w.capture_regs, w.look_regs, w.quant_regs);
            var (nc2, nl2, nq2) := match res2 case None => (cap, lk, q2) case Some(w) => (w.capture_regs, w.look_regs, w.quant_regs);
            assert nc1 == nc2 && nl1 == nl2 && QAgree(nq1, nq2, D);
            FNulledChildrenAgree(body, cdnt, cp, nc1, nl1, nq1, nq2, plus_bcv, str, ova, dir, D);
          }
      }
  }

  lemma FFindMatchPlusAgree(c: RB.code, ast: R.regex, plus_bcv: seq<RB.code>, str: string, ov: LOr.OracleView,
                            dir: LAnc.direction, start_cp: int, cap: AReg.Regs, lk: AReg.Regs,
                            q1: AReg.Regs, q2: AReg.Regs, clk: int, cdn: LCdn.cdns, D: set<int>)
    requires QAgree(q1, q2, D)
    requires QidsOf(ast) * D == {}
    ensures OptAgree(AI.FFindMatchPlus(c, ast, plus_bcv, str, ov, dir, start_cp, cap, lk, q1, clk, cdn).0,
                     AI.FFindMatchPlus(c, ast, plus_bcv, str, ov, dir, start_cp, cap, lk, q2, clk, cdn).0, D)
    ensures AI.FFindMatchPlus(c, ast, plus_bcv, str, ov, dir, start_cp, cap, lk, q1, clk, cdn).1
         == AI.FFindMatchPlus(c, ast, plus_bcv, str, ov, dir, start_cp, cap, lk, q2, clk, cdn).1
  {
    var ctx := AI.cp_context(start_cp, str, dir);
    var i1 := AI.FInitState(c, start_cp, cap, lk, q1, clk, ctx);
    var i2 := AI.FInitState(c, start_cp, cap, lk, q2, clk, ctx);
    FInitStateAgree(c, start_cp, cap, lk, q1, q2, clk, ctx, D);
    FFindMatchAgree(c, str, i1, i2, ov, dir, cdn, D);
    var (res1, ova) := AI.FFindMatch(c, str, i1, ov, dir, cdn);
    var (res2, ovb) := AI.FFindMatch(c, str, i2, ov, dir, cdn);
    if res1.Some? {
      var w1 := res1.value;
      var w2 := res2.value;
      FNulledPlusAgree(ast, w1.capture_regs, w1.look_regs, w1.quant_regs, w2.quant_regs, plus_bcv, str, ova, dir, D);
    }
  }

  /** The look loop, when no look body walks a quantifier in `D`. */
  ghost predicate LookAstsAvoid(crv: CP.FCompiled, D: set<int>) {
    forall l :: 0 <= l < |crv.f_look_ast| ==> QidsOf(crv.f_look_ast[l]) * D == {}
  }

  lemma FLookLoopAgree(crv: CP.FCompiled, str: string, lid: int, maxlook: int,
                       cap: AReg.Regs, lk: AReg.Regs, q1: AReg.Regs, q2: AReg.Regs, ov: LOr.OracleView, D: set<int>)
    requires QAgree(q1, q2, D)
    requires LookAstsAvoid(crv, D)
    ensures var r1 := AI.FLookLoop(crv, str, lid, maxlook, cap, lk, q1, ov);
            var r2 := AI.FLookLoop(crv, str, lid, maxlook, cap, lk, q2, ov);
            r1.0 == r2.0 && r1.1 == r2.1 && QAgree(r1.2, r2.2, D) && r1.3 == r2.3
    decreases maxlook - lid
  {
    if lid > maxlook { return; }
    var next := lid + 1;
    match AReg.get_cp(lk, lid) {
      case None => FLookLoopAgree(crv, str, next, maxlook, cap, lk, q1, q2, ov, D);
      case Some(cp) =>
        var looktype := if 0 <= lid < |crv.f_look_types| then crv.f_look_types[lid] else R.Lookahead;
        if AI.capture_type(looktype) {
          var bytecode := AI.get_code_v(crv.f_look_capture_bc, lid);
          var dir := AI.capture_direction(looktype);
          var lookcdn := if 0 <= lid < |crv.f_look_cdns| then crv.f_look_cdns[lid] else [];
          var lookast := if 0 <= lid < |crv.f_look_ast| then crv.f_look_ast[lid] else R.Re_empty;
          assert QidsOf(lookast) * D == {};
          FFindMatchPlusAgree(bytecode, lookast, crv.f_plus_bc, str, ov, dir, cp, cap, lk, q1, q2, 0, lookcdn, D);
          var (res1, ova) := AI.FFindMatchPlus(bytecode, lookast, crv.f_plus_bc, str, ov, dir, cp, cap, lk, q1, 0, lookcdn);
          var (res2, ovb) := AI.FFindMatchPlus(bytecode, lookast, crv.f_plus_bc, str, ov, dir, cp, cap, lk, q2, 0, lookcdn);
          var (nc1, nl1, nq1) := match res1 case None => (cap, lk, q1) case Some(t) => (t.capture_regs, t.look_regs, t.quant_regs);
          var (nc2, nl2, nq2) := match res2 case None => (cap, lk, q2) case Some(t) => (t.capture_regs, t.look_regs, t.quant_regs);
          assert nc1 == nc2 && nl1 == nl2 && QAgree(nq1, nq2, D) && ova == ovb;
          FLookLoopAgree(crv, str, next, maxlook, nc1, nl1, nq1, nq2, ova, D);
        } else {
          FLookLoopAgree(crv, str, next, maxlook, cap, lk, q1, q2, ov, D);
        }
    }
  }

  /** `filter_reset` reads quant CLOCKS only. */
  lemma FilterResetAgree(r: R.regex, cap: AReg.Regs, lk: AReg.Regs, q1: AReg.Regs, q2: AReg.Regs,
                         maxclock: int, D: set<int>)
    requires QAgree(q1, q2, D)
    ensures AI.filter_reset(r, cap, lk, q1, maxclock) == AI.filter_reset(r, cap, lk, q2, maxclock)
  {}
}
