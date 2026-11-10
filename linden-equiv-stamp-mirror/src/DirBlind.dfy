// G3b side result (W8, M2 work list item 1): the engine's nulled-plus reconstruction
// is DIRECTION-BLIND. A backward run's FReconstructPlus is literally the forward
// one at the same positions: direction enters the null pass only through
// `is_satisfied(a, ctx, dir)` with `ctx = cp_context(cp, str, dir)` (and the same
// pair inside the CDN formulas), and the Backward context is the Forward one
// with prev/next swapped, which `is_satisfied` undoes.
//
// Package linden-equiv-stamp-mirror; needs regex-engine alone.
module LindenElkDirBlind {
  import opened Std.Wrappers
  import RA = Anchors
  import AI = ArrayInterp
  import LCdn = Cdn
  import LOr = Oracle
  import RB = Bytecode
  import R = RegElkRegex
  import AReg = Array_Regs

  function SwapCtx(ctx: RA.char_context): RA.char_context {
    RA.CharContext(ctx.nextchar, ctx.prevchar)
  }

  lemma IsSatisfiedDirBlind(a: R.anchor, ctx: RA.char_context)
    ensures RA.is_satisfied(a, ctx, RA.Backward) == RA.is_satisfied(a, SwapCtx(ctx), RA.Forward)
  {}

  lemma CpContextSwap(cp: int, str: string)
    ensures AI.cp_context(cp, str, RA.Backward) == SwapCtx(AI.cp_context(cp, str, RA.Forward))
  {}

  lemma InterpretCdnDirBlind(f: LCdn.cdn_formula, cp: int, ov: LOr.OracleView, t: LCdn.cdn_table, ctx: RA.char_context)
    ensures LCdn.interpret_cdn_v(f, cp, ov, t, ctx, RA.Backward)
         == LCdn.interpret_cdn_v(f, cp, ov, t, SwapCtx(ctx), RA.Forward)
    decreases f
  {
    match f
    case CDN_and(f1, f2) =>
      InterpretCdnDirBlind(f1, cp, ov, t, ctx); InterpretCdnDirBlind(f2, cp, ov, t, ctx);
    case CDN_or(f1, f2) =>
      InterpretCdnDirBlind(f1, cp, ov, t, ctx); InterpretCdnDirBlind(f2, cp, ov, t, ctx);
    case CDN_anchor(a) => IsSatisfiedDirBlind(a, ctx);
    case _ =>
  }

  lemma BuildCdnRecDirBlind(cs: LCdn.cdns, cp: int, ov: LOr.OracleView, ctx: RA.char_context, table: LCdn.cdn_table)
    ensures LCdn.build_cdn_rec_v(cs, cp, ov, ctx, RA.Backward, table)
         == LCdn.build_cdn_rec_v(cs, cp, ov, SwapCtx(ctx), RA.Forward, table)
    decreases |cs|
  {
    if |cs| > 0 {
      var qid := cs[0].0; var formula := cs[0].1;
      InterpretCdnDirBlind(formula, cp, ov, table, ctx);
      var eval := LCdn.interpret_cdn_v(formula, cp, ov, table, ctx, RA.Backward);
      var table' := if eval then LCdn.cdn_set_true(table, qid) else table;
      BuildCdnRecDirBlind(cs[1..], cp, ov, ctx, table');
    }
  }

  /** The epsilon closure run Backward is the Forward one on the swapped context
      (every field but the context agrees; epsilon steps never touch it). */
  lemma AdvanceEpsilonDirBlind(c: RB.code, s: AI.VmState, ov: LOr.OracleView)
    requires |s.processed.true_set| == RB.size(c) && |s.processed.false_set| == RB.size(c)
    ensures AI.FAdvanceEpsilon(c, s, ov, RA.Backward).0
         == AI.FAdvanceEpsilon(c, s.(context := SwapCtx(s.context)), ov, RA.Forward).0.(context := s.context)
    ensures AI.FAdvanceEpsilon(c, s, ov, RA.Backward).1
         == AI.FAdvanceEpsilon(c, s.(context := SwapCtx(s.context)), ov, RA.Forward).1
    decreases AI.unprocessed(s.processed), |s.active|
  {
    var sw := s.(context := SwapCtx(s.context));
    if |s.active| == 0 {
    } else {
      var t := s.active[0];
      var ac := s.active[1..];
      var i := RB.get_instr(c, t.pc);
      if AI.bpc_mem(s.processed, t.pc, t.exit_allowed) {
        AdvanceEpsilonDirBlind(c, s.(active := ac), ov);
      } else {
        var b0 := s.processed;
        var s1 := s.(clock := s.clock + 1, processed := AI.bpc_add(b0, t.pc, t.exit_allowed));
        AI.UnprocessedAdd(b0, t.pc, t.exit_allowed);
        assert AI.unprocessed(s1.processed) <= AI.unprocessed(b0)
            && (0 <= t.pc < RB.size(c) ==> AI.unprocessed(s1.processed) < AI.unprocessed(b0));
        match i
        case Consume(ce) =>
          var (nb, ni) := AI.add_thread(t, ce, s1.blocked, s1.isblocked);
          AdvanceEpsilonDirBlind(c, s1.(blocked := nb, isblocked := ni, active := ac), ov);
        case Accept =>
        case Jmp(x) =>
          AdvanceEpsilonDirBlind(c, s1.(active := [t.(pc := x)] + ac), ov);
        case Fork(x, y) =>
          var newt := AI.Thread(x, t.capture_regs, t.look_regs, t.quant_regs, t.exit_allowed);
          AdvanceEpsilonDirBlind(c, s1.(active := [newt, t.(pc := y)] + ac), ov);
        case SetRegisterToCP(reg) =>
          var t' := t.(capture_regs := AReg.set_reg(t.capture_regs, reg, Some(s1.cp), s1.clock), pc := t.pc + 1);
          AdvanceEpsilonDirBlind(c, s1.(active := [t'] + ac), ov);
        case SetQuantToClock(q, b) =>
          var ocp := if b then Some(s1.cp) else None;
          var t' := t.(quant_regs := AReg.set_reg(t.quant_regs, q, ocp, s1.clock), pc := t.pc + 1);
          AdvanceEpsilonDirBlind(c, s1.(active := [t'] + ac), ov);
        case CheckOracle(l) =>
          if LOr.view_get_oracle(ov, s1.cp, l) {
            var t' := t.(pc := t.pc + 1, look_regs := AReg.set_reg(t.look_regs, l, Some(s1.cp), s1.clock));
            AdvanceEpsilonDirBlind(c, s1.(active := [t'] + ac), ov);
          } else {
            AdvanceEpsilonDirBlind(c, s1.(active := ac), ov);
          }
        case NegCheckOracle(l) =>
          if LOr.view_get_oracle(ov, s1.cp, l) {
            AdvanceEpsilonDirBlind(c, s1.(active := ac), ov);
          } else {
            AdvanceEpsilonDirBlind(c, s1.(active := [t.(pc := t.pc + 1)] + ac), ov);
          }
        case WriteOracle(l) =>
          AdvanceEpsilonDirBlind(c, s1.(active := ac), LOr.view_set_oracle(ov, s1.cp, l));
        case BeginLoop =>
          AdvanceEpsilonDirBlind(c, s1.(active := [t.(exit_allowed := false, pc := t.pc + 1)] + ac), ov);
        case EndLoop =>
          if t.exit_allowed {
            AdvanceEpsilonDirBlind(c, s1.(active := [t.(pc := t.pc + 1)] + ac), ov);
          } else {
            AdvanceEpsilonDirBlind(c, s1.(active := ac), ov);
          }
        case CheckNullable(qid) =>
          if LCdn.cdn_get(s1.cdn, qid) {
            AdvanceEpsilonDirBlind(c, s1.(active := [t.(pc := t.pc + 1)] + ac), ov);
          } else {
            AdvanceEpsilonDirBlind(c, s1.(active := ac), ov);
          }
        case AnchorAssertion(a) =>
          IsSatisfiedDirBlind(a, s.context);
          if RA.is_satisfied(a, s1.context, RA.Backward) {
            AdvanceEpsilonDirBlind(c, s1.(active := [t.(pc := t.pc + 1)] + ac), ov);
          } else {
            AdvanceEpsilonDirBlind(c, s1.(active := ac), ov);
          }
        case Fail =>
          AdvanceEpsilonDirBlind(c, s1.(active := ac), ov);
      }
    }
  }

  lemma NullInterpDirBlind(c: RB.code, s: AI.VmState, ov: LOr.OracleView)
    requires |s.processed.true_set| == RB.size(c) && |s.processed.false_set| == RB.size(c)
    ensures AI.FNullInterp(c, s, ov, RA.Backward).0
         == AI.FNullInterp(c, s.(context := SwapCtx(s.context)), ov, RA.Forward).0
    ensures AI.FNullInterp(c, s, ov, RA.Backward).2
         == AI.FNullInterp(c, s.(context := SwapCtx(s.context)), ov, RA.Forward).2
  {
    AdvanceEpsilonDirBlind(c, s, ov);
  }

  lemma NulledPlusDirBlind(reg: R.regex, cap: AReg.Regs, lk: AReg.Regs, qt: AReg.Regs,
                           plus_bcv: seq<RB.code>, str: string, ov: LOr.OracleView)
    ensures AI.FNulledPlus(reg, cap, lk, qt, plus_bcv, str, ov, RA.Backward)
         == AI.FNulledPlus(reg, cap, lk, qt, plus_bcv, str, ov, RA.Forward)
    decreases reg, 1
  {
    match reg
    case Re_empty =>
    case Re_character(_) =>
    case Re_anchor(_) =>
    case Re_lookaround(_, _, _) =>
    case Re_capture(_, r1) => NulledPlusDirBlind(r1, cap, lk, qt, plus_bcv, str, ov);
    case Re_alt(r1, r2) =>
      NulledPlusDirBlind(r1, cap, lk, qt, plus_bcv, str, ov);
      var (c1, l1, q1, ov1) := AI.FNulledPlus(r1, cap, lk, qt, plus_bcv, str, ov, RA.Forward);
      NulledPlusDirBlind(r2, c1, l1, q1, plus_bcv, str, ov1);
    case Re_con(r1, r2) =>
      NulledPlusDirBlind(r1, cap, lk, qt, plus_bcv, str, ov);
      var (c1, l1, q1, ov1) := AI.FNulledPlus(r1, cap, lk, qt, plus_bcv, str, ov, RA.Forward);
      NulledPlusDirBlind(r2, c1, l1, q1, plus_bcv, str, ov1);
    case Re_quant(nul, qid, quanttype, body) =>
      match AReg.get_cp(qt, qid)
      case None => NulledPlusDirBlind(body, cap, lk, qt, plus_bcv, str, ov);
      case Some(start_cp) =>
        var start_clock := AI.opt_int(AReg.get_clock(qt, qid));
        var bytecode := AI.get_code_v(plus_bcv, qid);
        var ctxB := AI.cp_context(start_cp, str, RA.Backward);
        var ctxF := AI.cp_context(start_cp, str, RA.Forward);
        CpContextSwap(start_cp, str);
        assert SwapCtx(ctxB) == ctxF;
        var subcdn := LCdn.compile_cdns(body);
        BuildCdnRecDirBlind(subcdn, start_cp, ov, ctxB, LCdn.init_cdn());
        var subtable := LCdn.build_cdn_v(subcdn, start_cp, ov, ctxF, RA.Forward);
        assert LCdn.build_cdn_v(subcdn, start_cp, ov, ctxB, RA.Backward) == subtable;
        var initsB := AI.FInitState(bytecode, start_cp, cap, lk, qt, start_clock, ctxB).(cdn := subtable);
        var initsF := AI.FInitState(bytecode, start_cp, cap, lk, qt, start_clock, ctxF).(cdn := subtable);
        assert initsB.(context := SwapCtx(initsB.context)) == initsF;
        NullInterpDirBlind(bytecode, initsB, ov);
        var (result, _, ov1) := AI.FNullInterp(bytecode, initsF, ov, RA.Forward);
        var (ncap, nlk, nqt) := match result
                                case None => (cap, lk, qt)
                                case Some(w) => (w.capture_regs, w.look_regs, w.quant_regs);
        NulledChildrenDirBlind(body, subtable, start_cp, ncap, nlk, nqt, plus_bcv, str, ov1);
  }

  lemma NulledChildrenDirBlind(reg: R.regex, cdnt: LCdn.cdn_table, cp: int, cap: AReg.Regs, lk: AReg.Regs, qt: AReg.Regs,
                               plus_bcv: seq<RB.code>, str: string, ov: LOr.OracleView)
    ensures AI.FNulledChildren(reg, cdnt, cp, cap, lk, qt, plus_bcv, str, ov, RA.Backward)
         == AI.FNulledChildren(reg, cdnt, cp, cap, lk, qt, plus_bcv, str, ov, RA.Forward)
    decreases reg, 0
  {
    match reg
    case Re_empty =>
    case Re_character(_) =>
    case Re_anchor(_) =>
    case Re_lookaround(_, _, _) =>
    case Re_capture(_, r1) => NulledChildrenDirBlind(r1, cdnt, cp, cap, lk, qt, plus_bcv, str, ov);
    case Re_alt(r1, r2) =>
      NulledChildrenDirBlind(r1, cdnt, cp, cap, lk, qt, plus_bcv, str, ov);
      var (c1, l1, q1, ov1) := AI.FNulledChildren(r1, cdnt, cp, cap, lk, qt, plus_bcv, str, ov, RA.Forward);
      NulledChildrenDirBlind(r2, cdnt, cp, c1, l1, q1, plus_bcv, str, ov1);
    case Re_con(r1, r2) =>
      NulledChildrenDirBlind(r1, cdnt, cp, cap, lk, qt, plus_bcv, str, ov);
      var (c1, l1, q1, ov1) := AI.FNulledChildren(r1, cdnt, cp, cap, lk, qt, plus_bcv, str, ov, RA.Forward);
      NulledChildrenDirBlind(r2, cdnt, cp, c1, l1, q1, plus_bcv, str, ov1);
    case Re_quant(nul, qid, quanttype, body) =>
      match AReg.get_cp(qt, qid)
      case None => NulledChildrenDirBlind(body, cdnt, cp, cap, lk, qt, plus_bcv, str, ov);
      case Some(start_cp) =>
        if start_cp == cp {
          var start_clock := AI.opt_int(AReg.get_clock(qt, qid));
          var bytecode := AI.get_code_v(plus_bcv, qid);
          var ctxB := AI.cp_context(cp, str, RA.Backward);
          var ctxF := AI.cp_context(cp, str, RA.Forward);
          CpContextSwap(cp, str);
          var initsB := AI.FInitState(bytecode, cp, cap, lk, qt, start_clock, ctxB).(cdn := cdnt);
          var initsF := AI.FInitState(bytecode, cp, cap, lk, qt, start_clock, ctxF).(cdn := cdnt);
          assert initsB.(context := SwapCtx(initsB.context)) == initsF;
          NullInterpDirBlind(bytecode, initsB, ov);
          var (result, _, ov1) := AI.FNullInterp(bytecode, initsF, ov, RA.Forward);
          var (ncap, nlk, nqt) := match result
                                  case None => (cap, lk, qt)
                                  case Some(w) => (w.capture_regs, w.look_regs, w.quant_regs);
          NulledChildrenDirBlind(body, cdnt, cp, ncap, nlk, nqt, plus_bcv, str, ov1);
        }
  }

  /** THE corollary: a backward row's reconstruction IS the forward one. */
  lemma ReconstructPlusDirBlind(th: AI.Thread, ast: R.regex, plus_bcv: seq<RB.code>, str: string, ov: LOr.OracleView)
    ensures AI.FReconstructPlus(th, ast, plus_bcv, str, ov, RA.Backward)
         == AI.FReconstructPlus(th, ast, plus_bcv, str, ov, RA.Forward)
  {
    NulledPlusDirBlind(ast, th.capture_regs, th.look_regs, th.quant_regs, plus_bcv, str, ov);
  }
}
