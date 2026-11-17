// G1-0 (ENDGAME_PLAN.md §9.2): the mirror-world lemmas the G1 descent needs
// before anything expensive is touched.
//
//   §1  every `a_cp` entry of every register bank (capture, look, quant) that an
//       `FFindMatch` run returns lies in [-1, |str|], in EITHER direction;
//   §2  `FXR` is an involution, with no fragment premise;
//   §3  the per-row fresh-match tie at a lookbehind row and at a lookahead row,
//       for ANY body shape; the lookahead row in the useful direction
//       (`RowTieFromLA`) needs §1 and nothing else;
//   §4  the double flip returns every `LookEntryOk` row unchanged.
module LindenElkMirrorWorld {
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
  import LC = Chars
  import NR = LindenElkNfaRep
  import MIR = LindenElkMirror
  import M = LindenElkMain
  import CM = LindenElkClockMono
  import LTB = LindenElkLookTables
  import BV = LindenElkBackValue
  import FG = LindenElkFlipGate
  import FST = LindenElkFlipStatics
  import FR = LindenElkFlipRev
  import OBu = LindenElkOracleBuild
  import FS = FunctionalSemantics
  import T = LindenElkTranslate
  import PIV = LindenElkPikeInv
  import CMr = LindenElkCdnMirror

  // ===========================================================================
  // §1  Bank bounds: every recorded position lies in [-1, ub]
  //
  // The only register writers are, in `FAdvanceEpsilon`,
  //   SetRegisterToCP(reg)  capture bank, `Some(s1.cp)`
  //   SetQuantToClock(q, b) quant bank,   `Some(s1.cp)` or `None` (-1)
  //   CheckOracle(l)        look bank,    `Some(s1.cp)`
  // and `s1.cp == s.cp`. `FConsume` writes nothing; `FFindMatch` moves cp by one
  // only when the next char exists, so cp stays in [0, |str|] in both directions.
  // A parallel induction, the all-bank, both-direction twin of
  // `CM.FFindMatchLookCpOk[B]`; it does not touch any simulation invariant.
  // ===========================================================================

  /** Every position recorded in bank `r` lies in `[-1, ub]` (`-1` = unset). */
  ghost predicate CpsIn(r: AReg.Regs, ub: int) {
    forall k :: 0 <= k < |r.a_cp| ==> -1 <= r.a_cp[k] <= ub
  }

  /** All three banks of `t` are in `[-1, ub]`. */
  ghost predicate ThreadCpsIn(t: AI.Thread, ub: int) {
    CpsIn(t.capture_regs, ub) && CpsIn(t.look_regs, ub) && CpsIn(t.quant_regs, ub)
  }

  /** Every thread of the state (active, blocked, best match) has its banks in `[-1, ub]`. */
  ghost predicate VmCpsIn(s: AI.VmState, ub: int) {
    (forall t | t in s.active :: ThreadCpsIn(t, ub))
    && (forall tb | tb in s.blocked :: ThreadCpsIn(tb.0, ub))
    && (s.bestmatch.Some? ==> ThreadCpsIn(s.bestmatch.value, ub))
  }

  lemma InitRegsCpsIn(size: int, ub: int)
    requires ub >= -1
    ensures CpsIn(AReg.init_regs(size), ub)
  {}

  /** Writing `Some(cp)` with `0 <= cp <= ub`, or `None`, keeps a bank in `[-1, ub]`. */
  lemma SetRegCpsIn(r: AReg.Regs, k: int, o: Option<int>, clk: int, ub: int)
    requires CpsIn(r, ub) && ub >= 0
    requires o.Some? ==> 0 <= o.value <= ub
    ensures CpsIn(AReg.set_reg(r, k, o, clk), ub)
  {
    var r2 := AReg.set_reg(r, k, o, clk);
    if 0 <= k < |r.a_cp| && 0 <= k < |r.a_clk| {
      match o {
        case None => assert r2.a_cp == r.a_cp[k := -1];
        case Some(x) => assert r2.a_cp == r.a_cp[k := x];
      }
    } else {
      assert r2 == r;
    }
  }

  /** An epsilon phase at a position `0 <= s.cp <= ub` writes only positions in range. */
  lemma FAdvanceEpsilonCpsIn(c: RB.code, s: AI.VmState, ov: LOr.OracleView,
                             dir: LAnc.direction, ub: int)
    requires |s.processed.true_set| == RB.size(c) && |s.processed.false_set| == RB.size(c)
    requires 0 <= s.cp <= ub
    requires VmCpsIn(s, ub)
    ensures VmCpsIn(AI.FAdvanceEpsilon(c, s, ov, dir).0, ub)
    decreases AI.unprocessed(s.processed), |s.active|
  {
    if |s.active| == 0 { return; }
    var t := s.active[0];
    var ac := s.active[1..];
    assert t in s.active;
    assert ThreadCpsIn(t, ub);
    assert forall x | x in ac :: x in s.active;
    if AI.bpc_mem(s.processed, t.pc, t.exit_allowed) {
      FAdvanceEpsilonCpsIn(c, s.(active := ac), ov, dir, ub);
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
        assert VmCpsIn(s2, ub) by {
          forall tb | tb in nb ensures ThreadCpsIn(tb.0, ub) {
            assert tb == (t, ce) || tb in s1.blocked;
          }
        }
        FAdvanceEpsilonCpsIn(c, s2, ov, dir, ub);
      case Accept =>
      case Jmp(x) =>
        FAdvanceEpsilonCpsIn(c, s1.(active := [t.(pc := x)] + ac), ov, dir, ub);
      case Fork(x, y) =>
        var newt := AI.Thread(x, t.capture_regs, t.look_regs, t.quant_regs, t.exit_allowed);
        FAdvanceEpsilonCpsIn(c, s1.(active := [newt, t.(pc := y)] + ac), ov, dir, ub);
      case SetRegisterToCP(reg) =>
        SetRegCpsIn(t.capture_regs, reg, Some(s1.cp), s1.clock, ub);
        var t2 := t.(capture_regs := AReg.set_reg(t.capture_regs, reg, Some(s1.cp), s1.clock), pc := t.pc + 1);
        FAdvanceEpsilonCpsIn(c, s1.(active := [t2] + ac), ov, dir, ub);
      case SetQuantToClock(q, bq) =>
        var ocp := if bq then Some(s1.cp) else None;
        SetRegCpsIn(t.quant_regs, q, ocp, s1.clock, ub);
        var t2 := t.(quant_regs := AReg.set_reg(t.quant_regs, q, ocp, s1.clock), pc := t.pc + 1);
        FAdvanceEpsilonCpsIn(c, s1.(active := [t2] + ac), ov, dir, ub);
      case CheckOracle(l) =>
        if LOr.view_get_oracle(ov, s1.cp, l) {
          SetRegCpsIn(t.look_regs, l, Some(s1.cp), s1.clock, ub);
          var t2 := t.(pc := t.pc + 1, look_regs := AReg.set_reg(t.look_regs, l, Some(s1.cp), s1.clock));
          FAdvanceEpsilonCpsIn(c, s1.(active := [t2] + ac), ov, dir, ub);
        } else {
          FAdvanceEpsilonCpsIn(c, s1.(active := ac), ov, dir, ub);
        }
      case NegCheckOracle(l) =>
        if LOr.view_get_oracle(ov, s1.cp, l) {
          FAdvanceEpsilonCpsIn(c, s1.(active := ac), ov, dir, ub);
        } else {
          FAdvanceEpsilonCpsIn(c, s1.(active := [t.(pc := t.pc + 1)] + ac), ov, dir, ub);
        }
      case WriteOracle(l) =>
        FAdvanceEpsilonCpsIn(c, s1.(active := ac), LOr.view_set_oracle(ov, s1.cp, l), dir, ub);
      case BeginLoop =>
        FAdvanceEpsilonCpsIn(c, s1.(active := [t.(exit_allowed := false, pc := t.pc + 1)] + ac), ov, dir, ub);
      case EndLoop =>
        if t.exit_allowed {
          FAdvanceEpsilonCpsIn(c, s1.(active := [t.(pc := t.pc + 1)] + ac), ov, dir, ub);
        } else {
          FAdvanceEpsilonCpsIn(c, s1.(active := ac), ov, dir, ub);
        }
      case CheckNullable(qid) =>
        if LCdn.cdn_get(s1.cdn, qid) {
          FAdvanceEpsilonCpsIn(c, s1.(active := [t.(pc := t.pc + 1)] + ac), ov, dir, ub);
        } else {
          FAdvanceEpsilonCpsIn(c, s1.(active := ac), ov, dir, ub);
        }
      case AnchorAssertion(a) =>
        if LAnc.is_satisfied(a, s1.context, dir) {
          FAdvanceEpsilonCpsIn(c, s1.(active := [t.(pc := t.pc + 1)] + ac), ov, dir, ub);
        } else {
          FAdvanceEpsilonCpsIn(c, s1.(active := ac), ov, dir, ub);
        }
      case Fail =>
        FAdvanceEpsilonCpsIn(c, s1.(active := ac), ov, dir, ub);
    }
  }

  /** The consume phase moves threads without touching any bank. */
  lemma FConsumeCpsIn(s: AI.VmState, ub: int)
    requires VmCpsIn(s, ub)
    ensures VmCpsIn(AI.FConsume(s), ub)
    decreases |s.blocked|
  {
    if |s.blocked| == 0 { return; }
    var t := s.blocked[0].0;
    var ce := s.blocked[0].1;
    var s1 := s.(blocked := s.blocked[1..]);
    assert VmCpsIn(s1, ub) by {
      forall tb | tb in s1.blocked ensures ThreadCpsIn(tb.0, ub) { assert tb in s.blocked; }
    }
    var s2 := if RC.is_accepted(s1.context.nextchar, ce)
              then s1.(active := [t.(exit_allowed := true, pc := t.pc + 1)] + s1.active)
              else s1;
    assert VmCpsIn(s2, ub) by {
      assert s.blocked[0] in s.blocked;
      assert ThreadCpsIn(t, ub);
      forall t2 | t2 in s2.active ensures ThreadCpsIn(t2, ub) {
        if t2 != t.(exit_allowed := true, pc := t.pc + 1) { assert t2 in s1.active; }
      }
    }
    FConsumeCpsIn(s2, ub);
  }

  /** THE bound: a whole search, FORWARD or BACKWARD, started at a position in
      `[0, |str|]` from threads whose banks lie in `[-1, |str|]`, returns a thread
      whose capture, look and quant banks all lie in `[-1, |str|]`. Subsumes
      `CM.FFindMatchLookCpOk` / `CM.FFindMatchLookCpOkB` (look bank, upper bound)
      and adds the capture and quant banks and the lower bound. */
  lemma FFindMatchCpsIn(c: RB.code, str: string, s: AI.VmState, ov: LOr.OracleView,
                        dir: LAnc.direction, cdn: LCdn.cdns)
    requires |s.processed.true_set| == RB.size(c) && |s.processed.false_set| == RB.size(c)
    requires dir.Forward? ==> s.context.nextchar == AI.get_char(str, s.cp)
    requires dir.Backward? ==> s.context.nextchar == AI.get_char(str, s.cp - 1)
    requires 0 <= s.cp <= |str|
    requires VmCpsIn(s, |str|)
    ensures var r := AI.FFindMatch(c, str, s, ov, dir, cdn).0;
      r.Some? ==> ThreadCpsIn(r.value, |str|)
    decreases if dir.Forward? then |str| - s.cp else s.cp
  {
    var s0 := s.(cdn := LCdn.build_cdn_v(cdn, s.cp, ov, s.context, dir));
    assert VmCpsIn(s0, |str|);
    var (s1, ov1) := AI.FAdvanceEpsilon(c, s0, ov, dir);
    FAdvanceEpsilonCpsIn(c, s0, ov, dir, |str|);
    assert VmCpsIn(s1, |str|);
    if |s1.blocked| == 0 { return; }
    match s1.context.nextchar {
      case None =>
      case Some(_) =>
        var s2 := AI.FConsume(s1);
        FConsumeCpsIn(s1, |str|);
        var s3 := s2.(processed := AI.init_bpcset(RB.size(c)), isblocked := AI.init_pcset(RB.size(c)),
                      cdn := LCdn.init_cdn(), cp := AI.incr_cp(s2.cp, dir));
        var newchar := AI.get_char(str, s3.cp - AI.cp_offset(dir));
        var s4 := s3.(context := LAnc.update_context(s3.context, newchar));
        if dir.Forward? {
          assert s.cp < |str|;                    // nextchar Some (forward) => cp in range
          assert s4.cp == s.cp + 1;
        } else {
          assert s.cp > 0;                        // nextchar Some (backward) => cp - 1 in range
          assert s4.cp == s.cp - 1;
        }
        assert VmCpsIn(s4, |str|);
        FFindMatchCpsIn(c, str, s4, ov1, dir, cdn);
    }
  }

  /** The fresh body match of any row, either kind, read at a recorded look cp
      `<= |str|`, returns banks in `[-1, |str|]`. */
  lemma FreshBodyMatchCpsIn(crv: CP.FCompiled, str: string, l: int, lk: AReg.Regs,
                            ov: LOr.OracleView, ncap: int, nlook: int, nquant: int)
    requires AReg.get_cp(lk, l).Some? ==> AReg.get_cp(lk, l).value <= |str|
    ensures var rf := M.FreshBodyMatch(crv, str, l, lk, ov, ncap, nlook, nquant);
            rf.Some? ==> ThreadCpsIn(rf.value, |str|)
  {
    var body := M.VBody(crv, l);
    var cp := if AReg.get_cp(lk, l).Some? then AReg.get_cp(lk, l).value else 0;
    var looktype := if 0 <= l < |crv.f_look_types| then crv.f_look_types[l] else R.Lookahead;
    var dir := AI.capture_direction(looktype);
    var bc := CP.compile_to_bytecode(CP.capture_regex(looktype, body));
    var cdn := if 0 <= l < |crv.f_look_cdns| then crv.f_look_cdns[l] else [];
    var s := AI.FInitState(bc, cp, AReg.init_regs(ncap), AReg.init_regs(nlook),
                           AReg.init_regs(nquant), 0, AI.cp_context(cp, str, dir));
    assert 0 <= cp <= |str|;
    InitRegsCpsIn(ncap, |str|); InitRegsCpsIn(nlook, |str|); InitRegsCpsIn(nquant, |str|);
    assert VmCpsIn(s, |str|) by {
      assert s.active == [AI.init_thread(AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant))];
    }
    FFindMatchCpsIn(bc, str, s, ov, dir, cdn);
    assert M.FreshBodyMatch(crv, str, l, lk, ov, ncap, nlook, nquant) == AI.FFindMatch(bc, str, s, ov, dir, cdn).0;
  }

  /** The capture-bank twin of `CM.FFindMatchLookCpOk[B]`, read off `FFindMatchCpsIn`. */
  lemma FFindMatchCapCpsIn(c: RB.code, str: string, s: AI.VmState, ov: LOr.OracleView,
                           dir: LAnc.direction, cdn: LCdn.cdns)
    requires |s.processed.true_set| == RB.size(c) && |s.processed.false_set| == RB.size(c)
    requires dir.Forward? ==> s.context.nextchar == AI.get_char(str, s.cp)
    requires dir.Backward? ==> s.context.nextchar == AI.get_char(str, s.cp - 1)
    requires 0 <= s.cp <= |str|
    requires VmCpsIn(s, |str|)
    ensures var r := AI.FFindMatch(c, str, s, ov, dir, cdn).0;
      r.Some? ==> CpsIn(r.value.capture_regs, |str|)
  { FFindMatchCpsIn(c, str, s, ov, dir, cdn); }

  /** The quant-bank twin of `CM.FFindMatchLookCpOk[B]`, read off `FFindMatchCpsIn`. */
  lemma FFindMatchQuantCpsIn(c: RB.code, str: string, s: AI.VmState, ov: LOr.OracleView,
                             dir: LAnc.direction, cdn: LCdn.cdns)
    requires |s.processed.true_set| == RB.size(c) && |s.processed.false_set| == RB.size(c)
    requires dir.Forward? ==> s.context.nextchar == AI.get_char(str, s.cp)
    requires dir.Backward? ==> s.context.nextchar == AI.get_char(str, s.cp - 1)
    requires 0 <= s.cp <= |str|
    requires VmCpsIn(s, |str|)
    ensures var r := AI.FFindMatch(c, str, s, ov, dir, cdn).0;
      r.Some? ==> CpsIn(r.value.quant_regs, |str|)
  { FFindMatchCpsIn(c, str, s, ov, dir, cdn); }

  /** `MirrorThread` is an involution on a thread whose banks lie in `[-1, n]`. */
  lemma MirrorThreadInvol(t: AI.Thread, n: int)
    requires ThreadCpsIn(t, n)
    ensures MIR.MirrorThread(MIR.MirrorThread(t, n), n) == t
  {
    MIR.MirrorRegsInvol(t.capture_regs, n);
    MIR.MirrorRegsInvol(t.look_regs, n);
    MIR.MirrorRegsInvol(t.quant_regs, n);
  }

  // ===========================================================================
  // §2  FXR is an involution, with no fragment premise
  // ===========================================================================

  lemma RevRev(r: R.regex)
    ensures R.reverse_regex(R.reverse_regex(r)) == r
    decreases r
  {
    match r
    case Re_alt(r1, r2) => RevRev(r1); RevRev(r2);
    case Re_con(r1, r2) => RevRev(r1); RevRev(r2);
    case Re_quant(_, _, _, r1) => RevRev(r1);
    case Re_capture(_, r1) => RevRev(r1);
    case Re_lookaround(_, _, r1) => RevRev(r1);
    case _ =>
  }

  lemma SwapSwap(r: R.regex)
    ensures OBu.SwapAnchorsRegex(OBu.SwapAnchorsRegex(r)) == r
    decreases r
  {
    match r
    case Re_alt(r1, r2) => SwapSwap(r1); SwapSwap(r2);
    case Re_con(r1, r2) => SwapSwap(r1); SwapSwap(r2);
    case Re_quant(_, _, _, r1) => SwapSwap(r1);
    case Re_capture(_, r1) => SwapSwap(r1);
    case Re_lookaround(_, _, r1) => SwapSwap(r1);
    case Re_anchor(a) => match a { case _ => }
    case _ =>
  }

  lemma RevSwap(r: R.regex)
    ensures R.reverse_regex(OBu.SwapAnchorsRegex(r)) == OBu.SwapAnchorsRegex(R.reverse_regex(r))
    decreases r
  {
    match r
    case Re_alt(r1, r2) => RevSwap(r1); RevSwap(r2);
    case Re_con(r1, r2) => RevSwap(r1); RevSwap(r2);
    case Re_quant(_, _, _, r1) => RevSwap(r1);
    case Re_capture(_, r1) => RevSwap(r1);
    case Re_lookaround(_, _, r1) => RevSwap(r1);
    case _ =>
  }

  lemma RevFlip(r: R.regex)
    ensures R.reverse_regex(FR.FlipRE(r)) == FR.FlipRE(R.reverse_regex(r))
    decreases r
  {
    match r
    case Re_alt(r1, r2) => RevFlip(r1); RevFlip(r2);
    case Re_con(r1, r2) => RevFlip(r1); RevFlip(r2);
    case Re_quant(_, _, _, r1) => RevFlip(r1);
    case Re_capture(_, r1) => RevFlip(r1);
    case Re_lookaround(_, _, r1) => RevFlip(r1);
    case _ =>
  }

  /** The forward program of the doubly-flipped row is the original row's. */
  lemma SwapRevFXR(r: R.regex)
    ensures OBu.SwapAnchorsRegex(R.reverse_regex(FST.FXR(r))) == FR.FlipRE(r)
  {
    var s := OBu.SwapAnchorsRegex(R.reverse_regex(r));
    assert FST.FXR(r) == FR.FlipRE(s);
    RevFlip(s);
    FR.FlipSwapAnchorsComm(R.reverse_regex(s));
    RevSwap(R.reverse_regex(r));
    RevRev(r);
    assert R.reverse_regex(s) == OBu.SwapAnchorsRegex(r);
    SwapSwap(r);
    assert OBu.SwapAnchorsRegex(R.reverse_regex(s)) == r;
  }

  lemma FXRInvol(r: R.regex)
    ensures FST.FXR(FST.FXR(r)) == r
  {
    SwapRevFXR(r);
    FR.FlipREInvolution(r);
    assert FST.FXR(FST.FXR(r)) == FR.FlipRE(OBu.SwapAnchorsRegex(R.reverse_regex(FST.FXR(r))));
  }

  // ===========================================================================
  // §3  The per-row fresh-match tie, for ANY body shape
  // ===========================================================================

  function MirrorOpt(t: Option<AI.Thread>, n: int): Option<AI.Thread> {
    match t
    case None => None
    case Some(x) => Some(MIR.MirrorThread(x, n))
  }

  /** The row facts the tie uses: a well-formed row whose body is in the Cdn fragment. (G5b-2) The body may
      hold a greedy CDN plus: the real list and the mirrored one build the same table at every position
      (`CMr.CdnTableSwapFXR`), so the runs agree (`CMr.FFindMatchTableCong`). Before G5b-2 this asked for
      EMPTY cdn lists on both sides. */
  ghost predicate RowOk(crv: CP.FCompiled, l: int) {
    0 <= l < |crv.f_look_types| && 0 <= l < |crv.f_look_ast|
    && LTB.LookEntryOk(crv, l, crv.f_look_types[l], crv.f_look_ast[l])
    && T.TransWf(crv.f_look_ast[l]) && NR.NestedFragmentCdnRE(crv.f_look_ast[l])
    && PIV.CapUnique(crv.f_look_ast[l]) && PIV.QuantUnique(crv.f_look_ast[l])
  }

  /** The mirrored world's forward run of `FXR(b)` with the anchor-swapped list of `b` is its run with
      `FXR(b)`'s own list (the list `FG.MirrorTables` installs). */
  lemma SwapRunIsOwnRun(b: R.regex, str: string, m: int, cap: AReg.Regs, lk: AReg.Regs, qt: AReg.Regs,
                        ov: LOr.OracleView)
    requires T.TransWf(b) && NR.NestedFragmentCdnRE(b) && PIV.CapUnique(b) && PIV.QuantUnique(b)
    requires |ov| == |str| + 1 && 0 <= m <= |str|
    ensures var n := |str|;
            var bcF := CP.compile_to_bytecode(FST.FXR(b));
            var initsF := AI.FInitState(bcF, m, cap, lk, qt, 0, AI.cp_context(m, LC.Reverse(str), LAnc.Forward));
            AI.FFindMatch(bcF, LC.Reverse(str), initsF, MIR.MirrorView(ov, n), LAnc.Forward,
                          MIR.SwapAnchorsCdns(LCdn.compile_cdns(b)))
            == AI.FFindMatch(bcF, LC.Reverse(str), initsF, MIR.MirrorView(ov, n), LAnc.Forward,
                             LCdn.compile_cdns(FST.FXR(b)))
  {
    var n := |str|;
    MIR.ReverseLen(str);
    var rstr := LC.Reverse(str);
    var ovF := MIR.MirrorView(ov, n);
    var bcF := CP.compile_to_bytecode(FST.FXR(b));
    FST.FXRStructuralCdn(b);
    M.NoWriteOracleBodyCodeCdn(FST.FXR(b));
    var initsF := AI.FInitState(bcF, m, cap, lk, qt, 0, AI.cp_context(m, rstr, LAnc.Forward));
    forall k: int | 0 <= k <= |rstr|
      ensures LCdn.build_cdn_v(MIR.SwapAnchorsCdns(LCdn.compile_cdns(b)), k, ovF, AI.cp_context(k, rstr, LAnc.Forward), LAnc.Forward)
           == LCdn.build_cdn_v(LCdn.compile_cdns(FST.FXR(b)), k, ovF, AI.cp_context(k, rstr, LAnc.Forward), LAnc.Forward)
    {
      CMr.CdnTableSwapFXR(b, str, ov, k);
    }
    CMr.FFindMatchTableCong(bcF, rstr, initsF, ovF, LAnc.Forward, MIR.SwapAnchorsCdns(LCdn.compile_cdns(b)),
                            LCdn.compile_cdns(FST.FXR(b)));
  }

  /** The per-row tie: the mirrored world's fresh match is the mirror of the real one. */
  ghost predicate RowTie(crv: CP.FCompiled, str: string, l: int, lk: AReg.Regs, ov: LOr.OracleView,
                         ncap: int, nlook: int, nquant: int)
    requires |crv.f_look_types| == |crv.f_look_ast|
    requires |ov| == |str| + 1
  {
    var n := |str|;
    M.FreshBodyMatch(FG.MirrorTables(crv), LC.Reverse(str), l, MIR.MirrorRegs(lk, n),
                     MIR.MirrorView(ov, n), ncap, nlook, nquant)
    == MirrorOpt(M.FreshBodyMatch(crv, str, l, lk, ov, ncap, nlook, nquant), n)
  }

  /** `SwapRunIsOwnRun` on the plus match (the reconstruction reads no cdn list). */
  lemma SwapRunIsOwnRunPlus(b: R.regex, str: string, m: int, cap: AReg.Regs, lk: AReg.Regs, qt: AReg.Regs,
                            ov: LOr.OracleView, plus: seq<RB.code>)
    requires T.TransWf(b) && NR.NestedFragmentCdnRE(b) && PIV.CapUnique(b) && PIV.QuantUnique(b)
    requires |ov| == |str| + 1 && 0 <= m <= |str|
    ensures var n := |str|;
            var bcF := CP.compile_to_bytecode(FST.FXR(b));
            AI.FFindMatchPlus(bcF, FST.FXR(b), plus, LC.Reverse(str), MIR.MirrorView(ov, n), LAnc.Forward, m,
                              cap, lk, qt, 0, MIR.SwapAnchorsCdns(LCdn.compile_cdns(b)))
            == AI.FFindMatchPlus(bcF, FST.FXR(b), plus, LC.Reverse(str), MIR.MirrorView(ov, n), LAnc.Forward, m,
                                 cap, lk, qt, 0, LCdn.compile_cdns(FST.FXR(b)))
  {
    SwapRunIsOwnRun(b, str, m, cap, lk, qt, ov);
  }

  /** LOOKBEHIND row, body arbitrary: mirrored fresh match == mirror of the real one. */
  lemma RowTieLB(crv: CP.FCompiled, str: string, l: int, lk: AReg.Regs, ov: LOr.OracleView,
                 ncap: int, nlook: int, nquant: int)
    requires |crv.f_look_types| == |crv.f_look_ast|
    requires RowOk(crv, l) && crv.f_look_types[l] == R.Lookbehind
    requires |ov| == |str| + 1
    requires AReg.get_cp(lk, l).Some? && CM.LookCpsLE(lk, |str|)
    ensures RowTie(crv, str, l, lk, ov, ncap, nlook, nquant)
  {
    var n := |str|;
    MIR.ReverseLen(str);
    var rstr := LC.Reverse(str);
    var crvF := FG.MirrorTables(crv);
    var lkF := MIR.MirrorRegs(lk, n);
    var ovF := MIR.MirrorView(ov, n);
    var b := crv.f_look_ast[l];
    var cp0 := AReg.get_cp(lk, l).value;
    assert 0 <= cp0 <= n by {
      assert 0 <= l < |lk.a_cp| && lk.a_cp[l] == cp0 && cp0 >= 0;
      assert AI.get_idx(lk.a_cp, l) == cp0;
    }
    FG.GetCpMirror(lk, n, l);
    assert AReg.get_cp(lkF, l).value == n - cp0;
    assert crvF.f_look_types[l] == R.Lookahead;
    assert crvF.f_look_ast[l] == FST.FXR(b);
    assert crvF.f_look_cdns[l] == LCdn.compile_cdns(FST.FXR(b));
    assert crv.f_look_cdns[l] == LCdn.compile_cdns(b);
    MIR.MirrorInitRegs(ncap, n); MIR.MirrorInitRegs(nlook, n); MIR.MirrorInitRegs(nquant, n);
    BV.BackwardReplayMirrorNested(b, str, cp0, AReg.init_regs(ncap), AReg.init_regs(nlook),
                                  AReg.init_regs(nquant), ov, LCdn.compile_cdns(b), n);
    FR.FlipCompileToBytecode(FST.XRV(b));
    assert CP.compile_to_bytecode(FST.FXR(b))
        == CP.compile_to_bytecode(OBu.SwapAnchorsRegex(R.reverse_regex(b)));
    // (G5b-2) the swapped list runs as the flipped body's own list
    SwapRunIsOwnRun(b, str, n - cp0, AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant), ov);
    assert CP.capture_regex(R.Lookahead, FST.FXR(b)) == FST.FXR(b);
    assert CP.capture_regex(R.Lookbehind, b) == R.reverse_regex(b);
    assert MIR.Mirror(cp0, n) == n - cp0;
  }

  /** LOOKAHEAD row, body arbitrary, the direction the engine lemma gives: the real
      forward match is the mirror of the mirrored backward one. */
  lemma RowTieLA(crv: CP.FCompiled, str: string, l: int, lk: AReg.Regs, ov: LOr.OracleView,
                 ncap: int, nlook: int, nquant: int)
    requires |crv.f_look_types| == |crv.f_look_ast|
    requires RowOk(crv, l) && crv.f_look_types[l] == R.Lookahead
    requires |ov| == |str| + 1
    requires AReg.get_cp(lk, l).Some? && CM.LookCpsLE(lk, |str|)
    ensures var n := |str|;
            M.FreshBodyMatch(crv, str, l, lk, ov, ncap, nlook, nquant)
            == MirrorOpt(M.FreshBodyMatch(FG.MirrorTables(crv), LC.Reverse(str), l,
                                          MIR.MirrorRegs(lk, n), MIR.MirrorView(ov, n),
                                          ncap, nlook, nquant), n)
  {
    var n := |str|;
    MIR.ReverseLen(str);
    var rstr := LC.Reverse(str);
    FS.ReverseReverse(str);
    assert LC.Reverse(rstr) == str;
    var crvF := FG.MirrorTables(crv);
    var lkF := MIR.MirrorRegs(lk, n);
    var ovF := MIR.MirrorView(ov, n);
    MIR.MirrorViewInvolution(ov, n);
    var b := crv.f_look_ast[l];
    var cp0 := AReg.get_cp(lk, l).value;
    assert 0 <= cp0 <= n by {
      assert 0 <= l < |lk.a_cp| && lk.a_cp[l] == cp0 && cp0 >= 0;
      assert AI.get_idx(lk.a_cp, l) == cp0;
    }
    FG.GetCpMirror(lk, n, l);
    assert AReg.get_cp(lkF, l).value == n - cp0;
    assert crvF.f_look_types[l] == R.Lookbehind;
    assert crvF.f_look_ast[l] == FST.FXR(b);
    assert crvF.f_look_cdns[l] == LCdn.compile_cdns(FST.FXR(b));
    assert crv.f_look_cdns[l] == LCdn.compile_cdns(b);
    MIR.MirrorInitRegs(ncap, n); MIR.MirrorInitRegs(nlook, n); MIR.MirrorInitRegs(nquant, n);
    BV.BackwardReplayMirrorNested(FST.FXR(b), rstr, n - cp0, AReg.init_regs(ncap), AReg.init_regs(nlook),
                                  AReg.init_regs(nquant), ovF, LCdn.compile_cdns(FST.FXR(b)), n);
    // (G5b-2) the swapped list of FXR(b) runs as b's own list (FXR is an involution)
    FST.FXRStructuralCdn(b);
    FXRInvol(b);
    SwapRunIsOwnRun(FST.FXR(b), rstr, cp0, AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant), ovF);
    assert MIR.MirrorView(ovF, n) == ov;
    SwapRevFXR(b);
    FR.FlipCompileToBytecode(b);
    assert CP.compile_to_bytecode(OBu.SwapAnchorsRegex(R.reverse_regex(FST.FXR(b))))
        == CP.compile_to_bytecode(b);
    assert CP.capture_regex(R.Lookbehind, FST.FXR(b)) == R.reverse_regex(FST.FXR(b));
    assert CP.capture_regex(R.Lookahead, b) == b;
    assert MIR.Mirror(n - cp0, n) == cp0;
  }

  /** LOOKAHEAD row in the useful direction, with NO bank hypothesis: the mirrored
      (backward) fresh match has its banks in `[-1, n]` by `FreshBodyMatchCpsIn`,
      so `MirrorThread` is an involution on it and `RowTieLA` turns around. */
  lemma RowTieFromLA(crv: CP.FCompiled, str: string, l: int, lk: AReg.Regs, ov: LOr.OracleView,
                     ncap: int, nlook: int, nquant: int)
    requires |crv.f_look_types| == |crv.f_look_ast|
    requires RowOk(crv, l) && crv.f_look_types[l] == R.Lookahead
    requires |ov| == |str| + 1
    requires AReg.get_cp(lk, l).Some? && CM.LookCpsLE(lk, |str|)
    ensures RowTie(crv, str, l, lk, ov, ncap, nlook, nquant)
  {
    var n := |str|;
    MIR.ReverseLen(str);
    var rstr := LC.Reverse(str);
    var crvF := FG.MirrorTables(crv);
    var lkF := MIR.MirrorRegs(lk, n);
    var ovF := MIR.MirrorView(ov, n);
    RowTieLA(crv, str, l, lk, ov, ncap, nlook, nquant);
    FG.GetCpMirror(lk, n, l);
    assert AReg.get_cp(lkF, l).Some? ==> AReg.get_cp(lkF, l).value <= |rstr| by {
      var cp0 := AReg.get_cp(lk, l).value;
      assert cp0 >= 0;
    }
    FreshBodyMatchCpsIn(crvF, rstr, l, lkF, ovF, ncap, nlook, nquant);
    var rfF := M.FreshBodyMatch(crvF, rstr, l, lkF, ovF, ncap, nlook, nquant);
    if rfF.Some? {
      MirrorThreadInvol(rfF.value, n);
    }
  }

  /** Both kinds of positive row, one statement: the shape the per-lid flip-back
      (`LookNestBackTTopDeepLidFlip`) consumes at a mixed host. */
  lemma RowTiePos(crv: CP.FCompiled, str: string, l: int, lk: AReg.Regs, ov: LOr.OracleView,
                  ncap: int, nlook: int, nquant: int)
    requires |crv.f_look_types| == |crv.f_look_ast|
    requires RowOk(crv, l) && (crv.f_look_types[l] == R.Lookahead || crv.f_look_types[l] == R.Lookbehind)
    requires |ov| == |str| + 1
    requires AReg.get_cp(lk, l).Some? && CM.LookCpsLE(lk, |str|)
    ensures RowTie(crv, str, l, lk, ov, ncap, nlook, nquant)
  {
    if crv.f_look_types[l] == R.Lookahead {
      RowTieFromLA(crv, str, l, lk, ov, ncap, nlook, nquant);
    } else {
      RowTieLB(crv, str, l, lk, ov, ncap, nlook, nquant);
    }
  }

  // ===========================================================================
  // §4  The double flip returns the original table row
  // ===========================================================================

  /** The double flip returns the original table row, so the mirrored descent can
      hand a child back to the real world. */
  lemma MirrorTablesRowInvol(crv: CP.FCompiled, l: int, la: R.lookaround, b: R.regex)
    requires |crv.f_look_types| == |crv.f_look_ast|
    requires LTB.LookEntryOk(crv, l, la, b)
    ensures LTB.LookEntryOk(FG.MirrorTables(FG.MirrorTables(crv)), l, la, b)
  {
    FXRInvol(b);
    FR.FlipLkRELaws(la);
    FG.MirrorTablesEntry(crv, l, la, b);
    FG.MirrorTablesEntry(FG.MirrorTables(crv), l, FR.FlipLkRE(la), FST.FXR(b));
  }
}
