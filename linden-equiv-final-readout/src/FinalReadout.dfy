// §2.5b STAGE 2, RUNG F (F-b) — THE FINAL READOUT at the best thread.
//
// `FFindMatchPlus` returns `FReconstructPlus(best)`; its `GmOfLive` is the
// reconstruction-aware readout `GmOfLiveR(best)` the simulation ties to the
// tree's first leaf (`PIV.BestMatchRE`). This file discharges rung E's
// `NRO.ReconReadout` hypotheses at the best thread of a MAIN pass:
//   * the statics: the plus table `FFullCompilation(ast).f_plus_bc` is the
//     canonical one (`PlusTableOkFull` — `FCompileExtra` fills exactly the
//     CIN-greedy slots, given no CDN-greedy plus), look ids are unique
//     (`LookUniqueBridge`, from the annotation's `LTB.LookUnique`);
//   * the stamp facts: every set stamp is a CIN-greedy plus inside the string
//     (`FV.RegsFinalOk`, a VM-only induction, with the code inventory
//     `TrueStampsInCin`), its body is in `qm.bodies` (`QmapOk`), and — the
//     simulation's contribution — it has a stale body and present capture
//     ancestors while live (`PSM.BestLiveRE` = `SL.StampLiveOk` at Accept);
//   * the capture facts: values set exactly with clocks (`FV.RegsFinalOk`),
//     inside-look captures unset (`PSM.BestLiveRE`'s `LooksCapUnset`),
//     sizes/foreign-capture-free (the caller's `Covers`/`OnlyCapIdsSet`).
// `FReconstructPlus` walks `ast`; the readout lives on `lazy_prefix(ast)`,
// whose prefix quantifier (qid 0, `min == 0`) is never stamped, so its
// reconstruction is the identity.
module LindenElkFinalReadout {
  import opened Std.Wrappers
  import R = RegElkRegex
  import RB = Bytecode
  import CP = Compiler
  import AI = ArrayInterp
  import AReg = Array_Regs
  import LOr = Oracle
  import LAnc = Anchors
  import LCdn = Cdn
  import T = LindenElkTranslate
  import NR = LindenElkNfaRep
  import AR = LindenElkActionsRep
  import LTB = LindenElkLookTables
  import PIV = LindenElkPikeInv
  import NI = LindenElkNestInv
  import NRC = LindenElkNulledRecon
  import NRR = LindenElkNulledReconRegs
  import NRO = LindenElkNulledReconReadout
  import SL = LindenElkStampLive
  import PSM = LindenElkPikeSim
  import FV = LindenElkFinalVm
  import FRG = LindenElkFinalRegs
  import CM = LindenElkClockMono

  // =========================================================================
  // 1. The true-stamp inventory: `SetQuantToClock(q, true)` sits only at the
  //    exit `e1 + 2` of a CIN-greedy plus (twin of `NI.StampFalseAt`).
  // =========================================================================

  /** The CIN-greedy pluses of `re`, as raw qids. */
  ghost function CinQids(re: R.regex): set<int> {
    set q: nat | q in PIV.QuantIds(re) && NRR.QidCinPlus(re, q) :: q as int
  }

  /** A true stamp at `pc` is on a CIN-greedy plus of `re`. */
  ghost predicate TrueAt(re: R.regex, code: RB.code, pc: nat) {
    forall qd: int :: NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(qd, true)) ==>
      qd >= 0 && (qd as nat) in PIV.QuantIds(re) && NRR.QidCinPlus(re, qd as nat)
  }

  lemma TrueAtLiftQuant(nul: R.nullability, qid: R.quantid, q: R.counted_quantifier, r1: R.regex,
                        code: RB.code, pc: nat)
    requires PIV.QuantUnique(R.Re_quant(nul, qid, q, r1))
    requires TrueAt(r1, code, pc)
    ensures TrueAt(R.Re_quant(nul, qid, q, r1), code, pc)
  {
    forall qd: int | NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(qd, true))
      ensures qd >= 0 && (qd as nat) in PIV.QuantIds(R.Re_quant(nul, qid, q, r1))
              && NRR.QidCinPlus(R.Re_quant(nul, qid, q, r1), qd as nat)
    {
      assert (qd as nat) in PIV.QuantIds(r1);
      assert qd != qid;
    }
  }

  lemma TrueAtLiftBin(re: R.regex, code: RB.code, pc: nat, left: bool)
    requires re.Re_alt? || re.Re_con?
    requires PIV.QuantUnique(re)
    requires left ==> TrueAt(NRR.L1(re), code, pc)
    requires !left ==> TrueAt(NRR.L2(re), code, pc)
    ensures TrueAt(re, code, pc)
  {
    var r1 := NRR.L1(re); var r2 := NRR.L2(re);
    assert PIV.QuantIds(r1) * PIV.QuantIds(r2) == {};
    forall qd: int | NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(qd, true))
      ensures qd >= 0 && (qd as nat) in PIV.QuantIds(re) && NRR.QidCinPlus(re, qd as nat)
    {
      if !left {
        var qn: nat := qd as nat;
        assert qn in PIV.QuantIds(r2);
        if qn in PIV.QuantIds(r1) { assert qn in PIV.QuantIds(r1) * PIV.QuantIds(r2); }
      }
    }
  }

  lemma TrueAtLiftCap(cid: R.capture, r1: R.regex, code: RB.code, pc: nat)
    requires TrueAt(r1, code, pc)
    ensures TrueAt(R.Re_capture(cid, r1), code, pc)
  {}

  lemma TrueStampCinMin(k: nat, qid: R.quantid, r1: R.regex, code: RB.code, pcb: nat, pce: nat, pc: nat)
    requires NR.NfaRepMinRE(k, qid, r1, code, pcb, pce)
    requires PIV.QuantUnique(r1)
    requires pcb <= pc < pce
    ensures TrueAt(r1, code, pc)
    decreases CP.rsize(r1), k + 2
  {
    assert k > 0 by { if k == 0 { assert pcb == pce; } }
    var e1: nat :| NR.GetPcRE(code, pcb) == Some(RB.SetQuantToClock(qid, false))
      && NR.NfaRepRE(r1, code, pcb + 1, e1)
      && NR.NfaRepMinRE(k - 1, qid, r1, code, e1, pce);
    NR.NfaRepIncrRE(r1, code, pcb + 1, e1);
    NR.NfaRepIncrMinRE(k - 1, qid, r1, code, e1, pce);
    if pc == pcb {
    } else if pcb + 1 <= pc < e1 {
      TrueStampCin(r1, code, pcb + 1, e1, pc);
    } else {
      TrueStampCinMin(k - 1, qid, r1, code, e1, pce, pc);
    }
  }

  lemma TrueStampCinOpt(k: nat, greedy: bool, qid: R.quantid, r1: R.regex, code: RB.code,
                        pcb: nat, pce: nat, pc: nat)
    requires NR.NfaRepOptRE(k, greedy, qid, r1, code, pcb, pce)
    requires PIV.QuantUnique(r1)
    requires pcb <= pc < pce
    ensures TrueAt(r1, code, pc)
    decreases CP.rsize(r1), k + 2
  {
    assert k > 0 by { if k == 0 { assert pcb == pce; } }
    var e1: nat :| NR.GetPcRE(code, pcb) == Some(if greedy then RB.Fork(pcb + 1, pce) else RB.Fork(pce, pcb + 1))
      && NR.GetPcRE(code, pcb + 1) == Some(RB.SetQuantToClock(qid, false))
      && NR.GetPcRE(code, pcb + 2) == Some(RB.BeginLoop)
      && NR.NfaRepRE(r1, code, pcb + 3, e1)
      && NR.GetPcRE(code, e1) == Some(RB.EndLoop)
      && NR.NfaRepOptRE(k - 1, greedy, qid, r1, code, e1 + 1, pce);
    NR.NfaRepIncrRE(r1, code, pcb + 3, e1);
    NR.NfaRepIncrOptRE(k - 1, greedy, qid, r1, code, e1 + 1, pce);
    if pc == pcb || pc == pcb + 1 || pc == pcb + 2 || pc == e1 {
    } else if pcb + 3 <= pc < e1 {
      TrueStampCin(r1, code, pcb + 3, e1, pc);
    } else {
      TrueStampCinOpt(k - 1, greedy, qid, r1, code, e1 + 1, pce, pc);
    }
  }

  /** THE INVENTORY: inside `re`'s block a true stamp carries a CIN-greedy
      plus's qid. */
  lemma TrueStampCin(re: R.regex, code: RB.code, pcb: nat, pce: nat, pc: nat)
    requires NR.NfaRepRE(re, code, pcb, pce)
    requires PIV.QuantUnique(re)
    requires pcb <= pc < pce
    ensures TrueAt(re, code, pc)
    decreases CP.rsize(re), 1
  {
    match re
    case Re_empty =>
    case Re_character(ch) =>
    case Re_alt(r1, r2) =>
      assert {:split_here} true;
      var e1: nat :| NR.GetPcRE(code, pcb) == Some(RB.Fork(pcb + 1, e1 + 1))
        && NR.NfaRepRE(r1, code, pcb + 1, e1)
        && NR.GetPcRE(code, e1) == Some(RB.Jmp(pce))
        && NR.NfaRepRE(r2, code, e1 + 1, pce);
      NR.NfaRepIncrRE(r1, code, pcb + 1, e1);
      NR.NfaRepIncrRE(r2, code, e1 + 1, pce);
      if pc == pcb || pc == e1 {
      } else if pcb + 1 <= pc < e1 {
        TrueStampCin(r1, code, pcb + 1, e1, pc);
        TrueAtLiftBin(re, code, pc, true);
      } else {
        TrueStampCin(r2, code, e1 + 1, pce, pc);
        TrueAtLiftBin(re, code, pc, false);
      }
    case Re_con(r1, r2) =>
      assert {:split_here} true;
      var e1: nat :| NR.NfaRepRE(r1, code, pcb, e1) && NR.NfaRepRE(r2, code, e1, pce);
      NR.NfaRepIncrRE(r1, code, pcb, e1);
      NR.NfaRepIncrRE(r2, code, e1, pce);
      if pc < e1 {
        TrueStampCin(r1, code, pcb, e1, pc);
        TrueAtLiftBin(re, code, pc, true);
      } else {
        TrueStampCin(r2, code, e1, pce, pc);
        TrueAtLiftBin(re, code, pc, false);
      }
    case Re_quant(nul, qid, q, r1) =>
      assert {:split_here} true;
      TrueStampCinQuant(nul, qid, q, r1, code, pcb, pce, pc);
    case Re_capture(cid, r1) =>
      assert {:split_here} true;
      var e1: nat :| NR.GetPcRE(code, pcb) == Some(RB.SetRegisterToCP(CP.start_reg(cid)))
        && NR.NfaRepRE(r1, code, pcb + 1, e1)
        && NR.GetPcRE(code, e1) == Some(RB.SetRegisterToCP(CP.end_reg(cid)))
        && pce == e1 + 1;
      NR.NfaRepIncrRE(r1, code, pcb + 1, e1);
      if pcb + 1 <= pc < e1 {
        TrueStampCin(r1, code, pcb + 1, e1, pc);
        TrueAtLiftCap(cid, r1, code, pc);
      }
    case Re_lookaround(_, _, _) =>
    case Re_anchor(_) =>
  }

  /** The quantifier arm, one scheme at a time. */
  lemma TrueStampCinQuant(nul: R.nullability, qid: R.quantid, q: R.counted_quantifier, r1: R.regex,
                          code: RB.code, pcb: nat, pce: nat, pc: nat)
    requires NR.NfaRepRE(R.Re_quant(nul, qid, q, r1), code, pcb, pce)
    requires PIV.QuantUnique(R.Re_quant(nul, qid, q, r1))
    requires pcb <= pc < pce
    ensures TrueAt(R.Re_quant(nul, qid, q, r1), code, pc)
    decreases CP.rsize(R.Re_quant(nul, qid, q, r1)), 0
  {
    var re := R.Re_quant(nul, qid, q, r1);
    assert PIV.QuantUnique(r1);
    if q.max.Some? {
      var em := NR.NfaRepREQuantInv(nul, qid, q, r1, code, pcb, pce);
      var mn := q.min as nat;
      var kx := (q.max.value - q.min) as nat;
      NR.NfaRepIncrMinRE(mn, qid, r1, code, pcb, em);
      NR.NfaRepIncrOptRE(kx, q.greedy, qid, r1, code, em, pce);
      if pc < em {
        TrueStampCinMin(mn, qid, r1, code, pcb, em, pc);
      } else {
        TrueStampCinOpt(kx, q.greedy, qid, r1, code, em, pce, pc);
      }
      TrueAtLiftQuant(nul, qid, q, r1, code, pc);
    } else if q.min == 0 {
      var e1: nat :| NR.GetPcRE(code, pcb) == Some(if q.greedy then RB.Fork(pcb + 1, e1 + 2) else RB.Fork(e1 + 2, pcb + 1))
        && NR.GetPcRE(code, pcb + 1) == Some(RB.SetQuantToClock(qid, false))
        && NR.GetPcRE(code, pcb + 2) == Some(RB.BeginLoop)
        && NR.NfaRepRE(r1, code, pcb + 3, e1)
        && NR.GetPcRE(code, e1) == Some(RB.EndLoop)
        && NR.GetPcRE(code, e1 + 1) == Some(RB.Jmp(pcb))
        && pce == e1 + 2;
      NR.NfaRepIncrRE(r1, code, pcb + 3, e1);
      if pcb + 3 <= pc < e1 {
        TrueStampCin(r1, code, pcb + 3, e1, pc);
        TrueAtLiftQuant(nul, qid, q, r1, code, pc);
      }
    } else if nul == R.NonNullable {
      var em, e1 := NR.NfaRepREPlusInv(nul, qid, q, r1, code, pcb, pce);
      var mn1 := (q.min - 1) as nat;
      NR.NfaRepIncrMinRE(mn1, qid, r1, code, pcb, em);
      NR.NfaRepIncrRE(r1, code, em + 1, e1);
      if pc < em {
        TrueStampCinMin(mn1, qid, r1, code, pcb, em, pc);
        TrueAtLiftQuant(nul, qid, q, r1, code, pc);
      } else if em + 1 <= pc < e1 {
        TrueStampCin(r1, code, em + 1, e1, pc);
        TrueAtLiftQuant(nul, qid, q, r1, code, pc);
      }
    } else if !q.greedy {
      var em, e1 := NR.NfaRepREGenInv(nul, qid, q, r1, code, pcb, pce);
      var mn := q.min as nat;
      NR.NfaRepIncrMinRE(mn, qid, r1, code, pcb, em);
      NR.NfaRepIncrRE(r1, code, em + 3, e1);
      if pc < em {
        TrueStampCinMin(mn, qid, r1, code, pcb, em, pc);
        TrueAtLiftQuant(nul, qid, q, r1, code, pc);
      } else if em + 3 <= pc < e1 {
        TrueStampCin(r1, code, em + 3, e1, pc);
        TrueAtLiftQuant(nul, qid, q, r1, code, pc);
      }
    } else {
      var em, e1 := NR.NfaRepRECinInv(nul, qid, q, r1, code, pcb, pce);
      var mn1 := (q.min - 1) as nat;
      NR.NfaRepIncrMinRE(mn1, qid, r1, code, pcb, em);
      NR.NfaRepIncrRE(r1, code, em + 3, e1);
      if pc < em {
        TrueStampCinMin(mn1, qid, r1, code, pcb, em, pc);
        TrueAtLiftQuant(nul, qid, q, r1, code, pc);
      } else if em + 3 <= pc < e1 {
        TrueStampCin(r1, code, em + 3, e1, pc);
        TrueAtLiftQuant(nul, qid, q, r1, code, pc);
      } else if pc == e1 + 2 {
        // THE true stamp: this very quantifier, a CIN-greedy plus
        assert qid >= 0 && (qid as nat) in PIV.QuantIds(re);
        assert NRR.QidCinPlus(re, qid as nat);
      }
    }
  }

  /** The whole main block: every true stamp's qid is in `CinQids(re)`. */
  lemma TrueStampsInCin(re: R.regex, code: RB.code, endl: nat)
    requires NR.NfaRepRE(re, code, 0, endl) && PIV.QuantUnique(re)
    requires NR.GetPcRE(code, endl) == Some(RB.Accept) && |code| == endl + 1
    ensures FV.TrueStampsIn(code, CinQids(re))
  {
    forall pc: nat, q: int | NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(q, true))
      ensures q in CinQids(re)
    {
      assert pc < endl;
      TrueStampCin(re, code, 0, endl, pc);
      var qn: nat := q as nat;
      assert qn in PIV.QuantIds(re) && NRR.QidCinPlus(re, qn) && qn as int == q;
    }
  }

  // =========================================================================
  // 2. The plus table: `FCompileExtra` fills exactly the CIN-greedy slots.
  // =========================================================================

  lemma FCompileExtraPlus(r: R.regex, c: CP.FCompiled, q: nat)
    requires T.TransWf(r) && PIV.QuantUnique(r) && NRC.NoCdnPlusRE(r)
    ensures |CP.FCompileExtra(r, c).f_plus_bc| == |c.f_plus_bc|
    ensures q !in PIV.QuantIds(r) ==>
              AI.get_code_v(CP.FCompileExtra(r, c).f_plus_bc, q) == AI.get_code_v(c.f_plus_bc, q)
    ensures q in PIV.QuantIds(r) && q < |c.f_plus_bc| ==>
              AI.get_code_v(CP.FCompileExtra(r, c).f_plus_bc, q)
              == (if NRR.QidCinPlus(r, q) then CP.compile_reconstruct_nulled(PIV.QidBody(r, q))
                  else AI.get_code_v(c.f_plus_bc, q))
    decreases r
  {
    match r
    case Re_empty =>
    case Re_character(_) =>
    case Re_anchor(_) =>
    case Re_capture(_, r1) =>
      FCompileExtraPlus(r1, c, q);
    case Re_alt(r1, r2) =>
      var c1 := CP.FCompileExtra(r1, c);
      FCompileExtraPlus(r1, c, q);
      FCompileExtraPlus(r2, c1, q);
      assert PIV.QuantIds(r1) * PIV.QuantIds(r2) == {};
      if q in PIV.QuantIds(r1) { assert q !in PIV.QuantIds(r2) by { assert q !in PIV.QuantIds(r1) * PIV.QuantIds(r2); } }
    case Re_con(r1, r2) =>
      var c1 := CP.FCompileExtra(r1, c);
      FCompileExtraPlus(r1, c, q);
      FCompileExtraPlus(r2, c1, q);
      assert PIV.QuantIds(r1) * PIV.QuantIds(r2) == {};
      if q in PIV.QuantIds(r1) { assert q !in PIV.QuantIds(r2) by { assert q !in PIV.QuantIds(r1) * PIV.QuantIds(r2); } }
    case Re_quant(nul, qid, quant, r1) =>
      var cond := quant.min > 0 && quant.max == None && nul != R.NonNullable && quant.greedy;
      var c1 := if cond then c.(f_plus_bc := CP.upd(c.f_plus_bc, qid, CP.compile_reconstruct_nulled(r1))) else c;
      assert |c1.f_plus_bc| == |c.f_plus_bc|;
      FCompileExtraPlus(r1, c1, q);
      if qid >= 0 && (qid as nat) == q {
        assert q !in PIV.QuantIds(r1);
        assert cond <==> NRR.QidCinPlus(r, q);
      } else {
        assert AI.get_code_v(c1.f_plus_bc, q) == AI.get_code_v(c.f_plus_bc, q);
      }
    case Re_lookaround(lid, la, body) =>
      var c1 := c.(f_look_types := CP.upd(c.f_look_types, lid, la));
      var c2 := c1.(f_look_cdns := CP.upd(c1.f_look_cdns, lid, LCdn.compile_cdns(body)));
      var c3 := c2.(f_look_ast := CP.upd(c2.f_look_ast, lid, body));
      var c4 := c3.(f_look_build_bc := CP.upd(c3.f_look_build_bc, lid, CP.compile_to_write(CP.oracle_regex(la, body), lid)));
      var c5 := c4.(f_look_capture_bc := CP.upd(c4.f_look_capture_bc, lid, CP.compile_to_bytecode(CP.capture_regex(la, body))));
      assert c5.f_plus_bc == c.f_plus_bc;
      FCompileExtraPlus(body, c5, q);
  }

  /** THE canonical table: `FFullCompilation(ast)`'s plus table is
      `PlusTableOk` for the main regex `lazy_prefix(ast)`. */
  lemma PlusTableOkFull(ast: R.regex)
    requires T.TransWf(R.lazy_prefix(ast)) && PIV.QuantUnique(R.lazy_prefix(ast)) && NRC.NoCdnPlusRE(ast)
    ensures NRR.PlusTableOk(R.lazy_prefix(ast), CP.FFullCompilation(ast).f_plus_bc)
  {
    var re := R.lazy_prefix(ast);
    var pre := R.Re_quant(R.NonNullable, 0, R.CountedQuant(0, None, false), R.Re_character(R.Dot));
    assert re == R.Re_con(pre, ast);
    var maxlook := R.max_lookaround(ast);
    var maxquant := R.max_quant(ast);
    var nlook := if maxlook + 1 >= 0 then maxlook + 1 else 0;
    var nquant := if maxquant + 1 >= 0 then maxquant + 1 else 0;
    var seed := CP.FCompiled(ast, CP.compile_to_bytecode(re), LCdn.compile_cdns(ast),
                             seq(nlook, i => R.Lookahead), seq(nlook, i => R.Re_empty),
                             seq(nlook, i => []), seq(nlook, i => []),
                             seq(nlook, i => []), seq(nquant, i => []));
    assert CP.FFullCompilation(ast) == CP.FCompileExtra(ast, seed);
    NI.QuantIdsLEMaxQuant(ast);
    assert PIV.QuantIds(pre) == {0};
    assert PIV.QuantIds(pre) * PIV.QuantIds(ast) == {};
    forall q: nat | q in PIV.QuantIds(re)
      ensures AI.get_code_v(CP.FFullCompilation(ast).f_plus_bc, q as int)
              == (if NRR.QidCinPlus(re, q) then CP.compile_reconstruct_nulled(PIV.QidBody(re, q)) else [])
    {
      FCompileExtraPlus(ast, seed, q);
      if q in PIV.QuantIds(ast) {
        assert q !in PIV.QuantIds(pre) by { assert q !in PIV.QuantIds(pre) * PIV.QuantIds(ast); }
        assert q < |seed.f_plus_bc|;
        assert AI.get_code_v(seed.f_plus_bc, q) == [];
      } else {
        assert q == 0;
        assert !NRR.QidCinPlus(re, q);
        assert AI.get_code_v(seed.f_plus_bc, q) == [];
      }
    }
  }

  // =========================================================================
  // 3. Look-id uniqueness: the annotation's (`LTB`) form gives rung E's.
  // =========================================================================

  lemma LookRegsOfIds(r: R.regex)
    requires LTB.LookUnique(r)
    ensures NRR.LookRegsOf(r) == set x | x in LTB.LookIds(r) :: x as int
    decreases r
  {
    match r
    case Re_empty =>
    case Re_character(_) =>
    case Re_anchor(_) =>
    case Re_alt(r1, r2) => LookRegsOfIds(r1); LookRegsOfIds(r2);
    case Re_con(r1, r2) => LookRegsOfIds(r1); LookRegsOfIds(r2);
    case Re_quant(_, _, _, r1) => LookRegsOfIds(r1);
    case Re_capture(_, r1) => LookRegsOfIds(r1);
    case Re_lookaround(lid, _, r1) =>
      LookRegsOfIds(r1);
      assert (set x | x in LTB.LookIds(r) :: x as int)
          == {lid} + (set x | x in LTB.LookIds(r1) :: x as int);
  }

  lemma LookUniqueBridge(r: R.regex)
    requires LTB.LookUnique(r)
    ensures NRR.LookUnique(r)
    decreases r
  {
    match r
    case Re_empty =>
    case Re_character(_) =>
    case Re_anchor(_) =>
    case Re_alt(r1, r2) =>
      LookUniqueBridge(r1); LookUniqueBridge(r2);
      LookRegsOfIds(r1); LookRegsOfIds(r2);
      forall x | x in NRR.LookRegsOf(r1) * NRR.LookRegsOf(r2) ensures false {
        var a: nat :| a in LTB.LookIds(r1) && a as int == x;
        var b: nat :| b in LTB.LookIds(r2) && b as int == x;
        assert a == b && a in LTB.LookIds(r1) * LTB.LookIds(r2);
      }
    case Re_con(r1, r2) =>
      LookUniqueBridge(r1); LookUniqueBridge(r2);
      LookRegsOfIds(r1); LookRegsOfIds(r2);
      forall x | x in NRR.LookRegsOf(r1) * NRR.LookRegsOf(r2) ensures false {
        var a: nat :| a in LTB.LookIds(r1) && a as int == x;
        var b: nat :| b in LTB.LookIds(r2) && b as int == x;
        assert a == b && a in LTB.LookIds(r1) * LTB.LookIds(r2);
      }
    case Re_quant(_, _, _, r1) => LookUniqueBridge(r1);
    case Re_capture(_, r1) => LookUniqueBridge(r1);
    case Re_lookaround(lid, _, r1) =>
      LookUniqueBridge(r1);
      LookRegsOfIds(r1);
      if lid in NRR.LookRegsOf(r1) {
        var a: nat :| a in LTB.LookIds(r1) && a as int == lid;
        assert (lid as nat) in LTB.LookIds(r1);
      }
  }

  // =========================================================================
  // 4. THE FINAL READOUT.
  // =========================================================================

  /** The prefix quantifier is never stamped: its reconstruction is the identity. */
  lemma PrefixIdentity(ast: R.regex, rg: NRC.Regs3, plus_bcv: seq<RB.code>, str: string, ov: LOr.OracleView)
    requires AReg.get_cp(rg.2, 0) == None
    ensures AI.FNulledPlus(R.lazy_prefix(ast), rg.0, rg.1, rg.2, plus_bcv, str, ov, LAnc.Forward)
         == AI.FNulledPlus(ast, rg.0, rg.1, rg.2, plus_bcv, str, ov, LAnc.Forward)
  {
    var pre := R.Re_quant(R.NonNullable, 0, R.CountedQuant(0, None, false), R.Re_character(R.Dot));
    assert R.lazy_prefix(ast) == R.Re_con(pre, ast);
    assert AI.FNulledPlus(pre, rg.0, rg.1, rg.2, plus_bcv, str, ov, LAnc.Forward) == (rg.0, rg.1, rg.2, ov);
  }

  /** THE FINAL READOUT: at the best thread of a main pass, `GmOfLive` of the
      reconstructed registers is the reconstruction-aware readout of the
      thread's own, and the oracle view is untouched. */
  lemma FinalReadout(qm: AR.QMap, ast: R.regex, str: string, th: AI.Thread, ncap: int, nlook: int, nquant: int)
    requires T.TransWf(R.lazy_prefix(ast))
    requires PIV.CapUnique(R.lazy_prefix(ast)) && PIV.QuantUnique(R.lazy_prefix(ast))
    requires LTB.LookUnique(R.lazy_prefix(ast)) && NRC.NoCdnPlusRE(ast)
    requires AR.QmapOk(R.lazy_prefix(ast), qm)
    requires PSM.BestLiveRE(R.lazy_prefix(ast), th)
    requires FV.RegsFinalOk(th, |str|, CinQids(R.lazy_prefix(ast)))
    requires NRR.WfRegs((th.capture_regs, th.look_regs, th.quant_regs))
    requires NRR.Covers(R.lazy_prefix(ast), (th.capture_regs, th.look_regs, th.quant_regs))
    requires NRO.OnlyCapIdsSet(R.lazy_prefix(ast), (th.capture_regs, th.look_regs, th.quant_regs))
    requires CM.ThreadRegsWf(th, ncap, nlook, nquant)
    ensures var rp := AI.FReconstructPlus(th, ast, CP.FFullCompilation(ast).f_plus_bc, str, qm.ov, LAnc.Forward);
            rp.1 == qm.ov && rp.0.pc == th.pc && rp.0.exit_allowed == th.exit_allowed
            && PIV.GmOfLive(R.lazy_prefix(ast), rp.0.capture_regs, rp.0.look_regs, rp.0.quant_regs)
               == PIV.GmOfLiveR(R.lazy_prefix(ast), qm, str, th.capture_regs, th.look_regs, th.quant_regs)
            // the reconstructed thread is a well-formed bank again, and the
            // prefix quantifier's clock is untouched (`FilterResetLazyPrefix`)
            && CM.ThreadRegsWf(rp.0, ncap, nlook, nquant)
            && AI.get_idx(rp.0.quant_regs.a_clk, 0) == AI.get_idx(th.quant_regs.a_clk, 0)
            // (F-c) quant clocks stay >= -1 (the synthetic winner's `WinRegsOk`)
            && (forall k: int :: AI.get_idx(rp.0.quant_regs.a_clk, k) >= -1)
  {
    var re := R.lazy_prefix(ast);
    var pre := R.Re_quant(R.NonNullable, 0, R.CountedQuant(0, None, false), R.Re_character(R.Dot));
    assert re == R.Re_con(pre, ast);
    var rg: NRC.Regs3 := (th.capture_regs, th.look_regs, th.quant_regs);
    var plus := CP.FFullCompilation(ast).f_plus_bc;

    // statics
    PlusTableOkFull(ast);
    LookUniqueBridge(re);
    assert NRC.NoCdnPlusRE(re);

    // register facts
    assert PSM.BestLiveRE(re, th);
    assert SL.StampLiveOk(re, rg.0.a_clk, rg.2.a_clk, rg.2.a_cp) && PIV.LooksCapUnset(re, rg.0.a_clk)
      by { reveal PSM.BestLiveRE; }
    assert NRR.CapValWf(rg);
    assert NRR.LookCapsAbsent(re, rg) by {
      forall c: nat | c in PIV.CapIdsInLooks(re) ensures AI.get_idx(rg.0.a_cp, CP.start_reg(c)) < 0 {
        assert AI.get_idx(rg.0.a_clk, CP.start_reg(c)) < 0;
      }
    }
    assert {:split_here} true;
    assert NRO.StampsLocal(qm, re, str, rg, -1) by {
      forall q: nat | q in PIV.QuantIds(re) && AI.get_idx(rg.2.a_cp, q) >= 0
        ensures NRR.QidCinPlus(re, q)
                && 0 <= AI.get_idx(rg.2.a_cp, q) <= |str|
                && (q as int) in qm.bodies && qm.bodies[q as int] == PIV.QidBody(re, q)
                && (PIV.QChainFresh(re, rg.2.a_clk, -1, q) ==>
                      PIV.PathPresentQ(re, rg.0.a_clk, rg.2.a_clk, -1, q)
                      && NRR.RegsStale(PIV.QidBody(re, q), rg, AI.get_idx(rg.2.a_clk, q)))
      {
        assert (q as int) in CinQids(re);
        var qn: nat :| qn in PIV.QuantIds(re) && NRR.QidCinPlus(re, qn) && qn as int == q as int;
        assert qn == q;
        PIV.QmapOkBodyAtQid(re, qm, q);
        SL.StampLiveAt(re, rg.0.a_clk, rg.2.a_clk, rg.2.a_cp, q);
      }
    }
    assert {:split_here} true;
    NRO.ReconReadout(qm, re, rg, plus, str, qm.ov);

    // the prefix is never stamped: FReconstructPlus(ast) is FNulledPlus(re)
    assert AReg.get_cp(rg.2, 0) == None by {
      assert 0 in PIV.QuantIds(re);
      if AI.get_idx(rg.2.a_cp, 0) >= 0 {
        assert (0 as int) in CinQids(re);
        var qn: nat :| qn in PIV.QuantIds(re) && NRR.QidCinPlus(re, qn) && qn as int == 0;
        assert qn == 0 && !NRR.QidCinPlus(re, 0);
      }
    }
    PrefixIdentity(ast, rg, plus, str, qm.ov);

    // the reconstructed bank: frame (rung E) + the value bound (FinalRegs)
    assert {:split_here} true;
    assert NRO.StampsInRange(re, rg, str);
    assert FRG.CapValGe(rg) by {
      forall k: int ensures AI.get_idx(rg.0.a_cp, k) >= -1 { assert PIV.CapRegWf(rg.0); }
    }
    assert FRG.QClkGe(rg);   // RegsFinalOk's clock half
    NRO.FNulledPlusFrame(qm, re, rg, plus, str, qm.ov);
    FRG.FPValGe(qm, re, rg, plus, str, qm.ov);
    var rg2 := NRO.FP(re, rg, plus, str, qm.ov);
    var rp := AI.FReconstructPlus(th, ast, plus, str, qm.ov, LAnc.Forward);
    assert (rp.0.capture_regs, rp.0.look_regs, rp.0.quant_regs) == rg2;
    assert FRG.QClkGe(rg2);
    assert PIV.CapRegWf(rp.0.capture_regs) by {
      assert NRR.WfRegs(rg2) && NRR.CapValWf(rg2) && FRG.CapValGe(rg2);
    }
    assert NRR.Sized3(rg2, rg);
    assert CM.ThreadRegsWf(rp.0, ncap, nlook, nquant);
    // quant register 0 (the prefix's) is outside every stamped body
    NRR.InnerSub(ast);
    NRR.QuantRegsOfChar(ast);
    assert PIV.QuantIds(pre) == {0};
    assert PIV.QuantIds(pre) * PIV.QuantIds(ast) == {};
    assert 0 !in NRR.InnerQuantRegs(re) by {
      assert NRR.InnerQuantRegs(pre) == {};
      if 0 in NRR.InnerQuantRegs(ast) {
        assert 0 in NRR.QuantRegsOf(ast);
        assert (0 as nat) in PIV.QuantIds(ast);
        assert (0 as nat) in PIV.QuantIds(pre) * PIV.QuantIds(ast);
      }
    }
  }
}
