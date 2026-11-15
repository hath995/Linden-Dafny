// §2.5b STAGE 2, RUNG F (F-c, c6) — CIN-GREEDY PLUSES NEXT TO LOOKAROUNDS.
//
// The main theorem, with no `NoNulledPlusRaw` gate: greedy
// CI-nullable pluses (`(a?)+`) may sit OUTSIDE lookarounds, provided their
// bodies are look-free and no look body holds a nulled plus. The two machines
// split the group space at `S = CapIdsInLooks(re)`:
//   * OUTSIDE `S` — machine A (`PSM.FindMatchSimRENested`, gate-free), rung C's
//     checked tree (`ResAgreeAtOutside(tstar, t, inp, S)`) and the F-b readout
//     (`FRD.FinalReadout`): the spec leaf is `GmOfLive` of the reconstructed
//     winner `rp = FReconstructPlus(best)`;
//   * INSIDE `S` — machine B (the lift-sim band on the engine-shaped walk,
//     `L3aCompositeCloseRecG`), whose carriers read only look registers and the
//     clocks of the looks' ANCESTORS, none of which a look-free CIN body owns
//     (`CLP.AncAvoidQ`), so they move from `best` to `rp`.
// The endpoint (look loop, owner packages, deep conclusion) runs on the
// SYNTHETIC winner `rp0` = `rp` with the outside-look quant positions cleared:
// it has the quant finality the endpoint's replay lemmas read, the same clocks
// (so the same `GmOfLive`), and the same engine answer (`QCI.FLookLoopAgree`).
module LindenElkMainCinLk {
  import opened Std.Wrappers
  import R = RegElkRegex
  import RB = Bytecode
  import CP = Compiler
  import NR = LindenElkNfaRep
  import AI = ArrayInterp
  import AReg = Array_Regs
  import LG = Groups
  import LT = Tree
  import LC = Chars
  import L = Regex
  import LS = Semantics
  import BS = BooleanSemantics
  import WP = WarblrePrimitives
  import LW = WarblreRegExpRecord
  import LOr = Oracle
  import LAnc = Anchors
  import LCdn = Cdn
  import LN = WarblreNumeric
  import AR = LindenElkActionsRep
  import EL = LindenElkEntryLk
  import GR = LindenElkGuardsRun         // (G5a-1 row N) the guard premise, for real
  import PIV = LindenElkPikeInv
  import CM = LindenElkClockMono
  import M = LindenElkMain
  import T = LindenElkTranslate
  import LL = LindenElkLookLeaves
  import NUL = LindenElkNullable
  import LTB = LindenElkLookTables
  import NI = LindenElkNestInv
  import CW = LindenElkCinWalk
  import RF = LindenElkReconFrame
  import CLP = LindenElkCinLookPaths
  import QCI = LindenElkQuantCpIrrel
  import FRD = LindenElkFinalReadout
  import FV = LindenElkFinalVm
  import NRR = LindenElkNulledReconRegs
  import NRC = LindenElkNulledRecon
  import RL = LindenElkRegsLaws
  import LES = LindenElkSpec
  import FC = LindenElkFlipClosed
  import TRM = LindenTreeResMirror
  import SD = LindenSpanDuality
  import OS = LindenElkOracleSpec
  import NRO = LindenElkNulledReconReadout
  import opened LindenElkLiftSimCore
  import opened LindenElkLiftSimOracle
  import opened LindenElkLiftSimChain
  import opened LindenElkLiftSimGate
  import opened LindenElkLiftSimCarriers
  import opened LindenElkLiftSimDeep
  import opened LindenElkLiftSimForward
  import opened LindenElkLiftSimMain
  import PSM = LindenElkPikeSim
  import PT = PikeTree
  import CR = Correctness
  import TT = LindenElkTreeThread
  import TREP = LindenElkTreeRep
  import ATR = LindenElkActionsTreeRep
  import WO = LindenElkWalkOk
  import WkE = LindenElkWalkOkEntry
  import NB = LindenElkNulledPlusBool
  import OE = LindenElkOracleEntry
  import OB = LindenElkOracleBuild
  import LFU = FunctionalUtils
  import FS = FunctionalSemantics
  import PTL = LindenElkPikeTreeLk
  import CG = LindenElkFlipClosedG       // (gate B) the scope-free closedness ladder
  import LB = LindenElkLookBank          // (gate C, G2) the look-bank invariant
  import opened LindenElkBankFrames      // (G3a, two-machines) ClkFrame, AncFrame, QInCinQ, NRRLookIdsEq, OnlyCapIdsFromFrameOuter
  import opened LindenElkTwoMachines     // (G3a) TranslateCinOk, the four tie transports

  // =========================================================================
  // 0. Statics: the glue's side condition on the translated regex.
  // =========================================================================

  // (G3a) `LookFreeLkBodies` and `TranslateCinOk` moved to two-machines (`LindenElkTwoMachines`).

  // =========================================================================
  // 1. The synthetic winner.
  // =========================================================================

  /** `th` with the quant positions in `D` cleared (clocks kept). */
  ghost function ClearQuantCps(th: AI.Thread, D: set<int>): AI.Thread {
    var q := th.quant_regs;
    th.(quant_regs := AReg.ARegs(seq(|q.a_cp|, i requires 0 <= i < |q.a_cp| => if i in D then -1 else q.a_cp[i]), q.a_clk))
  }

  lemma ClearQuantCpsFacts(th: AI.Thread, D: set<int>)
    ensures var th0 := ClearQuantCps(th, D);
            th0.pc == th.pc && th0.capture_regs == th.capture_regs && th0.look_regs == th.look_regs
            && th0.exit_allowed == th.exit_allowed
            && th0.quant_regs.a_clk == th.quant_regs.a_clk
            && |th0.quant_regs.a_cp| == |th.quant_regs.a_cp|
            && (forall k :: k in D ==> AI.get_idx(th0.quant_regs.a_cp, k) == -1)
            && (forall k :: k !in D ==> AI.get_idx(th0.quant_regs.a_cp, k) == AI.get_idx(th.quant_regs.a_cp, k))
            && QCI.QAgree(th.quant_regs, th0.quant_regs, D)
  {}

  /** Same clocks, same live group map. */
  lemma ClearQuantCpsGm(re: R.regex, th: AI.Thread, D: set<int>)
    ensures var th0 := ClearQuantCps(th, D);
            PIV.GmOfLive(re, th0.capture_regs, th0.look_regs, th0.quant_regs)
            == PIV.GmOfLive(re, th.capture_regs, th.look_regs, th.quant_regs)
  {
    var th0 := ClearQuantCps(th, D);
    PIV.GmOfLiveClkCong(re, th.capture_regs, th0.look_regs, th.look_regs, th0.quant_regs, th.quant_regs);
  }

  // =========================================================================
  // 2. The tie transport: machine B's carriers at (bleaf, best) become carriers
  //    at (the spec leaf, rp0).
  // =========================================================================

  // (G3a) `ClkFrame` and `AncFrame` moved to two-machines (`LindenElkBankFrames`), as were the four transports
  // (`TieOkTTransport`, `TieBackTransport`, `TieDeepTransport`, `TieTransport`).

  // =========================================================================
  // 3. The endpoint's register facts at the synthetic winner.
  // =========================================================================

  /** `M.WinRegsOk` minus the quant finality: what the main run delivers about
      its winner WITHOUT the gate (stamps may be true). */
  opaque ghost predicate WinRegsOkG(ast: R.regex, re: R.regex, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
                                    th: AI.Thread, ncap: int, nlook: int, nquant: int) {
    CM.ThreadRegsWf(th, ncap, nlook, nquant)
    && CM.LookCpsLE(th.look_regs, |str|)
    && (forall l: int :: 1 <= l <= R.max_lookaround(ast) && AReg.get_cp(th.look_regs, l).Some? ==>
                           exists la: R.lookaround, body: R.regex :: LTB.LookEntryOk(crv, l, la, body))
    && (forall l: int, la: R.lookaround, body: R.regex ::
          1 <= l <= R.max_lookaround(ast) && LTB.LookEntryOk(crv, l, la, body) ==>
            CM.RegsAgreeInside(th.capture_regs, AReg.init_regs(ncap), PIV.CaptureRegs(body)))
    && (forall l1: int, la1: R.lookaround, b1: R.regex, l2: int ::
          (1 <= l1 <= R.max_lookaround(ast) && LTB.LookEntryOk(crv, l1, la1, b1)
          && 1 <= l2 <= R.max_lookaround(ast) && l2 != l1
          && AReg.get_cp(th.look_regs, l2).Some?) ==> l2 !in M.LookIdSet(b1))
    && CM.RegsAgreeOutside(th.quant_regs, AReg.init_regs(nquant), M.QIdsOuter(re))
    && CM.RegsAgreeOutside(th.look_regs, AReg.init_regs(nlook), M.DirectLidSet(re))
    && CM.LookClkSetWithCp(th.look_regs) && CM.LookCpSetWithClk(th.look_regs)
    && CM.LookCpsOracleTrue(th.look_regs, ov)
    // (gate C, G2) only POSITIVE lids are ever recorded, as in `M.WinRegsOk`
    && LB.LookSetIn(th.look_regs, LB.PosLookIds(re))
  }

  /** The gate-free twin of `M.WinRegsOkFromRun` (the look-row producers need
      only the look-bodies gate). */
  lemma WinRegsOkGFromRun(
    ast: R.regex, re: R.regex, crv: CP.FCompiled, code: RB.code, str: string,
    ov: LOr.OracleView, cdn: LCdn.cdns, inits: AI.VmState,
    cap: AReg.Regs, look: AReg.Regs, quant: AReg.Regs,
    ncap: int, nlook: int, nquant: int, endl: nat, result: Option<AI.Thread>)
    requires crv == CP.FFullCompilation(ast)
    requires re == R.lazy_prefix(ast)
    requires M.LookBodiesPlusGateRE(re)   // (G3a) the weak gate
    requires T.TransWf(re)   // (G3a) main-theorem's re-gated row lemmas ask for it
    requires code == CP.compile_to_bytecode(re)
    requires NR.NestedFragmentCdnRE(re)
    requires PIV.CapUnique(re) && PIV.QuantUnique(re) && LTB.LookUnique(re)
    requires LTB.LookTablesOk(re, crv)
    requires NR.NfaRepRE(re, code, 0, endl) && |code| == endl + 1
    requires NR.GetPcRE(code, endl) == Some(RB.Accept)
    requires ncap >= 0 && nlook >= 0 && nquant >= 0
    requires cap == AReg.init_regs(ncap) && look == AReg.init_regs(nlook) && quant == AReg.init_regs(nquant)
    requires |inits.processed.true_set| == RB.size(code) && |inits.processed.false_set| == RB.size(code)
    requires inits.context.nextchar == AI.get_char(str, inits.cp)
    requires 0 <= inits.cp <= |str| && inits.clock >= 0
    requires inits.active == [AI.init_thread(cap, look, quant)]
    requires inits.blocked == [] && inits.bestmatch.None?
    requires result == AI.FFindMatch(code, str, inits, ov, LAnc.Forward, cdn).0
    ensures result.Some? ==> WinRegsOkG(ast, re, crv, str, ov, result.value, ncap, nlook, nquant)
  {
    M.LookRowsDynamicCdn(ast, re, crv, code, str, ov, cdn, inits, cap, look, quant,
                            ncap, nlook, nquant, endl, result);
    M.FStabilityCdn(ast, re, crv, code, str, ov, cdn, inits, cap, look, quant, nlook, result);
    var initlk := AReg.init_regs(nlook);
    var Sd := M.DirectLidSet(re);
    M.DirectLidClassifiedCdn(re);
    assert CM.VmLooksAgree(inits, initlk, Sd) by {
      forall t | t in inits.active ensures CM.RegsAgreeOutside(t.look_regs, initlk, Sd) {
        assert t == AI.init_thread(cap, look, quant);
      }
    }
    CM.FFindMatchLookFrame(code, str, inits, ov, LAnc.Forward, cdn, initlk, Sd);
    M.NoWriteOracleBodyCodeCdn(re);
    if result.Some? {
      M.MainMatchBodyQuantsInitCdn(re, code, str, inits, cap, look, quant, ov, cdn, result);
      assert CM.VmLookClkSet(inits) by {
        RL.AInitLaws(nlook);
        forall lz | AI.get_idx(look.a_cp, lz) >= 0 ensures AI.get_idx(look.a_clk, lz) >= 0 {
          if 0 <= lz < nlook { assert look.a_cp[lz] == -1; }
        }
      }
      CM.FFindMatchLookClkSet(code, str, inits, ov, LAnc.Forward, cdn);
      assert CM.VmLookCpSet(inits) by {
        RL.AInitLaws(nlook);
        forall lz | AI.get_idx(look.a_clk, lz) >= 0 ensures AI.get_idx(look.a_cp, lz) >= 0 {
          if 0 <= lz < nlook { assert look.a_clk[lz] == -1; }
        }
      }
      CM.FFindMatchLookCpSet(code, str, inits, ov, LAnc.Forward, cdn);
      assert CM.VmLookOracleTrue(inits, ov) by {
        RL.AInitLaws(nlook);
        forall lz | AI.get_idx(look.a_cp, lz) >= 0
          ensures LOr.view_get_oracle(ov, AI.get_idx(look.a_cp, lz), lz)
        {
          if 0 <= lz < nlook { assert look.a_cp[lz] == -1; }
        }
      }
      CM.FFindMatchLookOracleTrue(code, str, inits, ov, LAnc.Forward, cdn);
      // (gate C, G2) the main run records only positive lids (as in `M.WinRegsOkFromRun`)
      assert LB.LookSetIn(result.value.look_regs, LB.PosLookIds(re)) by {
        var P := LB.PosLookIds(re);
        LB.CompileToBytecodeChecksIn(re, P);
        assert LB.VmLookSetIn(inits, P) by {
          LB.InitRegsLookSetIn(nlook, P);
          forall t | t in inits.active ensures LB.LookSetIn(t.look_regs, P) { assert t == AI.init_thread(cap, look, quant); }
        }
        LB.FFindMatchLookSetIn(code, str, inits, ov, LAnc.Forward, cdn, P);
      }
      reveal WinRegsOkG();
    }
  }

  // (G3a) `NoNulledPlusNoCin` moved to lift-sim-core.

  /** Two banks of equal sizes agreeing at every index are equal. */
  lemma RegsEq(a: AReg.Regs, b: AReg.Regs)
    requires |a.a_cp| == |b.a_cp| && |a.a_clk| == |b.a_clk|
    requires forall k :: AI.get_idx(a.a_cp, k) == AI.get_idx(b.a_cp, k) && AI.get_idx(a.a_clk, k) == AI.get_idx(b.a_clk, k)
    ensures a == b
  {
    assert a.a_cp == b.a_cp by {
      forall i | 0 <= i < |a.a_cp| ensures a.a_cp[i] == b.a_cp[i] { assert AI.get_idx(a.a_cp, i) == AI.get_idx(b.a_cp, i); }
    }
    assert a.a_clk == b.a_clk by {
      forall i | 0 <= i < |a.a_clk| ensures a.a_clk[i] == b.a_clk[i] { assert AI.get_idx(a.a_clk, i) == AI.get_idx(b.a_clk, i); }
    }
  }

  /** A table row's body is the structural look body. */
  lemma RowBody(ast: R.regex, re: R.regex, crv: CP.FCompiled, l: int, la: R.lookaround, body: R.regex)
    requires crv == CP.FFullCompilation(ast) && re == R.lazy_prefix(ast)
    requires LTB.LookTablesOk(re, crv)
    requires 1 <= l <= R.max_lookaround(ast) && LTB.LookEntryOk(crv, l, la, body)
    ensures l >= 0 && (l as nat) in LTB.LookIds(re) && body == NI.LookBodyOfRE(re, l as nat)
  {
    var pre := R.Re_quant(R.NonNullable, 0, R.CountedQuant(0, None, false), R.Re_character(R.Dot));
    assert re == R.Re_con(pre, ast);
    M.LookEntryOnlyReal(ast, crv, l, la, body);
    assert LTB.LookIds(re) == LTB.LookIds(ast);
    NI.LookBodyOfTablesTie(re, crv, l as nat);
    var la0: R.lookaround :| LTB.LookEntryOk(crv, l, la0, NI.LookBodyOfRE(re, l as nat));
    M.LookEntryBody(crv, l, la, body, la0, NI.LookBodyOfRE(re, l as nat));
  }

  /** THE REGISTER TRANSPORT: the winner's gate-free facts + the reconstruction's
      sharp frame give the endpoint's `WinRegsOk` at the synthetic winner. */
  lemma WinRegsOkRecon(ast: R.regex, re: R.regex, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
                       best: AI.Thread, rp: AI.Thread, ncap: int, nlook: int, nquant: int)
    requires crv == CP.FFullCompilation(ast) && re == R.lazy_prefix(ast)
    requires T.TransWf(re) && RF.CinBodiesLookFreeRE(re) && NRC.CdnTopRE(re)
    requires PIV.CapUnique(re) && PIV.QuantUnique(re) && LTB.LookTablesOk(re, crv)
    requires WinRegsOkG(ast, re, crv, str, ov, best, ncap, nlook, nquant)
    requires FV.RegsFinalOk(best, |str|, FRD.StampQids(re))
    requires CM.ThreadRegsWf(rp, ncap, nlook, nquant)
    requires forall k :: AI.get_idx(rp.quant_regs.a_clk, k) >= -1
    requires var Q := FRD.StampQids(re);
             NRR.AgreeOutside((rp.capture_regs, rp.look_regs, rp.quant_regs),
                              (best.capture_regs, best.look_regs, best.quant_regs),
                              RF.CapsQ(re, Q), RF.LooksQ(re, Q), RF.QuantsQ(re, Q))
    ensures rp.look_regs == best.look_regs
    ensures M.WinRegsOk(ast, re, crv, str, ov, ClearQuantCps(rp, M.QIdsOuter(re)), ncap, nlook, nquant)
  {
    reveal WinRegsOkG();
    var Q := FRD.StampQids(re);
    var D := M.QIdsOuter(re);
    var rp0 := ClearQuantCps(rp, D);
    ClearQuantCpsFacts(rp, D);
    QInStampQ(re);
    RF.LooksQEmptyS(re, Q);
    CLP.QsOutsideS(re, Q);
    RegsEq(rp.look_regs, best.look_regs);
    assert rp0.look_regs == best.look_regs;

    // quant finality of rp0
    assert forall k :: AI.get_idx(rp0.quant_regs.a_cp, k) < 0 by {
      forall k ensures AI.get_idx(rp0.quant_regs.a_cp, k) < 0 {
        if k !in D {
          assert k !in RF.QuantsQ(re, Q) by {
            if k in RF.QuantsQ(re, Q) { assert k >= 0 && (k as nat) in PIV.QuantIdsOutsideLooks(re); assert k in D; }
          }
          assert AI.get_idx(rp0.quant_regs.a_cp, k) == AI.get_idx(best.quant_regs.a_cp, k);
          assert AI.get_idx(best.quant_regs.a_cp, k) < 0 by {   // (C6 probe) best is at init outside D
            assert AI.get_idx(best.quant_regs.a_cp, k) == AI.get_idx(AReg.init_regs(nquant).a_cp, k);
            RL.AInitLaws(nquant);
            assert AReg.get_cp(AReg.init_regs(nquant), k) == None;
          }
        }
      }
    }
    // the outside-look quant frame
    assert CM.RegsAgreeOutside(rp0.quant_regs, AReg.init_regs(nquant), D) by {
      forall k | k !in D
        ensures AI.get_idx(rp0.quant_regs.a_cp, k) == AI.get_idx(AReg.init_regs(nquant).a_cp, k)
                && AI.get_idx(rp0.quant_regs.a_clk, k) == AI.get_idx(AReg.init_regs(nquant).a_clk, k)
      {
        assert k !in RF.QuantsQ(re, Q) by {
          if k in RF.QuantsQ(re, Q) { assert k >= 0 && (k as nat) in PIV.QuantIdsOutsideLooks(re); assert k in D; }
        }
      }
    }
    // (c') the look bodies' captures
    assert forall l: int, la: R.lookaround, body: R.regex ::
             1 <= l <= R.max_lookaround(ast) && LTB.LookEntryOk(crv, l, la, body) ==>
               CM.RegsAgreeInside(rp0.capture_regs, AReg.init_regs(ncap), PIV.CaptureRegs(body)) by {
      forall l: int, la: R.lookaround, body: R.regex | 1 <= l <= R.max_lookaround(ast) && LTB.LookEntryOk(crv, l, la, body)
        ensures CM.RegsAgreeInside(rp0.capture_regs, AReg.init_regs(ncap), PIV.CaptureRegs(body))
      {
        RowBody(ast, re, crv, l, la, body);
        CLP.QsAvoidLookBodyS(re, Q, l as nat);
        assert CM.RegsAgreeInside(best.capture_regs, AReg.init_regs(ncap), PIV.CaptureRegs(body));
        forall k | k in PIV.CaptureRegs(body)
          ensures AI.get_idx(rp0.capture_regs.a_cp, k) == AI.get_idx(best.capture_regs.a_cp, k)
                  && AI.get_idx(rp0.capture_regs.a_clk, k) == AI.get_idx(best.capture_regs.a_clk, k)
        {
          assert k !in RF.CapsQ(re, Q) by { if k in RF.CapsQ(re, Q) { assert k in RF.CapsQ(re, Q) * PIV.CaptureRegs(body); } }
        }
      }
    }
    reveal M.WinRegsOk();
  }

  // =========================================================================
  // 5. The engine answer reads the synthetic winner (quant positions are
  //    never read by the look loop's bodies nor by `filter_reset`).
  // =========================================================================

  lemma QidsOfSub(r: R.regex, k: int)
    requires k in QCI.QidsOf(r)
    ensures k >= 0 ==> (k as nat) in PIV.QuantIds(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => if k in QCI.QidsOf(r1) { QidsOfSub(r1, k); } else { QidsOfSub(r2, k); }
    case Re_con(r1, r2) => if k in QCI.QidsOf(r1) { QidsOfSub(r1, k); } else { QidsOfSub(r2, k); }
    case Re_quant(_, qid, _, body) => if k != qid { QidsOfSub(body, k); }
    case Re_capture(_, r1) => QidsOfSub(r1, k);
  }

  /** The look ASTs name no outside-look quantifier. */
  lemma LookAstsAvoidOuter(ast: R.regex, re: R.regex, crv: CP.FCompiled)
    requires crv == CP.FFullCompilation(ast) && re == R.lazy_prefix(ast)
    requires LTB.LookTablesOk(re, crv) && PIV.QuantUnique(re)
    ensures QCI.LookAstsAvoid(crv, M.QIdsOuter(re))
  {
    var pre := R.Re_quant(R.NonNullable, 0, R.CountedQuant(0, None, false), R.Re_character(R.Dot));
    assert re == R.Re_con(pre, ast);
    assert LTB.LookIds(re) == LTB.LookIds(ast);
    var nlook0 := R.max_lookaround(ast) + 1;
    var nquant0 := R.max_quant(ast) + 1;
    var seed := CP.FCompiled(ast, CP.compile_to_bytecode(R.lazy_prefix(ast)), LCdn.compile_cdns(ast),
                             seq(nlook0, i => R.Lookahead), seq(nlook0, i => R.Re_empty),
                             seq(nlook0, i => []), seq(nlook0, i => []),
                             seq(nlook0, i => []), seq(nquant0, i => []));
    assert CP.FFullCompilation(ast) == CP.FCompileExtra(ast, seed);
    LTB.FCompileExtraLookFrame(ast, seed);
    PIV.QuantIdsLooksDisjoint(re);
    forall l | 0 <= l < |crv.f_look_ast| ensures QCI.QidsOf(crv.f_look_ast[l]) * M.QIdsOuter(re) == {} {
      if (l as nat) in LTB.LookIds(re) {
        NI.LookBodyOfTablesTie(re, crv, l as nat);
        var la0: R.lookaround :| LTB.LookEntryOk(crv, l, la0, NI.LookBodyOfRE(re, l as nat));
        var b := NI.LookBodyOfRE(re, l as nat);
        assert crv.f_look_ast[l] == b;
        CLP.LookBodyQuantsInL(re, l as nat);
        forall k | k in QCI.QidsOf(b) ensures k !in M.QIdsOuter(re) {
          QidsOfSub(b, k);
          if k in M.QIdsOuter(re) {
            assert k >= 0 && (k as nat) in PIV.QuantIdsOutsideLooks(re);
            assert (k as nat) in PIV.QuantIdsInLooks(re);
            assert (k as nat) in PIV.QuantIdsOutsideLooks(re) * PIV.QuantIdsInLooks(re);
          }
        }
      } else {
        assert LTB.AgreeAt(seed, crv, l as nat);
        assert crv.f_look_ast[l] == R.Re_empty;
      }
    }
  }

  /** THE ANSWER: the look loop + `filter_reset` read the synthetic winner the
      same as the reconstructed one. */
  lemma AnswerSynthetic(ast: R.regex, re: R.regex, crv: CP.FCompiled, str: string, ov: LOr.OracleView, rp: AI.Thread)
    requires crv == CP.FFullCompilation(ast) && re == R.lazy_prefix(ast)
    requires LTB.LookTablesOk(re, crv) && PIV.QuantUnique(re)
    ensures var rp0 := ClearQuantCps(rp, M.QIdsOuter(re));
            var r1 := AI.FLookLoop(crv, str, 1, R.max_lookaround(ast), rp.capture_regs, rp.look_regs, rp.quant_regs, ov);
            var r2 := AI.FLookLoop(crv, str, 1, R.max_lookaround(ast), rp0.capture_regs, rp0.look_regs, rp0.quant_regs, ov);
            AI.filter_reset(ast, r1.0, r1.1, r1.2, -1) == AI.filter_reset(ast, r2.0, r2.1, r2.2, -1)
            && r1.0 == r2.0 && r1.1 == r2.1 && r1.3 == r2.3 && r1.2.a_clk == r2.2.a_clk
  {
    var D := M.QIdsOuter(re);
    var rp0 := ClearQuantCps(rp, D);
    ClearQuantCpsFacts(rp, D);
    LookAstsAvoidOuter(ast, re, crv);
    QCI.FLookLoopAgree(crv, str, 1, R.max_lookaround(ast), rp.capture_regs, rp.look_regs, rp.quant_regs, rp0.quant_regs, ov, D);
    var r1 := AI.FLookLoop(crv, str, 1, R.max_lookaround(ast), rp.capture_regs, rp.look_regs, rp.quant_regs, ov);
    var r2 := AI.FLookLoop(crv, str, 1, R.max_lookaround(ast), rp0.capture_regs, rp0.look_regs, rp0.quant_regs, ov);
    QCI.FilterResetAgree(ast, r1.0, r1.1, r1.2, r2.2, -1, D);
  }

  // =========================================================================
  // 6. Gate-free twins of the remaining interim-gated steps.
  // =========================================================================

  /** `EL.TranslateFragmentPikeLkRec` under the look-bodies gate (its full gate
      serves only look bodies). */
  lemma TranslateFragmentPikeLkRecLk(re: R.regex)
    requires T.TransWf(re) && NR.NestedFragmentRE(re)
    ensures EL.PikeLkRegexRec(T.Translate(re))
    decreases re
  {
    match re
    case Re_alt(r1, r2) => TranslateFragmentPikeLkRecLk(r1); TranslateFragmentPikeLkRecLk(r2);
    case Re_con(r1, r2) => TranslateFragmentPikeLkRecLk(r1); TranslateFragmentPikeLkRecLk(r2);
    case Re_quant(nul, qid, q, r1) =>
      TranslateFragmentPikeLkRecLk(r1);
      // (G5a-1 step 3-L0) the head condition, as in EL.TranslateFragmentPikeLkRec
      reveal EL.CinHeadL();
      if q.min > 0 && q.max == None && q.greedy {
        if R.nullable(r1) == R.NonNullable { NUL.TransNonNullable(r1); }
        NUL.TransCINullable(r1);
      }
    case Re_capture(_, r1) => TranslateFragmentPikeLkRecLk(r1);
    case Re_lookaround(lid, la, r1) =>
      EL.TranslateFragmentPikeLkRec(r1);   // (gate C) the look arm is the body's own fragment
    case _ =>
  }

  /** (G5a-1 rows F, N) `TranslateFragmentPikeLkRecLk` on the top-level fragment. The head atom of a greedy
      CDN plus is the switch itself, so the lemma takes it: `EL.CdnHeadsAreOn()` supplies it after the flip. */
  lemma TranslateFragmentPikeLkRecLkCdn(re: R.regex)
    requires T.TransWf(re) && NR.NestedFragmentCdnRE(re)
    requires EL.CdnHeadsOn()
    ensures EL.PikeLkRegexRec(T.Translate(re))
    decreases re
  {
    match re
    case Re_alt(r1, r2) => TranslateFragmentPikeLkRecLkCdn(r1); TranslateFragmentPikeLkRecLkCdn(r2);
    case Re_con(r1, r2) => TranslateFragmentPikeLkRecLkCdn(r1); TranslateFragmentPikeLkRecLkCdn(r2);
    case Re_quant(nul, qid, q, r1) =>
      TranslateFragmentPikeLkRecLkCdn(r1);
      reveal EL.CinHeadL();   // the head condition holds by its second disjunct
    case Re_capture(_, r1) => TranslateFragmentPikeLkRecLkCdn(r1);
    case Re_lookaround(lid, la, r1) =>
      EL.TranslateFragmentPikeLkRec(r1);   // a look body is in the narrow fragment
    case _ =>
  }

  /** (G5a-1 row N) What `GateStaticsFromTablesCdn` takes of the plus table: the narrow table at every look
      node. From the widened table of the whole regex, since a look node of a regex in scope holds no CDN plus. */
  lemma LookNodesPlusOkFromS(re: R.regex, bc: seq<RB.code>)
    requires PIV.QuantUnique(re) && NRR.PlusTableOkS(re, bc) && NRC.CdnTopRE(re)
    ensures LookNodesPlusOk(re, bc)
    decreases re
  {
    NRR.PlusTableOkSChildren(re, bc);
    NRC.CdnTopChild(re);
    match re
    case Re_alt(r1, r2) => LookNodesPlusOkFromS(r1, bc); LookNodesPlusOkFromS(r2, bc);
    case Re_con(r1, r2) => LookNodesPlusOkFromS(r1, bc); LookNodesPlusOkFromS(r2, bc);
    case Re_quant(_, _, _, r1) => LookNodesPlusOkFromS(r1, bc);
    case Re_capture(_, r1) => LookNodesPlusOkFromS(r1, bc);
    case Re_lookaround(_, _, r1) =>
      assert NRC.NoCdnPlusRE(re);          // CdnTopRE's look arm: the body holds no CDN plus
      NRR.PlusTableOkSNarrow(re, bc);
    case _ =>
  }

  /** `LSC.MainExtractionL5` under the look-bodies gate. */
  lemma MainExtractionL5Lk(raw: R.raw_regex, str: string,
                           t: LT.Tree, thread: AI.Thread, leaf: LT.Leaf)
    requires NR.NestedFragmentCdnRaw(raw)
    requires T.Latin1Wf(raw)
    requires EL.BoolTreeLk(LES.TheRer(raw), [LS.Areg(LES.SpecRegex(raw))], LC.InitInput(str), BS.CannotExit, t)
    requires LS.IsTree(LES.TheRer(raw), [LS.Areg(LES.SpecRegex(raw))], LC.InitInput(str), LG.Empty, WP.Forward, t)
    requires CM.ThreadRegsWf(thread, 2 * R.max_group(R.annotate(raw)) + 2,
                             R.max_lookaround(R.annotate(raw)) + 1,
                             R.max_quant(R.annotate(raw)) + 1)
    requires M.QuantClkFinal(thread)   // (G3a) clocks only
    requires var re := R.lazy_prefix(R.annotate(raw));
             leaf.1 == PIV.NormGm(PIV.GmOfLive(re, thread.capture_regs, thread.look_regs, thread.quant_regs))
    requires LT.FirstLeaf(t, LC.InitInput(str)) == Some(leaf)
    requires AI.FFullMatch(raw, str)
          == Some(AI.filter_reset(R.annotate(raw), thread.capture_regs, thread.look_regs,
                                  thread.quant_regs, -1))
    ensures LES.MatcherSpec(raw, str, LES.Normalize(AI.FFullMatch(raw, str)))
  {
    hide T.TransWf, NR.PlusFragmentRE, NR.LookBehindFragmentRE, NR.CaptureFreeRE, NR.LookFreeRE, NR.LookBehindFragmentRaw, NR.CaptureFreeRaw, NR.LookFreeRaw, EL.PikeLkRegex, EL.LkGateOk, SD.GroupFreeL;
    var ast := R.annotate(raw);
    var re := R.lazy_prefix(ast);
    var rer := LES.TheRer(raw);
    var inp := LC.InitInput(str);
    T.AnnotateWf(raw);
    NR.SpecRegexNestedFragmentCdn(raw);
    assert LES.SpecRegex(raw) == T.Translate(re);

    // closedness of the leaf gm
    assert LT.TreeRes(t, LG.Empty, inp, WP.Forward) == Some(leaf);
    assert M.OpenOf(LG.Empty) <= M.PendingCloses([LS.Areg(T.Translate(re))]);
    EL.CdnHeadsAreOn();
    TranslateFragmentPikeLkRecLkCdn(re);
    assert EL.PikeLkActionsRec([LS.Areg(T.Translate(re))]) by {
      assert [LS.Areg(T.Translate(re))] == [LS.Areg(T.Translate(re))] + [];
      assert EL.PikeLkActionsRec([]);
      EL.PikeLkActionsRecConsIff(LS.Areg(T.Translate(re)), []);
    }
    assert M.LkClosedInGm(LG.Empty, [LS.Areg(T.Translate(re))]);
    M.SpecRegexOuterLkDisjoint(raw);
    assert T.Translate(re) == LES.SpecRegex(raw);
    assert M.OuterLkDisjoint([LS.Areg(T.Translate(re))]);
    assert M.NoDupRegsActs([LS.Areg(T.Translate(re))]) by { assert M.NoDupSeq(L.DefGroups(T.Translate(re))); }
    assert TRM.GmInBounds(LG.Empty, |inp.pref| + |inp.next|);
    assert M.NestDepthActsLe([LS.Areg(T.Translate(re))], M.NestDepthL(T.Translate(re)));
    CG.FirstLeafClosedRecAny(rer, [LS.Areg(T.Translate(re))], inp, BS.CannotExit, t, LG.Empty, leaf,
                            M.NestDepthL(T.Translate(re)));
    assert M.ClosedGm(leaf.1);
    M.MainExtractionFromClosedCdn(raw, str, t, thread, leaf);
  }
  /** (G3a) `MainExtractionL5Lk`'s premises as one opaque fact: at the end of `MainTheoremL5Cin` the call
      then matches a single ground atom (the eight separate premises took minutes in that context). */
  opaque ghost predicate ExtractionPre(raw: R.raw_regex, str: string, t: LT.Tree, thread: AI.Thread, leaf: LT.Leaf) {
    NR.NestedFragmentCdnRaw(raw)
    && T.Latin1Wf(raw)
    && EL.BoolTreeLk(LES.TheRer(raw), [LS.Areg(LES.SpecRegex(raw))], LC.InitInput(str), BS.CannotExit, t)
    && LS.IsTree(LES.TheRer(raw), [LS.Areg(LES.SpecRegex(raw))], LC.InitInput(str), LG.Empty, WP.Forward, t)
    && CM.ThreadRegsWf(thread, 2 * R.max_group(R.annotate(raw)) + 2,
                       R.max_lookaround(R.annotate(raw)) + 1,
                       R.max_quant(R.annotate(raw)) + 1)
    && M.QuantClkFinal(thread)
    && (var re := R.lazy_prefix(R.annotate(raw));
        leaf.1 == PIV.NormGm(PIV.GmOfLive(re, thread.capture_regs, thread.look_regs, thread.quant_regs)))
    && LT.FirstLeaf(t, LC.InitInput(str)) == Some(leaf)
    && AI.FFullMatch(raw, str)
       == Some(AI.filter_reset(R.annotate(raw), thread.capture_regs, thread.look_regs,
                               thread.quant_regs, -1))
  }

  /** (G5a-1) Package the extraction premises in a context of their own: revealing `ExtractionPre` inside
      `MainTheoremL5Cin` ran 772M once steps 2-3 grew that context. */
  lemma ExtractionPreIntro(raw: R.raw_regex, str: string, t: LT.Tree, thread: AI.Thread, leaf: LT.Leaf)
    requires NR.NestedFragmentCdnRaw(raw)
    requires T.Latin1Wf(raw)
    requires EL.BoolTreeLk(LES.TheRer(raw), [LS.Areg(LES.SpecRegex(raw))], LC.InitInput(str), BS.CannotExit, t)
    requires LS.IsTree(LES.TheRer(raw), [LS.Areg(LES.SpecRegex(raw))], LC.InitInput(str), LG.Empty, WP.Forward, t)
    requires CM.ThreadRegsWf(thread, 2 * R.max_group(R.annotate(raw)) + 2,
                             R.max_lookaround(R.annotate(raw)) + 1,
                             R.max_quant(R.annotate(raw)) + 1)
    requires M.QuantClkFinal(thread)
    requires var re := R.lazy_prefix(R.annotate(raw));
             leaf.1 == PIV.NormGm(PIV.GmOfLive(re, thread.capture_regs, thread.look_regs, thread.quant_regs))
    requires LT.FirstLeaf(t, LC.InitInput(str)) == Some(leaf)
    requires AI.FFullMatch(raw, str)
             == Some(AI.filter_reset(R.annotate(raw), thread.capture_regs, thread.look_regs,
                                     thread.quant_regs, -1))
    ensures ExtractionPre(raw, str, t, thread, leaf)
  {
    reveal ExtractionPre();
  }

  lemma MainExtractionL5LkPre(raw: R.raw_regex, str: string, t: LT.Tree, thread: AI.Thread, leaf: LT.Leaf)
    requires T.Latin1Wf(raw)   // the `ensures` reads `MatcherSpec`, which needs it visible
    requires ExtractionPre(raw, str, t, thread, leaf)
    ensures LES.MatcherSpec(raw, str, LES.Normalize(AI.FFullMatch(raw, str)))
  {
    reveal ExtractionPre();
    MainExtractionL5Lk(raw, str, t, thread, leaf);
  }



  /** Register sizes cover every id (the look-aware `CoversLookFree`). */
  lemma CoversAll(re: R.regex, rg: NRC.Regs3, ncap: int, nlook: int, nquant: int)
    requires ncap == 2 * R.max_group(re) + 2 && nlook == R.max_lookaround(re) + 1 && nquant == R.max_quant(re) + 1
    requires |rg.0.a_cp| == ncap && |rg.1.a_cp| == nlook && |rg.2.a_cp| == nquant
    ensures NRR.Covers(re, rg)
  {
    NI.CapIdsLEMaxGroup(re);
    NI.QuantIdsLEMaxQuant(re);
    LTB.LookIdsLeMax(re);
    NRRLookIdsEq(re);
  }


  // =========================================================================
  // 7. THE ASSEMBLY.
  // =========================================================================

  /** Machine A's winner, reconstructed: the F-b readout, the sharp frame and
      the endpoint's register facts at the synthetic winner. */
  lemma ReadoutAtWinner(qm: AR.QMap, ast: R.regex, re: R.regex, crv: CP.FCompiled, code: RB.code, endl: nat,
                        str: string, ov: LOr.OracleView, inits: AI.VmState,
                        capture: AReg.Regs, look: AReg.Regs, quant: AReg.Regs,
                        ncap: int, nlook: int, nquant: int, result: Option<AI.Thread>)
    returns (rp: AI.Thread)
    requires crv == CP.FFullCompilation(ast) && re == R.lazy_prefix(ast) && code == CP.compile_to_bytecode(re)
    requires crv.f_main_bc == code
    requires T.TransWf(re) && NR.NestedFragmentCdnRE(re) && M.LookBodiesPlusGateRE(re) && RF.CinBodiesLookFreeRE(re)
    requires PIV.CapUnique(re) && PIV.QuantUnique(re) && LTB.LookUnique(re) && LTB.LookTablesOk(re, crv)
    requires NRC.CdnTopRE(ast) && NRC.CdnTopRE(re) && AR.QmapOk(re, qm) && qm.ov == ov
    requires NR.NfaRepRE(re, code, 0, endl) && |code| == endl + 1 && NR.GetPcRE(code, endl) == Some(RB.Accept)
    requires ncap == 2 * R.max_group(re) + 2 && nlook == R.max_lookaround(re) + 1 && nquant == R.max_quant(re) + 1
    requires capture == AReg.init_regs(ncap) && look == AReg.init_regs(nlook) && quant == AReg.init_regs(nquant)
    requires inits == AI.FInitState(code, 0, capture, look, quant, 0, AI.cp_context(0, str, LAnc.Forward))
    requires result == AI.FFindMatch(code, str, inits, ov, LAnc.Forward, crv.f_main_cdns).0
    requires result.Some? && PSM.BestLiveRE(re, result.value)
    requires PSM.StampPathOk(qm, str, result.value.quant_regs.a_cp)   // (G5a-1 row E) the carried fact
    ensures AI.FFindMatch(code, str, inits, ov, LAnc.Forward, crv.f_main_cdns).1 == ov
    ensures var rpp := AI.FReconstructPlus(result.value, ast, crv.f_plus_bc, str, ov, LAnc.Forward);
            rp == rpp.0 && rpp.1 == ov
    ensures rp.pc == result.value.pc && rp.exit_allowed == result.value.exit_allowed
    ensures PIV.GmOfLive(re, rp.capture_regs, rp.look_regs, rp.quant_regs)
            == PIV.GmOfLiveR(re, qm, str, result.value.capture_regs, result.value.look_regs, result.value.quant_regs)
    ensures CM.ThreadRegsWf(rp, ncap, nlook, nquant)
    ensures M.WinRegsOk(ast, re, crv, str, ov, ClearQuantCps(rp, M.QIdsOuter(re)), ncap, nlook, nquant)
    ensures ClkFrame(re, FRD.StampQids(re), ClearQuantCps(rp, M.QIdsOuter(re)), result.value)
  {
    hide NUL.NonNullableL, NUL.CINullableL, NUL.NoNulledPlusL, AR.NfaRepCinL;
    var best := result.value;
    var ctx := AI.cp_context(0, str, LAnc.Forward);
    var rg: NRC.Regs3 := (best.capture_regs, best.look_regs, best.quant_regs);
    var Q := FRD.StampQids(re);
    // VM facts of the winning thread
    CM.FInitStateRegsWf(code, 0, ncap, nlook, nquant, 0, ctx);
    M.FFindMatchRegsWf(code, str, inits, ov, LAnc.Forward, crv.f_main_cdns, ncap, nlook, nquant);
    assert CM.ThreadRegsWf(best, ncap, nlook, nquant);
    FRD.TrueStampsInStamp(re, code, endl);
    FV.RegsFinalOkInit(ncap, nlook, nquant, |str|, Q);
    assert FV.VmRegsFinalOk(inits, |str|, Q) by {
      forall t0 | t0 in inits.active ensures FV.RegsFinalOk(t0, |str|, Q) {
        assert t0 == AI.init_thread(capture, look, quant);
      }
    }
    FV.FFindMatchRegsFinal(code, str, inits, ov, LAnc.Forward, crv.f_main_cdns, Q);
    assert FV.RegsFinalOk(best, |str|, Q);
    assert {:split_here} true;
    // the registers of groups outside the regex stay unset
    M.CaptureBytecodeClassifiedCdnOuter(re);
    var Sout := PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(re));
    assert CM.VmCapturesAgree(inits, capture, Sout) by {
      forall t0 | t0 in inits.active ensures CM.RegsAgreeOutside(t0.capture_regs, capture, Sout) {
        assert t0 == AI.init_thread(capture, look, quant);
      }
    }
    CM.FFindMatchCapWriteFrame(code, str, inits, ov, LAnc.Forward, crv.f_main_cdns, capture, Sout);
    OnlyCapIdsFromFrameOuter(re, best.capture_regs, ncap);
    assert NRO.OnlyCapIdsSet(re, rg);
    assert NRR.WfRegs(rg);
    CoversAll(re, rg, ncap, nlook, nquant);
    assert {:split_here} true;
    // THE FINAL READOUT (rung F-b) + its frame
    FRD.FinalReadoutS(qm, ast, str, best, ncap, nlook, nquant);
    CLP.FinalReadoutFrameS(qm, ast, str, best);
    M.NoWriteOracleBodyCodeCdn(re);
    CM.FFindMatchOvStable(code, str, inits, ov, LAnc.Forward, crv.f_main_cdns);
    rp := AI.FReconstructPlus(best, ast, crv.f_plus_bc, str, ov, LAnc.Forward).0;
    assert {:split_here} true;
    // the synthetic winner's endpoint facts
    WinRegsOkGFromRun(ast, re, crv, code, str, ov, crv.f_main_cdns, inits, capture, look, quant,
                      ncap, nlook, nquant, endl, result);
    WinRegsOkRecon(ast, re, crv, str, ov, best, rp, ncap, nlook, nquant);
    var rp0 := ClearQuantCps(rp, M.QIdsOuter(re));
    ClearQuantCpsFacts(rp, M.QIdsOuter(re));
    assert ClkFrame(re, Q, rp0, best);
  }

  /** The endpoint at the synthetic winner (the thread-level producers + the
      owner forall + `MainTheoremL4DeepConclude`). */
  lemma EndpointAtRp0(rer: LW.RegExpRecord, qm: AR.QMap, crv: CP.FCompiled, str: string, ast: R.regex, re: R.regex,
                      code: RB.code, endl: nat, ov: LOr.OracleView, th: AI.Thread, leaf: LT.Leaf,
                      t: LT.Tree, inp: LC.Input, S: set<LG.GroupId>, ncap: int, nlook: int, nquant: int)
    requires crv == CP.FFullCompilation(ast) && re == R.lazy_prefix(ast)
    requires T.TransWf(re) && NR.NestedFragmentCdnRE(re)
    requires M.LookBodiesPlusGateRE(re)   // (G3a) the weak gate
    requires PIV.CapUnique(re) && PIV.QuantUnique(re) && LTB.LookUnique(re)
    requires LTB.LookTablesOk(re, crv) && LTB.LidsWellNested(re)
    requires |crv.f_look_types| == |crv.f_look_ast|
    requires forall x: nat :: x in LTB.LookIds(re) ==> 1 <= x <= R.max_lookaround(ast)
    requires forall x: nat :: x in LTB.LookIds(re) ==> (x as int) in qm.looks
    requires ncap >= 0 && nquant >= 0
    requires nlook == R.max_lookaround(ast) + 1
    requires R.max_lookaround(re) == R.max_lookaround(ast)
    requires qm.ov == ov && !rer.multiline && !rer.ignoreCase && |ov| == |str| + 1
    requires forall l: int :: l in qm.looks ==> l >= 0
    requires M.OracleSufAllO(rer, qm, str)
    requires GateStaticsOkNested(qm, re, crv, ncap, nlook, nquant)
    requires S == PIV.CapIdsInLooks(re)
    requires M.OrderedGm(leaf.1)
    requires LT.FirstLeaf(t, inp) == Some(leaf)
    requires BestTieLkNestedTop(rer, re, crv, str, ov, S, Some(leaf), Some(th), ncap, nlook, nquant)
    requires M.WinRegsOk(ast, re, crv, str, ov, th, ncap, nlook, nquant)
    ensures var res := AI.FLookLoop(crv, str, 1, R.max_lookaround(ast), th.capture_regs, th.look_regs, th.quant_regs, ov);
            var synthetic := AI.Thread(th.pc, res.0, res.1, res.2, th.exit_allowed);
            leaf.1 == PIV.NormGm(PIV.GmOfLive(re, res.0, res.1, res.2))
            && CM.ThreadRegsWf(synthetic, ncap, nlook, nquant) && M.QuantClkFinal(synthetic)
  {
    hide NUL.NonNullableL, NUL.CINullableL, NUL.NoNulledPlusL, AR.NfaRepCinL;
    M.EndpointValueOkRegsCdn(ast, re, crv, str, ov, th, ncap, nlook, nquant);
    M.EndpointQuantValueOkRegsCdn(ast, re, crv, str, ov, th, ncap, nlook, nquant);
    M.EndpointChildLinkOkRegsCdn(ast, re, crv, str, ov, th, ncap, nlook, nquant);
    M.EndpointLookInvRegsCdn(ast, re, crv, str, ov, th, ncap, nlook, nquant);
    M.EndpointTopLookFrameRegsCdn(ast, re, crv, str, ov, th, ncap, nlook, nquant);
    var resO := AI.FLookLoop(crv, str, 1, R.max_lookaround(ast), th.capture_regs, th.look_regs, th.quant_regs, ov);
    ProduceOwnerForallResCdn(qm, crv, str, ast, re, ov, resO.0, resO.1, resO.2, S, ncap, nlook, nquant);
    var res := AI.FLookLoop(crv, str, 1, R.max_lookaround(ast), th.capture_regs, th.look_regs, th.quant_regs, ov);
    var synthetic := AI.Thread(th.pc, res.0, res.1, res.2, th.exit_allowed);
    assert CM.ThreadRegsWf(synthetic, ncap, nlook, nquant) && M.QuantClkFinal(synthetic);
    MainTheoremL4DeepConcludeCdn(rer, qm, crv, str, ast, re, code, endl, ov, th, leaf,
                              t, inp, S, ncap, nlook, nquant);
  }

  /** The two look tables of a full compilation have the same size. */
  lemma FFullCompilationLookLens(ast: R.regex)
    ensures |CP.FFullCompilation(ast).f_look_types| == |CP.FFullCompilation(ast).f_look_ast|
  {
    hide R.max_quant, R.lazy_prefix;   // recursive + in every term here (same loop as `FFullCompilationFactsNested`)
    var maxlook0 := R.max_lookaround(ast);
    var crv := CP.FFullCompilation(ast);
    var seed := CP.FCompiled(ast, CP.compile_to_bytecode(R.lazy_prefix(ast)), LCdn.compile_cdns(ast),
                             seq(maxlook0 + 1, i => R.Lookahead), seq(maxlook0 + 1, i => R.Re_empty),
                             seq(maxlook0 + 1, i => []), seq(maxlook0 + 1, i => []),
                             seq(maxlook0 + 1, i => []), seq(R.max_quant(ast) + 1, i => []));
    assert crv == CP.FCompileExtra(ast, seed);
    LTB.FCompileExtraLookFrame(ast, seed);
    assert LTB.SameLookSizes(seed, crv);
    assert |seed.f_look_types| == |seed.f_look_ast|;
  }

  /** THE THEOREM, with no interim gate: greedy
      CI-nullable pluses outside lookarounds, with look-free bodies, and no
      nulled plus inside a look body. */
  lemma MainTheoremL5Cin(raw: R.raw_regex, str: string)
    requires NR.NestedFragmentCdnRaw(raw)
    requires NRC.CdnTopRE(R.lazy_prefix(R.annotate(raw)))   // (G5a-1) every CDN plus at top level, body look-free
    requires T.Latin1Wf(raw)
    requires M.LookBodiesPlusGateRE(R.lazy_prefix(R.annotate(raw)))   // (G3a) lookbehind bodies stamp-free, lookahead bodies CIN
    requires RF.CinBodiesLookFreeRE(R.lazy_prefix(R.annotate(raw)))
    ensures LES.MatcherSpec(raw, str, LES.Normalize(AI.FFullMatch(raw, str)))
  {
    hide NUL.NonNullableL, NUL.CINullableL, NUL.NoNulledPlusL, AR.NfaRepCinL;
    // the two recursive gates are facts here, never unfolded (in context they blew batch 6 past 19 GB)
    hide M.LookBodiesPlusGateRE, RF.CinBodiesLookFreeRE;
    var ast := R.annotate(raw);
    var re := R.lazy_prefix(ast);
    var rer := LES.TheRer(raw);
    var inp := LC.InitInput(str);
    var ngroups := LES.NGroups(raw);
    assert !rer.multiline && !rer.ignoreCase;

    // ---- static packages -------------------------------------------------
    T.AnnotateWf(raw);
    NR.SpecRegexNestedFragmentCdn(raw);
    LTB.SpecRegexLookUnique(raw);
    LTB.SpecRegexLidsWellNested(raw);
    PIV.SpecRegexCapUnique(raw);
    PIV.SpecRegexQuantUnique(raw);
    var qm := AR.QMap(M.QmOfRE(re), OE.LmOf(re), AI.FBuildOracle(CP.FFullCompilation(ast), str), M.BodiesOfRE(re));
    M.QmOfREEntries(re);
    M.BodiesOfREEntries(re);
    M.QmapOkFromEntries(re, qm);
    OE.LmapOkOfLmOf(re, qm);
    assert AR.QmapOk(re, qm) && AR.LmapOk(re, qm);
    assert {:split_here} true;
    // ---- the nested oracle entry -------------------------------------------
    assert LL.OracleOkSuffix(rer, qm, inp) by {
      var crv0 := CP.FFullCompilation(ast);
      var pre := R.Re_quant(R.NonNullable, 0, R.CountedQuant(0, None, false), R.Re_character(R.Dot));
      assert re == R.Re_con(pre, ast);
      LTB.FFullCompilationLookOk(ast);
      assert LTB.LookTablesOk(pre, crv0);
      assert LTB.LookTablesOk(re, crv0);
      assert LTB.LookIds(pre) == {};
      assert LTB.LookIds(re) == LTB.LookIds(ast);
      assert NR.NestedFragmentCdnRE(ast);
      OracleOkRowsL5Cdn(rer, ast, crv0, str, re);
    }

    NR.CompileToBytecodeRepCdn(re);
    var code := CP.compile_to_bytecode(re);
    var next := CP.compile(re, 0, CP.Progress).1;
    var endl: nat := next as nat;
    assert NR.NfaRepRE(re, code, 0, endl)
           && NR.GetPcRE(code, endl) == Some(RB.Accept) && |code| == endl + 1;
    CompileStutterTameRECdn(re);
    assert PSM.StaticCoreCdnRE(qm, re, code, endl);

    var maxcap := R.max_group(ast);
    var maxquant := R.max_quant(ast);
    assert R.max_group(re) == maxcap;
    assert R.max_quant(re) == R.imax(0, maxquant) == maxquant;
    var ncap := 2 * maxcap + 2;
    var nlook := R.max_lookaround(ast) + 1;
    var nquant := maxquant + 1;
    assert PSM.SizesOkRE(re, ncap, nlook, nquant);
    assert ngroups == (maxcap + 1) as nat;
    var maxlook := R.max_lookaround(ast);
    assert R.max_lookaround(re) == maxlook by {
      var pre := R.Re_quant(R.NonNullable, 0, R.CountedQuant(0, None, false), R.Re_character(R.Dot));
      assert re == R.Re_con(pre, ast);
    }

    assert {:split_here} true;
    // ---- the spec tree -----------------------------------------------------
    LFU.ComputeTrIsTree(rer, [LS.Areg(T.Translate(re))], inp, LG.Empty, WP.Forward);
    var t := LFU.ComputeTr(rer, [LS.Areg(T.Translate(re))], inp, LG.Empty, WP.Forward);
    assert LS.IsTree(rer, [LS.Areg(T.Translate(re))], inp, LG.Empty, WP.Forward, t);
    assert LES.SpecRegex(raw) == T.Translate(re);
    EL.CdnHeadsAreOn();   // (G5a-1 rows F, N) the switch is on
    TranslateFragmentPikeLkRecLkCdn(re);
    EL.BooleanCorrectLkRec(rer, T.Translate(re), inp, t);
    assert forall i :: 0 <= i < |[LS.Areg(T.Translate(re))]| ==> ![LS.Areg(T.Translate(re))][i].Acheck?;
    M.BoolTreeLbIrrel(rer, [LS.Areg(T.Translate(re))], inp, BS.CanExit, BS.CannotExit, t);
    assert EL.BoolTreeLk(rer, [LS.Areg(T.Translate(re))], inp, BS.CannotExit, t);

    assert {:split_here} true;
    // ---- the CHECKED tree (machine A's, shared with B) ----------------------
    WkE.WalkOkEntryCdn(re);
    assert EL.PikeLkActionsRec([LS.Areg(T.Translate(re))]) by {
      assert [LS.Areg(T.Translate(re))] == [LS.Areg(T.Translate(re))] + [];
      assert EL.PikeLkActionsRec([]);
      EL.PikeLkActionsRecConsIff(LS.Areg(T.Translate(re)), []);
    }
    var S := PIV.CapIdsInLooks(re);
    M.LkBodyGroupsEqCapIdsInLooks(re);
    assert S == LL.LkBodyGroups(T.Translate(re));
    assert WO.WalkOk([LS.Areg(T.Translate(re))], code, 0, ATR.EaOf(BS.CannotExit));
    AR.CompileToBytecodeActionsRepCdn(rer, qm, re);
    assert AR.ActionsRepL(rer, qm, [LS.Areg(T.Translate(re))], code, 0);
    assert LL.LkActsInS([LS.Areg(T.Translate(re))], S) by {
      LL.LkBodyGroupsConfines(T.Translate(re), S);
      LL.LkActsInSCons(LS.Areg(T.Translate(re)), [], S);
    }
    LL.ComputeTrLkConfinedK(rer, [LS.Areg(T.Translate(re))], inp, LG.Empty, WP.Forward, S);
    assert NB.EncOk([LS.Areg(T.Translate(re))], inp, BS.CannotExit) by { NB.EncOkNoChecks([LS.Areg(T.Translate(re))], inp, BS.CannotExit); }
    var tstar := ATR.ActionsTreeRepRENested(rer, qm, [LS.Areg(T.Translate(re))], code, 0, inp, BS.CannotExit, t, S);
    assert TREP.TreeRepRE(qm, tstar, code, 0, inp, false);
    assert TT.TreeThreadRE(rer, qm, code, inp, tstar, 0, false);
    NB.RAFirstLeafOutside(tstar, t, inp, S);

    assert {:split_here} true;
    // ---- the engine pipeline ---------------------------------------------
    var crv := CP.FFullCompilation(ast);
    M.FFullCompilationFactsNested(ast);
    assert crv.f_main_ast == ast && crv.f_main_bc == code && crv.f_main_cdns == LCdn.compile_cdns(ast);
    FFullCompilationLookLens(ast);
    assert |crv.f_look_types| == |crv.f_look_ast|;
    assert {:split_here} true;
    var ov := AI.FBuildOracle(crv, str);
    OB.FBuildOracleViewLen(crv, str);
    assert qm.ov == ov;
    var capture := AReg.init_regs(ncap);
    var look := AReg.init_regs(nlook);
    var quant := AReg.init_regs(nquant);
    var ctx := AI.cp_context(0, str, LAnc.Forward);
    var inits := AI.FInitState(code, 0, capture, look, quant, 0, ctx);
    var fmres := AI.FFindMatch(code, str, inits, ov, LAnc.Forward, crv.f_main_cdns);
    var result := fmres.0;

    assert {:split_here} true;
    // ---- gate statics + look tables ---------------------------------------
    LTB.FFullCompilationLookOk(ast);
    assert LTB.LookTablesOk(re, crv) by {
      var pre := R.Re_quant(R.NonNullable, 0, R.CountedQuant(0, None, false), R.Re_character(R.Dot));
      assert re == R.Re_con(pre, ast);
      assert LTB.LookTablesOk(pre, crv);
      assert LTB.LookTablesOk(ast, crv);
    }
    OE.LmOfDom(re);
    LTB.LookIdsLeMax(re);
    assert forall l: int :: l in qm.looks ==>
                              l >= 0 && (l as nat) in LTB.LookIds(re) && l < nlook;
    assert forall x: nat :: x in LTB.LookIds(re) ==> (x as int) in qm.looks by {
      forall x: nat | x in LTB.LookIds(re) ensures (x as int) in qm.looks { }
    }
    assert GateStaticsOkNested(qm, re, crv, ncap, nlook, nquant) by {
      // (G3a) the plus-row premises at the top regex, scoped: as context facts they stalled the final call
      // (G5a-1 row N) the top may hold a CDN plus: the widened table, and the narrow one at each look node
      assert LookNodesPlusOk(re, crv.f_plus_bc) by {
        FRD.PlusTableOkFullS(ast);
        LookNodesPlusOkFromS(re, crv.f_plus_bc);
      }
      assert forall l: nat :: l in LTB.LookIds(re) ==> l < nlook;
      GateStaticsFromTablesCdn(qm, re, crv, ncap, nlook, nquant);
    }

    assert {:split_here} true;
    // ---- the two machines on the same checked tree --------------------------
    PSM.InitialPikeInvFullREAtCpCdn(rer, qm, re, code, endl, ngroups, str, 0, tstar,
                                       inits, ncap, nlook, nquant);
    assert ctx.nextchar == AI.get_char(str, 0);
    assert PIV.ContextOkRE(str, inits.cp, inits.context);
    assert M.OracleSufAllO(rer, qm, str) by {
      reveal M.OracleSufAllO();
      forall cp: nat | cp <= |str| ensures LL.OracleOkSuffix(rer, qm, PIV.InpOfCp(str, cp)) {
        OracleOkSuffixAtCp(rer, qm, str, cp);
      }
    }
    SufAllToColsOk(rer, qm, str);
    // machine B on the engine-shaped walk, agreeing with the spec leaf outside G
    var G: set<LG.GroupId> := PIV.CapIdsOutsideLooks(re);
    TranslateCinOkCdn(re, G);
    PIV.CapIdsLooksDisjoint(re);
    assert G * S == {};
    // (G5a-1 row N) the run premise of the guard, for real (cdn-sound through `GR.GuardsOkRunTop`).
    // Scoped: `OracleOkAt` is a transparent quantifier; at the top level it blew this batch past 10 GB.
    assert {:split_here} true;
    assert PSM.GuardsOkRun(qm, code, crv.f_main_cdns, ov, str) by {
      assert forall cp: nat :: cp <= |str| ==> LL.OracleOkAt(rer, qm, PIV.InpOfCp(str, cp)) by {
        forall cp: nat | cp <= |str| ensures LL.OracleOkAt(rer, qm, PIV.InpOfCp(str, cp)) {
          OracleOkSuffixAtCp(rer, qm, str, cp);   // the source of the suffix fact (no longer in scope here)
          assert LL.OracleOkSuffix(rer, qm, PIV.InpOfCp(str, cp));
        }
      }
      GR.GuardsOkRunTop(rer, qm, ast, re, code, endl, str, ov);
    }
    assert {:split_here} true;
    var bleaf := L3aCompositeCloseRecGCdn(rer, qm, re, code, endl, ngroups, crv, str, ov, S, tstar, t, inp,
                                       inits, crv.f_main_cdns, result, ncap, nlook, nquant, G);
    // machine A: the VM's best is the checked tree's first leaf
    assert {:split_here} true;
    var pts0 := PT.PikeTreeInitialState(tstar, inp);
    var bestT := PSM.FindMatchSimRECdn(rer, qm, re, code, endl, ngroups, str, pts0, inits,
                                          ov, LAnc.Forward, crv.f_main_cdns, ncap, nlook, nquant);
    M.TrcREToLinden(pts0, PT.PTS_final(bestT));
    TREP.TreeRepPikeSubtree(qm, tstar, code, 0, inp, false);
    PT.InitPiketreeInv(tstar, inp);
    CR.PikeTreeTrcCorrect(pts0, PT.PTS_final(bestT), LT.FirstLeaf(tstar, inp));
    assert bestT == LT.FirstLeaf(tstar, inp);
    assert PIV.BestMatchRE(re, qm, str, bestT, result);

    assert {:split_here} true;
    // ---- stage the engine answer ------------------------------------------
    var bc := AI.FBuildCapture(crv, str, ov);
    assert AI.FMatcher(crv, str) == bc.0;
    assert AI.FFullMatch(raw, str) == bc.0;
    var fmp := AI.FFindMatchPlus(crv.f_main_bc, crv.f_main_ast, crv.f_plus_bc, str, ov,
                                 LAnc.Forward, 0, capture, look, quant, 0, crv.f_main_cdns);
    assert AI.FInitState(crv.f_main_bc, 0, capture, look, quant, 0,
                         AI.cp_context(0, str, LAnc.Forward)) == inits;
    assert fmp.0 == (match result
                     case None => None
                     case Some(thread) =>
                       Some(AI.FReconstructPlus(thread, ast, crv.f_plus_bc, str, fmres.1, LAnc.Forward).0));
    assert R.max_group(crv.f_main_ast) == maxcap && R.max_quant(crv.f_main_ast) == maxquant;
    assert ncap == 2 * R.max_group(crv.f_main_ast) + 2;
    assert nquant == R.max_quant(crv.f_main_ast) + 1;

    if result.None? {
      assert fmp.0 == None;
      M.FBuildCaptureUnfoldL3a(crv, str, ov, ncap, nlook, nquant, capture, look, quant, fmp);
      assert bc.0 == None;
      assert LT.FirstLeaf(t, inp) == None;
      assert LES.Normalize(AI.FFullMatch(raw, str)) == None;
      assert LES.MatcherSpec(raw, str, None);
    } else {
      assert {:split_here} true;
      var best := result.value;
      assert PSM.BestLiveRE(re, best);
      NRC.CdnTopPrefix(ast);   // (G5a-1 row N) the scope on `ast`
      assert PSM.StampPathOk(qm, str, best.quant_regs.a_cp);   // FindMatchSimRECdn, for the winner
      var rp := ReadoutAtWinner(qm, ast, re, crv, code, endl, str, ov, inits, capture, look, quant,
                                ncap, nlook, nquant, result);
      var D := M.QIdsOuter(re);
      var rp0 := ClearQuantCps(rp, D);
      ClearQuantCpsGm(re, rp, D);
      ClearQuantCpsFacts(rp, D);
      assert fmres.1 == ov;
      assert fmp.0 == Some(rp) && fmp.1 == ov;

      assert {:split_here} true;
      // ---- the tie at (spec leaf, rp0) ---------------------------------------
      assert LT.FirstLeaf(t, inp).Some?;
      var leaf := LT.FirstLeaf(t, inp).value;
      assert bestT.Some?;
      assert PIV.ThreadTracksGm(re, qm, str, best, bestT.value.1);
      assert bestT.value.1 == PIV.GmOfLiveR(re, qm, str, best.capture_regs, best.look_regs, best.quant_regs)
        by { reveal PIV.TieGm; }
      assert PIV.GmOfLive(re, rp0.capture_regs, rp0.look_regs, rp0.quant_regs) == bestT.value.1;
      assert LL.GmAgreeOutside(bestT.value.1, leaf.1, S);
      assert GmtTieOutside(re, rp0, leaf.1, S);
      assert bleaf.Some? && LL.GmAgreeOutside(bleaf.value.1, leaf.1, G);
      QInStampQ(re);
      TieTransportS(rer, re, crv, str, ov, FRD.StampQids(re), S, G, bleaf.value, leaf, best, rp0,
                   ncap, nlook, nquant);
      M.FirstLeafOrdered(t, inp, leaf);

      assert {:split_here} true;
      // ---- the endpoint at rp0 ------------------------------------------------
      EndpointAtRp0(rer, qm, crv, str, ast, re, code, endl, ov, rp0, leaf, t, inp, S, ncap, nlook, nquant);
      var res := AI.FLookLoop(crv, str, 1, maxlook, rp0.capture_regs, rp0.look_regs, rp0.quant_regs, ov);
      var synthetic := AI.Thread(rp0.pc, res.0, res.1, res.2, rp0.exit_allowed);
      assert leaf.1 == PIV.NormGm(PIV.GmOfLive(re, res.0, res.1, res.2));

      assert {:split_here} true;
      // ---- the engine answer, read at rp0 ---------------------------------------
      M.FBuildCaptureUnfoldL3a(crv, str, ov, ncap, nlook, nquant, capture, look, quant, fmp);
      AnswerSynthetic(ast, re, crv, str, ov, rp);
      assert bc.0 == Some(AI.filter_reset(crv.f_main_ast, res.0, res.1, res.2, -1)) by {
        assert fmp.0.value == rp;
        var r1 := AI.FLookLoop(crv, str, 1, R.max_lookaround(crv.f_main_ast),
                               rp.capture_regs, rp.look_regs, rp.quant_regs, fmp.1);
        assert bc.0 == Some(AI.filter_reset(crv.f_main_ast, r1.0, r1.1, r1.2, -1));
      }
      assert AI.FFullMatch(raw, str)
          == Some(AI.filter_reset(ast, synthetic.capture_regs, synthetic.look_regs,
                                  synthetic.quant_regs, -1));

      assert {:split_here} true;
      // ---- extraction ------------------------------------------------------
      assert EL.BoolTreeLk(LES.TheRer(raw), [LS.Areg(LES.SpecRegex(raw))], LC.InitInput(str), BS.CannotExit, t);
      assert {:split_here} true;   // (G3a) the extraction section, one batch per step
      assert LS.IsTree(LES.TheRer(raw), [LS.Areg(LES.SpecRegex(raw))], LC.InitInput(str), LG.Empty, WP.Forward, t);
      assert {:split_here} true;   // (G3a) the extraction section, one batch per step
      assert CM.ThreadRegsWf(synthetic, ncap, nlook, nquant);
      assert ncap == 2 * R.max_group(R.annotate(raw)) + 2
             && nlook == R.max_lookaround(R.annotate(raw)) + 1
             && nquant == R.max_quant(R.annotate(raw)) + 1;
      assert {:split_here} true;   // (G3a) the extraction section, one batch per step
      assert M.QuantClkFinal(synthetic);
      assert {:split_here} true;   // (G3a) the extraction section, one batch per step
      assert leaf.1 == PIV.NormGm(PIV.GmOfLive(re, synthetic.capture_regs, synthetic.look_regs,
                                               synthetic.quant_regs));
      assert {:split_here} true;   // (G3a) the extraction section, one batch per step
      assert LT.FirstLeaf(t, LC.InitInput(str)) == Some(leaf);
      assert {:split_here} true;   // (G3a) the extraction section, one batch per step
      // (G3a) MainExtractionL5Lk's premises in its own syntax, one batch each: the call below is then
      // a match against ground facts (as one batch with the call it ran past 600 s twice).
      assert AI.FFullMatch(raw, str)
          == Some(AI.filter_reset(R.annotate(raw), synthetic.capture_regs, synthetic.look_regs,
                                  synthetic.quant_regs, -1));
      assert {:split_here} true;   // (G3a) the extraction section, one batch per step
      assert var re' := R.lazy_prefix(R.annotate(raw));
             leaf.1 == PIV.NormGm(PIV.GmOfLive(re', synthetic.capture_regs, synthetic.look_regs, synthetic.quant_regs));
      assert {:split_here} true;   // (G3a) the extraction section, one batch per step
      assert NR.NestedFragmentCdnRaw(raw) && T.Latin1Wf(raw);
      assert {:split_here} true;   // (G3a) the extraction section, one batch per step
      assert ExtractionPre(raw, str, t, synthetic, leaf) by {
        hide *;
        ExtractionPreIntro(raw, str, t, synthetic, leaf);   // (G5a-1) the body stays folded here
      }
      assert {:split_here} true;   // (G3a) the extraction section, one batch per step
      assert LES.MatcherSpec(raw, str, LES.Normalize(AI.FFullMatch(raw, str))) by {
        hide *;
        MainExtractionL5LkPre(raw, str, t, synthetic, leaf);
      }
    }
  }

  /** The nested fragment admits no CDN-greedy plus. */
  lemma NestedNoCdnLk(re: R.regex)
    requires NR.NestedFragmentRE(re)
    ensures NRC.NoCdnPlusRE(re)
    decreases re
  {
    match re
    case Re_empty =>
    case Re_character(_) =>
    case Re_anchor(_) =>
    case Re_alt(r1, r2) => NestedNoCdnLk(r1); NestedNoCdnLk(r2);
    case Re_con(r1, r2) => NestedNoCdnLk(r1); NestedNoCdnLk(r2);
    case Re_quant(_, _, _, r1) => NestedNoCdnLk(r1);
    case Re_capture(_, r1) => NestedNoCdnLk(r1);
    case Re_lookaround(_, _, r1) => NestedNoCdnLk(r1);
  }

  // =========================================================================
  // 8. Executable scope conditions (for `API.Supported`, rung G).
  // =========================================================================

  /** Every greedy CI-nullable plus has a look-free body (executable). */
  predicate CinBodiesLookFreeX(re: R.regex)
    decreases re
  {
    match re
    case Re_alt(r1, r2) => CinBodiesLookFreeX(r1) && CinBodiesLookFreeX(r2)
    case Re_con(r1, r2) => CinBodiesLookFreeX(r1) && CinBodiesLookFreeX(r2)
    case Re_quant(nul, qid, q, body) =>
      (q.min != 0 && q.max == None && nul == R.CINullable && q.greedy ==> NR.LookFreeRE(body))
      && CinBodiesLookFreeX(body)
    case Re_capture(_, r1) => CinBodiesLookFreeX(r1)
    case Re_lookaround(_, _, r1) => CinBodiesLookFreeX(r1)
    case _ => true
  }

  lemma CinBodiesLookFreeXSound(re: R.regex)
    requires CinBodiesLookFreeX(re)
    ensures RF.CinBodiesLookFreeRE(re)
    decreases re
  {
    match re
    case Re_alt(r1, r2) => CinBodiesLookFreeXSound(r1); CinBodiesLookFreeXSound(r2);
    case Re_con(r1, r2) => CinBodiesLookFreeXSound(r1); CinBodiesLookFreeXSound(r2);
    case Re_quant(_, _, _, r1) => CinBodiesLookFreeXSound(r1);
    case Re_capture(_, r1) => CinBodiesLookFreeXSound(r1);
    case Re_lookaround(_, _, r1) => CinBodiesLookFreeXSound(r1);
    case _ =>
  }

  /** (G5a-1 step 4) `NRC.NoCdnPlusRE`, compiled (that one is a ghost predicate). */
  predicate NoCdnPlusX(re: R.regex)
    decreases re
  {
    match re
    case Re_empty => true
    case Re_character(_) => true
    case Re_anchor(_) => true
    case Re_alt(r1, r2) => NoCdnPlusX(r1) && NoCdnPlusX(r2)
    case Re_con(r1, r2) => NoCdnPlusX(r1) && NoCdnPlusX(r2)
    case Re_quant(nul, qid, q, r1) =>
      !(q.min != 0 && q.max == None && nul == R.CDNullable && q.greedy) && NoCdnPlusX(r1)
    case Re_capture(_, r1) => NoCdnPlusX(r1)
    case Re_lookaround(_, _, r1) => NoCdnPlusX(r1)
  }

  lemma NoCdnPlusXSound(re: R.regex)
    ensures NoCdnPlusX(re) <==> NRC.NoCdnPlusRE(re)
    decreases re
  {
    match re
    case Re_alt(r1, r2) => NoCdnPlusXSound(r1); NoCdnPlusXSound(r2);
    case Re_con(r1, r2) => NoCdnPlusXSound(r1); NoCdnPlusXSound(r2);
    case Re_quant(_, _, _, r1) => NoCdnPlusXSound(r1);
    case Re_capture(_, r1) => NoCdnPlusXSound(r1);
    case Re_lookaround(_, _, r1) => NoCdnPlusXSound(r1);
    case _ =>
  }

  /** (G5a-1 step 4) `NRC.CdnTopRE`, compiled, for `API.Supported`. */
  predicate CdnTopX(re: R.regex)
    decreases re
  {
    match re
    case Re_alt(r1, r2) => CdnTopX(r1) && CdnTopX(r2)
    case Re_con(r1, r2) => CdnTopX(r1) && CdnTopX(r2)
    case Re_capture(_, r1) => CdnTopX(r1)
    case Re_lookaround(_, _, r1) => NoCdnPlusX(r1)
    case Re_quant(nul, _, q, r1) =>
      if q.min != 0 && q.max == None && q.greedy && nul == R.CDNullable then NR.LookFreeRE(r1) && NR.NoNulledPlusRE(r1) && NoCdnPlusX(r1)
      else if q.min != 0 && q.max == None && q.greedy && nul == R.CINullable then NoCdnPlusX(r1)
      else CdnTopX(r1)
    case _ => true
  }

  lemma CdnTopXSound(re: R.regex)
    requires CdnTopX(re)
    ensures NRC.CdnTopRE(re)
    decreases re
  {
    match re
    case Re_alt(r1, r2) => CdnTopXSound(r1); CdnTopXSound(r2);
    case Re_con(r1, r2) => CdnTopXSound(r1); CdnTopXSound(r2);
    case Re_capture(_, r1) => CdnTopXSound(r1);
    case Re_lookaround(_, _, r1) => NoCdnPlusXSound(r1);
    case Re_quant(nul, _, q, r1) =>
      if q.min != 0 && q.max == None && q.greedy && nul == R.CDNullable {
        NoCdnPlusXSound(r1);
      } else if q.min != 0 && q.max == None && q.greedy && nul == R.CINullable {
        NoCdnPlusXSound(r1);
      } else {
        CdnTopXSound(r1);
      }
    case _ =>
  }

  /** (G5a-1 step 4) No CDN-greedy plus at all is in scope (for `API.SupportedWidens`). */
  lemma NoCdnXIsCdnTopX(re: R.regex)
    requires NoCdnPlusX(re)
    ensures CdnTopX(re)
    decreases re
  {
    match re
    case Re_alt(r1, r2) => NoCdnXIsCdnTopX(r1); NoCdnXIsCdnTopX(r2);
    case Re_con(r1, r2) => NoCdnXIsCdnTopX(r1); NoCdnXIsCdnTopX(r2);
    case Re_capture(_, r1) => NoCdnXIsCdnTopX(r1);
    case Re_quant(_, _, _, r1) => NoCdnXIsCdnTopX(r1);
    case _ =>
  }
}
