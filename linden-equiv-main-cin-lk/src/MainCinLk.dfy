// §2.5b STAGE 2, RUNG F (F-c, c6) — CIN-GREEDY PLUSES NEXT TO LOOKAROUNDS.
//
// `MainTheoremL5` without the interim gate conjunct `NoNulledPlusRaw`: greedy
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

  // =========================================================================
  // 0. Statics: the glue's side condition on the translated regex.
  // =========================================================================

  lemma LookFreeLkBodies(r: R.regex, S: set<LG.GroupId>)
    requires T.TransWf(r) && NR.LookFreeRE(r)
    ensures LL.LkBodiesInS(T.Translate(r), S)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => LookFreeLkBodies(r1, S); LookFreeLkBodies(r2, S);
    case Re_con(r1, r2) => LookFreeLkBodies(r1, S); LookFreeLkBodies(r2, S);
    case Re_quant(_, _, _, r1) => LookFreeLkBodies(r1, S);
    case Re_capture(_, r1) => LookFreeLkBodies(r1, S);
    case _ =>
  }

  /** Every CIN-greedy plus of the translation has a look-free body whose groups
      lie in `G` (any `G` covering the outside-look captures). */
  lemma TranslateCinOk(r: R.regex, G: set<LG.GroupId>)
    requires T.TransWf(r) && NR.NestedFragmentRE(r)
    requires M.LooksNoNulledPlusRE(r) && RF.CinBodiesLookFreeRE(r)
    requires forall g: nat :: g in PIV.CapIdsOutsideLooks(r) ==> g in G
    ensures CW.CinOk(T.Translate(r), G)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => TranslateCinOk(r1, G); TranslateCinOk(r2, G);
    case Re_con(r1, r2) => TranslateCinOk(r1, G); TranslateCinOk(r2, G);
    case Re_capture(_, r1) => TranslateCinOk(r1, G);
    case Re_lookaround(_, _, r1) =>
      assert NR.NoNulledPlusRE(r1);
      NUL.TransNoNulledPlus(r1);
      CW.NoNulledPlusCinOk(T.Translate(r1), G);
    case Re_quant(nul, qid, q, body) =>
      TranslateCinOk(body, G);
      var tb := T.Translate(body);
      assert T.Translate(r) == L.Quantified(q.greedy, q.min as nat, T.TrDelta(q), tb);
      if q.min > 0 && CW.CinGreedyL(q.greedy, T.TrDelta(q), tb) {
        assert q.greedy && T.TrDelta(q) == LN.Inf by { reveal CW.CinGreedyL(); }
        assert q.max == None;
        if nul == R.NonNullable {
          NUL.TransNonNullable(body);
          CW.NotCinGreedyNonNullable(q.greedy, T.TrDelta(q), tb);
          assert false;
        }
        assert nul == R.CINullable;
        assert NR.LookFreeRE(body);
        LookFreeLkBodies(body, {});
        PIV.DefGroupsCapIds(body);
        PIV.LookFreeCapIdsInLooksEmpty(body);
        PIV.CapIdsSplit(body);
        forall g | g in L.DefGroups(tb) ensures g in G {
          assert g in PIV.CapIds(body);
          assert g in PIV.CapIdsOutsideLooks(r);
        }
      }
    case _ =>
  }

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

  /** The register frame the transport needs: look registers equal, capture and
      quant CLOCKS equal outside the reconstruction's write sets. */
  ghost predicate ClkFrame(re: R.regex, Q: set<int>, a: AI.Thread, b: AI.Thread) {
    a.look_regs == b.look_regs
    && (forall k :: k !in RF.CapsQ(re, Q) ==> AI.get_idx(a.capture_regs.a_clk, k) == AI.get_idx(b.capture_regs.a_clk, k))
    && (forall k :: k !in RF.QuantsQ(re, Q) ==> AI.get_idx(a.quant_regs.a_clk, k) == AI.get_idx(b.quant_regs.a_clk, k))
  }

  lemma AncFrame(re: R.regex, Q: set<int>, a: AI.Thread, b: AI.Thread, lid: nat)
    requires lid in LTB.LookIds(re)
    requires RF.CinBodiesLookFreeRE(re) && PIV.CapUnique(re) && PIV.QuantUnique(re) && RF.QInCin(re, Q)
    requires ClkFrame(re, Q, a, b)
    ensures forall mx :: NI.LookPathPresent(re, a.capture_regs.a_clk, a.quant_regs.a_clk, mx, lid)
                         == NI.LookPathPresent(re, b.capture_regs.a_clk, b.quant_regs.a_clk, mx, lid)
    ensures forall mx :: NI.MxAtLidLk(re, a.quant_regs.a_clk, mx, lid) == NI.MxAtLidLk(re, b.quant_regs.a_clk, mx, lid)
    ensures forall L :: NI.LookPathDom(re, L, a.quant_regs.a_clk, lid) == NI.LookPathDom(re, L, b.quant_regs.a_clk, lid)
  {
    CLP.AncAvoidQ(re, Q, lid);
    var cc1 := a.capture_regs.a_clk;
    var cc2 := b.capture_regs.a_clk;
    var qc1 := a.quant_regs.a_clk;
    var qc2 := b.quant_regs.a_clk;
    assert forall k :: k in CLP.AncCapRegs(re, lid) ==> AI.get_idx(cc1, k) == AI.get_idx(cc2, k) by {
      forall k | k in CLP.AncCapRegs(re, lid) ensures AI.get_idx(cc1, k) == AI.get_idx(cc2, k) {
        if k in RF.CapsQ(re, Q) { assert k in CLP.AncCapRegs(re, lid) * RF.CapsQ(re, Q); }
      }
    }
    assert forall k :: k in CLP.AncQuants(re, lid) ==> AI.get_idx(qc1, k) == AI.get_idx(qc2, k) by {
      forall k | k in CLP.AncQuants(re, lid) ensures AI.get_idx(qc1, k) == AI.get_idx(qc2, k) {
        if k in RF.QuantsQ(re, Q) { assert k in CLP.AncQuants(re, lid) * RF.QuantsQ(re, Q); }
      }
    }
    forall mx ensures NI.LookPathPresent(re, cc1, qc1, mx, lid) == NI.LookPathPresent(re, cc2, qc2, mx, lid)
                      && NI.MxAtLidLk(re, qc1, mx, lid) == NI.MxAtLidLk(re, qc2, mx, lid) {
      CLP.LookPathFrame(re, cc1, qc1, cc2, qc2, mx, lid);
    }
    forall L ensures NI.LookPathDom(re, L, qc1, lid) == NI.LookPathDom(re, L, qc2, lid) {
      CLP.LookPathDomFrame(re, L, qc1, qc2, lid);
    }
  }

  lemma TieOkTTransport(re: R.regex, Q: set<int>, S: set<LG.GroupId>, G: set<LG.GroupId>,
                        gmB: LG.GroupMap, gm: LG.GroupMap, best: AI.Thread, th: AI.Thread)
    requires RF.CinBodiesLookFreeRE(re) && PIV.CapUnique(re) && PIV.QuantUnique(re) && RF.QInCin(re, Q)
    requires G * S == {} && LL.GmAgreeOutside(gmB, gm, G)
    requires ClkFrame(re, Q, th, best)
    requires LookNestOkTTop(re, S, gmB, best)
    ensures LookNestOkTTop(re, S, gm, th)
  {
    forall lid: nat | lid in NI.TopLookIds(re)
                      && (lid in LTB.LookIds(re)
                          && exists g: LG.GroupId :: g in S && g in gm && g in PIV.CapIds(NI.LookBodyOfRE(re, lid)))
      ensures NI.LookPathPresent(re, th.capture_regs.a_clk, th.quant_regs.a_clk, -1, lid)
              && AI.get_idx(th.look_regs.a_clk, lid as int) >= 0
              && AI.get_idx(th.look_regs.a_clk, lid as int) >= NI.MxAtLidLk(re, th.quant_regs.a_clk, -1, lid)
    {
      var g: LG.GroupId :| g in S && g in gm && g in PIV.CapIds(NI.LookBodyOfRE(re, lid));
      assert g !in G by { if g in G { assert g in G * S; } }
      assert g in gmB;
      assert exists g0: LG.GroupId :: g0 in S && g0 in gmB && g0 in PIV.CapIds(NI.LookBodyOfRE(re, lid));
      assert NI.LookPathPresent(re, best.capture_regs.a_clk, best.quant_regs.a_clk, -1, lid)
             && AI.get_idx(best.look_regs.a_clk, lid as int) >= 0
             && AI.get_idx(best.look_regs.a_clk, lid as int) >= NI.MxAtLidLk(re, best.quant_regs.a_clk, -1, lid);
      AncFrame(re, Q, th, best, lid);
    }
  }

  lemma TieBackTransport(re: R.regex, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
                         Q: set<int>, S: set<LG.GroupId>, G: set<LG.GroupId>,
                         gmB: LG.GroupMap, gm: LG.GroupMap, best: AI.Thread, th: AI.Thread,
                         ncap: int, nlook: int, nquant: int)
    requires RF.CinBodiesLookFreeRE(re) && PIV.CapUnique(re) && PIV.QuantUnique(re) && RF.QInCin(re, Q)
    requires G * S == {} && LL.GmAgreeOutside(gmB, gm, G)
    requires ClkFrame(re, Q, th, best)
    requires LookNestBackTTop(re, crv, str, ov, S, gmB, best, ncap, nlook, nquant)
    ensures LookNestBackTTop(re, crv, str, ov, S, gm, th, ncap, nlook, nquant)
  {
    forall lid: nat | lid in NI.TopLookIds(re)
                      && (M.MatchedPosLA(crv, th.look_regs, lid as int)
                          && lid in LTB.LookIds(re)
                          && NI.LookPathDom(re, AI.get_idx(th.look_regs.a_clk, lid as int), th.quant_regs.a_clk, lid))
      ensures var rf := M.FreshBodyMatch(crv, str, lid as int, th.look_regs, ov, ncap, nlook, nquant);
              rf.Some? ==>
                forall g: LG.GroupId ::
                  g in S && g in PIV.CapIds(NI.LookBodyOfRE(re, lid))
                  && g in PIV.GmOfLive(NI.LookBodyOfRE(re, lid), rf.value.capture_regs,
                                       rf.value.look_regs, rf.value.quant_regs)
                  ==> g in gm
    {
      AncFrame(re, Q, th, best, lid);
      var rf := M.FreshBodyMatch(crv, str, lid as int, th.look_regs, ov, ncap, nlook, nquant);
      if rf.Some? {
        forall g: LG.GroupId | g in S && g in PIV.CapIds(NI.LookBodyOfRE(re, lid))
                               && g in PIV.GmOfLive(NI.LookBodyOfRE(re, lid), rf.value.capture_regs,
                                                    rf.value.look_regs, rf.value.quant_regs)
          ensures g in gm
        {
          assert g !in G by { if g in G { assert g in G * S; } }
          assert g in gmB;
        }
      }
    }
  }

  lemma TieDeepTransport(rer: LW.RegExpRecord, re: R.regex, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
                         Q: set<int>, S: set<LG.GroupId>, G: set<LG.GroupId>,
                         gmB: LG.GroupMap, gm: LG.GroupMap, best: AI.Thread, th: AI.Thread,
                         ncap: int, nlook: int, nquant: int)
    requires RF.CinBodiesLookFreeRE(re) && PIV.CapUnique(re) && PIV.QuantUnique(re) && RF.QInCin(re, Q)
    requires G * S == {} && LL.GmAgreeOutside(gmB, gm, G)
    requires ClkFrame(re, Q, th, best)
    requires LookNestBackTTopDeep(rer, re, crv, str, ov, S, gmB, best, ncap, nlook, nquant)
    ensures LookNestBackTTopDeep(rer, re, crv, str, ov, S, gm, th, ncap, nlook, nquant)
  {
    forall lid: nat | lid in NI.TopLookIds(re)
                      && (M.MatchedPosLA(crv, th.look_regs, lid as int)
                          && lid in LTB.LookIds(re)
                          && NI.LookPathDom(re, AI.get_idx(th.look_regs.a_clk, lid as int), th.quant_regs.a_clk, lid))
      ensures var lsub := SubFirstLeafAt(rer, crv, str, lid as int, th.look_regs);
              lsub.Some? ==>
                forall g: LG.GroupId ::
                  g in S && g in PIV.CapIds(NI.LookBodyOfRE(re, lid)) ==>
                    (g in lsub.value ==> g in gm && gm[g] == lsub.value[g])
                    && (g in gm ==> g in lsub.value)
    {
      AncFrame(re, Q, th, best, lid);
      var lsub := SubFirstLeafAt(rer, crv, str, lid as int, th.look_regs);
      if lsub.Some? {
        forall g: LG.GroupId | g in S && g in PIV.CapIds(NI.LookBodyOfRE(re, lid))
          ensures (g in lsub.value ==> g in gm && gm[g] == lsub.value[g])
                  && (g in gm ==> g in lsub.value)
        {
          assert g !in G by { if g in G { assert g in G * S; } }
          assert (g in gmB <==> g in gm) && (g in gmB ==> gmB[g] == gm[g]);
        }
      }
    }
  }

  /** THE TRANSPORT. */
  lemma TieTransport(rer: LW.RegExpRecord, re: R.regex, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
                     Q: set<int>, S: set<LG.GroupId>, G: set<LG.GroupId>,
                     bleaf: LT.Leaf, leaf: LT.Leaf, best: AI.Thread, th: AI.Thread,
                     ncap: int, nlook: int, nquant: int)
    requires RF.CinBodiesLookFreeRE(re) && PIV.CapUnique(re) && PIV.QuantUnique(re) && RF.QInCin(re, Q)
    requires G * S == {} && LL.GmAgreeOutside(bleaf.1, leaf.1, G)
    requires ClkFrame(re, Q, th, best)
    requires BestTieLkNestedTop(rer, re, crv, str, ov, S, Some(bleaf), Some(best), ncap, nlook, nquant)
    requires GmtTieOutside(re, th, leaf.1, S)   // machine A
    ensures BestTieLkNestedTop(rer, re, crv, str, ov, S, Some(leaf), Some(th), ncap, nlook, nquant)
  {
    TieOkTTransport(re, Q, S, G, bleaf.1, leaf.1, best, th);
    TieBackTransport(re, crv, str, ov, Q, S, G, bleaf.1, leaf.1, best, th, ncap, nlook, nquant);
    TieDeepTransport(rer, re, crv, str, ov, Q, S, G, bleaf.1, leaf.1, best, th, ncap, nlook, nquant);
  }

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
    requires M.LooksNoNulledPlusRE(re)
    requires code == CP.compile_to_bytecode(re)
    requires NR.NestedFragmentRE(re)
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
    M.LookRowsDynamicNested(ast, re, crv, code, str, ov, cdn, inits, cap, look, quant,
                            ncap, nlook, nquant, endl, result);
    M.FStabilityNested(ast, re, crv, code, str, ov, cdn, inits, cap, look, quant, nlook, result);
    var initlk := AReg.init_regs(nlook);
    var Sd := M.DirectLidSet(re);
    M.DirectLidClassified(re);
    assert CM.VmLooksAgree(inits, initlk, Sd) by {
      forall t | t in inits.active ensures CM.RegsAgreeOutside(t.look_regs, initlk, Sd) {
        assert t == AI.init_thread(cap, look, quant);
      }
    }
    CM.FFindMatchLookFrame(code, str, inits, ov, LAnc.Forward, cdn, initlk, Sd);
    M.NoWriteOracleBodyCodeNested(re);
    if result.Some? {
      M.MainMatchBodyQuantsInitNested(re, code, str, inits, cap, look, quant, ov, cdn, result);
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
      reveal WinRegsOkG();
    }
  }

  /** No CIN-greedy plus under a nulled-plus-free regex. */
  lemma NoNulledPlusNoCin(r: R.regex, q: nat)
    requires T.TransWf(r)   // QuantWf: min >= 0, so `min != 0` is `min > 0`
    requires NR.NoNulledPlusRE(r) && q in PIV.QuantIds(r)
    ensures !NRR.QidCinPlus(r, q)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => if q in PIV.QuantIds(r1) { NoNulledPlusNoCin(r1, q); } else { NoNulledPlusNoCin(r2, q); }
    case Re_con(r1, r2) => if q in PIV.QuantIds(r1) { NoNulledPlusNoCin(r1, q); } else { NoNulledPlusNoCin(r2, q); }
    case Re_quant(nul, qid, qq, r1) => if !(qid >= 0 && (qid as nat) == q) { NoNulledPlusNoCin(r1, q); }
    case Re_capture(_, r1) => NoNulledPlusNoCin(r1, q);
    case Re_lookaround(_, _, r1) => NoNulledPlusNoCin(r1, q);
  }

  /** The CIN-greedy pluses sit outside every lookaround. */
  lemma CinQidsOuter(r: R.regex, q: nat)
    requires T.TransWf(r)
    requires M.LooksNoNulledPlusRE(r)
    requires q in PIV.QuantIds(r) && NRR.QidCinPlus(r, q)
    ensures q in PIV.QuantIdsOutsideLooks(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => if q in PIV.QuantIds(r1) { CinQidsOuter(r1, q); } else { CinQidsOuter(r2, q); }
    case Re_con(r1, r2) => if q in PIV.QuantIds(r1) { CinQidsOuter(r1, q); } else { CinQidsOuter(r2, q); }
    case Re_quant(nul, qid, qq, r1) => if !(qid >= 0 && (qid as nat) == q) { CinQidsOuter(r1, q); }
    case Re_capture(_, r1) => CinQidsOuter(r1, q);
    case Re_lookaround(_, _, r1) =>
      assert NR.NoNulledPlusRE(r1);
      NoNulledPlusNoCin(r1, q);
  }

  lemma QInCinQ(re: R.regex)
    ensures RF.QInCin(re, FRD.CinQids(re))
  {
    forall q: nat | q in PIV.QuantIds(re) && (q as int) in FRD.CinQids(re) ensures NRR.QidCinPlus(re, q) {
      var qn: nat :| qn in PIV.QuantIds(re) && NRR.QidCinPlus(re, qn) && qn as int == q as int;
      assert qn == q;
    }
  }

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
    requires T.TransWf(re) && M.LooksNoNulledPlusRE(re) && RF.CinBodiesLookFreeRE(re)
    requires PIV.CapUnique(re) && PIV.QuantUnique(re) && LTB.LookTablesOk(re, crv)
    requires WinRegsOkG(ast, re, crv, str, ov, best, ncap, nlook, nquant)
    requires FV.RegsFinalOk(best, |str|, FRD.CinQids(re))
    requires CM.ThreadRegsWf(rp, ncap, nlook, nquant)
    requires forall k :: AI.get_idx(rp.quant_regs.a_clk, k) >= -1
    requires var Q := FRD.CinQids(re);
             NRR.AgreeOutside((rp.capture_regs, rp.look_regs, rp.quant_regs),
                              (best.capture_regs, best.look_regs, best.quant_regs),
                              RF.CapsQ(re, Q), RF.LooksQ(re, Q), RF.QuantsQ(re, Q))
    ensures rp.look_regs == best.look_regs
    ensures M.WinRegsOk(ast, re, crv, str, ov, ClearQuantCps(rp, M.QIdsOuter(re)), ncap, nlook, nquant)
  {
    reveal WinRegsOkG();
    var Q := FRD.CinQids(re);
    var D := M.QIdsOuter(re);
    var rp0 := ClearQuantCps(rp, D);
    ClearQuantCpsFacts(rp, D);
    QInCinQ(re);
    RF.LooksQEmpty(re, Q);
    CLP.QsOutside(re, Q);
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
          if AI.get_idx(best.quant_regs.a_cp, k) >= 0 {
            assert k in Q;
            var qn: nat :| qn in PIV.QuantIds(re) && NRR.QidCinPlus(re, qn) && qn as int == k;
            CinQidsOuter(re, qn);
            assert k in D;
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
        CLP.QsAvoidLookBody(re, Q, l as nat);
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
    requires M.LooksNoNulledPlusRE(re)
    ensures EL.PikeLkRegexRec(T.Translate(re))
    decreases re
  {
    match re
    case Re_alt(r1, r2) => TranslateFragmentPikeLkRecLk(r1); TranslateFragmentPikeLkRecLk(r2);
    case Re_con(r1, r2) => TranslateFragmentPikeLkRecLk(r1); TranslateFragmentPikeLkRecLk(r2);
    case Re_quant(nul, qid, q, r1) => TranslateFragmentPikeLkRecLk(r1);
    case Re_capture(_, r1) => TranslateFragmentPikeLkRecLk(r1);
    case Re_lookaround(lid, la, r1) =>
      assert NR.NoNulledPlusRE(r1);
      assert L.Positivity(T.TrLookaround(la)) == (la.Lookahead? || la.Lookbehind?);
      EL.TranslateFragmentPikeLkRec(r1);
      NUL.TransNoNulledPlus(r1);
      if !(la.Lookahead? || la.Lookbehind?) {
        EL.TranslateCaptureFreeNoDefs(r1);
      }
      reveal EL.NegBodyNoDefs();
    case _ =>
  }

  /** `LSC.MainExtractionL5` under the look-bodies gate. */
  lemma MainExtractionL5Lk(raw: R.raw_regex, str: string,
                           t: LT.Tree, thread: AI.Thread, leaf: LT.Leaf)
    requires NR.NestedFragmentRaw(raw)
    requires M.LooksNoNulledPlusRE(R.lazy_prefix(R.annotate(raw)))
    requires NR.L5ScopeRE(R.lazy_prefix(R.annotate(raw)))
    requires EL.NegBehindLBOnlyRE(R.lazy_prefix(R.annotate(raw)))
    requires T.Latin1Wf(raw)
    requires EL.BoolTreeLk(LES.TheRer(raw), [LS.Areg(LES.SpecRegex(raw))], LC.InitInput(str), BS.CannotExit, t)
    requires LS.IsTree(LES.TheRer(raw), [LS.Areg(LES.SpecRegex(raw))], LC.InitInput(str), LG.Empty, WP.Forward, t)
    requires CM.ThreadRegsWf(thread, 2 * R.max_group(R.annotate(raw)) + 2,
                             R.max_lookaround(R.annotate(raw)) + 1,
                             R.max_quant(R.annotate(raw)) + 1)
    requires M.QuantRegsFinal(thread)
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
    NR.SpecRegexNestedFragment(raw);
    assert LES.SpecRegex(raw) == T.Translate(re);

    // closedness of the leaf gm
    assert LT.TreeRes(t, LG.Empty, inp, WP.Forward) == Some(leaf);
    assert M.OpenOf(LG.Empty) <= M.PendingCloses([LS.Areg(T.Translate(re))]);
    TranslateFragmentPikeLkRecLk(re);
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
    L5ScopeL5PosL(re);
    assert FC.L5PosActsL([LS.Areg(T.Translate(re))]);
    assert M.NestDepthActsLe([LS.Areg(T.Translate(re))], M.NestDepthL(T.Translate(re)));
    FC.FirstLeafClosedRecL5(rer, [LS.Areg(T.Translate(re))], inp, BS.CannotExit, t, LG.Empty, leaf,
                            M.NestDepthL(T.Translate(re)));
    assert M.ClosedGm(leaf.1);
    M.MainExtractionFromClosed(raw, str, t, thread, leaf);
  }

  lemma NRRLookIdsEq(r: R.regex)
    ensures NRR.LookIds(r) == LTB.LookIds(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => NRRLookIdsEq(r1); NRRLookIdsEq(r2);
    case Re_con(r1, r2) => NRRLookIdsEq(r1); NRRLookIdsEq(r2);
    case Re_quant(_, _, _, r1) => NRRLookIdsEq(r1);
    case Re_capture(_, r1) => NRRLookIdsEq(r1);
    case Re_lookaround(_, _, r1) => NRRLookIdsEq(r1);
    case _ =>
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

  /** The outside-look capture-write frame, read off at start registers. */
  lemma OnlyCapIdsFromFrameOuter(re: R.regex, caps: AReg.Regs, ncap: int)
    requires CM.RegsAgreeOutside(caps, AReg.init_regs(ncap), PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(re)))
    ensures forall gid: nat :: gid !in PIV.CapIds(re) ==> AI.get_idx(caps.a_cp, CP.start_reg(gid)) < 0
  {
    var capture := AReg.init_regs(ncap);
    var Sreg := PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(re));
    PIV.CapIdsSplit(re);
    forall gid: nat | gid !in PIV.CapIds(re) ensures AI.get_idx(caps.a_cp, CP.start_reg(gid)) < 0 {
      var k := CP.start_reg(gid);
      assert k !in Sreg by {
        if k in Sreg {
          if k in (set cid | cid in PIV.CapIdsOutsideLooks(re) :: CP.start_reg(cid)) {
            var c :| c in PIV.CapIdsOutsideLooks(re) && CP.start_reg(c) == k;
            assert c == gid;
          } else {
            var c :| c in PIV.CapIdsOutsideLooks(re) && CP.end_reg(c) == k;
            assert 2 * c + 1 == 2 * gid;
          }
        }
      }
      assert AI.get_idx(caps.a_cp, k) == AI.get_idx(capture.a_cp, k);
      if 0 <= k < |capture.a_cp| { assert capture.a_cp[k] == -1; }
    }
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
    requires T.TransWf(re) && NR.NestedFragmentRE(re) && M.LooksNoNulledPlusRE(re) && RF.CinBodiesLookFreeRE(re)
    requires PIV.CapUnique(re) && PIV.QuantUnique(re) && LTB.LookUnique(re) && LTB.LookTablesOk(re, crv)
    requires NRC.NoCdnPlusRE(ast) && AR.QmapOk(re, qm) && qm.ov == ov
    requires NR.NfaRepRE(re, code, 0, endl) && |code| == endl + 1 && NR.GetPcRE(code, endl) == Some(RB.Accept)
    requires ncap == 2 * R.max_group(re) + 2 && nlook == R.max_lookaround(re) + 1 && nquant == R.max_quant(re) + 1
    requires capture == AReg.init_regs(ncap) && look == AReg.init_regs(nlook) && quant == AReg.init_regs(nquant)
    requires inits == AI.FInitState(code, 0, capture, look, quant, 0, AI.cp_context(0, str, LAnc.Forward))
    requires result == AI.FFindMatch(code, str, inits, ov, LAnc.Forward, crv.f_main_cdns).0
    requires result.Some? && PSM.BestLiveRE(re, result.value)
    ensures AI.FFindMatch(code, str, inits, ov, LAnc.Forward, crv.f_main_cdns).1 == ov
    ensures var rpp := AI.FReconstructPlus(result.value, ast, crv.f_plus_bc, str, ov, LAnc.Forward);
            rp == rpp.0 && rpp.1 == ov
    ensures rp.pc == result.value.pc && rp.exit_allowed == result.value.exit_allowed
    ensures PIV.GmOfLive(re, rp.capture_regs, rp.look_regs, rp.quant_regs)
            == PIV.GmOfLiveR(re, qm, str, result.value.capture_regs, result.value.look_regs, result.value.quant_regs)
    ensures CM.ThreadRegsWf(rp, ncap, nlook, nquant)
    ensures M.WinRegsOk(ast, re, crv, str, ov, ClearQuantCps(rp, M.QIdsOuter(re)), ncap, nlook, nquant)
    ensures ClkFrame(re, FRD.CinQids(re), ClearQuantCps(rp, M.QIdsOuter(re)), result.value)
  {
    hide NUL.NonNullableL, NUL.CINullableL, NUL.NoNulledPlusL, AR.NfaRepCinL;
    var best := result.value;
    var ctx := AI.cp_context(0, str, LAnc.Forward);
    var rg: NRC.Regs3 := (best.capture_regs, best.look_regs, best.quant_regs);
    var Q := FRD.CinQids(re);
    // VM facts of the winning thread
    CM.FInitStateRegsWf(code, 0, ncap, nlook, nquant, 0, ctx);
    M.FFindMatchRegsWf(code, str, inits, ov, LAnc.Forward, crv.f_main_cdns, ncap, nlook, nquant);
    assert CM.ThreadRegsWf(best, ncap, nlook, nquant);
    FRD.TrueStampsInCin(re, code, endl);
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
    M.CaptureBytecodeClassifiedNestedOuter(re);
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
    FRD.FinalReadout(qm, ast, str, best, ncap, nlook, nquant);
    CLP.FinalReadoutFrame(qm, ast, str, best);
    M.NoWriteOracleBodyCodeNested(re);
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
    requires T.TransWf(re) && NR.NestedFragmentRE(re) && NR.L5ScopeRE(re) && L5ScopeV1RE(re)
    requires M.LooksNoNulledPlusRE(re) && EL.NegBehindLBOnlyRE(re)
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
            && CM.ThreadRegsWf(synthetic, ncap, nlook, nquant) && M.QuantRegsFinal(synthetic)
  {
    hide NUL.NonNullableL, NUL.CINullableL, NUL.NoNulledPlusL, AR.NfaRepCinL;
    M.EndpointValueOkRegs(ast, re, crv, str, ov, th, ncap, nlook, nquant);
    M.EndpointQuantValueOkRegs(ast, re, crv, str, ov, th, ncap, nlook, nquant);
    M.EndpointChildLinkOkRegs(ast, re, crv, str, ov, th, ncap, nlook, nquant);
    M.EndpointLookInvRegs(ast, re, crv, str, ov, th, ncap, nlook, nquant);
    M.EndpointTopLookFrameRegs(ast, re, crv, str, ov, th, ncap, nlook, nquant);
    var resO := AI.FLookLoop(crv, str, 1, R.max_lookaround(ast), th.capture_regs, th.look_regs, th.quant_regs, ov);
    ProduceOwnerForallRes(qm, crv, str, ast, re, ov, resO.0, resO.1, resO.2, S, ncap, nlook, nquant);
    var res := AI.FLookLoop(crv, str, 1, R.max_lookaround(ast), th.capture_regs, th.look_regs, th.quant_regs, ov);
    var synthetic := AI.Thread(th.pc, res.0, res.1, res.2, th.exit_allowed);
    assert CM.ThreadRegsWf(synthetic, ncap, nlook, nquant) && M.QuantRegsFinal(synthetic);
    MainTheoremL4DeepConclude(rer, qm, crv, str, ast, re, code, endl, ov, th, leaf,
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

  /** THE THEOREM: `MainTheoremL5` without the interim gate — greedy
      CI-nullable pluses outside lookarounds, with look-free bodies, and no
      nulled plus inside a look body. */
  lemma MainTheoremL5Cin(raw: R.raw_regex, str: string)
    requires NR.NestedFragmentRaw(raw)
    requires T.Latin1Wf(raw)
    requires L5Scope(raw)
    requires M.LooksNoNulledPlusRE(R.lazy_prefix(R.annotate(raw)))
    requires RF.CinBodiesLookFreeRE(R.lazy_prefix(R.annotate(raw)))
    ensures LES.MatcherSpec(raw, str, LES.Normalize(AI.FFullMatch(raw, str)))
  {
    hide NUL.NonNullableL, NUL.CINullableL, NUL.NoNulledPlusL, AR.NfaRepCinL;
    // the two recursive gates are facts here, never unfolded (in context they blew batch 6 past 19 GB)
    hide M.LooksNoNulledPlusRE, RF.CinBodiesLookFreeRE;
    var ast := R.annotate(raw);
    var re := R.lazy_prefix(ast);
    var rer := LES.TheRer(raw);
    var inp := LC.InitInput(str);
    var ngroups := LES.NGroups(raw);
    assert !rer.multiline && !rer.ignoreCase;

    // ---- static packages -------------------------------------------------
    T.AnnotateWf(raw);
    NR.SpecRegexNestedFragment(raw);
    LTB.SpecRegexLookUnique(raw);
    LTB.SpecRegexLidsWellNested(raw);
    PIV.SpecRegexCapUnique(raw);
    PIV.SpecRegexQuantUnique(raw);
    assert L5ScopeV1RE(re);
    L5ScopeV1ImpliesL5(re);
    assert EL.NegBehindLBOnlyRE(re);
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
      assert NR.NestedFragmentRE(ast);
      OracleOkRowsL5(rer, ast, crv0, str, re);
    }

    NR.CompileToBytecodeRepNested(re);
    var code := CP.compile_to_bytecode(re);
    var next := CP.compile(re, 0, CP.Progress).1;
    var endl: nat := next as nat;
    assert NR.NfaRepRE(re, code, 0, endl)
           && NR.GetPcRE(code, endl) == Some(RB.Accept) && |code| == endl + 1;
    CompileStutterTameRENested(re);
    assert PSM.StaticCoreNestedRE(qm, re, code, endl);

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
    TranslateFragmentPikeLkRecLk(re);
    EL.BooleanCorrectLkRec(rer, T.Translate(re), inp, t);
    assert forall i :: 0 <= i < |[LS.Areg(T.Translate(re))]| ==> ![LS.Areg(T.Translate(re))][i].Acheck?;
    M.BoolTreeLbIrrel(rer, [LS.Areg(T.Translate(re))], inp, BS.CanExit, BS.CannotExit, t);
    assert EL.BoolTreeLk(rer, [LS.Areg(T.Translate(re))], inp, BS.CannotExit, t);

    assert {:split_here} true;
    // ---- the CHECKED tree (machine A's, shared with B) ----------------------
    WkE.WalkOkEntryNested(re);
    assert EL.PikeLkActionsRec([LS.Areg(T.Translate(re))]) by {
      assert [LS.Areg(T.Translate(re))] == [LS.Areg(T.Translate(re))] + [];
      assert EL.PikeLkActionsRec([]);
      EL.PikeLkActionsRecConsIff(LS.Areg(T.Translate(re)), []);
    }
    var S := PIV.CapIdsInLooks(re);
    M.LkBodyGroupsEqCapIdsInLooks(re);
    assert S == LL.LkBodyGroups(T.Translate(re));
    assert WO.WalkOk([LS.Areg(T.Translate(re))], code, 0, ATR.EaOf(BS.CannotExit));
    AR.CompileToBytecodeActionsRepNested(rer, qm, re);
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
    GateStaticsFromTablesNested(qm, re, crv, ncap, nlook, nquant);
    assert GateStaticsOkNested(qm, re, crv, ncap, nlook, nquant);

    assert {:split_here} true;
    // ---- the two machines on the same checked tree --------------------------
    PSM.InitialPikeInvFullREAtCpNested(rer, qm, re, code, endl, ngroups, str, 0, tstar,
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
    TranslateCinOk(re, G);
    PIV.CapIdsLooksDisjoint(re);
    assert G * S == {};
    var bleaf := L3aCompositeCloseRecG(rer, qm, re, code, endl, ngroups, crv, str, ov, S, tstar, t, inp,
                                       inits, crv.f_main_cdns, result, ncap, nlook, nquant, G);
    // machine A: the VM's best is the checked tree's first leaf
    var pts0 := PT.PikeTreeInitialState(tstar, inp);
    var bestT := PSM.FindMatchSimRENested(rer, qm, re, code, endl, ngroups, str, pts0, inits,
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
      NestedNoCdnLk(ast);
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
      QInCinQ(re);
      TieTransport(rer, re, crv, str, ov, FRD.CinQids(re), S, G, bleaf.value, leaf, best, rp0,
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
      assert LS.IsTree(LES.TheRer(raw), [LS.Areg(LES.SpecRegex(raw))], LC.InitInput(str), LG.Empty, WP.Forward, t);
      assert CM.ThreadRegsWf(synthetic, 2 * R.max_group(R.annotate(raw)) + 2,
                             R.max_lookaround(R.annotate(raw)) + 1,
                             R.max_quant(R.annotate(raw)) + 1) by {
        hide *;
        assert ncap == 2 * R.max_group(R.annotate(raw)) + 2
               && nlook == R.max_lookaround(R.annotate(raw)) + 1
               && nquant == R.max_quant(R.annotate(raw)) + 1;
      }
      assert M.QuantRegsFinal(synthetic);
      assert leaf.1 == PIV.NormGm(PIV.GmOfLive(re, synthetic.capture_regs, synthetic.look_regs,
                                               synthetic.quant_regs));
      assert LT.FirstLeaf(t, LC.InitInput(str)) == Some(leaf);
      assert LES.MatcherSpec(raw, str, LES.Normalize(AI.FFullMatch(raw, str))) by {
        hide *;
        MainExtractionL5Lk(raw, str, t, synthetic, leaf);
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
  // 8. Executable scope conditions (for `SupportedL5Cin`, rung G).
  // =========================================================================

  /** No nulled plus inside any look body (executable). */
  predicate LooksNoNulledPlusX(re: R.regex)
    decreases re
  {
    match re
    case Re_alt(r1, r2) => LooksNoNulledPlusX(r1) && LooksNoNulledPlusX(r2)
    case Re_con(r1, r2) => LooksNoNulledPlusX(r1) && LooksNoNulledPlusX(r2)
    case Re_quant(_, _, _, r1) => LooksNoNulledPlusX(r1)
    case Re_capture(_, r1) => LooksNoNulledPlusX(r1)
    case Re_lookaround(_, _, r1) => NR.NoNulledPlusRE(r1)
    case _ => true
  }

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

  lemma LooksNoNulledPlusXSound(re: R.regex)
    requires LooksNoNulledPlusX(re)
    ensures M.LooksNoNulledPlusRE(re)
    decreases re
  {
    match re
    case Re_alt(r1, r2) => LooksNoNulledPlusXSound(r1); LooksNoNulledPlusXSound(r2);
    case Re_con(r1, r2) => LooksNoNulledPlusXSound(r1); LooksNoNulledPlusXSound(r2);
    case Re_quant(_, _, _, r1) => LooksNoNulledPlusXSound(r1);
    case Re_capture(_, r1) => LooksNoNulledPlusXSound(r1);
    case _ =>
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
}
