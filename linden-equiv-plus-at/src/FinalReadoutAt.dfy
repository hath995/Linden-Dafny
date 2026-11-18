// (G3a, P3 A1/A2) Ported from the peer session's probe `endgame/probes/FinalReadoutAt.dfy.txt` (16/0).
// the final readout and its sharp frame AT ANY regex `re`
// and ANY plus table that is correct on `re`'s quantifiers. No `lazy_prefix`,
// no `FFullCompilation`: the look replay `FFindMatchPlus(bytecode, body,
// crv.f_plus_bc, ...)` reconstructs with `re := body` and the global table.
//
// Differences from `FRD.FinalReadout` / `CLP.FinalReadoutFrame`:
//  * `PlusTableOkFull(ast)` becomes the premise `NRR.PlusTableOk(re, plus)`;
//    `PlusTableOkLookBody` below derives it for a look body from the table of
//    the enclosing regex (so the main theorem's `PlusTableOkFull` feeds it).
//  * `PrefixIdentity` and the "quant register 0 untouched" clause are gone
//    (prefix-specific); A2's frame is the replacement.
//  * `FV.RegsFinalOk(th, |str|, CinQids(re))` quantifies over ALL quant
//    registers, which is false for a look replay that starts from the main
//    thread's bank. It is replaced by its three local consequences:
//    `StampsFinalAt` (only `re`'s own quantifiers), `NRR.CapValWf`, `FRG.QClkGe`.
module LindenElkFinalReadoutAt {
  import R = RegElkRegex
  import RB = Bytecode
  import CP = Compiler
  import AI = ArrayInterp
  import AReg = Array_Regs
  import LOr = Oracle
  import LAnc = Anchors
  import T = LindenElkTranslate
  import AR = LindenElkActionsRep
  import LTB = LindenElkLookTables
  import PIV = LindenElkPikeInv
  import NI = LindenElkNestInv
  import NRC = LindenElkNulledRecon
  import NRR = LindenElkNulledReconRegs
  import NRO = LindenElkNulledReconReadout
  import SL = LindenElkStampLive
  import PSM = LindenElkPikeSim
  import FRG = LindenElkFinalRegs
  import FRD = LindenElkFinalReadout
  import RF = LindenElkReconFrame
  import ELk = LindenElkEmptyLooks   // (G4b-1) the frame on the empty-path look set
  import CM = LindenElkClockMono
  import TR = LindenElkTreeRep   // (G5b-1) FirstEmptyPathR in StampsLocalS
  import LR = LindenElkLookRecord   // (G4b-2) the look record at the winner

  /** The local half of `FV.RegsFinalOk`: every stamped quantifier OF `re` is a
      CIN-greedy plus of `re`, stamped inside the string. */
  ghost predicate StampsFinalAt(re: R.regex, rg: NRC.Regs3, ub: int) {
    forall q: nat :: q in PIV.QuantIds(re) && AI.get_idx(rg.2.a_cp, q) >= 0 ==>
      AI.get_idx(rg.2.a_cp, q) <= ub && NRR.QidCinPlus(re, q)
  }

  // ---------------------------------------------------------------------------
  // The premise: the plus table of an enclosing regex is correct on a look body
  // ---------------------------------------------------------------------------

  lemma PlusTableOkLookBody(r: R.regex, plus: seq<RB.code>, lid: nat)
    requires PIV.QuantUnique(r) && NRR.PlusTableOk(r, plus)
    requires lid in LTB.LookIds(r)
    ensures NRR.PlusTableOk(NI.LookBodyOfRE(r, lid), plus)
    decreases r
  {
    NRR.PlusTableOkChildren(r, plus);
    match r
    case Re_alt(r1, r2) =>
      if lid in LTB.LookIds(r1) { PlusTableOkLookBody(r1, plus, lid); } else { PlusTableOkLookBody(r2, plus, lid); }
    case Re_con(r1, r2) =>
      if lid in LTB.LookIds(r1) { PlusTableOkLookBody(r1, plus, lid); } else { PlusTableOkLookBody(r2, plus, lid); }
    case Re_quant(_, _, _, r1) => PlusTableOkLookBody(r1, plus, lid);
    case Re_capture(_, r1) => PlusTableOkLookBody(r1, plus, lid);
    case Re_lookaround(lid0, _, r1) =>
      if lid0 >= 0 && (lid0 as nat) == lid { } else { PlusTableOkLookBody(r1, plus, lid); }
  }

  /** (G5a-1 step 4) `PlusTableOkLookBody` for the widened table. */
  lemma PlusTableOkSLookBodyS(r: R.regex, plus: seq<RB.code>, lid: nat)
    requires PIV.QuantUnique(r) && NRR.PlusTableOkS(r, plus)
    requires lid in LTB.LookIds(r)
    ensures NRR.PlusTableOkS(NI.LookBodyOfRE(r, lid), plus)
    decreases r
  {
    NRR.PlusTableOkSChildren(r, plus);
    match r
    case Re_alt(r1, r2) =>
      if lid in LTB.LookIds(r1) { PlusTableOkSLookBodyS(r1, plus, lid); } else { PlusTableOkSLookBodyS(r2, plus, lid); }
    case Re_con(r1, r2) =>
      if lid in LTB.LookIds(r1) { PlusTableOkSLookBodyS(r1, plus, lid); } else { PlusTableOkSLookBodyS(r2, plus, lid); }
    case Re_quant(_, _, _, r1) => PlusTableOkSLookBodyS(r1, plus, lid);
    case Re_capture(_, r1) => PlusTableOkSLookBodyS(r1, plus, lid);
    case Re_lookaround(lid0, _, r1) =>
      if lid0 >= 0 && (lid0 as nat) == lid { } else { PlusTableOkSLookBodyS(r1, plus, lid); }
  }

  /** (G5a-1 step 4) BRIDGE 1: the top's widened table is the rows' CIN table on a look body without a
      CDN-greedy plus (the gate's `NoCdnPlusRE(body)`). Replaces `PlusTableOkLookBody` at the hub. */
  lemma PlusTableOkSLookBody(re: R.regex, plus: seq<RB.code>, lid: nat)
    requires PIV.QuantUnique(re) && NRR.PlusTableOkS(re, plus)
    requires lid in LTB.LookIds(re)
    requires NRC.NoCdnPlusRE(NI.LookBodyOfRE(re, lid))
    ensures NRR.PlusTableOk(NI.LookBodyOfRE(re, lid), plus)
  {
    PlusTableOkSLookBodyS(re, plus, lid);
    NRR.PlusTableOkSNarrow(NI.LookBodyOfRE(re, lid), plus);
  }

  /** `NoCdnPlusRE` passes to look bodies. */
  lemma NoCdnPlusLookBody(r: R.regex, lid: nat)
    requires NRC.NoCdnPlusRE(r) && lid in LTB.LookIds(r)
    ensures NRC.NoCdnPlusRE(NI.LookBodyOfRE(r, lid))
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      if lid in LTB.LookIds(r1) { NoCdnPlusLookBody(r1, lid); } else { NoCdnPlusLookBody(r2, lid); }
    case Re_con(r1, r2) =>
      if lid in LTB.LookIds(r1) { NoCdnPlusLookBody(r1, lid); } else { NoCdnPlusLookBody(r2, lid); }
    case Re_quant(_, _, _, r1) => NoCdnPlusLookBody(r1, lid);
    case Re_capture(_, r1) => NoCdnPlusLookBody(r1, lid);
    case Re_lookaround(lid0, _, r1) =>
      if lid0 >= 0 && (lid0 as nat) == lid { } else { NoCdnPlusLookBody(r1, lid); }
  }

  // ---------------------------------------------------------------------------
  // A1. THE FINAL READOUT at `re`
  //
  // Two forms. `FinalReadoutSubAt` is the one a LOOK REPLAY needs: the replay
  // starts from the main thread's bank, so captures outside `re` are set and
  // `NRO.OnlyCapIdsSet(re, _)` is false; the readout is therefore stated on
  // `NRO.GmSub(re, _, -1)` (the groups of `re` only). `FinalReadoutAt` adds
  // `OnlyCapIdsSet` and returns the original `GmOfLive` / `GmOfLiveR` form.
  // ---------------------------------------------------------------------------

  ghost predicate ReadoutPre(qm: AR.QMap, re: R.regex, plus: seq<RB.code>, str: string, th: AI.Thread,
                             ncap: int, nlook: int, nquant: int) {
    var rg: NRC.Regs3 := (th.capture_regs, th.look_regs, th.quant_regs);
    T.TransWf(re)
    && PIV.CapUnique(re) && PIV.QuantUnique(re)
    && LTB.LookUnique(re) && NRC.NoCdnPlusRE(re)
    && NRR.PlusTableOk(re, plus)
    && AR.QmapOk(re, qm)
    && PSM.BestLiveRE(re, th)
    && StampsFinalAt(re, rg, |str|) && NRR.CapValWf(rg) && FRG.QClkGe(rg)
    && NRR.WfRegs(rg) && NRR.Covers(re, rg)
    && CM.ThreadRegsWf(th, ncap, nlook, nquant)
  }

  /** The statics + register facts rung E consumes, from `ReadoutPre`. */
  lemma ReadoutStamps(qm: AR.QMap, re: R.regex, plus: seq<RB.code>, str: string, th: AI.Thread,
                      ncap: int, nlook: int, nquant: int)
    requires ReadoutPre(qm, re, plus, str, th, ncap, nlook, nquant)
    ensures var rg: NRC.Regs3 := (th.capture_regs, th.look_regs, th.quant_regs);
            NRR.LookUnique(re) && NRR.LookCapsAbsent(re, rg) && NRO.StampsLocal(qm, re, str, rg, -1)
  {
    var rg: NRC.Regs3 := (th.capture_regs, th.look_regs, th.quant_regs);
    FRD.LookUniqueBridge(re);
    assert SL.StampLiveOk(re, rg.0.a_clk, rg.2.a_clk, rg.2.a_cp) && PIV.LooksCapUnset(re, rg.0.a_clk)
      by { reveal PSM.BestLiveRE; }
    assert NRR.LookCapsAbsent(re, rg) by {
      forall c: nat | c in PIV.CapIdsInLooks(re) ensures AI.get_idx(rg.0.a_cp, CP.start_reg(c)) < 0 {
        assert AI.get_idx(rg.0.a_clk, CP.start_reg(c)) < 0;
      }
    }
    assert {:split_here} true;
    forall q: nat | q in PIV.QuantIds(re) && AI.get_idx(rg.2.a_cp, q) >= 0
      ensures NRR.QidCinPlus(re, q)
              && 0 <= AI.get_idx(rg.2.a_cp, q) <= |str|
              && (q as int) in qm.bodies && qm.bodies[q as int] == PIV.QidBody(re, q)
              && (PIV.QChainFresh(re, rg.2.a_clk, -1, q) ==>
                    PIV.PathPresentQ(re, rg.0.a_clk, rg.2.a_clk, -1, q)
                    && NRR.RegsStale(PIV.QidBody(re, q), rg, AI.get_idx(rg.2.a_clk, q)))
    {
      PIV.QmapOkBodyAtQid(re, qm, q);
      SL.StampLiveAt(re, rg.0.a_clk, rg.2.a_clk, rg.2.a_cp, q);
    }
  }

  /** The reconstructed bank is a well-formed thread again; the view is kept. */
  lemma ReadoutBank(qm: AR.QMap, re: R.regex, plus: seq<RB.code>, str: string, th: AI.Thread,
                    ncap: int, nlook: int, nquant: int)
    requires ReadoutPre(qm, re, plus, str, th, ncap, nlook, nquant)
    ensures var rg: NRC.Regs3 := (th.capture_regs, th.look_regs, th.quant_regs);
            var rp := AI.FReconstructPlus(th, re, plus, str, qm.ov, LAnc.Forward);
            rp.1 == qm.ov && rp.0.pc == th.pc && rp.0.exit_allowed == th.exit_allowed
            && (rp.0.capture_regs, rp.0.look_regs, rp.0.quant_regs) == NRO.FP(re, rg, plus, str, qm.ov)
            && CM.ThreadRegsWf(rp.0, ncap, nlook, nquant)
            && (forall k: int :: AI.get_idx(rp.0.quant_regs.a_clk, k) >= -1)
  {
    var rg: NRC.Regs3 := (th.capture_regs, th.look_regs, th.quant_regs);
    assert NRO.StampsInRange(re, rg, str);
    assert FRG.CapValGe(rg) by {
      forall k: int ensures AI.get_idx(rg.0.a_cp, k) >= -1 { assert PIV.CapRegWf(rg.0); }
    }
    NRO.FNulledPlusFrame(qm, re, rg, plus, str, qm.ov);
    FRG.FPValGe(qm, re, rg, plus, str, qm.ov);
    var rg2 := NRO.FP(re, rg, plus, str, qm.ov);
    var rp := AI.FReconstructPlus(th, re, plus, str, qm.ov, LAnc.Forward);
    assert (rp.0.capture_regs, rp.0.look_regs, rp.0.quant_regs) == rg2;
    assert FRG.QClkGe(rg2);
    assert PIV.CapRegWf(rp.0.capture_regs) by {
      assert NRR.WfRegs(rg2) && NRR.CapValWf(rg2) && FRG.CapValGe(rg2);
    }
    assert NRR.Sized3(rg2, rg);
  }

  /** A1, look-replay form: the groups OF `re`, read at `mx = -1`. */
  lemma FinalReadoutSubAt(qm: AR.QMap, re: R.regex, plus: seq<RB.code>, str: string, th: AI.Thread,
                          ncap: int, nlook: int, nquant: int)
    requires ReadoutPre(qm, re, plus, str, th, ncap, nlook, nquant)
    ensures var rg: NRC.Regs3 := (th.capture_regs, th.look_regs, th.quant_regs);
            var rp := AI.FReconstructPlus(th, re, plus, str, qm.ov, LAnc.Forward);
            var rg2: NRC.Regs3 := (rp.0.capture_regs, rp.0.look_regs, rp.0.quant_regs);
            rp.1 == qm.ov && rp.0.pc == th.pc && rp.0.exit_allowed == th.exit_allowed
            && NRO.GmSub(re, rg2, -1)
               == PIV.LiveStampsGm(re, qm, str, rg.2.a_clk, rg.2.a_cp, -1, NRO.GmSub(re, rg, -1))
            && CM.ThreadRegsWf(rp.0, ncap, nlook, nquant)
            && (forall k: int :: AI.get_idx(rp.0.quant_regs.a_clk, k) >= -1)
  {
    var rg: NRC.Regs3 := (th.capture_regs, th.look_regs, th.quant_regs);
    ReadoutStamps(qm, re, plus, str, th, ncap, nlook, nquant);
    ReadoutBank(qm, re, plus, str, th, ncap, nlook, nquant);
    NRO.ReconReadoutSub(qm, re, rg, plus, str, qm.ov, -1);
  }

  /** A1, original form (`FRD.FinalReadout` without the prefix): needs
      `OnlyCapIdsSet`, so it fits a run from a fresh bank. */
  lemma FinalReadoutAt(qm: AR.QMap, re: R.regex, plus: seq<RB.code>, str: string, th: AI.Thread,
                       ncap: int, nlook: int, nquant: int)
    requires ReadoutPre(qm, re, plus, str, th, ncap, nlook, nquant)
    requires NRO.OnlyCapIdsSet(re, (th.capture_regs, th.look_regs, th.quant_regs))
    ensures var rp := AI.FReconstructPlus(th, re, plus, str, qm.ov, LAnc.Forward);
            rp.1 == qm.ov && rp.0.pc == th.pc && rp.0.exit_allowed == th.exit_allowed
            && PIV.GmOfLive(re, rp.0.capture_regs, rp.0.look_regs, rp.0.quant_regs)
               == PIV.GmOfLiveR(re, qm, str, th.capture_regs, th.look_regs, th.quant_regs)
            && CM.ThreadRegsWf(rp.0, ncap, nlook, nquant)
            && (forall k: int :: AI.get_idx(rp.0.quant_regs.a_clk, k) >= -1)
  {
    var rg: NRC.Regs3 := (th.capture_regs, th.look_regs, th.quant_regs);
    ReadoutStamps(qm, re, plus, str, th, ncap, nlook, nquant);
    ReadoutBank(qm, re, plus, str, th, ncap, nlook, nquant);
    NRO.ReconReadout(qm, re, rg, plus, str, qm.ov);
  }

  // ---------------------------------------------------------------------------
  // A2. The reconstruction's sharp frame at `re`
  // ---------------------------------------------------------------------------

  /** The stamped quantifiers of `re`, as raw qids: the `Q` of the frame. */
  ghost function StampedQ(re: R.regex, rg: NRC.Regs3): set<int> {
    set q: nat | q in PIV.QuantIds(re) && AI.get_idx(rg.2.a_cp, q) >= 0 :: q as int
  }

  lemma FinalReadoutFrameAt(qm: AR.QMap, re: R.regex, plus: seq<RB.code>, str: string, th: AI.Thread, Q: set<int>)
    requires PIV.CapUnique(re) && PIV.QuantUnique(re) && NRC.NoCdnPlusRE(re)
    requires NRR.PlusTableOk(re, plus)
    requires var rg: NRC.Regs3 := (th.capture_regs, th.look_regs, th.quant_regs);
             StampsFinalAt(re, rg, |str|) && NRR.CapValWf(rg) && NRR.WfRegs(rg)
             && RF.StampsIn(re, rg, Q)
    ensures var rp := AI.FReconstructPlus(th, re, plus, str, qm.ov, LAnc.Forward).0;
            NRR.AgreeOutside((rp.capture_regs, rp.look_regs, rp.quant_regs),
                             (th.capture_regs, th.look_regs, th.quant_regs),
                             RF.CapsQ(re, Q), RF.LooksQ(re, Q), RF.QuantsQ(re, Q))
  {
    var rg: NRC.Regs3 := (th.capture_regs, th.look_regs, th.quant_regs);
    assert NRO.StampsInRange(re, rg, str);
    RF.FNulledPlusFrameQ(qm, re, rg, plus, str, qm.ov, Q);
  }

  /** The two instances callers use: `Q := CinQids(re)` (the original's shape)
      and the sharpest `Q := StampedQ(re, rg)`. */
  lemma FinalReadoutFrameAtCin(qm: AR.QMap, re: R.regex, plus: seq<RB.code>, str: string, th: AI.Thread)
    requires PIV.CapUnique(re) && PIV.QuantUnique(re) && NRC.NoCdnPlusRE(re)
    requires NRR.PlusTableOk(re, plus)
    requires var rg: NRC.Regs3 := (th.capture_regs, th.look_regs, th.quant_regs);
             StampsFinalAt(re, rg, |str|) && NRR.CapValWf(rg) && NRR.WfRegs(rg)
    ensures var Q := FRD.CinQids(re);
            var rp := AI.FReconstructPlus(th, re, plus, str, qm.ov, LAnc.Forward).0;
            NRR.AgreeOutside((rp.capture_regs, rp.look_regs, rp.quant_regs),
                             (th.capture_regs, th.look_regs, th.quant_regs),
                             RF.CapsQ(re, Q), RF.LooksQ(re, Q), RF.QuantsQ(re, Q))
  {
    var rg: NRC.Regs3 := (th.capture_regs, th.look_regs, th.quant_regs);
    var Q := FRD.CinQids(re);
    assert RF.StampsIn(re, rg, Q) by {
      forall q: nat | q in PIV.QuantIds(re) && AI.get_idx(rg.2.a_cp, q) >= 0 ensures (q as int) in Q {
        assert NRR.QidCinPlus(re, q);
      }
    }
    FinalReadoutFrameAt(qm, re, plus, str, th, Q);
  }

  /** Sanity: the original statements are instances (the local premise follows
      from `FV.RegsFinalOk`), so the leaf can replace them. */
  lemma StampsFinalAtFromRegsFinalOk(re: R.regex, th: AI.Thread, ub: int)
    requires (forall q: int :: AI.get_idx(th.quant_regs.a_cp, q) >= 0 ==>
                AI.get_idx(th.quant_regs.a_cp, q) <= ub && q in FRD.CinQids(re))
    ensures StampsFinalAt(re, (th.capture_regs, th.look_regs, th.quant_regs), ub)
  {
    forall q: nat | q in PIV.QuantIds(re) && AI.get_idx(th.quant_regs.a_cp, q) >= 0
      ensures NRR.QidCinPlus(re, q)
    {
      assert (q as int) in FRD.CinQids(re);
      var qn: nat :| qn in PIV.QuantIds(re) && NRR.QidCinPlus(re, qn) && qn as int == q as int;
      assert qn == q;
    }
  }

  // ===========================================================================
  // (G5b-1) THE S FORMS: a row body that may hold a greedy CDN plus. The scope is `NRC.CdnTopRE`, the
  // stamped pluses are `NRR.QidStampPlus` (CIN or CDN), and a CDN stamp is reconstructed where its body has
  // an empty path, which the simulation carries (`PSM.StampPathOk`, ensured by `PSM.FindMatchSimRECdn`).
  // The twins of the lemmas above over nulled-recon's S readout (as `FRD.FinalReadoutS` at the top).
  // ===========================================================================

  ghost predicate StampsFinalAtS(re: R.regex, rg: NRC.Regs3, ub: int) {
    forall q: nat :: q in PIV.QuantIds(re) && AI.get_idx(rg.2.a_cp, q) >= 0 ==>
      AI.get_idx(rg.2.a_cp, q) <= ub && NRR.QidStampPlus(re, q)
  }

  ghost predicate ReadoutPreS(qm: AR.QMap, re: R.regex, plus: seq<RB.code>, str: string, th: AI.Thread,
                              ncap: int, nlook: int, nquant: int) {
    var rg: NRC.Regs3 := (th.capture_regs, th.look_regs, th.quant_regs);
    T.TransWf(re)
    && PIV.CapUnique(re) && PIV.QuantUnique(re)
    && LTB.LookUnique(re) && NRC.CdnTopRE(re)
    && NRR.PlusTableOkS(re, plus)
    && AR.QmapOk(re, qm)
    && PSM.BestLiveRE(re, th) && PSM.StampPathOk(qm, str, th.quant_regs.a_cp)
    && StampsFinalAtS(re, rg, |str|) && NRR.CapValWf(rg) && FRG.QClkGe(rg)
    && NRR.WfRegs(rg) && NRR.Covers(re, rg)
    && CM.ThreadRegsWf(th, ncap, nlook, nquant)
  }

  lemma ReadoutStampsS(qm: AR.QMap, re: R.regex, plus: seq<RB.code>, str: string, th: AI.Thread,
                       ncap: int, nlook: int, nquant: int)
    requires ReadoutPreS(qm, re, plus, str, th, ncap, nlook, nquant)
    ensures var rg: NRC.Regs3 := (th.capture_regs, th.look_regs, th.quant_regs);
            NRR.LookUnique(re) && NRR.LookCapsAbsent(re, rg) && NRO.StampsLocalS(qm, re, str, rg, -1)
  {
    var rg: NRC.Regs3 := (th.capture_regs, th.look_regs, th.quant_regs);
    FRD.LookUniqueBridge(re);
    assert SL.StampLiveOk(re, rg.0.a_clk, rg.2.a_clk, rg.2.a_cp) && PIV.LooksCapUnset(re, rg.0.a_clk)
      by { reveal PSM.BestLiveRE; }
    assert NRR.LookCapsAbsent(re, rg) by {
      forall c: nat | c in PIV.CapIdsInLooks(re) ensures AI.get_idx(rg.0.a_cp, CP.start_reg(c)) < 0 {
        assert AI.get_idx(rg.0.a_clk, CP.start_reg(c)) < 0;
      }
    }
    assert {:split_here} true;
    forall q: nat | q in PIV.QuantIds(re) && AI.get_idx(rg.2.a_cp, q) >= 0
      ensures NRR.QidStampPlus(re, q)
              && 0 <= AI.get_idx(rg.2.a_cp, q) <= |str|
              && (q as int) in qm.bodies && qm.bodies[q as int] == PIV.QidBody(re, q)
              && T.TransWf(qm.bodies[q as int])
              && TR.FirstEmptyPathR(qm, qm.bodies[q as int], T.InputAt(str, AI.get_idx(rg.2.a_cp, q) as nat)).Some?
              && (PIV.QChainFresh(re, rg.2.a_clk, -1, q) ==>
                    PIV.PathPresentQ(re, rg.0.a_clk, rg.2.a_clk, -1, q)
                    && NRR.RegsStale(PIV.QidBody(re, q), rg, AI.get_idx(rg.2.a_clk, q)))
    {
      PIV.QmapOkBodyAtQid(re, qm, q);
      SL.StampLiveAt(re, rg.0.a_clk, rg.2.a_clk, rg.2.a_cp, q);
      PIV.TransWfQidBodyPIV(re, q);
      var cq: nat := AI.get_idx(rg.2.a_cp, q) as nat;
      PSM.InpOfCpIsInputAt(str, cq);
      assert TR.FirstEmptyPathR(qm, qm.bodies[q as int], T.InputAt(str, cq)).Some? by {
        reveal PSM.StampPathOk();
        assert AI.get_idx(th.quant_regs.a_cp, q as int) == cq;
      }
    }
  }

  lemma ReadoutBankS(qm: AR.QMap, re: R.regex, plus: seq<RB.code>, str: string, th: AI.Thread,
                     ncap: int, nlook: int, nquant: int)
    requires ReadoutPreS(qm, re, plus, str, th, ncap, nlook, nquant)
    ensures var rg: NRC.Regs3 := (th.capture_regs, th.look_regs, th.quant_regs);
            var rp := AI.FReconstructPlus(th, re, plus, str, qm.ov, LAnc.Forward);
            rp.1 == qm.ov && rp.0.pc == th.pc && rp.0.exit_allowed == th.exit_allowed
            && (rp.0.capture_regs, rp.0.look_regs, rp.0.quant_regs) == NRO.FP(re, rg, plus, str, qm.ov)
            && CM.ThreadRegsWf(rp.0, ncap, nlook, nquant)
            && (forall k: int :: AI.get_idx(rp.0.quant_regs.a_clk, k) >= -1)
  {
    var rg: NRC.Regs3 := (th.capture_regs, th.look_regs, th.quant_regs);
    assert NRO.StampsInRangeS(re, rg, str);
    assert FRG.CapValGe(rg) by {
      forall k: int ensures AI.get_idx(rg.0.a_cp, k) >= -1 { assert PIV.CapRegWf(rg.0); }
    }
    NRO.FNulledPlusFrameS(qm, re, rg, plus, str, qm.ov);
    FRG.FPValGeS(qm, re, rg, plus, str, qm.ov);
    var rg2 := NRO.FP(re, rg, plus, str, qm.ov);
    var rp := AI.FReconstructPlus(th, re, plus, str, qm.ov, LAnc.Forward);
    assert (rp.0.capture_regs, rp.0.look_regs, rp.0.quant_regs) == rg2;
    assert FRG.QClkGe(rg2);
    assert PIV.CapRegWf(rp.0.capture_regs) by {
      assert NRR.WfRegs(rg2) && NRR.CapValWf(rg2) && FRG.CapValGe(rg2);
    }
    assert NRR.Sized3(rg2, rg);
  }

  /** A1, look-replay form, S. */
  lemma FinalReadoutSubAtS(qm: AR.QMap, re: R.regex, plus: seq<RB.code>, str: string, th: AI.Thread,
                           ncap: int, nlook: int, nquant: int)
    requires ReadoutPreS(qm, re, plus, str, th, ncap, nlook, nquant)
    ensures var rg: NRC.Regs3 := (th.capture_regs, th.look_regs, th.quant_regs);
            var rp := AI.FReconstructPlus(th, re, plus, str, qm.ov, LAnc.Forward);
            var rg2: NRC.Regs3 := (rp.0.capture_regs, rp.0.look_regs, rp.0.quant_regs);
            rp.1 == qm.ov && rp.0.pc == th.pc && rp.0.exit_allowed == th.exit_allowed
            && NRO.GmSub(re, rg2, -1)
               == PIV.LiveStampsGm(re, qm, str, rg.2.a_clk, rg.2.a_cp, -1, NRO.GmSub(re, rg, -1))
            && CM.ThreadRegsWf(rp.0, ncap, nlook, nquant)
            && (forall k: int :: AI.get_idx(rp.0.quant_regs.a_clk, k) >= -1)
  {
    var rg: NRC.Regs3 := (th.capture_regs, th.look_regs, th.quant_regs);
    ReadoutStampsS(qm, re, plus, str, th, ncap, nlook, nquant);
    ReadoutBankS(qm, re, plus, str, th, ncap, nlook, nquant);
    NRO.ReconReadoutSubS(qm, re, rg, plus, str, qm.ov, -1);
  }

  /** A1, original form, S: a run from a fresh bank. */
  lemma FinalReadoutAtS(qm: AR.QMap, re: R.regex, plus: seq<RB.code>, str: string, th: AI.Thread,
                        ncap: int, nlook: int, nquant: int)
    requires ReadoutPreS(qm, re, plus, str, th, ncap, nlook, nquant)
    requires NRO.OnlyCapIdsSet(re, (th.capture_regs, th.look_regs, th.quant_regs))
    ensures var rp := AI.FReconstructPlus(th, re, plus, str, qm.ov, LAnc.Forward);
            rp.1 == qm.ov && rp.0.pc == th.pc && rp.0.exit_allowed == th.exit_allowed
            && PIV.GmOfLive(re, rp.0.capture_regs, rp.0.look_regs, rp.0.quant_regs)
               == PIV.GmOfLiveR(re, qm, str, th.capture_regs, th.look_regs, th.quant_regs)
            && CM.ThreadRegsWf(rp.0, ncap, nlook, nquant)
            && (forall k: int :: AI.get_idx(rp.0.quant_regs.a_clk, k) >= -1)
  {
    var rg: NRC.Regs3 := (th.capture_regs, th.look_regs, th.quant_regs);
    ReadoutStampsS(qm, re, plus, str, th, ncap, nlook, nquant);
    ReadoutBankS(qm, re, plus, str, th, ncap, nlook, nquant);
    NRO.ReconReadoutS(qm, re, rg, plus, str, qm.ov);
  }

  /** (G4b-2) The look record at the reconstructed winner, per live stamp (`LR.WinnerLookRec`). */
  lemma FinalReadoutLookRecAtS(qm: AR.QMap, re: R.regex, plus: seq<RB.code>, str: string, th: AI.Thread,
                               ncap: int, nlook: int, nquant: int)
    requires ReadoutPreS(qm, re, plus, str, th, ncap, nlook, nquant)
    ensures LR.WinnerLookRec(qm, re, str, th, AI.FReconstructPlus(th, re, plus, str, qm.ov, LAnc.Forward).0)
  {
    ReadoutStampsS(qm, re, plus, str, th, ncap, nlook, nquant);
    var rp := AI.FReconstructPlus(th, re, plus, str, qm.ov, LAnc.Forward).0;
    assert LR.RgOf(rp) == NRO.FP(re, LR.RgOf(th), plus, str, qm.ov);
    LR.WinnerLookRecIntro(qm, re, th, plus, str, qm.ov, rp);
  }

  /** A2, S: the sharp frame for any stamp set `Q` covering the stamps. */
  lemma FinalReadoutFrameAtS(qm: AR.QMap, re: R.regex, plus: seq<RB.code>, str: string, th: AI.Thread, Q: set<int>)
    requires T.TransWf(re) && PIV.CapUnique(re) && PIV.QuantUnique(re) && NRC.CdnTopRE(re)
    requires NRR.PlusTableOkS(re, plus)
    requires var rg: NRC.Regs3 := (th.capture_regs, th.look_regs, th.quant_regs);
             StampsFinalAtS(re, rg, |str|) && NRR.CapValWf(rg) && NRR.WfRegs(rg)
             && RF.StampsIn(re, rg, Q)
    ensures var rp := AI.FReconstructPlus(th, re, plus, str, qm.ov, LAnc.Forward).0;
            NRR.AgreeOutside((rp.capture_regs, rp.look_regs, rp.quant_regs),
                             (th.capture_regs, th.look_regs, th.quant_regs),
                             RF.CapsQ(re, Q), RF.LooksQ(re, Q), RF.QuantsQ(re, Q))
  {
    var rg: NRC.Regs3 := (th.capture_regs, th.look_regs, th.quant_regs);
    assert NRO.StampsInRangeS(re, rg, str);
    RF.FNulledPlusFrameQS(qm, re, rg, plus, str, qm.ov, Q);
  }

  /** (G4b-1) The same frame on the sharper sets: looks outside `ELk.LooksQE`, captures outside `ELk.CapsQO` (the
      reconstruction never writes inside a look body). */
  lemma FinalReadoutFrameAtSE(qm: AR.QMap, re: R.regex, plus: seq<RB.code>, str: string, th: AI.Thread, Q: set<int>)
    requires T.TransWf(re) && PIV.CapUnique(re) && PIV.QuantUnique(re) && NRC.CdnTopRE(re)
    requires NRR.PlusTableOkS(re, plus)
    requires var rg: NRC.Regs3 := (th.capture_regs, th.look_regs, th.quant_regs);
             StampsFinalAtS(re, rg, |str|) && NRR.CapValWf(rg) && NRR.WfRegs(rg)
             && RF.StampsIn(re, rg, Q)
    ensures var rp := AI.FReconstructPlus(th, re, plus, str, qm.ov, LAnc.Forward).0;
            NRR.AgreeOutside((rp.capture_regs, rp.look_regs, rp.quant_regs),
                             (th.capture_regs, th.look_regs, th.quant_regs),
                             ELk.CapsQO(re, Q), ELk.LooksQE(re, Q), RF.QuantsQ(re, Q))
  {
    var rg: NRC.Regs3 := (th.capture_regs, th.look_regs, th.quant_regs);
    assert NRO.StampsInRangeS(re, rg, str);
    ELk.FNulledPlusFrameQSE(qm, re, rg, plus, str, qm.ov, Q);
  }

  /** (G4b-1) At the row winner's STAMPED set: the sharp frame, the stamps are stamp pluses, and (from the live
      stamps) the replay only raised quant clocks. */
  lemma FinalReadoutFrameAtStampE(qm: AR.QMap, re: R.regex, plus: seq<RB.code>, str: string, th: AI.Thread)
    requires T.TransWf(re) && PIV.CapUnique(re) && PIV.QuantUnique(re) && NRC.CdnTopRE(re)
    requires NRR.PlusTableOkS(re, plus)
    requires var rg: NRC.Regs3 := (th.capture_regs, th.look_regs, th.quant_regs);
             StampsFinalAtS(re, rg, |str|) && NRR.CapValWf(rg) && NRR.WfRegs(rg)
    requires SL.StampLiveOk(re, th.capture_regs.a_clk, th.quant_regs.a_clk, th.quant_regs.a_cp)
    ensures var Q := ELk.StampSet(th.quant_regs.a_cp);
            var rp := AI.FReconstructPlus(th, re, plus, str, qm.ov, LAnc.Forward).0;
            NRR.AgreeOutside((rp.capture_regs, rp.look_regs, rp.quant_regs),
                             (th.capture_regs, th.look_regs, th.quant_regs),
                             ELk.CapsQO(re, Q), ELk.LooksQE(re, Q), RF.QuantsQ(re, Q))
            && ELk.QClkGe(rp.quant_regs, th.quant_regs.a_clk)
            && RF.QInStamp(re, Q)
  {
    var rg: NRC.Regs3 := (th.capture_regs, th.look_regs, th.quant_regs);
    var Q := ELk.StampSet(th.quant_regs.a_cp);
    assert RF.StampsIn(re, rg, Q) by {
      forall q: nat | q in PIV.QuantIds(re) && AI.get_idx(rg.2.a_cp, q) >= 0 ensures (q as int) in Q {
        assert 0 <= q < |th.quant_regs.a_cp| && th.quant_regs.a_cp[q] >= 0;
      }
    }
    assert RF.QInStamp(re, Q) by {
      forall q: nat | q in PIV.QuantIds(re) && (q as int) in Q ensures NRR.QidStampPlus(re, q) {
        assert AI.get_idx(rg.2.a_cp, q) >= 0;
      }
    }
    FinalReadoutFrameAtSE(qm, re, plus, str, th, Q);
    assert NRO.StampsInRangeS(re, rg, str);
    ELk.ReplayQuantClkMono(qm, re, rg, plus, str, qm.ov, th.capture_regs.a_clk);
  }

  /** The instance callers use: `Q := StampQids(re)`. */
  lemma FinalReadoutFrameAtStamp(qm: AR.QMap, re: R.regex, plus: seq<RB.code>, str: string, th: AI.Thread)
    requires T.TransWf(re) && PIV.CapUnique(re) && PIV.QuantUnique(re) && NRC.CdnTopRE(re)
    requires NRR.PlusTableOkS(re, plus)
    requires var rg: NRC.Regs3 := (th.capture_regs, th.look_regs, th.quant_regs);
             StampsFinalAtS(re, rg, |str|) && NRR.CapValWf(rg) && NRR.WfRegs(rg)
    ensures var Q := FRD.StampQids(re);
            var rp := AI.FReconstructPlus(th, re, plus, str, qm.ov, LAnc.Forward).0;
            NRR.AgreeOutside((rp.capture_regs, rp.look_regs, rp.quant_regs),
                             (th.capture_regs, th.look_regs, th.quant_regs),
                             RF.CapsQ(re, Q), RF.LooksQ(re, Q), RF.QuantsQ(re, Q))
  {
    var rg: NRC.Regs3 := (th.capture_regs, th.look_regs, th.quant_regs);
    var Q := FRD.StampQids(re);
    assert RF.StampsIn(re, rg, Q) by {
      forall q: nat | q in PIV.QuantIds(re) && AI.get_idx(rg.2.a_cp, q) >= 0 ensures (q as int) in Q {
        assert NRR.QidStampPlus(re, q);
      }
    }
    FinalReadoutFrameAtS(qm, re, plus, str, th, Q);
  }

  lemma StampsFinalAtSFromRegsFinalOk(re: R.regex, th: AI.Thread, ub: int)
    requires (forall q: int :: AI.get_idx(th.quant_regs.a_cp, q) >= 0 ==>
                AI.get_idx(th.quant_regs.a_cp, q) <= ub && q in FRD.StampQids(re))
    ensures StampsFinalAtS(re, (th.capture_regs, th.look_regs, th.quant_regs), ub)
  {
    forall q: nat | q in PIV.QuantIds(re) && AI.get_idx(th.quant_regs.a_cp, q) >= 0
      ensures NRR.QidStampPlus(re, q)
    {
      assert (q as int) in FRD.StampQids(re);
      var qn: nat :| qn in PIV.QuantIds(re) && NRR.QidStampPlus(re, qn) && qn as int == q as int;
      assert qn == q;
    }
  }
}
