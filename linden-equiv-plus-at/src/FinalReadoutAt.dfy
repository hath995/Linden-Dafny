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
  import CM = LindenElkClockMono

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
}
