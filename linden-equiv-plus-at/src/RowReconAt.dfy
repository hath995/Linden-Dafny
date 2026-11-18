// (G3a commit 3, leaf slice) The lookahead ROW package: what `FReconstructPlus` does to the
// `FFindMatch` result of a look-body replay that started from a FINAL quant bank, plus the small
// glue the look-loop lemmas need (`ClearCps` on `Regs`, the `RAgree` / `RegsAgreeInside` bridge,
// `QidsOf <= QuantIds`).
module LindenElkRowReconAt {
  import opened Std.Wrappers
  import R = RegElkRegex
  import T = LindenElkTranslate
  import RB = Bytecode
  import CP = Compiler
  import AI = ArrayInterp
  import AReg = Array_Regs
  import LOr = Oracle
  import LAnc = Anchors
  import AR = LindenElkActionsRep
  import PIV = LindenElkPikeInv
  import NRC = LindenElkNulledRecon
  import NRR = LindenElkNulledReconRegs
  import NRO = LindenElkNulledReconReadout
  import FRG = LindenElkFinalRegs
  import FRD = LindenElkFinalReadout
  import FV = LindenElkFinalVm
  import RF = LindenElkReconFrame
  import CLP = LindenElkCinLookPaths
  import CM = LindenElkClockMono
  import QCI = LindenElkQuantCpIrrel
  import RA = LindenElkReconAgree
  import FRA = LindenElkFinalReadoutAt
  import LTB = LindenElkLookTables
  import SBk = LindenElkStampBank      // (G5b-3) the bank through the reconstruction
  import ELk = LindenElkEmptyLooks     // (G4b-1) the capture frame outside look bodies

  /** The int image of `body`'s outside-look quantifier ids (`M.QIdsOuter`). */
  ghost function QOuter(body: R.regex): set<int> {
    set q: nat | q in PIV.QuantIdsOutsideLooks(body) :: q as int
  }

  /** The int image of all of `body`'s quantifier ids (`LKC.QIdsInt`). */
  ghost function QAll(body: R.regex): set<int> {
    set q: nat | q in PIV.QuantIds(body) :: q as int
  }

  // ---------------------------------------------------------------------------
  // `ReadoutBank` under the premises its proof uses (no `BestLiveRE`, `QmapOk`, `Covers`)
  // ---------------------------------------------------------------------------

  lemma ReadoutBankLite(qm: AR.QMap, re: R.regex, plus: seq<RB.code>, str: string, th: AI.Thread,
                        ncap: int, nlook: int, nquant: int)
    requires PIV.CapUnique(re) && PIV.QuantUnique(re) && NRC.NoCdnPlusRE(re)
    requires NRR.PlusTableOk(re, plus)
    requires var rg: NRC.Regs3 := (th.capture_regs, th.look_regs, th.quant_regs);
             FRA.StampsFinalAt(re, rg, |str|) && NRR.CapValWf(rg) && FRG.QClkGe(rg)
    requires CM.ThreadRegsWf(th, ncap, nlook, nquant)
    ensures var rg: NRC.Regs3 := (th.capture_regs, th.look_regs, th.quant_regs);
            var rp := AI.FReconstructPlus(th, re, plus, str, qm.ov, LAnc.Forward);
            rp.1 == qm.ov && rp.0.pc == th.pc && rp.0.exit_allowed == th.exit_allowed
            && (rp.0.capture_regs, rp.0.look_regs, rp.0.quant_regs) == NRO.FP(re, rg, plus, str, qm.ov)
            && CM.ThreadRegsWf(rp.0, ncap, nlook, nquant)
            && (forall k: int :: AI.get_idx(rp.0.quant_regs.a_clk, k) >= -1)
  {
    var rg: NRC.Regs3 := (th.capture_regs, th.look_regs, th.quant_regs);
    assert NRR.WfRegs(rg);
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

  // ---------------------------------------------------------------------------
  // THE ROW PACKAGE
  // ---------------------------------------------------------------------------

  /** `th` is the `FFindMatch` result of a lookahead replay of `body` started from a final quant
      bank (so `FV.FFindMatchRegsFinal` gives the global `RegsFinalOk`). Its reconstruction keeps
      the view, the thread shape and the look bank, and moves captures / quants only on `body`'s
      outside-look ids. */
  lemma RowReconAt(qm: AR.QMap, body: R.regex, plus: seq<RB.code>, str: string, th: AI.Thread,
                   ncap: int, nlook: int, nquant: int)
    requires PIV.CapUnique(body) && PIV.QuantUnique(body)
    requires NRC.NoCdnPlusRE(body) && RF.CinBodiesLookFreeRE(body)
    requires NRR.PlusTableOk(body, plus)
    requires FV.RegsFinalOk(th, |str|, FRD.CinQids(body))
    requires CM.ThreadRegsWf(th, ncap, nlook, nquant)
    ensures var rp := AI.FReconstructPlus(th, body, plus, str, qm.ov, LAnc.Forward);
            rp.1 == qm.ov && rp.0.pc == th.pc && rp.0.exit_allowed == th.exit_allowed
            && CM.ThreadRegsWf(rp.0, ncap, nlook, nquant)
            && (forall k: int :: AI.get_idx(rp.0.quant_regs.a_clk, k) >= -1)
            && CM.RegsAgreeOutside(rp.0.capture_regs, th.capture_regs,
                                   PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(body)))
            && rp.0.look_regs == th.look_regs
            && CM.RegsAgreeOutside(rp.0.quant_regs, th.quant_regs, QOuter(body))
  {
    var rg: NRC.Regs3 := (th.capture_regs, th.look_regs, th.quant_regs);
    var Q := FRD.CinQids(body);
    var rp := AI.FReconstructPlus(th, body, plus, str, qm.ov, LAnc.Forward);
    FRA.StampsFinalAtFromRegsFinalOk(body, th, |str|);
    assert NRR.CapValWf(rg) && FRG.QClkGe(rg) && NRR.WfRegs(rg);
    ReadoutBankLite(qm, body, plus, str, th, ncap, nlook, nquant);
    FRA.FinalReadoutFrameAtCin(qm, body, plus, str, th);
    assert RF.QInCin(body, Q);
    RF.LooksQEmpty(body, Q);
    CLP.QsOutside(body, Q);
    assert {:split_here} true;
    assert rp.0.look_regs == th.look_regs by {
      var a := rp.0.look_regs; var b := th.look_regs;
      assert |a.a_cp| == |b.a_cp| && |a.a_clk| == |b.a_clk|;
      forall i | 0 <= i < |a.a_cp| ensures a.a_cp[i] == b.a_cp[i] {
        assert i !in RF.LooksQ(body, Q);
        assert AI.get_idx(a.a_cp, i) == AI.get_idx(b.a_cp, i);
      }
      forall i | 0 <= i < |a.a_clk| ensures a.a_clk[i] == b.a_clk[i] {
        assert i !in RF.LooksQ(body, Q);
        assert AI.get_idx(a.a_clk, i) == AI.get_idx(b.a_clk, i);
      }
      assert a.a_cp == b.a_cp && a.a_clk == b.a_clk;
    }
    assert CM.RegsAgreeOutside(rp.0.quant_regs, th.quant_regs, QOuter(body)) by {
      forall k: int | k !in QOuter(body)
        ensures AI.get_idx(rp.0.quant_regs.a_cp, k) == AI.get_idx(th.quant_regs.a_cp, k)
                && AI.get_idx(rp.0.quant_regs.a_clk, k) == AI.get_idx(th.quant_regs.a_clk, k)
      {
        if k in RF.QuantsQ(body, Q) {
          assert k >= 0 && (k as nat) in PIV.QuantIdsOutsideLooks(body);
          assert k in QOuter(body);
        }
      }
    }
  }

  /** (G5b-1) `ReadoutBankLite` on the S forms: the row body may hold a greedy CDN plus. */
  lemma ReadoutBankLiteS(qm: AR.QMap, re: R.regex, plus: seq<RB.code>, str: string, th: AI.Thread,
                         ncap: int, nlook: int, nquant: int)
    requires T.TransWf(re) && PIV.CapUnique(re) && PIV.QuantUnique(re) && NRC.CdnTopRE(re)
    requires NRR.PlusTableOkS(re, plus)
    requires var rg: NRC.Regs3 := (th.capture_regs, th.look_regs, th.quant_regs);
             FRA.StampsFinalAtS(re, rg, |str|) && NRR.CapValWf(rg) && FRG.QClkGe(rg)
    requires CM.ThreadRegsWf(th, ncap, nlook, nquant)
    ensures var rg: NRC.Regs3 := (th.capture_regs, th.look_regs, th.quant_regs);
            var rp := AI.FReconstructPlus(th, re, plus, str, qm.ov, LAnc.Forward);
            rp.1 == qm.ov && rp.0.pc == th.pc && rp.0.exit_allowed == th.exit_allowed
            && (rp.0.capture_regs, rp.0.look_regs, rp.0.quant_regs) == NRO.FP(re, rg, plus, str, qm.ov)
            && CM.ThreadRegsWf(rp.0, ncap, nlook, nquant)
            && (forall k: int :: AI.get_idx(rp.0.quant_regs.a_clk, k) >= -1)
  {
    var rg: NRC.Regs3 := (th.capture_regs, th.look_regs, th.quant_regs);
    assert NRR.WfRegs(rg);
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

  /** (G5b-1) THE ROW PACKAGE on the S forms: a lookahead row whose body may hold a greedy CDN plus
      (stamped pluses `StampQids`; every stamp body look-free, `RF.StampBodiesLookFreeRE`). */
  lemma RowReconAtS(qm: AR.QMap, body: R.regex, plus: seq<RB.code>, str: string, th: AI.Thread,
                    ncap: int, nlook: int, nquant: int)
    requires T.TransWf(body) && PIV.CapUnique(body) && PIV.QuantUnique(body)
    requires NRC.CdnTopRE(body) && RF.StampBodiesLookFreeRE(body)
    requires NRR.PlusTableOkS(body, plus)
    requires FV.RegsFinalOk(th, |str|, FRD.StampQids(body))
    requires CM.ThreadRegsWf(th, ncap, nlook, nquant)
    ensures var rp := AI.FReconstructPlus(th, body, plus, str, qm.ov, LAnc.Forward);
            rp.1 == qm.ov && rp.0.pc == th.pc && rp.0.exit_allowed == th.exit_allowed
            && CM.ThreadRegsWf(rp.0, ncap, nlook, nquant)
            && (forall k: int :: AI.get_idx(rp.0.quant_regs.a_clk, k) >= -1)
            && CM.RegsAgreeOutside(rp.0.capture_regs, th.capture_regs,
                                   PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(body)))
            && rp.0.look_regs == th.look_regs
            && CM.RegsAgreeOutside(rp.0.quant_regs, th.quant_regs, QOuter(body))
  {
    var rg: NRC.Regs3 := (th.capture_regs, th.look_regs, th.quant_regs);
    var Q := FRD.StampQids(body);
    var rp := AI.FReconstructPlus(th, body, plus, str, qm.ov, LAnc.Forward);
    FRA.StampsFinalAtSFromRegsFinalOk(body, th, |str|);
    assert NRR.CapValWf(rg) && FRG.QClkGe(rg) && NRR.WfRegs(rg);
    ReadoutBankLiteS(qm, body, plus, str, th, ncap, nlook, nquant);
    FRA.FinalReadoutFrameAtStamp(qm, body, plus, str, th);
    assert RF.QInStamp(body, Q);
    RF.LooksQEmptyS(body, Q);
    CLP.QsOutsideS(body, Q);
    assert {:split_here} true;
    assert rp.0.look_regs == th.look_regs by {
      var a := rp.0.look_regs; var b := th.look_regs;
      assert |a.a_cp| == |b.a_cp| && |a.a_clk| == |b.a_clk|;
      forall i | 0 <= i < |a.a_cp| ensures a.a_cp[i] == b.a_cp[i] {
        assert i !in RF.LooksQ(body, Q);
        assert AI.get_idx(a.a_cp, i) == AI.get_idx(b.a_cp, i);
      }
      forall i | 0 <= i < |a.a_clk| ensures a.a_clk[i] == b.a_clk[i] {
        assert i !in RF.LooksQ(body, Q);
        assert AI.get_idx(a.a_clk, i) == AI.get_idx(b.a_clk, i);
      }
      assert a.a_cp == b.a_cp && a.a_clk == b.a_clk;
    }
    assert CM.RegsAgreeOutside(rp.0.quant_regs, th.quant_regs, QOuter(body)) by {
      forall k: int | k !in QOuter(body)
        ensures AI.get_idx(rp.0.quant_regs.a_cp, k) == AI.get_idx(th.quant_regs.a_cp, k)
                && AI.get_idx(rp.0.quant_regs.a_clk, k) == AI.get_idx(th.quant_regs.a_clk, k)
      {
        if k in RF.QuantsQ(body, Q) {
          assert k >= 0 && (k as nat) in PIV.QuantIdsOutsideLooks(body);
          assert k in QOuter(body);
        }
      }
    }
  }

  /** (G5b-3) THE ROW PACKAGE when a stamp body may hold capture-free lookarounds (`RF.StampLooksCapFreeRE`): the
      reconstruction may re-set lids in `LooksQ` (inside a stamp body: their bodies capture nothing), and keeps every
      other look register; the look-bank invariants named by `F` pass through it (`SBk.RowBank`), and so does the quant
      frame (the replay writes only outside-look quants). Replaces `RowReconAtS`'s "the look bank is kept". */
  lemma RowReconAtG4(F: SBk.Flags, qm: AR.QMap, body: R.regex, plus: seq<RB.code>, str: string, th: AI.Thread,
                     ncap: int, nlook: int, nquant: int)
    requires T.TransWf(body) && PIV.CapUnique(body) && PIV.QuantUnique(body) && LTB.LookUnique(body)
    requires RF.StampLooksCapFreeRE(body)
    requires NRR.PlusTableOkS(body, plus)
    requires FV.RegsFinalOk(th, |str|, FRD.StampQids(body))
    requires CM.ThreadRegsWf(th, ncap, nlook, nquant)
    requires (F.o ==> CM.LookCpsOracleTrue(th.look_regs, qm.ov)) && (F.cs ==> CM.LookClkSetWithCp(th.look_regs))
             && (F.ps ==> CM.LookCpSetWithClk(th.look_regs))
    requires F.le ==> F.ub == |str| && CM.LookCpsLE(th.look_regs, |str|)
    ensures var rp := AI.FReconstructPlus(th, body, plus, str, qm.ov, LAnc.Forward);
            rp.1 == qm.ov && rp.0.pc == th.pc && rp.0.exit_allowed == th.exit_allowed
            && CM.ThreadRegsWf(rp.0, ncap, nlook, nquant)
            && (forall k: int :: AI.get_idx(rp.0.quant_regs.a_clk, k) >= -1)
            && CM.RegsAgreeOutside(rp.0.capture_regs, th.capture_regs,
                                   PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(body)))
            && CM.RegsAgreeOutside(rp.0.look_regs, th.look_regs, RF.LooksQ(body, FRD.StampQids(body)))
            && CM.RegsAgreeOutside(rp.0.look_regs, th.look_regs, ELk.LooksQE(body, FRD.StampQids(body)))   // (G4b-1b)
            && CM.RegsAgreeOutside(rp.0.look_regs, th.look_regs, SBk.DirectLidSetRN(body))
            && CM.RegsAgreeOutside(rp.0.quant_regs, th.quant_regs, QOuter(body))
            && (F.o ==> CM.LookCpsOracleTrue(rp.0.look_regs, qm.ov))
            && (F.cs ==> CM.LookClkSetWithCp(rp.0.look_regs))
            && (F.ps ==> CM.LookCpSetWithClk(rp.0.look_regs))
            && (F.le ==> CM.LookCpsLE(rp.0.look_regs, |str|))
  {
    var rg: NRC.Regs3 := (th.capture_regs, th.look_regs, th.quant_regs);
    var Q := FRD.StampQids(body);
    var rp := AI.FReconstructPlus(th, body, plus, str, qm.ov, LAnc.Forward);
    NRC.CdnTopAll(body);
    FRA.StampsFinalAtSFromRegsFinalOk(body, th, |str|);
    assert NRR.CapValWf(rg) && FRG.QClkGe(rg) && NRR.WfRegs(rg);
    ReadoutBankLiteS(qm, body, plus, str, th, ncap, nlook, nquant);
    FRA.FinalReadoutFrameAtStamp(qm, body, plus, str, th);
    assert RF.QInStamp(body, Q);
    assert RF.StampsIn(body, rg, Q) by {
      forall q: nat | q in PIV.QuantIds(body) && AI.get_idx(rg.2.a_cp, q) >= 0 ensures (q as int) in Q {
        assert NRR.QidStampPlus(body, q);
      }
    }
    FRA.FinalReadoutFrameAtSE(qm, body, plus, str, th, Q);   // (G4b-1) captures move only outside look bodies
    ELk.CapsQOOutside(body, Q);
    assert {:split_here} true;
    // the bank: the frames at the direct lids and the outside-look quants, and the selected invariants
    assert F.le ==> CM.LookCpsLE(th.quant_regs, |str|) by {   // the stamps are final: at most |str|
      if F.le {
        forall q: int ensures AI.get_idx(th.quant_regs.a_cp, q) <= |str| {
          if AI.get_idx(th.quant_regs.a_cp, q) >= 0 { assert FV.RegsFinalOk(th, |str|, Q); }
        }
      }
    }
    assert SBk.BankOk(F, th.look_regs, th.quant_regs, qm.ov, th.look_regs, SBk.DirectLidSetRN(body),
                      th.quant_regs, SBk.QOuterRN(body)) by {
      assert CM.RegsAgreeOutside(th.look_regs, th.look_regs, SBk.DirectLidSetRN(body));
      assert CM.RegsAgreeOutside(th.quant_regs, th.quant_regs, SBk.QOuterRN(body));
    }
    SBk.RowBank(F, body, plus, str, th, qm.ov, LAnc.Forward, th.look_regs, th.quant_regs);
    assert SBk.QOuterRN(body) == QOuter(body);
    assert {:split_here} true;
    // the look frame outside LooksQ and the capture frame outside the outside-look captures
    assert CM.RegsAgreeOutside(rp.0.look_regs, th.look_regs, RF.LooksQ(body, Q));
    assert CM.RegsAgreeOutside(rp.0.look_regs, th.look_regs, ELk.LooksQE(body, Q));
    assert CM.RegsAgreeOutside(rp.0.capture_regs, th.capture_regs,
                               PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(body))) by {
      forall k: int | k !in PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(body))
        ensures AI.get_idx(rp.0.capture_regs.a_cp, k) == AI.get_idx(th.capture_regs.a_cp, k)
                && AI.get_idx(rp.0.capture_regs.a_clk, k) == AI.get_idx(th.capture_regs.a_clk, k)
      {
        assert k !in ELk.CapsQO(body, Q);
      }
    }
  }

  /** What the loop keeps: after the row, the bank is final again once `QOuter(body)` is cleared.
      `thq` is the row's incoming (final) quant bank; `th` agrees with it outside `QOuter(body)`
      (`CM.FFindMatchQuantFrame`). */
  lemma RowQuantFinalOutside(th: AI.Thread, rpq: AReg.Regs, qt: AReg.Regs, D: set<int>)
    requires forall k: int :: AI.get_idx(qt.a_cp, k) < 0
    requires CM.RegsAgreeOutside(th.quant_regs, qt, D)
    requires CM.RegsAgreeOutside(rpq, th.quant_regs, D)
    ensures forall k: int :: k !in D ==> AI.get_idx(rpq.a_cp, k) < 0
    ensures CM.RegsAgreeOutside(rpq, qt, D)
  {}

  // ---------------------------------------------------------------------------
  // `ClearCps` on a register bank
  // ---------------------------------------------------------------------------

  /** `q` with the positions on `D` reset to unset; clocks kept. */
  ghost function ClearCps(q: AReg.Regs, D: set<int>): AReg.Regs {
    AReg.ARegs(seq(|q.a_cp|, i requires 0 <= i < |q.a_cp| => if i in D then -1 else q.a_cp[i]), q.a_clk)
  }

  lemma ClearCpsFacts(q: AReg.Regs, D: set<int>)
    ensures var c := ClearCps(q, D);
            |c.a_cp| == |q.a_cp| && c.a_clk == q.a_clk
            && QCI.QAgree(q, c, D)
            && (forall k: int :: k in D ==> AI.get_idx(c.a_cp, k) == -1)
            && (forall k: int :: k !in D ==> AI.get_idx(c.a_cp, k) == AI.get_idx(q.a_cp, k))
  {}

  /** Final outside `D` becomes final after clearing `D`. */
  lemma ClearCpsFinal(q: AReg.Regs, D: set<int>)
    requires forall k: int :: k !in D ==> AI.get_idx(q.a_cp, k) < 0
    ensures forall k: int :: AI.get_idx(ClearCps(q, D).a_cp, k) < 0
    ensures forall k: int :: AI.get_idx(ClearCps(q, D).a_clk, k) == AI.get_idx(q.a_clk, k)
  {
    ClearCpsFacts(q, D);
  }

  // ---------------------------------------------------------------------------
  // Glue for A4 and A5
  // ---------------------------------------------------------------------------

  lemma RAgreeFromInside(a: AReg.Regs, b: AReg.Regs, K: set<int>)
    requires CM.RegsAgreeInside(a, b, K)
    ensures RA.RAgree(a, b, K)
  {
    forall k | 0 <= k < |a.a_cp| && k in K ensures a.a_cp[k] == b.a_cp[k] {
      assert AI.get_idx(a.a_cp, k) == AI.get_idx(b.a_cp, k);
    }
    forall k | 0 <= k < |a.a_clk| && k in K ensures a.a_clk[k] == b.a_clk[k] {
      assert AI.get_idx(a.a_clk, k) == AI.get_idx(b.a_clk, k);
    }
  }

  lemma InsideFromRAgree(a: AReg.Regs, b: AReg.Regs, K: set<int>)
    requires RA.RAgree(a, b, K)
    ensures CM.RegsAgreeInside(a, b, K)
  {}

  /** `QAgree` in the `get_idx` form the loop lemmas speak. */
  lemma QAgreeIdx(q1: AReg.Regs, q2: AReg.Regs, D: set<int>)
    requires QCI.QAgree(q1, q2, D)
    ensures |q1.a_cp| == |q2.a_cp| && |q1.a_clk| == |q2.a_clk|
    ensures forall k: int :: AI.get_idx(q1.a_clk, k) == AI.get_idx(q2.a_clk, k)
    ensures forall k: int :: k !in D ==> AI.get_idx(q1.a_cp, k) == AI.get_idx(q2.a_cp, k)
    ensures CM.RegsAgreeOutside(q1, q2, D)
  {}

  /** The quantifiers `FNulledPlus` reads are outside-look quantifier ids of the regex. */
  lemma QidsOfNonneg(r: R.regex)
    ensures forall q: int :: q in QCI.QidsOf(r) && q >= 0 ==> q in QOuter(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => QidsOfNonneg(r1); QidsOfNonneg(r2);
    case Re_con(r1, r2) => QidsOfNonneg(r1); QidsOfNonneg(r2);
    case Re_quant(_, qid, _, r1) =>
      QidsOfNonneg(r1);
      if qid >= 0 { assert (qid as nat) in PIV.QuantIdsOutsideLooks(r); }
    case Re_capture(_, r1) => QidsOfNonneg(r1);
    case _ =>
  }

  lemma QidsOfSub(r: R.regex)
    requires forall q: int :: q in QCI.QidsOf(r) ==> q >= 0
    ensures QCI.QidsOf(r) <= QOuter(r)
    ensures QOuter(r) <= QAll(r)
  {
    QOuterSubAll(r);
    QidsOfNonneg(r);
  }

  lemma QOuterSubAll(r: R.regex)
    ensures PIV.QuantIdsOutsideLooks(r) <= PIV.QuantIds(r)
    ensures QOuter(r) <= QAll(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => QOuterSubAll(r1); QOuterSubAll(r2);
    case Re_con(r1, r2) => QOuterSubAll(r1); QOuterSubAll(r2);
    case Re_quant(_, _, _, r1) => QOuterSubAll(r1);
    case Re_capture(_, r1) => QOuterSubAll(r1);
    case _ =>
  }
}
