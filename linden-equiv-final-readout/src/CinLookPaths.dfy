// §2.5b rung F-c (c6): a lookaround's ANCESTOR path — the captures and
// quantifiers enclosing it, the registers the look-path predicates
// (`NI.LookPathPresent`, `NI.MxAtLidLk`, `NI.LookPathDom`) read — never enters
// a CIN-greedy body when those bodies are look-free. So the reconstruction
// (which moves registers only inside stamped CIN bodies, `RF.FNulledPlusFrameQ`)
// leaves every look-path fact of the winner intact.
module LindenElkCinLookPaths {
  import R = RegElkRegex
  import opened Std.Wrappers
  import CP = Compiler
  import AReg = Array_Regs
  import AI = ArrayInterp
  import LTB = LindenElkLookTables
  import NI = LindenElkNestInv
  import NR = LindenElkNfaRep
  import PIV = LindenElkPikeInv
  import NRR = LindenElkNulledReconRegs
  import RF = LindenElkReconFrame
  import RB = Bytecode
  import LOr = Oracle
  import LAnc = Anchors
  import T = LindenElkTranslate
  import AR = LindenElkActionsRep
  import NRC = LindenElkNulledRecon
  import NRO = LindenElkNulledReconReadout
  import FV = LindenElkFinalVm
  import FRD = LindenElkFinalReadout

  /** The start registers of the captures enclosing `lid`. */
  ghost function AncCapRegs(r: R.regex, lid: nat): set<int>
    requires lid in LTB.LookIds(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => if lid in LTB.LookIds(r1) then AncCapRegs(r1, lid) else AncCapRegs(r2, lid)
    case Re_con(r1, r2) => if lid in LTB.LookIds(r1) then AncCapRegs(r1, lid) else AncCapRegs(r2, lid)
    case Re_quant(_, _, _, r1) => AncCapRegs(r1, lid)
    case Re_capture(cid, r1) => {CP.start_reg(cid)} + AncCapRegs(r1, lid)
    case Re_lookaround(lid0, _, r1) => if lid0 >= 0 && (lid0 as nat) == lid then {} else AncCapRegs(r1, lid)
    case _ => {}
  }

  /** The quantifiers enclosing `lid`. */
  ghost function AncQuants(r: R.regex, lid: nat): set<int>
    requires lid in LTB.LookIds(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => if lid in LTB.LookIds(r1) then AncQuants(r1, lid) else AncQuants(r2, lid)
    case Re_con(r1, r2) => if lid in LTB.LookIds(r1) then AncQuants(r1, lid) else AncQuants(r2, lid)
    case Re_quant(_, qid, _, r1) => {qid as int} + AncQuants(r1, lid)
    case Re_capture(_, r1) => AncQuants(r1, lid)
    case Re_lookaround(lid0, _, r1) => if lid0 >= 0 && (lid0 as nat) == lid then {} else AncQuants(r1, lid)
    case _ => {}
  }

  // ---------------------------------------------------------------------------
  // The look-path predicates read only the ancestors
  // ---------------------------------------------------------------------------

  lemma LookPathFrame(r: R.regex, cc1: seq<int>, qc1: seq<int>, cc2: seq<int>, qc2: seq<int>, mx: int, lid: nat)
    requires lid in LTB.LookIds(r)
    requires forall k :: k in AncCapRegs(r, lid) ==> AI.get_idx(cc1, k) == AI.get_idx(cc2, k)
    requires forall k :: k in AncQuants(r, lid) ==> AI.get_idx(qc1, k) == AI.get_idx(qc2, k)
    ensures NI.LookPathPresent(r, cc1, qc1, mx, lid) == NI.LookPathPresent(r, cc2, qc2, mx, lid)
    ensures NI.MxAtLidLk(r, qc1, mx, lid) == NI.MxAtLidLk(r, qc2, mx, lid)
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      if lid in LTB.LookIds(r1) { LookPathFrame(r1, cc1, qc1, cc2, qc2, mx, lid); }
      else { LookPathFrame(r2, cc1, qc1, cc2, qc2, mx, lid); }
    case Re_con(r1, r2) =>
      if lid in LTB.LookIds(r1) { LookPathFrame(r1, cc1, qc1, cc2, qc2, mx, lid); }
      else { LookPathFrame(r2, cc1, qc1, cc2, qc2, mx, lid); }
    case Re_quant(_, qid, _, r1) =>
      assert (qid as int) in AncQuants(r, lid);
      LookPathFrame(r1, cc1, qc1, cc2, qc2, AI.get_idx(qc1, qid), lid);
    case Re_capture(cid, r1) =>
      assert CP.start_reg(cid) in AncCapRegs(r, lid);
      LookPathFrame(r1, cc1, qc1, cc2, qc2, mx, lid);
    case Re_lookaround(lid0, _, r1) =>
      if !(lid0 >= 0 && (lid0 as nat) == lid) { LookPathFrame(r1, cc1, qc1, cc2, qc2, -1, lid); }
    case _ =>
  }

  lemma LookPathDomFrame(r: R.regex, L: int, qc1: seq<int>, qc2: seq<int>, lid: nat)
    requires lid in LTB.LookIds(r)
    requires forall k :: k in AncQuants(r, lid) ==> AI.get_idx(qc1, k) == AI.get_idx(qc2, k)
    ensures NI.LookPathDom(r, L, qc1, lid) == NI.LookPathDom(r, L, qc2, lid)
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      if lid in LTB.LookIds(r1) { LookPathDomFrame(r1, L, qc1, qc2, lid); } else { LookPathDomFrame(r2, L, qc1, qc2, lid); }
    case Re_con(r1, r2) =>
      if lid in LTB.LookIds(r1) { LookPathDomFrame(r1, L, qc1, qc2, lid); } else { LookPathDomFrame(r2, L, qc1, qc2, lid); }
    case Re_quant(_, qid, _, r1) =>
      assert (qid as int) in AncQuants(r, lid);
      LookPathDomFrame(r1, L, qc1, qc2, lid);
    case Re_capture(_, r1) => LookPathDomFrame(r1, L, qc1, qc2, lid);
    case Re_lookaround(lid0, _, r1) =>
      if !(lid0 >= 0 && (lid0 as nat) == lid) { LookPathDomFrame(r1, L, qc1, qc2, lid); }
    case _ =>
  }

  lemma LookPathPresentLkFrame(r: R.regex, cc1: seq<int>, qc1: seq<int>, cc2: seq<int>, qc2: seq<int>,
                               lc: seq<int>, mx: int, lid: nat)
    requires lid in LTB.LookIds(r)
    requires forall k :: k in AncCapRegs(r, lid) ==> AI.get_idx(cc1, k) == AI.get_idx(cc2, k)
    requires forall k :: k in AncQuants(r, lid) ==> AI.get_idx(qc1, k) == AI.get_idx(qc2, k)
    ensures NI.LookPathPresentLk(r, cc1, lc, qc1, mx, lid) == NI.LookPathPresentLk(r, cc2, lc, qc2, mx, lid)
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      if lid in LTB.LookIds(r1) { LookPathPresentLkFrame(r1, cc1, qc1, cc2, qc2, lc, mx, lid); }
      else { LookPathPresentLkFrame(r2, cc1, qc1, cc2, qc2, lc, mx, lid); }
    case Re_con(r1, r2) =>
      if lid in LTB.LookIds(r1) { LookPathPresentLkFrame(r1, cc1, qc1, cc2, qc2, lc, mx, lid); }
      else { LookPathPresentLkFrame(r2, cc1, qc1, cc2, qc2, lc, mx, lid); }
    case Re_quant(_, qid, _, r1) =>
      assert (qid as int) in AncQuants(r, lid);
      LookPathPresentLkFrame(r1, cc1, qc1, cc2, qc2, lc, AI.get_idx(qc1, qid), lid);
    case Re_capture(cid, r1) =>
      assert CP.start_reg(cid) in AncCapRegs(r, lid);
      LookPathPresentLkFrame(r1, cc1, qc1, cc2, qc2, lc, mx, lid);
    case Re_lookaround(lid0, _, r1) =>
      if !(lid0 >= 0 && (lid0 as nat) == lid) { LookPathPresentLkFrame(r1, cc1, qc1, cc2, qc2, lc, -1, lid); }
    case _ =>
  }

  // ---------------------------------------------------------------------------
  // The ancestors avoid the stamped CIN bodies
  // ---------------------------------------------------------------------------

  lemma AncSub(r: R.regex, lid: nat)
    requires lid in LTB.LookIds(r)
    ensures AncCapRegs(r, lid) <= NRR.CapRegsOf(r) && AncQuants(r, lid) <= NRR.QuantRegsOf(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => if lid in LTB.LookIds(r1) { AncSub(r1, lid); } else { AncSub(r2, lid); }
    case Re_con(r1, r2) => if lid in LTB.LookIds(r1) { AncSub(r1, lid); } else { AncSub(r2, lid); }
    case Re_quant(_, _, _, r1) => AncSub(r1, lid);
    case Re_capture(_, r1) => AncSub(r1, lid);
    case Re_lookaround(lid0, _, r1) => if !(lid0 >= 0 && (lid0 as nat) == lid) { AncSub(r1, lid); }
    case _ =>
  }

  lemma QInCinLeft(r: R.regex, r1: R.regex, r2: R.regex, Q: set<int>)
    requires r == R.Re_alt(r1, r2) || r == R.Re_con(r1, r2)
    requires PIV.QuantUnique(r) && RF.QInCin(r, Q)
    ensures RF.QInCin(r1, Q) && RF.QInCin(r2, Q)
  {
    forall q2: nat | q2 in PIV.QuantIds(r1) && (q2 as int) in Q ensures NRR.QidCinPlus(r1, q2) {
      assert q2 in PIV.QuantIds(r) && NRR.QidCinPlus(r, q2);
    }
    forall q2: nat | q2 in PIV.QuantIds(r2) && (q2 as int) in Q ensures NRR.QidCinPlus(r2, q2) {
      assert q2 !in PIV.QuantIds(r1) by { if q2 in PIV.QuantIds(r1) { assert q2 in PIV.QuantIds(r1) * PIV.QuantIds(r2); } }
      assert q2 in PIV.QuantIds(r) && NRR.QidCinPlus(r, q2);
    }
  }

  /** THE AVOIDANCE: no ancestor of a look is a register of a stamped CIN body. */
  lemma AncAvoidQ(r: R.regex, Q: set<int>, lid: nat)
    requires lid in LTB.LookIds(r)
    requires RF.CinBodiesLookFreeRE(r) && PIV.CapUnique(r) && PIV.QuantUnique(r) && RF.QInCin(r, Q)
    ensures AncCapRegs(r, lid) * RF.CapsQ(r, Q) == {}
    ensures AncQuants(r, lid) * RF.QuantsQ(r, Q) == {}
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      QInCinLeft(r, r1, r2, Q);
      NRR.DisjointRegs(r);
      assert NRR.L1(r) == r1 && NRR.L2(r) == r2;
      RF.QSetsSub(r1, Q); RF.QSetsSub(r2, Q);
      if lid in LTB.LookIds(r1) { AncAvoidQ(r1, Q, lid); AncSub(r1, lid); }
      else { AncAvoidQ(r2, Q, lid); AncSub(r2, lid); }
    case Re_con(r1, r2) =>
      QInCinLeft(r, r1, r2, Q);
      NRR.DisjointRegs(r);
      assert NRR.L1(r) == r1 && NRR.L2(r) == r2;
      RF.QSetsSub(r1, Q); RF.QSetsSub(r2, Q);
      if lid in LTB.LookIds(r1) { AncAvoidQ(r1, Q, lid); AncSub(r1, lid); }
      else { AncAvoidQ(r2, Q, lid); AncSub(r2, lid); }
    case Re_quant(nul, qid, q, body) =>
      assert RF.QInCin(body, Q) by {
        forall q2: nat | q2 in PIV.QuantIds(body) && (q2 as int) in Q ensures NRR.QidCinPlus(body, q2) {
          assert q2 in PIV.QuantIds(r);
          assert !(qid >= 0 && (qid as nat) == q2);
        }
      }
      assert (qid as int) !in Q by {
        if (qid as int) in Q {
          assert qid >= 0 && (qid as nat) in PIV.QuantIds(r);
          assert NRR.QidCinPlus(r, qid as nat);
          NI.LookFreeNoLookIdsN(body);
        }
      }
      AncAvoidQ(body, Q, lid);
      RF.QSetsSub(body, Q);
      NRR.QuantRegsOfChar(body);
      assert (qid as int) !in RF.QuantsQ(body, Q);
    case Re_capture(cid, r1) =>
      assert RF.QInCin(r1, Q) by {
        forall q2: nat | q2 in PIV.QuantIds(r1) && (q2 as int) in Q ensures NRR.QidCinPlus(r1, q2) {
          assert q2 in PIV.QuantIds(r) && NRR.QidCinPlus(r, q2);
        }
      }
      AncAvoidQ(r1, Q, lid);
      RF.QSetsSub(r1, Q);
      NRR.CapRegsOfOwn(r);
      assert NRR.L1(r) == r1;
      assert CP.start_reg(cid) !in RF.CapsQ(r1, Q);
    case Re_lookaround(lid0, _, r1) =>
    case _ =>
  }

  // ---------------------------------------------------------------------------
  // The registers the reconstruction moves lie OUTSIDE every lookaround
  // ---------------------------------------------------------------------------

  lemma QInCinDown(r: R.regex, Q: set<int>)
    requires PIV.QuantUnique(r) && RF.QInCin(r, Q)
    ensures r.Re_alt? || r.Re_con? ==> RF.QInCin(NRR.L1(r), Q) && RF.QInCin(NRR.L2(r), Q)
    ensures r.Re_capture? || r.Re_lookaround? || r.Re_quant? ==> RF.QInCin(NRR.L1(r), Q)
  {
    match r
    case Re_alt(r1, r2) => QInCinLeft(r, r1, r2, Q);
    case Re_con(r1, r2) => QInCinLeft(r, r1, r2, Q);
    case Re_quant(_, qid, _, body) =>
      forall q2: nat | q2 in PIV.QuantIds(body) && (q2 as int) in Q ensures NRR.QidCinPlus(body, q2) {
        assert q2 in PIV.QuantIds(r);
        assert !(qid >= 0 && (qid as nat) == q2);
      }
    case Re_capture(_, r1) =>
      forall q2: nat | q2 in PIV.QuantIds(r1) && (q2 as int) in Q ensures NRR.QidCinPlus(r1, q2) {
        assert q2 in PIV.QuantIds(r) && NRR.QidCinPlus(r, q2);
      }
    case Re_lookaround(_, _, r1) =>
      forall q2: nat | q2 in PIV.QuantIds(r1) && (q2 as int) in Q ensures NRR.QidCinPlus(r1, q2) {
        assert q2 in PIV.QuantIds(r) && NRR.QidCinPlus(r, q2);
      }
    case _ =>
  }

  lemma LookFreeQuantIdsInLooksEmpty(r: R.regex)
    requires NR.LookFreeRE(r)
    ensures PIV.QuantIdsInLooks(r) == {}
    decreases r
  {
    match r
    case Re_alt(r1, r2) => LookFreeQuantIdsInLooksEmpty(r1); LookFreeQuantIdsInLooksEmpty(r2);
    case Re_con(r1, r2) => LookFreeQuantIdsInLooksEmpty(r1); LookFreeQuantIdsInLooksEmpty(r2);
    case Re_quant(_, _, _, r1) => LookFreeQuantIdsInLooksEmpty(r1);
    case Re_capture(_, r1) => LookFreeQuantIdsInLooksEmpty(r1);
    case _ =>
  }

  lemma QsOutside(r: R.regex, Q: set<int>)
    requires RF.CinBodiesLookFreeRE(r) && PIV.CapUnique(r) && PIV.QuantUnique(r) && RF.QInCin(r, Q)
    ensures RF.CapsQ(r, Q) <= PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(r))
    ensures forall k :: k in RF.QuantsQ(r, Q) ==> k >= 0 && (k as nat) in PIV.QuantIdsOutsideLooks(r)
    decreases r
  {
    QInCinDown(r, Q);
    match r
    case Re_alt(r1, r2) =>
      QsOutside(r1, Q); QsOutside(r2, Q);
      PIV.CaptureRegsSetMono(PIV.CapIdsOutsideLooks(r1), PIV.CapIdsOutsideLooks(r));
      PIV.CaptureRegsSetMono(PIV.CapIdsOutsideLooks(r2), PIV.CapIdsOutsideLooks(r));
    case Re_con(r1, r2) =>
      QsOutside(r1, Q); QsOutside(r2, Q);
      PIV.CaptureRegsSetMono(PIV.CapIdsOutsideLooks(r1), PIV.CapIdsOutsideLooks(r));
      PIV.CaptureRegsSetMono(PIV.CapIdsOutsideLooks(r2), PIV.CapIdsOutsideLooks(r));
    case Re_capture(cid, r1) =>
      QsOutside(r1, Q);
      PIV.CaptureRegsSetMono(PIV.CapIdsOutsideLooks(r1), PIV.CapIdsOutsideLooks(r));
    case Re_quant(nul, qid, q, body) =>
      QsOutside(body, Q);
      assert PIV.CapIdsOutsideLooks(r) == PIV.CapIdsOutsideLooks(body);
      if qid in Q {
        assert qid >= 0 && (qid as nat) in PIV.QuantIds(r);
        assert NRR.QidCinPlus(r, qid as nat);
        assert NR.LookFreeRE(body);
        PIV.LookFreeCapIdsInLooksEmpty(body); PIV.CapIdsSplit(body);
        LookFreeQuantIdsInLooksEmpty(body); PIV.QuantIdsSplit(body);
        NRR.CapRegsOfChar(body); NRR.QuantRegsOfChar(body);
        forall k | k in NRR.CapRegsOf(body) ensures k in PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(r)) {
          var c: nat :| c in PIV.CapIds(body) && (k == CP.start_reg(c) || k == CP.end_reg(c));
          assert c in PIV.CapIdsOutsideLooks(r);
          if k == CP.start_reg(c) {
            assert k in (set cid | cid in PIV.CapIdsOutsideLooks(r) :: CP.start_reg(cid));
          } else {
            assert k in (set cid | cid in PIV.CapIdsOutsideLooks(r) :: CP.end_reg(cid));
          }
        }
        forall k | k in NRR.QuantRegsOf(body) ensures k >= 0 && (k as nat) in PIV.QuantIdsOutsideLooks(r) {
          assert (k as nat) in PIV.QuantIdsOutsideLooks(body);
        }
      }
    case Re_lookaround(_, _, _) =>
    case _ =>
  }

  /** A look body's quant ids are inside-look quant ids (`M.LookBodyQuantsIn`'s twin). */
  lemma LookBodyQuantsInL(r: R.regex, lid: nat)
    requires lid in LTB.LookIds(r)
    ensures PIV.QuantIds(NI.LookBodyOfRE(r, lid)) <= PIV.QuantIdsInLooks(r)
    decreases r
  {
    PIV.QuantIdsSplit(r);
    match r
    case Re_alt(r1, r2) =>
      if lid in LTB.LookIds(r1) { LookBodyQuantsInL(r1, lid); } else { LookBodyQuantsInL(r2, lid); }
    case Re_con(r1, r2) =>
      if lid in LTB.LookIds(r1) { LookBodyQuantsInL(r1, lid); } else { LookBodyQuantsInL(r2, lid); }
    case Re_quant(_, _, _, r1) => LookBodyQuantsInL(r1, lid);
    case Re_capture(_, r1) => LookBodyQuantsInL(r1, lid);
    case Re_lookaround(lid0, _, r1) =>
      if !(lid0 >= 0 && (lid0 as nat) == lid) {
        LookBodyQuantsInL(r1, lid);
        PIV.QuantIdsSplit(r1);
      }
  }

  /** THE LOOK-BODY AVOIDANCE: the reconstruction moves no register of any look body. */
  lemma QsAvoidLookBody(r: R.regex, Q: set<int>, lid: nat)
    requires lid in LTB.LookIds(r)
    requires RF.CinBodiesLookFreeRE(r) && PIV.CapUnique(r) && PIV.QuantUnique(r) && RF.QInCin(r, Q)
    ensures RF.CapsQ(r, Q) * PIV.CaptureRegs(NI.LookBodyOfRE(r, lid)) == {}
    ensures forall k :: k in RF.QuantsQ(r, Q) ==> k >= 0 && (k as nat) !in PIV.QuantIds(NI.LookBodyOfRE(r, lid))
  {
    var b := NI.LookBodyOfRE(r, lid);
    QsOutside(r, Q);
    NI.LookBodyCapsIn(r, lid);
    PIV.CaptureRegsIsSet(b);
    PIV.CaptureRegsSetMono(PIV.CapIds(b), PIV.CapIdsInLooks(r));
    PIV.CapIdsLooksDisjoint(r);
    PIV.CaptureRegsSetDisjoint(PIV.CapIdsOutsideLooks(r), PIV.CapIdsInLooks(r));
    LookBodyQuantsInL(r, lid);
    PIV.QuantIdsLooksDisjoint(r);
    forall k | k in RF.QuantsQ(r, Q) ensures k >= 0 && (k as nat) !in PIV.QuantIds(b) {
      assert (k as nat) in PIV.QuantIdsOutsideLooks(r);
      if (k as nat) in PIV.QuantIds(b) { assert (k as nat) in PIV.QuantIdsOutsideLooks(r) * PIV.QuantIdsInLooks(r); }
    }
  }

  // ---------------------------------------------------------------------------
  // The reconstruction's sharp frame at the winner (companion of `FRD.FinalReadout`)
  // ---------------------------------------------------------------------------

  /** `FReconstructPlus(th)` moves only registers of the stamped CIN bodies. */
  lemma FinalReadoutFrame(qm: AR.QMap, ast: R.regex, str: string, th: AI.Thread)
    requires T.TransWf(R.lazy_prefix(ast))
    requires PIV.CapUnique(R.lazy_prefix(ast)) && PIV.QuantUnique(R.lazy_prefix(ast)) && NRC.NoCdnPlusRE(ast)
    requires FV.RegsFinalOk(th, |str|, FRD.CinQids(R.lazy_prefix(ast)))
    requires NRR.WfRegs((th.capture_regs, th.look_regs, th.quant_regs))
    ensures var re := R.lazy_prefix(ast);
            var Q := FRD.CinQids(re);
            var rp := AI.FReconstructPlus(th, ast, CP.FFullCompilation(ast).f_plus_bc, str, qm.ov, LAnc.Forward).0;
            NRR.AgreeOutside((rp.capture_regs, rp.look_regs, rp.quant_regs),
                             (th.capture_regs, th.look_regs, th.quant_regs),
                             RF.CapsQ(re, Q), RF.LooksQ(re, Q), RF.QuantsQ(re, Q))
  {
    var re := R.lazy_prefix(ast);
    var pre := R.Re_quant(R.NonNullable, 0, R.CountedQuant(0, None, false), R.Re_character(R.Dot));
    assert re == R.Re_con(pre, ast);
    var Q := FRD.CinQids(re);
    var rg: NRC.Regs3 := (th.capture_regs, th.look_regs, th.quant_regs);
    var plus := CP.FFullCompilation(ast).f_plus_bc;
    FRD.PlusTableOkFull(ast);
    assert NRC.NoCdnPlusRE(re);
    assert NRR.CapValWf(rg);
    assert NRO.StampsInRange(re, rg, str);
    assert RF.StampsIn(re, rg, Q) by {
      forall q: nat | q in PIV.QuantIds(re) && AI.get_idx(rg.2.a_cp, q) >= 0 ensures (q as int) in Q {
        assert (q as int) in Q;
      }
    }
    RF.FNulledPlusFrameQ(qm, re, rg, plus, str, qm.ov, Q);
    assert AReg.get_cp(rg.2, 0) == None by {
      assert 0 in PIV.QuantIds(re);
      if AI.get_idx(rg.2.a_cp, 0) >= 0 {
        assert (0 as int) in Q;
        var qn: nat :| qn in PIV.QuantIds(re) && NRR.QidCinPlus(re, qn) && qn as int == 0;
        assert qn == 0 && !NRR.QidCinPlus(re, 0);
      }
    }
    FRD.PrefixIdentity(ast, rg, plus, str, qm.ov);
  }
}
