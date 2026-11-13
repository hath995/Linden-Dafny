// (G3b) The lookbehind gate-tier lemmas on the plus replay (by the peer session): machine A's
// crossing coverage, readout tie and inner-group absence at a lookbehind body, without NoNulledPlusRE.
// G3b probe (2026-11-12): the gate tier's lookbehind corollaries on the plus match.
module LindenElkBackRowGate {
  import opened Std.Wrappers
  import M = LindenElkMain
  import LBV = LindenLookBehindValue
  import LBK = LindenLookBehindKeystone
  import BV = LindenElkBackValue
  import LW = WarblreRegExpRecord
  import CD = LindenCloseDisc
  import BGM = LindenBackGmMirror
  import R = RegElkRegex
  import RB = Bytecode
  import CP = Compiler
  import AI = ArrayInterp
  import AReg = Array_Regs
  import LOr = Oracle
  import LAnc = Anchors
  import LCdn = Cdn
  import NR = LindenElkNfaRep
  import MIR = LindenElkMirror
  import SD = LindenSpanDuality
  import LC = Chars
  import T = LindenElkTranslate
  import PIV = LindenElkPikeInv
  import CM = LindenElkClockMono
  import AR = LindenElkActionsRep
  import PSM = LindenElkPikeSim
  import LL = LindenElkLookLeaves
  import EL = LindenElkEntryLk
  import OE = LindenElkOracleEntry
  import LTB = LindenElkLookTables
  import TRM = LindenTreeResMirror
  import TML = LindenElkTreeMirrorLk
  import LG = Groups
  import LS = Semantics
  import LT = Tree
  import L = Regex
  import WP = WarblrePrimitives
  import FU = FunctionalUtils
  import FR = LindenElkFlipRev
  import FM = LindenElkFlipMirror
  import FD = LindenElkFlipDisc
  import NUL = LindenElkNullable
  import FO = LindenElkFlipOracle
  import FST = LindenElkFlipStatics
  import FK = LindenElkFlipKeystone
  import OG = LindenElkFlipOracleG
  import MG = LindenElkFlipMirrorG
  import G = LindenElkFlipMirrorG
  import NRC = LindenElkNulledRecon
  import NRR = LindenElkNulledReconRegs
  import RF = LindenElkReconFrame
  import FG = LindenElkFlipGate
  import MA = LindenElkMachineA
  import TB = LindenElkMirrorPlus
  import KG = LindenElkFlipKeystoneG
  import RP = LindenElkMachineABack
  import GG = LindenElkFlipGateG


  /** `LmapOk` reads the look entries only. */
  lemma LmapOkLooksCong(r: R.regex, qm: AR.QMap, qm2: AR.QMap)
    requires T.TransWf(r) && AR.LmapOk(r, qm) && qm2.looks == qm.looks
    ensures AR.LmapOk(r, qm2)
    decreases r
  {
    match r
    case Re_alt(a, b) => LmapOkLooksCong(a, qm, qm2); LmapOkLooksCong(b, qm, qm2);
    case Re_con(a, b) => LmapOkLooksCong(a, qm, qm2); LmapOkLooksCong(b, qm, qm2);
    case Re_quant(_, _, _, a) => LmapOkLooksCong(a, qm, qm2);
    case Re_capture(_, a) => LmapOkLooksCong(a, qm, qm2);
    case Re_lookaround(_, _, a) => LmapOkLooksCong(a, qm, qm2);
    case _ =>
  }

  /** The body's own site table: the caller's look entries and view, `body`'s quantifier entries. The
      band's lookbehind call sites hold `LmapOk(body, qm)` only; the readout wants `QmapOk(body, _)`. */
  lemma RowQm(rer: LW.RegExpRecord, qm: AR.QMap, body: R.regex, str: string, ov: LOr.OracleView)
    returns (qmR: AR.QMap)
    requires T.TransWf(body) && PIV.QuantUnique(body)
    requires qm.ov == ov && AR.LmapOk(body, qm) && OE.OracleColsOk(rer, qm, str)
    ensures qmR.ov == ov && AR.QmapOk(body, qmR) && AR.LmapOk(body, qmR) && OE.OracleColsOk(rer, qmR, str)
  {
    qmR := AR.QMap(M.QmOfRE(body), qm.looks, ov, M.BodiesOfRE(body));
    M.QmOfREEntries(body);
    M.BodiesOfREEntries(body);
    M.QmapOkFromEntries(body, qmR);
    LmapOkLooksCong(body, qm, qmR);
    forall k: int | 0 <= k <= |str| ensures LL.OracleOkAt(rer, qmR, T.InputAt(str, k)) {
      FST.OracleOkAtSubmap(rer, qm, qmR, T.InputAt(str, k));
    }
  }

  /** `KG.LkReplayMatchesSpecLBNestedG` on the PLUS match, no `NoNulledPlusRE(body)`: the passing
      lookbehind gate's `LkResult` (endpoint-swapped) agrees with the fresh backward plus match on
      the body's outer groups. */
  lemma LkReplayMatchesSpecPlusLB(
      rer: LW.RegExpRecord, qm: AR.QMap, body: R.regex, str: string, cp: nat,
      ov: LOr.OracleView, cdns: LCdn.cdns, plus: seq<RB.code>, la: R.lookaround, tlk: LT.Tree,
      gmMain: LG.GroupMap, ncap: int, nlook: int, nquant: int, n: nat)
    requires T.TransWf(body) && NR.NestedFragmentRE(body)
    requires PIV.CapUnique(body) && PIV.QuantUnique(body) && LTB.LookUnique(body)
    requires PSM.SizesOkRE(body, ncap, nlook, nquant)
    requires forall l: nat :: l in LTB.LookIds(body) ==> l < nlook
    requires NRC.NoCdnPlusRE(body) && RF.CinBodiesLookFreeRE(body) && NRR.PlusTableOk(body, plus)
    requires !rer.ignoreCase && !rer.multiline
    requires n == |str| && cp <= n && |ov| == n + 1
    requires qm.ov == ov && AR.LmapOk(body, qm) && OE.OracleColsOk(rer, qm, str)
    requires la.Lookbehind?
    requires tlk == FU.ComputeTr(rer, [LS.Areg(T.Translate(body))], PIV.InpOfCp(str, cp), gmMain, WP.Backward)
    requires M.GmAgreeOn(gmMain, LG.Empty, set g | g in L.DefGroups(T.Translate(body)))
    ensures
      var inp := PIV.InpOfCp(str, cp);
      var bcB := CP.compile_to_bytecode(R.reverse_regex(body));
      var rf := AI.FFindMatchPlus(bcB, body, plus, str, ov, LAnc.Backward, cp,
                                  AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant), 0, cdns).0;
      var S := set g | g in L.DefGroups(T.Translate(body)) && g !in LL.LkBodyGroups(T.Translate(body));
      var lkr := LS.LkResult(T.TrLookaround(la), tlk, gmMain, inp);
      (rf.None? <==> lkr.None?)
      && (rf.Some? ==>
            lkr.Some?
            && M.GmAgreeOn(LBV.SwapGm(lkr.value),
                           PIV.GmOfLive(body, rf.value.capture_regs, rf.value.look_regs, rf.value.quant_regs),
                           S))
  {
    var tr := T.Translate(body);
    var inp := PIV.InpOfCp(str, cp);
    var Sall := set g | g in L.DefGroups(tr);
    var Sin := LL.LkBodyGroups(tr);
    var S := set g | g in L.DefGroups(tr) && g !in Sin;
    var inpF := SD.SwapInput(inp);
    var qmR := RowQm(rer, qm, body, str, ov);
    var Gf, qmF, endlF := RP.BackRowReadout(rer, qmR, body, str, cp, ov, cdns, plus, ncap, nlook, nquant, n);
    var bcB := CP.compile_to_bytecode(R.reverse_regex(body));
    var rr := AI.FFindMatchPlus(bcB, body, plus, str, ov, LAnc.Backward, cp,
                                AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant), 0, cdns).0;
    var t_F := FU.ComputeTr(rer, [LS.Areg(FM.FlipRevL(tr))], inpF, LG.Empty, WP.Forward);
    var rf := LT.FirstLeaf(t_F, inpF);

    // ---- spec side (F2): the backward leaf is the exact MirrorGm-preimage ----
    MIR.ReverseLen(str[..cp]);
    assert n == |inp.pref| + |inp.next|;
    KG.TranslateNoBackref(body);
    FK.TranslateDefGroupsNoDupK(body);
    assert G.OppDir(WP.Backward) == WP.Forward;
    EL.TranslateFragmentNoCdn(body);   // (G5a-1 step 3-L0) NUL.NoCdnPlusL of the translation
    OG.BodyGmTieFlipG(rer, tr, inp, n, WP.Backward);
    var tB := FU.ComputeTr(rer, [LS.Areg(tr)], inp, LG.Empty, WP.Backward);
    var rb := LT.TreeRes(tB, LG.Empty, inp, WP.Backward);
    assert rf == LT.TreeRes(t_F, LG.Empty, inpF, WP.Forward);

    // ---- tlk == tB (gm-independence), and the LkResult fold ----
    OG.NoBackrefNegFreePikeLk(tr);
    EL.ComputeTrGmIndepLkRec(rer, tr, inp, gmMain, WP.Backward);
    assert tlk == tB;
    M.TreeResGmFrameRec(tlk, gmMain, LG.Empty, inp, WP.Backward, Sall);
    var lkr := LS.LkResult(T.TrLookaround(la), tlk, gmMain, inp);
    assert T.TrLookaround(la) == L.LookBehind;
    assert L.Positivity(L.LookBehind) && L.LkDir(L.LookBehind) == WP.Backward;
    assert lkr == (match LT.TreeRes(tlk, gmMain, inp, WP.Backward)
                   case None => None
                   case Some(pair) => Some(pair.1));
    assert LT.TreeRes(tlk, LG.Empty, inp, WP.Backward) == rb;
    assert rb.None? <==> rf.None?;
    assert rr.None? <==> lkr.None?;

    assert {:split_here} true;
    if rr.Some? {
      assert rf.Some? && rb.Some? && lkr.Some?;
      var Gm := PIV.GmOfLive(body, rr.value.capture_regs, rr.value.look_regs, rr.value.quant_regs);
      assert Gm == BGM.RawMirrorGm(Gf, n);
      assert LL.GmAgreeOutside(Gf, rf.value.1, Sin);
      assert rf.value.1 == TRM.MirrorGm(rb.value.1, n) && TRM.GmInBounds(rb.value.1, n);
      LBV.RawMirrorMirrorSwap(rb.value.1, n);
      FK.RawMirrorAgreeOutside(Gf, TRM.MirrorGm(rb.value.1, n), n, Sin);
      assert LL.GmAgreeOutside(Gm, LBV.SwapGm(rb.value.1), Sin);
      assert M.GmAgreeOn(lkr.value, rb.value.1, Sall);
      LBK.SwapGmAgree(lkr.value, rb.value.1, Sall);
      var Lsw := LBV.SwapGm(lkr.value);
      var Rsw := LBV.SwapGm(rb.value.1);
      forall g | g in S
        ensures (g in Lsw <==> g in Gm) && (g in Lsw ==> Lsw[g] == Gm[g])
      {
        assert g in Sall && g !in Sin;
        assert (g in Lsw <==> g in Rsw) && (g in Lsw ==> Lsw[g] == Rsw[g]);
        assert (g in Gm <==> g in Rsw) && (g in Gm ==> Gm[g] == Rsw[g]);
      }
      assert M.GmAgreeOn(Lsw, Gm, S);
    }
  }

  /** `GG.FreshBodyMatchGmOuterLBNested` on the PLUS match: the fresh backward plus match records no
      inner-look group. Through the flip: the keys are the flipped forward plus match's
      (`RP.RowKeysLB` at the mirrored table), which `MA.FreshPlusGmOuter` clears. */
  lemma FreshPlusGmOuterLB(
      rer: LW.RegExpRecord, qm: AR.QMap, body: R.regex, str: string, cp: nat,
      ov: LOr.OracleView, cdns: LCdn.cdns, plus: seq<RB.code>, ncap: int, nlook: int, nquant: int, n: nat)
    requires T.TransWf(body) && NR.NestedFragmentRE(body)
    requires PIV.CapUnique(body) && PIV.QuantUnique(body) && LTB.LookUnique(body)
    requires PSM.SizesOkRE(body, ncap, nlook, nquant)
    requires forall l: nat :: l in LTB.LookIds(body) ==> l < nlook
    requires NRC.NoCdnPlusRE(body) && RF.CinBodiesLookFreeRE(body) && NRR.PlusTableOk(body, plus)
    requires !rer.ignoreCase && !rer.multiline
    requires n == |str| && cp <= n && |ov| == n + 1
    requires qm.ov == ov && AR.LmapOk(body, qm) && OE.OracleColsOk(rer, qm, str)
    ensures
      var bcB := CP.compile_to_bytecode(R.reverse_regex(body));
      var rf := AI.FFindMatchPlus(bcB, body, plus, str, ov, LAnc.Backward, cp,
                                  AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant), 0, cdns).0;
      rf.Some? ==>
        forall g: nat :: g in PIV.CapIdsInLooks(body) ==>
          g !in PIV.GmOfLive(body, rf.value.capture_regs, rf.value.look_regs, rf.value.quant_regs)
  {
    var reF := FST.FXR(body);
    var plusF := TB.MirrorPlus(body, plus);
    TB.PlusTableOkMirror(body, plus);
    var qmR := RowQm(rer, qm, body, str, ov);
    RP.RowKeysLB(rer, qmR, body, str, cp, ov, cdns, plus, plusF, ncap, nlook, nquant, n);
    FST.FXRStructural(body);
    FG.LookUniqueFXR(body);
    TB.NoCdnPlusFXR(body);
    TB.CinBodiesLookFreeFXR(body);
    assert M.RowLAStatics(reF, plusF) by { reveal M.RowLAStatics(); }
    MA.FreshPlusGmOuter(reF, CP.compile_to_bytecode(reF), LC.Reverse(str), n - cp, MIR.MirrorView(ov, n),
                        MIR.SwapAnchorsCdns(cdns), plusF, ncap, nlook, nquant);
    FG.CapIdsInLooksFXR(body);
  }

  /** `GG.GateCrossCoverageLBNested` on the plus match. */
  lemma GateCrossCoveragePlusLB(
      rer: LW.RegExpRecord, qm: AR.QMap, body: R.regex, str: string, cp: nat,
      ov: LOr.OracleView, cdns: LCdn.cdns, plus: seq<RB.code>, la: R.lookaround, tlk: LT.Tree,
      gmMain: LG.GroupMap, ncap: int, nlook: int, nquant: int, n: nat)
    requires T.TransWf(body) && NR.NestedFragmentRE(body)
    requires PIV.CapUnique(body) && PIV.QuantUnique(body) && LTB.LookUnique(body)
    requires PSM.SizesOkRE(body, ncap, nlook, nquant)
    requires forall l: nat :: l in LTB.LookIds(body) ==> l < nlook
    requires NRC.NoCdnPlusRE(body) && RF.CinBodiesLookFreeRE(body)
    requires !rer.ignoreCase && !rer.multiline
    requires NRR.PlusTableOk(body, plus)
    requires n == |str| && cp <= n && |ov| == n + 1
    requires qm.ov == ov && AR.LmapOk(body, qm) && OE.OracleColsOk(rer, qm, str)
    requires la.Lookbehind?
    requires tlk == FU.ComputeTr(rer, [LS.Areg(T.Translate(body))], PIV.InpOfCp(str, cp), gmMain, WP.Backward)
    requires M.GmAgreeOn(gmMain, LG.Empty, set g | g in L.DefGroups(T.Translate(body)))
    ensures
      var inp := PIV.InpOfCp(str, cp);
      var bcB := CP.compile_to_bytecode(R.reverse_regex(body));
      var rf := AI.FFindMatchPlus(bcB, body, plus, str, ov, LAnc.Backward, cp,
                                  AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant), 0, cdns).0;
      var lkr := LS.LkResult(T.TrLookaround(la), tlk, gmMain, inp);
      rf.Some? ==>
        lkr.Some?
        && forall g: nat ::
             g in PIV.CapIds(body)
             && g in PIV.GmOfLive(body, rf.value.capture_regs, rf.value.look_regs, rf.value.quant_regs)
             ==> g in lkr.value
  {
    var inp := PIV.InpOfCp(str, cp);
    var tr := T.Translate(body);
    LkReplayMatchesSpecPlusLB(rer, qm, body, str, cp, ov, cdns, plus, la, tlk, gmMain, ncap, nlook, nquant, n);
    FreshPlusGmOuterLB(rer, qm, body, str, cp, ov, cdns, plus, ncap, nlook, nquant, n);
    M.TranslateDefGroupsEqCapIds(body);
    M.LkBodyGroupsEqCapIdsInLooks(body);
    var bcB := CP.compile_to_bytecode(R.reverse_regex(body));
    var rf := AI.FFindMatchPlus(bcB, body, plus, str, ov, LAnc.Backward, cp,
                                AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant), 0, cdns).0;
    var lkr := LS.LkResult(T.TrLookaround(la), tlk, gmMain, inp);
    var S := set g | g in L.DefGroups(tr) && g !in LL.LkBodyGroups(tr);
    if rf.Some? {
      assert lkr.Some?;
      var Gm := PIV.GmOfLive(body, rf.value.capture_regs, rf.value.look_regs, rf.value.quant_regs);
      var Lsw := LBV.SwapGm(lkr.value);
      assert M.GmAgreeOn(Lsw, Gm, S);
      forall g: nat | g in PIV.CapIds(body) && g in Gm
        ensures g in lkr.value
      {
        assert g !in PIV.CapIdsInLooks(body);
        assert g in (set gx | gx in L.DefGroups(tr));
        assert g !in LL.LkBodyGroups(tr);
        assert g in S;
        assert (g in Lsw <==> g in Gm) && (g in Lsw ==> Lsw[g] == Gm[g]);
        assert g in Lsw;
        assert g in lkr.value;
      }
    }
  }

  /** The fresh PLUS match of a LOOKBEHIND lid, spelled out. */
  lemma FreshPlusLBUnfold(crv: CP.FCompiled, str: string, l: int, lk: AReg.Regs,
                          ov: LOr.OracleView, body: R.regex, ncap: int, nlook: int, nquant: int)
    requires body == M.VBody(crv, l)
    requires 0 <= l < |crv.f_look_types| && crv.f_look_types[l].Lookbehind?
    requires 0 <= l < |crv.f_look_cdns|
    requires AReg.get_cp(lk, l).Some?
    ensures var cp := AReg.get_cp(lk, l).value;
            var bcB := CP.compile_to_bytecode(R.reverse_regex(body));
            M.FreshBodyMatchPlus(crv, str, l, lk, ov, ncap, nlook, nquant)
            == AI.FFindMatchPlus(bcB, body, crv.f_plus_bc, str, ov, LAnc.Backward, cp,
                                 AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant), 0,
                                 crv.f_look_cdns[l]).0
  {
    reveal M.FreshBodyMatchPlus();
    var looktype := crv.f_look_types[l];
    assert AI.capture_direction(looktype) == LAnc.Backward;
    assert CP.capture_regex(looktype, body) == R.reverse_regex(body);
  }

  /** `GG.FreshBodyDirectInBackLeaf` on the plus match. */
  lemma FreshPlusDirectInBackLeaf(
      rer: LW.RegExpRecord, qm: AR.QMap, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
      A0: nat, lk: AReg.Regs, body: R.regex, g2: nat, ncap: int, nlook: int, nquant: int)
    requires T.TransWf(body) && NR.NestedFragmentRE(body)
    requires PIV.CapUnique(body) && PIV.QuantUnique(body) && LTB.LookUnique(body)
    requires PSM.SizesOkRE(body, ncap, nlook, nquant)
    requires forall l: nat :: l in LTB.LookIds(body) ==> l < nlook
    requires NRC.NoCdnPlusRE(body) && RF.CinBodiesLookFreeRE(body)
    requires !rer.ignoreCase && !rer.multiline
    requires NRR.PlusTableOk(body, crv.f_plus_bc)
    requires |ov| == |str| + 1
    requires qm.ov == ov && AR.LmapOk(body, qm) && OE.OracleColsOk(rer, qm, str)
    requires body == M.VBody(crv, A0 as int)
    requires 0 <= (A0 as int) < |crv.f_look_types| && crv.f_look_types[A0 as int].Lookbehind?
    requires 0 <= (A0 as int) < |crv.f_look_cdns|
    requires M.MatchedPosLA(crv, lk, A0 as int)
    requires var cp := AReg.get_cp(lk, A0 as int).value; 0 <= cp <= |str|
    requires g2 in PIV.CapIds(body) && g2 !in PIV.CapIdsInLooks(body)
    requires var rf := M.FreshBodyMatchPlus(crv, str, A0 as int, lk, ov, ncap, nlook, nquant);
             rf.Some?
             && g2 in PIV.GmOfLive(body, rf.value.capture_regs, rf.value.look_regs, rf.value.quant_regs)
    ensures var cp := AReg.get_cp(lk, A0 as int).value;
            var lsub := GG.BackLeafAt(rer, body, str, cp);
            lsub.Some? && g2 in lsub.value
  {
    var l := A0 as int;
    var cpN: nat := AReg.get_cp(lk, l).value;
    var inp := PIV.InpOfCp(str, cpN);
    var cdns := crv.f_look_cdns[l];
    FreshPlusLBUnfold(crv, str, l, lk, ov, body, ncap, nlook, nquant);
    var tlk := FU.ComputeTr(rer, [LS.Areg(T.Translate(body))], inp, LG.Empty, WP.Backward);
    assert M.GmAgreeOn(LG.Empty, LG.Empty, set g | g in L.DefGroups(T.Translate(body)));
    GateCrossCoveragePlusLB(rer, qm, body, str, cpN, ov, cdns, crv.f_plus_bc, R.Lookbehind, tlk, LG.Empty,
                            ncap, nlook, nquant, |str|);
    var lkr := LS.LkResult(T.TrLookaround(R.Lookbehind), tlk, LG.Empty, inp);
    assert lkr.Some? && g2 in lkr.value;
    GG.LkResultIsBackLeaf(rer, body, str, cpN);
    assert GG.BackLeafAt(rer, body, str, cpN) == lkr;
  }

  /** `GG.BackLeafDirectInFresh` on the plus match. */
  lemma BackLeafDirectInFreshPlus(
      rer: LW.RegExpRecord, qm: AR.QMap, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
      A0: nat, lk: AReg.Regs, body: R.regex, g2: nat, ncap: int, nlook: int, nquant: int)
    requires T.TransWf(body) && NR.NestedFragmentRE(body)
    requires PIV.CapUnique(body) && PIV.QuantUnique(body) && LTB.LookUnique(body)
    requires PSM.SizesOkRE(body, ncap, nlook, nquant)
    requires forall l: nat :: l in LTB.LookIds(body) ==> l < nlook
    requires NRC.NoCdnPlusRE(body) && RF.CinBodiesLookFreeRE(body)
    requires !rer.ignoreCase && !rer.multiline
    requires NRR.PlusTableOk(body, crv.f_plus_bc)
    requires |ov| == |str| + 1
    requires qm.ov == ov && AR.LmapOk(body, qm) && OE.OracleColsOk(rer, qm, str)
    requires body == M.VBody(crv, A0 as int)
    requires 0 <= (A0 as int) < |crv.f_look_types| && crv.f_look_types[A0 as int].Lookbehind?
    requires 0 <= (A0 as int) < |crv.f_look_cdns|
    requires M.MatchedPosLA(crv, lk, A0 as int)
    requires var cp := AReg.get_cp(lk, A0 as int).value; 0 <= cp <= |str|
    requires g2 in PIV.CapIds(body) && g2 !in PIV.CapIdsInLooks(body)
    requires M.FreshBodyMatchPlus(crv, str, A0 as int, lk, ov, ncap, nlook, nquant).Some?
    requires var cp := AReg.get_cp(lk, A0 as int).value;
             var lsub := GG.BackLeafAt(rer, body, str, cp);
             lsub.Some? && g2 in lsub.value
    ensures var cp := AReg.get_cp(lk, A0 as int).value;
            var rf := M.FreshBodyMatchPlus(crv, str, A0 as int, lk, ov, ncap, nlook, nquant);
            var gmb := PIV.GmOfLive(body, rf.value.capture_regs, rf.value.look_regs, rf.value.quant_regs);
            g2 in gmb
            && GG.BackLeafAt(rer, body, str, cp).value[g2] == LBV.SwapRange(gmb[g2])
  {
    var l := A0 as int;
    var cpN: nat := AReg.get_cp(lk, l).value;
    var inp := PIV.InpOfCp(str, cpN);
    var cdns := crv.f_look_cdns[l];
    var rf := M.FreshBodyMatchPlus(crv, str, l, lk, ov, ncap, nlook, nquant);
    FreshPlusLBUnfold(crv, str, l, lk, ov, body, ncap, nlook, nquant);
    var tr := T.Translate(body);
    var tlk := FU.ComputeTr(rer, [LS.Areg(tr)], inp, LG.Empty, WP.Backward);
    assert M.GmAgreeOn(LG.Empty, LG.Empty, set g | g in L.DefGroups(tr));
    LkReplayMatchesSpecPlusLB(rer, qm, body, str, cpN, ov, cdns, crv.f_plus_bc, R.Lookbehind, tlk, LG.Empty,
                              ncap, nlook, nquant, |str|);
    var lkr := LS.LkResult(T.TrLookaround(R.Lookbehind), tlk, LG.Empty, inp);
    GG.LkResultIsBackLeaf(rer, body, str, cpN);
    assert GG.BackLeafAt(rer, body, str, cpN) == lkr;
    assert lkr.Some? && g2 in lkr.value;
    var Gm := PIV.GmOfLive(body, rf.value.capture_regs, rf.value.look_regs, rf.value.quant_regs);
    var S := set g | g in L.DefGroups(tr) && g !in LL.LkBodyGroups(tr);
    var Lsw := LBV.SwapGm(lkr.value);
    assert M.GmAgreeOn(Lsw, Gm, S);
    M.TranslateDefGroupsEqCapIds(body);
    M.LkBodyGroupsEqCapIdsInLooks(body);
    assert g2 in (set gx | gx in L.DefGroups(tr)) && g2 !in LL.LkBodyGroups(tr);
    assert g2 in S;
    assert g2 in Lsw && Lsw[g2] == LBV.SwapRange(lkr.value[g2]);
    assert (g2 in Lsw <==> g2 in Gm) && (g2 in Lsw ==> Lsw[g2] == Gm[g2]);
    assert g2 in Gm && LBV.SwapRange(lkr.value[g2]) == Gm[g2];
    LBV.SwapRangeInvol(lkr.value[g2]);
    assert lkr.value[g2] == LBV.SwapRange(Gm[g2]);
  }
}
