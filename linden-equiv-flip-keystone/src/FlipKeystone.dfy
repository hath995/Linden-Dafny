// L5 CAPTURES — BRICKS F4 (MainTheorem half) + F5: THE NESTED LOOKBEHIND
// VALUE KEYSTONE `LkReplayMatchesSpecLBNested`.
//
// The flip-route assembly (L5_HANDOFF.md §5.2), structurally the depth-1
// `LkReplayMatchesSpecLB` (LookBehindKeystone.dfy) with nested ingredients:
//
//   raB (backward replay of compile(reverse_regex(body)) at the ORIGINAL
//        positions/oracle/registers)
//     ==[T2a `BackwardReplayMirrorNested`]== forward run of compile(XRev(body))
//        over Reverse(str) with MirrorView(ov)
//     ==[F0 `FlipCompileToBytecode`]== the SAME bytecode is compile(FXR(body)),
//        the KIND-FLIPPED reversal, whose looks are lookahead-flavoured
//     ==[L4 forward keystone `ReplayCapIsBodyLeafNested` @ FXR(body); its
//        statics from F4, its oracle premise from F3 `MirrorOracleColsOk`]==
//        FirstLeaf(t_F) on SURFACE gids
//     ==[F2 `BackBodyGmTieFlip`, exact MirrorGm]== MirrorGm(FirstLeaf(t_B))
//     ==[`GmOfLiveMirror` + `RawMirrorMirrorSwap`]== SwapGm(backward leaf)
//     ==[`ComputeTrGmIndepLkRec` + `TreeResGmFrameRec`]== the spec `LkResult`.
//
// Conclusion (like the L4 forward nested keystone): None-iff, and on a match
// agreement on the SURFACE gids `DefGroups \ LkBodyGroups`. Inner-look gids
// are the direction-generic recon_inner's business (F6).
/** F4+F5: statics of the flip-reversed body at MainTheorem level, and the
    nested lookbehind value keystone. */
module LindenElkFlipKeystone {
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

  // ===========================================================================
  // Dup-free translated defs from CapUnique (LiftSim-local originals, copied)
  // ===========================================================================

  lemma NoDupAltConK(r1: R.regex, r2: R.regex)
    requires T.TransWf(r1) && T.TransWf(r2)
    requires M.NoDupSeq(L.DefGroups(T.Translate(r1))) && M.NoDupSeq(L.DefGroups(T.Translate(r2)))
    requires (set g | g in L.DefGroups(T.Translate(r1))) == PIV.CapIds(r1)
    requires (set g | g in L.DefGroups(T.Translate(r2))) == PIV.CapIds(r2)
    requires PIV.CapIds(r1) * PIV.CapIds(r2) == {}
    ensures M.NoDupSeq(L.DefGroups(T.Translate(r1)) + L.DefGroups(T.Translate(r2)))
  {
    var a := L.DefGroups(T.Translate(r1));
    var b := L.DefGroups(T.Translate(r2));
    assert forall i, j :: 0 <= i < |a| && 0 <= j < |b| ==> a[i] != b[j] by {
      forall i, j | 0 <= i < |a| && 0 <= j < |b| ensures a[i] != b[j] {
        assert a[i] in (set g | g in a) && a[i] in PIV.CapIds(r1);
        assert b[j] in (set g | g in b) && b[j] in PIV.CapIds(r2);
        if a[i] == b[j] { assert a[i] in PIV.CapIds(r1) * PIV.CapIds(r2); }
      }
    }
    M.NoDupFromDisjoint(a, b);
  }

  lemma TranslateDefGroupsNoDupK(r: R.regex)
    requires T.TransWf(r) && PIV.CapUnique(r)
    ensures M.NoDupSeq(L.DefGroups(T.Translate(r)))
    ensures CD.NoDupG(L.DefGroups(T.Translate(r)))
    decreases r
  {
    match r
    case Re_empty =>
    case Re_character(_) =>
    case Re_anchor(_) =>
    case Re_alt(r1, r2) =>
      TranslateDefGroupsNoDupK(r1); TranslateDefGroupsNoDupK(r2);
      M.TranslateDefGroupsEqCapIds(r1); M.TranslateDefGroupsEqCapIds(r2);
      assert L.DefGroups(T.Translate(r)) == L.DefGroups(T.Translate(r1)) + L.DefGroups(T.Translate(r2));
      NoDupAltConK(r1, r2);
    case Re_con(r1, r2) =>
      TranslateDefGroupsNoDupK(r1); TranslateDefGroupsNoDupK(r2);
      M.TranslateDefGroupsEqCapIds(r1); M.TranslateDefGroupsEqCapIds(r2);
      assert L.DefGroups(T.Translate(r)) == L.DefGroups(T.Translate(r1)) + L.DefGroups(T.Translate(r2));
      NoDupAltConK(r1, r2);
    case Re_quant(_, _, q, r1) =>
      TranslateDefGroupsNoDupK(r1);
      assert L.DefGroups(T.Translate(r)) == L.DefGroups(T.Translate(r1));
    case Re_capture(cid, r1) =>
      TranslateDefGroupsNoDupK(r1);
      M.TranslateDefGroupsEqCapIds(r1);
      assert L.DefGroups(T.Translate(r)) == [cid as nat] + L.DefGroups(T.Translate(r1));
      assert (cid as nat) !in PIV.CapIds(r1);
      assert forall j :: 0 <= j < |L.DefGroups(T.Translate(r1))| ==> L.DefGroups(T.Translate(r1))[j] != cid as nat by {
        forall j | 0 <= j < |L.DefGroups(T.Translate(r1))| ensures L.DefGroups(T.Translate(r1))[j] != cid as nat {
          assert L.DefGroups(T.Translate(r1))[j] in (set g | g in L.DefGroups(T.Translate(r1)));
        }
      }
      M.NoDupPrepend(cid as nat, L.DefGroups(T.Translate(r1)));
    case Re_lookaround(_, lk, r1) =>
      TranslateDefGroupsNoDupK(r1);
      assert L.DefGroups(T.Translate(r)) == L.DefGroups(T.Translate(r1));
  }

  // ===========================================================================
  // The body's lookaround table: entries, scope facts, restriction
  // ===========================================================================

  /** Every entry of the body's own table is in the v1 scope: lookbehind-
      flavoured, `GroupOkLB` body, group-free negative sub-bodies, dup-free
      gids. */
  lemma LmOfBodiesLBOk(body: R.regex)
    requires T.TransWf(body) && FST.LBOnlyLooksRE(body)
    requires NR.NestedFragmentRE(body) && NR.NegLooksLookFreeRE(body) && PIV.CapUnique(body)
    requires NR.NoNulledPlusRE(body)   // §2.5b interim
    ensures forall lid: int :: lid in OE.LmOf(body) ==>
      && (OE.LmOf(body)[lid].0.LookBehind? || OE.LmOf(body)[lid].0.NegLookBehind?)
      && SD.GroupOkLB(OE.LmOf(body)[lid].1)
      && FD.NegBodiesGroupFree(OE.LmOf(body)[lid].1)
      && NUL.NoNulledPlusL(OE.LmOf(body)[lid].1)   // §2.5b interim
      && CD.NoDupG(L.DefGroups(OE.LmOf(body)[lid].1))
    decreases body
  {
    match body
    case Re_alt(r1, r2) => LmOfBodiesLBOk(r1); LmOfBodiesLBOk(r2);
    case Re_con(r1, r2) => LmOfBodiesLBOk(r1); LmOfBodiesLBOk(r2);
    case Re_quant(_, _, _, r1) => LmOfBodiesLBOk(r1);
    case Re_capture(_, r1) => LmOfBodiesLBOk(r1);
    case Re_lookaround(lid0, la, r1) =>
      LmOfBodiesLBOk(r1);
      FST.TranslateGroupOkLB(r1);
      FST.TranslateNegBodiesGroupFree(r1);
      NUL.TransNoNulledPlus(r1);   // §2.5b interim
      TranslateDefGroupsNoDupK(r1);
      assert OE.LmOf(body) == OE.LmOf(r1)[lid0 := (T.TrLookaround(la), T.Translate(r1))];
    case _ =>
  }

  /** A table correct for `body` agrees with `body`'s own table on the latter's
      whole domain. */
  lemma LmapOkEntriesMatchLmOf(body: R.regex, qm: AR.QMap)
    requires T.TransWf(body) && AR.LmapOk(body, qm)
    ensures forall lid: int :: lid in OE.LmOf(body) ==>
              lid in qm.looks && qm.looks[lid] == OE.LmOf(body)[lid]
    decreases body
  {
    match body
    case Re_alt(r1, r2) => LmapOkEntriesMatchLmOf(r1, qm); LmapOkEntriesMatchLmOf(r2, qm);
    case Re_con(r1, r2) => LmapOkEntriesMatchLmOf(r1, qm); LmapOkEntriesMatchLmOf(r2, qm);
    case Re_quant(_, _, _, r1) => LmapOkEntriesMatchLmOf(r1, qm);
    case Re_capture(_, r1) => LmapOkEntriesMatchLmOf(r1, qm);
    case Re_lookaround(lid0, la, r1) =>
      LmapOkEntriesMatchLmOf(r1, qm);
      assert OE.LmOf(body) == OE.LmOf(r1)[lid0 := (T.TrLookaround(la), T.Translate(r1))];
    case _ =>
  }

  // ===========================================================================
  // F4 (M half): the statics package for the flip-reversed body
  // ===========================================================================

  /** All of `StaticOkNestedRE(qm'', FXR(body), compile(FXR(body)), endl')` +
      `SizesOkRE` + `NegLooksLookFreeRE`, from the body's structural facts.
      `qm''` carries the canonical quant map, the FLIPPED image of the body's
      own look table (so F3 applies by construction), and the caller's view. */
  lemma FlipXRevStaticOkNested(body: R.regex, someView: LOr.OracleView,
                               ncap: int, nlook: int, nquant: int)
      returns (qm'': AR.QMap, endl': nat)
    requires T.TransWf(body) && NR.NestedFragmentRE(body) && NR.NegLooksLookFreeRE(body)
    requires PIV.CapUnique(body) && PIV.QuantUnique(body) && LTB.LookUnique(body)
    requires PSM.SizesOkRE(body, ncap, nlook, nquant)
    ensures PSM.StaticOkNestedRE(qm'', FST.FXR(body), CP.compile_to_bytecode(FST.FXR(body)), endl')
    ensures PSM.SizesOkRE(FST.FXR(body), ncap, nlook, nquant)
    ensures NR.NegLooksLookFreeRE(FST.FXR(body))
    ensures qm''.ov == someView && qm''.looks == FST.FlipLooksMap(OE.LmOf(body))
  {
    var re' := FST.FXR(body);
    FST.FXRStructural(body);
    qm'' := AR.QMap(M.QmOfRE(re'), FST.FlipLooksMap(OE.LmOf(body)), someView);
    M.QmOfREEntries(re');
    M.QmapOkFromEntries(re', qm'');
    var qmB := AR.QMap(map[], OE.LmOf(body), someView);
    OE.LmapOkOfLmOf(body, qmB);
    FST.LmapOkFlipXRev(body, qmB, qm'');
    endl' := FST.FXRCompileFacts(body);
  }

  // ===========================================================================
  // F5 engine half: raB ~ the flipped forward tree's first leaf (surface)
  // ===========================================================================

  /** The nested twin of `LBEngineLeaf`: the backward replay `raB` matches
      (None-iff) the flip-reversed body's forward first leaf, and the FRESH
      forward run's readout agrees with that leaf OUTSIDE the inner-look gids.
      Oracle correctness for the flipped table comes from F3 (the site's
      whole-string column correctness, restricted to the body's lids). */
  lemma LBEngineLeafFlip(
      rer: LW.RegExpRecord, qm: AR.QMap, body: R.regex, str: string, cp: nat,
      cap: AReg.Regs, lk: AReg.Regs, qt: AReg.Regs, ov: LOr.OracleView,
      cdns: LCdn.cdns, ncap: int, nlook: int, nquant: int, n: nat)
    requires T.TransWf(body) && NR.NestedFragmentRE(body) && NR.NegLooksLookFreeRE(body)
    requires NR.NoNulledPlusRE(body)   // §2.5b interim: all stamps false
    requires FST.LBOnlyLooksRE(body)
    requires PIV.CapUnique(body) && PIV.QuantUnique(body) && LTB.LookUnique(body)
    requires PSM.SizesOkRE(body, ncap, nlook, nquant)
    requires !rer.ignoreCase && !rer.multiline
    requires n == |str| && cp <= n && |ov| == n + 1
    requires qm.ov == ov && AR.LmapOk(body, qm) && OE.OracleColsOk(rer, qm, str)
    requires CM.RegsAgreeInside(cap, AReg.init_regs(ncap), PIV.CaptureRegs(body))
    requires |qt.a_cp| == nquant && |qt.a_clk| == nquant
    ensures
      var rstr := LC.Reverse(str);
      var mcp := MIR.Mirror(cp, n);
      var ctxcF := AI.cp_context(mcp, rstr, LAnc.Forward);
      var bcF := CP.compile_to_bytecode(FST.FXR(body));
      var inpF := SD.SwapInput(PIV.InpOfCp(str, cp));
      var t_F := FU.ComputeTr(rer, [LS.Areg(FM.FlipRevL(T.Translate(body)))], inpF, LG.Empty, WP.Forward);
      var rfF := AI.FFindMatch(bcF, rstr,
                   AI.FInitState(bcF, mcp, AReg.init_regs(ncap), AReg.init_regs(nlook),
                                 AReg.init_regs(nquant), 0, ctxcF),
                   MIR.MirrorView(ov, n), LAnc.Forward, MIR.SwapAnchorsCdns(cdns)).0;
      var bcB := CP.compile_to_bytecode(R.reverse_regex(body));
      var ctxcB := AI.cp_context(cp, str, LAnc.Backward);
      var raB := AI.FFindMatch(bcB, str, AI.FInitState(bcB, cp, cap, lk, qt, 0, ctxcB),
                               ov, LAnc.Backward, cdns).0;
      |rstr| == n
      && (raB.None? <==> LT.FirstLeaf(t_F, inpF).None?)
      && (raB.Some? ==>
            rfF.Some? && LT.FirstLeaf(t_F, inpF).Some?
            && LL.GmAgreeOutside(
                 PIV.GmOfLive(body, rfF.value.capture_regs, rfF.value.look_regs, rfF.value.quant_regs),
                 LT.FirstLeaf(t_F, inpF).value.1,
                 LL.LkBodyGroups(T.Translate(body)))
            && (forall k :: AI.get_idx(AReg.as_arrays(rfF.value.capture_regs).0, k) <= n))
  {
    var tr := T.Translate(body);
    var re' := FST.FXR(body);
    MIR.ReverseLen(str);
    var rstr := LC.Reverse(str);
    var mcp := MIR.Mirror(cp, n);
    var mcpN: nat := n - cp;
    assert mcp == mcpN as int && 0 <= mcp <= n && |rstr| == n;
    var ov' := MIR.MirrorView(ov, n);
    var cdns' := MIR.SwapAnchorsCdns(cdns);
    var bcF := CP.compile_to_bytecode(re');
    var ctxcF := AI.cp_context(mcp, rstr, LAnc.Forward);
    var inpF := PIV.InpOfCp(rstr, mcpN);
    LBV.InpOfCpSwap(str, cp, n);
    assert inpF == SD.SwapInput(PIV.InpOfCp(str, cp));

    // ---- statics + the flipped table ----
    var qm'', endl' := FlipXRevStaticOkNested(body, ov', ncap, nlook, nquant);

    // ---- oracle for the flipped table: F3 on the body-restricted site table ----
    var qmB := AR.QMap(map[], OE.LmOf(body), ov);
    OE.LmapOkOfLmOf(body, qmB);
    LmapOkEntriesMatchLmOf(body, qm);
    assert OE.OracleColsOk(rer, qmB, str) by {
      forall k: int | 0 <= k <= |str| ensures LL.OracleOkAt(rer, qmB, T.InputAt(str, k)) {
        FST.OracleOkAtSubmap(rer, qm, qmB, T.InputAt(str, k));
      }
    }
    LmOfBodiesLBOk(body);
    assert FO.QmBodiesLBOk(qmB);
    FST.FlipLooksMapTie(qmB, qm'');
    assert |qmB.ov| == |str| + 1 && qm''.ov == MIR.MirrorView(qmB.ov, |str|);
    FO.MirrorOracleColsOk(rer, qmB, qm'', str);
    FO.ColsOkToSuffix(rer, qm'', rstr, mcpN);
    assert PIV.InpOfCp(rstr, mcpN) == T.InputAt(rstr, mcpN);
    assert LL.OracleOkSuffix(rer, qm'', PIV.InpOfCp(rstr, mcpN));

    // ---- mirrored engine caps are fresh on re''s cap regs ----
    FST.XRevIsRevRENested(body);
    LBV.CapIdsRevRE(body);
    FST.FlipCapIds(FST.XRV(body));
    assert PIV.CapIds(re') == PIV.CapIds(body);
    assert PIV.CaptureRegs(re') == PIV.CaptureRegs(body);
    LBK.MirrorRegsAgreeInit(cap, ncap, PIV.CaptureRegs(body), n);
    assert CM.RegsAgreeInside(MIR.MirrorRegs(cap, n), AReg.init_regs(ncap), PIV.CaptureRegs(re'));
    assert |MIR.MirrorRegs(qt, n).a_cp| == nquant && |MIR.MirrorRegs(qt, n).a_clk| == nquant;

    // ---- fresh forward run rfF and its capture upper bound ----
    var initsFresh := AI.FInitState(bcF, mcp, AReg.init_regs(ncap), AReg.init_regs(nlook),
                                    AReg.init_regs(nquant), 0, ctxcF);
    var rfF := AI.FFindMatch(bcF, rstr, initsFresh, ov', LAnc.Forward, cdns').0;
    assert ctxcF.nextchar == AI.get_char(rstr, mcp);
    CM.FInitStateCapsLE(bcF, mcp, ncap, nlook, nquant, 0, ctxcF);
    LBK.FFindMatchCapsLE(bcF, rstr, initsFresh, ov', cdns');

    // ---- the L4 forward keystone at the FLIPPED body ----
    var bestT := M.ReplayCapIsBodyLeafNested(rer, qm'', re', bcF, endl', 0, rstr, mcpN,
                   MIR.MirrorRegs(cap, n), MIR.MirrorRegs(lk, n), MIR.MirrorRegs(qt, n),
                   ov', cdns', ncap, nlook, nquant);
    FST.TranslateFlipXRev(body);
    assert T.Translate(re') == FM.FlipRevL(tr);
    var t_F := FU.ComputeTr(rer, [LS.Areg(FM.FlipRevL(tr))], inpF, LG.Empty, WP.Forward);
    var raF := AI.FFindMatch(bcF, rstr,
                 AI.FInitState(bcF, mcp, MIR.MirrorRegs(cap, n), MIR.MirrorRegs(lk, n),
                               MIR.MirrorRegs(qt, n), 0, ctxcF),
                 ov', LAnc.Forward, cdns').0;
    FST.LkBodyGroupsFlipL(SD.RevL(tr));
    TML.LkBodyGroupsRevL(tr);
    assert LL.LkBodyGroups(T.Translate(re')) == LL.LkBodyGroups(tr);
    assert bestT.None? <==> LT.FirstLeaf(t_F, inpF).None?;
    assert raF.None? <==> bestT.None?;

    // ---- T2a: the actual backward replay ~ raF ----
    BV.BackwardReplayMirrorNested(body, str, cp, cap, lk, qt, ov, cdns, n);
    FR.FlipCompileToBytecode(FST.XRV(body));
    assert bcF == CP.compile_to_bytecode(FST.XRV(body));
    var bcB := CP.compile_to_bytecode(R.reverse_regex(body));
    var ctxcB := AI.cp_context(cp, str, LAnc.Backward);
    var raB := AI.FFindMatch(bcB, str, AI.FInitState(bcB, cp, cap, lk, qt, 0, ctxcB),
                             ov, LAnc.Backward, cdns).0;
    assert raB.None? <==> raF.None?;

    if raB.Some? {
      assert raF.Some? && bestT.Some? && rfF.Some? && LT.FirstLeaf(t_F, inpF).Some?;
      assert bestT.value.1
          == PIV.GmOfLive(re', rfF.value.capture_regs, rfF.value.look_regs, rfF.value.quant_regs);
      FST.GmOfLiveFXR(body, rfF.value.capture_regs, rfF.value.look_regs, rfF.value.quant_regs);
      assert LL.GmAgreeOutside(
               PIV.GmOfLive(body, rfF.value.capture_regs, rfF.value.look_regs, rfF.value.quant_regs),
               LT.FirstLeaf(t_F, inpF).value.1, LL.LkBodyGroups(tr));
      assert AReg.as_arrays(rfF.value.capture_regs).0 == rfF.value.capture_regs.a_cp;
    }
  }

  // ===========================================================================
  // Readout mirror plumbing
  // ===========================================================================

  /** The raw readout mirror is pointwise, so outside-`S` agreement survives it. */
  lemma RawMirrorAgreeOutside(G: LG.GroupMap, H: LG.GroupMap, n: nat, S: set<LG.GroupId>)
    requires BGM.GmLeN(G, n) && BGM.GmLeN(H, n)
    requires LL.GmAgreeOutside(G, H, S)
    ensures LL.GmAgreeOutside(BGM.RawMirrorGm(G, n), BGM.RawMirrorGm(H, n), S)
  {
    forall g | g !in S
      ensures (g in BGM.RawMirrorGm(G, n) <==> g in BGM.RawMirrorGm(H, n))
           && (g in BGM.RawMirrorGm(G, n) ==> BGM.RawMirrorGm(G, n)[g] == BGM.RawMirrorGm(H, n)[g])
    {}
  }

  // ===========================================================================
  // F5: THE KEYSTONE
  // ===========================================================================

  /** THE NESTED LOOKBEHIND VALUE KEYSTONE. For a positive lookbehind whose
      body is in the v1 nested scope (lookbehind-only nesting), the engine's
      backward replay `raB` matches (None-iff) the spec `LkResult`, and on a
      match the endpoint-swapped spec value agrees with the FRESH mirrored
      run's readout on the SURFACE gids `DefGroups \ LkBodyGroups`. */
  lemma LkReplayMatchesSpecLBNested(
      rer: LW.RegExpRecord, qm: AR.QMap, body: R.regex, str: string, cp: nat,
      cap: AReg.Regs, lk: AReg.Regs, qt: AReg.Regs, ov: LOr.OracleView,
      cdns: LCdn.cdns, la: R.lookaround, tlk: LT.Tree, gmMain: LG.GroupMap,
      ncap: int, nlook: int, nquant: int, n: nat)
    requires T.TransWf(body) && NR.NestedFragmentRE(body) && NR.NegLooksLookFreeRE(body)
    requires NR.NoNulledPlusRE(body)   // §2.5b interim: all stamps false
    requires FST.LBOnlyLooksRE(body)
    requires PIV.CapUnique(body) && PIV.QuantUnique(body) && LTB.LookUnique(body)
    requires PSM.SizesOkRE(body, ncap, nlook, nquant)
    requires !rer.ignoreCase && !rer.multiline
    requires n == |str| && cp <= n && |ov| == n + 1
    requires qm.ov == ov && AR.LmapOk(body, qm) && OE.OracleColsOk(rer, qm, str)
    requires CM.RegsAgreeInside(cap, AReg.init_regs(ncap), PIV.CaptureRegs(body))
    requires |qt.a_cp| == nquant && |qt.a_clk| == nquant
    requires la.Lookbehind?
    requires tlk == FU.ComputeTr(rer, [LS.Areg(T.Translate(body))], PIV.InpOfCp(str, cp), gmMain, WP.Backward)
    requires M.GmAgreeOn(gmMain, LG.Empty, set g | g in L.DefGroups(T.Translate(body)))
    ensures
      var inp := PIV.InpOfCp(str, cp);
      var bcB := CP.compile_to_bytecode(R.reverse_regex(body));
      var ctxcB := AI.cp_context(cp, str, LAnc.Backward);
      var raB := AI.FFindMatch(bcB, str, AI.FInitState(bcB, cp, cap, lk, qt, 0, ctxcB),
                               ov, LAnc.Backward, cdns).0;
      var bcF := CP.compile_to_bytecode(FST.FXR(body));
      var mcp := MIR.Mirror(cp, n);
      var ctxcF := AI.cp_context(mcp, LC.Reverse(str), LAnc.Forward);
      var rfF := AI.FFindMatch(bcF, LC.Reverse(str),
                   AI.FInitState(bcF, mcp, AReg.init_regs(ncap), AReg.init_regs(nlook),
                                 AReg.init_regs(nquant), 0, ctxcF),
                   MIR.MirrorView(ov, n), LAnc.Forward, MIR.SwapAnchorsCdns(cdns)).0;
      var S := set g | g in L.DefGroups(T.Translate(body))
                    && g !in LL.LkBodyGroups(T.Translate(body));
      (raB.None? <==> LS.LkResult(T.TrLookaround(la), tlk, gmMain, inp).None?)
      && (raB.Some? ==>
            LS.LkResult(T.TrLookaround(la), tlk, gmMain, inp).Some?
            && rfF.Some?
            && M.GmAgreeOn(LBV.SwapGm(LS.LkResult(T.TrLookaround(la), tlk, gmMain, inp).value),
                           PIV.GmOfLive(body, MIR.MirrorRegs(rfF.value.capture_regs, n),
                                              MIR.MirrorRegs(rfF.value.look_regs, n),
                                              MIR.MirrorRegs(rfF.value.quant_regs, n)),
                           S))
  {
    var tr := T.Translate(body);
    var inp := PIV.InpOfCp(str, cp);
    var Sall := set g | g in L.DefGroups(tr);
    var Sin := LL.LkBodyGroups(tr);
    var S := set g | g in L.DefGroups(tr) && g !in Sin;
    MIR.ReverseLen(str);
    var rstr := LC.Reverse(str);
    var mcp := MIR.Mirror(cp, n);
    var ov' := MIR.MirrorView(ov, n);
    var cdns' := MIR.SwapAnchorsCdns(cdns);
    var bcF := CP.compile_to_bytecode(FST.FXR(body));
    var ctxcF := AI.cp_context(mcp, rstr, LAnc.Forward);
    var inpF := SD.SwapInput(inp);

    // ---- engine side ----
    LBEngineLeafFlip(rer, qm, body, str, cp, cap, lk, qt, ov, cdns, ncap, nlook, nquant, n);
    var rfF := AI.FFindMatch(bcF, rstr,
                 AI.FInitState(bcF, mcp, AReg.init_regs(ncap), AReg.init_regs(nlook),
                               AReg.init_regs(nquant), 0, ctxcF),
                 ov', LAnc.Forward, cdns').0;
    var bcB := CP.compile_to_bytecode(R.reverse_regex(body));
    var ctxcB := AI.cp_context(cp, str, LAnc.Backward);
    var raB := AI.FFindMatch(bcB, str, AI.FInitState(bcB, cp, cap, lk, qt, 0, ctxcB),
                             ov, LAnc.Backward, cdns).0;
    var t_F := FU.ComputeTr(rer, [LS.Areg(FM.FlipRevL(tr))], inpF, LG.Empty, WP.Forward);
    var rf := LT.FirstLeaf(t_F, inpF);

    // ---- spec side (F2): the backward leaf is the exact MirrorGm-preimage ----
    MIR.ReverseLen(str[..cp]);
    assert n == |inp.pref| + |inp.next|;
    FST.TranslateGroupOkLB(body);
    FST.TranslateNegBodiesGroupFree(body);
    TranslateDefGroupsNoDupK(body);
    FD.BackBodyGmTieFlip(rer, tr, inp, n);
    var tB := FU.ComputeTr(rer, [LS.Areg(tr)], inp, LG.Empty, WP.Backward);
    var rb := LT.TreeRes(tB, LG.Empty, inp, WP.Backward);
    assert rf == LT.TreeRes(t_F, LG.Empty, inpF, WP.Forward);

    // ---- tlk == tB (gm-independence), and the LkResult fold ----
    FD.GroupOkLBNegFreePikeLk(tr);
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

    // ---- None-iff (the gate) ----
    assert rb.None? <==> rf.None?;
    assert raB.None? <==> lkr.None?;

    // ---- value ----
    if raB.Some? {
      assert rf.Some? && rfF.Some? && rb.Some? && lkr.Some?;
      var rfc := rfF.value.capture_regs;
      var rfl := rfF.value.look_regs;
      var rfq := rfF.value.quant_regs;
      var G := PIV.GmOfLive(body, rfc, rfl, rfq);
      assert LL.GmAgreeOutside(G, rf.value.1, Sin);
      assert rf.value.1 == TRM.MirrorGm(rb.value.1, n) && TRM.GmInBounds(rb.value.1, n);
      assert forall k :: AI.get_idx(AReg.as_arrays(rfc).0, k) <= n;
      BGM.GmOfLiveMirror(body, rfc, rfl, rfq, n);
      assert PIV.GmOfLive(body, MIR.MirrorRegs(rfc, n), rfl, rfq) == BGM.RawMirrorGm(G, n);
      LBV.GmOfLiveClockIndep(body, MIR.MirrorRegs(rfc, n), MIR.MirrorRegs(rfl, n),
                             MIR.MirrorRegs(rfq, n), rfl, rfq);
      var Gm := PIV.GmOfLive(body, MIR.MirrorRegs(rfc, n), MIR.MirrorRegs(rfl, n),
                             MIR.MirrorRegs(rfq, n));
      assert Gm == BGM.RawMirrorGm(G, n);
      LBV.RawMirrorMirrorSwap(rb.value.1, n);
      RawMirrorAgreeOutside(G, TRM.MirrorGm(rb.value.1, n), n, Sin);
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
}
