// FlipGate.dfy — L5 F6: the nested-lookbehind keystone in the gate-step's
// CONSUMER FORM.
//
// F5 (`FK.LkReplayMatchesSpecLBNested`) states the value tie through the
// T2a-mirrored FORWARD fresh run `rfF` of the flip-reversed body `FXR(body)`.
// The gate step (LiftSim's `LiftPreserveGatePassLk*`) speaks instead about the
// engine's actual fresh BACKWARD body match `raB` (= `M.FreshBodyMatch(l)` at
// `a_cp[l] = cp` for a Lookbehind lid). This file re-expresses F5 in `raB`'s own
// registers — the nested twin of depth-1 `LBK.BackFreshBodyGmTie` — and adds the
// nested-backward twin of LiftSim's `FreshBodyMatchGmOuter` (a look compiles to a
// single `CheckOracle` leaf, so the fresh body match records NONE of the inner
// looks' captures; needed for the (E4) crossing-coverage arm).
//
//   F6-core `BackFreshCoreNested`   : rfF == MirrorThread(raB), caps involution,
//                                     wf, and the GmOfLive readout congruence
//   F6a     `BackFreshBodyGmTieNested` : SwapGm(LkResult) ~ GmOfLive(body, raB.*)
//                                     on the SURFACE gids (DefGroups \ LkBodyGroups)
//   F6b     `FreshBodyMatchGmOuterLBNested` : inner gids absent from GmOfLive(body, raB.*)
//
// Everything is derived from F5 + T2a + F0 + F4's structural facts; no LiftSim
// include (F7 wires these into the D5 dead arm).
module LindenElkFlipGate {
  import opened Std.Wrappers
  import M = LindenElkMain
  import LBV = LindenLookBehindValue
  import LBK = LindenLookBehindKeystone
  import BV = LindenElkBackValue
  import LW = WarblreRegExpRecord
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
  import OE = LindenElkOracleEntry
  import LTB = LindenElkLookTables
  import TML = LindenElkTreeMirrorLk
  import LG = Groups
  import LS = Semantics
  import LT = Tree
  import L = Regex
  import WP = WarblrePrimitives
  import FU = FunctionalUtils
  import FR = LindenElkFlipRev
  import FM = LindenElkFlipMirror
  import FST = LindenElkFlipStatics
  import FK = LindenElkFlipKeystone
  import RL = LindenElkRegsLaws
  import NI = LindenElkNestInv
  import OBu = LindenElkOracleBuild
  import TRM = LindenTreeResMirror

  // ===========================================================================
  // F6-core: the fresh backward run and its T2a mirror, in consumer form
  // ===========================================================================

  /** For the FRESH backward body match `raB` (cap = lk = qt = init) of a v1-scope
      nested body: the T2a-mirrored forward run `rfF` of `FXR(body)` is exactly
      `MirrorThread(raB)`; both banks are well-formed; `rfF`'s caps are bounded by
      `n`; the caps involution `MirrorRegs(rfF.caps) == raB.caps` holds; and the
      `GmOfLive` readout of the MIRRORED `rfF` banks (F5's form) IS the readout of
      `raB`'s own banks (look/quant banks are read by clock only). The nested twin
      of the engine half of `LBK.BackFreshBodyGmTie`. */
  lemma BackFreshCoreNested(
      rer: LW.RegExpRecord, qm: AR.QMap, body: R.regex, str: string, cp: nat,
      ov: LOr.OracleView, cdns: LCdn.cdns, ncap: int, nlook: int, nquant: int, n: nat)
    requires T.TransWf(body) && NR.NestedFragmentRE(body) && NR.NegLooksLookFreeRE(body)
    requires NR.NoNulledPlusRE(body)   // §2.5b interim: all stamps false
    requires FST.LBOnlyLooksRE(body)
    requires PIV.CapUnique(body) && PIV.QuantUnique(body) && LTB.LookUnique(body)
    requires PSM.SizesOkRE(body, ncap, nlook, nquant)
    requires !rer.ignoreCase && !rer.multiline
    requires n == |str| && cp <= n && |ov| == n + 1
    requires qm.ov == ov && AR.LmapOk(body, qm) && OE.OracleColsOk(rer, qm, str)
    ensures
      var bcB := CP.compile_to_bytecode(R.reverse_regex(body));
      var raB := AI.FFindMatch(bcB, str,
                   AI.FInitState(bcB, cp, AReg.init_regs(ncap), AReg.init_regs(nlook),
                                 AReg.init_regs(nquant), 0, AI.cp_context(cp, str, LAnc.Backward)),
                   ov, LAnc.Backward, cdns).0;
      var bcF := CP.compile_to_bytecode(FST.FXR(body));
      var mcp := MIR.Mirror(cp, n);
      var rfF := AI.FFindMatch(bcF, LC.Reverse(str),
                   AI.FInitState(bcF, mcp, AReg.init_regs(ncap), AReg.init_regs(nlook),
                                 AReg.init_regs(nquant), 0,
                                 AI.cp_context(mcp, LC.Reverse(str), LAnc.Forward)),
                   MIR.MirrorView(ov, n), LAnc.Forward, MIR.SwapAnchorsCdns(cdns)).0;
      |LC.Reverse(str)| == n
      && (raB.None? <==> rfF.None?)
      && (raB.Some? ==>
            rfF.Some?
            && rfF.value == MIR.MirrorThread(raB.value, n)
            && PIV.CapRegWf(raB.value.capture_regs)
            && PIV.CapRegWf(rfF.value.capture_regs)
            && (forall k :: AI.get_idx(AReg.as_arrays(rfF.value.capture_regs).0, k) <= n)
            && MIR.MirrorRegs(rfF.value.capture_regs, n) == raB.value.capture_regs
            && PIV.GmOfLive(body, MIR.MirrorRegs(rfF.value.capture_regs, n),
                                  MIR.MirrorRegs(rfF.value.look_regs, n),
                                  MIR.MirrorRegs(rfF.value.quant_regs, n))
               == PIV.GmOfLive(body, raB.value.capture_regs, raB.value.look_regs,
                               raB.value.quant_regs))
  {
    var cap := AReg.init_regs(ncap);
    var lk := AReg.init_regs(nlook);
    var qt := AReg.init_regs(nquant);
    MIR.ReverseLen(str);
    var rstr := LC.Reverse(str);
    var mcp := MIR.Mirror(cp, n);
    assert 0 <= mcp <= n && |rstr| == n;
    var ov' := MIR.MirrorView(ov, n);
    var cdns' := MIR.SwapAnchorsCdns(cdns);
    var bcB := CP.compile_to_bytecode(R.reverse_regex(body));
    var ctxcB := AI.cp_context(cp, str, LAnc.Backward);
    var initsB := AI.FInitState(bcB, cp, cap, lk, qt, 0, ctxcB);
    var raB := AI.FFindMatch(bcB, str, initsB, ov, LAnc.Backward, cdns).0;
    var bcF := CP.compile_to_bytecode(FST.FXR(body));
    var ctxcF := AI.cp_context(mcp, rstr, LAnc.Forward);
    var initsF := AI.FInitState(bcF, mcp, cap, lk, qt, 0, ctxcF);
    var rfF := AI.FFindMatch(bcF, rstr, initsF, ov', LAnc.Forward, cdns').0;

    // ---- T2a + F0: rfF == MirrorThread(raB) (init banks mirror to init) ----
    MIR.MirrorInitRegs(ncap, n); MIR.MirrorInitRegs(nlook, n); MIR.MirrorInitRegs(nquant, n);
    BV.BackwardReplayMirrorNested(body, str, cp, cap, lk, qt, ov, cdns, n);
    FR.FlipCompileToBytecode(FST.XRV(body));
    assert bcF == CP.compile_to_bytecode(FST.XRV(body));
    assert raB.None? <==> rfF.None?;

    if raB.Some? {
      assert rfF.Some? && rfF.value == MIR.MirrorThread(raB.value, n);
      assert rfF.value.capture_regs == MIR.MirrorRegs(raB.value.capture_regs, n);
      assert rfF.value.look_regs == MIR.MirrorRegs(raB.value.look_regs, n);
      assert rfF.value.quant_regs == MIR.MirrorRegs(raB.value.quant_regs, n);

      // ---- forward cap bound (LBEngineLeafFlip) ----
      assert CM.RegsAgreeInside(cap, AReg.init_regs(ncap), PIV.CaptureRegs(body));
      assert |qt.a_cp| == nquant && |qt.a_clk| == nquant;
      FK.LBEngineLeafFlip(rer, qm, body, str, cp, cap, lk, qt, ov, cdns, ncap, nlook, nquant, n);
      assert forall k :: AI.get_idx(AReg.as_arrays(rfF.value.capture_regs).0, k) <= n;

      // ---- CapRegWf(raB.caps): backward fresh-match wf (no fragment premise) ----
      assert ctxcB.nextchar == AI.get_char(str, cp - 1);
      CM.FInitStateRegsWf(bcB, cp, ncap, nlook, nquant, 0, ctxcB);
      M.FFindMatchRegsWf(bcB, str, initsB, ov, LAnc.Backward, cdns, ncap, nlook, nquant);
      assert PIV.CapRegWf(raB.value.capture_regs);

      // ---- CapRegWf(rfF.caps): forward fresh-match wf over the nested FXR(body) ----
      FST.FXRStructural(body);
      assert ctxcF.nextchar == AI.get_char(rstr, mcp);
      FST.NoNulledPlusFXR(body);   // §2.5b interim: NoNulledPlusRE(FXR(body))
      M.FreshMatchWfNested(bcF, rstr, mcp, ov', cdns', FST.FXR(body), ncap, nlook, nquant);
      assert PIV.CapRegWf(rfF.value.capture_regs);

      // ---- caps involution ----
      LBK.BackCapsInRange(raB.value.capture_regs, rfF.value.capture_regs, n);
      MIR.MirrorRegsInvol(raB.value.capture_regs, n);
      assert MIR.MirrorRegs(rfF.value.capture_regs, n) == raB.value.capture_regs;

      // ---- look/quant: clocks agree, GmOfLive ignores their positions ----
      assert AReg.as_arrays(MIR.MirrorRegs(rfF.value.look_regs, n)).1
          == AReg.as_arrays(raB.value.look_regs).1;
      assert AReg.as_arrays(MIR.MirrorRegs(rfF.value.quant_regs, n)).1
          == AReg.as_arrays(raB.value.quant_regs).1;
      PIV.GmOfLiveClkCong(body, raB.value.capture_regs,
                          MIR.MirrorRegs(rfF.value.look_regs, n), raB.value.look_regs,
                          MIR.MirrorRegs(rfF.value.quant_regs, n), raB.value.quant_regs);
    }
  }

  // ===========================================================================
  // F6a: the keystone in raB's own registers (the gate-step value crux)
  // ===========================================================================

  /** THE NESTED GATE-STEP CRUX: for a positive LOOKBEHIND whose body is in the v1
      nested fragment, the FRESH backward body match `raB` (= `FreshBodyMatch(l)`
      at cap = init) ties to the SPEC `LkResult` value through the endpoint swap:
      `SwapGm(LkResult.value)` agrees with `GmOfLive(body, raB.*)` on the SURFACE
      gids `S = DefGroups \ LkBodyGroups`. The nested twin of
      `LBK.BackFreshBodyGmTie` (which is the `LkBodyGroups == {}` special case).
      The inner gids are NOT in `raB` at all (`FreshBodyMatchGmOuterLBNested`) —
      they are reconstructed by the direction-generic `FLookLoop` seam. */
  lemma BackFreshBodyGmTieNested(
      rer: LW.RegExpRecord, qm: AR.QMap, body: R.regex, str: string, cp: nat,
      ov: LOr.OracleView, cdns: LCdn.cdns, la: R.lookaround, tlk: LT.Tree, gmMain: LG.GroupMap,
      ncap: int, nlook: int, nquant: int, n: nat)
    requires T.TransWf(body) && NR.NestedFragmentRE(body) && NR.NegLooksLookFreeRE(body)
    requires NR.NoNulledPlusRE(body)   // §2.5b interim: all stamps false
    requires FST.LBOnlyLooksRE(body)
    requires PIV.CapUnique(body) && PIV.QuantUnique(body) && LTB.LookUnique(body)
    requires PSM.SizesOkRE(body, ncap, nlook, nquant)
    requires !rer.ignoreCase && !rer.multiline
    requires n == |str| && cp <= n && |ov| == n + 1
    requires qm.ov == ov && AR.LmapOk(body, qm) && OE.OracleColsOk(rer, qm, str)
    requires la.Lookbehind?
    requires tlk == FU.ComputeTr(rer, [LS.Areg(T.Translate(body))], PIV.InpOfCp(str, cp), gmMain, WP.Backward)
    requires M.GmAgreeOn(gmMain, LG.Empty, set g | g in L.DefGroups(T.Translate(body)))
    ensures
      var inp := PIV.InpOfCp(str, cp);
      var bcB := CP.compile_to_bytecode(R.reverse_regex(body));
      var raB := AI.FFindMatch(bcB, str,
                   AI.FInitState(bcB, cp, AReg.init_regs(ncap), AReg.init_regs(nlook),
                                 AReg.init_regs(nquant), 0, AI.cp_context(cp, str, LAnc.Backward)),
                   ov, LAnc.Backward, cdns).0;
      var lkr := LS.LkResult(T.TrLookaround(la), tlk, gmMain, inp);
      var S := set g | g in L.DefGroups(T.Translate(body))
                    && g !in LL.LkBodyGroups(T.Translate(body));
      (raB.None? <==> lkr.None?)
      && (raB.Some? ==>
            lkr.Some?
            && M.GmAgreeOn(LBV.SwapGm(lkr.value),
                           PIV.GmOfLive(body, raB.value.capture_regs, raB.value.look_regs,
                                        raB.value.quant_regs),
                           S))
  {
    var inp := PIV.InpOfCp(str, cp);
    var cap := AReg.init_regs(ncap);
    var lk := AReg.init_regs(nlook);
    var qt := AReg.init_regs(nquant);
    // keystone preconditions at cap = lk = qt = init
    assert CM.RegsAgreeInside(cap, AReg.init_regs(ncap), PIV.CaptureRegs(body));
    assert |qt.a_cp| == nquant && |qt.a_clk| == nquant;
    FK.LkReplayMatchesSpecLBNested(rer, qm, body, str, cp, cap, lk, qt, ov, cdns, la, tlk, gmMain,
                                   ncap, nlook, nquant, n);
    BackFreshCoreNested(rer, qm, body, str, cp, ov, cdns, ncap, nlook, nquant, n);

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
    var lkr := LS.LkResult(T.TrLookaround(la), tlk, gmMain, inp);
    var S := set g | g in L.DefGroups(T.Translate(body))
                  && g !in LL.LkBodyGroups(T.Translate(body));

    assert raB.None? <==> lkr.None?;                       // F5
    if raB.Some? {
      assert lkr.Some? && rfF.Some?;
      assert M.GmAgreeOn(LBV.SwapGm(lkr.value),
                         PIV.GmOfLive(body, MIR.MirrorRegs(rfF.value.capture_regs, n),
                                            MIR.MirrorRegs(rfF.value.look_regs, n),
                                            MIR.MirrorRegs(rfF.value.quant_regs, n)),
                         S);                                // F5
      assert PIV.GmOfLive(body, MIR.MirrorRegs(rfF.value.capture_regs, n),
                                MIR.MirrorRegs(rfF.value.look_regs, n),
                                MIR.MirrorRegs(rfF.value.quant_regs, n))
          == PIV.GmOfLive(body, raB.value.capture_regs, raB.value.look_regs,
                          raB.value.quant_regs);            // core
    }
  }

  // ===========================================================================
  // F6b: inner-look gids are ABSENT from the fresh backward match
  // ===========================================================================

  /** `CapIdsInLooks` is invariant under the flip-reversal `FXR` (kind flips and
      concatenation reversal move nothing across a look boundary). Via the L side:
      `LkBodyGroups(Translate(·))` is `CapIdsInLooks(·)`, and `LkBodyGroups` is
      invariant under both `FlipL` and `RevL`. */
  lemma CapIdsInLooksFXR(body: R.regex)
    requires T.TransWf(body)
    ensures PIV.CapIdsInLooks(FST.FXR(body)) == PIV.CapIdsInLooks(body)
  {
    var tr := T.Translate(body);
    M.LkBodyGroupsEqCapIdsInLooks(body);
    FST.TranslateFlipXRev(body);
    M.LkBodyGroupsEqCapIdsInLooks(FST.FXR(body));
    assert T.Translate(FST.FXR(body)) == FR.FlipL(SD.RevL(tr));
    FST.LkBodyGroupsFlipL(SD.RevL(tr));
    TML.LkBodyGroupsRevL(tr);
  }

  /** The nested-BACKWARD twin of LiftSim's `FreshBodyMatchGmOuter`: the fresh
      backward body match `raB` records NONE of the body's inner-look captures
      (a nested look compiles to a single `CheckOracle` leaf). Proven through the
      T2a mirror: `raB.caps` shares its CLOCK bank with the forward fresh match
      `rfF` of `FXR(body)`, whose inside-look start slots stay at their `-1` init
      (`M.MainMatchInsideCapsInitNested`); `GmOfLive` reads liveness off that
      clock bank (`PIV.GmOfLiveInsideLookAbsent`). Consumer: the (E4) crossing
      coverage arm of the gate step — inside-`S` groups live in `raB` are the
      body's OWN surface groups, covered by `BackFreshBodyGmTieNested`. */
  lemma FreshBodyMatchGmOuterLBNested(
      rer: LW.RegExpRecord, qm: AR.QMap, body: R.regex, str: string, cp: nat,
      ov: LOr.OracleView, cdns: LCdn.cdns, ncap: int, nlook: int, nquant: int, n: nat)
    requires T.TransWf(body) && NR.NestedFragmentRE(body) && NR.NegLooksLookFreeRE(body)
    requires NR.NoNulledPlusRE(body)   // §2.5b interim: all stamps false
    requires FST.LBOnlyLooksRE(body)
    requires PIV.CapUnique(body) && PIV.QuantUnique(body) && LTB.LookUnique(body)
    requires PSM.SizesOkRE(body, ncap, nlook, nquant)
    requires !rer.ignoreCase && !rer.multiline
    requires n == |str| && cp <= n && |ov| == n + 1
    requires qm.ov == ov && AR.LmapOk(body, qm) && OE.OracleColsOk(rer, qm, str)
    ensures
      var bcB := CP.compile_to_bytecode(R.reverse_regex(body));
      var raB := AI.FFindMatch(bcB, str,
                   AI.FInitState(bcB, cp, AReg.init_regs(ncap), AReg.init_regs(nlook),
                                 AReg.init_regs(nquant), 0, AI.cp_context(cp, str, LAnc.Backward)),
                   ov, LAnc.Backward, cdns).0;
      raB.Some? ==>
        forall g: nat :: g in PIV.CapIdsInLooks(body) ==>
          g !in PIV.GmOfLive(body, raB.value.capture_regs, raB.value.look_regs,
                             raB.value.quant_regs)
  {
    var cap := AReg.init_regs(ncap);
    var lk := AReg.init_regs(nlook);
    var qt := AReg.init_regs(nquant);
    BackFreshCoreNested(rer, qm, body, str, cp, ov, cdns, ncap, nlook, nquant, n);
    MIR.ReverseLen(str);
    var rstr := LC.Reverse(str);
    var mcp := MIR.Mirror(cp, n);
    assert 0 <= mcp <= n && |rstr| == n;
    var ov' := MIR.MirrorView(ov, n);
    var cdns' := MIR.SwapAnchorsCdns(cdns);
    var bcB := CP.compile_to_bytecode(R.reverse_regex(body));
    var ctxcB := AI.cp_context(cp, str, LAnc.Backward);
    var raB := AI.FFindMatch(bcB, str, AI.FInitState(bcB, cp, cap, lk, qt, 0, ctxcB),
                             ov, LAnc.Backward, cdns).0;
    var re' := FST.FXR(body);
    var bcF := CP.compile_to_bytecode(re');
    var ctxcF := AI.cp_context(mcp, rstr, LAnc.Forward);
    var initsF := AI.FInitState(bcF, mcp, cap, lk, qt, 0, ctxcF);
    var rfF := AI.FFindMatch(bcF, rstr, initsF, ov', LAnc.Forward, cdns').0;
    assert {:split_here} true;   // (§2.5b) section: preamble | the raB.Some? arm

    if raB.Some? {
      assert rfF.Some? && rfF.value == MIR.MirrorThread(raB.value, n);
      var rc := raB.value.capture_regs;
      var fc := rfF.value.capture_regs;
      assert fc == MIR.MirrorRegs(rc, n);
      assert fc.a_clk == rc.a_clk;                          // MirrorRegs keeps a_clk
      assert PIV.CapRegWf(rc);

      // ---- the forward fresh match leaves inside-look regs at init ----
      FST.FXRStructural(body);
      var endl' := FST.FXRCompileFacts(body);
      assert ctxcF.nextchar == AI.get_char(rstr, mcp);
      FST.NoNulledPlusFXR(body);   // §2.5b interim: NoNulledPlusRE(re')
      M.MainMatchInsideCapsInitNested(re', bcF, endl', rstr, initsF, cap, lk, qt, ov', cdns', rfF);
      assert {:split_here} true;   // (§2.5b) section: statics | the per-group readout
      var Sc := PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(re'));
      assert CM.RegsAgreeOutside(fc, cap, Sc);

      // ---- inside-look start slots are OUTSIDE Sc (id transfer + parity) ----
      CapIdsInLooksFXR(body);
      PIV.CapIdsLooksDisjoint(re');
      assert PIV.LooksCapUnset(body, AReg.as_arrays(rc).1) by {
        forall c: nat | c in PIV.CapIdsInLooks(body)
          ensures AI.get_idx(AReg.as_arrays(rc).1, CP.start_reg(c)) < 0
        {
          assert c in PIV.CapIdsInLooks(re');
          assert CP.start_reg(c as int) !in Sc by {
            if CP.start_reg(c as int) in Sc {
              if CP.start_reg(c as int) in (set cid | cid in PIV.CapIdsOutsideLooks(re') :: CP.start_reg(cid as int)) {
                var cid: nat :| cid in PIV.CapIdsOutsideLooks(re') && CP.start_reg(cid as int) == CP.start_reg(c as int);
                assert cid == c;
                assert c in PIV.CapIdsOutsideLooks(re') * PIV.CapIdsInLooks(re');
              } else {
                var cid: nat :| cid in PIV.CapIdsOutsideLooks(re') && CP.end_reg(cid as int) == CP.start_reg(c as int);
                assert 2 * (cid as int) + 1 == 2 * (c as int);
              }
              assert false;
            }
          }
          assert AI.get_idx(fc.a_clk, CP.start_reg(c as int))
              == AI.get_idx(cap.a_clk, CP.start_reg(c as int));   // RegsAgreeOutside off Sc
          RL.AInitLaws(ncap);                                       // init clock == -1
          assert AI.get_idx(cap.a_clk, CP.start_reg(c as int)) < 0;
          assert AReg.as_arrays(rc).1 == rc.a_clk;
        }
      }

      forall g: nat | g in PIV.CapIdsInLooks(body)
        ensures g !in PIV.GmOfLive(body, rc, raB.value.look_regs, raB.value.quant_regs)
      {
        PIV.GmOfLiveInsideLookAbsent(body, rc, raB.value.look_regs, raB.value.quant_regs, g);
      }
    }
  }

  // ===========================================================================
  // (E4) crossing coverage, LB nested — the value fact the gate step's coverage
  // arm consumes (LiftSim `LiftPreserveGatePassLkRec`, the `la.Lookahead?` twin
  // at its `M.LkReplayMatchesSpecNested` + `FreshBodyMatchGmOuter` block)
  // ===========================================================================

  /** Every group of the body that is LIVE in the fresh backward match `raB`
      lands in the passing gate's `LkResult`. Inner-look gids are never live in
      `raB` (F6b); the surface ones are covered by F6a (`SwapGm` preserves keys). */
  lemma GateCrossCoverageLBNested(
      rer: LW.RegExpRecord, qm: AR.QMap, body: R.regex, str: string, cp: nat,
      ov: LOr.OracleView, cdns: LCdn.cdns, la: R.lookaround, tlk: LT.Tree, gmMain: LG.GroupMap,
      ncap: int, nlook: int, nquant: int, n: nat)
    requires T.TransWf(body) && NR.NestedFragmentRE(body) && NR.NegLooksLookFreeRE(body)
    requires NR.NoNulledPlusRE(body)   // §2.5b interim: all stamps false
    requires FST.LBOnlyLooksRE(body)
    requires PIV.CapUnique(body) && PIV.QuantUnique(body) && LTB.LookUnique(body)
    requires PSM.SizesOkRE(body, ncap, nlook, nquant)
    requires !rer.ignoreCase && !rer.multiline
    requires n == |str| && cp <= n && |ov| == n + 1
    requires qm.ov == ov && AR.LmapOk(body, qm) && OE.OracleColsOk(rer, qm, str)
    requires la.Lookbehind?
    requires tlk == FU.ComputeTr(rer, [LS.Areg(T.Translate(body))], PIV.InpOfCp(str, cp), gmMain, WP.Backward)
    requires M.GmAgreeOn(gmMain, LG.Empty, set g | g in L.DefGroups(T.Translate(body)))
    ensures
      var inp := PIV.InpOfCp(str, cp);
      var bcB := CP.compile_to_bytecode(R.reverse_regex(body));
      var raB := AI.FFindMatch(bcB, str,
                   AI.FInitState(bcB, cp, AReg.init_regs(ncap), AReg.init_regs(nlook),
                                 AReg.init_regs(nquant), 0, AI.cp_context(cp, str, LAnc.Backward)),
                   ov, LAnc.Backward, cdns).0;
      var lkr := LS.LkResult(T.TrLookaround(la), tlk, gmMain, inp);
      raB.Some? ==>
        lkr.Some?
        && forall g: nat ::
             g in PIV.CapIds(body)
             && g in PIV.GmOfLive(body, raB.value.capture_regs, raB.value.look_regs,
                                  raB.value.quant_regs)
             ==> g in lkr.value
  {
    var inp := PIV.InpOfCp(str, cp);
    var tr := T.Translate(body);
    BackFreshBodyGmTieNested(rer, qm, body, str, cp, ov, cdns, la, tlk, gmMain, ncap, nlook, nquant, n);
    FreshBodyMatchGmOuterLBNested(rer, qm, body, str, cp, ov, cdns, ncap, nlook, nquant, n);
    M.TranslateDefGroupsEqCapIds(body);
    M.LkBodyGroupsEqCapIdsInLooks(body);
    var bcB := CP.compile_to_bytecode(R.reverse_regex(body));
    var raB := AI.FFindMatch(bcB, str,
                 AI.FInitState(bcB, cp, AReg.init_regs(ncap), AReg.init_regs(nlook),
                               AReg.init_regs(nquant), 0, AI.cp_context(cp, str, LAnc.Backward)),
                 ov, LAnc.Backward, cdns).0;
    var lkr := LS.LkResult(T.TrLookaround(la), tlk, gmMain, inp);
    var S := set g | g in L.DefGroups(tr) && g !in LL.LkBodyGroups(tr);
    if raB.Some? {
      assert lkr.Some?;
      var G := PIV.GmOfLive(body, raB.value.capture_regs, raB.value.look_regs, raB.value.quant_regs);
      var Lsw := LBV.SwapGm(lkr.value);
      assert M.GmAgreeOn(Lsw, G, S);
      forall g: nat | g in PIV.CapIds(body) && g in G
        ensures g in lkr.value
      {
        assert g !in PIV.CapIdsInLooks(body);                       // F6b
        assert g in (set gx | gx in L.DefGroups(tr));               // TranslateDefGroupsEqCapIds
        assert g !in LL.LkBodyGroups(tr);                           // LkBodyGroupsEqCapIdsInLooks
        assert g in S;
        assert (g in Lsw <==> g in G) && (g in Lsw ==> Lsw[g] == G[g]);
        assert g in Lsw;
        assert g in lkr.value;                                      // SwapGm keeps keys
      }
    }
  }

  // ===========================================================================
  // F7b (value half): the fresh BACKWARD body match vs the lid's OWN backward
  // spec leaf — the LB twins of LiftSim's `FreshBodyDirectInSubFirstLeaf` /
  // `SubFirstLeafDirectInFresh`, stated on the explicit backward `TreeRes`
  // (`BackLeafAt`). LiftSim identifies `BackLeafAt` with `SubFirstLeafAt` under
  // `LidDir(crv, l) == WP.Backward` (thin wrappers, F7b proper).
  // ===========================================================================

  /** The lid's own BACKWARD spec leaf at the recorded cp: exactly what LiftSim's
      `SubFirstLeafAt` unfolds to for a lookbehind lid. */
  ghost function BackLeafAt(rer: LW.RegExpRecord, body: R.regex, str: string, cp: nat)
      : Option<LG.GroupMap>
    requires T.TransWf(body) && cp <= |str|
  {
    var inp := PIV.InpOfCp(str, cp);
    var tlk := FU.ComputeTr(rer, [LS.Areg(T.Translate(body))], inp, LG.Empty, WP.Backward);
    var res := LT.TreeRes(tlk, LG.Empty, inp, WP.Backward);
    if res.Some? then Some(res.value.1) else None
  }

  /** `LkResult(LookBehind, tlk, Empty, inp)` at the body's own backward tree IS
      `BackLeafAt` (definitional: a positive look's `LkResult` is the tree's
      `TreeRes` group map in `LkDir`). */
  lemma LkResultIsBackLeaf(rer: LW.RegExpRecord, body: R.regex, str: string, cp: nat)
    requires T.TransWf(body) && cp <= |str|
    ensures var inp := PIV.InpOfCp(str, cp);
            var tlk := FU.ComputeTr(rer, [LS.Areg(T.Translate(body))], inp, LG.Empty, WP.Backward);
            LS.LkResult(T.TrLookaround(R.Lookbehind), tlk, LG.Empty, inp) == BackLeafAt(rer, body, str, cp)
  {
    var inp := PIV.InpOfCp(str, cp);
    var tlk := FU.ComputeTr(rer, [LS.Areg(T.Translate(body))], inp, LG.Empty, WP.Backward);
    assert T.TrLookaround(R.Lookbehind) == L.LookBehind;
    assert L.Positivity(L.LookBehind) && L.LkDir(L.LookBehind) == WP.Backward;
    assert LS.LkResult(L.LookBehind, tlk, LG.Empty, inp)
        == (match LT.TreeRes(tlk, LG.Empty, inp, WP.Backward)
            case None => None
            case Some(pair) => Some(pair.1));
  }

  /** The fresh body match of a LOOKBEHIND lid, spelled out: the backward run of
      `compile(reverse_regex(body))` from init registers at the recorded cp with
      the lid's cdns row. */
  lemma FreshBodyMatchLBUnfold(crv: CP.FCompiled, str: string, l: int, lk: AReg.Regs,
                               ov: LOr.OracleView, body: R.regex, ncap: int, nlook: int, nquant: int)
    requires body == M.VBody(crv, l)
    requires 0 <= l < |crv.f_look_types| && crv.f_look_types[l].Lookbehind?
    requires 0 <= l < |crv.f_look_cdns|
    requires AReg.get_cp(lk, l).Some?
    ensures var cp := AReg.get_cp(lk, l).value;
            var bcB := CP.compile_to_bytecode(R.reverse_regex(body));
            M.FreshBodyMatch(crv, str, l, lk, ov, ncap, nlook, nquant)
            == AI.FFindMatch(bcB, str,
                 AI.FInitState(bcB, cp, AReg.init_regs(ncap), AReg.init_regs(nlook),
                               AReg.init_regs(nquant), 0, AI.cp_context(cp, str, LAnc.Backward)),
                 ov, LAnc.Backward, crv.f_look_cdns[l]).0
  {
    var looktype := crv.f_look_types[l];
    assert looktype.Lookbehind?;
    assert AI.capture_direction(looktype) == LAnc.Backward;
    assert CP.capture_regex(looktype, body) == R.reverse_regex(body);
  }

  /** LB twin of LiftSim's `FreshBodyDirectInSubFirstLeaf`: a DIRECT group of the
      body (not inside an inner look) that is LIVE in the fresh BACKWARD body match
      lands in the lid's own backward spec leaf. Via `GateCrossCoverageLBNested`
      at `gmMain = Empty`. */
  lemma FreshBodyDirectInBackLeaf(
      rer: LW.RegExpRecord, qm: AR.QMap, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
      A0: nat, lk: AReg.Regs, body: R.regex, g2: nat, ncap: int, nlook: int, nquant: int)
    requires T.TransWf(body) && NR.NestedFragmentRE(body) && NR.NegLooksLookFreeRE(body)
    requires NR.NoNulledPlusRE(body)   // §2.5b interim: all stamps false
    requires FST.LBOnlyLooksRE(body)
    requires PIV.CapUnique(body) && PIV.QuantUnique(body) && LTB.LookUnique(body)
    requires PSM.SizesOkRE(body, ncap, nlook, nquant)
    requires !rer.ignoreCase && !rer.multiline
    requires |ov| == |str| + 1
    requires qm.ov == ov && AR.LmapOk(body, qm) && OE.OracleColsOk(rer, qm, str)
    // A0's table row: VBody == body, cdns row present, look type is a lookBEHIND.
    requires body == M.VBody(crv, A0 as int)
    requires 0 <= (A0 as int) < |crv.f_look_types| && crv.f_look_types[A0 as int].Lookbehind?
    requires 0 <= (A0 as int) < |crv.f_look_cdns|
    requires M.MatchedPosLA(crv, lk, A0 as int)
    requires var cp := AReg.get_cp(lk, A0 as int).value; 0 <= cp <= |str|
    requires g2 in PIV.CapIds(body) && g2 !in PIV.CapIdsInLooks(body)
    requires var rf := M.FreshBodyMatch(crv, str, A0 as int, lk, ov, ncap, nlook, nquant);
             rf.Some?
             && g2 in PIV.GmOfLive(body, rf.value.capture_regs, rf.value.look_regs, rf.value.quant_regs)
    ensures var cp := AReg.get_cp(lk, A0 as int).value;
            var lsub := BackLeafAt(rer, body, str, cp);
            lsub.Some? && g2 in lsub.value
  {
    var l := A0 as int;
    var cpN: nat := AReg.get_cp(lk, l).value;
    var inp := PIV.InpOfCp(str, cpN);
    var cdns := crv.f_look_cdns[l];
    var rf := M.FreshBodyMatch(crv, str, l, lk, ov, ncap, nlook, nquant);
    FreshBodyMatchLBUnfold(crv, str, l, lk, ov, body, ncap, nlook, nquant);
    var bcB := CP.compile_to_bytecode(R.reverse_regex(body));
    var raB := AI.FFindMatch(bcB, str,
                 AI.FInitState(bcB, cpN, AReg.init_regs(ncap), AReg.init_regs(nlook),
                               AReg.init_regs(nquant), 0, AI.cp_context(cpN, str, LAnc.Backward)),
                 ov, LAnc.Backward, cdns).0;
    assert rf == raB;
    var tlk := FU.ComputeTr(rer, [LS.Areg(T.Translate(body))], inp, LG.Empty, WP.Backward);
    assert M.GmAgreeOn(LG.Empty, LG.Empty, set g | g in L.DefGroups(T.Translate(body)));
    GateCrossCoverageLBNested(rer, qm, body, str, cpN, ov, cdns, R.Lookbehind, tlk, LG.Empty,
                              ncap, nlook, nquant, |str|);
    var lkr := LS.LkResult(T.TrLookaround(R.Lookbehind), tlk, LG.Empty, inp);
    assert lkr.Some? && g2 in lkr.value;
    LkResultIsBackLeaf(rer, body, str, cpN);
    assert BackLeafAt(rer, body, str, cpN) == lkr;
  }

  /** LB twin of LiftSim's `SubFirstLeafDirectInFresh`: a DIRECT group present in
      the lid's own backward spec leaf is live in the fresh BACKWARD body match,
      and the leaf's (ordered) range is the ENDPOINT SWAP of the backward match's
      (reversed) read — the `looktype.Lookbehind?` arm of `GmtTieInside`. Via F6a. */
  lemma BackLeafDirectInFresh(
      rer: LW.RegExpRecord, qm: AR.QMap, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
      A0: nat, lk: AReg.Regs, body: R.regex, g2: nat, ncap: int, nlook: int, nquant: int)
    requires T.TransWf(body) && NR.NestedFragmentRE(body) && NR.NegLooksLookFreeRE(body)
    requires NR.NoNulledPlusRE(body)   // §2.5b interim: all stamps false
    requires FST.LBOnlyLooksRE(body)
    requires PIV.CapUnique(body) && PIV.QuantUnique(body) && LTB.LookUnique(body)
    requires PSM.SizesOkRE(body, ncap, nlook, nquant)
    requires !rer.ignoreCase && !rer.multiline
    requires |ov| == |str| + 1
    requires qm.ov == ov && AR.LmapOk(body, qm) && OE.OracleColsOk(rer, qm, str)
    requires body == M.VBody(crv, A0 as int)
    requires 0 <= (A0 as int) < |crv.f_look_types| && crv.f_look_types[A0 as int].Lookbehind?
    requires 0 <= (A0 as int) < |crv.f_look_cdns|
    requires M.MatchedPosLA(crv, lk, A0 as int)
    requires var cp := AReg.get_cp(lk, A0 as int).value; 0 <= cp <= |str|
    requires g2 in PIV.CapIds(body) && g2 !in PIV.CapIdsInLooks(body)
    requires M.FreshBodyMatch(crv, str, A0 as int, lk, ov, ncap, nlook, nquant).Some?
    requires var cp := AReg.get_cp(lk, A0 as int).value;
             var lsub := BackLeafAt(rer, body, str, cp);
             lsub.Some? && g2 in lsub.value
    ensures var cp := AReg.get_cp(lk, A0 as int).value;
            var rf := M.FreshBodyMatch(crv, str, A0 as int, lk, ov, ncap, nlook, nquant);
            var gmb := PIV.GmOfLive(body, rf.value.capture_regs, rf.value.look_regs, rf.value.quant_regs);
            g2 in gmb
            && BackLeafAt(rer, body, str, cp).value[g2] == LBV.SwapRange(gmb[g2])
  {
    var l := A0 as int;
    var cpN: nat := AReg.get_cp(lk, l).value;
    var inp := PIV.InpOfCp(str, cpN);
    var cdns := crv.f_look_cdns[l];
    var rf := M.FreshBodyMatch(crv, str, l, lk, ov, ncap, nlook, nquant);
    FreshBodyMatchLBUnfold(crv, str, l, lk, ov, body, ncap, nlook, nquant);
    var bcB := CP.compile_to_bytecode(R.reverse_regex(body));
    var raB := AI.FFindMatch(bcB, str,
                 AI.FInitState(bcB, cpN, AReg.init_regs(ncap), AReg.init_regs(nlook),
                               AReg.init_regs(nquant), 0, AI.cp_context(cpN, str, LAnc.Backward)),
                 ov, LAnc.Backward, cdns).0;
    assert rf == raB;
    var tr := T.Translate(body);
    var tlk := FU.ComputeTr(rer, [LS.Areg(tr)], inp, LG.Empty, WP.Backward);
    assert M.GmAgreeOn(LG.Empty, LG.Empty, set g | g in L.DefGroups(tr));
    BackFreshBodyGmTieNested(rer, qm, body, str, cpN, ov, cdns, R.Lookbehind, tlk, LG.Empty,
                             ncap, nlook, nquant, |str|);
    var lkr := LS.LkResult(T.TrLookaround(R.Lookbehind), tlk, LG.Empty, inp);
    LkResultIsBackLeaf(rer, body, str, cpN);
    assert BackLeafAt(rer, body, str, cpN) == lkr;
    assert lkr.Some? && g2 in lkr.value;
    var G := PIV.GmOfLive(body, raB.value.capture_regs, raB.value.look_regs, raB.value.quant_regs);
    var S := set g | g in L.DefGroups(tr) && g !in LL.LkBodyGroups(tr);
    var Lsw := LBV.SwapGm(lkr.value);
    assert M.GmAgreeOn(Lsw, G, S);
    M.TranslateDefGroupsEqCapIds(body);
    M.LkBodyGroupsEqCapIdsInLooks(body);
    assert g2 in (set gx | gx in L.DefGroups(tr)) && g2 !in LL.LkBodyGroups(tr);
    assert g2 in S;
    assert g2 in Lsw && Lsw[g2] == LBV.SwapRange(lkr.value[g2]);
    assert (g2 in Lsw <==> g2 in G) && (g2 in Lsw ==> Lsw[g2] == G[g2]);
    assert g2 in G && LBV.SwapRange(lkr.value[g2]) == G[g2];
    LBV.SwapRangeInvol(lkr.value[g2]);
    assert lkr.value[g2] == LBV.SwapRange(G[g2]);
  }

  // ===========================================================================
  // (L5 F7c) scope bridge: the Flip bricks' `FST.LBOnlyLooksRE` IS the base
  // `NR.LBOnlyLooksRE` (identical definitions; NfaRepRE cannot see FlipStatics).
  // ===========================================================================
  lemma LBOnlyEquiv(r: R.regex)
    ensures FST.LBOnlyLooksRE(r) <==> NR.LBOnlyLooksRE(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => LBOnlyEquiv(r1); LBOnlyEquiv(r2);
    case Re_con(r1, r2) => LBOnlyEquiv(r1); LBOnlyEquiv(r2);
    case Re_quant(_, _, _, r1) => LBOnlyEquiv(r1);
    case Re_capture(_, r1) => LBOnlyEquiv(r1);
    case Re_lookaround(_, _, r1) => LBOnlyEquiv(r1);
    case _ =>
  }

  // ===========================================================================
  // (L5 F7c-3) The FLIPPED WORLD of a lookbehind body: structural facts about
  // `FXR(body) = FlipRE(SwapAnchorsRegex(reverse_regex(body)))` and the
  // MIRRORED LOOK TABLES `MirrorTables(crv)`. A positive-lookbehind lid's body
  // replay is the BACKWARD run of `compile(reverse_regex(body))`; by T2a it
  // mirrors to the FORWARD run of `compile(FXR(body))` over `Reverse(str)`, and
  // `FXR(body)` (all looks flipped to lookaheads) sits in the L4 scope — so the
  // L4 FORWARD body-replay carrier applies to it verbatim, given tables that
  // describe `FXR(body)`'s rows. Every id / path predicate below is
  // `FXR`-invariant (ids, quantifier ids and nesting are untouched).
  // ===========================================================================

  lemma FXRAlt(r1: R.regex, r2: R.regex)
    ensures FST.FXR(R.Re_alt(r1, r2)) == R.Re_alt(FST.FXR(r1), FST.FXR(r2))
  {}
  lemma FXRCon(r1: R.regex, r2: R.regex)
    ensures FST.FXR(R.Re_con(r1, r2)) == R.Re_con(FST.FXR(r2), FST.FXR(r1))
  {}
  lemma FXRQuant(nul: R.nullability, qid: R.quantid, q: R.counted_quantifier, r1: R.regex)
    ensures FST.FXR(R.Re_quant(nul, qid, q, r1)) == R.Re_quant(nul, qid, q, FST.FXR(r1))
  {}
  lemma FXRCapture(cid: R.capture, r1: R.regex)
    ensures FST.FXR(R.Re_capture(cid, r1)) == R.Re_capture(cid, FST.FXR(r1))
  {}
  lemma FXRLook(lid: R.lookid, la: R.lookaround, r1: R.regex)
    ensures FST.FXR(R.Re_lookaround(lid, la, r1)) == R.Re_lookaround(lid, FR.FlipLkRE(la), FST.FXR(r1))
  {}

  lemma LookIdsFXR(r: R.regex)
    ensures LTB.LookIds(FST.FXR(r)) == LTB.LookIds(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => FXRAlt(r1, r2); LookIdsFXR(r1); LookIdsFXR(r2);
    case Re_con(r1, r2) => FXRCon(r1, r2); LookIdsFXR(r1); LookIdsFXR(r2);
    case Re_quant(nul, qid, q, r1) => FXRQuant(nul, qid, q, r1); LookIdsFXR(r1);
    case Re_capture(cid, r1) => FXRCapture(cid, r1); LookIdsFXR(r1);
    case Re_lookaround(lid, la, r1) => FXRLook(lid, la, r1); LookIdsFXR(r1);
    case _ =>
  }

  lemma LookUniqueFXR(r: R.regex)
    requires LTB.LookUnique(r)
    ensures LTB.LookUnique(FST.FXR(r))
    decreases r
  {
    match r
    case Re_alt(r1, r2) => FXRAlt(r1, r2); LookUniqueFXR(r1); LookUniqueFXR(r2); LookIdsFXR(r1); LookIdsFXR(r2);
    case Re_con(r1, r2) => FXRCon(r1, r2); LookUniqueFXR(r1); LookUniqueFXR(r2); LookIdsFXR(r1); LookIdsFXR(r2);
    case Re_quant(nul, qid, q, r1) => FXRQuant(nul, qid, q, r1); LookUniqueFXR(r1);
    case Re_capture(cid, r1) => FXRCapture(cid, r1); LookUniqueFXR(r1);
    case Re_lookaround(lid, la, r1) => FXRLook(lid, la, r1); LookUniqueFXR(r1); LookIdsFXR(r1);
    case _ =>
  }

  lemma TopLookIdsFXR(r: R.regex)
    ensures NI.TopLookIds(FST.FXR(r)) == NI.TopLookIds(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => FXRAlt(r1, r2); TopLookIdsFXR(r1); TopLookIdsFXR(r2);
    case Re_con(r1, r2) => FXRCon(r1, r2); TopLookIdsFXR(r1); TopLookIdsFXR(r2);
    case Re_quant(nul, qid, q, r1) => FXRQuant(nul, qid, q, r1); TopLookIdsFXR(r1);
    case Re_capture(cid, r1) => FXRCapture(cid, r1); TopLookIdsFXR(r1);
    case Re_lookaround(lid, la, r1) => FXRLook(lid, la, r1);
    case _ =>
  }

  lemma CapIdsFXR(r: R.regex)
    ensures PIV.CapIds(FST.FXR(r)) == PIV.CapIds(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => FXRAlt(r1, r2); CapIdsFXR(r1); CapIdsFXR(r2);
    case Re_con(r1, r2) => FXRCon(r1, r2); CapIdsFXR(r1); CapIdsFXR(r2);
    case Re_quant(nul, qid, q, r1) => FXRQuant(nul, qid, q, r1); CapIdsFXR(r1);
    case Re_capture(cid, r1) => FXRCapture(cid, r1); CapIdsFXR(r1);
    case Re_lookaround(lid, la, r1) => FXRLook(lid, la, r1); CapIdsFXR(r1);
    case _ =>
  }

  /** The look body of a lid is `FXR`-invariant up to `FXR` (unique lids pick the same branch). */
  lemma LookBodyOfREFXR(r: R.regex, lid: nat)
    requires LTB.LookUnique(r) && lid in LTB.LookIds(r)
    ensures lid in LTB.LookIds(FST.FXR(r))
    ensures NI.LookBodyOfRE(FST.FXR(r), lid) == FST.FXR(NI.LookBodyOfRE(r, lid))
    decreases r
  {
    LookIdsFXR(r);
    match r
    case Re_alt(r1, r2) =>
      FXRAlt(r1, r2); LookIdsFXR(r1); LookIdsFXR(r2);
      if lid in LTB.LookIds(r1) { LookBodyOfREFXR(r1, lid); } else { LookBodyOfREFXR(r2, lid); }
    case Re_con(r1, r2) =>
      FXRCon(r1, r2); LookIdsFXR(r1); LookIdsFXR(r2);
      assert LTB.LookIds(r1) * LTB.LookIds(r2) == {};
      if lid in LTB.LookIds(r1) {
        assert lid !in LTB.LookIds(FST.FXR(r2));
        LookBodyOfREFXR(r1, lid);
      } else {
        LookBodyOfREFXR(r2, lid);
      }
    case Re_quant(nul, qid, q, r1) => FXRQuant(nul, qid, q, r1); LookBodyOfREFXR(r1, lid);
    case Re_capture(cid, r1) => FXRCapture(cid, r1); LookBodyOfREFXR(r1, lid);
    case Re_lookaround(lid0, la, r1) =>
      FXRLook(lid0, la, r1);
      if lid0 >= 0 && (lid0 as nat) == lid {
      } else {
        LookBodyOfREFXR(r1, lid);
      }
    case _ =>
  }

  lemma LookPathDomFXR(r: R.regex, L: int, qc: seq<int>, lid: nat)
    requires LTB.LookUnique(r) && lid in LTB.LookIds(r)
    ensures lid in LTB.LookIds(FST.FXR(r))
    ensures NI.LookPathDom(FST.FXR(r), L, qc, lid) <==> NI.LookPathDom(r, L, qc, lid)
    decreases r
  {
    LookIdsFXR(r);
    match r
    case Re_alt(r1, r2) =>
      FXRAlt(r1, r2); LookIdsFXR(r1); LookIdsFXR(r2);
      if lid in LTB.LookIds(r1) { LookPathDomFXR(r1, L, qc, lid); } else { LookPathDomFXR(r2, L, qc, lid); }
    case Re_con(r1, r2) =>
      FXRCon(r1, r2); LookIdsFXR(r1); LookIdsFXR(r2);
      assert LTB.LookIds(r1) * LTB.LookIds(r2) == {};
      if lid in LTB.LookIds(r1) {
        assert lid !in LTB.LookIds(FST.FXR(r2));
        LookPathDomFXR(r1, L, qc, lid);
      } else {
        LookPathDomFXR(r2, L, qc, lid);
      }
    case Re_quant(nul, qid, q, r1) => FXRQuant(nul, qid, q, r1); LookPathDomFXR(r1, L, qc, lid);
    case Re_capture(cid, r1) => FXRCapture(cid, r1); LookPathDomFXR(r1, L, qc, lid);
    case Re_lookaround(lid0, la, r1) =>
      FXRLook(lid0, la, r1);
      if lid0 >= 0 && (lid0 as nat) == lid {} else { LookPathDomFXR(r1, L, qc, lid); }
    case _ =>
  }

  lemma LookPathPresentFXR(r: R.regex, cc: seq<int>, qc: seq<int>, mx: int, lid: nat)
    requires LTB.LookUnique(r) && lid in LTB.LookIds(r)
    ensures lid in LTB.LookIds(FST.FXR(r))
    ensures NI.LookPathPresent(FST.FXR(r), cc, qc, mx, lid) <==> NI.LookPathPresent(r, cc, qc, mx, lid)
    decreases r
  {
    LookIdsFXR(r);
    match r
    case Re_alt(r1, r2) =>
      FXRAlt(r1, r2); LookIdsFXR(r1); LookIdsFXR(r2);
      if lid in LTB.LookIds(r1) { LookPathPresentFXR(r1, cc, qc, mx, lid); } else { LookPathPresentFXR(r2, cc, qc, mx, lid); }
    case Re_con(r1, r2) =>
      FXRCon(r1, r2); LookIdsFXR(r1); LookIdsFXR(r2);
      assert LTB.LookIds(r1) * LTB.LookIds(r2) == {};
      if lid in LTB.LookIds(r1) {
        assert lid !in LTB.LookIds(FST.FXR(r2));
        LookPathPresentFXR(r1, cc, qc, mx, lid);
      } else {
        LookPathPresentFXR(r2, cc, qc, mx, lid);
      }
    case Re_quant(nul, qid, q, r1) => FXRQuant(nul, qid, q, r1); LookPathPresentFXR(r1, cc, qc, AI.get_idx(qc, qid), lid);
    case Re_capture(cid, r1) => FXRCapture(cid, r1); LookPathPresentFXR(r1, cc, qc, mx, lid);
    case Re_lookaround(lid0, la, r1) =>
      FXRLook(lid0, la, r1);
      if lid0 >= 0 && (lid0 as nat) == lid {} else { LookPathPresentFXR(r1, cc, qc, -1, lid); }
    case _ =>
  }

  lemma MxAtLidLkFXR(r: R.regex, qc: seq<int>, mx: int, lid: nat)
    requires LTB.LookUnique(r) && lid in LTB.LookIds(r)
    ensures lid in LTB.LookIds(FST.FXR(r))
    ensures NI.MxAtLidLk(FST.FXR(r), qc, mx, lid) == NI.MxAtLidLk(r, qc, mx, lid)
    decreases r
  {
    LookIdsFXR(r);
    match r
    case Re_alt(r1, r2) =>
      FXRAlt(r1, r2); LookIdsFXR(r1); LookIdsFXR(r2);
      if lid in LTB.LookIds(r1) { MxAtLidLkFXR(r1, qc, mx, lid); } else { MxAtLidLkFXR(r2, qc, mx, lid); }
    case Re_con(r1, r2) =>
      FXRCon(r1, r2); LookIdsFXR(r1); LookIdsFXR(r2);
      assert LTB.LookIds(r1) * LTB.LookIds(r2) == {};
      if lid in LTB.LookIds(r1) {
        assert lid !in LTB.LookIds(FST.FXR(r2));
        MxAtLidLkFXR(r1, qc, mx, lid);
      } else {
        MxAtLidLkFXR(r2, qc, mx, lid);
      }
    case Re_quant(nul, qid, q, r1) => FXRQuant(nul, qid, q, r1); MxAtLidLkFXR(r1, qc, AI.get_idx(qc, qid), lid);
    case Re_capture(cid, r1) => FXRCapture(cid, r1); MxAtLidLkFXR(r1, qc, mx, lid);
    case Re_lookaround(lid0, la, r1) =>
      FXRLook(lid0, la, r1);
      if lid0 >= 0 && (lid0 as nat) == lid {} else { MxAtLidLkFXR(r1, qc, -1, lid); }
    case _ =>
  }

  /** A nested-fragment regex records NO cdns (`compile_cdns` only collects
      conditionally-nullable greedy PLUS quantifiers, which the fragment forbids). */
  lemma NestedCdnsRec(r: R.regex, c: LCdn.cdns)
    requires NR.NestedFragmentRE(r)
    ensures LCdn.compile_cdns_rec(r, c) == c
    decreases r
  {
    match r
    case Re_alt(r1, r2) => NestedCdnsRec(r1, c); NestedCdnsRec(r2, c);
    case Re_con(r1, r2) => NestedCdnsRec(r1, c); NestedCdnsRec(r2, c);
    case Re_quant(nul, qid, q, r1) =>
      if nul == R.CDNullable && q.min > 0 && q.max == None && q.greedy {
        assert nul == R.NonNullable;      // NestedFragmentRE's plus arm
        assert false;
      }
      NestedCdnsRec(r1, c);
    case Re_capture(_, r1) => NestedCdnsRec(r1, c);
    case Re_lookaround(_, _, r1) => NestedCdnsRec(r1, c);
    case _ =>
  }
  lemma NestedCdnsEmpty(r: R.regex)
    requires NR.NestedFragmentRE(r)
    ensures LCdn.compile_cdns(r) == []
  { NestedCdnsRec(r, []); }

  /** A lookbehind-only body flips into the L4 scope (no positive lookbehinds). */
  lemma NoPosLookbehindFXR(body: R.regex)
    requires FST.LBOnlyLooksRE(body)
    ensures M.NoPosLookbehindRE(FST.FXR(body))
    decreases body
  {
    match body
    case Re_alt(r1, r2) => FXRAlt(r1, r2); NoPosLookbehindFXR(r1); NoPosLookbehindFXR(r2);
    case Re_con(r1, r2) => FXRCon(r1, r2); NoPosLookbehindFXR(r1); NoPosLookbehindFXR(r2);
    case Re_quant(nul, qid, q, r1) => FXRQuant(nul, qid, q, r1); NoPosLookbehindFXR(r1);
    case Re_capture(cid, r1) => FXRCapture(cid, r1); NoPosLookbehindFXR(r1);
    case Re_lookaround(lid, la, r1) =>
      FXRLook(lid, la, r1); NoPosLookbehindFXR(r1);
      assert la.Lookbehind? || la.NegLookbehind?;
      assert !FR.FlipLkRE(la).Lookbehind?;
    case _ =>
  }

  /** `FlipLooksMap` distributes over map union and update. */
  lemma FlipLooksMapUnion(m1: map<int, (L.Lookaround, L.Regex)>, m2: map<int, (L.Lookaround, L.Regex)>)
    ensures FST.FlipLooksMap(m1 + m2) == FST.FlipLooksMap(m1) + FST.FlipLooksMap(m2)
  {}
  lemma FlipLooksMapUpdate(m: map<int, (L.Lookaround, L.Regex)>, k: int, v: (L.Lookaround, L.Regex))
    ensures FST.FlipLooksMap(m[k := v]) == FST.FlipLooksMap(m)[k := (FR.FlipLk(v.0), FM.FlipRevL(v.1))]
  {}

  /** The flipped body's looks-map IS the flipped looks-map (F4's `FlipLooksMap`). */
  lemma LmOfFXR(body: R.regex)
    requires T.TransWf(body) && LTB.LookUnique(body)
    ensures T.TransWf(FST.FXR(body))
    ensures OE.LmOf(FST.FXR(body)) == FST.FlipLooksMap(OE.LmOf(body))
    decreases body
  {
    FST.TranslateFlipXRev(body);
    match body
    case Re_alt(r1, r2) =>
      FXRAlt(r1, r2); LmOfFXR(r1); LmOfFXR(r2);
      FlipLooksMapUnion(OE.LmOf(r1), OE.LmOf(r2));
    case Re_con(r1, r2) =>
      FXRCon(r1, r2); LmOfFXR(r1); LmOfFXR(r2);
      // disjoint domains (LookUnique): the union commutes
      OE.LmOfDom(r1); OE.LmOfDom(r2);
      assert LTB.LookIds(r1) * LTB.LookIds(r2) == {};
      assert OE.LmOf(r1) + OE.LmOf(r2) == OE.LmOf(r2) + OE.LmOf(r1) by {
        forall k | k in OE.LmOf(r1) + OE.LmOf(r2)
          ensures (OE.LmOf(r1) + OE.LmOf(r2))[k] == (OE.LmOf(r2) + OE.LmOf(r1))[k]
        {
          if k in OE.LmOf(r1) { assert k !in OE.LmOf(r2); }
        }
      }
      FlipLooksMapUnion(OE.LmOf(r2), OE.LmOf(r1));
    case Re_quant(nul, qid, q, r1) => FXRQuant(nul, qid, q, r1); LmOfFXR(r1);
    case Re_capture(cid, r1) => FXRCapture(cid, r1); LmOfFXR(r1);
    case Re_lookaround(lid, la, r1) =>
      FXRLook(lid, la, r1); LmOfFXR(r1);
      FR.FlipLkRELaws(la);
      FST.TranslateFlipXRev(r1);
      FlipLooksMapUpdate(OE.LmOf(r1), lid, (T.TrLookaround(la), T.Translate(r1)));
    case _ =>
  }

  // ---------------------------------------------------------------------------
  // The mirrored look tables
  // ---------------------------------------------------------------------------

  /** The tables of the FLIPPED WORLD: row `l` of `crv` (`la`, `body`) becomes
      (`FlipLkRE(la)`, `FXR(body)`) with the matching cdns / build / capture
      bytecodes (the main-regex and plus fields are irrelevant and kept). */
  ghost function MirrorTables(crv: CP.FCompiled): CP.FCompiled
    requires |crv.f_look_types| == |crv.f_look_ast|
  {
    var n := |crv.f_look_types|;
    crv.(f_look_types := seq(n, i requires 0 <= i < n => FR.FlipLkRE(crv.f_look_types[i])),
         f_look_ast := seq(n, i requires 0 <= i < n => FST.FXR(crv.f_look_ast[i])),
         f_look_cdns := seq(n, i requires 0 <= i < n => LCdn.compile_cdns(FST.FXR(crv.f_look_ast[i]))),
         f_look_build_bc := seq(n, i requires 0 <= i < n =>
            CP.compile_to_write(CP.oracle_regex(FR.FlipLkRE(crv.f_look_types[i]), FST.FXR(crv.f_look_ast[i])), i)),
         f_look_capture_bc := seq(n, i requires 0 <= i < n =>
            CP.compile_to_bytecode(CP.capture_regex(FR.FlipLkRE(crv.f_look_types[i]), FST.FXR(crv.f_look_ast[i])))))
  }

  lemma MirrorTablesEntry(crv: CP.FCompiled, lid: int, la: R.lookaround, body: R.regex)
    requires |crv.f_look_types| == |crv.f_look_ast|
    requires LTB.LookEntryOk(crv, lid, la, body)
    ensures LTB.LookEntryOk(MirrorTables(crv), lid, FR.FlipLkRE(la), FST.FXR(body))
  {}

  /** `LookTablesOk` transfers to the flipped world. */
  lemma LookTablesOkFXR(body: R.regex, crv: CP.FCompiled)
    requires |crv.f_look_types| == |crv.f_look_ast|
    requires LTB.LookTablesOk(body, crv)
    ensures LTB.LookTablesOk(FST.FXR(body), MirrorTables(crv))
    decreases body
  {
    match body
    case Re_alt(r1, r2) => FXRAlt(r1, r2); LookTablesOkFXR(r1, crv); LookTablesOkFXR(r2, crv);
    case Re_con(r1, r2) => FXRCon(r1, r2); LookTablesOkFXR(r1, crv); LookTablesOkFXR(r2, crv);
    case Re_quant(nul, qid, q, r1) => FXRQuant(nul, qid, q, r1); LookTablesOkFXR(r1, crv);
    case Re_capture(cid, r1) => FXRCapture(cid, r1); LookTablesOkFXR(r1, crv);
    case Re_lookaround(lid, la, r1) =>
      FXRLook(lid, la, r1);
      MirrorTablesEntry(crv, lid, la, r1);
      LookTablesOkFXR(r1, crv);
    case _ =>
  }
  // ===========================================================================
  // (L5 F7c-3) Per-lid helpers for the LB body-replay carrier transport
  // ===========================================================================

  /** Sub-body facts a look body inherits from its host — the keystone-package
      conjuncts `NI.LookBodyOfFragmentNested` / `M.TransWfLookBodyOfRE` /
      `M.CapUniqueLookBodyOfRE` do not cover. */
  lemma LookBodySubFactsLB(r: R.regex, lid: nat)
    requires lid in LTB.LookIds(r)
    ensures PIV.QuantUnique(r) ==> PIV.QuantUnique(NI.LookBodyOfRE(r, lid))
    ensures LTB.LookUnique(r) ==> LTB.LookUnique(NI.LookBodyOfRE(r, lid))
    ensures FST.LBOnlyLooksRE(r) ==> FST.LBOnlyLooksRE(NI.LookBodyOfRE(r, lid))
    ensures R.max_group(NI.LookBodyOfRE(r, lid)) <= R.max_group(r)
    ensures R.max_quant(NI.LookBodyOfRE(r, lid)) <= R.max_quant(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      if lid in LTB.LookIds(r1) { LookBodySubFactsLB(r1, lid); } else { LookBodySubFactsLB(r2, lid); }
    case Re_con(r1, r2) =>
      if lid in LTB.LookIds(r1) { LookBodySubFactsLB(r1, lid); } else { LookBodySubFactsLB(r2, lid); }
    case Re_quant(_, _, _, r1) => LookBodySubFactsLB(r1, lid);
    case Re_capture(_, r1) => LookBodySubFactsLB(r1, lid);
    case Re_lookaround(lid0, _, r1) =>
      if lid0 >= 0 && (lid0 as nat) == lid {} else { LookBodySubFactsLB(r1, lid); }
    case _ =>
  }

  /** `LmapOk` descends to a look body. */
  lemma LmapOkLookBody(r: R.regex, qm: AR.QMap, lid: nat)
    requires T.TransWf(r) && AR.LmapOk(r, qm)
    requires lid in LTB.LookIds(r)
    ensures T.TransWf(NI.LookBodyOfRE(r, lid)) && AR.LmapOk(NI.LookBodyOfRE(r, lid), qm)
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      if lid in LTB.LookIds(r1) { LmapOkLookBody(r1, qm, lid); } else { LmapOkLookBody(r2, qm, lid); }
    case Re_con(r1, r2) =>
      if lid in LTB.LookIds(r1) { LmapOkLookBody(r1, qm, lid); } else { LmapOkLookBody(r2, qm, lid); }
    case Re_quant(_, _, _, r1) => LmapOkLookBody(r1, qm, lid);
    case Re_capture(_, r1) => LmapOkLookBody(r1, qm, lid);
    case Re_lookaround(lid0, _, r1) =>
      if lid0 >= 0 && (lid0 as nat) == lid {} else { LmapOkLookBody(r1, qm, lid); }
    case _ =>
  }

  /** Under `LookTablesOk` + `LBOnlyLooksRE`, every lid's row is lookbehind-
      flavoured, its ast is the lid's body and its cdns are that body's. */
  lemma LookRowLBOnly(r: R.regex, crv: CP.FCompiled, lid: nat)
    requires LTB.LookTablesOk(r, crv) && FST.LBOnlyLooksRE(r)
    requires lid in LTB.LookIds(r)
    ensures 0 <= (lid as int) < |crv.f_look_types| && 0 <= (lid as int) < |crv.f_look_ast|
         && 0 <= (lid as int) < |crv.f_look_cdns|
    ensures crv.f_look_types[lid].Lookbehind? || crv.f_look_types[lid].NegLookbehind?
    ensures crv.f_look_ast[lid] == NI.LookBodyOfRE(r, lid)
    ensures crv.f_look_cdns[lid] == LCdn.compile_cdns(NI.LookBodyOfRE(r, lid))
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      if lid in LTB.LookIds(r1) { LookRowLBOnly(r1, crv, lid); } else { LookRowLBOnly(r2, crv, lid); }
    case Re_con(r1, r2) =>
      if lid in LTB.LookIds(r1) { LookRowLBOnly(r1, crv, lid); } else { LookRowLBOnly(r2, crv, lid); }
    case Re_quant(_, _, _, r1) => LookRowLBOnly(r1, crv, lid);
    case Re_capture(_, r1) => LookRowLBOnly(r1, crv, lid);
    case Re_lookaround(lid0, la, r1) =>
      if lid0 >= 0 && (lid0 as nat) == lid {
        assert LTB.LookEntryOk(crv, lid0, la, r1);
      } else {
        LookRowLBOnly(r1, crv, lid);
      }
    case _ =>
  }

  /** `get_cp` through `MirrorRegs`: a recorded position `<= n` reflects to
      `n - cp` (still recorded); an unset slot stays unset. */
  lemma GetCpMirror(lk: AReg.Regs, n: int, l: int)
    requires CM.LookCpsLE(lk, n)
    ensures AReg.get_cp(MIR.MirrorRegs(lk, n), l).Some? <==> AReg.get_cp(lk, l).Some?
    ensures AReg.get_cp(lk, l).Some? ==>
              AReg.get_cp(MIR.MirrorRegs(lk, n), l).value == n - AReg.get_cp(lk, l).value
  {
    var m := MIR.MirrorRegs(lk, n);
    assert |m.a_cp| == |lk.a_cp|;
    if 0 <= l < |lk.a_cp| {
      assert AI.get_idx(lk.a_cp, l) == lk.a_cp[l] <= n;
      assert m.a_cp[l] == MIR.MirrorCpVal(lk.a_cp[l], n);
    }
  }

  /** `MirrorRange` is injective on in-bounds ranges (the deep carrier's value
      equality transports back through the mirror). */
  lemma MirrorRangeInj(a: LG.Range, b: LG.Range, n: nat)
    requires a.startIdx <= n && (a.endIdx.Some? ==> a.endIdx.value <= n)
    requires b.startIdx <= n && (b.endIdx.Some? ==> b.endIdx.value <= n)
    requires TRM.MirrorRange(a, n) == TRM.MirrorRange(b, n)
    ensures a == b
  {}
}
