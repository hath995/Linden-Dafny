// §2.5b STAGE 2, RUNG F (F-d0) — THE FIRST END-TO-END CIN-GREEDY THEOREM.
//
// For a LOOKAROUND-FREE pattern in the nested fragment — which since stage 2a
// admits the greedy CI-nullable `+` (`(a?)+`, `(a|)+`, ...) — `Match` computes
// exactly the answer the ECMAScript tree semantics demands, with NO interim
// gate conjunct (`NoNulledPlusRaw`). The proof needs machine A only:
//   * rung C: the checked tree `tstar` (`ATR.ActionsTreeRepRENested`) agrees with
//     the spec tree `t` at the first result outside `S = CapIdsInLooks(re)`,
//     which is EMPTY here — so the two first leaves are EQUAL
//     (`NB.RAFirstLeafEmpty`);
//   * rung D: the simulation (`PSM.FindMatchSimRENested`, gate-free) ties the
//     VM's best thread to `tstar`'s first leaf through the reconstruction-aware
//     readout (`PIV.BestMatchRE` = `GmOfLiveR`), and records the live-stamp
//     facts of the best thread (`PSM.BestLiveRE`, rung F-a);
//   * rung E + F-b: `FReconstructPlus(best)` reads out as `GmOfLiveR(best)`
//     (`FRD.FinalReadout`);
//   * without lookarounds `FLookLoop` is the identity, so the engine's answer is
//     `filter_reset` of the reconstructed registers, and the extraction twins
//     below (gate-free copies of `LSC.MainExtractionL5` /
//     `M.MainExtractionFromClosed`, which only ever needed the prefix
//     quantifier's clock `>= -1`) finish.
// Machine B (the lift-sim band) is not involved: its stamp-awareness is rung
// F-c, needed only once lookarounds and CIN-greedy pluses meet.
module LindenElkMainCin {
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
  import PT = PikeTree
  import CR = Correctness
  import AR = LindenElkActionsRep
  import EL = LindenElkEntryLk
  import WO = LindenElkWalkOk
  import ATR = LindenElkActionsTreeRep
  import NB = LindenElkNulledPlusBool
  import PIV = LindenElkPikeInv
  import CM = LindenElkClockMono
  import M = LindenElkMain
  import FC = LindenElkFlipClosed
  import TRM = LindenTreeResMirror
  import SD = LindenSpanDuality
  import T = LindenElkTranslate
  import LL = LindenElkLookLeaves
  import LFU = FunctionalUtils
  import FS = FunctionalSemantics
  import PSM = LindenElkPikeSim
  import OE = LindenElkOracleEntry
  import LES = LindenElkSpec
  import WkE = LindenElkWalkOkEntry
  import TT = LindenElkTreeThread
  import NUL = LindenElkNullable
  import TR = LindenElkTreeRep
  import LTB = LindenElkLookTables
  import NI = LindenElkNestInv
  import NRC = LindenElkNulledRecon
  import NRR = LindenElkNulledReconRegs
  import NRO = LindenElkNulledReconReadout
  import FV = LindenElkFinalVm
  import FRD = LindenElkFinalReadout
  import LSC = LindenElkLiftSimCore

  // =========================================================================
  // 0. Static facts of the look-free nested fragment.
  // =========================================================================

  lemma LookFreeFacts(re: R.regex)
    requires NR.LookFreeRE(re)
    ensures R.max_lookaround(re) == 0
    ensures NR.L5ScopeRE(re) && EL.NegBehindLBOnlyRE(re)
    ensures LTB.LookIds(re) == {} && PIV.CapIdsInLooks(re) == {} && NRR.LookIds(re) == {}
    decreases re
  {
    match re
    case Re_empty =>
    case Re_character(_) =>
    case Re_anchor(_) =>
    case Re_alt(r1, r2) => LookFreeFacts(r1); LookFreeFacts(r2);
    case Re_con(r1, r2) => LookFreeFacts(r1); LookFreeFacts(r2);
    case Re_quant(_, _, _, r1) => LookFreeFacts(r1);
    case Re_capture(_, r1) => LookFreeFacts(r1);
  }

  /** The nested fragment admits no CDN-greedy plus (its unbounded greedy
      nullable arm pins `CINullable`). */
  lemma NestedNoCdn(re: R.regex)
    requires NR.NestedFragmentRE(re)
    ensures NRC.NoCdnPlusRE(re)
    decreases re
  {
    match re
    case Re_empty =>
    case Re_character(_) =>
    case Re_anchor(_) =>
    case Re_alt(r1, r2) => NestedNoCdn(r1); NestedNoCdn(r2);
    case Re_con(r1, r2) => NestedNoCdn(r1); NestedNoCdn(r2);
    case Re_quant(_, _, _, r1) => NestedNoCdn(r1);
    case Re_capture(_, r1) => NestedNoCdn(r1);
    case Re_lookaround(_, _, r1) => NestedNoCdn(r1);
  }

  /** Without lookarounds the nested fragment IS the lookbehind fragment (the
      quantifier arms coincide). */
  lemma NestedLookFreeLB(re: R.regex)
    requires NR.NestedFragmentRE(re) && NR.LookFreeRE(re)
    ensures NR.LookBehindFragmentRE(re)
    decreases re
  {
    match re
    case Re_empty =>
    case Re_character(_) =>
    case Re_anchor(_) =>
    case Re_alt(r1, r2) => NestedLookFreeLB(r1); NestedLookFreeLB(r2);
    case Re_con(r1, r2) => NestedLookFreeLB(r1); NestedLookFreeLB(r2);
    case Re_quant(_, _, _, r1) => NestedLookFreeLB(r1);
    case Re_capture(_, r1) => NestedLookFreeLB(r1);
  }

  lemma SpecRegexLookFree(raw: R.raw_regex)
    requires NR.LookFreeRaw(raw)
    ensures NR.LookFreeRE(R.annotate(raw)) && NR.LookFreeRE(R.lazy_prefix(R.annotate(raw)))
  {
    NR.AnnotateLookFree(R.Raw_capture(raw), 0, 1, 1);
  }

  /** The spec-fragment bridge without the gate: a look-free nested regex
      translates into `PikeLkRegexRec` (twin of `EL.TranslateFragmentPikeLkRec`,
      whose `NoNulledPlusRE` serves only look bodies). */
  lemma TranslateFragmentPikeLkRecCin(re: R.regex)
    requires T.TransWf(re) && NR.NestedFragmentRE(re) && NR.LookFreeRE(re)
    ensures EL.PikeLkRegexRec(T.Translate(re))
    decreases re
  {
    match re
    case Re_alt(r1, r2) => TranslateFragmentPikeLkRecCin(r1); TranslateFragmentPikeLkRecCin(r2);
    case Re_con(r1, r2) => TranslateFragmentPikeLkRecCin(r1); TranslateFragmentPikeLkRecCin(r2);
    case Re_quant(_, _, _, r1) => TranslateFragmentPikeLkRecCin(r1);
    case Re_capture(_, r1) => TranslateFragmentPikeLkRecCin(r1);
    case _ =>
  }

  /** The capture-write frame, read off at start registers: a group outside the
      regex keeps its initial (unset) start value. */
  lemma OnlyCapIdsFromFrame(re: R.regex, caps: AReg.Regs, ncap: int)
    requires CM.RegsAgreeOutside(caps, AReg.init_regs(ncap), PIV.CaptureRegs(re))
    ensures forall gid: nat :: gid !in PIV.CapIds(re) ==> AI.get_idx(caps.a_cp, CP.start_reg(gid)) < 0
  {
    var capture := AReg.init_regs(ncap);
    forall gid: nat | gid !in PIV.CapIds(re) ensures AI.get_idx(caps.a_cp, CP.start_reg(gid)) < 0 {
      var k := CP.start_reg(gid);
      assert k !in PIV.CaptureRegs(re) by {
        if k in PIV.CaptureRegs(re) {
          if k in (set cid | cid in PIV.CapIds(re) :: CP.start_reg(cid)) {
            var c :| c in PIV.CapIds(re) && CP.start_reg(c) == k;
            assert c == gid;
          } else {
            var c :| c in PIV.CapIds(re) && CP.end_reg(c) == k;
            assert 2 * c + 1 == 2 * gid;
          }
        }
      }
      assert AI.get_idx(caps.a_cp, k) == AI.get_idx(capture.a_cp, k);
      if 0 <= k < |capture.a_cp| { assert capture.a_cp[k] == -1; }
    }
  }

  /** Register sizes cover every id of a look-free regex. */
  lemma CoversLookFree(re: R.regex, rg: NRC.Regs3, ncap: int, nquant: int)
    requires NR.LookFreeRE(re)
    requires ncap == 2 * R.max_group(re) + 2 && nquant == R.max_quant(re) + 1
    requires |rg.0.a_cp| == ncap && |rg.2.a_cp| == nquant
    ensures NRR.Covers(re, rg)
  {
    LookFreeFacts(re);
    NI.CapIdsLEMaxGroup(re);
    NI.QuantIdsLEMaxQuant(re);
  }

  /** An ordered map is its own positional normalization. */
  lemma NormGmOrdered(gm: LG.GroupMap)
    requires M.OrderedGm(gm)
    ensures PIV.NormGm(gm) == gm
  {
    forall g | g in gm ensures PIV.NormRange(gm[g]) == gm[g] {}
  }

  // =========================================================================
  // 1. The extraction, gate-free (twins of `M.MainExtractionFromClosed` and
  //    `LSC.MainExtractionL5`: the quant bank is needed only through the prefix
  //    quantifier's clock, `>= -1`).
  // =========================================================================

  lemma MainExtractionFromClosedCin(raw: R.raw_regex, str: string,
                                    t: LT.Tree, thread: AI.Thread, leaf: LT.Leaf)
    requires NR.NestedFragmentRaw(raw)
    requires M.ClosedGm(leaf.1)
    requires T.Latin1Wf(raw)
    requires EL.BoolTreeLk(LES.TheRer(raw), [LS.Areg(LES.SpecRegex(raw))], LC.InitInput(str), BS.CannotExit, t)
    requires LS.IsTree(LES.TheRer(raw), [LS.Areg(LES.SpecRegex(raw))], LC.InitInput(str), LG.Empty, WP.Forward, t)
    requires CM.ThreadRegsWf(thread, 2 * R.max_group(R.annotate(raw)) + 2,
                             R.max_lookaround(R.annotate(raw)) + 1,
                             R.max_quant(R.annotate(raw)) + 1)
    requires AI.get_idx(thread.quant_regs.a_clk, 0) >= -1
    requires var re := R.lazy_prefix(R.annotate(raw));
             leaf.1 == PIV.NormGm(PIV.GmOfLive(re, thread.capture_regs, thread.look_regs, thread.quant_regs))
    requires LT.FirstLeaf(t, LC.InitInput(str)) == Some(leaf)
    requires AI.FFullMatch(raw, str)
          == Some(AI.filter_reset(R.annotate(raw), thread.capture_regs, thread.look_regs,
                                  thread.quant_regs, -1))
    ensures LES.MatcherSpec(raw, str, LES.Normalize(AI.FFullMatch(raw, str)))
  {
    hide T.TransWf, NR.PlusFragmentRE, NR.LookBehindFragmentRE, NR.CaptureFreeRE, NR.LookFreeRE, NR.LookBehindFragmentRaw, NR.CaptureFreeRaw, NR.LookFreeRaw, EL.PikeLkRegex, EL.LkGateOk, SD.GroupFreeL, R.annotate, R.max_group, R.max_lookaround, R.max_quant;
    var ast := R.annotate(raw);
    var re := R.lazy_prefix(ast);
    var rer := LES.TheRer(raw);
    var inp := LC.InitInput(str);
    var ngroups := LES.NGroups(raw);
    var ncap := 2 * R.max_group(ast) + 2;
    assert {:split_here} true;
    T.AnnotateWf(raw);
    assert {:split_here} true;
    NR.SpecRegexNestedFragment(raw);
    var caps := thread.capture_regs;
    var lk := thread.look_regs;
    var qt := thread.quant_regs;
    assert {:split_here} true;
    assert LES.SpecRegex(raw) == T.Translate(re);
    assert {:split_here} true;
    var f := AI.filter_reset(re, caps, lk, qt, -1);
    assert ncap == 2 * ngroups;
    assert {:split_here} true;
    assert NR.NestedFragmentRE(re);
    assert {:split_here} true;
    assert M.ClosedGm(leaf.1);
    assert {:split_here} true;
    assert leaf.1 == PIV.NormGm(PIV.GmOfLive(re, thread.capture_regs, thread.look_regs, thread.quant_regs));
    assert {:split_here} true;
    assert CM.ThreadRegsWf(thread, ncap, R.max_lookaround(ast) + 1, R.max_quant(ast) + 1);
    assert {:split_here} true;
    M.CapArrayFromRegs(re, thread, leaf, inp, ngroups, ncap,
                       R.max_lookaround(ast) + 1, R.max_quant(ast) + 1);
    assert {:split_here} true;
    assert LES.NormalizeArr(f) == LES.CapArrayOfLeaf(leaf, ngroups);
    assert {:split_here} true;
    assert AI.get_idx(qt.a_clk, 0) >= -1;
    assert {:split_here} true;
    M.FilterResetLazyPrefix(ast, caps, lk, qt);
    assert {:split_here} true;
    assert AI.filter_reset(ast, caps, lk, qt, -1) == f;
    assert {:split_here} true;
    assert LES.Normalize(AI.FFullMatch(raw, str)) == Some(LES.NormalizeArr(f));
    assert {:split_here} true;
    assert LES.MatcherSpec(raw, str, Some(LES.CapArrayOfLeaf(leaf, ngroups)));
  }

  lemma MainExtractionCin(raw: R.raw_regex, str: string,
                          t: LT.Tree, thread: AI.Thread, leaf: LT.Leaf)
    requires NR.NestedFragmentRaw(raw) && NR.LookFreeRaw(raw)
    requires T.Latin1Wf(raw)
    requires EL.BoolTreeLk(LES.TheRer(raw), [LS.Areg(LES.SpecRegex(raw))], LC.InitInput(str), BS.CannotExit, t)
    requires LS.IsTree(LES.TheRer(raw), [LS.Areg(LES.SpecRegex(raw))], LC.InitInput(str), LG.Empty, WP.Forward, t)
    requires CM.ThreadRegsWf(thread, 2 * R.max_group(R.annotate(raw)) + 2,
                             R.max_lookaround(R.annotate(raw)) + 1,
                             R.max_quant(R.annotate(raw)) + 1)
    requires AI.get_idx(thread.quant_regs.a_clk, 0) >= -1
    requires var re := R.lazy_prefix(R.annotate(raw));
             leaf.1 == PIV.NormGm(PIV.GmOfLive(re, thread.capture_regs, thread.look_regs, thread.quant_regs))
    requires LT.FirstLeaf(t, LC.InitInput(str)) == Some(leaf)
    requires AI.FFullMatch(raw, str)
          == Some(AI.filter_reset(R.annotate(raw), thread.capture_regs, thread.look_regs,
                                  thread.quant_regs, -1))
    ensures LES.MatcherSpec(raw, str, LES.Normalize(AI.FFullMatch(raw, str)))
  {
    hide T.TransWf, NR.PlusFragmentRE, NR.LookBehindFragmentRE, NR.CaptureFreeRE, NR.LookBehindFragmentRaw, NR.CaptureFreeRaw, EL.PikeLkRegex, EL.LkGateOk, SD.GroupFreeL;
    var ast := R.annotate(raw);
    var re := R.lazy_prefix(ast);
    var rer := LES.TheRer(raw);
    var inp := LC.InitInput(str);
    T.AnnotateWf(raw);
    NR.SpecRegexNestedFragment(raw);
    SpecRegexLookFree(raw);
    LookFreeFacts(re);
    assert LES.SpecRegex(raw) == T.Translate(re);

    // closedness of the leaf gm
    assert LT.TreeRes(t, LG.Empty, inp, WP.Forward) == Some(leaf);
    assert M.OpenOf(LG.Empty) <= M.PendingCloses([LS.Areg(T.Translate(re))]);
    TranslateFragmentPikeLkRecCin(re);
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
    LSC.L5ScopeL5PosL(re);
    assert FC.L5PosActsL([LS.Areg(T.Translate(re))]);
    assert M.NestDepthActsLe([LS.Areg(T.Translate(re))], M.NestDepthL(T.Translate(re)));
    FC.FirstLeafClosedRecL5(rer, [LS.Areg(T.Translate(re))], inp, BS.CannotExit, t, LG.Empty, leaf,
                            M.NestDepthL(T.Translate(re)));
    assert M.ClosedGm(leaf.1);
    MainExtractionFromClosedCin(raw, str, t, thread, leaf);
  }

  /** The extraction over the CALLER's names (`ast`, `re`, the sizes): a pure
      restatement, so `MainTheoremCin`'s large context never mentions
      `R.annotate(raw)`. (Restated there, the recursive `annotate`/`max_*`
      unfolding — the matching loop `M.MainExtractionFromClosed`'s own `hide`
      line names — made two 300 s batches.) */
  lemma MainExtractionCinAt(raw: R.raw_regex, str: string,
                            t: LT.Tree, thread: AI.Thread, leaf: LT.Leaf,
                            ast: R.regex, re: R.regex, ncap: int, nlook: int, nquant: int)
    requires NR.NestedFragmentRaw(raw) && NR.LookFreeRaw(raw)
    requires T.Latin1Wf(raw)
    requires ast == R.annotate(raw) && re == R.lazy_prefix(ast) && T.TransWf(re)
    requires LES.SpecRegex(raw) == T.Translate(re)
    requires ncap == 2 * R.max_group(ast) + 2 && nlook == R.max_lookaround(ast) + 1
             && nquant == R.max_quant(ast) + 1
    requires EL.BoolTreeLk(LES.TheRer(raw), [LS.Areg(T.Translate(re))], LC.InitInput(str), BS.CannotExit, t)
    requires LS.IsTree(LES.TheRer(raw), [LS.Areg(T.Translate(re))], LC.InitInput(str), LG.Empty, WP.Forward, t)
    requires CM.ThreadRegsWf(thread, ncap, nlook, nquant)
    requires AI.get_idx(thread.quant_regs.a_clk, 0) >= -1
    requires leaf.1 == PIV.NormGm(PIV.GmOfLive(re, thread.capture_regs, thread.look_regs, thread.quant_regs))
    requires LT.FirstLeaf(t, LC.InitInput(str)) == Some(leaf)
    requires AI.FFullMatch(raw, str)
          == Some(AI.filter_reset(ast, thread.capture_regs, thread.look_regs, thread.quant_regs, -1))
    ensures LES.MatcherSpec(raw, str, LES.Normalize(AI.FFullMatch(raw, str)))
  {
    hide *;
    MainExtractionCin(raw, str, t, thread, leaf);
  }

  // =========================================================================
  // 2. THE THEOREM.
  // =========================================================================

  lemma MainTheoremCin(raw: R.raw_regex, str: string)
    requires NR.NestedFragmentRaw(raw)
    requires T.Latin1Wf(raw)
    requires NR.LookFreeRaw(raw)
    ensures LES.MatcherSpec(raw, str, LES.Normalize(AI.FFullMatch(raw, str)))
  {
    hide NUL.NonNullableL, NUL.CINullableL, NUL.NoNulledPlusL, AR.NfaRepCinL;
    var ast := R.annotate(raw);
    var re := R.lazy_prefix(ast);
    var rer := LES.TheRer(raw);
    var inp := LC.InitInput(str);
    var ngroups := LES.NGroups(raw);
    assert !rer.multiline && !rer.ignoreCase;

    // ---- statics ----------------------------------------------------------
    T.AnnotateWf(raw);
    NR.SpecRegexNestedFragment(raw);
    SpecRegexLookFree(raw);
    LTB.SpecRegexLookUnique(raw);
    PIV.SpecRegexCapUnique(raw);
    PIV.SpecRegexQuantUnique(raw);
    LookFreeFacts(re);
    LookFreeFacts(ast);
    NestedNoCdn(ast);
    var qm := AR.QMap(M.QmOfRE(re), OE.LmOf(re), AI.FBuildOracle(CP.FFullCompilation(ast), str), M.BodiesOfRE(re));
    M.QmOfREEntries(re);
    M.BodiesOfREEntries(re);
    M.QmapOkFromEntries(re, qm);
    OE.LmapOkOfLmOf(re, qm);
    assert AR.QmapOk(re, qm) && AR.LmapOk(re, qm);
    // no lookarounds: the oracle tables are empty, the oracle entry vacuous
    OE.LmOfDom(re);
    assert forall k: int :: k !in qm.looks;
    assert LL.OracleOkSuffix(rer, qm, inp);

    assert {:split_here} true;
    // ---- code -------------------------------------------------------------
    NR.CompileToBytecodeRepNested(re);
    var code := CP.compile_to_bytecode(re);
    var next := CP.compile(re, 0, CP.Progress).1;
    var endl: nat := next as nat;
    assert NR.NfaRepRE(re, code, 0, endl)
           && NR.GetPcRE(code, endl) == Some(RB.Accept) && |code| == endl + 1;
    LSC.CompileStutterTameRENested(re);
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

    assert {:split_here} true;
    // ---- the spec tree ----------------------------------------------------
    var acts := [LS.Areg(T.Translate(re))];
    LFU.ComputeTrIsTree(rer, acts, inp, LG.Empty, WP.Forward);
    var t := LFU.ComputeTr(rer, acts, inp, LG.Empty, WP.Forward);
    assert LS.IsTree(rer, acts, inp, LG.Empty, WP.Forward, t);
    assert LES.SpecRegex(raw) == T.Translate(re);
    TranslateFragmentPikeLkRecCin(re);
    EL.BooleanCorrectLkRec(rer, T.Translate(re), inp, t);
    assert forall i :: 0 <= i < |acts| ==> !acts[i].Acheck?;
    M.BoolTreeLbIrrel(rer, acts, inp, BS.CanExit, BS.CannotExit, t);
    assert EL.BoolTreeLk(rer, acts, inp, BS.CannotExit, t);

    assert {:split_here} true;
    // ---- the checked tree (machine A's) ------------------------------------
    WkE.WalkOkEntryNested(re);
    assert EL.PikeLkActionsRec(acts) by {
      assert acts == acts + [];
      assert EL.PikeLkActionsRec([]);
      EL.PikeLkActionsRecConsIff(LS.Areg(T.Translate(re)), []);
    }
    var S: set<LG.GroupId> := {};
    M.LkBodyGroupsEqCapIdsInLooks(re);
    assert S == LL.LkBodyGroups(T.Translate(re));
    assert WO.WalkOk(acts, code, 0, ATR.EaOf(BS.CannotExit));
    AR.CompileToBytecodeActionsRepNested(rer, qm, re);
    assert AR.ActionsRepL(rer, qm, acts, code, 0);
    assert LL.LkActsInS(acts, S) by {
      LL.LkBodyGroupsConfines(T.Translate(re), S);
      LL.LkActsInSCons(LS.Areg(T.Translate(re)), [], S);
    }
    LL.ComputeTrLkConfinedK(rer, acts, inp, LG.Empty, WP.Forward, S);
    assert NB.EncOk(acts, inp, BS.CannotExit) by { NB.EncOkNoChecks(acts, inp, BS.CannotExit); }
    var tstar := ATR.ActionsTreeRepRENested(rer, qm, acts, code, 0, inp, BS.CannotExit, t, S);
    assert TR.TreeRepRE(qm, tstar, code, 0, inp, false);
    NB.RAFirstLeafEmpty(tstar, t, inp);
    assert LT.FirstLeaf(tstar, inp) == LT.FirstLeaf(t, inp);

    assert {:split_here} true;
    // ---- the engine pipeline ----------------------------------------------
    var crv := CP.FFullCompilation(ast);
    M.FFullCompilationFactsNested(ast);
    assert crv.f_main_ast == ast && crv.f_main_bc == code && crv.f_main_cdns == LCdn.compile_cdns(ast);
    var ov := AI.FBuildOracle(crv, str);
    assert qm.ov == ov;
    var capture := AReg.init_regs(ncap);
    var look := AReg.init_regs(nlook);
    var quant := AReg.init_regs(nquant);
    var ctx := AI.cp_context(0, str, LAnc.Forward);
    var inits := AI.FInitState(code, 0, capture, look, quant, 0, ctx);
    var fmres := AI.FFindMatch(code, str, inits, ov, LAnc.Forward, crv.f_main_cdns);
    var result := fmres.0;

    assert {:split_here} true;
    // ---- machine A: the VM's best is the checked tree's first leaf -----------
    assert str[..0] == [] && str[0..] == str;
    assert LC.Reverse(str[..0]) == [];
    assert inp == PIV.InpOfCp(str, 0);
    assert TT.TreeThreadRE(rer, qm, code, inp, tstar, 0, false);
    PSM.InitialPikeInvFullREAtCpNested(rer, qm, re, code, endl, ngroups, str, 0, tstar,
                                       inits, ncap, nlook, nquant);
    var pts0 := PT.PikeTreeInitialState(tstar, inp);
    assert ctx.nextchar == AI.get_char(str, 0);
    var bestT := PSM.FindMatchSimRENested(rer, qm, re, code, endl, ngroups, str, pts0, inits,
                                          ov, LAnc.Forward, crv.f_main_cdns, ncap, nlook, nquant);
    M.TrcREToLinden(pts0, PT.PTS_final(bestT));
    TR.TreeRepPikeSubtree(qm, tstar, code, 0, inp, false);
    PT.InitPiketreeInv(tstar, inp);
    CR.PikeTreeTrcCorrect(pts0, PT.PTS_final(bestT), LT.FirstLeaf(tstar, inp));
    assert bestT == LT.FirstLeaf(t, inp);
    assert PIV.BestMatchRE(re, qm, str, bestT, result);

    assert {:split_here} true;
    // ---- the engine answer ------------------------------------------------
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
    M.FBuildCaptureUnfoldL3a(crv, str, ov, ncap, nlook, nquant, capture, look, quant, fmp);

    if result.None? {
      assert fmp.0 == None;
      assert bc.0 == None;
      assert LT.FirstLeaf(t, inp) == None;
      assert LES.Normalize(AI.FFullMatch(raw, str)) == None;
      assert LES.MatcherSpec(raw, str, None);
    } else {
      assert {:split_here} true;
      var thread := result.value;
      var rg: NRC.Regs3 := (thread.capture_regs, thread.look_regs, thread.quant_regs);
      // VM facts of the winning thread
      CM.FInitStateRegsWf(code, 0, ncap, nlook, nquant, 0, ctx);
      M.FFindMatchRegsWf(code, str, inits, ov, LAnc.Forward, crv.f_main_cdns, ncap, nlook, nquant);
      assert CM.ThreadRegsWf(thread, ncap, nlook, nquant);
      FRD.TrueStampsInCin(re, code, endl);
      var Q := FRD.CinQids(re);
      FV.RegsFinalOkInit(ncap, nlook, nquant, |str|, Q);
      assert FV.VmRegsFinalOk(inits, |str|, Q) by {
        forall t0 | t0 in inits.active ensures FV.RegsFinalOk(t0, |str|, Q) {
          assert t0 == AI.init_thread(capture, look, quant);
        }
      }
      FV.FFindMatchRegsFinal(code, str, inits, ov, LAnc.Forward, crv.f_main_cdns, Q);
      assert FV.RegsFinalOk(thread, |str|, Q);
      assert PSM.BestLiveRE(re, thread);

      assert {:split_here} true;
      // the registers of groups outside the regex stay unset
      NestedLookFreeLB(re);
      CM.CaptureBytecodeClassified(re);
      assert CM.VmCapturesAgree(inits, capture, PIV.CaptureRegs(re)) by {
        forall t0 | t0 in inits.active ensures CM.RegsAgreeOutside(t0.capture_regs, capture, PIV.CaptureRegs(re)) {
          assert t0 == AI.init_thread(capture, look, quant);
        }
      }
      CM.FFindMatchCapWriteFrame(code, str, inits, ov, LAnc.Forward, crv.f_main_cdns, capture, PIV.CaptureRegs(re));
      assert CM.RegsAgreeOutside(thread.capture_regs, capture, PIV.CaptureRegs(re));
      assert NRO.OnlyCapIdsSet(re, rg) by {
        OnlyCapIdsFromFrame(re, thread.capture_regs, ncap);
      }
      assert NRR.WfRegs(rg);
      assert NRR.Covers(re, rg) by {
        CoversLookFree(re, rg, ncap, nquant);
      }

      assert {:split_here} true;
      // THE FINAL READOUT (rung F-b)
      FRD.FinalReadout(qm, ast, str, thread, ncap, nlook, nquant);
      M.NoWriteOracleBodyCodeNested(re);
      CM.FFindMatchOvStable(code, str, inits, ov, LAnc.Forward, crv.f_main_cdns);
      assert fmres.1 == ov;
      var rp := AI.FReconstructPlus(thread, ast, crv.f_plus_bc, str, ov, LAnc.Forward);
      var rt := rp.0;
      assert fmp.0 == Some(rt);
      assert fmp.1 == ov;
      assert PIV.GmOfLive(re, rt.capture_regs, rt.look_regs, rt.quant_regs)
          == PIV.GmOfLiveR(re, qm, str, thread.capture_regs, thread.look_regs, thread.quant_regs);
      assert CM.ThreadRegsWf(rt, ncap, nlook, nquant);
      assert AI.get_idx(rt.quant_regs.a_clk, 0) >= -1 by {
        assert AI.get_idx(rt.quant_regs.a_clk, 0) == AI.get_idx(thread.quant_regs.a_clk, 0);
      }

      assert {:split_here} true;
      // the leaf, tied to the readout
      assert LT.FirstLeaf(t, inp).Some?;
      var leaf := LT.FirstLeaf(t, inp).value;
      assert bestT == Some(leaf);
      assert PIV.ThreadTracksGm(re, qm, str, thread, leaf.1);
      assert leaf.1 == PIV.GmOfLiveR(re, qm, str, thread.capture_regs, thread.look_regs, thread.quant_regs)
        by { reveal PIV.TieGm; }
      M.FirstLeafOrdered(t, inp, leaf);
      NormGmOrdered(leaf.1);
      assert leaf.1 == PIV.NormGm(PIV.GmOfLive(re, rt.capture_regs, rt.look_regs, rt.quant_regs));

      assert {:split_here} true;
      // no lookarounds: the look loop is the identity
      assert R.max_lookaround(crv.f_main_ast) == 0;
      var res := AI.FLookLoop(crv, str, 1, R.max_lookaround(crv.f_main_ast),
                              rt.capture_regs, rt.look_regs, rt.quant_regs, fmp.1);
      assert res == (rt.capture_regs, rt.look_regs, rt.quant_regs, fmp.1);
      assert bc.0 == Some(AI.filter_reset(ast, rt.capture_regs, rt.look_regs, rt.quant_regs, -1));
      assert AI.FFullMatch(raw, str) == Some(AI.filter_reset(ast, rt.capture_regs, rt.look_regs, rt.quant_regs, -1));

      assert {:split_here} true;
      // ---- extraction ------------------------------------------------------
      MainExtractionCinAt(raw, str, t, rt, leaf, ast, re, ncap, nlook, nquant);
    }
  }
}
