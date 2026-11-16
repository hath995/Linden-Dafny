// G1(a) avoided (W9): the lookbehind oracle column by the MatchesV route, in the
// mirrored world -- no MatchesL, no GroupOkLB, no LBOnlyLooksRE.
//
//   bit(cp, lid)
//     <=> RecorderHitV(body, str, ovf, cp)                    [step 1: the forward build sweep]
//     <=> exists j :: MatchesV(FXR(body), rstr, mv, n-cp, j)  [step 2: MatchesVMirror + FlipRE-blindness]
//     <=> fresh forward run of FXR(body) at n-cp succeeds      [step 3: AcceptRunCharacterizationV]
//     <=> forward leaf of FlipRevL(Translate(body)) on SwapInput [step 4: BodyTreeAtCpNested @ FXR(body)]
//     <=> backward leaf of Translate(body) at cp               [step 5: W3 BodySomeTieFlipG @ Backward]
//
// First verified against lift-sim-oracle's deps + its .doo, with W3's FlipOracleG.dfy /
// FlipMirrorG.dfy as co-sources (see linden-equiv/endgame/W9-matchesv-route.md).
// Package linden-equiv-mirror-world. Differences from W9's scratch file: the
// two plumbing lemmas W9 copied from FlipKeystoneG are called there instead
// (`KG.TranslateNoBackref`, `KG.LmOfBodiesNoBackref`, same statements), and
// `MatchesVUpper` is a local copy of lift-sim-core's (the band must not be a
// dependency, and no package below the band states it).

module LindenElkMatchesVRoute {
  import opened Std.Wrappers
  import BRS = LindenElkBackRowStatics   // (G3b) the flipped statics, no stamp-free premise
  import LW = WarblreRegExpRecord
  import WP = WarblrePrimitives
  import LC = Chars
  import LG = Groups
  import L = Regex
  import LS = Semantics
  import LT = Tree
  import FU = FunctionalUtils
  import R = RegElkRegex
  import CP = Compiler
  import AI = ArrayInterp
  import AReg = Array_Regs
  import LOr = Oracle
  import LAnc = Anchors
  import LCdn = Cdn
  import NR = LindenElkNfaRep
  import LTB = LindenElkLookTables
  import T = LindenElkTranslate
  import PIV = LindenElkPikeInv
  import PSM = LindenElkPikeSim
  import AR = LindenElkActionsRep
  import LL = LindenElkLookLeaves
  import OE = LindenElkOracleEntry
  import OB = LindenElkOracleBuild
  import ODV = LindenElkOracleDecompV
  import OBV = LindenElkOracleBridgeV
  import OMV = LindenElkOracleMirrorV
  import OAV = LindenElkOracleAcceptV
  import MIR = LindenElkMirror
  import SD = LindenSpanDuality
  import FR = LindenElkFlipRev
  import FM = LindenElkFlipMirror
  import FST = LindenElkFlipStatics
  import FK = LindenElkFlipKeystone
  import FO = LindenElkFlipOracle
  import FG = LindenElkFlipGate
  import LBV = LindenLookBehindValue
  import M = LindenElkMain
  import OG = LindenElkFlipOracleG
  import MG = LindenElkFlipMirrorG
  import KG = LindenElkFlipKeystoneG
  import RC = Charclasses

  // ===========================================================================
  // Step 1: bit <=> RecorderHitV -- the first half of OE.OracleColumnSpecNested,
  // extracted. Its premises are FBuildOracleCorrectAtNested's: no GroupOkLB.
  // ===========================================================================

  lemma ColumnBehindBitIsRecorderHitCdn(re: R.regex, str: string, lid: int, la: R.lookaround,
                                     body: R.regex, cp: int)
    requires NR.NestedFragmentCdnRE(re) && LTB.LidsWellNested(re) && LTB.LookUnique(re)
    requires LTB.LookEntryOk(CP.FFullCompilation(re), lid, la, body)
    requires la.Lookbehind? || la.NegLookbehind?
    requires NR.NestedFragmentRE(body)
    requires 1 <= lid
    requires 0 <= cp <= |str|
    ensures LOr.view_get_oracle(AI.FBuildOracle(CP.FFullCompilation(re), str), cp, lid)
        <==> ODV.RecorderHitV(body, str, AI.FBuildOracle(CP.FFullCompilation(re), str), cp)
  {
    var ovf := AI.FBuildOracle(CP.FFullCompilation(re), str);
    var rcb := R.remove_capture(body);
    OMV.RemoveCaptureNestedFragment(body);
    OB.FBuildOracleCorrectAtCdn(re, str, lid, la, body, cp);
    if LOr.view_get_oracle(ovf, cp, lid) {
      var i := ODV.ReachesWriteVToMatchesV(rcb, lid, str, ovf, LCdn.compile_cdns(body), cp);
      OMV.MatchesVRemoveCapture(body, str, ovf, i, cp);
      ODV.RecorderHitVIntro(body, str, ovf, cp, i);
    }
    if ODV.RecorderHitV(body, str, ovf, cp) {
      var i := ODV.RecorderHitVInv(body, str, ovf, cp);
      OMV.MatchesVRemoveCapture(body, str, ovf, i, cp);
      OBV.MatchesVToReachesWriteV(rcb, lid, str, ovf, LCdn.compile_cdns(body), i, cp);
    }
  }

  /** (G5a-1 row J) The narrow name, as a corollary of `ColumnBehindBitIsRecorderHitCdn`. */
  lemma ColumnBehindBitIsRecorderHit(re: R.regex, str: string, lid: int, la: R.lookaround,
                                     body: R.regex, cp: int)
    requires NR.NestedFragmentRE(re) && LTB.LidsWellNested(re) && LTB.LookUnique(re)
    requires LTB.LookEntryOk(CP.FFullCompilation(re), lid, la, body)
    requires la.Lookbehind? || la.NegLookbehind?
    requires NR.NestedFragmentRE(body)
    requires 1 <= lid
    requires 0 <= cp <= |str|
    ensures LOr.view_get_oracle(AI.FBuildOracle(CP.FFullCompilation(re), str), cp, lid)
        <==> ODV.RecorderHitV(body, str, AI.FBuildOracle(CP.FFullCompilation(re), str), cp)
  {
    NR.NarrowIsCdn(re);
    ColumnBehindBitIsRecorderHitCdn(re, str, lid, la, body, cp);
  }

  // ===========================================================================
  // Step 2: MatchesV cannot see look kinds (FlipRE keeps lid and polarity)
  // ===========================================================================

  lemma MatchesVFlipRE(re: R.regex, str: string, ov: LOr.OracleView, i: int, j: int)
    ensures OBV.MatchesV(FR.FlipRE(re), str, ov, i, j) <==> OBV.MatchesV(re, str, ov, i, j)
    decreases CP.rsize(re), 0, 0
  {
    match re
    case Re_alt(r1, r2) =>
      MatchesVFlipRE(r1, str, ov, i, j); MatchesVFlipRE(r2, str, ov, i, j);
    case Re_con(r1, r2) =>
      forall m: int
        ensures (OBV.MatchesV(FR.FlipRE(r1), str, ov, i, m) && OBV.MatchesV(FR.FlipRE(r2), str, ov, m, j))
            <==> (OBV.MatchesV(r1, str, ov, i, m) && OBV.MatchesV(r2, str, ov, m, j))
      { MatchesVFlipRE(r1, str, ov, i, m); MatchesVFlipRE(r2, str, ov, m, j); }
    case Re_quant(nul, qid, q, r1) =>
      forall k: nat
        ensures OBV.MatchesIterV(FR.FlipRE(r1), k, str, ov, i, j) <==> OBV.MatchesIterV(r1, k, str, ov, i, j)
      { MatchesIterVFlipRE(r1, k, str, ov, i, j); }
    case Re_capture(cid, r1) => MatchesVFlipRE(r1, str, ov, i, j);
    case _ =>
  }

  lemma MatchesIterVFlipRE(r: R.regex, k: nat, str: string, ov: LOr.OracleView, i: int, j: int)
    ensures OBV.MatchesIterV(FR.FlipRE(r), k, str, ov, i, j) <==> OBV.MatchesIterV(r, k, str, ov, i, j)
    decreases CP.rsize(r), 1, k
  {
    if k > 0 {
      forall m: int
        ensures (OBV.MatchesV(FR.FlipRE(r), str, ov, i, m) && OBV.MatchesIterV(FR.FlipRE(r), k - 1, str, ov, m, j))
            <==> (OBV.MatchesV(r, str, ov, i, m) && OBV.MatchesIterV(r, k - 1, str, ov, m, j))
      { MatchesVFlipRE(r, str, ov, i, m); MatchesIterVFlipRE(r, k - 1, str, ov, m, j); }
    }
  }

  // Copied verbatim from lift-sim-core (`LiftSimCore.dfy:5207-5246`), which is in
  // the band and so cannot be a dependency of this leaf.
  /** A gated span that starts inside the string ends inside it
      (`is_accepted(None, _)` is false, so a read never steps past `|str|`). */
  lemma MatchesVUpper(re: R.regex, str: string, ov: LOr.OracleView, i: int, j: int)
    requires OBV.MatchesV(re, str, ov, i, j)
    requires i <= |str|
    ensures j <= |str|
    decreases CP.rsize(re), 0, 0
  {
    match re
    case Re_character(ch) =>
      assert RC.is_accepted(AI.get_char(str, i), T.ExpectationOf(ch));
      assert AI.get_char(str, i).Some?;
      assert i < |str|;
    case Re_alt(r1, r2) =>
      if OBV.MatchesV(r1, str, ov, i, j) { MatchesVUpper(r1, str, ov, i, j); }
      else { MatchesVUpper(r2, str, ov, i, j); }
    case Re_con(r1, r2) =>
      var m: int :| OBV.MatchesV(r1, str, ov, i, m) && OBV.MatchesV(r2, str, ov, m, j);
      MatchesVUpper(r1, str, ov, i, m); MatchesVUpper(r2, str, ov, m, j);
    case Re_quant(nul, qid, q, r1) =>
      var k: nat :| q.min <= k && (q.max.Some? ==> k <= q.max.value)
                    && OBV.MatchesIterV(r1, k, str, ov, i, j);
      MatchesIterVUpper(r1, k, str, ov, i, j);
    case Re_capture(cid, r1) => MatchesVUpper(r1, str, ov, i, j);
    case _ =>
  }

  /** The iteration-chain analogue (mutually recursive). */
  lemma MatchesIterVUpper(r: R.regex, k: nat, str: string, ov: LOr.OracleView, i: int, j: int)
    requires OBV.MatchesIterV(r, k, str, ov, i, j)
    requires i <= |str|
    ensures j <= |str|
    decreases CP.rsize(r), 1, k
  {
    if k > 0 {
      var m: int :| OBV.MatchesV(r, str, ov, i, m) && OBV.MatchesIterV(r, k - 1, str, ov, m, j);
      MatchesVUpper(r, str, ov, i, m); MatchesIterVUpper(r, k - 1, str, ov, m, j);
    }
  }


  /** Step 2: a span of the body ENDING at cp <=> a span of FXR(body) STARTING at
      n - cp over the reversed string and mirrored view. No fragment premise. */
  lemma RecorderHitVMirrorFXR(body: R.regex, str: string, ov: LOr.OracleView, cp: int, mcp: int)
    requires |ov| == |str| + 1
    requires 0 <= cp <= |str| && mcp == |str| - cp
    ensures |LC.Reverse(str)| == |str|
    ensures ODV.RecorderHitV(body, str, ov, cp)
        <==> exists j: int :: OBV.MatchesV(FST.FXR(body), LC.Reverse(str), MIR.MirrorView(ov, |str|), mcp, j)
  {
    var n := |str|;
    var rstr := LC.Reverse(str);
    var mv := MIR.MirrorView(ov, n);
    var x := OMV.XRev(body);
    SD.ReverseLength(str);
    assert FST.FXR(body) == FR.FlipRE(x);
    if ODV.RecorderHitV(body, str, ov, cp) {
      var i := ODV.RecorderHitVInv(body, str, ov, cp);
      OMV.MatchesVMirror(body, str, ov, i, cp);
      MatchesVFlipRE(x, rstr, mv, mcp, n - i);
      assert OBV.MatchesV(FST.FXR(body), rstr, mv, mcp, n - i);
    }
    if exists j: int :: OBV.MatchesV(FST.FXR(body), rstr, mv, mcp, j) {
      var j: int :| OBV.MatchesV(FST.FXR(body), rstr, mv, mcp, j);
      MatchesVFlipRE(x, rstr, mv, mcp, j);
      assert OBV.MatchesV(x, rstr, mv, mcp, j);
      OBV.MatchesVBounds(x, rstr, mv, mcp, j);
      MatchesVUpper(x, rstr, mv, mcp, j);
      var i := n - j;
      OMV.MatchesVMirror(body, str, ov, i, cp);
      assert n - i == j;
      assert OBV.MatchesV(body, str, ov, i, cp);
      OBV.MatchesVBounds(body, str, ov, i, cp);
      ODV.RecorderHitVIntro(body, str, ov, cp, i);
    }
  }

  // ===========================================================================
  // Steps 4-5: the fresh forward run of FXR(body) over the reversed string is the
  // BACKWARD leaf of Translate(body) at cp. Body of ANY look kinds: the oracle
  // premise is the body's own table over str (the inner-rows hypothesis).
  // ===========================================================================

  lemma FlippedRunIsBackLeaf(rer: LW.RegExpRecord, qmb: AR.QMap, body: R.regex, str: string, cp: nat,
                             cdnsF: LCdn.cdns, ncap: int, nlook: int, nquant: int)
    requires !rer.ignoreCase && !rer.multiline
    requires T.TransWf(body) && NR.NestedFragmentRE(body)   // (G3b) no stamp-free premise
    requires PIV.CapUnique(body) && PIV.QuantUnique(body) && LTB.LookUnique(body)
    requires PSM.SizesOkRE(body, ncap, nlook, nquant)
    requires cp <= |str| && |qmb.ov| == |str| + 1
    requires qmb.looks == OE.LmOf(body)
    requires OE.OracleColsOk(rer, qmb, str)
    ensures |LC.Reverse(str)| == |str|
    ensures var n := |str|;
            var rstr := LC.Reverse(str);
            var bcF := CP.compile_to_bytecode(FST.FXR(body));
            var initsF := AI.FInitState(bcF, n - cp, AReg.init_regs(ncap), AReg.init_regs(nlook),
                                        AReg.init_regs(nquant), 0, AI.cp_context(n - cp, rstr, LAnc.Forward));
            var inp := T.InputAt(str, cp);
            AI.FFindMatch(bcF, rstr, initsF, MIR.MirrorView(qmb.ov, n), LAnc.Forward, cdnsF).0.Some?
            <==> LT.TreeRes(FU.ComputeTr(rer, [LS.Areg(T.Translate(body))], inp, LG.Empty, WP.Backward),
                            LG.Empty, inp, WP.Backward).Some?
  {
    var n := |str|;
    var tr := T.Translate(body);
    var re' := FST.FXR(body);
    SD.ReverseLength(str);
    var rstr := LC.Reverse(str);
    var mcp: nat := n - cp;
    var mv := MIR.MirrorView(qmb.ov, n);

    // ---- statics of FXR(body) + the flipped table (F4; no kind premise) ----
    var qm'', endl' := BRS.FlipXRevStaticCoreNested(body, mv, ncap, nlook, nquant);

    // ---- oracle for the flipped table: W3's generic transport (mixed kinds) ----
    KG.LmOfBodiesNoBackref(body);
    assert OG.QmBodiesNoBackref(qmb);
    FST.FlipLooksMapTie(qmb, qm'');
    OG.MirrorOracleColsOkG(rer, qmb, qm'', str);
    FO.ColsOkToSuffix(rer, qm'', rstr, mcp);
    LBV.InpOfCpSwap(str, cp, n);
    assert PIV.InpOfCp(rstr, mcp) == T.InputAt(rstr, mcp);
    assert LL.OracleOkSuffix(rer, qm'', PIV.InpOfCp(rstr, mcp));

    // ---- the forward keystone at FXR(body) (step 4) ----
    var bcF := CP.compile_to_bytecode(re');
    var bestT := M.BodyTreeAtCpNested(rer, qm'', re', bcF, endl', 0, rstr, mcp, mv, cdnsF,
                                      ncap, nlook, nquant);
    FST.TranslateFlipXRev(body);
    assert T.Translate(re') == FM.FlipRevL(tr);
    var inp := T.InputAt(str, cp);
    assert PIV.InpOfCp(str, cp) == inp;
    var inpF := SD.SwapInput(inp);
    assert PIV.InpOfCp(rstr, mcp) == inpF;

    // ---- the backward leaf <=> the flipped forward leaf (step 5, W3) ----
    KG.TranslateNoBackref(body);
    OG.BodySomeTieFlipG(rer, tr, inp, WP.Backward);
    assert MG.OppDir(WP.Backward) == WP.Forward;
  }

  // ===========================================================================
  // THE NARROW CONTRACT: a lookbehind row's column, body of any look kinds.
  // ===========================================================================

  lemma ColumnBehindViaMirrorCdn(rer: LW.RegExpRecord, top: R.regex, qmb: AR.QMap, str: string,
                              lid: int, la: R.lookaround, body: R.regex, cp: nat)
    requires !rer.ignoreCase && !rer.multiline
    requires NR.NestedFragmentCdnRE(top) && LTB.LidsWellNested(top) && LTB.LookUnique(top)
    requires LTB.LookEntryOk(CP.FFullCompilation(top), lid, la, body)
    requires la.Lookbehind? || la.NegLookbehind?
    requires 1 <= lid && cp <= |str|
    requires T.TransWf(body) && NR.NestedFragmentRE(body)   // (G3b) no stamp-free premise
    requires PIV.CapUnique(body) && PIV.QuantUnique(body) && LTB.LookUnique(body)
    requires forall y: nat :: y in LTB.LookIds(body) ==> 1 <= y
    requires qmb.ov == AI.FBuildOracle(CP.FFullCompilation(top), str) && qmb.looks == OE.LmOf(body)
    requires OE.OracleColsOk(rer, qmb, str)
    ensures LOr.view_get_oracle(qmb.ov, cp, lid)
        <==> LT.TreeRes(FU.ComputeTr(rer, [LS.Areg(T.Translate(body))], T.InputAt(str, cp), LG.Empty, WP.Backward),
                        LG.Empty, T.InputAt(str, cp), WP.Backward).Some?
  {
    // every step is a lemma postcondition: hide every body (AGENTS §2.9, the
    // `ColumnAheadBitToRun` recipe); the chain is then propositional.
    hide *;
    var n := |str|;
    var crv := CP.FFullCompilation(top);
    var ovf := qmb.ov;
    OB.FBuildOracleViewLen(crv, str);
    assert |ovf| == n + 1;
    SD.ReverseLength(str);
    var rstr := LC.Reverse(str);
    var mv := MIR.MirrorView(ovf, n);
    var re' := FST.FXR(body);
    var mcp: int := n - cp;

    // step 1
    assert {:split_here} true;
    ColumnBehindBitIsRecorderHitCdn(top, str, lid, la, body, cp);
    // step 2
    assert {:split_here} true;
    RecorderHitVMirrorFXR(body, str, ovf, cp, mcp);
    // step 3
    assert {:split_here} true;
    FST.FXRStructural(body);
    FG.LookUniqueFXR(body);
    FG.LookIdsFXR(body);
    assert forall y: nat :: y in LTB.LookIds(re') ==> 1 <= y;
    var ncap := R.imax(0, 2 * R.max_group(body) + 2);
    var nlook := R.imax(0, R.max_lookaround(body) + 1);
    var nquant := R.imax(0, R.max_quant(body) + 1);
    assert {:split_here} true;
    assert PSM.SizesOkRE(body, ncap, nlook, nquant) by { reveal PSM.SizesOkRE, R.imax; }
    var cdnsF := LCdn.compile_cdns(re');
    assert {:split_here} true;
    OAV.AcceptRunCharacterizationV(re', rstr, mv, mcp, cdnsF, AReg.init_regs(ncap),
                                   AReg.init_regs(nlook), AReg.init_regs(nquant), 0);
    // steps 4-5
    assert {:split_here} true;
    FlippedRunIsBackLeaf(rer, qmb, body, str, cp, cdnsF, ncap, nlook, nquant);
    assert {:split_here} true;
  }

  /** (G5a-1 row J) The narrow name, as a corollary of `ColumnBehindViaMirrorCdn`. */
  lemma ColumnBehindViaMirror(rer: LW.RegExpRecord, top: R.regex, qmb: AR.QMap, str: string,
                              lid: int, la: R.lookaround, body: R.regex, cp: nat)
    requires !rer.ignoreCase && !rer.multiline
    requires NR.NestedFragmentRE(top) && LTB.LidsWellNested(top) && LTB.LookUnique(top)
    requires LTB.LookEntryOk(CP.FFullCompilation(top), lid, la, body)
    requires la.Lookbehind? || la.NegLookbehind?
    requires 1 <= lid && cp <= |str|
    requires T.TransWf(body) && NR.NestedFragmentRE(body)   // (G3b) no stamp-free premise
    requires PIV.CapUnique(body) && PIV.QuantUnique(body) && LTB.LookUnique(body)
    requires forall y: nat :: y in LTB.LookIds(body) ==> 1 <= y
    requires qmb.ov == AI.FBuildOracle(CP.FFullCompilation(top), str) && qmb.looks == OE.LmOf(body)
    requires OE.OracleColsOk(rer, qmb, str)
    ensures LOr.view_get_oracle(qmb.ov, cp, lid)
        <==> LT.TreeRes(FU.ComputeTr(rer, [LS.Areg(T.Translate(body))], T.InputAt(str, cp), LG.Empty, WP.Backward),
                        LG.Empty, T.InputAt(str, cp), WP.Backward).Some?
  {
    NR.NarrowIsCdn(top);
    ColumnBehindViaMirrorCdn(rer, top, qmb, str, lid, la, body, cp);
  }
}
