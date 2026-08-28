// L3b item 4, step 3 (the assembly): the lookbehind capture value tie.
//
// This file wires the four proved pieces into the value correspondence a
// matched positive lookbehind needs:
//   - TreeMirror.ComputeTrReverse  (backward body tree ~ forward RevRE tree)
//   - TreeResMirror.TreeResMirror  (their leaves mirror: MirrorGm)
//   - CloseDisc.CloseDiscBody      (discharges TreeResMirror's CloseDisc hyp)
//   - BackGmMirror.GmOfLiveMirror / GmOfLiveRevRE  (engine-side commutation)
//
// `BackBodyGmTie` is the tree+value CORE (no engine): the backward body tree's
// leaf group map is the ordered mirror (`MirrorGm`) of the forward RevRE tree's
// first leaf. The engine wrapper then reads the backward replay's registers
// (`GmOfLive(body, MirrorRegs(rf))`) as the RAW (reversed-span) mirror of the
// forward run's, and `RawMirrorGm(MirrorGm(X)) == SwapGm(X)` shows the engine's
// raw readout is exactly the endpoint-swapped spec leaf — the reversed-span
// quirk the widened `NormalizeArr` (item 0) absorbs.
module LindenLookBehindValue {
  import opened Std.Wrappers
  import R = RegElkRegex
  import LW = WarblreRegExpRecord
  import T = LindenElkTranslate
  import AReg = Array_Regs
  import AI = ArrayInterp
  import PIV = LindenElkPikeInv
  import MIR = LindenElkMirror
  import BGM = LindenBackGmMirror
  import SD = LindenSpanDuality
  import TM = LindenTreeMirror
  import TRM = LindenTreeResMirror
  import CD = LindenCloseDisc
  import L = Regex
  import LS = Semantics
  import LG = Groups
  import LT = Tree
  import LC = Chars
  import WP = WarblrePrimitives
  import FU = FunctionalUtils

  // ===========================================================================
  // The endpoint swap and the raw∘ordered = swap identity
  // ===========================================================================

  /** Swap a closed range's endpoints (open ranges unchanged) — the reversed
      lookbehind span vs the ordered spec range. */
  function SwapRange(rg: LG.Range): LG.Range {
    match rg.endIdx
    case None => rg
    case Some(e) => LG.Range(e, Some(rg.startIdx))
  }

  ghost function SwapGm(gm: LG.GroupMap): LG.GroupMap {
    map g | g in gm :: SwapRange(gm[g])
  }

  /** `SwapRange` is an involution (a closed range's endpoints swap back; open
      ranges are fixed). */
  lemma SwapRangeInvol(rg: LG.Range)
    ensures SwapRange(SwapRange(rg)) == rg
  {}

  /** The RAW (reversed-span) mirror of the ORDERED (spec) mirror is exactly the
      endpoint swap — `n` cancels. So the engine's raw readout of the mirrored
      registers is the swap of the spec leaf. */
  lemma RawMirrorMirrorSwap(X: LG.GroupMap, n: nat)
    requires TRM.GmInBounds(X, n)
    ensures BGM.GmLeN(TRM.MirrorGm(X, n), n)
    ensures BGM.RawMirrorGm(TRM.MirrorGm(X, n), n) == SwapGm(X)
  {
    var M := TRM.MirrorGm(X, n);
    forall g | g in M
      ensures M[g].startIdx <= n && (M[g].endIdx.Some? ==> M[g].endIdx.value <= n)
    {
      assert M[g] == TRM.MirrorRange(X[g], n);
    }
    assert BGM.GmLeN(M, n);
    forall g | g in M
      ensures BGM.RawMirrorRange(M[g], n) == SwapRange(X[g])
    {
      assert M[g] == TRM.MirrorRange(X[g], n);
    }
    assert BGM.RawMirrorGm(M, n) == SwapGm(X);
  }

  // ===========================================================================
  // GmOfLive ignores the look/quant capture positions (reads their clocks only)
  // ===========================================================================

  lemma GmOfLiveClockIndep(ast: R.regex, cap: AReg.Regs, l1: AReg.Regs, q1: AReg.Regs,
                           l2: AReg.Regs, q2: AReg.Regs)
    requires AReg.as_arrays(l1).1 == AReg.as_arrays(l2).1
    requires AReg.as_arrays(q1).1 == AReg.as_arrays(q2).1
    ensures PIV.GmOfLive(ast, cap, l1, q1) == PIV.GmOfLive(ast, cap, l2, q2)
  {
    assert AI.filter_reset(ast, cap, l1, q1, -1) == AI.filter_reset(ast, cap, l2, q2, -1);
  }

  // ===========================================================================
  // The tree+value CORE: backward body leaf mirrors forward RevRE first leaf
  // ===========================================================================

  /** For a group-OK, unique-id `tr` (an L3b lookbehind body after `Translate`),
      the backward tree's leaf group map (`TreeRes(.., Backward)`) is the ordered
      mirror of the forward `RevL(tr)` tree's first leaf. Pure tree-level: wires
      `ComputeTrReverse` + `TreeResMirror` + `CloseDiscBody`. */
  lemma BackBodyGmTie(rer: LW.RegExpRecord, tr: L.Regex, inpB: LC.Input, n: nat)
    requires SD.GroupOkL(tr)
    requires CD.NoDupG(L.DefGroups(tr))
    requires n == |inpB.pref| + |inpB.next|
    ensures
      var tB := FU.ComputeTr(rer, [LS.Areg(tr)], inpB, LG.Empty, WP.Backward);
      var tF := FU.ComputeTr(rer, [LS.Areg(SD.RevL(tr))], SD.SwapInput(inpB), LG.Empty, WP.Forward);
      var rb := LT.TreeRes(tB, LG.Empty, inpB, WP.Backward);
      var rf := LT.FirstLeaf(tF, SD.SwapInput(inpB));
      && (rb.None? <==> rf.None?)
      && (rb.Some? ==>
            rf.Some? && TRM.GmInBounds(rb.value.1, n)
            && rf.value.1 == TRM.MirrorGm(rb.value.1, n))
  {
    var acts := [LS.Areg(tr)];
    assert SD.GroupOkActs(acts) by { SD.GroupOkActsCons(LS.Areg(tr), []); }
    var tB := FU.ComputeTr(rer, acts, inpB, LG.Empty, WP.Backward);

    TM.ComputeTrReverse(rer, acts, inpB, LG.Empty, LG.Empty);
    assert SD.RevActs(acts) == [LS.Areg(SD.RevL(tr))] by { SD.RevActsCons(LS.Areg(tr), []); }
    var tF := FU.ComputeTr(rer, [LS.Areg(SD.RevL(tr))], SD.SwapInput(inpB), LG.Empty, WP.Forward);
    assert TM.TreeMirrorRel(tB, tF);

    CD.CloseDiscBody(rer, tr, inpB, LG.Empty, WP.Backward);
    assert TRM.CloseDisc(tB, {});
    assert TRM.GmInBounds(LG.Empty, n);
    assert TRM.OpenSubset(LG.Empty, {});

    TRM.TreeResMirror(tB, tF, LG.Empty, inpB, n, {});
    // TreeResMirror's forward side is TreeRes(tF, MirrorGm(Empty,n), SwapInput(inpB), Forward);
    // MirrorGm(Empty,n) == Empty, and FirstLeaf(tF, x) == TreeRes(tF, Empty, x, Forward).
    assert TRM.MirrorGm(LG.Empty, n) == LG.Empty;
  }

  // ===========================================================================
  // The engine wrapper: the reconstructed backward caps read as the SWAP of the
  // spec leaf. Composes every proved piece; takes the two engine facts —
  // `BackwardReplayMirror`'s mirror-regs relation and `ReplayCapIsBodyLeaf`@RevRE
  // 's value equality — as hypotheses. The full `LkReplayMatchesSpecLB` supplies
  // those (statics/oracle transport) and wraps this.
  // ===========================================================================

  lemma BackBodyEngineTie(rer: LW.RegExpRecord, body: R.regex, inpB: LC.Input, n: nat,
                          rfc: AReg.Regs, rfl: AReg.Regs, rfq: AReg.Regs)
    requires T.TransWf(body)
    requires SD.GroupOkL(T.Translate(body))
    requires CD.NoDupG(L.DefGroups(T.Translate(body)))
    requires n == |inpB.pref| + |inpB.next|
    requires forall k :: AI.get_idx(AReg.as_arrays(rfc).0, k) <= n
    requires
      var tF := FU.ComputeTr(rer, [LS.Areg(SD.RevL(T.Translate(body)))], SD.SwapInput(inpB),
                             LG.Empty, WP.Forward);
      && LT.TreeRes(FU.ComputeTr(rer, [LS.Areg(T.Translate(body))], inpB, LG.Empty, WP.Backward),
                    LG.Empty, inpB, WP.Backward).Some?
      && LT.FirstLeaf(tF, SD.SwapInput(inpB)).Some?
      && PIV.GmOfLive(SD.RevRE(body), rfc, rfl, rfq) == LT.FirstLeaf(tF, SD.SwapInput(inpB)).value.1
    ensures
      var rb := LT.TreeRes(FU.ComputeTr(rer, [LS.Areg(T.Translate(body))], inpB, LG.Empty, WP.Backward),
                           LG.Empty, inpB, WP.Backward);
      PIV.GmOfLive(body, MIR.MirrorRegs(rfc, n), MIR.MirrorRegs(rfl, n), MIR.MirrorRegs(rfq, n))
        == SwapGm(rb.value.1)
  {
    var tr := T.Translate(body);
    var tF := FU.ComputeTr(rer, [LS.Areg(SD.RevL(tr))], SD.SwapInput(inpB), LG.Empty, WP.Forward);
    var rb := LT.TreeRes(FU.ComputeTr(rer, [LS.Areg(tr)], inpB, LG.Empty, WP.Backward),
                         LG.Empty, inpB, WP.Backward);

    // (1) tree+value core: FirstLeaf(tF) == MirrorGm(rb.value.1, n)
    BackBodyGmTie(rer, tr, inpB, n);
    assert LT.FirstLeaf(tF, SD.SwapInput(inpB)).value.1 == TRM.MirrorGm(rb.value.1, n);
    assert TRM.GmInBounds(rb.value.1, n);
    assert PIV.GmOfLive(SD.RevRE(body), rfc, rfl, rfq) == TRM.MirrorGm(rb.value.1, n);

    // (2) engine side: GmOfLive(body, MirrorRegs(rfc)) == RawMirrorGm(GmOfLive(RevRE(body), rfc))
    BGM.GmOfLiveRevRE(body, rfc, rfl, rfq);
    assert PIV.GmOfLive(body, rfc, rfl, rfq) == PIV.GmOfLive(SD.RevRE(body), rfc, rfl, rfq);
    BGM.GmOfLiveMirror(body, rfc, rfl, rfq, n);
    assert PIV.GmOfLive(body, MIR.MirrorRegs(rfc, n), rfl, rfq)
        == BGM.RawMirrorGm(PIV.GmOfLive(body, rfc, rfl, rfq), n);

    // (3) look/quant a_cp irrelevant to GmOfLive (only clocks read; MirrorRegs keeps clocks)
    GmOfLiveClockIndep(body, MIR.MirrorRegs(rfc, n), MIR.MirrorRegs(rfl, n), MIR.MirrorRegs(rfq, n),
                       rfl, rfq);

    // (4) RawMirrorGm(MirrorGm(X)) == SwapGm(X)
    RawMirrorMirrorSwap(rb.value.1, n);
  }

  // ===========================================================================
  // Statics transport under RevRE (for instantiating ReplayCapIsBodyLeaf@RevRE
  // in the keystone). LookFreeRE(RevRE) is OS.RevRELookFree; TransWf(RevRE) is
  // SD.RevRETransWf; Translate(RevRE)==RevL(Translate) is SD.TranslateRevRE.
  // ===========================================================================

  /** The reversed run's input at `n-cp` over `Reverse(str)` is the swap of the
      forward input at `cp` over `str`. `InpOfCp` is definitionally `T.InputAt`,
      so this is `SD.InputAtSwap`. */
  lemma InpOfCpSwap(str: string, cp: nat, n: nat)
    requires n == |str| && cp <= n
    ensures |LC.Reverse(str)| == n
    ensures PIV.InpOfCp(LC.Reverse(str), n - cp) == SD.SwapInput(PIV.InpOfCp(str, cp))
  {
    SD.InputAtSwap(str, cp);              // |Reverse(str)|==n; InputAt swap
    assert PIV.InpOfCp(str, cp) == T.InputAt(str, cp);
    assert PIV.InpOfCp(LC.Reverse(str), n - cp) == T.InputAt(LC.Reverse(str), n - cp);
  }

  /** `RevRE` preserves the largest group id (`Re_con` reorder is `imax`-symmetric;
      captures/anchors/looks keep their ids). */
  lemma MaxGroupRevRE(re: R.regex)
    ensures R.max_group(SD.RevRE(re)) == R.max_group(re)
    decreases re
  {
    match re
    case Re_alt(r1, r2) => MaxGroupRevRE(r1); MaxGroupRevRE(r2);
    case Re_con(r1, r2) =>
      MaxGroupRevRE(r1); MaxGroupRevRE(r2);
      assert R.imax(R.max_group(r1), R.max_group(r2)) == R.imax(R.max_group(r2), R.max_group(r1));
    case Re_quant(_, _, _, r1) => MaxGroupRevRE(r1);
    case Re_capture(_, r1) => MaxGroupRevRE(r1);
    case _ =>
  }

  /** `RevRE` preserves the largest quantifier id. */
  lemma MaxQuantRevRE(re: R.regex)
    ensures R.max_quant(SD.RevRE(re)) == R.max_quant(re)
    decreases re
  {
    match re
    case Re_alt(r1, r2) => MaxQuantRevRE(r1); MaxQuantRevRE(r2);
    case Re_con(r1, r2) =>
      MaxQuantRevRE(r1); MaxQuantRevRE(r2);
      assert R.imax(R.max_quant(r1), R.max_quant(r2)) == R.imax(R.max_quant(r2), R.max_quant(r1));
    case Re_quant(_, _, _, r1) => MaxQuantRevRE(r1);
    case Re_capture(_, r1) => MaxQuantRevRE(r1);
    case _ =>
  }

  /** `RevRE` preserves the set of capture ids (reorder is set-union-symmetric). */
  lemma CapIdsRevRE(re: R.regex)
    ensures PIV.CapIds(SD.RevRE(re)) == PIV.CapIds(re)
    decreases re
  {
    match re
    case Re_alt(r1, r2) => CapIdsRevRE(r1); CapIdsRevRE(r2);
    case Re_con(r1, r2) => CapIdsRevRE(r1); CapIdsRevRE(r2);
    case Re_quant(_, _, _, r1) => CapIdsRevRE(r1);
    case Re_capture(_, r1) => CapIdsRevRE(r1);
    case _ =>
  }

  lemma QuantIdsRevRE(re: R.regex)
    ensures PIV.QuantIds(SD.RevRE(re)) == PIV.QuantIds(re)
    decreases re
  {
    match re
    case Re_alt(r1, r2) => QuantIdsRevRE(r1); QuantIdsRevRE(r2);
    case Re_con(r1, r2) => QuantIdsRevRE(r1); QuantIdsRevRE(r2);
    case Re_quant(_, _, _, r1) => QuantIdsRevRE(r1);
    case Re_capture(_, r1) => QuantIdsRevRE(r1);
    case _ =>
  }

  /** `RevRE` preserves capture-id uniqueness (`StaticOkRE`'s `CapUnique`). */
  lemma CapUniqueRevRE(re: R.regex)
    requires PIV.CapUnique(re)
    ensures PIV.CapUnique(SD.RevRE(re))
    decreases re
  {
    match re
    case Re_alt(r1, r2) => CapUniqueRevRE(r1); CapUniqueRevRE(r2); CapIdsRevRE(r1); CapIdsRevRE(r2);
    case Re_con(r1, r2) => CapUniqueRevRE(r1); CapUniqueRevRE(r2); CapIdsRevRE(r1); CapIdsRevRE(r2);
    case Re_quant(_, _, _, r1) => CapUniqueRevRE(r1);
    case Re_capture(_, r1) => CapUniqueRevRE(r1); CapIdsRevRE(r1);
    case _ =>
  }

  /** `RevRE` preserves quant-id uniqueness (`StaticOkRE`'s `QuantUnique`). */
  lemma QuantUniqueRevRE(re: R.regex)
    requires PIV.QuantUnique(re)
    ensures PIV.QuantUnique(SD.RevRE(re))
    decreases re
  {
    match re
    case Re_alt(r1, r2) => QuantUniqueRevRE(r1); QuantUniqueRevRE(r2); QuantIdsRevRE(r1); QuantIdsRevRE(r2);
    case Re_con(r1, r2) => QuantUniqueRevRE(r1); QuantUniqueRevRE(r2); QuantIdsRevRE(r1); QuantIdsRevRE(r2);
    case Re_quant(_, _, _, r1) => QuantUniqueRevRE(r1); QuantIdsRevRE(r1);
    case Re_capture(_, r1) => QuantUniqueRevRE(r1);
    case _ =>
  }
}
