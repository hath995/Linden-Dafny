// L3b item 4, step 3 (THE KEYSTONE): LkReplayMatchesSpecLB — the per-lookaround
// value theorem for positive LOOKBEHINDS. Sibling to the L3a keystone
// LindenElkMain.LkReplayMatchesSpec (lookaHEAD). Includes both MainTheorem.dfy
// (ReplayCapIsBodyLeaf / GmAgreeOn / TreeResGmFrame) and LookBehindValue.dfy
// (BackBodyEngineTie + the RevRE statics), plus BackValue's BackwardReplayMirror.
//
// The engine's lookbehind capture replay runs BACKWARD over
// compile_to_bytecode(reverse_regex(body)); BackwardReplayMirror transports it to
// a FORWARD run of compile_to_bytecode(RevRE(body)) over Reverse(str), which the
// forward L3a keystone ReplayCapIsBodyLeaf can read as a spec tree leaf. The
// reversed-span quirk (item 0) surfaces as SwapGm: the engine's raw readout of
// the mirrored fresh caps is the endpoint SWAP of the ordered spec leaf.
//
// The assembly is split so no single SMT context carries both the engine
// FFindMatch facts AND the spec tree-mirror facts: LBEngineLeaf owns the engine
// half, LkReplayMatchesSpecLB the spec/value half.
module LindenLookBehindKeystone {
  import opened Std.Wrappers
  import M = LindenElkMain
  import LBV = LindenLookBehindValue
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
  import RC = Charclasses
  import NR = LindenElkNfaRep
  import MIR = LindenElkMirror
  import SD = LindenSpanDuality
  import LC = Chars
  import T = LindenElkTranslate
  import PIV = LindenElkPikeInv
  import CM = LindenElkClockMono
  import AR = LindenElkActionsRep
  import PSM = LindenElkPikeSim
  import OS = LindenElkOracleSpec
  import LL = LindenElkLookLeaves
  import EL = LindenElkEntryLk
  import SSx = StrictSuffix
  import LG = Groups
  import LS = Semantics
  import LT = Tree
  import L = Regex
  import WP = WarblrePrimitives
  import FU = FunctionalUtils

  // ===========================================================================
  // Engine register upper bound: a FORWARD FFindMatch over a length-n string
  // leaves every capture position <= n (VmCapsLE is a forward invariant — caps
  // stay <= cp, and cp only grows). Needed to feed GmOfLiveMirror / BackBodyEngineTie.
  // ===========================================================================

  lemma RegsValsLEMono(regs: AReg.ARegs, B: int, B': int)
    requires CM.RegsValsLE(regs, B) && B <= B'
    ensures CM.RegsValsLE(regs, B')
  {}

  /** `FConsume` preserves `VmCapsLE` (it only moves blocked→active with pc+1;
      capture banks and cp are untouched). Mirrors `CM.FConsumeRegsWf`. */
  lemma FConsumeCapsLE(s: AI.VmState)
    requires CM.VmCapsLE(s)
    ensures CM.VmCapsLE(AI.FConsume(s))
    decreases |s.blocked|
  {
    if |s.blocked| == 0 { return; }
    var t := s.blocked[0].0;
    var ce := s.blocked[0].1;
    var s1 := s.(blocked := s.blocked[1..]);
    assert s.blocked[0] in s.blocked;
    assert forall x | x in s1.blocked :: x in s.blocked;
    var s2 := if RC.is_accepted(s1.context.nextchar, ce)
              then s1.(active := [t.(exit_allowed := true, pc := t.pc + 1)] + s1.active)
              else s1;
    assert CM.VmCapsLE(s2) by {
      assert s2.bestmatch == s.bestmatch && s2.cp == s.cp;
      forall t2 | t2 in s2.active ensures CM.RegsValsLE(t2.capture_regs, s2.cp) {
        if t2 != t.(exit_allowed := true, pc := t.pc + 1) { assert t2 in s.active; }
        else { assert CM.RegsValsLE(t.capture_regs, s.cp); }
      }
      forall tb | tb in s2.blocked ensures CM.RegsValsLE(tb.0.capture_regs, s2.cp) {
        assert tb in s.blocked;
      }
    }
    FConsumeCapsLE(s2);
  }

  /** A whole FORWARD search records only capture cps `<= |str|`. Mirrors
      `LindenElkMain.FFindMatchThreadFacts`, carrying `VmCapsLE` (not `VmRegsWf`). */
  lemma FFindMatchCapsLE(c: RB.code, str: string, s: AI.VmState, ov: LOr.OracleView, cdn: LCdn.cdns)
    requires |s.processed.true_set| == RB.size(c) && |s.processed.false_set| == RB.size(c)
    requires s.context.nextchar == AI.get_char(str, s.cp)
    requires 0 <= s.cp <= |str|
    requires CM.VmCapsLE(s)
    ensures var r := AI.FFindMatch(c, str, s, ov, LAnc.Forward, cdn).0;
      r.Some? ==> CM.RegsValsLE(r.value.capture_regs, |str|)
    decreases |str| - s.cp
  {
    var dir := LAnc.Forward;
    var s0 := s.(cdn := LCdn.build_cdn_v(cdn, s.cp, ov, s.context, dir));
    assert CM.VmCapsLE(s0) by {
      assert s0.active == s.active && s0.blocked == s.blocked && s0.bestmatch == s.bestmatch
          && s0.cp == s.cp;
    }
    CM.FAdvanceEpsilonCapsLE(c, s0, ov, dir);
    var (s1, ov1) := AI.FAdvanceEpsilon(c, s0, ov, dir);
    assert s1.cp == s.cp;
    if |s1.blocked| == 0 {
      assert AI.FFindMatch(c, str, s, ov, dir, cdn).0 == s1.bestmatch;
      if s1.bestmatch.Some? { RegsValsLEMono(s1.bestmatch.value.capture_regs, s1.cp, |str|); }
    } else if s1.context.nextchar.None? {
      assert AI.FFindMatch(c, str, s, ov, dir, cdn).0 == s1.bestmatch;
      if s1.bestmatch.Some? { RegsValsLEMono(s1.bestmatch.value.capture_regs, s1.cp, |str|); }
    } else {
      assert AI.get_char(str, s.cp).Some?;
      assert 0 <= s.cp < |str|;
      FConsumeCapsLE(s1);
      var s2 := AI.FConsume(s1);
      var s3 := s2.(processed := AI.init_bpcset(RB.size(c)), isblocked := AI.init_pcset(RB.size(c)),
                    cdn := LCdn.init_cdn(), cp := AI.incr_cp(s2.cp, dir));
      var newchar := AI.get_char(str, s3.cp - AI.cp_offset(dir));
      var s4 := s3.(context := LAnc.update_context(s3.context, newchar));
      assert s4.cp == s.cp + 1;
      assert s4.context.nextchar == AI.get_char(str, s4.cp);
      assert s2.cp == s.cp;
      assert CM.VmCapsLE(s4) by {
        assert s4.active == s2.active && s4.blocked == s2.blocked && s4.bestmatch == s2.bestmatch;
        forall t2 | t2 in s4.active ensures CM.RegsValsLE(t2.capture_regs, s4.cp) {
          RegsValsLEMono(t2.capture_regs, s2.cp, s4.cp);
        }
        forall tb | tb in s4.blocked ensures CM.RegsValsLE(tb.0.capture_regs, s4.cp) {
          RegsValsLEMono(tb.0.capture_regs, s2.cp, s4.cp);
        }
        if s4.bestmatch.Some? { RegsValsLEMono(s4.bestmatch.value.capture_regs, s2.cp, s4.cp); }
      }
      FFindMatchCapsLE(c, str, s4, ov1, cdn);
      assert AI.FFindMatch(c, str, s, ov, dir, cdn) == AI.FFindMatch(c, str, s4, ov1, dir, cdn);
    }
  }

  // ===========================================================================
  // Small structural bridges
  // ===========================================================================

  /** The BACKWARD run's capture bank lies in `[-1, n]` — WITHOUT a backward
      caps-LE lemma. From `rfF.caps == MirrorRegs(raB.caps)` (BackwardReplayMirror)
      + the FORWARD bound on `rfF.caps` (`FFindMatchCapsLE`, rfF is forward) + the
      clock-coupling of `CapRegWf` on both banks: where `rfF` is present,
      `n - raB.a_cp >= 0 ⟹ raB.a_cp <= n`; where `rfF` is absent, its clock is `<0`,
      and `MirrorRegs` keeps `a_clk`, so `raB`'s clock is `<0`, forcing `raB.a_cp = -1`.
      This is exactly `MirrorRegsInvol`'s precondition on `raB.caps`. */
  lemma BackCapsInRange(raBc: AReg.Regs, rfFc: AReg.Regs, n: int)
    requires rfFc == MIR.MirrorRegs(raBc, n)
    requires PIV.CapRegWf(rfFc) && PIV.CapRegWf(raBc)
    requires forall k :: AI.get_idx(rfFc.a_cp, k) <= n
    ensures forall k :: 0 <= k < |raBc.a_cp| ==> -1 <= raBc.a_cp[k] <= n
  {
    assert |rfFc.a_cp| == |raBc.a_cp|;
    assert rfFc.a_clk == raBc.a_clk;                        // MirrorRegs keeps a_clk
    forall k | 0 <= k < |raBc.a_cp|
      ensures -1 <= raBc.a_cp[k] <= n
    {
      assert rfFc.a_cp[k] == MIR.MirrorCpVal(raBc.a_cp[k], n);   // MirrorRegs def
      assert AI.get_idx(raBc.a_cp, k) == raBc.a_cp[k];
      assert raBc.a_cp[k] >= -1;                            // CapRegWf(raBc)
      if raBc.a_cp[k] >= 0 {
        if rfFc.a_cp[k] < 0 {
          // rfFc.a_cp[k] = n - raBc.a_cp[k] would be < 0; CapRegWf forces a contradiction.
          assert AI.get_idx(rfFc.a_cp, k) == rfFc.a_cp[k];
          assert AI.get_idx(rfFc.a_clk, k) < 0;             // CapRegWf(rfFc): a_cp<0 ⟹ a_clk<0
          assert AI.get_idx(rfFc.a_clk, k) == AI.get_idx(raBc.a_clk, k);
          assert AI.get_idx(raBc.a_clk, k) < 0;
          assert AI.get_idx(raBc.a_cp, k) < 0;              // CapRegWf(raBc): a_clk<0 ⟹ a_cp<0
          assert false;
        }
        assert AI.get_idx(rfFc.a_cp, k) == rfFc.a_cp[k] && rfFc.a_cp[k] <= n;   // forward bound
        // rfFc.a_cp[k] = n - raBc.a_cp[k] >= 0 ⟹ raBc.a_cp[k] <= n
      }
    }
  }

  /** The endpoint swap preserves `S`-agreement (same keys, `SwapRange` pointwise). */
  lemma SwapGmAgree(gm1: LG.GroupMap, gm2: LG.GroupMap, S: set<LG.GroupId>)
    requires M.GmAgreeOn(gm1, gm2, S)
    ensures M.GmAgreeOn(LBV.SwapGm(gm1), LBV.SwapGm(gm2), S)
  {
    forall g | g in S
      ensures (g in LBV.SwapGm(gm1) <==> g in LBV.SwapGm(gm2))
           && (g in LBV.SwapGm(gm1) ==> LBV.SwapGm(gm1)[g] == LBV.SwapGm(gm2)[g])
    {
      assert g in LBV.SwapGm(gm1) <==> g in gm1;
      assert g in LBV.SwapGm(gm2) <==> g in gm2;
      if g in LBV.SwapGm(gm1) {
        assert gm1[g] == gm2[g];
        assert LBV.SwapGm(gm1)[g] == LBV.SwapRange(gm1[g]);
        assert LBV.SwapGm(gm2)[g] == LBV.SwapRange(gm2[g]);
      }
    }
  }

  /** `RevRE` keeps the capture REGISTER set (it keeps the capture ids). */
  lemma CaptureRegsRevRE(body: R.regex)
    ensures PIV.CaptureRegs(SD.RevRE(body)) == PIV.CaptureRegs(body)
  {
    LBV.CapIdsRevRE(body);
  }

  /** `get_idx` through `MirrorRegs`' cp array is `MirrorCpVal` of the original. */
  lemma MirrorGetIdx(cap: AReg.Regs, k: int, n: int)
    ensures AI.get_idx(MIR.MirrorRegs(cap, n).a_cp, k) == MIR.MirrorCpVal(AI.get_idx(cap.a_cp, k), n)
  {
    assert MIR.MirrorRegs(cap, n).a_cp == BGM.MirrorArr(cap.a_cp, n);
    BGM.GetIdxMirror(cap.a_cp, k, n);
  }

  /** Mirroring a bank that is fresh (== init) on `S` keeps it fresh on `S`:
      `MirrorCpVal(-1) == -1` and clocks are untouched. */
  lemma MirrorRegsAgreeInit(cap: AReg.Regs, ncap: int, S: set<int>, n: int)
    requires CM.RegsAgreeInside(cap, AReg.init_regs(ncap), S)
    ensures CM.RegsAgreeInside(MIR.MirrorRegs(cap, n), AReg.init_regs(ncap), S)
  {
    var m := MIR.MirrorRegs(cap, n);
    var i0 := AReg.init_regs(ncap);
    forall k | k in S
      ensures AI.get_idx(m.a_cp, k) == AI.get_idx(i0.a_cp, k)
           && AI.get_idx(m.a_clk, k) == AI.get_idx(i0.a_clk, k)
    {
      assert AI.get_idx(i0.a_cp, k) == -1;
      assert AI.get_idx(cap.a_cp, k) == -1;                 // agrees init on S
      MirrorGetIdx(cap, k, n);
      assert MIR.MirrorCpVal(-1, n) == -1;
      assert m.a_clk == cap.a_clk;
    }
  }

  // ===========================================================================
  // The RevRE(body) static package (for ReplayCapIsBodyLeaf), qm' with EMPTY looks
  // ===========================================================================

  /** All of `StaticOkRE(qm', RevRE(body), compile(RevRE(body)), endl')` +
      `SizesOkRE(RevRE(body), ...)`, from the structural body facts. `qm'` uses
      the canonical quant map and an EMPTY look map (RevRE(body) is look-free, so
      LmapOk holds and OracleOkSuffix is vacuous). */
  lemma RevREStaticOk(body: R.regex, someView: LOr.OracleView, ncap: int, nlook: int, nquant: int)
      returns (qm': AR.QMap, endl': nat)
    requires T.TransWf(body) && NR.LookFreeRE(body) && NR.PlusFragmentRE(body)
    requires PIV.CapUnique(body) && PIV.QuantUnique(body)
    requires PSM.SizesOkRE(body, ncap, nlook, nquant)
    ensures PSM.StaticOkRE(qm', SD.RevRE(body), CP.compile_to_bytecode(SD.RevRE(body)), endl')
    ensures PSM.SizesOkRE(SD.RevRE(body), ncap, nlook, nquant)
    ensures qm'.ov == someView && qm'.looks == map[]
  {
    var re' := SD.RevRE(body);
    OS.RevREPlusFragment(body);                 // PlusFragmentRE(re')
    NR.PlusIsLookBehindFragmentRE(re');         // LookBehindFragmentRE(re')
    LBV.CapUniqueRevRE(body);
    LBV.QuantUniqueRevRE(body);
    SD.RevRETransWf(body);                       // TransWf(re')
    LBV.MaxGroupRevRE(body);
    LBV.MaxQuantRevRE(body);                     // SizesOkRE(re')

    qm' := AR.QMap(M.QmOfRE(re'), map[], someView);
    M.QmOfREEntries(re');
    M.QmapOkFromEntries(re', qm');               // QmapOk(re', qm')
    AR.PlusFragmentLmapOk(re', qm');             // LmapOk(re', qm')

    NR.CompileToBytecodeRepLookBehind(re');      // NfaRepRE + Accept + |code|==next+1
    var next := CP.compile(re', 0, CP.Progress).1;
    endl' := next as nat;
    PIV.CompileStutterTameRE(re');               // StutterTameRE(code)
  }

  // ===========================================================================
  // The ENGINE half: the backward lookbehind replay `raB` matches (None-iff) the
  // forward RevRE(body) tree's first leaf, and on a match the FRESH forward run
  // `rfF` reads that leaf as `GmOfLive(RevRE(body), rfF)` with capture cps `<= n`.
  // Composes RevREStaticOk + ReplayCapIsBodyLeaf + BackwardReplayMirror +
  // FFindMatchCapsLE. NO tree-mirror facts here (kept out of the SMT context).
  // ===========================================================================

  lemma LBEngineLeaf(rer: LW.RegExpRecord, body: R.regex, str: string, cp: nat,
                     cap: AReg.Regs, lk: AReg.Regs, qt: AReg.Regs, ov: LOr.OracleView,
                     cdns: LCdn.cdns, ncap: int, nlook: int, nquant: int, n: nat)
    requires T.TransWf(body) && NR.LookFreeRE(body) && NR.PlusFragmentRE(body)
    requires PIV.CapUnique(body) && PIV.QuantUnique(body)
    requires PSM.SizesOkRE(body, ncap, nlook, nquant)
    requires !rer.ignoreCase && !rer.multiline
    requires n == |str| && cp <= n && |ov| == n + 1
    requires CM.RegsAgreeInside(cap, AReg.init_regs(ncap), PIV.CaptureRegs(body))
    requires |qt.a_cp| == nquant && |qt.a_clk| == nquant
    ensures
      var rstr := LC.Reverse(str);
      var mcp := MIR.Mirror(cp, n);
      var ctxcF := AI.cp_context(mcp, rstr, LAnc.Forward);
      var bcF := CP.compile_to_bytecode(SD.RevRE(body));
      var inpF := SD.SwapInput(PIV.InpOfCp(str, cp));
      var t_F := FU.ComputeTr(rer, [LS.Areg(SD.RevL(T.Translate(body)))], inpF, LG.Empty, WP.Forward);
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
            && LT.FirstLeaf(t_F, inpF).value.1
                 == PIV.GmOfLive(SD.RevRE(body), rfF.value.capture_regs,
                                 rfF.value.look_regs, rfF.value.quant_regs)
            && (forall k :: AI.get_idx(AReg.as_arrays(rfF.value.capture_regs).0, k) <= n))
  {
    var re' := SD.RevRE(body);
    MIR.ReverseLen(str);
    var rstr := LC.Reverse(str);
    var mcp := MIR.Mirror(cp, n);
    var ov' := MIR.MirrorView(ov, n);
    var cdns' := MIR.SwapAnchorsCdns(cdns);
    var bcF := CP.compile_to_bytecode(re');
    var ctxcF := AI.cp_context(mcp, rstr, LAnc.Forward);
    var inpF := PIV.InpOfCp(rstr, mcp);
    assert 0 <= mcp <= n && |rstr| == n;

    // statics + qm' with empty looks
    var qm', endl' := RevREStaticOk(body, ov', ncap, nlook, nquant);
    OS.RevRELookFree(body);                      // LookFreeRE(re')
    assert LL.OracleOkSuffix(rer, qm', inpF) by {
      forall inp2: LC.Input | inp2 == inpF || SSx.IsStrictSuffix(inp2, inpF, WP.Forward)
        ensures LL.OracleOkAt(rer, qm', inp2) { }
    }
    // mirrored engine caps are fresh on RevRE(body)'s cap regs
    CaptureRegsRevRE(body);
    MirrorRegsAgreeInit(cap, ncap, PIV.CaptureRegs(body), n);
    assert CM.RegsAgreeInside(MIR.MirrorRegs(cap, n), AReg.init_regs(ncap), PIV.CaptureRegs(re'));

    // fresh forward run rfF and its capture upper bound
    var initsFresh := AI.FInitState(bcF, mcp, AReg.init_regs(ncap), AReg.init_regs(nlook),
                                    AReg.init_regs(nquant), 0, ctxcF);
    var rfF := AI.FFindMatch(bcF, rstr, initsFresh, ov', LAnc.Forward, cdns').0;
    assert ctxcF.nextchar == AI.get_char(rstr, mcp);
    CM.FInitStateCapsLE(bcF, mcp, ncap, nlook, nquant, 0, ctxcF);
    FFindMatchCapsLE(bcF, rstr, initsFresh, ov', cdns');

    // ReplayCapIsBodyLeaf @ RevRE(body): raF/rfF vs the spec tree leaf
    var bestT := M.ReplayCapIsBodyLeaf(rer, qm', re', bcF, endl', 0, rstr, mcp,
                   MIR.MirrorRegs(cap, n), MIR.MirrorRegs(lk, n), MIR.MirrorRegs(qt, n),
                   ov', cdns', ncap, nlook, nquant);
    var t_F := FU.ComputeTr(rer, [LS.Areg(T.Translate(re'))], inpF, LG.Empty, WP.Forward);
    var raF := AI.FFindMatch(bcF, rstr,
                 AI.FInitState(bcF, mcp, MIR.MirrorRegs(cap, n), MIR.MirrorRegs(lk, n),
                               MIR.MirrorRegs(qt, n), 0, ctxcF),
                 ov', LAnc.Forward, cdns').0;
    assert bestT == LT.FirstLeaf(t_F, inpF);
    assert raF.None? <==> bestT.None?;

    // bridge the proof-internal tree to the ensures' RevL form
    SD.TranslateRevRE(body);                     // Translate(re') == RevL(Translate(body))
    LBV.InpOfCpSwap(str, cp, n);                 // InpOfCp(rstr, mcp) == SwapInput(InpOfCp(str,cp))
    assert T.Translate(re') == SD.RevL(T.Translate(body));
    assert inpF == SD.SwapInput(PIV.InpOfCp(str, cp));

    // BackwardReplayMirror: the actual engine backward replay ~ raF
    BV.BackwardReplayMirror(body, str, cp, cap, lk, qt, ov, cdns, n);
    var bcB := CP.compile_to_bytecode(R.reverse_regex(body));
    var ctxcB := AI.cp_context(cp, str, LAnc.Backward);
    var raB := AI.FFindMatch(bcB, str, AI.FInitState(bcB, cp, cap, lk, qt, 0, ctxcB),
                             ov, LAnc.Backward, cdns).0;
    assert raB.None? <==> raF.None?;
    if rfF.Some? {
      assert AReg.as_arrays(rfF.value.capture_regs).0 == rfF.value.capture_regs.a_cp;
    }
  }

  // ===========================================================================
  // THE KEYSTONE (spec/value half)
  // ===========================================================================

  /** For a positive LOOKBEHIND with a look-free (plus-fragment) body: the
      engine's BACKWARD capture replay from the main thread's `cap/lk/qt`
      matches the spec `LkResult` on the body's own groups — the value tie stated
      through the reversed-span mirror (`SwapGm`), which the item-0 `NormalizeArr`
      widening reconciles at `MainExtraction`. Sibling of `LkReplayMatchesSpec`. */
  lemma LkReplayMatchesSpecLB(
      rer: LW.RegExpRecord, body: R.regex, str: string, cp: nat,
      cap: AReg.Regs, lk: AReg.Regs, qt: AReg.Regs, ov: LOr.OracleView,
      cdns: LCdn.cdns, la: R.lookaround, tlk: LT.Tree, gmMain: LG.GroupMap,
      ncap: int, nlook: int, nquant: int, n: nat)
    requires T.TransWf(body) && NR.LookFreeRE(body) && NR.PlusFragmentRE(body)
    requires PIV.CapUnique(body) && PIV.QuantUnique(body)
    requires SD.GroupOkL(T.Translate(body))
    requires CD.NoDupG(L.DefGroups(T.Translate(body)))
    requires PSM.SizesOkRE(body, ncap, nlook, nquant)
    requires !rer.ignoreCase && !rer.multiline
    requires n == |str| && cp <= n && |ov| == n + 1
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
      var bcF := CP.compile_to_bytecode(SD.RevRE(body));
      var mcp := MIR.Mirror(cp, n);
      var ctxcF := AI.cp_context(mcp, LC.Reverse(str), LAnc.Forward);
      var rfF := AI.FFindMatch(bcF, LC.Reverse(str),
                   AI.FInitState(bcF, mcp, AReg.init_regs(ncap), AReg.init_regs(nlook),
                                 AReg.init_regs(nquant), 0, ctxcF),
                   MIR.MirrorView(ov, n), LAnc.Forward, MIR.SwapAnchorsCdns(cdns)).0;
      var S := set g | g in L.DefGroups(T.Translate(body));
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
    var re' := SD.RevRE(body);
    var inp := PIV.InpOfCp(str, cp);
    var S := set g | g in L.DefGroups(tr);
    MIR.ReverseLen(str);
    var rstr := LC.Reverse(str);
    var mcp := MIR.Mirror(cp, n);
    var ov' := MIR.MirrorView(ov, n);
    var cdns' := MIR.SwapAnchorsCdns(cdns);
    var bcF := CP.compile_to_bytecode(re');
    var ctxcF := AI.cp_context(mcp, rstr, LAnc.Forward);

    // ---- engine side (LBEngineLeaf): raB ~ RevRE(body) forward leaf ----
    LBEngineLeaf(rer, body, str, cp, cap, lk, qt, ov, cdns, ncap, nlook, nquant, n);
    var rfF := AI.FFindMatch(bcF, rstr,
                 AI.FInitState(bcF, mcp, AReg.init_regs(ncap), AReg.init_regs(nlook),
                               AReg.init_regs(nquant), 0, ctxcF),
                 ov', LAnc.Forward, cdns').0;
    var bcB := CP.compile_to_bytecode(R.reverse_regex(body));
    var ctxcB := AI.cp_context(cp, str, LAnc.Backward);
    var raB := AI.FFindMatch(bcB, str, AI.FInitState(bcB, cp, cap, lk, qt, 0, ctxcB),
                             ov, LAnc.Backward, cdns).0;

    // ---- tree core (BackBodyGmTie): rf_g == the mirror-tree first leaf; the
    //      LBEngineLeaf ensures already speak of this same rf_g ----
    MIR.ReverseLen(str[..cp]);                   // |Reverse(str[..cp])| == cp
    assert n == |inp.pref| + |inp.next|;
    LBV.BackBodyGmTie(rer, tr, inp, n);
    var tF_g := FU.ComputeTr(rer, [LS.Areg(SD.RevL(tr))], SD.SwapInput(inp), LG.Empty, WP.Forward);
    var tB := FU.ComputeTr(rer, [LS.Areg(tr)], inp, LG.Empty, WP.Backward);
    var rb := LT.TreeRes(tB, LG.Empty, inp, WP.Backward);
    var rf_g := LT.FirstLeaf(tF_g, SD.SwapInput(inp));

    // ---- tlk == tB (look-free, gm-indep), and the LkResult fold ----
    EL.TranslateNoLkBr(body);
    EL.ComputeTrGmIndepLk(rer, tr, inp, gmMain, WP.Backward);
    EL.ComputeTrNoLK(rer, tr, inp, gmMain, WP.Backward);
    assert tlk == tB;
    M.TreeResGmFrame(tlk, gmMain, LG.Empty, inp, WP.Backward, S);
    var lkr := LS.LkResult(T.TrLookaround(la), tlk, gmMain, inp);
    assert T.TrLookaround(la) == L.LookBehind;
    assert L.Positivity(L.LookBehind) && L.LkDir(L.LookBehind) == WP.Backward;
    assert lkr == (match LT.TreeRes(tlk, gmMain, inp, WP.Backward)
                   case None => None
                   case Some(pair) => Some(pair.1));
    assert LT.TreeRes(tlk, LG.Empty, inp, WP.Backward) == rb;

    // ---- None-iff (the gate) ----
    assert rb.None? <==> rf_g.None?;                    // BackBodyGmTie
    assert raB.None? <==> lkr.None?;

    // ---- value ----
    if raB.Some? {
      assert rf_g.Some? && rfF.Some?;
      assert PIV.GmOfLive(re', rfF.value.capture_regs, rfF.value.look_regs, rfF.value.quant_regs)
          == rf_g.value.1;
      assert forall k :: AI.get_idx(AReg.as_arrays(rfF.value.capture_regs).0, k) <= n;
      LBV.BackBodyEngineTie(rer, body, inp, n,
                            rfF.value.capture_regs, rfF.value.look_regs, rfF.value.quant_regs);
      assert PIV.GmOfLive(body, MIR.MirrorRegs(rfF.value.capture_regs, n),
                                MIR.MirrorRegs(rfF.value.look_regs, n),
                                MIR.MirrorRegs(rfF.value.quant_regs, n))
          == LBV.SwapGm(rb.value.1);
      assert M.GmAgreeOn(lkr.value, rb.value.1, S);      // TreeResGmFrame (tlk==tB)
      SwapGmAgree(lkr.value, rb.value.1, S);
    }
  }

  /** THE GATE-STEP CRUX, packaged for `GateStepValueLB`. For a positive LOOKBEHIND,
      the FRESH backward body match `raB` (= `FreshBodyMatch(l)` at cap=init) ties to
      the SPEC `LkResult` value through the endpoint swap directly:
      `SwapGm(LkResult.value)` agrees on `Sbody` with `GmOfLive(body, raB.*)`. This
      re-expresses the keystone's `rfF`-flavoured statement in terms of the actual
      backward run, using `BackwardReplayMirror` (`rfF==MirrorThread(raB)`),
      `BackCapsInRange`+`MirrorRegsInvol` (caps involution — the only bank `GmOfLive`
      reads positionally), and `GmOfLiveClkCong` (look/quant banks agree on clocks). */
  lemma BackFreshBodyGmTie(
      rer: LW.RegExpRecord, body: R.regex, str: string, cp: nat,
      ov: LOr.OracleView, cdns: LCdn.cdns, la: R.lookaround, tlk: LT.Tree, gmMain: LG.GroupMap,
      ncap: int, nlook: int, nquant: int, n: nat)
    requires T.TransWf(body) && NR.LookFreeRE(body) && NR.PlusFragmentRE(body)
    requires PIV.CapUnique(body) && PIV.QuantUnique(body)
    requires SD.GroupOkL(T.Translate(body))
    requires CD.NoDupG(L.DefGroups(T.Translate(body)))
    requires PSM.SizesOkRE(body, ncap, nlook, nquant)
    requires !rer.ignoreCase && !rer.multiline
    requires n == |str| && cp <= n && |ov| == n + 1
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
      var Sbody := set g | g in L.DefGroups(T.Translate(body));
      (raB.None? <==> lkr.None?)
      && (raB.Some? ==>
            lkr.Some?
            && M.GmAgreeOn(LBV.SwapGm(lkr.value),
                           PIV.GmOfLive(body, raB.value.capture_regs, raB.value.look_regs,
                                        raB.value.quant_regs),
                           Sbody))
  {
    var inp := PIV.InpOfCp(str, cp);
    var cap := AReg.init_regs(ncap);
    var lk := AReg.init_regs(nlook);
    var qt := AReg.init_regs(nquant);
    // keystone preconditions at cap=lk=qt=init
    assert CM.RegsAgreeInside(cap, AReg.init_regs(ncap), PIV.CaptureRegs(body));
    assert |qt.a_cp| == nquant && |qt.a_clk| == nquant;
    LkReplayMatchesSpecLB(rer, body, str, cp, cap, lk, qt, ov, cdns, la, tlk, gmMain,
                          ncap, nlook, nquant, n);

    var bcB := CP.compile_to_bytecode(R.reverse_regex(body));
    var ctxcB := AI.cp_context(cp, str, LAnc.Backward);
    var raB := AI.FFindMatch(bcB, str, AI.FInitState(bcB, cp, cap, lk, qt, 0, ctxcB),
                             ov, LAnc.Backward, cdns).0;
    var bcF := CP.compile_to_bytecode(SD.RevRE(body));
    var mcp := MIR.Mirror(cp, n);
    var ctxcF := AI.cp_context(mcp, LC.Reverse(str), LAnc.Forward);
    var rfF := AI.FFindMatch(bcF, LC.Reverse(str),
                 AI.FInitState(bcF, mcp, AReg.init_regs(ncap), AReg.init_regs(nlook),
                               AReg.init_regs(nquant), 0, ctxcF),
                 MIR.MirrorView(ov, n), LAnc.Forward, MIR.SwapAnchorsCdns(cdns)).0;
    var lkr := LS.LkResult(T.TrLookaround(la), tlk, gmMain, inp);
    var Sbody := set g | g in L.DefGroups(T.Translate(body));

    if raB.Some? {
      // ---- rfF == MirrorThread(raB) (BackwardReplayMirror; init banks mirror to init) ----
      MIR.MirrorInitRegs(ncap, n); MIR.MirrorInitRegs(nlook, n); MIR.MirrorInitRegs(nquant, n);
      BV.BackwardReplayMirror(body, str, cp, cap, lk, qt, ov, cdns, n);
      assert rfF.Some? && rfF.value == MIR.MirrorThread(raB.value, n);
      assert rfF.value.capture_regs == MIR.MirrorRegs(raB.value.capture_regs, n);
      assert rfF.value.look_regs == MIR.MirrorRegs(raB.value.look_regs, n);
      assert rfF.value.quant_regs == MIR.MirrorRegs(raB.value.quant_regs, n);

      // ---- wf + forward bound (rfF is forward; LBEngineLeaf gives rfF.caps <= n) ----
      LBEngineLeaf(rer, body, str, cp, cap, lk, qt, ov, cdns, ncap, nlook, nquant, n);
      assert forall k :: AI.get_idx(AReg.as_arrays(rfF.value.capture_regs).0, k) <= n;
      // CapRegWf(raB.caps): backward fresh-match wf.
      M.FreshMatchWfLB(bcB, str, cp, ov, cdns, body, ncap, nlook, nquant);
      assert PIV.CapRegWf(raB.value.capture_regs);
      // CapRegWf(rfF.caps): forward fresh-match wf over RevRE(body).
      OS.RevREPlusFragment(body);
      NR.PlusIsLookBehindFragmentRE(SD.RevRE(body));
      LBV.CapUniqueRevRE(body);
      LBV.QuantUniqueRevRE(body);
      LBV.MaxGroupRevRE(body);
      LBV.MaxQuantRevRE(body);
      MIR.ReverseLen(str);
      M.FreshMatchWf(bcF, LC.Reverse(str), mcp, MIR.MirrorView(ov, n), MIR.SwapAnchorsCdns(cdns),
                     SD.RevRE(body), ncap, nlook, nquant);
      assert PIV.CapRegWf(rfF.value.capture_regs);

      // ---- caps: MirrorRegs(rfF.caps) == raB.caps (the only positionally-read bank) ----
      BackCapsInRange(raB.value.capture_regs, rfF.value.capture_regs, n);
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
      assert PIV.GmOfLive(body, MIR.MirrorRegs(rfF.value.capture_regs, n),
                                MIR.MirrorRegs(rfF.value.look_regs, n),
                                MIR.MirrorRegs(rfF.value.quant_regs, n))
          == PIV.GmOfLive(body, raB.value.capture_regs, raB.value.look_regs, raB.value.quant_regs);
    }
  }
}
