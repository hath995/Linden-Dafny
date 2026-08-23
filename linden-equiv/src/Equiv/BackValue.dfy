// L3b — captures inside positive LOOKBEHINDS: the backward-value TRANSPORT
// layer (§4.5.1 item 4 of LOOKAROUND_CAMPAIGN.md, the engine half).
//
// A matched lookbehind's capture pass replays
// `compile_to_bytecode(reverse_regex(body))` BACKWARD from the recorded cp
// (`capture_regex(Lookbehind) == reverse_regex(body)`,
// `capture_direction(Lookbehind) == Backward`). Everything value-flavoured
// upstream (the keystone `LkReplayMatchesSpec`, `ReplayCapIsBodyLeaf`, the
// whole forward simulation) is forward-only, so this file transports the
// backward replay to a forward run:
//
//   FFindMatch(compile_to_bytecode(reverse_regex(body)), str, @cp, Backward)
//     == unmirror of
//   FFindMatch(compile_to_bytecode(RevRE(body)), Reverse(str),
//              @|str|-cp, Forward)
//
// assembled from three banked pieces:
//   - Mirror.dfy's priority-preserving state isomorphism `FFindMatchMirror`,
//     which carries full register VALUES through `MirrorThread` (positions
//     map under `cp |-> |str| - cp`);
//   - OracleBuild's compile/anchor-swap commutation `CompileSwap`, lifted
//     here to `compile_to_bytecode`;
//   - SpanDuality's `RevRE` — the engine reversal PLUS the anchor swap —
//     which is exactly `SwapAnchorsRegex(reverse_regex(body))` for look-free
//     bodies (`SwapRevIsRevRE`), and which Translate carries to `RevL`
//     (`SD.TranslateRevRE`). So the forward run's SPEC side lands on
//     `RevL(Translate(body))`, where the (new, spec-side) tree mirror takes
//     over.

include "OracleBuild.dfy"

/** L3b engine transport: a lookbehind's backward capture replay IS a forward
    run of the RevRE'd body over the reversed string, register values and all. */
module LindenElkBackValue {
  import opened Std.Wrappers
  import R = RegElkRegex
  import RB = Bytecode
  import CP = Compiler
  import AI = ArrayInterp
  import AReg = Array_Regs
  import LOr = Oracle
  import LAnc = Anchors
  import LCdn = Cdn
  import NR = LindenElkNfaRep
  import OBu = LindenElkOracleBuild
  import MIR = LindenElkMirror
  import SD = LindenSpanDuality
  import LC = Chars

  // ===========================================================================
  // The two swap bridges: regex-level and bytecode-level
  // ===========================================================================

  /** For a look-free regex, anchor-swapping the engine reversal is exactly
      SpanDuality's `RevRE` (engine reversal + anchor swap in one map). */
  lemma SwapRevIsRevRE(r: R.regex)
    requires NR.LookFreeRE(r)
    ensures OBu.SwapAnchorsRegex(R.reverse_regex(r)) == SD.RevRE(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => SwapRevIsRevRE(r1); SwapRevIsRevRE(r2);
    case Re_con(r1, r2) => SwapRevIsRevRE(r1); SwapRevIsRevRE(r2);
    case Re_quant(_, _, _, r1) => SwapRevIsRevRE(r1);
    case Re_capture(_, r1) => SwapRevIsRevRE(r1);
    case Re_anchor(a) => assert MIR.SwapAnchor(a) == SD.SwapAnchorRE(a);
    case _ =>
  }

  /** The compile/anchor-swap commutation at the `compile_to_bytecode` level
      (the capture-replay form; `CompileToWriteSwap` is the build form). */
  lemma CompileToBytecodeSwap(r: R.regex)
    ensures MIR.SwapAnchorsCode(CP.compile_to_bytecode(r))
         == CP.compile_to_bytecode(OBu.SwapAnchorsRegex(r))
  {
    OBu.CompileSwap(r, 0, CP.Progress);
    OBu.SwapAnchorsFlatten(CP.compile(r, 0, CP.Progress).0, [RB.Accept]);
    assert MIR.SwapAnchorsCode([RB.Accept]) == [RB.Accept];
  }

  // ===========================================================================
  // The mirrored start state at an ARBITRARY cp (the replay anchors at the
  // recorded gate position, not at `init_cp`)
  // ===========================================================================

  /** The backward replay's start state at `cp` mirrors to the forward start
      state at `|str| - cp` over the reversed string. */
  lemma FInitStateMirrorAt(c: RB.code, str: string, cp: int, cap: AReg.Regs,
                           lk: AReg.Regs, qt: AReg.Regs, n: int)
    requires n == |str|
    ensures MIR.MirrorState(AI.FInitState(c, cp, cap, lk, qt, 0,
                                          AI.cp_context(cp, str, LAnc.Backward)), n)
         == AI.FInitState(MIR.SwapAnchorsCode(c), MIR.Mirror(cp, n),
                          MIR.MirrorRegs(cap, n), MIR.MirrorRegs(lk, n),
                          MIR.MirrorRegs(qt, n), 0,
                          AI.cp_context(MIR.Mirror(cp, n), LC.Reverse(str), LAnc.Forward))
  {
    MIR.CpContextMirror(str, cp);
    MIR.SwapAnchorsCodeLen(c);
    var bt := AI.init_thread(cap, lk, qt);
    assert MIR.MirrorThread(bt, n)
        == AI.init_thread(MIR.MirrorRegs(cap, n), MIR.MirrorRegs(lk, n),
                          MIR.MirrorRegs(qt, n));
    assert MIR.MirrorThreads([bt], n) == [MIR.MirrorThread(bt, n)];
    assert MIR.MirrorBlocked([], n) == [];
  }

  // ===========================================================================
  // THE PAYOFF: the lookbehind capture replay, transported
  // ===========================================================================

  /** A lookbehind's backward capture replay over `str` from `cp` — bytecode
      `compile_to_bytecode(reverse_regex(body))`, any start registers — is the
      mirror of the FORWARD run of `compile_to_bytecode(RevRE(body))` over
      `Reverse(str)` from `|str| - cp`: same match/no-match, and the winning
      thread's registers correspond value-for-value under `v |-> |str| - v`. */
  lemma BackwardReplayMirror(body: R.regex, str: string, cp: int, cap: AReg.Regs,
                             lk: AReg.Regs, qt: AReg.Regs, ov: LOr.OracleView,
                             cdn: LCdn.cdns, n: int)
    requires n == |str| && |ov| == n + 1
    requires 0 <= cp <= n
    requires NR.LookFreeRE(body)
    ensures
      var bc := CP.compile_to_bytecode(R.reverse_regex(body));
      var initsB := AI.FInitState(bc, cp, cap, lk, qt, 0,
                                  AI.cp_context(cp, str, LAnc.Backward));
      var bcF := CP.compile_to_bytecode(SD.RevRE(body));
      var initsF := AI.FInitState(bcF, MIR.Mirror(cp, n),
                                  MIR.MirrorRegs(cap, n), MIR.MirrorRegs(lk, n),
                                  MIR.MirrorRegs(qt, n), 0,
                                  AI.cp_context(MIR.Mirror(cp, n), LC.Reverse(str),
                                                LAnc.Forward));
      var resB := AI.FFindMatch(bc, str, initsB, ov, LAnc.Backward, cdn);
      var resF := AI.FFindMatch(bcF, LC.Reverse(str), initsF,
                                MIR.MirrorView(ov, n), LAnc.Forward,
                                MIR.SwapAnchorsCdns(cdn));
      |resB.1| == n + 1
      && resF == ((match resB.0
                   case None => None
                   case Some(t) => Some(MIR.MirrorThread(t, n))),
                  MIR.MirrorView(resB.1, n))
  {
    var bc := CP.compile_to_bytecode(R.reverse_regex(body));
    var initsB := AI.FInitState(bc, cp, cap, lk, qt, 0,
                                AI.cp_context(cp, str, LAnc.Backward));
    MIR.ReverseLen(str);
    MIR.GetCharMirror(str, cp);
    assert initsB.context.nextchar == AI.get_char(str, cp - 1);
    assert initsB.context.nextchar == AI.get_char(LC.Reverse(str), n - cp);
    assert |initsB.processed.true_set| == RB.size(bc)
        && |initsB.processed.false_set| == RB.size(bc);
    MIR.FFindMatchMirror(bc, str, initsB, ov, cdn, n);
    FInitStateMirrorAt(bc, str, cp, cap, lk, qt, n);
    CompileToBytecodeSwap(R.reverse_regex(body));
    SwapRevIsRevRE(body);
    assert MIR.SwapAnchorsCode(bc) == CP.compile_to_bytecode(SD.RevRE(body));
  }

  /** L5 T2a: the NESTED engine transport. Identical to `BackwardReplayMirror`
      but routed through `XRev := SwapAnchorsRegex o reverse_regex` instead of the
      depth-1 `SD.RevRE`, so it needs NO `LookFreeRE` premise and holds for
      arbitrarily nested bodies. The only place the depth-1 version used
      `LookFreeRE` was `SwapRevIsRevRE` (to spell the forward bytecode as
      `compile(RevRE(body))`); `CompileToBytecodeSwap` alone gives
      `SwapAnchorsCode(bc) == compile(XRev(body))` for ANY body. */
  lemma BackwardReplayMirrorNested(body: R.regex, str: string, cp: int, cap: AReg.Regs,
                                   lk: AReg.Regs, qt: AReg.Regs, ov: LOr.OracleView,
                                   cdn: LCdn.cdns, n: int)
    requires n == |str| && |ov| == n + 1
    requires 0 <= cp <= n
    ensures
      var bc := CP.compile_to_bytecode(R.reverse_regex(body));
      var initsB := AI.FInitState(bc, cp, cap, lk, qt, 0,
                                  AI.cp_context(cp, str, LAnc.Backward));
      var bcF := CP.compile_to_bytecode(OBu.SwapAnchorsRegex(R.reverse_regex(body)));
      var initsF := AI.FInitState(bcF, MIR.Mirror(cp, n),
                                  MIR.MirrorRegs(cap, n), MIR.MirrorRegs(lk, n),
                                  MIR.MirrorRegs(qt, n), 0,
                                  AI.cp_context(MIR.Mirror(cp, n), LC.Reverse(str),
                                                LAnc.Forward));
      var resB := AI.FFindMatch(bc, str, initsB, ov, LAnc.Backward, cdn);
      var resF := AI.FFindMatch(bcF, LC.Reverse(str), initsF,
                                MIR.MirrorView(ov, n), LAnc.Forward,
                                MIR.SwapAnchorsCdns(cdn));
      |resB.1| == n + 1
      && resF == ((match resB.0
                   case None => None
                   case Some(t) => Some(MIR.MirrorThread(t, n))),
                  MIR.MirrorView(resB.1, n))
  {
    var bc := CP.compile_to_bytecode(R.reverse_regex(body));
    var initsB := AI.FInitState(bc, cp, cap, lk, qt, 0,
                                AI.cp_context(cp, str, LAnc.Backward));
    MIR.ReverseLen(str);
    MIR.GetCharMirror(str, cp);
    assert initsB.context.nextchar == AI.get_char(str, cp - 1);
    assert initsB.context.nextchar == AI.get_char(LC.Reverse(str), n - cp);
    assert |initsB.processed.true_set| == RB.size(bc)
        && |initsB.processed.false_set| == RB.size(bc);
    MIR.FFindMatchMirror(bc, str, initsB, ov, cdn, n);
    FInitStateMirrorAt(bc, str, cp, cap, lk, qt, n);
    CompileToBytecodeSwap(R.reverse_regex(body));
    assert MIR.SwapAnchorsCode(bc)
        == CP.compile_to_bytecode(OBu.SwapAnchorsRegex(R.reverse_regex(body)));
  }
}
