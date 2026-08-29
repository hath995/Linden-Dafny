// L3a — THE LIFT: the standalone parallel simulation VM ↔ machine B.
//
// SCAFFOLD (2026-08-02): definitions are REAL and resolve; the lemmas are
// BODILESS — each carries a FILL note naming its template and ingredients.
// Fill order (historical; `TtLkSameTree` was superseded by the quotient
// `ETreeRepLkDeterm` and its dead admitted statement removed 2026-08-25): TtLkSameTree → GateStepValue → LiftInit → LiftAdvanceEpsilon →
// LiftConsume → LiftFindMatch → LiftEndpoint. Verify per-symbol as you go
// (bodiless lemmas verify trivially and warn; the warnings disappear as
// bodies land).
//
// WHAT THIS PROVES, once filled: the VM run induces a valid LK-aware
// PikeTree trace (PikeTreeLk) on the SPEC tree t, whose states pair with the
// VM's — per thread, the B-side group map `gmt` carries the t-side
// accumulated captures, tied OUTSIDE S to GmOfLive(thread regs) and INSIDE S
// to the fresh body replay at the thread's own a_cp[l]. At the end,
// PTL.PikeTreeLkComputesFirstLeaf pins B's best to FirstLeaf(t, inp), so the
// winner's leaf values — inside-look groups INCLUDED — equal the engine's
// reconstruction with no position theorem and no leaf-occurrence reasoning.
//
// WHY NO A-MACHINE / NO PikeSimRE COMPOSITION: B's own correctness layer
// (PtsPreservationLk) already handles priority and memoization soundness on
// the t side, so the lift only has to produce LEGAL B steps mirroring VM
// behavior; the one genuinely shared obligation with the old sim is the
// processed↔seen pairing (SeenRepLk below, mirrored from SeenInclusionRE).
// The existing sim and its files stay UNTOUCHED.
//
// GRANULARITY: the ClockMono frame trio (FAdvanceEpsilon / FConsume /
// FFindMatch parallel induction) — the shape that went first-try five times
// in this campaign (FFindMatchLookCpOk, LookClkSet, LookOracleTrue,
// FFindMatchLookFrame, FFindMatchCapWriteFrame). LiftAdvanceEpsilon's
// per-instruction cases mirror those recursions; the CheckOracle case is the
// only one that STEPS B through a gate, and its value content is
// GateStepValue = the proven keystone LkReplayMatchesSpec at cp = s1.cp.

/** The lift: a per-thread pairing between the RegElk VM and the LK-aware
    PikeTree machine on the SPEC tree, whose group-map tie carries the
    reconstructed inside-look capture values. Scaffold — lemmas are bodiless. */
module LindenElkLiftSimChain {
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
  import SS = SeenSets
  import AR = LindenElkActionsRep
  import EL = LindenElkEntryLk
  import WO = LindenElkWalkOk
  import ATR = LindenElkActionsTreeRep
  import PIV = LindenElkPikeInv
  import CM = LindenElkClockMono
  import PTL = LindenElkPikeTreeLk
  import M = LindenElkMain
  import LBK = LindenLookBehindKeystone
  import FG = LindenElkFlipGate
  import FC = LindenElkFlipClosed
  import FST = LindenElkFlipStatics
  import FK = LindenElkFlipKeystone
  import FO = LindenElkFlipOracle
  import FD = LindenElkFlipDisc
  import FM = LindenElkFlipMirror
  import FR = LindenElkFlipRev
  import TRM = LindenTreeResMirror
  import BGM = LindenBackGmMirror
  import LBV = LindenLookBehindValue
  import BV = LindenElkBackValue
  import SD = LindenSpanDuality
  import CD = LindenCloseDisc
  import OS = LindenElkOracleSpec
  import OB = LindenElkOracleBuild
  import OBr = LindenElkOracleBridge
  import ORc = LindenElkOracleReach
  import MIR = LindenElkMirror
  import OBV = LindenElkOracleBridgeV
  import ODV = LindenElkOracleDecompV
  import OAV = LindenElkOracleAcceptV
  import OMV = LindenElkOracleMirrorV
  import T = LindenElkTranslate
  import RC = Charclasses
  import LL = LindenElkLookLeaves
  import LFU = FunctionalUtils
  import FS = FunctionalSemantics
  import SSx = StrictSuffix
  import LN = WarblreNumeric
  import PSM = LindenElkPikeSim
  import RL = LindenElkRegsLaws
  import LKC = LindenElkLookCapture
  import OE = LindenElkOracleEntry
  import LES = LindenElkSpec
  import WOE = LindenElkWalkOkEntry
  import WkE = LindenElkWalkOkEntry
  import TT = LindenElkTreeThread
  import NUL = LindenElkNullable
  import CE = LindenElkCheckErase
  import TREP = LindenElkTreeRep
  import LTB = LindenElkLookTables
  import NI = LindenElkNestInv
  import opened LindenElkLiftSimCore
  import opened LindenElkLiftSimOracle

  /** The tb-pairing walk at a `pc`, WITH the `GateAheadClear` invariant and the
      same `tr_begin`-style BeginLoop stutter as `TtLk`. `ThreadRepLk` uses this
      (rather than a bare `ActionsRepL` existential) so the per-thread pairing
      survives a `BeginLoop` worklist step. Off a BeginLoop pc it is exactly the
      old existential. */
  ghost predicate WalkPairLk(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                             tb: LT.Tree, gmt: LG.GroupMap, pc: nat, ea: bool)
    decreases RB.size(code) - pc
  {
    (pc < RB.size(code) && NR.GetPcRE(code, pc) == Some(RB.BeginLoop)
     && WalkPairLk(rer, qm, code, inp, tb, gmt, pc + 1, false))
    // SQC see-through (2026-08-07 session 5): mirror of TtLk's — the iteration
    // arm's `GroupActionT(Reset, ·)` pairs AT the `SetQuantToClock` pc with the
    // child walking at the RESET-updated map (which is what re-clears the
    // body's gates for `GateAheadClear` downstream).
    || (pc < RB.size(code)
        && exists q: int ::
          NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(q, false))
          && q in qm.quants
          && tb.GroupActionT? && tb.g == LG.Reset(qm.quants[q])
          && WalkPairLk(rer, qm, code, inp, tb.t,
                        LG.GMUpdate(tb.g, LC.Idx(inp), gmt), pc + 1, ea))
    || (exists acts: LS.Actions, b: BS.LoopBool ::
          AR.ActionsRepL(rer, qm, acts, code, pc)
          && EL.PikeLkActions(acts)
          && ATR.EaOf(b) == ea
          && EL.BoolTreeLk(rer, acts, inp, b, tb)
          && GateAheadClear(acts, gmt)
          // Defs walk-invariant (carrier REPLACED 2026-08-07 session 5:
          // `NoDupSeq(AllDefsActs)` is FALSE after any quantifier unfold —
          // the (C1,C2,C3) `WalkDefsOk` is the quantifier-stable form; the
          // CheckOracle merge consumes C1 via `RegexTopGateSubTopLk`).
          && WalkDefsOk(acts))
  }

  /** The full per-thread pairing: the B-side `(tb, gmt)` corresponds to VM
      thread `th` — walk-represented at `th.pc`, reset-clear ahead, and
      value-tied on both sides of `S`. */
  ghost predicate ThreadRepLk(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code,
                              inp: LC.Input, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
                              S: set<LG.GroupId>, tb: LT.Tree, gmt: LG.GroupMap, th: AI.Thread,
                              ncap: int, nlook: int, nquant: int) {
    th.pc >= 0
    && WalkPairLk(rer, qm, code, inp, tb, gmt, th.pc as nat, th.exit_allowed)
    && GmtTieOutside(re, th, gmt, S)
    && GmtTieInside(crv, str, ov, th, gmt, S, ncap, nlook, nquant)
  }

  /** (L4 NESTED) The per-thread pairing with the depth-1-hardwired
      `GmtTieInside` conjunct DROPPED. Under look nesting an inside-S group can
      be captured inside a NESTED look, for which `GmtTieInside` (which pins the
      value to a SINGLE fresh-body replay `FreshBodyMatch(crv, str, l, ..)`) is
      FALSE; the nested endpoint closes those inner groups post-hoc via the
      already-proven components, so it drops the conjunct here. Everything else
      (`WalkPairLk`, `GmtTieOutside`, and the structural `th.pc >= 0`) is kept
      verbatim. */
  ghost predicate ThreadRepLkNested(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code,
                                    inp: LC.Input, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
                                    S: set<LG.GroupId>, tb: LT.Tree, gmt: LG.GroupMap, th: AI.Thread,
                                    ncap: int, nlook: int, nquant: int) {
    th.pc >= 0
    && WalkPairLk(rer, qm, code, inp, tb, gmt, th.pc as nat, th.exit_allowed)
    && GmtTieOutside(re, th, gmt, S)
  }

  /** Active lists pair index-wise, in order (priority is positional). */
  ghost predicate ActiveRepLk(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code,
                              inp: LC.Input, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
                              S: set<LG.GroupId>, tl: seq<(LT.Tree, LG.GroupMap)>, vl: seq<AI.Thread>,
                              ncap: int, nlook: int, nquant: int)
    decreases tl
  {
    (|tl| == 0 && |vl| == 0)
    || (|tl| > 0 && |vl| > 0
        && ThreadRepLk(rer, qm, re, code, inp, crv, str, ov, S, tl[0].0, tl[0].1, vl[0],
                       ncap, nlook, nquant)
        && ActiveRepLk(rer, qm, re, code, inp, crv, str, ov, S, tl[1..], vl[1..],
                       ncap, nlook, nquant))
  }

  /** `WalkPairLk` rebuilt on `EL.PikeLkActionsRec` (recursive fragment). */
  ghost predicate WalkPairLkRec(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                                tb: LT.Tree, gmt: LG.GroupMap, pc: nat, ea: bool)
    decreases RB.size(code) - pc
  {
    (pc < RB.size(code) && NR.GetPcRE(code, pc) == Some(RB.BeginLoop)
     && WalkPairLkRec(rer, qm, code, inp, tb, gmt, pc + 1, false))
    || (pc < RB.size(code)
        && exists q: int ::
          NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(q, false))
          && q in qm.quants
          && tb.GroupActionT? && tb.g == LG.Reset(qm.quants[q])
          && WalkPairLkRec(rer, qm, code, inp, tb.t,
                           LG.GMUpdate(tb.g, LC.Idx(inp), gmt), pc + 1, ea))
    || (exists acts: LS.Actions, b: BS.LoopBool ::
          AR.ActionsRepL(rer, qm, acts, code, pc)
          && EL.PikeLkActionsRec(acts)
          && ATR.EaOf(b) == ea
          && EL.BoolTreeLk(rer, acts, inp, b, tb)
          && GateAheadClear(acts, gmt)
          && WalkDefsOk(acts))
  }

  /** `ThreadRepLkNested` (the `GmtTieInside`-free per-thread tie) on
      `WalkPairLkRec`. */
  ghost predicate ThreadRepLkRec(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code,
                                 inp: LC.Input, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
                                 S: set<LG.GroupId>, tb: LT.Tree, gmt: LG.GroupMap, th: AI.Thread,
                                 ncap: int, nlook: int, nquant: int) {
    th.pc >= 0
    && WalkPairLkRec(rer, qm, code, inp, tb, gmt, th.pc as nat, th.exit_allowed)
    && GmtTieOutside(re, th, gmt, S)
  }

  /** `ThreadRepLkCNested` riding `ThreadRepLkRec`. */
  ghost predicate ThreadRepLkCRec(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code,
                                  inp: LC.Input, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
                                  S: set<LG.GroupId>, tcan: LT.Tree, gmt: LG.GroupMap, th: AI.Thread,
                                  ncap: int, nlook: int, nquant: int) {
    th.pc >= 0
    && TreeRepLkRE(rer, qm, code, inp, tcan, th.pc as nat, th.exit_allowed)
    && exists traw: LT.Tree ::
      CE.ProgErase(traw) == CE.ProgErase(tcan)
      && ThreadRepLkRec(rer, qm, re, code, inp, crv, str, ov, S, traw, gmt, th, ncap, nlook, nquant)
  }

  /** `ActiveRepLkCNested` riding `ThreadRepLkCRec`. */
  ghost predicate ActiveRepLkCRec(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code,
                                  inp: LC.Input, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
                                  S: set<LG.GroupId>, tl: seq<(LT.Tree, LG.GroupMap)>, vl: seq<AI.Thread>,
                                  ncap: int, nlook: int, nquant: int)
    decreases tl
  {
    (|tl| == 0 && |vl| == 0)
    || (|tl| > 0 && |vl| > 0
        && ThreadRepLkCRec(rer, qm, re, code, inp, crv, str, ov, S, tl[0].0, tl[0].1, vl[0],
                           ncap, nlook, nquant)
        && ActiveRepLkCRec(rer, qm, re, code, inp, crv, str, ov, S, tl[1..], vl[1..],
                           ncap, nlook, nquant))
  }

  /** `BlockedRepLkCNested` with its raw erasure witness on `WalkPairLkRec`. */
  ghost predicate BlockedRepLkCRec(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code,
                                   inp: LC.Input, nextinp: LC.Input, crv: CP.FCompiled, str: string,
                                   ov: LOr.OracleView, S: set<LG.GroupId>,
                                   tl: seq<(LT.Tree, LG.GroupMap)>, bl: seq<(AI.Thread, RC.char_expectation)>,
                                   ncap: int, nlook: int, nquant: int)
    decreases tl
  {
    (|tl| == 0 && |bl| == 0)
    || (|tl| > 0 && |bl| > 0
        && bl[0].0.pc >= 0
        && TreeRepLkRE(rer, qm, code, nextinp, tl[0].0, (bl[0].0.pc + 1) as nat, true)
        && (exists traw: LT.Tree ::
              CE.ProgErase(traw) == CE.ProgErase(tl[0].0)
              && WalkPairLkRec(rer, qm, code, nextinp, traw, tl[0].1, (bl[0].0.pc + 1) as nat, true))
        && GmtTieOutside(re, bl[0].0, tl[0].1, S)
        && BlockedRepLkCRec(rer, qm, re, code, inp, nextinp, crv, str, ov, S, tl[1..], bl[1..],
                            ncap, nlook, nquant))
  }

  /** `LiftInvNested` on the `*Rec` pairings (`ActiveRepLkCRec`,
      `BlockedRepLkCRec`, `BestTieLkNested`). (D3) The look-path carriers are the
      TOP-LEVEL-restricted `*Top` variants: at a nested gate only the top-level
      gate lid is stamped, so the inner-lid obligations of the full carriers are
      unsatisfiable at depth >= 2. Confined to the `*Rec` tier (the depth-1/`Nested`
      `LiftInv`/`LiftInvNested` keep the full carriers). */
  ghost predicate LiftInvRec(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code,
                             crv: CP.FCompiled, str: string, ov: LOr.OracleView, S: set<LG.GroupId>,
                             bst: PT.PikeTreeState, vms: AI.VmState,
                             ncap: int, nlook: int, nquant: int) {
    match bst
    case PTS_final(bbest) => BestTieLkNestedTop(rer, re, crv, str, ov, S, bbest, vms.bestmatch, ncap, nlook, nquant)
    case PTS(inp, bactive, bbest, bblocked, bseen) =>
      0 <= vms.cp <= |str|
      && inp == PIV.InpOfCp(str, vms.cp)
      && PIV.ContextOkRE(str, vms.cp, vms.context)
      && ActiveRepLkCRec(rer, qm, re, code, inp, crv, str, ov, S, bactive, vms.active, ncap, nlook, nquant)
      && (forall nextinp :: LC.AdvanceInput(inp, WP.Forward) == Some(nextinp) ==>
                              BlockedRepLkCRec(rer, qm, re, code, inp, nextinp, crv, str, ov, S, bblocked,
                                               PIV.MatchingBlocked(LC.Reverse(vms.blocked), inp), ncap, nlook, nquant))
      && (LC.AdvanceInput(inp, WP.Forward) == None ==> bblocked == [])
      && LookNestRepCTop(re, S, bactive, vms.active)
      && (LC.AdvanceInput(inp, WP.Forward).Some? ==>
            LookNestRepBTop(re, S, bblocked, PIV.MatchingBlocked(LC.Reverse(vms.blocked), inp)))
      && LookNestBackRepCTop(re, crv, str, ov, S, bactive, vms.active, ncap, nlook, nquant)
      && (LC.AdvanceInput(inp, WP.Forward).Some? ==>
            LookNestBackRepBTop(re, crv, str, ov, S, bblocked,
                                PIV.MatchingBlocked(LC.Reverse(vms.blocked), inp), ncap, nlook, nquant))
      // (R2 DEEP CARRIER) the deep-carrier rep predicates, threaded PARALLEL to
      // the direct `LookNestBackRepCTop`/`…BTop` (same shape, `SubFirstLeafAt`
      // landed set), so the best-match tie can carry `LookNestBackTTopDeep`.
      && LookNestBackRepCTopDeep(rer, re, crv, str, ov, S, bactive, vms.active, ncap, nlook, nquant)
      && (LC.AdvanceInput(inp, WP.Forward).Some? ==>
            LookNestBackRepBTopDeep(rer, re, crv, str, ov, S, bblocked,
                                    PIV.MatchingBlocked(LC.Reverse(vms.blocked), inp), ncap, nlook, nquant))
      && BestTieLkNestedTop(rer, re, crv, str, ov, S, bbest, vms.bestmatch, ncap, nlook, nquant)
      && SeenRepLk(rer, qm, code, inp, bseen, vms.processed,
                   PIV.HdTreeOf(bactive), PIV.HeadPcOf(vms.active))
      && IsblockedRepLk(rer, qm, code, inp, bseen, vms.isblocked)
      && LL.OracleOkSuffix(rer, qm, inp)
  }

  /** THE LIFT INVARIANT: the B state pairs with the VM state. Mirrors
      `PIV.PikeInvRE`'s shape with the B-side (t-based, value-carrying)
      relations. `PTS_final` pairs through `BestTieLk` alone.

      RE-KEYED on the PLANTED CANONICAL pairing (2026-08-07): machine B runs
      the `TreeRepLkRE`-canonical trees; `ActiveRepLkC`/`BlockedRepLkC` carry
      the canonical tie per head plus the value layer through the raw
      erasure-witness (see the §(c′) header before `ThreadRepLkC`). */
  ghost predicate LiftInv(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code,
                          crv: CP.FCompiled, str: string, ov: LOr.OracleView, S: set<LG.GroupId>,
                          bst: PT.PikeTreeState, vms: AI.VmState,
                          ncap: int, nlook: int, nquant: int) {
    match bst
    case PTS_final(bbest) => BestTieLk(re, crv, str, ov, S, bbest, vms.bestmatch, ncap, nlook, nquant)
    case PTS(inp, bactive, bbest, bblocked, bseen) =>
      0 <= vms.cp <= |str|
      && inp == PIV.InpOfCp(str, vms.cp)
      && PIV.ContextOkRE(str, vms.cp, vms.context)   // aligns VM anchor/char reads with the position
      && ActiveRepLkC(rer, qm, re, code, inp, crv, str, ov, S, bactive, vms.active, ncap, nlook, nquant)
      && (forall nextinp :: LC.AdvanceInput(inp, WP.Forward) == Some(nextinp) ==>
                              BlockedRepLkC(rer, qm, re, code, inp, nextinp, crv, str, ov, S, bblocked,
                                            PIV.MatchingBlocked(LC.Reverse(vms.blocked), inp), ncap, nlook, nquant))
      && (LC.AdvanceInput(inp, WP.Forward) == None ==> bblocked == [])
      // (E3) the look-path carrier, index-wise over both pairings
      && LookNestRepC(re, S, bactive, vms.active)
      && (LC.AdvanceInput(inp, WP.Forward).Some? ==>
            LookNestRepB(re, S, bblocked, PIV.MatchingBlocked(LC.Reverse(vms.blocked), inp)))
      // (E4) the converse carrier, same pairings
      && LookNestBackRepC(re, crv, str, ov, S, bactive, vms.active, ncap, nlook, nquant)
      && (LC.AdvanceInput(inp, WP.Forward).Some? ==>
            LookNestBackRepB(re, crv, str, ov, S, bblocked,
                             PIV.MatchingBlocked(LC.Reverse(vms.blocked), inp), ncap, nlook, nquant))
      && BestTieLk(re, crv, str, ov, S, bbest, vms.bestmatch, ncap, nlook, nquant)
      && SeenRepLk(rer, qm, code, inp, bseen, vms.processed,
                   PIV.HdTreeOf(bactive), PIV.HeadPcOf(vms.active))
      && IsblockedRepLk(rer, qm, code, inp, bseen, vms.isblocked)
      // the gate helpers read the oracle column at the current input; the
      // walk carries this (OracleOkSuffixStep advances it with cp)
      && LL.OracleOkSuffix(rer, qm, inp)
  }

  /** (L4 NESTED) The standalone lift invariant with the `GmtTieInside`-carrying
      pairings swapped for their `*Nested` forms (`ActiveRepLkCNested`,
      `BlockedRepLkCNested`, `BestTieLkNested`). Every other conjunct — the (E3)
      `LookNest*` carriers, the (E4) `LookNestBack*` carriers, the seen/isblocked
      bookkeeping, the oracle suffix — is depth-agnostic and kept verbatim. */
  ghost predicate LiftInvNested(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code,
                                crv: CP.FCompiled, str: string, ov: LOr.OracleView, S: set<LG.GroupId>,
                                bst: PT.PikeTreeState, vms: AI.VmState,
                                ncap: int, nlook: int, nquant: int) {
    match bst
    case PTS_final(bbest) => BestTieLkNested(re, crv, str, ov, S, bbest, vms.bestmatch, ncap, nlook, nquant)
    case PTS(inp, bactive, bbest, bblocked, bseen) =>
      0 <= vms.cp <= |str|
      && inp == PIV.InpOfCp(str, vms.cp)
      && PIV.ContextOkRE(str, vms.cp, vms.context)   // aligns VM anchor/char reads with the position
      && ActiveRepLkCNested(rer, qm, re, code, inp, crv, str, ov, S, bactive, vms.active, ncap, nlook, nquant)
      && (forall nextinp :: LC.AdvanceInput(inp, WP.Forward) == Some(nextinp) ==>
                              BlockedRepLkCNested(rer, qm, re, code, inp, nextinp, crv, str, ov, S, bblocked,
                                                  PIV.MatchingBlocked(LC.Reverse(vms.blocked), inp), ncap, nlook, nquant))
      && (LC.AdvanceInput(inp, WP.Forward) == None ==> bblocked == [])
      // (E3) the look-path carrier, index-wise over both pairings
      && LookNestRepC(re, S, bactive, vms.active)
      && (LC.AdvanceInput(inp, WP.Forward).Some? ==>
            LookNestRepB(re, S, bblocked, PIV.MatchingBlocked(LC.Reverse(vms.blocked), inp)))
      // (E4) the converse carrier, same pairings
      && LookNestBackRepC(re, crv, str, ov, S, bactive, vms.active, ncap, nlook, nquant)
      && (LC.AdvanceInput(inp, WP.Forward).Some? ==>
            LookNestBackRepB(re, crv, str, ov, S, bblocked,
                             PIV.MatchingBlocked(LC.Reverse(vms.blocked), inp), ncap, nlook, nquant))
      && BestTieLkNested(re, crv, str, ov, S, bbest, vms.bestmatch, ncap, nlook, nquant)
      && SeenRepLk(rer, qm, code, inp, bseen, vms.processed,
                   PIV.HdTreeOf(bactive), PIV.HeadPcOf(vms.active))
      && IsblockedRepLk(rer, qm, code, inp, bseen, vms.isblocked)
      // the gate helpers read the oracle column at the current input; the
      // walk carries this (OracleOkSuffixStep advances it with cp)
      && LL.OracleOkSuffix(rer, qm, inp)
  }

  /** WalkPairLk relocates through a `Jmp` — the SAME `(acts, b)` witness moves
      via `ActionsRepLThruJmp`, so `GateAheadClear`/NoDup transfer verbatim. */
  lemma WalkPairLkAtJmp(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                        tb: LT.Tree, gmt: LG.GroupMap, pc: nat, ea: bool, x: int)
    requires WalkPairLk(rer, qm, code, inp, tb, gmt, pc, ea)
    requires NR.GetPcRE(code, pc) == Some(RB.Jmp(x))
    ensures x >= 0 && WalkPairLk(rer, qm, code, inp, tb, gmt, x as nat, ea)
  {
    var acts: LS.Actions, b: BS.LoopBool :|
      AR.ActionsRepL(rer, qm, acts, code, pc)
      && EL.PikeLkActions(acts)
      && ATR.EaOf(b) == ea
      && EL.BoolTreeLk(rer, acts, inp, b, tb)
      && GateAheadClear(acts, gmt)
      && WalkDefsOk(acts);
    ActionsRepLThruJmp(rer, qm, acts, code, pc, x);
  }

  /** `BlockedRepLkC` commutes with appending one paired entry — the snoc
      companion the `Consume` case uses to align the appended B `Read`-child
      with the appended VM blocked pair. Mirror of `PSM.BlockedRepSnocRE`. */
  lemma BlockedRepLkCSnoc(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code,
                          inp: LC.Input, nextinp: LC.Input, crv: CP.FCompiled, str: string,
                          ov: LOr.OracleView, S: set<LG.GroupId>,
                          tl: seq<(LT.Tree, LG.GroupMap)>, bl: seq<(AI.Thread, RC.char_expectation)>,
                          tp: (LT.Tree, LG.GroupMap), p: (AI.Thread, RC.char_expectation),
                          ncap: int, nlook: int, nquant: int)
    requires BlockedRepLkC(rer, qm, re, code, inp, nextinp, crv, str, ov, S, tl, bl, ncap, nlook, nquant)
    requires p.0.pc >= 0
    requires TreeRepLkRE(rer, qm, code, nextinp, tp.0, (p.0.pc + 1) as nat, true)
    requires exists traw: LT.Tree ::
               CE.ProgErase(traw) == CE.ProgErase(tp.0)
               && WalkPairLk(rer, qm, code, nextinp, traw, tp.1, (p.0.pc + 1) as nat, true)
    requires GmtTieOutside(re, p.0, tp.1, S)
    requires GmtTieInside(crv, str, ov, p.0, tp.1, S, ncap, nlook, nquant)
    ensures BlockedRepLkC(rer, qm, re, code, inp, nextinp, crv, str, ov, S, tl + [tp], bl + [p],
                          ncap, nlook, nquant)
    decreases tl
  {
    if |tl| == 0 {
      assert |bl| == 0;
      assert tl + [tp] == [tp] && bl + [p] == [p];
      assert ([tp])[0] == tp && ([tp])[1..] == [] && ([p])[0] == p && ([p])[1..] == [];
    } else {
      assert |bl| > 0;
      assert (tl + [tp])[0] == tl[0] && (bl + [p])[0] == bl[0];
      assert (tl + [tp])[1..] == tl[1..] + [tp] && (bl + [p])[1..] == bl[1..] + [p];
      BlockedRepLkCSnoc(rer, qm, re, code, inp, nextinp, crv, str, ov, S, tl[1..], bl[1..],
                        tp, p, ncap, nlook, nquant);
    }
  }

  /** (L4 NESTED) `BlockedRepLkCSnoc` for the `GmtTieInside`-free pairing — the
      `GmtTieInside` requires is dropped; the snoc structure is unchanged. */
  lemma BlockedRepLkCSnocNested(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code,
                                inp: LC.Input, nextinp: LC.Input, crv: CP.FCompiled, str: string,
                                ov: LOr.OracleView, S: set<LG.GroupId>,
                                tl: seq<(LT.Tree, LG.GroupMap)>, bl: seq<(AI.Thread, RC.char_expectation)>,
                                tp: (LT.Tree, LG.GroupMap), p: (AI.Thread, RC.char_expectation),
                                ncap: int, nlook: int, nquant: int)
    requires BlockedRepLkCNested(rer, qm, re, code, inp, nextinp, crv, str, ov, S, tl, bl, ncap, nlook, nquant)
    requires p.0.pc >= 0
    requires TreeRepLkRE(rer, qm, code, nextinp, tp.0, (p.0.pc + 1) as nat, true)
    requires exists traw: LT.Tree ::
               CE.ProgErase(traw) == CE.ProgErase(tp.0)
               && WalkPairLk(rer, qm, code, nextinp, traw, tp.1, (p.0.pc + 1) as nat, true)
    requires GmtTieOutside(re, p.0, tp.1, S)
    ensures BlockedRepLkCNested(rer, qm, re, code, inp, nextinp, crv, str, ov, S, tl + [tp], bl + [p],
                                ncap, nlook, nquant)
    decreases tl
  {
    if |tl| == 0 {
      assert |bl| == 0;
      assert tl + [tp] == [tp] && bl + [p] == [p];
      assert ([tp])[0] == tp && ([tp])[1..] == [] && ([p])[0] == p && ([p])[1..] == [];
    } else {
      assert |bl| > 0;
      assert (tl + [tp])[0] == tl[0] && (bl + [p])[0] == bl[0];
      assert (tl + [tp])[1..] == tl[1..] + [tp] && (bl + [p])[1..] == bl[1..] + [p];
      BlockedRepLkCSnocNested(rer, qm, re, code, inp, nextinp, crv, str, ov, S, tl[1..], bl[1..],
                              tp, p, ncap, nlook, nquant);
    }
  }

  /** Fueled `WalkPairLk` core at a `Consume(ce)` pc — the READ, with the full
      carrier: the child walks at the ADVANCED input with the SAME map and
      re-armed flag (`GateAheadClear`/`WalkDefsOk` are input-independent tail
      facts). This is what lets `BlockedRepLkC` store a REACTIVATABLE payload. */
  lemma WalkPairLkAtConsumeCore(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                                tb: LT.Tree, gm: LG.GroupMap, pc: nat, b: BS.LoopBool,
                                acts: LS.Actions, ce: RC.char_expectation)
    requires AR.ActionsRepL(rer, qm, acts, code, pc)
    requires EL.PikeLkActions(acts)
    requires EL.BoolTreeLk(rer, acts, inp, b, tb)
    requires NR.GetPcRE(code, pc) == Some(RB.Consume(ce))
    requires GateAheadClear(acts, gm)
    requires WalkDefsOk(acts)
    ensures tb.Read? || tb == LT.Mismatch
    ensures tb.Read? ==> exists nextinp ::
                AR.ReadCharE(ce, inp) == Some((tb.c, nextinp))
                && WalkPairLk(rer, qm, code, nextinp, tb.t, gm, pc + 1, true)
    ensures tb == LT.Mismatch ==> AR.ReadCharE(ce, inp) == None
    decreases ATR.MsizeA(acts)
  {
    var g := ATR.EaOf(b);
    var pcmid: nat :| AR.ActionRepL(rer, qm, acts[0], code, pc, pcmid) && AR.ActionsRepL(rer, qm, acts[1..], code, pcmid);
    EL.PikeLkActionsTail(acts);
    assert acts == [acts[0]] + acts[1..];
    EL.PikeLkActionsConsIff(acts[0], acts[1..]);
    var cont := acts[1..];
    match acts[0]
    case Acheck(_) =>   // pins EndLoop / backward Fork — not Consume
    case Aclose(_) =>   // pins SetRegisterToCP — not Consume
    case Areg(r0) =>
      assert EL.PikeLkRegex(r0);
      match r0
      case Epsilon =>
        assert pcmid == pc;
        assert EL.BoolTreeLk(rer, cont, inp, b, tb);
        assert ATR.MsizeA(cont) < ATR.MsizeA(acts);
        GateAheadClearTail(acts, gm);
        WalkDefsOkTail(acts);
        WalkPairLkAtConsumeCore(rer, qm, code, inp, tb, gm, pc, b, cont, ce);
      case Sequence(r1, r2) =>
        assert acts[0] == LS.Areg(L.Sequence(r1, r2));
        assert AR.NfaRepL(rer, qm, L.Sequence(r1, r2), code, pc, pcmid);
        var e1: nat :| AR.NfaRepL(rer, qm, r1, code, pc, e1) && AR.NfaRepL(rer, qm, r2, code, e1, pcmid);
        var na := [LS.Areg(r1), LS.Areg(r2)] + cont;
        assert na == [LS.Areg(r1)] + ([LS.Areg(r2)] + cont);
        AR.ActionsRepLCons(rer, qm, LS.Areg(r2), cont, code, e1, pcmid);
        AR.ActionsRepLCons(rer, qm, LS.Areg(r1), [LS.Areg(r2)] + cont, code, pc, e1);
        assert AR.ActionsRepL(rer, qm, na, code, pc);
        assert EL.PikeLkActions(na) by {
          EL.PikeLkActionsConsIff(LS.Areg(r2), cont);
          EL.PikeLkActionsConsIff(LS.Areg(r1), [LS.Areg(r2)] + cont);
        }
        assert EL.BoolTreeLk(rer, na, inp, b, tb);
        assert LS.ActionsRegexSize(acts) == RegSz(r1) + RegSz(r2) + 1 + LS.ActionsRegexSize(cont);
        assert LS.ActionsRegexSize(na) == RegSz(r1) + RegSz(r2) + LS.ActionsRegexSize(cont);
        assert ATR.MsizeA(na) < ATR.MsizeA(acts);
        GateAheadClearSeqExpand(acts, r1, r2, gm);
        WalkDefsOkSeqExpand(acts, r1, r2);
        WalkPairLkAtConsumeCore(rer, qm, code, inp, tb, gm, pc, b, na, ce);
      case Quantified(greedy, min, delta, r1) =>
        if min == 0 && delta == LN.NN(0) {
          assert acts[0] == LS.Areg(L.Quantified(greedy, 0, LN.NN(0), r1));
          assert AR.NfaRepL(rer, qm, L.Quantified(greedy, 0, LN.NN(0), r1), code, pc, pcmid);
          var em: nat :| AR.NfaRepMinL(rer, qm, 0, r1, code, pc, em)
                         && AR.NfaRepOptL(rer, qm, 0, greedy, r1, code, em, pcmid);
          NfaRepMinLHeadPin(rer, qm, 0, r1, code, pc, em);
          NfaRepOptLHeadPin(rer, qm, 0, greedy, r1, code, em, pcmid);
          assert pcmid == pc;
          assert AR.ActionsRepL(rer, qm, cont, code, pc);
          assert EL.BoolTreeLk(rer, cont, inp, b, tb);
          assert ATR.MsizeA(cont) < ATR.MsizeA(acts);
          GateAheadClearTail(acts, gm);
          WalkDefsOkTail(acts);
          WalkPairLkAtConsumeCore(rer, qm, code, inp, tb, gm, pc, b, cont, ce);
        } else {
          assert acts[0] == LS.Areg(L.Quantified(greedy, min, delta, r1));
          assert AR.NfaRepL(rer, qm, L.Quantified(greedy, min, delta, r1), code, pc, pcmid);
          QuantHeadPinsNonConsume(rer, qm, greedy, min, delta, r1, code, pc, pcmid, ce);
        }
      case Character(cd) =>
        assert acts[0] == LS.Areg(L.Character(cd));
        var ce2 :| NR.GetPcRE(code, pc) == Some(RB.Consume(ce2)) && AR.ExpectationMatches(rer, ce2, cd);
        assert ce2 == ce && pcmid == pc + 1;
        AR.ReadAgree(rer, ce, cd, inp);   // ReadCharE(ce, inp) == ReadChar(rer, cd, inp, Forward)
        match LC.ReadChar(rer, cd, inp, WP.Forward) {
          case None =>
            assert tb == LT.Mismatch;
          case Some(pair) =>
            assert tb.Read? && tb.c == pair.0 && EL.BoolTreeLk(rer, cont, pair.1, BS.CanExit, tb.t);
            assert AR.ActionsRepL(rer, qm, cont, code, pc + 1);
            GateAheadClearTail(acts, gm);
            WalkDefsOkTail(acts);
            assert WalkPairLk(rer, qm, code, pair.1, tb.t, gm, pc + 1, true) by {
              assert ATR.EaOf(BS.CanExit) == true;
              assert EL.PikeLkActions(cont);
            }
            assert AR.ReadCharE(ce, inp) == Some((tb.c, pair.1));
        }
      case Disjunction(_, _) =>   // pins Fork — not Consume
      case Group(_, _) =>   // pins SetRegisterToCP — not Consume
      case LookaroundR(_, _) =>   // pins CheckOracle/NegCheckOracle — not Consume
      case AnchorR(_) =>   // pins AnchorAssertion — not Consume
      case Backreference(_) =>   // NfaRepL false
  }

  /** WalkPairLk→WalkPairLk wrapper at a `Consume(ce)`. */
  lemma WalkPairLkAtConsume(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                            tb: LT.Tree, gm: LG.GroupMap, pc: nat, ea: bool, ce: RC.char_expectation)
    requires WalkPairLk(rer, qm, code, inp, tb, gm, pc, ea)
    requires NR.GetPcRE(code, pc) == Some(RB.Consume(ce))
    ensures tb.Read? || tb == LT.Mismatch
    ensures tb.Read? ==> exists nextinp ::
                AR.ReadCharE(ce, inp) == Some((tb.c, nextinp))
                && WalkPairLk(rer, qm, code, nextinp, tb.t, gm, pc + 1, true)
    ensures tb == LT.Mismatch ==> AR.ReadCharE(ce, inp) == None
  {
    var acts: LS.Actions, b: BS.LoopBool :|
      AR.ActionsRepL(rer, qm, acts, code, pc)
      && EL.PikeLkActions(acts)
      && ATR.EaOf(b) == ea
      && EL.BoolTreeLk(rer, acts, inp, b, tb)
      && GateAheadClear(acts, gm)
      && WalkDefsOk(acts);
    WalkPairLkAtConsumeCore(rer, qm, code, inp, tb, gm, pc, b, acts, ce);
  }

  /** Fueled `WalkPairLk` core at a `NegCheckOracle` pc: the gate head is
      pinned by `ActionRepL`'s polarity split, and the PASSING merge is the
      IDENTITY (`LkResult` of a succeeding negative look returns `Some(gm)`),
      so the continuation's `GateAheadClear`/NoDup come from the plain tail
      bricks — no `AfterMerge` machinery. Keyed on the FUNCTIONAL verdict. */
  lemma WalkPairLkAtNegCheckOracleCore(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                                       tb: LT.Tree, gm: LG.GroupMap, pc: nat, b: BS.LoopBool,
                                       acts: LS.Actions, lid: int)
    requires AR.ActionsRepL(rer, qm, acts, code, pc)
    requires EL.PikeLkActions(acts)
    requires EL.BoolTreeLk(rer, acts, inp, b, tb)
    requires NR.GetPcRE(code, pc) == Some(RB.NegCheckOracle(lid))
    requires GateAheadClear(acts, gm)
    requires WalkDefsOk(acts)
    ensures lid in qm.looks
    ensures var (lk, r1) := qm.looks[lid];
            var tlk := LFU.ComputeTr(rer, [LS.Areg(r1)], inp, LG.Empty, L.LkDir(lk));
            !AR.PositiveL(lk)
            && (LS.LkResult(lk, tlk, LG.Empty, inp).Some? ==>
                  tb.LK? && tb.lk == lk && tb.tlk == tlk
                  && WalkPairLk(rer, qm, code, inp, tb.t, gm, pc + 1, ATR.EaOf(b)))
            && (LS.LkResult(lk, tlk, LG.Empty, inp).None? ==> tb == LT.LKFail(lk, tlk))
    decreases ATR.MsizeA(acts)
  {
    var g := ATR.EaOf(b);
    var pcmid: nat :| AR.ActionRepL(rer, qm, acts[0], code, pc, pcmid) && AR.ActionsRepL(rer, qm, acts[1..], code, pcmid);
    EL.PikeLkActionsTail(acts);
    assert acts == [acts[0]] + acts[1..];
    EL.PikeLkActionsConsIff(acts[0], acts[1..]);
    var cont := acts[1..];
    match acts[0]
    case Acheck(_) =>   // pins EndLoop / backward Fork — not NegCheckOracle
    case Aclose(_) =>   // pins SetRegisterToCP — not NegCheckOracle
    case Areg(r0) =>
      assert EL.PikeLkRegex(r0);
      match r0
      case Epsilon =>
        assert pcmid == pc;
        assert EL.BoolTreeLk(rer, cont, inp, b, tb);
        assert ATR.MsizeA(cont) < ATR.MsizeA(acts);
        GateAheadClearTail(acts, gm);
        WalkDefsOkTail(acts);
        WalkPairLkAtNegCheckOracleCore(rer, qm, code, inp, tb, gm, pc, b, cont, lid);
      case Sequence(r1, r2) =>
        assert acts[0] == LS.Areg(L.Sequence(r1, r2));
        assert AR.NfaRepL(rer, qm, L.Sequence(r1, r2), code, pc, pcmid);
        var e1: nat :| AR.NfaRepL(rer, qm, r1, code, pc, e1) && AR.NfaRepL(rer, qm, r2, code, e1, pcmid);
        var na := [LS.Areg(r1), LS.Areg(r2)] + cont;
        assert na == [LS.Areg(r1)] + ([LS.Areg(r2)] + cont);
        AR.ActionsRepLCons(rer, qm, LS.Areg(r2), cont, code, e1, pcmid);
        AR.ActionsRepLCons(rer, qm, LS.Areg(r1), [LS.Areg(r2)] + cont, code, pc, e1);
        assert AR.ActionsRepL(rer, qm, na, code, pc);
        assert EL.PikeLkActions(na) by {
          EL.PikeLkActionsConsIff(LS.Areg(r2), cont);
          EL.PikeLkActionsConsIff(LS.Areg(r1), [LS.Areg(r2)] + cont);
        }
        assert EL.BoolTreeLk(rer, na, inp, b, tb);
        assert LS.ActionsRegexSize(acts) == RegSz(r1) + RegSz(r2) + 1 + LS.ActionsRegexSize(cont);
        assert LS.ActionsRegexSize(na) == RegSz(r1) + RegSz(r2) + LS.ActionsRegexSize(cont);
        assert ATR.MsizeA(na) < ATR.MsizeA(acts);
        GateAheadClearSeqExpand(acts, r1, r2, gm);
        M.AllDefsActsCons(acts[0], cont);
        M.AllDefsActsCons(LS.Areg(r1), [LS.Areg(r2)] + cont);
        M.AllDefsActsCons(LS.Areg(r2), cont);
        assert L.DefGroups(L.Sequence(r1, r2)) == L.DefGroups(r1) + L.DefGroups(r2);
        assert L.DefGroups(r1) + (L.DefGroups(r2) + M.AllDefsActs(cont))
            == (L.DefGroups(r1) + L.DefGroups(r2)) + M.AllDefsActs(cont);
        assert M.AllDefsActs(na) == M.AllDefsActs(acts);
        WalkDefsOkSeqExpand(acts, r1, r2);
        WalkPairLkAtNegCheckOracleCore(rer, qm, code, inp, tb, gm, pc, b, na, lid);
      case Quantified(greedy, min, delta, r1) =>
        if min == 0 && delta == LN.NN(0) {
          assert acts[0] == LS.Areg(L.Quantified(greedy, 0, LN.NN(0), r1));
          assert AR.NfaRepL(rer, qm, L.Quantified(greedy, 0, LN.NN(0), r1), code, pc, pcmid);
          var em: nat :| AR.NfaRepMinL(rer, qm, 0, r1, code, pc, em)
                         && AR.NfaRepOptL(rer, qm, 0, greedy, r1, code, em, pcmid);
          NfaRepMinLHeadPin(rer, qm, 0, r1, code, pc, em);
          NfaRepOptLHeadPin(rer, qm, 0, greedy, r1, code, em, pcmid);
          assert pcmid == pc;
          assert AR.ActionsRepL(rer, qm, cont, code, pc);
          assert EL.BoolTreeLk(rer, cont, inp, b, tb);
          assert ATR.MsizeA(cont) < ATR.MsizeA(acts);
          GateAheadClearTail(acts, gm);
          WalkDefsOkTail(acts);
          WalkPairLkAtNegCheckOracleCore(rer, qm, code, inp, tb, gm, pc, b, cont, lid);
        } else {
          assert acts[0] == LS.Areg(L.Quantified(greedy, min, delta, r1));
          assert AR.NfaRepL(rer, qm, L.Quantified(greedy, min, delta, r1), code, pc, pcmid);
          QuantHeadPinsForkOrSQC(rer, qm, greedy, min, delta, r1, code, pc, pcmid);
        }
      case LookaroundR(lk0, r1) =>
        // ActionRepL's polarity split: a NegCheckOracle pc hosts a NEGATIVE look
        var lid0: int :| NR.GetPcRE(code, pc) == Some(if AR.PositiveL(lk0) then RB.CheckOracle(lid0)
                                                      else RB.NegCheckOracle(lid0))
                         && lid0 in qm.looks && qm.looks[lid0] == (lk0, r1);
        assert !AR.PositiveL(lk0) && lid0 == lid;
        assert pcmid == pc + 1;
        M.GateNodeAtInp(rer, acts, inp, b, tb, lk0, r1);   // tb is LK/LKFail with LkGateOk
        var tlk := LFU.ComputeTr(rer, [LS.Areg(r1)], inp, LG.Empty, L.LkDir(lk0));
        if tb.LK? {
          assert tb.tlk == tlk && LS.LkResult(lk0, tlk, LG.Empty, inp).Some?;   // LkGateOk true
          assert EL.BoolTreeLk(rer, cont, inp, b, tb.t);
          assert AR.ActionsRepL(rer, qm, cont, code, pc + 1);
          // the passing negative merge is the identity ⟹ plain tail bricks
          GateAheadClearTail(acts, gm);
          WalkDefsOkTail(acts);
          assert EL.PikeLkActions(cont);
          assert WalkPairLk(rer, qm, code, inp, tb.t, gm, pc + 1, g);
        } else {
          assert tb.LKFail? && tb.tlk == tlk;               // LkGateOk false
          assert LS.LkResult(lk0, tlk, LG.Empty, inp).None?;
          assert tb == LT.LKFail(lk0, tlk);
        }
      case Character(_) =>   // pins Consume — not NegCheckOracle
      case Disjunction(_, _) =>   // pins Fork — not NegCheckOracle
      case Group(_, _) =>   // pins SetRegisterToCP — not NegCheckOracle
      case AnchorR(_) =>   // pins AnchorAssertion — not NegCheckOracle
      case Backreference(_) =>   // NfaRepL false
  }

  /** WalkPairLk→WalkPairLk wrapper at a `NegCheckOracle`. */
  lemma WalkPairLkAtNegCheckOracle(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                                   tb: LT.Tree, gm: LG.GroupMap, pc: nat, ea: bool, lid: int)
    requires WalkPairLk(rer, qm, code, inp, tb, gm, pc, ea)
    requires NR.GetPcRE(code, pc) == Some(RB.NegCheckOracle(lid))
    ensures lid in qm.looks
    ensures var (lk, r1) := qm.looks[lid];
            var tlk := LFU.ComputeTr(rer, [LS.Areg(r1)], inp, LG.Empty, L.LkDir(lk));
            !AR.PositiveL(lk)
            && (LS.LkResult(lk, tlk, LG.Empty, inp).Some? ==>
                  tb.LK? && tb.lk == lk && tb.tlk == tlk
                  && WalkPairLk(rer, qm, code, inp, tb.t, gm, pc + 1, ea))
            && (LS.LkResult(lk, tlk, LG.Empty, inp).None? ==> tb == LT.LKFail(lk, tlk))
  {
    var acts: LS.Actions, b: BS.LoopBool :|
      AR.ActionsRepL(rer, qm, acts, code, pc)
      && EL.PikeLkActions(acts)
      && ATR.EaOf(b) == ea
      && EL.BoolTreeLk(rer, acts, inp, b, tb)
      && GateAheadClear(acts, gm)
      && WalkDefsOk(acts);
    WalkPairLkAtNegCheckOracleCore(rer, qm, code, inp, tb, gm, pc, b, acts, lid);
  }

  /** Fueled `WalkPairLk` core at an `EndLoop` pc: `TtLkAtEndLoopCore`'s case
      structure with `WalkPairLkAtAnchorCore`'s invariant threading — the
      `Acheck` head is consumed with `gm` UNCHANGED, so the tail bricks give
      the continuation its `GateAheadClear`/NoDup. */
  lemma WalkPairLkAtEndLoopCore(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                                tb: LT.Tree, gm: LG.GroupMap, pc: nat, b: BS.LoopBool,
                                acts: LS.Actions)
    requires AR.ActionsRepL(rer, qm, acts, code, pc)
    requires EL.PikeLkActions(acts)
    requires EL.BoolTreeLk(rer, acts, inp, b, tb)
    requires NR.GetPcRE(code, pc) == Some(RB.EndLoop)
    requires GateAheadClear(acts, gm)
    requires WalkDefsOk(acts)
    ensures ATR.EaOf(b) ==> tb.Progress? && WalkPairLk(rer, qm, code, inp, tb.t, gm, pc + 1, true)
    ensures !ATR.EaOf(b) ==> tb == LT.Mismatch
    decreases ATR.MsizeA(acts)
  {
    var g := ATR.EaOf(b);
    assert !AR.BackForkAt(code, pc);   // GetPcRE(pc)==EndLoop, not Fork
    var pcmid: nat :| AR.ActionRepL(rer, qm, acts[0], code, pc, pcmid) && AR.ActionsRepL(rer, qm, acts[1..], code, pcmid);
    EL.PikeLkActionsTail(acts);
    assert acts == [acts[0]] + acts[1..];
    EL.PikeLkActionsConsIff(acts[0], acts[1..]);
    var cont := acts[1..];
    match acts[0]
    case Acheck(strcheck) =>
      // ActionRepL(Acheck): EndLoop disjunct (BackFork excluded) ⇒ pcmid == pc+1
      assert pcmid == pc + 1;
      if b == BS.CanExit {
        assert g == true;
        assert tb.Progress? && EL.BoolTreeLk(rer, cont, inp, BS.CanExit, tb.t);
        assert AR.ActionsRepL(rer, qm, cont, code, pc + 1);
        // gm UNCHANGED across the guard ⟹ tail bricks give the continuation clear.
        GateAheadClearTail(acts, gm);       // GateAheadClear(cont, gm)
        WalkDefsOkTail(acts);             // NoDupSeq(AllDefsActs(cont))
        assert EL.PikeLkActions(cont);
        assert ATR.EaOf(BS.CanExit) == true;
        assert WalkPairLk(rer, qm, code, inp, tb.t, gm, pc + 1, true);
      } else {
        assert b == BS.CannotExit && g == false;
        assert tb == LT.Mismatch;
      }
    case Aclose(_) =>   // pins SetRegisterToCP — not EndLoop
    case Areg(r0) =>
      assert EL.PikeLkRegex(r0);
      match r0
      case Epsilon =>
        assert pcmid == pc;
        assert EL.BoolTreeLk(rer, cont, inp, b, tb);
        assert ATR.MsizeA(cont) < ATR.MsizeA(acts);
        GateAheadClearTail(acts, gm);
        WalkDefsOkTail(acts);
        WalkPairLkAtEndLoopCore(rer, qm, code, inp, tb, gm, pc, b, cont);
      case Sequence(r1, r2) =>
        assert acts[0] == LS.Areg(L.Sequence(r1, r2));
        assert AR.NfaRepL(rer, qm, L.Sequence(r1, r2), code, pc, pcmid);
        var e1: nat :| AR.NfaRepL(rer, qm, r1, code, pc, e1) && AR.NfaRepL(rer, qm, r2, code, e1, pcmid);
        var na := [LS.Areg(r1), LS.Areg(r2)] + cont;
        assert na == [LS.Areg(r1)] + ([LS.Areg(r2)] + cont);
        AR.ActionsRepLCons(rer, qm, LS.Areg(r2), cont, code, e1, pcmid);
        AR.ActionsRepLCons(rer, qm, LS.Areg(r1), [LS.Areg(r2)] + cont, code, pc, e1);
        assert AR.ActionsRepL(rer, qm, na, code, pc);
        assert EL.PikeLkActions(na) by {
          EL.PikeLkActionsConsIff(LS.Areg(r2), cont);
          EL.PikeLkActionsConsIff(LS.Areg(r1), [LS.Areg(r2)] + cont);
        }
        assert EL.BoolTreeLk(rer, na, inp, b, tb);
        assert LS.ActionsRegexSize(acts) == RegSz(r1) + RegSz(r2) + 1 + LS.ActionsRegexSize(cont);
        assert LS.ActionsRegexSize(na) == RegSz(r1) + RegSz(r2) + LS.ActionsRegexSize(cont);
        assert ATR.MsizeA(na) < ATR.MsizeA(acts);
        GateAheadClearSeqExpand(acts, r1, r2, gm);
        M.AllDefsActsCons(acts[0], cont);
        M.AllDefsActsCons(LS.Areg(r1), [LS.Areg(r2)] + cont);
        M.AllDefsActsCons(LS.Areg(r2), cont);
        assert L.DefGroups(L.Sequence(r1, r2)) == L.DefGroups(r1) + L.DefGroups(r2);
        assert L.DefGroups(r1) + (L.DefGroups(r2) + M.AllDefsActs(cont))
            == (L.DefGroups(r1) + L.DefGroups(r2)) + M.AllDefsActs(cont);
        assert M.AllDefsActs(na) == M.AllDefsActs(acts);
        WalkDefsOkSeqExpand(acts, r1, r2);
        WalkPairLkAtEndLoopCore(rer, qm, code, inp, tb, gm, pc, b, na);
      case Quantified(greedy, min, delta, r1) =>
        if min == 0 && delta == LN.NN(0) {
          assert acts[0] == LS.Areg(L.Quantified(greedy, 0, LN.NN(0), r1));
          assert AR.NfaRepL(rer, qm, L.Quantified(greedy, 0, LN.NN(0), r1), code, pc, pcmid);
          var em: nat :| AR.NfaRepMinL(rer, qm, 0, r1, code, pc, em)
                         && AR.NfaRepOptL(rer, qm, 0, greedy, r1, code, em, pcmid);
          NfaRepMinLHeadPin(rer, qm, 0, r1, code, pc, em);
          NfaRepOptLHeadPin(rer, qm, 0, greedy, r1, code, em, pcmid);
          assert pcmid == pc;
          assert AR.ActionsRepL(rer, qm, cont, code, pc);
          assert EL.BoolTreeLk(rer, cont, inp, b, tb);
          assert ATR.MsizeA(cont) < ATR.MsizeA(acts);
          GateAheadClearTail(acts, gm);
          WalkDefsOkTail(acts);
          WalkPairLkAtEndLoopCore(rer, qm, code, inp, tb, gm, pc, b, cont);
        } else {
          assert acts[0] == LS.Areg(L.Quantified(greedy, min, delta, r1));
          assert AR.NfaRepL(rer, qm, L.Quantified(greedy, min, delta, r1), code, pc, pcmid);
          QuantHeadPinsForkOrSQC(rer, qm, greedy, min, delta, r1, code, pc, pcmid);
        }
      case Character(_) =>   // pins Consume — not EndLoop
      case Disjunction(_, _) =>   // pins Fork — not EndLoop
      case Group(_, _) =>   // pins SetRegisterToCP — not EndLoop
      case LookaroundR(_, _) =>   // pins CheckOracle/NegCheckOracle — not EndLoop
      case AnchorR(_) =>   // pins AnchorAssertion — not EndLoop
      case Backreference(_) =>   // NfaRepL false
  }

  /** WalkPairLk→WalkPairLk wrapper at an `EndLoop`. */
  lemma WalkPairLkAtEndLoop(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                            tb: LT.Tree, gm: LG.GroupMap, pc: nat, ea: bool)
    requires WalkPairLk(rer, qm, code, inp, tb, gm, pc, ea)
    requires NR.GetPcRE(code, pc) == Some(RB.EndLoop)
    ensures ea ==> tb.Progress? && WalkPairLk(rer, qm, code, inp, tb.t, gm, pc + 1, true)
    ensures !ea ==> tb == LT.Mismatch
  {
    var acts: LS.Actions, b: BS.LoopBool :|
      AR.ActionsRepL(rer, qm, acts, code, pc)
      && EL.PikeLkActions(acts)
      && ATR.EaOf(b) == ea
      && EL.BoolTreeLk(rer, acts, inp, b, tb)
      && GateAheadClear(acts, gm)
      && WalkDefsOk(acts);
    WalkPairLkAtEndLoopCore(rer, qm, code, inp, tb, gm, pc, b, acts);
  }

  /** The `WalkPairLk` analogue of `TtLkAtBeginLoop`: the gated pairing walk also
      sees through a `BeginLoop` (the `ActionsRepL` disjunct is impossible there),
      so the whole per-thread `ThreadRepLk` follows the VM's BeginLoop step. */
  lemma WalkPairLkAtBeginLoop(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                              tb: LT.Tree, gmt: LG.GroupMap, pc: nat, ea: bool)
    requires WalkPairLk(rer, qm, code, inp, tb, gmt, pc, ea)
    requires NR.GetPcRE(code, pc) == Some(RB.BeginLoop)
    ensures WalkPairLk(rer, qm, code, inp, tb, gmt, pc + 1, false)
  {
    forall acts: LS.Actions, b: BS.LoopBool
      ensures !(AR.ActionsRepL(rer, qm, acts, code, pc)
                && EL.PikeLkActions(acts) && ATR.EaOf(b) == ea
                && EL.BoolTreeLk(rer, acts, inp, b, tb) && GateAheadClear(acts, gmt))
    {
      if AR.ActionsRepL(rer, qm, acts, code, pc) {
        TT.ActionsRepNotAtBeginLoop(rer, qm, acts, code, pc);   // ⇒ false
      }
    }
  }

  /** Per-thread BeginLoop preservation — the reusable core of `LiftAdvanceEpsilon`'s
      BeginLoop case. When the VM steps a thread through `BeginLoop`
      (`exit_allowed:=false, pc:=pc+1`), its whole pairing to `(tb, gmt)` carries:
      the walk sees through via `WalkPairLkAtBeginLoop`, and the value ties are
      frame-invariant (BeginLoop touches only `pc`/`exit_allowed`, not the
      capture/look/quant banks that `GmtTie*` reads). The B-machine does NOT step
      (a `BeginLoop` is absorbed by the walk stutter — the loop shows up in `tb`
      as `Choice` nodes, stepped later). */
  lemma ThreadRepLkStepBeginLoop(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code,
                                 inp: LC.Input, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
                                 S: set<LG.GroupId>, tb: LT.Tree, gmt: LG.GroupMap, th: AI.Thread,
                                 ncap: int, nlook: int, nquant: int)
    requires ThreadRepLk(rer, qm, re, code, inp, crv, str, ov, S, tb, gmt, th, ncap, nlook, nquant)
    requires NR.GetPcRE(code, th.pc as nat) == Some(RB.BeginLoop)
    ensures ThreadRepLk(rer, qm, re, code, inp, crv, str, ov, S, tb, gmt,
                        th.(exit_allowed := false, pc := th.pc + 1), ncap, nlook, nquant)
  {
    WalkPairLkAtBeginLoop(rer, qm, code, inp, tb, gmt, th.pc as nat, th.exit_allowed);
    // th.pc >= 0 (from ThreadRepLk) so (th.pc+1) as nat == (th.pc as nat) + 1.
    assert (th.pc + 1) as nat == (th.pc as nat) + 1;
    // GmtTieOutside/GmtTieInside read only capture/look/quant regs, unchanged by
    // the pc/exit_allowed update, so they transfer verbatim.
  }

  /** (SINGLE-THREADED) The DIRECT-case per-`g2` package with the SOLE owed residual
      of `DescentPackageDirectFromRes1` (the gate-crossing `LookPathDom` on the winning
      thread's banks) DISCHARGED by the extraction connective `NI.LookPathDomFromLivenessThread`.
      Input is FULL recon-bank liveness `g2 in GmOfLive(re,res)` (which the endpoint's
      reverse-(c) hypothesis carries) plus the res->thread frames at the top look A0
      (look-clock via `M.FLookLoopTopLookClkStableFull`, cp via `M.FLookLoopTopLookCpStableFull`,
      quant via the outside-look quant frame). Produces the exact
      `DescentProducerTopOwnersDeep` per-`g2` package. */
  lemma DescentPackageDirectFull(
    rer: LW.RegExpRecord, qm: AR.QMap, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
    re: R.regex, S: set<LG.GroupId>, thread: AI.Thread, res0: AReg.Regs, res1: AReg.Regs, res2: AReg.Regs,
    A0: nat, g2: nat, body: R.regex, bodycode: RB.code, endl: nat, ngroups: nat,
    ncap: int, nlook: int, nquant: int)
    requires NR.NestedFragmentRE(re) && PIV.CapUnique(re) && LTB.LookUnique(re)
    requires S == PIV.CapIdsInLooks(re)
    requires A0 in NI.TopLookIds(re) && A0 in LTB.LookIds(re)
    requires body == NI.LookBodyOfRE(re, A0) && body == M.VBody(crv, A0 as int)
    requires g2 in S && g2 in PIV.CapIds(body) && g2 !in PIV.CapIdsInLooks(body)   // DIRECT
    // ---- body facts for the landing bridge (same as DescentPackageDirectFromRes1) ----
    requires PSM.StaticOkNestedRE(qm, body, bodycode, endl)
    requires NR.NegLooksLookFreeRE(body)
    requires PSM.SizesOkRE(body, ncap, nlook, nquant)
    requires qm.ov == ov && !rer.ignoreCase && !rer.multiline
    requires bodycode == CP.compile_to_bytecode(body)
    requires T.TransWf(body)
    requires 0 <= (A0 as int) < |crv.f_look_types| && crv.f_look_types[A0 as int].Lookahead?
    requires 0 <= (A0 as int) < |crv.f_look_cdns|
    // ---- A1/A2 res1-side facts (matched + fresh-live g2) ----
    requires M.MatchedPosLA(crv, res1, A0 as int)
    requires var rf := M.FreshBodyMatch(crv, str, A0 as int, res1, ov, ncap, nlook, nquant);
             rf.Some?
             && g2 in PIV.GmOfLive(body, rf.value.capture_regs, rf.value.look_regs, rf.value.quant_regs)
    // ---- res1 <-> thread reconciliation at the top look A0 ----
    requires AReg.get_cp(res1, A0 as int) == AReg.get_cp(thread.look_regs, A0 as int)
    requires var cp := AReg.get_cp(res1, A0 as int).value;
             0 <= cp <= |str| && LL.OracleOkSuffix(rer, qm, PIV.InpOfCp(str, cp))
    requires AI.get_idx(res1.a_clk, A0 as int) == AI.get_idx(thread.look_regs.a_clk, A0 as int)
    requires forall q: nat :: q in PIV.QuantIdsOutsideLooks(re) ==>
                                AI.get_idx(res2.a_clk, q as int) == AI.get_idx(thread.quant_regs.a_clk, q as int)
    // ---- FULL recon-bank liveness (replaces the owed LookPathDom) ----
    requires forall c: nat :: c in PIV.CapIds(re) && AI.get_idx(res0.a_clk, CP.start_reg(c)) < 0
                              ==> AI.get_idx(res0.a_cp, CP.start_reg(c)) < 0
    requires g2 in PIV.GmOfLive(re, res0, res1, res2)
    ensures A0 in NI.TopLookIds(re) && A0 in LTB.LookIds(re)
            && g2 in PIV.CapIds(NI.LookBodyOfRE(re, A0))
            && M.MatchedPosLA(crv, thread.look_regs, A0 as int)
            && NI.LookPathDom(re, AI.get_idx(thread.look_regs.a_clk, A0 as int), thread.quant_regs.a_clk, A0)
            && var lsub := SubFirstLeafAt(rer, crv, str, A0 as int, thread.look_regs);
            lsub.Some? && g2 in lsub.value
  {
    // discharge the owed LookPathDom on thread banks by EXTRACTION from full liveness.
    NI.LookPathDomFromLivenessThread(re, res0, res1, res2, thread, g2, A0);
    // then the direct-case package.
    DescentPackageDirectFromRes1(rer, qm, crv, str, ov, re, S, thread, res1,
                                 A0, g2, body, bodycode, endl, ngroups, ncap, nlook, nquant);
  }

  /** L3b item 4 (task #8) — PROVEN: the BACKWARD-gate twin of
      `ThreadRepLkStepCheckOracle` for a CAPTURING positive lookbehind. It
      establishes `GmtTieInside`'s `SwapRange` form via `GateStepValueLB` (which
      calls the keystone `LBK.LkReplayMatchesSpecLB` at cap=init + `BV.BackwardReplayMirror`),
      with the outside frame / continuation walk direction-generic (as in the
      lookahead twin). The value chain: `FreshBodyMatch(LB)` runs the backward
      capture (= `raB`), the mirror gives `rfF == MirrorThread(raB)`, and the
      keystone yields `SwapRange(gm2[g]) == GmOfLive(body, raB.caps)[g]` for `g in S`. */
  lemma ThreadRepLkStepCheckOracleLB(
    rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, crv: CP.FCompiled,
    str: string, ov: LOr.OracleView, S: set<LG.GroupId>, lk: L.Lookaround, r1: L.Regex,
    tlk: LT.Tree, tc: LT.Tree, gm: LG.GroupMap, t: AI.Thread, l: int, cp: nat, clk: int,
    body: R.regex, la: R.lookaround, bodycode: RB.code, endl: nat, ngroups: nat,
    qt: AReg.Regs, ncap: int, nlook: int, nquant: int)
    requires qm.ov == ov && !rer.ignoreCase && !rer.multiline
    requires cp <= |str| && t.pc >= 0 && |ov| == |str| + 1
    requires l in qm.looks && qm.looks[l] == (lk, r1)
    requires L.Positivity(lk) && L.LkDir(lk) == WP.Backward
    requires LS.LkResult(lk, tlk, gm, PIV.InpOfCp(str, cp)).Some?
    requires EL.LkGateOk(rer, lk, r1, PIV.InpOfCp(str, cp), tlk, true)
    requires ThreadRepLk(rer, qm, re, code, PIV.InpOfCp(str, cp), crv, str, ov, S,
                         LT.LK(lk, tlk, tc), gm, t, ncap, nlook, nquant)
    requires forall g :: g in L.DefGroups(r1) ==> g !in gm
    requires T.TransWf(body) && NR.LookFreeRE(body) && la.Lookbehind?
    requires NR.PlusFragmentRE(body) && PIV.CapUnique(body) && PIV.QuantUnique(body)
    requires SD.GroupOkL(T.Translate(body)) && CD.NoDupG(L.DefGroups(T.Translate(body)))
    requires r1 == T.Translate(body) && lk == T.TrLookaround(la) && body == M.VBody(crv, l)
    requires bodycode == CP.compile_to_bytecode(body)
    requires PSM.StaticOkRE(qm, body, bodycode, endl)
    requires PSM.SizesOkRE(body, ncap, nlook, nquant)
    requires |qt.a_cp| == nquant && |qt.a_clk| == nquant
    requires LL.OracleOkSuffix(rer, qm, PIV.InpOfCp(str, cp))
    requires 0 <= l < nlook && l < RL.ASize(t.look_regs)
    requires 0 <= l < |crv.f_look_ast| && 0 <= l < |crv.f_look_cdns| && 0 <= l < |crv.f_look_types|
    requires crv.f_look_types[l].Lookbehind? && AI.capture_type(crv.f_look_types[l])
    requires NR.GetPcRE(code, t.pc as nat) == Some(RB.CheckOracle(l))
    requires T.TransWf(re) && NR.LookBehindFragmentRE(re)
    requires S == LL.LkBodyGroups(T.Translate(re))
    requires (set g | g in L.DefGroups(r1)) <= S
    ensures var t' := t.(pc := t.pc + 1, look_regs := AReg.set_reg(t.look_regs, l, Some(cp as int), clk));
            var gm2 := LS.LkResult(lk, tlk, gm, PIV.InpOfCp(str, cp)).value;
            ThreadRepLk(rer, qm, re, code, PIV.InpOfCp(str, cp), crv, str, ov, S, tc, gm2, t',
                        ncap, nlook, nquant)
  {
    var inp := PIV.InpOfCp(str, cp);
    var t' := t.(pc := t.pc + 1, look_regs := AReg.set_reg(t.look_regs, l, Some(cp as int), clk));
    var gm2 := LS.LkResult(lk, tlk, gm, inp).value;
    // (1) INSIDE tie: GateStepValueLB lifts GmtTieInside(t,gm) across the BACKWARD gate to (t',gm2).
    assert t' == t.(pc := t.pc + 1, look_regs := AReg.set_reg(t.look_regs, l, Some(cp as int), clk));
    GateStepValueLB(rer, qm, re, code, crv, str, ov, S, lk, r1, tlk, LT.LK(lk, tlk, tc),
                    gm, t, t', l, cp, body, la, bodycode, endl, ngroups, qt, ncap, nlook, nquant);
    // (2) CONTINUATION walk (direction-generic): from the incoming ThreadRepLk's WalkPairLk.
    assert LL.OracleOkAt(rer, qm, inp);
    assert WalkPairLk(rer, qm, code, inp, LT.LK(lk, tlk, tc), gm, t.pc as nat, t.exit_allowed);
    WalkPairLkAtCheckOracle(rer, qm, code, inp, LT.LK(lk, tlk, tc), gm, t.pc as nat, t.exit_allowed, l);
    assert LT.LK(lk, tlk, tc).LK?;        // ⟹ bit true (wrapper: !bit ==> LKFail?)
    assert (t.pc + 1) as nat == (t.pc as nat) + 1 && t'.exit_allowed == t.exit_allowed;
    assert WalkPairLk(rer, qm, code, inp, tc, gm2, (t.pc + 1) as nat, t.exit_allowed);
    // (3) OUTSIDE frame (GmtTieOutsideAfterGate works for backward gates too).
    assert GmtTieOutside(re, t, gm, S);
    EL.TranslateNoLkBr(body);
    GmtTieOutsideAfterGate(rer, re, str, lk, r1, tlk, gm, t, l, cp, clk, S);
  }

  /** (L4 NESTED) clone of `ThreadRepLkStepCheckOracleLB` — GmtTieInside dropped. */
  lemma ThreadRepLkStepCheckOracleLBNested(
    rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, crv: CP.FCompiled,
    str: string, ov: LOr.OracleView, S: set<LG.GroupId>, lk: L.Lookaround, r1: L.Regex,
    tlk: LT.Tree, tc: LT.Tree, gm: LG.GroupMap, t: AI.Thread, l: int, cp: nat, clk: int,
    body: R.regex, la: R.lookaround, bodycode: RB.code, endl: nat, ngroups: nat,
    qt: AReg.Regs, ncap: int, nlook: int, nquant: int)
    requires qm.ov == ov && !rer.ignoreCase && !rer.multiline
    requires cp <= |str| && t.pc >= 0 && |ov| == |str| + 1
    requires l in qm.looks && qm.looks[l] == (lk, r1)
    requires L.Positivity(lk) && L.LkDir(lk) == WP.Backward
    requires LS.LkResult(lk, tlk, gm, PIV.InpOfCp(str, cp)).Some?
    requires EL.LkGateOk(rer, lk, r1, PIV.InpOfCp(str, cp), tlk, true)
    requires ThreadRepLkNested(rer, qm, re, code, PIV.InpOfCp(str, cp), crv, str, ov, S,
                               LT.LK(lk, tlk, tc), gm, t, ncap, nlook, nquant)
    requires forall g :: g in L.DefGroups(r1) ==> g !in gm
    // (L4 NESTED) body-fragment weakened to the positive-nesting sub-fragment;
    // the GateStepValueLB backward-replay body package is DROPPED with the call.
    requires T.TransWf(body) && NR.NestedFragmentRE(body) && NR.NegLooksLookFreeRE(body) && la.Lookbehind?
    requires r1 == T.Translate(body) && lk == T.TrLookaround(la)
    requires LL.OracleOkSuffix(rer, qm, PIV.InpOfCp(str, cp))
    requires 0 <= l < nlook && l < RL.ASize(t.look_regs)
    requires NR.GetPcRE(code, t.pc as nat) == Some(RB.CheckOracle(l))
    requires T.TransWf(re) && NR.NestedFragmentRE(re)
    requires S == LL.LkBodyGroups(T.Translate(re))
    requires (set g | g in L.DefGroups(r1)) <= S
    ensures var t' := t.(pc := t.pc + 1, look_regs := AReg.set_reg(t.look_regs, l, Some(cp as int), clk));
            var gm2 := LS.LkResult(lk, tlk, gm, PIV.InpOfCp(str, cp)).value;
            ThreadRepLkNested(rer, qm, re, code, PIV.InpOfCp(str, cp), crv, str, ov, S, tc, gm2, t',
                              ncap, nlook, nquant)
  {
    var inp := PIV.InpOfCp(str, cp);
    var t' := t.(pc := t.pc + 1, look_regs := AReg.set_reg(t.look_regs, l, Some(cp as int), clk));
    var gm2 := LS.LkResult(lk, tlk, gm, inp).value;
    // (1) INSIDE tie DROPPED (GmtTieInside is not part of ThreadRepLkNested).
    assert t' == t.(pc := t.pc + 1, look_regs := AReg.set_reg(t.look_regs, l, Some(cp as int), clk));
    // (2) CONTINUATION walk (direction-generic): from the incoming ThreadRepLk's WalkPairLk.
    assert LL.OracleOkAt(rer, qm, inp);
    assert WalkPairLk(rer, qm, code, inp, LT.LK(lk, tlk, tc), gm, t.pc as nat, t.exit_allowed);
    WalkPairLkAtCheckOracle(rer, qm, code, inp, LT.LK(lk, tlk, tc), gm, t.pc as nat, t.exit_allowed, l);
    assert LT.LK(lk, tlk, tc).LK?;        // ⟹ bit true (wrapper: !bit ==> LKFail?)
    assert (t.pc + 1) as nat == (t.pc as nat) + 1 && t'.exit_allowed == t.exit_allowed;
    assert WalkPairLk(rer, qm, code, inp, tc, gm2, (t.pc + 1) as nat, t.exit_allowed);
    // (3) OUTSIDE frame: recursive-body confinement (backward gate, PikeLkRegexRec(r1)).
    assert GmtTieOutside(re, t, gm, S);
    EL.TranslateFragmentPikeLkRec(body);  // PikeLkRegexRec(Translate(body)) == PikeLkRegexRec(r1)
    GmtTieOutsideAfterGateNested(rer, re, str, lk, r1, tlk, gm, t, l, cp, clk, S);
  }

  /** THE CRUX per-instruction core: a thread crossing a PASSING positive-lookahead
      gate (`CheckOracle(l)`, oracle TRUE). The VM records `a_cp[l]:=cp` (t → t');
      the paired B-subtree `LK(lk,tlk,tc)` MERGES `LkResult` into `tc` (gm → gm2).
      The inside-`S` value tie is exactly `GateStepValue` (proven) — this is where
      it plugs in, and the POSITION TIE is automatic (`cp` is both the VM's write
      and the gate's input position). The continuation walk `WalkPairLk(tc,gm2,…)`
      (from the `TtLkAtCheckOracle` inversion + `GateAheadClearAfterMerge`) and the
      outside-`S` frame `GmtTieOutside(t',gm2)` (from `LkResultAgreeOutside` + look-
      register framing) are `requires` — the mechanical parts the caller supplies.
      `GateStepValue`'s static look-table package is threaded verbatim. */
  lemma ThreadRepLkStepCheckOracle(
    rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, crv: CP.FCompiled,
    str: string, ov: LOr.OracleView, S: set<LG.GroupId>, lk: L.Lookaround, r1: L.Regex,
    tlk: LT.Tree, tc: LT.Tree, gm: LG.GroupMap, t: AI.Thread, l: int, cp: nat, clk: int,
    body: R.regex, la: R.lookaround, bodycode: RB.code, endl: nat, ngroups: nat,
    qt: AReg.Regs, ncap: int, nlook: int, nquant: int)
    requires qm.ov == ov && !rer.ignoreCase && !rer.multiline
    requires cp <= |str| && t.pc >= 0
    requires l in qm.looks && qm.looks[l] == (lk, r1)
    requires L.Positivity(lk) && L.LkDir(lk) == WP.Forward
    requires LS.LkResult(lk, tlk, gm, PIV.InpOfCp(str, cp)).Some?
    requires EL.LkGateOk(rer, lk, r1, PIV.InpOfCp(str, cp), tlk, true)
    // the paired B-subtree at t.pc is the LK gate node (from TtLkAtCheckOracle):
    requires ThreadRepLk(rer, qm, re, code, PIV.InpOfCp(str, cp), crv, str, ov, S,
                         LT.LK(lk, tlk, tc), gm, t, ncap, nlook, nquant)
    requires forall g :: g in L.DefGroups(r1) ==> g !in gm        // GateAheadClear at this gate
    requires T.TransWf(body) && NR.LookFreeRE(body) && la.Lookahead?
    requires r1 == T.Translate(body) && lk == T.TrLookaround(la) && body == M.VBody(crv, l)
    requires bodycode == CP.compile_to_bytecode(body)
    requires PSM.StaticOkRE(qm, body, bodycode, endl)
    requires PSM.SizesOkRE(body, ncap, nlook, nquant)
    requires |qt.a_cp| == nquant && |qt.a_clk| == nquant
    requires LL.OracleOkSuffix(rer, qm, PIV.InpOfCp(str, cp))
    requires 0 <= l < nlook && l < RL.ASize(t.look_regs)
    requires 0 <= l < |crv.f_look_ast| && 0 <= l < |crv.f_look_cdns| && 0 <= l < |crv.f_look_types|
    requires crv.f_look_types[l].Lookahead? && AI.capture_type(crv.f_look_types[l])
    // gate position + outside-frame well-formedness (caller supplies); the
    // continuation walk and outside frame are now DERIVED in the body.
    requires NR.GetPcRE(code, t.pc as nat) == Some(RB.CheckOracle(l))
    requires T.TransWf(re) && NR.LookBehindFragmentRE(re)
    requires S == LL.LkBodyGroups(T.Translate(re))
    requires (set g | g in L.DefGroups(r1)) <= S
    ensures var t' := t.(pc := t.pc + 1, look_regs := AReg.set_reg(t.look_regs, l, Some(cp as int), clk));
            var gm2 := LS.LkResult(lk, tlk, gm, PIV.InpOfCp(str, cp)).value;
            ThreadRepLk(rer, qm, re, code, PIV.InpOfCp(str, cp), crv, str, ov, S, tc, gm2, t',
                        ncap, nlook, nquant)
  {
    var inp := PIV.InpOfCp(str, cp);
    var t' := t.(pc := t.pc + 1, look_regs := AReg.set_reg(t.look_regs, l, Some(cp as int), clk));
    var gm2 := LS.LkResult(lk, tlk, gm, inp).value;
    // (1) INSIDE tie: GateStepValue lifts GmtTieInside(t,gm) across the gate to (t',gm2).
    assert t' == t.(pc := t.pc + 1, look_regs := AReg.set_reg(t.look_regs, l, Some(cp as int), clk));
    GateStepValue(rer, qm, re, code, crv, str, ov, S, lk, r1, tlk, LT.LK(lk, tlk, tc),
                  gm, t, t', l, cp, body, la, bodycode, endl, ngroups, qt, ncap, nlook, nquant);
    // (2) CONTINUATION walk: from the incoming ThreadRepLk's WalkPairLk on the LK head.
    assert LL.OracleOkAt(rer, qm, inp);   // OracleOkSuffix instantiated at inp
    assert WalkPairLk(rer, qm, code, inp, LT.LK(lk, tlk, tc), gm, t.pc as nat, t.exit_allowed);
    WalkPairLkAtCheckOracle(rer, qm, code, inp, LT.LK(lk, tlk, tc), gm, t.pc as nat, t.exit_allowed, l);
    assert LT.LK(lk, tlk, tc).LK?;        // ⟹ bit true (wrapper: !bit ==> LKFail?)
    assert (t.pc + 1) as nat == (t.pc as nat) + 1 && t'.exit_allowed == t.exit_allowed;
    assert WalkPairLk(rer, qm, code, inp, tc, gm2, (t.pc + 1) as nat, t.exit_allowed);
    // (3) OUTSIDE frame.
    assert GmtTieOutside(re, t, gm, S);   // from the incoming ThreadRepLk(LK, gm, t)
    EL.TranslateNoLkBr(body);             // NoLkBrL(r1)  (r1 == Translate(body))
    GmtTieOutsideAfterGate(rer, re, str, lk, r1, tlk, gm, t, l, cp, clk, S);   // GmtTieOutside(t',gm2,S)
    // ThreadRepLk(tc,gm2,t') = t'.pc>=0 && WalkPairLk (2) && GmtTieOutside (3) && GmtTieInside (1).
  }

  /** (L4 NESTED) clone of `ThreadRepLkStepCheckOracle` — GmtTieInside dropped. */
  lemma ThreadRepLkStepCheckOracleNested(
    rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, crv: CP.FCompiled,
    str: string, ov: LOr.OracleView, S: set<LG.GroupId>, lk: L.Lookaround, r1: L.Regex,
    tlk: LT.Tree, tc: LT.Tree, gm: LG.GroupMap, t: AI.Thread, l: int, cp: nat, clk: int,
    body: R.regex, la: R.lookaround, bodycode: RB.code, endl: nat, ngroups: nat,
    qt: AReg.Regs, ncap: int, nlook: int, nquant: int)
    requires qm.ov == ov && !rer.ignoreCase && !rer.multiline
    requires cp <= |str| && t.pc >= 0
    requires l in qm.looks && qm.looks[l] == (lk, r1)
    requires L.Positivity(lk) && L.LkDir(lk) == WP.Forward
    requires LS.LkResult(lk, tlk, gm, PIV.InpOfCp(str, cp)).Some?
    requires EL.LkGateOk(rer, lk, r1, PIV.InpOfCp(str, cp), tlk, true)
    // the paired B-subtree at t.pc is the LK gate node (from TtLkAtCheckOracle):
    requires ThreadRepLkNested(rer, qm, re, code, PIV.InpOfCp(str, cp), crv, str, ov, S,
                               LT.LK(lk, tlk, tc), gm, t, ncap, nlook, nquant)
    requires forall g :: g in L.DefGroups(r1) ==> g !in gm        // GateAheadClear at this gate
    // (L4 NESTED) the body may itself contain looks: the depth-1 LookFreeRE(body)
    // is replaced by the positive-nesting sub-fragment (feeds PikeLkRegexRec(r1)
    // for the recursive outside-tie); the GateStepValue body-package requires
    // (StaticOkRE(body)/bodycode/qt/f_look_* rows) are DROPPED with the call.
    requires T.TransWf(body) && NR.NestedFragmentRE(body) && NR.NegLooksLookFreeRE(body) && la.Lookahead?
    requires r1 == T.Translate(body) && lk == T.TrLookaround(la)
    requires LL.OracleOkSuffix(rer, qm, PIV.InpOfCp(str, cp))
    requires 0 <= l < nlook && l < RL.ASize(t.look_regs)
    // gate position + outside-frame well-formedness (caller supplies); the
    // continuation walk and outside frame are now DERIVED in the body.
    requires NR.GetPcRE(code, t.pc as nat) == Some(RB.CheckOracle(l))
    requires T.TransWf(re) && NR.NestedFragmentRE(re)
    requires S == LL.LkBodyGroups(T.Translate(re))
    requires (set g | g in L.DefGroups(r1)) <= S
    ensures var t' := t.(pc := t.pc + 1, look_regs := AReg.set_reg(t.look_regs, l, Some(cp as int), clk));
            var gm2 := LS.LkResult(lk, tlk, gm, PIV.InpOfCp(str, cp)).value;
            ThreadRepLkNested(rer, qm, re, code, PIV.InpOfCp(str, cp), crv, str, ov, S, tc, gm2, t',
                              ncap, nlook, nquant)
  {
    var inp := PIV.InpOfCp(str, cp);
    var t' := t.(pc := t.pc + 1, look_regs := AReg.set_reg(t.look_regs, l, Some(cp as int), clk));
    var gm2 := LS.LkResult(lk, tlk, gm, inp).value;
    // (1) INSIDE tie DROPPED (GmtTieInside is not part of ThreadRepLkNested).
    assert t' == t.(pc := t.pc + 1, look_regs := AReg.set_reg(t.look_regs, l, Some(cp as int), clk));
    // (2) CONTINUATION walk: from the incoming ThreadRepLk's WalkPairLk on the LK head.
    assert LL.OracleOkAt(rer, qm, inp);   // OracleOkSuffix instantiated at inp
    assert WalkPairLk(rer, qm, code, inp, LT.LK(lk, tlk, tc), gm, t.pc as nat, t.exit_allowed);
    WalkPairLkAtCheckOracle(rer, qm, code, inp, LT.LK(lk, tlk, tc), gm, t.pc as nat, t.exit_allowed, l);
    assert LT.LK(lk, tlk, tc).LK?;        // ⟹ bit true (wrapper: !bit ==> LKFail?)
    assert (t.pc + 1) as nat == (t.pc as nat) + 1 && t'.exit_allowed == t.exit_allowed;
    assert WalkPairLk(rer, qm, code, inp, tc, gm2, (t.pc + 1) as nat, t.exit_allowed);
    // (3) OUTSIDE frame: recursive-body confinement (PikeLkRegexRec(r1)).
    assert GmtTieOutside(re, t, gm, S);   // from the incoming ThreadRepLkNested(LK, gm, t)
    EL.TranslateFragmentPikeLkRec(body);  // PikeLkRegexRec(Translate(body)) == PikeLkRegexRec(r1)
    GmtTieOutsideAfterGateNested(rer, re, str, lk, r1, tlk, gm, t, l, cp, clk, S);   // GmtTieOutside(t',gm2,S)
  }

  /** Fueled `WalkPairLk` core at a `SetQuantToClock(q, false)` pc — the
      FORCED-COPY (min>0) route: the real head emits the `Reset` stamp
      (payload pinned to `qm.quants[q]` by `QuantHeadSQCPin`), the continuation
      `[Areg r1, Areg(Quantified(min-1))] + cont` is represented at `pc+1`
      (`QuantForcedContRep`) and walks at the RESET-updated map:
      `GateAheadClear` re-established BY the Reset (r1's pending bodies ⊆ the
      reset set; cont's pendings survive the domain shrink), `WalkDefsOk` by
      the unfold brick (`WalkDefsOkUnfold`, mid = []). */
  lemma WalkPairLkAtSetQuantCore(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                                 tb: LT.Tree, gm: LG.GroupMap, pc: nat, b: BS.LoopBool,
                                 acts: LS.Actions, q: int)
    requires AR.ActionsRepL(rer, qm, acts, code, pc)
    requires EL.PikeLkActions(acts)
    requires EL.BoolTreeLk(rer, acts, inp, b, tb)
    requires NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(q, false))
    requires GateAheadClear(acts, gm)
    requires WalkDefsOk(acts)
    ensures q in qm.quants
    ensures tb.GroupActionT? && tb.g == LG.Reset(qm.quants[q])
    ensures WalkPairLk(rer, qm, code, inp, tb.t,
                       LG.GMUpdate(tb.g, LC.Idx(inp), gm), pc + 1, ATR.EaOf(b))
    decreases ATR.MsizeA(acts)
  {
    var g := ATR.EaOf(b);
    var pcmid: nat :| AR.ActionRepL(rer, qm, acts[0], code, pc, pcmid) && AR.ActionsRepL(rer, qm, acts[1..], code, pcmid);
    EL.PikeLkActionsTail(acts);
    assert acts == [acts[0]] + acts[1..];
    EL.PikeLkActionsConsIff(acts[0], acts[1..]);
    var cont := acts[1..];
    match acts[0]
    case Acheck(_) =>   // pins EndLoop / backward Fork — not SetQuantToClock
    case Aclose(_) =>   // pins SetRegisterToCP — not SetQuantToClock
    case Areg(r0) =>
      assert EL.PikeLkRegex(r0);
      match r0
      case Epsilon =>
        assert pcmid == pc;
        assert EL.BoolTreeLk(rer, cont, inp, b, tb);
        assert ATR.MsizeA(cont) < ATR.MsizeA(acts);
        GateAheadClearTail(acts, gm);
        WalkDefsOkTail(acts);
        WalkPairLkAtSetQuantCore(rer, qm, code, inp, tb, gm, pc, b, cont, q);
      case Sequence(r1, r2) =>
        assert acts[0] == LS.Areg(L.Sequence(r1, r2));
        assert AR.NfaRepL(rer, qm, L.Sequence(r1, r2), code, pc, pcmid);
        var e1: nat :| AR.NfaRepL(rer, qm, r1, code, pc, e1) && AR.NfaRepL(rer, qm, r2, code, e1, pcmid);
        var na := [LS.Areg(r1), LS.Areg(r2)] + cont;
        assert na == [LS.Areg(r1)] + ([LS.Areg(r2)] + cont);
        AR.ActionsRepLCons(rer, qm, LS.Areg(r2), cont, code, e1, pcmid);
        AR.ActionsRepLCons(rer, qm, LS.Areg(r1), [LS.Areg(r2)] + cont, code, pc, e1);
        assert AR.ActionsRepL(rer, qm, na, code, pc);
        assert EL.PikeLkActions(na) by {
          EL.PikeLkActionsConsIff(LS.Areg(r2), cont);
          EL.PikeLkActionsConsIff(LS.Areg(r1), [LS.Areg(r2)] + cont);
        }
        assert EL.BoolTreeLk(rer, na, inp, b, tb);
        assert LS.ActionsRegexSize(acts) == RegSz(r1) + RegSz(r2) + 1 + LS.ActionsRegexSize(cont);
        assert LS.ActionsRegexSize(na) == RegSz(r1) + RegSz(r2) + LS.ActionsRegexSize(cont);
        assert ATR.MsizeA(na) < ATR.MsizeA(acts);
        GateAheadClearSeqExpand(acts, r1, r2, gm);
        WalkDefsOkSeqExpand(acts, r1, r2);
        WalkPairLkAtSetQuantCore(rer, qm, code, inp, tb, gm, pc, b, na, q);
      case Quantified(greedy, min, delta, r1) =>
        assert acts[0] == LS.Areg(L.Quantified(greedy, min, delta, r1));
        assert AR.NfaRepL(rer, qm, L.Quantified(greedy, min, delta, r1), code, pc, pcmid);
        if min > 0 {
          // THE forced-copy real head.
          var quant1 := L.Quantified(greedy, min - 1, delta, r1);
          var contActs := [LS.Areg(r1), LS.Areg(quant1)] + cont;
          var gidl := L.DefGroups(r1);
          assert tb.GroupActionT? && tb.g == LG.Reset(gidl)
                 && EL.BoolTreeLk(rer, contActs, inp, b, tb.t);
          // the qm.quants binding of THIS instruction's qid
          QuantHeadSQCPin(rer, qm, greedy, min, delta, r1, code, pc, pcmid);
          var qid: int :| NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(qid, false))
                          && qid in qm.quants && qm.quants[qid] == L.DefGroups(r1);
          assert qid == q;
          assert q in qm.quants && qm.quants[q] == gidl;
          QuantForcedContRep(rer, qm, greedy, min, delta, r1, code, pc, pcmid, cont);   // ActionsRepL(contActs, pc+1)
          assert EL.PikeLkRegex(r1) && EL.PikeLkRegex(quant1);
          assert EL.PikeLkActions(contActs) by {
            EL.PikeLkActionsConsIff(LS.Areg(quant1), cont);
            EL.PikeLkActionsConsIff(LS.Areg(r1), [LS.Areg(quant1)] + cont);
          }
          // gm moves by the Reset
          var gm2 := LG.GMUpdate(LG.Reset(gidl), LC.Idx(inp), gm);
          assert gm2 == LG.GMReset(gidl, gm);
          // GateAheadClear(contActs, gm2): fresh r1-pendings ⊆ the reset set;
          // cont's pendings carry (absent in gm, and Reset only removes keys)
          assert GateAheadClear(contActs, gm2) by {
            forall lk2: L.Lookaround, rr: L.Regex | GatePending(contActs, lk2, rr)
              ensures forall gg :: gg in L.DefGroups(rr) ==> gg !in gm2
            {
              var j :| 0 <= j < |contActs| && contActs[j].Areg? && RegexTopGate(contActs[j].r, lk2, rr);
              if j == 0 {
                assert contActs[0] == LS.Areg(r1) && RegexTopGate(r1, lk2, rr);
                RegexTopGateSubDefs(r1, lk2, rr);
                var SRR := set gx | gx in L.DefGroups(rr);
                var SR1 := set gx | gx in L.DefGroups(r1);
                assert SRR <= SR1;
                forall gg | gg in L.DefGroups(rr) ensures gg !in gm2 {
                  assert gg in SRR;
                  assert gg in SR1;
                  assert gg in L.DefGroups(r1);
                  assert gm2 == gm - (set gx | gx in gidl);
                  assert gg in (set gx | gx in gidl);
                }
              } else if j == 1 {
                assert !RegexTopGate(quant1, lk2, rr);   // Quantified: never pending
                assert false;
              } else {
                assert contActs[j] == cont[j - 2];
                assert GatePending(cont, lk2, rr) by {
                  assert cont[j - 2].Areg? && RegexTopGate(cont[j - 2].r, lk2, rr);
                }
                GatePendingTail(acts, lk2, rr);
                forall gg | gg in L.DefGroups(rr) ensures gg !in gm2 {
                  assert gg !in gm;   // GateAheadClear(acts, gm)
                }
              }
            }
          }
          // WalkDefsOk(contActs): the unfold brick (mid = [])
          WalkDefsOkUnfold(acts, r1, quant1, []);
          assert [LS.Areg(r1)] + [] + [LS.Areg(quant1)] + cont == contActs;
          // pack the existential at pc+1
          assert AR.ActionsRepL(rer, qm, contActs, code, pc + 1)
                 && EL.PikeLkActions(contActs)
                 && ATR.EaOf(b) == g
                 && EL.BoolTreeLk(rer, contActs, inp, b, tb.t)
                 && GateAheadClear(contActs, gm2)
                 && WalkDefsOk(contActs);
          assert WalkPairLk(rer, qm, code, inp, tb.t, gm2, pc + 1, g);
        } else if delta == LN.NN(0) {
          var em: nat :| AR.NfaRepMinL(rer, qm, 0, r1, code, pc, em)
                         && AR.NfaRepOptL(rer, qm, 0, greedy, r1, code, em, pcmid);
          NfaRepMinLHeadPin(rer, qm, 0, r1, code, pc, em);
          NfaRepOptLHeadPin(rer, qm, 0, greedy, r1, code, em, pcmid);
          assert pcmid == pc;
          assert AR.ActionsRepL(rer, qm, cont, code, pc);
          assert EL.BoolTreeLk(rer, cont, inp, b, tb);
          assert ATR.MsizeA(cont) < ATR.MsizeA(acts);
          GateAheadClearTail(acts, gm);
          WalkDefsOkTail(acts);
          WalkPairLkAtSetQuantCore(rer, qm, code, inp, tb, gm, pc, b, cont, q);
        } else {
          // min==0 with Inf or NN(kx>0): pins a Fork at pc, not SetQuantToClock.
          match delta
          case Inf =>
            if exists e1: nat ::
                NR.GetPcRE(code, pc) == Some(if greedy then RB.Fork(pc + 1, e1 + 2) else RB.Fork(e1 + 2, pc + 1))
                && (exists qid: int :: NR.GetPcRE(code, pc + 1) == Some(RB.SetQuantToClock(qid, false))
                                       && qid in qm.quants && qm.quants[qid] == L.DefGroups(r1))
                && NR.GetPcRE(code, pc + 2) == Some(RB.BeginLoop)
                && AR.NfaRepL(rer, qm, r1, code, pc + 3, e1)
                && NR.GetPcRE(code, e1) == Some(RB.EndLoop)
                && NR.GetPcRE(code, e1 + 1) == Some(RB.Jmp(pc))
                && pcmid == e1 + 2 {
              var e1: nat :| NR.GetPcRE(code, pc) == Some(if greedy then RB.Fork(pc + 1, e1 + 2) else RB.Fork(e1 + 2, pc + 1));
            } else {
              var em: nat :| NR.GetPcRE(code, pc) == Some(if greedy then RB.Fork(em, pc + 1) else RB.Fork(pc + 1, em));
            }
          case NN(kx) =>
            var em: nat :| AR.NfaRepMinL(rer, qm, 0, r1, code, pc, em)
                           && AR.NfaRepOptL(rer, qm, kx, greedy, r1, code, em, pcmid);
            NfaRepMinLHeadPin(rer, qm, 0, r1, code, pc, em);
            NfaRepOptLHeadPin(rer, qm, kx, greedy, r1, code, em, pcmid);   // kx>0 ⇒ Fork at pc
        }
      case Character(_) =>   // pins Consume — not SetQuantToClock
      case Disjunction(_, _) =>   // pins Fork — not SetQuantToClock
      case Group(_, _) =>   // pins SetRegisterToCP — not SetQuantToClock
      case LookaroundR(_, _) =>   // pins CheckOracle/NegCheckOracle — not SetQuantToClock
      case AnchorR(_) =>   // pins AnchorAssertion — not SetQuantToClock
      case Backreference(_) =>   // NfaRepL false
  }

  /** WalkPairLk→WalkPairLk wrapper at a `SetQuantToClock(q, false)`: EITHER
      the walk's actions route (forced-copy head — the Core) OR the SQC
      see-through disjunct (star/backfork iteration arm) — both yield the
      `Reset` head and the child walking at the RESET-updated map. */
  lemma WalkPairLkAtSetQuant(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                             tb: LT.Tree, gm: LG.GroupMap, pc: nat, ea: bool, q: int)
    requires WalkPairLk(rer, qm, code, inp, tb, gm, pc, ea)
    requires NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(q, false))
    ensures q in qm.quants
    ensures tb.GroupActionT? && tb.g == LG.Reset(qm.quants[q])
    ensures WalkPairLk(rer, qm, code, inp, tb.t,
                       LG.GMUpdate(tb.g, LC.Idx(inp), gm), pc + 1, ea)
  {
    if (exists acts: LS.Actions, b: BS.LoopBool ::
          AR.ActionsRepL(rer, qm, acts, code, pc)
          && EL.PikeLkActions(acts)
          && ATR.EaOf(b) == ea
          && EL.BoolTreeLk(rer, acts, inp, b, tb)
          && GateAheadClear(acts, gm)
          && WalkDefsOk(acts)) {
      var acts: LS.Actions, b: BS.LoopBool :|
        AR.ActionsRepL(rer, qm, acts, code, pc)
        && EL.PikeLkActions(acts)
        && ATR.EaOf(b) == ea
        && EL.BoolTreeLk(rer, acts, inp, b, tb)
        && GateAheadClear(acts, gm)
        && WalkDefsOk(acts);
      WalkPairLkAtSetQuantCore(rer, qm, code, inp, tb, gm, pc, b, acts, q);
    } else {
      // the SQC see-through disjunct is the live one
      var q0: int :| NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(q0, false))
                     && q0 in qm.quants
                     && tb.GroupActionT? && tb.g == LG.Reset(qm.quants[q0])
                     && WalkPairLk(rer, qm, code, inp, tb.t, LG.GMUpdate(tb.g, LC.Idx(inp), gm), pc + 1, ea);
      assert q0 == q;
    }
  }

  /** The star iteration arm's invariants across the unfold: `GateAheadClear`
      by the Reset itself (the fresh body pendings sit inside the reset set;
      the tail's survive the domain shrink), the carrier by `WalkDefsOkUnfold`. */
  lemma StarArmInvariants(acts: LS.Actions, r1: L.Regex, q': L.Regex, chk: LS.Action,
                          gm: LG.GroupMap, gidl: LG.GroupSet)
    requires |acts| > 0 && acts[0].Areg? && acts[0].r.Quantified? && acts[0].r.r1 == r1
    requires q'.Quantified? && q'.r1 == r1
    requires chk.Acheck?
    requires gidl == L.DefGroups(r1)
    requires GateAheadClear(acts, gm)
    requires WalkDefsOk(acts)
    ensures GateAheadClear([LS.Areg(r1), chk, LS.Areg(q')] + acts[1..], LG.GMReset(gidl, gm))
    ensures WalkDefsOk([LS.Areg(r1), chk, LS.Areg(q')] + acts[1..])
  {
    var cont := acts[1..];
    var na := [LS.Areg(r1), chk, LS.Areg(q')] + cont;
    var gm2 := LG.GMReset(gidl, gm);
    WalkDefsOkUnfold(acts, r1, q', [chk]);
    assert [LS.Areg(r1)] + [chk] + [LS.Areg(q')] + cont == na;
    assert GateAheadClear(na, gm2) by {
      forall lk2: L.Lookaround, rr: L.Regex | GatePending(na, lk2, rr)
        ensures forall gg :: gg in L.DefGroups(rr) ==> gg !in gm2
      {
        var j :| 0 <= j < |na| && na[j].Areg? && RegexTopGate(na[j].r, lk2, rr);
        if j == 0 {
          assert na[0] == LS.Areg(r1) && RegexTopGate(r1, lk2, rr);
          RegexTopGateSubDefs(r1, lk2, rr);
          var SRR := set gx | gx in L.DefGroups(rr);
          var SR1 := set gx | gx in L.DefGroups(r1);
          assert SRR <= SR1;
          forall gg | gg in L.DefGroups(rr) ensures gg !in gm2 {
            assert gg in SRR;
            assert gg in SR1;
            assert gg in L.DefGroups(r1);
            assert gm2 == gm - (set gx | gx in gidl);
            assert gg in (set gx | gx in gidl);
          }
        } else if j == 1 {
          assert !na[1].Areg?;
          assert false;
        } else if j == 2 {
          assert na[2] == LS.Areg(q') && !RegexTopGate(q', lk2, rr);
          assert false;
        } else {
          assert na[j] == cont[j - 3];
          assert GatePending(cont, lk2, rr) by {
            assert cont[j - 3].Areg? && RegexTopGate(cont[j - 3].r, lk2, rr);
          }
          GatePendingTail(acts, lk2, rr);
          forall gg | gg in L.DefGroups(rr) ensures gg !in gm2 {
            assert gg !in gm;
          }
        }
      }
    }
  }

  /** The star iteration arm's WALK at its `SetQuantToClock` pc, WITH an
      interposed `BeginLoop` (the FORWARD star / bounded-star layouts): the
      see-through disjunct chains into the BeginLoop stutter (which absorbs
      ANY incoming flag) and lands on the arm list at `CannotExit`. */
  lemma StarIterArmWalkBL(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                          gm: LG.GroupMap, sqcpc: nat, ea: bool, qid: int,
                          r1: L.Regex, ti: LT.Tree, armlist: LS.Actions)
    requires NR.GetPcRE(code, sqcpc) == Some(RB.SetQuantToClock(qid, false))
    requires qid in qm.quants && qm.quants[qid] == L.DefGroups(r1)
    requires NR.GetPcRE(code, sqcpc + 1) == Some(RB.BeginLoop)
    requires AR.ActionsRepL(rer, qm, armlist, code, sqcpc + 2)
    requires EL.PikeLkActions(armlist)
    requires EL.BoolTreeLk(rer, armlist, inp, BS.CannotExit, ti)
    requires GateAheadClear(armlist, LG.GMReset(L.DefGroups(r1), gm))
    requires WalkDefsOk(armlist)
    ensures WalkPairLk(rer, qm, code, inp, LT.GroupActionT(LG.Reset(L.DefGroups(r1)), ti),
                       gm, sqcpc, ea)
  {
    var gidl := L.DefGroups(r1);
    var gm2 := LG.GMUpdate(LG.Reset(gidl), LC.Idx(inp), gm);
    assert gm2 == LG.GMReset(gidl, gm);
    assert sqcpc + 1 < RB.size(code);
    assert ATR.EaOf(BS.CannotExit) == false;
    assert WalkPairLk(rer, qm, code, inp, ti, gm2, sqcpc + 2, false);
    assert WalkPairLk(rer, qm, code, inp, ti, gm2, sqcpc + 1, ea);   // BeginLoop absorbs any flag
    assert sqcpc < RB.size(code);
  }

  /** The star iteration arm's WALK at its `SetQuantToClock` pc, with the body
      DIRECTLY following (the do-while LOOP-VIEW): at `ea == true` the arm list
      is entered at `CanExit`, which the NonNullable flag shield licenses. */
  lemma StarIterArmWalkLV(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                          gm: LG.GroupMap, sqcpc: nat, ea: bool, qid: int,
                          r1: L.Regex, ti: LT.Tree, rest: LS.Actions)
    requires NR.GetPcRE(code, sqcpc) == Some(RB.SetQuantToClock(qid, false))
    requires qid in qm.quants && qm.quants[qid] == L.DefGroups(r1)
    requires NUL.NonNullableL(r1)
    requires AR.ActionsRepL(rer, qm, [LS.Areg(r1)] + rest, code, sqcpc + 1)
    requires EL.PikeLkActions([LS.Areg(r1)] + rest)
    requires EL.BoolTreeLk(rer, [LS.Areg(r1)] + rest, inp, BS.CannotExit, ti)
    requires GateAheadClear([LS.Areg(r1)] + rest, LG.GMReset(L.DefGroups(r1), gm))
    requires WalkDefsOk([LS.Areg(r1)] + rest)
    ensures WalkPairLk(rer, qm, code, inp, LT.GroupActionT(LG.Reset(L.DefGroups(r1)), ti),
                       gm, sqcpc, ea)
  {
    var gidl := L.DefGroups(r1);
    var gm2 := LG.GMUpdate(LG.Reset(gidl), LC.Idx(inp), gm);
    assert gm2 == LG.GMReset(gidl, gm);
    var b2 := if ea then BS.CanExit else BS.CannotExit;
    if ea { BoolTreeLkGuardShield(rer, r1, rest, inp, ti); }
    assert EL.BoolTreeLk(rer, [LS.Areg(r1)] + rest, inp, b2, ti) && ATR.EaOf(b2) == ea;
    assert WalkPairLk(rer, qm, code, inp, ti, gm2, sqcpc + 1, ea);
    assert sqcpc < RB.size(code);
  }

  /** Fueled `WalkPairLk` core at a `Fork(x, y)` — THE BRANCH PAIRING, shape-
      disjunctive: a `Choice` head pairs its arms at `x`/`y` with the SAME map
      and flag (a star iteration arm pairs AT its `SetQuantToClock` pc via the
      see-through disjunct — the Reset applies when B steps that node); an
      `Acheck` head (backward fork) peels to `Progress` and recurses, arms at
      `true`; `CannotExit` at the guard dies. */
  lemma WalkPairLkAtForkCore(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                             tb: LT.Tree, gm: LG.GroupMap, pc: nat, b: BS.LoopBool,
                             acts: LS.Actions, x: int, y: int)
    requires AR.ActionsRepL(rer, qm, acts, code, pc)
    requires EL.PikeLkActions(acts)
    requires EL.BoolTreeLk(rer, acts, inp, b, tb)
    requires NR.GetPcRE(code, pc) == Some(RB.Fork(x, y))
    requires GateAheadClear(acts, gm)
    requires WalkDefsOk(acts)
    ensures x >= 0 && y >= 0
    // ERASURE-SHAPED (raw `Progress` guard wrappers can nest at a backfork):
    // dead, or the erased tree is a Choice whose arms have walking witnesses
    // at x/y — always at the OUTER flag (every Acheck peel preserves CanExit).
    ensures CE.ProgErase(tb) == LT.Mismatch
            || exists ta1: LT.Tree, ta2: LT.Tree ::
              CE.ProgErase(tb) == LT.Choice(CE.ProgErase(ta1), CE.ProgErase(ta2))
              && WalkPairLk(rer, qm, code, inp, ta1, gm, x as nat, ATR.EaOf(b))
              && WalkPairLk(rer, qm, code, inp, ta2, gm, y as nat, ATR.EaOf(b))
    decreases ATR.MsizeA(acts)
  {
    var g := ATR.EaOf(b);
    var pcmid: nat :| AR.ActionRepL(rer, qm, acts[0], code, pc, pcmid) && AR.ActionsRepL(rer, qm, acts[1..], code, pcmid);
    EL.PikeLkActionsTail(acts);
    assert acts == [acts[0]] + acts[1..];
    EL.PikeLkActionsConsIff(acts[0], acts[1..]);
    var cont := acts[1..];
    match acts[0]
    case Acheck(strcheck) =>
      // EndLoop != Fork ⟹ the BackForkAt disjunct: pcmid == pc.
      assert AR.BackForkAt(code, pc);
      assert x >= 0 && y >= 0;
      if b == BS.CanExit {
        assert tb.Progress? && EL.BoolTreeLk(rer, cont, inp, BS.CanExit, tb.t);
        assert AR.ActionsRepL(rer, qm, cont, code, pc);
        GateAheadClearTail(acts, gm);
        WalkDefsOkTail(acts);
        assert ATR.MsizeA(cont) < ATR.MsizeA(acts);
        WalkPairLkAtForkCore(rer, qm, code, inp, tb.t, gm, pc, BS.CanExit, cont, x, y);
        // the erased result lifts through the Progress wrapper verbatim
        assert CE.ProgErase(tb) == CE.ProgErase(tb.t);
        assert ATR.EaOf(BS.CanExit) == ATR.EaOf(b);
      } else {
        assert tb == LT.Mismatch;
      }
    case Aclose(_) =>   // pins SetRegisterToCP — not Fork
    case Areg(r0) =>
      assert EL.PikeLkRegex(r0);
      match r0
      case Epsilon =>
        assert pcmid == pc;
        assert EL.BoolTreeLk(rer, cont, inp, b, tb);
        assert ATR.MsizeA(cont) < ATR.MsizeA(acts);
        GateAheadClearTail(acts, gm);
        WalkDefsOkTail(acts);
        WalkPairLkAtForkCore(rer, qm, code, inp, tb, gm, pc, b, cont, x, y);
      case Sequence(r1, r2) =>
        assert acts[0] == LS.Areg(L.Sequence(r1, r2));
        assert AR.NfaRepL(rer, qm, L.Sequence(r1, r2), code, pc, pcmid);
        var e1: nat :| AR.NfaRepL(rer, qm, r1, code, pc, e1) && AR.NfaRepL(rer, qm, r2, code, e1, pcmid);
        var na := [LS.Areg(r1), LS.Areg(r2)] + cont;
        assert na == [LS.Areg(r1)] + ([LS.Areg(r2)] + cont);
        AR.ActionsRepLCons(rer, qm, LS.Areg(r2), cont, code, e1, pcmid);
        AR.ActionsRepLCons(rer, qm, LS.Areg(r1), [LS.Areg(r2)] + cont, code, pc, e1);
        assert AR.ActionsRepL(rer, qm, na, code, pc);
        assert EL.PikeLkActions(na) by {
          EL.PikeLkActionsConsIff(LS.Areg(r2), cont);
          EL.PikeLkActionsConsIff(LS.Areg(r1), [LS.Areg(r2)] + cont);
        }
        assert EL.BoolTreeLk(rer, na, inp, b, tb);
        assert LS.ActionsRegexSize(acts) == RegSz(r1) + RegSz(r2) + 1 + LS.ActionsRegexSize(cont);
        assert LS.ActionsRegexSize(na) == RegSz(r1) + RegSz(r2) + LS.ActionsRegexSize(cont);
        assert ATR.MsizeA(na) < ATR.MsizeA(acts);
        GateAheadClearSeqExpand(acts, r1, r2, gm);
        WalkDefsOkSeqExpand(acts, r1, r2);
        WalkPairLkAtForkCore(rer, qm, code, inp, tb, gm, pc, b, na, x, y);
      case Disjunction(r1, r2) =>
        var e1: nat :| NR.GetPcRE(code, pc) == Some(RB.Fork(pc + 1, e1 + 1))
                       && AR.NfaRepL(rer, qm, r1, code, pc + 1, e1)
                       && NR.GetPcRE(code, e1) == Some(RB.Jmp(pcmid))
                       && AR.NfaRepL(rer, qm, r2, code, e1 + 1, pcmid);
        assert x == pc + 1 && y == e1 + 1;
        assert tb.Choice?
               && EL.BoolTreeLk(rer, [LS.Areg(r1)] + cont, inp, b, tb.t1)
               && EL.BoolTreeLk(rer, [LS.Areg(r2)] + cont, inp, b, tb.t2);
        // arm reps: r1's tail rides the mid Jmp; r2's is direct
        assert AR.ActionsRepL(rer, qm, cont, code, e1);   // jump_bc via Jmp(pcmid)
        AR.ActionsRepLCons(rer, qm, LS.Areg(r1), cont, code, pc + 1, e1);
        AR.ActionsRepLCons(rer, qm, LS.Areg(r2), cont, code, e1 + 1, pcmid);
        assert EL.PikeLkActions([LS.Areg(r1)] + cont) && EL.PikeLkActions([LS.Areg(r2)] + cont) by {
          EL.PikeLkActionsConsIff(LS.Areg(r1), cont);
          EL.PikeLkActionsConsIff(LS.Areg(r2), cont);
        }
        GateAheadClearDisjArm(acts, r1, r2, r1, gm);
        GateAheadClearDisjArm(acts, r1, r2, r2, gm);
        WalkDefsOkDisjArm(acts, r1, r2, r1);
        WalkDefsOkDisjArm(acts, r1, r2, r2);
        assert WalkPairLk(rer, qm, code, inp, tb.t1, gm, x as nat, g)
               && WalkPairLk(rer, qm, code, inp, tb.t2, gm, y as nat, g);
        assert CE.ProgErase(tb) == LT.Choice(CE.ProgErase(tb.t1), CE.ProgErase(tb.t2));
        assert exists ta1: LT.Tree, ta2: LT.Tree ::
            CE.ProgErase(tb) == LT.Choice(CE.ProgErase(ta1), CE.ProgErase(ta2))
            && WalkPairLk(rer, qm, code, inp, ta1, gm, x as nat, ATR.EaOf(b))
            && WalkPairLk(rer, qm, code, inp, ta2, gm, y as nat, ATR.EaOf(b)) by {
          assert WalkPairLk(rer, qm, code, inp, tb.t1, gm, x as nat, ATR.EaOf(b));
          assert WalkPairLk(rer, qm, code, inp, tb.t2, gm, y as nat, ATR.EaOf(b));
        }
      case Quantified(greedy, min, delta, r1) =>
        assert acts[0] == LS.Areg(L.Quantified(greedy, min, delta, r1));
        assert AR.NfaRepL(rer, qm, L.Quantified(greedy, min, delta, r1), code, pc, pcmid);
        if min == 0 && delta == LN.NN(0) {
          var em: nat :| AR.NfaRepMinL(rer, qm, 0, r1, code, pc, em)
                         && AR.NfaRepOptL(rer, qm, 0, greedy, r1, code, em, pcmid);
          NfaRepMinLHeadPin(rer, qm, 0, r1, code, pc, em);
          NfaRepOptLHeadPin(rer, qm, 0, greedy, r1, code, em, pcmid);
          assert pcmid == pc;
          assert AR.ActionsRepL(rer, qm, cont, code, pc);
          assert EL.BoolTreeLk(rer, cont, inp, b, tb);
          assert ATR.MsizeA(cont) < ATR.MsizeA(acts);
          GateAheadClearTail(acts, gm);
          WalkDefsOkTail(acts);
          WalkPairLkAtForkCore(rer, qm, code, inp, tb, gm, pc, b, cont, x, y);
        } else if min > 0 {
          QuantHeadPinsForkOrSQC(rer, qm, greedy, min, delta, r1, code, pc, pcmid);
          assert false;   // min>0 head pins SetQuantToClock, not Fork
        } else {
          // min == 0 with Inf or NN(kx>0): the star fork — tb is the Choice.
          var gidl := L.DefGroups(r1);
          var q' := L.Quantified(greedy, 0, FS.NoiPred(delta), r1);
          var itert := if greedy then tb.t1 else tb.t2;
          var skipt := if greedy then tb.t2 else tb.t1;
          assert tb.Choice?
                 && itert.GroupActionT? && itert.g == LG.Reset(gidl)
                 && EL.BoolTreeLk(rer, [LS.Areg(r1), LS.Acheck(inp), LS.Areg(q')] + cont,
                                  inp, BS.CannotExit, itert.t)
                 && EL.BoolTreeLk(rer, cont, inp, b, skipt);
          var armlist := [LS.Areg(r1), LS.Acheck(inp), LS.Areg(q')] + cont;
          assert EL.PikeLkActions(armlist) by {
            assert EL.PikeLkRegex(r1) && EL.PikeLkRegex(q');
            EL.PikeLkActionsConsIff(LS.Areg(q'), cont);
            EL.PikeLkActionsConsIff(LS.Acheck(inp), [LS.Areg(q')] + cont);
            EL.PikeLkActionsConsIff(LS.Areg(r1), [LS.Acheck(inp)] + ([LS.Areg(q')] + cont));
            assert [LS.Areg(r1)] + ([LS.Acheck(inp)] + ([LS.Areg(q')] + cont)) == armlist;
          }
          StarArmInvariants(acts, r1, q', LS.Acheck(inp), gm, gidl);
          // skip arm invariants
          GateAheadClearTail(acts, gm);
          WalkDefsOkTail(acts);
          match delta
          case Inf =>
            assert q' == L.Quantified(greedy, 0, LN.Inf, r1);
            if exists e1: nat ::
                NR.GetPcRE(code, pc) == Some(if greedy then RB.Fork(pc + 1, e1 + 2) else RB.Fork(e1 + 2, pc + 1))
                && (exists qid: int :: NR.GetPcRE(code, pc + 1) == Some(RB.SetQuantToClock(qid, false))
                                       && qid in qm.quants && qm.quants[qid] == L.DefGroups(r1))
                && NR.GetPcRE(code, pc + 2) == Some(RB.BeginLoop)
                && AR.NfaRepL(rer, qm, r1, code, pc + 3, e1)
                && NR.GetPcRE(code, e1) == Some(RB.EndLoop)
                && NR.GetPcRE(code, e1 + 1) == Some(RB.Jmp(pc))
                && pcmid == e1 + 2 {
              // ---- the LOOP BLOCK: SQC at pc+1, BeginLoop at pc+2 ----------
              var e1: nat :|
                NR.GetPcRE(code, pc) == Some(if greedy then RB.Fork(pc + 1, e1 + 2) else RB.Fork(e1 + 2, pc + 1))
                && (exists qid: int :: NR.GetPcRE(code, pc + 1) == Some(RB.SetQuantToClock(qid, false))
                                       && qid in qm.quants && qm.quants[qid] == L.DefGroups(r1))
                && NR.GetPcRE(code, pc + 2) == Some(RB.BeginLoop)
                && AR.NfaRepL(rer, qm, r1, code, pc + 3, e1)
                && NR.GetPcRE(code, e1) == Some(RB.EndLoop)
                && NR.GetPcRE(code, e1 + 1) == Some(RB.Jmp(pc))
                && pcmid == e1 + 2;
              var qid: int :| NR.GetPcRE(code, pc + 1) == Some(RB.SetQuantToClock(qid, false))
                              && qid in qm.quants && qm.quants[qid] == L.DefGroups(r1);
              // armlist rep at pc+3: r1; Acheck at EndLoop; q'+cont via the back-jump
              assert AR.ActionsRepL(rer, qm, [LS.Areg(q')] + cont, code, pc) by {
                AR.ActionsRepLCons(rer, qm, LS.Areg(q'), cont, code, pc, pcmid);
              }
              assert AR.ActionsRepL(rer, qm, [LS.Areg(q')] + cont, code, e1 + 1);   // jump_bc
              assert AR.ActionRepL(rer, qm, LS.Acheck(inp), code, e1, e1 + 1);      // EndLoop
              AR.ActionsRepLCons(rer, qm, LS.Acheck(inp), [LS.Areg(q')] + cont, code, e1, e1 + 1);
              AR.ActionsRepLCons(rer, qm, LS.Areg(r1), [LS.Acheck(inp)] + ([LS.Areg(q')] + cont),
                                 code, pc + 3, e1);
              assert [LS.Areg(r1)] + ([LS.Acheck(inp)] + ([LS.Areg(q')] + cont)) == armlist;
              assert AR.ActionsRepL(rer, qm, armlist, code, pc + 3);
              StarIterArmWalkBL(rer, qm, code, inp, gm, pc + 1, g, qid, r1, itert.t, armlist);
              assert WalkPairLk(rer, qm, code, inp, itert, gm, pc + 1, g);
              // skip arm at pcmid == e1+2
              assert WalkPairLk(rer, qm, code, inp, skipt, gm, pcmid, g);
              if greedy {
                assert x == pc + 1 && y == e1 + 2;
              } else {
                assert x == e1 + 2 && y == pc + 1;
              }
              assert WalkPairLk(rer, qm, code, inp, tb.t1, gm, x as nat, g)
                     && WalkPairLk(rer, qm, code, inp, tb.t2, gm, y as nat, g);
              assert CE.ProgErase(tb) == LT.Choice(CE.ProgErase(tb.t1), CE.ProgErase(tb.t2));
              assert exists ta1: LT.Tree, ta2: LT.Tree ::
                  CE.ProgErase(tb) == LT.Choice(CE.ProgErase(ta1), CE.ProgErase(ta2))
                  && WalkPairLk(rer, qm, code, inp, ta1, gm, x as nat, ATR.EaOf(b))
                  && WalkPairLk(rer, qm, code, inp, ta2, gm, y as nat, ATR.EaOf(b)) by {
                assert WalkPairLk(rer, qm, code, inp, tb.t1, gm, x as nat, ATR.EaOf(b));
                assert WalkPairLk(rer, qm, code, inp, tb.t2, gm, y as nat, ATR.EaOf(b));
              }

            } else {
              // ---- the LOOP VIEW: SQC at em (backward), body directly after
              assert NUL.NonNullableL(r1);
              var em: nat :| NR.GetPcRE(code, pc) == Some(if greedy then RB.Fork(em, pc + 1) else RB.Fork(pc + 1, em))
                             && em <= pc
                             && (exists qid: int :: NR.GetPcRE(code, em) == Some(RB.SetQuantToClock(qid, false))
                                                    && qid in qm.quants && qm.quants[qid] == L.DefGroups(r1))
                             && AR.NfaRepL(rer, qm, r1, code, em + 1, pc)
                             && pcmid == pc + 1;
              var qid: int :| NR.GetPcRE(code, em) == Some(RB.SetQuantToClock(qid, false))
                              && qid in qm.quants && qm.quants[qid] == L.DefGroups(r1);
              // armlist rep at em+1: r1 to pc; Acheck dissolves at the back fork; q'+cont at pc
              assert AR.ActionsRepL(rer, qm, [LS.Areg(q')] + cont, code, pc) by {
                AR.ActionsRepLCons(rer, qm, LS.Areg(q'), cont, code, pc, pcmid);
              }
              assert AR.BackForkAt(code, pc);
              assert AR.ActionRepL(rer, qm, LS.Acheck(inp), code, pc, pc);
              AR.ActionsRepLCons(rer, qm, LS.Acheck(inp), [LS.Areg(q')] + cont, code, pc, pc);
              AR.ActionsRepLCons(rer, qm, LS.Areg(r1), [LS.Acheck(inp)] + ([LS.Areg(q')] + cont),
                                 code, em + 1, pc);
              assert [LS.Areg(r1)] + ([LS.Acheck(inp)] + ([LS.Areg(q')] + cont)) == armlist;
              assert AR.ActionsRepL(rer, qm, armlist, code, em + 1);
              assert armlist == [LS.Areg(r1)] + ([LS.Acheck(inp), LS.Areg(q')] + cont);
              StarIterArmWalkLV(rer, qm, code, inp, gm, em, g, qid, r1, itert.t,
                                [LS.Acheck(inp), LS.Areg(q')] + cont);
              assert WalkPairLk(rer, qm, code, inp, itert, gm, em, g);
              assert WalkPairLk(rer, qm, code, inp, skipt, gm, pc + 1, g);
              if greedy {
                assert x == em && y == pc + 1;
              } else {
                assert x == pc + 1 && y == em;
              }
              assert WalkPairLk(rer, qm, code, inp, tb.t1, gm, x as nat, g)
                     && WalkPairLk(rer, qm, code, inp, tb.t2, gm, y as nat, g);
              assert CE.ProgErase(tb) == LT.Choice(CE.ProgErase(tb.t1), CE.ProgErase(tb.t2));
              assert exists ta1: LT.Tree, ta2: LT.Tree ::
                  CE.ProgErase(tb) == LT.Choice(CE.ProgErase(ta1), CE.ProgErase(ta2))
                  && WalkPairLk(rer, qm, code, inp, ta1, gm, x as nat, ATR.EaOf(b))
                  && WalkPairLk(rer, qm, code, inp, ta2, gm, y as nat, ATR.EaOf(b)) by {
                assert WalkPairLk(rer, qm, code, inp, tb.t1, gm, x as nat, ATR.EaOf(b));
                assert WalkPairLk(rer, qm, code, inp, tb.t2, gm, y as nat, ATR.EaOf(b));
              }

            }
          case NN(kx) =>
            assert kx > 0;
            assert q' == L.Quantified(greedy, 0, LN.NN(kx - 1), r1);
            var em0: nat :| AR.NfaRepMinL(rer, qm, 0, r1, code, pc, em0)
                            && AR.NfaRepOptL(rer, qm, kx, greedy, r1, code, em0, pcmid);
            NfaRepMinLHeadPin(rer, qm, 0, r1, code, pc, em0);
            assert em0 == pc;
            var e1x: nat :| NR.GetPcRE(code, pc) == Some(if greedy then RB.Fork(pc + 1, pcmid) else RB.Fork(pcmid, pc + 1))
                            && (exists qid: int :: NR.GetPcRE(code, pc + 1) == Some(RB.SetQuantToClock(qid, false))
                                                   && qid in qm.quants && qm.quants[qid] == L.DefGroups(r1))
                            && NR.GetPcRE(code, pc + 2) == Some(RB.BeginLoop)
                            && AR.NfaRepL(rer, qm, r1, code, pc + 3, e1x)
                            && NR.GetPcRE(code, e1x) == Some(RB.EndLoop)
                            && AR.NfaRepOptL(rer, qm, kx - 1, greedy, r1, code, e1x + 1, pcmid);
            var qid: int :| NR.GetPcRE(code, pc + 1) == Some(RB.SetQuantToClock(qid, false))
                            && qid in qm.quants && qm.quants[qid] == L.DefGroups(r1);
            // q' at e1x+1: zero forced copies + the kx-1 optional layers
            assert AR.NfaRepL(rer, qm, q', code, e1x + 1, pcmid) by {
              assert AR.NfaRepMinL(rer, qm, 0, r1, code, e1x + 1, e1x + 1);
            }
            AR.ActionsRepLCons(rer, qm, LS.Areg(q'), cont, code, e1x + 1, pcmid);
            assert AR.ActionRepL(rer, qm, LS.Acheck(inp), code, e1x, e1x + 1);   // EndLoop
            AR.ActionsRepLCons(rer, qm, LS.Acheck(inp), [LS.Areg(q')] + cont, code, e1x, e1x + 1);
            AR.ActionsRepLCons(rer, qm, LS.Areg(r1), [LS.Acheck(inp)] + ([LS.Areg(q')] + cont),
                               code, pc + 3, e1x);
            assert [LS.Areg(r1)] + ([LS.Acheck(inp)] + ([LS.Areg(q')] + cont)) == armlist;
            assert AR.ActionsRepL(rer, qm, armlist, code, pc + 3);
            StarIterArmWalkBL(rer, qm, code, inp, gm, pc + 1, g, qid, r1, itert.t, armlist);
            assert WalkPairLk(rer, qm, code, inp, itert, gm, pc + 1, g);
            assert WalkPairLk(rer, qm, code, inp, skipt, gm, pcmid, g);
            if greedy {
              assert x == pc + 1 && y == pcmid;
            } else {
              assert x == pcmid && y == pc + 1;
            }
            assert WalkPairLk(rer, qm, code, inp, tb.t1, gm, x as nat, g)
                   && WalkPairLk(rer, qm, code, inp, tb.t2, gm, y as nat, g);
            assert CE.ProgErase(tb) == LT.Choice(CE.ProgErase(tb.t1), CE.ProgErase(tb.t2));
            assert exists ta1: LT.Tree, ta2: LT.Tree ::
                CE.ProgErase(tb) == LT.Choice(CE.ProgErase(ta1), CE.ProgErase(ta2))
                && WalkPairLk(rer, qm, code, inp, ta1, gm, x as nat, ATR.EaOf(b))
                && WalkPairLk(rer, qm, code, inp, ta2, gm, y as nat, ATR.EaOf(b)) by {
              assert WalkPairLk(rer, qm, code, inp, tb.t1, gm, x as nat, ATR.EaOf(b));
              assert WalkPairLk(rer, qm, code, inp, tb.t2, gm, y as nat, ATR.EaOf(b));
            }

        }
      case Character(_) =>   // pins Consume — not Fork
      case Group(_, _) =>   // pins SetRegisterToCP — not Fork
      case LookaroundR(_, _) =>   // pins CheckOracle/NegCheckOracle — not Fork
      case AnchorR(_) =>   // pins AnchorAssertion — not Fork
      case Backreference(_) =>   // NfaRepL false
  }

  /** WalkPairLk→arms wrapper at a `Fork(x, y)` (the two stutter disjuncts are
      dead at a Fork pc). */
  lemma WalkPairLkAtForkArms(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                             tb: LT.Tree, gm: LG.GroupMap, pc: nat, ea: bool, x: int, y: int)
    requires WalkPairLk(rer, qm, code, inp, tb, gm, pc, ea)
    requires NR.GetPcRE(code, pc) == Some(RB.Fork(x, y))
    ensures x >= 0 && y >= 0
    ensures CE.ProgErase(tb) == LT.Mismatch
            || exists ta1: LT.Tree, ta2: LT.Tree ::
              CE.ProgErase(tb) == LT.Choice(CE.ProgErase(ta1), CE.ProgErase(ta2))
              && WalkPairLk(rer, qm, code, inp, ta1, gm, x as nat, ea)
              && WalkPairLk(rer, qm, code, inp, ta2, gm, y as nat, ea)
  {
    var acts: LS.Actions, b: BS.LoopBool :|
      AR.ActionsRepL(rer, qm, acts, code, pc)
      && EL.PikeLkActions(acts)
      && ATR.EaOf(b) == ea
      && EL.BoolTreeLk(rer, acts, inp, b, tb)
      && GateAheadClear(acts, gm)
      && WalkDefsOk(acts);
    WalkPairLkAtForkCore(rer, qm, code, inp, tb, gm, pc, b, acts, x, y);
  }

  /** THE CheckOracle CONTINUATION WALK (fueled core). Mirrors
      `TtLkAtCheckOracleCore` — same transparent peel to the gate head — but
      carries `GateAheadClear(acts, gm)` and the `NoDupSeq(AllDefsActs(acts))`
      walk-invariant, and at a PASSING positive gate PRODUCES the continuation
      `WalkPairLk(tb.t, gm2, pc+1, ea)` (not a bare `TtLk`): the merged map
      `gm2 = LkResult(lk, tb.tlk, gm, inp).value` is `GateAheadClear` on the
      continuation `cont` via `GateAheadClearAfterMerge`, whose DefGroups-
      disjointness obligation is discharged from `NoDupConcat` on
      `DefGroups(r1) + AllDefsActs(cont)` (the crossed gate's body sits in the
      prefix, every other pending gate's body in the dup-free suffix). This is
      the intricate piece that finishes `ThreadRepLkStepCheckOracle`'s
      continuation-walk `requires`. */
  lemma WalkPairLkAtCheckOracleCore(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                                    tb: LT.Tree, gm: LG.GroupMap, pc: nat, b: BS.LoopBool,
                                    acts: LS.Actions, lid: int)
    requires AR.ActionsRepL(rer, qm, acts, code, pc)
    requires EL.PikeLkActions(acts)
    requires EL.BoolTreeLk(rer, acts, inp, b, tb)
    requires NR.GetPcRE(code, pc) == Some(RB.CheckOracle(lid))
    requires LL.OracleOkAt(rer, qm, inp)
    requires GateAheadClear(acts, gm)
    requires WalkDefsOk(acts)
    ensures lid in qm.looks
    ensures var (lk, r1) := qm.looks[lid];
            (LOr.view_get_oracle(qm.ov, TR_CpOf(inp), lid) ==>
               tb.LK? && tb.lk == lk
               && EL.LkGateOk(rer, lk, r1, inp, tb.tlk, true)
               && LS.LkResult(lk, tb.tlk, gm, inp).Some?
               && WalkPairLk(rer, qm, code, inp, tb.t, LS.LkResult(lk, tb.tlk, gm, inp).value,
                             pc + 1, ATR.EaOf(b)))
            && (!LOr.view_get_oracle(qm.ov, TR_CpOf(inp), lid) ==>
                  tb.LKFail? && tb.lk == lk
                  && EL.LkGateOk(rer, lk, r1, inp, tb.tlk, false))
    // the gate's OWN GateAheadClear instance: it is pending at the real head,
    // so its body groups are absent from the accumulated map (discharges
    // `ThreadRepLkStepCheckOracle`'s absence hypothesis)
    ensures forall gg :: gg in L.DefGroups(qm.looks[lid].1) ==> gg !in gm
    decreases ATR.MsizeA(acts)
  {
    var g := ATR.EaOf(b);
    var pcmid: nat :| AR.ActionRepL(rer, qm, acts[0], code, pc, pcmid) && AR.ActionsRepL(rer, qm, acts[1..], code, pcmid);
    EL.PikeLkActionsTail(acts);
    assert acts == [acts[0]] + acts[1..];
    EL.PikeLkActionsConsIff(acts[0], acts[1..]);
    var cont := acts[1..];
    match acts[0]
    case Acheck(_) =>   // pins EndLoop / backward Fork — not CheckOracle
    case Aclose(_) =>   // pins SetRegisterToCP — not CheckOracle
    case Areg(r0) =>
      assert EL.PikeLkRegex(r0);
      match r0
      case Epsilon =>
        assert pcmid == pc;
        assert EL.BoolTreeLk(rer, cont, inp, b, tb);
        assert ATR.MsizeA(cont) < ATR.MsizeA(acts);
        GateAheadClearTail(acts, gm);
        WalkDefsOkTail(acts);
        WalkPairLkAtCheckOracleCore(rer, qm, code, inp, tb, gm, pc, b, cont, lid);
      case Sequence(r1, r2) =>
        assert acts[0] == LS.Areg(L.Sequence(r1, r2));
        assert AR.NfaRepL(rer, qm, L.Sequence(r1, r2), code, pc, pcmid);
        var e1: nat :| AR.NfaRepL(rer, qm, r1, code, pc, e1) && AR.NfaRepL(rer, qm, r2, code, e1, pcmid);
        var na := [LS.Areg(r1), LS.Areg(r2)] + cont;
        assert na == [LS.Areg(r1)] + ([LS.Areg(r2)] + cont);
        AR.ActionsRepLCons(rer, qm, LS.Areg(r2), cont, code, e1, pcmid);
        AR.ActionsRepLCons(rer, qm, LS.Areg(r1), [LS.Areg(r2)] + cont, code, pc, e1);
        assert AR.ActionsRepL(rer, qm, na, code, pc);
        assert EL.PikeLkActions(na) by {
          EL.PikeLkActionsConsIff(LS.Areg(r2), cont);
          EL.PikeLkActionsConsIff(LS.Areg(r1), [LS.Areg(r2)] + cont);
        }
        assert EL.BoolTreeLk(rer, na, inp, b, tb);
        assert LS.ActionsRegexSize(acts) == RegSz(r1) + RegSz(r2) + 1 + LS.ActionsRegexSize(cont);
        assert LS.ActionsRegexSize(na) == RegSz(r1) + RegSz(r2) + LS.ActionsRegexSize(cont);
        assert ATR.MsizeA(na) < ATR.MsizeA(acts);
        GateAheadClearSeqExpand(acts, r1, r2, gm);
        // NoDupSeq(AllDefsActs(na)) == NoDupSeq(AllDefsActs(acts)) (same sequence).
        M.AllDefsActsCons(acts[0], cont);
        M.AllDefsActsCons(LS.Areg(r1), [LS.Areg(r2)] + cont);
        M.AllDefsActsCons(LS.Areg(r2), cont);
        assert L.DefGroups(L.Sequence(r1, r2)) == L.DefGroups(r1) + L.DefGroups(r2);
        assert L.DefGroups(r1) + (L.DefGroups(r2) + M.AllDefsActs(cont))
            == (L.DefGroups(r1) + L.DefGroups(r2)) + M.AllDefsActs(cont);
        assert M.AllDefsActs(na) == M.AllDefsActs(acts);
        WalkDefsOkSeqExpand(acts, r1, r2);
        WalkPairLkAtCheckOracleCore(rer, qm, code, inp, tb, gm, pc, b, na, lid);
      case Quantified(greedy, min, delta, r1) =>
        if min == 0 && delta == LN.NN(0) {
          assert acts[0] == LS.Areg(L.Quantified(greedy, 0, LN.NN(0), r1));
          assert AR.NfaRepL(rer, qm, L.Quantified(greedy, 0, LN.NN(0), r1), code, pc, pcmid);
          var em: nat :| AR.NfaRepMinL(rer, qm, 0, r1, code, pc, em)
                         && AR.NfaRepOptL(rer, qm, 0, greedy, r1, code, em, pcmid);
          NfaRepMinLHeadPin(rer, qm, 0, r1, code, pc, em);
          NfaRepOptLHeadPin(rer, qm, 0, greedy, r1, code, em, pcmid);
          assert pcmid == pc;
          assert AR.ActionsRepL(rer, qm, cont, code, pc);
          assert EL.BoolTreeLk(rer, cont, inp, b, tb);
          assert ATR.MsizeA(cont) < ATR.MsizeA(acts);
          GateAheadClearTail(acts, gm);
          WalkDefsOkTail(acts);
          WalkPairLkAtCheckOracleCore(rer, qm, code, inp, tb, gm, pc, b, cont, lid);
        } else {
          assert acts[0] == LS.Areg(L.Quantified(greedy, min, delta, r1));
          assert AR.NfaRepL(rer, qm, L.Quantified(greedy, min, delta, r1), code, pc, pcmid);
          QuantHeadPinsForkOrSQC(rer, qm, greedy, min, delta, r1, code, pc, pcmid);
        }
      case LookaroundR(lk0, r1) =>
        var lid0: int :| NR.GetPcRE(code, pc) == Some(if AR.PositiveL(lk0) then RB.CheckOracle(lid0)
                                                                           else RB.NegCheckOracle(lid0))
                         && lid0 in qm.looks && qm.looks[lid0] == (lk0, r1) && pcmid == pc + 1;
        assert AR.PositiveL(lk0) && lid0 == lid;
        assert L.Positivity(lk0);
        assert lid in qm.looks && qm.looks[lid] == (lk0, r1);
        // the gate is pending at index 0 ⟹ its body groups are clear NOW
        assert RegexTopGate(L.LookaroundR(lk0, r1), lk0, r1);
        assert GatePending(acts, lk0, r1) by {
          assert acts[0].Areg? && RegexTopGate(acts[0].r, lk0, r1);
        }
        assert forall gg :: gg in L.DefGroups(r1) ==> gg !in gm;
        M.GateNodeAtInp(rer, acts, inp, b, tb, lk0, r1);   // tb is LK/LKFail with LkGateOk
        var bit := LOr.view_get_oracle(qm.ov, TR_CpOf(inp), lid);
        if tb.LK? {
          assert EL.LkGateOk(rer, lk0, r1, inp, tb.tlk, true);
          assert EL.BoolTreeLk(rer, cont, inp, b, tb.t);
          assert AR.ActionsRepL(rer, qm, cont, code, pc + 1);
          assert bit;
          // ---- gate-frame facts for LkResultAgreeOutside ----
          assert r0 == L.LookaroundR(lk0, r1);
          LookBodyNoLkBr(lk0, r1);                                     // NoLkBrL(r1)
          assert LS.LkResult(lk0, tb.tlk, LG.Empty, inp).Some?;       // LkGateOk true
          EL.LkResultGmIndep(lk0, tb.tlk, gm, inp);
          assert LS.LkResult(lk0, tb.tlk, gm, inp).Some?;
          var gm2 := LS.LkResult(lk0, tb.tlk, gm, inp).value;
          assert tb.tlk == LFU.ComputeTr(rer, [LS.Areg(r1)], inp, LG.Empty, L.LkDir(lk0));   // LkGateOk
          LkResultAgreeOutside(rer, lk0, r1, inp, tb.tlk, gm);        // GmAgreeOutside(gm2, gm, Sr1)
          var Sr1 := set gx | gx in L.DefGroups(r1);
          // AfterMerge req (2): gm2 keys ⊆ gm ∪ DefGroups(r1).
          assert forall gg :: gg in gm2 ==> gg in gm || gg in L.DefGroups(r1) by {
            forall gg | gg in gm2 ensures gg in gm || gg in L.DefGroups(r1) {
              if gg !in Sr1 { assert gg in gm2 <==> gg in gm; assert gg in gm; }
              else { assert gg in L.DefGroups(r1); }
            }
          }
          // AfterMerge req (3): pending-in-cont ⟹ pending-in-acts.
          assert forall lk2: L.Lookaround, r2: L.Regex :: GatePending(cont, lk2, r2) ==> GatePending(acts, lk2, r2) by {
            forall lk2: L.Lookaround, r2: L.Regex | GatePending(cont, lk2, r2)
              ensures GatePending(acts, lk2, r2)
            { GatePendingTail(acts, lk2, r2); }
          }
          // AfterMerge req (4): every other pending gate's body disjoint from
          // DefGroups(r1) — from C1 (TopLk NoDup): the head gate contributes
          // DefGroups(r1) as a block, pending bodies in cont sit inside
          // TopLkDefsListActs(cont) (RegexTopGateSubTopLk).
          TopLkDefsListActsCons(acts[0], cont);
          assert TopLkDefsList(L.LookaroundR(lk0, r1)) == L.DefGroups(r1);
          assert TopLkDefsListActs(acts) == L.DefGroups(r1) + TopLkDefsListActs(cont);
          M.NoDupConcat(L.DefGroups(r1), TopLkDefsListActs(cont));
          assert forall lk2: L.Lookaround, r2: L.Regex :: GatePending(cont, lk2, r2) ==>
                                                            (forall gg :: gg in L.DefGroups(r2) ==> gg !in L.DefGroups(r1)) by {
            forall lk2: L.Lookaround, r2: L.Regex | GatePending(cont, lk2, r2)
              ensures forall gg :: gg in L.DefGroups(r2) ==> gg !in L.DefGroups(r1)
            {
              var j :| 0 <= j < |cont| && cont[j].Areg? && RegexTopGate(cont[j].r, lk2, r2);
              RegexTopGateSubTopLk(cont[j].r, lk2, r2);     // set(DefGroups r2) ⊆ set(TopLk cont[j].r)
              TopLkDefsListMemberSub(cont, j);              // set(TopLk cont[j].r) ⊆ set(TopLkActs cont)
              var SR2 := set gx | gx in L.DefGroups(r2);
              var SCJ := set gx | gx in TopLkDefsList(cont[j].r);
              var SAC := set gx | gx in TopLkDefsListActs(cont);
              var SR1 := set gx | gx in L.DefGroups(r1);
              assert SR2 <= SCJ && SCJ <= SAC;              // the two lemma subsets (named-set form)
              assert SR1 * SAC == {};                       // NoDupConcat disjointness
              forall gg | gg in L.DefGroups(r2) ensures gg !in L.DefGroups(r1) {
                assert gg in SR2;
                assert gg in SAC;                           // via SR2 ⊆ SCJ ⊆ SAC
                if gg in L.DefGroups(r1) {                   // contradiction: SR1 ∩ SAC == {}
                  assert gg in SR1 && gg in SAC;
                  assert gg in SR1 * SAC;
                  assert false;
                }
              }
            }
          }
          GateAheadClearAfterMerge(acts, cont, gm, gm2, lk0, r1);   // GateAheadClear(cont, gm2)
          // Assemble WalkPairLk(tb.t, gm2, pc+1, g) via the existential disjunct.
          assert EL.PikeLkActions(cont);
          WalkDefsOkTail(acts);
          assert AR.ActionsRepL(rer, qm, cont, code, pc + 1)
                 && EL.PikeLkActions(cont)
                 && ATR.EaOf(b) == g
                 && EL.BoolTreeLk(rer, cont, inp, b, tb.t)
                 && GateAheadClear(cont, gm2)
                 && WalkDefsOk(cont);
          assert WalkPairLk(rer, qm, code, inp, tb.t, gm2, pc + 1, g);
        } else {
          assert tb.LKFail?;   // GateNodeAtInp: only LK or LKFail
          assert !bit;
        }
      case Character(_) =>   // pins Consume — not CheckOracle
      case Disjunction(_, _) =>   // pins Fork — not CheckOracle
      case Group(_, _) =>   // pins SetRegisterToCP — not CheckOracle
      case AnchorR(_) =>   // pins AnchorAssertion — not CheckOracle
      case Backreference(_) =>   // NfaRepL false
  }

  /** WalkPairLk analogue of `TtLkAtCheckOracle` — the `WalkPairLk`→`WalkPairLk`
      wrapper. At a passing positive gate, the continuation `tc` walk-pairs with
      the merged map `gm2` at `pc+1`. Extracts the walk's `acts` (now carrying
      `GateAheadClear` + `NoDupSeq(AllDefsActs)` from the augmented `WalkPairLk`)
      and applies the fueled Core. DISCHARGES `ThreadRepLkStepCheckOracle`'s
      continuation `requires`. */
  lemma WalkPairLkAtCheckOracle(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                                tb: LT.Tree, gm: LG.GroupMap, pc: nat, ea: bool, lid: int)
    requires WalkPairLk(rer, qm, code, inp, tb, gm, pc, ea)
    requires NR.GetPcRE(code, pc) == Some(RB.CheckOracle(lid))
    requires LL.OracleOkAt(rer, qm, inp)
    ensures lid in qm.looks
    ensures var (lk, r1) := qm.looks[lid];
            (LOr.view_get_oracle(qm.ov, TR_CpOf(inp), lid) ==>
               tb.LK? && tb.lk == lk
               && EL.LkGateOk(rer, lk, r1, inp, tb.tlk, true)
               && LS.LkResult(lk, tb.tlk, gm, inp).Some?
               && WalkPairLk(rer, qm, code, inp, tb.t, LS.LkResult(lk, tb.tlk, gm, inp).value, pc + 1, ea))
            && (!LOr.view_get_oracle(qm.ov, TR_CpOf(inp), lid) ==>
                  tb.LKFail? && tb.lk == lk
                  && EL.LkGateOk(rer, lk, r1, inp, tb.tlk, false))
    ensures forall gg :: gg in L.DefGroups(qm.looks[lid].1) ==> gg !in gm
  {
    // GetPcRE==CheckOracle ≠ BeginLoop kills the stutter disjunct; extract the walk.
    var acts: LS.Actions, b: BS.LoopBool :|
      AR.ActionsRepL(rer, qm, acts, code, pc)
      && EL.PikeLkActions(acts)
      && ATR.EaOf(b) == ea
      && EL.BoolTreeLk(rer, acts, inp, b, tb)
      && GateAheadClear(acts, gm)
      && WalkDefsOk(acts);
    WalkPairLkAtCheckOracleCore(rer, qm, code, inp, tb, gm, pc, b, acts, lid);
  }

  /** WalkPairLk core at an `AnchorAssertion` — the TEMPLATE for the peel-based
      NON-GATE single-child cases. Mirrors `WalkPairLkAtCheckOracleCore`'s peel
      but the head is `Areg(AnchorR)` and there is NO gate merge: `gm` is
      UNCHANGED, so `GateAheadClear`/`NoDup` transfer to the continuation by the
      plain tail bricks (`GateAheadClearTail`, `NoDupAllDefsTail`). */
  lemma WalkPairLkAtAnchorCore(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                               tb: LT.Tree, gm: LG.GroupMap, pc: nat, b: BS.LoopBool,
                               acts: LS.Actions, a: R.anchor)
    requires AR.ActionsRepL(rer, qm, acts, code, pc)
    requires EL.PikeLkActions(acts)
    requires EL.BoolTreeLk(rer, acts, inp, b, tb)
    requires NR.GetPcRE(code, pc) == Some(RB.AnchorAssertion(a))
    requires GateAheadClear(acts, gm)
    requires WalkDefsOk(acts)
    ensures tb.AnchorPass? || tb == LT.Mismatch
    ensures tb.AnchorPass? ==> WalkPairLk(rer, qm, code, inp, tb.t, gm, pc + 1, ATR.EaOf(b))
    decreases ATR.MsizeA(acts)
  {
    var g := ATR.EaOf(b);
    var pcmid: nat :| AR.ActionRepL(rer, qm, acts[0], code, pc, pcmid) && AR.ActionsRepL(rer, qm, acts[1..], code, pcmid);
    EL.PikeLkActionsTail(acts);
    assert acts == [acts[0]] + acts[1..];
    EL.PikeLkActionsConsIff(acts[0], acts[1..]);
    var cont := acts[1..];
    match acts[0]
    case Acheck(_) =>   // pins EndLoop / backward Fork — not AnchorAssertion
    case Aclose(_) =>   // pins SetRegisterToCP — not AnchorAssertion
    case Areg(r0) =>
      assert EL.PikeLkRegex(r0);
      match r0
      case Epsilon =>
        assert pcmid == pc;
        assert EL.BoolTreeLk(rer, cont, inp, b, tb);
        assert ATR.MsizeA(cont) < ATR.MsizeA(acts);
        GateAheadClearTail(acts, gm);
        WalkDefsOkTail(acts);
        WalkPairLkAtAnchorCore(rer, qm, code, inp, tb, gm, pc, b, cont, a);
      case Sequence(r1, r2) =>
        assert acts[0] == LS.Areg(L.Sequence(r1, r2));
        assert AR.NfaRepL(rer, qm, L.Sequence(r1, r2), code, pc, pcmid);
        var e1: nat :| AR.NfaRepL(rer, qm, r1, code, pc, e1) && AR.NfaRepL(rer, qm, r2, code, e1, pcmid);
        var na := [LS.Areg(r1), LS.Areg(r2)] + cont;
        assert na == [LS.Areg(r1)] + ([LS.Areg(r2)] + cont);
        AR.ActionsRepLCons(rer, qm, LS.Areg(r2), cont, code, e1, pcmid);
        AR.ActionsRepLCons(rer, qm, LS.Areg(r1), [LS.Areg(r2)] + cont, code, pc, e1);
        assert AR.ActionsRepL(rer, qm, na, code, pc);
        assert EL.PikeLkActions(na) by {
          EL.PikeLkActionsConsIff(LS.Areg(r2), cont);
          EL.PikeLkActionsConsIff(LS.Areg(r1), [LS.Areg(r2)] + cont);
        }
        assert EL.BoolTreeLk(rer, na, inp, b, tb);
        assert LS.ActionsRegexSize(acts) == RegSz(r1) + RegSz(r2) + 1 + LS.ActionsRegexSize(cont);
        assert LS.ActionsRegexSize(na) == RegSz(r1) + RegSz(r2) + LS.ActionsRegexSize(cont);
        assert ATR.MsizeA(na) < ATR.MsizeA(acts);
        GateAheadClearSeqExpand(acts, r1, r2, gm);
        M.AllDefsActsCons(acts[0], cont);
        M.AllDefsActsCons(LS.Areg(r1), [LS.Areg(r2)] + cont);
        M.AllDefsActsCons(LS.Areg(r2), cont);
        assert L.DefGroups(L.Sequence(r1, r2)) == L.DefGroups(r1) + L.DefGroups(r2);
        assert L.DefGroups(r1) + (L.DefGroups(r2) + M.AllDefsActs(cont))
            == (L.DefGroups(r1) + L.DefGroups(r2)) + M.AllDefsActs(cont);
        assert M.AllDefsActs(na) == M.AllDefsActs(acts);
        WalkDefsOkSeqExpand(acts, r1, r2);
        WalkPairLkAtAnchorCore(rer, qm, code, inp, tb, gm, pc, b, na, a);
      case Quantified(greedy, min, delta, r1) =>
        if min == 0 && delta == LN.NN(0) {
          assert acts[0] == LS.Areg(L.Quantified(greedy, 0, LN.NN(0), r1));
          assert AR.NfaRepL(rer, qm, L.Quantified(greedy, 0, LN.NN(0), r1), code, pc, pcmid);
          var em: nat :| AR.NfaRepMinL(rer, qm, 0, r1, code, pc, em)
                         && AR.NfaRepOptL(rer, qm, 0, greedy, r1, code, em, pcmid);
          NfaRepMinLHeadPin(rer, qm, 0, r1, code, pc, em);
          NfaRepOptLHeadPin(rer, qm, 0, greedy, r1, code, em, pcmid);
          assert pcmid == pc;
          assert AR.ActionsRepL(rer, qm, cont, code, pc);
          assert EL.BoolTreeLk(rer, cont, inp, b, tb);
          assert ATR.MsizeA(cont) < ATR.MsizeA(acts);
          GateAheadClearTail(acts, gm);
          WalkDefsOkTail(acts);
          WalkPairLkAtAnchorCore(rer, qm, code, inp, tb, gm, pc, b, cont, a);
        } else {
          assert acts[0] == LS.Areg(L.Quantified(greedy, min, delta, r1));
          assert AR.NfaRepL(rer, qm, L.Quantified(greedy, min, delta, r1), code, pc, pcmid);
          QuantHeadPinsForkOrSQC(rer, qm, greedy, min, delta, r1, code, pc, pcmid);
        }
      case AnchorR(la) =>
        var a2: R.anchor :| NR.GetPcRE(code, pc) == Some(RB.AnchorAssertion(a2)) && T.TrAnchor(a2) == la;
        assert pcmid == pc + 1;
        if LS.AnchorSatisfied(rer, la, inp) {
          assert tb.AnchorPass? && EL.BoolTreeLk(rer, cont, inp, b, tb.t);
          assert AR.ActionsRepL(rer, qm, cont, code, pc + 1);
          // gm UNCHANGED across AnchorPass ⟹ tail bricks give the continuation clear.
          GateAheadClearTail(acts, gm);       // GateAheadClear(cont, gm)
          WalkDefsOkTail(acts);             // NoDupSeq(AllDefsActs(cont))
          assert EL.PikeLkActions(cont);
          assert WalkPairLk(rer, qm, code, inp, tb.t, gm, pc + 1, g);
        } else {
          assert tb == LT.Mismatch;
        }
      case Character(_) =>   // pins Consume — not AnchorAssertion
      case Disjunction(_, _) =>   // pins Fork — not AnchorAssertion
      case Group(_, _) =>   // pins SetRegisterToCP — not AnchorAssertion
      case LookaroundR(_, _) =>   // pins CheckOracle/NegCheckOracle — not AnchorAssertion
      case Backreference(_) =>   // NfaRepL false
  }

  /** WalkPairLk→WalkPairLk wrapper at an `AnchorAssertion`. */
  lemma WalkPairLkAtAnchor(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                           tb: LT.Tree, gm: LG.GroupMap, pc: nat, ea: bool, a: R.anchor)
    requires WalkPairLk(rer, qm, code, inp, tb, gm, pc, ea)
    requires NR.GetPcRE(code, pc) == Some(RB.AnchorAssertion(a))
    ensures tb.AnchorPass? || tb == LT.Mismatch
    ensures tb.AnchorPass? ==> WalkPairLk(rer, qm, code, inp, tb.t, gm, pc + 1, ea)
  {
    var acts: LS.Actions, b: BS.LoopBool :|
      AR.ActionsRepL(rer, qm, acts, code, pc)
      && EL.PikeLkActions(acts)
      && ATR.EaOf(b) == ea
      && EL.BoolTreeLk(rer, acts, inp, b, tb)
      && GateAheadClear(acts, gm)
      && WalkDefsOk(acts);
    WalkPairLkAtAnchorCore(rer, qm, code, inp, tb, gm, pc, b, acts, a);
  }

  /** Per-thread ANCHOR preservation (a satisfied `AnchorAssertion`): the VM
      steps `t → t.(pc:=pc+1)` with NO register change, so the value ties are
      frame-invariant (like BeginLoop) and the walk relocates via
      `WalkPairLkAtAnchor`. The B-machine steps the `AnchorPass` head to its
      child `tb.t` (same `gm`). */
  lemma ThreadRepLkStepAnchor(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code,
                              inp: LC.Input, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
                              S: set<LG.GroupId>, tb: LT.Tree, gm: LG.GroupMap, t: AI.Thread,
                              ncap: int, nlook: int, nquant: int, a: R.anchor)
    requires ThreadRepLk(rer, qm, re, code, inp, crv, str, ov, S, tb, gm, t, ncap, nlook, nquant)
    requires NR.GetPcRE(code, t.pc as nat) == Some(RB.AnchorAssertion(a))
    requires tb.AnchorPass?     // the anchor is satisfied (else the VM drops the thread)
    ensures ThreadRepLk(rer, qm, re, code, inp, crv, str, ov, S, tb.t, gm,
                        t.(pc := t.pc + 1), ncap, nlook, nquant)
  {
    WalkPairLkAtAnchor(rer, qm, code, inp, tb, gm, t.pc as nat, t.exit_allowed, a);
    assert (t.pc + 1) as nat == (t.pc as nat) + 1;
    // GmtTieOutside/GmtTieInside read only the capture/look/quant regs, unchanged
    // by the pc update, so they transfer verbatim from ThreadRepLk(tb, gm, t).
  }

  /** (L4 NESTED) clone of `ThreadRepLkStepAnchor` — GmtTieInside dropped. */
  lemma ThreadRepLkStepAnchorNested(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code,
                                    inp: LC.Input, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
                                    S: set<LG.GroupId>, tb: LT.Tree, gm: LG.GroupMap, t: AI.Thread,
                                    ncap: int, nlook: int, nquant: int, a: R.anchor)
    requires ThreadRepLkNested(rer, qm, re, code, inp, crv, str, ov, S, tb, gm, t, ncap, nlook, nquant)
    requires NR.GetPcRE(code, t.pc as nat) == Some(RB.AnchorAssertion(a))
    requires tb.AnchorPass?     // the anchor is satisfied (else the VM drops the thread)
    ensures ThreadRepLkNested(rer, qm, re, code, inp, crv, str, ov, S, tb.t, gm,
                              t.(pc := t.pc + 1), ncap, nlook, nquant)
  {
    WalkPairLkAtAnchor(rer, qm, code, inp, tb, gm, t.pc as nat, t.exit_allowed, a);
    assert (t.pc + 1) as nat == (t.pc as nat) + 1;
    // GmtTieOutside/GmtTieInside read only the capture/look/quant regs, unchanged
    // by the pc update, so they transfer verbatim from ThreadRepLkNested(tb, gm, t).
  }

  /** `WalkPairLk` is strictly stronger than `TtLk`: its existential adds
      `GateAheadClear` + `WalkDefsOk`, which we simply drop; the two stutter
      disjuncts (BeginLoop, SQC see-through) map to `TtLk`'s. This bridge lets
      the cases that need only the tree SHAPE (Accept ⟹ Match, the Fork shape,
      and the dying LKFail/Mismatch cases) reuse the proven `TtLkAt*`
      inversions directly, with no `WalkPairLk`-specific core. */
  lemma WalkPairLkImpliesTtLk(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                              tb: LT.Tree, gm: LG.GroupMap, pc: nat, ea: bool)
    requires WalkPairLk(rer, qm, code, inp, tb, gm, pc, ea)
    ensures TtLk(rer, qm, code, inp, tb, pc, ea)
    decreases RB.size(code) - pc
  {
    if (exists acts: LS.Actions, b: BS.LoopBool ::
          AR.ActionsRepL(rer, qm, acts, code, pc) && EL.PikeLkActions(acts) && ATR.EaOf(b) == ea
          && EL.BoolTreeLk(rer, acts, inp, b, tb) && GateAheadClear(acts, gm)
          && WalkDefsOk(acts)) {
      // the existential disjunct: the same (acts, b) satisfy TtLk's exists.
      var acts: LS.Actions, b: BS.LoopBool :|
        AR.ActionsRepL(rer, qm, acts, code, pc) && EL.PikeLkActions(acts) && ATR.EaOf(b) == ea
        && EL.BoolTreeLk(rer, acts, inp, b, tb) && GateAheadClear(acts, gm)
        && WalkDefsOk(acts);
    } else if pc < RB.size(code) && NR.GetPcRE(code, pc) == Some(RB.BeginLoop)
              && WalkPairLk(rer, qm, code, inp, tb, gm, pc + 1, false) {
      // the BeginLoop stutter disjunct; recurse at pc+1.
      WalkPairLkImpliesTtLk(rer, qm, code, inp, tb, gm, pc + 1, false);
    } else {
      // the SQC see-through disjunct: recurse on the child, re-pack TtLk's.
      var q: int :| NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(q, false))
                    && q in qm.quants
                    && tb.GroupActionT? && tb.g == LG.Reset(qm.quants[q])
                    && WalkPairLk(rer, qm, code, inp, tb.t, LG.GMUpdate(tb.g, LC.Idx(inp), gm), pc + 1, ea);
      WalkPairLkImpliesTtLk(rer, qm, code, inp, tb.t, LG.GMUpdate(tb.g, LC.Idx(inp), gm), pc + 1, ea);
      assert TtLk(rer, qm, code, inp, tb.t, pc + 1, ea);
    }
  }

  /** WalkPairLk at an `Accept`: the tree is `Match` (via the `TtLk` bridge). */
  lemma WalkPairLkAtAccept(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                           tb: LT.Tree, gm: LG.GroupMap, pc: nat, ea: bool)
    requires WalkPairLk(rer, qm, code, inp, tb, gm, pc, ea)
    requires NR.GetPcRE(code, pc) == Some(RB.Accept)
    ensures tb == LT.Match
  {
    WalkPairLkImpliesTtLk(rer, qm, code, inp, tb, gm, pc, ea);
    TtLkAtAccept(rer, qm, code, inp, tb, pc, ea);
  }

  /** WalkPairLk core at a `SetRegisterToCP` — the GROUP-ACTION case. Two real
      heads (mirror of `TtLkAtSetRegCore`): `Aclose(gid)` ⟹ `Close`, `Group(gid,r1)`
      ⟹ `Open` (expanding to `[Areg r1, Aclose gid]+cont`). `gm` steps by
      `GMUpdate(tb.g, Idx(inp), gm)`; the continuation stays `GateAheadClear` —
      Close shrinks the domain (`GateAheadClearMono`), Open's `gid` is NoDup-
      disjoint from every pending body (`GateAheadClearAfterOpen`), so NO
      outside/inside invariant is needed. */
  lemma WalkPairLkAtSetRegCore(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                               tb: LT.Tree, gm: LG.GroupMap, pc: nat, b: BS.LoopBool,
                               acts: LS.Actions, r: int)
    requires AR.ActionsRepL(rer, qm, acts, code, pc)
    requires EL.PikeLkActions(acts)
    requires EL.BoolTreeLk(rer, acts, inp, b, tb)
    requires NR.GetPcRE(code, pc) == Some(RB.SetRegisterToCP(r))
    requires GateAheadClear(acts, gm)
    requires WalkDefsOk(acts)
    ensures tb.GroupActionT?
    ensures (tb.g.Open? && r == CP.start_reg(tb.g.g as int))
            || (tb.g.Close? && r == CP.end_reg(tb.g.g as int))
    ensures WalkPairLk(rer, qm, code, inp, tb.t, LG.GMUpdate(tb.g, LC.Idx(inp), gm), pc + 1, ATR.EaOf(b))
    decreases ATR.MsizeA(acts)
  {
    var g := ATR.EaOf(b);
    var pcmid: nat :| AR.ActionRepL(rer, qm, acts[0], code, pc, pcmid) && AR.ActionsRepL(rer, qm, acts[1..], code, pcmid);
    EL.PikeLkActionsTail(acts);
    assert acts == [acts[0]] + acts[1..];
    EL.PikeLkActionsConsIff(acts[0], acts[1..]);
    var cont := acts[1..];
    match acts[0]
    case Acheck(_) =>   // pins EndLoop / backward Fork — not SetRegisterToCP
    case Aclose(gid) =>
      assert pcmid == pc + 1 && r == CP.end_reg(gid as int);
      assert tb.GroupActionT? && tb.g == LG.Close(gid) && EL.BoolTreeLk(rer, cont, inp, b, tb.t);
      assert AR.ActionsRepL(rer, qm, cont, code, pc + 1);
      var gm2 := LG.GMUpdate(LG.Close(gid), LC.Idx(inp), gm);
      assert gm2 == LG.GMClose(LC.Idx(inp), gid, gm);
      GateAheadClearTail(acts, gm);
      GateAheadClearMono(cont, gm, gm2);   // GMClose keeps the domain
      WalkDefsOkTail(acts);
      assert EL.PikeLkActions(cont);
      assert WalkPairLk(rer, qm, code, inp, tb.t, gm2, pc + 1, g);
    case Areg(r0) =>
      assert EL.PikeLkRegex(r0);
      match r0
      case Epsilon =>
        assert pcmid == pc;
        assert EL.BoolTreeLk(rer, cont, inp, b, tb);
        assert ATR.MsizeA(cont) < ATR.MsizeA(acts);
        GateAheadClearTail(acts, gm);
        WalkDefsOkTail(acts);
        WalkPairLkAtSetRegCore(rer, qm, code, inp, tb, gm, pc, b, cont, r);
      case Sequence(r1, r2) =>
        assert acts[0] == LS.Areg(L.Sequence(r1, r2));
        assert AR.NfaRepL(rer, qm, L.Sequence(r1, r2), code, pc, pcmid);
        var e1: nat :| AR.NfaRepL(rer, qm, r1, code, pc, e1) && AR.NfaRepL(rer, qm, r2, code, e1, pcmid);
        var na := [LS.Areg(r1), LS.Areg(r2)] + cont;
        assert na == [LS.Areg(r1)] + ([LS.Areg(r2)] + cont);
        AR.ActionsRepLCons(rer, qm, LS.Areg(r2), cont, code, e1, pcmid);
        AR.ActionsRepLCons(rer, qm, LS.Areg(r1), [LS.Areg(r2)] + cont, code, pc, e1);
        assert AR.ActionsRepL(rer, qm, na, code, pc);
        assert EL.PikeLkActions(na) by {
          EL.PikeLkActionsConsIff(LS.Areg(r2), cont);
          EL.PikeLkActionsConsIff(LS.Areg(r1), [LS.Areg(r2)] + cont);
        }
        assert EL.BoolTreeLk(rer, na, inp, b, tb);
        assert LS.ActionsRegexSize(acts) == RegSz(r1) + RegSz(r2) + 1 + LS.ActionsRegexSize(cont);
        assert LS.ActionsRegexSize(na) == RegSz(r1) + RegSz(r2) + LS.ActionsRegexSize(cont);
        assert ATR.MsizeA(na) < ATR.MsizeA(acts);
        GateAheadClearSeqExpand(acts, r1, r2, gm);
        M.AllDefsActsCons(acts[0], cont);
        M.AllDefsActsCons(LS.Areg(r1), [LS.Areg(r2)] + cont);
        M.AllDefsActsCons(LS.Areg(r2), cont);
        assert L.DefGroups(L.Sequence(r1, r2)) == L.DefGroups(r1) + L.DefGroups(r2);
        assert L.DefGroups(r1) + (L.DefGroups(r2) + M.AllDefsActs(cont))
            == (L.DefGroups(r1) + L.DefGroups(r2)) + M.AllDefsActs(cont);
        assert M.AllDefsActs(na) == M.AllDefsActs(acts);
        WalkDefsOkSeqExpand(acts, r1, r2);
        WalkPairLkAtSetRegCore(rer, qm, code, inp, tb, gm, pc, b, na, r);
      case Group(gid, r1) =>
        var e1: nat :| NR.GetPcRE(code, pc) == Some(RB.SetRegisterToCP(CP.start_reg(gid as int)))
                       && AR.NfaRepL(rer, qm, r1, code, pc + 1, e1)
                       && NR.GetPcRE(code, e1) == Some(RB.SetRegisterToCP(CP.end_reg(gid as int)))
                       && pcmid == e1 + 1;
        assert r == CP.start_reg(gid as int);
        var ga := [LS.Areg(r1), LS.Aclose(gid)] + cont;
        assert ga == [LS.Areg(r1)] + ([LS.Aclose(gid)] + cont);
        AR.ActionsRepLCons(rer, qm, LS.Aclose(gid), cont, code, e1, pcmid);
        AR.ActionsRepLCons(rer, qm, LS.Areg(r1), [LS.Aclose(gid)] + cont, code, pc + 1, e1);
        assert AR.ActionsRepL(rer, qm, ga, code, pc + 1);
        assert tb.GroupActionT? && tb.g == LG.Open(gid) && EL.BoolTreeLk(rer, ga, inp, b, tb.t);
        assert EL.PikeLkActions(ga) by {
          EL.PikeLkActionsConsIff(LS.Aclose(gid), cont);
          EL.PikeLkActionsConsIff(LS.Areg(r1), [LS.Aclose(gid)] + cont);
        }
        var gm2 := LG.GMUpdate(LG.Open(gid), LC.Idx(inp), gm);
        // carrier across the Group expand; C1 pins gid ∉ TopLk of both parts
        WalkDefsOkGroupExpand(acts, gid, r1);
        TopLkDefsListActsCons(acts[0], cont);
        TopLkDefsListActsCons(LS.Areg(r1), [LS.Aclose(gid)] + cont);
        TopLkDefsListActsCons(LS.Aclose(gid), cont);
        assert TopLkDefsList(L.Group(gid, r1)) == [gid] + TopLkDefsList(r1);
        assert TopLkDefsListActs(acts)
            == ([gid] + TopLkDefsList(r1)) + TopLkDefsListActs(cont);
        assert ([gid] + TopLkDefsList(r1)) + TopLkDefsListActs(cont)
            == [gid] + (TopLkDefsList(r1) + TopLkDefsListActs(cont));
        M.NoDupConcat([gid], TopLkDefsList(r1) + TopLkDefsListActs(cont));
        assert TopLkDefsListActs(ga) == TopLkDefsList(r1) + TopLkDefsListActs(cont);
        // GateAheadClear(ga, gm): pending-in-ga ⟹ pending-in-acts.
        assert forall lk2: L.Lookaround, rr: L.Regex :: GatePending(ga, lk2, rr) ==> GatePending(acts, lk2, rr) by {
          forall lk2: L.Lookaround, rr: L.Regex | GatePending(ga, lk2, rr) ensures GatePending(acts, lk2, rr) {
            GatePendingGroupBack(acts, gid, r1, lk2, rr);
          }
        }
        assert GateAheadClear(ga, gm) by {
          forall lk2: L.Lookaround, rr: L.Regex | GatePending(ga, lk2, rr)
            ensures forall gg :: gg in L.DefGroups(rr) ==> gg !in gm
          { GatePendingGroupBack(acts, gid, r1, lk2, rr); }
        }
        // gid ∉ every pending body of ga (via C1: gid ∉ TopLkDefsListActs(ga) ⊇ DefGroups(rr)).
        assert forall lk2: L.Lookaround, rr: L.Regex :: GatePending(ga, lk2, rr) ==> gid !in L.DefGroups(rr) by {
          forall lk2: L.Lookaround, rr: L.Regex | GatePending(ga, lk2, rr) ensures gid !in L.DefGroups(rr) {
            var j :| 0 <= j < |ga| && ga[j].Areg? && RegexTopGate(ga[j].r, lk2, rr);
            RegexTopGateSubTopLk(ga[j].r, lk2, rr);
            TopLkDefsListMemberSub(ga, j);
            var SRR := set gx | gx in L.DefGroups(rr);
            var SGJ := set gx | gx in TopLkDefsList(ga[j].r);
            var SAG := set gx | gx in TopLkDefsListActs(ga);
            assert SRR <= SGJ && SGJ <= SAG;   // the two lemma subsets (named-set form)
            assert (set gx | gx in [gid]) * SAG == {};   // NoDupConcat disjointness
            if gid in L.DefGroups(rr) {
              assert gid in SRR && gid in SAG;           // via SRR ⊆ SGJ ⊆ SAG
              assert gid in (set gx | gx in [gid]);
              assert gid in (set gx | gx in [gid]) * SAG;   // contradicts disjoint
            }
          }
        }
        GateAheadClearAfterOpen(ga, gm, gid, LC.Idx(inp));   // GateAheadClear(ga, gm2)
        assert WalkPairLk(rer, qm, code, inp, tb.t, gm2, pc + 1, g);
      case Quantified(greedy, min, delta, r1) =>
        if min == 0 && delta == LN.NN(0) {
          assert acts[0] == LS.Areg(L.Quantified(greedy, 0, LN.NN(0), r1));
          assert AR.NfaRepL(rer, qm, L.Quantified(greedy, 0, LN.NN(0), r1), code, pc, pcmid);
          var em: nat :| AR.NfaRepMinL(rer, qm, 0, r1, code, pc, em)
                         && AR.NfaRepOptL(rer, qm, 0, greedy, r1, code, em, pcmid);
          NfaRepMinLHeadPin(rer, qm, 0, r1, code, pc, em);
          NfaRepOptLHeadPin(rer, qm, 0, greedy, r1, code, em, pcmid);
          assert pcmid == pc;
          assert AR.ActionsRepL(rer, qm, cont, code, pc);
          assert EL.BoolTreeLk(rer, cont, inp, b, tb);
          assert ATR.MsizeA(cont) < ATR.MsizeA(acts);
          GateAheadClearTail(acts, gm);
          WalkDefsOkTail(acts);
          WalkPairLkAtSetRegCore(rer, qm, code, inp, tb, gm, pc, b, cont, r);
        } else {
          assert acts[0] == LS.Areg(L.Quantified(greedy, min, delta, r1));
          assert AR.NfaRepL(rer, qm, L.Quantified(greedy, min, delta, r1), code, pc, pcmid);
          QuantHeadPinsForkOrSQC(rer, qm, greedy, min, delta, r1, code, pc, pcmid);
        }
      case Character(_) =>   // pins Consume — not SetRegisterToCP
      case Disjunction(_, _) =>   // pins Fork — not SetRegisterToCP
      case LookaroundR(_, _) =>   // pins CheckOracle/NegCheckOracle — not SetRegisterToCP
      case AnchorR(_) =>   // pins AnchorAssertion — not SetRegisterToCP
      case Backreference(_) =>   // NfaRepL false
  }

  /** WalkPairLk→WalkPairLk wrapper at a `SetRegisterToCP`. */
  lemma WalkPairLkAtSetReg(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                           tb: LT.Tree, gm: LG.GroupMap, pc: nat, ea: bool, r: int)
    requires WalkPairLk(rer, qm, code, inp, tb, gm, pc, ea)
    requires NR.GetPcRE(code, pc) == Some(RB.SetRegisterToCP(r))
    ensures tb.GroupActionT?
    ensures (tb.g.Open? && r == CP.start_reg(tb.g.g as int))
            || (tb.g.Close? && r == CP.end_reg(tb.g.g as int))
    ensures WalkPairLk(rer, qm, code, inp, tb.t, LG.GMUpdate(tb.g, LC.Idx(inp), gm), pc + 1, ea)
  {
    var acts: LS.Actions, b: BS.LoopBool :|
      AR.ActionsRepL(rer, qm, acts, code, pc)
      && EL.PikeLkActions(acts)
      && ATR.EaOf(b) == ea
      && EL.BoolTreeLk(rer, acts, inp, b, tb)
      && GateAheadClear(acts, gm)
      && WalkDefsOk(acts);
    WalkPairLkAtSetRegCore(rer, qm, code, inp, tb, gm, pc, b, acts, r);
  }

  /** WalkPairLk at a `Fork` — SHAPE only (via the `TtLk` bridge): the tree is a
      `Choice` (forward fork), a `Progress` (do-while backward fork's dissolved
      guard), or `Mismatch`. The BRANCH-PAIRING is handled at the `LiftStepC`
      level, mirroring the PROVEN `PSM.PreserveForkCase`:
       - FORWARD fork (both arms `> pc`: Disjunction / free-star initial /
         bounded): `Choice(t1,t2)`, one `pts_active`, arms pair at `x`, `y`.
       - BACKWARD fork (do-while re-entry): `Progress(Choice(t1,t2))`, `ea` forced
         true, TWO tree steps (unwrap guard, then split), arms pair at `x`, `y`.
      SEAM (the one genuine obstacle): the free-star ITERATION arm's `t1` at
      `pc+1` is `GroupActionT(Reset,..)`, which `BoolTreeLk` does NOT represent at
      a `SetQuantToClock` pc (unlike tstar's `TreeRepRE`). RESOLUTION: augment
      `WalkPairLk` with a `SetQuantToClock`-`Reset` disjunct (analog of the
      BeginLoop stutter, but consuming the `Reset` and applying `GMReset` via
      `GateAheadClearAfterReset`), making `WalkPairLk(GroupActionT(Reset,..), pc)`
      satisfiable at a `SetQuantToClock` pc. */
  lemma WalkPairLkAtFork(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                         tb: LT.Tree, gm: LG.GroupMap, pc: nat, ea: bool, x: int, y: int)
    requires WalkPairLk(rer, qm, code, inp, tb, gm, pc, ea)
    requires NR.GetPcRE(code, pc) == Some(RB.Fork(x, y))
    ensures x >= 0 && y >= 0
    ensures tb.Choice? || tb.Progress? || tb == LT.Mismatch
  {
    WalkPairLkImpliesTtLk(rer, qm, code, inp, tb, gm, pc, ea);
    TtLkAtFork(rer, qm, code, inp, tb, pc, ea, x, y);
  }

  /** ACROSS the whole action list: `AllDefsActs` no-dup ⟹ `TopLkDefsListActs`
      no-dup (the latter is a per-`Areg` subsequence of the former). This is the
      converter used at a quantifier unfold: the pre-unfold `NoDupSeq(AllDefsActs)`
      establishes the post-unfold `NoDupSeq(TopLkDefsListActs)` (which the
      re-entrant `Quantified` residual no longer breaks). */
  lemma TopLkNoDupFromAllDefs(acts: LS.Actions)
    requires M.NoDupSeq(M.AllDefsActs(acts))
    ensures M.NoDupSeq(TopLkDefsListActs(acts))
    decreases |acts|
  {
    if |acts| == 0 { return; }
    assert acts == [acts[0]] + acts[1..];
    var cont := acts[1..];
    M.AllDefsActsCons(acts[0], cont);
    TopLkDefsListActsCons(acts[0], cont);
    var headAll: seq<LG.GroupId> := if acts[0].Areg? then L.DefGroups(acts[0].r) else [];
    var headTop: seq<LG.GroupId> := if acts[0].Areg? then TopLkDefsList(acts[0].r) else [];
    assert M.AllDefsActs(acts) == headAll + M.AllDefsActs(cont);
    assert TopLkDefsListActs(acts) == headTop + TopLkDefsListActs(cont);
    M.NoDupConcat(headAll, M.AllDefsActs(cont));
    var SH := set gx | gx in headAll;
    var SC := set gx | gx in M.AllDefsActs(cont);
    assert SH * SC == {};
    // head no-dup
    if acts[0].Areg? { TopLkNoDupFromDefGroups(acts[0].r); TopLkDefsListSubDefGroups(acts[0].r); }
    // tail no-dup
    TopLkNoDupFromAllDefs(cont);
    TopLkDefsListActsSubAllDefs(cont);
    // cross-disjoint: headTop ⊆ headAll, TopLkDefsListActs(cont) ⊆ AllDefsActs(cont), disjoint
    forall i, j | 0 <= i < |headTop| && 0 <= j < |TopLkDefsListActs(cont)|
      ensures headTop[i] != TopLkDefsListActs(cont)[j]
    {
      if headTop[i] == TopLkDefsListActs(cont)[j] {
        var g := headTop[i];
        assert g in headTop && g in TopLkDefsListActs(cont);
        assert g in headAll;                          // TopLkDefsListSubDefGroups / [] case
        assert g in M.AllDefsActs(cont);              // TopLkDefsListActsSubAllDefs
        assert g in SH && g in SC && g in SH * SC;
        assert false;
      }
    }
    M.NoDupFromDisjoint(headTop, TopLkDefsListActs(cont));
  }

  /** SetQuant-unfold converter: the PRE-unfold `NoDupSeq(DefGroups(r1) +
      AllDefsActs(cont))` (= `NoDupSeq(AllDefsActs([Areg(Quantified(..,r1))]+cont))`,
      since `DefGroups(Quantified(..,r1)) == DefGroups(r1)`) establishes the
      POST-unfold `NoDupSeq(TopLkDefsListActs([Areg(r1), Areg(q')]+cont))`. The
      re-entrant residual `q'=Quantified(..,r1)` contributes `[]` to
      `TopLkDefsListActs` (STOPS at Quantified), so its duplicate of
      `DefGroups(r1)` — which breaks `AllDefsActs` NoDup post-unfold — is invisible
      to `TopLkDefsListActs`. Closes the (non-nested) quantifier body-copy case. */
  lemma QuantUnfoldTopLkNoDup(r1: L.Regex, q': L.Regex, cont: LS.Actions)
    requires q'.Quantified? && q'.r1 == r1
    requires M.NoDupSeq(L.DefGroups(r1) + M.AllDefsActs(cont))
    ensures M.NoDupSeq(TopLkDefsListActs([LS.Areg(r1), LS.Areg(q')] + cont))
  {
    var acts1 := [LS.Areg(r1), LS.Areg(q')] + cont;
    assert acts1 == [LS.Areg(r1)] + ([LS.Areg(q')] + cont);
    TopLkDefsListActsCons(LS.Areg(r1), [LS.Areg(q')] + cont);
    TopLkDefsListActsCons(LS.Areg(q'), cont);
    assert TopLkDefsList(q') == [];                                  // Quantified → []
    assert TopLkDefsListActs(acts1) == TopLkDefsList(r1) + TopLkDefsListActs(cont);
    M.NoDupConcat(L.DefGroups(r1), M.AllDefsActs(cont));
    var SR := set gx | gx in L.DefGroups(r1);
    var SC := set gx | gx in M.AllDefsActs(cont);
    assert SR * SC == {};
    TopLkNoDupFromDefGroups(r1); TopLkDefsListSubDefGroups(r1);       // NoDup(TopLk r1), ⊆ DefGroups(r1)
    TopLkNoDupFromAllDefs(cont); TopLkDefsListActsSubAllDefs(cont);   // NoDup(TopLk cont), ⊆ AllDefsActs(cont)
    forall i, j | 0 <= i < |TopLkDefsList(r1)| && 0 <= j < |TopLkDefsListActs(cont)|
      ensures TopLkDefsList(r1)[i] != TopLkDefsListActs(cont)[j]
    {
      if TopLkDefsList(r1)[i] == TopLkDefsListActs(cont)[j] {
        var g := TopLkDefsList(r1)[i];
        assert g in TopLkDefsList(r1) && g in TopLkDefsListActs(cont);
        assert g in L.DefGroups(r1) && g in M.AllDefsActs(cont);
        assert g in SR && g in SC && g in SR * SC;
        assert false;
      }
    }
    M.NoDupFromDisjoint(TopLkDefsList(r1), TopLkDefsListActs(cont));
  }

  /** THE CARRIER. */
  ghost predicate WalkDefsOk(acts: LS.Actions) {
    M.NoDupSeq(TopLkDefsListActs(acts))                                        // C1
    && (forall i | 0 <= i < |acts| && acts[i].Areg? ::
          M.NoDupSeq(L.DefGroups(acts[i].r)))                                  // C2
    && QuantsClearActs(acts)                                                   // C3
  }

  /** Carrier tail: drop the head. */
  lemma WalkDefsOkTail(acts: LS.Actions)
    requires |acts| > 0 && WalkDefsOk(acts)
    ensures WalkDefsOk(acts[1..])
  {
    NoDupTopLkTail(acts);
    forall i | 0 <= i < |acts[1..]| && acts[1..][i].Areg?
      ensures M.NoDupSeq(L.DefGroups(acts[1..][i].r))
              && QuantsRightClear(acts[1..][i].r, TopLkSetActs(acts[1..][i + 1..]))
    {
      assert acts[1..][i] == acts[i + 1];
      assert acts[1..][i + 1..] == acts[i + 2..];
    }
  }

  /** Carrier across the `Sequence` two-head expand: the TopLk list is the SAME
      sequence, the head's C3 clause unfolds DEFINITIONALLY into the two new
      heads' clauses. */
  lemma WalkDefsOkSeqExpand(acts: LS.Actions, r1: L.Regex, r2: L.Regex)
    requires |acts| > 0 && acts[0] == LS.Areg(L.Sequence(r1, r2))
    requires WalkDefsOk(acts)
    ensures WalkDefsOk([LS.Areg(r1), LS.Areg(r2)] + acts[1..])
  {
    var cont := acts[1..];
    var na := [LS.Areg(r1), LS.Areg(r2)] + cont;
    assert acts == [acts[0]] + cont;
    // C1: same TopLk sequence
    TopLkDefsListActsCons(acts[0], cont);
    TopLkDefsListActsCons(LS.Areg(r1), [LS.Areg(r2)] + cont);
    TopLkDefsListActsCons(LS.Areg(r2), cont);
    assert na == [LS.Areg(r1)] + ([LS.Areg(r2)] + cont);
    assert TopLkDefsList(L.Sequence(r1, r2)) == TopLkDefsList(r1) + TopLkDefsList(r2);
    assert TopLkDefsListActs(na)
        == TopLkDefsList(r1) + (TopLkDefsList(r2) + TopLkDefsListActs(cont));
    assert TopLkDefsList(r1) + (TopLkDefsList(r2) + TopLkDefsListActs(cont))
        == (TopLkDefsList(r1) + TopLkDefsList(r2)) + TopLkDefsListActs(cont);
    assert TopLkDefsListActs(na) == TopLkDefsListActs(acts);
    // C2: split the head's NoDup
    assert M.NoDupSeq(L.DefGroups(L.Sequence(r1, r2)));
    assert L.DefGroups(L.Sequence(r1, r2)) == L.DefGroups(r1) + L.DefGroups(r2);
    M.NoDupConcat(L.DefGroups(r1), L.DefGroups(r2));
    // C3
    assert QuantsRightClear(L.Sequence(r1, r2), TopLkSetActs(cont));
    assert TopLkSetActs([LS.Areg(r2)] + cont)
        == (set g | g in TopLkDefsList(r2)) + TopLkSetActs(cont) by {
      forall g ensures g in TopLkSetActs([LS.Areg(r2)] + cont)
                  <==> g in ((set gx | gx in TopLkDefsList(r2)) + TopLkSetActs(cont)) {
      }
    }
    forall i | 0 <= i < |na| && na[i].Areg?
      ensures M.NoDupSeq(L.DefGroups(na[i].r))
              && QuantsRightClear(na[i].r, TopLkSetActs(na[i + 1..]))
    {
      if i == 0 {
        assert na[0] == LS.Areg(r1) && na[1..] == [LS.Areg(r2)] + cont;
      } else if i == 1 {
        assert na[1] == LS.Areg(r2) && na[2..] == cont;
      } else {
        assert na[i] == cont[i - 2] == acts[i - 1];
        assert na[i + 1..] == cont[i - 1..] == acts[i..];
      }
    }
  }

  /** Carrier across the `Group` expand (`[Areg rb, Aclose gid] + cont`). */
  lemma WalkDefsOkGroupExpand(acts: LS.Actions, gid: LG.GroupId, rb: L.Regex)
    requires |acts| > 0 && acts[0] == LS.Areg(L.Group(gid, rb))
    requires WalkDefsOk(acts)
    ensures WalkDefsOk([LS.Areg(rb), LS.Aclose(gid)] + acts[1..])
  {
    var cont := acts[1..];
    var na := [LS.Areg(rb), LS.Aclose(gid)] + cont;
    assert acts == [acts[0]] + cont;
    // C1: Group is TopLk-transparent, Aclose contributes []
    TopLkDefsListActsCons(acts[0], cont);
    TopLkDefsListActsCons(LS.Areg(rb), [LS.Aclose(gid)] + cont);
    TopLkDefsListActsCons(LS.Aclose(gid), cont);
    assert na == [LS.Areg(rb)] + ([LS.Aclose(gid)] + cont);
    assert TopLkDefsList(L.Group(gid, rb)) == [gid] + TopLkDefsList(rb);
    assert TopLkDefsListActs(acts)
        == ([gid] + TopLkDefsList(rb)) + TopLkDefsListActs(cont);
    assert ([gid] + TopLkDefsList(rb)) + TopLkDefsListActs(cont)
        == [gid] + (TopLkDefsList(rb) + TopLkDefsListActs(cont));
    M.NoDupConcat([gid], TopLkDefsList(rb) + TopLkDefsListActs(cont));
    assert TopLkDefsListActs(na) == TopLkDefsList(rb) + TopLkDefsListActs(cont);
    // C2
    assert M.NoDupSeq(L.DefGroups(L.Group(gid, rb)));
    assert L.DefGroups(L.Group(gid, rb)) == [gid] + L.DefGroups(rb);
    M.NoDupConcat([gid], L.DefGroups(rb));
    // C3
    assert QuantsRightClear(L.Group(gid, rb), TopLkSetActs(cont));
    assert TopLkSetActs([LS.Aclose(gid)] + cont) == TopLkSetActs(cont) by {
      forall g ensures g in TopLkSetActs([LS.Aclose(gid)] + cont) <==> g in TopLkSetActs(cont) {
      }
    }
    forall i | 0 <= i < |na| && na[i].Areg?
      ensures M.NoDupSeq(L.DefGroups(na[i].r))
              && QuantsRightClear(na[i].r, TopLkSetActs(na[i + 1..]))
    {
      if i == 0 {
        assert na[0] == LS.Areg(rb) && na[1..] == [LS.Aclose(gid)] + cont;
      } else if i == 1 {
      } else {
        assert na[i] == cont[i - 2] == acts[i - 1];
        assert na[i + 1..] == cont[i - 1..] == acts[i..];
      }
    }
  }

  /** Carrier at the single-action entry (`[Areg rex]`). */
  lemma WalkDefsOkEntry(rex: L.Regex)
    requires M.NoDupSeq(L.DefGroups(rex))
    ensures WalkDefsOk([LS.Areg(rex)])
  {
    var acts := [LS.Areg(rex)];
    TopLkDefsListActsCons(LS.Areg(rex), []);
    assert TopLkDefsListActs(acts) == TopLkDefsList(rex) + [] == TopLkDefsList(rex);
    TopLkNoDupFromDefGroups(rex);
    assert acts[1..] == [];
    assert TopLkSetActs([]) == {};
    QuantsRightClearFromNoDup(rex, {});
  }

  /** THE UNFOLD: carrier across a quantifier body-copy expansion
      `[Areg(Quantified(.., r1))] + cont  ⟶  [Areg r1] ++ mid ++ [Areg q'] + cont`
      stated for the two shapes the walk produces (`mid` = `[]` for the min>0
      forced copy, `[Acheck(inp0)]` for the star/backfork iteration arm). The
      unfolding node's OWN C3 clause supplies the body-vs-tail freshness; C2
      supplies the body's structural NoDup; the residual `q'` is TopLk-opaque. */
  lemma WalkDefsOkUnfold(acts: LS.Actions, r1: L.Regex, q': L.Regex, mid: LS.Actions)
    requires |acts| > 0 && acts[0].Areg? && acts[0].r.Quantified? && acts[0].r.r1 == r1
    requires q'.Quantified? && q'.r1 == r1
    requires mid == [] || (|mid| == 1 && mid[0].Acheck?)
    requires WalkDefsOk(acts)
    ensures WalkDefsOk([LS.Areg(r1)] + mid + [LS.Areg(q')] + acts[1..])
  {
    var cont := acts[1..];
    var na := [LS.Areg(r1)] + mid + [LS.Areg(q')] + cont;
    assert acts == [acts[0]] + cont;
    // structural facts from the folded head
    assert M.NoDupSeq(L.DefGroups(acts[0].r));
    assert L.DefGroups(acts[0].r) == L.DefGroups(r1);
    assert QuantsRightClear(acts[0].r, TopLkSetActs(cont));
    assert forall g :: g in L.DefGroups(r1) ==> g !in TopLkSetActs(cont);
    // the TopLk view of the unfolded list: TopLk(r1) ++ TopLk(cont)
    var tail1 := mid + [LS.Areg(q')] + cont;
    var tail2 := [LS.Areg(q')] + cont;
    assert na == [LS.Areg(r1)] + tail1;
    TopLkDefsListActsCons(LS.Areg(r1), tail1);
    TopLkDefsListActsCons(LS.Areg(q'), cont);
    assert TopLkDefsList(q') == [];
    assert TopLkDefsListActs(tail2) == TopLkDefsListActs(cont);
    if |mid| == 1 {
      assert tail1 == [mid[0]] + tail2;
      TopLkDefsListActsCons(mid[0], tail2);
      assert TopLkDefsListActs(tail1) == TopLkDefsListActs(tail2);
    } else {
      assert tail1 == tail2;
    }
    assert TopLkDefsListActs(na) == TopLkDefsList(r1) + TopLkDefsListActs(cont);
    // C1: NoDup(TopLk(r1)) structural + disjoint from TopLk(cont) via the C3 clause
    TopLkNoDupFromDefGroups(r1);
    TopLkDefsListSubDefGroups(r1);
    NoDupTopLkTail(acts);
    forall i, j | 0 <= i < |TopLkDefsList(r1)| && 0 <= j < |TopLkDefsListActs(cont)|
      ensures TopLkDefsList(r1)[i] != TopLkDefsListActs(cont)[j]
    {
      if TopLkDefsList(r1)[i] == TopLkDefsListActs(cont)[j] {
        var g := TopLkDefsList(r1)[i];
        assert g in L.DefGroups(r1);
        assert g in TopLkSetActs(cont);
        assert false;
      }
    }
    M.NoDupFromDisjoint(TopLkDefsList(r1), TopLkDefsListActs(cont));
    // C2 + C3 per index
    var koff := |mid| + 2;   // na[koff + k] == cont[k]
    forall i | 0 <= i < |na| && na[i].Areg?
      ensures M.NoDupSeq(L.DefGroups(na[i].r))
              && QuantsRightClear(na[i].r, TopLkSetActs(na[i + 1..]))
    {
      if i == 0 {
        assert na[0] == LS.Areg(r1) && na[1..] == tail1;
        assert TopLkSetActs(tail1) == TopLkSetActs(cont) by {
          forall g ensures g in TopLkSetActs(tail1) <==> g in TopLkSetActs(cont) {}
        }
        QuantsRightClearFromNoDup(r1, TopLkSetActs(cont));
      } else if i < koff - 1 {
        // mid slot (Acheck): not Areg — vacuous
        assert na[i] == mid[i - 1];
      } else if i == koff - 1 {
        assert na[i] == LS.Areg(q') && na[i + 1..] == cont;
        assert L.DefGroups(q') == L.DefGroups(r1);
        forall g | g in L.DefGroups(q') ensures g !in TopLkSetActs(cont) {}
      } else {
        assert na[i] == cont[i - koff] == acts[i - koff + 1];
        assert na[i + 1..] == cont[i - koff + 1..] == acts[i - koff + 2..];
      }
    }
  }

  /** Carrier across a `Disjunction` arm choice: the other arm's TopLk block is
      DROPPED (a sub-concat of the C1 NoDup); C2/C3 select the arm's halves. */
  lemma WalkDefsOkDisjArm(acts: LS.Actions, r1: L.Regex, r2: L.Regex, arm: L.Regex)
    requires |acts| > 0 && acts[0] == LS.Areg(L.Disjunction(r1, r2))
    requires WalkDefsOk(acts)
    requires arm == r1 || arm == r2
    ensures WalkDefsOk([LS.Areg(arm)] + acts[1..])
  {
    var cont := acts[1..];
    var na := [LS.Areg(arm)] + cont;
    assert acts == [acts[0]] + cont;
    TopLkDefsListActsCons(acts[0], cont);
    TopLkDefsListActsCons(LS.Areg(arm), cont);
    var A1 := TopLkDefsList(r1);
    var A2 := TopLkDefsList(r2);
    var C := TopLkDefsListActs(cont);
    assert TopLkDefsList(L.Disjunction(r1, r2)) == A1 + A2;
    assert TopLkDefsListActs(acts) == (A1 + A2) + C;
    assert (A1 + A2) + C == A1 + (A2 + C);
    M.NoDupConcat(A1, A2 + C);
    M.NoDupConcat(A2, C);
    var AA := TopLkDefsList(arm);
    assert TopLkDefsListActs(na) == AA + C;
    // C1: NoDup(AA + C) — AA is one of A1/A2; disjointness from C in both cases
    forall i, j | 0 <= i < |AA| && 0 <= j < |C| ensures AA[i] != C[j] {
      if AA[i] == C[j] {
        var g := AA[i];
        if arm == r1 {
          assert g in A1 && g in (A2 + C);
          assert g in (set gx | gx in A1) * (set gx | gx in A2 + C);
        } else {
          assert g in A2 && g in C;
          assert g in (set gx | gx in A2) * (set gx | gx in C);
        }
      }
    }
    M.NoDupFromDisjoint(AA, C);
    // C2: split the head's DefGroups NoDup
    assert M.NoDupSeq(L.DefGroups(L.Disjunction(r1, r2)));
    assert L.DefGroups(L.Disjunction(r1, r2)) == L.DefGroups(r1) + L.DefGroups(r2);
    M.NoDupConcat(L.DefGroups(r1), L.DefGroups(r2));
    // C3: the head clause's arm conjunct (Disjunction arms share R); shifts
    assert QuantsRightClear(L.Disjunction(r1, r2), TopLkSetActs(cont));
    forall i | 0 <= i < |na| && na[i].Areg?
      ensures M.NoDupSeq(L.DefGroups(na[i].r))
              && QuantsRightClear(na[i].r, TopLkSetActs(na[i + 1..]))
    {
      if i == 0 {
        assert na[0] == LS.Areg(arm) && na[1..] == cont;
      } else {
        assert na[i] == cont[i - 1] == acts[i];
        assert na[i + 1..] == cont[i..] == acts[i + 1..];
      }
    }
  }

  /** Fuel-induction workhorse (LK-aware mirror of `PS.ComputePikeSubtree`):
      running `ComputeTree` on a backref-free action stack yields a
      `PikeSubtreeLk` tree — the only forbidden shape (`ReadBackRef`) comes
      solely from `Backreference`, which `NoBackrefActions` rules out. The
      LK/LKFail cases are now PRODUCED (not contradictions); the lookaround BODY
      is never recursed into (`PikeSubtreeLk` leaves it unconstrained), only the
      continuation. */
  lemma ComputePikeSubtreeLk(rer: LW.RegExpRecord, act: LS.Actions, inp: LC.Input,
                             gm: LG.GroupMap, dir: WP.Direction, fuel: nat, t: LT.Tree)
    requires NoBackrefActions(act)
    requires FS.ComputeTree(rer, act, inp, gm, dir, fuel) == Some(t)
    ensures PTL.PikeSubtreeLk(t)
    decreases fuel
  {
    var f := fuel - 1;
    if |act| == 0 {
    } else {
      var cont := act[1..];
      NoBackrefActionsTail(act);            // NoBackrefActions(cont)
      assert act == [act[0]] + cont;
      NoBackrefActionsCons(act[0], cont);   // NoBackrefAction(act[0])
      match act[0]
      case Acheck(strcheck) =>
        if SSx.IsStrictSuffix(inp, strcheck, dir) {
          var sub := FS.ComputeTree(rer, cont, inp, gm, dir, f);
          if sub.Some? { ComputePikeSubtreeLk(rer, cont, inp, gm, dir, f, sub.value); }
        }
      case Aclose(gid) =>
        var gm' := LG.GMClose(LC.Idx(inp), gid, gm);
        var sub := FS.ComputeTree(rer, cont, inp, gm', dir, f);
        if sub.Some? { ComputePikeSubtreeLk(rer, cont, inp, gm', dir, f, sub.value); }
      case Areg(r) =>
        assert NoBackrefRegex(r);
        match r
        case Epsilon =>
          ComputePikeSubtreeLk(rer, cont, inp, gm, dir, f, t);
        case Character(cd) =>
          match LC.ReadChar(rer, cd, inp, dir) {
            case None =>
            case Some(pair) =>
              var sub := FS.ComputeTree(rer, cont, pair.1, gm, dir, f);
              if sub.Some? { ComputePikeSubtreeLk(rer, cont, pair.1, gm, dir, f, sub.value); }
          }
        case Disjunction(r1, r2) =>
          NoBackrefActionsCons(LS.Areg(r1), cont);
          NoBackrefActionsCons(LS.Areg(r2), cont);
          var s1 := FS.ComputeTree(rer, [LS.Areg(r1)] + cont, inp, gm, dir, f);
          var s2 := FS.ComputeTree(rer, [LS.Areg(r2)] + cont, inp, gm, dir, f);
          if s1.Some? { ComputePikeSubtreeLk(rer, [LS.Areg(r1)] + cont, inp, gm, dir, f, s1.value); }
          if s2.Some? { ComputePikeSubtreeLk(rer, [LS.Areg(r2)] + cont, inp, gm, dir, f, s2.value); }
        case Sequence(r1, r2) =>
          var na := LS.SeqList(r1, r2, dir) + cont;
          assert NoBackrefActions(na) by {
            match dir
            case Forward =>
          assert na == [LS.Areg(r1)] + ([LS.Areg(r2)] + cont);
          NoBackrefActionsCons(LS.Areg(r2), cont);
          NoBackrefActionsCons(LS.Areg(r1), [LS.Areg(r2)] + cont);
            case Backward =>
          assert na == [LS.Areg(r2)] + ([LS.Areg(r1)] + cont);
          NoBackrefActionsCons(LS.Areg(r1), cont);
          NoBackrefActionsCons(LS.Areg(r2), [LS.Areg(r1)] + cont);
          }
          var sub := FS.ComputeTree(rer, na, inp, gm, dir, f);
          if sub.Some? { ComputePikeSubtreeLk(rer, na, inp, gm, dir, f, sub.value); }
        case Quantified(greedy, min, delta, r1) =>
          var gidl := L.DefGroups(r1);
          if min > 0 {
            var quant := L.Quantified(greedy, min - 1, delta, r1);
            var na := [LS.Areg(r1), LS.Areg(quant)] + cont;
            var gm' := LG.GMReset(gidl, gm);
            assert NoBackrefActions(na) by {
              assert na == [LS.Areg(r1)] + ([LS.Areg(quant)] + cont);
              NoBackrefActionsCons(LS.Areg(quant), cont);
              NoBackrefActionsCons(LS.Areg(r1), [LS.Areg(quant)] + cont);
            }
            var sub := FS.ComputeTree(rer, na, inp, gm', dir, f);
            if sub.Some? { ComputePikeSubtreeLk(rer, na, inp, gm', dir, f, sub.value); }
          } else if delta == LN.NN(0) {
            var sub := FS.ComputeTree(rer, cont, inp, gm, dir, f);
            if sub.Some? { ComputePikeSubtreeLk(rer, cont, inp, gm, dir, f, sub.value); }
          } else {
            var quant := L.Quantified(greedy, 0, FS.NoiPred(delta), r1);
            var na := [LS.Areg(r1), LS.Acheck(inp), LS.Areg(quant)] + cont;
            var gm' := LG.GMReset(gidl, gm);
            assert NoBackrefActions(na) by {
              assert na == [LS.Areg(r1)] + ([LS.Acheck(inp)] + ([LS.Areg(quant)] + cont));
              NoBackrefActionsCons(LS.Areg(quant), cont);
              NoBackrefActionsCons(LS.Acheck(inp), [LS.Areg(quant)] + cont);
              NoBackrefActionsCons(LS.Areg(r1), [LS.Acheck(inp)] + ([LS.Areg(quant)] + cont));
            }
            var siter := FS.ComputeTree(rer, na, inp, gm', dir, f);
            var sskip := FS.ComputeTree(rer, cont, inp, gm, dir, f);
            if siter.Some? { ComputePikeSubtreeLk(rer, na, inp, gm', dir, f, siter.value); }
            if sskip.Some? { ComputePikeSubtreeLk(rer, cont, inp, gm, dir, f, sskip.value); }
          }
        case Group(gid, r1) =>
          var na := [LS.Areg(r1), LS.Aclose(gid)] + cont;
          var gm' := LG.GMOpen(LC.Idx(inp), gid, gm);
          assert NoBackrefActions(na) by {
            assert na == [LS.Areg(r1)] + ([LS.Aclose(gid)] + cont);
            NoBackrefActionsCons(LS.Aclose(gid), cont);
            NoBackrefActionsCons(LS.Areg(r1), [LS.Aclose(gid)] + cont);
          }
          var sub := FS.ComputeTree(rer, na, inp, gm', dir, f);
          if sub.Some? { ComputePikeSubtreeLk(rer, na, inp, gm', dir, f, sub.value); }
        case LookaroundR(lk, r1) =>
          // THE LK/LKFail case: the body treelk is NOT recursed into
          // (PikeSubtreeLk leaves it unconstrained); only the continuation.
          var slk := FS.ComputeTree(rer, [LS.Areg(r1)], inp, gm, L.LkDir(lk), f);
          match slk {
            case None =>
            case Some(treelk) =>
              match LS.LkResult(lk, treelk, gm, inp) {
                case Some(gmlk) =>
                  var sc := FS.ComputeTree(rer, cont, inp, gmlk, dir, f);
                  if sc.Some? { ComputePikeSubtreeLk(rer, cont, inp, gmlk, dir, f, sc.value); }
                case None =>   // t == LKFail(lk, treelk); PikeSubtreeLk trivially
              }
          }
        case AnchorR(a) =>
          if LS.AnchorSatisfied(rer, a, inp) {
            var sub := FS.ComputeTree(rer, cont, inp, gm, dir, f);
            if sub.Some? { ComputePikeSubtreeLk(rer, cont, inp, gm, dir, f, sub.value); }
          }
        case Backreference(gid) =>   // NoBackrefRegex(r) is false here — vacuous
    }
  }

  /** [SOLID] The spec tree builder only produces machine-B-explorable shapes
      (no `ReadBackRef` in the fragment; LK bodies are unconstrained). */
  lemma PikeSubtreeLkComputeTr(rer: LW.RegExpRecord, re: R.regex, str: string)
    requires T.TransWf(re) && NR.LookBehindFragmentRE(re)
    ensures PTL.PikeSubtreeLk(
              LFU.ComputeTr(rer, [LS.Areg(T.Translate(re))], LC.InitInput(str), LG.Empty, WP.Forward))
  {
    var act := [LS.Areg(T.Translate(re))];
    var inp := LC.InitInput(str);
    TranslateNoBackref(re);
    assert NoBackrefActions(act) by {
      assert act[0] == LS.Areg(T.Translate(re));
    }
    var fuel := FS.ActionsFuel(act, inp, WP.Forward) + 1;
    LFU.SubComputeTr(rer, act, inp, LG.Empty, WP.Forward, fuel);
    var t := LFU.ComputeTr(rer, act, inp, LG.Empty, WP.Forward);
    assert FS.ComputeTree(rer, act, inp, LG.Empty, WP.Forward, fuel) == Some(t);
    ComputePikeSubtreeLk(rer, act, inp, LG.Empty, WP.Forward, fuel, t);
  }

  // ==========================================================================
  // ---- (K) THE COMPOSITE SIM (thread-anchored — audit 2026-08-03) ------------
  //
  // ARCHITECTURE (settled by the #5 engine-connection audit): ride the PROVEN
  // machine-A simulation `PSM.PikeInvFullRE` for ALL VM mechanics (queue,
  // priority, seen, blocked, loop/BeginLoop via its `TreeRepRE` `tr_begin`), and
  // carry the LK-machine `ptsB` (`PTL.PikeTreeStepLk`, on the spec tree `t`)
  // ALONGSIDE — its trees paired to the VM THREADS via the standalone
  // `ThreadRepLk`/`ActiveRepLk`, NOT to the tstar trees.
  //
  // WHY THREAD-ANCHORED (not the dead §K tree↔tree route): `ActionsTreeRepFRE`
  // erases the LK head when building tstar, so `ta` (tstar) can NEVER recover
  // `tb` (LK) via `LeavesAgreeAtOutside` — that pairing is dead. BUT both
  // `PIV.ActiveRepRE(ta, vms.active)` (inside `PikeInvFullRE`) and
  // `ActiveRepLk(tb, vms.active)` are INDEX-WISE over the SAME `vms.active`, so
  // the VM thread is the shared anchor: carry PikeInvFullRE(ptsA,vms) AND
  // ThreadRepLk(tb,thread) as independent companions of one VM — no ta↔tb link.
  //
  // KEY STRUCTURAL FACTS:
  //  * `PikeInvFullRE(ptsA, vms)` relates the VM to `ptsA` (gate-transparent
  //    tstar), index-wise `vms.active[i]` ↔ `ptsA.active[i]` via `TreeRepRE`.
  //  * `PTL.PikeTreeStepLk` has the SAME case shape (skip/final/nextchar/active/
  //    match/blocked) as the tstar `PikeTreeStep` — so ptsA and ptsB step in
  //    LOCKSTEP with the same VM worklist. `LiftStepC` mirrors the PROVEN
  //    `PSM.InvariantPreservationRE` (ptsA side) with the per-instruction tb
  //    cores (ptsB side); `L3aCompositeClose` mirrors `PSM.FindMatchSimRE`.
  //  * `GateStepValue` (verified) preserves `GmtTieInside` across a passing gate
  //    (the crux; `ThreadRepLkStepCheckOracle` integrates it). Position tie is
  //    automatic — `ptsA.inp == ptsB.inp == InpOfCp(str, vms.cp)`.
  //  * Endpoint: `PTL.PikeTreeLkComputesFirstLeaf` ⟹ ptsB.best == FirstLeaf(t)
  //    (inside tie via `BestTieLk`); `PIV.BestMatchRE` gives the outside tie.

  // (K-pairing) DELETED `LiftPairC`/`ActivePairC` — the tstar-tree↔LK-tree
  // `LeavesAgreeAtOutside` pairing (the DEAD §K route: `ActionsTreeRepFRE` erases
  // the LK head, so `ta` can't recover `tb`). The composite now uses the THREAD-
  // anchored `ThreadRepLk`/`ActiveRepLk` directly (see `LiftInvC`): each ptsB tree
  // pairs with the VM thread, never with the tstar tree, so no ta↔tb link is
  // needed. Position tie stays automatic — `LiftInvC` pins `ptsA.inp == ptsB.inp
  // == InpOfCp(str, vms.cp)`, so the VM's `a_cp[l] := cp` at `CheckOracle(l)` IS
  // the gate's input position that `GateStepValue` consumes.

  // ---- (c′) the CANONICAL pairing layer (2026-08-07) -----------------------
  //
  // Machine B RUNS the PLANTED canonical tree `tcan` (built at entry by
  // `ActionsTreeRepLkRE`): unique per `(pc, ea)` by `TreeRepLkDetermRE` — the
  // skip-lockstep key — and stutter-discriminating, so `PikeTreeLk`'s
  // exact-tree memo works unchanged. The VALUE layer (all the proven
  // `ThreadRepLkStep*`/`WalkPairLkAt*` cores, on raw `BoolTreeLk` trees)
  // pairs the SAME thread through an ERASURE EXISTENTIAL: a raw witness
  // `traw` with `ProgErase(traw) == ProgErase(tcan)`. The planted guards are
  // leaf- and gm-transparent (`ProgEraseLeavesEq`; `Progress` is a pure
  // stutter in `TreeBfsStepLk`), so the raw walk's value conclusions
  // transport to `tcan` verbatim.
  //
  // WHY the existential (and NOT `WalkPairLk(tcan)` directly): `tcan` is NOT
  // `BoolTreeLk`-representable in general — `BoolTreeLk`'s forced-copy rule
  // (`Quantified min>0`) fixes the guardless continuation
  // `[Areg(r1), Areg(Quantified(min-1,..))]+cont`, so the planted
  // first-arrival `Progress` at a do-while's backward fork (e.g. in `a+`)
  // exists under NO action stack. Erasure is exactly the quotient on which
  // the two layers agree.

  /** Canonical per-thread pairing: the B-side tree `tcan` is the planted
      canonical tree at the thread's `(pc, exit_allowed)`, and the thread's
      value pairing rides a raw erasure-witness. */
  ghost predicate ThreadRepLkC(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code,
                               inp: LC.Input, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
                               S: set<LG.GroupId>, tcan: LT.Tree, gmt: LG.GroupMap, th: AI.Thread,
                               ncap: int, nlook: int, nquant: int) {
    th.pc >= 0
    && TreeRepLkRE(rer, qm, code, inp, tcan, th.pc as nat, th.exit_allowed)
    && exists traw: LT.Tree ::
      CE.ProgErase(traw) == CE.ProgErase(tcan)
      && ThreadRepLk(rer, qm, re, code, inp, crv, str, ov, S, traw, gmt, th, ncap, nlook, nquant)
  }

  /** (L4 NESTED) Canonical per-thread pairing riding the `*Nested` payload:
      identical to `ThreadRepLkC` but the erasure-witnessed raw pairing is
      `ThreadRepLkNested` (the `GmtTieInside`-free form). */
  ghost predicate ThreadRepLkCNested(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code,
                                     inp: LC.Input, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
                                     S: set<LG.GroupId>, tcan: LT.Tree, gmt: LG.GroupMap, th: AI.Thread,
                                     ncap: int, nlook: int, nquant: int) {
    th.pc >= 0
    && TreeRepLkRE(rer, qm, code, inp, tcan, th.pc as nat, th.exit_allowed)
    && exists traw: LT.Tree ::
      CE.ProgErase(traw) == CE.ProgErase(tcan)
      && ThreadRepLkNested(rer, qm, re, code, inp, crv, str, ov, S, traw, gmt, th, ncap, nlook, nquant)
  }

  /** Canonical active-list pairing (index-wise, priority positional) —
      `ActiveRepLk`'s shape with `ThreadRepLkC`. */
  ghost predicate ActiveRepLkC(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code,
                               inp: LC.Input, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
                               S: set<LG.GroupId>, tl: seq<(LT.Tree, LG.GroupMap)>, vl: seq<AI.Thread>,
                               ncap: int, nlook: int, nquant: int)
    decreases tl
  {
    (|tl| == 0 && |vl| == 0)
    || (|tl| > 0 && |vl| > 0
        && ThreadRepLkC(rer, qm, re, code, inp, crv, str, ov, S, tl[0].0, tl[0].1, vl[0],
                        ncap, nlook, nquant)
        && ActiveRepLkC(rer, qm, re, code, inp, crv, str, ov, S, tl[1..], vl[1..],
                        ncap, nlook, nquant))
  }

  /** (L4 NESTED) Canonical active-list pairing riding `ThreadRepLkCNested`
      (the `GmtTieInside`-free per-thread tie). */
  ghost predicate ActiveRepLkCNested(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code,
                                     inp: LC.Input, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
                                     S: set<LG.GroupId>, tl: seq<(LT.Tree, LG.GroupMap)>, vl: seq<AI.Thread>,
                                     ncap: int, nlook: int, nquant: int)
    decreases tl
  {
    (|tl| == 0 && |vl| == 0)
    || (|tl| > 0 && |vl| > 0
        && ThreadRepLkCNested(rer, qm, re, code, inp, crv, str, ov, S, tl[0].0, tl[0].1, vl[0],
                              ncap, nlook, nquant)
        && ActiveRepLkCNested(rer, qm, re, code, inp, crv, str, ov, S, tl[1..], vl[1..],
                              ncap, nlook, nquant))
  }

  /** Canonical blocked-list pairing — `BlockedRepLk`'s shape with the
      canonical tie at `(pc+1, CanExit)` over `nextinp` plus the erasure
      existential to a raw `TtLk` witness. */
  ghost predicate BlockedRepLkC(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code,
                                inp: LC.Input, nextinp: LC.Input, crv: CP.FCompiled, str: string,
                                ov: LOr.OracleView, S: set<LG.GroupId>,
                                tl: seq<(LT.Tree, LG.GroupMap)>, bl: seq<(AI.Thread, RC.char_expectation)>,
                                ncap: int, nlook: int, nquant: int)
    decreases tl
  {
    (|tl| == 0 && |bl| == 0)
    || (|tl| > 0 && |bl| > 0
        && bl[0].0.pc >= 0
        && TreeRepLkRE(rer, qm, code, nextinp, tl[0].0, (bl[0].0.pc + 1) as nat, true)
        && (exists traw: LT.Tree ::
              CE.ProgErase(traw) == CE.ProgErase(tl[0].0)
              && WalkPairLk(rer, qm, code, nextinp, traw, tl[0].1, (bl[0].0.pc + 1) as nat, true))
        && GmtTieOutside(re, bl[0].0, tl[0].1, S)
        && GmtTieInside(crv, str, ov, bl[0].0, tl[0].1, S, ncap, nlook, nquant)
        && BlockedRepLkC(rer, qm, re, code, inp, nextinp, crv, str, ov, S, tl[1..], bl[1..],
                         ncap, nlook, nquant))
  }

  /** (L4 NESTED) Canonical blocked-list pairing with the depth-1-hardwired
      `GmtTieInside` conjunct DROPPED (see `ThreadRepLkNested`). Canonical tie
      + raw-`WalkPairLk` erasure witness + outside value tie kept verbatim. */
  ghost predicate BlockedRepLkCNested(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code,
                                      inp: LC.Input, nextinp: LC.Input, crv: CP.FCompiled, str: string,
                                      ov: LOr.OracleView, S: set<LG.GroupId>,
                                      tl: seq<(LT.Tree, LG.GroupMap)>, bl: seq<(AI.Thread, RC.char_expectation)>,
                                      ncap: int, nlook: int, nquant: int)
    decreases tl
  {
    (|tl| == 0 && |bl| == 0)
    || (|tl| > 0 && |bl| > 0
        && bl[0].0.pc >= 0
        && TreeRepLkRE(rer, qm, code, nextinp, tl[0].0, (bl[0].0.pc + 1) as nat, true)
        && (exists traw: LT.Tree ::
              CE.ProgErase(traw) == CE.ProgErase(tl[0].0)
              && WalkPairLk(rer, qm, code, nextinp, traw, tl[0].1, (bl[0].0.pc + 1) as nat, true))
        && GmtTieOutside(re, bl[0].0, tl[0].1, S)
        && BlockedRepLkCNested(rer, qm, re, code, inp, nextinp, crv, str, ov, S, tl[1..], bl[1..],
                               ncap, nlook, nquant))
  }

  /** BLOCKED → ACTIVE at the consume: each stored pair reactivates into the
      resumed thread (`pc+1`, flag re-armed, registers unchanged) — the
      canonical tie and the strengthened `WalkPairLk` witness were stored at
      exactly that shape, and the value ties read only the registers. */
  lemma BlockedToActiveLkC(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code,
                           inp: LC.Input, nextinp: LC.Input, crv: CP.FCompiled, str: string,
                           ov: LOr.OracleView, S: set<LG.GroupId>,
                           tl: seq<(LT.Tree, LG.GroupMap)>, bl: seq<(AI.Thread, RC.char_expectation)>,
                           ncap: int, nlook: int, nquant: int)
    requires BlockedRepLkC(rer, qm, re, code, inp, nextinp, crv, str, ov, S, tl, bl, ncap, nlook, nquant)
    ensures ActiveRepLkC(rer, qm, re, code, nextinp, crv, str, ov, S, tl, PSM.ResumeAll(bl),
                         ncap, nlook, nquant)
    decreases tl
  {
    if |tl| == 0 {
      assert |bl| == 0;
    } else {
      assert |bl| > 0;
      var th := bl[0].0;
      var rth := th.(exit_allowed := true, pc := th.pc + 1);
      assert PSM.ResumeAll(bl) == [rth] + PSM.ResumeAll(bl[1..]);
      assert rth.pc >= 0 && (rth.pc as nat) == (th.pc + 1) as nat;
      assert TreeRepLkRE(rer, qm, code, nextinp, tl[0].0, rth.pc as nat, rth.exit_allowed);
      var traw: LT.Tree :| CE.ProgErase(traw) == CE.ProgErase(tl[0].0)
                           && WalkPairLk(rer, qm, code, nextinp, traw, tl[0].1, (th.pc + 1) as nat, true);
      assert rth.capture_regs == th.capture_regs && rth.look_regs == th.look_regs
             && rth.quant_regs == th.quant_regs;
      assert GmtTieOutside(re, rth, tl[0].1, S)
             && GmtTieInside(crv, str, ov, rth, tl[0].1, S, ncap, nlook, nquant);
      assert ThreadRepLk(rer, qm, re, code, nextinp, crv, str, ov, S, traw, tl[0].1, rth,
                         ncap, nlook, nquant);
      assert ThreadRepLkC(rer, qm, re, code, nextinp, crv, str, ov, S, tl[0].0, tl[0].1, rth,
                          ncap, nlook, nquant);
      BlockedToActiveLkC(rer, qm, re, code, inp, nextinp, crv, str, ov, S, tl[1..], bl[1..],
                         ncap, nlook, nquant);
      assert ([rth] + PSM.ResumeAll(bl[1..]))[0] == rth
             && ([rth] + PSM.ResumeAll(bl[1..]))[1..] == PSM.ResumeAll(bl[1..]);
    }
  }

  /** (L4 NESTED) clone of `BlockedToActiveLkC` — GmtTieInside dropped. */
  lemma BlockedToActiveLkCNested(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code,
                                 inp: LC.Input, nextinp: LC.Input, crv: CP.FCompiled, str: string,
                                 ov: LOr.OracleView, S: set<LG.GroupId>,
                                 tl: seq<(LT.Tree, LG.GroupMap)>, bl: seq<(AI.Thread, RC.char_expectation)>,
                                 ncap: int, nlook: int, nquant: int)
    requires BlockedRepLkCNested(rer, qm, re, code, inp, nextinp, crv, str, ov, S, tl, bl, ncap, nlook, nquant)
    ensures ActiveRepLkCNested(rer, qm, re, code, nextinp, crv, str, ov, S, tl, PSM.ResumeAll(bl),
                               ncap, nlook, nquant)
    decreases tl
  {
    if |tl| == 0 {
      assert |bl| == 0;
    } else {
      assert |bl| > 0;
      var th := bl[0].0;
      var rth := th.(exit_allowed := true, pc := th.pc + 1);
      assert PSM.ResumeAll(bl) == [rth] + PSM.ResumeAll(bl[1..]);
      assert rth.pc >= 0 && (rth.pc as nat) == (th.pc + 1) as nat;
      assert TreeRepLkRE(rer, qm, code, nextinp, tl[0].0, rth.pc as nat, rth.exit_allowed);
      var traw: LT.Tree :| CE.ProgErase(traw) == CE.ProgErase(tl[0].0)
                           && WalkPairLk(rer, qm, code, nextinp, traw, tl[0].1, (th.pc + 1) as nat, true);
      assert rth.capture_regs == th.capture_regs && rth.look_regs == th.look_regs
             && rth.quant_regs == th.quant_regs;
      assert GmtTieOutside(re, rth, tl[0].1, S)
        ;
      assert ThreadRepLkNested(rer, qm, re, code, nextinp, crv, str, ov, S, traw, tl[0].1, rth,
                               ncap, nlook, nquant);
      assert ThreadRepLkCNested(rer, qm, re, code, nextinp, crv, str, ov, S, tl[0].0, tl[0].1, rth,
                                ncap, nlook, nquant);
      BlockedToActiveLkCNested(rer, qm, re, code, inp, nextinp, crv, str, ov, S, tl[1..], bl[1..],
                               ncap, nlook, nquant);
      assert ([rth] + PSM.ResumeAll(bl[1..]))[0] == rth
             && ([rth] + PSM.ResumeAll(bl[1..]))[1..] == PSM.ResumeAll(bl[1..]);
    }
  }

  /** (BRICK D6 — THE VALUE THEOREM, forward chain DISCHARGED) `L3aEndpointAssembly
      Nested` with its inside-`S` FORWARD `TODO(C4)` premise (b) no longer assumed
      but PROVED, via the D6 wiring `ReconInnerForwardWired` (= D4
      `FLookLoopAncestorClockChain` feeds (i)/(ii) ∘ C4c `M.ReconInnerGmOfLiveClose`)
      applied per live inside-`S` group at its innermost owner. Consumes
      `BestTieLkNestedTop` (the sim's `L3aCompositeCloseRec` output) and threads the
      spec tree (`leaf == LT.FirstLeaf(t, inp)`), so it chains directly after the
      composite sim.

      RESIDUAL premises (the deferred ENGINE half, NOT value/spec algebra):
        - `AllBodyTopFeeds` on the reconstructed banks — the per-body ancestor-clock
          base evidence (its `re`-arm is discharged by `LocalTopFeedAtReFromFrames`
          modulo top-look-clock stability + the guard bridge; its body-arms need the
          per-body replay-tower reconcile);
        - `EndpointForwardFeeds` — per live inside-`S` `g`, the innermost owner and
          its fresh body match with the value-lift/quant-reconcile agreements (from
          `M.FLookLoopValueLiftFull` + `M.FLookLoopQuantCoversFromTables`) plus the
          leaf value tie `leaf.1[g] == NormRange(LiveRange(...))`;
        - the inside-`S` REVERSE (c) — still owed (needs the reverse-recon connective
          `(A)` of `GuardBridgeFromLookNestBackTTop`, which does not yet exist);
        - the recon_outer capture/quant frames + synthetic wf + `QuantRegsFinal`
          (mechanical, from the `*CoversFromTables` capstones).
      Everything from the canonical feeds to the endpoint conclusion is GREEN. */
  lemma L3aEndpointAssemblyNestedFull(
    ast: R.regex, re: R.regex, crv: CP.FCompiled, code: RB.code, endl: nat,
    str: string, ov: LOr.OracleView, S: set<LG.GroupId>,
    thread: AI.Thread, leaf: LT.Leaf, ncap: int, nlook: int, nquant: int,
    rer: LW.RegExpRecord, qm: AR.QMap, t: LT.Tree, inp: LC.Input)
    requires T.TransWf(re) && NR.NestedFragmentRE(re) && NR.NegLooksLookFreeRE(re)
    requires PIV.CapUnique(re) && PIV.QuantUnique(re) && LTB.LookUnique(re)
    requires S == PIV.CapIdsInLooks(re)
    requires R.max_lookaround(re) == R.max_lookaround(ast)
    requires M.OrderedGm(leaf.1)
    // the spec tree threaded: the sim's best is this leaf.
    requires LT.FirstLeaf(t, inp) == Some(leaf)
    // the nested best-match tie — the sim's `L3aCompositeCloseRec` output.
    requires BestTieLkNestedTop(rer, re, crv, str, ov, S, Some(leaf), Some(thread), ncap, nlook, nquant)
    // ---- the depth-general FLookLoop reconstruction + residual (engine half) ----
    requires var res := AI.FLookLoop(crv, str, 1, R.max_lookaround(ast),
                                     thread.capture_regs, thread.look_regs, thread.quant_regs, ov);
             // (a) recon_outer cap frame (M.FLookLoopFullCoversFromTables).
             (forall k: int :: k !in PIV.CaptureRegsSet(PIV.CapIdsInLooks(re)) ==>
                                 AI.get_idx(AReg.as_arrays(res.0).0, k) == AI.get_idx(AReg.as_arrays(thread.capture_regs).0, k)
                                 && AI.get_idx(AReg.as_arrays(res.0).1, k) == AI.get_idx(AReg.as_arrays(thread.capture_regs).1, k))
             // (a) quant frame outside looks (nested FLookLoopQuantFrame).
             && (forall q: nat :: q in PIV.QuantIdsOutsideLooks(re) ==>
                                    AI.get_idx(AReg.as_arrays(res.2).1, q as int) == AI.get_idx(AReg.as_arrays(thread.quant_regs).1, q as int))
             // (a) synthetic-res well-formedness (nested FLookLoopValueLiftFull).
             && CM.ThreadRegsWf(AI.Thread(thread.pc, res.0, res.1, res.2, thread.exit_allowed), ncap, nlook, nquant)
             && M.QuantRegsFinal(AI.Thread(thread.pc, res.0, res.1, res.2, thread.exit_allowed))
    // ---- ENGINE-HALF residuals feeding the FORWARD wiring ----
    requires var res := AI.FLookLoop(crv, str, 1, R.max_lookaround(ast),
                                     thread.capture_regs, thread.look_regs, thread.quant_regs, ov);
             AllBodyTopFeeds(re, res.0.a_clk, AReg.as_arrays(res.1).1, res.2.a_clk)
    requires var res := AI.FLookLoop(crv, str, 1, R.max_lookaround(ast),
                                     thread.capture_regs, thread.look_regs, thread.quant_regs, ov);
             // per live inside-S group: innermost owner + fresh body match + agreements + value tie
             forall g: LG.GroupId :: g in S && g in leaf.1 ==>
                                       exists owner: nat, rfcap: AReg.Regs, rflk: AReg.Regs, rfqt: AReg.Regs ::
                                         owner in LTB.LookIds(re)
                                         && NR.NestedFragmentRE(NI.LookBodyOfRE(re, owner)) && PIV.CapUnique(NI.LookBodyOfRE(re, owner))
                                         && g in PIV.CapIds(NI.LookBodyOfRE(re, owner))
                                         && g !in PIV.CapIdsInLooks(NI.LookBodyOfRE(re, owner))
                                         && AI.get_idx(res.0.a_clk, CP.start_reg(g)) >= 0
                                         && AI.get_idx(res.0.a_cp, CP.start_reg(g)) >= 0
                                         && (forall c: nat :: c in PIV.CapIds(NI.LookBodyOfRE(re, owner))
                                                              && AI.get_idx(rfcap.a_clk, CP.start_reg(c)) < 0
                                                              ==> AI.get_idx(rfcap.a_cp, CP.start_reg(c)) < 0)
                                         && g in PIV.GmOfLive(NI.LookBodyOfRE(re, owner), rfcap, rflk, rfqt)
                                         && (forall c: nat :: c in PIV.CapIds(NI.LookBodyOfRE(re, owner)) ==>
                                                                AI.get_idx(res.0.a_clk, CP.start_reg(c)) == AI.get_idx(rfcap.a_clk, CP.start_reg(c)))
                                         && (forall qd: nat :: qd in PIV.QuantIds(NI.LookBodyOfRE(re, owner)) ==>
                                                                 AI.get_idx(res.2.a_clk, qd as int) == AI.get_idx(rfqt.a_clk, qd as int))
                                         && leaf.1[g] == PIV.NormRange(PIV.LiveRange(res.0.a_cp, res.0.a_clk, g))
    // ---- inside-S REVERSE (c) — still owed (reverse-recon connective (A)) ----
    requires var res := AI.FLookLoop(crv, str, 1, R.max_lookaround(ast),
                                     thread.capture_regs, thread.look_regs, thread.quant_regs, ov);
             forall g: LG.GroupId :: g in S && g in PIV.GmOfLive(re, res.0, res.1, res.2) ==> g in leaf.1
    ensures var res := AI.FLookLoop(crv, str, 1, R.max_lookaround(ast),
                                    thread.capture_regs, thread.look_regs, thread.quant_regs, ov);
            leaf.1 == PIV.NormGm(PIV.GmOfLive(re, res.0, res.1, res.2))
            && CM.ThreadRegsWf(AI.Thread(thread.pc, res.0, res.1, res.2, thread.exit_allowed), ncap, nlook, nquant)
            && M.QuantRegsFinal(AI.Thread(thread.pc, res.0, res.1, res.2, thread.exit_allowed))
  {
    var res := AI.FLookLoop(crv, str, 1, R.max_lookaround(ast),
                            thread.capture_regs, thread.look_regs, thread.quant_regs, ov);
    var leafgm := leaf.1;
    var synthetic := AI.Thread(thread.pc, res.0, res.1, res.2, thread.exit_allowed);

    // ---- DISCHARGE the inside-S FORWARD (b) via the D6 wiring --------------
    assert forall g: LG.GroupId :: g in S && g in leafgm ==>
                                     g in PIV.GmOfLive(re, res.0, res.1, res.2)
                                     && leafgm[g] == PIV.NormRange(PIV.GmOfLive(re, res.0, res.1, res.2)[g])
    by {
      forall g: LG.GroupId | g in S && g in leafgm
        ensures g in PIV.GmOfLive(re, res.0, res.1, res.2)
                && leafgm[g] == PIV.NormRange(PIV.GmOfLive(re, res.0, res.1, res.2)[g])
      {
        var owner: nat, rfcap: AReg.Regs, rflk: AReg.Regs, rfqt: AReg.Regs :|
          owner in LTB.LookIds(re)
          && NR.NestedFragmentRE(NI.LookBodyOfRE(re, owner)) && PIV.CapUnique(NI.LookBodyOfRE(re, owner))
          && g in PIV.CapIds(NI.LookBodyOfRE(re, owner))
          && g !in PIV.CapIdsInLooks(NI.LookBodyOfRE(re, owner))
          && AI.get_idx(res.0.a_clk, CP.start_reg(g)) >= 0
          && AI.get_idx(res.0.a_cp, CP.start_reg(g)) >= 0
          && (forall c: nat :: c in PIV.CapIds(NI.LookBodyOfRE(re, owner))
                               && AI.get_idx(rfcap.a_clk, CP.start_reg(c)) < 0
                               ==> AI.get_idx(rfcap.a_cp, CP.start_reg(c)) < 0)
          && g in PIV.GmOfLive(NI.LookBodyOfRE(re, owner), rfcap, rflk, rfqt)
          && (forall c: nat :: c in PIV.CapIds(NI.LookBodyOfRE(re, owner)) ==>
                                 AI.get_idx(res.0.a_clk, CP.start_reg(c)) == AI.get_idx(rfcap.a_clk, CP.start_reg(c)))
          && (forall qd: nat :: qd in PIV.QuantIds(NI.LookBodyOfRE(re, owner)) ==>
                                  AI.get_idx(res.2.a_clk, qd as int) == AI.get_idx(rfqt.a_clk, qd as int))
          && leafgm[g] == PIV.NormRange(PIV.LiveRange(res.0.a_cp, res.0.a_clk, g));
        ReconInnerForwardWired(re, owner, res.0, res.1, res.2, rfcap, rflk, rfqt, g);
        // membership + LiveRange value in hand; value tie closes NormRange.
        assert PIV.GmOfLive(re, res.0, res.1, res.2)[g] == PIV.LiveRange(res.0.a_cp, res.0.a_clk, g);
      }
    }

    // ---- OUTSIDE S (derived green, verbatim from L3aEndpointAssemblyNested) -
    assert GmtTieOutside(re, thread, leafgm, S);            // from BestTieLkNestedTop
    var gmThread := PIV.GmOfLive(re, thread.capture_regs, thread.look_regs, thread.quant_regs);
    var gmBest := PIV.GmOfLive(re, thread.capture_regs, res.1, thread.quant_regs);
    PIV.GmOfLiveLookIndepNested(re, thread.capture_regs, thread.look_regs, res.1, thread.quant_regs);
    M.LkBodyGroupsEqCapIdsInLooks(re);
    assert forall g: nat :: g !in LL.LkBodyGroups(T.Translate(re)) ==>
                              (g in leafgm <==> g in gmBest) && (g in leafgm ==> leafgm[g] == gmBest[g])
    by {
      forall g: nat | g !in LL.LkBodyGroups(T.Translate(re))
        ensures (g in leafgm <==> g in gmBest) && (g in leafgm ==> leafgm[g] == gmBest[g])
      {
        assert g !in S;
        assert (g in leafgm <==> g in gmThread) && (g in leafgm ==> leafgm[g] == gmThread[g]);
        assert (g in gmThread <==> g in gmBest) && (g in gmThread ==> gmThread[g] == gmBest[g]);
      }
    }
    OutsideLookValueBridgeNested(re, thread.capture_regs, res.0, res.1, thread.quant_regs, res.2,
                                 gmBest, leafgm);
    assert forall g: LG.GroupId :: g !in S ==>
                                     (g in leafgm <==> g in PIV.GmOfLive(re, res.0, res.1, res.2))
                                     && (g in leafgm ==> leafgm[g] == PIV.GmOfLive(re, res.0, res.1, res.2)[g]);

    // ---- assemble (outside frame + derived (b) + kept (c)) -----------------
    assert synthetic.look_regs == res.1;
    L3aValueBridgeNested(re, synthetic, leafgm, res.0, res.2, S);
    assert leafgm == PIV.NormGm(PIV.GmOfLive(re, res.0, res.1, res.2));
  }

  /** (THE FINAL ENDPOINT — both inside-`S` directions supplied by the descent
      wrappers) `L3aEndpointAssemblyNestedFull` with the AllBodyTopFeeds/forward-
      existential/reverse residuals REPLACED by the two facts the completed
      machinery produces: (F) forward membership+VALUE (`ForwardMemberOne`,
      quantified) and (R) reverse membership (`ReverseCDeepFull`). Everything
      else — outside-`S`, frames, the NormGm assembly — is verbatim. */
  lemma L3aEndpointAssemblyNestedFull2(
    ast: R.regex, re: R.regex, crv: CP.FCompiled, code: RB.code, endl: nat,
    str: string, ov: LOr.OracleView, S: set<LG.GroupId>,
    thread: AI.Thread, leaf: LT.Leaf, ncap: int, nlook: int, nquant: int,
    rer: LW.RegExpRecord, qm: AR.QMap, t: LT.Tree, inp: LC.Input)
    requires T.TransWf(re) && NR.NestedFragmentRE(re) && NR.NegLooksLookFreeRE(re)
    requires PIV.CapUnique(re) && PIV.QuantUnique(re) && LTB.LookUnique(re)
    requires S == PIV.CapIdsInLooks(re)
    requires R.max_lookaround(re) == R.max_lookaround(ast)
    requires M.OrderedGm(leaf.1)
    requires LT.FirstLeaf(t, inp) == Some(leaf)
    requires BestTieLkNestedTop(rer, re, crv, str, ov, S, Some(leaf), Some(thread), ncap, nlook, nquant)
    // ---- the recon frames + wf (verbatim (a)) ----
    requires var res := AI.FLookLoop(crv, str, 1, R.max_lookaround(ast),
                                     thread.capture_regs, thread.look_regs, thread.quant_regs, ov);
             (forall k: int :: k !in PIV.CaptureRegsSet(PIV.CapIdsInLooks(re)) ==>
                                 AI.get_idx(AReg.as_arrays(res.0).0, k) == AI.get_idx(AReg.as_arrays(thread.capture_regs).0, k)
                                 && AI.get_idx(AReg.as_arrays(res.0).1, k) == AI.get_idx(AReg.as_arrays(thread.capture_regs).1, k))
             && (forall q: nat :: q in PIV.QuantIdsOutsideLooks(re) ==>
                                    AI.get_idx(AReg.as_arrays(res.2).1, q as int) == AI.get_idx(AReg.as_arrays(thread.quant_regs).1, q as int))
             && CM.ThreadRegsWf(AI.Thread(thread.pc, res.0, res.1, res.2, thread.exit_allowed), ncap, nlook, nquant)
             && M.QuantRegsFinal(AI.Thread(thread.pc, res.0, res.1, res.2, thread.exit_allowed))
    // ---- (F) FORWARD membership + VALUE (per leaf-present g, Norm-form) ----
    requires var res := AI.FLookLoop(crv, str, 1, R.max_lookaround(ast),
                                     thread.capture_regs, thread.look_regs, thread.quant_regs, ov);
             forall g: LG.GroupId :: g in S && g in leaf.1 ==>
                                       g in PIV.GmOfLive(re, res.0, res.1, res.2)
                                       && PIV.NormRange(leaf.1[g]) == PIV.NormRange(PIV.GmOfLive(re, res.0, res.1, res.2)[g])
    // ---- (R) REVERSE membership ----
    requires var res := AI.FLookLoop(crv, str, 1, R.max_lookaround(ast),
                                     thread.capture_regs, thread.look_regs, thread.quant_regs, ov);
             forall g: LG.GroupId :: g in S && g in PIV.GmOfLive(re, res.0, res.1, res.2) ==> g in leaf.1
    ensures var res := AI.FLookLoop(crv, str, 1, R.max_lookaround(ast),
                                    thread.capture_regs, thread.look_regs, thread.quant_regs, ov);
            leaf.1 == PIV.NormGm(PIV.GmOfLive(re, res.0, res.1, res.2))
            && CM.ThreadRegsWf(AI.Thread(thread.pc, res.0, res.1, res.2, thread.exit_allowed), ncap, nlook, nquant)
            && M.QuantRegsFinal(AI.Thread(thread.pc, res.0, res.1, res.2, thread.exit_allowed))
  {
    var res := AI.FLookLoop(crv, str, 1, R.max_lookaround(ast),
                            thread.capture_regs, thread.look_regs, thread.quant_regs, ov);
    var leafgm := leaf.1;
    var synthetic := AI.Thread(thread.pc, res.0, res.1, res.2, thread.exit_allowed);

    // ---- inside-S FORWARD (b): membership + value, NormRange collapses on the
    //      ORDERED leaf value ----
    assert forall g: LG.GroupId :: g in S && g in leafgm ==>
                                     g in PIV.GmOfLive(re, res.0, res.1, res.2)
                                     && leafgm[g] == PIV.NormRange(PIV.GmOfLive(re, res.0, res.1, res.2)[g])
    by {
      forall g: LG.GroupId | g in S && g in leafgm
        ensures g in PIV.GmOfLive(re, res.0, res.1, res.2)
                && leafgm[g] == PIV.NormRange(PIV.GmOfLive(re, res.0, res.1, res.2)[g])
      {
        assert g in PIV.GmOfLive(re, res.0, res.1, res.2)
               && PIV.NormRange(leafgm[g]) == PIV.NormRange(PIV.GmOfLive(re, res.0, res.1, res.2)[g]);
        // OrderedGm: NormRange is the identity on leafgm[g]
        assert leafgm[g].endIdx.Some? ==> leafgm[g].startIdx <= leafgm[g].endIdx.value;
        assert PIV.NormRange(leafgm[g]) == leafgm[g];
      }
    }

    // ---- OUTSIDE S (verbatim from L3aEndpointAssemblyNestedFull) ----
    assert GmtTieOutside(re, thread, leafgm, S);            // from BestTieLkNestedTop
    var gmThread := PIV.GmOfLive(re, thread.capture_regs, thread.look_regs, thread.quant_regs);
    var gmBest := PIV.GmOfLive(re, thread.capture_regs, res.1, thread.quant_regs);
    PIV.GmOfLiveLookIndepNested(re, thread.capture_regs, thread.look_regs, res.1, thread.quant_regs);
    M.LkBodyGroupsEqCapIdsInLooks(re);
    assert forall g: nat :: g !in LL.LkBodyGroups(T.Translate(re)) ==>
                              (g in leafgm <==> g in gmBest) && (g in leafgm ==> leafgm[g] == gmBest[g])
    by {
      forall g: nat | g !in LL.LkBodyGroups(T.Translate(re))
        ensures (g in leafgm <==> g in gmBest) && (g in leafgm ==> leafgm[g] == gmBest[g])
      {
        assert g !in S;
        assert (g in leafgm <==> g in gmThread) && (g in leafgm ==> leafgm[g] == gmThread[g]);
        assert (g in gmThread <==> g in gmBest) && (g in gmThread ==> gmThread[g] == gmBest[g]);
      }
    }
    OutsideLookValueBridgeNested(re, thread.capture_regs, res.0, res.1, thread.quant_regs, res.2,
                                 gmBest, leafgm);
    assert forall g: LG.GroupId :: g !in S ==>
                                     (g in leafgm <==> g in PIV.GmOfLive(re, res.0, res.1, res.2))
                                     && (g in leafgm ==> leafgm[g] == PIV.GmOfLive(re, res.0, res.1, res.2)[g]);

    // ---- assemble ----
    assert synthetic.look_regs == res.1;
    L3aValueBridgeNested(re, synthetic, leafgm, res.0, res.2, S);
    assert leafgm == PIV.NormGm(PIV.GmOfLive(re, res.0, res.1, res.2));
  }

  lemma WalkPairLkAtJmpRec(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                           tb: LT.Tree, gmt: LG.GroupMap, pc: nat, ea: bool, x: int)
    requires WalkPairLkRec(rer, qm, code, inp, tb, gmt, pc, ea)
    requires NR.GetPcRE(code, pc) == Some(RB.Jmp(x))
    ensures x >= 0 && WalkPairLkRec(rer, qm, code, inp, tb, gmt, x as nat, ea)
  {
    var acts: LS.Actions, b: BS.LoopBool :|
      AR.ActionsRepL(rer, qm, acts, code, pc)
      && EL.PikeLkActionsRec(acts)
      && ATR.EaOf(b) == ea
      && EL.BoolTreeLk(rer, acts, inp, b, tb)
      && GateAheadClear(acts, gmt)
      && WalkDefsOk(acts);
    ActionsRepLThruJmp(rer, qm, acts, code, pc, x);
  }

  lemma WalkPairLkAtConsumeCoreRec(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                                   tb: LT.Tree, gm: LG.GroupMap, pc: nat, b: BS.LoopBool,
                                   acts: LS.Actions, ce: RC.char_expectation)
    requires AR.ActionsRepL(rer, qm, acts, code, pc)
    requires EL.PikeLkActionsRec(acts)
    requires EL.BoolTreeLk(rer, acts, inp, b, tb)
    requires NR.GetPcRE(code, pc) == Some(RB.Consume(ce))
    requires GateAheadClear(acts, gm)
    requires WalkDefsOk(acts)
    ensures tb.Read? || tb == LT.Mismatch
    ensures tb.Read? ==> exists nextinp ::
                AR.ReadCharE(ce, inp) == Some((tb.c, nextinp))
                && WalkPairLkRec(rer, qm, code, nextinp, tb.t, gm, pc + 1, true)
    ensures tb == LT.Mismatch ==> AR.ReadCharE(ce, inp) == None
    decreases ATR.MsizeA(acts)
  {
    var g := ATR.EaOf(b);
    var pcmid: nat :| AR.ActionRepL(rer, qm, acts[0], code, pc, pcmid) && AR.ActionsRepL(rer, qm, acts[1..], code, pcmid);
    EL.PikeLkActionsRecTail(acts);
    assert acts == [acts[0]] + acts[1..];
    EL.PikeLkActionsRecConsIff(acts[0], acts[1..]);
    var cont := acts[1..];
    match acts[0]
    case Acheck(_) =>   // pins EndLoop / backward Fork — not Consume
    case Aclose(_) =>   // pins SetRegisterToCP — not Consume
    case Areg(r0) =>
      assert EL.PikeLkRegexRec(r0);
      match r0
      case Epsilon =>
        assert pcmid == pc;
        assert EL.BoolTreeLk(rer, cont, inp, b, tb);
        assert ATR.MsizeA(cont) < ATR.MsizeA(acts);
        GateAheadClearTail(acts, gm);
        WalkDefsOkTail(acts);
        WalkPairLkAtConsumeCoreRec(rer, qm, code, inp, tb, gm, pc, b, cont, ce);
      case Sequence(r1, r2) =>
        assert acts[0] == LS.Areg(L.Sequence(r1, r2));
        assert AR.NfaRepL(rer, qm, L.Sequence(r1, r2), code, pc, pcmid);
        var e1: nat :| AR.NfaRepL(rer, qm, r1, code, pc, e1) && AR.NfaRepL(rer, qm, r2, code, e1, pcmid);
        var na := [LS.Areg(r1), LS.Areg(r2)] + cont;
        assert na == [LS.Areg(r1)] + ([LS.Areg(r2)] + cont);
        AR.ActionsRepLCons(rer, qm, LS.Areg(r2), cont, code, e1, pcmid);
        AR.ActionsRepLCons(rer, qm, LS.Areg(r1), [LS.Areg(r2)] + cont, code, pc, e1);
        assert AR.ActionsRepL(rer, qm, na, code, pc);
        assert EL.PikeLkActionsRec(na) by {
          EL.PikeLkActionsRecConsIff(LS.Areg(r2), cont);
          EL.PikeLkActionsRecConsIff(LS.Areg(r1), [LS.Areg(r2)] + cont);
        }
        assert EL.BoolTreeLk(rer, na, inp, b, tb);
        assert LS.ActionsRegexSize(acts) == RegSz(r1) + RegSz(r2) + 1 + LS.ActionsRegexSize(cont);
        assert LS.ActionsRegexSize(na) == RegSz(r1) + RegSz(r2) + LS.ActionsRegexSize(cont);
        assert ATR.MsizeA(na) < ATR.MsizeA(acts);
        GateAheadClearSeqExpand(acts, r1, r2, gm);
        WalkDefsOkSeqExpand(acts, r1, r2);
        WalkPairLkAtConsumeCoreRec(rer, qm, code, inp, tb, gm, pc, b, na, ce);
      case Quantified(greedy, min, delta, r1) =>
        if min == 0 && delta == LN.NN(0) {
          assert acts[0] == LS.Areg(L.Quantified(greedy, 0, LN.NN(0), r1));
          assert AR.NfaRepL(rer, qm, L.Quantified(greedy, 0, LN.NN(0), r1), code, pc, pcmid);
          var em: nat :| AR.NfaRepMinL(rer, qm, 0, r1, code, pc, em)
                         && AR.NfaRepOptL(rer, qm, 0, greedy, r1, code, em, pcmid);
          NfaRepMinLHeadPin(rer, qm, 0, r1, code, pc, em);
          NfaRepOptLHeadPin(rer, qm, 0, greedy, r1, code, em, pcmid);
          assert pcmid == pc;
          assert AR.ActionsRepL(rer, qm, cont, code, pc);
          assert EL.BoolTreeLk(rer, cont, inp, b, tb);
          assert ATR.MsizeA(cont) < ATR.MsizeA(acts);
          GateAheadClearTail(acts, gm);
          WalkDefsOkTail(acts);
          WalkPairLkAtConsumeCoreRec(rer, qm, code, inp, tb, gm, pc, b, cont, ce);
        } else {
          assert acts[0] == LS.Areg(L.Quantified(greedy, min, delta, r1));
          assert AR.NfaRepL(rer, qm, L.Quantified(greedy, min, delta, r1), code, pc, pcmid);
          QuantHeadPinsNonConsume(rer, qm, greedy, min, delta, r1, code, pc, pcmid, ce);
        }
      case Character(cd) =>
        assert acts[0] == LS.Areg(L.Character(cd));
        var ce2 :| NR.GetPcRE(code, pc) == Some(RB.Consume(ce2)) && AR.ExpectationMatches(rer, ce2, cd);
        assert ce2 == ce && pcmid == pc + 1;
        AR.ReadAgree(rer, ce, cd, inp);   // ReadCharE(ce, inp) == ReadChar(rer, cd, inp, Forward)
        match LC.ReadChar(rer, cd, inp, WP.Forward) {
          case None =>
            assert tb == LT.Mismatch;
          case Some(pair) =>
            assert tb.Read? && tb.c == pair.0 && EL.BoolTreeLk(rer, cont, pair.1, BS.CanExit, tb.t);
            assert AR.ActionsRepL(rer, qm, cont, code, pc + 1);
            GateAheadClearTail(acts, gm);
            WalkDefsOkTail(acts);
            assert WalkPairLkRec(rer, qm, code, pair.1, tb.t, gm, pc + 1, true) by {
              assert ATR.EaOf(BS.CanExit) == true;
              assert EL.PikeLkActionsRec(cont);
            }
            assert AR.ReadCharE(ce, inp) == Some((tb.c, pair.1));
        }
      case Disjunction(_, _) =>   // pins Fork — not Consume
      case Group(_, _) =>   // pins SetRegisterToCP — not Consume
      case LookaroundR(_, _) =>   // pins CheckOracle/NegCheckOracle — not Consume
      case AnchorR(_) =>   // pins AnchorAssertion — not Consume
      case Backreference(_) =>   // NfaRepL false
  }

  lemma WalkPairLkAtConsumeRec(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                               tb: LT.Tree, gm: LG.GroupMap, pc: nat, ea: bool, ce: RC.char_expectation)
    requires WalkPairLkRec(rer, qm, code, inp, tb, gm, pc, ea)
    requires NR.GetPcRE(code, pc) == Some(RB.Consume(ce))
    ensures tb.Read? || tb == LT.Mismatch
    ensures tb.Read? ==> exists nextinp ::
                AR.ReadCharE(ce, inp) == Some((tb.c, nextinp))
                && WalkPairLkRec(rer, qm, code, nextinp, tb.t, gm, pc + 1, true)
    ensures tb == LT.Mismatch ==> AR.ReadCharE(ce, inp) == None
  {
    var acts: LS.Actions, b: BS.LoopBool :|
      AR.ActionsRepL(rer, qm, acts, code, pc)
      && EL.PikeLkActionsRec(acts)
      && ATR.EaOf(b) == ea
      && EL.BoolTreeLk(rer, acts, inp, b, tb)
      && GateAheadClear(acts, gm)
      && WalkDefsOk(acts);
    WalkPairLkAtConsumeCoreRec(rer, qm, code, inp, tb, gm, pc, b, acts, ce);
  }

  lemma WalkPairLkAtNegCheckOracleCoreRec(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                                          tb: LT.Tree, gm: LG.GroupMap, pc: nat, b: BS.LoopBool,
                                          acts: LS.Actions, lid: int)
    requires AR.ActionsRepL(rer, qm, acts, code, pc)
    requires EL.PikeLkActionsRec(acts)
    requires EL.BoolTreeLk(rer, acts, inp, b, tb)
    requires NR.GetPcRE(code, pc) == Some(RB.NegCheckOracle(lid))
    requires GateAheadClear(acts, gm)
    requires WalkDefsOk(acts)
    ensures lid in qm.looks
    ensures var (lk, r1) := qm.looks[lid];
            var tlk := LFU.ComputeTr(rer, [LS.Areg(r1)], inp, LG.Empty, L.LkDir(lk));
            !AR.PositiveL(lk)
            && (LS.LkResult(lk, tlk, LG.Empty, inp).Some? ==>
                  tb.LK? && tb.lk == lk && tb.tlk == tlk
                  && WalkPairLkRec(rer, qm, code, inp, tb.t, gm, pc + 1, ATR.EaOf(b)))
            && (LS.LkResult(lk, tlk, LG.Empty, inp).None? ==> tb == LT.LKFail(lk, tlk))
    decreases ATR.MsizeA(acts)
  {
    var g := ATR.EaOf(b);
    var pcmid: nat :| AR.ActionRepL(rer, qm, acts[0], code, pc, pcmid) && AR.ActionsRepL(rer, qm, acts[1..], code, pcmid);
    EL.PikeLkActionsRecTail(acts);
    assert acts == [acts[0]] + acts[1..];
    EL.PikeLkActionsRecConsIff(acts[0], acts[1..]);
    var cont := acts[1..];
    match acts[0]
    case Acheck(_) =>   // pins EndLoop / backward Fork — not NegCheckOracle
    case Aclose(_) =>   // pins SetRegisterToCP — not NegCheckOracle
    case Areg(r0) =>
      assert EL.PikeLkRegexRec(r0);
      match r0
      case Epsilon =>
        assert pcmid == pc;
        assert EL.BoolTreeLk(rer, cont, inp, b, tb);
        assert ATR.MsizeA(cont) < ATR.MsizeA(acts);
        GateAheadClearTail(acts, gm);
        WalkDefsOkTail(acts);
        WalkPairLkAtNegCheckOracleCoreRec(rer, qm, code, inp, tb, gm, pc, b, cont, lid);
      case Sequence(r1, r2) =>
        assert acts[0] == LS.Areg(L.Sequence(r1, r2));
        assert AR.NfaRepL(rer, qm, L.Sequence(r1, r2), code, pc, pcmid);
        var e1: nat :| AR.NfaRepL(rer, qm, r1, code, pc, e1) && AR.NfaRepL(rer, qm, r2, code, e1, pcmid);
        var na := [LS.Areg(r1), LS.Areg(r2)] + cont;
        assert na == [LS.Areg(r1)] + ([LS.Areg(r2)] + cont);
        AR.ActionsRepLCons(rer, qm, LS.Areg(r2), cont, code, e1, pcmid);
        AR.ActionsRepLCons(rer, qm, LS.Areg(r1), [LS.Areg(r2)] + cont, code, pc, e1);
        assert AR.ActionsRepL(rer, qm, na, code, pc);
        assert EL.PikeLkActionsRec(na) by {
          EL.PikeLkActionsRecConsIff(LS.Areg(r2), cont);
          EL.PikeLkActionsRecConsIff(LS.Areg(r1), [LS.Areg(r2)] + cont);
        }
        assert EL.BoolTreeLk(rer, na, inp, b, tb);
        assert LS.ActionsRegexSize(acts) == RegSz(r1) + RegSz(r2) + 1 + LS.ActionsRegexSize(cont);
        assert LS.ActionsRegexSize(na) == RegSz(r1) + RegSz(r2) + LS.ActionsRegexSize(cont);
        assert ATR.MsizeA(na) < ATR.MsizeA(acts);
        GateAheadClearSeqExpand(acts, r1, r2, gm);
        M.AllDefsActsCons(acts[0], cont);
        M.AllDefsActsCons(LS.Areg(r1), [LS.Areg(r2)] + cont);
        M.AllDefsActsCons(LS.Areg(r2), cont);
        assert L.DefGroups(L.Sequence(r1, r2)) == L.DefGroups(r1) + L.DefGroups(r2);
        assert L.DefGroups(r1) + (L.DefGroups(r2) + M.AllDefsActs(cont))
            == (L.DefGroups(r1) + L.DefGroups(r2)) + M.AllDefsActs(cont);
        assert M.AllDefsActs(na) == M.AllDefsActs(acts);
        WalkDefsOkSeqExpand(acts, r1, r2);
        WalkPairLkAtNegCheckOracleCoreRec(rer, qm, code, inp, tb, gm, pc, b, na, lid);
      case Quantified(greedy, min, delta, r1) =>
        if min == 0 && delta == LN.NN(0) {
          assert acts[0] == LS.Areg(L.Quantified(greedy, 0, LN.NN(0), r1));
          assert AR.NfaRepL(rer, qm, L.Quantified(greedy, 0, LN.NN(0), r1), code, pc, pcmid);
          var em: nat :| AR.NfaRepMinL(rer, qm, 0, r1, code, pc, em)
                         && AR.NfaRepOptL(rer, qm, 0, greedy, r1, code, em, pcmid);
          NfaRepMinLHeadPin(rer, qm, 0, r1, code, pc, em);
          NfaRepOptLHeadPin(rer, qm, 0, greedy, r1, code, em, pcmid);
          assert pcmid == pc;
          assert AR.ActionsRepL(rer, qm, cont, code, pc);
          assert EL.BoolTreeLk(rer, cont, inp, b, tb);
          assert ATR.MsizeA(cont) < ATR.MsizeA(acts);
          GateAheadClearTail(acts, gm);
          WalkDefsOkTail(acts);
          WalkPairLkAtNegCheckOracleCoreRec(rer, qm, code, inp, tb, gm, pc, b, cont, lid);
        } else {
          assert acts[0] == LS.Areg(L.Quantified(greedy, min, delta, r1));
          assert AR.NfaRepL(rer, qm, L.Quantified(greedy, min, delta, r1), code, pc, pcmid);
          QuantHeadPinsForkOrSQC(rer, qm, greedy, min, delta, r1, code, pc, pcmid);
        }
      case LookaroundR(lk0, r1) =>
        // ActionRepL's polarity split: a NegCheckOracle pc hosts a NEGATIVE look
        var lid0: int :| NR.GetPcRE(code, pc) == Some(if AR.PositiveL(lk0) then RB.CheckOracle(lid0)
                                                      else RB.NegCheckOracle(lid0))
                         && lid0 in qm.looks && qm.looks[lid0] == (lk0, r1);
        assert !AR.PositiveL(lk0) && lid0 == lid;
        assert pcmid == pc + 1;
        M.GateNodeAtInp(rer, acts, inp, b, tb, lk0, r1);   // tb is LK/LKFail with LkGateOk
        var tlk := LFU.ComputeTr(rer, [LS.Areg(r1)], inp, LG.Empty, L.LkDir(lk0));
        if tb.LK? {
          assert tb.tlk == tlk && LS.LkResult(lk0, tlk, LG.Empty, inp).Some?;   // LkGateOk true
          assert EL.BoolTreeLk(rer, cont, inp, b, tb.t);
          assert AR.ActionsRepL(rer, qm, cont, code, pc + 1);
          // the passing negative merge is the identity ⟹ plain tail bricks
          GateAheadClearTail(acts, gm);
          WalkDefsOkTail(acts);
          assert EL.PikeLkActionsRec(cont);
          assert WalkPairLkRec(rer, qm, code, inp, tb.t, gm, pc + 1, g);
        } else {
          assert tb.LKFail? && tb.tlk == tlk;               // LkGateOk false
          assert LS.LkResult(lk0, tlk, LG.Empty, inp).None?;
          assert tb == LT.LKFail(lk0, tlk);
        }
      case Character(_) =>   // pins Consume — not NegCheckOracle
      case Disjunction(_, _) =>   // pins Fork — not NegCheckOracle
      case Group(_, _) =>   // pins SetRegisterToCP — not NegCheckOracle
      case AnchorR(_) =>   // pins AnchorAssertion — not NegCheckOracle
      case Backreference(_) =>   // NfaRepL false
  }

  lemma WalkPairLkAtNegCheckOracleRec(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                                      tb: LT.Tree, gm: LG.GroupMap, pc: nat, ea: bool, lid: int)
    requires WalkPairLkRec(rer, qm, code, inp, tb, gm, pc, ea)
    requires NR.GetPcRE(code, pc) == Some(RB.NegCheckOracle(lid))
    ensures lid in qm.looks
    ensures var (lk, r1) := qm.looks[lid];
            var tlk := LFU.ComputeTr(rer, [LS.Areg(r1)], inp, LG.Empty, L.LkDir(lk));
            !AR.PositiveL(lk)
            && (LS.LkResult(lk, tlk, LG.Empty, inp).Some? ==>
                  tb.LK? && tb.lk == lk && tb.tlk == tlk
                  && WalkPairLkRec(rer, qm, code, inp, tb.t, gm, pc + 1, ea))
            && (LS.LkResult(lk, tlk, LG.Empty, inp).None? ==> tb == LT.LKFail(lk, tlk))
  {
    var acts: LS.Actions, b: BS.LoopBool :|
      AR.ActionsRepL(rer, qm, acts, code, pc)
      && EL.PikeLkActionsRec(acts)
      && ATR.EaOf(b) == ea
      && EL.BoolTreeLk(rer, acts, inp, b, tb)
      && GateAheadClear(acts, gm)
      && WalkDefsOk(acts);
    WalkPairLkAtNegCheckOracleCoreRec(rer, qm, code, inp, tb, gm, pc, b, acts, lid);
  }

  lemma WalkPairLkAtEndLoopCoreRec(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                                   tb: LT.Tree, gm: LG.GroupMap, pc: nat, b: BS.LoopBool,
                                   acts: LS.Actions)
    requires AR.ActionsRepL(rer, qm, acts, code, pc)
    requires EL.PikeLkActionsRec(acts)
    requires EL.BoolTreeLk(rer, acts, inp, b, tb)
    requires NR.GetPcRE(code, pc) == Some(RB.EndLoop)
    requires GateAheadClear(acts, gm)
    requires WalkDefsOk(acts)
    ensures ATR.EaOf(b) ==> tb.Progress? && WalkPairLkRec(rer, qm, code, inp, tb.t, gm, pc + 1, true)
    ensures !ATR.EaOf(b) ==> tb == LT.Mismatch
    decreases ATR.MsizeA(acts)
  {
    var g := ATR.EaOf(b);
    assert !AR.BackForkAt(code, pc);   // GetPcRE(pc)==EndLoop, not Fork
    var pcmid: nat :| AR.ActionRepL(rer, qm, acts[0], code, pc, pcmid) && AR.ActionsRepL(rer, qm, acts[1..], code, pcmid);
    EL.PikeLkActionsRecTail(acts);
    assert acts == [acts[0]] + acts[1..];
    EL.PikeLkActionsRecConsIff(acts[0], acts[1..]);
    var cont := acts[1..];
    match acts[0]
    case Acheck(strcheck) =>
      // ActionRepL(Acheck): EndLoop disjunct (BackFork excluded) ⇒ pcmid == pc+1
      assert pcmid == pc + 1;
      if b == BS.CanExit {
        assert g == true;
        assert tb.Progress? && EL.BoolTreeLk(rer, cont, inp, BS.CanExit, tb.t);
        assert AR.ActionsRepL(rer, qm, cont, code, pc + 1);
        // gm UNCHANGED across the guard ⟹ tail bricks give the continuation clear.
        GateAheadClearTail(acts, gm);       // GateAheadClear(cont, gm)
        WalkDefsOkTail(acts);             // NoDupSeq(AllDefsActs(cont))
        assert EL.PikeLkActionsRec(cont);
        assert ATR.EaOf(BS.CanExit) == true;
        assert WalkPairLkRec(rer, qm, code, inp, tb.t, gm, pc + 1, true);
      } else {
        assert b == BS.CannotExit && g == false;
        assert tb == LT.Mismatch;
      }
    case Aclose(_) =>   // pins SetRegisterToCP — not EndLoop
    case Areg(r0) =>
      assert EL.PikeLkRegexRec(r0);
      match r0
      case Epsilon =>
        assert pcmid == pc;
        assert EL.BoolTreeLk(rer, cont, inp, b, tb);
        assert ATR.MsizeA(cont) < ATR.MsizeA(acts);
        GateAheadClearTail(acts, gm);
        WalkDefsOkTail(acts);
        WalkPairLkAtEndLoopCoreRec(rer, qm, code, inp, tb, gm, pc, b, cont);
      case Sequence(r1, r2) =>
        assert acts[0] == LS.Areg(L.Sequence(r1, r2));
        assert AR.NfaRepL(rer, qm, L.Sequence(r1, r2), code, pc, pcmid);
        var e1: nat :| AR.NfaRepL(rer, qm, r1, code, pc, e1) && AR.NfaRepL(rer, qm, r2, code, e1, pcmid);
        var na := [LS.Areg(r1), LS.Areg(r2)] + cont;
        assert na == [LS.Areg(r1)] + ([LS.Areg(r2)] + cont);
        AR.ActionsRepLCons(rer, qm, LS.Areg(r2), cont, code, e1, pcmid);
        AR.ActionsRepLCons(rer, qm, LS.Areg(r1), [LS.Areg(r2)] + cont, code, pc, e1);
        assert AR.ActionsRepL(rer, qm, na, code, pc);
        assert EL.PikeLkActionsRec(na) by {
          EL.PikeLkActionsRecConsIff(LS.Areg(r2), cont);
          EL.PikeLkActionsRecConsIff(LS.Areg(r1), [LS.Areg(r2)] + cont);
        }
        assert EL.BoolTreeLk(rer, na, inp, b, tb);
        assert LS.ActionsRegexSize(acts) == RegSz(r1) + RegSz(r2) + 1 + LS.ActionsRegexSize(cont);
        assert LS.ActionsRegexSize(na) == RegSz(r1) + RegSz(r2) + LS.ActionsRegexSize(cont);
        assert ATR.MsizeA(na) < ATR.MsizeA(acts);
        GateAheadClearSeqExpand(acts, r1, r2, gm);
        M.AllDefsActsCons(acts[0], cont);
        M.AllDefsActsCons(LS.Areg(r1), [LS.Areg(r2)] + cont);
        M.AllDefsActsCons(LS.Areg(r2), cont);
        assert L.DefGroups(L.Sequence(r1, r2)) == L.DefGroups(r1) + L.DefGroups(r2);
        assert L.DefGroups(r1) + (L.DefGroups(r2) + M.AllDefsActs(cont))
            == (L.DefGroups(r1) + L.DefGroups(r2)) + M.AllDefsActs(cont);
        assert M.AllDefsActs(na) == M.AllDefsActs(acts);
        WalkDefsOkSeqExpand(acts, r1, r2);
        WalkPairLkAtEndLoopCoreRec(rer, qm, code, inp, tb, gm, pc, b, na);
      case Quantified(greedy, min, delta, r1) =>
        if min == 0 && delta == LN.NN(0) {
          assert acts[0] == LS.Areg(L.Quantified(greedy, 0, LN.NN(0), r1));
          assert AR.NfaRepL(rer, qm, L.Quantified(greedy, 0, LN.NN(0), r1), code, pc, pcmid);
          var em: nat :| AR.NfaRepMinL(rer, qm, 0, r1, code, pc, em)
                         && AR.NfaRepOptL(rer, qm, 0, greedy, r1, code, em, pcmid);
          NfaRepMinLHeadPin(rer, qm, 0, r1, code, pc, em);
          NfaRepOptLHeadPin(rer, qm, 0, greedy, r1, code, em, pcmid);
          assert pcmid == pc;
          assert AR.ActionsRepL(rer, qm, cont, code, pc);
          assert EL.BoolTreeLk(rer, cont, inp, b, tb);
          assert ATR.MsizeA(cont) < ATR.MsizeA(acts);
          GateAheadClearTail(acts, gm);
          WalkDefsOkTail(acts);
          WalkPairLkAtEndLoopCoreRec(rer, qm, code, inp, tb, gm, pc, b, cont);
        } else {
          assert acts[0] == LS.Areg(L.Quantified(greedy, min, delta, r1));
          assert AR.NfaRepL(rer, qm, L.Quantified(greedy, min, delta, r1), code, pc, pcmid);
          QuantHeadPinsForkOrSQC(rer, qm, greedy, min, delta, r1, code, pc, pcmid);
        }
      case Character(_) =>   // pins Consume — not EndLoop
      case Disjunction(_, _) =>   // pins Fork — not EndLoop
      case Group(_, _) =>   // pins SetRegisterToCP — not EndLoop
      case LookaroundR(_, _) =>   // pins CheckOracle/NegCheckOracle — not EndLoop
      case AnchorR(_) =>   // pins AnchorAssertion — not EndLoop
      case Backreference(_) =>   // NfaRepL false
  }

  lemma WalkPairLkAtEndLoopRec(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                               tb: LT.Tree, gm: LG.GroupMap, pc: nat, ea: bool)
    requires WalkPairLkRec(rer, qm, code, inp, tb, gm, pc, ea)
    requires NR.GetPcRE(code, pc) == Some(RB.EndLoop)
    ensures ea ==> tb.Progress? && WalkPairLkRec(rer, qm, code, inp, tb.t, gm, pc + 1, true)
    ensures !ea ==> tb == LT.Mismatch
  {
    var acts: LS.Actions, b: BS.LoopBool :|
      AR.ActionsRepL(rer, qm, acts, code, pc)
      && EL.PikeLkActionsRec(acts)
      && ATR.EaOf(b) == ea
      && EL.BoolTreeLk(rer, acts, inp, b, tb)
      && GateAheadClear(acts, gm)
      && WalkDefsOk(acts);
    WalkPairLkAtEndLoopCoreRec(rer, qm, code, inp, tb, gm, pc, b, acts);
  }

  lemma WalkPairLkAtBeginLoopRec(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                                 tb: LT.Tree, gmt: LG.GroupMap, pc: nat, ea: bool)
    requires WalkPairLkRec(rer, qm, code, inp, tb, gmt, pc, ea)
    requires NR.GetPcRE(code, pc) == Some(RB.BeginLoop)
    ensures WalkPairLkRec(rer, qm, code, inp, tb, gmt, pc + 1, false)
  {
    forall acts: LS.Actions, b: BS.LoopBool
      ensures !(AR.ActionsRepL(rer, qm, acts, code, pc)
                && EL.PikeLkActionsRec(acts) && ATR.EaOf(b) == ea
                && EL.BoolTreeLk(rer, acts, inp, b, tb) && GateAheadClear(acts, gmt))
    {
      if AR.ActionsRepL(rer, qm, acts, code, pc) {
        TT.ActionsRepNotAtBeginLoop(rer, qm, acts, code, pc);   // ⇒ false
      }
    }
  }

  lemma WalkPairLkAtSetQuantCoreRec(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                                    tb: LT.Tree, gm: LG.GroupMap, pc: nat, b: BS.LoopBool,
                                    acts: LS.Actions, q: int)
    requires AR.ActionsRepL(rer, qm, acts, code, pc)
    requires EL.PikeLkActionsRec(acts)
    requires EL.BoolTreeLk(rer, acts, inp, b, tb)
    requires NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(q, false))
    requires GateAheadClear(acts, gm)
    requires WalkDefsOk(acts)
    ensures q in qm.quants
    ensures tb.GroupActionT? && tb.g == LG.Reset(qm.quants[q])
    ensures WalkPairLkRec(rer, qm, code, inp, tb.t,
                          LG.GMUpdate(tb.g, LC.Idx(inp), gm), pc + 1, ATR.EaOf(b))
    decreases ATR.MsizeA(acts)
  {
    var g := ATR.EaOf(b);
    var pcmid: nat :| AR.ActionRepL(rer, qm, acts[0], code, pc, pcmid) && AR.ActionsRepL(rer, qm, acts[1..], code, pcmid);
    EL.PikeLkActionsRecTail(acts);
    assert acts == [acts[0]] + acts[1..];
    EL.PikeLkActionsRecConsIff(acts[0], acts[1..]);
    var cont := acts[1..];
    match acts[0]
    case Acheck(_) =>   // pins EndLoop / backward Fork — not SetQuantToClock
    case Aclose(_) =>   // pins SetRegisterToCP — not SetQuantToClock
    case Areg(r0) =>
      assert EL.PikeLkRegexRec(r0);
      match r0
      case Epsilon =>
        assert pcmid == pc;
        assert EL.BoolTreeLk(rer, cont, inp, b, tb);
        assert ATR.MsizeA(cont) < ATR.MsizeA(acts);
        GateAheadClearTail(acts, gm);
        WalkDefsOkTail(acts);
        WalkPairLkAtSetQuantCoreRec(rer, qm, code, inp, tb, gm, pc, b, cont, q);
      case Sequence(r1, r2) =>
        assert acts[0] == LS.Areg(L.Sequence(r1, r2));
        assert AR.NfaRepL(rer, qm, L.Sequence(r1, r2), code, pc, pcmid);
        var e1: nat :| AR.NfaRepL(rer, qm, r1, code, pc, e1) && AR.NfaRepL(rer, qm, r2, code, e1, pcmid);
        var na := [LS.Areg(r1), LS.Areg(r2)] + cont;
        assert na == [LS.Areg(r1)] + ([LS.Areg(r2)] + cont);
        AR.ActionsRepLCons(rer, qm, LS.Areg(r2), cont, code, e1, pcmid);
        AR.ActionsRepLCons(rer, qm, LS.Areg(r1), [LS.Areg(r2)] + cont, code, pc, e1);
        assert AR.ActionsRepL(rer, qm, na, code, pc);
        assert EL.PikeLkActionsRec(na) by {
          EL.PikeLkActionsRecConsIff(LS.Areg(r2), cont);
          EL.PikeLkActionsRecConsIff(LS.Areg(r1), [LS.Areg(r2)] + cont);
        }
        assert EL.BoolTreeLk(rer, na, inp, b, tb);
        assert LS.ActionsRegexSize(acts) == RegSz(r1) + RegSz(r2) + 1 + LS.ActionsRegexSize(cont);
        assert LS.ActionsRegexSize(na) == RegSz(r1) + RegSz(r2) + LS.ActionsRegexSize(cont);
        assert ATR.MsizeA(na) < ATR.MsizeA(acts);
        GateAheadClearSeqExpand(acts, r1, r2, gm);
        WalkDefsOkSeqExpand(acts, r1, r2);
        WalkPairLkAtSetQuantCoreRec(rer, qm, code, inp, tb, gm, pc, b, na, q);
      case Quantified(greedy, min, delta, r1) =>
        assert acts[0] == LS.Areg(L.Quantified(greedy, min, delta, r1));
        assert AR.NfaRepL(rer, qm, L.Quantified(greedy, min, delta, r1), code, pc, pcmid);
        if min > 0 {
          // THE forced-copy real head.
          var quant1 := L.Quantified(greedy, min - 1, delta, r1);
          var contActs := [LS.Areg(r1), LS.Areg(quant1)] + cont;
          var gidl := L.DefGroups(r1);
          assert tb.GroupActionT? && tb.g == LG.Reset(gidl)
                 && EL.BoolTreeLk(rer, contActs, inp, b, tb.t);
          // the qm.quants binding of THIS instruction's qid
          QuantHeadSQCPin(rer, qm, greedy, min, delta, r1, code, pc, pcmid);
          var qid: int :| NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(qid, false))
                          && qid in qm.quants && qm.quants[qid] == L.DefGroups(r1);
          assert qid == q;
          assert q in qm.quants && qm.quants[q] == gidl;
          QuantForcedContRep(rer, qm, greedy, min, delta, r1, code, pc, pcmid, cont);   // ActionsRepL(contActs, pc+1)
          assert EL.PikeLkRegexRec(r1) && EL.PikeLkRegexRec(quant1);
          assert EL.PikeLkActionsRec(contActs) by {
            EL.PikeLkActionsRecConsIff(LS.Areg(quant1), cont);
            EL.PikeLkActionsRecConsIff(LS.Areg(r1), [LS.Areg(quant1)] + cont);
          }
          // gm moves by the Reset
          var gm2 := LG.GMUpdate(LG.Reset(gidl), LC.Idx(inp), gm);
          assert gm2 == LG.GMReset(gidl, gm);
          // GateAheadClear(contActs, gm2): fresh r1-pendings ⊆ the reset set;
          // cont's pendings carry (absent in gm, and Reset only removes keys)
          assert GateAheadClear(contActs, gm2) by {
            forall lk2: L.Lookaround, rr: L.Regex | GatePending(contActs, lk2, rr)
              ensures forall gg :: gg in L.DefGroups(rr) ==> gg !in gm2
            {
              var j :| 0 <= j < |contActs| && contActs[j].Areg? && RegexTopGate(contActs[j].r, lk2, rr);
              if j == 0 {
                assert contActs[0] == LS.Areg(r1) && RegexTopGate(r1, lk2, rr);
                RegexTopGateSubDefs(r1, lk2, rr);
                var SRR := set gx | gx in L.DefGroups(rr);
                var SR1 := set gx | gx in L.DefGroups(r1);
                assert SRR <= SR1;
                forall gg | gg in L.DefGroups(rr) ensures gg !in gm2 {
                  assert gg in SRR;
                  assert gg in SR1;
                  assert gg in L.DefGroups(r1);
                  assert gm2 == gm - (set gx | gx in gidl);
                  assert gg in (set gx | gx in gidl);
                }
              } else if j == 1 {
                assert !RegexTopGate(quant1, lk2, rr);   // Quantified: never pending
                assert false;
              } else {
                assert contActs[j] == cont[j - 2];
                assert GatePending(cont, lk2, rr) by {
                  assert cont[j - 2].Areg? && RegexTopGate(cont[j - 2].r, lk2, rr);
                }
                GatePendingTail(acts, lk2, rr);
                forall gg | gg in L.DefGroups(rr) ensures gg !in gm2 {
                  assert gg !in gm;   // GateAheadClear(acts, gm)
                }
              }
            }
          }
          // WalkDefsOk(contActs): the unfold brick (mid = [])
          WalkDefsOkUnfold(acts, r1, quant1, []);
          assert [LS.Areg(r1)] + [] + [LS.Areg(quant1)] + cont == contActs;
          // pack the existential at pc+1
          assert AR.ActionsRepL(rer, qm, contActs, code, pc + 1)
                 && EL.PikeLkActionsRec(contActs)
                 && ATR.EaOf(b) == g
                 && EL.BoolTreeLk(rer, contActs, inp, b, tb.t)
                 && GateAheadClear(contActs, gm2)
                 && WalkDefsOk(contActs);
          assert WalkPairLkRec(rer, qm, code, inp, tb.t, gm2, pc + 1, g);
        } else if delta == LN.NN(0) {
          var em: nat :| AR.NfaRepMinL(rer, qm, 0, r1, code, pc, em)
                         && AR.NfaRepOptL(rer, qm, 0, greedy, r1, code, em, pcmid);
          NfaRepMinLHeadPin(rer, qm, 0, r1, code, pc, em);
          NfaRepOptLHeadPin(rer, qm, 0, greedy, r1, code, em, pcmid);
          assert pcmid == pc;
          assert AR.ActionsRepL(rer, qm, cont, code, pc);
          assert EL.BoolTreeLk(rer, cont, inp, b, tb);
          assert ATR.MsizeA(cont) < ATR.MsizeA(acts);
          GateAheadClearTail(acts, gm);
          WalkDefsOkTail(acts);
          WalkPairLkAtSetQuantCoreRec(rer, qm, code, inp, tb, gm, pc, b, cont, q);
        } else {
          // min==0 with Inf or NN(kx>0): pins a Fork at pc, not SetQuantToClock.
          match delta
          case Inf =>
            if exists e1: nat ::
                NR.GetPcRE(code, pc) == Some(if greedy then RB.Fork(pc + 1, e1 + 2) else RB.Fork(e1 + 2, pc + 1))
                && (exists qid: int :: NR.GetPcRE(code, pc + 1) == Some(RB.SetQuantToClock(qid, false))
                                       && qid in qm.quants && qm.quants[qid] == L.DefGroups(r1))
                && NR.GetPcRE(code, pc + 2) == Some(RB.BeginLoop)
                && AR.NfaRepL(rer, qm, r1, code, pc + 3, e1)
                && NR.GetPcRE(code, e1) == Some(RB.EndLoop)
                && NR.GetPcRE(code, e1 + 1) == Some(RB.Jmp(pc))
                && pcmid == e1 + 2 {
              var e1: nat :| NR.GetPcRE(code, pc) == Some(if greedy then RB.Fork(pc + 1, e1 + 2) else RB.Fork(e1 + 2, pc + 1));
            } else {
              var em: nat :| NR.GetPcRE(code, pc) == Some(if greedy then RB.Fork(em, pc + 1) else RB.Fork(pc + 1, em));
            }
          case NN(kx) =>
            var em: nat :| AR.NfaRepMinL(rer, qm, 0, r1, code, pc, em)
                           && AR.NfaRepOptL(rer, qm, kx, greedy, r1, code, em, pcmid);
            NfaRepMinLHeadPin(rer, qm, 0, r1, code, pc, em);
            NfaRepOptLHeadPin(rer, qm, kx, greedy, r1, code, em, pcmid);   // kx>0 ⇒ Fork at pc
        }
      case Character(_) =>   // pins Consume — not SetQuantToClock
      case Disjunction(_, _) =>   // pins Fork — not SetQuantToClock
      case Group(_, _) =>   // pins SetRegisterToCP — not SetQuantToClock
      case LookaroundR(_, _) =>   // pins CheckOracle/NegCheckOracle — not SetQuantToClock
      case AnchorR(_) =>   // pins AnchorAssertion — not SetQuantToClock
      case Backreference(_) =>   // NfaRepL false
  }

  lemma WalkPairLkAtSetQuantRec(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                                tb: LT.Tree, gm: LG.GroupMap, pc: nat, ea: bool, q: int)
    requires WalkPairLkRec(rer, qm, code, inp, tb, gm, pc, ea)
    requires NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(q, false))
    ensures q in qm.quants
    ensures tb.GroupActionT? && tb.g == LG.Reset(qm.quants[q])
    ensures WalkPairLkRec(rer, qm, code, inp, tb.t,
                          LG.GMUpdate(tb.g, LC.Idx(inp), gm), pc + 1, ea)
  {
    if (exists acts: LS.Actions, b: BS.LoopBool ::
          AR.ActionsRepL(rer, qm, acts, code, pc)
          && EL.PikeLkActionsRec(acts)
          && ATR.EaOf(b) == ea
          && EL.BoolTreeLk(rer, acts, inp, b, tb)
          && GateAheadClear(acts, gm)
          && WalkDefsOk(acts)) {
      var acts: LS.Actions, b: BS.LoopBool :|
        AR.ActionsRepL(rer, qm, acts, code, pc)
        && EL.PikeLkActionsRec(acts)
        && ATR.EaOf(b) == ea
        && EL.BoolTreeLk(rer, acts, inp, b, tb)
        && GateAheadClear(acts, gm)
        && WalkDefsOk(acts);
      WalkPairLkAtSetQuantCoreRec(rer, qm, code, inp, tb, gm, pc, b, acts, q);
    } else {
      // the SQC see-through disjunct is the live one
      var q0: int :| NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(q0, false))
                     && q0 in qm.quants
                     && tb.GroupActionT? && tb.g == LG.Reset(qm.quants[q0])
                     && WalkPairLkRec(rer, qm, code, inp, tb.t, LG.GMUpdate(tb.g, LC.Idx(inp), gm), pc + 1, ea);
      assert q0 == q;
    }
  }

  lemma WalkPairLkAtForkCoreRec(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                                tb: LT.Tree, gm: LG.GroupMap, pc: nat, b: BS.LoopBool,
                                acts: LS.Actions, x: int, y: int)
    requires AR.ActionsRepL(rer, qm, acts, code, pc)
    requires EL.PikeLkActionsRec(acts)
    requires EL.BoolTreeLk(rer, acts, inp, b, tb)
    requires NR.GetPcRE(code, pc) == Some(RB.Fork(x, y))
    requires GateAheadClear(acts, gm)
    requires WalkDefsOk(acts)
    ensures x >= 0 && y >= 0
    // ERASURE-SHAPED (raw `Progress` guard wrappers can nest at a backfork):
    // dead, or the erased tree is a Choice whose arms have walking witnesses
    // at x/y — always at the OUTER flag (every Acheck peel preserves CanExit).
    ensures CE.ProgErase(tb) == LT.Mismatch
            || exists ta1: LT.Tree, ta2: LT.Tree ::
              CE.ProgErase(tb) == LT.Choice(CE.ProgErase(ta1), CE.ProgErase(ta2))
              && WalkPairLkRec(rer, qm, code, inp, ta1, gm, x as nat, ATR.EaOf(b))
              && WalkPairLkRec(rer, qm, code, inp, ta2, gm, y as nat, ATR.EaOf(b))
    decreases ATR.MsizeA(acts)
  {
    var g := ATR.EaOf(b);
    var pcmid: nat :| AR.ActionRepL(rer, qm, acts[0], code, pc, pcmid) && AR.ActionsRepL(rer, qm, acts[1..], code, pcmid);
    EL.PikeLkActionsRecTail(acts);
    assert acts == [acts[0]] + acts[1..];
    EL.PikeLkActionsRecConsIff(acts[0], acts[1..]);
    var cont := acts[1..];
    match acts[0]
    case Acheck(strcheck) =>
      // EndLoop != Fork ⟹ the BackForkAt disjunct: pcmid == pc.
      assert AR.BackForkAt(code, pc);
      assert x >= 0 && y >= 0;
      if b == BS.CanExit {
        assert tb.Progress? && EL.BoolTreeLk(rer, cont, inp, BS.CanExit, tb.t);
        assert AR.ActionsRepL(rer, qm, cont, code, pc);
        GateAheadClearTail(acts, gm);
        WalkDefsOkTail(acts);
        assert ATR.MsizeA(cont) < ATR.MsizeA(acts);
        WalkPairLkAtForkCoreRec(rer, qm, code, inp, tb.t, gm, pc, BS.CanExit, cont, x, y);
        // the erased result lifts through the Progress wrapper verbatim
        assert CE.ProgErase(tb) == CE.ProgErase(tb.t);
        assert ATR.EaOf(BS.CanExit) == ATR.EaOf(b);
      } else {
        assert tb == LT.Mismatch;
      }
    case Aclose(_) =>   // pins SetRegisterToCP — not Fork
    case Areg(r0) =>
      assert EL.PikeLkRegexRec(r0);
      match r0
      case Epsilon =>
        assert pcmid == pc;
        assert EL.BoolTreeLk(rer, cont, inp, b, tb);
        assert ATR.MsizeA(cont) < ATR.MsizeA(acts);
        GateAheadClearTail(acts, gm);
        WalkDefsOkTail(acts);
        WalkPairLkAtForkCoreRec(rer, qm, code, inp, tb, gm, pc, b, cont, x, y);
      case Sequence(r1, r2) =>
        assert acts[0] == LS.Areg(L.Sequence(r1, r2));
        assert AR.NfaRepL(rer, qm, L.Sequence(r1, r2), code, pc, pcmid);
        var e1: nat :| AR.NfaRepL(rer, qm, r1, code, pc, e1) && AR.NfaRepL(rer, qm, r2, code, e1, pcmid);
        var na := [LS.Areg(r1), LS.Areg(r2)] + cont;
        assert na == [LS.Areg(r1)] + ([LS.Areg(r2)] + cont);
        AR.ActionsRepLCons(rer, qm, LS.Areg(r2), cont, code, e1, pcmid);
        AR.ActionsRepLCons(rer, qm, LS.Areg(r1), [LS.Areg(r2)] + cont, code, pc, e1);
        assert AR.ActionsRepL(rer, qm, na, code, pc);
        assert EL.PikeLkActionsRec(na) by {
          EL.PikeLkActionsRecConsIff(LS.Areg(r2), cont);
          EL.PikeLkActionsRecConsIff(LS.Areg(r1), [LS.Areg(r2)] + cont);
        }
        assert EL.BoolTreeLk(rer, na, inp, b, tb);
        assert LS.ActionsRegexSize(acts) == RegSz(r1) + RegSz(r2) + 1 + LS.ActionsRegexSize(cont);
        assert LS.ActionsRegexSize(na) == RegSz(r1) + RegSz(r2) + LS.ActionsRegexSize(cont);
        assert ATR.MsizeA(na) < ATR.MsizeA(acts);
        GateAheadClearSeqExpand(acts, r1, r2, gm);
        WalkDefsOkSeqExpand(acts, r1, r2);
        WalkPairLkAtForkCoreRec(rer, qm, code, inp, tb, gm, pc, b, na, x, y);
      case Disjunction(r1, r2) =>
        var e1: nat :| NR.GetPcRE(code, pc) == Some(RB.Fork(pc + 1, e1 + 1))
                       && AR.NfaRepL(rer, qm, r1, code, pc + 1, e1)
                       && NR.GetPcRE(code, e1) == Some(RB.Jmp(pcmid))
                       && AR.NfaRepL(rer, qm, r2, code, e1 + 1, pcmid);
        assert x == pc + 1 && y == e1 + 1;
        assert tb.Choice?
               && EL.BoolTreeLk(rer, [LS.Areg(r1)] + cont, inp, b, tb.t1)
               && EL.BoolTreeLk(rer, [LS.Areg(r2)] + cont, inp, b, tb.t2);
        // arm reps: r1's tail rides the mid Jmp; r2's is direct
        assert AR.ActionsRepL(rer, qm, cont, code, e1);   // jump_bc via Jmp(pcmid)
        AR.ActionsRepLCons(rer, qm, LS.Areg(r1), cont, code, pc + 1, e1);
        AR.ActionsRepLCons(rer, qm, LS.Areg(r2), cont, code, e1 + 1, pcmid);
        assert EL.PikeLkActionsRec([LS.Areg(r1)] + cont) && EL.PikeLkActionsRec([LS.Areg(r2)] + cont) by {
          EL.PikeLkActionsRecConsIff(LS.Areg(r1), cont);
          EL.PikeLkActionsRecConsIff(LS.Areg(r2), cont);
        }
        GateAheadClearDisjArm(acts, r1, r2, r1, gm);
        GateAheadClearDisjArm(acts, r1, r2, r2, gm);
        WalkDefsOkDisjArm(acts, r1, r2, r1);
        WalkDefsOkDisjArm(acts, r1, r2, r2);
        assert WalkPairLkRec(rer, qm, code, inp, tb.t1, gm, x as nat, g)
               && WalkPairLkRec(rer, qm, code, inp, tb.t2, gm, y as nat, g);
        assert CE.ProgErase(tb) == LT.Choice(CE.ProgErase(tb.t1), CE.ProgErase(tb.t2));
        assert exists ta1: LT.Tree, ta2: LT.Tree ::
            CE.ProgErase(tb) == LT.Choice(CE.ProgErase(ta1), CE.ProgErase(ta2))
            && WalkPairLkRec(rer, qm, code, inp, ta1, gm, x as nat, ATR.EaOf(b))
            && WalkPairLkRec(rer, qm, code, inp, ta2, gm, y as nat, ATR.EaOf(b)) by {
          assert WalkPairLkRec(rer, qm, code, inp, tb.t1, gm, x as nat, ATR.EaOf(b));
          assert WalkPairLkRec(rer, qm, code, inp, tb.t2, gm, y as nat, ATR.EaOf(b));
        }
      case Quantified(greedy, min, delta, r1) =>
        assert acts[0] == LS.Areg(L.Quantified(greedy, min, delta, r1));
        assert AR.NfaRepL(rer, qm, L.Quantified(greedy, min, delta, r1), code, pc, pcmid);
        if min == 0 && delta == LN.NN(0) {
          var em: nat :| AR.NfaRepMinL(rer, qm, 0, r1, code, pc, em)
                         && AR.NfaRepOptL(rer, qm, 0, greedy, r1, code, em, pcmid);
          NfaRepMinLHeadPin(rer, qm, 0, r1, code, pc, em);
          NfaRepOptLHeadPin(rer, qm, 0, greedy, r1, code, em, pcmid);
          assert pcmid == pc;
          assert AR.ActionsRepL(rer, qm, cont, code, pc);
          assert EL.BoolTreeLk(rer, cont, inp, b, tb);
          assert ATR.MsizeA(cont) < ATR.MsizeA(acts);
          GateAheadClearTail(acts, gm);
          WalkDefsOkTail(acts);
          WalkPairLkAtForkCoreRec(rer, qm, code, inp, tb, gm, pc, b, cont, x, y);
        } else if min > 0 {
          QuantHeadPinsForkOrSQC(rer, qm, greedy, min, delta, r1, code, pc, pcmid);
          assert false;   // min>0 head pins SetQuantToClock, not Fork
        } else {
          // min == 0 with Inf or NN(kx>0): the star fork — tb is the Choice.
          var gidl := L.DefGroups(r1);
          var q' := L.Quantified(greedy, 0, FS.NoiPred(delta), r1);
          var itert := if greedy then tb.t1 else tb.t2;
          var skipt := if greedy then tb.t2 else tb.t1;
          assert tb.Choice?
                 && itert.GroupActionT? && itert.g == LG.Reset(gidl)
                 && EL.BoolTreeLk(rer, [LS.Areg(r1), LS.Acheck(inp), LS.Areg(q')] + cont,
                                  inp, BS.CannotExit, itert.t)
                 && EL.BoolTreeLk(rer, cont, inp, b, skipt);
          var armlist := [LS.Areg(r1), LS.Acheck(inp), LS.Areg(q')] + cont;
          assert EL.PikeLkActionsRec(armlist) by {
            assert EL.PikeLkRegexRec(r1) && EL.PikeLkRegexRec(q');
            EL.PikeLkActionsRecConsIff(LS.Areg(q'), cont);
            EL.PikeLkActionsRecConsIff(LS.Acheck(inp), [LS.Areg(q')] + cont);
            EL.PikeLkActionsRecConsIff(LS.Areg(r1), [LS.Acheck(inp)] + ([LS.Areg(q')] + cont));
            assert [LS.Areg(r1)] + ([LS.Acheck(inp)] + ([LS.Areg(q')] + cont)) == armlist;
          }
          StarArmInvariants(acts, r1, q', LS.Acheck(inp), gm, gidl);
          // skip arm invariants
          GateAheadClearTail(acts, gm);
          WalkDefsOkTail(acts);
          match delta
          case Inf =>
            assert q' == L.Quantified(greedy, 0, LN.Inf, r1);
            if exists e1: nat ::
                NR.GetPcRE(code, pc) == Some(if greedy then RB.Fork(pc + 1, e1 + 2) else RB.Fork(e1 + 2, pc + 1))
                && (exists qid: int :: NR.GetPcRE(code, pc + 1) == Some(RB.SetQuantToClock(qid, false))
                                       && qid in qm.quants && qm.quants[qid] == L.DefGroups(r1))
                && NR.GetPcRE(code, pc + 2) == Some(RB.BeginLoop)
                && AR.NfaRepL(rer, qm, r1, code, pc + 3, e1)
                && NR.GetPcRE(code, e1) == Some(RB.EndLoop)
                && NR.GetPcRE(code, e1 + 1) == Some(RB.Jmp(pc))
                && pcmid == e1 + 2 {
              // ---- the LOOP BLOCK: SQC at pc+1, BeginLoop at pc+2 ----------
              var e1: nat :|
                NR.GetPcRE(code, pc) == Some(if greedy then RB.Fork(pc + 1, e1 + 2) else RB.Fork(e1 + 2, pc + 1))
                && (exists qid: int :: NR.GetPcRE(code, pc + 1) == Some(RB.SetQuantToClock(qid, false))
                                       && qid in qm.quants && qm.quants[qid] == L.DefGroups(r1))
                && NR.GetPcRE(code, pc + 2) == Some(RB.BeginLoop)
                && AR.NfaRepL(rer, qm, r1, code, pc + 3, e1)
                && NR.GetPcRE(code, e1) == Some(RB.EndLoop)
                && NR.GetPcRE(code, e1 + 1) == Some(RB.Jmp(pc))
                && pcmid == e1 + 2;
              var qid: int :| NR.GetPcRE(code, pc + 1) == Some(RB.SetQuantToClock(qid, false))
                              && qid in qm.quants && qm.quants[qid] == L.DefGroups(r1);
              // armlist rep at pc+3: r1; Acheck at EndLoop; q'+cont via the back-jump
              assert AR.ActionsRepL(rer, qm, [LS.Areg(q')] + cont, code, pc) by {
                AR.ActionsRepLCons(rer, qm, LS.Areg(q'), cont, code, pc, pcmid);
              }
              assert AR.ActionsRepL(rer, qm, [LS.Areg(q')] + cont, code, e1 + 1);   // jump_bc
              assert AR.ActionRepL(rer, qm, LS.Acheck(inp), code, e1, e1 + 1);      // EndLoop
              AR.ActionsRepLCons(rer, qm, LS.Acheck(inp), [LS.Areg(q')] + cont, code, e1, e1 + 1);
              AR.ActionsRepLCons(rer, qm, LS.Areg(r1), [LS.Acheck(inp)] + ([LS.Areg(q')] + cont),
                                 code, pc + 3, e1);
              assert [LS.Areg(r1)] + ([LS.Acheck(inp)] + ([LS.Areg(q')] + cont)) == armlist;
              assert AR.ActionsRepL(rer, qm, armlist, code, pc + 3);
              StarIterArmWalkBLRec(rer, qm, code, inp, gm, pc + 1, g, qid, r1, itert.t, armlist);
              assert WalkPairLkRec(rer, qm, code, inp, itert, gm, pc + 1, g);
              // skip arm at pcmid == e1+2
              assert WalkPairLkRec(rer, qm, code, inp, skipt, gm, pcmid, g);
              if greedy {
                assert x == pc + 1 && y == e1 + 2;
              } else {
                assert x == e1 + 2 && y == pc + 1;
              }
              assert WalkPairLkRec(rer, qm, code, inp, tb.t1, gm, x as nat, g)
                     && WalkPairLkRec(rer, qm, code, inp, tb.t2, gm, y as nat, g);
              assert CE.ProgErase(tb) == LT.Choice(CE.ProgErase(tb.t1), CE.ProgErase(tb.t2));
              assert exists ta1: LT.Tree, ta2: LT.Tree ::
                  CE.ProgErase(tb) == LT.Choice(CE.ProgErase(ta1), CE.ProgErase(ta2))
                  && WalkPairLkRec(rer, qm, code, inp, ta1, gm, x as nat, ATR.EaOf(b))
                  && WalkPairLkRec(rer, qm, code, inp, ta2, gm, y as nat, ATR.EaOf(b)) by {
                assert WalkPairLkRec(rer, qm, code, inp, tb.t1, gm, x as nat, ATR.EaOf(b));
                assert WalkPairLkRec(rer, qm, code, inp, tb.t2, gm, y as nat, ATR.EaOf(b));
              }

            } else {
              // ---- the LOOP VIEW: SQC at em (backward), body directly after
              assert NUL.NonNullableL(r1);
              var em: nat :| NR.GetPcRE(code, pc) == Some(if greedy then RB.Fork(em, pc + 1) else RB.Fork(pc + 1, em))
                             && em <= pc
                             && (exists qid: int :: NR.GetPcRE(code, em) == Some(RB.SetQuantToClock(qid, false))
                                                    && qid in qm.quants && qm.quants[qid] == L.DefGroups(r1))
                             && AR.NfaRepL(rer, qm, r1, code, em + 1, pc)
                             && pcmid == pc + 1;
              var qid: int :| NR.GetPcRE(code, em) == Some(RB.SetQuantToClock(qid, false))
                              && qid in qm.quants && qm.quants[qid] == L.DefGroups(r1);
              // armlist rep at em+1: r1 to pc; Acheck dissolves at the back fork; q'+cont at pc
              assert AR.ActionsRepL(rer, qm, [LS.Areg(q')] + cont, code, pc) by {
                AR.ActionsRepLCons(rer, qm, LS.Areg(q'), cont, code, pc, pcmid);
              }
              assert AR.BackForkAt(code, pc);
              assert AR.ActionRepL(rer, qm, LS.Acheck(inp), code, pc, pc);
              AR.ActionsRepLCons(rer, qm, LS.Acheck(inp), [LS.Areg(q')] + cont, code, pc, pc);
              AR.ActionsRepLCons(rer, qm, LS.Areg(r1), [LS.Acheck(inp)] + ([LS.Areg(q')] + cont),
                                 code, em + 1, pc);
              assert [LS.Areg(r1)] + ([LS.Acheck(inp)] + ([LS.Areg(q')] + cont)) == armlist;
              assert AR.ActionsRepL(rer, qm, armlist, code, em + 1);
              assert armlist == [LS.Areg(r1)] + ([LS.Acheck(inp), LS.Areg(q')] + cont);
              StarIterArmWalkLVRec(rer, qm, code, inp, gm, em, g, qid, r1, itert.t,
                                   [LS.Acheck(inp), LS.Areg(q')] + cont);
              assert WalkPairLkRec(rer, qm, code, inp, itert, gm, em, g);
              assert WalkPairLkRec(rer, qm, code, inp, skipt, gm, pc + 1, g);
              if greedy {
                assert x == em && y == pc + 1;
              } else {
                assert x == pc + 1 && y == em;
              }
              assert WalkPairLkRec(rer, qm, code, inp, tb.t1, gm, x as nat, g)
                     && WalkPairLkRec(rer, qm, code, inp, tb.t2, gm, y as nat, g);
              assert CE.ProgErase(tb) == LT.Choice(CE.ProgErase(tb.t1), CE.ProgErase(tb.t2));
              assert exists ta1: LT.Tree, ta2: LT.Tree ::
                  CE.ProgErase(tb) == LT.Choice(CE.ProgErase(ta1), CE.ProgErase(ta2))
                  && WalkPairLkRec(rer, qm, code, inp, ta1, gm, x as nat, ATR.EaOf(b))
                  && WalkPairLkRec(rer, qm, code, inp, ta2, gm, y as nat, ATR.EaOf(b)) by {
                assert WalkPairLkRec(rer, qm, code, inp, tb.t1, gm, x as nat, ATR.EaOf(b));
                assert WalkPairLkRec(rer, qm, code, inp, tb.t2, gm, y as nat, ATR.EaOf(b));
              }

            }
          case NN(kx) =>
            assert kx > 0;
            assert q' == L.Quantified(greedy, 0, LN.NN(kx - 1), r1);
            var em0: nat :| AR.NfaRepMinL(rer, qm, 0, r1, code, pc, em0)
                            && AR.NfaRepOptL(rer, qm, kx, greedy, r1, code, em0, pcmid);
            NfaRepMinLHeadPin(rer, qm, 0, r1, code, pc, em0);
            assert em0 == pc;
            var e1x: nat :| NR.GetPcRE(code, pc) == Some(if greedy then RB.Fork(pc + 1, pcmid) else RB.Fork(pcmid, pc + 1))
                            && (exists qid: int :: NR.GetPcRE(code, pc + 1) == Some(RB.SetQuantToClock(qid, false))
                                                   && qid in qm.quants && qm.quants[qid] == L.DefGroups(r1))
                            && NR.GetPcRE(code, pc + 2) == Some(RB.BeginLoop)
                            && AR.NfaRepL(rer, qm, r1, code, pc + 3, e1x)
                            && NR.GetPcRE(code, e1x) == Some(RB.EndLoop)
                            && AR.NfaRepOptL(rer, qm, kx - 1, greedy, r1, code, e1x + 1, pcmid);
            var qid: int :| NR.GetPcRE(code, pc + 1) == Some(RB.SetQuantToClock(qid, false))
                            && qid in qm.quants && qm.quants[qid] == L.DefGroups(r1);
            // q' at e1x+1: zero forced copies + the kx-1 optional layers
            assert AR.NfaRepL(rer, qm, q', code, e1x + 1, pcmid) by {
              assert AR.NfaRepMinL(rer, qm, 0, r1, code, e1x + 1, e1x + 1);
            }
            AR.ActionsRepLCons(rer, qm, LS.Areg(q'), cont, code, e1x + 1, pcmid);
            assert AR.ActionRepL(rer, qm, LS.Acheck(inp), code, e1x, e1x + 1);   // EndLoop
            AR.ActionsRepLCons(rer, qm, LS.Acheck(inp), [LS.Areg(q')] + cont, code, e1x, e1x + 1);
            AR.ActionsRepLCons(rer, qm, LS.Areg(r1), [LS.Acheck(inp)] + ([LS.Areg(q')] + cont),
                               code, pc + 3, e1x);
            assert [LS.Areg(r1)] + ([LS.Acheck(inp)] + ([LS.Areg(q')] + cont)) == armlist;
            assert AR.ActionsRepL(rer, qm, armlist, code, pc + 3);
            StarIterArmWalkBLRec(rer, qm, code, inp, gm, pc + 1, g, qid, r1, itert.t, armlist);
            assert WalkPairLkRec(rer, qm, code, inp, itert, gm, pc + 1, g);
            assert WalkPairLkRec(rer, qm, code, inp, skipt, gm, pcmid, g);
            if greedy {
              assert x == pc + 1 && y == pcmid;
            } else {
              assert x == pcmid && y == pc + 1;
            }
            assert WalkPairLkRec(rer, qm, code, inp, tb.t1, gm, x as nat, g)
                   && WalkPairLkRec(rer, qm, code, inp, tb.t2, gm, y as nat, g);
            assert CE.ProgErase(tb) == LT.Choice(CE.ProgErase(tb.t1), CE.ProgErase(tb.t2));
            assert exists ta1: LT.Tree, ta2: LT.Tree ::
                CE.ProgErase(tb) == LT.Choice(CE.ProgErase(ta1), CE.ProgErase(ta2))
                && WalkPairLkRec(rer, qm, code, inp, ta1, gm, x as nat, ATR.EaOf(b))
                && WalkPairLkRec(rer, qm, code, inp, ta2, gm, y as nat, ATR.EaOf(b)) by {
              assert WalkPairLkRec(rer, qm, code, inp, tb.t1, gm, x as nat, ATR.EaOf(b));
              assert WalkPairLkRec(rer, qm, code, inp, tb.t2, gm, y as nat, ATR.EaOf(b));
            }

        }
      case Character(_) =>   // pins Consume — not Fork
      case Group(_, _) =>   // pins SetRegisterToCP — not Fork
      case LookaroundR(_, _) =>   // pins CheckOracle/NegCheckOracle — not Fork
      case AnchorR(_) =>   // pins AnchorAssertion — not Fork
      case Backreference(_) =>   // NfaRepL false
  }

  lemma WalkPairLkAtForkArmsRec(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                                tb: LT.Tree, gm: LG.GroupMap, pc: nat, ea: bool, x: int, y: int)
    requires WalkPairLkRec(rer, qm, code, inp, tb, gm, pc, ea)
    requires NR.GetPcRE(code, pc) == Some(RB.Fork(x, y))
    ensures x >= 0 && y >= 0
    ensures CE.ProgErase(tb) == LT.Mismatch
            || exists ta1: LT.Tree, ta2: LT.Tree ::
              CE.ProgErase(tb) == LT.Choice(CE.ProgErase(ta1), CE.ProgErase(ta2))
              && WalkPairLkRec(rer, qm, code, inp, ta1, gm, x as nat, ea)
              && WalkPairLkRec(rer, qm, code, inp, ta2, gm, y as nat, ea)
  {
    var acts: LS.Actions, b: BS.LoopBool :|
      AR.ActionsRepL(rer, qm, acts, code, pc)
      && EL.PikeLkActionsRec(acts)
      && ATR.EaOf(b) == ea
      && EL.BoolTreeLk(rer, acts, inp, b, tb)
      && GateAheadClear(acts, gm)
      && WalkDefsOk(acts);
    WalkPairLkAtForkCoreRec(rer, qm, code, inp, tb, gm, pc, b, acts, x, y);
  }

  lemma WalkPairLkAtForkRec(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                            tb: LT.Tree, gm: LG.GroupMap, pc: nat, ea: bool, x: int, y: int)
    requires WalkPairLkRec(rer, qm, code, inp, tb, gm, pc, ea)
    requires NR.GetPcRE(code, pc) == Some(RB.Fork(x, y))
    ensures x >= 0 && y >= 0
    ensures tb.Choice? || tb.Progress? || tb == LT.Mismatch
  {
    WalkPairLkImpliesTtLkRec(rer, qm, code, inp, tb, gm, pc, ea);
    TtLkAtForkRec(rer, qm, code, inp, tb, pc, ea, x, y);
  }

  lemma WalkPairLkAtCheckOracleCoreRec(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                                       tb: LT.Tree, gm: LG.GroupMap, pc: nat, b: BS.LoopBool,
                                       acts: LS.Actions, lid: int)
    requires AR.ActionsRepL(rer, qm, acts, code, pc)
    requires EL.PikeLkActionsRec(acts)
    requires EL.BoolTreeLk(rer, acts, inp, b, tb)
    requires NR.GetPcRE(code, pc) == Some(RB.CheckOracle(lid))
    requires LL.OracleOkAt(rer, qm, inp)
    requires GateAheadClear(acts, gm)
    requires WalkDefsOk(acts)
    ensures lid in qm.looks
    ensures var (lk, r1) := qm.looks[lid];
            (LOr.view_get_oracle(qm.ov, TR_CpOf(inp), lid) ==>
               tb.LK? && tb.lk == lk
               && EL.LkGateOk(rer, lk, r1, inp, tb.tlk, true)
               && LS.LkResult(lk, tb.tlk, gm, inp).Some?
               && WalkPairLkRec(rer, qm, code, inp, tb.t, LS.LkResult(lk, tb.tlk, gm, inp).value,
                                pc + 1, ATR.EaOf(b)))
            && (!LOr.view_get_oracle(qm.ov, TR_CpOf(inp), lid) ==>
                  tb.LKFail? && tb.lk == lk
                  && EL.LkGateOk(rer, lk, r1, inp, tb.tlk, false))
    // the gate's OWN GateAheadClear instance: it is pending at the real head,
    // so its body groups are absent from the accumulated map (discharges
    // `ThreadRepLkStepCheckOracle`'s absence hypothesis)
    ensures forall gg :: gg in L.DefGroups(qm.looks[lid].1) ==> gg !in gm
    decreases ATR.MsizeA(acts)
  {
    var g := ATR.EaOf(b);
    var pcmid: nat :| AR.ActionRepL(rer, qm, acts[0], code, pc, pcmid) && AR.ActionsRepL(rer, qm, acts[1..], code, pcmid);
    EL.PikeLkActionsRecTail(acts);
    assert acts == [acts[0]] + acts[1..];
    EL.PikeLkActionsRecConsIff(acts[0], acts[1..]);
    var cont := acts[1..];
    match acts[0]
    case Acheck(_) =>   // pins EndLoop / backward Fork — not CheckOracle
    case Aclose(_) =>   // pins SetRegisterToCP — not CheckOracle
    case Areg(r0) =>
      assert EL.PikeLkRegexRec(r0);
      match r0
      case Epsilon =>
        assert pcmid == pc;
        assert EL.BoolTreeLk(rer, cont, inp, b, tb);
        assert ATR.MsizeA(cont) < ATR.MsizeA(acts);
        GateAheadClearTail(acts, gm);
        WalkDefsOkTail(acts);
        WalkPairLkAtCheckOracleCoreRec(rer, qm, code, inp, tb, gm, pc, b, cont, lid);
      case Sequence(r1, r2) =>
        assert acts[0] == LS.Areg(L.Sequence(r1, r2));
        assert AR.NfaRepL(rer, qm, L.Sequence(r1, r2), code, pc, pcmid);
        var e1: nat :| AR.NfaRepL(rer, qm, r1, code, pc, e1) && AR.NfaRepL(rer, qm, r2, code, e1, pcmid);
        var na := [LS.Areg(r1), LS.Areg(r2)] + cont;
        assert na == [LS.Areg(r1)] + ([LS.Areg(r2)] + cont);
        AR.ActionsRepLCons(rer, qm, LS.Areg(r2), cont, code, e1, pcmid);
        AR.ActionsRepLCons(rer, qm, LS.Areg(r1), [LS.Areg(r2)] + cont, code, pc, e1);
        assert AR.ActionsRepL(rer, qm, na, code, pc);
        assert EL.PikeLkActionsRec(na) by {
          EL.PikeLkActionsRecConsIff(LS.Areg(r2), cont);
          EL.PikeLkActionsRecConsIff(LS.Areg(r1), [LS.Areg(r2)] + cont);
        }
        assert EL.BoolTreeLk(rer, na, inp, b, tb);
        assert LS.ActionsRegexSize(acts) == RegSz(r1) + RegSz(r2) + 1 + LS.ActionsRegexSize(cont);
        assert LS.ActionsRegexSize(na) == RegSz(r1) + RegSz(r2) + LS.ActionsRegexSize(cont);
        assert ATR.MsizeA(na) < ATR.MsizeA(acts);
        GateAheadClearSeqExpand(acts, r1, r2, gm);
        // NoDupSeq(AllDefsActs(na)) == NoDupSeq(AllDefsActs(acts)) (same sequence).
        M.AllDefsActsCons(acts[0], cont);
        M.AllDefsActsCons(LS.Areg(r1), [LS.Areg(r2)] + cont);
        M.AllDefsActsCons(LS.Areg(r2), cont);
        assert L.DefGroups(L.Sequence(r1, r2)) == L.DefGroups(r1) + L.DefGroups(r2);
        assert L.DefGroups(r1) + (L.DefGroups(r2) + M.AllDefsActs(cont))
            == (L.DefGroups(r1) + L.DefGroups(r2)) + M.AllDefsActs(cont);
        assert M.AllDefsActs(na) == M.AllDefsActs(acts);
        WalkDefsOkSeqExpand(acts, r1, r2);
        WalkPairLkAtCheckOracleCoreRec(rer, qm, code, inp, tb, gm, pc, b, na, lid);
      case Quantified(greedy, min, delta, r1) =>
        if min == 0 && delta == LN.NN(0) {
          assert acts[0] == LS.Areg(L.Quantified(greedy, 0, LN.NN(0), r1));
          assert AR.NfaRepL(rer, qm, L.Quantified(greedy, 0, LN.NN(0), r1), code, pc, pcmid);
          var em: nat :| AR.NfaRepMinL(rer, qm, 0, r1, code, pc, em)
                         && AR.NfaRepOptL(rer, qm, 0, greedy, r1, code, em, pcmid);
          NfaRepMinLHeadPin(rer, qm, 0, r1, code, pc, em);
          NfaRepOptLHeadPin(rer, qm, 0, greedy, r1, code, em, pcmid);
          assert pcmid == pc;
          assert AR.ActionsRepL(rer, qm, cont, code, pc);
          assert EL.BoolTreeLk(rer, cont, inp, b, tb);
          assert ATR.MsizeA(cont) < ATR.MsizeA(acts);
          GateAheadClearTail(acts, gm);
          WalkDefsOkTail(acts);
          WalkPairLkAtCheckOracleCoreRec(rer, qm, code, inp, tb, gm, pc, b, cont, lid);
        } else {
          assert acts[0] == LS.Areg(L.Quantified(greedy, min, delta, r1));
          assert AR.NfaRepL(rer, qm, L.Quantified(greedy, min, delta, r1), code, pc, pcmid);
          QuantHeadPinsForkOrSQC(rer, qm, greedy, min, delta, r1, code, pc, pcmid);
        }
      case LookaroundR(lk0, r1) =>
        var lid0: int :| NR.GetPcRE(code, pc) == Some(if AR.PositiveL(lk0) then RB.CheckOracle(lid0)
                                                                           else RB.NegCheckOracle(lid0))
                         && lid0 in qm.looks && qm.looks[lid0] == (lk0, r1) && pcmid == pc + 1;
        assert AR.PositiveL(lk0) && lid0 == lid;
        assert L.Positivity(lk0);
        assert lid in qm.looks && qm.looks[lid] == (lk0, r1);
        // the gate is pending at index 0 ⟹ its body groups are clear NOW
        assert RegexTopGate(L.LookaroundR(lk0, r1), lk0, r1);
        assert GatePending(acts, lk0, r1) by {
          assert acts[0].Areg? && RegexTopGate(acts[0].r, lk0, r1);
        }
        assert forall gg :: gg in L.DefGroups(r1) ==> gg !in gm;
        M.GateNodeAtInp(rer, acts, inp, b, tb, lk0, r1);   // tb is LK/LKFail with LkGateOk
        var bit := LOr.view_get_oracle(qm.ov, TR_CpOf(inp), lid);
        if tb.LK? {
          assert EL.LkGateOk(rer, lk0, r1, inp, tb.tlk, true);
          assert EL.BoolTreeLk(rer, cont, inp, b, tb.t);
          assert AR.ActionsRepL(rer, qm, cont, code, pc + 1);
          assert bit;
          // ---- gate-frame facts for LkResultAgreeOutsideNested ----
          assert r0 == L.LookaroundR(lk0, r1);
          assert EL.PikeLkRegexRec(r1);                                     // NoLkBrL(r1)
          assert LS.LkResult(lk0, tb.tlk, LG.Empty, inp).Some?;       // LkGateOk true
          EL.LkResultGmIndep(lk0, tb.tlk, gm, inp);
          assert LS.LkResult(lk0, tb.tlk, gm, inp).Some?;
          var gm2 := LS.LkResult(lk0, tb.tlk, gm, inp).value;
          assert tb.tlk == LFU.ComputeTr(rer, [LS.Areg(r1)], inp, LG.Empty, L.LkDir(lk0));   // LkGateOk
          LkResultAgreeOutsideNested(rer, lk0, r1, inp, tb.tlk, gm);        // GmAgreeOutside(gm2, gm, Sr1)
          var Sr1 := set gx | gx in L.DefGroups(r1);
          // AfterMerge req (2): gm2 keys ⊆ gm ∪ DefGroups(r1).
          assert forall gg :: gg in gm2 ==> gg in gm || gg in L.DefGroups(r1) by {
            forall gg | gg in gm2 ensures gg in gm || gg in L.DefGroups(r1) {
              if gg !in Sr1 { assert gg in gm2 <==> gg in gm; assert gg in gm; }
              else { assert gg in L.DefGroups(r1); }
            }
          }
          // AfterMerge req (3): pending-in-cont ⟹ pending-in-acts.
          assert forall lk2: L.Lookaround, r2: L.Regex :: GatePending(cont, lk2, r2) ==> GatePending(acts, lk2, r2) by {
            forall lk2: L.Lookaround, r2: L.Regex | GatePending(cont, lk2, r2)
              ensures GatePending(acts, lk2, r2)
            { GatePendingTail(acts, lk2, r2); }
          }
          // AfterMerge req (4): every other pending gate's body disjoint from
          // DefGroups(r1) — from C1 (TopLk NoDup): the head gate contributes
          // DefGroups(r1) as a block, pending bodies in cont sit inside
          // TopLkDefsListActs(cont) (RegexTopGateSubTopLk).
          TopLkDefsListActsCons(acts[0], cont);
          assert TopLkDefsList(L.LookaroundR(lk0, r1)) == L.DefGroups(r1);
          assert TopLkDefsListActs(acts) == L.DefGroups(r1) + TopLkDefsListActs(cont);
          M.NoDupConcat(L.DefGroups(r1), TopLkDefsListActs(cont));
          assert forall lk2: L.Lookaround, r2: L.Regex :: GatePending(cont, lk2, r2) ==>
                                                            (forall gg :: gg in L.DefGroups(r2) ==> gg !in L.DefGroups(r1)) by {
            forall lk2: L.Lookaround, r2: L.Regex | GatePending(cont, lk2, r2)
              ensures forall gg :: gg in L.DefGroups(r2) ==> gg !in L.DefGroups(r1)
            {
              var j :| 0 <= j < |cont| && cont[j].Areg? && RegexTopGate(cont[j].r, lk2, r2);
              RegexTopGateSubTopLk(cont[j].r, lk2, r2);     // set(DefGroups r2) ⊆ set(TopLk cont[j].r)
              TopLkDefsListMemberSub(cont, j);              // set(TopLk cont[j].r) ⊆ set(TopLkActs cont)
              var SR2 := set gx | gx in L.DefGroups(r2);
              var SCJ := set gx | gx in TopLkDefsList(cont[j].r);
              var SAC := set gx | gx in TopLkDefsListActs(cont);
              var SR1 := set gx | gx in L.DefGroups(r1);
              assert SR2 <= SCJ && SCJ <= SAC;              // the two lemma subsets (named-set form)
              assert SR1 * SAC == {};                       // NoDupConcat disjointness
              forall gg | gg in L.DefGroups(r2) ensures gg !in L.DefGroups(r1) {
                assert gg in SR2;
                assert gg in SAC;                           // via SR2 ⊆ SCJ ⊆ SAC
                if gg in L.DefGroups(r1) {                   // contradiction: SR1 ∩ SAC == {}
                  assert gg in SR1 && gg in SAC;
                  assert gg in SR1 * SAC;
                  assert false;
                }
              }
            }
          }
          GateAheadClearAfterMerge(acts, cont, gm, gm2, lk0, r1);   // GateAheadClear(cont, gm2)
          // Assemble WalkPairLkRec(tb.t, gm2, pc+1, g) via the existential disjunct.
          assert EL.PikeLkActionsRec(cont);
          WalkDefsOkTail(acts);
          assert AR.ActionsRepL(rer, qm, cont, code, pc + 1)
                 && EL.PikeLkActionsRec(cont)
                 && ATR.EaOf(b) == g
                 && EL.BoolTreeLk(rer, cont, inp, b, tb.t)
                 && GateAheadClear(cont, gm2)
                 && WalkDefsOk(cont);
          assert WalkPairLkRec(rer, qm, code, inp, tb.t, gm2, pc + 1, g);
        } else {
          assert tb.LKFail?;   // GateNodeAtInp: only LK or LKFail
          assert !bit;
        }
      case Character(_) =>   // pins Consume — not CheckOracle
      case Disjunction(_, _) =>   // pins Fork — not CheckOracle
      case Group(_, _) =>   // pins SetRegisterToCP — not CheckOracle
      case AnchorR(_) =>   // pins AnchorAssertion — not CheckOracle
      case Backreference(_) =>   // NfaRepL false
  }

  lemma WalkPairLkAtCheckOracleRec(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                                   tb: LT.Tree, gm: LG.GroupMap, pc: nat, ea: bool, lid: int)
    requires WalkPairLkRec(rer, qm, code, inp, tb, gm, pc, ea)
    requires NR.GetPcRE(code, pc) == Some(RB.CheckOracle(lid))
    requires LL.OracleOkAt(rer, qm, inp)
    ensures lid in qm.looks
    ensures var (lk, r1) := qm.looks[lid];
            (LOr.view_get_oracle(qm.ov, TR_CpOf(inp), lid) ==>
               tb.LK? && tb.lk == lk
               && EL.LkGateOk(rer, lk, r1, inp, tb.tlk, true)
               && LS.LkResult(lk, tb.tlk, gm, inp).Some?
               && WalkPairLkRec(rer, qm, code, inp, tb.t, LS.LkResult(lk, tb.tlk, gm, inp).value, pc + 1, ea))
            && (!LOr.view_get_oracle(qm.ov, TR_CpOf(inp), lid) ==>
                  tb.LKFail? && tb.lk == lk
                  && EL.LkGateOk(rer, lk, r1, inp, tb.tlk, false))
    ensures forall gg :: gg in L.DefGroups(qm.looks[lid].1) ==> gg !in gm
  {
    // GetPcRE==CheckOracle ≠ BeginLoop kills the stutter disjunct; extract the walk.
    var acts: LS.Actions, b: BS.LoopBool :|
      AR.ActionsRepL(rer, qm, acts, code, pc)
      && EL.PikeLkActionsRec(acts)
      && ATR.EaOf(b) == ea
      && EL.BoolTreeLk(rer, acts, inp, b, tb)
      && GateAheadClear(acts, gm)
      && WalkDefsOk(acts);
    WalkPairLkAtCheckOracleCoreRec(rer, qm, code, inp, tb, gm, pc, b, acts, lid);
  }

  lemma WalkPairLkAtAnchorCoreRec(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                                  tb: LT.Tree, gm: LG.GroupMap, pc: nat, b: BS.LoopBool,
                                  acts: LS.Actions, a: R.anchor)
    requires AR.ActionsRepL(rer, qm, acts, code, pc)
    requires EL.PikeLkActionsRec(acts)
    requires EL.BoolTreeLk(rer, acts, inp, b, tb)
    requires NR.GetPcRE(code, pc) == Some(RB.AnchorAssertion(a))
    requires GateAheadClear(acts, gm)
    requires WalkDefsOk(acts)
    ensures tb.AnchorPass? || tb == LT.Mismatch
    ensures tb.AnchorPass? ==> WalkPairLkRec(rer, qm, code, inp, tb.t, gm, pc + 1, ATR.EaOf(b))
    decreases ATR.MsizeA(acts)
  {
    var g := ATR.EaOf(b);
    var pcmid: nat :| AR.ActionRepL(rer, qm, acts[0], code, pc, pcmid) && AR.ActionsRepL(rer, qm, acts[1..], code, pcmid);
    EL.PikeLkActionsRecTail(acts);
    assert acts == [acts[0]] + acts[1..];
    EL.PikeLkActionsRecConsIff(acts[0], acts[1..]);
    var cont := acts[1..];
    match acts[0]
    case Acheck(_) =>   // pins EndLoop / backward Fork — not AnchorAssertion
    case Aclose(_) =>   // pins SetRegisterToCP — not AnchorAssertion
    case Areg(r0) =>
      assert EL.PikeLkRegexRec(r0);
      match r0
      case Epsilon =>
        assert pcmid == pc;
        assert EL.BoolTreeLk(rer, cont, inp, b, tb);
        assert ATR.MsizeA(cont) < ATR.MsizeA(acts);
        GateAheadClearTail(acts, gm);
        WalkDefsOkTail(acts);
        WalkPairLkAtAnchorCoreRec(rer, qm, code, inp, tb, gm, pc, b, cont, a);
      case Sequence(r1, r2) =>
        assert acts[0] == LS.Areg(L.Sequence(r1, r2));
        assert AR.NfaRepL(rer, qm, L.Sequence(r1, r2), code, pc, pcmid);
        var e1: nat :| AR.NfaRepL(rer, qm, r1, code, pc, e1) && AR.NfaRepL(rer, qm, r2, code, e1, pcmid);
        var na := [LS.Areg(r1), LS.Areg(r2)] + cont;
        assert na == [LS.Areg(r1)] + ([LS.Areg(r2)] + cont);
        AR.ActionsRepLCons(rer, qm, LS.Areg(r2), cont, code, e1, pcmid);
        AR.ActionsRepLCons(rer, qm, LS.Areg(r1), [LS.Areg(r2)] + cont, code, pc, e1);
        assert AR.ActionsRepL(rer, qm, na, code, pc);
        assert EL.PikeLkActionsRec(na) by {
          EL.PikeLkActionsRecConsIff(LS.Areg(r2), cont);
          EL.PikeLkActionsRecConsIff(LS.Areg(r1), [LS.Areg(r2)] + cont);
        }
        assert EL.BoolTreeLk(rer, na, inp, b, tb);
        assert LS.ActionsRegexSize(acts) == RegSz(r1) + RegSz(r2) + 1 + LS.ActionsRegexSize(cont);
        assert LS.ActionsRegexSize(na) == RegSz(r1) + RegSz(r2) + LS.ActionsRegexSize(cont);
        assert ATR.MsizeA(na) < ATR.MsizeA(acts);
        GateAheadClearSeqExpand(acts, r1, r2, gm);
        M.AllDefsActsCons(acts[0], cont);
        M.AllDefsActsCons(LS.Areg(r1), [LS.Areg(r2)] + cont);
        M.AllDefsActsCons(LS.Areg(r2), cont);
        assert L.DefGroups(L.Sequence(r1, r2)) == L.DefGroups(r1) + L.DefGroups(r2);
        assert L.DefGroups(r1) + (L.DefGroups(r2) + M.AllDefsActs(cont))
            == (L.DefGroups(r1) + L.DefGroups(r2)) + M.AllDefsActs(cont);
        assert M.AllDefsActs(na) == M.AllDefsActs(acts);
        WalkDefsOkSeqExpand(acts, r1, r2);
        WalkPairLkAtAnchorCoreRec(rer, qm, code, inp, tb, gm, pc, b, na, a);
      case Quantified(greedy, min, delta, r1) =>
        if min == 0 && delta == LN.NN(0) {
          assert acts[0] == LS.Areg(L.Quantified(greedy, 0, LN.NN(0), r1));
          assert AR.NfaRepL(rer, qm, L.Quantified(greedy, 0, LN.NN(0), r1), code, pc, pcmid);
          var em: nat :| AR.NfaRepMinL(rer, qm, 0, r1, code, pc, em)
                         && AR.NfaRepOptL(rer, qm, 0, greedy, r1, code, em, pcmid);
          NfaRepMinLHeadPin(rer, qm, 0, r1, code, pc, em);
          NfaRepOptLHeadPin(rer, qm, 0, greedy, r1, code, em, pcmid);
          assert pcmid == pc;
          assert AR.ActionsRepL(rer, qm, cont, code, pc);
          assert EL.BoolTreeLk(rer, cont, inp, b, tb);
          assert ATR.MsizeA(cont) < ATR.MsizeA(acts);
          GateAheadClearTail(acts, gm);
          WalkDefsOkTail(acts);
          WalkPairLkAtAnchorCoreRec(rer, qm, code, inp, tb, gm, pc, b, cont, a);
        } else {
          assert acts[0] == LS.Areg(L.Quantified(greedy, min, delta, r1));
          assert AR.NfaRepL(rer, qm, L.Quantified(greedy, min, delta, r1), code, pc, pcmid);
          QuantHeadPinsForkOrSQC(rer, qm, greedy, min, delta, r1, code, pc, pcmid);
        }
      case AnchorR(la) =>
        var a2: R.anchor :| NR.GetPcRE(code, pc) == Some(RB.AnchorAssertion(a2)) && T.TrAnchor(a2) == la;
        assert pcmid == pc + 1;
        if LS.AnchorSatisfied(rer, la, inp) {
          assert tb.AnchorPass? && EL.BoolTreeLk(rer, cont, inp, b, tb.t);
          assert AR.ActionsRepL(rer, qm, cont, code, pc + 1);
          // gm UNCHANGED across AnchorPass ⟹ tail bricks give the continuation clear.
          GateAheadClearTail(acts, gm);       // GateAheadClear(cont, gm)
          WalkDefsOkTail(acts);             // NoDupSeq(AllDefsActs(cont))
          assert EL.PikeLkActionsRec(cont);
          assert WalkPairLkRec(rer, qm, code, inp, tb.t, gm, pc + 1, g);
        } else {
          assert tb == LT.Mismatch;
        }
      case Character(_) =>   // pins Consume — not AnchorAssertion
      case Disjunction(_, _) =>   // pins Fork — not AnchorAssertion
      case Group(_, _) =>   // pins SetRegisterToCP — not AnchorAssertion
      case LookaroundR(_, _) =>   // pins CheckOracle/NegCheckOracle — not AnchorAssertion
      case Backreference(_) =>   // NfaRepL false
  }

  lemma WalkPairLkAtAnchorRec(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                              tb: LT.Tree, gm: LG.GroupMap, pc: nat, ea: bool, a: R.anchor)
    requires WalkPairLkRec(rer, qm, code, inp, tb, gm, pc, ea)
    requires NR.GetPcRE(code, pc) == Some(RB.AnchorAssertion(a))
    ensures tb.AnchorPass? || tb == LT.Mismatch
    ensures tb.AnchorPass? ==> WalkPairLkRec(rer, qm, code, inp, tb.t, gm, pc + 1, ea)
  {
    var acts: LS.Actions, b: BS.LoopBool :|
      AR.ActionsRepL(rer, qm, acts, code, pc)
      && EL.PikeLkActionsRec(acts)
      && ATR.EaOf(b) == ea
      && EL.BoolTreeLk(rer, acts, inp, b, tb)
      && GateAheadClear(acts, gm)
      && WalkDefsOk(acts);
    WalkPairLkAtAnchorCoreRec(rer, qm, code, inp, tb, gm, pc, b, acts, a);
  }

  lemma WalkPairLkAtSetRegCoreRec(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                                  tb: LT.Tree, gm: LG.GroupMap, pc: nat, b: BS.LoopBool,
                                  acts: LS.Actions, r: int)
    requires AR.ActionsRepL(rer, qm, acts, code, pc)
    requires EL.PikeLkActionsRec(acts)
    requires EL.BoolTreeLk(rer, acts, inp, b, tb)
    requires NR.GetPcRE(code, pc) == Some(RB.SetRegisterToCP(r))
    requires GateAheadClear(acts, gm)
    requires WalkDefsOk(acts)
    ensures tb.GroupActionT?
    ensures (tb.g.Open? && r == CP.start_reg(tb.g.g as int))
            || (tb.g.Close? && r == CP.end_reg(tb.g.g as int))
    ensures WalkPairLkRec(rer, qm, code, inp, tb.t, LG.GMUpdate(tb.g, LC.Idx(inp), gm), pc + 1, ATR.EaOf(b))
    decreases ATR.MsizeA(acts)
  {
    var g := ATR.EaOf(b);
    var pcmid: nat :| AR.ActionRepL(rer, qm, acts[0], code, pc, pcmid) && AR.ActionsRepL(rer, qm, acts[1..], code, pcmid);
    EL.PikeLkActionsRecTail(acts);
    assert acts == [acts[0]] + acts[1..];
    EL.PikeLkActionsRecConsIff(acts[0], acts[1..]);
    var cont := acts[1..];
    match acts[0]
    case Acheck(_) =>   // pins EndLoop / backward Fork — not SetRegisterToCP
    case Aclose(gid) =>
      assert pcmid == pc + 1 && r == CP.end_reg(gid as int);
      assert tb.GroupActionT? && tb.g == LG.Close(gid) && EL.BoolTreeLk(rer, cont, inp, b, tb.t);
      assert AR.ActionsRepL(rer, qm, cont, code, pc + 1);
      var gm2 := LG.GMUpdate(LG.Close(gid), LC.Idx(inp), gm);
      assert gm2 == LG.GMClose(LC.Idx(inp), gid, gm);
      GateAheadClearTail(acts, gm);
      GateAheadClearMono(cont, gm, gm2);   // GMClose keeps the domain
      WalkDefsOkTail(acts);
      assert EL.PikeLkActionsRec(cont);
      assert WalkPairLkRec(rer, qm, code, inp, tb.t, gm2, pc + 1, g);
    case Areg(r0) =>
      assert EL.PikeLkRegexRec(r0);
      match r0
      case Epsilon =>
        assert pcmid == pc;
        assert EL.BoolTreeLk(rer, cont, inp, b, tb);
        assert ATR.MsizeA(cont) < ATR.MsizeA(acts);
        GateAheadClearTail(acts, gm);
        WalkDefsOkTail(acts);
        WalkPairLkAtSetRegCoreRec(rer, qm, code, inp, tb, gm, pc, b, cont, r);
      case Sequence(r1, r2) =>
        assert acts[0] == LS.Areg(L.Sequence(r1, r2));
        assert AR.NfaRepL(rer, qm, L.Sequence(r1, r2), code, pc, pcmid);
        var e1: nat :| AR.NfaRepL(rer, qm, r1, code, pc, e1) && AR.NfaRepL(rer, qm, r2, code, e1, pcmid);
        var na := [LS.Areg(r1), LS.Areg(r2)] + cont;
        assert na == [LS.Areg(r1)] + ([LS.Areg(r2)] + cont);
        AR.ActionsRepLCons(rer, qm, LS.Areg(r2), cont, code, e1, pcmid);
        AR.ActionsRepLCons(rer, qm, LS.Areg(r1), [LS.Areg(r2)] + cont, code, pc, e1);
        assert AR.ActionsRepL(rer, qm, na, code, pc);
        assert EL.PikeLkActionsRec(na) by {
          EL.PikeLkActionsRecConsIff(LS.Areg(r2), cont);
          EL.PikeLkActionsRecConsIff(LS.Areg(r1), [LS.Areg(r2)] + cont);
        }
        assert EL.BoolTreeLk(rer, na, inp, b, tb);
        assert LS.ActionsRegexSize(acts) == RegSz(r1) + RegSz(r2) + 1 + LS.ActionsRegexSize(cont);
        assert LS.ActionsRegexSize(na) == RegSz(r1) + RegSz(r2) + LS.ActionsRegexSize(cont);
        assert ATR.MsizeA(na) < ATR.MsizeA(acts);
        GateAheadClearSeqExpand(acts, r1, r2, gm);
        M.AllDefsActsCons(acts[0], cont);
        M.AllDefsActsCons(LS.Areg(r1), [LS.Areg(r2)] + cont);
        M.AllDefsActsCons(LS.Areg(r2), cont);
        assert L.DefGroups(L.Sequence(r1, r2)) == L.DefGroups(r1) + L.DefGroups(r2);
        assert L.DefGroups(r1) + (L.DefGroups(r2) + M.AllDefsActs(cont))
            == (L.DefGroups(r1) + L.DefGroups(r2)) + M.AllDefsActs(cont);
        assert M.AllDefsActs(na) == M.AllDefsActs(acts);
        WalkDefsOkSeqExpand(acts, r1, r2);
        WalkPairLkAtSetRegCoreRec(rer, qm, code, inp, tb, gm, pc, b, na, r);
      case Group(gid, r1) =>
        var e1: nat :| NR.GetPcRE(code, pc) == Some(RB.SetRegisterToCP(CP.start_reg(gid as int)))
                       && AR.NfaRepL(rer, qm, r1, code, pc + 1, e1)
                       && NR.GetPcRE(code, e1) == Some(RB.SetRegisterToCP(CP.end_reg(gid as int)))
                       && pcmid == e1 + 1;
        assert r == CP.start_reg(gid as int);
        var ga := [LS.Areg(r1), LS.Aclose(gid)] + cont;
        assert ga == [LS.Areg(r1)] + ([LS.Aclose(gid)] + cont);
        AR.ActionsRepLCons(rer, qm, LS.Aclose(gid), cont, code, e1, pcmid);
        AR.ActionsRepLCons(rer, qm, LS.Areg(r1), [LS.Aclose(gid)] + cont, code, pc + 1, e1);
        assert AR.ActionsRepL(rer, qm, ga, code, pc + 1);
        assert tb.GroupActionT? && tb.g == LG.Open(gid) && EL.BoolTreeLk(rer, ga, inp, b, tb.t);
        assert EL.PikeLkActionsRec(ga) by {
          EL.PikeLkActionsRecConsIff(LS.Aclose(gid), cont);
          EL.PikeLkActionsRecConsIff(LS.Areg(r1), [LS.Aclose(gid)] + cont);
        }
        var gm2 := LG.GMUpdate(LG.Open(gid), LC.Idx(inp), gm);
        // carrier across the Group expand; C1 pins gid ∉ TopLk of both parts
        WalkDefsOkGroupExpand(acts, gid, r1);
        TopLkDefsListActsCons(acts[0], cont);
        TopLkDefsListActsCons(LS.Areg(r1), [LS.Aclose(gid)] + cont);
        TopLkDefsListActsCons(LS.Aclose(gid), cont);
        assert TopLkDefsList(L.Group(gid, r1)) == [gid] + TopLkDefsList(r1);
        assert TopLkDefsListActs(acts)
            == ([gid] + TopLkDefsList(r1)) + TopLkDefsListActs(cont);
        assert ([gid] + TopLkDefsList(r1)) + TopLkDefsListActs(cont)
            == [gid] + (TopLkDefsList(r1) + TopLkDefsListActs(cont));
        M.NoDupConcat([gid], TopLkDefsList(r1) + TopLkDefsListActs(cont));
        assert TopLkDefsListActs(ga) == TopLkDefsList(r1) + TopLkDefsListActs(cont);
        // GateAheadClear(ga, gm): pending-in-ga ⟹ pending-in-acts.
        assert forall lk2: L.Lookaround, rr: L.Regex :: GatePending(ga, lk2, rr) ==> GatePending(acts, lk2, rr) by {
          forall lk2: L.Lookaround, rr: L.Regex | GatePending(ga, lk2, rr) ensures GatePending(acts, lk2, rr) {
            GatePendingGroupBack(acts, gid, r1, lk2, rr);
          }
        }
        assert GateAheadClear(ga, gm) by {
          forall lk2: L.Lookaround, rr: L.Regex | GatePending(ga, lk2, rr)
            ensures forall gg :: gg in L.DefGroups(rr) ==> gg !in gm
          { GatePendingGroupBack(acts, gid, r1, lk2, rr); }
        }
        // gid ∉ every pending body of ga (via C1: gid ∉ TopLkDefsListActs(ga) ⊇ DefGroups(rr)).
        assert forall lk2: L.Lookaround, rr: L.Regex :: GatePending(ga, lk2, rr) ==> gid !in L.DefGroups(rr) by {
          forall lk2: L.Lookaround, rr: L.Regex | GatePending(ga, lk2, rr) ensures gid !in L.DefGroups(rr) {
            var j :| 0 <= j < |ga| && ga[j].Areg? && RegexTopGate(ga[j].r, lk2, rr);
            RegexTopGateSubTopLk(ga[j].r, lk2, rr);
            TopLkDefsListMemberSub(ga, j);
            var SRR := set gx | gx in L.DefGroups(rr);
            var SGJ := set gx | gx in TopLkDefsList(ga[j].r);
            var SAG := set gx | gx in TopLkDefsListActs(ga);
            assert SRR <= SGJ && SGJ <= SAG;   // the two lemma subsets (named-set form)
            assert (set gx | gx in [gid]) * SAG == {};   // NoDupConcat disjointness
            if gid in L.DefGroups(rr) {
              assert gid in SRR && gid in SAG;           // via SRR ⊆ SGJ ⊆ SAG
              assert gid in (set gx | gx in [gid]);
              assert gid in (set gx | gx in [gid]) * SAG;   // contradicts disjoint
            }
          }
        }
        GateAheadClearAfterOpen(ga, gm, gid, LC.Idx(inp));   // GateAheadClear(ga, gm2)
        assert WalkPairLkRec(rer, qm, code, inp, tb.t, gm2, pc + 1, g);
      case Quantified(greedy, min, delta, r1) =>
        if min == 0 && delta == LN.NN(0) {
          assert acts[0] == LS.Areg(L.Quantified(greedy, 0, LN.NN(0), r1));
          assert AR.NfaRepL(rer, qm, L.Quantified(greedy, 0, LN.NN(0), r1), code, pc, pcmid);
          var em: nat :| AR.NfaRepMinL(rer, qm, 0, r1, code, pc, em)
                         && AR.NfaRepOptL(rer, qm, 0, greedy, r1, code, em, pcmid);
          NfaRepMinLHeadPin(rer, qm, 0, r1, code, pc, em);
          NfaRepOptLHeadPin(rer, qm, 0, greedy, r1, code, em, pcmid);
          assert pcmid == pc;
          assert AR.ActionsRepL(rer, qm, cont, code, pc);
          assert EL.BoolTreeLk(rer, cont, inp, b, tb);
          assert ATR.MsizeA(cont) < ATR.MsizeA(acts);
          GateAheadClearTail(acts, gm);
          WalkDefsOkTail(acts);
          WalkPairLkAtSetRegCoreRec(rer, qm, code, inp, tb, gm, pc, b, cont, r);
        } else {
          assert acts[0] == LS.Areg(L.Quantified(greedy, min, delta, r1));
          assert AR.NfaRepL(rer, qm, L.Quantified(greedy, min, delta, r1), code, pc, pcmid);
          QuantHeadPinsForkOrSQC(rer, qm, greedy, min, delta, r1, code, pc, pcmid);
        }
      case Character(_) =>   // pins Consume — not SetRegisterToCP
      case Disjunction(_, _) =>   // pins Fork — not SetRegisterToCP
      case LookaroundR(_, _) =>   // pins CheckOracle/NegCheckOracle — not SetRegisterToCP
      case AnchorR(_) =>   // pins AnchorAssertion — not SetRegisterToCP
      case Backreference(_) =>   // NfaRepL false
  }

  lemma WalkPairLkAtSetRegRec(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                              tb: LT.Tree, gm: LG.GroupMap, pc: nat, ea: bool, r: int)
    requires WalkPairLkRec(rer, qm, code, inp, tb, gm, pc, ea)
    requires NR.GetPcRE(code, pc) == Some(RB.SetRegisterToCP(r))
    ensures tb.GroupActionT?
    ensures (tb.g.Open? && r == CP.start_reg(tb.g.g as int))
            || (tb.g.Close? && r == CP.end_reg(tb.g.g as int))
    ensures WalkPairLkRec(rer, qm, code, inp, tb.t, LG.GMUpdate(tb.g, LC.Idx(inp), gm), pc + 1, ea)
  {
    var acts: LS.Actions, b: BS.LoopBool :|
      AR.ActionsRepL(rer, qm, acts, code, pc)
      && EL.PikeLkActionsRec(acts)
      && ATR.EaOf(b) == ea
      && EL.BoolTreeLk(rer, acts, inp, b, tb)
      && GateAheadClear(acts, gm)
      && WalkDefsOk(acts);
    WalkPairLkAtSetRegCoreRec(rer, qm, code, inp, tb, gm, pc, b, acts, r);
  }

  lemma WalkPairLkAtAcceptRec(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                              tb: LT.Tree, gm: LG.GroupMap, pc: nat, ea: bool)
    requires WalkPairLkRec(rer, qm, code, inp, tb, gm, pc, ea)
    requires NR.GetPcRE(code, pc) == Some(RB.Accept)
    ensures tb == LT.Match
  {
    WalkPairLkImpliesTtLkRec(rer, qm, code, inp, tb, gm, pc, ea);
    TtLkAtAcceptRec(rer, qm, code, inp, tb, pc, ea);
  }

  lemma WalkPairLkImpliesTtLkRec(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                                 tb: LT.Tree, gm: LG.GroupMap, pc: nat, ea: bool)
    requires WalkPairLkRec(rer, qm, code, inp, tb, gm, pc, ea)
    ensures TtLkRec(rer, qm, code, inp, tb, pc, ea)
    decreases RB.size(code) - pc
  {
    if (exists acts: LS.Actions, b: BS.LoopBool ::
          AR.ActionsRepL(rer, qm, acts, code, pc) && EL.PikeLkActionsRec(acts) && ATR.EaOf(b) == ea
          && EL.BoolTreeLk(rer, acts, inp, b, tb) && GateAheadClear(acts, gm)
          && WalkDefsOk(acts)) {
      // the existential disjunct: the same (acts, b) satisfy TtLkRec's exists.
      var acts: LS.Actions, b: BS.LoopBool :|
        AR.ActionsRepL(rer, qm, acts, code, pc) && EL.PikeLkActionsRec(acts) && ATR.EaOf(b) == ea
        && EL.BoolTreeLk(rer, acts, inp, b, tb) && GateAheadClear(acts, gm)
        && WalkDefsOk(acts);
    } else if pc < RB.size(code) && NR.GetPcRE(code, pc) == Some(RB.BeginLoop)
              && WalkPairLkRec(rer, qm, code, inp, tb, gm, pc + 1, false) {
      // the BeginLoop stutter disjunct; recurse at pc+1.
      WalkPairLkImpliesTtLkRec(rer, qm, code, inp, tb, gm, pc + 1, false);
    } else {
      // the SQC see-through disjunct: recurse on the child, re-pack TtLkRec's.
      var q: int :| NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(q, false))
                    && q in qm.quants
                    && tb.GroupActionT? && tb.g == LG.Reset(qm.quants[q])
                    && WalkPairLkRec(rer, qm, code, inp, tb.t, LG.GMUpdate(tb.g, LC.Idx(inp), gm), pc + 1, ea);
      WalkPairLkImpliesTtLkRec(rer, qm, code, inp, tb.t, LG.GMUpdate(tb.g, LC.Idx(inp), gm), pc + 1, ea);
      assert TtLkRec(rer, qm, code, inp, tb.t, pc + 1, ea);
    }
  }

  lemma ThreadRepLkStepBeginLoopRec(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code,
                                    inp: LC.Input, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
                                    S: set<LG.GroupId>, tb: LT.Tree, gmt: LG.GroupMap, th: AI.Thread,
                                    ncap: int, nlook: int, nquant: int)
    requires ThreadRepLkRec(rer, qm, re, code, inp, crv, str, ov, S, tb, gmt, th, ncap, nlook, nquant)
    requires NR.GetPcRE(code, th.pc as nat) == Some(RB.BeginLoop)
    ensures ThreadRepLkRec(rer, qm, re, code, inp, crv, str, ov, S, tb, gmt,
                           th.(exit_allowed := false, pc := th.pc + 1), ncap, nlook, nquant)
  {
    WalkPairLkAtBeginLoopRec(rer, qm, code, inp, tb, gmt, th.pc as nat, th.exit_allowed);
    // th.pc >= 0 (from ThreadRepLk) so (th.pc+1) as nat == (th.pc as nat) + 1.
    assert (th.pc + 1) as nat == (th.pc as nat) + 1;
    // GmtTieOutside/GmtTieInside read only capture/look/quant regs, unchanged by
    // the pc/exit_allowed update, so they transfer verbatim.
  }

  lemma StarIterArmWalkBLRec(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                             gm: LG.GroupMap, sqcpc: nat, ea: bool, qid: int,
                             r1: L.Regex, ti: LT.Tree, armlist: LS.Actions)
    requires NR.GetPcRE(code, sqcpc) == Some(RB.SetQuantToClock(qid, false))
    requires qid in qm.quants && qm.quants[qid] == L.DefGroups(r1)
    requires NR.GetPcRE(code, sqcpc + 1) == Some(RB.BeginLoop)
    requires AR.ActionsRepL(rer, qm, armlist, code, sqcpc + 2)
    requires EL.PikeLkActionsRec(armlist)
    requires EL.BoolTreeLk(rer, armlist, inp, BS.CannotExit, ti)
    requires GateAheadClear(armlist, LG.GMReset(L.DefGroups(r1), gm))
    requires WalkDefsOk(armlist)
    ensures WalkPairLkRec(rer, qm, code, inp, LT.GroupActionT(LG.Reset(L.DefGroups(r1)), ti),
                          gm, sqcpc, ea)
  {
    var gidl := L.DefGroups(r1);
    var gm2 := LG.GMUpdate(LG.Reset(gidl), LC.Idx(inp), gm);
    assert gm2 == LG.GMReset(gidl, gm);
    assert sqcpc + 1 < RB.size(code);
    assert ATR.EaOf(BS.CannotExit) == false;
    assert WalkPairLkRec(rer, qm, code, inp, ti, gm2, sqcpc + 2, false);
    assert WalkPairLkRec(rer, qm, code, inp, ti, gm2, sqcpc + 1, ea);   // BeginLoop absorbs any flag
    assert sqcpc < RB.size(code);
  }

  lemma StarIterArmWalkLVRec(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                             gm: LG.GroupMap, sqcpc: nat, ea: bool, qid: int,
                             r1: L.Regex, ti: LT.Tree, rest: LS.Actions)
    requires NR.GetPcRE(code, sqcpc) == Some(RB.SetQuantToClock(qid, false))
    requires qid in qm.quants && qm.quants[qid] == L.DefGroups(r1)
    requires NUL.NonNullableL(r1)
    requires AR.ActionsRepL(rer, qm, [LS.Areg(r1)] + rest, code, sqcpc + 1)
    requires EL.PikeLkActionsRec([LS.Areg(r1)] + rest)
    requires EL.BoolTreeLk(rer, [LS.Areg(r1)] + rest, inp, BS.CannotExit, ti)
    requires GateAheadClear([LS.Areg(r1)] + rest, LG.GMReset(L.DefGroups(r1), gm))
    requires WalkDefsOk([LS.Areg(r1)] + rest)
    ensures WalkPairLkRec(rer, qm, code, inp, LT.GroupActionT(LG.Reset(L.DefGroups(r1)), ti),
                          gm, sqcpc, ea)
  {
    var gidl := L.DefGroups(r1);
    var gm2 := LG.GMUpdate(LG.Reset(gidl), LC.Idx(inp), gm);
    assert gm2 == LG.GMReset(gidl, gm);
    var b2 := if ea then BS.CanExit else BS.CannotExit;
    if ea { BoolTreeLkGuardShieldRec(rer, r1, rest, inp, ti); }
    assert EL.BoolTreeLk(rer, [LS.Areg(r1)] + rest, inp, b2, ti) && ATR.EaOf(b2) == ea;
    assert WalkPairLkRec(rer, qm, code, inp, ti, gm2, sqcpc + 1, ea);
    assert sqcpc < RB.size(code);
  }

  lemma BlockedRepLkCSnocRec(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code,
                             inp: LC.Input, nextinp: LC.Input, crv: CP.FCompiled, str: string,
                             ov: LOr.OracleView, S: set<LG.GroupId>,
                             tl: seq<(LT.Tree, LG.GroupMap)>, bl: seq<(AI.Thread, RC.char_expectation)>,
                             tp: (LT.Tree, LG.GroupMap), p: (AI.Thread, RC.char_expectation),
                             ncap: int, nlook: int, nquant: int)
    requires BlockedRepLkCRec(rer, qm, re, code, inp, nextinp, crv, str, ov, S, tl, bl, ncap, nlook, nquant)
    requires p.0.pc >= 0
    requires TreeRepLkRE(rer, qm, code, nextinp, tp.0, (p.0.pc + 1) as nat, true)
    requires exists traw: LT.Tree ::
               CE.ProgErase(traw) == CE.ProgErase(tp.0)
               && WalkPairLkRec(rer, qm, code, nextinp, traw, tp.1, (p.0.pc + 1) as nat, true)
    requires GmtTieOutside(re, p.0, tp.1, S)
    ensures BlockedRepLkCRec(rer, qm, re, code, inp, nextinp, crv, str, ov, S, tl + [tp], bl + [p],
                             ncap, nlook, nquant)
    decreases tl
  {
    if |tl| == 0 {
      assert |bl| == 0;
      assert tl + [tp] == [tp] && bl + [p] == [p];
      assert ([tp])[0] == tp && ([tp])[1..] == [] && ([p])[0] == p && ([p])[1..] == [];
    } else {
      assert |bl| > 0;
      assert (tl + [tp])[0] == tl[0] && (bl + [p])[0] == bl[0];
      assert (tl + [tp])[1..] == tl[1..] + [tp] && (bl + [p])[1..] == bl[1..] + [p];
      BlockedRepLkCSnocRec(rer, qm, re, code, inp, nextinp, crv, str, ov, S, tl[1..], bl[1..],
                           tp, p, ncap, nlook, nquant);
    }
  }

  lemma ThreadRepLkStepAnchorRec(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code,
                                 inp: LC.Input, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
                                 S: set<LG.GroupId>, tb: LT.Tree, gm: LG.GroupMap, t: AI.Thread,
                                 ncap: int, nlook: int, nquant: int, a: R.anchor)
    requires ThreadRepLkRec(rer, qm, re, code, inp, crv, str, ov, S, tb, gm, t, ncap, nlook, nquant)
    requires NR.GetPcRE(code, t.pc as nat) == Some(RB.AnchorAssertion(a))
    requires tb.AnchorPass?     // the anchor is satisfied (else the VM drops the thread)
    ensures ThreadRepLkRec(rer, qm, re, code, inp, crv, str, ov, S, tb.t, gm,
                           t.(pc := t.pc + 1), ncap, nlook, nquant)
  {
    WalkPairLkAtAnchorRec(rer, qm, code, inp, tb, gm, t.pc as nat, t.exit_allowed, a);
    assert (t.pc + 1) as nat == (t.pc as nat) + 1;
    // GmtTieOutside/GmtTieInside read only the capture/look/quant regs, unchanged
    // by the pc update, so they transfer verbatim from ThreadRepLkRec(tb, gm, t).
  }

  lemma ThreadRepLkStepCheckOracleLBRec(
    rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, crv: CP.FCompiled,
    str: string, ov: LOr.OracleView, S: set<LG.GroupId>, lk: L.Lookaround, r1: L.Regex,
    tlk: LT.Tree, tc: LT.Tree, gm: LG.GroupMap, t: AI.Thread, l: int, cp: nat, clk: int,
    body: R.regex, la: R.lookaround, bodycode: RB.code, endl: nat, ngroups: nat,
    qt: AReg.Regs, ncap: int, nlook: int, nquant: int)
    requires qm.ov == ov && !rer.ignoreCase && !rer.multiline
    requires cp <= |str| && t.pc >= 0 && |ov| == |str| + 1
    requires l in qm.looks && qm.looks[l] == (lk, r1)
    requires L.Positivity(lk) && L.LkDir(lk) == WP.Backward
    requires LS.LkResult(lk, tlk, gm, PIV.InpOfCp(str, cp)).Some?
    requires EL.LkGateOk(rer, lk, r1, PIV.InpOfCp(str, cp), tlk, true)
    requires ThreadRepLkRec(rer, qm, re, code, PIV.InpOfCp(str, cp), crv, str, ov, S,
                            LT.LK(lk, tlk, tc), gm, t, ncap, nlook, nquant)
    requires forall g :: g in L.DefGroups(r1) ==> g !in gm
    // (L4 NESTED) body-fragment weakened to the positive-nesting sub-fragment;
    // the GateStepValueLB backward-replay body package is DROPPED with the call.
    requires T.TransWf(body) && NR.NestedFragmentRE(body) && NR.NegLooksLookFreeRE(body) && la.Lookbehind?
    requires r1 == T.Translate(body) && lk == T.TrLookaround(la)
    requires LL.OracleOkSuffix(rer, qm, PIV.InpOfCp(str, cp))
    requires 0 <= l < nlook && l < RL.ASize(t.look_regs)
    requires NR.GetPcRE(code, t.pc as nat) == Some(RB.CheckOracle(l))
    requires T.TransWf(re) && NR.NestedFragmentRE(re)
    requires S == LL.LkBodyGroups(T.Translate(re))
    requires (set g | g in L.DefGroups(r1)) <= S
    ensures var t' := t.(pc := t.pc + 1, look_regs := AReg.set_reg(t.look_regs, l, Some(cp as int), clk));
            var gm2 := LS.LkResult(lk, tlk, gm, PIV.InpOfCp(str, cp)).value;
            ThreadRepLkRec(rer, qm, re, code, PIV.InpOfCp(str, cp), crv, str, ov, S, tc, gm2, t',
                           ncap, nlook, nquant)
  {
    var inp := PIV.InpOfCp(str, cp);
    var t' := t.(pc := t.pc + 1, look_regs := AReg.set_reg(t.look_regs, l, Some(cp as int), clk));
    var gm2 := LS.LkResult(lk, tlk, gm, inp).value;
    // (1) INSIDE tie DROPPED (GmtTieInside is not part of ThreadRepLkRec).
    assert t' == t.(pc := t.pc + 1, look_regs := AReg.set_reg(t.look_regs, l, Some(cp as int), clk));
    // (2) CONTINUATION walk (direction-generic): from the incoming ThreadRepLk's WalkPairLkRec.
    assert LL.OracleOkAt(rer, qm, inp);
    assert WalkPairLkRec(rer, qm, code, inp, LT.LK(lk, tlk, tc), gm, t.pc as nat, t.exit_allowed);
    WalkPairLkAtCheckOracleRec(rer, qm, code, inp, LT.LK(lk, tlk, tc), gm, t.pc as nat, t.exit_allowed, l);
    assert LT.LK(lk, tlk, tc).LK?;        // ⟹ bit true (wrapper: !bit ==> LKFail?)
    assert (t.pc + 1) as nat == (t.pc as nat) + 1 && t'.exit_allowed == t.exit_allowed;
    assert WalkPairLkRec(rer, qm, code, inp, tc, gm2, (t.pc + 1) as nat, t.exit_allowed);
    // (3) OUTSIDE frame: recursive-body confinement (backward gate, PikeLkRegexRec(r1)).
    assert GmtTieOutside(re, t, gm, S);
    EL.TranslateFragmentPikeLkRec(body);  // PikeLkRegexRec(Translate(body)) == PikeLkRegexRec(r1)
    GmtTieOutsideAfterGateNested(rer, re, str, lk, r1, tlk, gm, t, l, cp, clk, S);
  }

  lemma ThreadRepLkStepCheckOracleRec(
    rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, crv: CP.FCompiled,
    str: string, ov: LOr.OracleView, S: set<LG.GroupId>, lk: L.Lookaround, r1: L.Regex,
    tlk: LT.Tree, tc: LT.Tree, gm: LG.GroupMap, t: AI.Thread, l: int, cp: nat, clk: int,
    body: R.regex, la: R.lookaround, bodycode: RB.code, endl: nat, ngroups: nat,
    qt: AReg.Regs, ncap: int, nlook: int, nquant: int)
    requires qm.ov == ov && !rer.ignoreCase && !rer.multiline
    requires cp <= |str| && t.pc >= 0
    requires l in qm.looks && qm.looks[l] == (lk, r1)
    requires L.Positivity(lk) && L.LkDir(lk) == WP.Forward
    requires LS.LkResult(lk, tlk, gm, PIV.InpOfCp(str, cp)).Some?
    requires EL.LkGateOk(rer, lk, r1, PIV.InpOfCp(str, cp), tlk, true)
    // the paired B-subtree at t.pc is the LK gate node (from TtLkAtCheckOracleRec):
    requires ThreadRepLkRec(rer, qm, re, code, PIV.InpOfCp(str, cp), crv, str, ov, S,
                            LT.LK(lk, tlk, tc), gm, t, ncap, nlook, nquant)
    requires forall g :: g in L.DefGroups(r1) ==> g !in gm        // GateAheadClear at this gate
    // (L4 NESTED) the body may itself contain looks: the depth-1 LookFreeRE(body)
    // is replaced by the positive-nesting sub-fragment (feeds PikeLkRegexRec(r1)
    // for the recursive outside-tie); the GateStepValue body-package requires
    // (StaticOkRE(body)/bodycode/qt/f_look_* rows) are DROPPED with the call.
    requires T.TransWf(body) && NR.NestedFragmentRE(body) && NR.NegLooksLookFreeRE(body) && la.Lookahead?
    requires r1 == T.Translate(body) && lk == T.TrLookaround(la)
    requires LL.OracleOkSuffix(rer, qm, PIV.InpOfCp(str, cp))
    requires 0 <= l < nlook && l < RL.ASize(t.look_regs)
    // gate position + outside-frame well-formedness (caller supplies); the
    // continuation walk and outside frame are now DERIVED in the body.
    requires NR.GetPcRE(code, t.pc as nat) == Some(RB.CheckOracle(l))
    requires T.TransWf(re) && NR.NestedFragmentRE(re)
    requires S == LL.LkBodyGroups(T.Translate(re))
    requires (set g | g in L.DefGroups(r1)) <= S
    ensures var t' := t.(pc := t.pc + 1, look_regs := AReg.set_reg(t.look_regs, l, Some(cp as int), clk));
            var gm2 := LS.LkResult(lk, tlk, gm, PIV.InpOfCp(str, cp)).value;
            ThreadRepLkRec(rer, qm, re, code, PIV.InpOfCp(str, cp), crv, str, ov, S, tc, gm2, t',
                           ncap, nlook, nquant)
  {
    var inp := PIV.InpOfCp(str, cp);
    var t' := t.(pc := t.pc + 1, look_regs := AReg.set_reg(t.look_regs, l, Some(cp as int), clk));
    var gm2 := LS.LkResult(lk, tlk, gm, inp).value;
    // (1) INSIDE tie DROPPED (GmtTieInside is not part of ThreadRepLkRec).
    assert t' == t.(pc := t.pc + 1, look_regs := AReg.set_reg(t.look_regs, l, Some(cp as int), clk));
    // (2) CONTINUATION walk: from the incoming ThreadRepLk's WalkPairLkRec on the LK head.
    assert LL.OracleOkAt(rer, qm, inp);   // OracleOkSuffix instantiated at inp
    assert WalkPairLkRec(rer, qm, code, inp, LT.LK(lk, tlk, tc), gm, t.pc as nat, t.exit_allowed);
    WalkPairLkAtCheckOracleRec(rer, qm, code, inp, LT.LK(lk, tlk, tc), gm, t.pc as nat, t.exit_allowed, l);
    assert LT.LK(lk, tlk, tc).LK?;        // ⟹ bit true (wrapper: !bit ==> LKFail?)
    assert (t.pc + 1) as nat == (t.pc as nat) + 1 && t'.exit_allowed == t.exit_allowed;
    assert WalkPairLkRec(rer, qm, code, inp, tc, gm2, (t.pc + 1) as nat, t.exit_allowed);
    // (3) OUTSIDE frame: recursive-body confinement (PikeLkRegexRec(r1)).
    assert GmtTieOutside(re, t, gm, S);   // from the incoming ThreadRepLkRec(LK, gm, t)
    EL.TranslateFragmentPikeLkRec(body);  // PikeLkRegexRec(Translate(body)) == PikeLkRegexRec(r1)
    GmtTieOutsideAfterGateNested(rer, re, str, lk, r1, tlk, gm, t, l, cp, clk, S);   // GmtTieOutside(t',gm2,S)
  }

  /** (L5 F6c) The LOOKBEHIND twin of `ThreadRepLkStepCheckOracleRec`: the same
      gate step for a POSITIVE LOOKBEHIND gate (`L.LkDir(lk) == WP.Backward`,
      `la.Lookbehind?`). Every ingredient is direction-generic
      (`WalkPairLkAtCheckOracleRec` is oracle-bit based; `GmtTieOutsideAfterGateNested`
      takes the direction from `L.LkDir(lk)`), so the proof body is verbatim; only
      the direction pin differs. Fills the (BRICK D5) dead arm of
      `LiftPreserveGatePassLkRec` once `NoPosLookbehindRE` is lifted (F7). */
  lemma ThreadRepLkStepCheckOracleRecLB(
    rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, crv: CP.FCompiled,
    str: string, ov: LOr.OracleView, S: set<LG.GroupId>, lk: L.Lookaround, r1: L.Regex,
    tlk: LT.Tree, tc: LT.Tree, gm: LG.GroupMap, t: AI.Thread, l: int, cp: nat, clk: int,
    body: R.regex, la: R.lookaround, bodycode: RB.code, endl: nat, ngroups: nat,
    qt: AReg.Regs, ncap: int, nlook: int, nquant: int)
    requires qm.ov == ov && !rer.ignoreCase && !rer.multiline
    requires cp <= |str| && t.pc >= 0
    requires l in qm.looks && qm.looks[l] == (lk, r1)
    requires L.Positivity(lk) && L.LkDir(lk) == WP.Backward
    requires LS.LkResult(lk, tlk, gm, PIV.InpOfCp(str, cp)).Some?
    requires EL.LkGateOk(rer, lk, r1, PIV.InpOfCp(str, cp), tlk, true)
    // the paired B-subtree at t.pc is the LK gate node (from TtLkAtCheckOracleRec):
    requires ThreadRepLkRec(rer, qm, re, code, PIV.InpOfCp(str, cp), crv, str, ov, S,
                            LT.LK(lk, tlk, tc), gm, t, ncap, nlook, nquant)
    requires forall g :: g in L.DefGroups(r1) ==> g !in gm        // GateAheadClear at this gate
    // (L4 NESTED) the body may itself contain looks: the depth-1 LookFreeRE(body)
    // is replaced by the positive-nesting sub-fragment (feeds PikeLkRegexRec(r1)
    // for the recursive outside-tie); the GateStepValue body-package requires
    // (StaticOkRE(body)/bodycode/qt/f_look_* rows) are DROPPED with the call.
    requires T.TransWf(body) && NR.NestedFragmentRE(body) && NR.NegLooksLookFreeRE(body) && la.Lookbehind?
    requires r1 == T.Translate(body) && lk == T.TrLookaround(la)
    requires LL.OracleOkSuffix(rer, qm, PIV.InpOfCp(str, cp))
    requires 0 <= l < nlook && l < RL.ASize(t.look_regs)
    // gate position + outside-frame well-formedness (caller supplies); the
    // continuation walk and outside frame are now DERIVED in the body.
    requires NR.GetPcRE(code, t.pc as nat) == Some(RB.CheckOracle(l))
    requires T.TransWf(re) && NR.NestedFragmentRE(re)
    requires S == LL.LkBodyGroups(T.Translate(re))
    requires (set g | g in L.DefGroups(r1)) <= S
    ensures var t' := t.(pc := t.pc + 1, look_regs := AReg.set_reg(t.look_regs, l, Some(cp as int), clk));
            var gm2 := LS.LkResult(lk, tlk, gm, PIV.InpOfCp(str, cp)).value;
            ThreadRepLkRec(rer, qm, re, code, PIV.InpOfCp(str, cp), crv, str, ov, S, tc, gm2, t',
                           ncap, nlook, nquant)
  {
    var inp := PIV.InpOfCp(str, cp);
    var t' := t.(pc := t.pc + 1, look_regs := AReg.set_reg(t.look_regs, l, Some(cp as int), clk));
    var gm2 := LS.LkResult(lk, tlk, gm, inp).value;
    // (1) INSIDE tie DROPPED (GmtTieInside is not part of ThreadRepLkRec).
    assert t' == t.(pc := t.pc + 1, look_regs := AReg.set_reg(t.look_regs, l, Some(cp as int), clk));
    // (2) CONTINUATION walk: from the incoming ThreadRepLk's WalkPairLkRec on the LK head.
    assert LL.OracleOkAt(rer, qm, inp);   // OracleOkSuffix instantiated at inp
    assert WalkPairLkRec(rer, qm, code, inp, LT.LK(lk, tlk, tc), gm, t.pc as nat, t.exit_allowed);
    WalkPairLkAtCheckOracleRec(rer, qm, code, inp, LT.LK(lk, tlk, tc), gm, t.pc as nat, t.exit_allowed, l);
    assert LT.LK(lk, tlk, tc).LK?;        // ⟹ bit true (wrapper: !bit ==> LKFail?)
    assert (t.pc + 1) as nat == (t.pc as nat) + 1 && t'.exit_allowed == t.exit_allowed;
    assert WalkPairLkRec(rer, qm, code, inp, tc, gm2, (t.pc + 1) as nat, t.exit_allowed);
    // (3) OUTSIDE frame: recursive-body confinement (PikeLkRegexRec(r1)).
    assert GmtTieOutside(re, t, gm, S);   // from the incoming ThreadRepLkRec(LK, gm, t)
    EL.TranslateFragmentPikeLkRec(body);  // PikeLkRegexRec(Translate(body)) == PikeLkRegexRec(r1)
    GmtTieOutsideAfterGateNested(rer, re, str, lk, r1, tlk, gm, t, l, cp, clk, S);   // GmtTieOutside(t',gm2,S)
  }

  /** (R2 DEEP CARRIER — the gate-pass rep step, EXTRACTED from
      `LiftPreserveGatePassLkRec`) The deep-carrier converse across a positive
      lookAHEAD gate crossing, packaged as a standalone (non-isolate-assertions)
      lemma so the giant gate-pass preserver's VC count does not balloon. Composes
      `DeepGateReqFromCrossing` (the crossing lands l's whole sub-first-leaf into
      `gm2`) with `LookNestBackTGatePassTopDeep` (every other top lid transports by
      congruence), then rebuilds the deep active rep for the stepped head + tail.
      MIRRORS the DIRECT gate-pass rep threading verbatim, `SubFirstLeafAt` landed
      set in place of `GmOfLive(body, FreshBodyMatch)`. */
  lemma GatePassDeepRepStep(
    rer: LW.RegExpRecord, re: R.regex, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
    S: set<LG.GroupId>, ta: seq<(LT.Tree, LG.GroupMap)>, sactive: seq<AI.Thread>,
    tt: LT.Tree, gm: LG.GroupMap, gm2: LG.GroupMap, th: AI.Thread, th': AI.Thread,
    l: int, lk: L.Lookaround, r1: L.Regex, tlk: LT.Tree, body: R.regex, cp: nat,
    ncap: int, nlook: int, nquant: int)
    requires |ta| > 0 && |sactive| == |ta|
    requires sactive[0] == th && ta[0].1 == gm
    requires PIV.CapUnique(re) && LTB.LookUnique(re)
    requires LookNestBackRepCTopDeep(rer, re, crv, str, ov, S, ta, sactive, ncap, nlook, nquant)
    // frame: gate touches only look_regs at l
    requires th'.quant_regs == th.quant_regs
    requires forall j: int :: j != l ==>
                                AI.get_idx(th'.look_regs.a_clk, j) == AI.get_idx(th.look_regs.a_clk, j)
                                && AI.get_idx(th'.look_regs.a_cp, j) == AI.get_idx(th.look_regs.a_cp, j)
    // the crossing seam (feeds `DeepGateReqFromCrossing`)
    requires cp <= |str|
    requires l >= 0 && (l as nat) in LTB.LookIds(re) && (l as nat) in NI.TopLookIds(re)
    requires T.TransWf(body)
    requires L.Positivity(lk) && L.LkDir(lk) == LidDir(crv, l)   // (L5 F7a) direction-generic
    requires EL.PikeLkRegexRec(r1)
    requires r1 == T.Translate(body)
    requires body == M.VBody(crv, l) && NI.LookBodyOfRE(re, l as nat) == body
    requires tlk == LFU.ComputeTr(rer, [LS.Areg(r1)], PIV.InpOfCp(str, cp), LG.Empty, L.LkDir(lk))
    requires LS.LkResult(lk, tlk, gm, PIV.InpOfCp(str, cp)).Some?
    requires gm2 == LS.LkResult(lk, tlk, gm, PIV.InpOfCp(str, cp)).value
    requires M.GmAgreeOn(gm, LG.Empty, set g | g in L.DefGroups(r1))
    requires AReg.get_cp(th'.look_regs, l) == Some(cp as int)
    ensures LookNestBackRepCTopDeep(rer, re, crv, str, ov, S, [(tt, gm2)] + ta[1..],
                                    [th'] + sactive[1..], ncap, nlook, nquant)
  {
    assert LookNestBackTTopDeep(rer, re, crv, str, ov, S, gm, th, ncap, nlook, nquant);  // rep element 0
    DeepGateReqFromCrossing(rer, re, crv, str, ov, S, gm, gm2, lk, r1, tlk, th', l, cp, body,
                            ncap, nlook, nquant);
    // the off-body region frame from the crossing's confinement
    assert LL.GmAgreeOutside(gm2, gm, PIV.CapIds(NI.LookBodyOfRE(re, l as nat)));
    assert forall g: LG.GroupId ::
        g in S && !(l >= 0 && (l as nat) in LTB.LookIds(re) && g in PIV.CapIds(NI.LookBodyOfRE(re, l as nat)))
        ==> ((g in gm <==> g in gm2) && (g in gm ==> gm2[g] == gm[g]));
    LookNestBackTGatePassTopDeep(rer, re, crv, str, ov, S, gm, gm2, th, th', l, ncap, nlook, nquant);
    forall i | 0 <= i < |[(tt, gm2)] + ta[1..]|
      ensures LookNestBackTTopDeep(rer, re, crv, str, ov, S, ([(tt, gm2)] + ta[1..])[i].1,
                                   ([th'] + sactive[1..])[i], ncap, nlook, nquant)
    {
      if i == 0 {
      } else {
        assert ([(tt, gm2)] + ta[1..])[i] == ta[i];
        assert ([th'] + sactive[1..])[i] == sactive[i];
      }
    }
  }

  lemma BlockedToActiveLkCRec(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code,
                              inp: LC.Input, nextinp: LC.Input, crv: CP.FCompiled, str: string,
                              ov: LOr.OracleView, S: set<LG.GroupId>,
                              tl: seq<(LT.Tree, LG.GroupMap)>, bl: seq<(AI.Thread, RC.char_expectation)>,
                              ncap: int, nlook: int, nquant: int)
    requires BlockedRepLkCRec(rer, qm, re, code, inp, nextinp, crv, str, ov, S, tl, bl, ncap, nlook, nquant)
    ensures ActiveRepLkCRec(rer, qm, re, code, nextinp, crv, str, ov, S, tl, PSM.ResumeAll(bl),
                            ncap, nlook, nquant)
    decreases tl
  {
    if |tl| == 0 {
      assert |bl| == 0;
    } else {
      assert |bl| > 0;
      var th := bl[0].0;
      var rth := th.(exit_allowed := true, pc := th.pc + 1);
      assert PSM.ResumeAll(bl) == [rth] + PSM.ResumeAll(bl[1..]);
      assert rth.pc >= 0 && (rth.pc as nat) == (th.pc + 1) as nat;
      assert TreeRepLkRE(rer, qm, code, nextinp, tl[0].0, rth.pc as nat, rth.exit_allowed);
      var traw: LT.Tree :| CE.ProgErase(traw) == CE.ProgErase(tl[0].0)
                           && WalkPairLkRec(rer, qm, code, nextinp, traw, tl[0].1, (th.pc + 1) as nat, true);
      assert rth.capture_regs == th.capture_regs && rth.look_regs == th.look_regs
             && rth.quant_regs == th.quant_regs;
      assert GmtTieOutside(re, rth, tl[0].1, S)
        ;
      assert ThreadRepLkRec(rer, qm, re, code, nextinp, crv, str, ov, S, traw, tl[0].1, rth,
                            ncap, nlook, nquant);
      assert ThreadRepLkCRec(rer, qm, re, code, nextinp, crv, str, ov, S, tl[0].0, tl[0].1, rth,
                             ncap, nlook, nquant);
      BlockedToActiveLkCRec(rer, qm, re, code, inp, nextinp, crv, str, ov, S, tl[1..], bl[1..],
                            ncap, nlook, nquant);
      assert ([rth] + PSM.ResumeAll(bl[1..]))[0] == rth
             && ([rth] + PSM.ResumeAll(bl[1..]))[1..] == PSM.ResumeAll(bl[1..]);
    }
  }

  /** (BRICK D6 — forward inside-`S` per-g WIRING) The composition of the two
      capstones the endpoint's inside-`S` FORWARD chain bottoms out on: the D4
      whole-loop ancestor-clock chain (`FLookLoopAncestorClockChain`, supplying
      feeds (i)/(ii)) feeding `M.ReconInnerGmOfLiveClose` (the C4c close). For an
      innermost-owned inside-look group `g` this lands `g` in the whole-regex live
      denotation of the RECONSTRUCTED banks at the raw `LiveRange`, GREEN, isolating
      the residuals to exactly `AllBodyTopFeeds` (the engine half) + the body-side
      value-lift/quant-reconcile feeds (from `M.FLookLoopValueLiftFull` +
      `M.FLookLoopQuantCoversFromTables`). No further algebra — the endpoint then
      only converts `LiveRange` to `NormRange` against the ordered leaf. */
  lemma ReconInnerForwardWired(
    re: R.regex, owner: nat, res0: AReg.Regs, res1: AReg.Regs, res2: AReg.Regs,
    rfcap: AReg.Regs, rflk: AReg.Regs, rfqt: AReg.Regs, g: nat)
    requires NR.NestedFragmentRE(re) && NR.NegLooksLookFreeRE(re)
    requires PIV.CapUnique(re) && LTB.LookUnique(re)
    requires owner in LTB.LookIds(re)
    requires NR.NestedFragmentRE(NI.LookBodyOfRE(re, owner)) && PIV.CapUnique(NI.LookBodyOfRE(re, owner))
    requires g in PIV.CapIds(NI.LookBodyOfRE(re, owner))
    requires g !in PIV.CapIdsInLooks(NI.LookBodyOfRE(re, owner))
    // engine feeds (i)/(ii) input: the whole-loop ancestor-chain base evidence.
    requires AllBodyTopFeeds(re, res0.a_clk, AReg.as_arrays(res1).1, res2.a_clk)
    requires AI.get_idx(res0.a_clk, CP.start_reg(g)) >= 0
    // body-side feeds (value lift + quant reconcile + fresh liveness).
    requires forall c: nat :: c in PIV.CapIds(NI.LookBodyOfRE(re, owner))
                              && AI.get_idx(rfcap.a_clk, CP.start_reg(c)) < 0
                              ==> AI.get_idx(rfcap.a_cp, CP.start_reg(c)) < 0
    requires g in PIV.GmOfLive(NI.LookBodyOfRE(re, owner), rfcap, rflk, rfqt)
    requires forall c: nat :: c in PIV.CapIds(NI.LookBodyOfRE(re, owner)) ==>
                                AI.get_idx(res0.a_clk, CP.start_reg(c)) == AI.get_idx(rfcap.a_clk, CP.start_reg(c))
    requires forall qd: nat :: qd in PIV.QuantIds(NI.LookBodyOfRE(re, owner)) ==>
                                 AI.get_idx(res2.a_clk, qd as int) == AI.get_idx(rfqt.a_clk, qd as int)
    requires AI.get_idx(res0.a_cp, CP.start_reg(g)) >= 0
    ensures g in PIV.CapIds(re)
    ensures g in PIV.GmOfLive(re, res0, res1, res2)
    ensures PIV.GmOfLive(re, res0, res1, res2)[g] == PIV.LiveRange(res0.a_cp, res0.a_clk, g)
  {
    // feeds (i)/(ii) from the D4 capstone
    FLookLoopAncestorClockChain(re, res0.a_clk, AReg.as_arrays(res1).1, res2.a_clk, owner, g);
    // C4c close via M's capstone
    M.ReconInnerGmOfLiveClose(re, NI.LookBodyOfRE(re, owner), owner, res0, res1, res2,
                              rfcap, rflk, rfqt, g);
  }

  /** (R2 — DEEP top-owner producer) The reverse-recon descent conclusion assembled
      for EVERY recon-live inside-look capture — DIRECT or DEEP — via the DEEP
      carrier. Same shape as `DescentProducerTopOwners`, but the per-`g2` package is
      keyed on `SubFirstLeafAt(A0)` (the whole sub-first-leaf at `A0`'s recorded
      position) instead of `GmOfLive(body(A0), FreshBodyMatch(A0))` (direct captures
      only). Since the sub-first-leaf carries `A0`'s deep captures too, this single
      producer lands both the top-owner (`g2` directly in `body(A0)`) and the DEEP
      cases (`g2` nested below `A0`, delivered into `SubFirstLeafAt(A0)` by the
      body-level replay `LookNestBackTFromBodyReplay` + inner descent). Closes the
      R2 wall's conclusion side: the missing bridge `g2 in leaf_{A0} ==> g2 in leaf`
      is exactly the per-`g2` `SubFirstLeafAt` membership feeding `DescentLandTopDeep`. */
  lemma DescentProducerTopOwnersDeep(
    rer: LW.RegExpRecord, re: R.regex, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
    S: set<LG.GroupId>, gmt: LG.GroupMap, thread: AI.Thread, res0: AReg.Regs,
    ncap: int, nlook: int, nquant: int)
    requires S == PIV.CapIdsInLooks(re)
    requires LookNestBackTTopDeep(rer, re, crv, str, ov, S, gmt, thread, ncap, nlook, nquant)
    // per recon-live inside-look g2 (DIRECT or DEEP): a TOP ancestor A0 matched +
    // dominating on the carrier thread's banks, whose sub-first-leaf carries g2.
    requires forall g2: nat :: g2 in S && AI.get_idx(res0.a_clk, CP.start_reg(g2)) >= 0 ==>
                                 exists A0: nat ::
                                   A0 in NI.TopLookIds(re) && A0 in LTB.LookIds(re)
                                   && g2 in PIV.CapIds(NI.LookBodyOfRE(re, A0))
                                   && M.MatchedPosLA(crv, thread.look_regs, A0 as int)
                                   && NI.LookPathDom(re, AI.get_idx(thread.look_regs.a_clk, A0 as int), thread.quant_regs.a_clk, A0)
                                   && var lsub := SubFirstLeafAt(rer, crv, str, A0 as int, thread.look_regs);
                                   lsub.Some? && g2 in lsub.value
    ensures forall g2: nat :: g2 in S && AI.get_idx(res0.a_clk, CP.start_reg(g2)) >= 0 ==> g2 in gmt
  {
    forall g2: nat | g2 in S && AI.get_idx(res0.a_clk, CP.start_reg(g2)) >= 0
      ensures g2 in gmt
    {
      var A0: nat :|
        A0 in NI.TopLookIds(re) && A0 in LTB.LookIds(re)
        && g2 in PIV.CapIds(NI.LookBodyOfRE(re, A0))
        && M.MatchedPosLA(crv, thread.look_regs, A0 as int)
        && NI.LookPathDom(re, AI.get_idx(thread.look_regs.a_clk, A0 as int), thread.quant_regs.a_clk, A0)
        && var lsub := SubFirstLeafAt(rer, crv, str, A0 as int, thread.look_regs);
        lsub.Some? && g2 in lsub.value;
      DescentLandTopDeep(rer, re, crv, str, ov, S, gmt, thread, A0, g2, ncap, nlook, nquant);
    }
  }

  /** (SINGLE-THREADED) FULL-LIVENESS descent producer — keyed on
      `g2 in GmOfLive(re,res)` instead of bare res0-live. This is the CORRECT key:
      bare res0-live is NOT producible (an ESCAPED look — matched early, its enclosing
      quantifier re-stamped later — stays res0-live [quant `Reset` clears capture regs,
      not look clocks] yet is non-dominant, so `res0`-live ⟹ gmt is FALSE for it). Full
      `GmOfLive` membership excludes escaped looks by construction (it checks dominance),
      so the per-`g2` package is establishable. The `ensures` IS the endpoint's
      reverse-(c) residual (`forall g in S && g in GmOfLive(re,res) ==> g in gmt`),
      discharged DIRECTLY — no `ReverseCFromDescent` weakening. */
  lemma DescentProducerTopOwnersDeepFull(
    rer: LW.RegExpRecord, re: R.regex, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
    S: set<LG.GroupId>, gmt: LG.GroupMap, thread: AI.Thread,
    res0: AReg.Regs, res1: AReg.Regs, res2: AReg.Regs,
    ncap: int, nlook: int, nquant: int)
    requires S == PIV.CapIdsInLooks(re)
    requires LookNestBackTTopDeep(rer, re, crv, str, ov, S, gmt, thread, ncap, nlook, nquant)
    // per LIVE inside-look g2 (DIRECT or DEEP): a TOP ancestor A0 matched + dominating
    // on the winning thread's banks, whose sub-first-leaf carries g2.
    requires forall g2: nat :: g2 in S && g2 in PIV.GmOfLive(re, res0, res1, res2) ==>
                                 exists A0: nat ::
                                   A0 in NI.TopLookIds(re) && A0 in LTB.LookIds(re)
                                   && g2 in PIV.CapIds(NI.LookBodyOfRE(re, A0))
                                   && M.MatchedPosLA(crv, thread.look_regs, A0 as int)
                                   && NI.LookPathDom(re, AI.get_idx(thread.look_regs.a_clk, A0 as int), thread.quant_regs.a_clk, A0)
                                   && var lsub := SubFirstLeafAt(rer, crv, str, A0 as int, thread.look_regs);
                                   lsub.Some? && g2 in lsub.value
    ensures forall g2: nat :: g2 in S && g2 in PIV.GmOfLive(re, res0, res1, res2) ==> g2 in gmt
  {
    forall g2: nat | g2 in S && g2 in PIV.GmOfLive(re, res0, res1, res2)
      ensures g2 in gmt
    {
      var A0: nat :|
        A0 in NI.TopLookIds(re) && A0 in LTB.LookIds(re)
        && g2 in PIV.CapIds(NI.LookBodyOfRE(re, A0))
        && M.MatchedPosLA(crv, thread.look_regs, A0 as int)
        && NI.LookPathDom(re, AI.get_idx(thread.look_regs.a_clk, A0 as int), thread.quant_regs.a_clk, A0)
        && var lsub := SubFirstLeafAt(rer, crv, str, A0 as int, thread.look_regs);
        lsub.Some? && g2 in lsub.value;
      DescentLandTopDeep(rer, re, crv, str, ov, S, gmt, thread, A0, g2, ncap, nlook, nquant);
    }
  }

  /** L4 PERF: the FULL per-g fresh-wf side condition (all four conjuncts,
      including the g-dependent GNotUnderQuantL), proven in a MINIMAL context.
      In ProduceOwnerForall this forall sat inside `forall g { forall owner0 }`
      under isolate_assertions; the inner ENSURES-check ran in a ~5000-fact
      context and timed out (10x) even after the g-independent facts were hoisted
      to FreshWfGIndep. Extracted here, the g-loop obtains it as one cheap call. */
  lemma FreshWfAtG(
    qm: AR.QMap, crv: CP.FCompiled, str: string, re: R.regex, ov: LOr.OracleView,
    res1: AReg.Regs, g: LG.GroupId, ncap: int, nlook: int, nquant: int)
    requires LTB.LookTablesOk(re, crv)
    requires GateStaticsOkNested(qm, re, crv, ncap, nlook, nquant)
    requires forall x: nat :: x in LTB.LookIds(re) ==> (x as int) in qm.looks
    requires M.LookInvO(res1, ov, str)
    requires T.TransWf(re)
    requires M.GNotUnderQuantL(T.Translate(re), g)
    ensures M.FreshWfO(crv, str, re, res1, g, ncap, nlook, nquant)
  {
    reveal M.FreshWfO();
    FreshWfGIndep(qm, crv, str, re, ov, res1, ncap, nlook, nquant);
    forall owner0: nat |
      owner0 in LTB.LookIds(re)
      && g in PIV.CapIds(NI.LookBodyOfRE(re, owner0))
      && g !in PIV.CapIdsInLooks(NI.LookBodyOfRE(re, owner0))
      && M.MatchedPosLA(crv, res1, owner0)
      ensures var body := NI.LookBodyOfRE(re, owner0);
              PSM.SizesOkRE(body, ncap, nlook, nquant)
              && (AReg.get_cp(res1, owner0).Some? ==> M.cp_ctx_ok(crv, str, res1, owner0))
              && T.TransWf(body)
              && M.GNotUnderQuantL(T.Translate(body), g)
    {
      // SizesOkRE(body), cp_ctx_ok, TransWf(body): g-independent, from FreshWfGIndep.
      // GNotUnderQuantL(Translate(body), g): descends the top-level fact to the body.
      GNotUnderQuantLLookBody(re, owner0, g);
    }
  }

  /** L4 PERF: the owner-package forall, produced OPAQUE in a MINIMAL context.
      The `forall g :: exists owner :: OwnerPkg` needs the a-h tables (for
      `FreshBodyDirectMember`), whose triggers make it slow in MainTheoremL4's
      ~5000-fact context. Here the a-h stay local, and MainTheoremL4 obtains
      `OwnerForallO(...)` atomically. */
  lemma ProduceOwnerForall(
    qm: AR.QMap, crv: CP.FCompiled, str: string, ast: R.regex, re: R.regex, code: RB.code,
    endl: nat, ov: LOr.OracleView, thread: AI.Thread, S: set<LG.GroupId>, inits: AI.VmState,
    capture: AReg.Regs, look: AReg.Regs, quant: AReg.Regs, result: Option<AI.Thread>,
    ncap: int, nlook: int, nquant: int)
    requires crv == CP.FFullCompilation(ast)
    requires re == R.lazy_prefix(ast)
    requires code == CP.compile_to_bytecode(re)
    requires NR.NestedFragmentRE(re) && NR.L5ScopeRE(re) && T.TransWf(re)
    requires PIV.CapUnique(re) && PIV.QuantUnique(re) && LTB.LookUnique(re)
    requires LTB.LookTablesOk(re, crv) && LTB.LidsWellNested(re)
    requires NR.NfaRepRE(re, code, 0, endl) && |code| == endl + 1
    requires NR.GetPcRE(code, endl) == Some(RB.Accept)
    requires ncap >= 0 && nlook >= 0 && nquant >= 0
    requires ncap == 2 * R.max_group(ast) + 2 && nlook == R.max_lookaround(ast) + 1 && nquant == R.max_quant(ast) + 1
    requires forall x: nat :: x in LTB.LookIds(re) ==> 1 <= x <= R.max_lookaround(ast)
    requires forall x: nat :: x in LTB.LookIds(re) ==> (x as int) in qm.looks
    requires capture == AReg.init_regs(ncap) && look == AReg.init_regs(nlook) && quant == AReg.init_regs(nquant)
    requires |inits.processed.true_set| == RB.size(code) && |inits.processed.false_set| == RB.size(code)
    requires inits.context.nextchar == AI.get_char(str, inits.cp)
    requires 0 <= inits.cp <= |str| && inits.clock >= 0
    requires inits.active == [AI.init_thread(capture, look, quant)]
    requires inits.blocked == [] && inits.bestmatch.None?
    requires result == AI.FFindMatch(code, str, inits, ov, LAnc.Forward, crv.f_main_cdns).0
    requires result.Some? && thread == result.value
    requires GateStaticsOkNested(qm, re, crv, ncap, nlook, nquant)
    requires forall c: nat :: c in PIV.CapIdsInLooks(re) ==> M.GNotUnderQuantL(T.Translate(re), c)
    requires S == PIV.CapIdsInLooks(re)
    requires var res := AI.FLookLoop(crv, str, 1, R.max_lookaround(ast), thread.capture_regs, thread.look_regs, thread.quant_regs, ov);
             M.LookInvO(res.1, ov, str) && M.Res0LiveO(re, res.0)
    requires M.ThreadLookInvO(thread.look_regs, ov, str)
    ensures var res := AI.FLookLoop(crv, str, 1, R.max_lookaround(ast), thread.capture_regs, thread.look_regs, thread.quant_regs, ov);
            OwnerForallO(crv, str, re, ov, res.0, res.1, res.2, S, ncap, nlook, nquant)
  {
    var maxlook := R.max_lookaround(ast);
    var res := AI.FLookLoop(crv, str, 1, maxlook, thread.capture_regs, thread.look_regs, thread.quant_regs, ov);
    var lkT := thread.look_regs;
    var qtT := thread.quant_regs;
    var Sreg := PIV.CaptureRegsSet(PIV.CapIdsInLooks(re));
    var Slook := M.LookIdSet(re);
    // OwnerForallO stays opaque until the final assembly, and LookInvO(res.1) is
    // handled inside FreshWfGIndep -- both kept out of the g-loop's trigger context.
    reveal M.ThreadLookInvO(), M.Res0LiveO();
    // Establish the a-h tables OPAQUELY (scoped): the 6-variable (D-ord)/(g_new)
    // quantifiers never enter the forall's own trigger context.
    // one LookRows call establishes AhO AND the winning thread's register
    // well-formedness + quant-reg facts, so FreshBodyDirectMember's register-wf
    // preconditions are DIRECT HITS in the g-loop (no per-VC FFindMatch unfold).
    assert M.AhO(crv, ast, thread.capture_regs, thread.look_regs, Sreg, Slook, ncap, str)
           && CM.ThreadRegsWf(thread, ncap, nlook, nquant)
           && (forall k :: AI.get_idx(thread.quant_regs.a_cp, k) < 0)
           && (forall k :: AI.get_idx(thread.quant_regs.a_clk, k) >= -1)
    by {
      reveal M.AhO();
      M.LookRowsFromTablesNested(ast, re, crv, code, str, ov, crv.f_main_cdns, inits,
                                 capture, look, quant, ncap, nlook, nquant, endl, result);
    }
    // g-independent fresh-wf (SizesOkRE, cp_ctx_ok, TransWf), proven ONCE in a
    // minimal context; the g-loop below only owes the g-dependent GNotUnderQuantL.
    FreshWfGIndep(qm, crv, str, re, ov, res.1, ncap, nlook, nquant);
    forall g: LG.GroupId | g in S && g in PIV.GmOfLive(re, res.0, res.1, res.2)
      ensures exists owner: nat :: OwnerPkg(crv, str, re, ov, res.1, g, owner, ncap, nlook, nquant)
    {
      // res0-liveness at g
      PIV.CapIdsSplit(re);
      NI.GmOfLivePresenceExtractLkNested(re, res.0, res.1, res.2, g);
      assert AI.get_idx(res.0.a_clk, CP.start_reg(g)) >= 0;
      // fresh-wf side condition (all four conjuncts) for this g, in a
      // minimal context -- the nested forall here timed out (10x) otherwise.
      FreshWfAtG(qm, crv, str, re, ov, res.1, g, ncap, nlook, nquant);
      var owner := M.FreshBodyDirectMember(crv, str, ast, re, thread.capture_regs, lkT, qtT, ov,
                                           Sreg, Slook, ncap, nlook, nquant, g);
      assert OwnerPkg(crv, str, re, ov, res.1, g, owner, ncap, nlook, nquant);
    }
    // assemble the opaque wrapper from the forall just proven.
    assert OwnerForallO(crv, str, re, ov, res.0, res.1, res.2, S, ncap, nlook, nquant) by {
      reveal OwnerForallO();
    }
  }

}
