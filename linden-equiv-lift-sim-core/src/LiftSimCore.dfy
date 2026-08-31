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
module LindenElkLiftSimCore {
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

  // ==========================================================================
  // SOLID definitions — the pairing.
  // ==========================================================================

  /** The t-side walk state at a pc: some action list represented at `pc`
      whose (checked-flag-erased) spec tree is `tb`. The B-side analogue of
      `TT.TreeThreadRE`.

      NOTE (2026-08-03 do-while-seam reformulation): `WO.WalkOk` was DROPPED from
      this bundle. It was a construction artifact of `ActionsTreeRepFRE` (which
      builds `tstar` top-down and needs the star loop-view guard to proceed).
      `EL.BoolTreeLk` ALREADY self-guards the do-while: its free-star iteration
      arm hardcodes `Acheck` at `CannotExit`, so a nullable empty iteration
      dead-ends at `Mismatch`. Keeping `WalkOk` made the `min==1 Inf` seam
      unsatisfiable (`WalkOkQuantSeam` inserts an `Acheck` the `BoolTreeLk`
      continuation lacks); without it the seam continuation
      `[Areg(r1),Areg(star)]+cont` satisfies `ActionsRepL` + `BoolTreeLk` = tb.t. */
  ghost predicate TtLk(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                       tb: LT.Tree, pc: nat, ea: bool)
    decreases RB.size(code) - pc
  {
    // `tr_begin`-style transparency: `ActionsRepL` has no `BeginLoop` disjunct
    // (TT.ActionsRepNotAtBeginLoop), yet the VM steps a `BeginLoop` thread
    // straight to `pc+1` (exit_allowed:=false). This stutter lets the tb-pairing
    // see through it, mirroring `TreeRepRE.tr_begin` on the tstar side — so
    // `TtLkAtBeginLoop` becomes a REAL stutter and every non-BeginLoop `TtLkAt*`
    // inversion is unaffected (the first disjunct is dead off a BeginLoop pc).
    (pc < RB.size(code) && NR.GetPcRE(code, pc) == Some(RB.BeginLoop)
     && TtLk(rer, qm, code, inp, tb, pc + 1, false))
    // SQC see-through (2026-08-07 session 5): the star/backfork iteration arm
    // parks a thread AT the `SetQuantToClock` pc, where NO `ActionsRepL`
    // exists for the arm's `GroupActionT(Reset, ·)` tree (the body's actions
    // live past the following BeginLoop). Instruction-gated, like the
    // BeginLoop stutter — dead off an SQC pc.
    || (pc < RB.size(code)
        && exists q: int ::
          NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(q, false))
          && q in qm.quants
          && tb.GroupActionT? && tb.g == LG.Reset(qm.quants[q])
          && TtLk(rer, qm, code, inp, tb.t, pc + 1, ea))
    || (exists acts: LS.Actions, b: BS.LoopBool ::
          AR.ActionsRepL(rer, qm, acts, code, pc)
          && EL.PikeLkActions(acts)
          && ATR.EaOf(b) == ea
          && EL.BoolTreeLk(rer, acts, inp, b, tb))
  }

  /** A lookaround occurrence at the TOP LEVEL of `r` — reachable without
      passing an enclosing quantifier's `Reset`. (Under a quantifier the walk
      re-enters through `Reset(DefGroups(body))`, which re-clears the gate's
      groups; a top-level occurrence has no such guard, so `GateAheadClear`
      must hold of it NOW.) */
  ghost predicate RegexTopGate(r: L.Regex, lk: L.Lookaround, r1: L.Regex)
    decreases r
  {
    match r
    case LookaroundR(lk2, rb) => lk2 == lk && rb == r1
    case Sequence(a, b) => RegexTopGate(a, lk, r1) || RegexTopGate(b, lk, r1)
    case Disjunction(a, b) => RegexTopGate(a, lk, r1) || RegexTopGate(b, lk, r1)
    case Group(_, rb) => RegexTopGate(rb, lk, r1)
    case Quantified(_, _, _, _) => false
    case _ => false
  }

  /** A gate is PENDING in the action list when some `Areg` holds it at top
      level. */
  ghost predicate GatePending(acts: LS.Actions, lk: L.Lookaround, r1: L.Regex) {
    exists i :: 0 <= i < |acts| && acts[i].Areg? && RegexTopGate(acts[i].r, lk, r1)
  }

  /** OUTSIDE `S`: `gmt` is exactly the thread's live denotation — today's
      `ThreadTracksGm`, transported to the t side. */
  ghost predicate GmtTieOutside(re: R.regex, th: AI.Thread, gmt: LG.GroupMap, S: set<LG.GroupId>) {
    var gml := PIV.GmOfLive(re, th.capture_regs, th.look_regs, th.quant_regs);
    forall g: LG.GroupId | g !in S ::
      (g in gmt <==> g in gml) && (g in gmt ==> gmt[g] == gml[g])
  }

  /** INSIDE `S`: each present inside-look group's value is the FRESH BODY
      REPLAY's value at the thread's own recorded `a_cp[l]` — the exact shape
      `FLookLoopValueOk` delivers engine-side, so the endpoint composes with
      the existing (E) bridge with no translation. (SEAM: the owner-lid
      existential may want the `LookEntryOk` table pin added once the gate case
      is filled — `M.LookRowsFromTablesL3a` produces that bundle.) */
  ghost predicate GmtTieInside(crv: CP.FCompiled, str: string, ov: LOr.OracleView,
                               th: AI.Thread, gmt: LG.GroupMap, S: set<LG.GroupId>,
                               ncap: int, nlook: int, nquant: int) {
    forall g: LG.GroupId | g in S && g in gmt ::
      exists l: int ::
        0 <= l < nlook
        && g in PIV.CapIds(M.VBody(crv, l))
        && M.MatchedPosLA(crv, th.look_regs, l)
        && var rf := M.FreshBodyMatch(crv, str, l, th.look_regs, ov, ncap, nlook, nquant);
        rf.Some?
        && var gmb := PIV.GmOfLive(M.VBody(crv, l), rf.value.capture_regs,
                                   rf.value.look_regs, rf.value.quant_regs);
        // L3b: a LOOKBEHIND's fresh match runs BACKWARD, so its `GmOfLive` reads
        // the span REVERSED (item-0 quirk); the ordered spec `gmt[g]` is the
        // endpoint SWAP of that reversed read. NO-OP for lookaheads (forward,
        // already ordered) and for capture-free lookbehinds (no such `g`).
        var looktype := if 0 <= l < |crv.f_look_types| then crv.f_look_types[l] else R.Lookahead;
        g in gmb && gmt[g] == (if looktype.Lookbehind? then LBV.SwapRange(gmb[g]) else gmb[g])
  }

  /** Blocked lists pair through the SAME matching filter as the existing sim
      (landmine 3): RegElk blocks unconditionally, the tree machine only blocks
      `Read` trees, and `PIV.MatchingBlocked` realigns them — char checks are
      gate-free, so the verdicts transfer verbatim. The B-side blocked tree is
      the post-`Read` continuation at `nextinp` with the flag re-armed, exactly
      `BlockedRepRE`'s shape with `TtLk` in place of `TreeThreadRE`. */
  ghost predicate BlockedRepLk(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code,
                               inp: LC.Input, nextinp: LC.Input, crv: CP.FCompiled, str: string,
                               ov: LOr.OracleView, S: set<LG.GroupId>,
                               tl: seq<(LT.Tree, LG.GroupMap)>, bl: seq<(AI.Thread, RC.char_expectation)>,
                               ncap: int, nlook: int, nquant: int)
    decreases tl
  {
    (|tl| == 0 && |bl| == 0)
    || (|tl| > 0 && |bl| > 0
        && bl[0].0.pc >= 0
        && TtLk(rer, qm, code, nextinp, tl[0].0, (bl[0].0.pc + 1) as nat, true)
        && GmtTieOutside(re, bl[0].0, tl[0].1, S)
        && GmtTieInside(crv, str, ov, bl[0].0, tl[0].1, S, ncap, nlook, nquant)
        && BlockedRepLk(rer, qm, re, code, inp, nextinp, crv, str, ov, S, tl[1..], bl[1..],
                        ncap, nlook, nquant))
  }

  /** (L4 NESTED) The blocked-list pairing with the depth-1-hardwired
      `GmtTieInside` conjunct DROPPED (see `ThreadRepLkNested`). The blocked-tie
      filter (`TtLk` at `pc+1`) and the outside value tie are kept verbatim. */
  ghost predicate BlockedRepLkNested(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code,
                                     inp: LC.Input, nextinp: LC.Input, crv: CP.FCompiled, str: string,
                                     ov: LOr.OracleView, S: set<LG.GroupId>,
                                     tl: seq<(LT.Tree, LG.GroupMap)>, bl: seq<(AI.Thread, RC.char_expectation)>,
                                     ncap: int, nlook: int, nquant: int)
    decreases tl
  {
    (|tl| == 0 && |bl| == 0)
    || (|tl| > 0 && |bl| > 0
        && bl[0].0.pc >= 0
        && TtLk(rer, qm, code, nextinp, tl[0].0, (bl[0].0.pc + 1) as nat, true)
        && GmtTieOutside(re, bl[0].0, tl[0].1, S)
        && BlockedRepLkNested(rer, qm, re, code, inp, nextinp, crv, str, ov, S, tl[1..], bl[1..],
                              ncap, nlook, nquant))
  }

  /** Best-match tie: `None` together, or the recorded B leaf carries the
      winning thread's values on both sides of `S`. */
  ghost predicate BestTieLk(re: R.regex, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
                            S: set<LG.GroupId>, bbest: Option<LT.Leaf>, bm: Option<AI.Thread>,
                            ncap: int, nlook: int, nquant: int) {
    (bbest.None? <==> bm.None?)
    && (bbest.Some? ==>
          bm.Some?
          && GmtTieOutside(re, bm.value, bbest.value.1, S)
          && GmtTieInside(crv, str, ov, bm.value, bbest.value.1, S, ncap, nlook, nquant)
          // (E3) the winning thread carries the look-path facts for every lid
          // owning a leaf-present inside-S group — the (E) PathPresentLk feed.
          && LookNestOkT(re, S, bbest.value.1, bm.value)
          // (E4) the CONVERSE: dominance-surviving fresh-match groups are in
          // the leaf — the reverse value tie's feed.
          && LookNestBackT(re, crv, str, ov, S, bbest.value.1, bm.value, ncap, nlook, nquant))
  }

  /** (L4 NESTED) The best-match tie with the depth-1-hardwired `GmtTieInside`
      conjunct DROPPED (see `ThreadRepLkNested`). The outside value tie and BOTH
      look-path carriers (`LookNestOkT` (E3), `LookNestBackT` (E4)) are kept
      verbatim — those are already stated over the depth-general ownership
      machinery. */
  ghost predicate BestTieLkNested(re: R.regex, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
                                  S: set<LG.GroupId>, bbest: Option<LT.Leaf>, bm: Option<AI.Thread>,
                                  ncap: int, nlook: int, nquant: int) {
    (bbest.None? <==> bm.None?)
    && (bbest.Some? ==>
          bm.Some?
          && GmtTieOutside(re, bm.value, bbest.value.1, S)
          && LookNestOkT(re, S, bbest.value.1, bm.value)
          && LookNestBackT(re, crv, str, ov, S, bbest.value.1, bm.value, ncap, nlook, nquant))
  }

  // ==========================================================================
  // L4 depth-k RECURSIVE walk tower (brick C3.6). The `WalkPairLk`/`TtLk` family
  // and its `ThreadRepLk*`/`BlockedRepLk*`/`LiftInv*` clients rebuilt on the
  // RECURSIVE action predicate `EL.PikeLkActionsRec` (EntryLk.dfy:785) in place
  // of the depth-1 `EL.PikeLkActions`. NOTE: `EL.BoolTreeLk` is SHARED — there is
  // NO `BoolTreeLkRec`; `EL.ComputeBoolTreeLkRec` also ensures `EL.BoolTreeLk`,
  // so the ONLY leaf-arm change is `PikeLkActions -> PikeLkActionsRec`. The
  // BeginLoop/SetQuant see-through arms, `GateAheadClear`, and `WalkDefsOk` are
  // verbatim. Everything above `WalkPairLk`'s leaf arm (the `*Nested` tier, which
  // drops `GmtTieInside`) is what these `*Rec` clones mirror.
  // ==========================================================================

  /** `TtLk` rebuilt on `EL.PikeLkActionsRec` (recursive fragment). */
  ghost predicate TtLkRec(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                          tb: LT.Tree, pc: nat, ea: bool)
    decreases RB.size(code) - pc
  {
    (pc < RB.size(code) && NR.GetPcRE(code, pc) == Some(RB.BeginLoop)
     && TtLkRec(rer, qm, code, inp, tb, pc + 1, false))
    || (pc < RB.size(code)
        && exists q: int ::
          NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(q, false))
          && q in qm.quants
          && tb.GroupActionT? && tb.g == LG.Reset(qm.quants[q])
          && TtLkRec(rer, qm, code, inp, tb.t, pc + 1, ea))
    || (exists acts: LS.Actions, b: BS.LoopBool ::
          AR.ActionsRepL(rer, qm, acts, code, pc)
          && EL.PikeLkActionsRec(acts)
          && ATR.EaOf(b) == ea
          && EL.BoolTreeLk(rer, acts, inp, b, tb))
  }

  /** `BlockedRepLkNested` on `TtLkRec`. */
  ghost predicate BlockedRepLkRec(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code,
                                  inp: LC.Input, nextinp: LC.Input, crv: CP.FCompiled, str: string,
                                  ov: LOr.OracleView, S: set<LG.GroupId>,
                                  tl: seq<(LT.Tree, LG.GroupMap)>, bl: seq<(AI.Thread, RC.char_expectation)>,
                                  ncap: int, nlook: int, nquant: int)
    decreases tl
  {
    (|tl| == 0 && |bl| == 0)
    || (|tl| > 0 && |bl| > 0
        && bl[0].0.pc >= 0
        && TtLkRec(rer, qm, code, nextinp, tl[0].0, (bl[0].0.pc + 1) as nat, true)
        && GmtTieOutside(re, bl[0].0, tl[0].1, S)
        && BlockedRepLkRec(rer, qm, re, code, inp, nextinp, crv, str, ov, S, tl[1..], bl[1..],
                           ncap, nlook, nquant))
  }

  /** processed ↔ seen pairing (landmine 2) — the ONE obligation genuinely
      shared with the old sim's structure. Mirrors `PIV.SeenInclusionRE`: every
      processed `(pc, b)` has its B-tree in `seen`, with the same stutter-chain
      escape hatch for the head being processed.

      RE-KEYED on the PLANTED CANONICAL form (2026-08-07): machine B runs the
      `TreeRepLkRE`-canonical trees, which are UNIQUE per `(pc, b)`
      (`TreeRepLkDetermRE`) — so a processed slot's recorded tree EQUALS any
      later head canonical at the same `(pc, b)`, and `LiftStepC`'s skip case
      closes: VM skips on `bpc_mem` ⟹ head tree is `Inseen` ⟹ `pts_skip`. */
  ghost predicate SeenRepLk(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                            treeseen: SS.SeenTrees, processed: AI.Bpcset,
                            current: Option<LT.Tree>, currentpc: nat) {
    // Verbatim mirror of `PIV.SeenInclusionRE` with `TreeRepLkRE` in place of
    // `TT.TreeThreadRE`: every processed `(pc, b)` either has its canonical
    // B-tree recorded in `treeseen`, or it is a gate/loop STUTTER whose chain
    // reaches the head currently being processed (`current` at `currentpc`).
    forall pc: nat, b: bool :: AI.bpc_mem(processed, pc, b) ==>
                                 (exists t: LT.Tree :: SS.Inseen(treeseen, t) && TreeRepLkRE(rer, qm, code, inp, t, pc, b))
                                 || (TT.StuttersRE(pc, code)
                                     && exists t: LT.Tree ::
                                       PIV.StutterChainTo(code, pc, currentpc) && current == Some(t)
                                       && TreeRepLkRE(rer, qm, code, inp, t, pc, b))
  }

  /** The `isblocked` dedup pairing — mirror of `PSM.IsblockedInclusionRE`
      with the canonical `TreeRepLkRE`: every pc the VM has already blocked
      this phase has its canonical tree memoized, so the `Consume`-dedup drop
      is a B `pts_skip` (at a `Consume` pc the canonical rule is
      flag-independent, so the recorded `b` transfers to the head's). */
  ghost predicate IsblockedRepLk(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code,
                                 inp: LC.Input, treeseen: SS.SeenTrees, isblocked: AI.pcset)
  {
    forall pc0: nat :: AI.pc_mem(isblocked, pc0) ==>
                         exists t: LT.Tree, b: bool ::
                           SS.Inseen(treeseen, t) && TreeRepLkRE(rer, qm, code, inp, t, pc0, b)
  }

  // ==========================================================================
  // THE FILLER'S WORKLIST — bodiless lemmas, in fill order.
  // ==========================================================================

  /** PER-ACTS functional determinism: `BoolTreeLk` is a function of
      `(acts, inp, b)`. Every head pins the tree's shape and recurses; the gate
      case is closed by `LkGateOk` pinning `tlk == ComputeTr(...)` (so both
      bodies agree) and the verdict `LkResult(...).Some?` being single-valued
      (so both take the same `LK`/`LKFail` branch). */
  least lemma BoolTreeLkDeterm(rer: LW.RegExpRecord, acts: LS.Actions, inp: LC.Input,
                               b: BS.LoopBool, t1: LT.Tree, t2: LT.Tree)
    requires EL.BoolTreeLk(rer, acts, inp, b, t1)
    requires EL.BoolTreeLk(rer, acts, inp, b, t2)
    ensures t1 == t2
  {
    if |acts| == 0 {
    } else {
      var cont := acts[1..];
      match acts[0]
      case Acheck(strcheck) =>
        if b == BS.CanExit {
          match t1 { case Progress(c1) => match t2 { case Progress(c2) =>
                BoolTreeLkDeterm(rer, cont, inp, BS.CanExit, c1, c2); case _ => } case _ => }
        }
      case Aclose(gid) =>
        match t1 { case GroupActionT(g1, c1) => match t2 { case GroupActionT(g2, c2) =>
              BoolTreeLkDeterm(rer, cont, inp, b, c1, c2); case _ => } case _ => }
      case Areg(r) =>
        match r
        case Epsilon => BoolTreeLkDeterm(rer, cont, inp, b, t1, t2);
        case Character(cd) =>
          match LC.ReadChar(rer, cd, inp, WP.Forward) {
            case None =>
            case Some(pair) =>
              match t1 { case Read(cc1, c1) => match t2 { case Read(cc2, c2) =>
                    BoolTreeLkDeterm(rer, cont, pair.1, BS.CanExit, c1, c2); case _ => } case _ => }
          }
        case Disjunction(r1, r2) =>
          match t1 { case Choice(a1, b1t) => match t2 { case Choice(a2, b2t) =>
                BoolTreeLkDeterm(rer, [LS.Areg(r1)] + cont, inp, b, a1, a2);
                BoolTreeLkDeterm(rer, [LS.Areg(r2)] + cont, inp, b, b1t, b2t); case _ => } case _ => }
        case Sequence(r1, r2) =>
          BoolTreeLkDeterm(rer, [LS.Areg(r1), LS.Areg(r2)] + cont, inp, b, t1, t2);
        case Quantified(greedy, min, delta, r1) =>
          var gidl := L.DefGroups(r1);
          if min > 0 {
            var q1 := L.Quantified(greedy, min - 1, delta, r1);
            match t1 { case GroupActionT(g1, c1) => match t2 { case GroupActionT(g2, c2) =>
                  BoolTreeLkDeterm(rer, [LS.Areg(r1), LS.Areg(q1)] + cont, inp, b, c1, c2); case _ => } case _ => }
          } else if delta == LN.NN(0) {
            BoolTreeLkDeterm(rer, cont, inp, b, t1, t2);
          } else {
            var qn := L.Quantified(greedy, 0, FS.NoiPred(delta), r1);
            var iacts := [LS.Areg(r1), LS.Acheck(inp), LS.Areg(qn)] + cont;
            match t1 {
              case Choice(a1, b1t) =>
                match t2 {
                  case Choice(a2, b2t) =>
                    var it1 := if greedy then a1 else b1t;  var sk1 := if greedy then b1t else a1;
                    var it2 := if greedy then a2 else b2t;  var sk2 := if greedy then b2t else a2;
                    match it1 {
                      case GroupActionT(g1, ti1) =>
                        match it2 {
                          case GroupActionT(g2, ti2) =>
                            BoolTreeLkDeterm(rer, iacts, inp, BS.CannotExit, ti1, ti2);
                            BoolTreeLkDeterm(rer, cont, inp, b, sk1, sk2);
                          case _ =>
                        }
                      case _ =>
                    }
                  case _ =>
                }
              case _ =>
            }
          }
        case Group(gid, r1) =>
          match t1 { case GroupActionT(g1, c1) => match t2 { case GroupActionT(g2, c2) =>
                BoolTreeLkDeterm(rer, [LS.Areg(r1), LS.Aclose(gid)] + cont, inp, b, c1, c2); case _ => } case _ => }
        case AnchorR(a) =>
          if LS.AnchorSatisfied(rer, a, inp) {
            match t1 { case AnchorPass(a1, c1) => match t2 { case AnchorPass(a2, c2) =>
                  BoolTreeLkDeterm(rer, cont, inp, b, c1, c2); case _ => } case _ => }
          }
        case LookaroundR(lk, r1) =>
          // LkGateOk pins tlk == ComputeTr(rer,[Areg(r1)],inp,Empty,LkDir(lk)) on BOTH
          // sides; its verdict LkResult(lk,tlk,Empty,inp).Some? is single-valued.
          var tlkc := LFU.ComputeTr(rer, [LS.Areg(r1)], inp, LG.Empty, L.LkDir(lk));
          match t1 {
            case LK(l1, k1, c1) =>
              assert k1 == tlkc;
              match t2 {
                case LK(l2, k2, c2) =>
                  assert k2 == tlkc;
                  BoolTreeLkDeterm(rer, cont, inp, b, c1, c2);
                case LKFail(l2, k2) =>
                  assert k2 == tlkc;   // both verdicts read LkResult(lk,tlkc,Empty,inp).Some?
                  assert false;
                case _ =>
              }
            case LKFail(l1, k1) =>
              assert k1 == tlkc;
              match t2 {
                case LK(l2, k2, c2) => assert k2 == tlkc; assert false;
                case LKFail(l2, k2) => assert k2 == tlkc;
                case _ =>
              }
            case _ =>
          }
        case Backreference(_) =>
    }
  }

  // ==========================================================================
  // ERASED-CANONICAL LK TREES — the determinism layer for the seen/skip pairing.
  //
  // WHY (2026-08-05): `TtLkSameTree` as originally stated is FALSE. At a
  // do-while's backward fork BOTH `[Areg(star)]+cont` (the loop-view `NfaRepL`
  // disjunct) and `[Acheck(s), Areg(star)]+cont` (`ActionRepL`'s zero-width
  // Acheck at a `BackForkAt` pc, strcheck unconstrained) are
  // `ActionsRepL`-representable at the same pc, and their `BoolTreeLk` trees
  // differ by exactly a `Progress` wrapper — the per-`(pc, ea)` tree is NOT
  // unique. This is real machine behavior, not a proof artifact: in `(a+)+` a
  // first-outer-iteration thread and a re-entered thread reach the same inner
  // fork in the same ε-phase carrying trees that differ by a planted
  // `Progress`, so B's exact-tree-keyed `pts_skip` cannot fire where the VM's
  // `(pc, ea)`-keyed skip does. Machine-A canonicalized by PLANTING the guard
  // (`ActionsTreeRepFRE`'s tr_plus construction) and running the machine on
  // canonical `TreeRepRE` trees; machine B runs the RAW spec tree, so the fix
  // here is the QUOTIENT: `Progress` is leaf-transparent
  // (`TreeLeaves(Progress(t)) == TreeLeaves(t)`, Tree.dfy), so erase it —
  // key B's memoization on `ProgErase`d trees and prove walk confluence
  // MODULO erasure. `ETreeRepLk` is the erased canonical form: a least
  // predicate keyed on `(code, pc, inp, b)` alone (mirror of `TR.TreeRepRE`
  // with LK/LKFail nodes KEPT at the gates, pinned functionally by
  // `ComputeTr`/`LkResult`, and the two Progress-producing rules turned into
  // stutters). Its determinism (`ETreeRepLkDeterm`) is a least lemma —
  // termination by ordinal induction, no hand-rolled measure.
  // ==========================================================================

  // `ProgErase` (the quotient map — erase every `Progress` guard) lives in
  // `CE` (CheckErase.dfy) beside `PSize`/`BoolCheckInsert`, whose strengthened
  // ensures `CE.ProgErase(tstar) == CE.ProgErase(t)` records that check insertion is
  // the IDENTITY on erased trees.

  /** `Progress` is leaf-transparent, so erasure preserves the leaf sequence —
      the fact that keeps an erased seen-key SOUND for first-leaf memoization
      (skipping a tree whose erasure was already processed skips equal
      leaves). */
  lemma ProgEraseLeavesEq(t: LT.Tree, gm: LG.GroupMap, inp: LC.Input, dir: WP.Direction)
    ensures LT.TreeLeaves(CE.ProgErase(t), gm, inp, dir) == LT.TreeLeaves(t, gm, inp, dir)
    decreases t
  {
    match t
    case Mismatch =>
    case Match =>
    case Choice(t1, t2) =>
      ProgEraseLeavesEq(t1, gm, inp, dir);
      ProgEraseLeavesEq(t2, gm, inp, dir);
    case Read(c, t1) =>
      ProgEraseLeavesEq(t1, gm, LC.AdvanceInputP(inp, dir), dir);
    case ReadBackRef(s, t1) =>
      ProgEraseLeavesEq(t1, gm, LC.AdvanceInputN(inp, |s|, dir), dir);
    case Progress(t1) =>
      ProgEraseLeavesEq(t1, gm, inp, dir);
    case AnchorPass(a, t1) =>
      ProgEraseLeavesEq(t1, gm, inp, dir);
    case GroupActionT(g, t1) =>
      ProgEraseLeavesEq(t1, LG.GMUpdate(g, LC.Idx(inp), gm), inp, dir);
    case LK(lk, tlk, t1) =>
      ProgEraseLeavesEq(tlk, gm, inp, L.LkDir(lk));
      var sub := LT.TreeLeaves(tlk, gm, inp, L.LkDir(lk));
      if L.Positivity(lk) {
        if |sub| > 0 { ProgEraseLeavesEq(t1, sub[0].1, inp, dir); }
      } else {
        if |sub| == 0 { ProgEraseLeavesEq(t1, gm, inp, dir); }
      }
    case LKFail(lk, tlk) =>
  }

  /** The ERASED canonical LK tree at `(code, pc, inp, b)` — `TR.TreeRepRE`'s
      rule set with (i) LK/LKFail nodes KEPT at the oracle gates, pinned
      FUNCTIONALLY by `ComputeTr`/`LkResult` (`LkGateOk`'s shape — no oracle
      consultation, no acts existential), and (ii) the two Progress-producing
      rules (`tr_progress` at EndLoop, the guard of `tr_plus` at a backward
      fork) turned into STUTTERS. This is the image of every `BoolTreeLk` walk
      tree under `ProgErase`, and it is a FUNCTION of `(pc, inp, b)`
      (`ETreeRepLkDeterm`). The gate cases are instruction-first with no
      existential over `lid`, per `TreeRepRE`'s hard-won style note. */
  least predicate ETreeRepLk(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                             t: LT.Tree, pc: nat, b: bool)
  {
    // e_match
    (NR.GetPcRE(code, pc) == Some(RB.Accept) && t == LT.Match)
    // e_jmp
    || (exists nextpc: int :: NR.GetPcRE(code, pc) == Some(RB.Jmp(nextpc)) && nextpc >= 0
                              && ETreeRepLk(rer, qm, code, inp, t, nextpc as nat, b))
    // e_begin
    || (NR.GetPcRE(code, pc) == Some(RB.BeginLoop)
        && ETreeRepLk(rer, qm, code, inp, t, pc + 1, false))
    // e_reset
    || (t.GroupActionT? && t.g.Reset? && exists qid: int ::
          NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(qid, false))
          && qid in qm.quants && qm.quants[qid] == t.g.gl
          && ETreeRepLk(rer, qm, code, inp, t.t, pc + 1, b))
    // e_choice (forward forks)
    || (t.Choice? && exists pcl: int, pcr: int ::
          NR.GetPcRE(code, pc) == Some(RB.Fork(pcl, pcr)) && pcl >= 0 && pcr >= 0
          && pcl as nat > pc && pcr as nat > pc
          && ETreeRepLk(rer, qm, code, inp, t.t1, pcl as nat, b)
          && ETreeRepLk(rer, qm, code, inp, t.t2, pcr as nat, b))
    // e_plus — tr_plus with the Progress guard ERASED: a BARE Choice at the
    // do-while's backward fork, representable only at b == true (like tr_plus)
    || (t.Choice? && b == true && exists pcl: int, pcr: int ::
          NR.GetPcRE(code, pc) == Some(RB.Fork(pcl, pcr)) && pcl >= 0 && pcr >= 0
          && (pcl as nat <= pc || pcr as nat <= pc)
          && ETreeRepLk(rer, qm, code, inp, t.t1, pcl as nat, true)
          && ETreeRepLk(rer, qm, code, inp, t.t2, pcr as nat, true))
    // e_plusfail
    || (t == LT.Mismatch && b == false && exists pcl: int, pcr: int ::
          NR.GetPcRE(code, pc) == Some(RB.Fork(pcl, pcr)) && pcl >= 0 && pcr >= 0
          && (pcl as nat <= pc || pcr as nat <= pc))
    // e_read
    || (t.Read? && exists ce, nextinp ::
          NR.GetPcRE(code, pc) == Some(RB.Consume(ce))
          && AR.ReadCharE(ce, inp) == Some((t.c, nextinp))
          && ETreeRepLk(rer, qm, code, nextinp, t.t, pc + 1, true))
    // e_progress — tr_progress ERASED to a stutter (EndLoop falls through)
    || (b == true && NR.GetPcRE(code, pc) == Some(RB.EndLoop)
        && ETreeRepLk(rer, qm, code, inp, t, pc + 1, true))
    // e_progressfail
    || (t == LT.Mismatch && b == false && NR.GetPcRE(code, pc) == Some(RB.EndLoop))
    // e_open
    || (t.GroupActionT? && t.g.Open?
        && NR.GetPcRE(code, pc) == Some(RB.SetRegisterToCP(CP.start_reg(t.g.g as int)))
        && ETreeRepLk(rer, qm, code, inp, t.t, pc + 1, b))
    // e_close
    || (t.GroupActionT? && t.g.Close?
        && NR.GetPcRE(code, pc) == Some(RB.SetRegisterToCP(CP.end_reg(t.g.g as int)))
        && ETreeRepLk(rer, qm, code, inp, t.t, pc + 1, b))
    // e_anchorpass (Linden-side satisfaction; the anchor is pinned by the
    // instruction through `TrAnchor`)
    || (t.AnchorPass? && exists a: R.anchor ::
          NR.GetPcRE(code, pc) == Some(RB.AnchorAssertion(a))
          && T.TrAnchor(a) == t.a
          && LS.AnchorSatisfied(rer, t.a, inp)
          && ETreeRepLk(rer, qm, code, inp, t.t, pc + 1, b))
    // e_anchorfail
    || (t == LT.Mismatch && exists a: R.anchor ::
          NR.GetPcRE(code, pc) == Some(RB.AnchorAssertion(a))
          && !LS.AnchorSatisfied(rer, T.TrAnchor(a), inp))
    // e_readfail
    || (t == LT.Mismatch && exists ce ::
          NR.GetPcRE(code, pc) == Some(RB.Consume(ce)) && AR.ReadCharE(ce, inp) == None)
    // e_lk / e_lkfail — the gate, LK nodes KEPT. The body tree and verdict are
    // functional in `(lk, r1, inp)`; the node stores the ERASED body image.
    || (match NR.GetPcRE(code, pc)
        case Some(CheckOracle(lid)) =>
          lid in qm.looks
          && var lk := qm.looks[lid].0;
          var r1 := qm.looks[lid].1;
          var tlk := LFU.ComputeTr(rer, [LS.Areg(r1)], inp, LG.Empty, L.LkDir(lk));
          if LS.LkResult(lk, tlk, LG.Empty, inp).Some?
          then t.LK? && t.lk == lk && t.tlk == CE.ProgErase(tlk)
               && ETreeRepLk(rer, qm, code, inp, t.t, pc + 1, b)
          else t == LT.LKFail(lk, CE.ProgErase(tlk))
        case Some(NegCheckOracle(lid)) =>
          lid in qm.looks
          && var lk := qm.looks[lid].0;
          var r1 := qm.looks[lid].1;
          var tlk := LFU.ComputeTr(rer, [LS.Areg(r1)], inp, LG.Empty, L.LkDir(lk));
          if LS.LkResult(lk, tlk, LG.Empty, inp).Some?
          then t.LK? && t.lk == lk && t.tlk == CE.ProgErase(tlk)
               && ETreeRepLk(rer, qm, code, inp, t.t, pc + 1, b)
          else t == LT.LKFail(lk, CE.ProgErase(tlk))
        case _ => false)
  }

  /** Determinism of the erased canonical form: at a fixed `(pc, inp, b)` the
      represented tree is unique — the quotient replacement for the FALSE
      exact-tree `TtLkSameTree`. Mirror of `TR.TreeRepDetermRE` (least-lemma
      ordinal induction; `qm` pins the Reset payload, `SetRegisterToCP` parity
      separates Open from Close); the erased stutters recurse on the SAME
      trees, and the gate cases close functionally (both sides' `tlk` and
      verdict are pinned by `ComputeTr`/`LkResult` at the instruction's
      table entry). */
  least lemma ETreeRepLkDeterm(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                               t1: LT.Tree, t2: LT.Tree, pc: nat, b: bool)
    requires ETreeRepLk(rer, qm, code, inp, t1, pc, b)
    requires ETreeRepLk(rer, qm, code, inp, t2, pc, b)
    ensures t1 == t2
  {
    match NR.GetPcRE(code, pc)
    case Some(Accept) =>            // both e_match
    case Some(Jmp(np)) =>           // both e_jmp
      ETreeRepLkDeterm(rer, qm, code, inp, t1, t2, np as nat, b);
    case Some(BeginLoop) =>         // both e_begin
      ETreeRepLkDeterm(rer, qm, code, inp, t1, t2, pc + 1, false);
    case Some(SetQuantToClock(qid, bb)) =>  // both e_reset (only bb == false has a rule)
      match t1 {
        case GroupActionT(g1, tc1) =>
          match t2 {
            case GroupActionT(g2, tc2) =>
              assert g1 == LG.Reset(qm.quants[qid]) && g2 == LG.Reset(qm.quants[qid]);
              ETreeRepLkDeterm(rer, qm, code, inp, tc1, tc2, pc + 1, b);
            case _ =>
          }
        case _ =>
      }
    case Some(Fork(pl, pr)) =>
      if pl >= 0 && pr >= 0 && pl as nat > pc && pr as nat > pc {
        // forward fork: both e_choice
        match t1 {
          case Choice(ta1, tb1) =>
            match t2 {
              case Choice(ta2, tb2) =>
                ETreeRepLkDeterm(rer, qm, code, inp, ta1, ta2, pl as nat, b);
                ETreeRepLkDeterm(rer, qm, code, inp, tb1, tb2, pr as nat, b);
              case _ =>
            }
          case _ =>
        }
      } else if !b {
        // backward-arm fork at b == false: both e_plusfail (Mismatch)
      } else {
        // backward-arm fork at b == true: both e_plus (bare Choice — the
        // erased guard makes first- and re-traversal shapes IDENTICAL, which
        // is the entire point of the quotient)
        match t1 {
          case Choice(ta1, tb1) =>
            match t2 {
              case Choice(ta2, tb2) =>
                ETreeRepLkDeterm(rer, qm, code, inp, ta1, ta2, pl as nat, true);
                ETreeRepLkDeterm(rer, qm, code, inp, tb1, tb2, pr as nat, true);
              case _ =>
            }
          case _ =>
        }
      }
    case Some(Consume(ce)) =>       // e_read (Some) or e_readfail (None)
      match AR.ReadCharE(ce, inp) {
        case None =>                // both Mismatch
        case Some(pair) =>
          match t1 {
            case Read(c1, tc1) =>
              match t2 {
                case Read(c2, tc2) =>
                  ETreeRepLkDeterm(rer, qm, code, pair.1, tc1, tc2, pc + 1, true);
                case _ =>
              }
            case _ =>
          }
      }
    case Some(EndLoop) =>           // e_progress stutter (b) or e_progressfail (!b)
      if b {
        ETreeRepLkDeterm(rer, qm, code, inp, t1, t2, pc + 1, true);
      }
    case Some(SetRegisterToCP(reg)) =>  // e_open (even reg) xor e_close (odd reg)
      match t1 {
        case GroupActionT(g1, tc1) =>
          match t2 {
            case GroupActionT(g2, tc2) =>
              assert g1.Open? ==> reg == 2 * (g1.g as int);
              assert g1.Close? ==> reg == 2 * (g1.g as int) + 1;
              assert g2.Open? ==> reg == 2 * (g2.g as int);
              assert g2.Close? ==> reg == 2 * (g2.g as int) + 1;
              assert g1 == g2;
              ETreeRepLkDeterm(rer, qm, code, inp, tc1, tc2, pc + 1, b);
            case _ =>
          }
        case _ =>
      }
    case Some(AnchorAssertion(a)) =>  // e_anchorpass (satisfied) or e_anchorfail
      if LS.AnchorSatisfied(rer, T.TrAnchor(a), inp) {
        match t1 {
          case AnchorPass(a1, tc1) =>
            match t2 {
              case AnchorPass(a2, tc2) =>
                ETreeRepLkDeterm(rer, qm, code, inp, tc1, tc2, pc + 1, b);
              case _ =>
            }
          case _ =>
        }
      }
    case Some(CheckOracle(lid)) =>  // e_lk (verdict Some) or e_lkfail — functional split
      if lid in qm.looks {
        var lk := qm.looks[lid].0;
        var r1 := qm.looks[lid].1;
        var tlk := LFU.ComputeTr(rer, [LS.Areg(r1)], inp, LG.Empty, L.LkDir(lk));
        if LS.LkResult(lk, tlk, LG.Empty, inp).Some? {
          match t1 {
            case LK(l1, k1, tc1) =>
              match t2 {
                case LK(l2, k2, tc2) =>
                  ETreeRepLkDeterm(rer, qm, code, inp, tc1, tc2, pc + 1, b);
                case _ =>
              }
            case _ =>
          }
        }
        // verdict None: both == LKFail(lk, CE.ProgErase(tlk)) directly
      }
    case Some(NegCheckOracle(lid)) =>
      if lid in qm.looks {
        var lk := qm.looks[lid].0;
        var r1 := qm.looks[lid].1;
        var tlk := LFU.ComputeTr(rer, [LS.Areg(r1)], inp, LG.Empty, L.LkDir(lk));
        if LS.LkResult(lk, tlk, LG.Empty, inp).Some? {
          match t1 {
            case LK(l1, k1, tc1) =>
              match t2 {
                case LK(l2, k2, tc2) =>
                  ETreeRepLkDeterm(rer, qm, code, inp, tc1, tc2, pc + 1, b);
                case _ =>
              }
            case _ =>
          }
        }
      }
    case Some(_) =>                 // WriteOracle/CheckNullable/Fail: no rule — vacuous
    case None =>                    // vacuous
  }

  /** The PLANTED canonical LK tree at `(code, pc, inp, b)` — `TR.TreeRepRE`'s
      rule set verbatim (tr_progress/tr_plus KEEP their `Progress` guards) with
      LK/LKFail nodes KEPT at the oracle gates, pinned functionally. This is
      the tree machine B actually RUNS (unique per `(pc, ea)` by
      `TreeRepLkDetermRE`, AND stutter-discriminating: at an EndLoop pc the
      tree is `Progress(x)`, at pc+1 it is `x` — matching the VM's distinct
      `(pc, ea)` memo entries, which the ERASED form cannot: erasure conflates
      a processed `Progress(x)` with its queued child `x` and would make B
      skip work the VM performs). `ETreeRepLk` above remains as the erased
      image; `ProgErase` of a planted tree relates it to the raw spec tree. */
  least predicate TreeRepLkRE(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                              t: LT.Tree, pc: nat, b: bool)
  {
    // tr_match
    (NR.GetPcRE(code, pc) == Some(RB.Accept) && t == LT.Match)
    // tr_jmp
    || (exists nextpc: int :: NR.GetPcRE(code, pc) == Some(RB.Jmp(nextpc)) && nextpc >= 0
                              && TreeRepLkRE(rer, qm, code, inp, t, nextpc as nat, b))
    // tr_begin
    || (NR.GetPcRE(code, pc) == Some(RB.BeginLoop)
        && TreeRepLkRE(rer, qm, code, inp, t, pc + 1, false))
    // tr_reset
    || (t.GroupActionT? && t.g.Reset? && exists qid: int ::
          NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(qid, false))
          && qid in qm.quants && qm.quants[qid] == t.g.gl
          && TreeRepLkRE(rer, qm, code, inp, t.t, pc + 1, b))
    // tr_choice (forward forks)
    || (t.Choice? && exists pcl: int, pcr: int ::
          NR.GetPcRE(code, pc) == Some(RB.Fork(pcl, pcr)) && pcl >= 0 && pcr >= 0
          && pcl as nat > pc && pcr as nat > pc
          && TreeRepLkRE(rer, qm, code, inp, t.t1, pcl as nat, b)
          && TreeRepLkRE(rer, qm, code, inp, t.t2, pcr as nat, b))
    // tr_plus (the guard KEPT: consumed with the Choice at the backward fork)
    || (t.Progress? && t.t.Choice? && b == true && exists pcl: int, pcr: int ::
          NR.GetPcRE(code, pc) == Some(RB.Fork(pcl, pcr)) && pcl >= 0 && pcr >= 0
          && (pcl as nat <= pc || pcr as nat <= pc)
          && TreeRepLkRE(rer, qm, code, inp, t.t.t1, pcl as nat, true)
          && TreeRepLkRE(rer, qm, code, inp, t.t.t2, pcr as nat, true))
    // tr_plusfail
    || (t == LT.Mismatch && b == false && exists pcl: int, pcr: int ::
          NR.GetPcRE(code, pc) == Some(RB.Fork(pcl, pcr)) && pcl >= 0 && pcr >= 0
          && (pcl as nat <= pc || pcr as nat <= pc))
    // tr_read
    || (t.Read? && exists ce, nextinp ::
          NR.GetPcRE(code, pc) == Some(RB.Consume(ce))
          && AR.ReadCharE(ce, inp) == Some((t.c, nextinp))
          && TreeRepLkRE(rer, qm, code, nextinp, t.t, pc + 1, true))
    // tr_progress (the guard KEPT: EndLoop falls through)
    || (t.Progress? && b == true && NR.GetPcRE(code, pc) == Some(RB.EndLoop)
        && TreeRepLkRE(rer, qm, code, inp, t.t, pc + 1, true))
    // tr_progressfail
    || (t == LT.Mismatch && b == false && NR.GetPcRE(code, pc) == Some(RB.EndLoop))
    // tr_open
    || (t.GroupActionT? && t.g.Open?
        && NR.GetPcRE(code, pc) == Some(RB.SetRegisterToCP(CP.start_reg(t.g.g as int)))
        && TreeRepLkRE(rer, qm, code, inp, t.t, pc + 1, b))
    // tr_close
    || (t.GroupActionT? && t.g.Close?
        && NR.GetPcRE(code, pc) == Some(RB.SetRegisterToCP(CP.end_reg(t.g.g as int)))
        && TreeRepLkRE(rer, qm, code, inp, t.t, pc + 1, b))
    // tr_anchorpass
    || (t.AnchorPass? && exists a: R.anchor ::
          NR.GetPcRE(code, pc) == Some(RB.AnchorAssertion(a))
          && T.TrAnchor(a) == t.a
          && LS.AnchorSatisfied(rer, t.a, inp)
          && TreeRepLkRE(rer, qm, code, inp, t.t, pc + 1, b))
    // tr_anchorfail
    || (t == LT.Mismatch && exists a: R.anchor ::
          NR.GetPcRE(code, pc) == Some(RB.AnchorAssertion(a))
          && !LS.AnchorSatisfied(rer, T.TrAnchor(a), inp))
    // tr_readfail
    || (t == LT.Mismatch && exists ce ::
          NR.GetPcRE(code, pc) == Some(RB.Consume(ce)) && AR.ReadCharE(ce, inp) == None)
    // tr_lk / tr_lkfail — the gate, LK nodes KEPT with the RAW functional body
    // (what machine B's LkResult merge evaluates)
    || (match NR.GetPcRE(code, pc)
        case Some(CheckOracle(lid)) =>
          lid in qm.looks
          && var lk := qm.looks[lid].0;
          var r1 := qm.looks[lid].1;
          var tlk := LFU.ComputeTr(rer, [LS.Areg(r1)], inp, LG.Empty, L.LkDir(lk));
          if LS.LkResult(lk, tlk, LG.Empty, inp).Some?
          then t.LK? && t.lk == lk && t.tlk == tlk
               && TreeRepLkRE(rer, qm, code, inp, t.t, pc + 1, b)
          else t == LT.LKFail(lk, tlk)
        case Some(NegCheckOracle(lid)) =>
          lid in qm.looks
          && var lk := qm.looks[lid].0;
          var r1 := qm.looks[lid].1;
          var tlk := LFU.ComputeTr(rer, [LS.Areg(r1)], inp, LG.Empty, L.LkDir(lk));
          if LS.LkResult(lk, tlk, LG.Empty, inp).Some?
          then t.LK? && t.lk == lk && t.tlk == tlk
               && TreeRepLkRE(rer, qm, code, inp, t.t, pc + 1, b)
          else t == LT.LKFail(lk, tlk)
        case _ => false)
  }

  /** Determinism of the PLANTED canonical form: at a fixed `(pc, inp, b)` the
      represented tree is unique — what closes machine B's EXACT-tree skip in
      lockstep with the VM's `(pc, ea)` skip, with `PikeTreeLk` unchanged.
      Mirror of `TR.TreeRepDetermRE` extended with the functional gate. */
  least lemma TreeRepLkDetermRE(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                                t1: LT.Tree, t2: LT.Tree, pc: nat, b: bool)
    requires TreeRepLkRE(rer, qm, code, inp, t1, pc, b)
    requires TreeRepLkRE(rer, qm, code, inp, t2, pc, b)
    ensures t1 == t2
  {
    match NR.GetPcRE(code, pc)
    case Some(Accept) =>            // both tr_match
    case Some(Jmp(np)) =>           // both tr_jmp
      TreeRepLkDetermRE(rer, qm, code, inp, t1, t2, np as nat, b);
    case Some(BeginLoop) =>         // both tr_begin
      TreeRepLkDetermRE(rer, qm, code, inp, t1, t2, pc + 1, false);
    case Some(SetQuantToClock(qid, bb)) =>  // both tr_reset
      match t1 {
        case GroupActionT(g1, tc1) =>
          match t2 {
            case GroupActionT(g2, tc2) =>
              assert g1 == LG.Reset(qm.quants[qid]) && g2 == LG.Reset(qm.quants[qid]);
              TreeRepLkDetermRE(rer, qm, code, inp, tc1, tc2, pc + 1, b);
            case _ =>
          }
        case _ =>
      }
    case Some(Fork(pl, pr)) =>
      if pl >= 0 && pr >= 0 && pl as nat > pc && pr as nat > pc {
        // forward fork: both tr_choice
        match t1 {
          case Choice(ta1, tb1) =>
            match t2 {
              case Choice(ta2, tb2) =>
                TreeRepLkDetermRE(rer, qm, code, inp, ta1, ta2, pl as nat, b);
                TreeRepLkDetermRE(rer, qm, code, inp, tb1, tb2, pr as nat, b);
              case _ =>
            }
          case _ =>
        }
      } else if !b {
        // backward-arm fork at b == false: both tr_plusfail (Mismatch)
      } else {
        // backward-arm fork: both tr_plus (Progress(Choice))
        match t1 {
          case Progress(tc1) =>
            match t2 {
              case Progress(tc2) =>
                match tc1 {
                  case Choice(ta1, tb1) =>
                    match tc2 {
                      case Choice(ta2, tb2) =>
                        TreeRepLkDetermRE(rer, qm, code, inp, ta1, ta2, pl as nat, true);
                        TreeRepLkDetermRE(rer, qm, code, inp, tb1, tb2, pr as nat, true);
                      case _ =>
                    }
                  case _ =>
                }
              case _ =>
            }
          case _ =>
        }
      }
    case Some(Consume(ce)) =>       // tr_read (Some) or tr_readfail (None)
      match AR.ReadCharE(ce, inp) {
        case None =>                // both Mismatch
        case Some(pair) =>
          match t1 {
            case Read(c1, tc1) =>
              match t2 {
                case Read(c2, tc2) =>
                  TreeRepLkDetermRE(rer, qm, code, pair.1, tc1, tc2, pc + 1, true);
                case _ =>
              }
            case _ =>
          }
      }
    case Some(EndLoop) =>           // tr_progress (b) or tr_progressfail (!b)
      if b {
        match t1 {
          case Progress(tc1) =>
            match t2 {
              case Progress(tc2) =>
                TreeRepLkDetermRE(rer, qm, code, inp, tc1, tc2, pc + 1, true);
              case _ =>
            }
          case _ =>
        }
      }
    case Some(SetRegisterToCP(reg)) =>  // tr_open (even reg) xor tr_close (odd reg)
      match t1 {
        case GroupActionT(g1, tc1) =>
          match t2 {
            case GroupActionT(g2, tc2) =>
              assert g1.Open? ==> reg == 2 * (g1.g as int);
              assert g1.Close? ==> reg == 2 * (g1.g as int) + 1;
              assert g2.Open? ==> reg == 2 * (g2.g as int);
              assert g2.Close? ==> reg == 2 * (g2.g as int) + 1;
              assert g1 == g2;
              TreeRepLkDetermRE(rer, qm, code, inp, tc1, tc2, pc + 1, b);
            case _ =>
          }
        case _ =>
      }
    case Some(AnchorAssertion(a)) =>  // tr_anchorpass (satisfied) or tr_anchorfail
      if LS.AnchorSatisfied(rer, T.TrAnchor(a), inp) {
        match t1 {
          case AnchorPass(a1, tc1) =>
            match t2 {
              case AnchorPass(a2, tc2) =>
                TreeRepLkDetermRE(rer, qm, code, inp, tc1, tc2, pc + 1, b);
              case _ =>
            }
          case _ =>
        }
      }
    case Some(CheckOracle(lid)) =>  // tr_lk (verdict Some) or tr_lkfail — functional split
      if lid in qm.looks {
        var lk := qm.looks[lid].0;
        var r1 := qm.looks[lid].1;
        var tlk := LFU.ComputeTr(rer, [LS.Areg(r1)], inp, LG.Empty, L.LkDir(lk));
        if LS.LkResult(lk, tlk, LG.Empty, inp).Some? {
          match t1 {
            case LK(l1, k1, tc1) =>
              match t2 {
                case LK(l2, k2, tc2) =>
                  TreeRepLkDetermRE(rer, qm, code, inp, tc1, tc2, pc + 1, b);
                case _ =>
              }
            case _ =>
          }
        }
      }
    case Some(NegCheckOracle(lid)) =>
      if lid in qm.looks {
        var lk := qm.looks[lid].0;
        var r1 := qm.looks[lid].1;
        var tlk := LFU.ComputeTr(rer, [LS.Areg(r1)], inp, LG.Empty, L.LkDir(lk));
        if LS.LkResult(lk, tlk, LG.Empty, inp).Some? {
          match t1 {
            case LK(l1, k1, tc1) =>
              match t2 {
                case LK(l2, k2, tc2) =>
                  TreeRepLkDetermRE(rer, qm, code, inp, tc1, tc2, pc + 1, b);
                case _ =>
              }
            case _ =>
          }
        }
      }
    case Some(_) =>                 // WriteOracle/CheckNullable/Fail: no rule — vacuous
    case None =>                    // vacuous
  }

  // ---- per-instruction CANONICAL inversions (the `TreeRepLkRE`-At* tier) ----
  //
  // `LiftStepC`'s per-instruction cases use these to read off the canonical
  // head's shape and re-establish the canonical tie for the children — the
  // rules are instruction-gated, so at a pinned instruction exactly one rule
  // family can fire (the same discrimination the determinism lemma performs).
  // Fork arms come FREE here (tr_choice/tr_plus carry both arms) — the old
  // "Fork branches hardest" problem does not exist at the canonical level.

  lemma TreeRepLkREAtAccept(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                            t: LT.Tree, pc: nat, b: bool)
    requires TreeRepLkRE(rer, qm, code, inp, t, pc, b)
    requires NR.GetPcRE(code, pc) == Some(RB.Accept)
    ensures t == LT.Match
  { }

  lemma TreeRepLkREAtJmp(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                         t: LT.Tree, pc: nat, b: bool, x: int)
    requires TreeRepLkRE(rer, qm, code, inp, t, pc, b)
    requires NR.GetPcRE(code, pc) == Some(RB.Jmp(x))
    ensures x >= 0 && TreeRepLkRE(rer, qm, code, inp, t, x as nat, b)
  { }

  lemma TreeRepLkREAtBeginLoop(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                               t: LT.Tree, pc: nat, b: bool)
    requires TreeRepLkRE(rer, qm, code, inp, t, pc, b)
    requires NR.GetPcRE(code, pc) == Some(RB.BeginLoop)
    ensures TreeRepLkRE(rer, qm, code, inp, t, pc + 1, false)
  { }

  lemma TreeRepLkREAtSetQuant(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                              t: LT.Tree, pc: nat, b: bool, qid: int, bb: bool)
    requires TreeRepLkRE(rer, qm, code, inp, t, pc, b)
    requires NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(qid, bb))
    ensures !bb && qid in qm.quants
    ensures t.GroupActionT? && t.g == LG.Reset(qm.quants[qid])
    ensures TreeRepLkRE(rer, qm, code, inp, t.t, pc + 1, b)
  { }

  lemma TreeRepLkREAtFork(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                          t: LT.Tree, pc: nat, b: bool, x: int, y: int)
    requires TreeRepLkRE(rer, qm, code, inp, t, pc, b)
    requires NR.GetPcRE(code, pc) == Some(RB.Fork(x, y))
    ensures x >= 0 && y >= 0
    ensures x as nat > pc && y as nat > pc ==>       // forward fork: tr_choice
              t.Choice?
              && TreeRepLkRE(rer, qm, code, inp, t.t1, x as nat, b)
              && TreeRepLkRE(rer, qm, code, inp, t.t2, y as nat, b)
    ensures (x as nat <= pc || y as nat <= pc) && b ==>   // backward fork: tr_plus
              t.Progress? && t.t.Choice?
              && TreeRepLkRE(rer, qm, code, inp, t.t.t1, x as nat, true)
              && TreeRepLkRE(rer, qm, code, inp, t.t.t2, y as nat, true)
    ensures (x as nat <= pc || y as nat <= pc) && !b ==>  // tr_plusfail
              t == LT.Mismatch
  { }

  lemma TreeRepLkREAtConsume(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                             t: LT.Tree, pc: nat, b: bool, ce: RC.char_expectation)
    requires TreeRepLkRE(rer, qm, code, inp, t, pc, b)
    requires NR.GetPcRE(code, pc) == Some(RB.Consume(ce))
    ensures AR.ReadCharE(ce, inp).None? ==> t == LT.Mismatch
    ensures AR.ReadCharE(ce, inp).Some? ==>
              t.Read? && t.c == AR.ReadCharE(ce, inp).value.0
              && TreeRepLkRE(rer, qm, code, AR.ReadCharE(ce, inp).value.1, t.t, pc + 1, true)
  { }

  lemma TreeRepLkREAtEndLoop(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                             t: LT.Tree, pc: nat, b: bool)
    requires TreeRepLkRE(rer, qm, code, inp, t, pc, b)
    requires NR.GetPcRE(code, pc) == Some(RB.EndLoop)
    ensures b ==> t.Progress? && TreeRepLkRE(rer, qm, code, inp, t.t, pc + 1, true)
    ensures !b ==> t == LT.Mismatch
  { }

  lemma TreeRepLkREAtSetReg(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                            t: LT.Tree, pc: nat, b: bool, reg: int)
    requires TreeRepLkRE(rer, qm, code, inp, t, pc, b)
    requires NR.GetPcRE(code, pc) == Some(RB.SetRegisterToCP(reg))
    ensures t.GroupActionT? && (t.g.Open? || t.g.Close?)
    ensures t.g.Open? ==> reg == CP.start_reg(t.g.g as int)
    ensures t.g.Close? ==> reg == CP.end_reg(t.g.g as int)
    ensures TreeRepLkRE(rer, qm, code, inp, t.t, pc + 1, b)
  { }

  lemma TreeRepLkREAtAnchor(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                            t: LT.Tree, pc: nat, b: bool, a: R.anchor)
    requires TreeRepLkRE(rer, qm, code, inp, t, pc, b)
    requires NR.GetPcRE(code, pc) == Some(RB.AnchorAssertion(a))
    ensures LS.AnchorSatisfied(rer, T.TrAnchor(a), inp) ==>
              t.AnchorPass? && t.a == T.TrAnchor(a)
              && TreeRepLkRE(rer, qm, code, inp, t.t, pc + 1, b)
    ensures !LS.AnchorSatisfied(rer, T.TrAnchor(a), inp) ==> t == LT.Mismatch
  { }

  lemma TreeRepLkREAtCheckOracle(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                                 t: LT.Tree, pc: nat, b: bool, lid: int)
    requires TreeRepLkRE(rer, qm, code, inp, t, pc, b)
    requires NR.GetPcRE(code, pc) == Some(RB.CheckOracle(lid))
    ensures lid in qm.looks
    ensures var lk := qm.looks[lid].0;
            var r1 := qm.looks[lid].1;
            var tlk := LFU.ComputeTr(rer, [LS.Areg(r1)], inp, LG.Empty, L.LkDir(lk));
            if LS.LkResult(lk, tlk, LG.Empty, inp).Some?
            then t.LK? && t.lk == lk && t.tlk == tlk
                 && TreeRepLkRE(rer, qm, code, inp, t.t, pc + 1, b)
            else t == LT.LKFail(lk, tlk)
  { }

  lemma TreeRepLkREAtNegCheckOracle(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                                    t: LT.Tree, pc: nat, b: bool, lid: int)
    requires TreeRepLkRE(rer, qm, code, inp, t, pc, b)
    requires NR.GetPcRE(code, pc) == Some(RB.NegCheckOracle(lid))
    ensures lid in qm.looks
    ensures var lk := qm.looks[lid].0;
            var r1 := qm.looks[lid].1;
            var tlk := LFU.ComputeTr(rer, [LS.Areg(r1)], inp, LG.Empty, L.LkDir(lk));
            if LS.LkResult(lk, tlk, LG.Empty, inp).Some?
            then t.LK? && t.lk == lk && t.tlk == tlk
                 && TreeRepLkRE(rer, qm, code, inp, t.t, pc + 1, b)
            else t == LT.LKFail(lk, tlk)
  { }

  // ==========================================================================
  // THE CONSTRUCTOR: from a represented, walk-guarded stack's BoolTreeLk tree
  // to the PLANTED canonical tree machine B runs.
  //
  // Mirror of the PROVEN `ATR.ActionsTreeRepFRE` / `AtBackForkTreeRep` pair
  // (ActionsTreeRepRE.dfy:177/:826) with LK nodes KEPT and the S-machinery/
  // leaf-agreement congruences replaced by ERASURE EQUALITY (`ProgErase(tcan)
  // == ProgErase(t)` — the constructed tree differs from the spec walk tree
  // only by planted `Progress` guards, so their leaves are EQUAL via
  // `ProgEraseLeavesEq`). No oracle: the gate is decided by the FUNCTIONAL
  // verdict, exactly like `BoolTreeLk`'s `LkGateOk`. `WalkOk` is kept — it
  // excludes the one adversarial config (a bare loop-view star at
  // `CannotExit`) and is available at the ONE invocation site: the entry
  // pairing (`WkE.WalkOkEntry`). The check-insertion seam (`min == 1, Inf`)
  // uses `CE.BoolCheckInsert`, whose strengthened ensures makes the insertion
  // invisible to the erasure tie.
  // ==========================================================================

  /** Fuel-indexed core of the construction: returns the PLANTED canonical
      tree — `TreeRepLkRE`-represented at `(pc, EaOf(b))` and erasure-equal to
      the spec walk tree `t`. One case per action/regex shape, mirroring
      `ATR.ActionsTreeRepFRE` case-for-case. */
  lemma {:isolate_assertions} ActionsTreeRepLkF(rer: LW.RegExpRecord, qm: AR.QMap, acts: LS.Actions,
                                                code: RB.code, pc: nat, inp: LC.Input,
                                                b: BS.LoopBool, t: LT.Tree, n: nat)
    returns (tcan: LT.Tree)
    requires EL.PikeLkActions(acts)
    requires ATR.ActionsRepFuelL(rer, qm, acts, code, pc, n)
    requires WO.WalkOk(acts, code, pc, ATR.EaOf(b))
    requires EL.BoolTreeLk(rer, acts, inp, b, t)
    ensures TreeRepLkRE(rer, qm, code, inp, tcan, pc, ATR.EaOf(b))
    ensures CE.ProgErase(tcan) == CE.ProgErase(t)
    decreases CE.PSize(t), ATR.MsizeA(acts), n, 1
  {
    // (§2.5b) the new recursive nullability predicates' definitional axioms send
    // z3 4.14 into a matching loop on otherwise-trivial goals in the quant arms;
    // every use here is opaque (guards + lemma calls), so hide them.
    hide NUL.NonNullableL, NUL.CINullableL, NUL.NoNulledPlusL, AR.NfaRepCinL;
    if |acts| == 0 && NR.GetPcRE(code, pc) == Some(RB.Accept) {
      assert t == LT.Match;
      tcan := LT.Match;
      // tr_match
    } else if exists pcstart: nat :: NR.GetPcRE(code, pc) == Some(RB.Jmp(pcstart))
                                     && ATR.ActionsRepFuelL(rer, qm, acts, code, pcstart, n - 1) {
      var pcstart: nat :| NR.GetPcRE(code, pc) == Some(RB.Jmp(pcstart))
                          && ATR.ActionsRepFuelL(rer, qm, acts, code, pcstart, n - 1);
      WO.WalkOkJmp(acts, code, pc, ATR.EaOf(b), pcstart);
      tcan := ActionsTreeRepLkF(rer, qm, acts, code, pcstart, inp, b, t, n - 1);
      // tr_jmp
      assert TreeRepLkRE(rer, qm, code, inp, tcan, pc, ATR.EaOf(b));
    } else {
      var cont := acts[1..];
      var pcmid: nat :| AR.ActionRepL(rer, qm, acts[0], code, pc, pcmid)
                        && ATR.ActionsRepFuelL(rer, qm, cont, code, pcmid, n - 1);
      EL.PikeLkActionsTail(acts);
      assert acts == [acts[0]] + cont;
      EL.PikeLkActionsConsIff(acts[0], cont);
      match acts[0]
      case Acheck(strcheck) =>
        assert LS.ActionsRegexSize(acts) == LS.ActionsRegexSize(cont);
        if NR.GetPcRE(code, pc) == Some(RB.EndLoop) {
          assert pcmid == pc + 1;
          if b == BS.CanExit {
            match t {
              case Progress(tc) =>
                WO.WalkOkAcheckEndLoop(acts, code, pc, ATR.EaOf(b));
                var sub := ActionsTreeRepLkF(rer, qm, cont, code, pc + 1, inp, BS.CanExit, tc, n - 1);
                tcan := LT.Progress(sub);
                // tr_progress (fall-through EndLoop)
                assert TreeRepLkRE(rer, qm, code, inp, tcan, pc, true);
              case _ =>
            }
          } else {
            // t == Mismatch: tr_progressfail
            tcan := LT.Mismatch;
            assert TreeRepLkRE(rer, qm, code, inp, tcan, pc, false);
          }
        } else {
          // the zero-width check at the do-while's backward fork
          assert AR.BackForkAt(code, pc) && pcmid == pc;
          if b == BS.CanExit {
            match t {
              case Progress(tc) =>
                WO.WalkOkAcheckBackFork(acts, code, pc, ATR.EaOf(b));
                var sub := AtBackForkTreeLkF(rer, qm, cont, code, pc, inp, tc, n - 1);
                tcan := LT.Progress(sub);
                // the companion's ensures IS tr_plus for Progress(sub)
                assert TreeRepLkRE(rer, qm, code, inp, tcan, pc, true);
              case _ =>
            }
          } else {
            // t == Mismatch: tr_plusfail
            var fx: int, fy: int :| NR.GetPcRE(code, pc) == Some(RB.Fork(fx, fy))
                                    && fx >= 0 && fy >= 0 && (fx as nat <= pc || fy as nat <= pc);
            tcan := LT.Mismatch;
            assert TreeRepLkRE(rer, qm, code, inp, tcan, pc, false);
          }
        }
      case Aclose(gid) =>
        match t {
          case GroupActionT(g, tc) =>
            assert g == LG.Close(gid);
            WO.WalkOkAclose(acts, code, pc, ATR.EaOf(b));
            assert CE.PSize(tc) < CE.PSize(t);
            var sub := ActionsTreeRepLkF(rer, qm, cont, code, pc + 1, inp, b, tc, n - 1);
            tcan := LT.GroupActionT(g, sub);
            // tr_close
            assert TreeRepLkRE(rer, qm, code, inp, tcan, pc, ATR.EaOf(b));
          case _ =>
        }
      case Areg(r) =>
        assert EL.PikeLkRegex(r);
        match r
        case Epsilon =>
          assert {:split_here} true;   // (E3) one assertion batch per arm
          assert pcmid == pc;
          WO.WalkOkEpsilon(acts, code, pc, ATR.EaOf(b));
          assert ATR.MsizeA(cont) < ATR.MsizeA(acts);
          tcan := ActionsTreeRepLkF(rer, qm, cont, code, pc, inp, b, t, n - 1);
        case Character(cd) => {
          assert {:split_here} true;   // (E3) one assertion batch per arm
          var ce :| NR.GetPcRE(code, pc) == Some(RB.Consume(ce)) && AR.ExpectationMatches(rer, ce, cd);
          AR.ReadAgree(rer, ce, cd, inp);
          match LC.ReadChar(rer, cd, inp, WP.Forward) {
            case None =>
              // t == Mismatch; tr_readfail (ReadCharE == None by ReadAgree)
              tcan := LT.Mismatch;
              assert TreeRepLkRE(rer, qm, code, inp, tcan, pc, ATR.EaOf(b));
            case Some(pair) =>
              match t {
                case Read(c, tc) =>
                  assert c == pair.0;
                  WO.WalkOkCharacter(acts, code, pc, ATR.EaOf(b));
                  assert CE.PSize(tc) < CE.PSize(t);
                  var sub := ActionsTreeRepLkF(rer, qm, cont, code, pc + 1, pair.1, BS.CanExit, tc, n - 1);
                  tcan := LT.Read(c, sub);
                  // tr_read with witness (ce, pair.1)
                  assert AR.ReadCharE(ce, inp) == Some((c, pair.1));
                  assert TreeRepLkRE(rer, qm, code, inp, tcan, pc, ATR.EaOf(b));
                case _ =>
              }
          }
        }
        case Disjunction(r1, r2) => {
          assert {:split_here} true;   // (E3) one assertion batch per arm
          EL.PikeLkActionsConsIff(LS.Areg(r1), cont);
          EL.PikeLkActionsConsIff(LS.Areg(r2), cont);
          var e1: nat :| NR.GetPcRE(code, pc) == Some(RB.Fork(pc + 1, e1 + 1))
                         && AR.NfaRepL(rer, qm, r1, code, pc + 1, e1)
                         && NR.GetPcRE(code, e1) == Some(RB.Jmp(pcmid))
                         && AR.NfaRepL(rer, qm, r2, code, e1 + 1, pcmid);
          AR.NfaRepIncrL(rer, qm, r1, code, pc + 1, e1);
          match t {
            case Choice(ta, tb) =>
              WO.WalkOkAlt(acts, code, pc, ATR.EaOf(b), r1, r2, pc + 1, e1 + 1);
              // left branch: [Areg r1]+cont at pc+1 (cont reached via Jmp(e1 -> pcmid))
              var la := [LS.Areg(r1)] + cont;
              assert AR.ActionsRepL(rer, qm, cont, code, e1) by {
                ATR.FuelToActionsRepL(rer, qm, cont, code, pcmid, n - 1);
                assert NR.GetPcRE(code, e1) == Some(RB.Jmp(pcmid));
              }
              assert AR.ActionRepL(rer, qm, LS.Areg(r1), code, pc + 1, e1);
              assert la[0] == LS.Areg(r1) && la[1..] == cont;
              assert AR.ActionsRepL(rer, qm, la, code, pc + 1);
              ATR.ActionsRepLToFuel(rer, qm, la, code, pc + 1);
              var na: nat :| ATR.ActionsRepFuelL(rer, qm, la, code, pc + 1, na);
              assert CE.PSize(ta) < CE.PSize(t);
              var suba := ActionsTreeRepLkF(rer, qm, la, code, pc + 1, inp, b, ta, na);
              // right branch: [Areg r2]+cont at e1+1
              var lb := [LS.Areg(r2)] + cont;
              ATR.FuelToActionsRepL(rer, qm, cont, code, pcmid, n - 1);
              assert AR.ActionRepL(rer, qm, LS.Areg(r2), code, e1 + 1, pcmid);
              assert lb[0] == LS.Areg(r2) && lb[1..] == cont;
              assert AR.ActionsRepL(rer, qm, lb, code, e1 + 1);
              ATR.ActionsRepLToFuel(rer, qm, lb, code, e1 + 1);
              var nb: nat :| ATR.ActionsRepFuelL(rer, qm, lb, code, e1 + 1, nb);
              assert CE.PSize(tb) < CE.PSize(t);
              var subb := ActionsTreeRepLkF(rer, qm, lb, code, e1 + 1, inp, b, tb, nb);
              tcan := LT.Choice(suba, subb);
              // tr_choice with the forward Fork(pc+1, e1+1): e1 >= pc+1 by NfaRepIncrL
              assert TreeRepLkRE(rer, qm, code, inp, tcan, pc, ATR.EaOf(b));
            case _ =>
          }
        }
        case Sequence(r1, r2) => {
          assert {:split_here} true;   // (E3) one assertion batch per arm
          EL.PikeLkActionsConsIff(LS.Areg(r2), cont);
          EL.PikeLkActionsConsIff(LS.Areg(r1), [LS.Areg(r2)] + cont);
          assert AR.NfaRepL(rer, qm, L.Sequence(r1, r2), code, pc, pcmid);
          var e1: nat :| AR.NfaRepL(rer, qm, r1, code, pc, e1) && AR.NfaRepL(rer, qm, r2, code, e1, pcmid);
          var na := [LS.Areg(r1), LS.Areg(r2)] + cont;
          assert na == [LS.Areg(r1)] + ([LS.Areg(r2)] + cont);
          assert AR.ActionRepL(rer, qm, LS.Areg(r2), code, e1, pcmid);
          assert ([LS.Areg(r2)] + cont)[0] == LS.Areg(r2) && ([LS.Areg(r2)] + cont)[1..] == cont;
          ATR.FuelToActionsRepL(rer, qm, cont, code, pcmid, n - 1);
          assert AR.ActionsRepL(rer, qm, [LS.Areg(r2)] + cont, code, e1);
          assert AR.ActionRepL(rer, qm, LS.Areg(r1), code, pc, e1);
          assert na[0] == LS.Areg(r1) && na[1..] == [LS.Areg(r2)] + cont;
          assert AR.ActionsRepL(rer, qm, na, code, pc);
          assert LS.ActionsRegexSize(na) < LS.ActionsRegexSize(acts);
          assert ATR.MsizeA(na) < ATR.MsizeA(acts);
          ATR.ActionsRepLToFuel(rer, qm, na, code, pc);
          var nn: nat :| ATR.ActionsRepFuelL(rer, qm, na, code, pc, nn);
          WO.WalkOkSeq(acts, code, pc, ATR.EaOf(b), r1, r2);
          tcan := ActionsTreeRepLkF(rer, qm, na, code, pc, inp, b, t, nn);
        }
        case Quantified(greedy, min, delta, r1) => {
          assert {:split_here} true;   // (E3) one assertion batch per arm
          var gidl := L.DefGroups(r1);
          if min > 0 {
            match delta {
              case Inf =>
                if !NUL.NonNullableL(r1) {
                  assert {:split_here} true;   // (E3) generic arm in its own batch
                  assert !greedy by {          // §2.5b interim (PikeLk conjunct)
                    assert acts[0] == LS.Areg(L.Quantified(greedy, min, delta, r1));
                  }
                  // §2.5a GENERIC: `min` forced copies then the ordinary star
                  // loop at `emg`. No seam -- the code's BeginLoop/EndLoop sits
                  // exactly where the spec's Acheck is, so nothing is inserted
                  // and this arm needs no nullability hypothesis.
                  var emg, e1g := AR.NfaRepLGenInv(rer, qm, greedy, min, r1, code, pc, pcmid);
                  var qidg: int :| NR.GetPcRE(code, emg + 1) == Some(RB.SetQuantToClock(qidg, false))
                                   && qidg in qm.quants && qm.quants[qidg] == gidl;
                  AR.NfaRepIncrL(rer, qm, r1, code, emg + 3, e1g);
                  var quant1g := L.Quantified(greedy, min - 1, LN.Inf, r1);
                  var ebg: nat :| (exists qid2: int ::
                                     NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(qid2, false))
                                     && qid2 in qm.quants && qm.quants[qid2] == gidl)
                                  && AR.NfaRepL(rer, qm, r1, code, pc + 1, ebg)
                                  && AR.NfaRepMinL(rer, qm, min - 1, r1, code, ebg, emg);
                  if min > 1 {
                    AR.NfaRepLGenIntro(rer, qm, greedy, min - 1, r1, code, ebg, emg, e1g, pcmid, qidg);
                  } else {
                    assert ebg == emg;   // NfaRepMinL(0, …); the star arm at emg IS quant1g
                  }
                  assert AR.NfaRepL(rer, qm, quant1g, code, ebg, pcmid);
                  match t {
                    case GroupActionT(g, tc) =>
                      assert g == LG.Reset(gidl);
                      EL.PikeLkActionsConsIff(LS.Areg(quant1g), cont);
                      EL.PikeLkActionsConsIff(LS.Areg(r1), [LS.Areg(quant1g)] + cont);
                      ATR.FuelToActionsRepL(rer, qm, cont, code, pcmid, n - 1);
                      assert AR.ActionRepL(rer, qm, LS.Areg(quant1g), code, ebg, pcmid);
                      var lq1g := [LS.Areg(quant1g)] + cont;
                      assert lq1g[0] == LS.Areg(quant1g) && lq1g[1..] == cont;
                      assert AR.ActionsRepL(rer, qm, lq1g, code, ebg);
                      var iag := [LS.Areg(r1)] + lq1g;
                      assert AR.ActionRepL(rer, qm, LS.Areg(r1), code, pc + 1, ebg);
                      assert iag[0] == LS.Areg(r1) && iag[1..] == lq1g;
                      assert AR.ActionsRepL(rer, qm, iag, code, pc + 1);
                      assert iag == [LS.Areg(r1), LS.Areg(quant1g)] + cont;
                      ATR.ActionsRepLToFuel(rer, qm, iag, code, pc + 1);
                      var nig: nat :| ATR.ActionsRepFuelL(rer, qm, iag, code, pc + 1, nig);
                      WO.WalkOkQuantForced(acts, code, pc, ATR.EaOf(b), greedy, min, delta, r1);
                      assert CE.PSize(tc) < CE.PSize(t);
                      var subg := ActionsTreeRepLkF(rer, qm, iag, code, pc + 1, inp, b, tc, nig);
                      tcan := LT.GroupActionT(g, subg);
                      assert TreeRepLkRE(rer, qm, code, inp, tcan, pc, ATR.EaOf(b));
                    case _ =>
                  }
                } else {
                assert {:split_here} true;   // (E3) do-while arm in its own batch
                var em, e1x := AR.NfaRepLPlusInv(rer, qm, greedy, min, r1, code, pc, pcmid);
                assert NUL.NonNullableL(r1);
                var qid: int :| NR.GetPcRE(code, em) == Some(RB.SetQuantToClock(qid, false))
                                && qid in qm.quants && qm.quants[qid] == gidl;
                AR.NfaRepIncrL(rer, qm, r1, code, em + 1, e1x);
                if min > 1 {
                  var quant1 := L.Quantified(greedy, min - 1, LN.Inf, r1);
                  var eb: nat :| (exists qid2: int ::
                                    NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(qid2, false))
                                    && qid2 in qm.quants && qm.quants[qid2] == gidl)
                                 && AR.NfaRepL(rer, qm, r1, code, pc + 1, eb)
                                 && AR.NfaRepMinL(rer, qm, min - 2, r1, code, eb, em);
                  AR.NfaRepLPlusIntro(rer, qm, greedy, min - 1, r1, code, eb, em, e1x, pcmid, qid);
                  assert AR.NfaRepL(rer, qm, quant1, code, eb, pcmid);
                  match t {
                    case GroupActionT(g, tc) =>
                      assert g == LG.Reset(gidl);
                      EL.PikeLkActionsConsIff(LS.Areg(quant1), cont);
                      EL.PikeLkActionsConsIff(LS.Areg(r1), [LS.Areg(quant1)] + cont);
                      ATR.FuelToActionsRepL(rer, qm, cont, code, pcmid, n - 1);
                      assert AR.ActionRepL(rer, qm, LS.Areg(quant1), code, eb, pcmid);
                      var lq1 := [LS.Areg(quant1)] + cont;
                      assert lq1[0] == LS.Areg(quant1) && lq1[1..] == cont;
                      assert AR.ActionsRepL(rer, qm, lq1, code, eb);
                      var ia := [LS.Areg(r1)] + lq1;
                      assert AR.ActionRepL(rer, qm, LS.Areg(r1), code, pc + 1, eb);
                      assert ia[0] == LS.Areg(r1) && ia[1..] == lq1;
                      assert AR.ActionsRepL(rer, qm, ia, code, pc + 1);
                      assert ia == [LS.Areg(r1), LS.Areg(quant1)] + cont;
                      ATR.ActionsRepLToFuel(rer, qm, ia, code, pc + 1);
                      var ni: nat :| ATR.ActionsRepFuelL(rer, qm, ia, code, pc + 1, ni);
                      WO.WalkOkQuantForced(acts, code, pc, ATR.EaOf(b), greedy, min, delta, r1);
                      assert CE.PSize(tc) < CE.PSize(t);
                      var sub := ActionsTreeRepLkF(rer, qm, ia, code, pc + 1, inp, b, tc, ni);
                      tcan := LT.GroupActionT(g, sub);
                      // tr_reset at pc (the copy's clock-mark carries the Reset)
                      assert TreeRepLkRE(rer, qm, code, inp, tcan, pc, ATR.EaOf(b));
                    case _ =>
                  }
                } else {
                  // min == 1: THE SEAM. Insert the check; erasure makes the
                  // insertion invisible (BoolCheckInsert's ProgErase ensures).
                  assert em == pc;
                  var q0 := L.Quantified(greedy, 0, LN.Inf, r1);
                  match t {
                    case GroupActionT(g, tc) =>
                      assert g == LG.Reset(gidl);
                      assert EL.BoolTreeLk(rer, [LS.Areg(r1), LS.Areg(q0)] + cont, inp, b, tc);
                      var pre := [LS.Areg(r1)];
                      var rest := [LS.Areg(q0)] + cont;
                      EL.PikeLkActionsConsIff(LS.Areg(q0), cont);
                      EL.PikeLkActionsConsIff(LS.Areg(r1), rest);
                      assert EL.PikeLkActions(pre) by {
                        assert pre == [LS.Areg(r1)] + [];
                        EL.PikeLkActionsConsIff(LS.Areg(r1), []);
                      }
                      assert pre + rest == [LS.Areg(r1), LS.Areg(q0)] + cont;
                      assert CE.ConsumesBeforeAreg(pre) by {
                        assert pre[0].Areg? && NUL.NonNullableL(pre[0].r);
                      }
                      var t1ck := CE.BoolCheckInsert(rer, pre, inp, rest, inp, b, tc);
                      assert CE.ProgErase(t1ck) == CE.ProgErase(tc);
                      var ia := [LS.Areg(r1), LS.Acheck(inp), LS.Areg(q0)] + cont;
                      assert ia == pre + [LS.Acheck(inp)] + rest;
                      assert EL.BoolTreeLk(rer, ia, inp, b, t1ck);
                      assert AR.BackForkAt(code, e1x) by {
                        assert NR.GetPcRE(code, e1x)
                            == Some(if greedy then RB.Fork(em, e1x + 1) else RB.Fork(e1x + 1, em));
                        assert em <= e1x;
                      }
                      assert AR.NfaRepL(rer, qm, q0, code, e1x, e1x + 1) by {
                        // (§2.5b/z3 4.14) granular witnesses first — the packed
                        // conjunction alone sends the solver hunting for the skolem
                        assert NUL.NonNullableL(r1);
                        assert NR.GetPcRE(code, e1x)
                            == Some(if greedy then RB.Fork(em, e1x + 1) else RB.Fork(e1x + 1, em));
                        assert em <= e1x;
                        assert NR.GetPcRE(code, em) == Some(RB.SetQuantToClock(qid, false))
                               && qid in qm.quants && qm.quants[qid] == L.DefGroups(r1);
                        assert AR.NfaRepL(rer, qm, r1, code, em + 1, e1x);
                        assert NUL.NonNullableL(r1)
                               && NR.GetPcRE(code, e1x)
                                  == Some(if greedy then RB.Fork(em, e1x + 1) else RB.Fork(e1x + 1, em))
                               && em <= e1x
                               && (exists qid2: int ::
                                     NR.GetPcRE(code, em) == Some(RB.SetQuantToClock(qid2, false))
                                     && qid2 in qm.quants && qm.quants[qid2] == L.DefGroups(r1))
                               && AR.NfaRepL(rer, qm, r1, code, em + 1, e1x);
                      }
                      ATR.FuelToActionsRepL(rer, qm, cont, code, pcmid, n - 1);
                      var lq := [LS.Areg(q0)] + cont;
                      assert AR.ActionRepL(rer, qm, LS.Areg(q0), code, e1x, e1x + 1);
                      assert lq[0] == LS.Areg(q0) && lq[1..] == cont;
                      assert AR.ActionsRepL(rer, qm, lq, code, e1x);
                      var lc := [LS.Acheck(inp)] + lq;
                      EL.PikeLkActionsConsIff(LS.Acheck(inp), lq);
                      assert AR.ActionRepL(rer, qm, LS.Acheck(inp), code, e1x, e1x);
                      assert lc[0] == LS.Acheck(inp) && lc[1..] == lq;
                      assert AR.ActionsRepL(rer, qm, lc, code, e1x);
                      assert AR.ActionRepL(rer, qm, LS.Areg(r1), code, pc + 1, e1x);
                      assert ia == [LS.Areg(r1)] + lc;
                      assert ia[0] == LS.Areg(r1) && ia[1..] == lc;
                      assert AR.ActionsRepL(rer, qm, ia, code, pc + 1);
                      EL.PikeLkActionsConsIff(LS.Areg(r1), lc);
                      assert EL.PikeLkActions(ia);
                      ATR.ActionsRepLToFuel(rer, qm, ia, code, pc + 1);
                      var ni: nat :| ATR.ActionsRepFuelL(rer, qm, ia, code, pc + 1, ni);
                      WO.WalkOkQuantSeam(acts, code, pc, ATR.EaOf(b), greedy, r1, inp);
                      assert CE.PSize(t1ck) == CE.PSize(tc);
                      assert CE.PSize(t1ck) < CE.PSize(t);
                      var sub := ActionsTreeRepLkF(rer, qm, ia, code, pc + 1, inp, b, t1ck, ni);
                      tcan := LT.GroupActionT(g, sub);
                      // erasure: ProgErase(sub) == ProgErase(t1ck) == ProgErase(tc)
                      // (BoolCheckInsert's insertion is Progress-only); tr_reset at pc
                      assert CE.ProgErase(sub) == CE.ProgErase(tc);
                      assert TreeRepLkRE(rer, qm, code, inp, tcan, pc, ATR.EaOf(b));
                    case _ =>
                  }
                }
                }
              case NN(kx) =>
                var em := AR.NfaRepLQuantInv(rer, qm, greedy, min, kx, r1, code, pc, pcmid);
                var quant1 := L.Quantified(greedy, min - 1, delta, r1);
                var eb: nat :| (exists qid: int ::
                                  NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(qid, false))
                                  && qid in qm.quants && qm.quants[qid] == gidl)
                               && AR.NfaRepL(rer, qm, r1, code, pc + 1, eb)
                               && AR.NfaRepMinL(rer, qm, min - 1, r1, code, eb, em);
                AR.NfaRepLQuantIntro(rer, qm, greedy, min - 1, kx, r1, code, eb, em, pcmid);
                assert AR.NfaRepL(rer, qm, quant1, code, eb, pcmid);
                match t {
                  case GroupActionT(g, tc) =>
                    assert g == LG.Reset(gidl);
                    EL.PikeLkActionsConsIff(LS.Areg(quant1), cont);
                    EL.PikeLkActionsConsIff(LS.Areg(r1), [LS.Areg(quant1)] + cont);
                    ATR.FuelToActionsRepL(rer, qm, cont, code, pcmid, n - 1);
                    assert AR.ActionRepL(rer, qm, LS.Areg(quant1), code, eb, pcmid);
                    var lq1 := [LS.Areg(quant1)] + cont;
                    assert lq1[0] == LS.Areg(quant1) && lq1[1..] == cont;
                    assert AR.ActionsRepL(rer, qm, lq1, code, eb);
                    var ia := [LS.Areg(r1)] + lq1;
                    assert AR.ActionRepL(rer, qm, LS.Areg(r1), code, pc + 1, eb);
                    assert ia[0] == LS.Areg(r1) && ia[1..] == lq1;
                    assert AR.ActionsRepL(rer, qm, ia, code, pc + 1);
                    assert ia == [LS.Areg(r1), LS.Areg(quant1)] + cont;
                    ATR.ActionsRepLToFuel(rer, qm, ia, code, pc + 1);
                    var ni: nat :| ATR.ActionsRepFuelL(rer, qm, ia, code, pc + 1, ni);
                    WO.WalkOkQuantForced(acts, code, pc, ATR.EaOf(b), greedy, min, delta, r1);
                    assert CE.PSize(tc) < CE.PSize(t);
                    var sub := ActionsTreeRepLkF(rer, qm, ia, code, pc + 1, inp, b, tc, ni);
                    tcan := LT.GroupActionT(g, sub);
                    // tr_reset at pc
                    assert TreeRepLkRE(rer, qm, code, inp, tcan, pc, ATR.EaOf(b));
                  case _ =>
                }
            }
            return;
          }
          if delta.NN? {
            var k := delta.n;
            var em := AR.NfaRepLQuantInv(rer, qm, greedy, 0, k, r1, code, pc, pcmid);
            assert em == pc;
            if k == 0 {
              // spent quantifier: transparent, peel
              assert pc == pcmid;
              WO.WalkOkQuantSpent(acts, code, pc, ATR.EaOf(b), greedy, r1);
              assert LS.ActionsRegexSize(cont) < LS.ActionsRegexSize(acts);
              assert ATR.MsizeA(cont) < ATR.MsizeA(acts);
              tcan := ActionsTreeRepLkF(rer, qm, cont, code, pcmid, inp, b, t, n - 1);
            } else {
              // one bounded layer: the fork skips to the common end pcmid
              var quant := L.Quantified(greedy, 0, FS.NoiPred(delta), r1);
              assert quant == L.Quantified(greedy, 0, LN.NN(k - 1), r1);
              var e1: nat :| NR.GetPcRE(code, pc) == Some(if greedy then RB.Fork(pc + 1, pcmid) else RB.Fork(pcmid, pc + 1))
                             && (exists qid: int ::
                                   NR.GetPcRE(code, pc + 1) == Some(RB.SetQuantToClock(qid, false))
                                   && qid in qm.quants && qm.quants[qid] == gidl)
                             && NR.GetPcRE(code, pc + 2) == Some(RB.BeginLoop)
                             && AR.NfaRepL(rer, qm, r1, code, pc + 3, e1)
                             && NR.GetPcRE(code, e1) == Some(RB.EndLoop)
                             && AR.NfaRepOptL(rer, qm, k - 1, greedy, r1, code, e1 + 1, pcmid);
              AR.NfaRepIncrL(rer, qm, r1, code, pc + 3, e1);
              AR.NfaRepIncrOptL(rer, qm, k - 1, greedy, r1, code, e1 + 1, pcmid);
              match t {
                case Choice(ta, tb) =>
                  var itert := if greedy then ta else tb;
                  var skipt := if greedy then tb else ta;
                  match itert {
                    case GroupActionT(g, ti) =>
                      assert g == LG.Reset(gidl);
                      WO.WalkOkQuantLayer(acts, code, pc, ATR.EaOf(b), greedy, delta, r1,
                                          if greedy then pc + 1 else pcmid,
                                          if greedy then pcmid else pc + 1, inp);
                      // skip branch: cont at the common end pcmid
                      assert CE.PSize(skipt) < CE.PSize(t);
                      var subs := ActionsTreeRepLkF(rer, qm, cont, code, pcmid, inp, b, skipt, n - 1);
                      // iteration branch at pc+3 with the NN(k-1) continuation at e1+1
                      EL.PikeLkActionsConsIff(LS.Areg(quant), cont);
                      EL.PikeLkActionsConsIff(LS.Acheck(inp), [LS.Areg(quant)] + cont);
                      EL.PikeLkActionsConsIff(LS.Areg(r1), [LS.Acheck(inp)] + ([LS.Areg(quant)] + cont));
                      ATR.FuelToActionsRepL(rer, qm, cont, code, pcmid, n - 1);
                      var lq := [LS.Areg(quant)] + cont;
                      assert AR.NfaRepMinL(rer, qm, 0, r1, code, e1 + 1, e1 + 1);
                      AR.NfaRepLQuantIntro(rer, qm, greedy, 0, k - 1, r1, code, e1 + 1, e1 + 1, pcmid);
                      assert AR.ActionRepL(rer, qm, LS.Areg(quant), code, e1 + 1, pcmid);
                      assert lq[0] == LS.Areg(quant) && lq[1..] == cont;
                      assert AR.ActionsRepL(rer, qm, lq, code, e1 + 1);
                      var lc := [LS.Acheck(inp)] + lq;
                      assert AR.ActionRepL(rer, qm, LS.Acheck(inp), code, e1, e1 + 1);
                      assert lc[0] == LS.Acheck(inp) && lc[1..] == lq;
                      assert AR.ActionsRepL(rer, qm, lc, code, e1);
                      var ia := [LS.Areg(r1)] + lc;
                      assert AR.ActionRepL(rer, qm, LS.Areg(r1), code, pc + 3, e1);
                      assert ia[0] == LS.Areg(r1) && ia[1..] == lc;
                      assert AR.ActionsRepL(rer, qm, ia, code, pc + 3);
                      assert ia == [LS.Areg(r1), LS.Acheck(inp), LS.Areg(quant)] + cont;
                      ATR.ActionsRepLToFuel(rer, qm, ia, code, pc + 3);
                      var ni: nat :| ATR.ActionsRepFuelL(rer, qm, ia, code, pc + 3, ni);
                      assert CE.PSize(ti) < CE.PSize(t);
                      var subi := ActionsTreeRepLkF(rer, qm, ia, code, pc + 3, inp, BS.CannotExit, ti, ni);
                      // assemble: subi at pc+3 (false) -> tr_begin at pc+2 ->
                      // tr_reset at pc+1 -> tr_choice with the skip at pcmid
                      assert TreeRepLkRE(rer, qm, code, inp, subi, pc + 3, false);
                      assert TreeRepLkRE(rer, qm, code, inp, subi, pc + 2, ATR.EaOf(b));
                      var iterstar := LT.GroupActionT(g, subi);
                      assert TreeRepLkRE(rer, qm, code, inp, iterstar, pc + 1, ATR.EaOf(b));
                      tcan := if greedy then LT.Choice(iterstar, subs) else LT.Choice(subs, iterstar);
                      assert TreeRepLkRE(rer, qm, code, inp, tcan, pc, ATR.EaOf(b));
                      assert CE.ProgErase(iterstar) == CE.ProgErase(itert);
                      assert CE.ProgErase(tcan) == CE.ProgErase(t);
                    case _ =>
                  }
                case _ =>
              }
            }
            return;
          }
          assert min == 0 && delta == LN.Inf;
          var quant := L.Quantified(greedy, 0, FS.NoiPred(delta), r1);
          assert quant == L.Quantified(greedy, 0, LN.Inf, r1) == L.Quantified(greedy, min, delta, r1);
          if exists e1: nat :: NR.GetPcRE(code, pc) == Some(if greedy then RB.Fork(pc + 1, e1 + 2) else RB.Fork(e1 + 2, pc + 1))
                               && (exists qid: int ::
                                     NR.GetPcRE(code, pc + 1) == Some(RB.SetQuantToClock(qid, false))
                                     && qid in qm.quants && qm.quants[qid] == gidl)
                               && NR.GetPcRE(code, pc + 2) == Some(RB.BeginLoop)
                               && AR.NfaRepL(rer, qm, r1, code, pc + 3, e1)
                               && NR.GetPcRE(code, e1) == Some(RB.EndLoop)
                               && NR.GetPcRE(code, e1 + 1) == Some(RB.Jmp(pc))
                               && pcmid == e1 + 2 {
            // the star FAST PATH (forward decision point)
            var e1: nat :| NR.GetPcRE(code, pc) == Some(if greedy then RB.Fork(pc + 1, e1 + 2) else RB.Fork(e1 + 2, pc + 1))
                           && (exists qid: int ::
                                 NR.GetPcRE(code, pc + 1) == Some(RB.SetQuantToClock(qid, false))
                                 && qid in qm.quants && qm.quants[qid] == gidl)
                           && NR.GetPcRE(code, pc + 2) == Some(RB.BeginLoop)
                           && AR.NfaRepL(rer, qm, r1, code, pc + 3, e1)
                           && NR.GetPcRE(code, e1) == Some(RB.EndLoop)
                           && NR.GetPcRE(code, e1 + 1) == Some(RB.Jmp(pc))
                           && pcmid == e1 + 2;
            AR.NfaRepIncrL(rer, qm, r1, code, pc + 3, e1);
            match t {
              case Choice(ta, tb) =>
                var itert := if greedy then ta else tb;
                var skipt := if greedy then tb else ta;
                match itert {
                  case GroupActionT(g, ti) =>
                    assert g == LG.Reset(gidl);
                    WO.WalkOkQuantLayer(acts, code, pc, ATR.EaOf(b), greedy, delta, r1,
                                        if greedy then pc + 1 else pcmid,
                                        if greedy then pcmid else pc + 1, inp);
                    // skip branch at pcmid == e1+2
                    assert CE.PSize(skipt) < CE.PSize(t);
                    var subs := ActionsTreeRepLkF(rer, qm, cont, code, pcmid, inp, b, skipt, n - 1);
                    // iteration branch: [Areg r1, Acheck inp, Areg quant] + cont at pc+3
                    EL.PikeLkActionsConsIff(LS.Areg(quant), cont);
                    EL.PikeLkActionsConsIff(LS.Acheck(inp), [LS.Areg(quant)] + cont);
                    EL.PikeLkActionsConsIff(LS.Areg(r1), [LS.Acheck(inp)] + ([LS.Areg(quant)] + cont));
                    ATR.FuelToActionsRepL(rer, qm, cont, code, pcmid, n - 1);
                    var lq := [LS.Areg(quant)] + cont;
                    assert AR.ActionRepL(rer, qm, LS.Areg(quant), code, pc, pcmid);
                    assert lq[0] == LS.Areg(quant) && lq[1..] == cont;
                    assert AR.ActionsRepL(rer, qm, lq, code, pc);
                    AR.ActionsRepLJmp(rer, qm, lq, code, e1 + 1, pc);
                    var lc := [LS.Acheck(inp)] + lq;
                    assert AR.ActionRepL(rer, qm, LS.Acheck(inp), code, e1, e1 + 1);
                    assert lc[0] == LS.Acheck(inp) && lc[1..] == lq;
                    assert AR.ActionsRepL(rer, qm, lc, code, e1);
                    var ia := [LS.Areg(r1)] + lc;
                    assert AR.ActionRepL(rer, qm, LS.Areg(r1), code, pc + 3, e1);
                    assert ia[0] == LS.Areg(r1) && ia[1..] == lc;
                    assert AR.ActionsRepL(rer, qm, ia, code, pc + 3);
                    assert ia == [LS.Areg(r1), LS.Acheck(inp), LS.Areg(quant)] + cont;
                    ATR.ActionsRepLToFuel(rer, qm, ia, code, pc + 3);
                    var ni: nat :| ATR.ActionsRepFuelL(rer, qm, ia, code, pc + 3, ni);
                    assert CE.PSize(ti) < CE.PSize(t);
                    var subi := ActionsTreeRepLkF(rer, qm, ia, code, pc + 3, inp, BS.CannotExit, ti, ni);
                    // assemble: tr_begin at pc+2, tr_reset at pc+1, tr_choice at pc
                    assert TreeRepLkRE(rer, qm, code, inp, subi, pc + 3, false);
                    assert TreeRepLkRE(rer, qm, code, inp, subi, pc + 2, ATR.EaOf(b));
                    var iterstar := LT.GroupActionT(g, subi);
                    assert TreeRepLkRE(rer, qm, code, inp, iterstar, pc + 1, ATR.EaOf(b));
                    tcan := if greedy then LT.Choice(iterstar, subs) else LT.Choice(subs, iterstar);
                    assert TreeRepLkRE(rer, qm, code, inp, tcan, pc, ATR.EaOf(b));
                    assert CE.ProgErase(iterstar) == CE.ProgErase(itert);
                    assert CE.ProgErase(tcan) == CE.ProgErase(t);
                  case _ =>
                }
              case _ =>
            }
          } else {
            // the LOOP VIEW: a bare star at the do-while's backward fork.
            // WalkOk pins the flag to CanExit; the fused fork lemma builds the
            // Choice and tr_plus consumes the PLANTED Progress with the fork.
            assert NUL.NonNullableL(r1);
            var em: nat :| NR.GetPcRE(code, pc) == Some(if greedy then RB.Fork(em, pc + 1) else RB.Fork(pc + 1, em))
                           && em <= pc
                           && (exists qid: int ::
                                 NR.GetPcRE(code, em) == Some(RB.SetQuantToClock(qid, false))
                                 && qid in qm.quants && qm.quants[qid] == gidl)
                           && AR.NfaRepL(rer, qm, r1, code, em + 1, pc)
                           && pcmid == pc + 1;
            WO.WalkOkLoopView(acts, code, pc, ATR.EaOf(b), greedy, LN.Inf, r1,
                              if greedy then em else pc + 1,
                              if greedy then pc + 1 else em, inp);
            assert ATR.EaOf(b) == true;
            assert b == BS.CanExit;
            assert AR.BackForkAt(code, pc);
            var sub := AtBackForkTreeLkF(rer, qm, acts, code, pc, inp, t, n);
            tcan := LT.Progress(sub);
            assert TreeRepLkRE(rer, qm, code, inp, tcan, pc, ATR.EaOf(b));
          }
        }
        case Group(gid, r1) => {
          assert {:split_here} true;   // (E3) one assertion batch per arm
          EL.PikeLkActionsConsIff(LS.Aclose(gid), cont);
          EL.PikeLkActionsConsIff(LS.Areg(r1), [LS.Aclose(gid)] + cont);
          var e1: nat :| NR.GetPcRE(code, pc) == Some(RB.SetRegisterToCP(CP.start_reg(gid as int)))
                         && AR.NfaRepL(rer, qm, r1, code, pc + 1, e1)
                         && NR.GetPcRE(code, e1) == Some(RB.SetRegisterToCP(CP.end_reg(gid as int)))
                         && pcmid == e1 + 1;
          match t {
            case GroupActionT(g, tc) =>
              assert g == LG.Open(gid);
              WO.WalkOkGroup(acts, code, pc, ATR.EaOf(b), gid, r1);
              var lc := [LS.Aclose(gid)] + cont;
              assert AR.ActionRepL(rer, qm, LS.Aclose(gid), code, e1, e1 + 1);
              assert lc[0] == LS.Aclose(gid) && lc[1..] == cont;
              ATR.FuelToActionsRepL(rer, qm, cont, code, pcmid, n - 1);
              assert AR.ActionsRepL(rer, qm, lc, code, e1);
              var ga := [LS.Areg(r1)] + lc;
              assert AR.ActionRepL(rer, qm, LS.Areg(r1), code, pc + 1, e1);
              assert ga[0] == LS.Areg(r1) && ga[1..] == lc;
              assert AR.ActionsRepL(rer, qm, ga, code, pc + 1);
              assert ga == [LS.Areg(r1), LS.Aclose(gid)] + cont;
              ATR.ActionsRepLToFuel(rer, qm, ga, code, pc + 1);
              var ng: nat :| ATR.ActionsRepFuelL(rer, qm, ga, code, pc + 1, ng);
              assert CE.PSize(tc) < CE.PSize(t);
              var sub := ActionsTreeRepLkF(rer, qm, ga, code, pc + 1, inp, b, tc, ng);
              tcan := LT.GroupActionT(g, sub);
              // tr_open
              assert TreeRepLkRE(rer, qm, code, inp, tcan, pc, ATR.EaOf(b));
            case _ =>
          }
        }
        case AnchorR(la) => {
          assert {:split_here} true;   // (E3) one assertion batch per arm
          var ra: R.anchor :| NR.GetPcRE(code, pc) == Some(RB.AnchorAssertion(ra))
                              && T.TrAnchor(ra) == la;
          if LS.AnchorSatisfied(rer, la, inp) {
            match t {
              case AnchorPass(la2, tc) =>
                assert la2 == la;
                WO.WalkOkAnchor(acts, code, pc, ATR.EaOf(b));
                assert CE.PSize(tc) < CE.PSize(t);
                var sub := ActionsTreeRepLkF(rer, qm, cont, code, pc + 1, inp, b, tc, n - 1);
                tcan := LT.AnchorPass(la2, sub);
                // tr_anchorpass (Linden-side satisfaction, anchor pinned via ra)
                assert TreeRepLkRE(rer, qm, code, inp, tcan, pc, ATR.EaOf(b));
              case _ =>
            }
          } else {
            // t == Mismatch; tr_anchorfail via ra
            tcan := LT.Mismatch;
            assert TreeRepLkRE(rer, qm, code, inp, tcan, pc, ATR.EaOf(b));
          }
        }
        case LookaroundR(lk, r1) => {
          assert {:split_here} true;   // (E3) one assertion batch per arm
          // THE GATE. NfaRepL pins the oracle instruction + the looks-table
          // row; TreeRepLkRE's gate rule is decided by the same FUNCTIONAL
          // verdict BoolTreeLk's LkGateOk used — no oracle bit involved. The
          // node is KEPT with the RAW functional body.
          var lid: int :| NR.GetPcRE(code, pc)
                          == Some(if AR.PositiveL(lk) then RB.CheckOracle(lid)
                                                      else RB.NegCheckOracle(lid))
                          && lid in qm.looks && qm.looks[lid] == (lk, r1);
          assert pcmid == pc + 1;
          var tlkc := LFU.ComputeTr(rer, [LS.Areg(r1)], inp, LG.Empty, L.LkDir(lk));
          match t {
            case LK(lk2, tlk, tc) =>
              assert lk2 == lk && tlk == tlkc && LS.LkResult(lk, tlk, LG.Empty, inp).Some?;
              WO.WalkOkLookaround(acts, code, pc, ATR.EaOf(b));
              assert CE.PSize(tc) < CE.PSize(t);
              var sub := ActionsTreeRepLkF(rer, qm, cont, code, pc + 1, inp, b, tc, n - 1);
              tcan := LT.LK(lk, tlkc, sub);
              // tr_lk
              assert TreeRepLkRE(rer, qm, code, inp, tcan, pc, ATR.EaOf(b));
            case LKFail(lk2, tlk) =>
              assert lk2 == lk && tlk == tlkc && LS.LkResult(lk, tlk, LG.Empty, inp).None?;
              // tr_lkfail: direct, no recursion
              tcan := LT.LKFail(lk, tlkc);
              assert TreeRepLkRE(rer, qm, code, inp, tcan, pc, ATR.EaOf(b));
            case _ =>
          }
        }
        case Backreference(gid) =>   // not pike
          assert {:split_here} true;   // (E3) one assertion batch per arm
    }
  }

  /** The fused fork lemma: at the do-while's backward fork with the walk
      allowed to exit, builds the canonical Choice whose PLANTED `Progress`
      wrapper is consumed by `tr_plus` together with the fork. Mirror of
      `ATR.AtBackForkTreeRep`: pops `Acheck`/`Epsilon`/`Sequence`/spent heads;
      every other head shape contradicts the pinned Fork; at the loop-view
      star the iteration is lifted to `CanExit` (`CE.BoolFlagLift`) and both
      branches delegate to the general construction. */
  lemma {:isolate_assertions} AtBackForkTreeLkF(rer: LW.RegExpRecord, qm: AR.QMap, acts: LS.Actions, code: RB.code,
                          pc: nat, inp: LC.Input, tc: LT.Tree, n: nat)
    returns (tcstar: LT.Tree)
    requires EL.PikeLkActions(acts)
    requires ATR.ActionsRepFuelL(rer, qm, acts, code, pc, n)
    requires WO.WalkOk(acts, code, pc, true)
    requires EL.BoolTreeLk(rer, acts, inp, BS.CanExit, tc)
    requires AR.BackForkAt(code, pc)
    ensures TreeRepLkRE(rer, qm, code, inp, LT.Progress(tcstar), pc, true)
    ensures CE.ProgErase(tcstar) == CE.ProgErase(tc)
    decreases CE.PSize(tc), ATR.MsizeA(acts), n, 0
  {
    // (§2.5b) the new recursive nullability predicates' definitional axioms send
    // z3 4.14 into a matching loop on otherwise-trivial goals in the quant arms;
    // every use here is opaque (guards + lemma calls), so hide them.
    hide NUL.NonNullableL, NUL.CINullableL, NUL.NoNulledPlusL, AR.NfaRepCinL;
    var fx: int, fy: int :| NR.GetPcRE(code, pc) == Some(RB.Fork(fx, fy))
                            && fx >= 0 && fy >= 0 && (fx as nat <= pc || fy as nat <= pc);
    assert |acts| > 0;
    var cont := acts[1..];
    var pcmid: nat :| AR.ActionRepL(rer, qm, acts[0], code, pc, pcmid)
                      && ATR.ActionsRepFuelL(rer, qm, cont, code, pcmid, n - 1);
    EL.PikeLkActionsTail(acts);
    assert acts == [acts[0]] + cont;
    EL.PikeLkActionsConsIff(acts[0], cont);
    match acts[0]
    case Acheck(strcheck) =>
      // a stacked check: zero-width at the fork; its Progress collapses into
      // the single planted guard
      assert pcmid == pc;
      assert LS.ActionsRegexSize(acts) == LS.ActionsRegexSize(cont);
      match tc {
        case Progress(tc2) =>
          WO.WalkOkAcheckBackFork(acts, code, pc, true);
          tcstar := AtBackForkTreeLkF(rer, qm, cont, code, pc, inp, tc2, n - 1);
          assert CE.ProgErase(tc) == CE.ProgErase(tc2);
        case _ =>
      }
    case Aclose(gid) =>
      assert false;   // SetRegisterToCP != Fork
    case Areg(r) =>
      assert EL.PikeLkRegex(r);
      match r
      case Epsilon =>
        assert pcmid == pc;
        WO.WalkOkEpsilon(acts, code, pc, true);
        assert ATR.MsizeA(cont) < ATR.MsizeA(acts);
        tcstar := AtBackForkTreeLkF(rer, qm, cont, code, pc, inp, tc, n - 1);
      case Character(cd) =>
        var ce :| NR.GetPcRE(code, pc) == Some(RB.Consume(ce)) && AR.ExpectationMatches(rer, ce, cd);
        assert false;   // Consume != Fork
      case AnchorR(la) =>
        var ra: R.anchor :| NR.GetPcRE(code, pc) == Some(RB.AnchorAssertion(ra)) && T.TrAnchor(ra) == la;
        assert false;   // AnchorAssertion != Fork
      case Disjunction(r1, r2) =>
        var e1: nat :| NR.GetPcRE(code, pc) == Some(RB.Fork(pc + 1, e1 + 1))
                       && AR.NfaRepL(rer, qm, r1, code, pc + 1, e1)
                       && NR.GetPcRE(code, e1) == Some(RB.Jmp(pcmid))
                       && AR.NfaRepL(rer, qm, r2, code, e1 + 1, pcmid);
        AR.NfaRepIncrL(rer, qm, r1, code, pc + 1, e1);
        assert false;   // both arms forward: contradicts the backward arm
      case Sequence(r1, r2) =>
        EL.PikeLkActionsConsIff(LS.Areg(r2), cont);
        EL.PikeLkActionsConsIff(LS.Areg(r1), [LS.Areg(r2)] + cont);
        assert AR.NfaRepL(rer, qm, L.Sequence(r1, r2), code, pc, pcmid);
        var e1: nat :| AR.NfaRepL(rer, qm, r1, code, pc, e1) && AR.NfaRepL(rer, qm, r2, code, e1, pcmid);
        var na := [LS.Areg(r1), LS.Areg(r2)] + cont;
        assert na == [LS.Areg(r1)] + ([LS.Areg(r2)] + cont);
        assert AR.ActionRepL(rer, qm, LS.Areg(r2), code, e1, pcmid);
        assert ([LS.Areg(r2)] + cont)[0] == LS.Areg(r2) && ([LS.Areg(r2)] + cont)[1..] == cont;
        ATR.FuelToActionsRepL(rer, qm, cont, code, pcmid, n - 1);
        assert AR.ActionsRepL(rer, qm, [LS.Areg(r2)] + cont, code, e1);
        assert AR.ActionRepL(rer, qm, LS.Areg(r1), code, pc, e1);
        assert na[0] == LS.Areg(r1) && na[1..] == [LS.Areg(r2)] + cont;
        assert AR.ActionsRepL(rer, qm, na, code, pc);
        assert LS.ActionsRegexSize(na) < LS.ActionsRegexSize(acts);
        assert ATR.MsizeA(na) < ATR.MsizeA(acts);
        ATR.ActionsRepLToFuel(rer, qm, na, code, pc);
        var nn: nat :| ATR.ActionsRepFuelL(rer, qm, na, code, pc, nn);
        WO.WalkOkSeq(acts, code, pc, true, r1, r2);
        tcstar := AtBackForkTreeLkF(rer, qm, na, code, pc, inp, tc, nn);
      case Quantified(greedy, min, delta, r1) =>
        var gidl := L.DefGroups(r1);
        if min > 0 {
          match delta {
            case Inf =>
              if NUL.NonNullableL(r1) {
                var em, e1x := AR.NfaRepLPlusInv(rer, qm, greedy, min, r1, code, pc, pcmid);
                if em == pc {
                  assert false;    // SetQuantToClock != Fork
                } else {
                  var eb: nat :| (exists qid: int ::
                                    NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(qid, false))
                                    && qid in qm.quants && qm.quants[qid] == gidl)
                                 && AR.NfaRepL(rer, qm, r1, code, pc + 1, eb)
                                 && AR.NfaRepMinL(rer, qm, min - 2, r1, code, eb, em);
                  assert false;    // SetQuantToClock != Fork
                }
              } else {
                // §2.5a GENERIC: min >= 1 forced copies, so `pc` still carries a
                // clock-mark -- refuted against the pinned Fork just the same
                assert !greedy by {            // §2.5b interim (PikeLk conjunct)
                  assert acts[0] == LS.Areg(L.Quantified(greedy, min, delta, r1));
                }
                var em, e1x := AR.NfaRepLGenInv(rer, qm, greedy, min, r1, code, pc, pcmid);
                var eb: nat :| (exists qid: int ::
                                  NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(qid, false))
                                  && qid in qm.quants && qm.quants[qid] == gidl)
                               && AR.NfaRepL(rer, qm, r1, code, pc + 1, eb)
                               && AR.NfaRepMinL(rer, qm, min - 1, r1, code, eb, em);
                assert false;    // SetQuantToClock != Fork
              }
            case NN(kx) =>
              var em := AR.NfaRepLQuantInv(rer, qm, greedy, min, kx, r1, code, pc, pcmid);
              var eb: nat :| (exists qid: int ::
                                NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(qid, false))
                                && qid in qm.quants && qm.quants[qid] == gidl)
                             && AR.NfaRepL(rer, qm, r1, code, pc + 1, eb)
                             && AR.NfaRepMinL(rer, qm, min - 1, r1, code, eb, em);
              assert false;      // SetQuantToClock != Fork
          }
        } else if delta.NN? {
          var k := delta.n;
          var em := AR.NfaRepLQuantInv(rer, qm, greedy, 0, k, r1, code, pc, pcmid);
          assert em == pc;
          if k == 0 {
            assert pc == pcmid;
            WO.WalkOkQuantSpent(acts, code, pc, true, greedy, r1);
            assert LS.ActionsRegexSize(cont) < LS.ActionsRegexSize(acts);
            assert ATR.MsizeA(cont) < ATR.MsizeA(acts);
            tcstar := AtBackForkTreeLkF(rer, qm, cont, code, pc, inp, tc, n - 1);
          } else {
            var e1: nat :| NR.GetPcRE(code, pc) == Some(if greedy then RB.Fork(pc + 1, pcmid) else RB.Fork(pcmid, pc + 1))
                           && (exists qid: int ::
                                 NR.GetPcRE(code, pc + 1) == Some(RB.SetQuantToClock(qid, false))
                                 && qid in qm.quants && qm.quants[qid] == gidl)
                           && NR.GetPcRE(code, pc + 2) == Some(RB.BeginLoop)
                           && AR.NfaRepL(rer, qm, r1, code, pc + 3, e1)
                           && NR.GetPcRE(code, e1) == Some(RB.EndLoop)
                           && AR.NfaRepOptL(rer, qm, k - 1, greedy, r1, code, e1 + 1, pcmid);
            AR.NfaRepIncrL(rer, qm, r1, code, pc + 3, e1);
            AR.NfaRepIncrOptL(rer, qm, k - 1, greedy, r1, code, e1 + 1, pcmid);
            assert false;   // a bounded layer pins a FORWARD fork
          }
        } else {
          assert min == 0 && delta == LN.Inf;
          if exists e1: nat :: NR.GetPcRE(code, pc) == Some(if greedy then RB.Fork(pc + 1, e1 + 2) else RB.Fork(e1 + 2, pc + 1))
                               && (exists qid: int ::
                                     NR.GetPcRE(code, pc + 1) == Some(RB.SetQuantToClock(qid, false))
                                     && qid in qm.quants && qm.quants[qid] == gidl)
                               && NR.GetPcRE(code, pc + 2) == Some(RB.BeginLoop)
                               && AR.NfaRepL(rer, qm, r1, code, pc + 3, e1)
                               && NR.GetPcRE(code, e1) == Some(RB.EndLoop)
                               && NR.GetPcRE(code, e1 + 1) == Some(RB.Jmp(pc))
                               && pcmid == e1 + 2 {
            var e1: nat :| NR.GetPcRE(code, pc) == Some(if greedy then RB.Fork(pc + 1, e1 + 2) else RB.Fork(e1 + 2, pc + 1))
                           && AR.NfaRepL(rer, qm, r1, code, pc + 3, e1)
                           && pcmid == e1 + 2;
            AR.NfaRepIncrL(rer, qm, r1, code, pc + 3, e1);
            assert false;   // the fast path pins a forward fork
          } else {
            // THE LOOP VIEW: the star seen from the fork itself
            assert NUL.NonNullableL(r1);
            var em: nat :| NR.GetPcRE(code, pc) == Some(if greedy then RB.Fork(em, pc + 1) else RB.Fork(pc + 1, em))
                           && em <= pc
                           && (exists qid: int ::
                                 NR.GetPcRE(code, em) == Some(RB.SetQuantToClock(qid, false))
                                 && qid in qm.quants && qm.quants[qid] == gidl)
                           && AR.NfaRepL(rer, qm, r1, code, em + 1, pc)
                           && pcmid == pc + 1;
            var qid: int :| NR.GetPcRE(code, em) == Some(RB.SetQuantToClock(qid, false))
                            && qid in qm.quants && qm.quants[qid] == gidl;
            var q0 := L.Quantified(greedy, 0, FS.NoiPred(delta), r1);
            assert q0 == L.Quantified(greedy, 0, LN.Inf, r1) == r;
            WO.WalkOkLoopView(acts, code, pc, true, greedy, LN.Inf, r1,
                              if greedy then em else pc + 1,
                              if greedy then pc + 1 else em, inp);
            match tc {
              case Choice(cta, ctb) =>
                var itert := if greedy then cta else ctb;
                var skipt := if greedy then ctb else cta;
                match itert {
                  case GroupActionT(g, ti) =>
                    assert g == LG.Reset(gidl);
                    var il := [LS.Areg(r1), LS.Acheck(inp), LS.Areg(q0)] + cont;
                    assert EL.BoolTreeLk(rer, il, inp, BS.CannotExit, ti);
                    // skip branch: the general construction at the exit arm
                    assert CE.PSize(skipt) < CE.PSize(tc);
                    var subs := ActionsTreeRepLkF(rer, qm, cont, code, pc + 1, inp, BS.CanExit, skipt, n - 1);
                    // iteration branch: lift to CanExit, then bridge
                    EL.PikeLkActionsConsIff(LS.Areg(q0), cont);
                    EL.PikeLkActionsConsIff(LS.Acheck(inp), [LS.Areg(q0)] + cont);
                    EL.PikeLkActionsConsIff(LS.Areg(r1), [LS.Acheck(inp)] + ([LS.Areg(q0)] + cont));
                    assert il == [LS.Areg(r1)] + ([LS.Acheck(inp)] + ([LS.Areg(q0)] + cont)) by {
                      hide *;   // (§2.5b) pure seq-concat; the ambient axioms drown z3 4.14
                    }
                    assert EL.PikeLkActions(il);
                    assert CE.ShieldedActs(il) by {
                      forall i | 0 <= i < |il| && il[i].Acheck?
                        ensures exists j :: 0 <= j < i && il[j].Areg? && NUL.NonNullableL(il[j].r)
                      {
                        assert il[0] == LS.Areg(r1);
                        assert i > 0;
                        assert il[0].Areg? && NUL.NonNullableL(il[0].r);
                      }
                    }
                    CE.BoolFlagLift(rer, il, inp, ti);
                    assert EL.BoolTreeLk(rer, il, inp, BS.CanExit, ti);
                    // representation of the iteration list at em+1
                    ATR.FuelToActionsRepL(rer, qm, cont, code, pcmid, n - 1);
                    var lq := [LS.Areg(q0)] + cont;
                    assert AR.NfaRepL(rer, qm, q0, code, pc, pc + 1) by {
                      assert NUL.NonNullableL(r1)
                             && NR.GetPcRE(code, pc)
                                == Some(if greedy then RB.Fork(em, pc + 1) else RB.Fork(pc + 1, em))
                             && em <= pc
                             && (exists qid2: int ::
                                   NR.GetPcRE(code, em) == Some(RB.SetQuantToClock(qid2, false))
                                   && qid2 in qm.quants && qm.quants[qid2] == L.DefGroups(r1))
                             && AR.NfaRepL(rer, qm, r1, code, em + 1, pc);
                    }
                    assert AR.ActionRepL(rer, qm, LS.Areg(q0), code, pc, pc + 1);
                    assert lq[0] == LS.Areg(q0) && lq[1..] == cont;
                    assert AR.ActionsRepL(rer, qm, lq, code, pc);
                    var lc := [LS.Acheck(inp)] + lq;
                    assert AR.ActionRepL(rer, qm, LS.Acheck(inp), code, pc, pc);
                    assert lc[0] == LS.Acheck(inp) && lc[1..] == lq;
                    assert AR.ActionsRepL(rer, qm, lc, code, pc);
                    assert AR.ActionRepL(rer, qm, LS.Areg(r1), code, em + 1, pc);
                    assert il == [LS.Areg(r1)] + lc;
                    assert il[0] == LS.Areg(r1) && il[1..] == lc;
                    assert AR.ActionsRepL(rer, qm, il, code, em + 1);
                    ATR.ActionsRepLToFuel(rer, qm, il, code, em + 1);
                    var ni: nat :| ATR.ActionsRepFuelL(rer, qm, il, code, em + 1, ni);
                    assert CE.PSize(ti) < CE.PSize(tc);
                    var subi := ActionsTreeRepLkF(rer, qm, il, code, em + 1, inp, BS.CanExit, ti, ni);
                    // assemble: tr_reset at the stamp, then tr_plus at the
                    // fork — arms at (em, true)/(pc+1, true), the planted
                    // Progress consumed with the Choice
                    assert TreeRepLkRE(rer, qm, code, inp, subi, em + 1, true);
                    var iterstar := LT.GroupActionT(g, subi);
                    assert TreeRepLkRE(rer, qm, code, inp, iterstar, em, true);
                    tcstar := if greedy then LT.Choice(iterstar, subs) else LT.Choice(subs, iterstar);
                    assert TreeRepLkRE(rer, qm, code, inp, LT.Progress(tcstar), pc, true);
                    assert CE.ProgErase(iterstar) == CE.ProgErase(itert);
                    assert CE.ProgErase(tcstar) == CE.ProgErase(tc);
                  case _ =>
                }
              case _ =>
            }
          }
        }
      case Group(gid, r1) =>
        var e1: nat :| NR.GetPcRE(code, pc) == Some(RB.SetRegisterToCP(CP.start_reg(gid as int)))
                       && AR.NfaRepL(rer, qm, r1, code, pc + 1, e1)
                       && NR.GetPcRE(code, e1) == Some(RB.SetRegisterToCP(CP.end_reg(gid as int)))
                       && pcmid == e1 + 1;
        assert false;   // SetRegisterToCP != Fork
      case LookaroundR(lk, r1) =>
        var lid: int :| NR.GetPcRE(code, pc)
                        == Some(if AR.PositiveL(lk) then RB.CheckOracle(lid)
                                                    else RB.NegCheckOracle(lid))
                        && lid in qm.looks && qm.looks[lid] == (lk, r1);
        assert false;   // CheckOracle/NegCheckOracle != Fork
      case Backreference(_) =>     // not pike
  }

  /** FRAME for GateStepValue's non-owned-group carry: a positive gate's merged
      map `LkResult(lk, tlk, gmt, inp).value` differs from the incoming `gmt`
      ONLY on the body's own `DefGroups(r1)` — the body tree is confined there
      (`LL.ComputeTrConfined`), so every leaf (and hence the first-leaf merge)
      agrees with `gmt` outside it. Lets the gate-step reuse the standing
      `GmtTieInside` for lids other than the one being crossed. */
  lemma LkResultAgreeOutside(rer: LW.RegExpRecord, lk: L.Lookaround, r1: L.Regex, inp: LC.Input,
                             tlk: LT.Tree, gmt: LG.GroupMap)
    requires L.Positivity(lk)
    requires EL.NoLkBrL(r1)
    requires tlk == LFU.ComputeTr(rer, [LS.Areg(r1)], inp, LG.Empty, L.LkDir(lk))
    requires LS.LkResult(lk, tlk, gmt, inp).Some?
    ensures LL.GmAgreeOutside(LS.LkResult(lk, tlk, gmt, inp).value, gmt,
                              set g | g in L.DefGroups(r1))
  {
    var S := set g | g in L.DefGroups(r1);
    assert LL.DefGroupsIn(r1, S);
    LL.ComputeTrConfined(rer, r1, inp, LG.Empty, L.LkDir(lk), S);   // GmConfinedTree(tlk, S)
    var dir := L.LkDir(lk);
    var tr := LT.TreeRes(tlk, gmt, inp, dir);
    // positive-gate unfold: LkResult.value == TreeRes(tlk, gmt, inp, dir).value.1
    assert LS.LkResult(lk, tlk, gmt, inp).value == tr.value.1;
    LT.FirstTreeLeaf(tlk, gmt, inp, dir);                           // tr == HdError(TreeLeaves)
    var leaves := LT.TreeLeaves(tlk, gmt, inp, dir);
    assert |leaves| > 0 && tr.value == leaves[0];
    LL.GmConfinedLeaves(tlk, gmt, inp, dir, S);                     // each leaf agrees gmt outside S
    assert LL.GmAgreeOutside(leaves[0].1, gmt, S);
  }

  /** (L4 NESTED) `LkResultAgreeOutside` for a look body that may itself contain
      nested looks: the depth-1 `NoLkBrL(r1)` (body look-free) is replaced by
      the recursive `EL.PikeLkRegexRec(r1)`, and the confinement walk uses the
      depth-k `ComputeTrConfinedRec`/`GmConfinedLeavesRec` (recursive
      `LkConfinedTreeRec`) — the outer tree still writes only `DefGroups(r1)`, so
      the outside-S agreement is identical. */
  lemma LkResultAgreeOutsideNested(rer: LW.RegExpRecord, lk: L.Lookaround, r1: L.Regex, inp: LC.Input,
                                   tlk: LT.Tree, gmt: LG.GroupMap)
    requires L.Positivity(lk)
    requires EL.PikeLkRegexRec(r1)
    requires tlk == LFU.ComputeTr(rer, [LS.Areg(r1)], inp, LG.Empty, L.LkDir(lk))
    requires LS.LkResult(lk, tlk, gmt, inp).Some?
    ensures LL.GmAgreeOutside(LS.LkResult(lk, tlk, gmt, inp).value, gmt,
                              set g | g in L.DefGroups(r1))
  {
    var S := set g | g in L.DefGroups(r1);
    assert LL.DefGroupsIn(r1, S);
    LL.ComputeTrConfinedRec(rer, r1, inp, LG.Empty, L.LkDir(lk), S);   // LkConfinedTreeRec(tlk, S)
    var dir := L.LkDir(lk);
    var tr := LT.TreeRes(tlk, gmt, inp, dir);
    // positive-gate unfold: LkResult.value == TreeRes(tlk, gmt, inp, dir).value.1
    assert LS.LkResult(lk, tlk, gmt, inp).value == tr.value.1;
    LT.FirstTreeLeaf(tlk, gmt, inp, dir);                           // tr == HdError(TreeLeaves)
    var leaves := LT.TreeLeaves(tlk, gmt, inp, dir);
    assert |leaves| > 0 && tr.value == leaves[0];
    LL.GmConfinedLeavesRec(tlk, gmt, inp, dir, S);                  // each leaf agrees gmt outside S
    assert LL.GmAgreeOutside(leaves[0].1, gmt, S);
  }

  /** (2) THE GATE VALUE STEP — the crux, and it is the PROVEN keystone
      re-packaged. When the VM crosses `CheckOracle(l)` at `cp` (writing
      `a_cp[l] := cp` with the bit set), the B head's LK node dissolves and the
      merged `LkResult` values on the body's groups equal the FRESH REPLAY at
      the just-written `a_cp[l]` — i.e. `GmtTieInside` is re-established for
      the new entries, and `GateAheadClear` supplies the keystone's
      `GmAgreeOn(gmt, Empty, DefGroups(body))` hypothesis.
      FILL: instantiate `M.LkReplayMatchesSpec` at `cp`; the per-lid static
      package (`StaticOkRE`/`SizesOkRE`/body compile/`LookEntryOk`) comes from
      `M.LookRowsFromTablesL3a`'s bundle; `CM.RegsAgreeInside(cap, init,
      CaptureRegs(body))` from the standing `LooksCapUnset` +
      `CaptureBytecodeClassifiedOutside`; `OracleOkSuffix` via
      `LL.OracleOkSuffixStep`. The statement below is the SEAM to adjust
      against the keystone's exact ensures.

      FILL RECIPE (reverse-engineered 2026-08-03): this does NOT need the walk
      peel — it is a pure value step. `M.LkReplayMatchesSpec` (MainTheorem.dfy:
      4253) is the keystone; its ensures ties `LS.LkResult(TrLookaround(la),
      tlk, gmMain, inp).value` to `PIV.GmOfLive(body, rf.captures...)` on
      `S' = DefGroups(Translate(body))`, with `rf = FFindMatch(bodycode, ...,
      init regs at cp)` — which is EXACTLY `M.FreshBodyMatch(crv,str,l,...)`.
      So: (1) SIGNATURE IS UNDERSPECIFIED — add the keystone's requires (its
      static package from `LookRowsFromTablesL3a`, `body == VBody(crv,l)`,
      `bodycode == compile_to_bytecode(body)`, `LookFreeRE(body)`,
      `RegsAgreeInside(cap,init,CaptureRegs(body))`, and note `gmMain := gmt`).
      The `GmAgreeOn(gmt, Empty, DefGroups(Translate(body)))` keystone hyp IS
      the `GateAheadClear`-derived `forall g in DefGroups(r1) ==> g !in gmt`
      requires already present (Empty and gmt agree on absent groups).
      (2) SPLIT g in S ∩ gmt2 by owner: g owned by l ⇒ new value via keystone;
      g owned by l'' != l ⇒ preserved from GmtTieInside(th) since th2 only
      changed a_cp[l] and FreshBodyMatch(l'') reads only a_cp[l''] (stable);
      owner uniqueness from `M.LmOfBodiesDisjoint`. `MatchedPosLA(th2,l)` holds
      because th2 set look_regs[l] := Some(cp).

      READY-TO-WRITE RECIPE (2026-08-03 — every ingredient located/verified):
      add params `body, la, bodycode, endl, ngroups, qt` + requires
      `r1==T.Translate(body)`, `lk==T.TrLookaround(la)`, `body==M.VBody(crv,l)`,
      `PSM.StaticOkRE(qm,body,bodycode,endl)`, `PSM.SizesOkRE(body,ncap,nlook,
      nquant)`, `bodycode==CP.compile_to_bytecode(body)`, `NR.LookFreeRE(body)`,
      `la.Lookahead?`, `T.TransWf(body)`, `|qt.a_cp|==nquant && |qt.a_clk|==
      nquant`, `LL.OracleOkSuffix(rer,qm,InpOfCp(str,cp))`, and the l-th table
      bounds/type (`0<=l<nlook`, `0<=l<|crv.f_look_{ast,cdns,types}|`,
      `crv.f_look_types[l].Lookahead?`, `AI.capture_type(crv.f_look_types[l])`,
      `RL.ASize(th.look_regs)>l`). BODY:
      (a) tlk bridge: `EL.TranslateNoLkBr(body)` (⇒NoLkBrL(r1)) +
          `EL.ComputeTrGmIndepLk(rer,r1,inp,gmt,Forward)` ⇒ LkGateOk's Empty-tlk
          == keystone's gmt-tlk.
      (b) keystone Empty-hyp: `M.GmAgreeOn(gmt,Empty,DefGroups(r1))` from the
          GateAheadClear requires (g in DefGroups(r1) ⇒ g!in gmt; Empty has none).
      (c) call `M.LkReplayMatchesSpec(rer,qm,body,bodycode,endl,ngroups,str,cp,
          AReg.init_regs(ncap),AReg.init_regs(nlook),qt,ov,crv.f_look_cdns[l],la,
          tlk,gmt,ncap,nlook,nquant)` — cap=init makes RegsAgreeInside reflexive;
          LkResult.Some ⇒ ra.Some ⇒ rf.Some && GmAgreeOn(gmt2,GmOfLive(body,rf),
          DefGroups(Translate(body))). Its rf == M.FreshBodyMatch(crv,str,l,th2)
          because get_cp(th2.look_regs,l)==Some(cp) (RL.ASetLaws) and body/cdn/cp
          align.
      (d) forall g in S∩gmt2: `M.TranslateDefGroupsEqCapIds(body)` (DefGroups(r1)
          ==CapIds(body)==CapIds(VBody(crv,l))); if g in DefGroups(r1) ⇒ owner l
          via keystone GmAgreeOn; else `LkResultAgreeOutside(rer,lk,r1,inp,tlk,
          gmt)` (VERIFIED above) gives gmt2[g]==gmt[g], reduce to GmtTieInside(th)
          with owner l'!=l (l'==l impossible: g!in CapIds(VBody(crv,l))); carry
          MatchedPosLA/FreshBodyMatch across the l-only set_reg via RL.ASetLaws
          (get_cp at l'!=l unchanged ⇒ FreshBodyMatch(l',th2)==FreshBodyMatch(
          l',th)). */
  lemma GateStepValue(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code,
                      crv: CP.FCompiled, str: string, ov: LOr.OracleView, S: set<LG.GroupId>,
                      lk: L.Lookaround, r1: L.Regex, tlk: LT.Tree, tb: LT.Tree,
                      gmt: LG.GroupMap, th: AI.Thread, th2: AI.Thread, l: int, cp: nat,
                      body: R.regex, la: R.lookaround, bodycode: RB.code, endl: nat, ngroups: nat,
                      qt: AReg.Regs, ncap: int, nlook: int, nquant: int)
    requires qm.ov == ov && !rer.ignoreCase && !rer.multiline
    requires cp <= |str|
    requires l in qm.looks && qm.looks[l] == (lk, r1)
    requires L.Positivity(lk) && L.LkDir(lk) == WP.Forward
    requires LS.LkResult(lk, tlk, gmt, PIV.InpOfCp(str, cp)).Some?
    requires EL.LkGateOk(rer, lk, r1, PIV.InpOfCp(str, cp), tlk, true)
    // th2 = th with a_cp[l] := cp at some clock stamp (the CheckOracle write)
    requires exists clkv: int {:trigger AReg.set_reg(th.look_regs, l, Some(cp as int), clkv)} ::
               th2 == th.(pc := th.pc + 1,
               look_regs := AReg.set_reg(th.look_regs, l, Some(cp as int), clkv))
    requires GmtTieInside(crv, str, ov, th, gmt, S, ncap, nlook, nquant)
    requires forall g :: g in L.DefGroups(r1) ==> g !in gmt        // GateAheadClear at this gate
    // --- the keystone's static package + the l-th table identification ---
    requires T.TransWf(body) && NR.LookFreeRE(body) && la.Lookahead?
    requires r1 == T.Translate(body) && lk == T.TrLookaround(la) && body == M.VBody(crv, l)
    requires bodycode == CP.compile_to_bytecode(body)
    requires PSM.StaticOkRE(qm, body, bodycode, endl)
    requires PSM.SizesOkRE(body, ncap, nlook, nquant)
    requires |qt.a_cp| == nquant && |qt.a_clk| == nquant
    requires LL.OracleOkSuffix(rer, qm, PIV.InpOfCp(str, cp))
    requires 0 <= l < nlook && l < RL.ASize(th.look_regs)
    requires 0 <= l < |crv.f_look_ast| && 0 <= l < |crv.f_look_cdns| && 0 <= l < |crv.f_look_types|
    requires crv.f_look_types[l].Lookahead? && AI.capture_type(crv.f_look_types[l])
    ensures var gmt2 := LS.LkResult(lk, tlk, gmt, PIV.InpOfCp(str, cp)).value;
            GmtTieInside(crv, str, ov, th2, gmt2, S, ncap, nlook, nquant)
  {
    var inp := PIV.InpOfCp(str, cp);
    var tr := T.Translate(body);
    var gmt2 := LS.LkResult(lk, tlk, gmt, inp).value;
    var Sbody := set g | g in L.DefGroups(tr);
    var clkv: int :| th2 == th.(pc := th.pc + 1,
                            look_regs := AReg.set_reg(th.look_regs, l, Some(cp as int), clkv));

    // ---- (a) tlk bridge: LkGateOk's Empty-tlk == keystone's gmt-tlk ----
    EL.TranslateNoLkBr(body);                                // NoLkBrL(tr)
    EL.ComputeTrGmIndepLk(rer, tr, inp, gmt, WP.Forward);    // ComputeTr(tr,gmt) == ComputeTr(tr,Empty)
    assert tlk == LFU.ComputeTr(rer, [LS.Areg(tr)], inp, gmt, WP.Forward);

    // ---- (b) the keystone's Empty-agreement hypothesis from GateAheadClear ----
    assert M.GmAgreeOn(gmt, LG.Empty, Sbody) by {
      forall g | g in Sbody
        ensures (g in gmt <==> g in LG.Empty) && (g in gmt ==> gmt[g] == LG.Empty[g])
      { assert g in L.DefGroups(r1); }
    }

    // ---- (c) invoke the keystone ----
    assert T.TrLookaround(la) == lk;
    M.LkReplayMatchesSpec(rer, qm, body, bodycode, endl, ngroups, str, cp,
                          AReg.init_regs(ncap), AReg.init_regs(nlook), qt, ov,
                          crv.f_look_cdns[l], la, tlk, gmt, ncap, nlook, nquant);
    var rfK := AI.FFindMatch(bodycode, str,
                             AI.FInitState(bodycode, cp, AReg.init_regs(ncap), AReg.init_regs(nlook),
                                           AReg.init_regs(nquant), 0, AI.cp_context(cp, str, LAnc.Forward)),
                             ov, LAnc.Forward, crv.f_look_cdns[l]).0;
    assert rfK.Some?;
    assert M.GmAgreeOn(gmt2,
                       PIV.GmOfLive(body, rfK.value.capture_regs, rfK.value.look_regs, rfK.value.quant_regs), Sbody);

    // ---- rf alignment: FreshBodyMatch(l, th2) == the keystone's rfK ----
    RL.ASetLaws(th.look_regs, l, Some(cp as int), clkv);
    assert AReg.get_cp(th2.look_regs, l) == Some(cp as int);
    assert cp as int == cp;
    var rfl := M.FreshBodyMatch(crv, str, l, th2.look_regs, ov, ncap, nlook, nquant);
    assert rfl == rfK;

    M.TranslateDefGroupsEqCapIds(body);                      // Sbody == CapIds(body) == CapIds(VBody(crv,l))
    assert Sbody == PIV.CapIds(body);

    // ---- (d) re-establish GmtTieInside for th2 / gmt2 ----
    forall g: LG.GroupId | g in S && g in gmt2
      ensures exists l': int ::
                0 <= l' < nlook
                && g in PIV.CapIds(M.VBody(crv, l'))
                && M.MatchedPosLA(crv, th2.look_regs, l')
                && var rf' := M.FreshBodyMatch(crv, str, l', th2.look_regs, ov, ncap, nlook, nquant);
                rf'.Some?
                && var gmb := PIV.GmOfLive(M.VBody(crv, l'), rf'.value.capture_regs,
                                           rf'.value.look_regs, rf'.value.quant_regs);
                var looktype := if 0 <= l' < |crv.f_look_types| then crv.f_look_types[l'] else R.Lookahead;
                g in gmb && gmt2[g] == (if looktype.Lookbehind? then LBV.SwapRange(gmb[g]) else gmb[g])
    {
      if g in Sbody {
        // Case A: g is owned by the gate just crossed (lid l), value from the keystone.
        var gmbK := PIV.GmOfLive(body, rfK.value.capture_regs, rfK.value.look_regs, rfK.value.quant_regs);
        assert g in gmbK && gmt2[g] == gmbK[g];              // keystone GmAgreeOn at g in Sbody
        assert g in PIV.CapIds(M.VBody(crv, l));             // Sbody == CapIds(body) == CapIds(VBody(crv,l))
        assert M.MatchedPosLA(crv, th2.look_regs, l);        // get_cp l = Some(cp); type Lookahead
        assert M.VBody(crv, l) == body && rfl == rfK;
        assert 0 <= l < nlook;                               // witness l' = l
      } else {
        // Case B: g owned by a DIFFERENT lid; gmt2 == gmt off Sbody (frame), carry GmtTieInside(th).
        LkResultAgreeOutside(rer, lk, r1, inp, tlk, gmt);    // GmAgreeOutside(gmt2, gmt, Sbody)
        assert g !in Sbody;
        assert g in gmt && gmt2[g] == gmt[g];
        assert exists l'': int ::
            0 <= l'' < nlook && g in PIV.CapIds(M.VBody(crv, l''))
            && M.MatchedPosLA(crv, th.look_regs, l'')
            && var rf'' := M.FreshBodyMatch(crv, str, l'', th.look_regs, ov, ncap, nlook, nquant);
            rf''.Some?
            && var gmb'' := PIV.GmOfLive(M.VBody(crv, l''), rf''.value.capture_regs,
                                         rf''.value.look_regs, rf''.value.quant_regs);
            var looktype := if 0 <= l'' < |crv.f_look_types| then crv.f_look_types[l''] else R.Lookahead;
            g in gmb'' && gmt[g] == (if looktype.Lookbehind? then LBV.SwapRange(gmb''[g]) else gmb''[g]);
        var l'': int :|
          0 <= l'' < nlook && g in PIV.CapIds(M.VBody(crv, l''))
          && M.MatchedPosLA(crv, th.look_regs, l'')
          && var rf'' := M.FreshBodyMatch(crv, str, l'', th.look_regs, ov, ncap, nlook, nquant);
          rf''.Some?
          && var gmb'' := PIV.GmOfLive(M.VBody(crv, l''), rf''.value.capture_regs,
                                       rf''.value.look_regs, rf''.value.quant_regs);
          var looktype := if 0 <= l'' < |crv.f_look_types| then crv.f_look_types[l''] else R.Lookahead;
          g in gmb'' && gmt[g] == (if looktype.Lookbehind? then LBV.SwapRange(gmb''[g]) else gmb''[g]);
        // l'' != l: else g in CapIds(VBody(crv,l)) == Sbody, contradicting g !in Sbody.
        assert l'' != l by {
          if l'' == l { assert g in PIV.CapIds(M.VBody(crv, l)); }
        }
        // th2 differs from th only at slot l, so l'' reads the SAME cp on both banks.
        RL.ASetLaws(th.look_regs, l, Some(cp as int), clkv);
        assert AReg.get_cp(th2.look_regs, l'') == AReg.get_cp(th.look_regs, l'');
        assert M.MatchedPosLA(crv, th2.look_regs, l'');
        assert M.FreshBodyMatch(crv, str, l'', th2.look_regs, ov, ncap, nlook, nquant)
            == M.FreshBodyMatch(crv, str, l'', th.look_regs, ov, ncap, nlook, nquant);
      }
    }
  }

  /** THE LB TWIN of `GateStepValue`: a thread crossing a passing positive
      LOOKBEHIND gate lifts `GmtTieInside` across the merge to `(th2, gmt2)`. The
      inside-`Sbody` value is the ENDPOINT SWAP of the fresh BACKWARD body match
      (`LBK.BackFreshBodyGmTie`) — `gmt2[g] == SwapRange(gmbK[g])`, exactly the
      `looktype.Lookbehind?` arm of `GmtTieInside`. Case B (off `Sbody`) is the same
      frame carry as the lookahead twin. */
  lemma GateStepValueLB(
    rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code,
    crv: CP.FCompiled, str: string, ov: LOr.OracleView, S: set<LG.GroupId>,
    lk: L.Lookaround, r1: L.Regex, tlk: LT.Tree, tb: LT.Tree,
    gmt: LG.GroupMap, th: AI.Thread, th2: AI.Thread, l: int, cp: nat,
    body: R.regex, la: R.lookaround, bodycode: RB.code, endl: nat, ngroups: nat,
    qt: AReg.Regs, ncap: int, nlook: int, nquant: int)
    requires qm.ov == ov && !rer.ignoreCase && !rer.multiline
    requires cp <= |str| && |ov| == |str| + 1
    requires l in qm.looks && qm.looks[l] == (lk, r1)
    requires L.Positivity(lk) && L.LkDir(lk) == WP.Backward
    requires LS.LkResult(lk, tlk, gmt, PIV.InpOfCp(str, cp)).Some?
    requires EL.LkGateOk(rer, lk, r1, PIV.InpOfCp(str, cp), tlk, true)
    requires exists clkv: int {:trigger AReg.set_reg(th.look_regs, l, Some(cp as int), clkv)} ::
               th2 == th.(pc := th.pc + 1,
               look_regs := AReg.set_reg(th.look_regs, l, Some(cp as int), clkv))
    requires GmtTieInside(crv, str, ov, th, gmt, S, ncap, nlook, nquant)
    requires forall g :: g in L.DefGroups(r1) ==> g !in gmt        // GateAheadClear at this gate
    requires T.TransWf(body) && NR.LookFreeRE(body) && la.Lookbehind?
    requires NR.PlusFragmentRE(body) && PIV.CapUnique(body) && PIV.QuantUnique(body)
    requires SD.GroupOkL(T.Translate(body)) && CD.NoDupG(L.DefGroups(T.Translate(body)))
    requires r1 == T.Translate(body) && lk == T.TrLookaround(la) && body == M.VBody(crv, l)
    requires bodycode == CP.compile_to_bytecode(body)
    requires PSM.StaticOkRE(qm, body, bodycode, endl)
    requires PSM.SizesOkRE(body, ncap, nlook, nquant)
    requires |qt.a_cp| == nquant && |qt.a_clk| == nquant
    requires LL.OracleOkSuffix(rer, qm, PIV.InpOfCp(str, cp))
    requires 0 <= l < nlook && l < RL.ASize(th.look_regs)
    requires 0 <= l < |crv.f_look_ast| && 0 <= l < |crv.f_look_cdns| && 0 <= l < |crv.f_look_types|
    requires crv.f_look_types[l].Lookbehind? && AI.capture_type(crv.f_look_types[l])
    ensures var gmt2 := LS.LkResult(lk, tlk, gmt, PIV.InpOfCp(str, cp)).value;
            GmtTieInside(crv, str, ov, th2, gmt2, S, ncap, nlook, nquant)
  {
    var inp := PIV.InpOfCp(str, cp);
    var tr := T.Translate(body);
    var gmt2 := LS.LkResult(lk, tlk, gmt, inp).value;
    var Sbody := set g | g in L.DefGroups(tr);
    var clkv: int :| th2 == th.(pc := th.pc + 1,
                            look_regs := AReg.set_reg(th.look_regs, l, Some(cp as int), clkv));

    // ---- (a) tlk bridge (BACKWARD): LkGateOk's Empty-tlk == the gmt-tlk ----
    EL.TranslateNoLkBr(body);
    EL.ComputeTrGmIndepLk(rer, tr, inp, gmt, WP.Backward);
    assert tlk == LFU.ComputeTr(rer, [LS.Areg(tr)], inp, gmt, WP.Backward);

    // ---- (b) the keystone's Empty-agreement hypothesis from GateAheadClear ----
    assert M.GmAgreeOn(gmt, LG.Empty, Sbody) by {
      forall g | g in Sbody
        ensures (g in gmt <==> g in LG.Empty) && (g in gmt ==> gmt[g] == LG.Empty[g])
      { assert g in L.DefGroups(r1); }
    }

    // ---- (c) invoke the BACKWARD value crux ----
    assert T.TrLookaround(la) == lk;
    LBK.BackFreshBodyGmTie(rer, body, str, cp, ov, crv.f_look_cdns[l], la, tlk, gmt,
                           ncap, nlook, nquant, |str|);
    var bcB := CP.compile_to_bytecode(R.reverse_regex(body));
    var raB := AI.FFindMatch(bcB, str,
                             AI.FInitState(bcB, cp, AReg.init_regs(ncap), AReg.init_regs(nlook),
                                           AReg.init_regs(nquant), 0, AI.cp_context(cp, str, LAnc.Backward)),
                             ov, LAnc.Backward, crv.f_look_cdns[l]).0;

    // ---- rf alignment: FreshBodyMatch(l, th2) == the backward run raB ----
    RL.ASetLaws(th.look_regs, l, Some(cp as int), clkv);
    assert AReg.get_cp(th2.look_regs, l) == Some(cp as int);
    assert CP.capture_regex(crv.f_look_types[l], body) == R.reverse_regex(body);   // Lookbehind
    assert AI.capture_direction(crv.f_look_types[l]) == LAnc.Backward;
    var rfl := M.FreshBodyMatch(crv, str, l, th2.look_regs, ov, ncap, nlook, nquant);
    assert rfl == raB;

    M.TranslateDefGroupsEqCapIds(body);                      // Sbody == CapIds(body) == CapIds(VBody(crv,l))
    assert Sbody == PIV.CapIds(body);

    // ---- (d) re-establish GmtTieInside for th2 / gmt2 ----
    forall g: LG.GroupId | g in S && g in gmt2
      ensures exists l': int ::
                0 <= l' < nlook
                && g in PIV.CapIds(M.VBody(crv, l'))
                && M.MatchedPosLA(crv, th2.look_regs, l')
                && var rf' := M.FreshBodyMatch(crv, str, l', th2.look_regs, ov, ncap, nlook, nquant);
                rf'.Some?
                && var gmb := PIV.GmOfLive(M.VBody(crv, l'), rf'.value.capture_regs,
                                           rf'.value.look_regs, rf'.value.quant_regs);
                var looktype := if 0 <= l' < |crv.f_look_types| then crv.f_look_types[l'] else R.Lookahead;
                g in gmb && gmt2[g] == (if looktype.Lookbehind? then LBV.SwapRange(gmb[g]) else gmb[g])
    {
      if g in Sbody {
        // Case A: g owned by the crossed lookbehind l; value = SWAP of the fresh backward match.
        var gmbK := PIV.GmOfLive(body, rfl.value.capture_regs, rfl.value.look_regs, rfl.value.quant_regs);
        assert g in gmbK && LBV.SwapGm(gmt2)[g] == gmbK[g];   // BackFreshBodyGmTie GmAgreeOn at g in Sbody
        assert LBV.SwapGm(gmt2)[g] == LBV.SwapRange(gmt2[g]);
        LBV.SwapRangeInvol(gmt2[g]);
        assert gmt2[g] == LBV.SwapRange(gmbK[g]);
        assert g in PIV.CapIds(M.VBody(crv, l));
        assert M.MatchedPosLA(crv, th2.look_regs, l);          // get_cp l = Some(cp); type Lookbehind
        assert M.VBody(crv, l) == body && rfl == raB;
        assert 0 <= l < nlook;                                 // witness l' = l
      } else {
        // Case B: g owned by a DIFFERENT lid; gmt2 == gmt off Sbody (frame), carry GmtTieInside(th).
        LkResultAgreeOutside(rer, lk, r1, inp, tlk, gmt);      // GmAgreeOutside(gmt2, gmt, Sbody)
        assert g !in Sbody;
        assert g in gmt && gmt2[g] == gmt[g];
        assert exists l'': int ::
            0 <= l'' < nlook && g in PIV.CapIds(M.VBody(crv, l''))
            && M.MatchedPosLA(crv, th.look_regs, l'')
            && var rf'' := M.FreshBodyMatch(crv, str, l'', th.look_regs, ov, ncap, nlook, nquant);
            rf''.Some?
            && var gmb'' := PIV.GmOfLive(M.VBody(crv, l''), rf''.value.capture_regs,
                                         rf''.value.look_regs, rf''.value.quant_regs);
            var looktype := if 0 <= l'' < |crv.f_look_types| then crv.f_look_types[l''] else R.Lookahead;
            g in gmb'' && gmt[g] == (if looktype.Lookbehind? then LBV.SwapRange(gmb''[g]) else gmb''[g]);
        var l'': int :|
          0 <= l'' < nlook && g in PIV.CapIds(M.VBody(crv, l''))
          && M.MatchedPosLA(crv, th.look_regs, l'')
          && var rf'' := M.FreshBodyMatch(crv, str, l'', th.look_regs, ov, ncap, nlook, nquant);
          rf''.Some?
          && var gmb'' := PIV.GmOfLive(M.VBody(crv, l''), rf''.value.capture_regs,
                                       rf''.value.look_regs, rf''.value.quant_regs);
          var looktype := if 0 <= l'' < |crv.f_look_types| then crv.f_look_types[l''] else R.Lookahead;
          g in gmb'' && gmt[g] == (if looktype.Lookbehind? then LBV.SwapRange(gmb''[g]) else gmb''[g]);
        assert l'' != l by {
          if l'' == l { assert g in PIV.CapIds(M.VBody(crv, l)); }
        }
        RL.ASetLaws(th.look_regs, l, Some(cp as int), clkv);
        assert AReg.get_cp(th2.look_regs, l'') == AReg.get_cp(th.look_regs, l'');
        assert M.MatchedPosLA(crv, th2.look_regs, l'');
        assert M.FreshBodyMatch(crv, str, l'', th2.look_regs, ov, ncap, nlook, nquant)
            == M.FreshBodyMatch(crv, str, l'', th.look_regs, ov, ncap, nlook, nquant);
      }
    }
  }

  // ==========================================================================
  // (4a) THE ε-PHASE CASE TIER — per-VM-worklist-step preservation lemmas,
  // mirroring PSM's Preserve*Case set. Each takes the pre-states (bst, s), the
  // ticked state s1 (clock+1, slot marked processed) and the case's successor
  // vms2, and returns the B successor with its step(s) and LiftInv(bst1, vms2).
  // The canonical tie (TreeRepLkREAt*) pins the head shape; the raw
  // erasure-witness carries the value layer through the proven cores.
  // ==========================================================================

  /** `TrcPikeTreeLk` is reflexive. */
  lemma TrcLkRefl(s: PT.PikeTreeState)
    ensures PTL.TrcPikeTreeLk(s, s)
  {}

  /** Prepending one `PikeTreeStepLk` keeps a `TrcPikeTreeLk` chain. */
  lemma TrcLkCons(s1: PT.PikeTreeState, mid: PT.PikeTreeState, s2: PT.PikeTreeState)
    requires PTL.PikeTreeStepLk(s1, mid)
    requires PTL.TrcPikeTreeLk(mid, s2)
    ensures PTL.TrcPikeTreeLk(s1, s2)
  {}

  /** Step-counted `TrcPikeTreeLk` — the nat-indexed detour that lets
      transitivity avoid a two-least-requires induction (PSM's `TrcN` shape). */
  ghost predicate TrcLkN(a: PT.PikeTreeState, b: PT.PikeTreeState, n: nat)
    decreases n
  {
    (a == b && n == 0)
    || (n > 0 && exists z :: PTL.PikeTreeStepLk(a, z) && TrcLkN(z, b, n - 1))
  }

  /** Every `TrcPikeTreeLk` chain has a finite step count. */
  least lemma TrcLkToN(a: PT.PikeTreeState, b: PT.PikeTreeState)
    requires PTL.TrcPikeTreeLk(a, b)
    ensures exists n: nat :: TrcLkN(a, b, n)
  {
    if a == b {
      assert TrcLkN(a, b, 0);
    } else {
      var z :| PTL.PikeTreeStepLk(a, z) && PTL.TrcPikeTreeLk(z, b);
      TrcLkToN(z, b);
      var n: nat :| TrcLkN(z, b, n);
      assert TrcLkN(a, b, n + 1);
    }
  }

  /** A counted chain is a plain chain. */
  lemma TrcLkFromN(a: PT.PikeTreeState, b: PT.PikeTreeState, n: nat)
    requires TrcLkN(a, b, n)
    ensures PTL.TrcPikeTreeLk(a, b)
    decreases n
  {
    if a == b && n == 0 {
    } else {
      var z :| PTL.PikeTreeStepLk(a, z) && TrcLkN(z, b, n - 1);
      TrcLkFromN(z, b, n - 1);
      TrcLkCons(a, z, b);
    }
  }

  /** `TrcLkN` is transitive with counts adding. */
  lemma TrcLkNTrans(a: PT.PikeTreeState, b: PT.PikeTreeState, c: PT.PikeTreeState, n: nat, m: nat)
    requires TrcLkN(a, b, n)
    requires TrcLkN(b, c, m)
    ensures TrcLkN(a, c, n + m)
    decreases n
  {
    if a == b && n == 0 {
    } else {
      var z :| PTL.PikeTreeStepLk(a, z) && TrcLkN(z, b, n - 1);
      TrcLkNTrans(z, b, c, n - 1, m);
    }
  }

  /** A canonical head sits at a fetchable pc (every rule pins an instruction). */
  lemma TreeRepLkREInRange(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                           t: LT.Tree, pc: nat, b: bool)
    requires TreeRepLkRE(rer, qm, code, inp, t, pc, b)
    ensures NR.GetPcRE(code, pc).Some? && pc < |code|
  { }

  /** POLARITY PIN at gate pcs — the static sweep tying a `CheckOracle` /
      `NegCheckOracle` instruction to its look's recorded flavour through
      `qm.looks`: `NfaRepRE`'s lookaround rule CHOOSES the instruction by the
      look's positivity, and `LmapOk` records the table row. This is what lets
      the kill/pass gate cases read the FUNCTIONAL verdict off the oracle BIT
      (`LkResult` branches on `Positivity`). `PIV.LookCheckIdsRE`'s skeleton. */
  lemma GatePolarityRE(re: R.regex, qm: AR.QMap, code: RB.code, start: nat, endl: nat, pc: nat)
    requires T.TransWf(re) && AR.LmapOk(re, qm)
    requires NR.NfaRepRE(re, code, start, endl)
    requires start <= pc < endl
    ensures NR.GetPcRE(code, pc).Some? && NR.GetPcRE(code, pc).value.CheckOracle? ==>
              var l := NR.GetPcRE(code, pc).value.col;
              l in qm.looks && AR.PositiveL(qm.looks[l].0)
    ensures NR.GetPcRE(code, pc).Some? && NR.GetPcRE(code, pc).value.NegCheckOracle? ==>
              var l := NR.GetPcRE(code, pc).value.ncl;
              l in qm.looks && !AR.PositiveL(qm.looks[l].0)
    decreases CP.rsize(re), 1
  {
    match re
    case Re_empty =>
    case Re_character(_) =>
    case Re_anchor(_) =>
    case Re_lookaround(lid, la, r1) =>
      assert pc == start;
      assert lid in qm.looks && qm.looks[lid] == (T.TrLookaround(la), T.Translate(r1));
      assert AR.PositiveL(T.TrLookaround(la)) <==> (la.Lookahead? || la.Lookbehind?);
    case Re_alt(r1, r2) =>
      var e1: nat :| NR.GetPcRE(code, start) == Some(RB.Fork(start + 1, e1 + 1))
                     && NR.NfaRepRE(r1, code, start + 1, e1)
                     && NR.GetPcRE(code, e1) == Some(RB.Jmp(endl))
                     && NR.NfaRepRE(r2, code, e1 + 1, endl);
      NR.NfaRepIncrRE(r1, code, start + 1, e1);
      NR.NfaRepIncrRE(r2, code, e1 + 1, endl);
      if pc == start {
      } else if pc < e1 {
        GatePolarityRE(r1, qm, code, start + 1, e1, pc);
      } else if pc == e1 {
      } else {
        GatePolarityRE(r2, qm, code, e1 + 1, endl, pc);
      }
    case Re_con(r1, r2) =>
      var e1: nat :| NR.NfaRepRE(r1, code, start, e1) && NR.NfaRepRE(r2, code, e1, endl);
      NR.NfaRepIncrRE(r1, code, start, e1);
      NR.NfaRepIncrRE(r2, code, e1, endl);
      if pc < e1 {
        GatePolarityRE(r1, qm, code, start, e1, pc);
      } else {
        GatePolarityRE(r2, qm, code, e1, endl, pc);
      }
    case Re_capture(cid, r1) =>
      var e1: nat :| NR.GetPcRE(code, start) == Some(RB.SetRegisterToCP(CP.start_reg(cid)))
                     && NR.NfaRepRE(r1, code, start + 1, e1)
                     && NR.GetPcRE(code, e1) == Some(RB.SetRegisterToCP(CP.end_reg(cid)))
                     && endl == e1 + 1;
      NR.NfaRepIncrRE(r1, code, start + 1, e1);
      if pc == start {
      } else if pc < e1 {
        GatePolarityRE(r1, qm, code, start + 1, e1, pc);
      } else {
      }
    case Re_quant(nul, qid, q, r1) =>
      if q.min == 0 && q.max == None {
        var e1: nat :| NR.GetPcRE(code, start) == Some(if q.greedy then RB.Fork(start + 1, e1 + 2) else RB.Fork(e1 + 2, start + 1))
                       && NR.GetPcRE(code, start + 1) == Some(RB.SetQuantToClock(qid, false))
                       && NR.GetPcRE(code, start + 2) == Some(RB.BeginLoop)
                       && NR.NfaRepRE(r1, code, start + 3, e1)
                       && NR.GetPcRE(code, e1) == Some(RB.EndLoop)
                       && NR.GetPcRE(code, e1 + 1) == Some(RB.Jmp(start))
                       && endl == e1 + 2;
        NR.NfaRepIncrRE(r1, code, start + 3, e1);
        if pc <= start + 2 {
        } else if pc < e1 {
          GatePolarityRE(r1, qm, code, start + 3, e1, pc);
        } else {
        }
      } else if q.max.Some? {
        var em := NR.NfaRepREQuantInv(nul, qid, q, r1, code, start, endl);
        NR.NfaRepIncrMinRE(q.min as nat, qid, r1, code, start, em);
        NR.NfaRepIncrOptRE((q.max.value - q.min) as nat, q.greedy, qid, r1, code, em, endl);
        if pc < em {
          GatePolarityMinRE(q.min as nat, qid, r1, qm, code, start, em, pc);
        } else {
          GatePolarityOptRE((q.max.value - q.min) as nat, q.greedy, qid, r1, qm, code, em, endl, pc);
        }
      } else if nul != R.NonNullable && !q.greedy {
        // §2.5a GENERIC: min forced copies then the star loop; the loop's own
        // five instructions carry no oracle gate
        var em, e1 := NR.NfaRepREGenInv(nul, qid, q, r1, code, start, endl);
        NR.NfaRepIncrMinRE(q.min as nat, qid, r1, code, start, em);
        NR.NfaRepIncrRE(r1, code, em + 3, e1);
        if pc < em {
          GatePolarityMinRE(q.min as nat, qid, r1, qm, code, start, em, pc);
        } else if pc <= em + 2 {
        } else if pc < e1 {
          GatePolarityRE(r1, qm, code, em + 3, e1, pc);
        } else {
        }
      } else if nul != R.NonNullable {
        // §2.5b CIN-GREEDY: the loop's six own instructions carry no gate
        var em, e1 := NR.NfaRepRECinInv(nul, qid, q, r1, code, start, endl);
        NR.NfaRepIncrMinRE((q.min - 1) as nat, qid, r1, code, start, em);
        NR.NfaRepIncrRE(r1, code, em + 3, e1);
        if pc < em {
          GatePolarityMinRE((q.min - 1) as nat, qid, r1, qm, code, start, em, pc);
        } else if pc <= em + 2 {
        } else if pc < e1 {
          GatePolarityRE(r1, qm, code, em + 3, e1, pc);
        } else {
        }
      } else {
        var em, e1 := NR.NfaRepREPlusInv(nul, qid, q, r1, code, start, endl);
        NR.NfaRepIncrMinRE((q.min - 1) as nat, qid, r1, code, start, em);
        NR.NfaRepIncrRE(r1, code, em + 1, e1);
        if pc < em {
          GatePolarityMinRE((q.min - 1) as nat, qid, r1, qm, code, start, em, pc);
        } else if pc == em {
        } else if pc < e1 {
          GatePolarityRE(r1, qm, code, em + 1, e1, pc);
        } else {
        }
      }
  }

  /** `GatePolarityRE` for the forced-copy chain. */
  lemma GatePolarityMinRE(k: nat, qid: R.quantid, r1: R.regex, qm: AR.QMap, code: RB.code,
                          start: nat, endl: nat, pc: nat)
    requires T.TransWf(r1) && AR.LmapOk(r1, qm)
    requires NR.NfaRepMinRE(k, qid, r1, code, start, endl)
    requires start <= pc < endl
    ensures NR.GetPcRE(code, pc).Some? && NR.GetPcRE(code, pc).value.CheckOracle? ==>
              var l := NR.GetPcRE(code, pc).value.col;
              l in qm.looks && AR.PositiveL(qm.looks[l].0)
    ensures NR.GetPcRE(code, pc).Some? && NR.GetPcRE(code, pc).value.NegCheckOracle? ==>
              var l := NR.GetPcRE(code, pc).value.ncl;
              l in qm.looks && !AR.PositiveL(qm.looks[l].0)
    decreases CP.rsize(r1), k + 2
  {
    if k == 0 { return; }
    var e1: nat :| NR.GetPcRE(code, start) == Some(RB.SetQuantToClock(qid, false))
                   && NR.NfaRepRE(r1, code, start + 1, e1)
                   && NR.NfaRepMinRE(k - 1, qid, r1, code, e1, endl);
    NR.NfaRepIncrRE(r1, code, start + 1, e1);
    NR.NfaRepIncrMinRE(k - 1, qid, r1, code, e1, endl);
    if pc == start {
    } else if pc < e1 {
      GatePolarityRE(r1, qm, code, start + 1, e1, pc);
    } else {
      GatePolarityMinRE(k - 1, qid, r1, qm, code, e1, endl, pc);
    }
  }

  /** `GatePolarityRE` for the optional-layer chain. */
  lemma GatePolarityOptRE(k: nat, greedy: bool, qid: R.quantid, r1: R.regex, qm: AR.QMap,
                          code: RB.code, start: nat, endl: nat, pc: nat)
    requires T.TransWf(r1) && AR.LmapOk(r1, qm)
    requires NR.NfaRepOptRE(k, greedy, qid, r1, code, start, endl)
    requires start <= pc < endl
    ensures NR.GetPcRE(code, pc).Some? && NR.GetPcRE(code, pc).value.CheckOracle? ==>
              var l := NR.GetPcRE(code, pc).value.col;
              l in qm.looks && AR.PositiveL(qm.looks[l].0)
    ensures NR.GetPcRE(code, pc).Some? && NR.GetPcRE(code, pc).value.NegCheckOracle? ==>
              var l := NR.GetPcRE(code, pc).value.ncl;
              l in qm.looks && !AR.PositiveL(qm.looks[l].0)
    decreases CP.rsize(r1), k + 2
  {
    if k == 0 { return; }
    var e1: nat :| NR.GetPcRE(code, start) == Some(if greedy then RB.Fork(start + 1, endl) else RB.Fork(endl, start + 1))
                   && NR.GetPcRE(code, start + 1) == Some(RB.SetQuantToClock(qid, false))
                   && NR.GetPcRE(code, start + 2) == Some(RB.BeginLoop)
                   && NR.NfaRepRE(r1, code, start + 3, e1)
                   && NR.GetPcRE(code, e1) == Some(RB.EndLoop)
                   && NR.NfaRepOptRE(k - 1, greedy, qid, r1, code, e1 + 1, endl);
    NR.NfaRepIncrRE(r1, code, start + 3, e1);
    NR.NfaRepIncrOptRE(k - 1, greedy, qid, r1, code, e1 + 1, endl);
    if pc <= start + 2 {
    } else if pc < e1 {
      GatePolarityRE(r1, qm, code, start + 3, e1, pc);
    } else if pc == e1 {
    } else {
      GatePolarityOptRE(k - 1, greedy, qid, r1, qm, code, e1 + 1, endl, pc);
    }
  }

  /** The per-lid STATIC look-table package, bundled over `qm.looks`' domain:
      each gated lid has a correct `crv` row whose body is look-free, well-
      translated (`qm.looks[l]` IS the row's translation), compile-static
      (`StaticOkRE`/`SizesOkRE` for the body's own bytecode), value-confined
      (its groups are inside-look groups of `re`), and — for every flavour
      except the capturing `Lookahead` — capture-free. Threaded through
      `LiftStepC`/`LiftAdvanceEpsilon` into the gate-pass case; established
      once at the composite entry from the `FFullCompilation` tables. */
  ghost predicate GateStaticAt(qm: AR.QMap, re: R.regex, crv: CP.FCompiled, l: int,
                               ncap: int, nlook: int, nquant: int) {
    l in qm.looks
    && exists la: R.lookaround, body: R.regex ::
      LTB.LookEntryOk(crv, l, la, body)
      && T.TransWf(body) && NR.LookFreeRE(body)
      && NR.NoNulledPlusRE(body)   // §2.5b interim: all stamps false, per lid
      && qm.looks[l].0 == T.TrLookaround(la)
      && qm.looks[l].1 == T.Translate(body)
      && (set g: LG.GroupId | g in L.DefGroups(T.Translate(body))) <= PIV.CapIdsInLooks(re)
      && var bodycode := CP.compile_to_bytecode(body);
      |bodycode| >= 1
      && PSM.StaticOkRE(qm, body, bodycode, |bodycode| - 1)
      && PSM.SizesOkRE(body, ncap, nlook, nquant)
      && ((la.NegLookbehind? || la.NegLookahead?) ==> NR.CaptureFreeRE(body))
  }

  ghost predicate GateStaticsOk(qm: AR.QMap, re: R.regex, crv: CP.FCompiled,
                                ncap: int, nlook: int, nquant: int) {
    forall l: int | l in qm.looks ::
      0 <= l < nlook && GateStaticAt(qm, re, crv, l, ncap, nlook, nquant)
  }

  /** (L4 NESTED) depth-agnostic sibling of `GateStaticAt`: the per-lid look-
      table package with the body cap generalized off the DEPTH-1 look-free leaf.
      `NR.LookFreeRE(body)` becomes `NR.NestedFragmentRE(body)` (arbitrary look
      nesting) qualified by the positive-lookahead-nesting side conditions
      (`NR.NegLooksLookFreeRE(body)` — negative bodies stay look-free; and
      (L5 F7f) a KIND-SPLIT scope conjunct: a LOOKAHEAD (or negative) lid keeps the
      L4 fact `M.NoPosLookbehindRE(body)` — every forward path's pruning fact, without
      which the giant descent lemmas' VCs blow up — and a positive LOOKBEHIND lid gets
      `NR.LBOnlyLooksRE(body)`, what the LB paths consume. So the hub is satisfiable on
      the v1 L5 fragment: positive lookbehinds with lookbehind-only bodies, nested to any
      depth, while lookAHEAD bodies stay free of positive lookbehinds). The body's compile statics lift from
      `PSM.StaticOkRE` to `PSM.StaticOkNestedRE`. The `DefGroups(body) ⊆
      CapIdsInLooks(re)` confinement + the negative-capture-free clause are
      verbatim. On look-free bodies (`NestDepth(body) == 0`) it coincides with
      `GateStaticAt` (`GateStaticAtFromDepth1`). */
  ghost predicate GateStaticAtNested(qm: AR.QMap, re: R.regex, crv: CP.FCompiled, l: int,
                                     ncap: int, nlook: int, nquant: int) {
    l in qm.looks
    && exists la: R.lookaround, body: R.regex ::
      LTB.LookEntryOk(crv, l, la, body)
      && T.TransWf(body) && NR.NestedFragmentRE(body)
      && NR.NoNulledPlusRE(body)   // §2.5b interim: all stamps false, per lid
      && NR.NegLooksLookFreeRE(body)
      && (la.Lookbehind? ==> NR.LBOnlyLooksRE(body))
      && (!la.Lookbehind? ==> L5ScopeV1RE(body))
      && qm.looks[l].0 == T.TrLookaround(la)
      && qm.looks[l].1 == T.Translate(body)
      && (set g: LG.GroupId | g in L.DefGroups(T.Translate(body))) <= PIV.CapIdsInLooks(re)
      && var bodycode := CP.compile_to_bytecode(body);
      |bodycode| >= 1
      && PSM.StaticOkNestedRE(qm, body, bodycode, |bodycode| - 1)
      && PSM.SizesOkRE(body, ncap, nlook, nquant)
      && ((la.NegLookbehind? || la.NegLookahead?) ==> NR.CaptureFreeRE(body))
  }

  // ==========================================================================
  // (DEEP reverse-recon) The BODY-RESTRICTED qmap: `GateStaticsOkNested(·, host,
  // crv, ·)` quantifies over the table's WHOLE look domain, but its per-row
  // confinement (`DefGroups(row body) ⊆ CapIdsInLooks(host)`) can only hold for
  // rows INSIDE `host`. The recursion therefore instantiates the per-body sim
  // with `qm_b := qm` restricted to `host`'s own lids — these three transfer
  // lemmas move every qm-keyed hypothesis across the restriction.
  // ==========================================================================

  /** `QmapOk` reads only `qm.quants`: any looks-map change is irrelevant. */
  lemma QmapOkLooksIrrel(r: R.regex, qm: AR.QMap, qm2: AR.QMap)
    requires T.TransWf(r)
    requires AR.QmapOk(r, qm)
    requires qm2.quants == qm.quants
    ensures AR.QmapOk(r, qm2)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => QmapOkLooksIrrel(r1, qm, qm2); QmapOkLooksIrrel(r2, qm, qm2);
    case Re_con(r1, r2) => QmapOkLooksIrrel(r1, qm, qm2); QmapOkLooksIrrel(r2, qm, qm2);
    case Re_quant(_, _, _, r1) => QmapOkLooksIrrel(r1, qm, qm2);
    case Re_capture(_, r1) => QmapOkLooksIrrel(r1, qm, qm2);
    case Re_lookaround(_, _, r1) => QmapOkLooksIrrel(r1, qm, qm2);
    case _ =>
  }

  /** `LmapOk` survives restricting the looks map to a superset of `r`'s own
      lids: every look node of `r` keeps its (unchanged) entry. */
  lemma LmapOkRestrict(r: R.regex, qm: AR.QMap, qm2: AR.QMap)
    requires T.TransWf(r)
    requires AR.LmapOk(r, qm)
    requires forall l: int :: l in qm.looks ==> l >= 0
    requires forall l: int :: l in qm.looks && (l as nat) in LTB.LookIds(r) ==>
                                l in qm2.looks && qm2.looks[l] == qm.looks[l]
    ensures AR.LmapOk(r, qm2)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => LmapOkRestrict(r1, qm, qm2); LmapOkRestrict(r2, qm, qm2);
    case Re_con(r1, r2) => LmapOkRestrict(r1, qm, qm2); LmapOkRestrict(r2, qm, qm2);
    case Re_quant(_, _, _, r1) => LmapOkRestrict(r1, qm, qm2);
    case Re_capture(_, r1) => LmapOkRestrict(r1, qm, qm2);
    case Re_lookaround(lid, la, r1) =>
      assert lid in qm.looks;              // LmapOk at the node
      assert lid >= 0;                     // qm key fact
      assert (lid as nat) in LTB.LookIds(r);
      assert lid in qm2.looks && qm2.looks[lid] == qm.looks[lid];
      LmapOkRestrict(r1, qm, qm2);
    case _ =>
  }

  /** `OracleOkSuffix` survives restricting the looks map (fewer rows, same
      entries, same oracle view): the per-row bit truth is monotone down. */
  lemma OracleOkSuffixRestrict(rer: LW.RegExpRecord, qm: AR.QMap, qm2: AR.QMap, inp0: LC.Input)
    requires LL.OracleOkSuffix(rer, qm, inp0)
    requires qm2.ov == qm.ov
    requires forall l: int :: l in qm2.looks ==> l in qm.looks && qm2.looks[l] == qm.looks[l]
    ensures LL.OracleOkSuffix(rer, qm2, inp0)
  {
    forall inp: LC.Input | inp == inp0 || SSx.IsStrictSuffix(inp, inp0, WP.Forward)
      ensures LL.OracleOkAt(rer, qm2, inp)
    {
      assert LL.OracleOkAt(rer, qm, inp);
      forall lid: int, lk: L.Lookaround, r1: L.Regex |
        lid in qm2.looks && qm2.looks[lid] == (lk, r1)
        ensures LOr.view_get_oracle(qm2.ov, TREP.CpOf(inp), lid)
           <==> LT.TreeRes(LFU.ComputeTr(rer, [LS.Areg(r1)], inp, LG.Empty, L.LkDir(lk)),
                           LG.Empty, inp, L.LkDir(lk)).Some?
      {
        assert lid in qm.looks && qm.looks[lid] == (lk, r1);
      }
    }
  }

  // ==========================================================================
  // (L5 F7d) WHOLE-STRING oracle-column correctness for the backward keystone.
  // The lift carries only the from-cp `OracleOkSuffix`; a lookbehind body reads
  // positions <= cp, so `FG.*`/F5/F6 need `OE.OracleColsOk(rer, qm, str)` — a
  // STATIC fact, threaded as a `requires` from the top down to the gate step.
  // ==========================================================================

  /** From the opaque all-cps suffix bundle (column `cp` is in its own suffix). */
  lemma SufAllToColsOk(rer: LW.RegExpRecord, qm: AR.QMap, str: string)
    requires M.OracleSufAllO(rer, qm, str)
    ensures OE.OracleColsOk(rer, qm, str)
  {
    reveal M.OracleSufAllO();
    forall k: int | 0 <= k <= |str| ensures LL.OracleOkAt(rer, qm, T.InputAt(str, k)) {
      var kn: nat := k;
      assert LL.OracleOkSuffix(rer, qm, PIV.InpOfCp(str, kn));
      assert PIV.InpOfCp(str, kn) == T.InputAt(str, kn);
    }
  }

  /** From the unfolded all-cps forall (the form the descent lemmas carry). */
  lemma SufForallToColsOk(rer: LW.RegExpRecord, qm: AR.QMap, str: string)
    requires forall cp: nat :: cp <= |str| ==> LL.OracleOkSuffix(rer, qm, PIV.InpOfCp(str, cp))
    ensures OE.OracleColsOk(rer, qm, str)
  {
    forall k: int | 0 <= k <= |str| ensures LL.OracleOkAt(rer, qm, T.InputAt(str, k)) {
      var kn: nat := k;
      assert LL.OracleOkSuffix(rer, qm, PIV.InpOfCp(str, kn));
      assert PIV.InpOfCp(str, kn) == T.InputAt(str, kn);
    }
  }

  /** Restriction to a sub-table (the body-restricted `qmB` of the descent). */
  lemma OracleColsOkRestrict(rer: LW.RegExpRecord, qm: AR.QMap, qm2: AR.QMap, str: string)
    requires OE.OracleColsOk(rer, qm, str)
    requires qm2.ov == qm.ov
    requires forall l: int :: l in qm2.looks ==> l in qm.looks && qm2.looks[l] == qm.looks[l]
    ensures OE.OracleColsOk(rer, qm2, str)
  {
    forall k: int | 0 <= k <= |str| ensures LL.OracleOkAt(rer, qm2, T.InputAt(str, k)) {
      FST.OracleOkAtSubmap(rer, qm, qm2, T.InputAt(str, k));
    }
  }

  /** `PlusFragmentRE` is look-free by construction, so it sits inside the
      compile fragment (the two predicates differ only at the lookaround case,
      which `PlusFragmentRE` forbids). */
  lemma PlusFragmentIsLBF(r: R.regex)
    requires NR.PlusFragmentRE(r)
    ensures NR.LookBehindFragmentRE(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => PlusFragmentIsLBF(r1); PlusFragmentIsLBF(r2);
    case Re_con(r1, r2) => PlusFragmentIsLBF(r1); PlusFragmentIsLBF(r2);
    case Re_quant(_, _, _, r1) => PlusFragmentIsLBF(r1);
    case Re_capture(_, r1) => PlusFragmentIsLBF(r1);
    case _ =>
  }

  /** A look-free regex owns no lookaround ids. */
  lemma LookFreeNoLids(r: R.regex)
    requires NR.LookFreeRE(r)
    ensures LTB.LookIds(r) == {}
    decreases r
  {
    match r
    case Re_alt(r1, r2) => LookFreeNoLids(r1); LookFreeNoLids(r2);
    case Re_con(r1, r2) => LookFreeNoLids(r1); LookFreeNoLids(r2);
    case Re_quant(_, _, _, r1) => LookFreeNoLids(r1);
    case Re_capture(_, r1) => LookFreeNoLids(r1);
    case _ =>
  }

  /** THE `GateStaticsOk` establishment sweep: every lid of `re` gets its
      per-lid bundle. All the qm/fragment facts descend definitionally to the
      lookaround node; the body's compile statics come from
      `CompileToBytecodeRepLookBehind` + `CompileStutterTameRE` via
      `PlusFragmentIsLBF`. `re0` carries the whole-regex confinement target. */
  lemma GateStaticsSweepRE(qm: AR.QMap, re0: R.regex, re: R.regex, crv: CP.FCompiled,
                           ncap: int, nlook: int, nquant: int)
    requires T.TransWf(re) && AR.QmapOk(re, qm) && AR.LmapOk(re, qm)
    requires NR.NoNulledPlusRE(re)   // §2.5b interim
    requires NR.LookBehindFragmentRE(re) && PIV.CapUnique(re) && PIV.QuantUnique(re)
    requires LTB.LookTablesOk(re, crv)
    requires PSM.SizesOkRE(re, ncap, nlook, nquant)
    requires PIV.CapIdsInLooks(re) <= PIV.CapIdsInLooks(re0)
    ensures forall l: int :: l >= 0 && (l as nat) in LTB.LookIds(re) ==>
                               GateStaticAt(qm, re0, crv, l, ncap, nlook, nquant)
    decreases re
  {
    match re
    case Re_alt(r1, r2) =>
      GateStaticsSweepRE(qm, re0, r1, crv, ncap, nlook, nquant);
      GateStaticsSweepRE(qm, re0, r2, crv, ncap, nlook, nquant);
    case Re_con(r1, r2) =>
      GateStaticsSweepRE(qm, re0, r1, crv, ncap, nlook, nquant);
      GateStaticsSweepRE(qm, re0, r2, crv, ncap, nlook, nquant);
    case Re_quant(_, _, _, r1) =>
      GateStaticsSweepRE(qm, re0, r1, crv, ncap, nlook, nquant);
    case Re_capture(_, r1) =>
      GateStaticsSweepRE(qm, re0, r1, crv, ncap, nlook, nquant);
    case Re_lookaround(lid, la, body) =>
      LookFreeNoLids(body);
      if lid >= 0 {
        // the node's own bundle
        assert LTB.LookEntryOk(crv, lid, la, body);
        assert T.TransWf(body) && NR.LookFreeRE(body) && NR.PlusFragmentRE(body);
        assert NR.NoNulledPlusRE(body);   // §2.5b: descends definitionally
        assert lid in qm.looks && qm.looks[lid] == (T.TrLookaround(la), T.Translate(body));
        // confinement: the body's groups are inside-look groups of re0
        M.TranslateDefGroupsEqCapIds(body);
        assert PIV.CapIdsInLooks(re) == PIV.CapIds(body);
        assert (set g: LG.GroupId | g in L.DefGroups(T.Translate(body))) <= PIV.CapIdsInLooks(re0);
        // compile statics for the body's own bytecode
        PlusFragmentIsLBF(body);
        NR.CompileToBytecodeRepLookBehind(body);
        PIV.CompileStutterTameRE(body);
        var bodycode := CP.compile_to_bytecode(body);
        var next := CP.compile(body, 0, CP.Progress).1;
        assert next >= 0 && |bodycode| == next + 1 && |bodycode| >= 1;
        assert NR.NfaRepRE(body, bodycode, 0, next as nat)
               && NR.GetPcRE(bodycode, next as nat) == Some(RB.Accept);
        assert (next as nat) == |bodycode| - 1;
        assert PSM.StaticOkRE(qm, body, bodycode, |bodycode| - 1);
        assert PSM.SizesOkRE(body, ncap, nlook, nquant);
        assert (la.NegLookbehind? || la.NegLookahead?) ==> NR.CaptureFreeRE(body);
        assert GateStaticAt(qm, re0, crv, lid, ncap, nlook, nquant);
      }
    case _ =>
  }

  /** (L4 NESTED) `PIV.CompileStutterTameRE` off the depth-1 fragment: the Jmp-
      target tameness of a compiled block depends only on `NfaRepRE(re, code, 0,
      endl)` (which `PIV.CompileJumpsRE` consumes — it takes NO fragment
      hypothesis), so `NR.CompileToBytecodeRepNested` supplies it for any nested
      fragment. Depth-general. */
  lemma CompileStutterTameRENested(re: R.regex)
    requires NR.NestedFragmentRE(re)
    ensures PIV.StutterTameRE(CP.compile_to_bytecode(re))
  {
    var code := CP.compile_to_bytecode(re);
    var endl := CP.compile(re, 0, CP.Progress).1;
    NR.CompileToBytecodeRepNested(re);   // NfaRepRE(re, code, 0, endl), GetPc(endl)==Accept, |code|==endl+1
    forall pc: nat | pc < |code|
      ensures match NR.GetPcRE(code, pc)
              case Some(Jmp(next)) =>
                pc < next
                || (next >= 0 && NR.GetPcRE(code, next as nat).Some? && NR.GetPcRE(code, next as nat).value.Fork?)
              case _ => true
    {
      match NR.GetPcRE(code, pc)
      case Some(Jmp(n)) =>
        assert pc < endl as nat;   // code[endl] == Accept ≠ Jmp, and pc < |code| == endl+1
        PIV.CompileJumpsRE(re, code, 0, endl as nat, pc, n);
      case _ =>
    }
  }

  /** A look-free regex has no lookaround nodes, so it vacuously has no positive
      lookbehinds (`M.NoPosLookbehindRE` only constrains lookaround leaves). */
  lemma LookFreeNoPosLookbehindRE(re: R.regex)
    requires NR.LookFreeRE(re)
    ensures M.NoPosLookbehindRE(re)
    decreases re
  {
    match re
    case Re_alt(r1, r2) => LookFreeNoPosLookbehindRE(r1); LookFreeNoPosLookbehindRE(r2);
    case Re_con(r1, r2) => LookFreeNoPosLookbehindRE(r1); LookFreeNoPosLookbehindRE(r2);
    case Re_quant(_, _, _, r1) => LookFreeNoPosLookbehindRE(r1);
    case Re_capture(_, r1) => LookFreeNoPosLookbehindRE(r1);
    case _ =>
  }

  /** Dispatcher helper (VC diet): the SetReg gm effect off machine A's head —
      the `PreserveOpenCase`/`PreserveCloseCase` preamble + `OpenStepThreadRE`/
      `CloseStepThreadRE`, packaged so the dispatcher's own VC stays small. */
  lemma DispatchSetRegEffect(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
                             ngroups: nat, str: string, ptsA: PT.PikeTreeState, s: AI.VmState,
                             s1: AI.VmState, reg: int, th': AI.Thread,
                             ncap: int, nlook: int, nquant: int)
    requires !rer.multiline
    requires PSM.StaticOkRE(qm, re, code, endl) && PSM.SizesOkRE(re, ncap, nlook, nquant)
    requires ptsA.PTS?
    requires PSM.PikeInvFullRE(rer, qm, re, code, endl, ngroups, str, ptsA, s, ncap, nlook, nquant)
    requires |s.active| > 0 && s.active[0].pc >= 0
    requires NR.GetPcRE(code, s.active[0].pc as nat) == Some(RB.SetRegisterToCP(reg))
    requires s1 == s.(clock := s.clock + 1,
                   processed := AI.bpc_add(s.processed, s.active[0].pc, s.active[0].exit_allowed))
    requires th' == s.active[0].(capture_regs := AReg.set_reg(s.active[0].capture_regs, reg, Some(s1.cp), s1.clock),
                    pc := s.active[0].pc + 1)
    ensures reg >= 0 && 0 <= s1.cp
    ensures PIV.GmOfLive(re, th'.capture_regs, th'.look_regs, th'.quant_regs)
         == (if reg % 2 == 0
             then LG.GMOpen(s1.cp as nat, (reg / 2) as nat,
                            PIV.GmOfLive(re, s.active[0].capture_regs, s.active[0].look_regs,
                                         s.active[0].quant_regs))
             else LG.GMClose(s1.cp as nat, (reg / 2) as nat,
                             PIV.GmOfLive(re, s.active[0].capture_regs, s.active[0].look_regs,
                                          s.active[0].quant_regs)))
  {
    var th := s.active[0];
    var pc: nat := th.pc as nat;
    var PTS(inpA, taA, bestA, tbA, seenA) := ptsA;
    assert PIV.ActiveRepRE(rer, qm, re, code, inpA, taA, s.active);
    assert |taA| > 0;
    var tA := taA[0].0;
    var gmA := taA[0].1;
    assert TT.TreeThreadRE(rer, qm, code, inpA, tA, pc, th.exit_allowed);
    assert PIV.ThreadTracksGm(re, th, gmA);
    assert th in s.active;
    assert PSM.ThreadNestRE(re, code, endl, th.pc, th);
    assert CM.ThreadClocksLE(th, s.clock) && CM.ThreadRegsWf(th, ncap, nlook, nquant)
           && CM.RegsValsLE(th.capture_regs, s.cp);
    assert PIV.LooksCapUnset(re, th.capture_regs.a_clk);
    assert 0 <= s1.cp;
    if reg % 2 == 0 {
      PSM.OpenStepThreadRE(rer, qm, re, code, endl, inpA, tA, gmA, th, pc, reg, s.cp, s.clock);
      assert tA.GroupActionT? && tA.g.Open? && reg == CP.start_reg(tA.g.g as int);
      assert reg == 2 * (tA.g.g as int) && (reg / 2) as nat == tA.g.g;
    } else {
      PSM.CloseStepThreadRE(rer, qm, re, code, endl, inpA, tA, gmA, th, pc, reg, s.cp, s.clock);
      assert tA.GroupActionT? && tA.g.Close? && reg == CP.end_reg(tA.g.g as int);
      assert reg == 2 * (tA.g.g as int) + 1 && (reg / 2) as nat == tA.g.g;
    }
  }

  /** Dispatcher helper (VC diet): the SetQuant `GMReset` gm effect off machine
      A's head — the `PreserveResetCase` preamble + `ResetStepThreadRE`. `!bq`
      is the caller's obligation (from the B-side canonical inversion). */
  lemma DispatchResetEffect(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
                            ngroups: nat, str: string, ptsA: PT.PikeTreeState, s: AI.VmState,
                            s1: AI.VmState, q: int, th': AI.Thread,
                            ncap: int, nlook: int, nquant: int)
    requires !rer.multiline
    requires PSM.StaticOkRE(qm, re, code, endl) && PSM.SizesOkRE(re, ncap, nlook, nquant)
    requires ptsA.PTS?
    requires PSM.PikeInvFullRE(rer, qm, re, code, endl, ngroups, str, ptsA, s, ncap, nlook, nquant)
    requires |s.active| > 0 && s.active[0].pc >= 0
    requires NR.GetPcRE(code, s.active[0].pc as nat) == Some(RB.SetQuantToClock(q, false))
    requires s1 == s.(clock := s.clock + 1,
                   processed := AI.bpc_add(s.processed, s.active[0].pc, s.active[0].exit_allowed))
    requires th' == s.active[0].(quant_regs := AReg.set_reg(s.active[0].quant_regs, q, None, s1.clock),
                    pc := s.active[0].pc + 1)
    ensures q in qm.quants
    ensures PIV.GmOfLive(re, th'.capture_regs, th'.look_regs, th'.quant_regs)
         == LG.GMReset(qm.quants[q],
                       PIV.GmOfLive(re, s.active[0].capture_regs, s.active[0].look_regs,
                                    s.active[0].quant_regs))
  {
    var th := s.active[0];
    var pc: nat := th.pc as nat;
    var PTS(inpA, taA, bestA, tbA, seenA) := ptsA;
    assert PIV.ActiveRepRE(rer, qm, re, code, inpA, taA, s.active);
    assert |taA| > 0;
    var tA := taA[0].0;
    var gmA := taA[0].1;
    assert TT.TreeThreadRE(rer, qm, code, inpA, tA, pc, th.exit_allowed);
    assert PIV.ThreadTracksGm(re, th, gmA);
    assert th in s.active;
    assert PSM.ThreadNestRE(re, code, endl, th.pc, th);
    assert CM.ThreadClocksLE(th, s.clock) && CM.ThreadRegsWf(th, ncap, nlook, nquant);
    assert PIV.LooksCapUnset(re, th.capture_regs.a_clk);
    PSM.ResetStepThreadRE(rer, qm, re, code, endl, inpA, tA, gmA, th, pc, q, s.clock);
    assert tA.GroupActionT? && tA.g.Reset? && qm.quants[q] == tA.g.gl;
  }

  /** (L4 NESTED) clone of `DispatchSetRegEffect` under `StaticOkNestedRE`: the
      Open/Close gm-effect callees are swapped to their nested-fragment
      counterparts (`OpenStepThreadRENested`/`CloseStepThreadRENested`, which
      take `NestedFragmentRE(re)` in place of `LookBehindFragmentRE(re)`). The
      body is otherwise verbatim — every other fact rides `PikeInvFullRE`. */
  lemma DispatchSetRegEffectNested(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
                                   ngroups: nat, str: string, ptsA: PT.PikeTreeState, s: AI.VmState,
                                   s1: AI.VmState, reg: int, th': AI.Thread,
                                   ncap: int, nlook: int, nquant: int)
    requires !rer.multiline
    requires PSM.StaticOkNestedRE(qm, re, code, endl) && PSM.SizesOkRE(re, ncap, nlook, nquant)
    requires ptsA.PTS?
    requires PSM.PikeInvFullRE(rer, qm, re, code, endl, ngroups, str, ptsA, s, ncap, nlook, nquant)
    requires |s.active| > 0 && s.active[0].pc >= 0
    requires NR.GetPcRE(code, s.active[0].pc as nat) == Some(RB.SetRegisterToCP(reg))
    requires s1 == s.(clock := s.clock + 1,
                   processed := AI.bpc_add(s.processed, s.active[0].pc, s.active[0].exit_allowed))
    requires th' == s.active[0].(capture_regs := AReg.set_reg(s.active[0].capture_regs, reg, Some(s1.cp), s1.clock),
                    pc := s.active[0].pc + 1)
    ensures reg >= 0 && 0 <= s1.cp
    ensures PIV.GmOfLive(re, th'.capture_regs, th'.look_regs, th'.quant_regs)
         == (if reg % 2 == 0
             then LG.GMOpen(s1.cp as nat, (reg / 2) as nat,
                            PIV.GmOfLive(re, s.active[0].capture_regs, s.active[0].look_regs,
                                         s.active[0].quant_regs))
             else LG.GMClose(s1.cp as nat, (reg / 2) as nat,
                             PIV.GmOfLive(re, s.active[0].capture_regs, s.active[0].look_regs,
                                          s.active[0].quant_regs)))
  {
    var th := s.active[0];
    var pc: nat := th.pc as nat;
    var PTS(inpA, taA, bestA, tbA, seenA) := ptsA;
    assert PIV.ActiveRepRE(rer, qm, re, code, inpA, taA, s.active);
    assert |taA| > 0;
    var tA := taA[0].0;
    var gmA := taA[0].1;
    assert TT.TreeThreadRE(rer, qm, code, inpA, tA, pc, th.exit_allowed);
    assert PIV.ThreadTracksGm(re, th, gmA);
    assert th in s.active;
    assert PSM.ThreadNestRE(re, code, endl, th.pc, th);
    assert CM.ThreadClocksLE(th, s.clock) && CM.ThreadRegsWf(th, ncap, nlook, nquant)
           && CM.RegsValsLE(th.capture_regs, s.cp);
    assert PIV.LooksCapUnset(re, th.capture_regs.a_clk);
    assert 0 <= s1.cp;
    if reg % 2 == 0 {
      PSM.OpenStepThreadRENested(rer, qm, re, code, endl, inpA, tA, gmA, th, pc, reg, s.cp, s.clock);
      assert tA.GroupActionT? && tA.g.Open? && reg == CP.start_reg(tA.g.g as int);
      assert reg == 2 * (tA.g.g as int) && (reg / 2) as nat == tA.g.g;
    } else {
      PSM.CloseStepThreadRENested(rer, qm, re, code, endl, inpA, tA, gmA, th, pc, reg, s.cp, s.clock);
      assert tA.GroupActionT? && tA.g.Close? && reg == CP.end_reg(tA.g.g as int);
      assert reg == 2 * (tA.g.g as int) + 1 && (reg / 2) as nat == tA.g.g;
    }
  }

  /** (L4 NESTED) clone of `DispatchResetEffect` under `StaticOkNestedRE`: the
      `GMReset` gm-effect callee is `ResetStepThreadRENested`. Body verbatim. */
  lemma DispatchResetEffectNested(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
                                  ngroups: nat, str: string, ptsA: PT.PikeTreeState, s: AI.VmState,
                                  s1: AI.VmState, q: int, th': AI.Thread,
                                  ncap: int, nlook: int, nquant: int)
    requires !rer.multiline
    requires PSM.StaticOkNestedRE(qm, re, code, endl) && PSM.SizesOkRE(re, ncap, nlook, nquant)
    requires ptsA.PTS?
    requires PSM.PikeInvFullRE(rer, qm, re, code, endl, ngroups, str, ptsA, s, ncap, nlook, nquant)
    requires |s.active| > 0 && s.active[0].pc >= 0
    requires NR.GetPcRE(code, s.active[0].pc as nat) == Some(RB.SetQuantToClock(q, false))
    requires s1 == s.(clock := s.clock + 1,
                   processed := AI.bpc_add(s.processed, s.active[0].pc, s.active[0].exit_allowed))
    requires th' == s.active[0].(quant_regs := AReg.set_reg(s.active[0].quant_regs, q, None, s1.clock),
                    pc := s.active[0].pc + 1)
    ensures q in qm.quants
    ensures PIV.GmOfLive(re, th'.capture_regs, th'.look_regs, th'.quant_regs)
         == LG.GMReset(qm.quants[q],
                       PIV.GmOfLive(re, s.active[0].capture_regs, s.active[0].look_regs,
                                    s.active[0].quant_regs))
  {
    var th := s.active[0];
    var pc: nat := th.pc as nat;
    var PTS(inpA, taA, bestA, tbA, seenA) := ptsA;
    assert PIV.ActiveRepRE(rer, qm, re, code, inpA, taA, s.active);
    assert |taA| > 0;
    var tA := taA[0].0;
    var gmA := taA[0].1;
    assert TT.TreeThreadRE(rer, qm, code, inpA, tA, pc, th.exit_allowed);
    assert PIV.ThreadTracksGm(re, th, gmA);
    assert th in s.active;
    assert PSM.ThreadNestRE(re, code, endl, th.pc, th);
    assert CM.ThreadClocksLE(th, s.clock) && CM.ThreadRegsWf(th, ncap, nlook, nquant);
    assert PIV.LooksCapUnset(re, th.capture_regs.a_clk);
    PSM.ResetStepThreadRENested(rer, qm, re, code, endl, inpA, tA, gmA, th, pc, q, s.clock);
    assert tA.GroupActionT? && tA.g.Reset? && qm.quants[q] == tA.g.gl;
  }

  // (5)/(6)/(7): the pre-composite LiftConsume / LiftFindMatch / LiftEndpoint
  // scaffolds are SUPERSEDED by the composite spine (LiftInitC -> LiftFindMatchC
  // -> L3aCompositeClose, all PROVEN) and were deleted 2026-08-08.

  // ==========================================================================
  // THE REST OF THE LADDER — the sub-DAG below LiftAdvanceEpsilon, plus the
  // two bridges that reach MainTheorem. With these filled, L3 is:
  //   helpers → LiftAdvanceEpsilon → LiftConsume → LiftFindMatch →
  //   LiftEndpoint → L3aValueBridge → else-branch rewrite → delete
  //   LkBodyGroupsEmpty / FilterUnmoved / L1 LookRowsFromTables → package
  //   verify → repack.
  // Confidence tiers: [SOLID] statement believed exact; [SEAM] shape right,
  // details expected to shift during fill — adjust freely, the consumer is
  // LiftAdvanceEpsilon's matching case.
  // ==========================================================================

  // ---- (H) per-instruction walk inversions: the B-side mirrors of
  //      TT.TtAtJmp / TtAtBeginLoop, one per LiftAdvanceEpsilon case. Each
  //      says what the B head MUST look like at that instruction and where
  //      the walk stands after. FILL from the corresponding
  //      ActionsTreeRepFRE case (it performs exactly this inversion inline).
  //
  // FILL RECIPE (reverse-engineered 2026-08-03 — read before starting):
  //  * TtLk bundles four conjuncts over an EXISTENTIAL (acts, b). Extract them;
  //    the tree-side conclusion (tb.Read? / tb == LT.Match / tb.LK? / ...) is a
  //    ONE-STEP unfold of the `least predicate` EL.BoolTreeLk once acts[0] is
  //    known (the `case _ => false` arms make the shape forced). There are NO
  //    standalone BoolTreeLk-shape inverters yet — unfold inline.
  //  * The walk MOVE (TtLk at nextpc) reuses the SAME (acts, b): only
  //    AR.ActionsRepL must be transferred; WO.WalkOk moves via the matching
  //    destructor (WalkOkJmp/WalkOkEpsilon/WalkOkCharacter/WalkOkAclose/
  //    WalkOkAnchor/WalkOkLookaround/WalkOkSeq/WalkOkGroup/WalkOkAlt/... ,
  //    WalkOk.dfy:162+), PikeLkActions via PikeLkActionsTail, EaOf(b) is inert.
  //  * The ActionsRepL transfer is the WORK, and it is NOT a plain `least
  //    lemma`: cons_bc JUMPS a whole sub-regex (acts[1..] at the sub-regex's
  //    end) whereas BoolTreeLk EXPANDS it ([Areg(r1),Areg(r2)]+cont, etc.), so
  //    reconciling them re-expands `acts` and GROWS it. Mirror
  //    ActionsTreeRepFRE EXACTLY: take `ActionsRepFuelL` (fueled ActionsRepL,
  //    via AR.ActionsRepLToFuel) and `decreases MsizeA(acts), n` — plain
  //    least-recursion is unsound here. Transparent heads (Epsilon, and
  //    Sequences/spent-quants reducing to it) peel in place (pcmid == pc, use
  //    AR.NfaRepIncrL for the span bound); every non-transparent head pins a
  //    GetPcRE instruction that contradicts the inversion's target (⇒ vacuous
  //    `case _`). The stutter set (Jmp/BeginLoop/Accept) bottoms at jump_bc or
  //    empty_bc; the consuming/gate cases pin their instruction directly.
  //  * TtLkAtCheckOracle additionally needs LL.OracleOkAt(rer,qm,inp) to tie
  //    the bit (LOr.view_get_oracle) to LkGateOk's verdict — carry it in TtLk
  //    or thread it as a requires (it is already a LiftInv conjunct via
  //    LL.OracleOkSuffix). This is the ONE inversion that yields tb.LK?/tb.LKFail?.

  /** `NfaRepMinL`'s head: `k==0` is transparent (`em==pc`), `k>0` pins a
      `SetQuantToClock` at `pc`. */
  lemma NfaRepMinLHeadPin(rer: LW.RegExpRecord, qm: AR.QMap, k: nat, r1: L.Regex, code: RB.code, pc: nat, em: nat)
    requires AR.NfaRepMinL(rer, qm, k, r1, code, pc, em)
    ensures k == 0 ==> em == pc
    ensures k > 0 ==> NR.GetPcRE(code, pc).Some? && NR.GetPcRE(code, pc).value.SetQuantToClock?
  {
    if k > 0 {
      var e1: nat :|
        (exists qid: int :: NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(qid, false))
                            && qid in qm.quants && qm.quants[qid] == L.DefGroups(r1))
        && AR.NfaRepL(rer, qm, r1, code, pc + 1, e1)
        && AR.NfaRepMinL(rer, qm, k - 1, r1, code, e1, em);
    }
  }

  /** `NfaRepOptL`'s head: `k==0` is transparent (`em==pc`), `k>0` pins a `Fork`
      at `pc`. */
  lemma NfaRepOptLHeadPin(rer: LW.RegExpRecord, qm: AR.QMap, k: nat, greedy: bool, r1: L.Regex, code: RB.code, pc: nat, em: nat)
    requires AR.NfaRepOptL(rer, qm, k, greedy, r1, code, pc, em)
    ensures k == 0 ==> em == pc
    ensures k > 0 ==> NR.GetPcRE(code, pc).Some? && NR.GetPcRE(code, pc).value.Fork?
  {
    if k > 0 {
      var e1: nat :|
        NR.GetPcRE(code, pc) == Some(if greedy then RB.Fork(pc + 1, em) else RB.Fork(em, pc + 1))
        && (exists qid: int :: NR.GetPcRE(code, pc + 1) == Some(RB.SetQuantToClock(qid, false))
                               && qid in qm.quants && qm.quants[qid] == L.DefGroups(r1))
        && NR.GetPcRE(code, pc + 2) == Some(RB.BeginLoop)
        && AR.NfaRepL(rer, qm, r1, code, pc + 3, e1)
        && NR.GetPcRE(code, e1) == Some(RB.EndLoop)
        && AR.NfaRepOptL(rer, qm, k - 1, greedy, r1, code, e1 + 1, em);
    }
  }

  /** A regex whose `NfaRepL` span STARTS at a `Jmp` is transparent: the span is
      empty (`pcmid == pc`) and it re-represents empty at any position `x`. Every
      non-transparent shape pins a conflicting instruction at `pc`. */
  lemma NfaRepLAtJmpTransparent(rer: LW.RegExpRecord, qm: AR.QMap, r: L.Regex, code: RB.code,
                                pc: nat, pcmid: nat, x: int)
    requires AR.NfaRepL(rer, qm, r, code, pc, pcmid)
    requires NR.GetPcRE(code, pc) == Some(RB.Jmp(x))
    ensures pcmid == pc
    ensures x >= 0 ==> AR.NfaRepL(rer, qm, r, code, x as nat, x as nat)
    decreases r
  {
    match r
    case Epsilon =>
    case Character(cd) =>
      var ce :| NR.GetPcRE(code, pc) == Some(RB.Consume(ce)) && AR.ExpectationMatches(rer, ce, cd);
    case Disjunction(r1, r2) =>
      var e1: nat :| NR.GetPcRE(code, pc) == Some(RB.Fork(pc + 1, e1 + 1))
                     && AR.NfaRepL(rer, qm, r1, code, pc + 1, e1)
                     && NR.GetPcRE(code, e1) == Some(RB.Jmp(pcmid))
                     && AR.NfaRepL(rer, qm, r2, code, e1 + 1, pcmid);
    case Sequence(r1, r2) =>
      var e1: nat :| AR.NfaRepL(rer, qm, r1, code, pc, e1) && AR.NfaRepL(rer, qm, r2, code, e1, pcmid);
      NfaRepLAtJmpTransparent(rer, qm, r1, code, pc, e1, x);       // e1 == pc
      NfaRepLAtJmpTransparent(rer, qm, r2, code, pc, pcmid, x);    // pcmid == pc
      if x >= 0 {
        assert AR.NfaRepL(rer, qm, r1, code, x as nat, x as nat);
        assert AR.NfaRepL(rer, qm, r2, code, x as nat, x as nat);
      }
    case Quantified(greedy, min, delta, r1) =>
      if min == 0 && delta == LN.Inf {
        // the star: pins Fork at pc (fast path or loop view) — contradiction
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
      } else {
        match delta
        case Inf =>
          if NUL.NonNullableL(r1) {
            var em: nat, e1: nat :|
              AR.NfaRepMinL(rer, qm, min - 1, r1, code, pc, em)
              && (exists qid: int :: NR.GetPcRE(code, em) == Some(RB.SetQuantToClock(qid, false))
                                     && qid in qm.quants && qm.quants[qid] == L.DefGroups(r1))
              && AR.NfaRepL(rer, qm, r1, code, em + 1, e1)
              && NR.GetPcRE(code, e1) == Some(if greedy then RB.Fork(em, e1 + 1) else RB.Fork(e1 + 1, em))
              && pcmid == e1 + 1;
            NfaRepMinLHeadPin(rer, qm, min - 1, r1, code, pc, em);   // min-1==0 ⇒ em==pc; else Fork/SQC at pc
          } else if !greedy {
            // §2.5a GENERIC: min >= 1 copies, so pc carries a clock-mark ≠ Jmp
            var em, e1 := AR.NfaRepLGenInv(rer, qm, greedy, min, r1, code, pc, pcmid);
            NfaRepMinLHeadPin(rer, qm, min, r1, code, pc, em);
          } else {
            // §2.5b CIN-GREEDY: clock-mark (min > 1) or the head Fork (min == 1),
            // either ≠ Jmp
            var em, e1 := AR.NfaRepLCinInv(rer, qm, greedy, min, r1, code, pc, pcmid);
            NfaRepMinLHeadPin(rer, qm, min - 1, r1, code, pc, em);
            if min == 1 {
              assert em == pc;
              assert NR.GetPcRE(code, pc) == Some(RB.Fork(em + 1, e1 + 2));
            }
          }
        // either way GetPcRE(pc) is SetQuantToClock ≠ Jmp
        case NN(kx) =>
          var em: nat :| AR.NfaRepMinL(rer, qm, min, r1, code, pc, em)
                         && AR.NfaRepOptL(rer, qm, kx, greedy, r1, code, em, pcmid);
          NfaRepMinLHeadPin(rer, qm, min, r1, code, pc, em);
          if min == 0 {
            assert em == pc;
            NfaRepOptLHeadPin(rer, qm, kx, greedy, r1, code, em, pcmid);
            // kx==0 ⇒ pcmid==em==pc (and NfaRepL(...,x,x) via transparent chains);
            // kx>0 ⇒ Fork at pc, contradiction
            if kx == 0 && x >= 0 {
              assert AR.NfaRepMinL(rer, qm, 0, r1, code, x as nat, x as nat);
              assert AR.NfaRepOptL(rer, qm, 0, greedy, r1, code, x as nat, x as nat);
            }
          }
        // min>0 ⇒ SetQuantToClock at pc, contradiction
      }
    case Group(gid, r1) =>
      var e1: nat :| NR.GetPcRE(code, pc) == Some(RB.SetRegisterToCP(CP.start_reg(gid as int)))
                     && AR.NfaRepL(rer, qm, r1, code, pc + 1, e1)
                     && NR.GetPcRE(code, e1) == Some(RB.SetRegisterToCP(CP.end_reg(gid as int)))
                     && pcmid == e1 + 1;
    case LookaroundR(lk, r1) =>
      var lid: int :| NR.GetPcRE(code, pc) == Some(if AR.PositiveL(lk) then RB.CheckOracle(lid)
                                                                       else RB.NegCheckOracle(lid))
                      && lid in qm.looks && qm.looks[lid] == (lk, r1);
    case AnchorR(la) =>
      var a: R.anchor :| NR.GetPcRE(code, pc) == Some(RB.AnchorAssertion(a)) && T.TrAnchor(a) == la;
    case Backreference(_) =>
  }

  /** [SOLID] BeginLoop: a REAL stutter now. `TtLk`'s new first disjunct sees
      through a `BeginLoop` to `pc+1` (mirroring `TreeRepRE.tr_begin`). The
      `ActionsRepL` (second) disjunct is impossible at a `BeginLoop` pc
      (`TT.ActionsRepNotAtBeginLoop`), so `TtLk(pc)` must hold via the stutter,
      which IS `TtLk(pc+1, false)`. This unblocks `LiftAdvanceEpsilon`: the VM
      steps a BeginLoop thread to `pc+1` with `exit_allowed:=false`, and the
      pairing follows it. */
  lemma TtLkAtBeginLoop(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                        tb: LT.Tree, pc: nat, ea: bool)
    requires TtLk(rer, qm, code, inp, tb, pc, ea)
    requires NR.GetPcRE(code, pc) == Some(RB.BeginLoop)
    ensures TtLk(rer, qm, code, inp, tb, pc + 1, false)
  {
    // The ActionsRepL disjunct is unsatisfiable at a BeginLoop pc.
    forall acts: LS.Actions, b: BS.LoopBool
      ensures !(AR.ActionsRepL(rer, qm, acts, code, pc)
                && EL.PikeLkActions(acts) && ATR.EaOf(b) == ea
                && EL.BoolTreeLk(rer, acts, inp, b, tb))
    {
      if AR.ActionsRepL(rer, qm, acts, code, pc) {
        TT.ActionsRepNotAtBeginLoop(rer, qm, acts, code, pc);   // ⇒ false
      }
    }
    // So TtLk(pc) holds via the BeginLoop stutter, whose payload is TtLk(pc+1, false).
  }

  /** Discharges the CheckOracle core's OUTSIDE-`S` frame: crossing a positive gate
      (gm → gm2 = `LkResult` merge, and `a_cp[l]` newly set in `t'`) preserves the
      outside-`S` value tie. Three proven pieces chain: `LkResultAgreeOutside`
      (merge touches only `DefGroups(r1) ⊆ S`), `GmtTieOutside(t)` (the incoming
      tie), and `PIV.GmOfLiveLookIndep` (setting look register `l` cannot change
      any group outside `CapIdsInLooks(re) == S`). */
  lemma GmtTieOutsideAfterGate(rer: LW.RegExpRecord, re: R.regex, str: string, lk: L.Lookaround,
                               r1: L.Regex, tlk: LT.Tree, gm: LG.GroupMap, t: AI.Thread,
                               l: int, cp: nat, clk: int, S: set<LG.GroupId>)
    requires cp <= |str|
    requires NR.LookBehindFragmentRE(re) && T.TransWf(re)
    requires S == LL.LkBodyGroups(T.Translate(re))
    requires (set g | g in L.DefGroups(r1)) <= S
    requires GmtTieOutside(re, t, gm, S)
    requires L.Positivity(lk) && EL.NoLkBrL(r1)
    requires tlk == LFU.ComputeTr(rer, [LS.Areg(r1)], PIV.InpOfCp(str, cp), LG.Empty, L.LkDir(lk))
    requires LS.LkResult(lk, tlk, gm, PIV.InpOfCp(str, cp)).Some?
    ensures var t' := t.(pc := t.pc + 1, look_regs := AReg.set_reg(t.look_regs, l, Some(cp as int), clk));
            GmtTieOutside(re, t', LS.LkResult(lk, tlk, gm, PIV.InpOfCp(str, cp)).value, S)
  {
    var inp := PIV.InpOfCp(str, cp);
    var gm2 := LS.LkResult(lk, tlk, gm, inp).value;
    var t' := t.(pc := t.pc + 1, look_regs := AReg.set_reg(t.look_regs, l, Some(cp as int), clk));
    LkResultAgreeOutside(rer, lk, r1, inp, tlk, gm);      // GmAgreeOutside(gm2, gm, DefGroups(r1))
    M.LkBodyGroupsEqCapIdsInLooks(re);                    // S == CapIdsInLooks(re)
    PIV.GmOfLiveLookIndep(re, t.capture_regs, t.look_regs, t'.look_regs, t.quant_regs);
    forall g: LG.GroupId | g !in S
      ensures (g in gm2 <==> g in PIV.GmOfLive(re, t'.capture_regs, t'.look_regs, t'.quant_regs))
              && (g in gm2 ==> gm2[g] == PIV.GmOfLive(re, t'.capture_regs, t'.look_regs, t'.quant_regs)[g])
    {
      assert g !in (set g': LG.GroupId | g' in L.DefGroups(r1));   // DefGroups(r1) ⊆ S
      assert g !in PIV.CapIdsInLooks(re);                          // S == CapIdsInLooks(re)
      // gm2[g] ~ gm[g] (LkResultAgreeOutside) ~ gml[g] (GmtTieOutside t) ~ gml'[g] (LookIndep).
    }
  }

  /** (L4 NESTED) clone of `GmtTieOutsideAfterGate` — GmtTieInside dropped. */
  lemma GmtTieOutsideAfterGateNested(rer: LW.RegExpRecord, re: R.regex, str: string, lk: L.Lookaround,
                                     r1: L.Regex, tlk: LT.Tree, gm: LG.GroupMap, t: AI.Thread,
                                     l: int, cp: nat, clk: int, S: set<LG.GroupId>)
    requires cp <= |str|
    requires NR.NestedFragmentRE(re) && T.TransWf(re)
    requires S == LL.LkBodyGroups(T.Translate(re))
    requires (set g | g in L.DefGroups(r1)) <= S
    requires GmtTieOutside(re, t, gm, S)
    requires L.Positivity(lk) && EL.PikeLkRegexRec(r1)
    requires tlk == LFU.ComputeTr(rer, [LS.Areg(r1)], PIV.InpOfCp(str, cp), LG.Empty, L.LkDir(lk))
    requires LS.LkResult(lk, tlk, gm, PIV.InpOfCp(str, cp)).Some?
    ensures var t' := t.(pc := t.pc + 1, look_regs := AReg.set_reg(t.look_regs, l, Some(cp as int), clk));
            GmtTieOutside(re, t', LS.LkResult(lk, tlk, gm, PIV.InpOfCp(str, cp)).value, S)
  {
    var inp := PIV.InpOfCp(str, cp);
    var gm2 := LS.LkResult(lk, tlk, gm, inp).value;
    var t' := t.(pc := t.pc + 1, look_regs := AReg.set_reg(t.look_regs, l, Some(cp as int), clk));
    LkResultAgreeOutsideNested(rer, lk, r1, inp, tlk, gm);      // GmAgreeOutside(gm2, gm, DefGroups(r1))
    M.LkBodyGroupsEqCapIdsInLooks(re);                    // S == CapIdsInLooks(re)
    PIV.GmOfLiveLookIndepNested(re, t.capture_regs, t.look_regs, t'.look_regs, t.quant_regs);
    forall g: LG.GroupId | g !in S
      ensures (g in gm2 <==> g in PIV.GmOfLive(re, t'.capture_regs, t'.look_regs, t'.quant_regs))
              && (g in gm2 ==> gm2[g] == PIV.GmOfLive(re, t'.capture_regs, t'.look_regs, t'.quant_regs)[g])
    {
      assert g !in (set g': LG.GroupId | g' in L.DefGroups(r1));   // DefGroups(r1) ⊆ S
      assert g !in PIV.CapIdsInLooks(re);                          // S == CapIdsInLooks(re)
      // gm2[g] ~ gm[g] (LkResultAgreeOutside) ~ gml[g] (GmtTieOutside t) ~ gml'[g] (LookIndep).
    }
  }

  /** (R2 — DEEP-CAPTURE CROSSING BRIDGE) The generalization of the gate crossing's
      DIRECT-capture tie to the WHOLE sub-first-leaf. When a positive look with body
      `r1` passes at `inp` with its body groups CLEAR coming in (`GmAgreeOn(gm, Empty,
      DefGroups(r1))` — the GateAheadClear reset condition), the merged `LkResult`
      group map `gm2` agrees, on EVERY group of `r1` (INNER/deep looks included, not
      just the DIRECT ones), with the look body's OWN first leaf `leafSub =
      FirstLeaf(tlk, inp)` computed from `Empty`. This is exactly the tie the
      direct-only carrier gets from `LkReplayMatchesSpecNested` — but there the fresh
      Pike replay STRUCTURALLY omits inner-look captures (a look compiles to a single
      `CheckOracle` leaf), whereas `LkResult == TreeRes(tlk, gm, inp, dir).1` threads
      the WHOLE body group map (`Semantics.TreeRes` LK case), so the deep captures ARE
      present in `gm2`. The tie is a PURE spec-tree fact — `M.LookBodyLeafValue`
      (`TreeLeavesFrameInside`: `gm` and `Empty` agree on the cleared body groups, so
      all leaves agree there) — needing NO oracle, NO fresh replay, and NO winning-
      thread path history. `leafSub` is taken at THIS crossing's `inp`, so the position
      is the crossing position by construction: the "position correspondence" prior
      scouts flagged is a non-issue for the carrier route. This packages the crossing
      half of the deep descent bridge `g2 in leaf_{A0} ==> g2 in leaf`. */
  lemma LkResultLandsSubFirstLeaf(rer: LW.RegExpRecord, lk: L.Lookaround, r1: L.Regex,
                                  inp: LC.Input, tlk: LT.Tree, gm: LG.GroupMap, S: set<LG.GroupId>)
    requires L.Positivity(lk)
    requires EL.PikeLkRegexRec(r1)
    requires tlk == LFU.ComputeTr(rer, [LS.Areg(r1)], inp, LG.Empty, L.LkDir(lk))
    requires LS.LkResult(lk, tlk, gm, inp).Some?
    requires S == (set g | g in L.DefGroups(r1))
    requires M.GmAgreeOn(gm, LG.Empty, S)
    ensures var dir := L.LkDir(lk);
            var gm2 := LS.LkResult(lk, tlk, gm, inp).value;
            var leafSub := LT.TreeRes(tlk, LG.Empty, inp, dir);
            leafSub.Some?
            && forall g: LG.GroupId :: g in S ==>
                                         (g in leafSub.value.1 ==> g in gm2 && gm2[g] == leafSub.value.1[g])
                                         && (g in gm2 ==> g in leafSub.value.1)
  {
    var dir := L.LkDir(lk);
    var gm2 := LS.LkResult(lk, tlk, gm, inp).value;
    // positive-gate unfold: LkResult.value == TreeRes(tlk, gm, inp, dir).value.1
    var tr := LT.TreeRes(tlk, gm, inp, dir);
    assert tr.Some? && gm2 == tr.value.1;
    // both leaf lists (from gm and from Empty) agree on S, equal length (LookBodyLeafValue)
    M.LookBodyLeafValue(rer, lk, r1, tlk, gm, inp, S);
    var sub := LT.TreeLeaves(tlk, gm, inp, dir);
    var subE := LT.TreeLeaves(tlk, LG.Empty, inp, dir);
    // tie TreeRes to the head of TreeLeaves on BOTH runs
    LT.FirstTreeLeaf(tlk, gm, inp, dir);
    LT.FirstTreeLeaf(tlk, LG.Empty, inp, dir);
    assert |sub| > 0 && tr.value == sub[0];          // tr.Some? ⟹ HdError(sub) = Some(sub[0])
    assert |subE| == |sub| && |subE| > 0;            // LookBodyLeafValue: equal length
    var leafSub := LT.TreeRes(tlk, LG.Empty, inp, dir);
    assert leafSub == LT.HdError(subE) && leafSub.Some? && leafSub.value == subE[0];
    // per-leaf S-agreement at the head leaf
    assert M.GmAgreeOn(sub[0].1, subE[0].1, S);      // LookBodyLeafValue at i == 0
    assert gm2 == sub[0].1 && leafSub.value.1 == subE[0].1;
  }

  /** (R2 — the sub-first-leaf of a top look at its RECORDED position) The spec-tree
      analogue of `M.FreshBodyMatch`: the whole first leaf of `l`'s body tree, from
      `Empty`, at the position the winning thread RECORDED for `l`
      (`AReg.get_cp(lk, l)`). Unlike `FreshBodyMatch` — an engine Pike replay that
      compiles nested looks to `CheckOracle` leaves and so records ONLY `l`'s direct
      captures — this is the SPEC tree, whose `TreeRes` threads the whole body group
      map, so it carries `l`'s DEEP (inner-look) captures too. Reads only
      `AReg.get_cp(lk, l)`, so it is congruent under any `look_regs` change off `l`
      (the property the gate-pass maintenance needs). (L5 F7a) The body tree is
      walked in the lid's OWN direction `LidDir(crv, l)` — Backward for a
      lookbehind lid, Forward otherwise — so the deep carrier is direction-generic
      (spec-to-spec: both sides are ordered spec maps, no `SwapGm` enters). Under
      the L4 scope `M.NoPosLookbehindRE` every lid is Forward. */
  ghost function SubFirstLeafAt(rer: LW.RegExpRecord, crv: CP.FCompiled, str: string, l: int,
                                lk: AReg.Regs): Option<LG.GroupMap> {
    var body := M.VBody(crv, l);
    var cp := if AReg.get_cp(lk, l).Some? then AReg.get_cp(lk, l).value else 0;
    // (2026-08-25) totality guard: `InpOfCp` needs `0 <= cp <= |str|` and
    // `Translate` needs `TransWf(body)`; every consumer that unfolds this has both.
    // (The unguarded original failed its own well-formedness check — never
    // individually verified.)
    if 0 <= cp <= |str| && T.TransWf(body) then
      var inp := PIV.InpOfCp(str, cp);
      var dir := LidDir(crv, l);
      var tlk := LFU.ComputeTr(rer, [LS.Areg(T.Translate(body))], inp, LG.Empty, dir);
      var res := LT.TreeRes(tlk, LG.Empty, inp, dir);
      if res.Some? then Some(res.value.1) else None
    else None
  }

  /** (L5 F7a) The direction a lid's body tree is walked in, read off the look
      table: `Lookbehind` ⇒ Backward, every other kind ⇒ Forward (out-of-range
      lids default to Forward; they never occur under `LookTablesOk`). Agrees
      with `L.LkDir(T.TrLookaround(crv.f_look_types[l]))` for positive lids. */
  ghost function LidDir(crv: CP.FCompiled, l: int): WP.Direction {
    if 0 <= l < |crv.f_look_types| && crv.f_look_types[l].Lookbehind? then WP.Backward else WP.Forward
  }

  // ==========================================================================
  // (L5 F7b) LOOKBEHIND lids: `SubFirstLeafAt` is the explicit backward leaf
  // `FG.BackLeafAt`, and the per-lid engine<->spec ties are the FlipGate LB
  // twins of `FreshBodyDirectInSubFirstLeaf` / `SubFirstLeafDirectInFresh`
  // (values through the endpoint swap, exactly `GmtTieInside`'s Lookbehind arm).
  // ==========================================================================

  /** (L5 F7c-4) `NormRange` absorbs the endpoint swap: `SwapRange` re-orders a
      closed range's endpoints; `NormRange` re-orders any reversed closed range.
      Either way a closed range ends ordered — so the descent value tie can be
      phrased `NormRange(x) == NormRange(y)` uniformly across forward/backward
      hops (the backward fresh match's reversed read vs the spec leaf's ordered
      value). */
  lemma NormSwapCong(rg: LG.Range)
    ensures PIV.NormRange(LBV.SwapRange(rg)) == PIV.NormRange(rg)
  {
  }

  /** RegexSize re-exported (avoids importing Semantics' unqualified name here). */
  function RegSz(r: L.Regex): nat { LS.RegexSize(r) }

  /** A non-spent quantifier head pins a `Fork`/`SetQuantToClock`, never `Accept`. */
  lemma QuantHeadPinsNonAccept(rer: LW.RegExpRecord, qm: AR.QMap, greedy: bool, min: nat, delta: LN.NoI,
                               r1: L.Regex, code: RB.code, pc: nat, pcmid: nat)
    requires AR.NfaRepL(rer, qm, L.Quantified(greedy, min, delta, r1), code, pc, pcmid)
    requires !(min == 0 && delta == LN.NN(0))
    requires NR.GetPcRE(code, pc) == Some(RB.Accept)
    ensures false
  {
    if min == 0 && delta == LN.Inf {
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
    } else {
      match delta
      case Inf =>
        if NUL.NonNullableL(r1) {
          var em: nat, e1: nat :|
            AR.NfaRepMinL(rer, qm, min - 1, r1, code, pc, em)
            && (exists qid: int :: NR.GetPcRE(code, em) == Some(RB.SetQuantToClock(qid, false))
                                   && qid in qm.quants && qm.quants[qid] == L.DefGroups(r1))
            && AR.NfaRepL(rer, qm, r1, code, em + 1, e1)
            && NR.GetPcRE(code, e1) == Some(if greedy then RB.Fork(em, e1 + 1) else RB.Fork(e1 + 1, em))
            && pcmid == e1 + 1;
          NfaRepMinLHeadPin(rer, qm, min - 1, r1, code, pc, em);
        } else if !greedy {
          // §2.5a GENERIC: `min` forced copies then the ordinary star loop.
          // With min > 0 the head at `pc` is still a clock-mark, which is all
          // these head pins need.
          var em, e1 := AR.NfaRepLGenInv(rer, qm, greedy, min, r1, code, pc, pcmid);
          NfaRepMinLHeadPin(rer, qm, min, r1, code, pc, em);
        } else {
          // §2.5b CIN-GREEDY: the head is a chain clock-mark (min > 1) or the
          // head FORK (min == 1) -- either satisfies these pins.
          var em, e1 := AR.NfaRepLCinInv(rer, qm, greedy, min, r1, code, pc, pcmid);
          NfaRepMinLHeadPin(rer, qm, min - 1, r1, code, pc, em);
          if min == 1 {
            assert em == pc;
            assert NR.GetPcRE(code, pc) == Some(RB.Fork(em + 1, e1 + 2));
          }
        }
      case NN(kx) =>
        var em: nat :| AR.NfaRepMinL(rer, qm, min, r1, code, pc, em)
                       && AR.NfaRepOptL(rer, qm, kx, greedy, r1, code, em, pcmid);
        NfaRepMinLHeadPin(rer, qm, min, r1, code, pc, em);
        if min == 0 {
          assert em == pc;
          NfaRepOptLHeadPin(rer, qm, kx, greedy, r1, code, em, pcmid);   // kx>0 ⇒ Fork; kx==0 excluded
        }
    }
  }

  /** A non-spent quantifier head pins `Fork`/`SetQuantToClock`, never `Consume`. */
  lemma QuantHeadPinsNonConsume(rer: LW.RegExpRecord, qm: AR.QMap, greedy: bool, min: nat, delta: LN.NoI,
                                r1: L.Regex, code: RB.code, pc: nat, pcmid: nat, ce: RC.char_expectation)
    requires AR.NfaRepL(rer, qm, L.Quantified(greedy, min, delta, r1), code, pc, pcmid)
    requires !(min == 0 && delta == LN.NN(0))
    requires NR.GetPcRE(code, pc) == Some(RB.Consume(ce))
    ensures false
  {
    if min == 0 && delta == LN.Inf {
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
    } else {
      match delta
      case Inf =>
        if NUL.NonNullableL(r1) {
          var em: nat, e1: nat :|
            AR.NfaRepMinL(rer, qm, min - 1, r1, code, pc, em)
            && (exists qid: int :: NR.GetPcRE(code, em) == Some(RB.SetQuantToClock(qid, false))
                                   && qid in qm.quants && qm.quants[qid] == L.DefGroups(r1))
            && AR.NfaRepL(rer, qm, r1, code, em + 1, e1)
            && NR.GetPcRE(code, e1) == Some(if greedy then RB.Fork(em, e1 + 1) else RB.Fork(e1 + 1, em))
            && pcmid == e1 + 1;
          NfaRepMinLHeadPin(rer, qm, min - 1, r1, code, pc, em);
        } else if !greedy {
          // §2.5a GENERIC: `min` forced copies then the ordinary star loop.
          // With min > 0 the head at `pc` is still a clock-mark, which is all
          // these head pins need.
          var em, e1 := AR.NfaRepLGenInv(rer, qm, greedy, min, r1, code, pc, pcmid);
          NfaRepMinLHeadPin(rer, qm, min, r1, code, pc, em);
        } else {
          // §2.5b CIN-GREEDY: the head is a chain clock-mark (min > 1) or the
          // head FORK (min == 1) -- either satisfies these pins.
          var em, e1 := AR.NfaRepLCinInv(rer, qm, greedy, min, r1, code, pc, pcmid);
          NfaRepMinLHeadPin(rer, qm, min - 1, r1, code, pc, em);
          if min == 1 {
            assert em == pc;
            assert NR.GetPcRE(code, pc) == Some(RB.Fork(em + 1, e1 + 2));
          }
        }
      case NN(kx) =>
        var em: nat :| AR.NfaRepMinL(rer, qm, min, r1, code, pc, em)
                       && AR.NfaRepOptL(rer, qm, kx, greedy, r1, code, em, pcmid);
        NfaRepMinLHeadPin(rer, qm, min, r1, code, pc, em);
        if min == 0 {
          assert em == pc;
          NfaRepOptLHeadPin(rer, qm, kx, greedy, r1, code, em, pcmid);
        }
    }
  }

  /** GENERAL: a non-spent quantifier head always pins a `Fork` or a
      `SetQuantToClock` at `pc` — the one fact every peel-with-expansion
      inversion needs to dismiss the quantifier head at a non-Fork/SQC pc. */
  lemma QuantHeadPinsForkOrSQC(rer: LW.RegExpRecord, qm: AR.QMap, greedy: bool, min: nat, delta: LN.NoI,
                               r1: L.Regex, code: RB.code, pc: nat, pcmid: nat)
    requires AR.NfaRepL(rer, qm, L.Quantified(greedy, min, delta, r1), code, pc, pcmid)
    requires !(min == 0 && delta == LN.NN(0))
    ensures NR.GetPcRE(code, pc).Some?
            && (NR.GetPcRE(code, pc).value.Fork? || NR.GetPcRE(code, pc).value.SetQuantToClock?)
  {
    if min == 0 && delta == LN.Inf {
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
    } else {
      match delta
      case Inf =>
        if NUL.NonNullableL(r1) {
          var em: nat, e1: nat :|
            AR.NfaRepMinL(rer, qm, min - 1, r1, code, pc, em)
            && (exists qid: int :: NR.GetPcRE(code, em) == Some(RB.SetQuantToClock(qid, false))
                                   && qid in qm.quants && qm.quants[qid] == L.DefGroups(r1))
            && AR.NfaRepL(rer, qm, r1, code, em + 1, e1)
            && NR.GetPcRE(code, e1) == Some(if greedy then RB.Fork(em, e1 + 1) else RB.Fork(e1 + 1, em))
            && pcmid == e1 + 1;
          NfaRepMinLHeadPin(rer, qm, min - 1, r1, code, pc, em);
          if min - 1 == 0 {
            assert em == pc;
            var qid: int :| NR.GetPcRE(code, em) == Some(RB.SetQuantToClock(qid, false));
          }
        } else if !greedy {
          // §2.5a GENERIC: `min` forced copies then the ordinary star loop; the
          // head at `pc` is a clock-mark either way, and there is no min == 1
          // special case since `min` (not `min - 1`) copies precede the loop.
          var em, e1 := AR.NfaRepLGenInv(rer, qm, greedy, min, r1, code, pc, pcmid);
          NfaRepMinLHeadPin(rer, qm, min, r1, code, pc, em);
          var qidg: int :| NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(qidg, false));
        } else {
          // §2.5b CIN-GREEDY: a chain clock-mark (min > 1) or the head FORK
          // (min == 1) -- both satisfy Fork-or-SQC.
          var em, e1 := AR.NfaRepLCinInv(rer, qm, greedy, min, r1, code, pc, pcmid);
          NfaRepMinLHeadPin(rer, qm, min - 1, r1, code, pc, em);
          if min == 1 {
            assert em == pc;
            assert NR.GetPcRE(code, pc) == Some(RB.Fork(em + 1, e1 + 2));
          }
        }
      case NN(kx) =>
        var em: nat :| AR.NfaRepMinL(rer, qm, min, r1, code, pc, em)
                       && AR.NfaRepOptL(rer, qm, kx, greedy, r1, code, em, pcmid);
        NfaRepMinLHeadPin(rer, qm, min, r1, code, pc, em);
        if min == 0 {
          assert em == pc;
          NfaRepOptLHeadPin(rer, qm, kx, greedy, r1, code, em, pcmid);
        }
    }
  }

  /** (§2.5a) The STRONG head fact for `min > 0`: the head at `pc` is always a
      clock-mark, never a `Fork` -- every scheme with `min > 0` (bounded,
      do-while, and the generic nullable-lazy one) starts with a forced-copy
      chain whose head pins `SetQuantToClock`. `QuantHeadPinsForkOrSQC`'s weaker
      `Fork? || SetQuantToClock?` cannot refute a `Fork`; callers sitting AT a
      `Fork` need this. Stated separately because factoring the generic arm
      behind `NfaRepGenL`'s trigger stopped Dafny deriving it by unfolding. */
  lemma QuantHeadMinPosPinsSQC(rer: LW.RegExpRecord, qm: AR.QMap, greedy: bool, min: nat, delta: LN.NoI,
                               r1: L.Regex, code: RB.code, pc: nat, pcmid: nat)
    requires AR.NfaRepL(rer, qm, L.Quantified(greedy, min, delta, r1), code, pc, pcmid)
    requires min > 0
    // §2.5b interim: the CIN-GREEDY head at min == 1 is a FORK, so this
    // lemma's claim needs the gate conjunct (dropped at the §2.5b flip)
    requires delta.Inf? && greedy ==> NUL.NonNullableL(r1)
    ensures NR.GetPcRE(code, pc).Some? && NR.GetPcRE(code, pc).value.SetQuantToClock?
  {
    match delta
    case Inf =>
      if NUL.NonNullableL(r1) {
        var em: nat, e1: nat :|
          AR.NfaRepMinL(rer, qm, min - 1, r1, code, pc, em)
          && (exists qid: int :: NR.GetPcRE(code, em) == Some(RB.SetQuantToClock(qid, false))
                                 && qid in qm.quants && qm.quants[qid] == L.DefGroups(r1))
          && AR.NfaRepL(rer, qm, r1, code, em + 1, e1)
          && NR.GetPcRE(code, e1) == Some(if greedy then RB.Fork(em, e1 + 1) else RB.Fork(e1 + 1, em))
          && pcmid == e1 + 1;
        NfaRepMinLHeadPin(rer, qm, min - 1, r1, code, pc, em);
        if min - 1 == 0 {
          assert em == pc;
          var qid: int :| NR.GetPcRE(code, em) == Some(RB.SetQuantToClock(qid, false));
        }
      } else {
        // GENERIC: `min` (not `min - 1`) forced copies precede the star loop,
        // so the chain is non-empty and its head pins the clock-mark directly.
        assert !greedy;   // §2.5b interim conjunct
        var em, e1 := AR.NfaRepLGenInv(rer, qm, greedy, min, r1, code, pc, pcmid);
        NfaRepMinLHeadPin(rer, qm, min, r1, code, pc, em);
      }
    case NN(kx) =>
      var em: nat :| AR.NfaRepMinL(rer, qm, min, r1, code, pc, em)
                     && AR.NfaRepOptL(rer, qm, kx, greedy, r1, code, em, pcmid);
      NfaRepMinLHeadPin(rer, qm, min, r1, code, pc, em);
  }

  /** THE forced-copy continuation builder: a `min>0` quantifier head crossing
      its first `SetQuantToClock` at `pc` unfolds to `r1` then
      `Quantified(min-1, delta)` — so the walk continuation
      `[Areg(r1), Areg(Quantified(greedy, min-1, delta, r1))] + cont` is
      represented at `pc+1`. NN via `NfaRepLQuantInv`+`Intro`; Inf via
      `NfaRepLPlusInv` (min==1 rebuilds the star's loop-view by hand, min>1 via
      `NfaRepLPlusIntro`). This is the piece the do-while seam blocked while
      `WalkOk` was in `TtLk`; with `WalkOk` gone (no Acheck-mismatch), it closes. */
  lemma QuantForcedContRep(rer: LW.RegExpRecord, qm: AR.QMap, greedy: bool, min: nat, delta: LN.NoI,
                           r1: L.Regex, code: RB.code, pc: nat, pcmid: nat, cont: LS.Actions)
    requires min > 0
    // §2.5b interim: the CIN-GREEDY head at min == 1 is a FORK, so this
    // lemma's claim needs the gate conjunct (dropped at the §2.5b flip)
    requires delta.Inf? && greedy ==> NUL.NonNullableL(r1)
    requires AR.NfaRepL(rer, qm, L.Quantified(greedy, min, delta, r1), code, pc, pcmid)
    requires AR.ActionsRepL(rer, qm, cont, code, pcmid)
    ensures AR.ActionsRepL(rer, qm,
                           [LS.Areg(r1), LS.Areg(L.Quantified(greedy, min - 1, delta, r1))] + cont, code, pc + 1)
  {
    match delta
    case NN(kx) =>
      var quant1 := L.Quantified(greedy, min - 1, LN.NN(kx), r1);
      var em := AR.NfaRepLQuantInv(rer, qm, greedy, min, kx, r1, code, pc, pcmid);
      var e_body: nat :|
        (exists qid: int :: NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(qid, false))
                            && qid in qm.quants && qm.quants[qid] == L.DefGroups(r1))
        && AR.NfaRepL(rer, qm, r1, code, pc + 1, e_body)
        && AR.NfaRepMinL(rer, qm, min - 1, r1, code, e_body, em);
      AR.NfaRepLQuantIntro(rer, qm, greedy, min - 1, kx, r1, code, e_body, em, pcmid);
      AR.ActionsRepLCons(rer, qm, LS.Areg(quant1), cont, code, e_body, pcmid);
      assert [LS.Areg(r1), LS.Areg(quant1)] + cont == [LS.Areg(r1)] + ([LS.Areg(quant1)] + cont);
      AR.ActionsRepLCons(rer, qm, LS.Areg(r1), [LS.Areg(quant1)] + cont, code, pc + 1, e_body);
    case Inf =>
      var quant1 := L.Quantified(greedy, min - 1, LN.Inf, r1);
      if !NUL.NonNullableL(r1) {
        assert {:split_here} true;   // (§2.5b) section: the generic (non-greedy) arm
        // §2.5a GENERIC: structurally the BOUNDED NN case -- min forced copies
        // then the star loop -- with no min == 1 loop-view special case, since
        // the residual at min == 1 is the plain star arm at `emg`.
        assert !greedy;   // §2.5b interim conjunct
        var emg, e1g := AR.NfaRepLGenInv(rer, qm, greedy, min, r1, code, pc, pcmid);
        var qidg: int :| NR.GetPcRE(code, emg + 1) == Some(RB.SetQuantToClock(qidg, false))
                         && qidg in qm.quants && qm.quants[qidg] == L.DefGroups(r1);
        var e_bodyg: nat :|
          (exists qid: int :: NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(qid, false))
                              && qid in qm.quants && qm.quants[qid] == L.DefGroups(r1))
          && AR.NfaRepL(rer, qm, r1, code, pc + 1, e_bodyg)
          && AR.NfaRepMinL(rer, qm, min - 1, r1, code, e_bodyg, emg);
        if min > 1 {
          AR.NfaRepLGenIntro(rer, qm, greedy, min - 1, r1, code, e_bodyg, emg, e1g, pcmid, qidg);
        } else {
          assert e_bodyg == emg;   // NfaRepMinL(0, …); the star arm at emg IS quant1
        }
        AR.ActionsRepLCons(rer, qm, LS.Areg(quant1), cont, code, e_bodyg, pcmid);
        assert [LS.Areg(r1), LS.Areg(quant1)] + cont == [LS.Areg(r1)] + ([LS.Areg(quant1)] + cont);
        AR.ActionsRepLCons(rer, qm, LS.Areg(r1), [LS.Areg(quant1)] + cont, code, pc + 1, e_bodyg);
        return;
      }
      assert {:split_here} true;   // (§2.5b) section: the NonNullable plus arm
      var em, e1 := AR.NfaRepLPlusInv(rer, qm, greedy, min, r1, code, pc, pcmid);
      var qid_em: int :| NR.GetPcRE(code, em) == Some(RB.SetQuantToClock(qid_em, false))
                         && qid_em in qm.quants && qm.quants[qid_em] == L.DefGroups(r1);
      if min == 1 {
        assert {:split_here} true;   // (§2.5b) section: min == 1 loop view
        NfaRepMinLHeadPin(rer, qm, 0, r1, code, pc, em);   // em == pc
        assert em == pc;
        // quant1 == Quantified(greedy, 0, Inf, r1) == the star; build its loop-view NfaRepL at e1.
        AR.NfaRepIncrL(rer, qm, r1, code, pc + 1, e1);   // pc + 1 <= e1, so pc <= e1
        assert pc <= e1;
        assert AR.NfaRepL(rer, qm, quant1, code, e1, e1 + 1) by {
          assert NUL.NonNullableL(r1);
          assert NR.GetPcRE(code, e1) == Some(if greedy then RB.Fork(pc, e1 + 1) else RB.Fork(e1 + 1, pc));
          assert NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(qid_em, false))
                 && qid_em in qm.quants && qm.quants[qid_em] == L.DefGroups(r1);   // em == pc
          assert AR.NfaRepL(rer, qm, r1, code, pc + 1, e1);
          // the loop-view disjunct holds with witness em2 == pc
          assert NR.GetPcRE(code, e1) == Some(if greedy then RB.Fork(pc, e1 + 1) else RB.Fork(e1 + 1, pc))
                 && pc <= e1
                 && (exists qid: int :: NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(qid, false))
                                        && qid in qm.quants && qm.quants[qid] == L.DefGroups(r1))
                 && AR.NfaRepL(rer, qm, r1, code, pc + 1, e1)
                 && e1 + 1 == e1 + 1;
        }
        AR.ActionsRepLCons(rer, qm, LS.Areg(quant1), cont, code, e1, pcmid);
        assert [LS.Areg(r1), LS.Areg(quant1)] + cont == [LS.Areg(r1)] + ([LS.Areg(quant1)] + cont);
        AR.ActionsRepLCons(rer, qm, LS.Areg(r1), [LS.Areg(quant1)] + cont, code, pc + 1, e1);
      } else {
        var e_body: nat :|
          (exists qid: int :: NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(qid, false))
                              && qid in qm.quants && qm.quants[qid] == L.DefGroups(r1))
          && AR.NfaRepL(rer, qm, r1, code, pc + 1, e_body)
          && AR.NfaRepMinL(rer, qm, min - 2, r1, code, e_body, em);
        AR.NfaRepLPlusIntro(rer, qm, greedy, min - 1, r1, code, e_body, em, e1, pcmid, qid_em);
        AR.ActionsRepLCons(rer, qm, LS.Areg(quant1), cont, code, e_body, pcmid);
        assert [LS.Areg(r1), LS.Areg(quant1)] + cont == [LS.Areg(r1)] + ([LS.Areg(quant1)] + cont);
        AR.ActionsRepLCons(rer, qm, LS.Areg(r1), [LS.Areg(quant1)] + cont, code, pc + 1, e_body);
      }
  }

  /** The forced-copy head's `qm.quants` binding: a `min>0` quantifier block
      opens with `SetQuantToClock(qid, false)` whose `qid` the tables map to
      exactly `DefGroups(r1)` — extracted from the same `NfaRepL` inversions
      `QuantForcedContRep` uses, without building the continuation. */
  lemma QuantHeadSQCPin(rer: LW.RegExpRecord, qm: AR.QMap, greedy: bool, min: nat, delta: LN.NoI,
                        r1: L.Regex, code: RB.code, pc: nat, pcmid: nat)
    requires min > 0
    // §2.5b interim: the CIN-GREEDY head at min == 1 is a FORK, so this
    // lemma's claim needs the gate conjunct (dropped at the §2.5b flip)
    requires delta.Inf? && greedy ==> NUL.NonNullableL(r1)
    requires AR.NfaRepL(rer, qm, L.Quantified(greedy, min, delta, r1), code, pc, pcmid)
    ensures exists qid: int ::
              NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(qid, false))
              && qid in qm.quants && qm.quants[qid] == L.DefGroups(r1)
  {
    match delta
    case NN(kx) =>
      var em := AR.NfaRepLQuantInv(rer, qm, greedy, min, kx, r1, code, pc, pcmid);
      var e_body: nat :|
        (exists qid: int :: NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(qid, false))
                            && qid in qm.quants && qm.quants[qid] == L.DefGroups(r1))
        && AR.NfaRepL(rer, qm, r1, code, pc + 1, e_body)
        && AR.NfaRepMinL(rer, qm, min - 1, r1, code, e_body, em);
    case Inf =>
      if !NUL.NonNullableL(r1) {
        // §2.5a GENERIC: min >= 1 forced copies, so `pc` carries the clock-mark
        assert !greedy;   // §2.5b interim conjunct
        var emg, e1g := AR.NfaRepLGenInv(rer, qm, greedy, min, r1, code, pc, pcmid);
        NfaRepMinLHeadPin(rer, qm, min, r1, code, pc, emg);
        return;
      }
      var em, e1 := AR.NfaRepLPlusInv(rer, qm, greedy, min, r1, code, pc, pcmid);
      if min == 1 {
        NfaRepMinLHeadPin(rer, qm, 0, r1, code, pc, em);
        assert em == pc;
        var qid_em: int :| NR.GetPcRE(code, em) == Some(RB.SetQuantToClock(qid_em, false))
                           && qid_em in qm.quants && qm.quants[qid_em] == L.DefGroups(r1);
      } else {
        var e_body: nat :|
          (exists qid: int :: NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(qid, false))
                              && qid in qm.quants && qm.quants[qid] == L.DefGroups(r1))
          && AR.NfaRepL(rer, qm, r1, code, pc + 1, e_body)
          && AR.NfaRepMinL(rer, qm, min - 2, r1, code, e_body, em);
      }
  }

  /** THE ONE OUTSTANDING WALK FACT (the do-while flag shield): a
      NonNullable-headed iteration list's tree is flag-INSENSITIVE —
      `BoolTreeLk` reads the flag only at `Acheck` nodes and re-arms it at
      every `Read`, and a NonNullable body Reads on every completing path
      before the guard. TRUE for the fragment (`NfaRepL`'s do-while shapes
      carry `NonNullableL(r1)`); BODILESS pending the structural induction
      (fuel over `MsizeA` with a Read-shielding measure). Consumed only by the
      BACKWARD (loop-view) fork arm, where the iteration thread runs at
      `exit_allowed == true` with no interposed `BeginLoop` to absorb it.
      PROOF: the NonNullable head at index 0 shields EVERY `Acheck` in the
      list (`ShieldedActs`' witness is j == 0 throughout), so the proven
      `CE.BoolFlagLift` applies directly. */
  lemma BoolTreeLkGuardShield(rer: LW.RegExpRecord, r1: L.Regex, rest: LS.Actions,
                              inp: LC.Input, ti: LT.Tree)
    requires NUL.NonNullableL(r1)
    requires EL.PikeLkActions([LS.Areg(r1)] + rest)
    requires EL.BoolTreeLk(rer, [LS.Areg(r1)] + rest, inp, BS.CannotExit, ti)
    ensures EL.BoolTreeLk(rer, [LS.Areg(r1)] + rest, inp, BS.CanExit, ti)
  {
    var acts := [LS.Areg(r1)] + rest;
    assert CE.ShieldedActs(acts) by {
      forall i | 0 <= i < |acts| && acts[i].Acheck?
        ensures exists j :: 0 <= j < i && acts[j].Areg? && NUL.NonNullableL(acts[j].r)
      {
        assert acts[0] == LS.Areg(r1);
        assert i >= 1;
        assert acts[0].Areg? && NUL.NonNullableL(acts[0].r);
      }
    }
    CE.BoolFlagLift(rer, acts, inp, ti);
  }

  /** `TR.CpOf` re-exported locally (avoids importing TreeRep just for it). */
  function TR_CpOf(inp: LC.Input): nat { |inp.pref| }

  /** A `PikeLk` lookaround head has a `NoLkBrL` body: a POSITIVE look (fwd/bwd)
      gives it directly (widened `PikeLkRegex(LookaroundR)`), the NEGATIVE flavours
      are group-free (⊆ `NoLkBrL`). Reusable at the gate for `LkResultAgreeOutside`. */
  lemma LookBodyNoLkBr(lk: L.Lookaround, r1: L.Regex)
    requires EL.PikeLkRegex(L.LookaroundR(lk, r1))
    ensures EL.NoLkBrL(r1)
  {
    if L.Positivity(lk) {
      // widened PikeLkRegex(LookaroundR) == NoLkBrL(r1) for a positive look.
    } else {
      EL.GroupFreeLNoLkBr(r1);   // requires GroupFreeL(r1), the else-branch of PikeLkRegex
    }
  }

  /** `NoDupSeq(AllDefsActs)` threads to the tail (any head): the head contributes
      a PREFIX of `AllDefsActs`, so the suffix stays dup-free (`NoDupConcat`). */
  lemma NoDupAllDefsTail(acts: LS.Actions)
    requires |acts| > 0 && M.NoDupSeq(M.AllDefsActs(acts))
    ensures M.NoDupSeq(M.AllDefsActs(acts[1..]))
  {
    assert acts == [acts[0]] + acts[1..];
    M.AllDefsActsCons(acts[0], acts[1..]);
    var pre: seq<LG.GroupId> := if acts[0].Areg? then L.DefGroups(acts[0].r) else [];
    assert M.AllDefsActs(acts) == pre + M.AllDefsActs(acts[1..]);
    M.NoDupConcat(pre, M.AllDefsActs(acts[1..]));
  }

  /** A top-level gate's body groups are among the regex's defined groups. */
  lemma RegexTopGateSubDefs(r: L.Regex, lk: L.Lookaround, r1: L.Regex)
    requires RegexTopGate(r, lk, r1)
    ensures (set g | g in L.DefGroups(r1)) <= (set g | g in L.DefGroups(r))
    decreases r
  {
    match r
    case LookaroundR(lk2, rb) =>
      assert rb == r1 && L.DefGroups(r) == L.DefGroups(r1);
    case Sequence(a, b) =>
      assert L.DefGroups(r) == L.DefGroups(a) + L.DefGroups(b);
      if RegexTopGate(a, lk, r1) { RegexTopGateSubDefs(a, lk, r1); }
      else { RegexTopGateSubDefs(b, lk, r1); }
      assert forall g :: g in L.DefGroups(a) || g in L.DefGroups(b) ==> g in L.DefGroups(a) + L.DefGroups(b);
    case Disjunction(a, b) =>
      assert L.DefGroups(r) == L.DefGroups(a) + L.DefGroups(b);
      if RegexTopGate(a, lk, r1) { RegexTopGateSubDefs(a, lk, r1); }
      else { RegexTopGateSubDefs(b, lk, r1); }
      assert forall g :: g in L.DefGroups(a) || g in L.DefGroups(b) ==> g in L.DefGroups(a) + L.DefGroups(b);
    case Group(id, rb) =>
      assert L.DefGroups(r) == [id] + L.DefGroups(rb);
      RegexTopGateSubDefs(rb, lk, r1);
      assert forall g :: g in L.DefGroups(rb) ==> g in [id] + L.DefGroups(rb);
    case Quantified(_, _, _, _) =>   // RegexTopGate false — vacuous
    case Epsilon =>
    case Character(_) =>
    case AnchorR(_) =>
    case Backreference(_) =>
  }

  /** A top-level gate's body groups are among the regex's INSIDE-LOOK groups
      (`LkBodyGroups`). The SET-based analog of `RegexTopGateSubDefs` — needed for
      the quantifier-STABLE disjointness invariant (`LkBodyGroups` is a set, so
      `LkBodyGroups(Quantified(..,r1)) == LkBodyGroups(r1)` absorbs the iteration
      duplication that breaks the seq-based `NoDupSeq(AllDefsActs)`). */
  lemma RegexTopGateSubLkBody(r: L.Regex, lk: L.Lookaround, r1: L.Regex)
    requires RegexTopGate(r, lk, r1)
    ensures (set g | g in L.DefGroups(r1)) <= LL.LkBodyGroups(r)
    decreases r
  {
    match r
    case LookaroundR(lk2, rb) =>
      assert rb == r1;
      assert LL.LkBodyGroups(r) == (set g | g in L.DefGroups(r1)) + LL.LkBodyGroups(r1);
    case Sequence(a, b) =>
      assert LL.LkBodyGroups(r) == LL.LkBodyGroups(a) + LL.LkBodyGroups(b);
      if RegexTopGate(a, lk, r1) { RegexTopGateSubLkBody(a, lk, r1); }
      else { RegexTopGateSubLkBody(b, lk, r1); }
    case Disjunction(a, b) =>
      assert LL.LkBodyGroups(r) == LL.LkBodyGroups(a) + LL.LkBodyGroups(b);
      if RegexTopGate(a, lk, r1) { RegexTopGateSubLkBody(a, lk, r1); }
      else { RegexTopGateSubLkBody(b, lk, r1); }
    case Group(id, rb) =>
      assert LL.LkBodyGroups(r) == LL.LkBodyGroups(rb);
      RegexTopGateSubLkBody(rb, lk, r1);
    case Quantified(_, _, _, _) =>   // RegexTopGate false — vacuous
    case Epsilon =>
    case Character(_) =>
    case AnchorR(_) =>
    case Backreference(_) =>
  }

  // ---- TOP-LEVEL look def-list: the QUANTIFIER-STABLE disjointness carrier -----
  // `AllDefsActs` is a seq and its `NoDupSeq` breaks at a min>0 quantifier unfold
  // (`[Areg r1, Areg (Quantified .. r1)]` duplicates `DefGroups(r1)`). `TopLkDefsList`
  // collects only the def-groups of TOP-LEVEL looks (mirrors `RegexTopGate` — STOPS
  // at `Quantified`), so a re-entrant look under a quantifier contributes nothing
  // and the duplication vanishes. `NoDupSeq(TopLkDefsListActs(acts))` gives the
  // CheckOracle look-vs-look disjointness (crossed body ∩ sibling body == {}) and
  // is the replacement target for the `NoDupSeq(AllDefsActs)` invariant.

  /** TOP-LEVEL def-list of `r` (not under a quantifier): look bodies contribute
      their full `DefGroups`, `Group` prepends its OWN id (session 5: needed so
      the carrier also pins Open-crossing freshness — the opened gid is absent
      from every pending body ahead), quantifiers are OPAQUE. */
  ghost function TopLkDefsList(r: L.Regex): seq<LG.GroupId>
    decreases r
  {
    match r
    case LookaroundR(lk, r1) => L.DefGroups(r1)
    case Sequence(a, b) => TopLkDefsList(a) + TopLkDefsList(b)
    case Disjunction(a, b) => TopLkDefsList(a) + TopLkDefsList(b)
    case Group(gid, r1) => [gid] + TopLkDefsList(r1)
    case Quantified(_, _, _, _) => []   // STOP: re-entrant looks handled by the Reset
    case _ => []
  }

  /** Action-level lift of `TopLkDefsList`. */
  ghost function TopLkDefsListActs(acts: LS.Actions): seq<LG.GroupId>
    decreases |acts|
  {
    if |acts| == 0 then []
    else (if acts[0].Areg? then TopLkDefsList(acts[0].r) else []) + TopLkDefsListActs(acts[1..])
  }

  /** A top-level gate's body groups are among `r`'s top-level look def-list. */
  lemma RegexTopGateSubTopLk(r: L.Regex, lk: L.Lookaround, r1: L.Regex)
    requires RegexTopGate(r, lk, r1)
    ensures (set g | g in L.DefGroups(r1)) <= (set g | g in TopLkDefsList(r))
    decreases r
  {
    match r
    case LookaroundR(lk2, rb) =>
      assert rb == r1 && TopLkDefsList(r) == L.DefGroups(r1);
    case Sequence(a, b) =>
      assert TopLkDefsList(r) == TopLkDefsList(a) + TopLkDefsList(b);
      if RegexTopGate(a, lk, r1) { RegexTopGateSubTopLk(a, lk, r1); }
      else { RegexTopGateSubTopLk(b, lk, r1); }
    case Disjunction(a, b) =>
      assert TopLkDefsList(r) == TopLkDefsList(a) + TopLkDefsList(b);
      if RegexTopGate(a, lk, r1) { RegexTopGateSubTopLk(a, lk, r1); }
      else { RegexTopGateSubTopLk(b, lk, r1); }
    case Group(id, rb) =>
      assert TopLkDefsList(r) == [id] + TopLkDefsList(rb);
      RegexTopGateSubTopLk(rb, lk, r1);
      assert forall g :: g in TopLkDefsList(rb) ==> g in TopLkDefsList(r);
    case Quantified(_, _, _, _) =>
    case Epsilon =>
    case Character(_) =>
    case AnchorR(_) =>
    case Backreference(_) =>
  }

  /** A regex's top-level look def-list is a SUBSEQUENCE of its full `DefGroups`
      (top-level looks contribute `DefGroups(body)`, which is among `DefGroups(r)`;
      `Group` prepends only its own id, `Quantified` drops to `[]`). Membership form. */
  lemma TopLkDefsListSubDefGroups(r: L.Regex)
    ensures forall g :: g in TopLkDefsList(r) ==> g in L.DefGroups(r)
    decreases r
  {
    match r
    case LookaroundR(lk, r1) =>
    case Sequence(a, b) =>
      TopLkDefsListSubDefGroups(a); TopLkDefsListSubDefGroups(b);
    case Disjunction(a, b) =>
      TopLkDefsListSubDefGroups(a); TopLkDefsListSubDefGroups(b);
    case Group(id, r1) =>
      TopLkDefsListSubDefGroups(r1);
    case Quantified(_, _, _, _) =>
    case Epsilon =>
    case Character(_) =>
    case AnchorR(_) =>
    case Backreference(_) =>
  }

  /** C3, per-regex: every top-level `Quantified` body's groups avoid `R` (the
      top-level look groups of the RIGHT context); `Sequence` widens `R` for its
      left arm by the right arm's contribution; `Disjunction` arms are
      alternatives (same `R`); STOPS at `Quantified` (inner quantifiers are
      re-established at their own unfold) and `LookaroundR` (look bodies never
      enter the walk). */
  ghost predicate QuantsRightClear(r: L.Regex, R: set<LG.GroupId>)
    decreases r
  {
    match r
    case Sequence(a, b) =>
      QuantsRightClear(a, (set g | g in TopLkDefsList(b)) + R) && QuantsRightClear(b, R)
    case Disjunction(a, b) => QuantsRightClear(a, R) && QuantsRightClear(b, R)
    case Group(_, rb) => QuantsRightClear(rb, R)
    case Quantified(_, _, _, r1) => forall g :: g in L.DefGroups(r1) ==> g !in R
    case _ => true
  }

  /** An `Areg` member's body groups are among the action list's `AllDefsActs`. */
  lemma AllDefsActsMemberSub(acts: LS.Actions, i: nat)
    requires 0 <= i < |acts| && acts[i].Areg?
    ensures (set g | g in L.DefGroups(acts[i].r)) <= (set g | g in M.AllDefsActs(acts))
    decreases |acts|
  {
    assert acts == [acts[0]] + acts[1..];
    M.AllDefsActsCons(acts[0], acts[1..]);   // AllDefsActs(acts) == DefGroups(acts[0].r) + AllDefsActs(acts[1..])
    if i == 0 {
      assert forall g :: g in L.DefGroups(acts[0].r) ==> g in M.AllDefsActs(acts);
    } else {
      AllDefsActsMemberSub(acts[1..], i - 1);
      assert acts[1..][i - 1] == acts[i];
      assert forall g :: g in M.AllDefsActs(acts[1..]) ==> g in M.AllDefsActs(acts);
    }
  }

  /** Two dup-free translated `DefGroups` sequences over CAP-DISJOINT `R.regex`
      concatenate dup-free — the alt/con step of `TranslateDefGroupsNoDup`. */
  lemma NoDupAltCon(r1: R.regex, r2: R.regex)
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
        if a[i] == b[j] { assert a[i] in PIV.CapIds(r1) * PIV.CapIds(r2); }   // contradicts disjoint
      }
    }
    M.NoDupFromDisjoint(a, b);
  }

  /** The translated regex's `DefGroups` sequence has NO DUPLICATES: sibling
      subtrees get disjoint cap ids (`CapUnique`), a capture's own id is fresh
      (`cid ∉ CapIds(body)`). The seq-level companion of
      `M.TranslateDefGroupsEqCapIds` (which gives only the set). This is what feeds
      the `NoDupSeq(AllDefsActs)` walk-invariant at the entry (`LiftInit`). */
  lemma TranslateDefGroupsNoDup(r: R.regex)
    requires T.TransWf(r) && PIV.CapUnique(r)
    ensures M.NoDupSeq(L.DefGroups(T.Translate(r)))
    decreases r
  {
    match r
    case Re_empty =>
    case Re_character(_) =>
    case Re_anchor(_) =>
    case Re_alt(r1, r2) =>
      TranslateDefGroupsNoDup(r1); TranslateDefGroupsNoDup(r2);
      M.TranslateDefGroupsEqCapIds(r1); M.TranslateDefGroupsEqCapIds(r2);
      assert L.DefGroups(T.Translate(r)) == L.DefGroups(T.Translate(r1)) + L.DefGroups(T.Translate(r2));
      NoDupAltCon(r1, r2);
    case Re_con(r1, r2) =>
      TranslateDefGroupsNoDup(r1); TranslateDefGroupsNoDup(r2);
      M.TranslateDefGroupsEqCapIds(r1); M.TranslateDefGroupsEqCapIds(r2);
      assert L.DefGroups(T.Translate(r)) == L.DefGroups(T.Translate(r1)) + L.DefGroups(T.Translate(r2));
      NoDupAltCon(r1, r2);
    case Re_quant(_, _, q, r1) =>
      TranslateDefGroupsNoDup(r1);
      assert L.DefGroups(T.Translate(r)) == L.DefGroups(T.Translate(r1));
    case Re_capture(cid, r1) =>
      TranslateDefGroupsNoDup(r1);
      M.TranslateDefGroupsEqCapIds(r1);   // set(DefGroups(Translate(r1))) == CapIds(r1)
      assert L.DefGroups(T.Translate(r)) == [cid as nat] + L.DefGroups(T.Translate(r1));
      assert (cid as nat) !in PIV.CapIds(r1);   // CapUnique(capture)
      assert forall j :: 0 <= j < |L.DefGroups(T.Translate(r1))| ==> L.DefGroups(T.Translate(r1))[j] != cid as nat by {
        forall j | 0 <= j < |L.DefGroups(T.Translate(r1))| ensures L.DefGroups(T.Translate(r1))[j] != cid as nat {
          assert L.DefGroups(T.Translate(r1))[j] in (set g | g in L.DefGroups(T.Translate(r1)));
        }
      }
      M.NoDupPrepend(cid as nat, L.DefGroups(T.Translate(r1)));
    case Re_lookaround(_, lk, r1) =>
      TranslateDefGroupsNoDup(r1);
      assert L.DefGroups(T.Translate(r)) == L.DefGroups(T.Translate(r1));
  }

  // ---- (C) the ComputeTr shape fact -----------------------------------------

  /** No `Backreference` anywhere in a Linden regex (including inside lookaround
      bodies). `Translate` NEVER emits a `Backreference`, so every translated
      regex satisfies this — which is exactly what keeps `ReadBackRef` (the one
      shape `PikeSubtreeLk` forbids) out of the computed tree. */
  predicate NoBackrefRegex(r: L.Regex)
    decreases r
  {
    match r
    case Epsilon => true
    case Character(_) => true
    case Disjunction(r1, r2) => NoBackrefRegex(r1) && NoBackrefRegex(r2)
    case Sequence(r1, r2) => NoBackrefRegex(r1) && NoBackrefRegex(r2)
    case Quantified(_, _, _, r1) => NoBackrefRegex(r1)
    case Group(_, r1) => NoBackrefRegex(r1)
    case LookaroundR(_, r1) => NoBackrefRegex(r1)
    case AnchorR(_) => true
    case Backreference(_) => false
  }

  predicate NoBackrefAction(a: LS.Action) {
    match a case Areg(r) => NoBackrefRegex(r) case Aclose(_) => true case Acheck(_) => true
  }

  /** `Translate` produces a backreference-free Linden regex. */
  lemma TranslateNoBackref(re: R.regex)
    requires T.TransWf(re)
    ensures NoBackrefRegex(T.Translate(re))
    decreases re
  {
    match re
    case Re_empty =>
    case Re_character(c) =>
    case Re_alt(r1, r2) => TranslateNoBackref(r1); TranslateNoBackref(r2);
    case Re_con(r1, r2) => TranslateNoBackref(r1); TranslateNoBackref(r2);
    case Re_quant(_, _, q, r1) => TranslateNoBackref(r1);
    case Re_capture(cid, r1) => TranslateNoBackref(r1);
    case Re_lookaround(_, lk, r1) => TranslateNoBackref(r1);
    case Re_anchor(a) =>
  }

  // ---- (V) the value bridge into MainExtraction ------------------------------

  /** The FREE half of the winning leaf's value tie: OUTSIDE `S`, the leaf gm
      equals the winning thread's live denotation — no sim, no (E) path-presence.
      It is pure machine-A + leaf agreement: `BestMatchRE` gives the tstar first
      leaf's gm IS `GmOfLive(re, th.caps)`, and `FirstLeafAgreeOutside` gives that
      same gm agrees with the t-side leaf `leafgm` outside `S`. `GmAgreeOutside`
      is symmetric in the value clause, so it flips to `GmtTieOutside`'s shape
      (leaf-keyed). This is the exact `GmtTieOutside` hypothesis `L3aValueBridge`
      consumes for its outside-`S` branch, discharged from already-proven facts. */
  // ==========================================================================
  // (E3) THE LOOK-PATH CARRIER (per-thread). For every lid owning a present
  // inside-S group in gmt, the thread's OWN clocks witness the outer path to
  // lid's node plus the look-stamp dominance pair — the coupled fact "the look
  // was crossed AFTER the last enclosing-quant re-stamp" that no engine-only
  // invariant can see (g surviving in gmt IS its tracker: the B-side Reset
  // removes look-body groups at every SetQuantToClock). Established at gate
  // pass (NI.GateCrossLookNest), vacated at SetQuantToClock (NI.LookBodyCaps-
  // UnderQid), monotone elsewhere. Carried at LiftInv level — ThreadRepLk and
  // the per-instruction case lemmas are untouched.
  // ==========================================================================
  ghost predicate LookNestOkT(re: R.regex, S: set<LG.GroupId>, gmt: LG.GroupMap, th: AI.Thread) {
    forall lid: nat | lid in LTB.LookIds(re) ::
      (exists g: LG.GroupId :: g in S && g in gmt && g in PIV.CapIds(NI.LookBodyOfRE(re, lid))) ==>
        NI.LookPathPresent(re, th.capture_regs.a_clk, th.quant_regs.a_clk, -1, lid)
        && AI.get_idx(th.look_regs.a_clk, lid as int) >= 0
        && AI.get_idx(th.look_regs.a_clk, lid as int)
           >= NI.MxAtLidLk(re, th.quant_regs.a_clk, -1, lid)
  }

  /** The carrier, index-wise over the ACTIVE pairing (deliberately a plain
      forall, not a cons-recursion: list surgery reduces to index shifts). */
  ghost predicate LookNestRepC(re: R.regex, S: set<LG.GroupId>,
                               tl: seq<(LT.Tree, LG.GroupMap)>, vl: seq<AI.Thread>) {
    |tl| == |vl| && forall i | 0 <= i < |tl| :: LookNestOkT(re, S, tl[i].1, vl[i])
  }

  /** The converse carrier, index-wise over both pairings. */
  ghost predicate LookNestBackRepC(re: R.regex, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
                                   S: set<LG.GroupId>, tl: seq<(LT.Tree, LG.GroupMap)>,
                                   vl: seq<AI.Thread>, ncap: int, nlook: int, nquant: int) {
    |tl| == |vl|
    && forall i | 0 <= i < |tl| ::
      LookNestBackT(re, crv, str, ov, S, tl[i].1, vl[i], ncap, nlook, nquant)
  }

  ghost predicate LookNestBackRepB(re: R.regex, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
                                   S: set<LG.GroupId>, tl: seq<(LT.Tree, LG.GroupMap)>,
                                   bl: seq<(AI.Thread, RC.char_expectation)>,
                                   ncap: int, nlook: int, nquant: int) {
    |tl| == |bl|
    && forall i | 0 <= i < |tl| ::
      LookNestBackT(re, crv, str, ov, S, tl[i].1, bl[i].0, ncap, nlook, nquant)
  }

  /** `PSM.ResumeAll` element-wise: same length, each thread re-armed at pc+1
      with REGISTERS UNCHANGED — the carrier crosses the consume for free. */
  lemma ResumeAllLen(bl: seq<(AI.Thread, RC.char_expectation)>)
    ensures |PSM.ResumeAll(bl)| == |bl|
    decreases bl
  {
    if |bl| > 0 { ResumeAllLen(bl[1..]); }
  }

  lemma ResumeAllIndex(bl: seq<(AI.Thread, RC.char_expectation)>, i: int)
    requires 0 <= i < |bl|
    ensures |PSM.ResumeAll(bl)| == |bl|
    ensures PSM.ResumeAll(bl)[i] == bl[i].0.(exit_allowed := true, pc := bl[i].0.pc + 1)
    decreases bl
  {
    ResumeAllLen(bl);
    if i > 0 { ResumeAllIndex(bl[1..], i - 1); }
  }

  /** The carrier over the BLOCKED pairing (same matching filter as
      `BlockedRepLkC`). */
  ghost predicate LookNestRepB(re: R.regex, S: set<LG.GroupId>,
                               tl: seq<(LT.Tree, LG.GroupMap)>,
                               bl: seq<(AI.Thread, RC.char_expectation)>) {
    |tl| == |bl| && forall i | 0 <= i < |tl| :: LookNestOkT(re, S, tl[i].1, bl[i].0)
  }

  /** `QmapOk`'s entry at a specific quant id IS the def-groups of that id's
      body subtree — the per-qid extraction the SetQuant carrier case needs
      (`QidBody`'s descent matches `QmapOk`'s recursion, so no uniqueness is
      required). */
  lemma QmapOkAtQid(re: R.regex, qm: AR.QMap, qid: nat)
    requires T.TransWf(re) && AR.QmapOk(re, qm)
    requires qid in PIV.QuantIds(re)
    ensures (qid as int) in qm.quants
    ensures T.TransWf(PIV.QidBody(re, qid))
    ensures qm.quants[qid as int] == L.DefGroups(T.Translate(PIV.QidBody(re, qid)))
    decreases re
  {
    match re
    case Re_alt(r1, r2) =>
      if qid in PIV.QuantIds(r1) { QmapOkAtQid(r1, qm, qid); } else { QmapOkAtQid(r2, qm, qid); }
    case Re_con(r1, r2) =>
      if qid in PIV.QuantIds(r1) { QmapOkAtQid(r1, qm, qid); } else { QmapOkAtQid(r2, qm, qid); }
    case Re_quant(nul, qid0, cq, r1) =>
      if qid0 >= 0 && (qid0 as nat) == qid {
      } else {
        QmapOkAtQid(r1, qm, qid);
      }
    case Re_capture(_, r1) => QmapOkAtQid(r1, qm, qid);
    case Re_lookaround(_, _, r1) => QmapOkAtQid(r1, qm, qid);
  }

  /** `LmapOk`'s entry at a specific look id IS that node's translated flavour
      and body — the per-lid extraction the gate carrier case needs (the
      descent matches `LookBodyOfRE`'s, so no uniqueness is required). */
  lemma LmapOkAtLid(re: R.regex, qm: AR.QMap, lid: nat)
    requires T.TransWf(re) && AR.LmapOk(re, qm)
    requires lid in LTB.LookIds(re)
    ensures (lid as int) in qm.looks
    ensures T.TransWf(NI.LookBodyOfRE(re, lid))
    ensures qm.looks[lid as int].1 == T.Translate(NI.LookBodyOfRE(re, lid))
    decreases re
  {
    match re
    case Re_alt(r1, r2) =>
      if lid in LTB.LookIds(r1) { LmapOkAtLid(r1, qm, lid); } else { LmapOkAtLid(r2, qm, lid); }
    case Re_con(r1, r2) =>
      if lid in LTB.LookIds(r1) { LmapOkAtLid(r1, qm, lid); } else { LmapOkAtLid(r2, qm, lid); }
    case Re_quant(_, _, _, r1) => LmapOkAtLid(r1, qm, lid);
    case Re_capture(_, r1) => LmapOkAtLid(r1, qm, lid);
    case Re_lookaround(lid0, la0, r1) =>
      if lid0 >= 0 && (lid0 as nat) == lid {
      } else {
        LmapOkAtLid(r1, qm, lid);
      }
  }

  // ==========================================================================
  // (E4) THE CONVERSE CARRIER: dominance ⟹ the fresh match's inside-S groups
  // SURVIVE in gmt. "The look stamp beats every path-quant clock" means no
  // enclosing quantifier re-stamped (hence no Reset fired on the look's
  // groups) since the last crossing — so what the crossing folded is still
  // there. This is the reverse value tie's missing half: presence in the
  // RECONSTRUCTED bank exhibits dominance (FilterPresenceExtractLk), and
  // dominance here forces leaf membership.
  // ==========================================================================
  ghost predicate LookNestBackT(re: R.regex, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
                                S: set<LG.GroupId>, gmt: LG.GroupMap, th: AI.Thread,
                                ncap: int, nlook: int, nquant: int) {
    forall lid: nat | lid in LTB.LookIds(re) ::
      (M.MatchedPosLA(crv, th.look_regs, lid as int)
       && NI.LookPathDom(re, AI.get_idx(th.look_regs.a_clk, lid as int), th.quant_regs.a_clk, lid))
      ==>
        var rf := M.FreshBodyMatch(crv, str, lid as int, th.look_regs, ov, ncap, nlook, nquant);
        rf.Some? ==>
          forall g: LG.GroupId ::
            g in S && g in PIV.CapIds(NI.LookBodyOfRE(re, lid))
            && g in PIV.GmOfLive(NI.LookBodyOfRE(re, lid), rf.value.capture_regs,
                                 rf.value.look_regs, rf.value.quant_regs)
            ==> g in gmt
  }

  // ==========================================================================
  // (D3) TOP-LEVEL-RESTRICTED CARRIERS. The `*Top` variants quantify over
  // `NI.TopLookIds(re)` (the looks whose gate sits in the MAIN code) instead of
  // `LTB.LookIds(re)`. At a nested gate the main thread stamps ONLY top-level
  // looks (inner looks have no main-code CheckOracle), so the inner-lid
  // obligations of `LookNestOkT`/`LookNestBackT` are UNSATISFIABLE at depth >= 2;
  // restricting to `TopLookIds` DROPS them. `TopLookIds == LookIds` at depth 1,
  // so `*Top` is a strict weakening of the full carrier (`NI.TopLookIdsIn`).
  // ==========================================================================
  ghost predicate LookNestOkTTop(re: R.regex, S: set<LG.GroupId>, gmt: LG.GroupMap, th: AI.Thread) {
    forall lid: nat | lid in NI.TopLookIds(re) ::
      (lid in LTB.LookIds(re)   // (2026-08-28) wf guard for `LookBodyOfRE`/`LookPathPresent` (TopLookIds ⊆ LookIds)
       && exists g: LG.GroupId :: g in S && g in gmt && g in PIV.CapIds(NI.LookBodyOfRE(re, lid))) ==>
        NI.LookPathPresent(re, th.capture_regs.a_clk, th.quant_regs.a_clk, -1, lid)
        && AI.get_idx(th.look_regs.a_clk, lid as int) >= 0
        && AI.get_idx(th.look_regs.a_clk, lid as int)
           >= NI.MxAtLidLk(re, th.quant_regs.a_clk, -1, lid)
  }

  ghost predicate LookNestBackTTop(re: R.regex, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
                                   S: set<LG.GroupId>, gmt: LG.GroupMap, th: AI.Thread,
                                   ncap: int, nlook: int, nquant: int) {
    forall lid: nat | lid in NI.TopLookIds(re) ::
      (M.MatchedPosLA(crv, th.look_regs, lid as int)
       && lid in LTB.LookIds(re)   // (2026-08-25) wf guard for `LookPathDom` (TopLookIds ⊆ LookIds)
       && NI.LookPathDom(re, AI.get_idx(th.look_regs.a_clk, lid as int), th.quant_regs.a_clk, lid))
      ==>
        var rf := M.FreshBodyMatch(crv, str, lid as int, th.look_regs, ov, ncap, nlook, nquant);
        rf.Some? ==>
          forall g: LG.GroupId ::
            g in S && g in PIV.CapIds(NI.LookBodyOfRE(re, lid))
            && g in PIV.GmOfLive(NI.LookBodyOfRE(re, lid), rf.value.capture_regs,
                                 rf.value.look_regs, rf.value.quant_regs)
            ==> g in gmt
  }

  ghost predicate LookNestRepCTop(re: R.regex, S: set<LG.GroupId>,
                                  tl: seq<(LT.Tree, LG.GroupMap)>, vl: seq<AI.Thread>) {
    |tl| == |vl| && forall i | 0 <= i < |tl| :: LookNestOkTTop(re, S, tl[i].1, vl[i])
  }

  ghost predicate LookNestBackRepCTop(re: R.regex, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
                                      S: set<LG.GroupId>, tl: seq<(LT.Tree, LG.GroupMap)>,
                                      vl: seq<AI.Thread>, ncap: int, nlook: int, nquant: int) {
    |tl| == |vl|
    && forall i | 0 <= i < |tl| ::
      LookNestBackTTop(re, crv, str, ov, S, tl[i].1, vl[i], ncap, nlook, nquant)
  }

  ghost predicate LookNestRepBTop(re: R.regex, S: set<LG.GroupId>,
                                  tl: seq<(LT.Tree, LG.GroupMap)>,
                                  bl: seq<(AI.Thread, RC.char_expectation)>) {
    |tl| == |bl| && forall i | 0 <= i < |tl| :: LookNestOkTTop(re, S, tl[i].1, bl[i].0)
  }

  ghost predicate LookNestBackRepBTop(re: R.regex, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
                                      S: set<LG.GroupId>, tl: seq<(LT.Tree, LG.GroupMap)>,
                                      bl: seq<(AI.Thread, RC.char_expectation)>,
                                      ncap: int, nlook: int, nquant: int) {
    |tl| == |bl|
    && forall i | 0 <= i < |tl| ::
      LookNestBackTTop(re, crv, str, ov, S, tl[i].1, bl[i].0, ncap, nlook, nquant)
  }

  /** Converse effect — REGISTER-INERT steps (SetReg and every stutter): the
      look and quant banks are untouched and the gm only grows. */
  lemma LookNestBackTRegSame(re: R.regex, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
                             S: set<LG.GroupId>, gmt: LG.GroupMap, gmt': LG.GroupMap,
                             th: AI.Thread, th': AI.Thread,
                             ncap: int, nlook: int, nquant: int)
    requires LookNestBackT(re, crv, str, ov, S, gmt, th, ncap, nlook, nquant)
    requires th'.look_regs == th.look_regs && th'.quant_regs == th.quant_regs
    requires forall g: LG.GroupId :: g in gmt ==> g in gmt'
    ensures LookNestBackT(re, crv, str, ov, S, gmt', th', ncap, nlook, nquant)
  {
  }

  /** Converse effect — QUANT RE-STAMP: on-path lids lose dominance outright
      (the fresh stamp beats their look stamp); off-path lids keep dominance
      by congruence and their groups survive the Reset by scope disjointness. */
  lemma LookNestBackTSetQuant(re: R.regex, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
                              S: set<LG.GroupId>, gmt: LG.GroupMap, gmt': LG.GroupMap,
                              th: AI.Thread, th': AI.Thread, qn: nat,
                              ncap: int, nlook: int, nquant: int)
    requires NR.LookBehindFragmentRE(re) && PIV.CapUnique(re) && PIV.QuantUnique(re)
    requires LTB.LookUnique(re)
    requires LookNestBackT(re, crv, str, ov, S, gmt, th, ncap, nlook, nquant)
    requires qn in PIV.QuantIds(re) && qn in PIV.QuantIdsOutsideLooks(re)
    requires th'.look_regs == th.look_regs
    requires forall j: int :: j != qn as int ==>
                                AI.get_idx(th'.quant_regs.a_clk, j) == AI.get_idx(th.quant_regs.a_clk, j)
    // the fresh stamp beats every stored look stamp
    requires forall j: int ::
               AI.get_idx(th.look_regs.a_clk, j) < AI.get_idx(th'.quant_regs.a_clk, qn as int)
    // the Reset removes only qn's scope
    requires forall g: LG.GroupId :: g in gmt && g !in PIV.CapIds(PIV.QidBody(re, qn)) ==> g in gmt'
    ensures LookNestBackT(re, crv, str, ov, S, gmt', th', ncap, nlook, nquant)
  {
    forall lid: nat | lid in LTB.LookIds(re)
                      && M.MatchedPosLA(crv, th'.look_regs, lid as int)
                      && NI.LookPathDom(re, AI.get_idx(th'.look_regs.a_clk, lid as int), th'.quant_regs.a_clk, lid)
      ensures var rf := M.FreshBodyMatch(crv, str, lid as int, th'.look_regs, ov, ncap, nlook, nquant);
              rf.Some? ==>
                forall g: LG.GroupId ::
                  g in S && g in PIV.CapIds(NI.LookBodyOfRE(re, lid))
                  && g in PIV.GmOfLive(NI.LookBodyOfRE(re, lid), rf.value.capture_regs,
                                       rf.value.look_regs, rf.value.quant_regs)
                  ==> g in gmt'
    {
      var L := AI.get_idx(th.look_regs.a_clk, lid as int);
      if lid in LTB.LookIds(PIV.QidBody(re, qn)) {
        // ON path: the fresh stamp broke dominance — hypothesis impossible.
        assert AI.get_idx(th'.quant_regs.a_clk, qn as int) > L;
        NI.LookPathDomOnPathBreaks(re, L, th'.quant_regs.a_clk, lid, qn);
        assert false;
      } else {
        NI.LookPathDomQuantOffPath(re, L, th.quant_regs.a_clk, th'.quant_regs.a_clk, lid, qn);
        assert NI.LookPathDom(re, L, th.quant_regs.a_clk, lid);
        NI.LookBodyQidBodyDisjoint(re, qn, lid);
        var rf := M.FreshBodyMatch(crv, str, lid as int, th'.look_regs, ov, ncap, nlook, nquant);
        forall g: LG.GroupId |
          rf.Some? && g in S && g in PIV.CapIds(NI.LookBodyOfRE(re, lid))
          && g in PIV.GmOfLive(NI.LookBodyOfRE(re, lid), rf.value.capture_regs,
                               rf.value.look_regs, rf.value.quant_regs)
          ensures g in gmt'
        {
          assert g in gmt;
          assert g !in PIV.CapIds(PIV.QidBody(re, qn)) by {
            if g in PIV.CapIds(PIV.QidBody(re, qn)) {
              assert g in PIV.CapIds(NI.LookBodyOfRE(re, lid)) * PIV.CapIds(PIV.QidBody(re, qn));
            }
          }
        }
      }
    }
  }

  /** (L4 NESTED) clone of `LookNestBackTSetQuant` under `NestedFragmentRE`: the
      on-path dominance-break appeals to the nested `LookPathDomOnPathBreaksNested`
      (its lookaround case recurses into the body). Body otherwise verbatim. */
  lemma LookNestBackTSetQuantNested(re: R.regex, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
                                    S: set<LG.GroupId>, gmt: LG.GroupMap, gmt': LG.GroupMap,
                                    th: AI.Thread, th': AI.Thread, qn: nat,
                                    ncap: int, nlook: int, nquant: int)
    requires NR.NestedFragmentRE(re) && PIV.CapUnique(re) && PIV.QuantUnique(re)
    requires LTB.LookUnique(re)
    requires LookNestBackT(re, crv, str, ov, S, gmt, th, ncap, nlook, nquant)
    requires qn in PIV.QuantIds(re) && qn in PIV.QuantIdsOutsideLooks(re)
    requires th'.look_regs == th.look_regs
    requires forall j: int :: j != qn as int ==>
                                AI.get_idx(th'.quant_regs.a_clk, j) == AI.get_idx(th.quant_regs.a_clk, j)
    // the fresh stamp beats every stored look stamp
    requires forall j: int ::
               AI.get_idx(th.look_regs.a_clk, j) < AI.get_idx(th'.quant_regs.a_clk, qn as int)
    // the Reset removes only qn's scope
    requires forall g: LG.GroupId :: g in gmt && g !in PIV.CapIds(PIV.QidBody(re, qn)) ==> g in gmt'
    ensures LookNestBackT(re, crv, str, ov, S, gmt', th', ncap, nlook, nquant)
  {
    forall lid: nat | lid in LTB.LookIds(re)
                      && M.MatchedPosLA(crv, th'.look_regs, lid as int)
                      && NI.LookPathDom(re, AI.get_idx(th'.look_regs.a_clk, lid as int), th'.quant_regs.a_clk, lid)
      ensures var rf := M.FreshBodyMatch(crv, str, lid as int, th'.look_regs, ov, ncap, nlook, nquant);
              rf.Some? ==>
                forall g: LG.GroupId ::
                  g in S && g in PIV.CapIds(NI.LookBodyOfRE(re, lid))
                  && g in PIV.GmOfLive(NI.LookBodyOfRE(re, lid), rf.value.capture_regs,
                                       rf.value.look_regs, rf.value.quant_regs)
                  ==> g in gmt'
    {
      var L := AI.get_idx(th.look_regs.a_clk, lid as int);
      if lid in LTB.LookIds(PIV.QidBody(re, qn)) {
        // ON path: the fresh stamp broke dominance — hypothesis impossible.
        assert AI.get_idx(th'.quant_regs.a_clk, qn as int) > L;
        NI.LookPathDomOnPathBreaksNested(re, L, th'.quant_regs.a_clk, lid, qn);
        assert false;
      } else {
        NI.LookPathDomQuantOffPath(re, L, th.quant_regs.a_clk, th'.quant_regs.a_clk, lid, qn);
        assert NI.LookPathDom(re, L, th.quant_regs.a_clk, lid);
        NI.LookBodyQidBodyDisjoint(re, qn, lid);
        var rf := M.FreshBodyMatch(crv, str, lid as int, th'.look_regs, ov, ncap, nlook, nquant);
        forall g: LG.GroupId |
          rf.Some? && g in S && g in PIV.CapIds(NI.LookBodyOfRE(re, lid))
          && g in PIV.GmOfLive(NI.LookBodyOfRE(re, lid), rf.value.capture_regs,
                               rf.value.look_regs, rf.value.quant_regs)
          ensures g in gmt'
        {
          assert g in gmt;
          assert g !in PIV.CapIds(PIV.QidBody(re, qn)) by {
            if g in PIV.CapIds(PIV.QidBody(re, qn)) {
              assert g in PIV.CapIds(NI.LookBodyOfRE(re, lid)) * PIV.CapIds(PIV.QidBody(re, qn));
            }
          }
        }
      }
    }
  }

  /** Converse effect — GATE PASS at `l0`: the crossing's own coverage is the
      caller's (from the replay↔spec agreement); every other lid keeps its
      stamp, dominance, fresh match, and old witnesses. */
  lemma LookNestBackTGatePass(re: R.regex, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
                              S: set<LG.GroupId>, gmt: LG.GroupMap, gmt': LG.GroupMap,
                              th: AI.Thread, th': AI.Thread, l0: int,
                              ncap: int, nlook: int, nquant: int)
    requires LookNestBackT(re, crv, str, ov, S, gmt, th, ncap, nlook, nquant)
    requires th'.quant_regs == th.quant_regs
    requires forall j: int :: j != l0 ==>
                                AI.get_idx(th'.look_regs.a_clk, j) == AI.get_idx(th.look_regs.a_clk, j)
                                && AI.get_idx(th'.look_regs.a_cp, j) == AI.get_idx(th.look_regs.a_cp, j)
    requires forall g: LG.GroupId :: g in gmt ==> g in gmt'
    // the crossing coverage for l0 itself, paid by the gate case
    requires l0 >= 0 && (l0 as nat) in LTB.LookIds(re) ==>
               var rf := M.FreshBodyMatch(crv, str, l0, th'.look_regs, ov, ncap, nlook, nquant);
               rf.Some? ==>
                 forall g: LG.GroupId ::
                   g in S && g in PIV.CapIds(NI.LookBodyOfRE(re, l0 as nat))
                   && g in PIV.GmOfLive(NI.LookBodyOfRE(re, l0 as nat), rf.value.capture_regs,
                                        rf.value.look_regs, rf.value.quant_regs)
                   ==> g in gmt'
    ensures LookNestBackT(re, crv, str, ov, S, gmt', th', ncap, nlook, nquant)
  {
    forall lid: nat | lid in LTB.LookIds(re)
                      && M.MatchedPosLA(crv, th'.look_regs, lid as int)
                      && NI.LookPathDom(re, AI.get_idx(th'.look_regs.a_clk, lid as int), th'.quant_regs.a_clk, lid)
      ensures var rf := M.FreshBodyMatch(crv, str, lid as int, th'.look_regs, ov, ncap, nlook, nquant);
              rf.Some? ==>
                forall g: LG.GroupId ::
                  g in S && g in PIV.CapIds(NI.LookBodyOfRE(re, lid))
                  && g in PIV.GmOfLive(NI.LookBodyOfRE(re, lid), rf.value.capture_regs,
                                       rf.value.look_regs, rf.value.quant_regs)
                  ==> g in gmt'
    {
      if lid as int == l0 {
        // covered by the caller's crossing coverage
      } else {
        // untouched lid: same cp (so MatchedPosLA and the SAME fresh match),
        // same stamp, same quant bank ⟹ old hypothesis + old conclusion.
        assert AI.get_idx(th'.look_regs.a_clk, lid as int) == AI.get_idx(th.look_regs.a_clk, lid as int);
        assert M.MatchedPosLA(crv, th.look_regs, lid as int) by {
          assert AReg.get_cp(th'.look_regs, lid as int) == AReg.get_cp(th.look_regs, lid as int);
        }
        assert M.FreshBodyMatch(crv, str, lid as int, th'.look_regs, ov, ncap, nlook, nquant)
            == M.FreshBodyMatch(crv, str, lid as int, th.look_regs, ov, ncap, nlook, nquant) by {
          assert AReg.get_cp(th'.look_regs, lid as int) == AReg.get_cp(th.look_regs, lid as int);
        }
      }
    }
  }

  /** Carrier effect — FRESH CAPTURE STAMP (the SetReg case): the look and
      quant banks are untouched, every capture-clock slot either keeps its
      value or takes a stamp `>= B` beating every stored quant clock, and the
      gm gains no inside-S group. */
  lemma LookNestOkTFreshCap(re: R.regex, S: set<LG.GroupId>, gmt: LG.GroupMap, gmt': LG.GroupMap,
                            th: AI.Thread, th': AI.Thread, B: int)
    requires LookNestOkT(re, S, gmt, th)
    requires th'.look_regs == th.look_regs && th'.quant_regs == th.quant_regs
    requires -1 <= B
    requires forall k :: AI.get_idx(th.quant_regs.a_clk, k) <= B
    requires forall j: int ::
               AI.get_idx(th'.capture_regs.a_clk, j) == AI.get_idx(th.capture_regs.a_clk, j)
               || (AI.get_idx(th'.capture_regs.a_clk, j) >= 0 && AI.get_idx(th'.capture_regs.a_clk, j) >= B)
    requires forall g: LG.GroupId :: g in S && g in gmt' ==> g in gmt
    ensures LookNestOkT(re, S, gmt', th')
  {
    forall lid: nat | lid in LTB.LookIds(re)
                      && (exists g: LG.GroupId :: g in S && g in gmt' && g in PIV.CapIds(NI.LookBodyOfRE(re, lid)))
      ensures NI.LookPathPresent(re, th'.capture_regs.a_clk, th'.quant_regs.a_clk, -1, lid)
              && AI.get_idx(th'.look_regs.a_clk, lid as int) >= 0
              && AI.get_idx(th'.look_regs.a_clk, lid as int)
                 >= NI.MxAtLidLk(re, th'.quant_regs.a_clk, -1, lid)
    {
      var g: LG.GroupId :| g in S && g in gmt' && g in PIV.CapIds(NI.LookBodyOfRE(re, lid));
      assert g in gmt;
      NI.LookPathPresentFreshCap(re, th.capture_regs.a_clk, th'.capture_regs.a_clk,
                                 th.quant_regs.a_clk, -1, lid, B);
    }
  }

  /** Carrier effect — QUANT RE-STAMP (the SetQuantToClock case): the B-side
      `Reset` clears `qid`'s whole reset scope from the gm, so lids INSIDE
      `qid`'s body are vacated (`NI.LookBodyCapsUnderQid`); for lids OUTSIDE,
      `qid` is off their path and the re-stamp is invisible
      (`NI.LookPathPresentQuantOffPath`). */
  lemma LookNestOkTSetQuant(re: R.regex, S: set<LG.GroupId>, gmt: LG.GroupMap, gmt': LG.GroupMap,
                            th: AI.Thread, th': AI.Thread, qid: nat)
    requires PIV.QuantUnique(re) && LTB.LookUnique(re)
    requires LookNestOkT(re, S, gmt, th)
    requires qid in PIV.QuantIds(re)
    requires th'.capture_regs == th.capture_regs && th'.look_regs == th.look_regs
    requires forall j: int :: j != qid as int ==>
                                AI.get_idx(th'.quant_regs.a_clk, j) == AI.get_idx(th.quant_regs.a_clk, j)
    requires forall g: nat :: g in PIV.CapIds(PIV.QidBody(re, qid)) ==> g !in gmt'
    requires forall g: LG.GroupId :: g in gmt' ==> g in gmt
    ensures LookNestOkT(re, S, gmt', th')
  {
    forall lid: nat | lid in LTB.LookIds(re)
                      && (exists g: LG.GroupId :: g in S && g in gmt' && g in PIV.CapIds(NI.LookBodyOfRE(re, lid)))
      ensures NI.LookPathPresent(re, th'.capture_regs.a_clk, th'.quant_regs.a_clk, -1, lid)
              && AI.get_idx(th'.look_regs.a_clk, lid as int) >= 0
              && AI.get_idx(th'.look_regs.a_clk, lid as int)
                 >= NI.MxAtLidLk(re, th'.quant_regs.a_clk, -1, lid)
    {
      var g: LG.GroupId :| g in S && g in gmt' && g in PIV.CapIds(NI.LookBodyOfRE(re, lid));
      if lid in LTB.LookIds(PIV.QidBody(re, qid)) {
        // ON path: Reset removed lid's whole ownership — no witness survives.
        NI.LookBodyCapsUnderQid(re, qid, lid);
        assert g in PIV.CapIds(PIV.QidBody(re, qid));
        assert false;
      } else {
        assert g in gmt;
        NI.LookPathPresentQuantOffPath(re, th.capture_regs.a_clk, th.quant_regs.a_clk,
                                       th'.quant_regs.a_clk, -1, lid, qid);
      }
    }
  }

  /** Carrier effect — GATE PASS (the CheckOracle case): the crossing thread's
      positional invariant plus the FRESH look stamp establish the fact for
      `lid0` outright (`NI.GateCrossLookNest`); groups folded in are owned by
      `lid0` alone, so other lids keep their old witnesses and unchanged
      registers (`NI.LookBodiesCapsDisjoint` kills cross-ownership). */
  lemma LookNestOkTGatePass(re: R.regex, code: RB.code, endl: nat, S: set<LG.GroupId>,
                            gmt: LG.GroupMap, gmt': LG.GroupMap,
                            th: AI.Thread, th': AI.Thread, pc: nat, lid0: int)
    requires NR.NfaRepRE(re, code, 0, endl)
    requires NR.LookBehindFragmentRE(re) && LTB.LookUnique(re) && PIV.CapUnique(re)
    requires LookNestOkT(re, S, gmt, th)
    requires pc < endl && NR.GetPcRE(code, pc) == Some(RB.CheckOracle(lid0))
    requires NI.NestInvRE(re, code, 0, endl, pc, th.capture_regs.a_clk, th.quant_regs.a_clk, -1)
    requires th'.capture_regs == th.capture_regs && th'.quant_regs == th.quant_regs
    requires forall j: int :: j != lid0 ==>
                                AI.get_idx(th'.look_regs.a_clk, j) == AI.get_idx(th.look_regs.a_clk, j)
    requires AI.get_idx(th'.look_regs.a_clk, lid0) >= 0
    requires forall k :: AI.get_idx(th.quant_regs.a_clk, k) <= AI.get_idx(th'.look_regs.a_clk, lid0)
    requires forall g: LG.GroupId :: g in S && g in gmt' && g !in gmt ==>
                                       lid0 >= 0 && (lid0 as nat) in LTB.LookIds(re)
                                       && g in PIV.CapIds(NI.LookBodyOfRE(re, lid0 as nat))
    ensures LookNestOkT(re, S, gmt', th')
  {
    NI.GateCrossLookNest(re, code, endl, pc, th.capture_regs.a_clk, th.quant_regs.a_clk,
                         th'.look_regs.a_clk, lid0);
    forall lid: nat | lid in LTB.LookIds(re)
                      && (exists g: LG.GroupId :: g in S && g in gmt' && g in PIV.CapIds(NI.LookBodyOfRE(re, lid)))
      ensures NI.LookPathPresent(re, th'.capture_regs.a_clk, th'.quant_regs.a_clk, -1, lid)
              && AI.get_idx(th'.look_regs.a_clk, lid as int) >= 0
              && AI.get_idx(th'.look_regs.a_clk, lid as int)
                 >= NI.MxAtLidLk(re, th'.quant_regs.a_clk, -1, lid)
    {
      var g: LG.GroupId :| g in S && g in gmt' && g in PIV.CapIds(NI.LookBodyOfRE(re, lid));
      if lid == lid0 as nat {
        // established fresh at the crossing (caps/quant banks unchanged)
      } else {
        if g in gmt {
          assert AI.get_idx(th'.look_regs.a_clk, lid as int)
              == AI.get_idx(th.look_regs.a_clk, lid as int) by {
            assert lid as int != lid0;
          }
        } else {
          assert g in PIV.CapIds(NI.LookBodyOfRE(re, lid0 as nat));
          NI.LookBodiesCapsDisjoint(re, lid, lid0 as nat);
          assert g in PIV.CapIds(NI.LookBodyOfRE(re, lid))
                      * PIV.CapIds(NI.LookBodyOfRE(re, lid0 as nat));
          assert false;
        }
      }
    }
  }

  /** (L4 NESTED) `LookNestOkTGatePass` under `NestedFragmentRE`. Two rewires
      versus the depth-1 form:
        (i)  `NI.GateCrossLookNest` → `NI.GateCrossLookNestNested` (the gate-site
             extraction under the full nested fragment; a pure fragment swap);
        (ii) `NI.LookBodiesCapsDisjoint` (FALSE at depth ≥ 2) → the trichotomy
             `NI.LookBodiesCapsDisjointOrNested`, whose "one nests the other"
             arms are BOTH ruled out for a FRESH fold:

      The fold-ownership hypothesis is STRENGTHENED to DIRECT ownership — a
      freshly-folded `g` sits DIRECTLY in `lid0`'s body, `g !in
      CapIdsInLooks(body(lid0))` (at a top-level gate the endpoint folds only
      `lid0`'s direct groups; inner-look groups are closed post-hoc). Then for
      `lid != lid0` with `g` fresh and `g in CapIds(body(lid))`:
        · disjoint arm  → `g` in an empty intersection, contradiction;
        · `lid` nested in `lid0` → `LookBodyCompose`+`LookBodyCapsIn` put `g` in
          `CapIdsInLooks(body(lid0))`, contradicting DIRECT;
        · `lid0` nested in `lid` → IMPOSSIBLE: `lid0`'s `CheckOracle` is in the
          MAIN code, so `lid0` is TOP-LEVEL (`NI.LookSiteTopNested`), hence sits
          in no look body (`NI.TopLookNotNested`), contradicting the arm.
      So a cross-lid fresh fold is vacuous exactly as at depth 1; only the
      argument that kills it changed. */
  lemma LookNestOkTGatePassNested(re: R.regex, code: RB.code, endl: nat, S: set<LG.GroupId>,
                                  gmt: LG.GroupMap, gmt': LG.GroupMap,
                                  th: AI.Thread, th': AI.Thread, pc: nat, lid0: int)
    requires NR.NfaRepRE(re, code, 0, endl)
    requires NR.NestedFragmentRE(re) && LTB.LookUnique(re) && PIV.CapUnique(re)
    requires LookNestOkT(re, S, gmt, th)
    requires pc < endl && NR.GetPcRE(code, pc) == Some(RB.CheckOracle(lid0))
    requires NI.NestInvRE(re, code, 0, endl, pc, th.capture_regs.a_clk, th.quant_regs.a_clk, -1)
    requires th'.capture_regs == th.capture_regs && th'.quant_regs == th.quant_regs
    requires forall j: int :: j != lid0 ==>
                                AI.get_idx(th'.look_regs.a_clk, j) == AI.get_idx(th.look_regs.a_clk, j)
    requires AI.get_idx(th'.look_regs.a_clk, lid0) >= 0
    requires forall k :: AI.get_idx(th.quant_regs.a_clk, k) <= AI.get_idx(th'.look_regs.a_clk, lid0)
    // DIRECT ownership: a fresh fold sits directly in lid0's body, not buried in
    // a nested look (the endpoint's top-level-gate fold; inner groups post-hoc).
    requires forall g: LG.GroupId :: g in S && g in gmt' && g !in gmt ==>
                                       lid0 >= 0 && (lid0 as nat) in LTB.LookIds(re)
                                       && g in PIV.CapIds(NI.LookBodyOfRE(re, lid0 as nat))
                                       && g !in PIV.CapIdsInLooks(NI.LookBodyOfRE(re, lid0 as nat))
    ensures LookNestOkT(re, S, gmt', th')
  {
    NI.GateCrossLookNestNested(re, code, endl, pc, th.capture_regs.a_clk, th.quant_regs.a_clk,
                               th'.look_regs.a_clk, lid0);
    // lid0's CheckOracle is in the MAIN code ⟹ lid0 is a TOP-LEVEL look.
    NI.LookSiteTopNested(re, code, 0, endl, pc);
    assert lid0 >= 0 && (lid0 as nat) in NI.TopLookIds(re);
    forall lid: nat | lid in LTB.LookIds(re)
                      && (exists g: LG.GroupId :: g in S && g in gmt' && g in PIV.CapIds(NI.LookBodyOfRE(re, lid)))
      ensures NI.LookPathPresent(re, th'.capture_regs.a_clk, th'.quant_regs.a_clk, -1, lid)
              && AI.get_idx(th'.look_regs.a_clk, lid as int) >= 0
              && AI.get_idx(th'.look_regs.a_clk, lid as int)
                 >= NI.MxAtLidLk(re, th'.quant_regs.a_clk, -1, lid)
    {
      var g: LG.GroupId :| g in S && g in gmt' && g in PIV.CapIds(NI.LookBodyOfRE(re, lid));
      if lid == lid0 as nat {
        // established fresh at the crossing (caps/quant banks unchanged)
      } else {
        if g in gmt {
          assert AI.get_idx(th'.look_regs.a_clk, lid as int)
              == AI.get_idx(th.look_regs.a_clk, lid as int) by {
            assert lid as int != lid0;
          }
        } else {
          // FRESH fold: g is DIRECT in lid0's body.
          assert g in PIV.CapIds(NI.LookBodyOfRE(re, lid0 as nat));
          assert g !in PIV.CapIdsInLooks(NI.LookBodyOfRE(re, lid0 as nat));
          NI.LookBodiesCapsDisjointOrNested(re, lid, lid0 as nat);
          if PIV.CapIds(NI.LookBodyOfRE(re, lid)) * PIV.CapIds(NI.LookBodyOfRE(re, lid0 as nat)) == {} {
            assert g in PIV.CapIds(NI.LookBodyOfRE(re, lid))
                        * PIV.CapIds(NI.LookBodyOfRE(re, lid0 as nat));
            assert false;
          } else if lid0 as nat in LTB.LookIds(NI.LookBodyOfRE(re, lid))
                    && PIV.CapIds(NI.LookBodyOfRE(re, lid0 as nat))
                       <= PIV.CapIds(NI.LookBodyOfRE(re, lid)) {
            // lid0 nested in lid — impossible: lid0 is top-level.
            NI.TopLookNotNested(re, lid0 as nat, lid);
            assert lid0 as nat !in LTB.LookIds(NI.LookBodyOfRE(re, lid));
            assert false;
          } else {
            // lid nested in lid0 — g would then be in CapIdsInLooks(body(lid0)).
            assert lid in LTB.LookIds(NI.LookBodyOfRE(re, lid0 as nat));
            NI.LookBodyCompose(re, lid0 as nat, lid);
            assert NI.LookBodyOfRE(re, lid)
                == NI.LookBodyOfRE(NI.LookBodyOfRE(re, lid0 as nat), lid);
            NI.LookBodyCapsIn(NI.LookBodyOfRE(re, lid0 as nat), lid);
            assert g in PIV.CapIdsInLooks(NI.LookBodyOfRE(re, lid0 as nat));
            assert false;
          }
        }
      }
    }
  }

  // ==========================================================================
  // (D3) TOP-LEVEL carrier EFFECT lemmas. Each is the `*Top`-carrier sibling of
  // the corresponding full-carrier effect lemma: the quantifier iterates
  // `NI.TopLookIds(re)` (via `NI.TopLookIdsIn` for the `lid in LookIds` facts the
  // inner navigation needs), the requires/ensures carriers are the `*Top`
  // variants. For every step but the gate-pass the argument is verbatim — a
  // strict weakening. At the gate pass the DIRECT-ownership hypothesis is DROPPED
  // (inner-look folds no longer create obligations) and a cross-lid fresh fold is
  // killed by TOP-LEVEL disjointness (`NI.TopLookNotNested` rules out BOTH nesting
  // arms, since lid and lid0 are both top-level).
  // ==========================================================================

  lemma LookNestBackTRegSameTop(re: R.regex, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
                                S: set<LG.GroupId>, gmt: LG.GroupMap, gmt': LG.GroupMap,
                                th: AI.Thread, th': AI.Thread,
                                ncap: int, nlook: int, nquant: int)
    requires LookNestBackTTop(re, crv, str, ov, S, gmt, th, ncap, nlook, nquant)
    requires th'.look_regs == th.look_regs && th'.quant_regs == th.quant_regs
    requires forall g: LG.GroupId :: g in gmt ==> g in gmt'
    ensures LookNestBackTTop(re, crv, str, ov, S, gmt', th', ncap, nlook, nquant)
  {
  }

  lemma LookNestOkTFreshCapTop(re: R.regex, S: set<LG.GroupId>, gmt: LG.GroupMap, gmt': LG.GroupMap,
                               th: AI.Thread, th': AI.Thread, B: int)
    requires LookNestOkTTop(re, S, gmt, th)
    requires th'.look_regs == th.look_regs && th'.quant_regs == th.quant_regs
    requires -1 <= B
    requires forall k :: AI.get_idx(th.quant_regs.a_clk, k) <= B
    requires forall j: int ::
               AI.get_idx(th'.capture_regs.a_clk, j) == AI.get_idx(th.capture_regs.a_clk, j)
               || (AI.get_idx(th'.capture_regs.a_clk, j) >= 0 && AI.get_idx(th'.capture_regs.a_clk, j) >= B)
    requires forall g: LG.GroupId :: g in S && g in gmt' ==> g in gmt
    ensures LookNestOkTTop(re, S, gmt', th')
  {
    NI.TopLookIdsIn(re);
    forall lid: nat | lid in NI.TopLookIds(re)
                      && (exists g: LG.GroupId :: g in S && g in gmt' && g in PIV.CapIds(NI.LookBodyOfRE(re, lid)))
      ensures NI.LookPathPresent(re, th'.capture_regs.a_clk, th'.quant_regs.a_clk, -1, lid)
              && AI.get_idx(th'.look_regs.a_clk, lid as int) >= 0
              && AI.get_idx(th'.look_regs.a_clk, lid as int)
                 >= NI.MxAtLidLk(re, th'.quant_regs.a_clk, -1, lid)
    {
      var g: LG.GroupId :| g in S && g in gmt' && g in PIV.CapIds(NI.LookBodyOfRE(re, lid));
      assert g in gmt;
      NI.LookPathPresentFreshCap(re, th.capture_regs.a_clk, th'.capture_regs.a_clk,
                                 th.quant_regs.a_clk, -1, lid, B);
    }
  }

  lemma LookNestOkTSetQuantTop(re: R.regex, S: set<LG.GroupId>, gmt: LG.GroupMap, gmt': LG.GroupMap,
                               th: AI.Thread, th': AI.Thread, qid: nat)
    requires PIV.QuantUnique(re) && LTB.LookUnique(re)
    requires LookNestOkTTop(re, S, gmt, th)
    requires qid in PIV.QuantIds(re)
    requires th'.capture_regs == th.capture_regs && th'.look_regs == th.look_regs
    requires forall j: int :: j != qid as int ==>
                                AI.get_idx(th'.quant_regs.a_clk, j) == AI.get_idx(th.quant_regs.a_clk, j)
    requires forall g: nat :: g in PIV.CapIds(PIV.QidBody(re, qid)) ==> g !in gmt'
    requires forall g: LG.GroupId :: g in gmt' ==> g in gmt
    ensures LookNestOkTTop(re, S, gmt', th')
  {
    NI.TopLookIdsIn(re);
    forall lid: nat | lid in NI.TopLookIds(re)
                      && (exists g: LG.GroupId :: g in S && g in gmt' && g in PIV.CapIds(NI.LookBodyOfRE(re, lid)))
      ensures NI.LookPathPresent(re, th'.capture_regs.a_clk, th'.quant_regs.a_clk, -1, lid)
              && AI.get_idx(th'.look_regs.a_clk, lid as int) >= 0
              && AI.get_idx(th'.look_regs.a_clk, lid as int)
                 >= NI.MxAtLidLk(re, th'.quant_regs.a_clk, -1, lid)
    {
      var g: LG.GroupId :| g in S && g in gmt' && g in PIV.CapIds(NI.LookBodyOfRE(re, lid));
      if lid in LTB.LookIds(PIV.QidBody(re, qid)) {
        NI.LookBodyCapsUnderQid(re, qid, lid);
        assert g in PIV.CapIds(PIV.QidBody(re, qid));
        assert false;
      } else {
        assert g in gmt;
        NI.LookPathPresentQuantOffPath(re, th.capture_regs.a_clk, th.quant_regs.a_clk,
                                       th'.quant_regs.a_clk, -1, lid, qid);
      }
    }
  }

  lemma LookNestBackTSetQuantNestedTop(re: R.regex, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
                                       S: set<LG.GroupId>, gmt: LG.GroupMap, gmt': LG.GroupMap,
                                       th: AI.Thread, th': AI.Thread, qn: nat,
                                       ncap: int, nlook: int, nquant: int)
    requires NR.NestedFragmentRE(re) && PIV.CapUnique(re) && PIV.QuantUnique(re)
    requires LTB.LookUnique(re)
    requires LookNestBackTTop(re, crv, str, ov, S, gmt, th, ncap, nlook, nquant)
    requires qn in PIV.QuantIds(re) && qn in PIV.QuantIdsOutsideLooks(re)
    requires th'.look_regs == th.look_regs
    requires forall j: int :: j != qn as int ==>
                                AI.get_idx(th'.quant_regs.a_clk, j) == AI.get_idx(th.quant_regs.a_clk, j)
    requires forall j: int ::
               AI.get_idx(th.look_regs.a_clk, j) < AI.get_idx(th'.quant_regs.a_clk, qn as int)
    requires forall g: LG.GroupId :: g in gmt && g !in PIV.CapIds(PIV.QidBody(re, qn)) ==> g in gmt'
    ensures LookNestBackTTop(re, crv, str, ov, S, gmt', th', ncap, nlook, nquant)
  {
    NI.TopLookIdsIn(re);
    forall lid: nat | lid in NI.TopLookIds(re)
                      && M.MatchedPosLA(crv, th'.look_regs, lid as int)
                      && NI.LookPathDom(re, AI.get_idx(th'.look_regs.a_clk, lid as int), th'.quant_regs.a_clk, lid)
      ensures var rf := M.FreshBodyMatch(crv, str, lid as int, th'.look_regs, ov, ncap, nlook, nquant);
              rf.Some? ==>
                forall g: LG.GroupId ::
                  g in S && g in PIV.CapIds(NI.LookBodyOfRE(re, lid))
                  && g in PIV.GmOfLive(NI.LookBodyOfRE(re, lid), rf.value.capture_regs,
                                       rf.value.look_regs, rf.value.quant_regs)
                  ==> g in gmt'
    {
      var L := AI.get_idx(th.look_regs.a_clk, lid as int);
      if lid in LTB.LookIds(PIV.QidBody(re, qn)) {
        assert AI.get_idx(th'.quant_regs.a_clk, qn as int) > L;
        NI.LookPathDomOnPathBreaksNested(re, L, th'.quant_regs.a_clk, lid, qn);
        assert false;
      } else {
        NI.LookPathDomQuantOffPath(re, L, th.quant_regs.a_clk, th'.quant_regs.a_clk, lid, qn);
        assert NI.LookPathDom(re, L, th.quant_regs.a_clk, lid);
        NI.LookBodyQidBodyDisjoint(re, qn, lid);
        var rf := M.FreshBodyMatch(crv, str, lid as int, th'.look_regs, ov, ncap, nlook, nquant);
        forall g: LG.GroupId |
          rf.Some? && g in S && g in PIV.CapIds(NI.LookBodyOfRE(re, lid))
          && g in PIV.GmOfLive(NI.LookBodyOfRE(re, lid), rf.value.capture_regs,
                               rf.value.look_regs, rf.value.quant_regs)
          ensures g in gmt'
        {
          assert g in gmt;
          assert g !in PIV.CapIds(PIV.QidBody(re, qn)) by {
            if g in PIV.CapIds(PIV.QidBody(re, qn)) {
              assert g in PIV.CapIds(NI.LookBodyOfRE(re, lid)) * PIV.CapIds(PIV.QidBody(re, qn));
            }
          }
        }
      }
    }
  }

  lemma LookNestBackTGatePassTop(re: R.regex, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
                                 S: set<LG.GroupId>, gmt: LG.GroupMap, gmt': LG.GroupMap,
                                 th: AI.Thread, th': AI.Thread, l0: int,
                                 ncap: int, nlook: int, nquant: int)
    requires LookNestBackTTop(re, crv, str, ov, S, gmt, th, ncap, nlook, nquant)
    requires th'.quant_regs == th.quant_regs
    requires forall j: int :: j != l0 ==>
                                AI.get_idx(th'.look_regs.a_clk, j) == AI.get_idx(th.look_regs.a_clk, j)
                                && AI.get_idx(th'.look_regs.a_cp, j) == AI.get_idx(th.look_regs.a_cp, j)
    requires forall g: LG.GroupId :: g in gmt ==> g in gmt'
    requires l0 >= 0 && (l0 as nat) in LTB.LookIds(re) ==>
               var rf := M.FreshBodyMatch(crv, str, l0, th'.look_regs, ov, ncap, nlook, nquant);
               rf.Some? ==>
                 forall g: LG.GroupId ::
                   g in S && g in PIV.CapIds(NI.LookBodyOfRE(re, l0 as nat))
                   && g in PIV.GmOfLive(NI.LookBodyOfRE(re, l0 as nat), rf.value.capture_regs,
                                        rf.value.look_regs, rf.value.quant_regs)
                   ==> g in gmt'
    ensures LookNestBackTTop(re, crv, str, ov, S, gmt', th', ncap, nlook, nquant)
  {
    NI.TopLookIdsIn(re);
    forall lid: nat | lid in NI.TopLookIds(re)
                      && M.MatchedPosLA(crv, th'.look_regs, lid as int)
                      && NI.LookPathDom(re, AI.get_idx(th'.look_regs.a_clk, lid as int), th'.quant_regs.a_clk, lid)
      ensures var rf := M.FreshBodyMatch(crv, str, lid as int, th'.look_regs, ov, ncap, nlook, nquant);
              rf.Some? ==>
                forall g: LG.GroupId ::
                  g in S && g in PIV.CapIds(NI.LookBodyOfRE(re, lid))
                  && g in PIV.GmOfLive(NI.LookBodyOfRE(re, lid), rf.value.capture_regs,
                                       rf.value.look_regs, rf.value.quant_regs)
                  ==> g in gmt'
    {
      if lid as int == l0 {
      } else {
        assert AI.get_idx(th'.look_regs.a_clk, lid as int) == AI.get_idx(th.look_regs.a_clk, lid as int);
        assert M.MatchedPosLA(crv, th.look_regs, lid as int) by {
          assert AReg.get_cp(th'.look_regs, lid as int) == AReg.get_cp(th.look_regs, lid as int);
        }
        assert M.FreshBodyMatch(crv, str, lid as int, th'.look_regs, ov, ncap, nlook, nquant)
            == M.FreshBodyMatch(crv, str, lid as int, th.look_regs, ov, ncap, nlook, nquant) by {
          assert AReg.get_cp(th'.look_regs, lid as int) == AReg.get_cp(th.look_regs, lid as int);
        }
      }
    }
  }

  /** (D3) `LookNestOkTGatePassNested` on the `*Top` carrier. The DIRECT-ownership
      hypothesis (`g !in CapIdsInLooks(body(lid0))`) is DROPPED — a fresh fold may
      land an inner-look group, but inner looks are NOT in `TopLookIds`, so they
      raise no obligation. A cross-lid fresh fold (`lid != lid0`, both top-level)
      is impossible: `NI.LookBodiesCapsDisjointOrNested`'s two nesting arms are
      BOTH ruled out by `NI.TopLookNotNested` (a top-level look sits in no look
      body), leaving disjointness that contradicts the shared `g`. */
  lemma LookNestOkTGatePassNestedTop(re: R.regex, code: RB.code, endl: nat, S: set<LG.GroupId>,
                                     gmt: LG.GroupMap, gmt': LG.GroupMap,
                                     th: AI.Thread, th': AI.Thread, pc: nat, lid0: int)
    requires NR.NfaRepRE(re, code, 0, endl)
    requires NR.NestedFragmentRE(re) && LTB.LookUnique(re) && PIV.CapUnique(re)
    requires LookNestOkTTop(re, S, gmt, th)
    requires pc < endl && NR.GetPcRE(code, pc) == Some(RB.CheckOracle(lid0))
    requires NI.NestInvRE(re, code, 0, endl, pc, th.capture_regs.a_clk, th.quant_regs.a_clk, -1)
    requires th'.capture_regs == th.capture_regs && th'.quant_regs == th.quant_regs
    requires forall j: int :: j != lid0 ==>
                                AI.get_idx(th'.look_regs.a_clk, j) == AI.get_idx(th.look_regs.a_clk, j)
    requires AI.get_idx(th'.look_regs.a_clk, lid0) >= 0
    requires forall k :: AI.get_idx(th.quant_regs.a_clk, k) <= AI.get_idx(th'.look_regs.a_clk, lid0)
    // fresh folds sit in lid0's body (nested-look groups allowed — dropped the DIRECT clause).
    requires forall g: LG.GroupId :: g in S && g in gmt' && g !in gmt ==>
                                       lid0 >= 0 && (lid0 as nat) in LTB.LookIds(re)
                                       && g in PIV.CapIds(NI.LookBodyOfRE(re, lid0 as nat))
    ensures LookNestOkTTop(re, S, gmt', th')
  {
    NI.GateCrossLookNestNested(re, code, endl, pc, th.capture_regs.a_clk, th.quant_regs.a_clk,
                               th'.look_regs.a_clk, lid0);
    NI.LookSiteTopNested(re, code, 0, endl, pc);
    assert lid0 >= 0 && (lid0 as nat) in NI.TopLookIds(re);
    NI.TopLookIdsIn(re);
    forall lid: nat | lid in NI.TopLookIds(re)
                      && (exists g: LG.GroupId :: g in S && g in gmt' && g in PIV.CapIds(NI.LookBodyOfRE(re, lid)))
      ensures NI.LookPathPresent(re, th'.capture_regs.a_clk, th'.quant_regs.a_clk, -1, lid)
              && AI.get_idx(th'.look_regs.a_clk, lid as int) >= 0
              && AI.get_idx(th'.look_regs.a_clk, lid as int)
                 >= NI.MxAtLidLk(re, th'.quant_regs.a_clk, -1, lid)
    {
      var g: LG.GroupId :| g in S && g in gmt' && g in PIV.CapIds(NI.LookBodyOfRE(re, lid));
      if lid == lid0 as nat {
        // established fresh at the crossing (caps/quant banks unchanged)
      } else {
        if g in gmt {
          assert AI.get_idx(th'.look_regs.a_clk, lid as int)
              == AI.get_idx(th.look_regs.a_clk, lid as int) by {
            assert lid as int != lid0;
          }
        } else {
          // FRESH cross-lid fold: g in body(lid0) AND g in body(lid), lid != lid0
          // both TOP-LEVEL — impossible.
          assert g in PIV.CapIds(NI.LookBodyOfRE(re, lid0 as nat));
          NI.LookBodiesCapsDisjointOrNested(re, lid, lid0 as nat);
          if PIV.CapIds(NI.LookBodyOfRE(re, lid)) * PIV.CapIds(NI.LookBodyOfRE(re, lid0 as nat)) == {} {
            assert g in PIV.CapIds(NI.LookBodyOfRE(re, lid))
                        * PIV.CapIds(NI.LookBodyOfRE(re, lid0 as nat));
            assert false;
          } else if lid0 as nat in LTB.LookIds(NI.LookBodyOfRE(re, lid))
                    && PIV.CapIds(NI.LookBodyOfRE(re, lid0 as nat))
                       <= PIV.CapIds(NI.LookBodyOfRE(re, lid)) {
            // lid0 nested in lid — impossible: lid0 is top-level.
            NI.TopLookNotNested(re, lid0 as nat, lid);
            assert lid0 as nat !in LTB.LookIds(NI.LookBodyOfRE(re, lid));
            assert false;
          } else {
            // lid nested in lid0 — impossible: lid is ALSO top-level.
            assert lid in LTB.LookIds(NI.LookBodyOfRE(re, lid0 as nat));
            NI.TopLookNotNested(re, lid, lid0 as nat);
            assert lid !in LTB.LookIds(NI.LookBodyOfRE(re, lid0 as nat));
            assert false;
          }
        }
      }
    }
  }

  lemma WinningGmtTieOutside(re: R.regex, th: AI.Thread, leafgm: LG.GroupMap,
                             ftstar: LG.GroupMap, S: set<LG.GroupId>)
    requires ftstar == PIV.GmOfLive(re, th.capture_regs, th.look_regs, th.quant_regs)
    requires LL.GmAgreeOutside(ftstar, leafgm, S)
    ensures GmtTieOutside(re, th, leafgm, S)
  {
    // GmtTieOutside's internal `gml` unfolds to exactly `ftstar` (the requires).
    forall g: LG.GroupId | g !in S
      ensures (g in leafgm <==> g in ftstar) && (g in leafgm ==> leafgm[g] == ftstar[g])
    {
      // GmAgreeOutside(ftstar, leafgm, S): g in ftstar <==> g in leafgm, and
      // g in ftstar ==> ftstar[g] == leafgm[g]. The membership clause is
      // symmetric; for the value, g in leafgm ==> g in ftstar (flip) ==>
      // ftstar[g] == leafgm[g] ==> leafgm[g] == ftstar[g].
    }
  }

  /** The fresh body match at a recorded look cp is `CapRegWf` — straight from
      `M.FreshMatchWf` (`ThreadRegsWf ⟹ CapRegWf`, since `FreshBodyMatch` IS the
      `FFindMatch`-from-fresh-registers form `FreshMatchWf` covers). This is the
      thread-wf `InsidePresentResBridge` needs: clock and value are set together,
      so `BodyPathPresentLk`'s clock-set yields the value-set at `g` that
      `GmOfLiveInsideLookPresentEq` requires. The cp-validity `requires`
      (`0<=cp<=|str|`, context match) are the caller's look-table facts. */
  lemma FreshBodyMatchCapWf(crv: CP.FCompiled, str: string, l: int, lk: AReg.Regs,
                            ov: LOr.OracleView, ncap: int, nlook: int, nquant: int, body: R.regex)
    requires body == M.VBody(crv, l)
    requires NR.LookBehindFragmentRE(body) && NR.PlusFragmentRE(body)
             && PIV.CapUnique(body) && PIV.QuantUnique(body)
    requires NR.NoNulledPlusRE(body)   // §2.5b interim: all stamps false
    requires M.MatchedPosLA(crv, lk, l)   // POSITIVE look: rules out the capture-free negatives
    requires ncap >= 0 && nlook >= 0 && nquant >= 0
    requires var cp := if AReg.get_cp(lk, l).Some? then AReg.get_cp(lk, l).value else 0;
             0 <= cp <= |str| && AI.cp_context(cp, str, LAnc.Forward).nextchar == AI.get_char(str, cp)
    ensures var rf := M.FreshBodyMatch(crv, str, l, lk, ov, ncap, nlook, nquant);
            rf.Some? ==> PIV.CapRegWf(rf.value.capture_regs)
  {
    var cp := if AReg.get_cp(lk, l).Some? then AReg.get_cp(lk, l).value else 0;
    var looktype := if 0 <= l < |crv.f_look_types| then crv.f_look_types[l] else R.Lookahead;
    var cdn := if 0 <= l < |crv.f_look_cdns| then crv.f_look_cdns[l] else [];
    // MatchedPosLA => looktype is Lookahead or Lookbehind. FreshBodyMatch runs the
    // look's CAPTURE direction over `capture_regex(looktype, body)`: for a lookAHEAD
    // that is `body` FORWARD (FreshMatchWf); for a lookBEHIND `reverse_regex(body)`
    // BACKWARD (FreshMatchWfLB). Either yields `ThreadRegsWf`, whose first conjunct
    // is `CapRegWf(capture_regs)`. The backward context fact is definitional.
    if looktype.Lookbehind? {
      var bc := CP.compile_to_bytecode(R.reverse_regex(body));
      assert AI.cp_context(cp, str, LAnc.Backward).nextchar == AI.get_char(str, cp - 1);
      M.FreshMatchWfLB(bc, str, cp, ov, cdn, body, ncap, nlook, nquant);
    } else {
      assert looktype.Lookahead?;
      var bc := CP.compile_to_bytecode(body);
      M.FreshMatchWf(bc, str, cp, ov, cdn, body, ncap, nlook, nquant);
    }
  }

  /** (2026-08-25) NESTED twin of `FreshBodyMatchCapWf` (whose depth-1 fragment
      requires `LookBehindFragmentRE && PlusFragmentRE` cannot hold for a nested
      host — `ForwardFindRec` called it on one; unprovable precondition). Register
      wf of the fresh body match for a NESTED body, either direction: the
      lookahead arm is `M.FreshMatchWfNested`; the lookbehind arm needs no
      fragment at all (`FFindMatchRegsWf` is fragment-blind). */
  lemma FreshBodyMatchCapWfNested(crv: CP.FCompiled, str: string, l: int, lk: AReg.Regs,
                                  ov: LOr.OracleView, ncap: int, nlook: int, nquant: int, body: R.regex)
    requires body == M.VBody(crv, l)
    requires NR.NestedFragmentRE(body) && PIV.CapUnique(body) && PIV.QuantUnique(body)
    requires NR.NoNulledPlusRE(body)   // §2.5b interim: all stamps false
    requires M.MatchedPosLA(crv, lk, l)
    requires ncap >= 0 && nlook >= 0 && nquant >= 0
    requires var cp := if AReg.get_cp(lk, l).Some? then AReg.get_cp(lk, l).value else 0;
             0 <= cp <= |str| && AI.cp_context(cp, str, LAnc.Forward).nextchar == AI.get_char(str, cp)
    ensures var rf := M.FreshBodyMatch(crv, str, l, lk, ov, ncap, nlook, nquant);
            rf.Some? ==> PIV.CapRegWf(rf.value.capture_regs)
  {
    var cp := if AReg.get_cp(lk, l).Some? then AReg.get_cp(lk, l).value else 0;
    var looktype := if 0 <= l < |crv.f_look_types| then crv.f_look_types[l] else R.Lookahead;
    var cdn := if 0 <= l < |crv.f_look_cdns| then crv.f_look_cdns[l] else [];
    if looktype.Lookbehind? {
      var bc := CP.compile_to_bytecode(R.reverse_regex(body));
      var ctx := AI.cp_context(cp, str, LAnc.Backward);
      assert ctx.nextchar == AI.get_char(str, cp - 1);
      var inits := AI.FInitState(bc, cp, AReg.init_regs(ncap), AReg.init_regs(nlook),
                                 AReg.init_regs(nquant), 0, ctx);
      CM.FInitStateRegsWf(bc, cp, ncap, nlook, nquant, 0, ctx);
      M.FFindMatchRegsWf(bc, str, inits, ov, LAnc.Backward, cdn, ncap, nlook, nquant);
    } else {
      assert looktype.Lookahead?;
      var bc := CP.compile_to_bytecode(body);
      M.FreshMatchWfNested(bc, str, cp, ov, cdn, body, ncap, nlook, nquant);
    }
  }

  /** INSIDE `S`, PRESENT case — the crux value equality, modulo the (E)
      RE-side path hypothesis. For a present inside-look group `g` captured by
      look `l`, the winning leaf's value `leafgm[g]` equals the reconstructed
      `GmOfLive(re, res0)[g]`. Chain: `GmtTieInside` (content passed as the
      `gmb` requires) gives `leafgm[g] == gmb[g]` where `gmb = GmOfLive(body,
      rf)`; `M.FLookLoopValueOk` (the `RegsAgreeInside` requires) ties `res0` to
      the fresh match `rf` on `CaptureRegs(body)`; `PIV.BodyPathPresentLk`
      discharges the BODY-side path hypotheses of `GmOfLiveInsideLookPresentEq`,
      which then equates `GmOfLive(re, res0)[g]` with `gmb[g]`. The `rf` thread-
      wf facts (value-set at `g` + clock-consistency, from `FreshMatchWf`) and
      the (E) RE-side `PathPresentLk(re, res0)` + clock-dominance (the winning-
      thread outer-path fact, coupled to the sim/position gate) are `requires` —
      the caller pays them. This is the inside-`S` companion of the free
      `WinningGmtTieOutside`; together they are `L3aValueBridge`'s two branches. */
  lemma InsidePresentResBridge(
    re: R.regex, body: R.regex, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
    th: AI.Thread, leafgm: LG.GroupMap, res0: AReg.Regs, res2: AReg.Regs, l: int,
    ncap: int, nlook: int, nquant: int, g: LG.GroupId)
    requires NR.LookBehindFragmentRE(re) && PIV.CapUnique(re)
    requires NR.LookBehindFragmentRE(body) && NR.LookFreeRE(body) && PIV.CapUnique(body)
    requires body == M.VBody(crv, l)
    requires g in PIV.CapIds(re)     // (from CapIds(body) <= CapIdsInLooks(re) <= CapIds(re), caller-side)
    requires 0 <= l < nlook && g in PIV.CapIds(body) && M.MatchedPosLA(crv, th.look_regs, l)
    // GmtTieInside content at (g, l): fresh match present, leaf value == its value.
    requires var rf := M.FreshBodyMatch(crv, str, l, th.look_regs, ov, ncap, nlook, nquant);
             rf.Some?
             && var gmb := PIV.GmOfLive(body, rf.value.capture_regs, rf.value.look_regs, rf.value.quant_regs);
             var looktype := if 0 <= l < |crv.f_look_types| then crv.f_look_types[l] else R.Lookahead;
             g in gmb && g in leafgm && leafgm[g] == (if looktype.Lookbehind? then LBV.SwapRange(gmb[g]) else gmb[g])
    // FLookLoopValueOk relation at l: res0 agrees with the fresh match on body regs.
    requires var rf := M.FreshBodyMatch(crv, str, l, th.look_regs, ov, ncap, nlook, nquant);
             rf.Some? ==> CM.RegsAgreeInside(res0, rf.value.capture_regs, PIV.CaptureRegs(body))
    // rf thread-wf: clock and value are set together on the body's capture regs
    // (`CapRegWf`, from `FreshBodyMatchCapWf`). This supplies BodyPathPresentLk's
    // clock-consistency and, via its clock-set output, the value-set at g.
    requires var rf := M.FreshBodyMatch(crv, str, l, th.look_regs, ov, ncap, nlook, nquant);
             rf.Some? ==> PIV.CapRegWf(rf.value.capture_regs)
    // (E) RE-side path-presence at g for the reconstructed (res0, res2) state
    // (the sim-coupled gap, paid by caller; res2 is the reconstructed quant that
    // carries the look bodies' clocks — th.quant leaves those unset).
    requires PIV.PathPresentLk(re, AReg.as_arrays(res0).1, AReg.as_arrays(th.look_regs).1,
                               AReg.as_arrays(res2).1, -1, g)
    requires AI.get_idx(AReg.as_arrays(res0).1, CP.start_reg(g))
          >= PIV.MxAtGidLk(re, AReg.as_arrays(res0).1, AReg.as_arrays(th.look_regs).1,
                           AReg.as_arrays(res2).1, -1, g)
    ensures g in leafgm && g in PIV.GmOfLive(re, res0, th.look_regs, res2)
    // L3b: for a LOOKBEHIND lid the reconstructed engine value is the REVERSED span
    // (item-0 quirk); the ordered leaf value is its SWAP. NormalizeArr absorbs this
    // at the top. NO-OP for lookaheads (forward) and capture-free lookbehinds.
    ensures var looktype := if 0 <= l < |crv.f_look_types| then crv.f_look_types[l] else R.Lookahead;
            leafgm[g] == (if looktype.Lookbehind?
                          then LBV.SwapRange(PIV.GmOfLive(re, res0, th.look_regs, res2)[g])
                          else PIV.GmOfLive(re, res0, th.look_regs, res2)[g])
  {
    var rf := M.FreshBodyMatch(crv, str, l, th.look_regs, ov, ncap, nlook, nquant);
    var gmb := PIV.GmOfLive(body, rf.value.capture_regs, rf.value.look_regs, rf.value.quant_regs);
    // Body-side path hypotheses of GmOfLiveInsideLookPresentEq.
    PIV.BodyPathPresentLk(body, rf.value.capture_regs, rf.value.look_regs, rf.value.quant_regs, g);
    // The value equality: GmOfLive(re, res0, _, res2)[g] == GmOfLive(body, rf)[g] == gmb[g].
    M.GmOfLiveInsideLookPresentEq(re, body, res0, th.look_regs, res2,
                                  rf.value.capture_regs, rf.value.look_regs, rf.value.quant_regs, g);
  }

  /** [SEAM — THE LAST GLUE] From the endpoint's leaf ties and the engine's
      FLookLoop facts, conclude MainExtraction's precondition: the leaf gm IS
      the live denotation of the RECONSTRUCTED registers.

      FILL ingredients (this is where the remaining (E) work lives):
      - inside S, present: `GmtTieInside` gives the fresh-replay value;
        `M.FLookLoopValueOk` gives the same value in `res.0`;
        `PIV.GmOfLiveInsideLookPresentEq` + `PIV.BodyPathPresentLk` turn
        register agreement into GmOfLive agreement — their RE-side outer-path
        hypothesis (`PathPresentLk`'s outer ancestors + `lc >= mx`) is the ONE
        (E) piece not yet banked: derive the outer-capture presence from the
        t-side leaf (an inside-look g present in the leaf forces its ancestors'
        opens on the same path — a FirstLeaf structural fact), and `lc >= 0`
        from `M.MainMatchLookClkSet`.
      - inside S, absent: `PIV.GmOfLiveInsideLookAbsentEq`.
      - outside S: `GmtTieOutside` + `M.FLookLoopCaptureFrame` (the fold only
        writes inside `CaptureRegsSet(CapIdsInLooks)`) + `FLookLoopQuantFrame`.
      Statement uses the fold over the FULL lid range as the else branch calls
      it (`lid == 0`, `maxlook == R.max_lookaround(ast)`). */

  /** Convert `InsidePresentResBridge`'s LOOK-TYPE swap into the POSITIONAL
      `NormRange`, using leaf-orderedness. For a lookbehind `lr == SwapRange(rg)`
      and `lr` ordered ⟹ `rg` reversed ⟹ `NormRange(rg) == SwapRange(rg) == lr`;
      for a lookahead `lr == rg` ordered ⟹ `NormRange(rg) == rg == lr`. So no
      separate "LB ⟺ reversed" lemma is needed — it falls out of `lr` ordered. */
  lemma NormRangeFromSwap(rg: LG.Range, lr: LG.Range, isLB: bool)
    requires lr == (if isLB then LBV.SwapRange(rg) else rg)
    requires lr.endIdx.Some? ==> lr.startIdx <= lr.endIdx.value          // lr ordered
    ensures lr == PIV.NormRange(rg)
  {
    if isLB {
      match rg.endIdx {
        case None =>            // SwapRange / NormRange both identity on an open range
        case Some(e) =>
          assert lr == LG.Range(e, Some(rg.startIdx));                   // SwapRange def
          assert e <= rg.startIdx;                                       // lr ordered
      }
    } else {
      PIV.NormRangeOrdered(rg);
    }
  }

  lemma L3aValueBridge(re: R.regex, th: AI.Thread, leafgm: LG.GroupMap,
                       res0: AReg.Regs, res2: AReg.Regs, S: set<LG.GroupId>)
    requires T.TransWf(re) && NR.LookBehindFragmentRE(re) && PIV.CapUnique(re)
    requires S == PIV.CapIdsInLooks(re)
    // L3b: the leaf value is ORDERED (spec GMClose ordering); this lets NormRange
    // collapse to the identity on the outside/forward groups.
    requires M.OrderedGm(leafgm)
    // OUTSIDE S: the winning-thread tie + FLookLoop frame conclusions.
    requires GmtTieOutside(re, th, leafgm, S)
    requires forall k: int :: k !in PIV.CaptureRegsSet(PIV.CapIdsInLooks(re)) ==>
                                AI.get_idx(AReg.as_arrays(res0).0, k) == AI.get_idx(AReg.as_arrays(th.capture_regs).0, k)
                                && AI.get_idx(AReg.as_arrays(res0).1, k) == AI.get_idx(AReg.as_arrays(th.capture_regs).1, k)
    requires forall q: nat :: q in PIV.QuantIdsOutsideLooks(re) ==>
                                AI.get_idx(AReg.as_arrays(res2).1, q) == AI.get_idx(AReg.as_arrays(th.quant_regs).1, q)
    // INSIDE S, present: the leaf value is the POSITIONAL normalization of the
    // reconstructed value (aggregated per-g from `InsidePresentResBridge`; the
    // reversed lookbehind span is swapped, forward looks are unchanged).
    requires forall g: LG.GroupId :: g in S && g in leafgm ==>
                                       g in PIV.GmOfLive(re, res0, th.look_regs, res2)
                                       && leafgm[g] == PIV.NormRange(PIV.GmOfLive(re, res0, th.look_regs, res2)[g])
    // INSIDE S, absent (reverse tie): the reconstruction invents no S-group the
    // leaf lacks — the other half of the key-set equality.
    requires forall g: LG.GroupId :: g in S && g in PIV.GmOfLive(re, res0, th.look_regs, res2) ==> g in leafgm
    ensures leafgm == PIV.NormGm(PIV.GmOfLive(re, res0, th.look_regs, res2))
  {
    var gml := PIV.GmOfLive(re, res0, th.look_regs, res2);
    var ngml := PIV.NormGm(gml);
    var gmBest := PIV.GmOfLive(re, th.capture_regs, th.look_regs, th.quant_regs);
    // S == LkBodyGroups(Translate(re)) so GmtTieOutside feeds OutsideLookValueBridge.
    M.LkBodyGroupsEqCapIdsInLooks(re);
    M.OutsideLookValueBridge(re, th.capture_regs, res0, th.look_regs, th.quant_regs, res2, gmBest, leafgm);
    forall g: LG.GroupId
      ensures (g in leafgm <==> g in ngml) && (g in leafgm ==> leafgm[g] == ngml[g])
    {
      assert (g in ngml) <==> (g in gml);              // NormGm preserves keys
      if g in leafgm {
        if g in S {
          // present ⟹ (requires) leafgm[g] == NormRange(gml[g]) == ngml[g].
        } else {
          // OutsideLookValueBridge: leafgm[g] == gml[g] off S; leafgm ORDERED ⟹
          // gml[g] ordered ⟹ NormRange is identity.
          PIV.NormRangeOrdered(gml[g]);
        }
      }
    }
    assert leafgm == ngml;
  }

  /** (L4 NESTED) Structure-agnostic clone of `L3aValueBridge`. The depth-1
      original derives the OUTSIDE-`S` leaf/reconstruction agreement internally
      from register frames via `M.OutsideLookValueBridge`, which requires
      `LookBehindFragmentRE(re)` (FALSE under nesting). Here that outside-`S`
      agreement is taken as a DIRECT premise (the endpoint supplies it via the
      nested outside frame), so the assembly carries NO fragment hypothesis and
      is entirely depth-agnostic. The INSIDE-`S` present/absent premises keep
      their EXACT shape (C4 supplies them from the 3-component chain). */
  lemma L3aValueBridgeNested(re: R.regex, th: AI.Thread, leafgm: LG.GroupMap,
                             res0: AReg.Regs, res2: AReg.Regs, S: set<LG.GroupId>)
    requires S == PIV.CapIdsInLooks(re)
    // L3b: the leaf value is ORDERED (spec GMClose ordering); this lets NormRange
    // collapse to the identity on the outside/forward groups.
    requires M.OrderedGm(leafgm)
    // OUTSIDE S: leaf agrees with the reconstructed GmOfLive (membership + value)
    // — supplied by the caller (endpoint) via the nested outside frame.
    requires forall g: LG.GroupId :: g !in S ==>
                                       (g in leafgm <==> g in PIV.GmOfLive(re, res0, th.look_regs, res2))
                                       && (g in leafgm ==> leafgm[g] == PIV.GmOfLive(re, res0, th.look_regs, res2)[g])
    // INSIDE S, present: the leaf value is the POSITIONAL normalization of the
    // reconstructed value (aggregated per-g from the 3-component chain).
    requires forall g: LG.GroupId :: g in S && g in leafgm ==>
                                       g in PIV.GmOfLive(re, res0, th.look_regs, res2)
                                       && leafgm[g] == PIV.NormRange(PIV.GmOfLive(re, res0, th.look_regs, res2)[g])
    // INSIDE S, absent (reverse tie): the reconstruction invents no S-group the
    // leaf lacks — the other half of the key-set equality.
    requires forall g: LG.GroupId :: g in S && g in PIV.GmOfLive(re, res0, th.look_regs, res2) ==> g in leafgm
    ensures leafgm == PIV.NormGm(PIV.GmOfLive(re, res0, th.look_regs, res2))
  {
    var gml := PIV.GmOfLive(re, res0, th.look_regs, res2);
    var ngml := PIV.NormGm(gml);
    forall g: LG.GroupId
      ensures (g in leafgm <==> g in ngml) && (g in leafgm ==> leafgm[g] == ngml[g])
    {
      assert (g in ngml) <==> (g in gml);              // NormGm preserves keys
      if g in leafgm {
        if g in S {
          // present ⟹ (requires) leafgm[g] == NormRange(gml[g]) == ngml[g].
        } else {
          // outside: leafgm[g] == gml[g] (direct premise); leafgm ORDERED ⟹
          // gml[g] ordered ⟹ NormRange is identity.
          PIV.NormRangeOrdered(gml[g]);
        }
      }
    }
    assert leafgm == ngml;
  }

  /** (L4 NESTED) `M.OutsideLookValueBridge` under `NestedFragmentRE`. The depth-1
      original goes through `PIV.GmOfLiveFrameOutside`, whose `LookBehindFragmentRE`
      requirement is FALSE under nesting. But the underlying combined cap+quant
      frame `PIV.FilterFrameOutside` is FRAGMENT-FREE (it recurses purely on the
      register-layout W-set, handling `Re_lookaround` via `FilterCaptureAgreeOutsideOwn`),
      so the nested outside frame is a SINGLE `FilterFrameOutside` call — no
      fragment hypothesis anywhere. Feeds the endpoint's outside-`S` half. */
  lemma OutsideLookValueBridgeNested(re: R.regex, capT: AReg.Regs, capR: AReg.Regs, look: AReg.Regs,
                                     quantT: AReg.Regs, quantR: AReg.Regs, gmBest: LG.GroupMap, ft: LG.GroupMap)
    requires T.TransWf(re) && NR.NestedFragmentRE(re) && PIV.CapUnique(re)
    requires gmBest == PIV.GmOfLive(re, capT, look, quantT)
    requires forall g: nat :: g !in LL.LkBodyGroups(T.Translate(re)) ==>
                                (g in ft <==> g in gmBest) && (g in ft ==> ft[g] == gmBest[g])
    requires forall k: int :: k !in PIV.CaptureRegsSet(PIV.CapIdsInLooks(re)) ==>
                                AI.get_idx(AReg.as_arrays(capR).0, k) == AI.get_idx(AReg.as_arrays(capT).0, k)
                                && AI.get_idx(AReg.as_arrays(capR).1, k) == AI.get_idx(AReg.as_arrays(capT).1, k)
    requires forall q: nat :: q in PIV.QuantIdsOutsideLooks(re) ==>
                                AI.get_idx(AReg.as_arrays(quantR).1, q) == AI.get_idx(AReg.as_arrays(quantT).1, q)
    ensures forall g: nat :: g !in PIV.CapIdsInLooks(re) ==>
                               (g in ft <==> g in PIV.GmOfLive(re, capR, look, quantR))
                               && (g in ft ==> ft[g] == PIV.GmOfLive(re, capR, look, quantR)[g])
  {
    M.LkBodyGroupsEqCapIdsInLooks(re);                 // LkBodyGroups(Translate(re)) == CapIdsInLooks(re)
    var W := PIV.CaptureRegsSet(PIV.CapIdsInLooks(re));
    var crA := AReg.as_arrays(capT).0;  var ccA := AReg.as_arrays(capT).1;
    var crB := AReg.as_arrays(capR).0;  var ccB := AReg.as_arrays(capR).1;
    var lc := AReg.as_arrays(look).1;
    var qcA := AReg.as_arrays(quantT).1; var qcB := AReg.as_arrays(quantR).1;

    // structural requires of FilterFrameOutside (mirrors GmOfLiveFrameOutside)
    PIV.CapIdsLooksDisjoint(re);
    assert forall g: nat :: g in PIV.CapIdsInLooks(re) ==> CP.start_reg(g) in W by {
      forall g: nat | g in PIV.CapIdsInLooks(re) ensures CP.start_reg(g) in W { PIV.StartRegInCaptureRegsSet(PIV.CapIdsInLooks(re), g); }
    }
    assert forall g: nat :: g in PIV.CapIdsOutsideLooks(re) ==> CP.start_reg(g) !in W by {
      forall g: nat | g in PIV.CapIdsOutsideLooks(re) ensures CP.start_reg(g) !in W {
        assert g !in PIV.CapIdsInLooks(re) by { if g in PIV.CapIdsInLooks(re) { assert g in PIV.CapIdsOutsideLooks(re) * PIV.CapIdsInLooks(re); } }
        PIV.StartRegInCaptureRegsSet(PIV.CapIdsInLooks(re), g);
      }
    }
    assert forall x: int :: x in W ==> x >= 0 by {
      forall x: int | x in W ensures x >= 0 {}
    }
    // single combined cap+quant swap outside W (FRAGMENT-FREE).
    PIV.FilterFrameOutside(re, crA, crB, ccA, ccB, lc, qcA, qcB, -1, W);

    var f1 := AI.filter_reset(re, capT, look, quantT, -1);
    var f2 := AI.filter_reset(re, capR, look, quantR, -1);
    assert f1 == AI.filter_capture(re, crA, ccA, lc, qcA, -1);
    assert f2 == AI.filter_capture(re, crB, ccB, lc, qcB, -1);

    forall g: nat | g !in PIV.CapIdsInLooks(re)
      ensures (g in ft <==> g in PIV.GmOfLive(re, capR, look, quantR))
              && (g in ft ==> ft[g] == PIV.GmOfLive(re, capR, look, quantR)[g])
    {
      assert g !in LL.LkBodyGroups(T.Translate(re));       // set identity
      PIV.StartRegInCaptureRegsSet(PIV.CapIdsInLooks(re), g);
      PIV.EndRegInCaptureRegsSet(PIV.CapIdsInLooks(re), g);
      assert CP.start_reg(g) !in W && CP.end_reg(g) !in W;
      assert AI.get_idx(f1, CP.start_reg(g)) == AI.get_idx(f2, CP.start_reg(g));
      assert AI.get_idx(f1, CP.end_reg(g)) == AI.get_idx(f2, CP.end_reg(g));
      assert AI.get_idx(ccA, CP.start_reg(g)) == AI.get_idx(ccB, CP.start_reg(g));
      assert AI.get_idx(ccA, CP.end_reg(g)) == AI.get_idx(ccB, CP.end_reg(g));
    }
  }

  /** (K-close) TOP-LEVEL: the winning VM thread and the spec tree's FIRST LEAF
      satisfy the two-sided value tie (`BestTieLk` = `GmtTieOutside` +
      `GmtTieInside`). Drives `LiftInitC` → `LiftStepC*` → the `PTS_final` case,
      mirroring `FindMatchSimRE` on the machine-A side and `PTL.TrcPikeTreeLk` +
      `PTL.PikeTreeLkComputesFirstLeaf` on the machine-B side. This is the SINGLE
      remaining sim output; it feeds `WinningGmtTieOutside` (already banked) and,
      per-`g`, `InsidePresentResBridge` → `L3aValueBridge`. BODILESS — this is
      where the (E) path-presence, the reverse tie, and the position tie
      (`a_cp[l]` == the LK node's first-leaf position) are discharged. */
  /** `PikeSubtreeLk` transfers across erasure-equality: erasure drops only
      `Progress` wrappers and maps every other constructor (incl. the
      unconstrained LK bodies) in place, so `ReadBackRef`-freeness is
      erasure-invariant. Lets the FirstLeaf theorem run on `tcan` from the raw
      entry tree's shape fact. */
  lemma PikeSubtreeLkEraseIff(x: LT.Tree)
    ensures PTL.PikeSubtreeLk(x) <==> PTL.PikeSubtreeLk(CE.ProgErase(x))
    decreases x
  {
    match x
    case Choice(t1, t2) => PikeSubtreeLkEraseIff(t1); PikeSubtreeLkEraseIff(t2);
    case Read(_, t1) => PikeSubtreeLkEraseIff(t1);
    case ReadBackRef(_, t1) =>
    case Progress(t1) => PikeSubtreeLkEraseIff(t1);
    case AnchorPass(_, t1) => PikeSubtreeLkEraseIff(t1);
    case GroupActionT(_, t1) => PikeSubtreeLkEraseIff(t1);
    case LK(_, _, t1) => PikeSubtreeLkEraseIff(t1);
    case _ =>
  }

  lemma TtLkAtBeginLoopRec(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                           tb: LT.Tree, pc: nat, ea: bool)
    requires TtLkRec(rer, qm, code, inp, tb, pc, ea)
    requires NR.GetPcRE(code, pc) == Some(RB.BeginLoop)
    ensures TtLkRec(rer, qm, code, inp, tb, pc + 1, false)
  {
    // The ActionsRepL disjunct is unsatisfiable at a BeginLoop pc.
    forall acts: LS.Actions, b: BS.LoopBool
      ensures !(AR.ActionsRepL(rer, qm, acts, code, pc)
                && EL.PikeLkActionsRec(acts) && ATR.EaOf(b) == ea
                && EL.BoolTreeLk(rer, acts, inp, b, tb))
    {
      if AR.ActionsRepL(rer, qm, acts, code, pc) {
        TT.ActionsRepNotAtBeginLoop(rer, qm, acts, code, pc);   // ⇒ false
      }
    }
    // So TtLkRec(pc) holds via the BeginLoop stutter, whose payload is TtLkRec(pc+1, false).
  }

  lemma BoolTreeLkGuardShieldRec(rer: LW.RegExpRecord, r1: L.Regex, rest: LS.Actions,
                                 inp: LC.Input, ti: LT.Tree)
    requires NUL.NonNullableL(r1)
    requires EL.PikeLkActionsRec([LS.Areg(r1)] + rest)
    requires EL.BoolTreeLk(rer, [LS.Areg(r1)] + rest, inp, BS.CannotExit, ti)
    ensures EL.BoolTreeLk(rer, [LS.Areg(r1)] + rest, inp, BS.CanExit, ti)
  {
    var acts := [LS.Areg(r1)] + rest;
    assert CE.ShieldedActs(acts) by {
      forall i | 0 <= i < |acts| && acts[i].Acheck?
        ensures exists j :: 0 <= j < i && acts[j].Areg? && NUL.NonNullableL(acts[j].r)
      {
        assert acts[0] == LS.Areg(r1);
        assert i >= 1;
        assert acts[0].Areg? && NUL.NonNullableL(acts[0].r);
      }
    }
    CE.BoolFlagLiftRec(rer, acts, inp, ti);
  }

  lemma ActionsTreeRepLkFRec(rer: LW.RegExpRecord, qm: AR.QMap, acts: LS.Actions,
                                                   code: RB.code, pc: nat, inp: LC.Input,
                                                   b: BS.LoopBool, t: LT.Tree, n: nat)
    returns (tcan: LT.Tree)
    requires EL.PikeLkActionsRec(acts)
    requires ATR.ActionsRepFuelL(rer, qm, acts, code, pc, n)
    requires WO.WalkOk(acts, code, pc, ATR.EaOf(b))
    requires EL.BoolTreeLk(rer, acts, inp, b, t)
    ensures TreeRepLkRE(rer, qm, code, inp, tcan, pc, ATR.EaOf(b))
    ensures CE.ProgErase(tcan) == CE.ProgErase(t)
    decreases CE.PSize(t), ATR.MsizeA(acts), n, 1
  {
    // (§2.5b) the new recursive nullability predicates' definitional axioms send
    // z3 4.14 into a matching loop on otherwise-trivial goals in the quant arms;
    // every use here is opaque (guards + lemma calls), so hide them.
    hide NUL.NonNullableL, NUL.CINullableL, NUL.NoNulledPlusL, AR.NfaRepCinL;
    if |acts| == 0 && NR.GetPcRE(code, pc) == Some(RB.Accept) {
      assert t == LT.Match;
      tcan := LT.Match;
      // tr_match
    } else if exists pcstart: nat :: NR.GetPcRE(code, pc) == Some(RB.Jmp(pcstart))
                                     && ATR.ActionsRepFuelL(rer, qm, acts, code, pcstart, n - 1) {
      var pcstart: nat :| NR.GetPcRE(code, pc) == Some(RB.Jmp(pcstart))
                          && ATR.ActionsRepFuelL(rer, qm, acts, code, pcstart, n - 1);
      WO.WalkOkJmp(acts, code, pc, ATR.EaOf(b), pcstart);
      tcan := ActionsTreeRepLkFRec(rer, qm, acts, code, pcstart, inp, b, t, n - 1);
      // tr_jmp
      assert TreeRepLkRE(rer, qm, code, inp, tcan, pc, ATR.EaOf(b));
    } else {
      var cont := acts[1..];
      var pcmid: nat :| AR.ActionRepL(rer, qm, acts[0], code, pc, pcmid)
                        && ATR.ActionsRepFuelL(rer, qm, cont, code, pcmid, n - 1);
      EL.PikeLkActionsRecTail(acts);
      assert acts == [acts[0]] + cont;
      EL.PikeLkActionsRecConsIff(acts[0], cont);
      match acts[0]
      case Acheck(strcheck) =>
        assert LS.ActionsRegexSize(acts) == LS.ActionsRegexSize(cont);
        if NR.GetPcRE(code, pc) == Some(RB.EndLoop) {
          assert pcmid == pc + 1;
          if b == BS.CanExit {
            match t {
              case Progress(tc) =>
                WO.WalkOkAcheckEndLoop(acts, code, pc, ATR.EaOf(b));
                var sub := ActionsTreeRepLkFRec(rer, qm, cont, code, pc + 1, inp, BS.CanExit, tc, n - 1);
                tcan := LT.Progress(sub);
                // tr_progress (fall-through EndLoop)
                assert TreeRepLkRE(rer, qm, code, inp, tcan, pc, true);
              case _ =>
            }
          } else {
            // t == Mismatch: tr_progressfail
            tcan := LT.Mismatch;
            assert TreeRepLkRE(rer, qm, code, inp, tcan, pc, false);
          }
        } else {
          // the zero-width check at the do-while's backward fork
          assert AR.BackForkAt(code, pc) && pcmid == pc;
          if b == BS.CanExit {
            match t {
              case Progress(tc) =>
                WO.WalkOkAcheckBackFork(acts, code, pc, ATR.EaOf(b));
                var sub := AtBackForkTreeLkFRec(rer, qm, cont, code, pc, inp, tc, n - 1);
                tcan := LT.Progress(sub);
                // the companion's ensures IS tr_plus for Progress(sub)
                assert TreeRepLkRE(rer, qm, code, inp, tcan, pc, true);
              case _ =>
            }
          } else {
            // t == Mismatch: tr_plusfail
            var fx: int, fy: int :| NR.GetPcRE(code, pc) == Some(RB.Fork(fx, fy))
                                    && fx >= 0 && fy >= 0 && (fx as nat <= pc || fy as nat <= pc);
            tcan := LT.Mismatch;
            assert TreeRepLkRE(rer, qm, code, inp, tcan, pc, false);
          }
        }
      case Aclose(gid) =>
        match t {
          case GroupActionT(g, tc) =>
            assert g == LG.Close(gid);
            WO.WalkOkAclose(acts, code, pc, ATR.EaOf(b));
            assert CE.PSize(tc) < CE.PSize(t);
            var sub := ActionsTreeRepLkFRec(rer, qm, cont, code, pc + 1, inp, b, tc, n - 1);
            tcan := LT.GroupActionT(g, sub);
            // tr_close
            assert TreeRepLkRE(rer, qm, code, inp, tcan, pc, ATR.EaOf(b));
          case _ =>
        }
      case Areg(r) =>
        assert EL.PikeLkRegexRec(r);
        match r
        case Epsilon =>
          assert {:split_here} true;   // (E3) one assertion batch per arm
          assert pcmid == pc;
          WO.WalkOkEpsilon(acts, code, pc, ATR.EaOf(b));
          assert ATR.MsizeA(cont) < ATR.MsizeA(acts);
          tcan := ActionsTreeRepLkFRec(rer, qm, cont, code, pc, inp, b, t, n - 1);
        case Character(cd) => {
          assert {:split_here} true;   // (E3) one assertion batch per arm
          var ce :| NR.GetPcRE(code, pc) == Some(RB.Consume(ce)) && AR.ExpectationMatches(rer, ce, cd);
          AR.ReadAgree(rer, ce, cd, inp);
          match LC.ReadChar(rer, cd, inp, WP.Forward) {
            case None =>
              // t == Mismatch; tr_readfail (ReadCharE == None by ReadAgree)
              tcan := LT.Mismatch;
              assert TreeRepLkRE(rer, qm, code, inp, tcan, pc, ATR.EaOf(b));
            case Some(pair) =>
              match t {
                case Read(c, tc) =>
                  assert c == pair.0;
                  WO.WalkOkCharacter(acts, code, pc, ATR.EaOf(b));
                  assert CE.PSize(tc) < CE.PSize(t);
                  var sub := ActionsTreeRepLkFRec(rer, qm, cont, code, pc + 1, pair.1, BS.CanExit, tc, n - 1);
                  tcan := LT.Read(c, sub);
                  // tr_read with witness (ce, pair.1)
                  assert AR.ReadCharE(ce, inp) == Some((c, pair.1));
                  assert TreeRepLkRE(rer, qm, code, inp, tcan, pc, ATR.EaOf(b));
                case _ =>
              }
          }
        }
        case Disjunction(r1, r2) => {
          assert {:split_here} true;   // (E3) one assertion batch per arm
          EL.PikeLkActionsRecConsIff(LS.Areg(r1), cont);
          EL.PikeLkActionsRecConsIff(LS.Areg(r2), cont);
          var e1: nat :| NR.GetPcRE(code, pc) == Some(RB.Fork(pc + 1, e1 + 1))
                         && AR.NfaRepL(rer, qm, r1, code, pc + 1, e1)
                         && NR.GetPcRE(code, e1) == Some(RB.Jmp(pcmid))
                         && AR.NfaRepL(rer, qm, r2, code, e1 + 1, pcmid);
          AR.NfaRepIncrL(rer, qm, r1, code, pc + 1, e1);
          match t {
            case Choice(ta, tb) =>
              WO.WalkOkAlt(acts, code, pc, ATR.EaOf(b), r1, r2, pc + 1, e1 + 1);
              // left branch: [Areg r1]+cont at pc+1 (cont reached via Jmp(e1 -> pcmid))
              var la := [LS.Areg(r1)] + cont;
              assert AR.ActionsRepL(rer, qm, cont, code, e1) by {
                ATR.FuelToActionsRepL(rer, qm, cont, code, pcmid, n - 1);
                assert NR.GetPcRE(code, e1) == Some(RB.Jmp(pcmid));
              }
              assert AR.ActionRepL(rer, qm, LS.Areg(r1), code, pc + 1, e1);
              assert la[0] == LS.Areg(r1) && la[1..] == cont;
              assert AR.ActionsRepL(rer, qm, la, code, pc + 1);
              ATR.ActionsRepLToFuel(rer, qm, la, code, pc + 1);
              var na: nat :| ATR.ActionsRepFuelL(rer, qm, la, code, pc + 1, na);
              assert CE.PSize(ta) < CE.PSize(t);
              var suba := ActionsTreeRepLkFRec(rer, qm, la, code, pc + 1, inp, b, ta, na);
              // right branch: [Areg r2]+cont at e1+1
              var lb := [LS.Areg(r2)] + cont;
              ATR.FuelToActionsRepL(rer, qm, cont, code, pcmid, n - 1);
              assert AR.ActionRepL(rer, qm, LS.Areg(r2), code, e1 + 1, pcmid);
              assert lb[0] == LS.Areg(r2) && lb[1..] == cont;
              assert AR.ActionsRepL(rer, qm, lb, code, e1 + 1);
              ATR.ActionsRepLToFuel(rer, qm, lb, code, e1 + 1);
              var nb: nat :| ATR.ActionsRepFuelL(rer, qm, lb, code, e1 + 1, nb);
              assert CE.PSize(tb) < CE.PSize(t);
              var subb := ActionsTreeRepLkFRec(rer, qm, lb, code, e1 + 1, inp, b, tb, nb);
              tcan := LT.Choice(suba, subb);
              // tr_choice with the forward Fork(pc+1, e1+1): e1 >= pc+1 by NfaRepIncrL
              assert TreeRepLkRE(rer, qm, code, inp, tcan, pc, ATR.EaOf(b));
            case _ =>
          }
        }
        case Sequence(r1, r2) => {
          assert {:split_here} true;   // (E3) one assertion batch per arm
          EL.PikeLkActionsRecConsIff(LS.Areg(r2), cont);
          EL.PikeLkActionsRecConsIff(LS.Areg(r1), [LS.Areg(r2)] + cont);
          assert AR.NfaRepL(rer, qm, L.Sequence(r1, r2), code, pc, pcmid);
          var e1: nat :| AR.NfaRepL(rer, qm, r1, code, pc, e1) && AR.NfaRepL(rer, qm, r2, code, e1, pcmid);
          var na := [LS.Areg(r1), LS.Areg(r2)] + cont;
          assert na == [LS.Areg(r1)] + ([LS.Areg(r2)] + cont);
          assert AR.ActionRepL(rer, qm, LS.Areg(r2), code, e1, pcmid);
          assert ([LS.Areg(r2)] + cont)[0] == LS.Areg(r2) && ([LS.Areg(r2)] + cont)[1..] == cont;
          ATR.FuelToActionsRepL(rer, qm, cont, code, pcmid, n - 1);
          assert AR.ActionsRepL(rer, qm, [LS.Areg(r2)] + cont, code, e1);
          assert AR.ActionRepL(rer, qm, LS.Areg(r1), code, pc, e1);
          assert na[0] == LS.Areg(r1) && na[1..] == [LS.Areg(r2)] + cont;
          assert AR.ActionsRepL(rer, qm, na, code, pc);
          assert LS.ActionsRegexSize(na) < LS.ActionsRegexSize(acts);
          assert ATR.MsizeA(na) < ATR.MsizeA(acts);
          ATR.ActionsRepLToFuel(rer, qm, na, code, pc);
          var nn: nat :| ATR.ActionsRepFuelL(rer, qm, na, code, pc, nn);
          WO.WalkOkSeq(acts, code, pc, ATR.EaOf(b), r1, r2);
          tcan := ActionsTreeRepLkFRec(rer, qm, na, code, pc, inp, b, t, nn);
        }
        case Quantified(greedy, min, delta, r1) => {
          assert {:split_here} true;   // (E3) one assertion batch per arm
          var gidl := L.DefGroups(r1);
          if min > 0 {
            match delta {
              case Inf =>
                if !NUL.NonNullableL(r1) {
                  assert {:split_here} true;   // (E3) generic arm in its own batch
                  assert !greedy by {          // §2.5b interim (PikeLk conjunct)
                    assert acts[0] == LS.Areg(L.Quantified(greedy, min, delta, r1));
                  }
                  // §2.5a GENERIC: `min` forced copies then the ordinary star
                  // loop at `emg`. No seam -- the code's BeginLoop/EndLoop sits
                  // exactly where the spec's Acheck is, so nothing is inserted
                  // and this arm needs no nullability hypothesis.
                  var emg, e1g := AR.NfaRepLGenInv(rer, qm, greedy, min, r1, code, pc, pcmid);
                  var qidg: int :| NR.GetPcRE(code, emg + 1) == Some(RB.SetQuantToClock(qidg, false))
                                   && qidg in qm.quants && qm.quants[qidg] == gidl;
                  AR.NfaRepIncrL(rer, qm, r1, code, emg + 3, e1g);
                  var quant1g := L.Quantified(greedy, min - 1, LN.Inf, r1);
                  var ebg: nat :| (exists qid2: int ::
                                     NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(qid2, false))
                                     && qid2 in qm.quants && qm.quants[qid2] == gidl)
                                  && AR.NfaRepL(rer, qm, r1, code, pc + 1, ebg)
                                  && AR.NfaRepMinL(rer, qm, min - 1, r1, code, ebg, emg);
                  if min > 1 {
                    AR.NfaRepLGenIntro(rer, qm, greedy, min - 1, r1, code, ebg, emg, e1g, pcmid, qidg);
                  } else {
                    assert ebg == emg;   // NfaRepMinL(0, …); the star arm at emg IS quant1g
                  }
                  assert AR.NfaRepL(rer, qm, quant1g, code, ebg, pcmid);
                  match t {
                    case GroupActionT(g, tc) =>
                      assert g == LG.Reset(gidl);
                      EL.PikeLkActionsConsIff(LS.Areg(quant1g), cont);
                      EL.PikeLkActionsConsIff(LS.Areg(r1), [LS.Areg(quant1g)] + cont);
                      ATR.FuelToActionsRepL(rer, qm, cont, code, pcmid, n - 1);
                      assert AR.ActionRepL(rer, qm, LS.Areg(quant1g), code, ebg, pcmid);
                      var lq1g := [LS.Areg(quant1g)] + cont;
                      assert lq1g[0] == LS.Areg(quant1g) && lq1g[1..] == cont;
                      assert AR.ActionsRepL(rer, qm, lq1g, code, ebg);
                      var iag := [LS.Areg(r1)] + lq1g;
                      assert AR.ActionRepL(rer, qm, LS.Areg(r1), code, pc + 1, ebg);
                      assert iag[0] == LS.Areg(r1) && iag[1..] == lq1g;
                      assert AR.ActionsRepL(rer, qm, iag, code, pc + 1);
                      assert iag == [LS.Areg(r1), LS.Areg(quant1g)] + cont;
                      ATR.ActionsRepLToFuel(rer, qm, iag, code, pc + 1);
                      var nig: nat :| ATR.ActionsRepFuelL(rer, qm, iag, code, pc + 1, nig);
                      WO.WalkOkQuantForced(acts, code, pc, ATR.EaOf(b), greedy, min, delta, r1);
                      assert CE.PSize(tc) < CE.PSize(t);
                      var subg := ActionsTreeRepLkFRec(rer, qm, iag, code, pc + 1, inp, b, tc, nig);
                      tcan := LT.GroupActionT(g, subg);
                      assert TreeRepLkRE(rer, qm, code, inp, tcan, pc, ATR.EaOf(b));
                    case _ =>
                  }
                } else {
                assert {:split_here} true;   // (E3) do-while arm in its own batch
                var em, e1x := AR.NfaRepLPlusInv(rer, qm, greedy, min, r1, code, pc, pcmid);
                assert NUL.NonNullableL(r1);
                var qid: int :| NR.GetPcRE(code, em) == Some(RB.SetQuantToClock(qid, false))
                                && qid in qm.quants && qm.quants[qid] == gidl;
                AR.NfaRepIncrL(rer, qm, r1, code, em + 1, e1x);
                if min > 1 {
                  var quant1 := L.Quantified(greedy, min - 1, LN.Inf, r1);
                  var eb: nat :| (exists qid2: int ::
                                    NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(qid2, false))
                                    && qid2 in qm.quants && qm.quants[qid2] == gidl)
                                 && AR.NfaRepL(rer, qm, r1, code, pc + 1, eb)
                                 && AR.NfaRepMinL(rer, qm, min - 2, r1, code, eb, em);
                  AR.NfaRepLPlusIntro(rer, qm, greedy, min - 1, r1, code, eb, em, e1x, pcmid, qid);
                  assert AR.NfaRepL(rer, qm, quant1, code, eb, pcmid);
                  match t {
                    case GroupActionT(g, tc) =>
                      assert g == LG.Reset(gidl);
                      EL.PikeLkActionsRecConsIff(LS.Areg(quant1), cont);
                      EL.PikeLkActionsRecConsIff(LS.Areg(r1), [LS.Areg(quant1)] + cont);
                      ATR.FuelToActionsRepL(rer, qm, cont, code, pcmid, n - 1);
                      assert AR.ActionRepL(rer, qm, LS.Areg(quant1), code, eb, pcmid);
                      var lq1 := [LS.Areg(quant1)] + cont;
                      assert lq1[0] == LS.Areg(quant1) && lq1[1..] == cont;
                      assert AR.ActionsRepL(rer, qm, lq1, code, eb);
                      var ia := [LS.Areg(r1)] + lq1;
                      assert AR.ActionRepL(rer, qm, LS.Areg(r1), code, pc + 1, eb);
                      assert ia[0] == LS.Areg(r1) && ia[1..] == lq1;
                      assert AR.ActionsRepL(rer, qm, ia, code, pc + 1);
                      assert ia == [LS.Areg(r1), LS.Areg(quant1)] + cont;
                      ATR.ActionsRepLToFuel(rer, qm, ia, code, pc + 1);
                      var ni: nat :| ATR.ActionsRepFuelL(rer, qm, ia, code, pc + 1, ni);
                      WO.WalkOkQuantForced(acts, code, pc, ATR.EaOf(b), greedy, min, delta, r1);
                      assert CE.PSize(tc) < CE.PSize(t);
                      var sub := ActionsTreeRepLkFRec(rer, qm, ia, code, pc + 1, inp, b, tc, ni);
                      tcan := LT.GroupActionT(g, sub);
                      // tr_reset at pc (the copy's clock-mark carries the Reset)
                      assert TreeRepLkRE(rer, qm, code, inp, tcan, pc, ATR.EaOf(b));
                    case _ =>
                  }
                } else {
                  // min == 1: THE SEAM. Insert the check; erasure makes the
                  // insertion invisible (BoolCheckInsert's ProgErase ensures).
                  assert em == pc;
                  var q0 := L.Quantified(greedy, 0, LN.Inf, r1);
                  match t {
                    case GroupActionT(g, tc) =>
                      assert g == LG.Reset(gidl);
                      assert EL.BoolTreeLk(rer, [LS.Areg(r1), LS.Areg(q0)] + cont, inp, b, tc);
                      var pre := [LS.Areg(r1)];
                      var rest := [LS.Areg(q0)] + cont;
                      EL.PikeLkActionsRecConsIff(LS.Areg(q0), cont);
                      EL.PikeLkActionsRecConsIff(LS.Areg(r1), rest);
                      assert EL.PikeLkActionsRec(pre) by {
                        assert pre == [LS.Areg(r1)] + [];
                        EL.PikeLkActionsRecConsIff(LS.Areg(r1), []);
                      }
                      assert pre + rest == [LS.Areg(r1), LS.Areg(q0)] + cont;
                      assert CE.ConsumesBeforeAreg(pre) by {
                        assert pre[0].Areg? && NUL.NonNullableL(pre[0].r);
                      }
                      var t1ck := CE.BoolCheckInsertK(rer, pre, inp, rest, inp, b, tc);   // (2026-08-28) the Rec twin — `pre` is only PikeLkActionsRec here
                      assert CE.ProgErase(t1ck) == CE.ProgErase(tc);
                      var ia := [LS.Areg(r1), LS.Acheck(inp), LS.Areg(q0)] + cont;
                      assert ia == pre + [LS.Acheck(inp)] + rest;
                      assert EL.BoolTreeLk(rer, ia, inp, b, t1ck);
                      assert AR.BackForkAt(code, e1x) by {
                        assert NR.GetPcRE(code, e1x)
                            == Some(if greedy then RB.Fork(em, e1x + 1) else RB.Fork(e1x + 1, em));
                        assert em <= e1x;
                      }
                      assert AR.NfaRepL(rer, qm, q0, code, e1x, e1x + 1) by {
                        // (§2.5b/z3 4.14) granular witnesses first — the packed
                        // conjunction alone sends the solver hunting for the skolem
                        assert NUL.NonNullableL(r1);
                        assert NR.GetPcRE(code, e1x)
                            == Some(if greedy then RB.Fork(em, e1x + 1) else RB.Fork(e1x + 1, em));
                        assert em <= e1x;
                        assert NR.GetPcRE(code, em) == Some(RB.SetQuantToClock(qid, false))
                               && qid in qm.quants && qm.quants[qid] == L.DefGroups(r1);
                        assert AR.NfaRepL(rer, qm, r1, code, em + 1, e1x);
                        assert NUL.NonNullableL(r1)
                               && NR.GetPcRE(code, e1x)
                                  == Some(if greedy then RB.Fork(em, e1x + 1) else RB.Fork(e1x + 1, em))
                               && em <= e1x
                               && (exists qid2: int ::
                                     NR.GetPcRE(code, em) == Some(RB.SetQuantToClock(qid2, false))
                                     && qid2 in qm.quants && qm.quants[qid2] == L.DefGroups(r1))
                               && AR.NfaRepL(rer, qm, r1, code, em + 1, e1x);
                      }
                      ATR.FuelToActionsRepL(rer, qm, cont, code, pcmid, n - 1);
                      var lq := [LS.Areg(q0)] + cont;
                      assert AR.ActionRepL(rer, qm, LS.Areg(q0), code, e1x, e1x + 1);
                      assert lq[0] == LS.Areg(q0) && lq[1..] == cont;
                      assert AR.ActionsRepL(rer, qm, lq, code, e1x);
                      var lc := [LS.Acheck(inp)] + lq;
                      EL.PikeLkActionsRecConsIff(LS.Acheck(inp), lq);
                      assert AR.ActionRepL(rer, qm, LS.Acheck(inp), code, e1x, e1x);
                      assert lc[0] == LS.Acheck(inp) && lc[1..] == lq;
                      assert AR.ActionsRepL(rer, qm, lc, code, e1x);
                      assert AR.ActionRepL(rer, qm, LS.Areg(r1), code, pc + 1, e1x);
                      assert ia == [LS.Areg(r1)] + lc;
                      assert ia[0] == LS.Areg(r1) && ia[1..] == lc;
                      assert AR.ActionsRepL(rer, qm, ia, code, pc + 1);
                      EL.PikeLkActionsRecConsIff(LS.Areg(r1), lc);
                      assert EL.PikeLkActionsRec(ia);
                      ATR.ActionsRepLToFuel(rer, qm, ia, code, pc + 1);
                      var ni: nat :| ATR.ActionsRepFuelL(rer, qm, ia, code, pc + 1, ni);
                      WO.WalkOkQuantSeam(acts, code, pc, ATR.EaOf(b), greedy, r1, inp);
                      assert CE.PSize(t1ck) == CE.PSize(tc);
                      assert CE.PSize(t1ck) < CE.PSize(t);
                      var sub := ActionsTreeRepLkFRec(rer, qm, ia, code, pc + 1, inp, b, t1ck, ni);
                      tcan := LT.GroupActionT(g, sub);
                      // erasure: ProgErase(sub) == ProgErase(t1ck) == ProgErase(tc)
                      // (BoolCheckInsert's insertion is Progress-only); tr_reset at pc
                      assert CE.ProgErase(sub) == CE.ProgErase(tc);
                      assert TreeRepLkRE(rer, qm, code, inp, tcan, pc, ATR.EaOf(b));
                    case _ =>
                  }
                }
                }
              case NN(kx) =>
                var em := AR.NfaRepLQuantInv(rer, qm, greedy, min, kx, r1, code, pc, pcmid);
                var quant1 := L.Quantified(greedy, min - 1, delta, r1);
                var eb: nat :| (exists qid: int ::
                                  NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(qid, false))
                                  && qid in qm.quants && qm.quants[qid] == gidl)
                               && AR.NfaRepL(rer, qm, r1, code, pc + 1, eb)
                               && AR.NfaRepMinL(rer, qm, min - 1, r1, code, eb, em);
                AR.NfaRepLQuantIntro(rer, qm, greedy, min - 1, kx, r1, code, eb, em, pcmid);
                assert AR.NfaRepL(rer, qm, quant1, code, eb, pcmid);
                match t {
                  case GroupActionT(g, tc) =>
                    assert g == LG.Reset(gidl);
                    EL.PikeLkActionsRecConsIff(LS.Areg(quant1), cont);
                    EL.PikeLkActionsRecConsIff(LS.Areg(r1), [LS.Areg(quant1)] + cont);
                    ATR.FuelToActionsRepL(rer, qm, cont, code, pcmid, n - 1);
                    assert AR.ActionRepL(rer, qm, LS.Areg(quant1), code, eb, pcmid);
                    var lq1 := [LS.Areg(quant1)] + cont;
                    assert lq1[0] == LS.Areg(quant1) && lq1[1..] == cont;
                    assert AR.ActionsRepL(rer, qm, lq1, code, eb);
                    var ia := [LS.Areg(r1)] + lq1;
                    assert AR.ActionRepL(rer, qm, LS.Areg(r1), code, pc + 1, eb);
                    assert ia[0] == LS.Areg(r1) && ia[1..] == lq1;
                    assert AR.ActionsRepL(rer, qm, ia, code, pc + 1);
                    assert ia == [LS.Areg(r1), LS.Areg(quant1)] + cont;
                    ATR.ActionsRepLToFuel(rer, qm, ia, code, pc + 1);
                    var ni: nat :| ATR.ActionsRepFuelL(rer, qm, ia, code, pc + 1, ni);
                    WO.WalkOkQuantForced(acts, code, pc, ATR.EaOf(b), greedy, min, delta, r1);
                    assert CE.PSize(tc) < CE.PSize(t);
                    var sub := ActionsTreeRepLkFRec(rer, qm, ia, code, pc + 1, inp, b, tc, ni);
                    tcan := LT.GroupActionT(g, sub);
                    // tr_reset at pc
                    assert TreeRepLkRE(rer, qm, code, inp, tcan, pc, ATR.EaOf(b));
                  case _ =>
                }
            }
            return;
          }
          if delta.NN? {
            var k := delta.n;
            var em := AR.NfaRepLQuantInv(rer, qm, greedy, 0, k, r1, code, pc, pcmid);
            assert em == pc;
            if k == 0 {
              // spent quantifier: transparent, peel
              assert pc == pcmid;
              WO.WalkOkQuantSpent(acts, code, pc, ATR.EaOf(b), greedy, r1);
              assert LS.ActionsRegexSize(cont) < LS.ActionsRegexSize(acts);
              assert ATR.MsizeA(cont) < ATR.MsizeA(acts);
              tcan := ActionsTreeRepLkFRec(rer, qm, cont, code, pcmid, inp, b, t, n - 1);
            } else {
              // one bounded layer: the fork skips to the common end pcmid
              var quant := L.Quantified(greedy, 0, FS.NoiPred(delta), r1);
              assert quant == L.Quantified(greedy, 0, LN.NN(k - 1), r1);
              var e1: nat :| NR.GetPcRE(code, pc) == Some(if greedy then RB.Fork(pc + 1, pcmid) else RB.Fork(pcmid, pc + 1))
                             && (exists qid: int ::
                                   NR.GetPcRE(code, pc + 1) == Some(RB.SetQuantToClock(qid, false))
                                   && qid in qm.quants && qm.quants[qid] == gidl)
                             && NR.GetPcRE(code, pc + 2) == Some(RB.BeginLoop)
                             && AR.NfaRepL(rer, qm, r1, code, pc + 3, e1)
                             && NR.GetPcRE(code, e1) == Some(RB.EndLoop)
                             && AR.NfaRepOptL(rer, qm, k - 1, greedy, r1, code, e1 + 1, pcmid);
              AR.NfaRepIncrL(rer, qm, r1, code, pc + 3, e1);
              AR.NfaRepIncrOptL(rer, qm, k - 1, greedy, r1, code, e1 + 1, pcmid);
              match t {
                case Choice(ta, tb) =>
                  var itert := if greedy then ta else tb;
                  var skipt := if greedy then tb else ta;
                  match itert {
                    case GroupActionT(g, ti) =>
                      assert g == LG.Reset(gidl);
                      WO.WalkOkQuantLayer(acts, code, pc, ATR.EaOf(b), greedy, delta, r1,
                                          if greedy then pc + 1 else pcmid,
                                          if greedy then pcmid else pc + 1, inp);
                      // skip branch: cont at the common end pcmid
                      assert CE.PSize(skipt) < CE.PSize(t);
                      var subs := ActionsTreeRepLkFRec(rer, qm, cont, code, pcmid, inp, b, skipt, n - 1);
                      // iteration branch at pc+3 with the NN(k-1) continuation at e1+1
                      EL.PikeLkActionsRecConsIff(LS.Areg(quant), cont);
                      EL.PikeLkActionsRecConsIff(LS.Acheck(inp), [LS.Areg(quant)] + cont);
                      EL.PikeLkActionsRecConsIff(LS.Areg(r1), [LS.Acheck(inp)] + ([LS.Areg(quant)] + cont));
                      ATR.FuelToActionsRepL(rer, qm, cont, code, pcmid, n - 1);
                      var lq := [LS.Areg(quant)] + cont;
                      assert AR.NfaRepMinL(rer, qm, 0, r1, code, e1 + 1, e1 + 1);
                      AR.NfaRepLQuantIntro(rer, qm, greedy, 0, k - 1, r1, code, e1 + 1, e1 + 1, pcmid);
                      assert AR.ActionRepL(rer, qm, LS.Areg(quant), code, e1 + 1, pcmid);
                      assert lq[0] == LS.Areg(quant) && lq[1..] == cont;
                      assert AR.ActionsRepL(rer, qm, lq, code, e1 + 1);
                      var lc := [LS.Acheck(inp)] + lq;
                      assert AR.ActionRepL(rer, qm, LS.Acheck(inp), code, e1, e1 + 1);
                      assert lc[0] == LS.Acheck(inp) && lc[1..] == lq;
                      assert AR.ActionsRepL(rer, qm, lc, code, e1);
                      var ia := [LS.Areg(r1)] + lc;
                      assert AR.ActionRepL(rer, qm, LS.Areg(r1), code, pc + 3, e1);
                      assert ia[0] == LS.Areg(r1) && ia[1..] == lc;
                      assert AR.ActionsRepL(rer, qm, ia, code, pc + 3);
                      assert ia == [LS.Areg(r1), LS.Acheck(inp), LS.Areg(quant)] + cont;
                      ATR.ActionsRepLToFuel(rer, qm, ia, code, pc + 3);
                      var ni: nat :| ATR.ActionsRepFuelL(rer, qm, ia, code, pc + 3, ni);
                      assert CE.PSize(ti) < CE.PSize(t);
                      var subi := ActionsTreeRepLkFRec(rer, qm, ia, code, pc + 3, inp, BS.CannotExit, ti, ni);
                      // assemble: subi at pc+3 (false) -> tr_begin at pc+2 ->
                      // tr_reset at pc+1 -> tr_choice with the skip at pcmid
                      assert TreeRepLkRE(rer, qm, code, inp, subi, pc + 3, false);
                      assert TreeRepLkRE(rer, qm, code, inp, subi, pc + 2, ATR.EaOf(b));
                      var iterstar := LT.GroupActionT(g, subi);
                      assert TreeRepLkRE(rer, qm, code, inp, iterstar, pc + 1, ATR.EaOf(b));
                      tcan := if greedy then LT.Choice(iterstar, subs) else LT.Choice(subs, iterstar);
                      assert TreeRepLkRE(rer, qm, code, inp, tcan, pc, ATR.EaOf(b));
                      assert CE.ProgErase(iterstar) == CE.ProgErase(itert);
                      assert CE.ProgErase(tcan) == CE.ProgErase(t);
                    case _ =>
                  }
                case _ =>
              }
            }
            return;
          }
          assert min == 0 && delta == LN.Inf;
          var quant := L.Quantified(greedy, 0, FS.NoiPred(delta), r1);
          assert quant == L.Quantified(greedy, 0, LN.Inf, r1) == L.Quantified(greedy, min, delta, r1);
          if exists e1: nat :: NR.GetPcRE(code, pc) == Some(if greedy then RB.Fork(pc + 1, e1 + 2) else RB.Fork(e1 + 2, pc + 1))
                               && (exists qid: int ::
                                     NR.GetPcRE(code, pc + 1) == Some(RB.SetQuantToClock(qid, false))
                                     && qid in qm.quants && qm.quants[qid] == gidl)
                               && NR.GetPcRE(code, pc + 2) == Some(RB.BeginLoop)
                               && AR.NfaRepL(rer, qm, r1, code, pc + 3, e1)
                               && NR.GetPcRE(code, e1) == Some(RB.EndLoop)
                               && NR.GetPcRE(code, e1 + 1) == Some(RB.Jmp(pc))
                               && pcmid == e1 + 2 {
            // the star FAST PATH (forward decision point)
            var e1: nat :| NR.GetPcRE(code, pc) == Some(if greedy then RB.Fork(pc + 1, e1 + 2) else RB.Fork(e1 + 2, pc + 1))
                           && (exists qid: int ::
                                 NR.GetPcRE(code, pc + 1) == Some(RB.SetQuantToClock(qid, false))
                                 && qid in qm.quants && qm.quants[qid] == gidl)
                           && NR.GetPcRE(code, pc + 2) == Some(RB.BeginLoop)
                           && AR.NfaRepL(rer, qm, r1, code, pc + 3, e1)
                           && NR.GetPcRE(code, e1) == Some(RB.EndLoop)
                           && NR.GetPcRE(code, e1 + 1) == Some(RB.Jmp(pc))
                           && pcmid == e1 + 2;
            AR.NfaRepIncrL(rer, qm, r1, code, pc + 3, e1);
            match t {
              case Choice(ta, tb) =>
                var itert := if greedy then ta else tb;
                var skipt := if greedy then tb else ta;
                match itert {
                  case GroupActionT(g, ti) =>
                    assert g == LG.Reset(gidl);
                    WO.WalkOkQuantLayer(acts, code, pc, ATR.EaOf(b), greedy, delta, r1,
                                        if greedy then pc + 1 else pcmid,
                                        if greedy then pcmid else pc + 1, inp);
                    // skip branch at pcmid == e1+2
                    assert CE.PSize(skipt) < CE.PSize(t);
                    var subs := ActionsTreeRepLkFRec(rer, qm, cont, code, pcmid, inp, b, skipt, n - 1);
                    // iteration branch: [Areg r1, Acheck inp, Areg quant] + cont at pc+3
                    EL.PikeLkActionsRecConsIff(LS.Areg(quant), cont);
                    EL.PikeLkActionsRecConsIff(LS.Acheck(inp), [LS.Areg(quant)] + cont);
                    EL.PikeLkActionsRecConsIff(LS.Areg(r1), [LS.Acheck(inp)] + ([LS.Areg(quant)] + cont));
                    ATR.FuelToActionsRepL(rer, qm, cont, code, pcmid, n - 1);
                    var lq := [LS.Areg(quant)] + cont;
                    assert AR.ActionRepL(rer, qm, LS.Areg(quant), code, pc, pcmid);
                    assert lq[0] == LS.Areg(quant) && lq[1..] == cont;
                    assert AR.ActionsRepL(rer, qm, lq, code, pc);
                    AR.ActionsRepLJmp(rer, qm, lq, code, e1 + 1, pc);
                    var lc := [LS.Acheck(inp)] + lq;
                    assert AR.ActionRepL(rer, qm, LS.Acheck(inp), code, e1, e1 + 1);
                    assert lc[0] == LS.Acheck(inp) && lc[1..] == lq;
                    assert AR.ActionsRepL(rer, qm, lc, code, e1);
                    var ia := [LS.Areg(r1)] + lc;
                    assert AR.ActionRepL(rer, qm, LS.Areg(r1), code, pc + 3, e1);
                    assert ia[0] == LS.Areg(r1) && ia[1..] == lc;
                    assert AR.ActionsRepL(rer, qm, ia, code, pc + 3);
                    assert ia == [LS.Areg(r1), LS.Acheck(inp), LS.Areg(quant)] + cont;
                    ATR.ActionsRepLToFuel(rer, qm, ia, code, pc + 3);
                    var ni: nat :| ATR.ActionsRepFuelL(rer, qm, ia, code, pc + 3, ni);
                    assert CE.PSize(ti) < CE.PSize(t);
                    var subi := ActionsTreeRepLkFRec(rer, qm, ia, code, pc + 3, inp, BS.CannotExit, ti, ni);
                    // assemble: tr_begin at pc+2, tr_reset at pc+1, tr_choice at pc
                    assert TreeRepLkRE(rer, qm, code, inp, subi, pc + 3, false);
                    assert TreeRepLkRE(rer, qm, code, inp, subi, pc + 2, ATR.EaOf(b));
                    var iterstar := LT.GroupActionT(g, subi);
                    assert TreeRepLkRE(rer, qm, code, inp, iterstar, pc + 1, ATR.EaOf(b));
                    tcan := if greedy then LT.Choice(iterstar, subs) else LT.Choice(subs, iterstar);
                    assert TreeRepLkRE(rer, qm, code, inp, tcan, pc, ATR.EaOf(b));
                    assert CE.ProgErase(iterstar) == CE.ProgErase(itert);
                    assert CE.ProgErase(tcan) == CE.ProgErase(t);
                  case _ =>
                }
              case _ =>
            }
          } else {
            // the LOOP VIEW: a bare star at the do-while's backward fork.
            // WalkOk pins the flag to CanExit; the fused fork lemma builds the
            // Choice and tr_plus consumes the PLANTED Progress with the fork.
            assert NUL.NonNullableL(r1);
            var em: nat :| NR.GetPcRE(code, pc) == Some(if greedy then RB.Fork(em, pc + 1) else RB.Fork(pc + 1, em))
                           && em <= pc
                           && (exists qid: int ::
                                 NR.GetPcRE(code, em) == Some(RB.SetQuantToClock(qid, false))
                                 && qid in qm.quants && qm.quants[qid] == gidl)
                           && AR.NfaRepL(rer, qm, r1, code, em + 1, pc)
                           && pcmid == pc + 1;
            WO.WalkOkLoopView(acts, code, pc, ATR.EaOf(b), greedy, LN.Inf, r1,
                              if greedy then em else pc + 1,
                              if greedy then pc + 1 else em, inp);
            assert ATR.EaOf(b) == true;
            assert b == BS.CanExit;
            assert AR.BackForkAt(code, pc);
            var sub := AtBackForkTreeLkFRec(rer, qm, acts, code, pc, inp, t, n);
            tcan := LT.Progress(sub);
            assert TreeRepLkRE(rer, qm, code, inp, tcan, pc, ATR.EaOf(b));
          }
        }
        case Group(gid, r1) => {
          assert {:split_here} true;   // (E3) one assertion batch per arm
          EL.PikeLkActionsRecConsIff(LS.Aclose(gid), cont);
          EL.PikeLkActionsRecConsIff(LS.Areg(r1), [LS.Aclose(gid)] + cont);
          var e1: nat :| NR.GetPcRE(code, pc) == Some(RB.SetRegisterToCP(CP.start_reg(gid as int)))
                         && AR.NfaRepL(rer, qm, r1, code, pc + 1, e1)
                         && NR.GetPcRE(code, e1) == Some(RB.SetRegisterToCP(CP.end_reg(gid as int)))
                         && pcmid == e1 + 1;
          match t {
            case GroupActionT(g, tc) =>
              assert g == LG.Open(gid);
              WO.WalkOkGroup(acts, code, pc, ATR.EaOf(b), gid, r1);
              var lc := [LS.Aclose(gid)] + cont;
              assert AR.ActionRepL(rer, qm, LS.Aclose(gid), code, e1, e1 + 1);
              assert lc[0] == LS.Aclose(gid) && lc[1..] == cont;
              ATR.FuelToActionsRepL(rer, qm, cont, code, pcmid, n - 1);
              assert AR.ActionsRepL(rer, qm, lc, code, e1);
              var ga := [LS.Areg(r1)] + lc;
              assert AR.ActionRepL(rer, qm, LS.Areg(r1), code, pc + 1, e1);
              assert ga[0] == LS.Areg(r1) && ga[1..] == lc;
              assert AR.ActionsRepL(rer, qm, ga, code, pc + 1);
              assert ga == [LS.Areg(r1), LS.Aclose(gid)] + cont;
              ATR.ActionsRepLToFuel(rer, qm, ga, code, pc + 1);
              var ng: nat :| ATR.ActionsRepFuelL(rer, qm, ga, code, pc + 1, ng);
              assert CE.PSize(tc) < CE.PSize(t);
              var sub := ActionsTreeRepLkFRec(rer, qm, ga, code, pc + 1, inp, b, tc, ng);
              tcan := LT.GroupActionT(g, sub);
              // tr_open
              assert TreeRepLkRE(rer, qm, code, inp, tcan, pc, ATR.EaOf(b));
            case _ =>
          }
        }
        case AnchorR(la) => {
          assert {:split_here} true;   // (E3) one assertion batch per arm
          var ra: R.anchor :| NR.GetPcRE(code, pc) == Some(RB.AnchorAssertion(ra))
                              && T.TrAnchor(ra) == la;
          if LS.AnchorSatisfied(rer, la, inp) {
            match t {
              case AnchorPass(la2, tc) =>
                assert la2 == la;
                WO.WalkOkAnchor(acts, code, pc, ATR.EaOf(b));
                assert CE.PSize(tc) < CE.PSize(t);
                var sub := ActionsTreeRepLkFRec(rer, qm, cont, code, pc + 1, inp, b, tc, n - 1);
                tcan := LT.AnchorPass(la2, sub);
                // tr_anchorpass (Linden-side satisfaction, anchor pinned via ra)
                assert TreeRepLkRE(rer, qm, code, inp, tcan, pc, ATR.EaOf(b));
              case _ =>
            }
          } else {
            // t == Mismatch; tr_anchorfail via ra
            tcan := LT.Mismatch;
            assert TreeRepLkRE(rer, qm, code, inp, tcan, pc, ATR.EaOf(b));
          }
        }
        case LookaroundR(lk, r1) => {
          assert {:split_here} true;   // (E3) one assertion batch per arm
          // THE GATE. NfaRepL pins the oracle instruction + the looks-table
          // row; TreeRepLkRE's gate rule is decided by the same FUNCTIONAL
          // verdict BoolTreeLk's LkGateOk used — no oracle bit involved. The
          // node is KEPT with the RAW functional body.
          var lid: int :| NR.GetPcRE(code, pc)
                          == Some(if AR.PositiveL(lk) then RB.CheckOracle(lid)
                                                      else RB.NegCheckOracle(lid))
                          && lid in qm.looks && qm.looks[lid] == (lk, r1);
          assert pcmid == pc + 1;
          var tlkc := LFU.ComputeTr(rer, [LS.Areg(r1)], inp, LG.Empty, L.LkDir(lk));
          match t {
            case LK(lk2, tlk, tc) =>
              assert lk2 == lk && tlk == tlkc && LS.LkResult(lk, tlk, LG.Empty, inp).Some?;
              WO.WalkOkLookaround(acts, code, pc, ATR.EaOf(b));
              assert CE.PSize(tc) < CE.PSize(t);
              var sub := ActionsTreeRepLkFRec(rer, qm, cont, code, pc + 1, inp, b, tc, n - 1);
              tcan := LT.LK(lk, tlkc, sub);
              // tr_lk
              assert TreeRepLkRE(rer, qm, code, inp, tcan, pc, ATR.EaOf(b));
            case LKFail(lk2, tlk) =>
              assert lk2 == lk && tlk == tlkc && LS.LkResult(lk, tlk, LG.Empty, inp).None?;
              // tr_lkfail: direct, no recursion
              tcan := LT.LKFail(lk, tlkc);
              assert TreeRepLkRE(rer, qm, code, inp, tcan, pc, ATR.EaOf(b));
            case _ =>
          }
        }
        case Backreference(gid) =>   // not pike
          assert {:split_here} true;   // (E3) one assertion batch per arm
    }
  }

  lemma {:isolate_assertions} AtBackForkTreeLkFRec(rer: LW.RegExpRecord, qm: AR.QMap, acts: LS.Actions, code: RB.code,
                             pc: nat, inp: LC.Input, tc: LT.Tree, n: nat)
    returns (tcstar: LT.Tree)
    requires EL.PikeLkActionsRec(acts)
    requires ATR.ActionsRepFuelL(rer, qm, acts, code, pc, n)
    requires WO.WalkOk(acts, code, pc, true)
    requires EL.BoolTreeLk(rer, acts, inp, BS.CanExit, tc)
    requires AR.BackForkAt(code, pc)
    ensures TreeRepLkRE(rer, qm, code, inp, LT.Progress(tcstar), pc, true)
    ensures CE.ProgErase(tcstar) == CE.ProgErase(tc)
    decreases CE.PSize(tc), ATR.MsizeA(acts), n, 0
  {
    // (§2.5b) the new recursive nullability predicates' definitional axioms send
    // z3 4.14 into a matching loop on otherwise-trivial goals in the quant arms;
    // every use here is opaque (guards + lemma calls), so hide them.
    hide NUL.NonNullableL, NUL.CINullableL, NUL.NoNulledPlusL, AR.NfaRepCinL;
    var fx: int, fy: int :| NR.GetPcRE(code, pc) == Some(RB.Fork(fx, fy))
                            && fx >= 0 && fy >= 0 && (fx as nat <= pc || fy as nat <= pc);
    assert |acts| > 0;
    var cont := acts[1..];
    var pcmid: nat :| AR.ActionRepL(rer, qm, acts[0], code, pc, pcmid)
                      && ATR.ActionsRepFuelL(rer, qm, cont, code, pcmid, n - 1);
    EL.PikeLkActionsRecTail(acts);
    assert acts == [acts[0]] + cont;
    EL.PikeLkActionsRecConsIff(acts[0], cont);
    match acts[0]
    case Acheck(strcheck) =>
      // a stacked check: zero-width at the fork; its Progress collapses into
      // the single planted guard
      assert pcmid == pc;
      assert LS.ActionsRegexSize(acts) == LS.ActionsRegexSize(cont);
      match tc {
        case Progress(tc2) =>
          WO.WalkOkAcheckBackFork(acts, code, pc, true);
          tcstar := AtBackForkTreeLkFRec(rer, qm, cont, code, pc, inp, tc2, n - 1);
          assert CE.ProgErase(tc) == CE.ProgErase(tc2);
        case _ =>
      }
    case Aclose(gid) =>
      assert false;   // SetRegisterToCP != Fork
    case Areg(r) =>
      assert EL.PikeLkRegexRec(r);
      match r
      case Epsilon =>
        assert pcmid == pc;
        WO.WalkOkEpsilon(acts, code, pc, true);
        assert ATR.MsizeA(cont) < ATR.MsizeA(acts);
        tcstar := AtBackForkTreeLkFRec(rer, qm, cont, code, pc, inp, tc, n - 1);
      case Character(cd) =>
        var ce :| NR.GetPcRE(code, pc) == Some(RB.Consume(ce)) && AR.ExpectationMatches(rer, ce, cd);
        assert false;   // Consume != Fork
      case AnchorR(la) =>
        var ra: R.anchor :| NR.GetPcRE(code, pc) == Some(RB.AnchorAssertion(ra)) && T.TrAnchor(ra) == la;
        assert false;   // AnchorAssertion != Fork
      case Disjunction(r1, r2) =>
        var e1: nat :| NR.GetPcRE(code, pc) == Some(RB.Fork(pc + 1, e1 + 1))
                       && AR.NfaRepL(rer, qm, r1, code, pc + 1, e1)
                       && NR.GetPcRE(code, e1) == Some(RB.Jmp(pcmid))
                       && AR.NfaRepL(rer, qm, r2, code, e1 + 1, pcmid);
        AR.NfaRepIncrL(rer, qm, r1, code, pc + 1, e1);
        assert false;   // both arms forward: contradicts the backward arm
      case Sequence(r1, r2) =>
        EL.PikeLkActionsRecConsIff(LS.Areg(r2), cont);
        EL.PikeLkActionsRecConsIff(LS.Areg(r1), [LS.Areg(r2)] + cont);
        assert AR.NfaRepL(rer, qm, L.Sequence(r1, r2), code, pc, pcmid);
        var e1: nat :| AR.NfaRepL(rer, qm, r1, code, pc, e1) && AR.NfaRepL(rer, qm, r2, code, e1, pcmid);
        var na := [LS.Areg(r1), LS.Areg(r2)] + cont;
        assert na == [LS.Areg(r1)] + ([LS.Areg(r2)] + cont);
        assert AR.ActionRepL(rer, qm, LS.Areg(r2), code, e1, pcmid);
        assert ([LS.Areg(r2)] + cont)[0] == LS.Areg(r2) && ([LS.Areg(r2)] + cont)[1..] == cont;
        ATR.FuelToActionsRepL(rer, qm, cont, code, pcmid, n - 1);
        assert AR.ActionsRepL(rer, qm, [LS.Areg(r2)] + cont, code, e1);
        assert AR.ActionRepL(rer, qm, LS.Areg(r1), code, pc, e1);
        assert na[0] == LS.Areg(r1) && na[1..] == [LS.Areg(r2)] + cont;
        assert AR.ActionsRepL(rer, qm, na, code, pc);
        assert LS.ActionsRegexSize(na) < LS.ActionsRegexSize(acts);
        assert ATR.MsizeA(na) < ATR.MsizeA(acts);
        ATR.ActionsRepLToFuel(rer, qm, na, code, pc);
        var nn: nat :| ATR.ActionsRepFuelL(rer, qm, na, code, pc, nn);
        WO.WalkOkSeq(acts, code, pc, true, r1, r2);
        tcstar := AtBackForkTreeLkFRec(rer, qm, na, code, pc, inp, tc, nn);
      case Quantified(greedy, min, delta, r1) =>
        var gidl := L.DefGroups(r1);
        if min > 0 {
          match delta {
            case Inf =>
              if NUL.NonNullableL(r1) {
                var em, e1x := AR.NfaRepLPlusInv(rer, qm, greedy, min, r1, code, pc, pcmid);
                if em == pc {
                  assert false;    // SetQuantToClock != Fork
                } else {
                  var eb: nat :| (exists qid: int ::
                                    NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(qid, false))
                                    && qid in qm.quants && qm.quants[qid] == gidl)
                                 && AR.NfaRepL(rer, qm, r1, code, pc + 1, eb)
                                 && AR.NfaRepMinL(rer, qm, min - 2, r1, code, eb, em);
                  assert false;    // SetQuantToClock != Fork
                }
              } else {
                // §2.5a GENERIC: min >= 1 forced copies, so `pc` still carries a
                // clock-mark -- refuted against the pinned Fork just the same
                assert !greedy by {            // §2.5b interim (PikeLk conjunct)
                  assert acts[0] == LS.Areg(L.Quantified(greedy, min, delta, r1));
                }
                var em, e1x := AR.NfaRepLGenInv(rer, qm, greedy, min, r1, code, pc, pcmid);
                var eb: nat :| (exists qid: int ::
                                  NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(qid, false))
                                  && qid in qm.quants && qm.quants[qid] == gidl)
                               && AR.NfaRepL(rer, qm, r1, code, pc + 1, eb)
                               && AR.NfaRepMinL(rer, qm, min - 1, r1, code, eb, em);
                assert false;    // SetQuantToClock != Fork
              }
            case NN(kx) =>
              var em := AR.NfaRepLQuantInv(rer, qm, greedy, min, kx, r1, code, pc, pcmid);
              var eb: nat :| (exists qid: int ::
                                NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(qid, false))
                                && qid in qm.quants && qm.quants[qid] == gidl)
                             && AR.NfaRepL(rer, qm, r1, code, pc + 1, eb)
                             && AR.NfaRepMinL(rer, qm, min - 1, r1, code, eb, em);
              assert false;      // SetQuantToClock != Fork
          }
        } else if delta.NN? {
          var k := delta.n;
          var em := AR.NfaRepLQuantInv(rer, qm, greedy, 0, k, r1, code, pc, pcmid);
          assert em == pc;
          if k == 0 {
            assert pc == pcmid;
            WO.WalkOkQuantSpent(acts, code, pc, true, greedy, r1);
            assert LS.ActionsRegexSize(cont) < LS.ActionsRegexSize(acts);
            assert ATR.MsizeA(cont) < ATR.MsizeA(acts);
            tcstar := AtBackForkTreeLkFRec(rer, qm, cont, code, pc, inp, tc, n - 1);
          } else {
            var e1: nat :| NR.GetPcRE(code, pc) == Some(if greedy then RB.Fork(pc + 1, pcmid) else RB.Fork(pcmid, pc + 1))
                           && (exists qid: int ::
                                 NR.GetPcRE(code, pc + 1) == Some(RB.SetQuantToClock(qid, false))
                                 && qid in qm.quants && qm.quants[qid] == gidl)
                           && NR.GetPcRE(code, pc + 2) == Some(RB.BeginLoop)
                           && AR.NfaRepL(rer, qm, r1, code, pc + 3, e1)
                           && NR.GetPcRE(code, e1) == Some(RB.EndLoop)
                           && AR.NfaRepOptL(rer, qm, k - 1, greedy, r1, code, e1 + 1, pcmid);
            AR.NfaRepIncrL(rer, qm, r1, code, pc + 3, e1);
            AR.NfaRepIncrOptL(rer, qm, k - 1, greedy, r1, code, e1 + 1, pcmid);
            assert false;   // a bounded layer pins a FORWARD fork
          }
        } else {
          assert min == 0 && delta == LN.Inf;
          if exists e1: nat :: NR.GetPcRE(code, pc) == Some(if greedy then RB.Fork(pc + 1, e1 + 2) else RB.Fork(e1 + 2, pc + 1))
                               && (exists qid: int ::
                                     NR.GetPcRE(code, pc + 1) == Some(RB.SetQuantToClock(qid, false))
                                     && qid in qm.quants && qm.quants[qid] == gidl)
                               && NR.GetPcRE(code, pc + 2) == Some(RB.BeginLoop)
                               && AR.NfaRepL(rer, qm, r1, code, pc + 3, e1)
                               && NR.GetPcRE(code, e1) == Some(RB.EndLoop)
                               && NR.GetPcRE(code, e1 + 1) == Some(RB.Jmp(pc))
                               && pcmid == e1 + 2 {
            var e1: nat :| NR.GetPcRE(code, pc) == Some(if greedy then RB.Fork(pc + 1, e1 + 2) else RB.Fork(e1 + 2, pc + 1))
                           && AR.NfaRepL(rer, qm, r1, code, pc + 3, e1)
                           && pcmid == e1 + 2;
            AR.NfaRepIncrL(rer, qm, r1, code, pc + 3, e1);
            assert false;   // the fast path pins a forward fork
          } else {
            // THE LOOP VIEW: the star seen from the fork itself
            assert NUL.NonNullableL(r1);
            var em: nat :| NR.GetPcRE(code, pc) == Some(if greedy then RB.Fork(em, pc + 1) else RB.Fork(pc + 1, em))
                           && em <= pc
                           && (exists qid: int ::
                                 NR.GetPcRE(code, em) == Some(RB.SetQuantToClock(qid, false))
                                 && qid in qm.quants && qm.quants[qid] == gidl)
                           && AR.NfaRepL(rer, qm, r1, code, em + 1, pc)
                           && pcmid == pc + 1;
            var qid: int :| NR.GetPcRE(code, em) == Some(RB.SetQuantToClock(qid, false))
                            && qid in qm.quants && qm.quants[qid] == gidl;
            var q0 := L.Quantified(greedy, 0, FS.NoiPred(delta), r1);
            assert q0 == L.Quantified(greedy, 0, LN.Inf, r1) == r;
            WO.WalkOkLoopView(acts, code, pc, true, greedy, LN.Inf, r1,
                              if greedy then em else pc + 1,
                              if greedy then pc + 1 else em, inp);
            match tc {
              case Choice(cta, ctb) =>
                var itert := if greedy then cta else ctb;
                var skipt := if greedy then ctb else cta;
                match itert {
                  case GroupActionT(g, ti) =>
                    assert g == LG.Reset(gidl);
                    var il := [LS.Areg(r1), LS.Acheck(inp), LS.Areg(q0)] + cont;
                    assert EL.BoolTreeLk(rer, il, inp, BS.CannotExit, ti);
                    // skip branch: the general construction at the exit arm
                    assert CE.PSize(skipt) < CE.PSize(tc);
                    // (§2.5b/z3 4.14) spell the call's preconditions out one by one —
                    // the packed precondition VC grinds past the limit otherwise
                    assert EL.PikeLkActionsRec(cont);
                    assert ATR.ActionsRepFuelL(rer, qm, cont, code, pc + 1, n - 1);
                    assert WO.WalkOk(cont, code, pc + 1, ATR.EaOf(BS.CanExit));
                    assert EL.BoolTreeLk(rer, cont, inp, BS.CanExit, skipt);
                    var subs := ActionsTreeRepLkFRec(rer, qm, cont, code, pc + 1, inp, BS.CanExit, skipt, n - 1);
                    // iteration branch: lift to CanExit, then bridge
                    EL.PikeLkActionsRecConsIff(LS.Areg(q0), cont);
                    EL.PikeLkActionsRecConsIff(LS.Acheck(inp), [LS.Areg(q0)] + cont);
                    EL.PikeLkActionsRecConsIff(LS.Areg(r1), [LS.Acheck(inp)] + ([LS.Areg(q0)] + cont));
                    assert il == [LS.Areg(r1)] + ([LS.Acheck(inp)] + ([LS.Areg(q0)] + cont)) by {
                      hide *;   // (§2.5b) pure seq-concat; the ambient axioms drown z3 4.14
                    }
                    assert EL.PikeLkActionsRec(il);
                    assert CE.ShieldedActs(il) by {
                      forall i | 0 <= i < |il| && il[i].Acheck?
                        ensures exists j :: 0 <= j < i && il[j].Areg? && NUL.NonNullableL(il[j].r)
                      {
                        assert il[0] == LS.Areg(r1);
                        assert i > 0;
                        assert il[0].Areg? && NUL.NonNullableL(il[0].r);
                      }
                    }
                    CE.BoolFlagLiftRec(rer, il, inp, ti);
                    assert EL.BoolTreeLk(rer, il, inp, BS.CanExit, ti);
                    // representation of the iteration list at em+1
                    ATR.FuelToActionsRepL(rer, qm, cont, code, pcmid, n - 1);
                    var lq := [LS.Areg(q0)] + cont;
                    assert AR.NfaRepL(rer, qm, q0, code, pc, pc + 1) by {
                      assert NUL.NonNullableL(r1)
                             && NR.GetPcRE(code, pc)
                                == Some(if greedy then RB.Fork(em, pc + 1) else RB.Fork(pc + 1, em))
                             && em <= pc
                             && (exists qid2: int ::
                                   NR.GetPcRE(code, em) == Some(RB.SetQuantToClock(qid2, false))
                                   && qid2 in qm.quants && qm.quants[qid2] == L.DefGroups(r1))
                             && AR.NfaRepL(rer, qm, r1, code, em + 1, pc);
                    }
                    assert AR.ActionRepL(rer, qm, LS.Areg(q0), code, pc, pc + 1);
                    assert lq[0] == LS.Areg(q0) && lq[1..] == cont;
                    assert AR.ActionsRepL(rer, qm, lq, code, pc);
                    var lc := [LS.Acheck(inp)] + lq;
                    assert AR.ActionRepL(rer, qm, LS.Acheck(inp), code, pc, pc);
                    assert lc[0] == LS.Acheck(inp) && lc[1..] == lq;
                    assert AR.ActionsRepL(rer, qm, lc, code, pc);
                    assert AR.ActionRepL(rer, qm, LS.Areg(r1), code, em + 1, pc);
                    assert il == [LS.Areg(r1)] + lc;
                    assert il[0] == LS.Areg(r1) && il[1..] == lc;
                    assert AR.ActionsRepL(rer, qm, il, code, em + 1);
                    ATR.ActionsRepLToFuel(rer, qm, il, code, em + 1);
                    var ni: nat :| ATR.ActionsRepFuelL(rer, qm, il, code, em + 1, ni);
                    assert CE.PSize(ti) < CE.PSize(tc);
                    var subi := ActionsTreeRepLkFRec(rer, qm, il, code, em + 1, inp, BS.CanExit, ti, ni);
                    // assemble: tr_reset at the stamp, then tr_plus at the
                    // fork — arms at (em, true)/(pc+1, true), the planted
                    // Progress consumed with the Choice
                    assert TreeRepLkRE(rer, qm, code, inp, subi, em + 1, true);
                    var iterstar := LT.GroupActionT(g, subi);
                    assert TreeRepLkRE(rer, qm, code, inp, iterstar, em, true);
                    tcstar := if greedy then LT.Choice(iterstar, subs) else LT.Choice(subs, iterstar);
                    assert TreeRepLkRE(rer, qm, code, inp, LT.Progress(tcstar), pc, true);
                    assert CE.ProgErase(iterstar) == CE.ProgErase(itert);
                    assert CE.ProgErase(tcstar) == CE.ProgErase(tc);
                  case _ =>
                }
              case _ =>
            }
          }
        }
      case Group(gid, r1) =>
        var e1: nat :| NR.GetPcRE(code, pc) == Some(RB.SetRegisterToCP(CP.start_reg(gid as int)))
                       && AR.NfaRepL(rer, qm, r1, code, pc + 1, e1)
                       && NR.GetPcRE(code, e1) == Some(RB.SetRegisterToCP(CP.end_reg(gid as int)))
                       && pcmid == e1 + 1;
        assert false;   // SetRegisterToCP != Fork
      case LookaroundR(lk, r1) =>
        var lid: int :| NR.GetPcRE(code, pc)
                        == Some(if AR.PositiveL(lk) then RB.CheckOracle(lid)
                                                    else RB.NegCheckOracle(lid))
                        && lid in qm.looks && qm.looks[lid] == (lk, r1);
        assert false;   // CheckOracle/NegCheckOracle != Fork
      case Backreference(_) =>     // not pike
  }

  /** (BRICK D5) The (E4) INSIDE-look coverage VACATOR for the gate-pass preserver.
      The FRESH body match of a nested positive-lookAHEAD body records NONE of its
      INNER-look capture groups (a lookaround compiles to a single `CheckOracle`
      leaf, so the body's MAIN pass never writes inner-look captures), so those
      groups are ABSENT from `GmOfLive(body, rf)`. Proof: the body's main pass
      writes only OUTSIDE-look capture registers (`M.MainMatchInsideCapsInitNested`),
      leaving the inside-look start clocks at their `-1` init (`PIV.LooksCapUnset`,
      via the outside/inside register PARITY), and `PIV.GmOfLiveInsideLookAbsent`
      then drops each such group. The `FInitState` preconditions of
      `M.FFindMatchThreadFacts` (for `CapRegWf`) + `M.MainMatchInsideCapsInitNested`
      are discharged verbatim off the fresh-entry VM (mirror
      `LookNestOkTFromBodyReplay` / `L3aEndpointAssembly`). This complements
      `M.LkReplayMatchesSpecNested` (which covers the OUTER groups
      `DefGroups(tr) \ LkBodyGroups(tr)`) to close the WHOLE `CapIds(body)` in the
      backward (E4) crossing arm. */
  lemma FreshBodyMatchGmOuter(
    qm: AR.QMap, body: R.regex, bodycode: RB.code, endl: nat,
    str: string, cp: nat, ov: LOr.OracleView, cdn: LCdn.cdns,
    ncap: int, nlook: int, nquant: int)
    requires PSM.StaticOkNestedRE(qm, body, bodycode, endl)
    requires PSM.SizesOkRE(body, ncap, nlook, nquant)
    requires cp <= |str|
    requires bodycode == CP.compile_to_bytecode(body)
    ensures
      var rf := AI.FFindMatch(bodycode, str,
                              AI.FInitState(bodycode, cp, AReg.init_regs(ncap), AReg.init_regs(nlook),
                                            AReg.init_regs(nquant), 0, AI.cp_context(cp, str, LAnc.Forward)),
                              ov, LAnc.Forward, cdn).0;
      rf.Some? ==>
        forall g: nat :: g in PIV.CapIdsInLooks(body) ==>
                           g !in PIV.GmOfLive(body, rf.value.capture_regs, rf.value.look_regs, rf.value.quant_regs)
  {
    var ctx := AI.cp_context(cp, str, LAnc.Forward);
    var capture := AReg.init_regs(ncap);
    var look := AReg.init_regs(nlook);
    var quant := AReg.init_regs(nquant);
    var vms := AI.FInitState(bodycode, cp, capture, look, quant, 0, ctx);
    assert ctx.nextchar == AI.get_char(str, cp);

    // code shape: every SetQuantToClock has b == false (mirror LookNestOkTFromBodyReplay).
    // (§2.5b) CodeShapeAt lost the !b claim; the gated StampFalseAt carries it,
    // fed by the bundle's NoNulledPlusRE(body).
    forall pc: nat, q: int, b: bool | NR.GetPcRE(bodycode, pc) == Some(RB.SetQuantToClock(q, b))
      ensures !b
    {
      if pc < endl {
        NI.StampFalseAt(body, bodycode, 0, endl, pc);
      } else if pc == endl {
      } else {
        assert pc >= |bodycode|;
      }
    }

    // fresh-entry engine facts: winning-thread register wf + quant-final.
    CM.RegsClocksLEInit(ncap, 0);
    CM.RegsClocksLEInit(nlook, 0);
    CM.RegsClocksLEInit(nquant, 0);
    CM.FInitStateClocksLE(bodycode, cp, capture, look, quant, 0, ctx);
    CM.FInitStateRegsWf(bodycode, cp, ncap, nlook, nquant, 0, ctx);
    assert M.VmQuantFinal(vms) by {
      var th0 := AI.init_thread(capture, look, quant);
      assert M.QuantRegsFinal(th0) by {
        forall k ensures AI.get_idx(quant.a_cp, k) < 0 && AI.get_idx(quant.a_clk, k) >= -1 {
          if 0 <= k < |quant.a_cp| { assert quant.a_cp[k] == -1; }
          if 0 <= k < |quant.a_clk| { assert quant.a_clk[k] == -1; }
        }
      }
      forall t2 | t2 in vms.active ensures M.QuantRegsFinal(t2) { assert t2 == th0; }
    }

    var rf := AI.FFindMatch(bodycode, str, vms, ov, LAnc.Forward, cdn).0;
    M.FFindMatchThreadFacts(bodycode, str, vms, ov, LAnc.Forward, cdn, ncap, nlook, nquant);
    M.MainMatchInsideCapsInitNested(body, bodycode, endl, str, vms, capture, look, quant, ov, cdn, rf);

    if rf.Some? {
      var caps := rf.value.capture_regs;
      var Sc := PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(body));
      assert CM.RegsAgreeOutside(caps, capture, Sc);         // MainMatchInsideCapsInitNested
      assert CM.ThreadRegsWf(rf.value, ncap, nlook, nquant);  // FFindMatchThreadFacts
      assert PIV.CapRegWf(caps);
      PIV.CapIdsLooksDisjoint(body);

      // inside-look start slots are OUTSIDE `Sc` (parity + disjointness), so they
      // remain at their -1 init: LooksCapUnset(body, caps.a_clk).
      assert PIV.LooksCapUnset(body, caps.a_clk) by {
        forall c: nat | c in PIV.CapIdsInLooks(body)
          ensures AI.get_idx(caps.a_clk, CP.start_reg(c)) < 0
        {
          assert CP.start_reg(c as int) !in Sc by {
            if CP.start_reg(c as int) in Sc {
              if CP.start_reg(c as int) in (set cid | cid in PIV.CapIdsOutsideLooks(body) :: CP.start_reg(cid as int)) {
                var cid: nat :| cid in PIV.CapIdsOutsideLooks(body) && CP.start_reg(cid as int) == CP.start_reg(c as int);
                assert cid == c;
                assert c in PIV.CapIdsOutsideLooks(body) * PIV.CapIdsInLooks(body);
              } else {
                var cid: nat :| cid in PIV.CapIdsOutsideLooks(body) && CP.end_reg(cid as int) == CP.start_reg(c as int);
                assert 2 * (cid as int) + 1 == 2 * (c as int);
              }
              assert false;
            }
          }
          assert AI.get_idx(caps.a_clk, CP.start_reg(c as int))
              == AI.get_idx(capture.a_clk, CP.start_reg(c as int));   // RegsAgreeOutside off Sc
          RL.AInitLaws(ncap);                                          // init clock == -1
        }
      }

      forall g: nat | g in PIV.CapIdsInLooks(body)
        ensures g !in PIV.GmOfLive(body, caps, rf.value.look_regs, rf.value.quant_regs)
      {
        PIV.GmOfLiveInsideLookAbsent(body, caps, rf.value.look_regs, rf.value.quant_regs, g);
      }
    }
  }

  // ==========================================================================
  // (L5 F7c-3) The LOOKBEHIND twin of the layer-6 body-replay carriers.
  //
  // NOT a port of the forward carrier: the carrier IS the forward lift
  // simulation of the body, so its lookbehind twin is the FLIP-TRANSPORT of the
  // forward carrier — apply `LookNestBackTFromBodyReplay` to `FXR(body)` over
  // `Reverse(str)` with the mirrored view, the flipped oracle table (F3/F4) and
  // the MIRRORED look tables (`FG.MirrorTables`), then transport every carrier
  // predicate back through T2a (`FG.BackFreshCoreNested`: the backward fresh
  // run is the mirror of the forward fresh run of the flipped body) and F2
  // (`FD.BackBodyGmTieFlip`: the backward leaf is the mirror of the flipped
  // forward leaf), per lid.
  // ==========================================================================

  /** Per-lid fresh-match transport: at a lookbehind lid of `body`, the fresh
      BACKWARD body match on `crv` over `str` and the fresh FORWARD body match on
      `MirrorTables(crv)` over `Reverse(str)` (at the mirrored bank) are T2a
      mirrors of each other, and their `GmOfLive` readouts are raw mirrors. */
  lemma FreshMatchLidFlip(
    rer: LW.RegExpRecord, qm: AR.QMap, body: R.regex, crv: CP.FCompiled, str: string,
    ov: LOr.OracleView, lk: AReg.Regs, lid: nat, ncap: int, nlook: int, nquant: int)
    requires T.TransWf(body) && NR.NestedFragmentRE(body) && NR.NegLooksLookFreeRE(body)
    requires NR.NoNulledPlusRE(body)   // §2.5b interim: all stamps false
    requires FST.LBOnlyLooksRE(body)
    requires PIV.CapUnique(body) && PIV.QuantUnique(body) && LTB.LookUnique(body)
    requires PSM.SizesOkRE(body, ncap, nlook, nquant)
    requires !rer.ignoreCase && !rer.multiline
    requires |ov| == |str| + 1
    requires qm.ov == ov && AR.LmapOk(body, qm) && OE.OracleColsOk(rer, qm, str)
    requires LTB.LookTablesOk(body, crv) && |crv.f_look_types| == |crv.f_look_ast|
    requires lid in LTB.LookIds(body)
    requires M.MatchedPosLA(crv, lk, lid as int)
    requires CM.LookCpsLE(lk, |str|)
    ensures
      var n := |str|;
      var r1 := NI.LookBodyOfRE(body, lid);
      var rf := M.FreshBodyMatch(crv, str, lid as int, lk, ov, ncap, nlook, nquant);
      var rfF := M.FreshBodyMatch(FG.MirrorTables(crv), LC.Reverse(str), lid as int,
                                  MIR.MirrorRegs(lk, n), MIR.MirrorView(ov, n), ncap, nlook, nquant);
      && 0 <= (lid as int) < |crv.f_look_types| && crv.f_look_types[lid].Lookbehind?
      && 0 <= (lid as int) < |crv.f_look_cdns|
      && crv.f_look_ast[lid] == r1 && T.TransWf(r1)
      && M.MatchedPosLA(FG.MirrorTables(crv), MIR.MirrorRegs(lk, n), lid as int)
      && 0 <= AReg.get_cp(lk, lid as int).value <= n
      && AReg.get_cp(MIR.MirrorRegs(lk, n), lid as int).value == n - AReg.get_cp(lk, lid as int).value
      && (rf.Some? <==> rfF.Some?)
      && (rf.Some? ==>
            rfF.value == MIR.MirrorThread(rf.value, n)
            && BGM.GmLeN(PIV.GmOfLive(r1, rf.value.capture_regs, rf.value.look_regs, rf.value.quant_regs), n)
            && PIV.GmOfLive(r1, rfF.value.capture_regs, rfF.value.look_regs, rfF.value.quant_regs)
               == BGM.RawMirrorGm(PIV.GmOfLive(r1, rf.value.capture_regs, rf.value.look_regs,
                                               rf.value.quant_regs), n))
  {
    var n := |str|;
    MIR.ReverseLen(str);
    var rstr := LC.Reverse(str);
    var ov' := MIR.MirrorView(ov, n);
    var crvF := FG.MirrorTables(crv);
    var lkF := MIR.MirrorRegs(lk, n);
    var r1 := NI.LookBodyOfRE(body, lid);
    var l := lid as int;

    // ---- the row and its mirror ----
    FG.LookRowLBOnly(body, crv, lid);
    assert crv.f_look_types[l].Lookbehind?;      // MatchedPosLA: capture_type excludes NegLookbehind
    assert crv.f_look_ast[l] == r1 && M.VBody(crv, l) == r1;
    assert crvF.f_look_types[l] == FR.FlipLkRE(crv.f_look_types[l]) == R.Lookahead;
    assert crvF.f_look_ast[l] == FST.FXR(r1) && M.VBody(crvF, l) == FST.FXR(r1);
    assert crvF.f_look_cdns[l] == LCdn.compile_cdns(FST.FXR(r1));

    // ---- the recorded cp and its mirror ----
    assert AReg.get_cp(lk, l).Some?;
    assert 0 <= l < |lk.a_cp| && lk.a_cp[l] >= 0 by {
      if !(0 <= l < |lk.a_cp|) { assert AReg.get_cp(lk, l) == None; }
      if lk.a_cp[l] < 0 { assert AReg.get_cp(lk, l) == None; }
    }
    assert AI.get_idx(lk.a_cp, l) == lk.a_cp[l];
    assert AI.get_idx(lk.a_cp, l) <= n;                // CM.LookCpsLE(lk, n) at l
    var cp0 := AReg.get_cp(lk, l).value;
    assert cp0 == lk.a_cp[l];
    assert 0 <= cp0 <= n;
    FG.GetCpMirror(lk, n, l);
    assert AReg.get_cp(lkF, l).Some? && AReg.get_cp(lkF, l).value == n - cp0;
    assert M.MatchedPosLA(crvF, lkF, l);
    var cp: nat := cp0;

    // ---- sub-body facts ----
    M.TransWfLookBodyOfRE(body, lid);
    M.CapUniqueLookBodyOfRE(body, lid);
    NI.LookBodyOfFragmentNested(body, lid);
    FG.LookBodySubFactsLB(body, lid);
    assert PSM.SizesOkRE(r1, ncap, nlook, nquant);
    FG.LmapOkLookBody(body, qm, lid);
    FST.FXRStructural(r1);
    FG.NestedCdnsEmpty(r1);
    FG.NestedCdnsEmpty(FST.FXR(r1));
    assert crv.f_look_cdns[l] == [] && crvF.f_look_cdns[l] == [];
    assert MIR.SwapAnchorsCdns([]) == [];

    // ---- unfold both fresh matches ----
    FG.FreshBodyMatchLBUnfold(crv, str, l, lk, ov, r1, ncap, nlook, nquant);
    var bcB := CP.compile_to_bytecode(R.reverse_regex(r1));
    var raB := AI.FFindMatch(bcB, str,
                             AI.FInitState(bcB, cp, AReg.init_regs(ncap), AReg.init_regs(nlook),
                                           AReg.init_regs(nquant), 0, AI.cp_context(cp, str, LAnc.Backward)),
                             ov, LAnc.Backward, []).0;
    assert M.FreshBodyMatch(crv, str, l, lk, ov, ncap, nlook, nquant) == raB;
    var bcF := CP.compile_to_bytecode(FST.FXR(r1));
    var mcp := MIR.Mirror(cp, n);
    assert mcp == n - cp0;
    assert AI.capture_direction(R.Lookahead) == LAnc.Forward;
    assert CP.capture_regex(R.Lookahead, FST.FXR(r1)) == FST.FXR(r1);
    var rfF := AI.FFindMatch(bcF, rstr,
                             AI.FInitState(bcF, mcp, AReg.init_regs(ncap), AReg.init_regs(nlook),
                                           AReg.init_regs(nquant), 0, AI.cp_context(mcp, rstr, LAnc.Forward)),
                             ov', LAnc.Forward, []).0;
    assert M.FreshBodyMatch(crvF, rstr, l, lkF, ov', ncap, nlook, nquant) == rfF;

    // ---- F6 core at r1: rfF == MirrorThread(raB) ----
    NI.NoNulledPlusLookBody(body, lid);   // §2.5b interim: NoNulledPlusRE(r1)
    FG.BackFreshCoreNested(rer, qm, r1, str, cp, ov, [], ncap, nlook, nquant, n);
    assert (raB.None? <==> rfF.None?);
    if raB.Some? {
      assert rfF.Some? && rfF.value == MIR.MirrorThread(raB.value, n);
      var cB := raB.value.capture_regs;
      var cF := rfF.value.capture_regs;
      assert cF == MIR.MirrorRegs(cB, n);
      LBK.BackCapsInRange(cB, cF, n);
      assert forall k :: AI.get_idx(AReg.as_arrays(cB).0, k) <= n by {
        forall k ensures AI.get_idx(cB.a_cp, k) <= n {
          if 0 <= k < |cB.a_cp| { assert -1 <= cB.a_cp[k] <= n; }
        }
      }
      BGM.GmOfLiveMirror(r1, cB, raB.value.look_regs, raB.value.quant_regs, n);
      // the flipped thread's look/quant banks share their CLOCKS with raB's
      PIV.GmOfLiveClkCong(r1, cF, rfF.value.look_regs, raB.value.look_regs,
                          rfF.value.quant_regs, raB.value.quant_regs);
    }
  }

  /** (presence carrier) `LookNestOkTTop` transports back through the flip by
      pure congruence: same top lids, same gids, same clock banks. */
  lemma LookNestOkTTopFlip(body: R.regex, S: set<LG.GroupId>, gmt: LG.GroupMap, th: AI.Thread, n: nat)
    requires LTB.LookUnique(body) && TRM.GmInBounds(gmt, n)
    requires LookNestOkTTop(FST.FXR(body), S, TRM.MirrorGm(gmt, n), MIR.MirrorThread(th, n))
    ensures LookNestOkTTop(body, S, gmt, th)
  {
    var reF := FST.FXR(body);
    var gmtF := TRM.MirrorGm(gmt, n);
    var thF := MIR.MirrorThread(th, n);
    FG.TopLookIdsFXR(body);
    TRM.MirrorGmAt(gmt, n);
    NI.TopLookIdsIn(body);
    forall lid: nat | lid in NI.TopLookIds(body)
                      && (exists g: LG.GroupId :: g in S && g in gmt && g in PIV.CapIds(NI.LookBodyOfRE(body, lid)))
      ensures NI.LookPathPresent(body, th.capture_regs.a_clk, th.quant_regs.a_clk, -1, lid)
              && AI.get_idx(th.look_regs.a_clk, lid as int) >= 0
              && AI.get_idx(th.look_regs.a_clk, lid as int)
                 >= NI.MxAtLidLk(body, th.quant_regs.a_clk, -1, lid)
    {
      assert lid in LTB.LookIds(body);
      FG.LookBodyOfREFXR(body, lid);
      FG.CapIdsFXR(NI.LookBodyOfRE(body, lid));
      assert lid in NI.TopLookIds(reF);
      assert exists g: LG.GroupId :: g in S && g in gmtF && g in PIV.CapIds(NI.LookBodyOfRE(reF, lid));
      assert NI.LookPathPresent(reF, thF.capture_regs.a_clk, thF.quant_regs.a_clk, -1, lid)
             && AI.get_idx(thF.look_regs.a_clk, lid as int) >= 0
             && AI.get_idx(thF.look_regs.a_clk, lid as int)
                >= NI.MxAtLidLk(reF, thF.quant_regs.a_clk, -1, lid);
      assert thF.capture_regs.a_clk == th.capture_regs.a_clk;
      assert thF.quant_regs.a_clk == th.quant_regs.a_clk;
      assert thF.look_regs.a_clk == th.look_regs.a_clk;
      FG.LookPathPresentFXR(body, th.capture_regs.a_clk, th.quant_regs.a_clk, -1, lid);
      FG.MxAtLidLkFXR(body, th.quant_regs.a_clk, -1, lid);
    }
  }

  /** (key carrier, per lid) The `LookNestBackTTop` clause at a top lookbehind
      lid transports back through the flip: the backward fresh match's live
      inner gids are the flipped forward fresh match's (raw mirror, same keys),
      which the flipped carrier puts in the mirrored leaf — same keys as `gmt`. */
  lemma LookNestBackTTopLidFlip(
    rer: LW.RegExpRecord, qm: AR.QMap, body: R.regex, crv: CP.FCompiled, str: string,
    ov: LOr.OracleView, gmt: LG.GroupMap, th: AI.Thread, lid: nat,
    ncap: int, nlook: int, nquant: int)
    requires T.TransWf(body) && NR.NestedFragmentRE(body) && NR.NegLooksLookFreeRE(body)
    requires NR.NoNulledPlusRE(body)   // §2.5b interim: all stamps false
    requires FST.LBOnlyLooksRE(body)
    requires PIV.CapUnique(body) && PIV.QuantUnique(body) && LTB.LookUnique(body)
    requires PSM.SizesOkRE(body, ncap, nlook, nquant)
    requires !rer.ignoreCase && !rer.multiline
    requires |ov| == |str| + 1
    requires qm.ov == ov && AR.LmapOk(body, qm) && OE.OracleColsOk(rer, qm, str)
    requires LTB.LookTablesOk(body, crv) && |crv.f_look_types| == |crv.f_look_ast|
    requires TRM.GmInBounds(gmt, |str|)
    requires CM.LookCpsLE(th.look_regs, |str|)
    requires lid in NI.TopLookIds(body) && lid in LTB.LookIds(body)
    requires M.MatchedPosLA(crv, th.look_regs, lid as int)
    requires NI.LookPathDom(body, AI.get_idx(th.look_regs.a_clk, lid as int), th.quant_regs.a_clk, lid)
    requires LookNestBackTTop(FST.FXR(body), FG.MirrorTables(crv), LC.Reverse(str),
                              MIR.MirrorView(ov, |str|), PIV.CapIdsInLooks(body),
                              TRM.MirrorGm(gmt, |str|), MIR.MirrorThread(th, |str|), ncap, nlook, nquant)
    ensures var rf := M.FreshBodyMatch(crv, str, lid as int, th.look_regs, ov, ncap, nlook, nquant);
            rf.Some? ==>
              forall g: LG.GroupId ::
                g in PIV.CapIdsInLooks(body) && g in PIV.CapIds(NI.LookBodyOfRE(body, lid))
                && g in PIV.GmOfLive(NI.LookBodyOfRE(body, lid), rf.value.capture_regs,
                                     rf.value.look_regs, rf.value.quant_regs)
                ==> g in gmt
  {
    var n := |str|;
    MIR.ReverseLen(str);
    var rstr := LC.Reverse(str);
    var ov' := MIR.MirrorView(ov, n);
    var reF := FST.FXR(body);
    var crvF := FG.MirrorTables(crv);
    var thF := MIR.MirrorThread(th, n);
    var S := PIV.CapIdsInLooks(body);
    var gmtF := TRM.MirrorGm(gmt, n);
    var r1 := NI.LookBodyOfRE(body, lid);
    var l := lid as int;

    FreshMatchLidFlip(rer, qm, body, crv, str, ov, th.look_regs, lid, ncap, nlook, nquant);
    var rf := M.FreshBodyMatch(crv, str, l, th.look_regs, ov, ncap, nlook, nquant);
    var rfF := M.FreshBodyMatch(crvF, rstr, l, thF.look_regs, ov', ncap, nlook, nquant);
    assert thF.look_regs == MIR.MirrorRegs(th.look_regs, n);

    // ---- instantiate the flipped carrier at lid ----
    FG.TopLookIdsFXR(body);
    FG.LookIdsFXR(body);
    assert lid in NI.TopLookIds(reF) && lid in LTB.LookIds(reF);
    assert M.MatchedPosLA(crvF, thF.look_regs, l);
    assert thF.look_regs.a_clk == th.look_regs.a_clk && thF.quant_regs.a_clk == th.quant_regs.a_clk;
    FG.LookPathDomFXR(body, AI.get_idx(th.look_regs.a_clk, l), th.quant_regs.a_clk, lid);
    assert NI.LookPathDom(reF, AI.get_idx(thF.look_regs.a_clk, l), thF.quant_regs.a_clk, lid);
    FG.LookBodyOfREFXR(body, lid);
    assert NI.LookBodyOfRE(reF, lid) == FST.FXR(r1);
    FG.CapIdsFXR(r1);
    assert rfF.Some? ==>
        forall g: LG.GroupId ::
          g in S && g in PIV.CapIds(NI.LookBodyOfRE(reF, lid))
          && g in PIV.GmOfLive(NI.LookBodyOfRE(reF, lid), rfF.value.capture_regs,
                               rfF.value.look_regs, rfF.value.quant_regs)
          ==> g in gmtF;

    if rf.Some? {
      assert rfF.Some?;
      FST.GmOfLiveFXR(r1, rfF.value.capture_regs, rfF.value.look_regs, rfF.value.quant_regs);
      TRM.MirrorGmAt(gmt, n);
      var G := PIV.GmOfLive(r1, rf.value.capture_regs, rf.value.look_regs, rf.value.quant_regs);
      assert PIV.GmOfLive(r1, rfF.value.capture_regs, rfF.value.look_regs, rfF.value.quant_regs)
          == BGM.RawMirrorGm(G, n);
      forall g: LG.GroupId | g in S && g in PIV.CapIds(r1) && g in G
        ensures g in gmt
      {
        assert g in BGM.RawMirrorGm(G, n);
        assert g in PIV.GmOfLive(NI.LookBodyOfRE(reF, lid), rfF.value.capture_regs,
                                 rfF.value.look_regs, rfF.value.quant_regs);
        assert g in PIV.CapIds(NI.LookBodyOfRE(reF, lid));
        assert g in gmtF;
      }
    }
  }

  // ==========================================================================
  // BRICK D4: the RECONSTRUCTED-bank ancestor look-clock chain (feeds (i)/(ii)
  // of `M.ReconInnerGmOfLiveClose`). Two structural spine lemmas first.
  // ==========================================================================

  /** (BRICK D4 infra) Lk-LIFT for TOP-LEVEL looks: for `lid in TopLookIds(re)`
      the descent to `lid` crosses no OTHER lookaround node, so `LookPathPresentLk`
      (which records the ancestor look clocks) coincides with the lc-free
      `LookPathPresent`. The only differing branch — `Re_lookaround(lid0 != lid)`
      — is unreachable: a top-level id equals the node's own id there. */
  lemma LookPathPresentLkOfTop(re: R.regex, cc: seq<int>, lc: seq<int>, qc: seq<int>, mx: int, lid: nat)
    requires LTB.LookUnique(re)
    requires lid in NI.TopLookIds(re)
    requires lid in LTB.LookIds(re)
    requires NI.LookPathPresent(re, cc, qc, mx, lid)
    ensures NI.LookPathPresentLk(re, cc, lc, qc, mx, lid)
    decreases re
  {
    match re
    case Re_alt(r1, r2) =>
      if lid in LTB.LookIds(r1) {
        NI.TopLookIdsIn(r2);
        assert lid !in NI.TopLookIds(r2);
        assert lid in NI.TopLookIds(r1);
        LookPathPresentLkOfTop(r1, cc, lc, qc, mx, lid);
      } else {
        assert lid in LTB.LookIds(r2);
        NI.TopLookIdsIn(r1);
        assert lid !in NI.TopLookIds(r1);
        assert lid in NI.TopLookIds(r2);
        LookPathPresentLkOfTop(r2, cc, lc, qc, mx, lid);
      }
    case Re_con(r1, r2) =>
      if lid in LTB.LookIds(r1) {
        NI.TopLookIdsIn(r2);
        assert lid !in NI.TopLookIds(r2);
        assert lid in NI.TopLookIds(r1);
        LookPathPresentLkOfTop(r1, cc, lc, qc, mx, lid);
      } else {
        assert lid in LTB.LookIds(r2);
        NI.TopLookIdsIn(r1);
        assert lid !in NI.TopLookIds(r1);
        assert lid in NI.TopLookIds(r2);
        LookPathPresentLkOfTop(r2, cc, lc, qc, mx, lid);
      }
    case Re_quant(nul, qid, q, r1) =>
      LookPathPresentLkOfTop(r1, cc, lc, qc, AI.get_idx(qc, qid), lid);
    case Re_capture(cid, r1) =>
      LookPathPresentLkOfTop(r1, cc, lc, qc, mx, lid);
    case Re_lookaround(lid0, la, r1) =>
      assert lid0 >= 0 && (lid0 as nat) == lid;    // lid in TopLookIds == {lid0}
  }

  /** (BRICK D4 infra) COMPOSE-TO-LOOK: the `LookPathComposeNested` analogue whose
      TARGET is a nested LOOK `lid2` in `body` rather than a capture group. Stitches
      the ancestor-chain presence to `lid` + `lid`'s own look-clock clause + the
      body-side presence to `lid2` into the full presence to `lid2` in `r`. Same
      alt/con/quant/capture descent as `LookPathComposeNested`; the lookaround base
      case walks the body via the supplied body premise. */
  lemma LookPathComposeLkNested(r: R.regex, body: R.regex, cc: seq<int>, lc: seq<int>, qc: seq<int>,
                                mx: int, lid: nat, lid2: nat)
    requires NR.NestedFragmentRE(r) && LTB.LookUnique(r)
    requires lid in LTB.LookIds(r)
    requires body == NI.LookBodyOfRE(r, lid)
    requires lid2 in LTB.LookIds(body)
    requires NI.LookPathPresentLk(r, cc, lc, qc, mx, lid)
    requires AI.get_idx(lc, lid as int) >= 0
    requires AI.get_idx(lc, lid as int) >= NI.MxAtLidLk(r, qc, mx, lid)
    requires NI.LookPathPresentLk(body, cc, lc, qc, -1, lid2)
    ensures lid2 in LTB.LookIds(r)
    ensures NI.LookPathPresentLk(r, cc, lc, qc, mx, lid2)
    ensures NI.MxAtLidLk(r, qc, mx, lid2) == NI.MxAtLidLk(body, qc, -1, lid2)
    decreases r
  {
    NI.LookBodyLookIdsIn(r, lid);
    assert lid2 in LTB.LookIds(r);
    match r
    case Re_alt(r1, r2) =>
      if lid in LTB.LookIds(r1) {
        assert body == NI.LookBodyOfRE(r1, lid);
        NI.LookBodyLookIdsIn(r1, lid);
        assert lid2 in LTB.LookIds(r1);
        LookPathComposeLkNested(r1, body, cc, lc, qc, mx, lid, lid2);
      } else {
        assert lid in LTB.LookIds(r2);
        assert body == NI.LookBodyOfRE(r2, lid);
        NI.LookBodyLookIdsIn(r2, lid);
        assert lid2 in LTB.LookIds(r2);
        assert lid2 !in LTB.LookIds(r1) by {
          if lid2 in LTB.LookIds(r1) { assert lid2 in LTB.LookIds(r1) * LTB.LookIds(r2); }
        }
        LookPathComposeLkNested(r2, body, cc, lc, qc, mx, lid, lid2);
      }
    case Re_con(r1, r2) =>
      if lid in LTB.LookIds(r1) {
        assert body == NI.LookBodyOfRE(r1, lid);
        NI.LookBodyLookIdsIn(r1, lid);
        assert lid2 in LTB.LookIds(r1);
        LookPathComposeLkNested(r1, body, cc, lc, qc, mx, lid, lid2);
      } else {
        assert lid in LTB.LookIds(r2);
        assert body == NI.LookBodyOfRE(r2, lid);
        NI.LookBodyLookIdsIn(r2, lid);
        assert lid2 in LTB.LookIds(r2);
        assert lid2 !in LTB.LookIds(r1) by {
          if lid2 in LTB.LookIds(r1) { assert lid2 in LTB.LookIds(r1) * LTB.LookIds(r2); }
        }
        LookPathComposeLkNested(r2, body, cc, lc, qc, mx, lid, lid2);
      }
    case Re_quant(nul, qid, q, r1) =>
      var qv := AI.get_idx(qc, qid);
      assert qv >= mx;                               // LookPathPresentLk(r,..,lid)
      LookPathComposeLkNested(r1, body, cc, lc, qc, qv, lid, lid2);
    case Re_capture(cid, r1) =>
      NI.LookBodyLookIdsIn(r1, lid);
      assert lid2 in LTB.LookIds(r1);
      LookPathComposeLkNested(r1, body, cc, lc, qc, mx, lid, lid2);
    case Re_lookaround(lid0, la, r1) =>
      if lid0 >= 0 && (lid0 as nat) == lid {
        assert body == r1;
        assert NI.MxAtLidLk(r, qc, mx, lid) == mx;
        assert (lid0 as nat) !in LTB.LookIds(r1);    // LookUnique
        assert lid2 != lid;                          // lid2 in LookIds(r1)
        assert AI.get_idx(lc, lid0) >= 0 && AI.get_idx(lc, lid0) >= mx;
      } else {
        assert lid in LTB.LookIds(r1);
        assert body == NI.LookBodyOfRE(r1, lid);
        assert AI.get_idx(lc, lid0) >= 0 && AI.get_idx(lc, lid0) >= mx;   // LookPathPresentLk(r,..,lid)
        assert NI.LookPathPresentLk(r1, cc, lc, qc, -1, lid);
        assert NI.MxAtLidLk(r, qc, mx, lid) == NI.MxAtLidLk(r1, qc, -1, lid);
        NI.LookBodyLookIdsIn(r1, lid);
        assert lid2 in LTB.LookIds(r1);
        assert (lid0 as nat) !in LTB.LookIds(r1);    // LookUnique
        assert lid2 != lid0 as nat;
        LookPathComposeLkNested(r1, body, cc, lc, qc, -1, lid, lid2);
      }
  }

  /** (BRICK D4 infra) `LookPathPresentAgree` for a NESTED `re` restricted to a
      TOP-LEVEL `lid`. The depth-1 form needs the whole fragment look-free to kill
      the outer `Re_lookaround(lid0 != lid)` branch; under nesting that branch is
      instead unreachable because a top-level id equals the node's own id. So the
      path to `lid` still crosses only OUTSIDE-look captures/quants, and
      `LookPathPresent`/`MxAtLidLk` are congruent under outside-look agreement —
      the transport that moves the main thread's presence onto the RECONSTRUCTED
      banks (which agree with it outside the look registers). */
  lemma LookPathPresentAgreeTopNested(r: R.regex, cc1: seq<int>, qc1: seq<int>,
                                      cc2: seq<int>, qc2: seq<int>, mx: int, lid: nat)
    requires LTB.LookUnique(r)
    requires lid in NI.TopLookIds(r)
    requires lid in LTB.LookIds(r)
    requires forall c: nat :: c in PIV.CapIdsOutsideLooks(r) ==>
                                AI.get_idx(cc1, CP.start_reg(c as int)) == AI.get_idx(cc2, CP.start_reg(c as int))
    requires forall q: nat :: q in PIV.QuantIdsOutsideLooks(r) ==>
                                AI.get_idx(qc1, q as int) == AI.get_idx(qc2, q as int)
    ensures NI.LookPathPresent(r, cc1, qc1, mx, lid) == NI.LookPathPresent(r, cc2, qc2, mx, lid)
    ensures NI.MxAtLidLk(r, qc1, mx, lid) == NI.MxAtLidLk(r, qc2, mx, lid)
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      assert PIV.CapIdsOutsideLooks(r1) <= PIV.CapIdsOutsideLooks(r)
             && PIV.CapIdsOutsideLooks(r2) <= PIV.CapIdsOutsideLooks(r);
      assert PIV.QuantIdsOutsideLooks(r1) <= PIV.QuantIdsOutsideLooks(r)
             && PIV.QuantIdsOutsideLooks(r2) <= PIV.QuantIdsOutsideLooks(r);
      if lid in LTB.LookIds(r1) {
        NI.TopLookIdsIn(r2);
        assert lid !in NI.TopLookIds(r2);
        assert lid in NI.TopLookIds(r1);
        LookPathPresentAgreeTopNested(r1, cc1, qc1, cc2, qc2, mx, lid);
      } else {
        assert lid in LTB.LookIds(r2);
        NI.TopLookIdsIn(r1);
        assert lid !in NI.TopLookIds(r1);
        assert lid in NI.TopLookIds(r2);
        LookPathPresentAgreeTopNested(r2, cc1, qc1, cc2, qc2, mx, lid);
      }
    case Re_con(r1, r2) =>
      assert PIV.CapIdsOutsideLooks(r1) <= PIV.CapIdsOutsideLooks(r)
             && PIV.CapIdsOutsideLooks(r2) <= PIV.CapIdsOutsideLooks(r);
      assert PIV.QuantIdsOutsideLooks(r1) <= PIV.QuantIdsOutsideLooks(r)
             && PIV.QuantIdsOutsideLooks(r2) <= PIV.QuantIdsOutsideLooks(r);
      if lid in LTB.LookIds(r1) {
        NI.TopLookIdsIn(r2);
        assert lid !in LTB.LookIds(r2) by {   // LookUnique(r): the halves' lid sets are disjoint
          assert LTB.LookIds(r1) * LTB.LookIds(r2) == {};
          assert lid !in LTB.LookIds(r1) * LTB.LookIds(r2);
          assert lid in LTB.LookIds(r1);
        }
        assert lid !in NI.TopLookIds(r2);
        assert lid in NI.TopLookIds(r1);
        LookPathPresentAgreeTopNested(r1, cc1, qc1, cc2, qc2, mx, lid);
      } else {
        assert lid in LTB.LookIds(r2);
        NI.TopLookIdsIn(r1);
        assert lid !in NI.TopLookIds(r1);
        assert lid in NI.TopLookIds(r2);
        LookPathPresentAgreeTopNested(r2, cc1, qc1, cc2, qc2, mx, lid);
      }
    case Re_quant(_, qid, _, r1) =>
      assert PIV.CapIdsOutsideLooks(r1) <= PIV.CapIdsOutsideLooks(r);
      assert PIV.QuantIdsOutsideLooks(r1) <= PIV.QuantIdsOutsideLooks(r);
      assert AI.get_idx(qc1, qid) == AI.get_idx(qc2, qid) by {
        if qid >= 0 { assert (qid as nat) in PIV.QuantIdsOutsideLooks(r); }
      }
      LookPathPresentAgreeTopNested(r1, cc1, qc1, cc2, qc2, AI.get_idx(qc1, qid), lid);
    case Re_capture(cid, r1) =>
      assert PIV.CapIdsOutsideLooks(r1) <= PIV.CapIdsOutsideLooks(r);
      assert PIV.QuantIdsOutsideLooks(r1) <= PIV.QuantIdsOutsideLooks(r);
      assert AI.get_idx(cc1, CP.start_reg(cid)) == AI.get_idx(cc2, CP.start_reg(cid)) by {
        if cid >= 0 { assert (cid as nat) in PIV.CapIdsOutsideLooks(r); }
        else { assert CP.start_reg(cid) < 0; }
      }
      LookPathPresentAgreeTopNested(r1, cc1, qc1, cc2, qc2, mx, lid);
    case Re_lookaround(lid0, _, r1) =>
      assert lid0 >= 0 && (lid0 as nat) == lid;    // lid in TopLookIds == {lid0}
  }

  /** (BRICK D4) TOP-ANCESTOR base step: turns the MAIN thread's `LookNestOkTTop`
      presence at a TOP-LEVEL `owner` into the RECONSTRUCTED-bank feeds (i)/(ii) of
      `M.ReconInnerGmOfLiveClose`. The three engine facts owed by the whole-regex
      setup are the hypotheses (matching how `ReconInnerGmOfLiveClose` isolates
      (i)/(ii)):
        - (P1)-(P3): `owner`'s main-thread presence + look-clock (from
          `LookNestOkTTop`, its guard discharged by the caller's live witness);
        - (A1)/(A2): the recon_outer capture/quant frames (`res.0`/`res.2` agree
          with the main thread OUTSIDE the look registers — `FLookLoopFullCovers
          FromTables`/`FLookLoopQuantCoversFromTables`);
        - (S): the top-look-clock stability `res.1[owner] == thread[owner]`
          (`M.FLookLoopLidLookClkStable`).
      Transports the presence via `LookPathPresentAgreeTopNested`, lifts to the
      look-clock-aware `LookPathPresentLk` via `LookPathPresentLkOfTop`, and moves
      the two clock bounds across the stability + the `MxAtLidLk` congruence. */
  lemma TopAncestorClockReconStep(re: R.regex,
                                  rcc: seq<int>, rlc: seq<int>, rqc: seq<int>,
                                  tcc: seq<int>, tlc: seq<int>, tqc: seq<int>, owner: nat)
    requires LTB.LookUnique(re)
    requires owner in NI.TopLookIds(re)
    requires owner in LTB.LookIds(re)
    // (P1)-(P3): main-thread presence at owner (from LookNestOkTTop)
    requires NI.LookPathPresent(re, tcc, tqc, -1, owner)
    requires AI.get_idx(tlc, owner as int) >= 0
    requires AI.get_idx(tlc, owner as int) >= NI.MxAtLidLk(re, tqc, -1, owner)
    // (A1)/(A2): recon_outer frames on the OUTSIDE-look slots
    requires forall c: nat :: c in PIV.CapIdsOutsideLooks(re) ==>
                                AI.get_idx(rcc, CP.start_reg(c as int)) == AI.get_idx(tcc, CP.start_reg(c as int))
    requires forall q: nat :: q in PIV.QuantIdsOutsideLooks(re) ==>
                                AI.get_idx(rqc, q as int) == AI.get_idx(tqc, q as int)
    // (S): top-look-clock stability
    requires AI.get_idx(rlc, owner as int) == AI.get_idx(tlc, owner as int)
    ensures NI.LookPathPresentLk(re, rcc, rlc, rqc, -1, owner)
    ensures AI.get_idx(rlc, owner as int) >= 0
    ensures AI.get_idx(rlc, owner as int) >= NI.MxAtLidLk(re, rqc, -1, owner)
  {
    // transport the presence + MxAtLidLk from the main thread to the recon banks
    LookPathPresentAgreeTopNested(re, tcc, tqc, rcc, rqc, -1, owner);
    assert NI.LookPathPresent(re, rcc, rqc, -1, owner);
    assert NI.MxAtLidLk(re, rqc, -1, owner) == NI.MxAtLidLk(re, tqc, -1, owner);
    // lift to the look-clock-aware LookPathPresentLk (owner top-level: lc unread)
    LookPathPresentLkOfTop(re, rcc, rlc, rqc, -1, owner);
    // the two clock bounds cross via stability + the MxAtLidLk equality
    assert AI.get_idx(rlc, owner as int) == AI.get_idx(tlc, owner as int);
  }

  /** (BRICK D4) ANCESTOR PEEL: one level of the nesting recursion. Given the
      reconstructed-bank feed (i)/(ii) at a TOP-LEVEL ancestor `A` (from
      `TopAncestorClockReconStep`) and the feed at `owner` WITHIN `A`'s body `bA`
      (from `A`'s replay tower — `LookNestOkTFromBodyReplay(bA)` reconciled onto the
      recon banks), `LookPathComposeLkNested` stitches them into the feed at `owner`
      in the whole `re`. `owner` may sit at ANY depth inside `bA`: supplying its
      within-`bA` feed by a recursive peel drives the chain to arbitrary nesting. */
  lemma AncestorChainPeelStep(re: R.regex, rcc: seq<int>, rlc: seq<int>, rqc: seq<int>,
                              A: nat, owner: nat)
    requires NR.NestedFragmentRE(re) && LTB.LookUnique(re)
    requires A in LTB.LookIds(re)
    requires owner in LTB.LookIds(NI.LookBodyOfRE(re, A))
    // A's feed on the reconstructed banks (base step)
    requires NI.LookPathPresentLk(re, rcc, rlc, rqc, -1, A)
    requires AI.get_idx(rlc, A as int) >= 0
    requires AI.get_idx(rlc, A as int) >= NI.MxAtLidLk(re, rqc, -1, A)
    // owner's feed WITHIN bA on the reconstructed banks (A's replay tower)
    requires NI.LookPathPresentLk(NI.LookBodyOfRE(re, A), rcc, rlc, rqc, -1, owner)
    requires AI.get_idx(rlc, owner as int) >= 0
    requires AI.get_idx(rlc, owner as int) >= NI.MxAtLidLk(NI.LookBodyOfRE(re, A), rqc, -1, owner)
    ensures owner in LTB.LookIds(re)
    ensures NI.LookPathPresentLk(re, rcc, rlc, rqc, -1, owner)
    ensures AI.get_idx(rlc, owner as int) >= 0
    ensures AI.get_idx(rlc, owner as int) >= NI.MxAtLidLk(re, rqc, -1, owner)
  {
    var bA := NI.LookBodyOfRE(re, A);
    NI.LookBodyLookIdsIn(re, A);
    assert owner in LTB.LookIds(re);
    LookPathComposeLkNested(re, bA, rcc, rlc, rqc, -1, A, owner);
    assert NI.MxAtLidLk(re, rqc, -1, owner) == NI.MxAtLidLk(bA, rqc, -1, owner);
  }

  // ---- driver plumbing: the per-body base evidence + nesting recursion ----

  /** `S <= T` with a witness `x in T \ S` ⟹ `|S| < |T|` — robust strict subset
      cardinality via the disjoint partition `T == S + (T - S)`. */
  lemma SubsetCardLt(S: set<nat>, T: set<nat>, x: nat)
    requires S <= T && x in T && x !in S
    ensures |S| < |T|
  {
    assert S + (T - S) == T;
    assert S * (T - S) == {};
    assert |S + (T - S)| == |S| + |T - S|;   // disjoint union
    assert x in T - S;                        // T - S nonempty
  }

  /** A look's own id is not among its body's look ids (LookUnique). */
  lemma LookIdNotInOwnBody(re: R.regex, lid: nat)
    requires LTB.LookUnique(re)
    requires lid in LTB.LookIds(re)
    ensures lid !in LTB.LookIds(NI.LookBodyOfRE(re, lid))
    decreases re
  {
    match re
    case Re_alt(r1, r2) =>
      if lid in LTB.LookIds(r1) { LookIdNotInOwnBody(r1, lid); } else { LookIdNotInOwnBody(r2, lid); }
    case Re_con(r1, r2) =>
      if lid in LTB.LookIds(r1) { LookIdNotInOwnBody(r1, lid); } else { LookIdNotInOwnBody(r2, lid); }
    case Re_quant(_, _, _, r1) => LookIdNotInOwnBody(r1, lid);
    case Re_capture(_, r1) => LookIdNotInOwnBody(r1, lid);
    case Re_lookaround(lid0, _, r1) =>
      if lid0 >= 0 && (lid0 as nat) == lid {
        assert (lid0 as nat) !in LTB.LookIds(r1);   // LookUnique
      } else {
        LookIdNotInOwnBody(r1, lid);
      }
  }

  /** `LookUnique` descends into a look body. */
  lemma LookBodyLookUnique(re: R.regex, lid: nat)
    requires LTB.LookUnique(re)
    requires lid in LTB.LookIds(re)
    ensures LTB.LookUnique(NI.LookBodyOfRE(re, lid))
    decreases re
  {
    match re
    case Re_alt(r1, r2) =>
      if lid in LTB.LookIds(r1) { LookBodyLookUnique(r1, lid); } else { LookBodyLookUnique(r2, lid); }
    case Re_con(r1, r2) =>
      if lid in LTB.LookIds(r1) { LookBodyLookUnique(r1, lid); } else { LookBodyLookUnique(r2, lid); }
    case Re_quant(_, _, _, r1) => LookBodyLookUnique(r1, lid);
    case Re_capture(_, r1) => LookBodyLookUnique(r1, lid);
    case Re_lookaround(lid0, _, r1) =>
      if lid0 >= 0 && (lid0 as nat) == lid { } else { LookBodyLookUnique(r1, lid); }
  }

  /** Every NON-top look has a TOP-LEVEL ancestor whose body contains it. The
      outermost-ancestor witness the peel recursion consumes. */
  lemma TopAncestorExists(re: R.regex, owner: nat) returns (A0: nat)
    requires LTB.LookUnique(re)
    requires owner in LTB.LookIds(re)
    requires owner !in NI.TopLookIds(re)
    ensures A0 in NI.TopLookIds(re)
    ensures A0 in LTB.LookIds(re)
    ensures owner in LTB.LookIds(NI.LookBodyOfRE(re, A0))
    decreases re
  {
    match re
    case Re_empty => assert false; A0 := 0;
    case Re_character(_) => assert false; A0 := 0;
    case Re_anchor(_) => assert false; A0 := 0;
    case Re_alt(r1, r2) =>
      if owner in LTB.LookIds(r1) {
        assert owner !in NI.TopLookIds(r1);
        A0 := TopAncestorExists(r1, owner);
        NI.TopLookIdsIn(r1);
        assert A0 in LTB.LookIds(r1);
      } else {
        assert owner in LTB.LookIds(r2);
        assert owner !in NI.TopLookIds(r2);
        A0 := TopAncestorExists(r2, owner);
        NI.TopLookIdsIn(r2);
        assert A0 in LTB.LookIds(r2);
        assert A0 !in LTB.LookIds(r1) by {
          if A0 in LTB.LookIds(r1) { assert A0 in LTB.LookIds(r1) * LTB.LookIds(r2); }
        }
      }
    case Re_con(r1, r2) =>
      if owner in LTB.LookIds(r1) {
        assert owner !in NI.TopLookIds(r1);
        A0 := TopAncestorExists(r1, owner);
        NI.TopLookIdsIn(r1);
        assert A0 in LTB.LookIds(r1);
      } else {
        assert owner in LTB.LookIds(r2);
        assert owner !in NI.TopLookIds(r2);
        A0 := TopAncestorExists(r2, owner);
        NI.TopLookIdsIn(r2);
        assert A0 in LTB.LookIds(r2);
        assert A0 !in LTB.LookIds(r1) by {
          if A0 in LTB.LookIds(r1) { assert A0 in LTB.LookIds(r1) * LTB.LookIds(r2); }
        }
      }
    case Re_quant(_, _, _, r1) => A0 := TopAncestorExists(r1, owner);
    case Re_capture(_, r1) => A0 := TopAncestorExists(r1, owner);
    case Re_lookaround(lid0, _, r1) =>
      assert lid0 >= 0;                         // LookUnique
      assert (lid0 as nat) != owner;            // owner !in TopLookIds == {lid0}
      assert owner in LTB.LookIds(r1);
      assert (lid0 as nat) in LTB.LookIds(re);
      A0 := lid0 as nat;
  }

  /** The per-body BASE EVIDENCE at one body `host`: every TOP-LEVEL look of `host`
      carries feed (i)/(ii) on the reconstructed banks. For `host == re` this is
      the main thread's `LookNestOkTTop` reconciled by `TopAncestorClockReconStep`;
      for `host` a look body it is that look's REPLAY tower (`LookNestOkTFrom
      BodyReplay`) reconciled the same way. */
  ghost predicate LocalTopFeed(host: R.regex, rcc: seq<int>, rlc: seq<int>, rqc: seq<int>) {
    forall l: nat :: l in LTB.LookIds(host) && l in NI.TopLookIds(host)
                     // GUARD: some inner capture of `l`'s body is SET on the reconstructed capture
                     // bank — the reconstructed-bank echo of `LookNestOkTTop`'s live-witness guard,
                     // so the base evidence is demanded only at LIVE (matched) top looks.
                     && (exists g2: nat :: g2 in PIV.CapIds(NI.LookBodyOfRE(host, l))
                                           && AI.get_idx(rcc, CP.start_reg(g2)) >= 0)
                     ==>
                       NI.LookPathPresentLk(host, rcc, rlc, rqc, -1, l)
                       && AI.get_idx(rlc, l as int) >= 0
                       && AI.get_idx(rlc, l as int) >= NI.MxAtLidLk(host, rqc, -1, l)
  }

  /** (BRICK D6 clock-frame twin — CAPTURE) The `a_clk` face of
      `M.FLookLoopFullCoversFromTables`'s recon_outer capture frame, in the exact
      shape `LocalTopFeedFromNestOkT` demands: for every OUTSIDE-look group `c`,
      the reconstructed capture-clock bank agrees with the host thread's at
      `start_reg(c)`. `RegsAgreeOutside` already covers `a_clk`; the only work is
      moving OFF `CaptureRegsSet(CapIdsInLooks(host))` onto `CapIdsOutsideLooks`
      via `CapIdsLooksDisjoint` + `StartRegInCaptureRegsSet` (start-reg parity). */
  lemma CapClkFrameOutsideLooksTwin(host: R.regex, res0: AReg.Regs, thcap: AReg.Regs)
    requires PIV.CapUnique(host)
    requires CM.RegsAgreeOutside(res0, thcap, PIV.CaptureRegsSet(PIV.CapIdsInLooks(host)))
    ensures forall c: nat :: c in PIV.CapIdsOutsideLooks(host) ==>
                               AI.get_idx(res0.a_clk, CP.start_reg(c as int)) == AI.get_idx(thcap.a_clk, CP.start_reg(c as int))
  {
    PIV.CapIdsLooksDisjoint(host);
    forall c: nat | c in PIV.CapIdsOutsideLooks(host)
      ensures AI.get_idx(res0.a_clk, CP.start_reg(c as int)) == AI.get_idx(thcap.a_clk, CP.start_reg(c as int))
    {
      assert c !in PIV.CapIdsInLooks(host);
      PIV.StartRegInCaptureRegsSet(PIV.CapIdsInLooks(host), c);
      assert CP.start_reg(c as int) !in PIV.CaptureRegsSet(PIV.CapIdsInLooks(host));
    }
  }

  /** (BRICK D6 clock-frame twin — QUANT) The `a_clk` face of
      `M.FLookLoopQuantCoversFromTables`'s recon_outer quant frame, in the shape
      `LocalTopFeedFromNestOkT` demands: for every OUTSIDE-look quant `q`, the
      reconstructed quant-clock bank agrees with the host thread's at `q`. Off
      the in-look quant int-image via `QuantIdsLooksDisjoint`. */
  lemma QuantClkFrameOutsideLooksTwin(host: R.regex, res2: AReg.Regs, thqt: AReg.Regs)
    requires PIV.QuantUnique(host)
    requires CM.RegsAgreeOutside(res2, thqt, (set q: nat | q in PIV.QuantIdsInLooks(host) :: q as int))
    ensures forall q: nat :: q in PIV.QuantIdsOutsideLooks(host) ==>
                               AI.get_idx(res2.a_clk, q as int) == AI.get_idx(thqt.a_clk, q as int)
  {
    PIV.QuantIdsLooksDisjoint(host);
    var Sq := set q: nat | q in PIV.QuantIdsInLooks(host) :: q as int;
    forall q: nat | q in PIV.QuantIdsOutsideLooks(host)
      ensures AI.get_idx(res2.a_clk, q as int) == AI.get_idx(thqt.a_clk, q as int)
    {
      assert (q as int) !in Sq by {
        if (q as int) in Sq {
          var q2: nat :| q2 in PIV.QuantIdsInLooks(host) && q2 as int == q as int;
          assert q2 == q;
          assert q in PIV.QuantIdsOutsideLooks(host) * PIV.QuantIdsInLooks(host);
        }
      }
    }
  }

  /** (BRICK D6 — the GUARD BRIDGE, reduced) `LocalTopFeedFromNestOkT`'s guard
      bridge (reconstructed-bank live witness ==> `gmt` live witness) discharged
      via the `LookNestBackTTop` carrier of `BestTieLkNestedTop`, MODULO exactly one
      owed engine connective: the REVERSE of `M.FLookLoopFullCoversFromTables`'s
      recon_inner. That connective (hypothesis `(A)`) says a res0-live inner cap
      `g2` of a top look `l`'s body pins `l` matched+dominating in the thread's look
      bank WITH a live fresh body match carrying `g2`. The forward route (through
      `ReconInnerGmOfLiveClose`) is CIRCULAR here — it feeds `AllBodyTopFeeds`, which
      feeds this guard — so the tie MUST come from the backward carrier, which does
      not depend on `AllBodyTopFeeds`. Given `(A)`, `g2` itself is the `gmt` witness:
      `g2 in S` structurally (`LookBodyCapsIn`), `g2 in gmt` from `LookNestBackTTop`. */
  lemma GuardBridgeFromLookNestBackTTop(
    re: R.regex, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
    S: set<LG.GroupId>, gmt: LG.GroupMap, th: AI.Thread, res0: AReg.Regs,
    ncap: int, nlook: int, nquant: int)
    requires LTB.LookUnique(re)
    requires S == PIV.CapIdsInLooks(re)
    requires LookNestBackTTop(re, crv, str, ov, S, gmt, th, ncap, nlook, nquant)
    // (A) REVERSE-RECON connective — the sole owed engine piece.
    requires forall l: nat, g2: nat ::
               l in NI.TopLookIds(re) && l in LTB.LookIds(re)
               && g2 in PIV.CapIds(NI.LookBodyOfRE(re, l))
               && AI.get_idx(res0.a_clk, CP.start_reg(g2)) >= 0
               ==>
                 M.MatchedPosLA(crv, th.look_regs, l as int)
                 && NI.LookPathDom(re, AI.get_idx(th.look_regs.a_clk, l as int), th.quant_regs.a_clk, l)
                 && var rf := M.FreshBodyMatch(crv, str, l as int, th.look_regs, ov, ncap, nlook, nquant);
                 rf.Some?
                 && g2 in PIV.GmOfLive(NI.LookBodyOfRE(re, l), rf.value.capture_regs,
                                       rf.value.look_regs, rf.value.quant_regs)
    ensures forall l: nat :: l in LTB.LookIds(re) && l in NI.TopLookIds(re)
                             && (exists g2: nat :: g2 in PIV.CapIds(NI.LookBodyOfRE(re, l)) && AI.get_idx(res0.a_clk, CP.start_reg(g2)) >= 0)
                             ==> (exists g3: LG.GroupId :: g3 in S && g3 in gmt && g3 in PIV.CapIds(NI.LookBodyOfRE(re, l)))
  {
    forall l: nat | l in LTB.LookIds(re) && l in NI.TopLookIds(re)
                    && (exists g2: nat :: g2 in PIV.CapIds(NI.LookBodyOfRE(re, l)) && AI.get_idx(res0.a_clk, CP.start_reg(g2)) >= 0)
      ensures exists g3: LG.GroupId :: g3 in S && g3 in gmt && g3 in PIV.CapIds(NI.LookBodyOfRE(re, l))
    {
      var g2: nat :| g2 in PIV.CapIds(NI.LookBodyOfRE(re, l)) && AI.get_idx(res0.a_clk, CP.start_reg(g2)) >= 0;
      NI.LookBodyCapsIn(re, l);                       // CapIds(body(l)) <= CapIdsInLooks(re) == S
      assert g2 in S;
      var rf := M.FreshBodyMatch(crv, str, l as int, th.look_regs, ov, ncap, nlook, nquant);
      assert M.MatchedPosLA(crv, th.look_regs, l as int)
             && NI.LookPathDom(re, AI.get_idx(th.look_regs.a_clk, l as int), th.quant_regs.a_clk, l)
             && rf.Some?
             && g2 in PIV.GmOfLive(NI.LookBodyOfRE(re, l), rf.value.capture_regs,
                                   rf.value.look_regs, rf.value.quant_regs);        // (A)@(l,g2)
      assert g2 in gmt;                               // LookNestBackTTop@(l, g:=g2)
    }
  }

  /** (BRICK D-8 FINDING 3) The GUARD BRIDGE re-derived from the REVERSE-RECON
      DESCENT conclusion (FINDING 2) in place of the false-for-deep-caps connective
      `(A)`. The descent conclusion — every recon-live in-look capture of `re` lands
      in the spec group map `gmt` — makes the guard bridge trivial: the recon-live
      witness `g2` of top look `l`'s body IS the `gmt` witness `g3` (`g2 in S` by
      `LookBodyCapsIn`, `g2 in gmt` by the descent, `g2 in CapIds(body(l))` given).
      This is the exact shape `LocalTopFeedFromNestOkT`/`LocalTopFeedAtReFromFrames`
      consume — with NO dependence on the (deep-false) reverse-recon connective. */
  lemma GuardBridgeFromDescent(
    re: R.regex, S: set<LG.GroupId>, gmt: LG.GroupMap, res0: AReg.Regs)
    requires S == PIV.CapIdsInLooks(re)
    // DESCENT conclusion (FINDING 2): every recon-live in-look capture is in gmt.
    requires forall g2: nat :: g2 in S && AI.get_idx(res0.a_clk, CP.start_reg(g2)) >= 0 ==> g2 in gmt
    ensures forall l: nat :: l in LTB.LookIds(re) && l in NI.TopLookIds(re)
                             && (exists g2: nat :: g2 in PIV.CapIds(NI.LookBodyOfRE(re, l)) && AI.get_idx(res0.a_clk, CP.start_reg(g2)) >= 0)
                             ==> (exists g3: LG.GroupId :: g3 in S && g3 in gmt && g3 in PIV.CapIds(NI.LookBodyOfRE(re, l)))
  {
    forall l: nat | l in LTB.LookIds(re) && l in NI.TopLookIds(re)
                    && (exists g2: nat :: g2 in PIV.CapIds(NI.LookBodyOfRE(re, l)) && AI.get_idx(res0.a_clk, CP.start_reg(g2)) >= 0)
      ensures exists g3: LG.GroupId :: g3 in S && g3 in gmt && g3 in PIV.CapIds(NI.LookBodyOfRE(re, l))
    {
      var g2: nat :| g2 in PIV.CapIds(NI.LookBodyOfRE(re, l)) && AI.get_idx(res0.a_clk, CP.start_reg(g2)) >= 0;
      NI.LookBodyCapsIn(re, l);                        // CapIds(body(l)) <= CapIdsInLooks(re) == S
      assert g2 in S;
      assert g2 in gmt;                                // DESCENT@(g2)
    }
  }

  /** (BRICK D-8 FINDING 2 consumer) The endpoint's inside-`S` REVERSE (c) residual
      re-derived from the REVERSE-RECON DESCENT conclusion. `g in GmOfLive(re, res)`
      is STRONGER than recon-live: `GmOfLivePresenceExtractLkNested` peels off the
      look-aware path presence, exposing `res0`'s start clock SET at `g` — then the
      descent lands `g` in `gmt`. This reduces the endpoint's third owed hypothesis
      (`:16346`) to the single descent conclusion. */
  lemma ReverseCFromDescent(re: R.regex, res0: AReg.Regs, res1: AReg.Regs, res2: AReg.Regs,
                            gmt: LG.GroupMap, S: set<LG.GroupId>)
    requires NR.NestedFragmentRE(re) && PIV.CapUnique(re)
    requires S == PIV.CapIdsInLooks(re)
    // synthetic-res wf: an unset start clock forces an unset start cp (extract premise)
    requires forall c: nat :: c in PIV.CapIds(re) && AI.get_idx(res0.a_clk, CP.start_reg(c)) < 0
                              ==> AI.get_idx(res0.a_cp, CP.start_reg(c)) < 0
    // DESCENT conclusion (FINDING 2): every recon-live in-look capture is in gmt.
    requires forall g2: nat :: g2 in S && AI.get_idx(res0.a_clk, CP.start_reg(g2)) >= 0 ==> g2 in gmt
    ensures forall g: LG.GroupId :: g in S && g in PIV.GmOfLive(re, res0, res1, res2) ==> g in gmt
  {
    forall g: LG.GroupId | g in S && g in PIV.GmOfLive(re, res0, res1, res2)
      ensures g in gmt
    {
      PIV.CapIdsSplit(re);                              // CapIdsInLooks(re) <= CapIds(re)
      assert g in PIV.CapIds(re);
      NI.GmOfLivePresenceExtractLkNested(re, res0, res1, res2, g);
      assert AI.get_idx(res0.a_clk, CP.start_reg(g)) >= 0;
      assert g in gmt;                                 // DESCENT@(g)
    }
  }

  /** The base evidence at `re` AND at every look body of `re` (any depth). The
      hereditary hypothesis the nesting recursion peels one body at a time. */
  ghost predicate AllBodyTopFeeds(re: R.regex, rcc: seq<int>, rlc: seq<int>, rqc: seq<int>) {
    LocalTopFeed(re, rcc, rlc, rqc)
    && forall a: nat :: a in LTB.LookIds(re) ==> LocalTopFeed(NI.LookBodyOfRE(re, a), rcc, rlc, rqc)
  }

  /** (BRICK D-11 descent — LEVEL STEP) Land a fresh-body-live capture into a
      level's spec leaf via the SIM BACKWARD carrier. For a TOP look `A0`
      matched + dominating on the carrier thread's banks, any `g2` (in `S`, in
      `body(A0)`'s caps) that the FRESH body match of `A0` carries LIVE in its
      OWN banks lands in that level's `gmt`. Pure instantiation of the
      `LookNestBackTTop` carrier — delivered at the top by `BestTieLkNestedTop`
      (winning thread) and one nesting level down by `LookNestBackTFromBodyReplay`
      (a look body's replay). This is the "use the backward carrier to land g2 in
      that level's gmt" step of the reverse-recon descent. */
  lemma DescentLandTop(
    re: R.regex, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
    S: set<LG.GroupId>, gmt: LG.GroupMap, thread: AI.Thread, A0: nat, g2: nat,
    ncap: int, nlook: int, nquant: int)
    requires S == PIV.CapIdsInLooks(re)
    requires LookNestBackTTop(re, crv, str, ov, S, gmt, thread, ncap, nlook, nquant)
    requires A0 in NI.TopLookIds(re)
    requires A0 in LTB.LookIds(re)
    requires M.MatchedPosLA(crv, thread.look_regs, A0 as int)
    requires NI.LookPathDom(re, AI.get_idx(thread.look_regs.a_clk, A0 as int), thread.quant_regs.a_clk, A0)
    requires g2 in S && g2 in PIV.CapIds(NI.LookBodyOfRE(re, A0))
    requires var rf := M.FreshBodyMatch(crv, str, A0 as int, thread.look_regs, ov, ncap, nlook, nquant);
             rf.Some?
             && g2 in PIV.GmOfLive(NI.LookBodyOfRE(re, A0), rf.value.capture_regs,
                                   rf.value.look_regs, rf.value.quant_regs)
    ensures g2 in gmt
  {
  }

  /** (BRICK D-11 descent — TOP-ANCESTOR PEEL) The REVERSE mirror of the forward
      `FLookLoopAncestorClockChain`'s `A0 := TopAncestorExists` peel. Given a
      recon-live inside-look capture `g2` with its innermost-DIRECT owner `owner0`
      (as delivered by `M.FLookLoopInLookLiveOwnerMatched` / `InnermostOwnerDirect`),
      exposes `g2`'s outermost TOP-level ancestor look `A0`: a top look of `re`
      whose body still contains `g2`, with `owner0` nested inside `body(A0)` (or
      `A0 == owner0` when `owner0` is already top). Pure structural descent
      (`TopAncestorExists` + `LookBodyCompose` + `LookBodyCapsIn`); this is the
      "descend to `g2`'s innermost owner, peel its top ancestor" skeleton of the
      reverse-recon descent. */
  lemma ReconLiveTopAncestor(re: R.regex, g2: nat, owner0: nat) returns (A0: nat)
    requires PIV.CapUnique(re) && LTB.LookUnique(re)
    requires g2 in PIV.CapIdsInLooks(re)
    requires owner0 in LTB.LookIds(re)
    requires g2 in PIV.CapIds(NI.LookBodyOfRE(re, owner0))
    requires g2 !in PIV.CapIdsInLooks(NI.LookBodyOfRE(re, owner0))
    ensures A0 in NI.TopLookIds(re)
    ensures A0 in LTB.LookIds(re)
    ensures g2 in PIV.CapIds(NI.LookBodyOfRE(re, A0))
    ensures A0 == owner0 || owner0 in LTB.LookIds(NI.LookBodyOfRE(re, A0))
  {
    if owner0 in NI.TopLookIds(re) {
      A0 := owner0;
      NI.TopLookIdsIn(re);
    } else {
      A0 := TopAncestorExists(re, owner0);   // owner0 in LookIds(body(A0)); A0 top
      NI.LookBodyCompose(re, A0, owner0);     // body(owner0) == LookBodyOfRE(body(A0), owner0)
      NI.LookBodyCapsIn(NI.LookBodyOfRE(re, A0), owner0);  // CapIds(body(owner0)) <= CapIds(body(A0))
    }
  }

  /** (BRICK D-11 — INTERFACE CHECK) Confirms the reverse-recon descent
      conclusion `DescentProducerTopOwners` emits (its `ensures`, restated here
      verbatim as the sole descent `requires`) is EXACTLY what both D-8 descent
      consumers take: it discharges `GuardBridgeFromDescent` and
      `ReverseCFromDescent` with no adaptation. Green here means the produced
      descent conclusion type-matches and closes both consumers directly. */
  lemma DescentProducerWiringCheck(
    re: R.regex, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
    S: set<LG.GroupId>, gmt: LG.GroupMap,
    res0: AReg.Regs, res1: AReg.Regs, res2: AReg.Regs)
    requires S == PIV.CapIdsInLooks(re)
    requires NR.NestedFragmentRE(re) && PIV.CapUnique(re)
    requires forall c: nat :: c in PIV.CapIds(re) && AI.get_idx(res0.a_clk, CP.start_reg(c)) < 0
                              ==> AI.get_idx(res0.a_cp, CP.start_reg(c)) < 0
    // the reverse-recon descent conclusion — DescentProducerTopOwners' `ensures`.
    requires forall g2: nat :: g2 in S && AI.get_idx(res0.a_clk, CP.start_reg(g2)) >= 0 ==> g2 in gmt
    // both consumers' conclusions, derived through the produced descent conclusion:
    ensures forall l: nat :: l in LTB.LookIds(re) && l in NI.TopLookIds(re)
                             && (exists g2: nat :: g2 in PIV.CapIds(NI.LookBodyOfRE(re, l)) && AI.get_idx(res0.a_clk, CP.start_reg(g2)) >= 0)
                             ==> (exists g3: LG.GroupId :: g3 in S && g3 in gmt && g3 in PIV.CapIds(NI.LookBodyOfRE(re, l)))
    ensures forall g: LG.GroupId :: g in S && g in PIV.GmOfLive(re, res0, res1, res2) ==> g in gmt
  {
    GuardBridgeFromDescent(re, S, gmt, res0);
    ReverseCFromDescent(re, res0, res1, res2, gmt, S);
  }

  /** `TopLookIds` and `DirectLookIds` are the same function (definitional
      clones in NI and M); the deep carrier speaks `TopLookIds`, the level-link
      speaks `DirectLidSet`. */
  lemma TopEqDirectLookIds(r: R.regex)
    ensures NI.TopLookIds(r) == M.DirectLookIds(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => TopEqDirectLookIds(r1); TopEqDirectLookIds(r2);
    case Re_con(r1, r2) => TopEqDirectLookIds(r1); TopEqDirectLookIds(r2);
    case Re_quant(_, _, _, r1) => TopEqDirectLookIds(r1);
    case Re_capture(_, r1) => TopEqDirectLookIds(r1);
    case _ =>
  }

  /** `GNotUnderQuantL` descends into look bodies: `Translate` is a homomorphism
      and `GNotUnderQuantL` is a conjunction over the whole tree, so the subterm
      `Translate(LookBodyOfRE(r, lid))` inherits it. Feeds the per-level
      `AncQuants(host, g2) == {}` (body-level dominance is then structural). */
  lemma GNotUnderQuantLLookBody(r: R.regex, lid: nat, g: LG.GroupId)
    requires T.TransWf(r)
    requires lid in LTB.LookIds(r)
    requires M.GNotUnderQuantL(T.Translate(r), g)
    ensures T.TransWf(NI.LookBodyOfRE(r, lid))
    ensures M.GNotUnderQuantL(T.Translate(NI.LookBodyOfRE(r, lid)), g)
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      if lid in LTB.LookIds(r1) { GNotUnderQuantLLookBody(r1, lid, g); }
      else { GNotUnderQuantLLookBody(r2, lid, g); }
    case Re_con(r1, r2) =>
      if lid in LTB.LookIds(r1) { GNotUnderQuantLLookBody(r1, lid, g); }
      else { GNotUnderQuantLLookBody(r2, lid, g); }
    case Re_quant(_, _, _, r1) => GNotUnderQuantLLookBody(r1, lid, g);
    case Re_capture(_, r1) => GNotUnderQuantLLookBody(r1, lid, g);
    case Re_lookaround(lid0, la, r1) =>
      if lid0 >= 0 && (lid0 as nat) == lid {
        // body == r1; GNotUnderQuantL(LookaroundR(_, Translate(r1)), g) unfolds to r1's
      } else {
        GNotUnderQuantLLookBody(r1, lid, g);
      }
  }

  /** (THE LAST KERNEL — the deep per-`g2` landing RECURSION) For a live inside
      capture `g2` and ANY of its look-ancestors `A` (any depth; `host` = `A`'s
      body; `A` matched in the FINAL reconstructed look bank `res1`), `g2` lands
      in `host`'s spec FIRST LEAF at `A`'s recorded position — i.e. in
      `SubFirstLeafAt(A, res1)`. Recursion on `|LookIds(host)|`:

      BASE (`g2` DIRECT in `host`): `A` IS `g2`'s innermost-direct owner
      (`InnermostOwnerUnique`), so the A2 fresh-membership hypothesis speaks
      about `A`, and `FreshBodyDirectInSubFirstLeaf` lands `g2` in the leaf.

      DEEP (`g2` inside `host`'s own looks): let `A1` be `g2`'s top-in-`host`
      ancestor (`ReconLiveTopAncestor`). The per-body replay
      (`LookNestBackTFromBodyReplay`, at the BODY-RESTRICTED qmap) delivers the
      DEEP carrier at (`host`'s first leaf, `rf_A` = the fresh body match);
      `rf_A.Some?` comes from the ORACLE (`res1`'s record at `A` is oracle-true,
      so `host`'s spec tree matches there; the replay's None-iff converts);
      `A1`-matched on `rf_A`'s banks from `PathPresentLk`'s ancestor clock
      (`LookPathDecomposeNested`) + the reverse invariant on `res1`
      (`FLookLoopLookCpSet`, hypothesis) + the LEVEL-LINK
      (`FLookLoopChildLinkOk`: `res1`'s record at `A1` IS `rf_A`'s);
      `A1`-dominance on `rf_A`'s banks is STRUCTURAL (`LookPathDomNoAncQuants` —
      no quants above capture-owning looks inside bodies, from `GNotUnderQuantL`);
      and the landing INTO `SubFirstLeafAt(A1, rf_A.look_regs)` is the RECURSIVE
      CALL at `A1` (its `res1`-keyed leaf equals the `rf_A`-keyed one by the
      level-link position tie). `DescentLandTopDeep` then lands `g2` in `host`'s
      leaf. */
  /** (L5 F7f perf) The fresh BACKWARD body run needs no plus-reconstruction: its
      quant registers are at their init values, so `FReconstructPlus` is the identity
      and `FFindMatchPlus` collapses to `FFindMatch`. Extracted from the LB arms of
      `DeepFindRec`/`ForwardFindRec` (inline, its `FFindMatchQuantFinalAny` precondition
      check timed out at 900 s in their giant contexts). */
  lemma BackFreshPlusIsPlain(host: R.regex, bodycodeB: RB.code, plus_bc: seq<RB.code>,
                             str: string, ov: LOr.OracleView, cp: nat, cdn: LCdn.cdns,
                             ncap: int, nlook: int, nquant: int)
    requires NR.NoNulledPlusRE(host)   // §2.5b interim
    requires NR.NestedFragmentRE(host) && PIV.CapUnique(host) && PIV.QuantUnique(host)
    requires bodycodeB == CP.compile_to_bytecode(R.reverse_regex(host))
    requires cp <= |str|
    ensures
      var ctx := AI.cp_context(cp, str, LAnc.Backward);
      var inits := AI.FInitState(bodycodeB, cp, AReg.init_regs(ncap), AReg.init_regs(nlook),
                                 AReg.init_regs(nquant), 0, ctx);
      var fm := AI.FFindMatch(bodycodeB, str, inits, ov, LAnc.Backward, cdn).0;
      var rfP := AI.FFindMatchPlus(bodycodeB, host, plus_bc, str, ov, LAnc.Backward, cp,
                                   AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant),
                                   0, cdn).0;
      (rfP.Some? <==> fm.Some?) && (fm.Some? ==> rfP == Some(fm.value))
  {
    var ctx := AI.cp_context(cp, str, LAnc.Backward);
    var inits := AI.FInitState(bodycodeB, cp, AReg.init_regs(ncap), AReg.init_regs(nlook),
                               AReg.init_regs(nquant), 0, ctx);
    var th0 := AI.init_thread(AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant));
    assert |inits.active| == 1 && inits.active[0] == th0;
    assert M.QuantRegsFinal(th0) by {
      RL.AInitLaws(nquant);
      forall k ensures AI.get_idx(AReg.init_regs(nquant).a_cp, k) < 0
                       && AI.get_idx(AReg.init_regs(nquant).a_clk, k) >= -1 {
        if 0 <= k < nquant { }
      }
    }
    assert M.VmQuantFinal(inits) by {
      forall t2 | t2 in inits.active ensures M.QuantRegsFinal(t2) { assert t2 == th0; }
    }
    // the stamp fact is about the code actually run — the REVERSED body
    M.ReverseNestedPackage(host);
    NR.NoNulledPlusReverse(host);
    M.NoTrueQuantStampNested(R.reverse_regex(host));
    M.FFindMatchQuantFinalAny(bodycodeB, str, inits, ov, LAnc.Backward, cdn);
    var (fm, ovx) := AI.FFindMatch(bodycodeB, str, inits, ov, LAnc.Backward, cdn);
    if fm.Some? {
      assert M.QuantRegsFinal(fm.value);
      RL.AInitLaws(nquant);
      M.FNulledPlusIdentity(host, fm.value.capture_regs, fm.value.look_regs, fm.value.quant_regs,
                            plus_bc, str, ovx, LAnc.Backward);
      assert AI.FReconstructPlus(fm.value, host, plus_bc, str, ovx, LAnc.Backward).0 == fm.value;
    }
  }

  /** (descent wrapper input) The per-live-`g` OWNER package — A1/A2's outputs at
      `g`'s innermost-direct owner, keyed on the FINAL look bank `res1`. */
  ghost predicate OwnerPkg(crv: CP.FCompiled, str: string, re: R.regex, ov: LOr.OracleView,
                           res1: AReg.Regs, g: LG.GroupId, owner: nat,
                           ncap: int, nlook: int, nquant: int) {
    owner in LTB.LookIds(re)
    && g in PIV.CapIds(NI.LookBodyOfRE(re, owner))
    && g !in PIV.CapIdsInLooks(NI.LookBodyOfRE(re, owner))
    && M.FreshBodyMatch(crv, str, owner as int, res1, ov, ncap, nlook, nquant).Some?
    && g in PIV.GmOfLive(NI.LookBodyOfRE(re, owner),
                         M.FreshBodyMatch(crv, str, owner as int, res1, ov, ncap, nlook, nquant).value.capture_regs,
                         M.FreshBodyMatch(crv, str, owner as int, res1, ov, ncap, nlook, nquant).value.look_regs,
                         M.FreshBodyMatch(crv, str, owner as int, res1, ov, ncap, nlook, nquant).value.quant_regs)
  }

  /** L4 PERF: the owner-package forall, OPAQUE (the `forall g :: exists owner`
      is the single heaviest trigger source; wrapping it lets MainTheoremL4 pass
      it to DeepConclude atomically, established once in MainTheoremL4 from the
      inline owner-forall proof and revealed inside DeepConclude). */
  ghost opaque predicate OwnerForallO(crv: CP.FCompiled, str: string, re: R.regex, ov: LOr.OracleView,
                                      res0: AReg.Regs, res1: AReg.Regs, res2: AReg.Regs, S: set<LG.GroupId>, ncap: int, nlook: int, nquant: int) {
    forall g: LG.GroupId :: g in S && g in PIV.GmOfLive(re, res0, res1, res2) ==>
                              exists owner: nat :: OwnerPkg(crv, str, re, ov, res1, g, owner, ncap, nlook, nquant)
  }

  /** The L4 fragment scope, packaged: positive looks are forward-only and no
      inside-look capture sits under any quantifier (the `GNotUnderQuantL` shadow,
      stated on the translated whole regex). `TransWf` guards the `Translate`. */
  ghost predicate L4Scope(raw: R.raw_regex)
    requires T.Latin1Wf(raw)
  {
    var re := R.lazy_prefix(R.annotate(raw));
    M.NoPosLookbehindRE(re)
    && NR.NegLooksLookFreeRE(re)
    && T.TransWf(re)
    && forall c: nat :: c in PIV.CapIdsInLooks(re) ==> M.GNotUnderQuantL(T.Translate(re), c)
  }

  /** THE EXECUTABLE-SCOPE BRIDGE: `L4Scope` from four purely SYNTACTIC raw-level
      predicates — no positive lookbehind, look-free negative bodies, (1) no
      capture under a quant inside look bodies, (2) capture-free look bodies
      under quants. `T.AnnotateWf` gives `TransWf`; the per-id `GNotUnderQuantL`
      obligation is `M.GNQLTop` fed by the annotate transfers +
      `PIV.SpecRegexCapUnique`, with the `lazy_prefix` dot-star wrapper
      discharged by computation. */
  lemma L4ScopeFromRaw(raw: R.raw_regex)
    requires T.Latin1Wf(raw)
    requires NR.NoPosLookbehindRaw(raw)
    requires NR.NegLooksLookFreeRaw(raw)
    requires NR.LookBodiesNoCapUnderQuantRaw(raw)
    requires NR.QuantsLookCapFreeRaw(raw)
    ensures L4Scope(raw)
  {
    var ast := R.annotate(raw);
    var re := R.lazy_prefix(ast);
    assert ast == R.annotate_regex(R.Raw_capture(raw), 0, 1, 1).0;
    // TransWf
    T.AnnotateWf(raw);
    // NoPosLookbehind: transfer at the implicit Raw_capture wrapper, then
    // the dot-star prefix is look-free by computation.
    assert NR.NoPosLookbehindRaw(R.Raw_capture(raw));
    M.AnnotateNoPosLookbehind(R.Raw_capture(raw), 0, 1, 1);
    assert M.NoPosLookbehindRE(ast);
    assert M.NoPosLookbehindRE(re);
    // NegLooksLookFree
    assert NR.NegLooksLookFreeRaw(R.Raw_capture(raw));
    NR.AnnotateNegLooksLookFree(R.Raw_capture(raw), 0, 1, 1);
    assert NR.NegLooksLookFreeRE(ast);
    assert NR.NegLooksLookFreeRE(re);
    // The GNotUnderQuantL shadow, for every inside-look capture id.
    assert NR.LookBodiesNoCapUnderQuantRaw(R.Raw_capture(raw));
    NR.AnnotateLookBodiesNoCapUnderQuant(R.Raw_capture(raw), 0, 1, 1);
    assert NR.LookBodiesNoCapUnderQuantRE(ast);
    assert NR.QuantsLookCapFreeRaw(R.Raw_capture(raw));
    NR.AnnotateQuantsLookCapFree(R.Raw_capture(raw), 0, 1, 1);
    assert NR.QuantsLookCapFreeRE(ast);
    // Push through the lazy_prefix wrapper (dot-star side is by computation).
    var pfx := R.Re_quant(R.NonNullable, 0, R.CountedQuant(0, None, false), R.Re_character(R.Dot));
    assert re == R.Re_con(pfx, ast);
    assert NR.LookBodiesNoCapUnderQuantRE(pfx);
    assert NR.QuantsLookCapFreeRE(pfx);
    assert NR.LookBodiesNoCapUnderQuantRE(re);
    assert NR.QuantsLookCapFreeRE(re);
    PIV.SpecRegexCapUnique(raw);
    forall c: nat | c in PIV.CapIdsInLooks(re)
      ensures M.GNotUnderQuantL(T.Translate(re), c)
    {
      M.GNQLTop(re, c);
    }
  }

  /** (L5 F7c) The L5 scope at the annotated, lazy-prefixed regex from the raw
      syntactic predicate `NR.L5ScopeRaw` — the L5 leg of `L4ScopeFromRaw`
      (annotation preserves look constructors; the dot-star prefix is look-free). */

  /** (L5 F7f, v1 scope, RE level) positive lookbehinds are allowed with
      lookbehind-only bodies, but a lookAHEAD body must stay free of positive
      lookbehinds — the shape the gate hub `GateStaticAtNested` asserts per lid
      (a lookahead lid keeps the L4 pruning fact `M.NoPosLookbehindRE(body)`).
      `M.NoPosLookbehindRE(re) ==> L5ScopeV1RE(re) ==> NR.L5ScopeRE(re)`. */
  opaque predicate L5ScopeV1RE(re: R.regex)
    decreases re
  {
    match re
    case Re_alt(r1, r2) => L5ScopeV1RE(r1) && L5ScopeV1RE(r2)
    case Re_con(r1, r2) => L5ScopeV1RE(r1) && L5ScopeV1RE(r2)
    case Re_quant(_, _, _, r1) => L5ScopeV1RE(r1)
    case Re_capture(_, r1) => L5ScopeV1RE(r1)
    case Re_lookaround(_, la, r1) =>
      // (2026-08-28 s6, the `(?=x(?<=y))` widening) a lookAHEAD body is scoped RECURSIVELY
      // (it may contain positive lookbehinds); a lookBEHIND body stays lookbehind-only.
      // OPAQUE so the gate hub's `exists` never unfolds the recursion (the s5 timeout cliff).
      (la.Lookbehind? ==> NR.LBOnlyLooksRE(r1))
      && L5ScopeV1RE(r1)
      && L5ScopeV1RE(r1)
    case _ => true
  }

  lemma NoPosImpliesL5ScopeV1(re: R.regex)
    requires M.NoPosLookbehindRE(re)
    ensures L5ScopeV1RE(re)
    decreases re
  {
    reveal L5ScopeV1RE();
    match re
    case Re_alt(r1, r2) => NoPosImpliesL5ScopeV1(r1); NoPosImpliesL5ScopeV1(r2);
    case Re_con(r1, r2) => NoPosImpliesL5ScopeV1(r1); NoPosImpliesL5ScopeV1(r2);
    case Re_quant(_, _, _, r1) => NoPosImpliesL5ScopeV1(r1);
    case Re_capture(_, r1) => NoPosImpliesL5ScopeV1(r1);
    case Re_lookaround(_, la, r1) => NoPosImpliesL5ScopeV1(r1);
    case _ =>
  }

  lemma L5ScopeV1ImpliesL5(re: R.regex)
    requires L5ScopeV1RE(re)
    ensures NR.L5ScopeRE(re)
    decreases re
  {
    reveal L5ScopeV1RE();
    match re
    case Re_alt(r1, r2) => L5ScopeV1ImpliesL5(r1); L5ScopeV1ImpliesL5(r2);
    case Re_con(r1, r2) => L5ScopeV1ImpliesL5(r1); L5ScopeV1ImpliesL5(r2);
    case Re_quant(_, _, _, r1) => L5ScopeV1ImpliesL5(r1);
    case Re_capture(_, r1) => L5ScopeV1ImpliesL5(r1);
    case Re_lookaround(_, la, r1) => L5ScopeV1ImpliesL5(r1);
    case _ =>
  }

  /** The v1 scope descends into a look body (definitional at the node). */
  lemma L5ScopeV1LookBody(re: R.regex, lid: nat)
    requires L5ScopeV1RE(re) && lid in LTB.LookIds(re)
    ensures L5ScopeV1RE(NI.LookBodyOfRE(re, lid))
    decreases re
  {
    reveal L5ScopeV1RE();
    match re
    case Re_alt(r1, r2) =>
      if lid in LTB.LookIds(r1) { L5ScopeV1LookBody(r1, lid); } else { L5ScopeV1LookBody(r2, lid); }
    case Re_con(r1, r2) =>
      if lid in LTB.LookIds(r1) { L5ScopeV1LookBody(r1, lid); } else { L5ScopeV1LookBody(r2, lid); }
    case Re_quant(_, _, _, r1) => L5ScopeV1LookBody(r1, lid);
    case Re_capture(_, r1) => L5ScopeV1LookBody(r1, lid);
    case Re_lookaround(lid0, la, r1) =>
      if lid0 >= 0 && (lid0 as nat) == lid { } else { L5ScopeV1LookBody(r1, lid); }
    case _ =>
  }

  /** (L5) The L5 fragment scope, packaged: `L4Scope` with `NoPosLookbehindRE`
      widened to `NR.L5ScopeRE` (positive lookbehinds whose bodies are lookbehind-only). */
  ghost predicate L5Scope(raw: R.raw_regex)
    requires T.Latin1Wf(raw)
  {
    var re := R.lazy_prefix(R.annotate(raw));
    L5ScopeV1RE(re)                       // (L5 F7f) the v1 fragment (kind-split hub)
    && NR.NegLooksLookFreeRE(re)
    && T.TransWf(re)
    && forall c: nat :: c in PIV.CapIdsInLooks(re) ==> M.GNotUnderQuantL(T.Translate(re), c)
  }

  // ==========================================================================
  // THE MAIN THEOREM, L4: arbitrarily NESTED capturing positive lookaheads.
  // Mirrors `MainTheoremL3` on the RECURSIVE (depth-k) tier: the Rec composite
  // lockstep (`L3aCompositeCloseRec`) delivers the leaf ties WITH the deep
  // region-equality carrier; the FLookLoop banks' invariants (value/quant lifts,
  // child link, reverse/oracle-true invariants) key the two descent wrappers
  // (`ReverseCDeepFull` membership-in, `ForwardMemberOne` membership+value-out);
  // the final endpoint (`L3aEndpointAssemblyNestedFull2`) converts them into the
  // reconstructed-register denotation; `MainExtractionL5` finishes.
  //
  // The SINGLE remaining hypothesis is the NESTED ORACLE ENTRY `OracleOkSuffix`
  // (the depth-1 `OE.OracleOkFromColumns` chain composed with the gated build
  // characterization `OB.FBuildOracleCorrectAboveNested` — the V-model column
  // spec for nested rows), taken as a `requires` until that bridge lands.
  // ==========================================================================
  /** (L5 F7e-2) the L5 scope translates to the L-side `FC.L5PosLooksL`: a positive
      lookbehind's lookbehind-only body is `SD.GroupOkLB` (`FST.TranslateGroupOkLB`). */
  lemma L5ScopeL5PosL(re: R.regex)
    requires T.TransWf(re) && NR.L5ScopeRE(re)
    ensures FC.L5PosLooksL(T.Translate(re))
    decreases re
  {
    match re
    case Re_alt(r1, r2) => L5ScopeL5PosL(r1); L5ScopeL5PosL(r2);
    case Re_con(r1, r2) => L5ScopeL5PosL(r1); L5ScopeL5PosL(r2);
    case Re_quant(_, _, _, r1) => L5ScopeL5PosL(r1);
    case Re_capture(_, r1) => L5ScopeL5PosL(r1);
    case Re_lookaround(lid, la, r1) =>
      L5ScopeL5PosL(r1);
      if la.Lookbehind? {
        FG.LBOnlyEquiv(r1);
        FST.TranslateGroupOkLB(r1);
      }
    case _ =>
  }

  /** (L5 F7e-2) THE L5 EXTRACTION under the L5 scope — the
      leaf's closedness from the L5 ladder (`FC.FirstLeafClosedRecL5`), the rest is
      the scope-free `M.MainExtractionFromClosed`. */
  lemma MainExtractionL5(raw: R.raw_regex, str: string,
                         t: LT.Tree, thread: AI.Thread, leaf: LT.Leaf)
    requires NR.NestedFragmentRaw(raw)
    requires NR.NoNulledPlusRaw(raw)   // §2.5b interim gate conjunct
    requires NR.L5ScopeRE(R.lazy_prefix(R.annotate(raw)))
    requires NR.NegLooksLookFreeRE(R.lazy_prefix(R.annotate(raw)))
    requires T.Latin1Wf(raw)
    requires EL.BoolTreeLk(LES.TheRer(raw), [LS.Areg(LES.SpecRegex(raw))], LC.InitInput(str), BS.CannotExit, t)
    requires LS.IsTree(LES.TheRer(raw), [LS.Areg(LES.SpecRegex(raw))], LC.InitInput(str), LG.Empty, WP.Forward, t)
    requires CM.ThreadRegsWf(thread, 2 * R.max_group(R.annotate(raw)) + 2,
                             R.max_lookaround(R.annotate(raw)) + 1,
                             R.max_quant(R.annotate(raw)) + 1)
    requires M.QuantRegsFinal(thread)
    // L3b: for a CAPTURING lookbehind the engine registers hold the REVERSED span,
    // so the ordered spec leaf is the POSITIONAL normalization (`NormGm`) of the
    // reconstructed `GmOfLive`. NO-OP for forward matches (`NormGm` is identity on
    // ordered ranges), so this subsumes the old `leaf.1 == GmOfLive`.
    requires var re := R.lazy_prefix(R.annotate(raw));
             leaf.1 == PIV.NormGm(PIV.GmOfLive(re, thread.capture_regs, thread.look_regs, thread.quant_regs))
    requires LT.FirstLeaf(t, LC.InitInput(str)) == Some(leaf)
    requires AI.FFullMatch(raw, str)
          == Some(AI.filter_reset(R.annotate(raw), thread.capture_regs, thread.look_regs,
                                  thread.quant_regs, -1))
    ensures LES.MatcherSpec(raw, str, LES.Normalize(AI.FFullMatch(raw, str)))
  {
    hide T.TransWf, NR.PlusFragmentRE, NR.LookBehindFragmentRE, NR.CaptureFreeRE, NR.LookFreeRE, NR.LookBehindFragmentRaw, NR.CaptureFreeRaw, NR.LookFreeRaw, EL.PikeLkRegex, EL.LkGateOk, SD.GroupFreeL;
    var ast := R.annotate(raw);
    var re := R.lazy_prefix(ast);
    var rer := LES.TheRer(raw);
    var inp := LC.InitInput(str);
    var ngroups := LES.NGroups(raw);
    var ncap := 2 * R.max_group(ast) + 2;
    T.AnnotateWf(raw);
    NR.SpecRegexNestedFragment(raw);
    NR.SpecRegexNoNulledPlus(raw);   // §2.5b interim: NoNulledPlusRE(re)
    var caps := thread.capture_regs;
    var lk := thread.look_regs;
    var qt := thread.quant_regs;
    assert LES.SpecRegex(raw) == T.Translate(re);

    // closedness of the leaf gm
    assert LT.TreeRes(t, LG.Empty, inp, WP.Forward) == Some(leaf);
    assert M.OpenOf(LG.Empty) <= M.PendingCloses([LS.Areg(T.Translate(re))]);
    EL.TranslateFragmentPikeLkRec(re);
    assert EL.PikeLkActionsRec([LS.Areg(T.Translate(re))]) by {
      assert [LS.Areg(T.Translate(re))] == [LS.Areg(T.Translate(re))] + [];
      assert EL.PikeLkActionsRec([]);
      EL.PikeLkActionsRecConsIff(LS.Areg(T.Translate(re)), []);
    }
    assert M.LkClosedInGm(LG.Empty, [LS.Areg(T.Translate(re))]);   // Empty has no groups
    M.SpecRegexOuterLkDisjoint(raw);   // also ensures M.NoDupSeq(L.DefGroups(SpecRegex(raw)))
    assert T.Translate(re) == LES.SpecRegex(raw);
    assert M.OuterLkDisjoint([LS.Areg(T.Translate(re))]);
    assert M.NoDupRegsActs([LS.Areg(T.Translate(re))]) by { assert M.NoDupSeq(L.DefGroups(T.Translate(re))); }
    assert TRM.GmInBounds(LG.Empty, |inp.pref| + |inp.next|);   // Empty has no ranges
    L5ScopeL5PosL(re);                                        // (L5 F7e-2)
    assert FC.L5PosActsL([LS.Areg(T.Translate(re))]);
    assert M.NestDepthActsLe([LS.Areg(T.Translate(re))], M.NestDepthL(T.Translate(re)));
    FC.FirstLeafClosedRecL5(rer, [LS.Areg(T.Translate(re))], inp, BS.CannotExit, t, LG.Empty, leaf,
                            M.NestDepthL(T.Translate(re)));
    assert M.ClosedGm(leaf.1);
    M.MainExtractionFromClosed(raw, str, t, thread, leaf);
  }

  /** `InputAt(str, cp)` is a strict FORWARD suffix of `InputAt(str, k)` for
      `k < cp` — the decision procedure hits it after `cp - k` steps. */
  lemma InputAtSuffixFrom(str: string, k: nat, cp: nat)
    requires k < cp <= |str|
    ensures SSx.StrictSuffixForward(T.InputAt(str, cp), T.InputAt(str, k).next, T.InputAt(str, k).pref)
    decreases cp - k
  {
    var cur := T.InputAt(str, k);
    assert cur.next == str[k..] && |cur.next| > 0;
    var nxt := LC.Input(cur.next[1..], [cur.next[0]] + cur.pref);
    assert nxt == T.InputAt(str, k + 1) by {
      assert cur.next[1..] == str[k + 1..];
      assert str[..k + 1] == str[..k] + [str[k]];
      SSx.ReverseSnoc(str[..k], str[k]);
    }
    if k + 1 == cp {
    } else {
      InputAtSuffixFrom(str, k + 1, cp);
    }
  }

  /** `OracleOkSuffix` steps from the initial input to any `InpOfCp`. */
  lemma OracleOkSuffixAtCp(rer: LW.RegExpRecord, qm: AR.QMap, str: string, cp: nat)
    requires cp <= |str|
    requires LL.OracleOkSuffix(rer, qm, LC.InitInput(str))
    ensures LL.OracleOkSuffix(rer, qm, PIV.InpOfCp(str, cp))
  {
    OE.InitInputAt(str);
    assert PIV.InpOfCp(str, cp) == T.InputAt(str, cp) by { LS.ReverseLength(str[..cp]); }
    if cp == 0 {
      assert T.InputAt(str, 0) == LC.InitInput(str);
    } else {
      InputAtSuffixFrom(str, 0, cp);
      assert SSx.IsStrictSuffix(T.InputAt(str, cp), LC.InitInput(str), WP.Forward) by {
        assert LC.InitInput(str) == T.InputAt(str, 0);
      }
      LL.OracleOkSuffixStep(rer, qm, LC.InitInput(str), T.InputAt(str, cp));
    }
  }

  // ==========================================================================
  // THE NESTED ORACLE ENTRY (L4 depth-k — the last brick).
  // `OE.OracleOkFromColumns` for the NESTED fragment. The per-row column spec
  // is the V-model chain: `OB.FBuildOracleCorrectAboveNested` (bit ⟺
  // `LidReachesVFinal` against the FINAL view) + the V1/V2 span bridges
  // (`MatchesVToReachesWriteV` / `ReachesWriteVToMatchesV`) + the V3
  // mirror/remove-capture layer + the V4 accept-run characterization
  // (`AcceptRunCharacterizationV`) + `M.BodyTreeAtCpNested` (the body's engine
  // run at `cp` ⟺ its spec first leaf — which needs the INNER rows' oracle
  // truth, supplied by the recursion on the body, `decreases |LookIds|`).
  // Flavours: positive/negative lookAHEAD rows (backward build, mirrored) go
  // through the tree; negative lookBEHIND rows (forward build, look-free body
  // by `NegLooksLookFreeRE`) go through the blind span duality.
  // ==========================================================================

  /** Gated spans of a LOOK-FREE regex are blind spans: no gate is ever read. */
  lemma MatchesVLookFree(re: R.regex, str: string, ov: LOr.OracleView, i: int, j: int)
    requires NR.LookFreeRE(re)
    ensures OBV.MatchesV(re, str, ov, i, j) <==> OBr.Matches(re, str, i, j)
    decreases CP.rsize(re), 0, 0
  {
    match re
    case Re_alt(r1, r2) =>
      MatchesVLookFree(r1, str, ov, i, j); MatchesVLookFree(r2, str, ov, i, j);
    case Re_con(r1, r2) =>
      forall m: int
        ensures (OBV.MatchesV(r1, str, ov, i, m) && OBV.MatchesV(r2, str, ov, m, j))
           <==> (OBr.Matches(r1, str, i, m) && OBr.Matches(r2, str, m, j))
      { MatchesVLookFree(r1, str, ov, i, m); MatchesVLookFree(r2, str, ov, m, j); }
    case Re_quant(nul, qid, q, r1) =>
      forall k: nat
        ensures OBV.MatchesIterV(r1, k, str, ov, i, j) <==> OBr.MatchesIter(r1, k, str, i, j)
      { MatchesIterVLookFree(r1, k, str, ov, i, j); }
    case Re_capture(cid, r1) => MatchesVLookFree(r1, str, ov, i, j);
    case _ =>
  }

  /** The iteration-chain analogue (mutually recursive). */
  lemma MatchesIterVLookFree(r: R.regex, k: nat, str: string, ov: LOr.OracleView, i: int, j: int)
    requires NR.LookFreeRE(r)
    ensures OBV.MatchesIterV(r, k, str, ov, i, j) <==> OBr.MatchesIter(r, k, str, i, j)
    decreases CP.rsize(r), 1, k
  {
    if k > 0 {
      forall m: int
        ensures (OBV.MatchesV(r, str, ov, i, m) && OBV.MatchesIterV(r, k - 1, str, ov, m, j))
           <==> (OBr.Matches(r, str, i, m) && OBr.MatchesIter(r, k - 1, str, m, j))
      { MatchesVLookFree(r, str, ov, i, m); MatchesIterVLookFree(r, k - 1, str, ov, m, j); }
    }
  }

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

  /** The look-body row facts the nested entry needs beyond
      `M.LookBodyFactsNested`: the scope predicates descend into the body, and
      `LmOf(sub)` at `lid` IS the compiled table row (flavour + translated body);
      a NEGATIVE row's body is look-free (`NegLooksLookFreeRE`). */
  lemma LookBodyRowNested(sub: R.regex, crv: CP.FCompiled, lid: nat)
    requires T.TransWf(sub) && LTB.LookUnique(sub) && LTB.LookTablesOk(sub, crv)
    requires M.NoPosLookbehindRE(sub) && NR.NegLooksLookFreeRE(sub)
    requires lid in LTB.LookIds(sub)
    ensures var body := NI.LookBodyOfRE(sub, lid);
            T.TransWf(body) && M.NoPosLookbehindRE(body) && NR.NegLooksLookFreeRE(body)
            && (lid as int) in OE.LmOf(sub)
            && exists la: R.lookaround ::
              LTB.LookEntryOk(crv, lid as int, la, body)
              && OE.LmOf(sub)[lid as int] == (T.TrLookaround(la), T.Translate(body))
              && !la.Lookbehind?
              && ((la.NegLookahead? || la.NegLookbehind?) ==> NR.LookFreeRE(body))
    decreases sub
  {
    OE.LmOfDom(sub);
    match sub
    case Re_alt(r1, r2) =>
      OE.LmOfDom(r1); OE.LmOfDom(r2);
      if lid in LTB.LookIds(r1) {
        LookBodyRowNested(r1, crv, lid);
        assert lid !in LTB.LookIds(r2);                    // LookUnique disjointness
        assert (lid as int) !in OE.LmOf(r2);
        assert OE.LmOf(sub)[lid as int] == OE.LmOf(r1)[lid as int];
      } else {
        LookBodyRowNested(r2, crv, lid);
        assert OE.LmOf(sub)[lid as int] == OE.LmOf(r2)[lid as int];
      }
    case Re_con(r1, r2) =>
      OE.LmOfDom(r1); OE.LmOfDom(r2);
      if lid in LTB.LookIds(r1) {
        LookBodyRowNested(r1, crv, lid);
        assert lid !in LTB.LookIds(r2);                    // LookUnique disjointness
        assert (lid as int) !in OE.LmOf(r2);
        assert OE.LmOf(sub)[lid as int] == OE.LmOf(r1)[lid as int];
      } else {
        LookBodyRowNested(r2, crv, lid);
        assert OE.LmOf(sub)[lid as int] == OE.LmOf(r2)[lid as int];
      }
    case Re_quant(_, _, _, r1) => LookBodyRowNested(r1, crv, lid);
    case Re_capture(_, r1) => LookBodyRowNested(r1, crv, lid);
    case Re_lookaround(lid0, la0, r1) =>
      if lid0 >= 0 && (lid0 as nat) == lid {
        assert NI.LookBodyOfRE(sub, lid) == r1;
        assert LTB.LookEntryOk(crv, lid as int, la0, r1);   // LookTablesOk's lookaround case
        assert OE.LmOf(sub)[lid as int] == (T.TrLookaround(la0), T.Translate(r1));
        assert !la0.Lookbehind?;                            // NoPosLookbehindRE
        assert (la0.NegLookahead? || la0.NegLookbehind?) ==> NR.LookFreeRE(r1);   // NegLooksLookFreeRE
      } else {
        assert lid in LTB.LookIds(r1);
        OE.LmOfDom(r1);
        LookBodyRowNested(r1, crv, lid);
        assert lid0 != lid as int;
        assert OE.LmOf(sub)[lid as int] == OE.LmOf(r1)[lid as int];
      }
  }

  /** (L5) The L5-scope twin of `LookBodyRowNested`: the row facts under
      `NR.L5ScopeRE` — the owning look is either not a positive lookbehind or one
      whose body is lookbehind-only; the body is itself in scope. */
  lemma LookBodyRowL5(sub: R.regex, crv: CP.FCompiled, lid: nat)
    requires T.TransWf(sub) && LTB.LookUnique(sub) && LTB.LookTablesOk(sub, crv)
    requires NR.L5ScopeRE(sub) && NR.NegLooksLookFreeRE(sub)
    requires lid in LTB.LookIds(sub)
    ensures var body := NI.LookBodyOfRE(sub, lid);
            T.TransWf(body) && NR.L5ScopeRE(body) && NR.NegLooksLookFreeRE(body)
            && (lid as int) in OE.LmOf(sub)
            && exists la: R.lookaround ::
              LTB.LookEntryOk(crv, lid as int, la, body)
              && OE.LmOf(sub)[lid as int] == (T.TrLookaround(la), T.Translate(body))
              && (la.Lookbehind? ==> NR.LBOnlyLooksRE(body))
              && ((la.NegLookahead? || la.NegLookbehind?) ==> NR.LookFreeRE(body))
    decreases sub
  {
    OE.LmOfDom(sub);
    match sub
    case Re_alt(r1, r2) =>
      OE.LmOfDom(r1); OE.LmOfDom(r2);
      if lid in LTB.LookIds(r1) {
        LookBodyRowL5(r1, crv, lid);
        assert lid !in LTB.LookIds(r2);                    // LookUnique disjointness
        assert (lid as int) !in OE.LmOf(r2);
        assert OE.LmOf(sub)[lid as int] == OE.LmOf(r1)[lid as int];
      } else {
        LookBodyRowL5(r2, crv, lid);
        assert OE.LmOf(sub)[lid as int] == OE.LmOf(r2)[lid as int];
      }
    case Re_con(r1, r2) =>
      OE.LmOfDom(r1); OE.LmOfDom(r2);
      if lid in LTB.LookIds(r1) {
        LookBodyRowL5(r1, crv, lid);
        assert lid !in LTB.LookIds(r2);                    // LookUnique disjointness
        assert (lid as int) !in OE.LmOf(r2);
        assert OE.LmOf(sub)[lid as int] == OE.LmOf(r1)[lid as int];
      } else {
        LookBodyRowL5(r2, crv, lid);
        assert OE.LmOf(sub)[lid as int] == OE.LmOf(r2)[lid as int];
      }
    case Re_quant(_, _, _, r1) => LookBodyRowL5(r1, crv, lid);
    case Re_capture(_, r1) => LookBodyRowL5(r1, crv, lid);
    case Re_lookaround(lid0, la0, r1) =>
      if lid0 >= 0 && (lid0 as nat) == lid {
        assert NI.LookBodyOfRE(sub, lid) == r1;
        assert LTB.LookEntryOk(crv, lid as int, la0, r1);   // LookTablesOk's lookaround case
        assert OE.LmOf(sub)[lid as int] == (T.TrLookaround(la0), T.Translate(r1));
        assert la0.Lookbehind? ==> NR.LBOnlyLooksRE(r1);     // L5ScopeRE
        assert NR.L5ScopeRE(r1);
        assert (la0.NegLookahead? || la0.NegLookbehind?) ==> NR.LookFreeRE(r1);   // NegLooksLookFreeRE
      } else {
        assert lid in LTB.LookIds(r1);
        OE.LmOfDom(r1);
        LookBodyRowL5(r1, crv, lid);
        assert lid0 != lid as int;
        assert OE.LmOf(sub)[lid as int] == OE.LmOf(r1)[lid as int];
      }
  }

}
