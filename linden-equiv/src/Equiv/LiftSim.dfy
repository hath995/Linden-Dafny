// L3a — THE LIFT: the standalone parallel simulation VM ↔ machine B.
//
// SCAFFOLD (2026-08-02): definitions are REAL and resolve; the lemmas are
// BODILESS — each carries a FILL note naming its template and ingredients.
// Fill order: TtLkSameTree → GateStepValue → LiftInit → LiftAdvanceEpsilon →
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
include "MainTheorem.dfy"
include "PikeTreeLk.dfy"

/** The lift: a per-thread pairing between the RegElk VM and the LK-aware
    PikeTree machine on the SPEC tree, whose group-map tie carries the
    reconstructed inside-look capture values. Scaffold — lemmas are bodiless. */
module LindenElkLiftSim {
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
  import T = LindenElkTranslate
  import RC = Charclasses
  import LL = LindenElkLookLeaves
  import LFU = FunctionalUtils
  import FS = FunctionalSemantics
  import SSx = StrictSuffix
  import LN = WarblreNumeric
  import PSM = LindenElkPikeSim
  import RL = LindenElkRegsLaws
  import WkE = LindenElkWalkOkEntry
  import TT = LindenElkTreeThread
  import NUL = LindenElkNullable
  import CE = LindenElkCheckErase
  import TREP = LindenElkTreeRep

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

  /** The keystone's `Empty` hypothesis, as a walk-state invariant: any gate
      pending without an intervening reset has its body groups ABSENT from the
      accumulated map. First encounter: never set; re-entry: the iteration's
      `Reset` cleared them; other lids' merges are disjoint
      (`M.LmOfBodiesDisjoint`). */
  ghost predicate GateAheadClear(acts: LS.Actions, gmt: LG.GroupMap) {
    forall lk: L.Lookaround, r1: L.Regex | GatePending(acts, lk, r1) ::
      forall g :: g in L.DefGroups(r1) ==> g !in gmt
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
              g in gmb && gmt[g] == gmb[g]
  }

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
    || (exists acts: LS.Actions, b: BS.LoopBool ::
          AR.ActionsRepL(rer, qm, acts, code, pc)
          && EL.PikeLkActions(acts)
          && ATR.EaOf(b) == ea
          && EL.BoolTreeLk(rer, acts, inp, b, tb)
          && GateAheadClear(acts, gmt)
          // NoDup walk-invariant (audit 2026-08-03): the gate-disjointness the
          // CheckOracle continuation needs. Established at entry via
          // `TranslateDefGroupsNoDup`, preserved by every peel (`NoDupAllDefsTail`).
          && M.NoDupSeq(M.AllDefsActs(acts)))
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

  /** Best-match tie: `None` together, or the recorded B leaf carries the
      winning thread's values on both sides of `S`. */
  ghost predicate BestTieLk(re: R.regex, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
                            S: set<LG.GroupId>, bbest: Option<LT.Leaf>, bm: Option<AI.Thread>,
                            ncap: int, nlook: int, nquant: int) {
    (bbest.None? <==> bm.None?)
    && (bbest.Some? ==>
          bm.Some?
          && GmtTieOutside(re, bm.value, bbest.value.1, S)
          && GmtTieInside(crv, str, ov, bm.value, bbest.value.1, S, ncap, nlook, nquant))
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
      && BestTieLk(re, crv, str, ov, S, bbest, vms.bestmatch, ncap, nlook, nquant)
      && SeenRepLk(rer, qm, code, inp, bseen, vms.processed,
                   PIV.HdTreeOf(bactive), PIV.HeadPcOf(vms.active))
      && IsblockedRepLk(rer, qm, code, inp, bseen, vms.isblocked)
      // the gate helpers read the oracle column at the current input; the
      // walk carries this (OracleOkSuffixStep advances it with cp)
      && LL.OracleOkSuffix(rer, qm, inp)
  }

  // ---- seen-tracking bricks (mirror PIV's SeenInclusion bookkeeping) ---------

  /** Initial state satisfies `SeenRepLk` vacuously (`init_bpcset` is all-false,
      so no `(pc, b)` is processed). Mirror of `PIV.InitialInclusionRE`. Feeds the
      `LiftInitC`/`L3aCompositeClose` entry (`bseen == SS.InitialSeenTrees`). */
  lemma InitialSeenRepLk(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                         current: Option<LT.Tree>, currentpc: nat, n: int)
    ensures SeenRepLk(rer, qm, code, inp, SS.InitialSeenTrees, AI.init_bpcset(n), current, currentpc)
  {
    forall pc: nat, b: bool | AI.bpc_mem(AI.init_bpcset(n), pc, b)
      ensures false
    { }
  }

  /** After memoizing the current tree `t` at `(pc, b)`, `SeenRepLk` still holds —
      every entry resolves to the LEFT (seen-tree) disjunct. Mirror of
      `PIV.AddInclusionRE`. Used at B's pts_active/pts_match/pts_blocked steps
      (each does `SS.AddSeenTrees(seen, active[0].0)` on the just-processed head). */
  lemma AddSeenRepLk(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                     treeseen: SS.SeenTrees, processed: AI.Bpcset, t: LT.Tree, pc: nat, b: bool,
                     nextcurrent: Option<LT.Tree>, nextpc: nat)
    requires SeenRepLk(rer, qm, code, inp, treeseen, processed, Some(t), pc)
    requires TreeRepLkRE(rer, qm, code, inp, t, pc, b)
    ensures SeenRepLk(rer, qm, code, inp, SS.AddSeenTrees(treeseen, t),
                      AI.bpc_add(processed, pc, b), nextcurrent, nextpc)
  {
    forall pc0: nat, b0: bool | AI.bpc_mem(AI.bpc_add(processed, pc, b), pc0, b0)
      ensures (exists t': LT.Tree :: SS.Inseen(SS.AddSeenTrees(treeseen, t), t')
                 && TreeRepLkRE(rer, qm, code, inp, t', pc0, b0))
           || (TT.StuttersRE(pc0, code) && exists t': LT.Tree ::
                 PIV.StutterChainTo(code, pc0, nextpc) && nextcurrent == Some(t')
                 && TreeRepLkRE(rer, qm, code, inp, t', pc0, b0))
    {
      PIV.BpcAddMemFwd(processed, pc, b, pc0, b0);
      if pc0 == pc && b0 == b {
        SS.InAdd(treeseen, t, t);            // Inseen(AddSeenTrees(treeseen, t), t)
      } else {
        assert AI.bpc_mem(processed, pc0, b0);
        if exists t': LT.Tree :: SS.Inseen(treeseen, t') && TreeRepLkRE(rer, qm, code, inp, t', pc0, b0) {
          var t': LT.Tree :| SS.Inseen(treeseen, t') && TreeRepLkRE(rer, qm, code, inp, t', pc0, b0);
          SS.InAdd(treeseen, t', t);
        } else {
          // right disjunct at (pc0,b0): current == Some(t) forces the witness to be
          // t, now memoized ⟹ new LEFT disjunct.
          var t': LT.Tree :| TT.StuttersRE(pc0, code) && PIV.StutterChainTo(code, pc0, pc)
            && Some(t) == Some(t') && TreeRepLkRE(rer, qm, code, inp, t', pc0, b0);
          SS.InAdd(treeseen, t', t);
        }
      }
    }
  }

  /** Growing only the seen set (no new processed slot) preserves `SeenRepLk`:
      LEFT witnesses survive the add, the stutter disjunct is untouched. Mirror of
      `PIV.SeenGrowInclusionRE` (B's do-while fork memoizes a second tree). */
  lemma SeenGrowSeenRepLk(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                          treeseen: SS.SeenTrees, processed: AI.Bpcset, extra: LT.Tree,
                          current: Option<LT.Tree>, currentpc: nat)
    requires SeenRepLk(rer, qm, code, inp, treeseen, processed, current, currentpc)
    ensures SeenRepLk(rer, qm, code, inp, SS.AddSeenTrees(treeseen, extra),
                      processed, current, currentpc)
  {
    forall pc0: nat, b0: bool | AI.bpc_mem(processed, pc0, b0)
      ensures (exists t': LT.Tree :: SS.Inseen(SS.AddSeenTrees(treeseen, extra), t')
                 && TreeRepLkRE(rer, qm, code, inp, t', pc0, b0))
           || (TT.StuttersRE(pc0, code) && exists t': LT.Tree ::
                 PIV.StutterChainTo(code, pc0, currentpc) && current == Some(t')
                 && TreeRepLkRE(rer, qm, code, inp, t', pc0, b0))
    {
      if exists t': LT.Tree :: SS.Inseen(treeseen, t') && TreeRepLkRE(rer, qm, code, inp, t', pc0, b0) {
        var t': LT.Tree :| SS.Inseen(treeseen, t') && TreeRepLkRE(rer, qm, code, inp, t', pc0, b0);
        SS.InAdd(treeseen, t', extra);
      }
    }
  }

  /** Skipping an already-seen tree leaves `SeenRepLk` intact (the stutter
      disjunct promotes to LEFT since the tree is already memoized), advancing the
      head pointer. Mirror of `PIV.SkipInclusionRE` — B's `pts_skip` case. */
  lemma SkipSeenRepLk(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                      treeseen: SS.SeenTrees, processed: AI.Bpcset, tree: LT.Tree, currentpc: nat,
                      current: Option<LT.Tree>, nextpc: nat)
    requires SeenRepLk(rer, qm, code, inp, treeseen, processed, Some(tree), currentpc)
    requires SS.Inseen(treeseen, tree)
    ensures SeenRepLk(rer, qm, code, inp, treeseen, processed, current, nextpc)
  {
    forall pc0: nat, b0: bool | AI.bpc_mem(processed, pc0, b0)
      ensures (exists t': LT.Tree :: SS.Inseen(treeseen, t')
                 && TreeRepLkRE(rer, qm, code, inp, t', pc0, b0))
           || (TT.StuttersRE(pc0, code) && exists t': LT.Tree ::
                 PIV.StutterChainTo(code, pc0, nextpc) && current == Some(t')
                 && TreeRepLkRE(rer, qm, code, inp, t', pc0, b0))
    {
      if exists t': LT.Tree :: SS.Inseen(treeseen, t') && TreeRepLkRE(rer, qm, code, inp, t', pc0, b0) {
      } else {
        var t': LT.Tree :| TT.StuttersRE(pc0, code) && PIV.StutterChainTo(code, pc0, currentpc)
          && Some(tree) == Some(t') && TreeRepLkRE(rer, qm, code, inp, t', pc0, b0);
        assert SS.Inseen(treeseen, t');   // t' == tree, already seen
      }
    }
  }

  /** Marking a slot processed whose tree is ALREADY memoized (B skips, seen
      unchanged): the new slot resolves LEFT with the head itself; old escape
      entries promote to LEFT since their witness (the head) is seen. The
      `Consume`-dedup drop's seen brick. */
  lemma SeenAddProcessedSlotRepLk(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                                  treeseen: SS.SeenTrees, processed: AI.Bpcset, t: LT.Tree,
                                  pc: nat, b: bool, current: Option<LT.Tree>, nextpc: nat)
    requires SeenRepLk(rer, qm, code, inp, treeseen, processed, Some(t), pc)
    requires SS.Inseen(treeseen, t)
    requires TreeRepLkRE(rer, qm, code, inp, t, pc, b)
    ensures SeenRepLk(rer, qm, code, inp, treeseen, AI.bpc_add(processed, pc, b), current, nextpc)
  {
    forall pc0: nat, b0: bool | AI.bpc_mem(AI.bpc_add(processed, pc, b), pc0, b0)
      ensures (exists t': LT.Tree :: SS.Inseen(treeseen, t')
                 && TreeRepLkRE(rer, qm, code, inp, t', pc0, b0))
           || (TT.StuttersRE(pc0, code) && exists t': LT.Tree ::
                 PIV.StutterChainTo(code, pc0, nextpc) && current == Some(t')
                 && TreeRepLkRE(rer, qm, code, inp, t', pc0, b0))
    {
      PIV.BpcAddMemFwd(processed, pc, b, pc0, b0);
      if pc0 == pc && b0 == b {
        // LEFT with the head itself — already memoized.
      } else {
        assert AI.bpc_mem(processed, pc0, b0);
        if exists t': LT.Tree :: SS.Inseen(treeseen, t') && TreeRepLkRE(rer, qm, code, inp, t', pc0, b0) {
        } else {
          var t': LT.Tree :| TT.StuttersRE(pc0, code) && PIV.StutterChainTo(code, pc0, pc)
            && Some(t) == Some(t') && TreeRepLkRE(rer, qm, code, inp, t', pc0, b0);
          assert SS.Inseen(treeseen, t');   // t' == t, already seen ⟹ LEFT
        }
      }
    }
  }

  /** Processing a STUTTER pc (Jmp/BeginLoop — B does not step, nothing is
      memoized): the new processed slot resolves to the stutter escape hatch,
      whose chain extends by the one stutter step to the head's new pc.
      Mirror of `PIV.StutterInclusionRE`. */
  lemma StutterSeenRepLk(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                         treeseen: SS.SeenTrees, processed: AI.Bpcset, t: LT.Tree, pc: nat, b: bool,
                         nextpc: nat)
    requires PIV.StutterSuccIs(code, pc, nextpc)
    requires SeenRepLk(rer, qm, code, inp, treeseen, processed, Some(t), pc)
    requires TT.StuttersRE(pc, code)
    requires TreeRepLkRE(rer, qm, code, inp, t, pc, b)
    ensures SeenRepLk(rer, qm, code, inp, treeseen, AI.bpc_add(processed, pc, b), Some(t), nextpc)
  {
    forall pc0: nat, b0: bool | AI.bpc_mem(AI.bpc_add(processed, pc, b), pc0, b0)
      ensures (exists t': LT.Tree :: SS.Inseen(treeseen, t')
                 && TreeRepLkRE(rer, qm, code, inp, t', pc0, b0))
           || (TT.StuttersRE(pc0, code) && exists t': LT.Tree ::
                 PIV.StutterChainTo(code, pc0, nextpc) && Some(t) == Some(t')
                 && TreeRepLkRE(rer, qm, code, inp, t', pc0, b0))
    {
      PIV.BpcAddMemFwd(processed, pc, b, pc0, b0);
      if pc0 == pc && b0 == b {
        // RIGHT disjunct: the just-stuttered head, one step from nextpc.
        assert PIV.StutterChainTo(code, pc, nextpc);   // base: StutterSuccIs(code, pc, nextpc)
      } else {
        assert AI.bpc_mem(processed, pc0, b0);
        if exists t': LT.Tree :: SS.Inseen(treeseen, t') && TreeRepLkRE(rer, qm, code, inp, t', pc0, b0) {
        } else {
          var t': LT.Tree :| TT.StuttersRE(pc0, code) && PIV.StutterChainTo(code, pc0, pc)
            && Some(t) == Some(t') && TreeRepLkRE(rer, qm, code, inp, t', pc0, b0);
          PIV.StutterChainExtend(code, pc0, pc, nextpc);   // StutterChainTo(code, pc0, nextpc)
        }
      }
    }
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
          assert pcmid == pc;
          WO.WalkOkEpsilon(acts, code, pc, ATR.EaOf(b));
          assert ATR.MsizeA(cont) < ATR.MsizeA(acts);
          tcan := ActionsTreeRepLkF(rer, qm, cont, code, pc, inp, b, t, n - 1);
        case Character(cd) => {
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
          var gidl := L.DefGroups(r1);
          if min > 0 {
            match delta {
              case Inf =>
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
    }
  }

  /** The fused fork lemma: at the do-while's backward fork with the walk
      allowed to exit, builds the canonical Choice whose PLANTED `Progress`
      wrapper is consumed by `tr_plus` together with the fork. Mirror of
      `ATR.AtBackForkTreeRep`: pops `Acheck`/`Epsilon`/`Sequence`/spent heads;
      every other head shape contradicts the pinned Fork; at the loop-view
      star the iteration is lifted to `CanExit` (`CE.BoolFlagLift`) and both
      branches delegate to the general construction. */
  lemma AtBackForkTreeLkF(rer: LW.RegExpRecord, qm: AR.QMap, acts: LS.Actions, code: RB.code,
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
                    assert il == [LS.Areg(r1)] + ([LS.Acheck(inp)] + ([LS.Areg(q0)] + cont));
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

  /** The construction, fuel-free: from a represented, walk-guarded stack's
      `BoolTreeLk` tree, the PLANTED canonical tree machine B runs — unique
      per `(pc, ea)` (`TreeRepLkDetermRE`) and leaf-equal to the spec tree
      (erasure-equal, then `ProgEraseLeavesEq`). THE ONE INVOCATION SITE is
      the entry pairing (`WkE.WalkOkEntry` supplies `WalkOk` there);
      downstream the canonical tie is maintained by per-instruction
      `TreeRepLkRE` inversions, never by re-running this. */
  lemma ActionsTreeRepLkRE(rer: LW.RegExpRecord, qm: AR.QMap, acts: LS.Actions, code: RB.code,
                           pc: nat, inp: LC.Input, b: BS.LoopBool, t: LT.Tree)
    returns (tcan: LT.Tree)
    requires EL.PikeLkActions(acts)
    requires AR.ActionsRepL(rer, qm, acts, code, pc)
    requires WO.WalkOk(acts, code, pc, ATR.EaOf(b))
    requires EL.BoolTreeLk(rer, acts, inp, b, t)
    ensures TreeRepLkRE(rer, qm, code, inp, tcan, pc, ATR.EaOf(b))
    ensures CE.ProgErase(tcan) == CE.ProgErase(t)
  {
    ATR.ActionsRepLToFuel(rer, qm, acts, code, pc);
    var n: nat :| ATR.ActionsRepFuelL(rer, qm, acts, code, pc, n);
    tcan := ActionsTreeRepLkF(rer, qm, acts, code, pc, inp, b, t, n);
  }

  /** (1) t-side determinism — QUOTIENTED (2026-08-05). The exact-tree
      statement is FALSE (see the section header above: Progress-planting at
      backward forks). The TRUE statement is confluence MODULO `ProgErase`,
      which is what the seen/skip pairing actually needs once B's memo is
      keyed on erased trees. FILL: bridge `ActionsRepL + BoolTreeLk ⟹
      ETreeRepLk(CE.ProgErase(t))` (mirror `ActionsTreeRepFRE`'s fuel induction,
      LK nodes kept, no tstar construction), then `ETreeRepLkDeterm` closes.
      The bridge needs the b == CanExit side condition at backward-fork heads
      (from `NonNullableL` of loop-view bodies inductively; at the TOP from
      the invariant fact that VM threads at a `BackForkAt` pc have
      `exit_allowed` — carried in `LiftInvC`). */
  lemma TtLkSameTree(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                     t1: LT.Tree, t2: LT.Tree, pc: nat, ea: bool)
    requires !rer.multiline
    requires TtLk(rer, qm, code, inp, t1, pc, ea)
    requires TtLk(rer, qm, code, inp, t2, pc, ea)
    ensures CE.ProgErase(t1) == CE.ProgErase(t2)

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
              g in gmb && gmt2[g] == gmb[g]
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
                g in gmb'' && gmt[g] == gmb''[g];
        var l'': int :|
          0 <= l'' < nlook && g in PIV.CapIds(M.VBody(crv, l''))
          && M.MatchedPosLA(crv, th.look_regs, l'')
          && var rf'' := M.FreshBodyMatch(crv, str, l'', th.look_regs, ov, ncap, nlook, nquant);
             rf''.Some?
             && var gmb'' := PIV.GmOfLive(M.VBody(crv, l''), rf''.value.capture_regs,
                                          rf''.value.look_regs, rf''.value.quant_regs);
                g in gmb'' && gmt[g] == gmb''[g];
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

  /** (3) Initial pairing: fresh VM state ↔ `PikeTreeInitialState(tcan, inp)`
      where `tcan` is the PLANTED CANONICAL entry tree (constructed here from
      the raw entry walk tree `t` by `ActionsTreeRepLkRE` + `WkE.WalkOkEntry`;
      `t` remains the value layer's erasure witness, and
      `ProgErase(tcan) == ProgErase(t)` is the endpoint `FirstLeaf` glue). */
  lemma LiftInit(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code,
                 crv: CP.FCompiled, str: string, ov: LOr.OracleView, S: set<LG.GroupId>,
                 t: LT.Tree, vms: AI.VmState, ncap: int, nlook: int, nquant: int)
    returns (tcan: LT.Tree)
    requires !rer.multiline
    requires T.TransWf(re) && NR.LookBehindFragmentRE(re) && PIV.CapUnique(re)
    requires code == CP.compile_to_bytecode(re)
    requires AR.ActionsRepL(rer, qm, [LS.Areg(T.Translate(re))], code, 0)
    requires LL.OracleOkSuffix(rer, qm, LC.InitInput(str))
    requires EL.BoolTreeLk(rer, [LS.Areg(T.Translate(re))], LC.InitInput(str), BS.CannotExit, t)
    requires vms.cp == 0
    requires vms.active == [AI.init_thread(AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant))]
    requires vms.blocked == [] && vms.bestmatch.None?
    requires vms.processed == AI.init_bpcset(|code|)
    requires vms.isblocked == AI.init_pcset(|code|)
    requires PIV.ContextOkRE(str, vms.cp, vms.context)
    ensures TreeRepLkRE(rer, qm, code, LC.InitInput(str), tcan, 0, false)
    ensures CE.ProgErase(tcan) == CE.ProgErase(t)   // endpoint glue: FirstLeaf(tcan) == FirstLeaf(t)
    ensures LiftInv(rer, qm, re, code, crv, str, ov, S,
                    PT.PikeTreeInitialState(tcan, LC.InitInput(str)), vms, ncap, nlook, nquant)
  {
    var inp := LC.InitInput(str);
    var itr := AI.init_thread(AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant));
    var acts := [LS.Areg(T.Translate(re))];

    // inp == InpOfCp(str, 0)
    assert str[..0] == [] && str[0..] == str;
    assert LC.Reverse(str[..0]) == [];
    assert inp == PIV.InpOfCp(str, 0);

    // entry walk-state facts
    EL.TranslateFragmentPikeLk(re);                           // PikeLkRegex(Translate(re))
    EL.PikeLkActionsConsIff(LS.Areg(T.Translate(re)), []);    // PikeLkActions(acts)
    assert EL.PikeLkActions(acts);
    PIV.GmOfLiveInit(re, ncap, nlook, nquant);               // GmOfLive(re, init...) == Empty

    // the single entry thread pairs with (t, Empty)
    assert ThreadRepLk(rer, qm, re, code, inp, crv, str, ov, S, t, LG.Empty, itr, ncap, nlook, nquant) by {
      assert itr.pc == 0 && itr.exit_allowed == false;
      assert GateAheadClear(acts, LG.Empty);                 // Empty has no keys
      assert ATR.EaOf(BS.CannotExit) == itr.exit_allowed;
      TranslateDefGroupsNoDup(re);                            // NoDupSeq(DefGroups(Translate(re)))
      M.AllDefsActsCons(LS.Areg(T.Translate(re)), []);
      assert M.AllDefsActs(acts) == L.DefGroups(T.Translate(re));   // AllDefsActs([]) == []
      assert exists actsw: LS.Actions, bw: BS.LoopBool ::
          AR.ActionsRepL(rer, qm, actsw, code, itr.pc as nat)
          && EL.PikeLkActions(actsw)
          && ATR.EaOf(bw) == itr.exit_allowed
          && EL.BoolTreeLk(rer, actsw, inp, bw, t)
          && GateAheadClear(actsw, LG.Empty)
          && M.NoDupSeq(M.AllDefsActs(actsw));
      assert PIV.GmOfLive(re, itr.capture_regs, itr.look_regs, itr.quant_regs) == LG.Empty;
      assert GmtTieOutside(re, itr, LG.Empty, S);
      assert GmtTieInside(crv, str, ov, itr, LG.Empty, S, ncap, nlook, nquant);  // vacuous
    }
    // Construct machine B's PLANTED CANONICAL entry tree; the raw walk tree
    // `t` is its value-layer erasure witness.
    WkE.WalkOkEntry(re);
    assert WO.WalkOk(acts, code, 0, false);
    assert ATR.EaOf(BS.CannotExit) == false;
    tcan := ActionsTreeRepLkRE(rer, qm, acts, code, 0, inp, BS.CannotExit, t);
    var bst := PT.PikeTreeInitialState(tcan, inp);
    assert bst == PT.PTS(inp, [(tcan, LG.Empty)], None, [], SS.InitialSeenTrees);
    assert ThreadRepLkC(rer, qm, re, code, inp, crv, str, ov, S, tcan, LG.Empty, itr,
                        ncap, nlook, nquant) by {
      assert TreeRepLkRE(rer, qm, code, inp, tcan, itr.pc as nat, itr.exit_allowed);
      assert CE.ProgErase(t) == CE.ProgErase(tcan)
          && ThreadRepLk(rer, qm, re, code, inp, crv, str, ov, S, t, LG.Empty, itr, ncap, nlook, nquant);
    }
    assert ActiveRepLkC(rer, qm, re, code, inp, crv, str, ov, S, [(tcan, LG.Empty)], [itr], ncap, nlook, nquant);

    // blocked: both sides empty (vms.blocked == [])
    forall nextinp | LC.AdvanceInput(inp, WP.Forward) == Some(nextinp)
      ensures BlockedRepLkC(rer, qm, re, code, inp, nextinp, crv, str, ov, S, [],
                            PIV.MatchingBlocked(LC.Reverse(vms.blocked), inp), ncap, nlook, nquant)
    {
      assert LC.Reverse(vms.blocked) == [];
      assert PIV.MatchingBlocked([], inp) == [];
    }
    assert BestTieLk(re, crv, str, ov, S, None, vms.bestmatch, ncap, nlook, nquant);
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

  /** Concatenating `TrcPikeTreeLk` chains. */
  lemma TrcLkTrans(a: PT.PikeTreeState, b: PT.PikeTreeState, c: PT.PikeTreeState)
    requires PTL.TrcPikeTreeLk(a, b)
    requires PTL.TrcPikeTreeLk(b, c)
    ensures PTL.TrcPikeTreeLk(a, c)
  {
    TrcLkToN(a, b);
    TrcLkToN(b, c);
    var n: nat :| TrcLkN(a, b, n);
    var m: nat :| TrcLkN(b, c, m);
    TrcLkNTrans(a, b, c, n, m);
    TrcLkFromN(a, c, n + m);
  }

  /** A canonical head sits at a fetchable pc (every rule pins an instruction). */
  lemma TreeRepLkREInRange(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                           t: LT.Tree, pc: nat, b: bool)
    requires TreeRepLkRE(rer, qm, code, inp, t, pc, b)
    ensures NR.GetPcRE(code, pc).Some? && pc < |code|
  { }

  /** Growing the seen set preserves the isblocked pairing (witness carries).
      Mirror of `PSM.IsblockedGrow`. */
  lemma IsblockedGrowLk(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                        treeseen: SS.SeenTrees, isblocked: AI.pcset, extra: LT.Tree)
    requires IsblockedRepLk(rer, qm, code, inp, treeseen, isblocked)
    ensures IsblockedRepLk(rer, qm, code, inp, SS.AddSeenTrees(treeseen, extra), isblocked)
  {
    forall pc0: nat | AI.pc_mem(isblocked, pc0)
      ensures exists t: LT.Tree, b: bool ::
        SS.Inseen(SS.AddSeenTrees(treeseen, extra), t) && TreeRepLkRE(rer, qm, code, inp, t, pc0, b)
    {
      var t: LT.Tree, b: bool :| SS.Inseen(treeseen, t) && TreeRepLkRE(rer, qm, code, inp, t, pc0, b);
      SS.InAdd(treeseen, t, extra);
    }
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
      && M.NoDupSeq(M.AllDefsActs(acts));
    ActionsRepLThruJmp(rer, qm, acts, code, pc, x);
  }

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

  /** SKIP: the head's `(pc, ea)` is already processed — the VM drops it, and
      B fires `pts_skip`: the seen slot's canonical tree EQUALS the head's by
      `TreeRepLkDetermRE` (the whole point of the planted-canonical pivot);
      the stutter escape is killed by `NoStutterCycle`. */
  lemma LiftPreserveSkipLk(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
                           crv: CP.FCompiled, str: string, ov: LOr.OracleView, S: set<LG.GroupId>,
                           bst: PT.PikeTreeState, s: AI.VmState, ncap: int, nlook: int, nquant: int)
    returns (bst1: PT.PikeTreeState)
    requires PSM.StaticOkRE(qm, re, code, endl)
    requires bst.PTS?
    requires LiftInv(rer, qm, re, code, crv, str, ov, S, bst, s, ncap, nlook, nquant)
    requires |s.active| > 0
    requires AI.bpc_mem(s.processed, s.active[0].pc, s.active[0].exit_allowed)
    ensures PTL.PikeTreeStepLk(bst, bst1)
    ensures bst1.PTS?
    ensures LiftInv(rer, qm, re, code, crv, str, ov, S, bst1, s.(active := s.active[1..]),
                    ncap, nlook, nquant)
  {
    var PTS(inp, ta, best, tb, seen) := bst;
    var th := s.active[0];
    assert ActiveRepLkC(rer, qm, re, code, inp, crv, str, ov, S, ta, s.active, ncap, nlook, nquant);
    assert |ta| > 0;
    var t := ta[0].0;
    var gm := ta[0].1;
    assert ThreadRepLkC(rer, qm, re, code, inp, crv, str, ov, S, t, gm, th, ncap, nlook, nquant);
    var pc: nat := th.pc as nat;
    var ea := th.exit_allowed;
    assert TreeRepLkRE(rer, qm, code, inp, t, pc, ea);
    assert PIV.HdTreeOf(ta) == Some(t) && PIV.HeadPcOf(s.active) == pc;

    // The processed slot resolves LEFT: the stutter escape would need
    // StutterChainTo(pc, pc), impossible in tame code.
    assert AI.bpc_mem(s.processed, pc, ea);
    assert (exists t': LT.Tree :: SS.Inseen(seen, t') && TreeRepLkRE(rer, qm, code, inp, t', pc, ea))
        || (TT.StuttersRE(pc, code)
            && exists t': LT.Tree ::
                 PIV.StutterChainTo(code, pc, pc) && Some(t) == Some(t')
                 && TreeRepLkRE(rer, qm, code, inp, t', pc, ea));
    if !(exists t': LT.Tree :: SS.Inseen(seen, t') && TreeRepLkRE(rer, qm, code, inp, t', pc, ea)) {
      PIV.NoStutterCycle(code, pc);
      assert false;
    }
    var t': LT.Tree :| SS.Inseen(seen, t') && TreeRepLkRE(rer, qm, code, inp, t', pc, ea);
    TreeRepLkDetermRE(rer, qm, code, inp, t, t', pc, ea);
    assert SS.Inseen(seen, t);

    // pts_skip
    bst1 := PT.PTS(inp, ta[1..], best, tb, seen);
    assert PTL.PikeTreeStepLk(bst, bst1);

    // invariant at the successor
    SkipSeenRepLk(rer, qm, code, inp, seen, s.processed, t, pc,
                  PIV.HdTreeOf(ta[1..]), PIV.HeadPcOf(s.active[1..]));
    assert ActiveRepLkC(rer, qm, re, code, inp, crv, str, ov, S, ta[1..], s.active[1..],
                        ncap, nlook, nquant);
  }

  /** STUTTER (Jmp / BeginLoop): the VM relocates the head thread, B does not
      step — the SAME canonical tree represents at the relocated `(pc', ea')`
      (`tr_jmp`/`tr_begin`), the raw witness relocates with its stack, and the
      seen escape chain extends one step (`StutterSeenRepLk`). */
  lemma LiftPreserveStutterLk(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
                              crv: CP.FCompiled, str: string, ov: LOr.OracleView, S: set<LG.GroupId>,
                              bst: PT.PikeTreeState, s: AI.VmState, s1: AI.VmState, th': AI.Thread,
                              vms2: AI.VmState, ncap: int, nlook: int, nquant: int)
    requires PSM.StaticOkRE(qm, re, code, endl)
    requires bst.PTS?
    requires LiftInv(rer, qm, re, code, crv, str, ov, S, bst, s, ncap, nlook, nquant)
    requires |s.active| > 0
    requires !AI.bpc_mem(s.processed, s.active[0].pc, s.active[0].exit_allowed)
    requires s.active[0].pc >= 0
    requires s1 == s.(clock := s.clock + 1,
                      processed := AI.bpc_add(s.processed, s.active[0].pc, s.active[0].exit_allowed))
    requires (exists x: int ::
                NR.GetPcRE(code, s.active[0].pc as nat) == Some(RB.Jmp(x))
                && th' == s.active[0].(pc := x))
          || (NR.GetPcRE(code, s.active[0].pc as nat) == Some(RB.BeginLoop)
              && th' == s.active[0].(exit_allowed := false, pc := s.active[0].pc + 1))
    requires vms2 == s1.(active := [th'] + s1.active[1..])
    ensures LiftInv(rer, qm, re, code, crv, str, ov, S, bst, vms2, ncap, nlook, nquant)
  {
    var PTS(inp, ta, best, tb, seen) := bst;
    var th := s.active[0];
    assert ActiveRepLkC(rer, qm, re, code, inp, crv, str, ov, S, ta, s.active, ncap, nlook, nquant);
    assert |ta| > 0;
    var t := ta[0].0;
    var gm := ta[0].1;
    assert ThreadRepLkC(rer, qm, re, code, inp, crv, str, ov, S, t, gm, th, ncap, nlook, nquant);
    var pc: nat := th.pc as nat;
    var ea := th.exit_allowed;
    assert TreeRepLkRE(rer, qm, code, inp, t, pc, ea);
    var traw: LT.Tree :| CE.ProgErase(traw) == CE.ProgErase(t)
      && ThreadRepLk(rer, qm, re, code, inp, crv, str, ov, S, traw, gm, th, ncap, nlook, nquant);

    // the relocated head pairing
    var pc': nat;
    if exists x: int :: NR.GetPcRE(code, pc) == Some(RB.Jmp(x)) && th' == th.(pc := x) {
      var x: int :| NR.GetPcRE(code, pc) == Some(RB.Jmp(x)) && th' == th.(pc := x);
      TreeRepLkREAtJmp(rer, qm, code, inp, t, pc, ea, x);
      WalkPairLkAtJmp(rer, qm, code, inp, traw, gm, pc, ea, x);
      pc' := x as nat;
      assert PIV.StutterSuccIs(code, pc, pc');
    } else {
      TreeRepLkREAtBeginLoop(rer, qm, code, inp, t, pc, ea);
      WalkPairLkAtBeginLoop(rer, qm, code, inp, traw, gm, pc, ea);
      pc' := pc + 1;
      assert PIV.StutterSuccIs(code, pc, pc');
    }
    assert th'.pc == pc' as int;
    assert TreeRepLkRE(rer, qm, code, inp, t, pc', th'.exit_allowed);
    assert WalkPairLk(rer, qm, code, inp, traw, gm, pc', th'.exit_allowed);
    assert th'.capture_regs == th.capture_regs && th'.look_regs == th.look_regs
        && th'.quant_regs == th.quant_regs;
    assert GmtTieOutside(re, th', gm, S);
    assert GmtTieInside(crv, str, ov, th', gm, S, ncap, nlook, nquant);
    assert ThreadRepLk(rer, qm, re, code, inp, crv, str, ov, S, traw, gm, th', ncap, nlook, nquant);
    assert ThreadRepLkC(rer, qm, re, code, inp, crv, str, ov, S, t, gm, th', ncap, nlook, nquant);

    // active: same (tree, gm) list against the relocated head
    assert ActiveRepLkC(rer, qm, re, code, inp, crv, str, ov, S, ta[1..], s.active[1..],
                        ncap, nlook, nquant);
    assert vms2.active[0] == th' && vms2.active[1..] == s.active[1..];
    assert ta == [ta[0]] + ta[1..];
    assert ActiveRepLkC(rer, qm, re, code, inp, crv, str, ov, S, ta, vms2.active, ncap, nlook, nquant);

    // seen: the escape chain extends by one stutter step
    assert TT.StuttersRE(pc, code);
    assert PIV.HdTreeOf(ta) == Some(t) && PIV.HeadPcOf(s.active) == pc;
    StutterSeenRepLk(rer, qm, code, inp, seen, s.processed, t, pc, ea, pc');
    assert PIV.HeadPcOf(vms2.active) == pc';
  }

  /** ACCEPT: the VM records the winner and CUTS the queue; B fires
      `pts_match` — the head canonical tree IS `Match` and its `gm` carries
      exactly the two-sided value tie (`BestTieLk` straight from
      `ThreadRepLkC`'s payload). */
  lemma LiftPreserveAcceptLk(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
                             crv: CP.FCompiled, str: string, ov: LOr.OracleView, S: set<LG.GroupId>,
                             bst: PT.PikeTreeState, s: AI.VmState, s1: AI.VmState,
                             vms2: AI.VmState, ncap: int, nlook: int, nquant: int)
    returns (bst1: PT.PikeTreeState)
    requires PSM.StaticOkRE(qm, re, code, endl)
    requires bst.PTS?
    requires LiftInv(rer, qm, re, code, crv, str, ov, S, bst, s, ncap, nlook, nquant)
    requires |s.active| > 0
    requires !AI.bpc_mem(s.processed, s.active[0].pc, s.active[0].exit_allowed)
    requires s.active[0].pc >= 0
    requires NR.GetPcRE(code, s.active[0].pc as nat) == Some(RB.Accept)
    requires s1 == s.(clock := s.clock + 1,
                      processed := AI.bpc_add(s.processed, s.active[0].pc, s.active[0].exit_allowed))
    requires vms2 == s1.(active := [], bestmatch := Some(s.active[0]))
    ensures PTL.PikeTreeStepLk(bst, bst1)
    ensures bst1.PTS?
    ensures LiftInv(rer, qm, re, code, crv, str, ov, S, bst1, vms2, ncap, nlook, nquant)
  {
    var PTS(inp, ta, best, tb, seen) := bst;
    var th := s.active[0];
    assert ActiveRepLkC(rer, qm, re, code, inp, crv, str, ov, S, ta, s.active, ncap, nlook, nquant);
    assert |ta| > 0;
    var t := ta[0].0;
    var gm := ta[0].1;
    assert ThreadRepLkC(rer, qm, re, code, inp, crv, str, ov, S, t, gm, th, ncap, nlook, nquant);
    var pc: nat := th.pc as nat;
    var ea := th.exit_allowed;
    assert TreeRepLkRE(rer, qm, code, inp, t, pc, ea);
    TreeRepLkREAtAccept(rer, qm, code, inp, t, pc, ea);
    assert t == LT.Match;
    assert PTL.TreeBfsStepLk(t, gm, inp) == PT.StepMatch;

    // pts_match
    bst1 := PT.PTS(inp, [], Some((inp, gm)), tb, SS.AddSeenTrees(seen, t));
    assert PTL.PikeTreeStepLk(bst, bst1);

    // the value tie for the recorded best — straight from the head's payload
    var traw: LT.Tree :| CE.ProgErase(traw) == CE.ProgErase(t)
      && ThreadRepLk(rer, qm, re, code, inp, crv, str, ov, S, traw, gm, th, ncap, nlook, nquant);
    assert GmtTieOutside(re, th, gm, S);
    assert GmtTieInside(crv, str, ov, th, gm, S, ncap, nlook, nquant);
    assert BestTieLk(re, crv, str, ov, S, Some((inp, gm)), vms2.bestmatch, ncap, nlook, nquant);

    // bookkeeping: seen grows with the memoized head; active empty both sides
    AddSeenRepLk(rer, qm, code, inp, seen, s.processed, t, pc, ea,
                 PIV.HdTreeOf([]), PIV.HeadPcOf(vms2.active));
    IsblockedGrowLk(rer, qm, code, inp, seen, s.isblocked, t);
    assert ActiveRepLkC(rer, qm, re, code, inp, crv, str, ov, S, [], vms2.active, ncap, nlook, nquant);
  }

  /** DEAD HEAD, shared bookkeeping: the head canonical tree steps to an EMPTY
      `pts_active` (`Mismatch`/`LKFail` — `StepDead() == StepActive([])`), the
      VM drops the thread, B memoizes the dead tree. Every kill case
      (EndLoop/Anchor/gate) reduces to this after pinning the head shape. */
  lemma LiftDropDeadHeadLk(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
                           crv: CP.FCompiled, str: string, ov: LOr.OracleView, S: set<LG.GroupId>,
                           bst: PT.PikeTreeState, s: AI.VmState, s1: AI.VmState,
                           vms2: AI.VmState, ncap: int, nlook: int, nquant: int)
    returns (bst1: PT.PikeTreeState)
    requires PSM.StaticOkRE(qm, re, code, endl)
    requires bst.PTS?
    requires LiftInv(rer, qm, re, code, crv, str, ov, S, bst, s, ncap, nlook, nquant)
    requires |s.active| > 0
    requires !AI.bpc_mem(s.processed, s.active[0].pc, s.active[0].exit_allowed)
    requires s.active[0].pc >= 0
    requires |bst.active| > 0
    requires PTL.TreeBfsStepLk(bst.active[0].0, bst.active[0].1, bst.inp) == PT.StepActive([])
    requires s1 == s.(clock := s.clock + 1,
                      processed := AI.bpc_add(s.processed, s.active[0].pc, s.active[0].exit_allowed))
    requires vms2 == s1.(active := s1.active[1..])
    ensures PTL.PikeTreeStepLk(bst, bst1)
    ensures bst1.PTS?
    ensures LiftInv(rer, qm, re, code, crv, str, ov, S, bst1, vms2, ncap, nlook, nquant)
  {
    var PTS(inp, ta, best, tb, seen) := bst;
    var th := s.active[0];
    assert ActiveRepLkC(rer, qm, re, code, inp, crv, str, ov, S, ta, s.active, ncap, nlook, nquant);
    var t := ta[0].0;
    var gm := ta[0].1;
    assert ThreadRepLkC(rer, qm, re, code, inp, crv, str, ov, S, t, gm, th, ncap, nlook, nquant);
    var pc: nat := th.pc as nat;
    var ea := th.exit_allowed;
    assert TreeRepLkRE(rer, qm, code, inp, t, pc, ea);

    // pts_active with an empty successor list: the branch dies on both sides.
    bst1 := PT.PTS(inp, ta[1..], best, tb, SS.AddSeenTrees(seen, t));
    assert [] + ta[1..] == ta[1..];
    assert PTL.PikeTreeStepLk(bst, bst1);

    // bookkeeping at the successor
    assert PIV.HdTreeOf(ta) == Some(t) && PIV.HeadPcOf(s.active) == pc;
    AddSeenRepLk(rer, qm, code, inp, seen, s.processed, t, pc, ea,
                 PIV.HdTreeOf(ta[1..]), PIV.HeadPcOf(vms2.active));
    IsblockedGrowLk(rer, qm, code, inp, seen, s.isblocked, t);
    assert ActiveRepLkC(rer, qm, re, code, inp, crv, str, ov, S, ta[1..], s.active[1..],
                        ncap, nlook, nquant);
    assert vms2.active == s.active[1..];
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
      && TtLk(rer, qm, code, nextinp, traw, (p.0.pc + 1) as nat, true)
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

  /** CONSUME, pc not yet blocked: the VM blocks the head unconditionally;
      B blocks a matching `Read` (`pts_blocked`, keeping `BlockedRepLkC`
      aligned through the `MatchingBlocked` filter) or drops a `Mismatch`
      (empty `pts_active` — the doomed blocked thread is invisible to the
      filter). Mirror of `PSM.PreserveConsumeAdd`. */
  lemma LiftPreserveConsumeAddLk(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
                                 crv: CP.FCompiled, str: string, ov: LOr.OracleView, S: set<LG.GroupId>,
                                 bst: PT.PikeTreeState, s: AI.VmState, s1: AI.VmState,
                                 ce: RC.char_expectation, vms2: AI.VmState,
                                 ncap: int, nlook: int, nquant: int)
    returns (bst1: PT.PikeTreeState)
    requires PSM.StaticOkRE(qm, re, code, endl)
    requires bst.PTS?
    requires LiftInv(rer, qm, re, code, crv, str, ov, S, bst, s, ncap, nlook, nquant)
    requires |s.active| > 0
    requires !AI.bpc_mem(s.processed, s.active[0].pc, s.active[0].exit_allowed)
    requires s.active[0].pc >= 0
    requires NR.GetPcRE(code, s.active[0].pc as nat) == Some(RB.Consume(ce))
    requires s1 == s.(clock := s.clock + 1,
                      processed := AI.bpc_add(s.processed, s.active[0].pc, s.active[0].exit_allowed))
    requires !AI.pc_mem(s1.isblocked, s.active[0].pc)
    requires vms2 == s1.(blocked := [(s.active[0], ce)] + s1.blocked,
                         isblocked := AI.pc_add(s1.isblocked, s.active[0].pc),
                         active := s1.active[1..])
    ensures PTL.TrcPikeTreeLk(bst, bst1)
    ensures bst1.PTS?
    ensures LiftInv(rer, qm, re, code, crv, str, ov, S, bst1, vms2, ncap, nlook, nquant)
  {
    var PTS(inp, ta, best, tb, seen) := bst;
    var th := s.active[0];
    assert ActiveRepLkC(rer, qm, re, code, inp, crv, str, ov, S, ta, s.active, ncap, nlook, nquant);
    assert |ta| > 0;
    var t := ta[0].0;
    var gm := ta[0].1;
    assert ThreadRepLkC(rer, qm, re, code, inp, crv, str, ov, S, t, gm, th, ncap, nlook, nquant);
    var pc: nat := th.pc as nat;
    var ea := th.exit_allowed;
    assert TreeRepLkRE(rer, qm, code, inp, t, pc, ea);
    TreeRepLkREAtConsume(rer, qm, code, inp, t, pc, ea, ce);

    // shared list bookkeeping
    PSM.ReversePrepend((th, ce), s.blocked);
    PSM.MatchingBlockedSnoc(LC.Reverse(s.blocked), (th, ce), inp);

    // the new isblocked entry pc is covered by the freshly-seen head tree
    assert IsblockedRepLk(rer, qm, code, inp, SS.AddSeenTrees(seen, t), vms2.isblocked) by {
      forall pc0: nat | AI.pc_mem(vms2.isblocked, pc0)
        ensures exists t0: LT.Tree, b0: bool ::
          SS.Inseen(SS.AddSeenTrees(seen, t), t0) && TreeRepLkRE(rer, qm, code, inp, t0, pc0, b0)
      {
        PIV.PcAddMemFwd(s1.isblocked, th.pc, pc0);
        if pc0 == pc {
          SS.InAdd(seen, t, t);
          assert SS.Inseen(SS.AddSeenTrees(seen, t), t) && TreeRepLkRE(rer, qm, code, inp, t, pc0, ea);
        } else {
          assert AI.pc_mem(s.isblocked, pc0);
          var t0: LT.Tree, b0: bool :| SS.Inseen(seen, t0) && TreeRepLkRE(rer, qm, code, inp, t0, pc0, b0);
          SS.InAdd(seen, t0, t);
        }
      }
    }

    if AR.ReadCharE(ce, inp).Some? {
      // MATCHING: pts_blocked pairs the appended entries.
      var (c, nextinp0) := AR.ReadCharE(ce, inp).value;
      assert t.Read? && t.c == c
          && TreeRepLkRE(rer, qm, code, nextinp0, t.t, pc + 1, true);
      assert PTL.TreeBfsStepLk(t, gm, inp) == PT.StepBlocked(t.t);
      bst1 := PT.PTS(inp, ta[1..], best, tb + [(t.t, gm)], SS.AddSeenTrees(seen, t));
      assert PTL.PikeTreeStepLk(bst, bst1);
      TrcLkRefl(bst1);
      TrcLkCons(bst, bst1, bst1);

      // the raw child witness for the blocked pair: the head's raw witness
      // reads the same character (erasure pins the Read root)
      var traw: LT.Tree :| CE.ProgErase(traw) == CE.ProgErase(t)
        && ThreadRepLk(rer, qm, re, code, inp, crv, str, ov, S, traw, gm, th, ncap, nlook, nquant);
      assert WalkPairLk(rer, qm, code, inp, traw, gm, pc, ea);
      WalkPairLkImpliesTtLk(rer, qm, code, inp, traw, gm, pc, ea);
      TtLkAtConsume(rer, qm, code, inp, traw, pc, ea, ce);
      assert traw.Read? by {
        if !traw.Read? {
          assert traw == LT.Mismatch;
          assert CE.ProgErase(traw) == LT.Mismatch;
          assert CE.ProgErase(t).Read?;
          assert false;
        }
      }
      var nextinpw: LC.Input :| AR.ReadCharE(ce, inp) == Some((traw.c, nextinpw))
        && TtLk(rer, qm, code, nextinpw, traw.t, pc + 1, true);
      assert traw.c == c && nextinpw == nextinp0;    // ReadCharE is a function
      assert CE.ProgErase(traw.t) == CE.ProgErase(t.t) by {
        assert CE.ProgErase(traw) == LT.Read(traw.c, CE.ProgErase(traw.t));
        assert CE.ProgErase(t) == LT.Read(t.c, CE.ProgErase(t.t));
      }

      // blocked correspondence: the filter gains exactly the new pair
      forall nextinp | LC.AdvanceInput(inp, WP.Forward) == Some(nextinp)
        ensures BlockedRepLkC(rer, qm, re, code, inp, nextinp, crv, str, ov, S, tb + [(t.t, gm)],
                              PIV.MatchingBlocked(LC.Reverse(vms2.blocked), inp), ncap, nlook, nquant)
      {
        assert nextinp == nextinp0;
        assert PIV.MatchingBlocked(LC.Reverse(vms2.blocked), inp)
            == PIV.MatchingBlocked(LC.Reverse(s.blocked), inp) + [(th, ce)];
        assert GmtTieOutside(re, th, gm, S);
        assert GmtTieInside(crv, str, ov, th, gm, S, ncap, nlook, nquant);
        BlockedRepLkCSnoc(rer, qm, re, code, inp, nextinp, crv, str, ov, S, tb,
                          PIV.MatchingBlocked(LC.Reverse(s.blocked), inp), (t.t, gm), (th, ce),
                          ncap, nlook, nquant);
      }
      assert |inp.next| > 0;                          // ReadCharE Some
      assert LC.AdvanceInput(inp, WP.Forward).Some?;

      AddSeenRepLk(rer, qm, code, inp, seen, s.processed, t, pc, ea,
                   PIV.HdTreeOf(ta[1..]), PIV.HeadPcOf(vms2.active));
      assert ActiveRepLkC(rer, qm, re, code, inp, crv, str, ov, S, ta[1..], s.active[1..],
                          ncap, nlook, nquant);
      assert vms2.active == s.active[1..];
    } else {
      // MISMATCH: the tree is Mismatch and dies; the doomed blocked thread is
      // invisible to the filter.
      assert t == LT.Mismatch;
      assert PTL.TreeBfsStepLk(t, gm, inp) == PT.StepActive([]);
      bst1 := PT.PTS(inp, ta[1..], best, tb, SS.AddSeenTrees(seen, t));
      assert [] + ta[1..] == ta[1..];
      assert PTL.PikeTreeStepLk(bst, bst1);
      TrcLkRefl(bst1);
      TrcLkCons(bst, bst1, bst1);

      assert PIV.MatchingBlocked(LC.Reverse(vms2.blocked), inp)
          == PIV.MatchingBlocked(LC.Reverse(s.blocked), inp);

      AddSeenRepLk(rer, qm, code, inp, seen, s.processed, t, pc, ea,
                   PIV.HdTreeOf(ta[1..]), PIV.HeadPcOf(vms2.active));
      assert ActiveRepLkC(rer, qm, re, code, inp, crv, str, ov, S, ta[1..], s.active[1..],
                          ncap, nlook, nquant);
      assert vms2.active == s.active[1..];
    }
  }

  /** CONSUME, pc already blocked (dedup): the VM drops the head; B fires
      `pts_skip` — `IsblockedRepLk` holds a canonical tree at the `Consume`
      pc, whose rule is flag-independent, so determinism identifies it with
      the head's. Mirror of `PSM.PreserveConsumeDrop`. BODILESS. */
  lemma LiftPreserveConsumeDropLk(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
                                  crv: CP.FCompiled, str: string, ov: LOr.OracleView, S: set<LG.GroupId>,
                                  bst: PT.PikeTreeState, s: AI.VmState, s1: AI.VmState,
                                  ce: RC.char_expectation, vms2: AI.VmState,
                                  ncap: int, nlook: int, nquant: int)
    returns (bst1: PT.PikeTreeState)
    requires PSM.StaticOkRE(qm, re, code, endl)
    requires bst.PTS?
    requires LiftInv(rer, qm, re, code, crv, str, ov, S, bst, s, ncap, nlook, nquant)
    requires |s.active| > 0
    requires !AI.bpc_mem(s.processed, s.active[0].pc, s.active[0].exit_allowed)
    requires s.active[0].pc >= 0
    requires NR.GetPcRE(code, s.active[0].pc as nat) == Some(RB.Consume(ce))
    requires s1 == s.(clock := s.clock + 1,
                      processed := AI.bpc_add(s.processed, s.active[0].pc, s.active[0].exit_allowed))
    requires AI.pc_mem(s1.isblocked, s.active[0].pc)
    requires vms2 == s1.(active := s1.active[1..])
    ensures PTL.TrcPikeTreeLk(bst, bst1)
    ensures bst1.PTS?
    ensures LiftInv(rer, qm, re, code, crv, str, ov, S, bst1, vms2, ncap, nlook, nquant)
  {
    var PTS(inp, ta, best, tb, seen) := bst;
    var th := s.active[0];
    assert ActiveRepLkC(rer, qm, re, code, inp, crv, str, ov, S, ta, s.active, ncap, nlook, nquant);
    assert |ta| > 0;
    var t := ta[0].0;
    var gm := ta[0].1;
    assert ThreadRepLkC(rer, qm, re, code, inp, crv, str, ov, S, t, gm, th, ncap, nlook, nquant);
    var pc: nat := th.pc as nat;
    var ea := th.exit_allowed;
    assert TreeRepLkRE(rer, qm, code, inp, t, pc, ea);

    // the blocked pc's memoized canonical tree IS the head's — the Consume
    // rules are flag-independent, so the recorded flag transfers.
    assert IsblockedRepLk(rer, qm, code, inp, seen, s.isblocked);
    assert AI.pc_mem(s.isblocked, th.pc) && th.pc == pc as int;
    assert AI.pc_mem(s.isblocked, pc);
    var t': LT.Tree, b': bool :| SS.Inseen(seen, t') && TreeRepLkRE(rer, qm, code, inp, t', pc, b');
    TreeRepLkREAtConsume(rer, qm, code, inp, t', pc, b', ce);
    assert TreeRepLkRE(rer, qm, code, inp, t', pc, ea) by {
      match AR.ReadCharE(ce, inp) {
        case None =>
          assert t' == LT.Mismatch;      // tr_readfail — flag-independent
        case Some(pair) =>
          assert t'.Read? && t'.c == pair.0
              && TreeRepLkRE(rer, qm, code, pair.1, t'.t, pc + 1, true);   // tr_read — flag-independent
      }
    }
    TreeRepLkDetermRE(rer, qm, code, inp, t, t', pc, ea);
    assert SS.Inseen(seen, t);

    // pts_skip
    bst1 := PT.PTS(inp, ta[1..], best, tb, seen);
    assert PTL.PikeTreeStepLk(bst, bst1);
    TrcLkRefl(bst1);
    TrcLkCons(bst, bst1, bst1);

    // bookkeeping: the new processed slot's tree is already memoized
    assert PIV.HdTreeOf(ta) == Some(t) && PIV.HeadPcOf(s.active) == pc;
    SeenAddProcessedSlotRepLk(rer, qm, code, inp, seen, s.processed, t, pc, ea,
                              PIV.HdTreeOf(ta[1..]), PIV.HeadPcOf(vms2.active));
    assert ActiveRepLkC(rer, qm, re, code, inp, crv, str, ov, S, ta[1..], s.active[1..],
                        ncap, nlook, nquant);
    assert vms2.active == s.active[1..];
  }

  /** SETREG (group Open/Close): B steps the `GroupActionT` head, `gmt` moves
      by `GMUpdate` at the current index; outside-`S` tie via the GmOfLive
      machinery (the remaining SetReg VALUE-tie obligation), inside-`S` stable.
      Mirror of `PSM.PreserveOpenCase`/`PreserveCloseCase`. BODILESS. */
  lemma LiftPreserveSetRegLk(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
                             crv: CP.FCompiled, str: string, ov: LOr.OracleView, S: set<LG.GroupId>,
                             bst: PT.PikeTreeState, s: AI.VmState, s1: AI.VmState,
                             reg: int, th': AI.Thread, vms2: AI.VmState,
                             ncap: int, nlook: int, nquant: int)
    returns (bst1: PT.PikeTreeState)
    requires PSM.StaticOkRE(qm, re, code, endl)
    requires bst.PTS?
    requires LiftInv(rer, qm, re, code, crv, str, ov, S, bst, s, ncap, nlook, nquant)
    requires |s.active| > 0
    requires !AI.bpc_mem(s.processed, s.active[0].pc, s.active[0].exit_allowed)
    requires s.active[0].pc >= 0
    requires NR.GetPcRE(code, s.active[0].pc as nat) == Some(RB.SetRegisterToCP(reg))
    requires s1 == s.(clock := s.clock + 1,
                      processed := AI.bpc_add(s.processed, s.active[0].pc, s.active[0].exit_allowed))
    requires th' == s.active[0].(capture_regs := AReg.set_reg(s.active[0].capture_regs, reg, Some(s1.cp), s1.clock),
                                 pc := s.active[0].pc + 1)
    requires vms2 == s1.(active := [th'] + s1.active[1..])
    ensures PTL.TrcPikeTreeLk(bst, bst1)
    ensures bst1.PTS?
    ensures LiftInv(rer, qm, re, code, crv, str, ov, S, bst1, vms2, ncap, nlook, nquant)

  /** SETQUANT (the quantifier Reset): B steps the `GroupActionT(Reset)` head.
      BLOCKED on the quantifier-NoDup research gap (the carried NoDup breaks
      at the unfold — see the campaign memory, option D). BODILESS. */
  lemma LiftPreserveSetQuantLk(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
                               crv: CP.FCompiled, str: string, ov: LOr.OracleView, S: set<LG.GroupId>,
                               bst: PT.PikeTreeState, s: AI.VmState, s1: AI.VmState,
                               q: int, bq: bool, th': AI.Thread, vms2: AI.VmState,
                               ncap: int, nlook: int, nquant: int)
    returns (bst1: PT.PikeTreeState)
    requires PSM.StaticOkRE(qm, re, code, endl)
    requires bst.PTS?
    requires LiftInv(rer, qm, re, code, crv, str, ov, S, bst, s, ncap, nlook, nquant)
    requires |s.active| > 0
    requires !AI.bpc_mem(s.processed, s.active[0].pc, s.active[0].exit_allowed)
    requires s.active[0].pc >= 0
    requires NR.GetPcRE(code, s.active[0].pc as nat) == Some(RB.SetQuantToClock(q, bq))
    requires s1 == s.(clock := s.clock + 1,
                      processed := AI.bpc_add(s.processed, s.active[0].pc, s.active[0].exit_allowed))
    requires th' == s.active[0].(quant_regs := AReg.set_reg(s.active[0].quant_regs, q,
                                                            if bq then Some(s1.cp) else None, s1.clock),
                                 pc := s.active[0].pc + 1)
    requires vms2 == s1.(active := [th'] + s1.active[1..])
    ensures PTL.TrcPikeTreeLk(bst, bst1)
    ensures bst1.PTS?
    ensures LiftInv(rer, qm, re, code, crv, str, ov, S, bst1, vms2, ncap, nlook, nquant)

  /** FORK: forward = one `pts_active` on the `Choice` head (arms at `x`/`y`
      in VM priority order); backward = TWO B steps (`Progress` unwrap, then
      `Choice` split) per one VM step. Mirror of `PSM.PreserveForkCase`.
      BODILESS. */
  lemma LiftPreserveForkLk(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
                           crv: CP.FCompiled, str: string, ov: LOr.OracleView, S: set<LG.GroupId>,
                           bst: PT.PikeTreeState, s: AI.VmState, s1: AI.VmState,
                           x: int, y: int, vms2: AI.VmState,
                           ncap: int, nlook: int, nquant: int)
    returns (bst1: PT.PikeTreeState)
    requires PSM.StaticOkRE(qm, re, code, endl)
    requires bst.PTS?
    requires LiftInv(rer, qm, re, code, crv, str, ov, S, bst, s, ncap, nlook, nquant)
    requires |s.active| > 0
    requires !AI.bpc_mem(s.processed, s.active[0].pc, s.active[0].exit_allowed)
    requires s.active[0].pc >= 0
    requires NR.GetPcRE(code, s.active[0].pc as nat) == Some(RB.Fork(x, y))
    requires s1 == s.(clock := s.clock + 1,
                      processed := AI.bpc_add(s.processed, s.active[0].pc, s.active[0].exit_allowed))
    requires vms2 == s1.(active := [AI.Thread(x, s.active[0].capture_regs, s.active[0].look_regs,
                                              s.active[0].quant_regs, s.active[0].exit_allowed),
                                    s.active[0].(pc := y)] + s1.active[1..])
    ensures PTL.TrcPikeTreeLk(bst, bst1)
    ensures bst1.PTS?
    ensures LiftInv(rer, qm, re, code, crv, str, ov, S, bst1, vms2, ncap, nlook, nquant)

  /** POSITIVE GATE, PASSING: the VM writes `a_cp[l] := cp` and continues; B
      steps the `LK` head, `gmt` merges `LkResult` — the proven
      `ThreadRepLkStepCheckOracle` (with `GateStepValue` inside) is the whole
      content; this wrapper threads the per-lid static look-table package.
      BODILESS. */
  lemma LiftPreserveGatePassLk(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
                               crv: CP.FCompiled, str: string, ov: LOr.OracleView, S: set<LG.GroupId>,
                               bst: PT.PikeTreeState, s: AI.VmState, s1: AI.VmState,
                               l: int, th': AI.Thread, vms2: AI.VmState,
                               ncap: int, nlook: int, nquant: int)
    returns (bst1: PT.PikeTreeState)
    requires PSM.StaticOkRE(qm, re, code, endl)
    requires qm.ov == ov
    requires bst.PTS?
    requires LiftInv(rer, qm, re, code, crv, str, ov, S, bst, s, ncap, nlook, nquant)
    requires |s.active| > 0
    requires !AI.bpc_mem(s.processed, s.active[0].pc, s.active[0].exit_allowed)
    requires s.active[0].pc >= 0
    requires NR.GetPcRE(code, s.active[0].pc as nat) == Some(RB.CheckOracle(l))
    requires LOr.view_get_oracle(ov, s.cp, l)
    requires s1 == s.(clock := s.clock + 1,
                      processed := AI.bpc_add(s.processed, s.active[0].pc, s.active[0].exit_allowed))
    requires th' == s.active[0].(pc := s.active[0].pc + 1,
                                 look_regs := AReg.set_reg(s.active[0].look_regs, l, Some(s1.cp), s1.clock))
    requires vms2 == s1.(active := [th'] + s1.active[1..])
    ensures PTL.TrcPikeTreeLk(bst, bst1)
    ensures bst1.PTS?
    ensures LiftInv(rer, qm, re, code, crv, str, ov, S, bst1, vms2, ncap, nlook, nquant)

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
    requires M.NoDupSeq(M.AllDefsActs(acts))
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
        NoDupAllDefsTail(acts);
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
          NoDupAllDefsTail(acts);
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
          NoDupAllDefsTail(acts);
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
      && M.NoDupSeq(M.AllDefsActs(acts));
    WalkPairLkAtNegCheckOracleCore(rer, qm, code, inp, tb, gm, pc, b, acts, lid);
  }

  /** NEGATIVE GATE, PASSING (clear bit): zero-width, no register write; B
      steps the `LK` head — a succeeding negative look's merge IS the running
      map (`LkResult` returns `Some(gm)`), so every tie transfers verbatim. */
  lemma LiftPreserveNegGatePassLk(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
                                  crv: CP.FCompiled, str: string, ov: LOr.OracleView, S: set<LG.GroupId>,
                                  bst: PT.PikeTreeState, s: AI.VmState, s1: AI.VmState,
                                  l: int, vms2: AI.VmState,
                                  ncap: int, nlook: int, nquant: int)
    returns (bst1: PT.PikeTreeState)
    requires PSM.StaticOkRE(qm, re, code, endl)
    requires qm.ov == ov
    requires bst.PTS?
    requires LiftInv(rer, qm, re, code, crv, str, ov, S, bst, s, ncap, nlook, nquant)
    requires |s.active| > 0
    requires !AI.bpc_mem(s.processed, s.active[0].pc, s.active[0].exit_allowed)
    requires s.active[0].pc >= 0
    requires NR.GetPcRE(code, s.active[0].pc as nat) == Some(RB.NegCheckOracle(l))
    requires !LOr.view_get_oracle(ov, s.cp, l)
    requires s1 == s.(clock := s.clock + 1,
                      processed := AI.bpc_add(s.processed, s.active[0].pc, s.active[0].exit_allowed))
    requires vms2 == s1.(active := [s.active[0].(pc := s.active[0].pc + 1)] + s1.active[1..])
    ensures PTL.TrcPikeTreeLk(bst, bst1)
    ensures bst1.PTS?
    ensures LiftInv(rer, qm, re, code, crv, str, ov, S, bst1, vms2, ncap, nlook, nquant)
  {
    var PTS(inp, ta, best, tb, seen) := bst;
    var th := s.active[0];
    var th' := th.(pc := th.pc + 1);
    assert ActiveRepLkC(rer, qm, re, code, inp, crv, str, ov, S, ta, s.active, ncap, nlook, nquant);
    assert |ta| > 0;
    var t := ta[0].0;
    var gm := ta[0].1;
    assert ThreadRepLkC(rer, qm, re, code, inp, crv, str, ov, S, t, gm, th, ncap, nlook, nquant);
    var pc: nat := th.pc as nat;
    var ea := th.exit_allowed;
    assert TreeRepLkRE(rer, qm, code, inp, t, pc, ea);

    // polarity + the bit ⟹ the functional verdict is Some (negative passes)
    TreeRepLkREInRange(rer, qm, code, inp, t, pc, ea);
    assert |code| == endl + 1 && NR.GetPcRE(code, endl) == Some(RB.Accept);
    assert pc < endl;
    GatePolarityRE(re, qm, code, 0, endl, pc);
    assert l in qm.looks;
    var lk := qm.looks[l].0;
    var r1 := qm.looks[l].1;
    assert AR.PositiveL(lk) == L.Positivity(lk);
    assert !L.Positivity(lk);
    var tlk := LFU.ComputeTr(rer, [LS.Areg(r1)], inp, LG.Empty, L.LkDir(lk));
    assert LL.OracleOkAt(rer, qm, inp);
    PIV.IdxInpOfCp(str, s.cp as nat);
    assert TREP.CpOf(inp) == s.cp as nat;
    assert qm.looks[l] == (lk, r1);
    assert LOr.view_get_oracle(qm.ov, TREP.CpOf(inp), l)
       <==> LT.TreeRes(tlk, LG.Empty, inp, L.LkDir(lk)).Some?;
    assert LS.LkResult(lk, tlk, LG.Empty, inp).Some?;      // clear bit + negative

    // canonical head: the LK branch of the gate rule
    TreeRepLkREAtNegCheckOracle(rer, qm, code, inp, t, pc, ea, l);
    assert t.LK? && t.lk == lk && t.tlk == tlk
        && TreeRepLkRE(rer, qm, code, inp, t.t, pc + 1, ea);

    // B step: the merge at the RUNNING map is Some(gm) — the identity
    EL.LkResultGmIndep(lk, tlk, gm, inp);
    assert LS.LkResult(lk, tlk, gm, inp).Some?;
    assert LS.LkResult(lk, tlk, gm, inp).value == gm;      // negative: Some(gm)
    assert PTL.TreeBfsStepLk(t, gm, inp) == PT.StepActive([(t.t, gm)]);
    bst1 := PT.PTS(inp, [(t.t, gm)] + ta[1..], best, tb, SS.AddSeenTrees(seen, t));
    assert PTL.PikeTreeStepLk(bst, bst1);
    TrcLkRefl(bst1);
    TrcLkCons(bst, bst1, bst1);

    // the child pairing: the raw witness steps by the neg-gate walk core; the
    // erasure tie transports the child
    var traw: LT.Tree :| CE.ProgErase(traw) == CE.ProgErase(t)
      && ThreadRepLk(rer, qm, re, code, inp, crv, str, ov, S, traw, gm, th, ncap, nlook, nquant);
    WalkPairLkAtNegCheckOracle(rer, qm, code, inp, traw, gm, pc, ea, l);
    assert traw.LK? && WalkPairLk(rer, qm, code, inp, traw.t, gm, pc + 1, ea);
    assert (th.pc + 1) as nat == pc + 1;
    assert GmtTieOutside(re, th', gm, S);
    assert GmtTieInside(crv, str, ov, th', gm, S, ncap, nlook, nquant);
    assert ThreadRepLk(rer, qm, re, code, inp, crv, str, ov, S, traw.t, gm, th', ncap, nlook, nquant);
    assert CE.ProgErase(traw.t) == CE.ProgErase(t.t) by {
      assert CE.ProgErase(traw) == LT.LK(traw.lk, CE.ProgErase(traw.tlk), CE.ProgErase(traw.t));
      assert CE.ProgErase(t) == LT.LK(t.lk, CE.ProgErase(t.tlk), CE.ProgErase(t.t));
    }
    assert ThreadRepLkC(rer, qm, re, code, inp, crv, str, ov, S, t.t, gm, th', ncap, nlook, nquant);

    // list bookkeeping
    assert ActiveRepLkC(rer, qm, re, code, inp, crv, str, ov, S, ta[1..], s.active[1..],
                        ncap, nlook, nquant);
    assert vms2.active[0] == th' && vms2.active[1..] == s.active[1..];
    assert ([(t.t, gm)] + ta[1..])[0] == (t.t, gm) && ([(t.t, gm)] + ta[1..])[1..] == ta[1..];
    assert ActiveRepLkC(rer, qm, re, code, inp, crv, str, ov, S, [(t.t, gm)] + ta[1..], vms2.active,
                        ncap, nlook, nquant);

    // seen + isblocked bookkeeping
    assert PIV.HdTreeOf(ta) == Some(t) && PIV.HeadPcOf(s.active) == pc;
    AddSeenRepLk(rer, qm, code, inp, seen, s.processed, t, pc, ea,
                 PIV.HdTreeOf([(t.t, gm)] + ta[1..]), PIV.HeadPcOf(vms2.active));
    IsblockedGrowLk(rer, qm, code, inp, seen, s.isblocked, t);
  }

  /** GATE KILL (either polarity, failing bit): the head canonical tree is
      `LKFail` — the polarity pin (`GatePolarityRE`) + the oracle column
      (`OracleOkAt`) convert the failing BIT into a `None` functional verdict,
      which is exactly the canonical rule's `LKFail` branch. B drops the head
      with an empty `pts_active`. */
  lemma LiftPreserveGateKillLk(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
                               crv: CP.FCompiled, str: string, ov: LOr.OracleView, S: set<LG.GroupId>,
                               bst: PT.PikeTreeState, s: AI.VmState, s1: AI.VmState,
                               l: int, pos: bool, vms2: AI.VmState,
                               ncap: int, nlook: int, nquant: int)
    returns (bst1: PT.PikeTreeState)
    requires PSM.StaticOkRE(qm, re, code, endl)
    requires qm.ov == ov
    requires bst.PTS?
    requires LiftInv(rer, qm, re, code, crv, str, ov, S, bst, s, ncap, nlook, nquant)
    requires |s.active| > 0
    requires !AI.bpc_mem(s.processed, s.active[0].pc, s.active[0].exit_allowed)
    requires s.active[0].pc >= 0
    requires NR.GetPcRE(code, s.active[0].pc as nat)
          == Some(if pos then RB.CheckOracle(l) else RB.NegCheckOracle(l))
    requires LOr.view_get_oracle(ov, s.cp, l) != pos
    requires s1 == s.(clock := s.clock + 1,
                      processed := AI.bpc_add(s.processed, s.active[0].pc, s.active[0].exit_allowed))
    requires vms2 == s1.(active := s1.active[1..])
    ensures PTL.TrcPikeTreeLk(bst, bst1)
    ensures bst1.PTS?
    ensures LiftInv(rer, qm, re, code, crv, str, ov, S, bst1, vms2, ncap, nlook, nquant)
  {
    var PTS(inp, ta, best, tb, seen) := bst;
    var th := s.active[0];
    assert ActiveRepLkC(rer, qm, re, code, inp, crv, str, ov, S, ta, s.active, ncap, nlook, nquant);
    assert |ta| > 0;
    var t := ta[0].0;
    var gm := ta[0].1;
    assert ThreadRepLkC(rer, qm, re, code, inp, crv, str, ov, S, t, gm, th, ncap, nlook, nquant);
    var pc: nat := th.pc as nat;
    var ea := th.exit_allowed;
    assert TreeRepLkRE(rer, qm, code, inp, t, pc, ea);

    // the gate pc is interior (endl holds Accept), so the polarity pin applies
    TreeRepLkREInRange(rer, qm, code, inp, t, pc, ea);
    assert |code| == endl + 1 && NR.GetPcRE(code, endl) == Some(RB.Accept);
    assert pc < endl;
    GatePolarityRE(re, qm, code, 0, endl, pc);
    assert l in qm.looks;
    var lk := qm.looks[l].0;
    var r1 := qm.looks[l].1;
    assert AR.PositiveL(lk) == L.Positivity(lk);
    assert L.Positivity(lk) == pos;

    // the bit at this position IS the body tree's verdict (oracle column)
    var tlk := LFU.ComputeTr(rer, [LS.Areg(r1)], inp, LG.Empty, L.LkDir(lk));
    assert LL.OracleOkAt(rer, qm, inp);          // inp == inp0 instance of OracleOkSuffix
    PIV.IdxInpOfCp(str, s.cp as nat);
    assert TREP.CpOf(inp) == s.cp as nat;
    assert qm.looks[l] == (lk, r1);
    assert LOr.view_get_oracle(qm.ov, TREP.CpOf(inp), l)
       <==> LT.TreeRes(tlk, LG.Empty, inp, L.LkDir(lk)).Some?;
    // failing bit + polarity ⟹ the functional verdict is None (both flavours)
    assert LS.LkResult(lk, tlk, LG.Empty, inp).None?;

    // canonical head: the LKFail branch of the gate rule
    if pos {
      TreeRepLkREAtCheckOracle(rer, qm, code, inp, t, pc, ea, l);
    } else {
      TreeRepLkREAtNegCheckOracle(rer, qm, code, inp, t, pc, ea, l);
    }
    assert t == LT.LKFail(lk, tlk);
    assert PTL.TreeBfsStepLk(t, gm, inp) == PT.StepActive([]);
    bst1 := LiftDropDeadHeadLk(rer, qm, re, code, endl, crv, str, ov, S,
                               bst, s, s1, vms2, ncap, nlook, nquant);
    TrcLkRefl(bst1);
    TrcLkCons(bst, bst1, bst1);
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
    requires M.NoDupSeq(M.AllDefsActs(acts))
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
        NoDupAllDefsTail(acts);             // NoDupSeq(AllDefsActs(cont))
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
        NoDupAllDefsTail(acts);
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
          NoDupAllDefsTail(acts);
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
      && M.NoDupSeq(M.AllDefsActs(acts));
    WalkPairLkAtEndLoopCore(rer, qm, code, inp, tb, gm, pc, b, acts);
  }

  /** ENDLOOP, PASSING (`exit_allowed`): B steps the `Progress` head (unwrap,
      same gm, child at `pc+1`/CanExit). `Progress` is erasure-transparent, so
      the raw child witness is just the raw walk's own child. */
  lemma LiftPreserveEndLoopPassLk(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
                                  crv: CP.FCompiled, str: string, ov: LOr.OracleView, S: set<LG.GroupId>,
                                  bst: PT.PikeTreeState, s: AI.VmState, s1: AI.VmState,
                                  vms2: AI.VmState, ncap: int, nlook: int, nquant: int)
    returns (bst1: PT.PikeTreeState)
    requires PSM.StaticOkRE(qm, re, code, endl)
    requires bst.PTS?
    requires LiftInv(rer, qm, re, code, crv, str, ov, S, bst, s, ncap, nlook, nquant)
    requires |s.active| > 0
    requires !AI.bpc_mem(s.processed, s.active[0].pc, s.active[0].exit_allowed)
    requires s.active[0].pc >= 0
    requires NR.GetPcRE(code, s.active[0].pc as nat) == Some(RB.EndLoop)
    requires s.active[0].exit_allowed
    requires s1 == s.(clock := s.clock + 1,
                      processed := AI.bpc_add(s.processed, s.active[0].pc, s.active[0].exit_allowed))
    requires vms2 == s1.(active := [s.active[0].(pc := s.active[0].pc + 1)] + s1.active[1..])
    ensures PTL.TrcPikeTreeLk(bst, bst1)
    ensures bst1.PTS?
    ensures LiftInv(rer, qm, re, code, crv, str, ov, S, bst1, vms2, ncap, nlook, nquant)
  {
    var PTS(inp, ta, best, tb, seen) := bst;
    var th := s.active[0];
    var th' := th.(pc := th.pc + 1);
    assert ActiveRepLkC(rer, qm, re, code, inp, crv, str, ov, S, ta, s.active, ncap, nlook, nquant);
    assert |ta| > 0;
    var t := ta[0].0;
    var gm := ta[0].1;
    assert ThreadRepLkC(rer, qm, re, code, inp, crv, str, ov, S, t, gm, th, ncap, nlook, nquant);
    var pc: nat := th.pc as nat;
    var ea := th.exit_allowed;
    assert TreeRepLkRE(rer, qm, code, inp, t, pc, ea);

    // canonical head: Progress with canonical child at (pc+1, true)
    TreeRepLkREAtEndLoop(rer, qm, code, inp, t, pc, ea);
    assert t.Progress? && TreeRepLkRE(rer, qm, code, inp, t.t, pc + 1, true);

    // B step: pts_active queues the child with the same gm
    assert PTL.TreeBfsStepLk(t, gm, inp) == PT.StepActive([(t.t, gm)]);
    bst1 := PT.PTS(inp, [(t.t, gm)] + ta[1..], best, tb, SS.AddSeenTrees(seen, t));
    assert PTL.PikeTreeStepLk(bst, bst1);
    TrcLkRefl(bst1);
    TrcLkCons(bst, bst1, bst1);

    // the child pairing: the raw witness unwraps its own Progress; erasure is
    // transparent to the guard on BOTH sides
    var traw: LT.Tree :| CE.ProgErase(traw) == CE.ProgErase(t)
      && ThreadRepLk(rer, qm, re, code, inp, crv, str, ov, S, traw, gm, th, ncap, nlook, nquant);
    WalkPairLkAtEndLoop(rer, qm, code, inp, traw, gm, pc, ea);
    assert traw.Progress? && WalkPairLk(rer, qm, code, inp, traw.t, gm, pc + 1, true);
    assert (th.pc + 1) as nat == pc + 1;
    assert th'.exit_allowed == true;
    assert GmtTieOutside(re, th', gm, S);
    assert GmtTieInside(crv, str, ov, th', gm, S, ncap, nlook, nquant);
    assert ThreadRepLk(rer, qm, re, code, inp, crv, str, ov, S, traw.t, gm, th', ncap, nlook, nquant);
    assert CE.ProgErase(traw.t) == CE.ProgErase(t.t) by {
      assert CE.ProgErase(traw) == CE.ProgErase(traw.t);   // Progress transparent
      assert CE.ProgErase(t) == CE.ProgErase(t.t);
    }
    assert ThreadRepLkC(rer, qm, re, code, inp, crv, str, ov, S, t.t, gm, th', ncap, nlook, nquant);

    // list bookkeeping
    assert ActiveRepLkC(rer, qm, re, code, inp, crv, str, ov, S, ta[1..], s.active[1..],
                        ncap, nlook, nquant);
    assert vms2.active[0] == th' && vms2.active[1..] == s.active[1..];
    assert ([(t.t, gm)] + ta[1..])[0] == (t.t, gm) && ([(t.t, gm)] + ta[1..])[1..] == ta[1..];
    assert ActiveRepLkC(rer, qm, re, code, inp, crv, str, ov, S, [(t.t, gm)] + ta[1..], vms2.active,
                        ncap, nlook, nquant);

    // seen + isblocked bookkeeping
    assert PIV.HdTreeOf(ta) == Some(t) && PIV.HeadPcOf(s.active) == pc;
    AddSeenRepLk(rer, qm, code, inp, seen, s.processed, t, pc, ea,
                 PIV.HdTreeOf([(t.t, gm)] + ta[1..]), PIV.HeadPcOf(vms2.active));
    IsblockedGrowLk(rer, qm, code, inp, seen, s.isblocked, t);
  }

  /** ENDLOOP, KILLING (`!exit_allowed`): the head canonical tree is
      `Mismatch` (`tr_progressfail`), B drops it. */
  lemma LiftPreserveEndLoopKillLk(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
                                  crv: CP.FCompiled, str: string, ov: LOr.OracleView, S: set<LG.GroupId>,
                                  bst: PT.PikeTreeState, s: AI.VmState, s1: AI.VmState,
                                  vms2: AI.VmState, ncap: int, nlook: int, nquant: int)
    returns (bst1: PT.PikeTreeState)
    requires PSM.StaticOkRE(qm, re, code, endl)
    requires bst.PTS?
    requires LiftInv(rer, qm, re, code, crv, str, ov, S, bst, s, ncap, nlook, nquant)
    requires |s.active| > 0
    requires !AI.bpc_mem(s.processed, s.active[0].pc, s.active[0].exit_allowed)
    requires s.active[0].pc >= 0
    requires NR.GetPcRE(code, s.active[0].pc as nat) == Some(RB.EndLoop)
    requires !s.active[0].exit_allowed
    requires s1 == s.(clock := s.clock + 1,
                      processed := AI.bpc_add(s.processed, s.active[0].pc, s.active[0].exit_allowed))
    requires vms2 == s1.(active := s1.active[1..])
    ensures PTL.TrcPikeTreeLk(bst, bst1)
    ensures bst1.PTS?
    ensures LiftInv(rer, qm, re, code, crv, str, ov, S, bst1, vms2, ncap, nlook, nquant)
  {
    var PTS(inp, ta, best, tb, seen) := bst;
    var th := s.active[0];
    assert ActiveRepLkC(rer, qm, re, code, inp, crv, str, ov, S, ta, s.active, ncap, nlook, nquant);
    assert |ta| > 0;
    var t := ta[0].0;
    assert ThreadRepLkC(rer, qm, re, code, inp, crv, str, ov, S, t, ta[0].1, th, ncap, nlook, nquant);
    var pc: nat := th.pc as nat;
    assert TreeRepLkRE(rer, qm, code, inp, t, pc, th.exit_allowed);
    TreeRepLkREAtEndLoop(rer, qm, code, inp, t, pc, th.exit_allowed);
    assert t == LT.Mismatch;
    assert PTL.TreeBfsStepLk(t, ta[0].1, inp) == PT.StepActive([]);
    bst1 := LiftDropDeadHeadLk(rer, qm, re, code, endl, crv, str, ov, S,
                               bst, s, s1, vms2, ncap, nlook, nquant);
    TrcLkRefl(bst1);
    TrcLkCons(bst, bst1, bst1);
  }

  /** ANCHOR, PASSING: B steps the `AnchorPass` head (child, same gm); the
      VM/spec branch agreement rides `ContextOkRE` + `AnchorAgreeInput`; the
      erasure tie pins the RAW witness's shape (a `Mismatch` witness would
      erase to `Mismatch`, contradicting the canonical `AnchorPass`). */
  lemma LiftPreserveAnchorPassLk(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
                                 crv: CP.FCompiled, str: string, ov: LOr.OracleView, S: set<LG.GroupId>,
                                 bst: PT.PikeTreeState, s: AI.VmState, s1: AI.VmState,
                                 a: R.anchor, vms2: AI.VmState, ncap: int, nlook: int, nquant: int)
    returns (bst1: PT.PikeTreeState)
    requires PSM.StaticOkRE(qm, re, code, endl)
    requires !rer.multiline
    requires bst.PTS?
    requires LiftInv(rer, qm, re, code, crv, str, ov, S, bst, s, ncap, nlook, nquant)
    requires |s.active| > 0
    requires !AI.bpc_mem(s.processed, s.active[0].pc, s.active[0].exit_allowed)
    requires s.active[0].pc >= 0
    requires NR.GetPcRE(code, s.active[0].pc as nat) == Some(RB.AnchorAssertion(a))
    requires LAnc.is_satisfied(a, s.context, LAnc.Forward)
    requires s1 == s.(clock := s.clock + 1,
                      processed := AI.bpc_add(s.processed, s.active[0].pc, s.active[0].exit_allowed))
    requires vms2 == s1.(active := [s.active[0].(pc := s.active[0].pc + 1)] + s1.active[1..])
    ensures PTL.TrcPikeTreeLk(bst, bst1)
    ensures bst1.PTS?
    ensures LiftInv(rer, qm, re, code, crv, str, ov, S, bst1, vms2, ncap, nlook, nquant)
  {
    var PTS(inp, ta, best, tb, seen) := bst;
    var th := s.active[0];
    var th' := th.(pc := th.pc + 1);
    assert ActiveRepLkC(rer, qm, re, code, inp, crv, str, ov, S, ta, s.active, ncap, nlook, nquant);
    assert |ta| > 0;
    var t := ta[0].0;
    var gm := ta[0].1;
    assert ThreadRepLkC(rer, qm, re, code, inp, crv, str, ov, S, t, gm, th, ncap, nlook, nquant);
    var pc: nat := th.pc as nat;
    var ea := th.exit_allowed;
    assert TreeRepLkRE(rer, qm, code, inp, t, pc, ea);

    // the VM-side check IS the spec-side check
    assert PIV.ContextOkRE(str, s.cp, s.context);
    PSM.ContextOkIsCtxOf(str, s.cp as nat);
    assert LAnc.is_satisfied(a, TREP.CtxOf(inp), LAnc.Forward);
    TREP.AnchorAgreeInput(rer, a, inp);
    assert LS.AnchorSatisfied(rer, T.TrAnchor(a), inp);

    // canonical head: AnchorPass with canonical child at (pc+1, ea)
    TreeRepLkREAtAnchor(rer, qm, code, inp, t, pc, ea, a);
    assert t.AnchorPass? && TreeRepLkRE(rer, qm, code, inp, t.t, pc + 1, ea);

    // B step: pts_active queues the child with the same gm
    assert PTL.TreeBfsStepLk(t, gm, inp) == PT.StepActive([(t.t, gm)]);
    bst1 := PT.PTS(inp, [(t.t, gm)] + ta[1..], best, tb, SS.AddSeenTrees(seen, t));
    assert PTL.PikeTreeStepLk(bst, bst1);
    TrcLkRefl(bst1);
    TrcLkCons(bst, bst1, bst1);

    // the child pairing: raw witness steps by the proven Anchor core; the
    // erasure tie transports to the canonical child
    var traw: LT.Tree :| CE.ProgErase(traw) == CE.ProgErase(t)
      && ThreadRepLk(rer, qm, re, code, inp, crv, str, ov, S, traw, gm, th, ncap, nlook, nquant);
    assert traw.AnchorPass? by {
      if !traw.AnchorPass? {
        var acts: LS.Actions, b: BS.LoopBool :|
          AR.ActionsRepL(rer, qm, acts, code, pc)
          && EL.PikeLkActions(acts)
          && ATR.EaOf(b) == ea
          && EL.BoolTreeLk(rer, acts, inp, b, traw)
          && GateAheadClear(acts, gm)
          && M.NoDupSeq(M.AllDefsActs(acts));
        assert TtLk(rer, qm, code, inp, traw, pc, ea);
        TtLkAtAnchor(rer, qm, code, inp, traw, pc, ea, a);
        assert traw == LT.Mismatch;
        assert CE.ProgErase(traw) == LT.Mismatch;
        assert CE.ProgErase(t).AnchorPass?;
        assert false;
      }
    }
    ThreadRepLkStepAnchor(rer, qm, re, code, inp, crv, str, ov, S, traw, gm, th,
                          ncap, nlook, nquant, a);
    assert ThreadRepLk(rer, qm, re, code, inp, crv, str, ov, S, traw.t, gm, th', ncap, nlook, nquant);
    assert CE.ProgErase(traw.t) == CE.ProgErase(t.t) by {
      assert CE.ProgErase(traw) == LT.AnchorPass(traw.a, CE.ProgErase(traw.t));
      assert CE.ProgErase(t) == LT.AnchorPass(t.a, CE.ProgErase(t.t));
    }
    assert (th.pc + 1) as nat == pc + 1;
    assert ThreadRepLkC(rer, qm, re, code, inp, crv, str, ov, S, t.t, gm, th', ncap, nlook, nquant);

    // list bookkeeping
    assert ActiveRepLkC(rer, qm, re, code, inp, crv, str, ov, S, ta[1..], s.active[1..],
                        ncap, nlook, nquant);
    assert vms2.active[0] == th' && vms2.active[1..] == s.active[1..];
    assert ([(t.t, gm)] + ta[1..])[0] == (t.t, gm) && ([(t.t, gm)] + ta[1..])[1..] == ta[1..];
    assert ActiveRepLkC(rer, qm, re, code, inp, crv, str, ov, S, [(t.t, gm)] + ta[1..], vms2.active,
                        ncap, nlook, nquant);

    // seen + isblocked bookkeeping
    assert PIV.HdTreeOf(ta) == Some(t) && PIV.HeadPcOf(s.active) == pc;
    AddSeenRepLk(rer, qm, code, inp, seen, s.processed, t, pc, ea,
                 PIV.HdTreeOf([(t.t, gm)] + ta[1..]), PIV.HeadPcOf(vms2.active));
    IsblockedGrowLk(rer, qm, code, inp, seen, s.isblocked, t);
  }

  /** ANCHOR, KILLING: the head canonical tree is `Mismatch`
      (`tr_anchorfail` via `ContextOkRE` + `AnchorAgreeInput`), B drops it. */
  lemma LiftPreserveAnchorKillLk(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
                                 crv: CP.FCompiled, str: string, ov: LOr.OracleView, S: set<LG.GroupId>,
                                 bst: PT.PikeTreeState, s: AI.VmState, s1: AI.VmState,
                                 a: R.anchor, vms2: AI.VmState, ncap: int, nlook: int, nquant: int)
    returns (bst1: PT.PikeTreeState)
    requires PSM.StaticOkRE(qm, re, code, endl)
    requires !rer.multiline
    requires bst.PTS?
    requires LiftInv(rer, qm, re, code, crv, str, ov, S, bst, s, ncap, nlook, nquant)
    requires |s.active| > 0
    requires !AI.bpc_mem(s.processed, s.active[0].pc, s.active[0].exit_allowed)
    requires s.active[0].pc >= 0
    requires NR.GetPcRE(code, s.active[0].pc as nat) == Some(RB.AnchorAssertion(a))
    requires !LAnc.is_satisfied(a, s.context, LAnc.Forward)
    requires s1 == s.(clock := s.clock + 1,
                      processed := AI.bpc_add(s.processed, s.active[0].pc, s.active[0].exit_allowed))
    requires vms2 == s1.(active := s1.active[1..])
    ensures PTL.TrcPikeTreeLk(bst, bst1)
    ensures bst1.PTS?
    ensures LiftInv(rer, qm, re, code, crv, str, ov, S, bst1, vms2, ncap, nlook, nquant)
  {
    var PTS(inp, ta, best, tb, seen) := bst;
    var th := s.active[0];
    assert ActiveRepLkC(rer, qm, re, code, inp, crv, str, ov, S, ta, s.active, ncap, nlook, nquant);
    assert |ta| > 0;
    var t := ta[0].0;
    assert ThreadRepLkC(rer, qm, re, code, inp, crv, str, ov, S, t, ta[0].1, th, ncap, nlook, nquant);
    var pc: nat := th.pc as nat;
    assert TreeRepLkRE(rer, qm, code, inp, t, pc, th.exit_allowed);

    // the VM-side check IS the spec-side check
    assert PIV.ContextOkRE(str, s.cp, s.context);
    PSM.ContextOkIsCtxOf(str, s.cp as nat);
    assert !LAnc.is_satisfied(a, TREP.CtxOf(inp), LAnc.Forward);
    TREP.AnchorAgreeInput(rer, a, inp);
    assert !LS.AnchorSatisfied(rer, T.TrAnchor(a), inp);

    TreeRepLkREAtAnchor(rer, qm, code, inp, t, pc, th.exit_allowed, a);
    assert t == LT.Mismatch;
    assert PTL.TreeBfsStepLk(t, ta[0].1, inp) == PT.StepActive([]);
    bst1 := LiftDropDeadHeadLk(rer, qm, re, code, endl, crv, str, ov, S,
                               bst, s, s1, vms2, ncap, nlook, nquant);
    TrcLkRefl(bst1);
    TrcLkCons(bst, bst1, bst1);
  }

  /** (4) The epsilon-phase lift: one VM epsilon phase maps to a legal B-trace
      segment preserving the pairing. THE DISPATCHER (filled 2026-08-07):
      mirrors `FAdvanceEpsilon`'s worklist recursion case-for-case, invoking
      the `LiftPreserve*Lk` case tier; `WriteOracle`/`CheckNullable`/`Fail`
      are refuted outright by the canonical tie (no `TreeRepLkRE` rule). */
  lemma LiftAdvanceEpsilon(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
                           crv: CP.FCompiled, str: string, ov: LOr.OracleView, S: set<LG.GroupId>,
                           s: AI.VmState, bst: PT.PikeTreeState, dir: LAnc.direction,
                           ncap: int, nlook: int, nquant: int)
    returns (bst1: PT.PikeTreeState)
    requires !rer.multiline && qm.ov == ov
    requires PSM.StaticOkRE(qm, re, code, endl)
    requires dir == LAnc.Forward
    requires bst.PTS?
    requires |s.processed.true_set| == RB.size(code) && |s.processed.false_set| == RB.size(code)
    requires LiftInv(rer, qm, re, code, crv, str, ov, S, bst, s, ncap, nlook, nquant)
    ensures PTL.TrcPikeTreeLk(bst, bst1)
    ensures bst1.PTS?           // the ε-phase never finalizes; pts_final is LiftConsume's
    ensures LiftInv(rer, qm, re, code, crv, str, ov, S, bst1,
                    AI.FAdvanceEpsilon(code, s, ov, dir).0, ncap, nlook, nquant)
    decreases AI.unprocessed(s.processed), |s.active|
  {
    if |s.active| == 0 {
      bst1 := bst;
      TrcLkRefl(bst);
      return;
    }
    var th := s.active[0];
    var ac := s.active[1..];

    // Head bounds from the canonical tie (machine A used ThreadNestRE here).
    var PTS(inp, ta, best, tb, seen) := bst;
    assert ActiveRepLkC(rer, qm, re, code, inp, crv, str, ov, S, ta, s.active, ncap, nlook, nquant);
    assert |ta| > 0 && th.pc >= 0;
    assert ThreadRepLkC(rer, qm, re, code, inp, crv, str, ov, S, ta[0].0, ta[0].1, th, ncap, nlook, nquant);
    var pc: nat := th.pc as nat;
    assert TreeRepLkRE(rer, qm, code, inp, ta[0].0, pc, th.exit_allowed);
    TreeRepLkREInRange(rer, qm, code, inp, ta[0].0, pc, th.exit_allowed);
    assert pc < |code| && RB.size(code) == |code|;
    var i := RB.get_instr(code, th.pc);
    assert i == code[pc] && NR.GetPcRE(code, pc) == Some(i);

    if AI.bpc_mem(s.processed, th.pc, th.exit_allowed) {
      var bstS := LiftPreserveSkipLk(rer, qm, re, code, endl, crv, str, ov, S, bst, s, ncap, nlook, nquant);
      var bst2 := LiftAdvanceEpsilon(rer, qm, re, code, endl, crv, str, ov, S,
                                     s.(active := ac), bstS, dir, ncap, nlook, nquant);
      TrcLkCons(bst, bstS, bst2);
      bst1 := bst2;
      return;
    }

    var s1 := s.(clock := s.clock + 1, processed := AI.bpc_add(s.processed, th.pc, th.exit_allowed));
    assert AI.unprocessed(s1.processed) <= AI.unprocessed(s.processed)
        && (0 <= th.pc < RB.size(code) ==> AI.unprocessed(s1.processed) < AI.unprocessed(s.processed))
      by { AI.UnprocessedAdd(s.processed, th.pc, th.exit_allowed); }
    assert AI.unprocessed(s1.processed) < AI.unprocessed(s.processed);
    assert |s1.processed.true_set| == RB.size(code) && |s1.processed.false_set| == RB.size(code);

    match i {
      case Accept =>
        var vms2 := s1.(active := [], bestmatch := Some(th));
        bst1 := LiftPreserveAcceptLk(rer, qm, re, code, endl, crv, str, ov, S,
                                     bst, s, s1, vms2, ncap, nlook, nquant);
        TrcLkRefl(bst1);
        TrcLkCons(bst, bst1, bst1);
        assert AI.FAdvanceEpsilon(code, s, ov, dir).0 == vms2;
      case Jmp(x) =>
        var th' := th.(pc := x);
        var vms2 := s1.(active := [th'] + ac);
        LiftPreserveStutterLk(rer, qm, re, code, endl, crv, str, ov, S,
                              bst, s, s1, th', vms2, ncap, nlook, nquant);
        bst1 := LiftAdvanceEpsilon(rer, qm, re, code, endl, crv, str, ov, S,
                                   vms2, bst, dir, ncap, nlook, nquant);
      case BeginLoop =>
        var th' := th.(exit_allowed := false, pc := th.pc + 1);
        var vms2 := s1.(active := [th'] + ac);
        LiftPreserveStutterLk(rer, qm, re, code, endl, crv, str, ov, S,
                              bst, s, s1, th', vms2, ncap, nlook, nquant);
        bst1 := LiftAdvanceEpsilon(rer, qm, re, code, endl, crv, str, ov, S,
                                   vms2, bst, dir, ncap, nlook, nquant);
      case Consume(ce) =>
        var (nb, ni) := AI.add_thread(th, ce, s1.blocked, s1.isblocked);
        if AI.pc_mem(s1.isblocked, th.pc) {
          assert nb == s1.blocked && ni == s1.isblocked;
          var vms2 := s1.(blocked := nb, isblocked := ni, active := ac);
          assert vms2 == s1.(active := ac);
          var bstS := LiftPreserveConsumeDropLk(rer, qm, re, code, endl, crv, str, ov, S,
                                                bst, s, s1, ce, vms2, ncap, nlook, nquant);
          var bst2 := LiftAdvanceEpsilon(rer, qm, re, code, endl, crv, str, ov, S,
                                         vms2, bstS, dir, ncap, nlook, nquant);
          TrcLkTrans(bst, bstS, bst2);
          bst1 := bst2;
        } else {
          assert nb == [(th, ce)] + s1.blocked && ni == AI.pc_add(s1.isblocked, th.pc);
          var vms2 := s1.(blocked := nb, isblocked := ni, active := ac);
          var bstS := LiftPreserveConsumeAddLk(rer, qm, re, code, endl, crv, str, ov, S,
                                               bst, s, s1, ce, vms2, ncap, nlook, nquant);
          var bst2 := LiftAdvanceEpsilon(rer, qm, re, code, endl, crv, str, ov, S,
                                         vms2, bstS, dir, ncap, nlook, nquant);
          TrcLkTrans(bst, bstS, bst2);
          bst1 := bst2;
        }
      case Fork(x, y) =>
        var newt := AI.Thread(x, th.capture_regs, th.look_regs, th.quant_regs, th.exit_allowed);
        var vms2 := s1.(active := [newt, th.(pc := y)] + ac);
        var bstS := LiftPreserveForkLk(rer, qm, re, code, endl, crv, str, ov, S,
                                       bst, s, s1, x, y, vms2, ncap, nlook, nquant);
        var bst2 := LiftAdvanceEpsilon(rer, qm, re, code, endl, crv, str, ov, S,
                                       vms2, bstS, dir, ncap, nlook, nquant);
        TrcLkTrans(bst, bstS, bst2);
        bst1 := bst2;
      case SetRegisterToCP(reg) =>
        var th' := th.(capture_regs := AReg.set_reg(th.capture_regs, reg, Some(s1.cp), s1.clock),
                       pc := th.pc + 1);
        var vms2 := s1.(active := [th'] + ac);
        var bstS := LiftPreserveSetRegLk(rer, qm, re, code, endl, crv, str, ov, S,
                                         bst, s, s1, reg, th', vms2, ncap, nlook, nquant);
        var bst2 := LiftAdvanceEpsilon(rer, qm, re, code, endl, crv, str, ov, S,
                                       vms2, bstS, dir, ncap, nlook, nquant);
        TrcLkTrans(bst, bstS, bst2);
        bst1 := bst2;
      case SetQuantToClock(q, bq) =>
        var ocp := if bq then Some(s1.cp) else None;
        var th' := th.(quant_regs := AReg.set_reg(th.quant_regs, q, ocp, s1.clock), pc := th.pc + 1);
        var vms2 := s1.(active := [th'] + ac);
        var bstS := LiftPreserveSetQuantLk(rer, qm, re, code, endl, crv, str, ov, S,
                                           bst, s, s1, q, bq, th', vms2, ncap, nlook, nquant);
        var bst2 := LiftAdvanceEpsilon(rer, qm, re, code, endl, crv, str, ov, S,
                                       vms2, bstS, dir, ncap, nlook, nquant);
        TrcLkTrans(bst, bstS, bst2);
        bst1 := bst2;
      case CheckOracle(l) =>
        if LOr.view_get_oracle(ov, s1.cp, l) {
          var th' := th.(pc := th.pc + 1,
                         look_regs := AReg.set_reg(th.look_regs, l, Some(s1.cp), s1.clock));
          var vms2 := s1.(active := [th'] + ac);
          var bstS := LiftPreserveGatePassLk(rer, qm, re, code, endl, crv, str, ov, S,
                                             bst, s, s1, l, th', vms2, ncap, nlook, nquant);
          var bst2 := LiftAdvanceEpsilon(rer, qm, re, code, endl, crv, str, ov, S,
                                         vms2, bstS, dir, ncap, nlook, nquant);
          TrcLkTrans(bst, bstS, bst2);
          bst1 := bst2;
        } else {
          var vms2 := s1.(active := ac);
          var bstS := LiftPreserveGateKillLk(rer, qm, re, code, endl, crv, str, ov, S,
                                             bst, s, s1, l, true, vms2, ncap, nlook, nquant);
          var bst2 := LiftAdvanceEpsilon(rer, qm, re, code, endl, crv, str, ov, S,
                                         vms2, bstS, dir, ncap, nlook, nquant);
          TrcLkTrans(bst, bstS, bst2);
          bst1 := bst2;
        }
      case NegCheckOracle(l) =>
        if LOr.view_get_oracle(ov, s1.cp, l) {
          var vms2 := s1.(active := ac);
          var bstS := LiftPreserveGateKillLk(rer, qm, re, code, endl, crv, str, ov, S,
                                             bst, s, s1, l, false, vms2, ncap, nlook, nquant);
          var bst2 := LiftAdvanceEpsilon(rer, qm, re, code, endl, crv, str, ov, S,
                                         vms2, bstS, dir, ncap, nlook, nquant);
          TrcLkTrans(bst, bstS, bst2);
          bst1 := bst2;
        } else {
          var vms2 := s1.(active := [th.(pc := th.pc + 1)] + ac);
          var bstS := LiftPreserveNegGatePassLk(rer, qm, re, code, endl, crv, str, ov, S,
                                                bst, s, s1, l, vms2, ncap, nlook, nquant);
          var bst2 := LiftAdvanceEpsilon(rer, qm, re, code, endl, crv, str, ov, S,
                                         vms2, bstS, dir, ncap, nlook, nquant);
          TrcLkTrans(bst, bstS, bst2);
          bst1 := bst2;
        }
      case WriteOracle(l) =>
        // no TreeRepLkRE rule at WriteOracle — the canonical head tie is refuted
        assert false;
        bst1 := bst;
      case EndLoop =>
        if th.exit_allowed {
          var vms2 := s1.(active := [th.(pc := th.pc + 1)] + ac);
          var bstS := LiftPreserveEndLoopPassLk(rer, qm, re, code, endl, crv, str, ov, S,
                                                bst, s, s1, vms2, ncap, nlook, nquant);
          var bst2 := LiftAdvanceEpsilon(rer, qm, re, code, endl, crv, str, ov, S,
                                         vms2, bstS, dir, ncap, nlook, nquant);
          TrcLkTrans(bst, bstS, bst2);
          bst1 := bst2;
        } else {
          var vms2 := s1.(active := ac);
          var bstS := LiftPreserveEndLoopKillLk(rer, qm, re, code, endl, crv, str, ov, S,
                                                bst, s, s1, vms2, ncap, nlook, nquant);
          var bst2 := LiftAdvanceEpsilon(rer, qm, re, code, endl, crv, str, ov, S,
                                         vms2, bstS, dir, ncap, nlook, nquant);
          TrcLkTrans(bst, bstS, bst2);
          bst1 := bst2;
        }
      case CheckNullable(qid) =>
        // no TreeRepLkRE rule at CheckNullable — refuted
        assert false;
        bst1 := bst;
      case AnchorAssertion(a) =>
        if LAnc.is_satisfied(a, s1.context, dir) {
          var vms2 := s1.(active := [th.(pc := th.pc + 1)] + ac);
          var bstS := LiftPreserveAnchorPassLk(rer, qm, re, code, endl, crv, str, ov, S,
                                               bst, s, s1, a, vms2, ncap, nlook, nquant);
          var bst2 := LiftAdvanceEpsilon(rer, qm, re, code, endl, crv, str, ov, S,
                                         vms2, bstS, dir, ncap, nlook, nquant);
          TrcLkTrans(bst, bstS, bst2);
          bst1 := bst2;
        } else {
          var vms2 := s1.(active := ac);
          var bstS := LiftPreserveAnchorKillLk(rer, qm, re, code, endl, crv, str, ov, S,
                                               bst, s, s1, a, vms2, ncap, nlook, nquant);
          var bst2 := LiftAdvanceEpsilon(rer, qm, re, code, endl, crv, str, ov, S,
                                         vms2, bstS, dir, ncap, nlook, nquant);
          TrcLkTrans(bst, bstS, bst2);
          bst1 := bst2;
        }
      case Fail =>
        // no TreeRepLkRE rule at Fail — refuted
        assert false;
        bst1 := bst;
    }
  }

  /** (5) The consume/next-char lift: `FConsume` + the phase transition map to
      B's `pts_nextchar` (blocked lists become active at the advanced input;
      the matching filter's verdicts realign the lists — landmine 3).
      FILL: mirror `FConsumeLookCpOk`'s recursion for the filter alignment,
      then one `pts_nextchar` step. */
  lemma LiftConsume(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code,
                    crv: CP.FCompiled, str: string, ov: LOr.OracleView, S: set<LG.GroupId>,
                    s: AI.VmState, bst: PT.PikeTreeState, ncap: int, nlook: int, nquant: int)
    returns (bst1: PT.PikeTreeState)
    requires !rer.multiline && qm.ov == ov
    requires LiftInv(rer, qm, re, code, crv, str, ov, S, bst, s, ncap, nlook, nquant)
    ensures PTL.TrcPikeTreeLk(bst, bst1)
    // SEAM: state the post-FConsume + cp-advance successor exactly as
    // FFindMatch's else-branch constructs it (s2/s3/s4 in the frame clones).
    decreases |s.blocked|

  /** (6) The whole-search lift: `FFindMatch` from a paired state yields a
      complete B trace to `PTS_final` paired with the result.
      FILL: the `FFindMatchLookCpOk` skeleton — LiftAdvanceEpsilon, then
      either finish (empty blocked → `pts_final`) or LiftConsume and recurse
      on `|str| - s.cp`. */
  lemma LiftFindMatch(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code,
                      crv: CP.FCompiled, str: string, ov: LOr.OracleView, S: set<LG.GroupId>,
                      s: AI.VmState, bst: PT.PikeTreeState, cdn: LCdn.cdns,
                      ncap: int, nlook: int, nquant: int)
    returns (bst1: PT.PikeTreeState)
    requires !rer.multiline && qm.ov == ov
    requires |s.processed.true_set| == RB.size(code) && |s.processed.false_set| == RB.size(code)
    requires s.context.nextchar == AI.get_char(str, s.cp)
    requires 0 <= s.cp <= |str|
    requires LiftInv(rer, qm, re, code, crv, str, ov, S, bst, s, ncap, nlook, nquant)
    ensures bst1.PTS_final?
    ensures PTL.TrcPikeTreeLk(bst, bst1)
    ensures BestTieLk(re, crv, str, ov, S, bst1.best,
                      AI.FFindMatch(code, str, s, ov, LAnc.Forward, cdn).0, ncap, nlook, nquant)
    decreases |str| - s.cp

  /** (7) THE ENDPOINT, shaped for the else branch: the winner's leaf IS
      `FirstLeaf(t, InitInput(str))`, its values tied to the winning thread on
      BOTH sides of `S`. Composes `LiftInit` + `LiftFindMatch` +
      `PTL.PikeTreeLkComputesFirstLeaf` (which needs `PTL.PikeSubtreeLk(t)` —
      a small structural lemma over `ComputeTr` output, also to fill).
      The else branch then reads: outside-S values == `GmOfLive(winner)`
      (replacing the old S=={} chain), inside-S values == the fresh replay at
      the winner's `a_cp[l]` == (via the (E) bridge + `FLookLoopValueOk`) the
      reconstructed registers `FBuildCapture` returns. NO position theorem,
      NO (S-ii) extraction, NO leaf-occurrence reasoning. */
  lemma LiftEndpoint(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code,
                     crv: CP.FCompiled, str: string, ov: LOr.OracleView, S: set<LG.GroupId>,
                     t: LT.Tree, vms: AI.VmState, cdn: LCdn.cdns, result: Option<AI.Thread>,
                     ncap: int, nlook: int, nquant: int)
    requires !rer.multiline && qm.ov == ov
    requires T.TransWf(re)
    requires PTL.PikeSubtreeLk(t)
    requires EL.BoolTreeLk(rer, [LS.Areg(T.Translate(re))], LC.InitInput(str), BS.CannotExit, t)
    requires vms.cp == 0 && vms.context.nextchar == AI.get_char(str, 0)
    requires |vms.processed.true_set| == RB.size(code) && |vms.processed.false_set| == RB.size(code)
    requires vms.active == [AI.init_thread(AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant))]
    requires vms.blocked == [] && vms.bestmatch.None?
    requires result == AI.FFindMatch(code, str, vms, ov, LAnc.Forward, cdn).0
    ensures (LT.FirstLeaf(t, LC.InitInput(str)).None? <==> result.None?)
    ensures result.Some? ==>
      var leaf := LT.FirstLeaf(t, LC.InitInput(str)).value;
      GmtTieOutside(re, result.value, leaf.1, S)
      && GmtTieInside(crv, str, ov, result.value, leaf.1, S, ncap, nlook, nquant)

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
          var em: nat, e1: nat :|
            AR.NfaRepMinL(rer, qm, min - 1, r1, code, pc, em)
            && (exists qid: int :: NR.GetPcRE(code, em) == Some(RB.SetQuantToClock(qid, false))
                                   && qid in qm.quants && qm.quants[qid] == L.DefGroups(r1))
            && AR.NfaRepL(rer, qm, r1, code, em + 1, e1)
            && NR.GetPcRE(code, e1) == Some(if greedy then RB.Fork(em, e1 + 1) else RB.Fork(e1 + 1, em))
            && pcmid == e1 + 1;
          NfaRepMinLHeadPin(rer, qm, min - 1, r1, code, pc, em);   // min-1==0 ⇒ em==pc; else Fork/SQC at pc
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

  /** `ActionsRepL` sees THROUGH a `Jmp`: representing at a `Jmp(x)` pc is the
      same as representing at the target `x`. Transparent `Areg` heads are
      relocated intact (`NfaRepLAtJmpTransparent`); every other head pins a
      non-`Jmp` instruction. */
  least lemma ActionsRepLThruJmp(rer: LW.RegExpRecord, qm: AR.QMap, acts: LS.Actions, code: RB.code, pc: nat, x: int)
    requires AR.ActionsRepL(rer, qm, acts, code, pc)
    requires NR.GetPcRE(code, pc) == Some(RB.Jmp(x))
    ensures x >= 0 && AR.ActionsRepL(rer, qm, acts, code, x as nat)
  {
    if |acts| == 0 && NR.GetPcRE(code, pc) == Some(RB.Accept) {
      // Accept != Jmp: contradiction
    } else if |acts| > 0 && exists pcmid: nat :: AR.ActionRepL(rer, qm, acts[0], code, pc, pcmid) && AR.ActionsRepL(rer, qm, acts[1..], code, pcmid) {
      var pcmid: nat :| AR.ActionRepL(rer, qm, acts[0], code, pc, pcmid) && AR.ActionsRepL(rer, qm, acts[1..], code, pcmid);
      match acts[0]
      case Acheck(_) =>   // pins EndLoop or a backward Fork — not Jmp
      case Aclose(_) =>   // pins SetRegisterToCP — not Jmp
      case Areg(r) =>
        NfaRepLAtJmpTransparent(rer, qm, r, code, pc, pcmid, x);   // pcmid == pc; (x>=0 ⇒ NfaRepL(r,x,x))
        assert pcmid == pc;
        ActionsRepLThruJmp(rer, qm, acts[1..], code, pc, x);       // ⇒ x >= 0 && ActionsRepL(acts[1..], code, x)
        assert AR.ActionRepL(rer, qm, acts[0], code, x as nat, x as nat);
        assert acts == [acts[0]] + acts[1..];
        AR.ActionsRepLCons(rer, qm, acts[0], acts[1..], code, x as nat, x as nat);
    } else {
      var pcstart: nat :| NR.GetPcRE(code, pc) == Some(RB.Jmp(pcstart)) && AR.ActionsRepL(rer, qm, acts, code, pcstart);
      assert pcstart == x;
    }
  }

  /** [SOLID] Jmp is a pure stutter: same tree, walk at the target. */
  lemma TtLkAtJmp(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                  tb: LT.Tree, pc: nat, ea: bool, x: int)
    requires TtLk(rer, qm, code, inp, tb, pc, ea)
    requires NR.GetPcRE(code, pc) == Some(RB.Jmp(x))
    ensures x >= 0 && TtLk(rer, qm, code, inp, tb, x as nat, ea)
  {
    var acts: LS.Actions, b: BS.LoopBool :|
      AR.ActionsRepL(rer, qm, acts, code, pc)
      && EL.PikeLkActions(acts)
      && ATR.EaOf(b) == ea
      && EL.BoolTreeLk(rer, acts, inp, b, tb);
    ActionsRepLThruJmp(rer, qm, acts, code, pc, x);   // x >= 0 && ActionsRepL(acts, code, x)
    // same (acts, b) witness TtLk at x — only the pc moved
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

  /** Fueled core of `TtLkAtAccept`: at an `Accept` pc every `ActionsRepL` head
      is transparent (Epsilon / a spent `{0}` quantifier / a Sequence of those),
      so `BoolTreeLk` peels — expanding Sequences — down to the empty stack,
      whose tree is `Match`. Every consuming/branching head pins a non-`Accept`
      instruction. `decreases MsizeA(acts)` (Sequence expansion still shrinks it).*/
  lemma TtLkAtAcceptCore(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                         tb: LT.Tree, pc: nat, b: BS.LoopBool, acts: LS.Actions)
    requires AR.ActionsRepL(rer, qm, acts, code, pc)
    requires EL.PikeLkActions(acts)
    requires EL.BoolTreeLk(rer, acts, inp, b, tb)
    requires NR.GetPcRE(code, pc) == Some(RB.Accept)
    ensures tb == LT.Match
    decreases ATR.MsizeA(acts)
  {
    if |acts| == 0 {
      // BoolTreeLk([], inp, b, tb) ⟹ tb == Match
    } else if exists pcmid: nat :: AR.ActionRepL(rer, qm, acts[0], code, pc, pcmid) && AR.ActionsRepL(rer, qm, acts[1..], code, pcmid) {
      var pcmid: nat :| AR.ActionRepL(rer, qm, acts[0], code, pc, pcmid) && AR.ActionsRepL(rer, qm, acts[1..], code, pcmid);
      EL.PikeLkActionsTail(acts);
      assert acts == [acts[0]] + acts[1..];
      EL.PikeLkActionsConsIff(acts[0], acts[1..]);
      var cont := acts[1..];
      match acts[0]
      case Acheck(_) =>   // pins EndLoop or a backward Fork — not Accept
      case Aclose(_) =>   // pins SetRegisterToCP — not Accept
      case Areg(r) =>
        assert EL.PikeLkRegex(r);
        match r
        case Epsilon =>
          assert pcmid == pc;
          assert EL.BoolTreeLk(rer, cont, inp, b, tb);
          assert ATR.MsizeA(cont) < ATR.MsizeA(acts);
          TtLkAtAcceptCore(rer, qm, code, inp, tb, pc, b, cont);
        case Sequence(r1, r2) =>
          assert acts[0] == LS.Areg(L.Sequence(r1, r2));
          assert AR.NfaRepL(rer, qm, L.Sequence(r1, r2), code, pc, pcmid);   // == ActionRepL(acts[0],..)
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
          TtLkAtAcceptCore(rer, qm, code, inp, tb, pc, b, na);
        case Quantified(greedy, min, delta, r1) =>
          // At an Accept pc the only transparent quantifier is a spent {0}
          // (min==0, delta==NN(0)); every other shape pins Fork/SetQuantToClock.
          if min == 0 && delta == LN.NN(0) {
            assert acts[0] == LS.Areg(L.Quantified(greedy, 0, LN.NN(0), r1));
            assert AR.NfaRepL(rer, qm, L.Quantified(greedy, 0, LN.NN(0), r1), code, pc, pcmid);
            var em: nat :| AR.NfaRepMinL(rer, qm, 0, r1, code, pc, em)
                         && AR.NfaRepOptL(rer, qm, 0, greedy, r1, code, em, pcmid);
            NfaRepMinLHeadPin(rer, qm, 0, r1, code, pc, em);              // em == pc
            NfaRepOptLHeadPin(rer, qm, 0, greedy, r1, code, em, pcmid);   // pcmid == em
            assert pcmid == pc;
            assert AR.ActionsRepL(rer, qm, cont, code, pc);
            assert EL.BoolTreeLk(rer, cont, inp, b, tb);   // Quantified NN(0) skip case
            assert ATR.MsizeA(cont) < ATR.MsizeA(acts);
            TtLkAtAcceptCore(rer, qm, code, inp, tb, pc, b, cont);
          } else {
            QuantHeadPinsNonAccept(rer, qm, greedy, min, delta, r1, code, pc, pcmid);   // ⇒ false
          }
        case Character(_) =>   // pins Consume — not Accept
        case Disjunction(_, _) =>   // pins Fork — not Accept
        case Group(_, _) =>   // pins SetRegisterToCP — not Accept
        case LookaroundR(_, _) =>   // pins CheckOracle/NegCheckOracle — not Accept
        case AnchorR(_) =>   // pins AnchorAssertion — not Accept
        case Backreference(_) =>   // NfaRepL false
    } else {
      var pcstart: nat :| NR.GetPcRE(code, pc) == Some(RB.Jmp(pcstart)) && AR.ActionsRepL(rer, qm, acts, code, pcstart);
      // Jmp != Accept: contradiction
    }
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
        var em: nat, e1: nat :|
          AR.NfaRepMinL(rer, qm, min - 1, r1, code, pc, em)
          && (exists qid: int :: NR.GetPcRE(code, em) == Some(RB.SetQuantToClock(qid, false))
                                 && qid in qm.quants && qm.quants[qid] == L.DefGroups(r1))
          && AR.NfaRepL(rer, qm, r1, code, em + 1, e1)
          && NR.GetPcRE(code, e1) == Some(if greedy then RB.Fork(em, e1 + 1) else RB.Fork(e1 + 1, em))
          && pcmid == e1 + 1;
        NfaRepMinLHeadPin(rer, qm, min - 1, r1, code, pc, em);
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

  /** [SOLID] At Accept the walk is exhausted: the tree is `Match`. */
  lemma TtLkAtAccept(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                     tb: LT.Tree, pc: nat, ea: bool)
    requires TtLk(rer, qm, code, inp, tb, pc, ea)
    requires NR.GetPcRE(code, pc) == Some(RB.Accept)
    ensures tb == LT.Match
  {
    var acts: LS.Actions, b: BS.LoopBool :|
      AR.ActionsRepL(rer, qm, acts, code, pc)
      && EL.PikeLkActions(acts)
      && ATR.EaOf(b) == ea
      && EL.BoolTreeLk(rer, acts, inp, b, tb);
    TtLkAtAcceptCore(rer, qm, code, inp, tb, pc, b, acts);
  }

  /** Fueled core of `TtLkAtConsume` (the RELOCATING template): peel the
      transparent prefix (carrying `WalkOk` via its destructors), reach the
      `Character` head — the only one whose `NfaRepL` pins `Consume` — then
      `BoolTreeLk` reads off `Read`/`Mismatch` and the continuation `TtLk` walks
      from `pc+1` at the advanced input with the flag re-armed to `CanExit`. */
  lemma TtLkAtConsumeCore(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                          tb: LT.Tree, pc: nat, b: BS.LoopBool, acts: LS.Actions, ce: RC.char_expectation)
    requires AR.ActionsRepL(rer, qm, acts, code, pc)
    requires EL.PikeLkActions(acts)
    requires EL.BoolTreeLk(rer, acts, inp, b, tb)
    requires NR.GetPcRE(code, pc) == Some(RB.Consume(ce))
    ensures tb.Read? || tb == LT.Mismatch
    ensures tb.Read? ==> exists nextinp ::
      AR.ReadCharE(ce, inp) == Some((tb.c, nextinp))
      && TtLk(rer, qm, code, nextinp, tb.t, pc + 1, true)
    ensures tb == LT.Mismatch ==> AR.ReadCharE(ce, inp) == None
    decreases ATR.MsizeA(acts)
  {
    var g := ATR.EaOf(b);
    // empty_bc needs Accept, jump_bc needs Jmp — neither is Consume, so cons_bc.
    var pcmid: nat :| AR.ActionRepL(rer, qm, acts[0], code, pc, pcmid) && AR.ActionsRepL(rer, qm, acts[1..], code, pcmid);
    EL.PikeLkActionsTail(acts);
    assert acts == [acts[0]] + acts[1..];
    EL.PikeLkActionsConsIff(acts[0], acts[1..]);
    var cont := acts[1..];
    match acts[0]
    case Acheck(_) =>   // pins EndLoop / backward Fork — not Consume
    case Aclose(_) =>   // pins SetRegisterToCP — not Consume
    case Areg(r) =>
      assert EL.PikeLkRegex(r);
      match r
      case Epsilon =>
        assert pcmid == pc;
        assert EL.BoolTreeLk(rer, cont, inp, b, tb);
        assert ATR.MsizeA(cont) < ATR.MsizeA(acts);
        TtLkAtConsumeCore(rer, qm, code, inp, tb, pc, b, cont, ce);
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
        TtLkAtConsumeCore(rer, qm, code, inp, tb, pc, b, na, ce);
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
          TtLkAtConsumeCore(rer, qm, code, inp, tb, pc, b, cont, ce);
        } else {
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
            assert TtLk(rer, qm, code, pair.1, tb.t, pc + 1, true) by {
              assert ATR.EaOf(BS.CanExit) == true;
            }
            assert AR.ReadCharE(ce, inp) == Some((tb.c, pair.1));
        }
      case Disjunction(_, _) =>   // pins Fork — not Consume
      case Group(_, _) =>   // pins SetRegisterToCP — not Consume
      case LookaroundR(_, _) =>   // pins CheckOracle/NegCheckOracle — not Consume
      case AnchorR(_) =>   // pins AnchorAssertion — not Consume
      case Backreference(_) =>   // NfaRepL false
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
        var em: nat, e1: nat :|
          AR.NfaRepMinL(rer, qm, min - 1, r1, code, pc, em)
          && (exists qid: int :: NR.GetPcRE(code, em) == Some(RB.SetQuantToClock(qid, false))
                                 && qid in qm.quants && qm.quants[qid] == L.DefGroups(r1))
          && AR.NfaRepL(rer, qm, r1, code, em + 1, e1)
          && NR.GetPcRE(code, e1) == Some(if greedy then RB.Fork(em, e1 + 1) else RB.Fork(e1 + 1, em))
          && pcmid == e1 + 1;
        NfaRepMinLHeadPin(rer, qm, min - 1, r1, code, pc, em);
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

  /** [SOLID] At Consume the tree is a `Read` (char accepted, post-Read walk at
      `pc+1` on the advanced input with the flag re-armed) or `Mismatch`. */
  lemma TtLkAtConsume(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                      tb: LT.Tree, pc: nat, ea: bool, ce: RC.char_expectation)
    requires TtLk(rer, qm, code, inp, tb, pc, ea)
    requires NR.GetPcRE(code, pc) == Some(RB.Consume(ce))
    ensures tb.Read? || tb == LT.Mismatch
    ensures tb.Read? ==> exists nextinp ::
      AR.ReadCharE(ce, inp) == Some((tb.c, nextinp))
      && TtLk(rer, qm, code, nextinp, tb.t, pc + 1, true)
    ensures tb == LT.Mismatch ==> AR.ReadCharE(ce, inp) == None
  {
    var acts: LS.Actions, b: BS.LoopBool :|
      AR.ActionsRepL(rer, qm, acts, code, pc)
      && EL.PikeLkActions(acts)
      && ATR.EaOf(b) == ea
      && EL.BoolTreeLk(rer, acts, inp, b, tb);
    TtLkAtConsumeCore(rer, qm, code, inp, tb, pc, b, acts, ce);
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

  /** Fueled core of `TtLkAtSetReg`: peel the transparent prefix; the real head
      is either an `Aclose(gid)` (a `Close`) or a `Group(gid, r1)` (an `Open`),
      each pinning `SetRegisterToCP` by register parity. */
  lemma TtLkAtSetRegCore(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                         tb: LT.Tree, pc: nat, b: BS.LoopBool, acts: LS.Actions, r: int)
    requires AR.ActionsRepL(rer, qm, acts, code, pc)
    requires EL.PikeLkActions(acts)
    requires EL.BoolTreeLk(rer, acts, inp, b, tb)
    requires NR.GetPcRE(code, pc) == Some(RB.SetRegisterToCP(r))
    ensures tb.GroupActionT?
    ensures (tb.g.Open? && r == CP.start_reg(tb.g.g as int))
         || (tb.g.Close? && r == CP.end_reg(tb.g.g as int))
    ensures TtLk(rer, qm, code, inp, tb.t, pc + 1, ATR.EaOf(b))
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
      // ActionRepL(Aclose(gid)) pins SetRegisterToCP(end_reg(gid)), pcmid == pc+1
      assert pcmid == pc + 1 && r == CP.end_reg(gid as int);
      assert tb.GroupActionT? && tb.g == LG.Close(gid) && EL.BoolTreeLk(rer, cont, inp, b, tb.t);
      assert TtLk(rer, qm, code, inp, tb.t, pc + 1, g);
    case Areg(r0) =>
      assert EL.PikeLkRegex(r0);
      match r0
      case Epsilon =>
        assert pcmid == pc;
        assert EL.BoolTreeLk(rer, cont, inp, b, tb);
        assert ATR.MsizeA(cont) < ATR.MsizeA(acts);
        TtLkAtSetRegCore(rer, qm, code, inp, tb, pc, b, cont, r);
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
        TtLkAtSetRegCore(rer, qm, code, inp, tb, pc, b, na, r);
      case Group(gid, r1) =>
        // ActionRepL(Areg(Group)) pins SetRegisterToCP(start_reg(gid))
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
        assert TtLk(rer, qm, code, inp, tb.t, pc + 1, g);
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
          TtLkAtSetRegCore(rer, qm, code, inp, tb, pc, b, cont, r);
        } else {
          assert acts[0] == LS.Areg(L.Quantified(greedy, min, delta, r1));
          assert AR.NfaRepL(rer, qm, L.Quantified(greedy, min, delta, r1), code, pc, pcmid);
          QuantHeadPinsForkOrSQC(rer, qm, greedy, min, delta, r1, code, pc, pcmid);   // Fork/SQC ≠ SetReg
        }
      case Character(_) =>   // pins Consume — not SetRegisterToCP
      case Disjunction(_, _) =>   // pins Fork — not SetRegisterToCP
      case LookaroundR(_, _) =>   // pins CheckOracle/NegCheckOracle — not SetRegisterToCP
      case AnchorR(_) =>   // pins AnchorAssertion — not SetRegisterToCP
      case Backreference(_) =>   // NfaRepL false
  }

  /** [SOLID] At SetRegisterToCP the tree is a `GroupActionT` whose action is
      `Open`/`Close` by register parity (mirror of tr_open/tr_close). */
  lemma TtLkAtSetReg(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                     tb: LT.Tree, pc: nat, ea: bool, r: int)
    requires TtLk(rer, qm, code, inp, tb, pc, ea)
    requires NR.GetPcRE(code, pc) == Some(RB.SetRegisterToCP(r))
    ensures tb.GroupActionT?
    ensures (tb.g.Open? && r == CP.start_reg(tb.g.g as int))
         || (tb.g.Close? && r == CP.end_reg(tb.g.g as int))
    ensures TtLk(rer, qm, code, inp, tb.t, pc + 1, ea)
  {
    var acts: LS.Actions, b: BS.LoopBool :|
      AR.ActionsRepL(rer, qm, acts, code, pc)
      && EL.PikeLkActions(acts)
      && ATR.EaOf(b) == ea
      && EL.BoolTreeLk(rer, acts, inp, b, tb);
    TtLkAtSetRegCore(rer, qm, code, inp, tb, pc, b, acts, r);
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
      var em, e1 := AR.NfaRepLPlusInv(rer, qm, greedy, min, r1, code, pc, pcmid);
      var qid_em: int :| NR.GetPcRE(code, em) == Some(RB.SetQuantToClock(qid_em, false))
                       && qid_em in qm.quants && qm.quants[qid_em] == L.DefGroups(r1);
      if min == 1 {
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

  /** Fueled core of `TtLkAtSetQuant`: peel the transparent prefix; the real head
      is an `Areg(Quantified(min>0))` whose first `SetQuantToClock` stamps a
      `Reset`, and the continuation `[Areg(r1),Areg(Quantified(min-1))]+cont` is
      represented at `pc+1` by `QuantForcedContRep` (the do-while seam is now
      satisfiable — `WalkOk` was dropped from `TtLk`). */
  lemma TtLkAtSetQuantCore(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                           tb: LT.Tree, pc: nat, b: BS.LoopBool, acts: LS.Actions, q: int)
    requires AR.ActionsRepL(rer, qm, acts, code, pc)
    requires EL.PikeLkActions(acts)
    requires EL.BoolTreeLk(rer, acts, inp, b, tb)
    requires NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(q, false))
    ensures tb.GroupActionT? && tb.g.Reset?
    ensures TtLk(rer, qm, code, inp, tb.t, pc + 1, ATR.EaOf(b))
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
        TtLkAtSetQuantCore(rer, qm, code, inp, tb, pc, b, cont, q);
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
        TtLkAtSetQuantCore(rer, qm, code, inp, tb, pc, b, na, q);
      case Quantified(greedy, min, delta, r1) =>
        assert acts[0] == LS.Areg(L.Quantified(greedy, min, delta, r1));
        assert AR.NfaRepL(rer, qm, L.Quantified(greedy, min, delta, r1), code, pc, pcmid);
        if min > 0 {
          // THE forced-copy real head: reset stamp + continuation via QuantForcedContRep.
          var quant1 := L.Quantified(greedy, min - 1, delta, r1);
          var contActs := [LS.Areg(r1), LS.Areg(quant1)] + cont;
          assert tb.GroupActionT? && tb.g == LG.Reset(L.DefGroups(r1))
                 && EL.BoolTreeLk(rer, contActs, inp, b, tb.t);
          QuantForcedContRep(rer, qm, greedy, min, delta, r1, code, pc, pcmid, cont);   // ActionsRepL(contActs, pc+1)
          assert EL.PikeLkRegex(r1) && EL.PikeLkRegex(quant1);
          assert EL.PikeLkActions(contActs) by {
            EL.PikeLkActionsConsIff(LS.Areg(quant1), cont);
            EL.PikeLkActionsConsIff(LS.Areg(r1), [LS.Areg(quant1)] + cont);
          }
          assert TtLk(rer, qm, code, inp, tb.t, pc + 1, g);
        } else if delta == LN.NN(0) {
          var em: nat :| AR.NfaRepMinL(rer, qm, 0, r1, code, pc, em)
                       && AR.NfaRepOptL(rer, qm, 0, greedy, r1, code, em, pcmid);
          NfaRepMinLHeadPin(rer, qm, 0, r1, code, pc, em);
          NfaRepOptLHeadPin(rer, qm, 0, greedy, r1, code, em, pcmid);
          assert pcmid == pc;
          assert AR.ActionsRepL(rer, qm, cont, code, pc);
          assert EL.BoolTreeLk(rer, cont, inp, b, tb);
          assert ATR.MsizeA(cont) < ATR.MsizeA(acts);
          TtLkAtSetQuantCore(rer, qm, code, inp, tb, pc, b, cont, q);
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

  /** [SOLID] At SetQuantToClock the tree is the quantifier's `Reset` stamp
      (payload pinned by `qm.quants`). Resolved by the do-while-seam
      reformulation (WalkOk dropped from TtLk) + `QuantForcedContRep`. */
  lemma TtLkAtSetQuant(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                       tb: LT.Tree, pc: nat, ea: bool, q: int)
    requires TtLk(rer, qm, code, inp, tb, pc, ea)
    requires NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(q, false))
    ensures tb.GroupActionT? && tb.g.Reset?
    ensures TtLk(rer, qm, code, inp, tb.t, pc + 1, ea)
  {
    var acts: LS.Actions, b: BS.LoopBool :|
      AR.ActionsRepL(rer, qm, acts, code, pc)
      && EL.PikeLkActions(acts)
      && ATR.EaOf(b) == ea
      && EL.BoolTreeLk(rer, acts, inp, b, tb);
    TtLkAtSetQuantCore(rer, qm, code, inp, tb, pc, b, acts, q);
  }

  /** [SOLID] THE GATE, B side: at `CheckOracle(lid)` the tree IS the gate's
      own node — `LK` when the bit is set (and its `LkResult` verdict agrees
      via `OracleOkAt`), `LKFail` when clear; a passing gate's continuation
      walks from `pc+1` at the SAME input. This is `GateNodeAtInp` +
      `GateFiresAtWalkInp` transported into the pairing's vocabulary — the
      point where LiftAdvanceEpsilon's CheckOracle case meets `GateStepValue`. */
  /** Fueled core of `TtLkAtCheckOracle`: peel the transparent prefix (`OracleOkAt`
      is at the same `inp`, so it survives); the real head is a `LookaroundR`
      whose gate node `M.GateNodeAtInp` pins to `LK`/`LKFail`, and `OracleOkAt`
      ties the oracle bit to the `LkGateOk` verdict (positive gate: bit ⟺
      `LkResult.Some?`). */
  lemma TtLkAtCheckOracleCore(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                              tb: LT.Tree, pc: nat, b: BS.LoopBool, acts: LS.Actions, lid: int)
    requires AR.ActionsRepL(rer, qm, acts, code, pc)
    requires EL.PikeLkActions(acts)
    requires EL.BoolTreeLk(rer, acts, inp, b, tb)
    requires NR.GetPcRE(code, pc) == Some(RB.CheckOracle(lid))
    requires LL.OracleOkAt(rer, qm, inp)
    ensures lid in qm.looks
    ensures var (lk, r1) := qm.looks[lid];
      (LOr.view_get_oracle(qm.ov, TR_CpOf(inp), lid) ==>
         tb.LK? && tb.lk == lk
         && EL.LkGateOk(rer, lk, r1, inp, tb.tlk, true)
         && TtLk(rer, qm, code, inp, tb.t, pc + 1, ATR.EaOf(b)))
      && (!LOr.view_get_oracle(qm.ov, TR_CpOf(inp), lid) ==>
            tb.LKFail? && tb.lk == lk
            && EL.LkGateOk(rer, lk, r1, inp, tb.tlk, false))
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
        TtLkAtCheckOracleCore(rer, qm, code, inp, tb, pc, b, cont, lid);
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
        TtLkAtCheckOracleCore(rer, qm, code, inp, tb, pc, b, na, lid);
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
          TtLkAtCheckOracleCore(rer, qm, code, inp, tb, pc, b, cont, lid);
        } else {
          assert acts[0] == LS.Areg(L.Quantified(greedy, min, delta, r1));
          assert AR.NfaRepL(rer, qm, L.Quantified(greedy, min, delta, r1), code, pc, pcmid);
          QuantHeadPinsForkOrSQC(rer, qm, greedy, min, delta, r1, code, pc, pcmid);
        }
      case LookaroundR(lk0, r1) =>
        // NfaRepL(LookaroundR) pins CheckOracle(lid0)/NegCheckOracle(lid0); here it is CheckOracle.
        var lid0: int :| NR.GetPcRE(code, pc) == Some(if AR.PositiveL(lk0) then RB.CheckOracle(lid0)
                                                                           else RB.NegCheckOracle(lid0))
          && lid0 in qm.looks && qm.looks[lid0] == (lk0, r1) && pcmid == pc + 1;
        assert AR.PositiveL(lk0) && lid0 == lid;
        assert L.Positivity(lk0);
        assert lid in qm.looks && qm.looks[lid] == (lk0, r1);
        M.GateNodeAtInp(rer, acts, inp, b, tb, lk0, r1);   // tb is LK/LKFail with LkGateOk
        // OracleOkAt at lid: bit ⟺ TreeRes(ComputeTr([Areg(r1)],inp,Empty,LkDir(lk0)),..).Some?
        var bit := LOr.view_get_oracle(qm.ov, TR_CpOf(inp), lid);
        if tb.LK? {
          // LkGateOk(..,true) ⇒ LkResult.Some? ⇒ TreeRes.Some? ⇒ bit
          assert EL.BoolTreeLk(rer, cont, inp, b, tb.t);
          assert AR.ActionsRepL(rer, qm, cont, code, pc + 1);
          assert TtLk(rer, qm, code, inp, tb.t, pc + 1, g);
          assert bit;
        } else {
          assert tb.LKFail?;   // GateNodeAtInp: only LK or LKFail
          // LkGateOk(..,false) ⇒ LkResult.None? ⇒ TreeRes.None? ⇒ !bit
          assert !bit;
        }
      case Character(_) =>   // pins Consume — not CheckOracle
      case Disjunction(_, _) =>   // pins Fork — not CheckOracle
      case Group(_, _) =>   // pins SetRegisterToCP — not CheckOracle
      case AnchorR(_) =>   // pins AnchorAssertion — not CheckOracle
      case Backreference(_) =>   // NfaRepL false
  }

  lemma TtLkAtCheckOracle(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                          tb: LT.Tree, pc: nat, ea: bool, lid: int)
    requires TtLk(rer, qm, code, inp, tb, pc, ea)
    requires NR.GetPcRE(code, pc) == Some(RB.CheckOracle(lid))
    requires LL.OracleOkAt(rer, qm, inp)
    ensures lid in qm.looks
    ensures var (lk, r1) := qm.looks[lid];
      (LOr.view_get_oracle(qm.ov, TR_CpOf(inp), lid) ==>
         tb.LK? && tb.lk == lk
         && EL.LkGateOk(rer, lk, r1, inp, tb.tlk, true)
         && TtLk(rer, qm, code, inp, tb.t, pc + 1, ea))
      && (!LOr.view_get_oracle(qm.ov, TR_CpOf(inp), lid) ==>
            tb.LKFail? && tb.lk == lk
            && EL.LkGateOk(rer, lk, r1, inp, tb.tlk, false))
  {
    var acts: LS.Actions, b: BS.LoopBool :|
      AR.ActionsRepL(rer, qm, acts, code, pc)
      && EL.PikeLkActions(acts)
      && ATR.EaOf(b) == ea
      && EL.BoolTreeLk(rer, acts, inp, b, tb);
    TtLkAtCheckOracleCore(rer, qm, code, inp, tb, pc, b, acts, lid);
  }

  /** `TR.CpOf` re-exported locally (avoids importing TreeRep just for it). */
  function TR_CpOf(inp: LC.Input): nat { |inp.pref| }

  /** A `PikeLk` lookaround head has a `NoLkBrL` body: positive-forward gives it
      directly (`PikeLkRegex(LookaroundR)`), every other flavour is group-free
      (⊆ `NoLkBrL`). Reusable at the gate for `LkResultAgreeOutside`. */
  lemma LookBodyNoLkBr(lk: L.Lookaround, r1: L.Regex)
    requires EL.PikeLkRegex(L.LookaroundR(lk, r1))
    ensures EL.NoLkBrL(r1)
  {
    if L.Positivity(lk) && L.LkDir(lk) == WP.Forward {
      // PikeLkRegex(LookaroundR) == NoLkBrL(r1) in this branch.
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
    requires M.NoDupSeq(M.AllDefsActs(acts))
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
        NoDupAllDefsTail(acts);
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
          NoDupAllDefsTail(acts);
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
          // AfterMerge req (4): every other pending gate's body disjoint from DefGroups(r1).
          M.AllDefsActsCons(acts[0], cont);
          assert L.DefGroups(L.LookaroundR(lk0, r1)) == L.DefGroups(r1);
          assert M.AllDefsActs(acts) == L.DefGroups(r1) + M.AllDefsActs(cont);
          M.NoDupConcat(L.DefGroups(r1), M.AllDefsActs(cont));   // set(DefGroups r1) ∩ set(AllDefsActs cont) == {}
          assert forall lk2: L.Lookaround, r2: L.Regex :: GatePending(cont, lk2, r2) ==>
                   (forall gg :: gg in L.DefGroups(r2) ==> gg !in L.DefGroups(r1)) by {
            forall lk2: L.Lookaround, r2: L.Regex | GatePending(cont, lk2, r2)
              ensures forall gg :: gg in L.DefGroups(r2) ==> gg !in L.DefGroups(r1)
            {
              var j :| 0 <= j < |cont| && cont[j].Areg? && RegexTopGate(cont[j].r, lk2, r2);
              RegexTopGateSubDefs(cont[j].r, lk2, r2);      // set(DefGroups r2) ⊆ set(DefGroups cont[j].r)
              AllDefsActsMemberSub(cont, j);                // set(DefGroups cont[j].r) ⊆ set(AllDefsActs cont)
              var SR2 := set gx | gx in L.DefGroups(r2);
              var SCJ := set gx | gx in L.DefGroups(cont[j].r);
              var SAC := set gx | gx in M.AllDefsActs(cont);
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
          // Assemble WalkPairLk(tb.t, gm2, pc+1, g) via the existential (2nd) disjunct.
          assert EL.PikeLkActions(cont);
          assert M.NoDupSeq(M.AllDefsActs(cont));   // from NoDupConcat(DefGroups(r1), AllDefsActs(cont))
          assert AR.ActionsRepL(rer, qm, cont, code, pc + 1)
              && EL.PikeLkActions(cont)
              && ATR.EaOf(b) == g
              && EL.BoolTreeLk(rer, cont, inp, b, tb.t)
              && GateAheadClear(cont, gm2)
              && M.NoDupSeq(M.AllDefsActs(cont));
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
  {
    // GetPcRE==CheckOracle ≠ BeginLoop kills the stutter disjunct; extract the walk.
    var acts: LS.Actions, b: BS.LoopBool :|
      AR.ActionsRepL(rer, qm, acts, code, pc)
      && EL.PikeLkActions(acts)
      && ATR.EaOf(b) == ea
      && EL.BoolTreeLk(rer, acts, inp, b, tb)
      && GateAheadClear(acts, gm)
      && M.NoDupSeq(M.AllDefsActs(acts));
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
    requires M.NoDupSeq(M.AllDefsActs(acts))
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
        NoDupAllDefsTail(acts);
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
          NoDupAllDefsTail(acts);
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
          NoDupAllDefsTail(acts);             // NoDupSeq(AllDefsActs(cont))
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
      && M.NoDupSeq(M.AllDefsActs(acts));
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

  /** `WalkPairLk` is strictly stronger than `TtLk`: its existential adds
      `GateAheadClear` + `NoDupSeq(AllDefsActs)`, which we simply drop. This
      bridge lets the cases that need only the tree SHAPE (Accept ⟹ Match, the
      Fork shape, and the dying LKFail/Mismatch cases) reuse the proven
      `TtLkAt*` inversions directly, with no `WalkPairLk`-specific core. */
  lemma WalkPairLkImpliesTtLk(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                              tb: LT.Tree, gm: LG.GroupMap, pc: nat, ea: bool)
    requires WalkPairLk(rer, qm, code, inp, tb, gm, pc, ea)
    ensures TtLk(rer, qm, code, inp, tb, pc, ea)
    decreases RB.size(code) - pc
  {
    if (exists acts: LS.Actions, b: BS.LoopBool ::
          AR.ActionsRepL(rer, qm, acts, code, pc) && EL.PikeLkActions(acts) && ATR.EaOf(b) == ea
          && EL.BoolTreeLk(rer, acts, inp, b, tb) && GateAheadClear(acts, gm)
          && M.NoDupSeq(M.AllDefsActs(acts))) {
      // the existential disjunct: the same (acts, b) satisfy TtLk's exists.
      var acts: LS.Actions, b: BS.LoopBool :|
        AR.ActionsRepL(rer, qm, acts, code, pc) && EL.PikeLkActions(acts) && ATR.EaOf(b) == ea
        && EL.BoolTreeLk(rer, acts, inp, b, tb) && GateAheadClear(acts, gm)
        && M.NoDupSeq(M.AllDefsActs(acts));
    } else {
      // B false ⟹ the BeginLoop stutter disjunct holds; recurse at pc+1.
      assert pc < RB.size(code) && NR.GetPcRE(code, pc) == Some(RB.BeginLoop)
          && WalkPairLk(rer, qm, code, inp, tb, gm, pc + 1, false);
      WalkPairLkImpliesTtLk(rer, qm, code, inp, tb, gm, pc + 1, false);
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

  // ---- (G+) SetReg bricks: GroupActionT Open/Close preservation --------------

  /** `GateAheadClear` survives ANY domain-shrinking `gm` change (the `Close`
      case: `GMClose` keeps the domain, so nothing new appears). */
  lemma GateAheadClearMono(acts: LS.Actions, gm: LG.GroupMap, gm2: LG.GroupMap)
    requires GateAheadClear(acts, gm)
    requires forall g :: g in gm2 ==> g in gm
    ensures GateAheadClear(acts, gm2)
  {
    forall lk: L.Lookaround, r1: L.Regex | GatePending(acts, lk, r1)
      ensures forall g :: g in L.DefGroups(r1) ==> g !in gm2
    { forall g | g in L.DefGroups(r1) ensures g !in gm2 { assert g !in gm; } }
  }

  /** `GateAheadClear` survives an `Open(gid)` when `gid` is not in any pending
      body (`GMOpen` adds only `gid`). */
  lemma GateAheadClearAfterOpen(acts: LS.Actions, gm: LG.GroupMap, gid: LG.GroupId, idx: nat)
    requires GateAheadClear(acts, gm)
    requires forall lk: L.Lookaround, r1: L.Regex | GatePending(acts, lk, r1) :: gid !in L.DefGroups(r1)
    ensures GateAheadClear(acts, LG.GMUpdate(LG.Open(gid), idx, gm))
  {
    var gm2 := LG.GMUpdate(LG.Open(gid), idx, gm);
    assert gm2 == LG.GMOpen(idx, gid, gm);
    forall lk: L.Lookaround, r1: L.Regex | GatePending(acts, lk, r1)
      ensures forall g :: g in L.DefGroups(r1) ==> g !in gm2
    {
      forall g | g in L.DefGroups(r1) ensures g !in gm2 {
        assert g !in gm;    // GateAheadClear(acts, gm)
        assert g != gid;    // requires
        assert forall gx :: gx in gm2 ==> gx == gid || gx in gm;   // GMOpen adds only gid
      }
    }
  }

  /** A gate pending in the `Group` open-expansion `[Areg r1, Aclose gid]+cont`
      is pending in `[Areg (Group gid r1)]+cont` (head folds into the `Group`
      top-gate; `Aclose` holds no gate; the tail is shared). */
  lemma GatePendingGroupBack(acts: LS.Actions, gid: LG.GroupId, r1: L.Regex, lk: L.Lookaround, rr: L.Regex)
    requires |acts| > 0 && acts[0] == LS.Areg(L.Group(gid, r1))
    requires GatePending([LS.Areg(r1), LS.Aclose(gid)] + acts[1..], lk, rr)
    ensures GatePending(acts, lk, rr)
  {
    var cont := acts[1..];
    var ga := [LS.Areg(r1), LS.Aclose(gid)] + cont;
    var i :| 0 <= i < |ga| && ga[i].Areg? && RegexTopGate(ga[i].r, lk, rr);
    if i == 0 {
      assert ga[0] == LS.Areg(r1) && RegexTopGate(r1, lk, rr);
      assert RegexTopGate(L.Group(gid, r1), lk, rr);              // Group case
      assert acts[0].Areg? && RegexTopGate(acts[0].r, lk, rr);    // witness 0
    } else if i == 1 {
      assert ga[1] == LS.Aclose(gid);   // not Areg — contradicts ga[i].Areg?
    } else {
      assert ga[i] == cont[i - 2] == acts[i - 1];
      assert acts[i - 1].Areg? && RegexTopGate(acts[i - 1].r, lk, rr);   // witness i-1
    }
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
    requires M.NoDupSeq(M.AllDefsActs(acts))
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
      NoDupAllDefsTail(acts);
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
        NoDupAllDefsTail(acts);
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
        // AllDefsActs(ga) == DefGroups(r1) + AllDefsActs(cont); AllDefsActs(acts) == [gid] + AllDefsActs(ga).
        M.AllDefsActsCons(LS.Areg(r1), [LS.Aclose(gid)] + cont);
        M.AllDefsActsCons(LS.Aclose(gid), cont);
        M.AllDefsActsCons(acts[0], cont);
        assert L.DefGroups(L.Group(gid, r1)) == [gid] + L.DefGroups(r1);
        assert M.AllDefsActs(ga) == L.DefGroups(r1) + M.AllDefsActs(cont);
        assert M.AllDefsActs(acts) == [gid] + M.AllDefsActs(ga);
        M.NoDupConcat([gid], M.AllDefsActs(ga));   // NoDup(AllDefsActs(ga)) && gid ∉ AllDefsActs(ga)
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
        // gid ∉ every pending body of ga (via NoDup: gid ∉ AllDefsActs(ga) ⊇ DefGroups(rr)).
        assert forall lk2: L.Lookaround, rr: L.Regex :: GatePending(ga, lk2, rr) ==> gid !in L.DefGroups(rr) by {
          forall lk2: L.Lookaround, rr: L.Regex | GatePending(ga, lk2, rr) ensures gid !in L.DefGroups(rr) {
            var j :| 0 <= j < |ga| && ga[j].Areg? && RegexTopGate(ga[j].r, lk2, rr);
            RegexTopGateSubDefs(ga[j].r, lk2, rr);
            AllDefsActsMemberSub(ga, j);
            var SRR := set gx | gx in L.DefGroups(rr);
            var SGJ := set gx | gx in L.DefGroups(ga[j].r);
            var SAG := set gx | gx in M.AllDefsActs(ga);
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
          NoDupAllDefsTail(acts);
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
      && M.NoDupSeq(M.AllDefsActs(acts));
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

  /** Fueled core of `TtLkAtAnchor`: peel the transparent prefix; the real head
      is an `Areg(AnchorR(la))` pinning `AnchorAssertion` — `BoolTreeLk` reads
      off `AnchorPass` (satisfied) or `Mismatch`, and the continuation walks from
      `pc+1` with the flag unchanged. */
  lemma TtLkAtAnchorCore(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                         tb: LT.Tree, pc: nat, b: BS.LoopBool, acts: LS.Actions, a: R.anchor)
    requires AR.ActionsRepL(rer, qm, acts, code, pc)
    requires EL.PikeLkActions(acts)
    requires EL.BoolTreeLk(rer, acts, inp, b, tb)
    requires NR.GetPcRE(code, pc) == Some(RB.AnchorAssertion(a))
    ensures tb.AnchorPass? || tb == LT.Mismatch
    ensures tb.AnchorPass? ==> TtLk(rer, qm, code, inp, tb.t, pc + 1, ATR.EaOf(b))
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
        TtLkAtAnchorCore(rer, qm, code, inp, tb, pc, b, cont, a);
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
        TtLkAtAnchorCore(rer, qm, code, inp, tb, pc, b, na, a);
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
          TtLkAtAnchorCore(rer, qm, code, inp, tb, pc, b, cont, a);
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
          assert TtLk(rer, qm, code, inp, tb.t, pc + 1, g);
        } else {
          assert tb == LT.Mismatch;
        }
      case Character(_) =>   // pins Consume — not AnchorAssertion
      case Disjunction(_, _) =>   // pins Fork — not AnchorAssertion
      case Group(_, _) =>   // pins SetRegisterToCP — not AnchorAssertion
      case LookaroundR(_, _) =>   // pins CheckOracle/NegCheckOracle — not AnchorAssertion
      case Backreference(_) =>   // NfaRepL false
  }

  /** [SOLID] At an AnchorAssertion the tree is `AnchorPass` (satisfied) or
      `Mismatch` (mirror of tr_anchorpass / tr_anchorfail). */
  lemma TtLkAtAnchor(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                     tb: LT.Tree, pc: nat, ea: bool, a: R.anchor)
    requires TtLk(rer, qm, code, inp, tb, pc, ea)
    requires NR.GetPcRE(code, pc) == Some(RB.AnchorAssertion(a))
    ensures tb.AnchorPass? || tb == LT.Mismatch
    ensures tb.AnchorPass? ==> TtLk(rer, qm, code, inp, tb.t, pc + 1, ea)
  {
    var acts: LS.Actions, b: BS.LoopBool :|
      AR.ActionsRepL(rer, qm, acts, code, pc)
      && EL.PikeLkActions(acts)
      && ATR.EaOf(b) == ea
      && EL.BoolTreeLk(rer, acts, inp, b, tb);
    TtLkAtAnchorCore(rer, qm, code, inp, tb, pc, b, acts, a);
  }

  /** Fueled core of `TtLkAtEndLoop`: peel the transparent prefix; the real head
      is an `Acheck` (RegElk's `EndLoop` falls through) — `BoolTreeLk` gives
      `Progress` (`CanExit`) or `Mismatch` (`CannotExit`), with the passing
      continuation walking from `pc+1` at `CanExit`. */
  lemma TtLkAtEndLoopCore(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                          tb: LT.Tree, pc: nat, b: BS.LoopBool, acts: LS.Actions)
    requires AR.ActionsRepL(rer, qm, acts, code, pc)
    requires EL.PikeLkActions(acts)
    requires EL.BoolTreeLk(rer, acts, inp, b, tb)
    requires NR.GetPcRE(code, pc) == Some(RB.EndLoop)
    ensures ATR.EaOf(b) ==> tb.Progress? && TtLk(rer, qm, code, inp, tb.t, pc + 1, true)
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
        assert TtLk(rer, qm, code, inp, tb.t, pc + 1, true);
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
        TtLkAtEndLoopCore(rer, qm, code, inp, tb, pc, b, cont);
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
        TtLkAtEndLoopCore(rer, qm, code, inp, tb, pc, b, na);
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
          TtLkAtEndLoopCore(rer, qm, code, inp, tb, pc, b, cont);
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

  /** [SOLID] At EndLoop: with the flag armed the tree is `Progress`
      (tr_progress); with it cold the tree is `Mismatch` (tr_progressfail) and
      the VM drops the thread. */
  lemma TtLkAtEndLoop(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                      tb: LT.Tree, pc: nat, ea: bool)
    requires TtLk(rer, qm, code, inp, tb, pc, ea)
    requires NR.GetPcRE(code, pc) == Some(RB.EndLoop)
    ensures ea ==> tb.Progress? && TtLk(rer, qm, code, inp, tb.t, pc + 1, true)
    ensures !ea ==> tb == LT.Mismatch
  {
    var acts: LS.Actions, b: BS.LoopBool :|
      AR.ActionsRepL(rer, qm, acts, code, pc)
      && EL.PikeLkActions(acts)
      && ATR.EaOf(b) == ea
      && EL.BoolTreeLk(rer, acts, inp, b, tb);
    TtLkAtEndLoopCore(rer, qm, code, inp, tb, pc, b, acts);
  }

  /** Fueled core of `TtLkAtFork` (SHAPE only). At a `Fork` the head is a
      `Disjunction` / free-star / bounded / loop-view quantifier (all ⇒ `Choice`)
      or an `Acheck` at a backward fork (⇒ `Progress` when `CanExit`, else
      `Mismatch`). `BoolTreeLk` FORCES the shape in every case. */
  lemma TtLkAtForkCore(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                       tb: LT.Tree, pc: nat, b: BS.LoopBool, acts: LS.Actions, x: int, y: int)
    requires AR.ActionsRepL(rer, qm, acts, code, pc)
    requires EL.PikeLkActions(acts)
    requires EL.BoolTreeLk(rer, acts, inp, b, tb)
    requires NR.GetPcRE(code, pc) == Some(RB.Fork(x, y))
    ensures x >= 0 && y >= 0
    ensures tb.Choice? || tb.Progress? || tb == LT.Mismatch
    decreases ATR.MsizeA(acts)
  {
    var pcmid: nat :| AR.ActionRepL(rer, qm, acts[0], code, pc, pcmid) && AR.ActionsRepL(rer, qm, acts[1..], code, pcmid);
    EL.PikeLkActionsTail(acts);
    assert acts == [acts[0]] + acts[1..];
    EL.PikeLkActionsConsIff(acts[0], acts[1..]);
    var cont := acts[1..];
    match acts[0]
    case Acheck(strcheck) =>
      // EndLoop != Fork, so the BackForkAt disjunct: pcmid == pc; BoolTreeLk ⇒ Progress / Mismatch
      assert AR.BackForkAt(code, pc);
      assert x >= 0 && y >= 0;
    case Aclose(_) =>   // pins SetRegisterToCP — not Fork
    case Areg(r0) =>
      assert EL.PikeLkRegex(r0);
      match r0
      case Epsilon =>
        assert pcmid == pc;
        assert EL.BoolTreeLk(rer, cont, inp, b, tb);
        assert ATR.MsizeA(cont) < ATR.MsizeA(acts);
        TtLkAtForkCore(rer, qm, code, inp, tb, pc, b, cont, x, y);
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
        TtLkAtForkCore(rer, qm, code, inp, tb, pc, b, na, x, y);
      case Disjunction(r1, r2) =>
        // Fork(pc+1, e1+1) ⇒ x,y >= 0; BoolTreeLk ⇒ tb.Choice?
        var e1: nat :| NR.GetPcRE(code, pc) == Some(RB.Fork(pc + 1, e1 + 1))
          && AR.NfaRepL(rer, qm, r1, code, pc + 1, e1)
          && NR.GetPcRE(code, e1) == Some(RB.Jmp(pcmid))
          && AR.NfaRepL(rer, qm, r2, code, e1 + 1, pcmid);
        assert x == pc + 1 && y == e1 + 1;
        assert tb.Choice?;
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
          TtLkAtForkCore(rer, qm, code, inp, tb, pc, b, cont, x, y);
        } else if min > 0 {
          QuantHeadPinsForkOrSQC(rer, qm, greedy, min, delta, r1, code, pc, pcmid);   // pins SQC ≠ Fork
        } else {
          // min==0, Inf or NN(kx>0): the star/bounded fork ⇒ tb.Choice?; targets are nats.
          match delta
          case Inf =>
            if exists e1: nat :: NR.GetPcRE(code, pc) == Some(if greedy then RB.Fork(pc + 1, e1 + 2) else RB.Fork(e1 + 2, pc + 1))
                         && (exists qid: int :: NR.GetPcRE(code, pc + 1) == Some(RB.SetQuantToClock(qid, false))
                                                && qid in qm.quants && qm.quants[qid] == L.DefGroups(r1))
                         && NR.GetPcRE(code, pc + 2) == Some(RB.BeginLoop)
                         && AR.NfaRepL(rer, qm, r1, code, pc + 3, e1)
                         && NR.GetPcRE(code, e1) == Some(RB.EndLoop)
                         && NR.GetPcRE(code, e1 + 1) == Some(RB.Jmp(pc))
                         && pcmid == e1 + 2 {
              var e1: nat :| NR.GetPcRE(code, pc) == Some(if greedy then RB.Fork(pc + 1, e1 + 2) else RB.Fork(e1 + 2, pc + 1));
              assert x >= 0 && y >= 0;
            } else {
              var em: nat :| NR.GetPcRE(code, pc) == Some(if greedy then RB.Fork(em, pc + 1) else RB.Fork(pc + 1, em));
              assert x >= 0 && y >= 0;
            }
            assert tb.Choice?;
          case NN(kx) =>
            var em: nat :| AR.NfaRepMinL(rer, qm, 0, r1, code, pc, em)
                         && AR.NfaRepOptL(rer, qm, kx, greedy, r1, code, em, pcmid);
            NfaRepMinLHeadPin(rer, qm, 0, r1, code, pc, em);
            assert em == pc;
            var e1x: nat :| NR.GetPcRE(code, pc) == Some(if greedy then RB.Fork(pc + 1, pcmid) else RB.Fork(pcmid, pc + 1))
              && (exists qid: int :: NR.GetPcRE(code, pc + 1) == Some(RB.SetQuantToClock(qid, false))
                                     && qid in qm.quants && qm.quants[qid] == L.DefGroups(r1))
              && NR.GetPcRE(code, pc + 2) == Some(RB.BeginLoop)
              && AR.NfaRepL(rer, qm, r1, code, pc + 3, e1x)
              && NR.GetPcRE(code, e1x) == Some(RB.EndLoop)
              && AR.NfaRepOptL(rer, qm, kx - 1, greedy, r1, code, e1x + 1, pcmid);
            assert x >= 0 && y >= 0;
            assert tb.Choice?;
        }
      case Character(_) =>   // pins Consume — not Fork
      case Group(_, _) =>   // pins SetRegisterToCP — not Fork
      case LookaroundR(_, _) =>   // pins CheckOracle/NegCheckOracle — not Fork
      case AnchorR(_) =>   // pins AnchorAssertion — not Fork
      case Backreference(_) =>   // NfaRepL false
  }

  /** At a `Fork` the tree is a `Choice` (Disjunction / quantifier fork), a
      `Progress` (the do-while backward fork's `Acheck` guard when `CanExit`), or
      `Mismatch`. SHAPE-only ensures: `TtLk` cannot pair the free-star fork's
      iteration arm — that arm is `GroupActionT(Reset,...)` at `pc+1`, but `pc+1`
      is `SetQuantToClock` and `pc+2` is `BeginLoop` (which has NO `ActionsRepL`),
      so `ti` lives at `pc+3`. The branch-pairings are `LiftAdvanceEpsilon`'s job
      (it steps through the `SetQuantToClock`/`BeginLoop` setup); a Disjunction
      fork DOES pair `TtLk(t1,x)`/`TtLk(t2,y)` and can be recovered separately. */
  lemma TtLkAtFork(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                   tb: LT.Tree, pc: nat, ea: bool, x: int, y: int)
    requires TtLk(rer, qm, code, inp, tb, pc, ea)
    requires NR.GetPcRE(code, pc) == Some(RB.Fork(x, y))
    ensures x >= 0 && y >= 0
    ensures tb.Choice? || tb.Progress? || tb == LT.Mismatch
  {
    var acts: LS.Actions, b: BS.LoopBool :|
      AR.ActionsRepL(rer, qm, acts, code, pc)
      && EL.PikeLkActions(acts)
      && ATR.EaOf(b) == ea
      && EL.BoolTreeLk(rer, acts, inp, b, tb);
    TtLkAtForkCore(rer, qm, code, inp, tb, pc, b, acts, x, y);
  }

  // NOTE on CheckNullable / Fail / NegCheckOracle / WriteOracle: the L3a MAIN
  // code should pin each as either absent (WriteOracle — NR.NoWriteInstrRE;
  // likely CheckNullable under NonNullable plus-fragment bodies) or
  // tree-trivial (Fail → Mismatch; NegCheckOracle → the negative gate, whose
  // bodies are capture-free so B's merge is value-empty). FILL: prove the
  // absence from the code shape (NI.CodeShapeAt) where possible instead of an
  // inversion lemma; otherwise mirror TtLkAtCheckOracle.

  // ---- (G) GateAheadClear preservation bricks --------------------------------

  /** [SOLID] A `Reset` only removes groups, so clear-ness survives. */
  lemma GateAheadClearAfterReset(acts: LS.Actions, gmt: LG.GroupMap, gidl: LG.GroupSet, idx: nat)
    requires GateAheadClear(acts, gmt)
    ensures GateAheadClear(acts, LG.GMUpdate(LG.Reset(gidl), idx, gmt))
  {
    var gmt2 := LG.GMUpdate(LG.Reset(gidl), idx, gmt);
    assert gmt2 == LG.GMReset(gidl, gmt);
    forall lk: L.Lookaround, r1: L.Regex | GatePending(acts, lk, r1)
      ensures forall g :: g in L.DefGroups(r1) ==> g !in gmt2
    {
      forall g | g in L.DefGroups(r1) ensures g !in gmt2 {
        // GateAheadClear(acts, gmt) gives g !in gmt; GMReset only removes keys.
        assert g !in gmt;
      }
    }
  }

  /** [SEAM] An outside-S group action cannot populate a pending gate's body
      groups (every pending body's groups sit inside S). */
  lemma GateAheadClearAfterOutside(acts: LS.Actions, gmt: LG.GroupMap, a: LG.GroupAction, idx: nat,
                                   S: set<LG.GroupId>)
    requires GateAheadClear(acts, gmt)
    requires forall lk: L.Lookaround, r1: L.Regex | GatePending(acts, lk, r1) ::
               forall g :: g in L.DefGroups(r1) ==> g in S
    requires a.Open? ==> a.g !in S
    requires a.Close? ==> a.g !in S
    requires a.Reset? ==> true
    ensures GateAheadClear(acts, LG.GMUpdate(a, idx, gmt))
  {
    var gmt2 := LG.GMUpdate(a, idx, gmt);
    forall lk: L.Lookaround, r1: L.Regex | GatePending(acts, lk, r1)
      ensures forall g :: g in L.DefGroups(r1) ==> g !in gmt2
    {
      forall g | g in L.DefGroups(r1) ensures g !in gmt2 {
        assert g !in gmt;   // GateAheadClear(acts, gmt)
        assert g in S;      // the pending body's groups sit inside S
        match a
        case Open(g0) =>
          // gmt2 == gmt[g0 := ...]; g0 !in S so g != g0, and g !in gmt.
          assert g0 !in S;
          assert g != g0;
        case Close(g0) =>
          // GMClose only re-maps g0 (already present) or is the identity;
          // g0 !in S so g != g0 either way.
          assert g0 !in S;
          assert g != g0;
        case Reset(gs) =>
          // GMReset only removes keys.
      }
    }
  }

  /** [SEAM] Crossing gate `(lk, r1)` merges ONLY `r1`'s groups
      (`LmOfBodiesDisjoint`), and the crossed occurrence is consumed from the
      continuation acts — every OTHER pending gate stays clear. FILL alongside
      LiftAdvanceEpsilon's CheckOracle case; the acts-evolution premise below
      is the SEAM to nail down (mirror the walk's gate case: `pcmid == pc+1`,
      `cont == acts[1..]`-shaped). */
  lemma GateAheadClearAfterMerge(acts: LS.Actions, cont: LS.Actions, gmt: LG.GroupMap,
                                 gmerged: LG.GroupMap, lk: L.Lookaround, r1: L.Regex)
    requires GateAheadClear(acts, gmt)
    requires forall g :: g in gmerged ==> g in gmt || g in L.DefGroups(r1)
    // NOTE: `GatePending(acts,·)` alone (dropped the earlier `(lk2!=lk||r2!=r1)`
    // clause — unsatisfiable for duplicate capture-free looks like `(?=a)(?=a)`,
    // and unused: the body drives off `GatePending(acts,·)` + the disjointness).
    requires forall lk2: L.Lookaround, r2: L.Regex | GatePending(cont, lk2, r2) ::
               GatePending(acts, lk2, r2)
    requires forall lk2: L.Lookaround, r2: L.Regex | GatePending(cont, lk2, r2) ::
               forall g :: g in L.DefGroups(r2) ==> g !in L.DefGroups(r1)
    ensures GateAheadClear(cont, gmerged)
  {
    forall lk2: L.Lookaround, r2: L.Regex | GatePending(cont, lk2, r2)
      ensures forall g :: g in L.DefGroups(r2) ==> g !in gmerged
    {
      forall g | g in L.DefGroups(r2) ensures g !in gmerged {
        assert GatePending(acts, lk2, r2);   // pending-in-cont ==> pending-in-acts
        assert g !in gmt;                     // GateAheadClear(acts, gmt) at (lk2, r2)
        assert g !in L.DefGroups(r1);         // disjointness requires
        // gmerged only holds gmt-keys or r1-body groups, and g is in neither.
      }
    }
  }

  // ---- (G+) transparent-peel bricks for the CheckOracle continuation walk ----
  // These carry `GateAheadClear` and the `NoDupSeq(AllDefsActs)` walk-invariant
  // through the SAME transparent peels the tb-pairing walk performs (Epsilon /
  // spent-`{0}` quantifier ⤳ tail; `Sequence` ⤳ two-head expand), and supply the
  // gate-head DefGroups-disjointness `GateAheadClearAfterMerge` needs — all from
  // MainTheorem's already-proven `AllDefsActs`/`NoDupConcat` vocabulary.

  /** A gate pending in the tail is pending in the whole list. */
  lemma GatePendingTail(acts: LS.Actions, lk: L.Lookaround, r1: L.Regex)
    requires |acts| > 0 && GatePending(acts[1..], lk, r1)
    ensures GatePending(acts, lk, r1)
  {
    var i :| 0 <= i < |acts[1..]| && acts[1..][i].Areg? && RegexTopGate(acts[1..][i].r, lk, r1);
    assert acts[1..][i] == acts[i + 1];
    assert acts[i + 1].Areg? && RegexTopGate(acts[i + 1].r, lk, r1);   // witness i+1
  }

  /** `GateAheadClear` threads to the tail (Epsilon / spent-`{0}` quantifier peel). */
  lemma GateAheadClearTail(acts: LS.Actions, gmt: LG.GroupMap)
    requires |acts| > 0 && GateAheadClear(acts, gmt)
    ensures GateAheadClear(acts[1..], gmt)
  {
    forall lk: L.Lookaround, r1: L.Regex | GatePending(acts[1..], lk, r1)
      ensures forall g :: g in L.DefGroups(r1) ==> g !in gmt
    { GatePendingTail(acts, lk, r1); }
  }

  /** A gate pending in the `Sequence`-expanded list `[Areg r1, Areg r2]+cont`
      is pending in `[Areg (Sequence r1 r2)]+cont` (head 0/1 fold into the
      `Sequence` top-gate; the tail is shared). */
  lemma GatePendingSeqBack(acts: LS.Actions, r1: L.Regex, r2: L.Regex, lk: L.Lookaround, rr: L.Regex)
    requires |acts| > 0 && acts[0] == LS.Areg(L.Sequence(r1, r2))
    requires GatePending([LS.Areg(r1), LS.Areg(r2)] + acts[1..], lk, rr)
    ensures GatePending(acts, lk, rr)
  {
    var cont := acts[1..];
    var na := [LS.Areg(r1), LS.Areg(r2)] + cont;
    var i :| 0 <= i < |na| && na[i].Areg? && RegexTopGate(na[i].r, lk, rr);
    if i == 0 {
      assert na[0] == LS.Areg(r1) && RegexTopGate(r1, lk, rr);
      assert RegexTopGate(L.Sequence(r1, r2), lk, rr);            // def: a-arm
      assert acts[0].Areg? && RegexTopGate(acts[0].r, lk, rr);   // witness 0
    } else if i == 1 {
      assert na[1] == LS.Areg(r2) && RegexTopGate(r2, lk, rr);
      assert RegexTopGate(L.Sequence(r1, r2), lk, rr);           // def: b-arm
      assert acts[0].Areg? && RegexTopGate(acts[0].r, lk, rr);   // witness 0
    } else {
      assert na[i] == cont[i - 2] == acts[i - 1];
      assert acts[i - 1].Areg? && RegexTopGate(acts[i - 1].r, lk, rr);   // witness i-1
    }
  }

  /** `GateAheadClear` threads across the `Sequence` two-head expand. */
  lemma GateAheadClearSeqExpand(acts: LS.Actions, r1: L.Regex, r2: L.Regex, gmt: LG.GroupMap)
    requires |acts| > 0 && acts[0] == LS.Areg(L.Sequence(r1, r2)) && GateAheadClear(acts, gmt)
    ensures GateAheadClear([LS.Areg(r1), LS.Areg(r2)] + acts[1..], gmt)
  {
    forall lk: L.Lookaround, rr: L.Regex | GatePending([LS.Areg(r1), LS.Areg(r2)] + acts[1..], lk, rr)
      ensures forall g :: g in L.DefGroups(rr) ==> g !in gmt
    { GatePendingSeqBack(acts, r1, r2, lk, rr); }
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

  /** Def-groups of the TOP-LEVEL looks of `r` (not under a quantifier). */
  ghost function TopLkDefsList(r: L.Regex): seq<LG.GroupId>
    decreases r
  {
    match r
    case LookaroundR(lk, r1) => L.DefGroups(r1)
    case Sequence(a, b) => TopLkDefsList(a) + TopLkDefsList(b)
    case Disjunction(a, b) => TopLkDefsList(a) + TopLkDefsList(b)
    case Group(_, r1) => TopLkDefsList(r1)
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

  lemma TopLkDefsListActsCons(x: LS.Action, cont: LS.Actions)
    ensures TopLkDefsListActs([x] + cont)
         == (if x.Areg? then TopLkDefsList(x.r) else []) + TopLkDefsListActs(cont)
  { assert ([x] + cont)[0] == x && ([x] + cont)[1..] == cont; }

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
      assert TopLkDefsList(r) == TopLkDefsList(rb);
      RegexTopGateSubTopLk(rb, lk, r1);
    case Quantified(_, _, _, _) =>
    case Epsilon =>
    case Character(_) =>
    case AnchorR(_) =>
    case Backreference(_) =>
  }

  /** An `Areg` member's top-level look def-list is within the acts' `TopLkDefsListActs`. */
  lemma TopLkDefsListMemberSub(acts: LS.Actions, i: nat)
    requires 0 <= i < |acts| && acts[i].Areg?
    ensures (set g | g in TopLkDefsList(acts[i].r)) <= (set g | g in TopLkDefsListActs(acts))
    decreases |acts|
  {
    assert acts == [acts[0]] + acts[1..];
    TopLkDefsListActsCons(acts[0], acts[1..]);
    if i == 0 {
      assert forall g :: g in TopLkDefsList(acts[0].r) ==> g in TopLkDefsListActs(acts);
    } else {
      TopLkDefsListMemberSub(acts[1..], i - 1);
      assert acts[1..][i - 1] == acts[i];
      assert forall g :: g in TopLkDefsListActs(acts[1..]) ==> g in TopLkDefsListActs(acts);
    }
  }

  /** `NoDupSeq(TopLkDefsListActs)` threads to the tail. */
  lemma NoDupTopLkTail(acts: LS.Actions)
    requires |acts| > 0 && M.NoDupSeq(TopLkDefsListActs(acts))
    ensures M.NoDupSeq(TopLkDefsListActs(acts[1..]))
  {
    assert acts == [acts[0]] + acts[1..];
    TopLkDefsListActsCons(acts[0], acts[1..]);
    var pre: seq<LG.GroupId> := if acts[0].Areg? then TopLkDefsList(acts[0].r) else [];
    assert TopLkDefsListActs(acts) == pre + TopLkDefsListActs(acts[1..]);
    M.NoDupConcat(pre, TopLkDefsListActs(acts[1..]));
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

  /** WITHIN one regex: `DefGroups` no-dup ⟹ its top-level look def-list is
      no-dup (since the latter is a subsequence). The per-`Areg` half of the
      structural NoDup. */
  lemma TopLkNoDupFromDefGroups(r: L.Regex)
    requires M.NoDupSeq(L.DefGroups(r))
    ensures M.NoDupSeq(TopLkDefsList(r))
    decreases r
  {
    match r
    case LookaroundR(lk, r1) =>
      assert TopLkDefsList(r) == L.DefGroups(r1) == L.DefGroups(r);
    case Sequence(a, b) =>
      assert L.DefGroups(r) == L.DefGroups(a) + L.DefGroups(b);
      M.NoDupConcat(L.DefGroups(a), L.DefGroups(b));
      var SA := set gx | gx in L.DefGroups(a);
      var SB := set gx | gx in L.DefGroups(b);
      assert SA * SB == {};
      TopLkNoDupFromDefGroups(a); TopLkNoDupFromDefGroups(b);
      TopLkDefsListSubDefGroups(a); TopLkDefsListSubDefGroups(b);
      forall i, j | 0 <= i < |TopLkDefsList(a)| && 0 <= j < |TopLkDefsList(b)|
        ensures TopLkDefsList(a)[i] != TopLkDefsList(b)[j]
      {
        if TopLkDefsList(a)[i] == TopLkDefsList(b)[j] {
          var g := TopLkDefsList(a)[i];
          assert g in TopLkDefsList(a) && g in TopLkDefsList(b);
          assert g in L.DefGroups(a) && g in L.DefGroups(b);
          assert g in SA && g in SB && g in SA * SB;
          assert false;
        }
      }
      M.NoDupFromDisjoint(TopLkDefsList(a), TopLkDefsList(b));
      assert TopLkDefsList(r) == TopLkDefsList(a) + TopLkDefsList(b);
    case Disjunction(a, b) =>
      assert L.DefGroups(r) == L.DefGroups(a) + L.DefGroups(b);
      M.NoDupConcat(L.DefGroups(a), L.DefGroups(b));
      var SA := set gx | gx in L.DefGroups(a);
      var SB := set gx | gx in L.DefGroups(b);
      assert SA * SB == {};
      TopLkNoDupFromDefGroups(a); TopLkNoDupFromDefGroups(b);
      TopLkDefsListSubDefGroups(a); TopLkDefsListSubDefGroups(b);
      forall i, j | 0 <= i < |TopLkDefsList(a)| && 0 <= j < |TopLkDefsList(b)|
        ensures TopLkDefsList(a)[i] != TopLkDefsList(b)[j]
      {
        if TopLkDefsList(a)[i] == TopLkDefsList(b)[j] {
          var g := TopLkDefsList(a)[i];
          assert g in TopLkDefsList(a) && g in TopLkDefsList(b);
          assert g in L.DefGroups(a) && g in L.DefGroups(b);
          assert g in SA && g in SB && g in SA * SB;
          assert false;
        }
      }
      M.NoDupFromDisjoint(TopLkDefsList(a), TopLkDefsList(b));
      assert TopLkDefsList(r) == TopLkDefsList(a) + TopLkDefsList(b);
    case Group(id, r1) =>
      assert L.DefGroups(r) == [id] + L.DefGroups(r1);
      M.NoDupConcat([id], L.DefGroups(r1));
      TopLkNoDupFromDefGroups(r1);
      assert TopLkDefsList(r) == TopLkDefsList(r1);
    case Quantified(_, _, _, _) =>
    case Epsilon =>
    case Character(_) =>
    case AnchorR(_) =>
    case Backreference(_) =>
  }

  /** Action-level: top-level look groups are a subset of ALL defined groups
      (per-`Areg` subsequence, lifted). Membership form. */
  lemma TopLkDefsListActsSubAllDefs(acts: LS.Actions)
    ensures forall g :: g in TopLkDefsListActs(acts) ==> g in M.AllDefsActs(acts)
    decreases |acts|
  {
    if |acts| == 0 { return; }
    assert acts == [acts[0]] + acts[1..];
    TopLkDefsListActsCons(acts[0], acts[1..]);
    M.AllDefsActsCons(acts[0], acts[1..]);
    TopLkDefsListActsSubAllDefs(acts[1..]);
    if acts[0].Areg? { TopLkDefsListSubDefGroups(acts[0].r); }
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

  predicate NoBackrefActions(acts: LS.Actions) {
    forall i :: 0 <= i < |acts| ==> NoBackrefAction(acts[i])
  }

  lemma NoBackrefActionsTail(act: LS.Actions)
    requires |act| > 0 && NoBackrefActions(act)
    ensures NoBackrefActions(act[1..])
  {
    forall i | 0 <= i < |act[1..]| ensures NoBackrefAction(act[1..][i]) { assert act[1..][i] == act[i + 1]; }
  }

  lemma NoBackrefActionsCons(a: LS.Action, cont: LS.Actions)
    ensures NoBackrefActions([a] + cont) <==> (NoBackrefAction(a) && NoBackrefActions(cont))
  {
    if NoBackrefAction(a) && NoBackrefActions(cont) {
      forall i | 0 <= i < |[a] + cont| ensures NoBackrefAction(([a] + cont)[i]) {
        if i == 0 {} else { assert ([a] + cont)[i] == cont[i - 1]; }
      }
    } else if NoBackrefActions([a] + cont) {
      assert ([a] + cont)[0] == a;
      forall i | 0 <= i < |cont| ensures NoBackrefAction(cont[i]) { assert cont[i] == ([a] + cont)[i + 1]; }
    }
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

  // ---- (V) the value bridge into MainExtraction ------------------------------

  /** The FREE half of the winning leaf's value tie: OUTSIDE `S`, the leaf gm
      equals the winning thread's live denotation — no sim, no (E) path-presence.
      It is pure machine-A + leaf agreement: `BestMatchRE` gives the tstar first
      leaf's gm IS `GmOfLive(re, th.caps)`, and `FirstLeafAgreeOutside` gives that
      same gm agrees with the t-side leaf `leafgm` outside `S`. `GmAgreeOutside`
      is symmetric in the value clause, so it flips to `GmtTieOutside`'s shape
      (leaf-keyed). This is the exact `GmtTieOutside` hypothesis `L3aValueBridge`
      consumes for its outside-`S` branch, discharged from already-proven facts. */
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
    requires NR.LookBehindFragmentRE(body) && PIV.CapUnique(body) && PIV.QuantUnique(body)
    requires ncap >= 0 && nlook >= 0 && nquant >= 0
    requires var cp := if AReg.get_cp(lk, l).Some? then AReg.get_cp(lk, l).value else 0;
             0 <= cp <= |str| && AI.cp_context(cp, str, LAnc.Forward).nextchar == AI.get_char(str, cp)
    ensures var rf := M.FreshBodyMatch(crv, str, l, lk, ov, ncap, nlook, nquant);
            rf.Some? ==> PIV.CapRegWf(rf.value.capture_regs)
  {
    var cp := if AReg.get_cp(lk, l).Some? then AReg.get_cp(lk, l).value else 0;
    var bc := CP.compile_to_bytecode(body);
    var cdn := if 0 <= l < |crv.f_look_cdns| then crv.f_look_cdns[l] else [];
    M.FreshMatchWf(bc, str, cp, ov, cdn, body, ncap, nlook, nquant);
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
                g in gmb && g in leafgm && leafgm[g] == gmb[g]
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
    ensures leafgm[g] == PIV.GmOfLive(re, res0, th.look_regs, res2)[g]
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
  lemma L3aValueBridge(re: R.regex, th: AI.Thread, leafgm: LG.GroupMap,
                       res0: AReg.Regs, res2: AReg.Regs, S: set<LG.GroupId>)
    requires T.TransWf(re) && NR.LookBehindFragmentRE(re) && PIV.CapUnique(re)
    requires S == PIV.CapIdsInLooks(re)
    // OUTSIDE S: the winning-thread tie + FLookLoop frame conclusions.
    requires GmtTieOutside(re, th, leafgm, S)
    requires forall k: int :: k !in PIV.CaptureRegsSet(PIV.CapIdsInLooks(re)) ==>
               AI.get_idx(AReg.as_arrays(res0).0, k) == AI.get_idx(AReg.as_arrays(th.capture_regs).0, k)
               && AI.get_idx(AReg.as_arrays(res0).1, k) == AI.get_idx(AReg.as_arrays(th.capture_regs).1, k)
    requires forall q: nat :: q in PIV.QuantIdsOutsideLooks(re) ==>
               AI.get_idx(AReg.as_arrays(res2).1, q) == AI.get_idx(AReg.as_arrays(th.quant_regs).1, q)
    // INSIDE S, present: the reconstructed value equals the leaf value
    // (aggregated per-g from `InsidePresentResBridge`).
    requires forall g: LG.GroupId :: g in S && g in leafgm ==>
               g in PIV.GmOfLive(re, res0, th.look_regs, res2)
               && leafgm[g] == PIV.GmOfLive(re, res0, th.look_regs, res2)[g]
    // INSIDE S, absent (reverse tie): the reconstruction invents no S-group the
    // leaf lacks — the other half of the key-set equality.
    requires forall g: LG.GroupId :: g in S
               && g in PIV.GmOfLive(re, res0, th.look_regs, res2) ==> g in leafgm
    ensures leafgm == PIV.GmOfLive(re, res0, th.look_regs, res2)
  {
    var gml := PIV.GmOfLive(re, res0, th.look_regs, res2);
    var gmBest := PIV.GmOfLive(re, th.capture_regs, th.look_regs, th.quant_regs);
    // S == LkBodyGroups(Translate(re)) so GmtTieOutside feeds OutsideLookValueBridge.
    M.LkBodyGroupsEqCapIdsInLooks(re);
    M.OutsideLookValueBridge(re, th.capture_regs, res0, th.look_regs, th.quant_regs, res2, gmBest, leafgm);
    forall g: LG.GroupId
      ensures (g in leafgm <==> g in gml) && (g in leafgm ==> leafgm[g] == gml[g])
    {
      if g in S {
        // present ⟹ (requires) g in gml, values agree; absent ⟹ (reverse) g in leafgm.
      } else {
        // OutsideLookValueBridge: leafgm agrees gml outside CapIdsInLooks(re) == S.
      }
    }
    assert leafgm == gml;
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
              && TtLk(rer, qm, code, nextinp, traw, (bl[0].0.pc + 1) as nat, true))
        && GmtTieOutside(re, bl[0].0, tl[0].1, S)
        && GmtTieInside(crv, str, ov, bl[0].0, tl[0].1, S, ncap, nlook, nquant)
        && BlockedRepLkC(rer, qm, re, code, inp, nextinp, crv, str, ov, S, tl[1..], bl[1..],
                         ncap, nlook, nquant))
  }

  /** THE COMPOSITE INVARIANT: machine-A sim (VM↔tstar, PROVEN) PLUS the
      machine-A↔machine-B tree pairing + value payload. `ptsA` is the tstar
      (gate-transparent) PikeTree state driven by `PikeInvFullRE`; `ptsB` is the
      `tcan` (LK-aware, planted-canonical) PikeTree state driven by
      `PTL.PikeTreeStepLk`. */
  ghost predicate LiftInvC(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code,
                           endl: nat, ngroups: nat, crv: CP.FCompiled, str: string,
                           ov: LOr.OracleView, S: set<LG.GroupId>,
                           ptsA: PT.PikeTreeState, ptsB: PT.PikeTreeState, vms: AI.VmState,
                           ncap: int, nlook: int, nquant: int)
    requires NR.NfaRepRE(re, code, 0, endl)
  {
    PSM.PikeInvFullRE(rer, qm, re, code, endl, ngroups, str, ptsA, vms, ncap, nlook, nquant)
    // THREAD-ANCHORED pairing (audit 2026-08-03): each ptsB tree pairs with
    // the VM thread via ThreadRepLkC (canonical tie + raw erasure witness),
    // NOT with the tstar tree — so no ta↔tb link is needed (that was the
    // dead §K route). ptsA is carried only for PikeInvFullRE's VM backbone;
    // the whole B side IS the (canonical-keyed) standalone `LiftInv`.
    && (ptsB.PTS? ==> ptsA.PTS? && ptsA.inp == ptsB.inp)
    && LiftInv(rer, qm, re, code, crv, str, ov, S, ptsB, vms, ncap, nlook, nquant)
  }

  /** (K-init) The composite holds at the start: `PSM.InitialPikeInvFullRE` gives
      the machine-A half; machine B starts on the PLANTED CANONICAL tree `tcan`
      (constructed here by `ActionsTreeRepLkRE` from the entry walk, with
      `WkE.WalkOkEntry` supplying the walk carrier), erasure-tied to the spec
      walk tree `t` — the endpoint glue is `FirstLeaf(tcan) == FirstLeaf(t)`
      via `ProgEraseLeavesEq`. The single active pair `(tcan, init_thread)`
      ties via `ThreadRepLkC` with raw witness `t` + a VACUOUS payload
      (init thread's live map is `LG.Empty`, no `g in S`). */
  lemma LiftInitC(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code,
                  endl: nat, ngroups: nat, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
                  S: set<LG.GroupId>, tstar: LT.Tree, t: LT.Tree, inp: LC.Input, vms: AI.VmState,
                  ncap: int, nlook: int, nquant: int)
    returns (tcan: LT.Tree)
    requires NR.NfaRepRE(re, code, 0, endl)
    requires code == CP.compile_to_bytecode(re)               // WalkOkEntry's carrier
    requires PSM.PikeInvFullRE(rer, qm, re, code, endl, ngroups, str,
                               PT.PikeTreeInitialState(tstar, inp), vms, ncap, nlook, nquant)
    requires T.TransWf(re) && NR.LookBehindFragmentRE(re) && PIV.CapUnique(re)
    requires AR.ActionsRepL(rer, qm, [LS.Areg(T.Translate(re))], code, 0)
    requires EL.BoolTreeLk(rer, [LS.Areg(T.Translate(re))], inp, BS.CannotExit, t)
    requires LL.OracleOkSuffix(rer, qm, inp)
    requires inp == PIV.InpOfCp(str, vms.cp) && 0 <= vms.cp <= |str|
    requires vms.active == [AI.init_thread(AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant))]
    requires vms.bestmatch.None?
    requires vms.blocked == []                                // genuine start: nothing blocked yet
    requires vms.processed == AI.init_bpcset(RB.size(code))   // genuine start: nothing processed yet
    requires vms.isblocked == AI.init_pcset(RB.size(code))
    requires PIV.ContextOkRE(str, vms.cp, vms.context)
    ensures TreeRepLkRE(rer, qm, code, inp, tcan, 0, false)
    ensures CE.ProgErase(tcan) == CE.ProgErase(t)             // endpoint glue: FirstLeaf(tcan) == FirstLeaf(t)
    ensures LiftInvC(rer, qm, re, code, endl, ngroups, crv, str, ov, S,
                     PT.PikeTreeInitialState(tstar, inp), PT.PikeTreeInitialState(tcan, inp), vms,
                     ncap, nlook, nquant)
  {
    // The single active pair (t, init_thread) ties via ThreadRepLk (THREAD-
    // anchored — no tstar↔t tree link); the payload is vacuous because a fresh
    // thread denotes Empty. PikeInvFullRE(ptsA, vms) is the hypothesis.
    PIV.GmOfLiveInit(re, ncap, nlook, nquant);        // GmOfLive(re, init...) == Empty
    var it := AI.init_thread(AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant));
    var acts := [LS.Areg(T.Translate(re))];
    assert it.pc == 0 && it.exit_allowed == false;
    assert it.capture_regs == AReg.init_regs(ncap)
        && it.look_regs == AReg.init_regs(nlook) && it.quant_regs == AReg.init_regs(nquant);
    EL.TranslateFragmentPikeLk(re);                     // PikeLkRegex(Translate(re))
    EL.PikeLkActionsConsIff(LS.Areg(T.Translate(re)), []);
    assert EL.PikeLkActions(acts);
    assert GateAheadClear(acts, LG.Empty);              // Empty has no keys
    TranslateDefGroupsNoDup(re);                        // NoDupSeq(DefGroups(Translate(re)))
    M.AllDefsActsCons(LS.Areg(T.Translate(re)), []);
    assert M.AllDefsActs(acts) == L.DefGroups(T.Translate(re));   // AllDefsActs([]) == []
    assert WalkPairLk(rer, qm, code, inp, t, LG.Empty, it.pc as nat, it.exit_allowed) by {
      assert it.pc as nat == 0;
      assert AR.ActionsRepL(rer, qm, acts, code, 0);
      assert ATR.EaOf(BS.CannotExit) == it.exit_allowed;   // both false
      assert EL.BoolTreeLk(rer, acts, inp, BS.CannotExit, t);
      assert exists actsw: LS.Actions, bw: BS.LoopBool ::
          AR.ActionsRepL(rer, qm, actsw, code, it.pc as nat)
          && EL.PikeLkActions(actsw)
          && ATR.EaOf(bw) == it.exit_allowed
          && EL.BoolTreeLk(rer, actsw, inp, bw, t)
          && GateAheadClear(actsw, LG.Empty)
          && M.NoDupSeq(M.AllDefsActs(actsw));
    }
    assert GmtTieOutside(re, it, LG.Empty, S);          // gml == Empty, agrees with Empty
    assert GmtTieInside(crv, str, ov, it, LG.Empty, S, ncap, nlook, nquant);  // no g in Empty
    assert ThreadRepLk(rer, qm, re, code, inp, crv, str, ov, S, t, LG.Empty, it, ncap, nlook, nquant);
    // Construct machine B's PLANTED CANONICAL entry tree; the raw walk tree
    // `t` is its value-layer erasure witness.
    WkE.WalkOkEntry(re);
    assert WO.WalkOk(acts, code, 0, false);
    assert ATR.EaOf(BS.CannotExit) == false;
    tcan := ActionsTreeRepLkRE(rer, qm, acts, code, 0, inp, BS.CannotExit, t);
    assert ThreadRepLkC(rer, qm, re, code, inp, crv, str, ov, S, tcan, LG.Empty, it,
                        ncap, nlook, nquant) by {
      assert TreeRepLkRE(rer, qm, code, inp, tcan, it.pc as nat, it.exit_allowed);
      assert CE.ProgErase(t) == CE.ProgErase(tcan)
          && ThreadRepLk(rer, qm, re, code, inp, crv, str, ov, S, t, LG.Empty, it, ncap, nlook, nquant);
    }
    assert ActiveRepLkC(rer, qm, re, code, inp, crv, str, ov, S, [(tcan, LG.Empty)], [it], ncap, nlook, nquant);
    // ptsB = PTS(inp, [(tcan, Empty)], None, [], InitialSeenTrees); best None both sides.
    assert PT.PikeTreeInitialState(tcan, inp) == PT.PTS(inp, [(tcan, LG.Empty)], None, [], SS.InitialSeenTrees);
    assert PT.PikeTreeInitialState(tstar, inp).PTS? && PT.PikeTreeInitialState(tstar, inp).inp == inp;
    assert BestTieLk(re, crv, str, ov, S, None, vms.bestmatch, ncap, nlook, nquant);
    // Blocked: genuine start — both sides empty.
    assert PIV.MatchingBlocked(LC.Reverse(vms.blocked), inp) == [];
    forall nextinp | LC.AdvanceInput(inp, WP.Forward) == Some(nextinp)
      ensures BlockedRepLkC(rer, qm, re, code, inp, nextinp, crv, str, ov, S, [],
                            PIV.MatchingBlocked(LC.Reverse(vms.blocked), inp), ncap, nlook, nquant)
    { }
    // B-side seen ↔ processed: at the genuine start nothing is processed, so
    // `SeenRepLk` holds vacuously (mirror of `PIV.InitialInclusionRE`).
    InitialSeenRepLk(rer, qm, code, inp,
                     PIV.HdTreeOf([(tcan, LG.Empty)]), PIV.HeadPcOf([it]), RB.size(code));
  }

  /** (K-step) The composite is preserved across ONE ε-phase. Machine A
      advances by the PROVEN `PSM.InvariantPreservationRE` (a whole-phase
      `TrcRE` — queue/priority/loop mechanics inherited, never re-proved);
      machine B advances by `LiftAdvanceEpsilon` (the B-side worklist
      recursion over the SAME VM steps). The two sides never link directly:
      each pins its `inp` to `InpOfCp(str, cp)` through its own invariant. */
  lemma LiftStepC(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code,
                  endl: nat, ngroups: nat, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
                  S: set<LG.GroupId>, ptsA: PT.PikeTreeState, ptsB: PT.PikeTreeState, vms: AI.VmState,
                  ncap: int, nlook: int, nquant: int)
    returns (ptsA': PT.PikeTreeState, ptsB': PT.PikeTreeState)
    requires NR.NfaRepRE(re, code, 0, endl)
    requires PSM.StaticOkRE(qm, re, code, endl) && PSM.SizesOkRE(re, ncap, nlook, nquant)
    requires qm.ov == ov && !rer.multiline
    requires ptsA.PTS? && ptsB.PTS?
    requires |vms.processed.true_set| == RB.size(code) && |vms.processed.false_set| == RB.size(code)
    requires LiftInvC(rer, qm, re, code, endl, ngroups, crv, str, ov, S, ptsA, ptsB, vms, ncap, nlook, nquant)
    ensures PTL.TrcPikeTreeLk(ptsB, ptsB')
    ensures ptsA'.PTS? && ptsB'.PTS?
    ensures LiftInvC(rer, qm, re, code, endl, ngroups, crv, str, ov, S,
                     ptsA', ptsB', AI.FAdvanceEpsilon(code, vms, ov, LAnc.Forward).0, ncap, nlook, nquant)
  {
    var vms' := AI.FAdvanceEpsilon(code, vms, ov, LAnc.Forward).0;
    // machine A: the proven engine simulation moves ptsA across the whole phase
    ptsA' := PSM.InvariantPreservationRE(rer, qm, re, code, endl, ngroups, str,
                                         ptsA, vms, ov, LAnc.Forward, ncap, nlook, nquant);
    // machine B: the canonical/value worklist recursion over the same phase
    ptsB' := LiftAdvanceEpsilon(rer, qm, re, code, endl, crv, str, ov, S,
                                vms, ptsB, LAnc.Forward, ncap, nlook, nquant);
    // the inp link: both sides pin their inp to InpOfCp(str, vms'.cp)
    assert PIV.PikeInvRE(rer, qm, re, code, ngroups, str, ptsA', vms');
    assert ptsA'.inp == PIV.InpOfCp(str, vms'.cp);
    assert ptsB'.inp == PIV.InpOfCp(str, vms'.cp);
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
  lemma L3aCompositeClose(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code,
                          endl: nat, ngroups: nat, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
                          S: set<LG.GroupId>, tstar: LT.Tree, t: LT.Tree, inp: LC.Input,
                          vms: AI.VmState, cdn: LCdn.cdns, result: Option<AI.Thread>,
                          ncap: int, nlook: int, nquant: int)
    requires NR.NfaRepRE(re, code, 0, endl)
    requires PSM.StaticOkRE(qm, re, code, endl) && PSM.SizesOkRE(re, ncap, nlook, nquant)
    requires qm.ov == ov && !rer.multiline
    // Thread-anchored entry facts (feed LiftInitC) — replace the dead
    // LeavesAgreeAtOutside(tstar, t) tree link.
    requires T.TransWf(re) && NR.LookBehindFragmentRE(re)
    requires AR.ActionsRepL(rer, qm, [LS.Areg(T.Translate(re))], code, 0)
    requires EL.BoolTreeLk(rer, [LS.Areg(T.Translate(re))], inp, BS.CannotExit, t)
    requires PTL.PikeSubtreeLk(t)
    requires PSM.PikeInvFullRE(rer, qm, re, code, endl, ngroups, str,
                               PT.PikeTreeInitialState(tstar, inp), vms, ncap, nlook, nquant)
    requires LL.OracleOkSuffix(rer, qm, inp)
    requires inp == PIV.InpOfCp(str, vms.cp) && 0 <= vms.cp <= |str|
    requires vms.active == [AI.init_thread(AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant))]
    requires vms.bestmatch.None?
    requires |vms.processed.true_set| == RB.size(code) && |vms.processed.false_set| == RB.size(code)
    requires vms.context.nextchar == AI.get_char(str, vms.cp)
    requires result == AI.FFindMatch(code, str, vms, ov, LAnc.Forward, cdn).0
    ensures BestTieLk(re, crv, str, ov, S, LT.FirstLeaf(t, inp), result, ncap, nlook, nquant)

  // ---- (F) final assembly (no scaffold lemma — a recipe) ---------------------
  //
  // The else-branch rewrite of MainTheorem, once (H)/(G)/(C)/(V) and the seven
  // lift lemmas are green:
  //   1. Replace `LkBodyGroupsEmpty(re); assert S == {}` with
  //      `PikeSubtreeLkComputeTr` + `LiftEndpoint` (feeding the entry facts it
  //      requires — all are already established in the surrounding body).
  //   2. Replace the L1 `FBuildCaptureUnfold` chain's leaf identification with
  //      `L3aValueBridge`, then feed the SYNTHETIC thread carrying
  //      `res.0/res.1/res.2` into the EXISTING `MainExtraction`
  //      (`ReplayThreadWfLA`/`FreshMatchWf` supply its ThreadRegsWf +
  //      QuantRegsFinal, per handoff §3).
  //   3. Delete `LkBodyGroupsEmpty`, `FilterUnmoved`, and the L1
  //      `LookRowsFromTables`; whole-package verify; repack (blocked on the
  //      lem 10-minute wall until Lemmata's Native.cs is fixed).
}
