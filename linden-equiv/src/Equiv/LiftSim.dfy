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

  // ==========================================================================
  // SOLID definitions — the pairing.
  // ==========================================================================

  /** The t-side walk state at a pc: some action list represented at `pc`
      whose (checked-flag-erased) spec tree is `tb`. The B-side analogue of
      `TT.TreeThreadRE`. (SEAM: the exact conjunct set — WalkOk / PikeLkActions
      — may need trimming or augmenting once LiftAdvanceEpsilon's cases are
      filled; the walk inversions in ActionsTreeRepFRE's cases show what each
      instruction step preserves.) */
  ghost predicate TtLk(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                       tb: LT.Tree, pc: nat, ea: bool) {
    exists acts: LS.Actions, b: BS.LoopBool ::
      AR.ActionsRepL(rer, qm, acts, code, pc)
      && WO.WalkOk(acts, code, pc, ea)
      && EL.PikeLkActions(acts)
      && ATR.EaOf(b) == ea
      && EL.BoolTreeLk(rer, acts, inp, b, tb)
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

  /** The full per-thread pairing: the B-side `(tb, gmt)` corresponds to VM
      thread `th` — walk-represented at `th.pc`, reset-clear ahead, and
      value-tied on both sides of `S`. */
  ghost predicate ThreadRepLk(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code,
                              inp: LC.Input, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
                              S: set<LG.GroupId>, tb: LT.Tree, gmt: LG.GroupMap, th: AI.Thread,
                              ncap: int, nlook: int, nquant: int) {
    th.pc >= 0
    && (exists acts: LS.Actions, b: BS.LoopBool ::
          AR.ActionsRepL(rer, qm, acts, code, th.pc as nat)
          && WO.WalkOk(acts, code, th.pc as nat, th.exit_allowed)
          && EL.PikeLkActions(acts)
          && ATR.EaOf(b) == th.exit_allowed
          && EL.BoolTreeLk(rer, acts, inp, b, tb)
          && GateAheadClear(acts, gmt))
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
      processed `(pc, b)` has its (unique — `TtLkSameTree`) B-tree in `seen`,
      with the same stutter-chain escape hatch for the head being processed.

      SEAM — PLACEHOLDER BODY. The filler discovers the exact strength from
      `LiftAdvanceEpsilon`'s skip case (B may fire `pts_skip` only when
      `SS.Inseen(seen, head)`); start from `SeenInclusionRE`'s statement
      verbatim with `TtLk` for `TreeThreadRE` and `StuttersRE`/`StutterChainTo`
      reused as-is (gates stutter on BOTH sides). */
  ghost predicate SeenRepLk(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                            treeseen: SS.SeenTrees, processed: AI.Bpcset,
                            current: Option<LT.Tree>, currentpc: nat) {
    true  // TODO(filler): mirror PIV.SeenInclusionRE — see the FILL note above
  }

  /** THE LIFT INVARIANT: the B state pairs with the VM state. Mirrors
      `PIV.PikeInvRE`'s shape with the B-side (t-based, value-carrying)
      relations. `PTS_final` pairs through `BestTieLk` alone. */
  ghost predicate LiftInv(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code,
                          crv: CP.FCompiled, str: string, ov: LOr.OracleView, S: set<LG.GroupId>,
                          bst: PT.PikeTreeState, vms: AI.VmState,
                          ncap: int, nlook: int, nquant: int) {
    match bst
    case PTS_final(bbest) => BestTieLk(re, crv, str, ov, S, bbest, vms.bestmatch, ncap, nlook, nquant)
    case PTS(inp, bactive, bbest, bblocked, bseen) =>
      0 <= vms.cp <= |str|
      && inp == PIV.InpOfCp(str, vms.cp)
      && ActiveRepLk(rer, qm, re, code, inp, crv, str, ov, S, bactive, vms.active, ncap, nlook, nquant)
      && (forall nextinp :: LC.AdvanceInput(inp, WP.Forward) == Some(nextinp) ==>
            BlockedRepLk(rer, qm, re, code, inp, nextinp, crv, str, ov, S, bblocked,
                         PIV.MatchingBlocked(LC.Reverse(vms.blocked), inp), ncap, nlook, nquant))
      && (LC.AdvanceInput(inp, WP.Forward) == None ==> bblocked == [])
      && BestTieLk(re, crv, str, ov, S, bbest, vms.bestmatch, ncap, nlook, nquant)
      && SeenRepLk(rer, qm, code, inp, bseen, vms.processed,
                   PIV.HdTreeOf(bactive), PIV.HeadPcOf(vms.active))
      // the gate helpers read the oracle column at the current input; the
      // walk carries this (OracleOkSuffixStep advances it with cp)
      && LL.OracleOkSuffix(rer, qm, inp)
  }

  // ==========================================================================
  // THE FILLER'S WORKLIST — bodiless lemmas, in fill order.
  // ==========================================================================

  /** (1) t-side determinism: at a fixed `(pc, ea, inp)` the walk tree is
      unique. Kills the seen-desync (landmine 2): pc-equal heads have equal
      B-trees, so B's skip fires exactly when the VM drops a processed head.
      FILL: mirror `TR.TreeRepDetermRE`'s instruction-pinning induction at the
      walk level — every `BoolTreeLk` node shape is pinned by the instruction
      at its pc (the `ActionsTreeRepFRE` cases enumerate the pinnings), and
      `LkGateOk` pins the LK body FUNCTIONALLY (`ComputeTr`), so LK nodes agree
      too. Expect the bulk to be an `ActionsRepL`-determinism helper. */
  lemma TtLkSameTree(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                     t1: LT.Tree, t2: LT.Tree, pc: nat, ea: bool)
    requires !rer.multiline
    requires TtLk(rer, qm, code, inp, t1, pc, ea)
    requires TtLk(rer, qm, code, inp, t2, pc, ea)
    ensures t1 == t2

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
      against the keystone's exact ensures. */
  lemma GateStepValue(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code,
                      crv: CP.FCompiled, str: string, ov: LOr.OracleView, S: set<LG.GroupId>,
                      lk: L.Lookaround, r1: L.Regex, tlk: LT.Tree, tb: LT.Tree,
                      gmt: LG.GroupMap, th: AI.Thread, th2: AI.Thread, l: int, cp: nat,
                      ncap: int, nlook: int, nquant: int)
    requires qm.ov == ov && !rer.ignoreCase && !rer.multiline
    requires cp <= |str|
    requires l in qm.looks && qm.looks[l] == (lk, r1)
    requires L.Positivity(lk) && L.LkDir(lk) == WP.Forward
    requires LS.LkResult(lk, tlk, gmt, PIV.InpOfCp(str, cp)).Some?
    requires EL.LkGateOk(rer, lk, r1, PIV.InpOfCp(str, cp), tlk, true)
    // th2 = th with a_cp[l] := cp at some clock stamp (the CheckOracle write)
    requires exists clkv: int ::
      th2 == th.(pc := th.pc + 1,
                 look_regs := AReg.set_reg(th.look_regs, l, Some(cp as int), clkv))
    requires GmtTieInside(crv, str, ov, th, gmt, S, ncap, nlook, nquant)
    requires forall g :: g in L.DefGroups(r1) ==> g !in gmt        // GateAheadClear at this gate
    ensures var gmt2 := LS.LkResult(lk, tlk, gmt, PIV.InpOfCp(str, cp)).value;
            GmtTieInside(crv, str, ov, th2, gmt2, S, ncap, nlook, nquant)

  /** (3) Initial pairing: fresh VM state ↔ `PikeTreeInitialState(t, inp)`.
      FILL: `MainTheorem`'s entry construction supplies every conjunct
      (`BoolTreeLk` of the entry acts is established there verbatim); the value
      ties are vacuous on all-init registers; `GateAheadClear` from the
      entry-time absence of every group. */
  lemma LiftInit(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code,
                 crv: CP.FCompiled, str: string, ov: LOr.OracleView, S: set<LG.GroupId>,
                 t: LT.Tree, vms: AI.VmState, ncap: int, nlook: int, nquant: int)
    requires !rer.multiline
    requires T.TransWf(re)
    requires EL.BoolTreeLk(rer, [LS.Areg(T.Translate(re))], LC.InitInput(str), BS.CannotExit, t)
    requires vms.cp == 0
    requires vms.active == [AI.init_thread(AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant))]
    requires vms.blocked == [] && vms.bestmatch.None?
    requires vms.processed == AI.init_bpcset(|code|)
    ensures LiftInv(rer, qm, re, code, crv, str, ov, S,
                    PT.PikeTreeInitialState(t, LC.InitInput(str)), vms, ncap, nlook, nquant)

  /** (4) The epsilon-phase lift: one VM epsilon phase maps to a legal B-trace
      segment preserving the pairing. FILL: the ClockMono frame recursion
      (clone `FAdvanceEpsilonLookCpOk`'s skeleton), stepping B per case —
      skip → `pts_skip` (via `SeenRepLk` + `TtLkSameTree`); `Accept` →
      `pts_match`; `Fork` → `pts_active` on a `Choice` head; `Consume` →
      `pts_blocked`; `SetRegisterToCP`/`SetQuantToClock` → `pts_active` on a
      `GroupActionT` head (`gmt` steps by `GMUpdate`, outside-S tie via the
      standing GmOfLive machinery, inside-S stable since `FreshBodyMatch`
      depends only on `a_cp`); `CheckOracle` pass → the gate: B `pts_active`
      on the LK head with `GateStepValue`; fail → B `pts_active` to dead;
      `Jmp`/`BeginLoop`/`EndLoop`/`AnchorAssertion`/`CheckNullable`/`Fail` →
      walk stutters or dead branches, B follows the same shapes the walk's own
      cases (ActionsTreeRepFRE) enumerate. `WriteOracle` is absent from main
      code. */
  lemma LiftAdvanceEpsilon(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code,
                           crv: CP.FCompiled, str: string, ov: LOr.OracleView, S: set<LG.GroupId>,
                           s: AI.VmState, bst: PT.PikeTreeState, dir: LAnc.direction,
                           ncap: int, nlook: int, nquant: int)
    returns (bst1: PT.PikeTreeState)
    requires !rer.multiline && qm.ov == ov
    requires dir == LAnc.Forward
    requires |s.processed.true_set| == RB.size(code) && |s.processed.false_set| == RB.size(code)
    requires LiftInv(rer, qm, re, code, crv, str, ov, S, bst, s, ncap, nlook, nquant)
    ensures PTL.TrcPikeTreeLk(bst, bst1)
    ensures LiftInv(rer, qm, re, code, crv, str, ov, S, bst1,
                    AI.FAdvanceEpsilon(code, s, ov, dir).0, ncap, nlook, nquant)
    decreases AI.unprocessed(s.processed), |s.active|

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

  /** [SOLID] Jmp is a pure stutter: same tree, walk at the target. */
  lemma TtLkAtJmp(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                  tb: LT.Tree, pc: nat, ea: bool, x: int)
    requires TtLk(rer, qm, code, inp, tb, pc, ea)
    requires NR.GetPcRE(code, pc) == Some(RB.Jmp(x))
    ensures x >= 0 && TtLk(rer, qm, code, inp, tb, x as nat, ea)

  /** [SOLID] BeginLoop is a stutter that forces the flag false. */
  lemma TtLkAtBeginLoop(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                        tb: LT.Tree, pc: nat, ea: bool)
    requires TtLk(rer, qm, code, inp, tb, pc, ea)
    requires NR.GetPcRE(code, pc) == Some(RB.BeginLoop)
    ensures TtLk(rer, qm, code, inp, tb, pc + 1, false)

  /** [SOLID] At Accept the walk is exhausted: the tree is `Match`. */
  lemma TtLkAtAccept(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                     tb: LT.Tree, pc: nat, ea: bool)
    requires TtLk(rer, qm, code, inp, tb, pc, ea)
    requires NR.GetPcRE(code, pc) == Some(RB.Accept)
    ensures tb == LT.Match

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

  /** [SEAM] At SetQuantToClock the tree is the quantifier's `Reset` stamp
      (payload pinned by `qm.quants` — TreeRepDetermRE's note). The fragment
      compiles every stamp with `bq == false` (`NI.CodeShapeAt`). */
  lemma TtLkAtSetQuant(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                       tb: LT.Tree, pc: nat, ea: bool, q: int)
    requires TtLk(rer, qm, code, inp, tb, pc, ea)
    requires NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(q, false))
    ensures tb.GroupActionT? && tb.g.Reset?
    ensures TtLk(rer, qm, code, inp, tb.t, pc + 1, ea)

  /** [SOLID] THE GATE, B side: at `CheckOracle(lid)` the tree IS the gate's
      own node — `LK` when the bit is set (and its `LkResult` verdict agrees
      via `OracleOkAt`), `LKFail` when clear; a passing gate's continuation
      walks from `pc+1` at the SAME input. This is `GateNodeAtInp` +
      `GateFiresAtWalkInp` transported into the pairing's vocabulary — the
      point where LiftAdvanceEpsilon's CheckOracle case meets `GateStepValue`. */
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

  /** `TR.CpOf` re-exported locally (avoids importing TreeRep just for it). */
  function TR_CpOf(inp: LC.Input): nat { |inp.pref| }

  /** [SOLID] At an AnchorAssertion the tree is `AnchorPass` (satisfied) or
      `Mismatch` (mirror of tr_anchorpass / tr_anchorfail). */
  lemma TtLkAtAnchor(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                     tb: LT.Tree, pc: nat, ea: bool, a: R.anchor)
    requires TtLk(rer, qm, code, inp, tb, pc, ea)
    requires NR.GetPcRE(code, pc) == Some(RB.AnchorAssertion(a))
    ensures tb.AnchorPass? || tb == LT.Mismatch
    ensures tb.AnchorPass? ==> TtLk(rer, qm, code, inp, tb.t, pc + 1, ea)

  /** [SOLID] At EndLoop: with the flag armed the tree is `Progress`
      (tr_progress); with it cold the tree is `Mismatch` (tr_progressfail) and
      the VM drops the thread. */
  lemma TtLkAtEndLoop(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                      tb: LT.Tree, pc: nat, ea: bool)
    requires TtLk(rer, qm, code, inp, tb, pc, ea)
    requires NR.GetPcRE(code, pc) == Some(RB.EndLoop)
    ensures ea ==> tb.Progress? && TtLk(rer, qm, code, inp, tb.t, pc + 1, true)
    ensures !ea ==> tb == LT.Mismatch

  /** [SEAM] At a Fork the tree is a `Choice` whose branches walk from the two
      targets. TRUE for the forward forks (Disjunction, quantifier entry); the
      do-while BACKWARD fork at the quant seam has the fused
      `AtBackForkTreeRep` shape — derive the exact seam statement from that
      lemma (615-line file; its fork case enumerates the shapes) and split
      this into forward/backward versions if needed. */
  lemma TtLkAtFork(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                   tb: LT.Tree, pc: nat, ea: bool, x: int, y: int)
    requires TtLk(rer, qm, code, inp, tb, pc, ea)
    requires NR.GetPcRE(code, pc) == Some(RB.Fork(x, y))
    ensures x >= 0 && y >= 0
    ensures (tb.Choice?
             && TtLk(rer, qm, code, inp, tb.t1, x as nat, ea)
             && TtLk(rer, qm, code, inp, tb.t2, y as nat, ea))
         || tb == LT.Mismatch   // the zero-progress back-fork kill (tr's Fork-Mismatch rule)

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
    requires forall lk2: L.Lookaround, r2: L.Regex | GatePending(cont, lk2, r2) ::
               GatePending(acts, lk2, r2) && (lk2 != lk || r2 != r1)
    requires forall lk2: L.Lookaround, r2: L.Regex | GatePending(cont, lk2, r2) ::
               forall g :: g in L.DefGroups(r2) ==> g !in L.DefGroups(r1)
    ensures GateAheadClear(cont, gmerged)

  // ---- (C) the ComputeTr shape fact -----------------------------------------

  /** [SOLID] The spec tree builder only produces machine-B-explorable shapes
      (no `ReadBackRef` in the fragment; LK bodies are unconstrained).
      FILL: structural induction over `ComputeTr` mirroring
      `LFU.ComputeTrIsTree`'s recursion; the fragment premise kills the
      backreference case. */
  lemma PikeSubtreeLkComputeTr(rer: LW.RegExpRecord, re: R.regex, str: string)
    requires T.TransWf(re) && NR.LookBehindFragmentRE(re)
    ensures PTL.PikeSubtreeLk(
      LFU.ComputeTr(rer, [LS.Areg(T.Translate(re))], LC.InitInput(str), LG.Empty, WP.Forward))

  // ---- (V) the value bridge into MainExtraction ------------------------------

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
  lemma L3aValueBridge(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, ast: R.regex,
                       crv: CP.FCompiled, str: string, ov: LOr.OracleView, S: set<LG.GroupId>,
                       th: AI.Thread, leafgm: LG.GroupMap, maxlook: int,
                       ncap: int, nlook: int, nquant: int)
    requires qm.ov == ov
    requires T.TransWf(re) && S == LL.LkBodyGroups(T.Translate(re))
    requires GmtTieOutside(re, th, leafgm, S)
    requires GmtTieInside(crv, str, ov, th, leafgm, S, ncap, nlook, nquant)
    requires M.FLookLoopValueOk(crv, str,
               AI.FLookLoop(crv, str, 0, maxlook, th.capture_regs, th.look_regs, th.quant_regs, ov).0,
               0, maxlook, th.look_regs, ov, ncap, nlook, nquant)
    ensures var res := AI.FLookLoop(crv, str, 0, maxlook, th.capture_regs, th.look_regs, th.quant_regs, ov);
            leafgm == PIV.GmOfLive(re, res.0, th.look_regs, th.quant_regs)

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
