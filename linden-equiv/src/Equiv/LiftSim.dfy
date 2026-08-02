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
}
