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
          && GateAheadClear(acts, gmt))
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

  /** (3) Initial pairing: fresh VM state ↔ `PikeTreeInitialState(t, inp)`.
      FILL: `MainTheorem`'s entry construction supplies every conjunct
      (`BoolTreeLk` of the entry acts is established there verbatim); the value
      ties are vacuous on all-init registers; `GateAheadClear` from the
      entry-time absence of every group. */
  lemma LiftInit(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code,
                 crv: CP.FCompiled, str: string, ov: LOr.OracleView, S: set<LG.GroupId>,
                 t: LT.Tree, vms: AI.VmState, ncap: int, nlook: int, nquant: int)
    requires !rer.multiline
    requires T.TransWf(re) && NR.LookBehindFragmentRE(re)
    requires code == CP.compile_to_bytecode(re)
    requires AR.ActionsRepL(rer, qm, [LS.Areg(T.Translate(re))], code, 0)
    requires LL.OracleOkSuffix(rer, qm, LC.InitInput(str))
    requires EL.BoolTreeLk(rer, [LS.Areg(T.Translate(re))], LC.InitInput(str), BS.CannotExit, t)
    requires vms.cp == 0
    requires vms.active == [AI.init_thread(AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant))]
    requires vms.blocked == [] && vms.bestmatch.None?
    requires vms.processed == AI.init_bpcset(|code|)
    ensures LiftInv(rer, qm, re, code, crv, str, ov, S,
                    PT.PikeTreeInitialState(t, LC.InitInput(str)), vms, ncap, nlook, nquant)
  {
    var inp := LC.InitInput(str);
    var itr := AI.init_thread(AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant));
    var acts := [LS.Areg(T.Translate(re))];
    var bst := PT.PikeTreeInitialState(t, inp);
    assert bst == PT.PTS(inp, [(t, LG.Empty)], None, [], SS.InitialSeenTrees);

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
      assert exists actsw: LS.Actions, bw: BS.LoopBool ::
          AR.ActionsRepL(rer, qm, actsw, code, itr.pc as nat)
          && EL.PikeLkActions(actsw)
          && ATR.EaOf(bw) == itr.exit_allowed
          && EL.BoolTreeLk(rer, actsw, inp, bw, t)
          && GateAheadClear(actsw, LG.Empty);
      assert PIV.GmOfLive(re, itr.capture_regs, itr.look_regs, itr.quant_regs) == LG.Empty;
      assert GmtTieOutside(re, itr, LG.Empty, S);
      assert GmtTieInside(crv, str, ov, itr, LG.Empty, S, ncap, nlook, nquant);  // vacuous
    }
    assert ActiveRepLk(rer, qm, re, code, inp, crv, str, ov, S, [(t, LG.Empty)], [itr], ncap, nlook, nquant);

    // blocked: both sides empty (vms.blocked == [])
    forall nextinp | LC.AdvanceInput(inp, WP.Forward) == Some(nextinp)
      ensures BlockedRepLk(rer, qm, re, code, inp, nextinp, crv, str, ov, S, [],
                           PIV.MatchingBlocked(LC.Reverse(vms.blocked), inp), ncap, nlook, nquant)
    {
      assert LC.Reverse(vms.blocked) == [];
      assert PIV.MatchingBlocked([], inp) == [];
    }
    assert BestTieLk(re, crv, str, ov, S, None, vms.bestmatch, ncap, nlook, nquant);
  }

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
    requires forall lk2: L.Lookaround, r2: L.Regex | GatePending(cont, lk2, r2) ::
               GatePending(acts, lk2, r2) && (lk2 != lk || r2 != r1)
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
  // ---- (K) THE COMPOSITE SIM (backfill) --------------------------------------
  //
  // The standalone TtLk/BoolTreeLk VM-walk (above) is architecturally flawed:
  // its `ActionsRepL` walk has no representation at a `BeginLoop`, so the VM↔B
  // pairing cannot be threaded through a free-star iteration. The FIX is to ride
  // the PROVEN machine-A simulation `PSM.PikeInvFullRE` for ALL VM mechanics
  // (its `TreeRepRE` carries the `tr_begin`/BeginLoop disjunct), and add ONLY a
  // machine-A(tstar)↔machine-B(t) tree pairing that carries the value payload.
  //
  // KEY STRUCTURAL FACTS (from the two machine audits):
  //  * `PikeInvFullRE(ptsA, vms)` relates the VM to a machine-A PikeTree state
  //    `ptsA` (on the gate-transparent `tstar`), element-wise `vms.active[i]`
  //    ↔ `ptsA.active[i]` via `TreeRepRE`.
  //  * A `CheckOracle` gate is a machine-A STUTTER (`PSM.PreserveOraclePass`:
  //    `ptsA` unchanged, only the VM writes `a_cp[l] := cp`).
  //  * Machine B (`PTL.PikeTreeStepLk`, on `t`) DOES step an `LK` node: it
  //    merges `LS.LkResult(lk, tlk, gm, inp)` into the continuation.
  //  * `tstar` and `t` agree only LEAF-wise (`LL.LeavesAgreeAtOutside`); there
  //    is NO node-level dissolve function. BUT `LL.LAAtGatePassL3a` gives the
  //    per-gate node dissolution: a passing positive `LK(lk,tlk,tc)` leaf-agrees
  //    its continuation `tc` outside `S`. So the leaf pairing SURVIVES a gate.
  //  * `GateStepValue` (verified) preserves `GmtTieInside` across that one gate
  //    (payload: `th → th2` with the `a_cp` write, `gmt → LkResult(...).value`).
  //
  // So the gate step composes: `PreserveOraclePass` (VM+ptsA) ∥ machine-B LK
  // merge (ptsB) ∥ `LAAtGatePassL3a` (leaf agreement) ∥ `GateStepValue`
  // (payload). Non-gate steps move both machines the same way and leave the
  // inside-`S` payload untouched (`GateAheadClear`).

  /** Per-active-pair tie: the machine-A subtree `ta` (tstar side) and machine-B
      subtree `tb` (t side) leaf-agree outside `S`, and the VM thread `th` carries
      the two-sided value tie against `tb`'s group map `gm`. Replaces the flawed
      `ThreadRepLk` (its `BoolTreeLk` walk clause is dropped — the VM↔ta link now
      lives in `PikeInvFullRE`; only the ta↔tb leaf link and the payload remain).

      TWO NOTES FOR THE STEP FILL (`LiftStepC`):
      (1) POSITION TIE IS AUTOMATIC. `LiftInvC` pins `ptsA.inp == inp ==
          InpOfCp(str, vms.cp)`, so when the VM crosses `CheckOracle(l)` it writes
          `a_cp[l] := vms.cp` — which IS the paired LK node's position `cp` that
          `GateStepValue` consumes. No separate position-tie proof; it falls out of
          position-synchronisation, and `GateStepValue` ties the value.
      (2) MISSING STRUCTURAL LINK — this predicate is NOT yet strong enough for the
          step. Leaf agreement alone does not tell me that when the VM is at
          `CheckOracle(l)` the paired `tb` is `LK(lk_l, tlk, tc)` (needed to fire the
          machine-B LK step + `GateStepValue`). `PikeInvFullRE` links VM↔ta (tstar,
          gate-TRANSPARENT — no LK node), and `ta` is already one gate AHEAD of `tb`
          at a gate. The fill must add a HEAD-level ta↔tb correspondence that (a)
          lets `tb` be gate-ahead of `ta` (`tb == LK(..,tc)`, `ta` pairs `tc`), and
          (b) survives BeginLoop (the reason the `BoolTreeLk` walk failed). Candidate:
          a `GateAhead(ta, tb)` relation ("`tb` is `ta` with pending head gates"),
          preserved by `LAAtGatePassL3a` at gates and by identical heads elsewhere. */
  ghost predicate LiftPairC(re: R.regex, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
                            inp: LC.Input, S: set<LG.GroupId>, ta: LT.Tree, tb: LT.Tree,
                            gm: LG.GroupMap, th: AI.Thread, ncap: int, nlook: int, nquant: int) {
    LL.LeavesAgreeAtOutside(ta, tb, inp, S)
    && GmtTieOutside(re, th, gm, S)
    && GmtTieInside(crv, str, ov, th, gm, S, ncap, nlook, nquant)
  }

  /** The three active worklists (machine A `al`, machine B `bl`, VM `vl`) pair
      index-wise (priority is positional). Mirrors `ActiveRepLk`/`ActiveRepRE`. */
  ghost predicate ActivePairC(re: R.regex, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
                              inp: LC.Input, S: set<LG.GroupId>,
                              al: seq<(LT.Tree, LG.GroupMap)>, bl: seq<(LT.Tree, LG.GroupMap)>,
                              vl: seq<AI.Thread>, ncap: int, nlook: int, nquant: int)
    decreases bl
  {
    (|al| == 0 && |bl| == 0 && |vl| == 0)
    || (|al| > 0 && |bl| > 0 && |vl| > 0
        && LiftPairC(re, crv, str, ov, inp, S, al[0].0, bl[0].0, bl[0].1, vl[0], ncap, nlook, nquant)
        && ActivePairC(re, crv, str, ov, inp, S, al[1..], bl[1..], vl[1..], ncap, nlook, nquant))
  }

  /** THE COMPOSITE INVARIANT: machine-A sim (VM↔tstar, PROVEN) PLUS the
      machine-A↔machine-B tree pairing + value payload. `ptsA` is the tstar
      (gate-transparent) PikeTree state driven by `PikeInvFullRE`; `ptsB` is the
      `t` (LK-aware) PikeTree state driven by `PTL.PikeTreeStepLk`. */
  ghost predicate LiftInvC(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code,
                           endl: nat, ngroups: nat, crv: CP.FCompiled, str: string,
                           ov: LOr.OracleView, S: set<LG.GroupId>,
                           ptsA: PT.PikeTreeState, ptsB: PT.PikeTreeState, vms: AI.VmState,
                           ncap: int, nlook: int, nquant: int)
    requires NR.NfaRepRE(re, code, 0, endl)
  {
    PSM.PikeInvFullRE(rer, qm, re, code, endl, ngroups, str, ptsA, vms, ncap, nlook, nquant)
    && (match ptsB
        case PTS_final(bbest) =>
          BestTieLk(re, crv, str, ov, S, bbest, vms.bestmatch, ncap, nlook, nquant)
        case PTS(inp, bactive, bbest, bblocked, bseen) =>
          ptsA.PTS? && ptsA.inp == inp
          && ActivePairC(re, crv, str, ov, inp, S, ptsA.active, bactive, vms.active, ncap, nlook, nquant)
          && BestTieLk(re, crv, str, ov, S, bbest, vms.bestmatch, ncap, nlook, nquant)
          && LL.OracleOkSuffix(rer, qm, inp))
  }

  /** (K-init) The composite holds at the start: `PSM.InitialPikeInvFullRE` gives
      the machine-A half; the single active pair `(tstar, t, init_thread)` ties
      via `LeavesAgreeAtOutside(tstar, t)` (hypothesis) + a VACUOUS payload
      (init thread's live map is `LG.Empty`, no `g in S`). BODILESS. */
  lemma LiftInitC(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code,
                  endl: nat, ngroups: nat, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
                  S: set<LG.GroupId>, tstar: LT.Tree, t: LT.Tree, inp: LC.Input, vms: AI.VmState,
                  ncap: int, nlook: int, nquant: int)
    requires NR.NfaRepRE(re, code, 0, endl)
    requires PSM.PikeInvFullRE(rer, qm, re, code, endl, ngroups, str,
                               PT.PikeTreeInitialState(tstar, inp), vms, ncap, nlook, nquant)
    requires LL.LeavesAgreeAtOutside(tstar, t, inp, S)
    requires LL.OracleOkSuffix(rer, qm, inp)
    requires inp == PIV.InpOfCp(str, vms.cp) && 0 <= vms.cp <= |str|
    requires vms.active == [AI.init_thread(AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant))]
    requires vms.bestmatch.None?
    ensures LiftInvC(rer, qm, re, code, endl, ngroups, crv, str, ov, S,
                     PT.PikeTreeInitialState(tstar, inp), PT.PikeTreeInitialState(t, inp), vms,
                     ncap, nlook, nquant)
  {
    // The one active pair (tstar, t, init_thread): leaf agreement is the
    // hypothesis; the payload is vacuous because a fresh thread denotes Empty.
    PIV.GmOfLiveInit(re, ncap, nlook, nquant);        // GmOfLive(re, init...) == Empty
    var it := AI.init_thread(AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant));
    assert it.capture_regs == AReg.init_regs(ncap)
        && it.look_regs == AReg.init_regs(nlook) && it.quant_regs == AReg.init_regs(nquant);
    assert GmtTieOutside(re, it, LG.Empty, S);          // gml == Empty, agrees with Empty
    assert GmtTieInside(crv, str, ov, it, LG.Empty, S, ncap, nlook, nquant);  // no g in Empty
    // ptsB = PTS(inp, [(t, Empty)], None, [], InitialSeenTrees); its single active
    // pair ties via LiftPairC; best is None both sides.
  }

  /** (K-step) The composite is preserved across ONE position. Machine A advances
      by `PSM.InvariantPreservationRE` (a whole-position `TrcRE`); machine B
      advances by a matching `PTL.TrcPikeTreeLk` on `ptsB`; the pairing is
      re-established pair-by-pair. The gate case is the crux: `PreserveOraclePass`
      + machine-B `LK` merge + `LL.LAAtGatePassL3a` + `GateStepValue`. Non-gate
      cases move both machines identically and leave inside-`S` untouched
      (`GateAheadClear`). SEAM: also needs a real seen/processed pairing (the
      standalone `SeenRepLk` is stubbed `true`). BODILESS. */
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
    ensures LiftInvC(rer, qm, re, code, endl, ngroups, crv, str, ov, S,
                     ptsA', ptsB', AI.FAdvanceEpsilon(code, vms, ov, LAnc.Forward).0, ncap, nlook, nquant)

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
    requires LL.LeavesAgreeAtOutside(tstar, t, inp, S)
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
