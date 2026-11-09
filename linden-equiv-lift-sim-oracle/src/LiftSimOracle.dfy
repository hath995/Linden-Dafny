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
module LindenElkLiftSimOracle {
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
  import CW = LindenElkCinWalk
  import opened LindenElkLiftSimCore

  /** The keystone's `Empty` hypothesis, as a walk-state invariant: any gate
      pending without an intervening reset has its body groups ABSENT from the
      accumulated map. First encounter: never set; re-entry: the iteration's
      `Reset` cleared them; other lids' merges are disjoint
      (`M.LmOfBodiesDisjoint`). */
  ghost predicate GateAheadClear(acts: LS.Actions, gmt: LG.GroupMap) {
    forall lk: L.Lookaround, r1: L.Regex | GatePending(acts, lk, r1) ::
      forall g :: g in L.DefGroups(r1) ==> g !in gmt
  }

  /** (D3) `BestTieLkNested` with the two look-path carriers restricted to
      TOP-LEVEL looks (`*Top` variants). Consumed ONLY by the `*Rec` tier
      (`LiftInvRec`, `L3aCompositeCloseRec`) — leaves the depth-1/`Nested`
      tiers' `BestTieLkNested` untouched. */
  ghost predicate BestTieLkNestedTop(rer: LW.RegExpRecord, re: R.regex, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
                                     S: set<LG.GroupId>, bbest: Option<LT.Leaf>, bm: Option<AI.Thread>,
                                     ncap: int, nlook: int, nquant: int) {
    (bbest.None? <==> bm.None?)
    && (bbest.Some? ==>
          bm.Some?
          && GmtTieOutside(re, bm.value, bbest.value.1, S)
          && LookNestOkTTop(re, S, bbest.value.1, bm.value)
          && LookNestBackTTop(re, crv, str, ov, S, bbest.value.1, bm.value, ncap, nlook, nquant)
          // (R2 DEEP CARRIER) the strengthened converse: lands l's WHOLE
          // sub-first-leaf captures (inner-look included), not just direct ones.
          && LookNestBackTTopDeep(rer, re, crv, str, ov, S, bbest.value.1, bm.value, ncap, nlook, nquant))
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

  ghost predicate GateStaticsOkNested(qm: AR.QMap, re: R.regex, crv: CP.FCompiled,
                                      ncap: int, nlook: int, nquant: int) {
    forall l: int | l in qm.looks ::
      0 <= l < nlook && GateStaticAtNested(qm, re, crv, l, ncap, nlook, nquant)
  }

  /** (§2.3/§2.4 perf) A lid whose body holds a capture and whose record is set is a
      matched POSITIVE look: the hub row's negative-look clause, picked in a minimal
      context (in the giant reverse-descent lemmas this pick took 5+ minutes). */
  lemma MatchedPosFromHub(qm: AR.QMap, re: R.regex, crv: CP.FCompiled, lk: AReg.Regs, lid: nat, g: nat,
                          ncap: int, nlook: int, nquant: int)
    requires GateStaticsOkNested(qm, re, crv, ncap, nlook, nquant)
    requires (lid as int) in qm.looks
    requires LTB.LookTablesOk(re, crv) && lid in LTB.LookIds(re)
    requires g in PIV.CapIds(NI.LookBodyOfRE(re, lid))
    requires AReg.get_cp(lk, lid as int).Some?
    ensures M.MatchedPosLA(crv, lk, lid as int)
  {
    assert GateStaticAtNested(qm, re, crv, lid as int, ncap, nlook, nquant) by {
      hide *; reveal GateStaticsOkNested;
    }
    var la: R.lookaround, b: R.regex :|
      LTB.LookEntryOk(crv, lid as int, la, b)
      && T.TransWf(b) && NR.NestedFragmentRE(b)
      && EL.NegBehindLookFreeRE(b)
      && (la.Lookbehind? ==> NR.LBOnlyLooksRE(b))
      && (!la.Lookbehind? ==> L5ScopeV1RE(b))
      && qm.looks[lid as int].0 == T.TrLookaround(la)
      && qm.looks[lid as int].1 == T.Translate(b)
      && (set gx: LG.GroupId | gx in L.DefGroups(T.Translate(b))) <= PIV.CapIdsInLooks(re)
      && var bc := CP.compile_to_bytecode(b);
      |bc| >= 1
      && PSM.StaticOkNestedRE(qm, b, bc, |bc| - 1)
      && PSM.SizesOkRE(b, ncap, nlook, nquant)
      && ((la.NegLookbehind? || la.NegLookahead?) ==> NR.CaptureFreeRE(b));
    assert crv.f_look_types[lid as int] == la;
    assert b == NI.LookBodyOfRE(re, lid) by {
      NI.LookBodyOfTablesTie(re, crv, lid);
      var laT: R.lookaround :| LTB.LookEntryOk(crv, lid as int, laT, NI.LookBodyOfRE(re, lid));
      assert crv.f_look_ast[lid as int] == b == NI.LookBodyOfRE(re, lid);
    }
    if la.NegLookahead? || la.NegLookbehind? {
      PIV.CaptureFreeNoCapIds(b);
      assert false;
    }
    assert AI.capture_type(crv.f_look_types[lid as int]);
  }

  /** (L4 NESTED) `GateStaticsSweepRENested` — the nested-fragment establishment
      sweep, off `GateStaticsSweepRE`. Two changes: the body-cap facts are the
      NESTED ones (`NestedFragmentRE`/`StaticOkNestedRE` via
      `CompileToBytecodeRepNested`+`CompileStutterTameRENested`), and — crucially —
      the sweep RECURSES INTO each lookaround body (`GateStaticsSweepRE` stopped at
      the leaf because look-free bodies own no lids). Every static fact descends
      DEFINITIONALLY to the body at a `Re_lookaround` node (TransWf/QmapOk/LmapOk/
      CapUnique/QuantUnique/NestedFragmentRE/NegLooksLookFreeRE/NoPosLookbehindRE/
      LookTablesOk/SizesOkRE); the confinement descends via `CapIdsInLooks(body) ⊆
      CapIds(body) == CapIdsInLooks(re) ⊆ CapIdsInLooks(re0)`. `re0` carries the
      whole-regex confinement target. */
  lemma GateStaticsSweepRENested(qm: AR.QMap, re0: R.regex, re: R.regex, crv: CP.FCompiled,
                                 ncap: int, nlook: int, nquant: int)
    requires T.TransWf(re) && AR.QmapOk(re, qm) && AR.LmapOk(re, qm)
    requires M.LooksNoNulledPlusRE(re)   // (§2.5b F-c) look bodies stay stamp-free
    requires NR.NestedFragmentRE(re) && EL.NegBehindLookFreeRE(re) && L5ScopeV1RE(re)
    requires PIV.CapUnique(re) && PIV.QuantUnique(re)
    requires LTB.LookTablesOk(re, crv)
    requires PSM.SizesOkRE(re, ncap, nlook, nquant)
    requires PIV.CapIdsInLooks(re) <= PIV.CapIdsInLooks(re0)
    ensures forall l: int :: l >= 0 && (l as nat) in LTB.LookIds(re) ==>
                               GateStaticAtNested(qm, re0, crv, l, ncap, nlook, nquant)
    decreases re
  {
    reveal L5ScopeV1RE();                   // (s6 widening) the per-node kind-split conjunct
    match re
    case Re_alt(r1, r2) =>
      GateStaticsSweepRENested(qm, re0, r1, crv, ncap, nlook, nquant);
      GateStaticsSweepRENested(qm, re0, r2, crv, ncap, nlook, nquant);
    case Re_con(r1, r2) =>
      GateStaticsSweepRENested(qm, re0, r1, crv, ncap, nlook, nquant);
      GateStaticsSweepRENested(qm, re0, r2, crv, ncap, nlook, nquant);
    case Re_quant(_, _, _, r1) =>
      GateStaticsSweepRENested(qm, re0, r1, crv, ncap, nlook, nquant);
    case Re_capture(_, r1) =>
      GateStaticsSweepRENested(qm, re0, r1, crv, ncap, nlook, nquant);
    case Re_lookaround(lid, la, body) =>
      // confinement: CapIdsInLooks(body) ⊆ CapIds(body) == CapIdsInLooks(re) ⊆ CapIdsInLooks(re0)
      PIV.CapIdsSplit(body);
      assert PIV.CapIdsInLooks(re) == PIV.CapIds(body);
      assert PIV.CapIdsInLooks(body) <= PIV.CapIdsInLooks(re0);
      // recurse into the body for its OWN inner lids
      M.LooksNoNulledPlusFromFull(body);   // (§2.5b F-c) the body is stamp-free
      GateStaticsSweepRENested(qm, re0, body, crv, ncap, nlook, nquant);
      if lid >= 0 {
        // the node's own bundle
        assert LTB.LookEntryOk(crv, lid, la, body);
        assert T.TransWf(body) && NR.NestedFragmentRE(body)
               && EL.NegBehindLookFreeRE(body);
        assert NR.NoNulledPlusRE(body);   // §2.5b: descends definitionally
        assert (la.Lookbehind? ==> NR.LBOnlyLooksRE(body))                  // (L5 F7f) kind-split
               && (!la.Lookbehind? ==> L5ScopeV1RE(body));
        assert lid in qm.looks && qm.looks[lid] == (T.TrLookaround(la), T.Translate(body));
        // confinement: the body's groups are inside-look groups of re0
        M.TranslateDefGroupsEqCapIds(body);
        assert (set g: LG.GroupId | g in L.DefGroups(T.Translate(body))) <= PIV.CapIdsInLooks(re0);
        // compile statics for the body's own bytecode (NESTED)
        NR.CompileToBytecodeRepNested(body);
        CompileStutterTameRENested(body);
        var bodycode := CP.compile_to_bytecode(body);
        var next := CP.compile(body, 0, CP.Progress).1;
        assert next >= 0 && |bodycode| == next + 1 && |bodycode| >= 1;
        assert NR.NfaRepRE(body, bodycode, 0, next as nat)
               && NR.GetPcRE(bodycode, next as nat) == Some(RB.Accept);
        assert (next as nat) == |bodycode| - 1;
        assert PSM.StaticOkNestedRE(qm, body, bodycode, |bodycode| - 1);
        assert PSM.SizesOkRE(body, ncap, nlook, nquant);
        assert (la.NegLookbehind? || la.NegLookahead?) ==> NR.CaptureFreeRE(body);
        assert GateStaticAtNested(qm, re0, crv, lid, ncap, nlook, nquant);
      }
    case _ =>
  }

  /** (L4 NESTED) TOP-LEVEL establishment of `GateStaticsOkNested` from the
      compile tables + nested-fragment well-formedness (`M.NoPosLookbehindRE` +
      `EL.NegBehindLookFreeRE` pin the positive-lookahead-nesting scope). Proves
      `GateStaticsOkNested` is DISCHARGEABLE for the nested fragment — the
      "requires-side" of the non-vacuity claim. Off `GateStaticsFromTables`. */
  lemma GateStaticsFromTablesNested(qm: AR.QMap, re: R.regex, crv: CP.FCompiled,
                                    ncap: int, nlook: int, nquant: int)
    requires T.TransWf(re) && AR.QmapOk(re, qm) && AR.LmapOk(re, qm)
    requires M.LooksNoNulledPlusRE(re)   // (§2.5b F-c) look bodies stay stamp-free
    requires NR.NestedFragmentRE(re) && EL.NegBehindLookFreeRE(re) && L5ScopeV1RE(re)
    requires PIV.CapUnique(re) && PIV.QuantUnique(re)
    requires LTB.LookTablesOk(re, crv)
    requires PSM.SizesOkRE(re, ncap, nlook, nquant)
    requires forall l: int :: l in qm.looks ==>
                                l >= 0 && (l as nat) in LTB.LookIds(re) && l < nlook
    ensures GateStaticsOkNested(qm, re, crv, ncap, nlook, nquant)
  {
    GateStaticsSweepRENested(qm, re, re, crv, ncap, nlook, nquant);
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

  /** (R2 — definitional identification) `SubFirstLeafAt(A0, lk)` IS the body
      replay's first-leaf group map: the spec body tree `t` that
      `LookNestBackTFromBodyReplay` builds at `cp = get_cp(lk, A0)` over
      `Translate(body)` has `FirstLeaf(t, inp) == TreeRes(t, Empty, inp, Forward)`
      (definitional), and `SubFirstLeafAt` unfolds to exactly that `TreeRes`'s group
      map (`body == VBody(crv, A0)`, same `cp`, same `inp`). This lets the body
      replay's DEEP carrier — stated on `FirstLeaf(t).value.1` — feed the deep
      per-`g2` existential, whose landing target is `SubFirstLeafAt(A0)`. */
  lemma BodyReplayGmtIsSubFirstLeaf(rer: LW.RegExpRecord, crv: CP.FCompiled, str: string,
                                    A0: int, lk: AReg.Regs, body: R.regex)
    requires body == M.VBody(crv, A0)
    requires T.TransWf(body)
    requires LidDir(crv, A0) == WP.Forward                   // (L5 F7a) a lookAHEAD lid
    requires AReg.get_cp(lk, A0).Some? && AReg.get_cp(lk, A0).value <= |str|
    ensures var cp := AReg.get_cp(lk, A0).value;
            var inp := PIV.InpOfCp(str, cp);
            var t := LFU.ComputeTr(rer, [LS.Areg(T.Translate(body))], inp, LG.Empty, WP.Forward);
            (LT.FirstLeaf(t, inp).Some? <==> SubFirstLeafAt(rer, crv, str, A0, lk).Some?)
            && (LT.FirstLeaf(t, inp).Some? ==>
                  SubFirstLeafAt(rer, crv, str, A0, lk) == Some(LT.FirstLeaf(t, inp).value.1))
  {
    var cp := AReg.get_cp(lk, A0).value;
    var inp := PIV.InpOfCp(str, cp);
    var acts := [LS.Areg(T.Translate(body))];
    LFU.ComputeTrIsTree(rer, acts, inp, LG.Empty, WP.Forward);
    var t := LFU.ComputeTr(rer, acts, inp, LG.Empty, WP.Forward);
    assert LS.IsTree(rer, acts, inp, LG.Empty, WP.Forward, t);
    assert LT.FirstLeaf(t, inp) == LT.TreeRes(t, LG.Empty, inp, WP.Forward);   // definitional
    // SubFirstLeafAt unfolds to TreeRes(t, Empty, inp, Forward) at the same cp/body.
  }

  /** (R2 — the DEEP carrier) The strengthening of `LookNestBackTTop` from `l`'s
      DIRECT captures (`GmOfLive(body(l), FreshBodyMatch(l))`) to `l`'s WHOLE
      sub-first-leaf (`SubFirstLeafAt(l)`, deep/inner-look captures included). Same
      shape, same hypotheses (matched + path-dominant top look on `th`'s banks);
      only the landed set grows. This is the carrier the reverse-recon DEEP descent
      needs: at the final leaf it lands every recon-live inside-look capture, not
      just the directly-owned ones. `LookNestBackTTop` is its DIRECT-slice
      specialization (`GmOfLive(body(l), fresh) ⊆ SubFirstLeafAt(l)` on the outer
      groups). */
  ghost predicate LookNestBackTTopDeep(rer: LW.RegExpRecord, re: R.regex, crv: CP.FCompiled,
                                       str: string, ov: LOr.OracleView, S: set<LG.GroupId>,
                                       gmt: LG.GroupMap, th: AI.Thread,
                                       ncap: int, nlook: int, nquant: int) {
    forall lid: nat | lid in NI.TopLookIds(re) ::
      (M.MatchedPosLA(crv, th.look_regs, lid as int)
       && lid in LTB.LookIds(re)   // (2026-08-25) wf guard for `LookPathDom` (TopLookIds ⊆ LookIds)
       && NI.LookPathDom(re, AI.get_idx(th.look_regs.a_clk, lid as int), th.quant_regs.a_clk, lid))
      ==>
        var lsub := SubFirstLeafAt(rer, crv, str, lid as int, th.look_regs);
        lsub.Some? ==>
          forall g: LG.GroupId ::
            g in S && g in PIV.CapIds(NI.LookBodyOfRE(re, lid)) ==>
              // REGION EQUALITY at a matched+dominant top look: the leaf gm's
              // lid-region IS lid's sub-first-leaf — membership BOTH ways + values.
              (g in lsub.value ==> g in gmt && gmt[g] == lsub.value[g])
              && (g in gmt ==> g in lsub.value)
  }

  /** (R2 — DEEP gate-pass maintenance) `LookNestBackTGatePassTop` for the DEEP
      carrier. Verbatim structure: for the crossed lid `l0` the caller supplies the
      landing (its `SubFirstLeafAt(l0)` groups are in `gmt'` — dischargeable by
      `LkResultLandsSubFirstLeaf` at the crossing, since `gm2 == LkResult` contains
      the whole sub-first-leaf); every other top lid is transported by CONGRUENCE —
      `SubFirstLeafAt` and `MatchedPosLA` read only `look_regs`'s `l`-th cp, which is
      unchanged off `l0`, and `gmt` only grows. So the STRENGTHENED carrier threads
      the gate exactly as the direct one does — the position tie is definitional at
      the crossing (LEAD 1), NOT a path-history obligation. */
  lemma LookNestBackTGatePassTopDeep(rer: LW.RegExpRecord, re: R.regex, crv: CP.FCompiled,
                                     str: string, ov: LOr.OracleView, S: set<LG.GroupId>,
                                     gmt: LG.GroupMap, gmt': LG.GroupMap,
                                     th: AI.Thread, th': AI.Thread, l0: int,
                                     ncap: int, nlook: int, nquant: int)
    requires PIV.CapUnique(re) && LTB.LookUnique(re)
    requires l0 >= 0 && (l0 as nat) in LTB.LookIds(re) ==> (l0 as nat) in NI.TopLookIds(re)
    requires LookNestBackTTopDeep(rer, re, crv, str, ov, S, gmt, th, ncap, nlook, nquant)
    requires th'.quant_regs == th.quant_regs
    requires forall j: int :: j != l0 ==>
                                AI.get_idx(th'.look_regs.a_clk, j) == AI.get_idx(th.look_regs.a_clk, j)
                                && AI.get_idx(th'.look_regs.a_cp, j) == AI.get_idx(th.look_regs.a_cp, j)
    // REGION FRAME off l0's body: the step preserves every other region verbatim.
    requires forall g: LG.GroupId ::
               g in S && !(l0 >= 0 && (l0 as nat) in LTB.LookIds(re) && g in PIV.CapIds(NI.LookBodyOfRE(re, l0 as nat)))
               ==> ((g in gmt <==> g in gmt') && (g in gmt ==> gmt'[g] == gmt[g]))
    // the crossing: l0's region in gmt' IS its (fresh) sub-first-leaf.
    requires l0 >= 0 && (l0 as nat) in LTB.LookIds(re) ==>
               var lsub := SubFirstLeafAt(rer, crv, str, l0, th'.look_regs);
               lsub.Some? ==>
                 forall g: LG.GroupId ::
                   g in S && g in PIV.CapIds(NI.LookBodyOfRE(re, l0 as nat)) ==>
                     (g in lsub.value ==> g in gmt' && gmt'[g] == lsub.value[g])
                     && (g in gmt' ==> g in lsub.value)
    ensures LookNestBackTTopDeep(rer, re, crv, str, ov, S, gmt', th', ncap, nlook, nquant)
  {
    NI.TopLookIdsIn(re);
    forall lid: nat | lid in NI.TopLookIds(re)
                      && M.MatchedPosLA(crv, th'.look_regs, lid as int)
                      && NI.LookPathDom(re, AI.get_idx(th'.look_regs.a_clk, lid as int), th'.quant_regs.a_clk, lid)
      ensures var lsub := SubFirstLeafAt(rer, crv, str, lid as int, th'.look_regs);
              lsub.Some? ==>
                forall g: LG.GroupId ::
                  g in S && g in PIV.CapIds(NI.LookBodyOfRE(re, lid)) ==>
                    (g in lsub.value ==> g in gmt' && gmt'[g] == lsub.value[g])
                    && (g in gmt' ==> g in lsub.value)
    {
      if lid as int == l0 {
        // established fresh at the crossing (caller's requires)
      } else {
        assert AI.get_idx(th'.look_regs.a_clk, lid as int) == AI.get_idx(th.look_regs.a_clk, lid as int);
        assert AReg.get_cp(th'.look_regs, lid as int) == AReg.get_cp(th.look_regs, lid as int) by {
          assert AI.get_idx(th'.look_regs.a_cp, lid as int) == AI.get_idx(th.look_regs.a_cp, lid as int);
        }
        assert M.MatchedPosLA(crv, th.look_regs, lid as int);
        assert SubFirstLeafAt(rer, crv, str, lid as int, th'.look_regs)
            == SubFirstLeafAt(rer, crv, str, lid as int, th.look_regs);   // reads only get_cp at lid
        // lid's region is off l0's body (top-top cap disjointness), so the frame applies.
        var lsub := SubFirstLeafAt(rer, crv, str, lid as int, th'.look_regs);
        forall g: LG.GroupId | g in S && g in PIV.CapIds(NI.LookBodyOfRE(re, lid))
          ensures !(l0 >= 0 && (l0 as nat) in LTB.LookIds(re) && g in PIV.CapIds(NI.LookBodyOfRE(re, l0 as nat)))
        {
          if l0 >= 0 && (l0 as nat) in LTB.LookIds(re) && g in PIV.CapIds(NI.LookBodyOfRE(re, l0 as nat)) {
            if lid == l0 as nat {
              assert false;                                    // lid != l0 in this branch
            } else {
              NI.LookBodiesCapsDisjointOrNested(re, lid, l0 as nat);
              NI.TopLookIdsIn(re);
              NI.TopLookNotNested(re, lid, l0 as nat);         // lid !in LookIds(body(l0))
              NI.TopLookNotNested(re, l0 as nat, lid);         // l0 !in LookIds(body(lid))
              assert g in PIV.CapIds(NI.LookBodyOfRE(re, lid)) * PIV.CapIds(NI.LookBodyOfRE(re, l0 as nat));
              assert false;
            }
          }
        }
      }
    }
  }

  /** (R2 — DEEP landing) The deep analogue of the empty-bodied `DescentLandTop`:
      pure instantiation of the DEEP carrier. For a matched + path-dominant top look
      `A0` whose sub-first-leaf `SubFirstLeafAt(A0)` carries a deep inside-look
      capture `g2`, the carrier lands `g2` in `gmt`. */
  lemma DescentLandTopDeep(
    rer: LW.RegExpRecord, re: R.regex, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
    S: set<LG.GroupId>, gmt: LG.GroupMap, thread: AI.Thread, A0: nat, g2: nat,
    ncap: int, nlook: int, nquant: int)
    requires S == PIV.CapIdsInLooks(re)
    requires LookNestBackTTopDeep(rer, re, crv, str, ov, S, gmt, thread, ncap, nlook, nquant)
    requires A0 in NI.TopLookIds(re)
    requires A0 in LTB.LookIds(re)
    requires M.MatchedPosLA(crv, thread.look_regs, A0 as int)
    requires NI.LookPathDom(re, AI.get_idx(thread.look_regs.a_clk, A0 as int), thread.quant_regs.a_clk, A0)
    requires g2 in S && g2 in PIV.CapIds(NI.LookBodyOfRE(re, A0))
    requires var lsub := SubFirstLeafAt(rer, crv, str, A0 as int, thread.look_regs);
             lsub.Some? && g2 in lsub.value
    ensures g2 in gmt
    ensures var lsub := SubFirstLeafAt(rer, crv, str, A0 as int, thread.look_regs);
            gmt[g2] == lsub.value[g2]
  {
  }

  /** (R2 direct-capture landing) A DIRECTLY-owned inside-look capture `g2` (in
      `body`'s caps but OUTSIDE `body`'s own inner looks) that the FRESH body match
      of a top lookAHEAD `A0` carries LIVE lands in `A0`'s sub-first-leaf
      `SubFirstLeafAt(A0, lk)`. `M.ReplayCapIsBodyLeafNested` ties the fresh body
      match to `A0`'s CHECKED first leaf (`bestT.value.1 == GmOfLive(body, fresh)`)
      and `GmAgreeOutside(bestT.value.1, FirstLeaf(t).value.1, LkBodyGroups)`; since
      `g2` is DIRECT (outside `CapIdsInLooks(body) == LkBodyGroups(Translate(body))`)
      it survives into `FirstLeaf(t).value.1`, which is definitionally the
      `SubFirstLeafAt(A0, lk).value` (`FirstLeaf == TreeRes(·,Empty,·,Forward)`).
      This is the concrete `g2 in GmOfLive(body(A0), FreshBodyMatch(A0)) ==> g2 in
      SubFirstLeafAt(A0)` bridge the DIRECT case of the reverse-recon deep descent
      needs (the deep case is delivered by the per-body replay `LookNestBackTFrom
      BodyReplay` + inner descent instead). */
  lemma FreshBodyDirectInSubFirstLeaf(
    rer: LW.RegExpRecord, qm: AR.QMap, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
    A0: nat, lk: AReg.Regs, body: R.regex, bodycode: RB.code, endl: nat, ngroups: nat,
    g2: nat, ncap: int, nlook: int, nquant: int)
    requires PSM.StaticOkNestedRE(qm, body, bodycode, endl)
    requires EL.NegBehindLookFreeRE(body)
    requires PSM.SizesOkRE(body, ncap, nlook, nquant)
    requires qm.ov == ov && !rer.ignoreCase && !rer.multiline
    requires bodycode == CP.compile_to_bytecode(body)
    requires T.TransWf(body)
    // A0's table row: VBody == body, cdns row present, look type is a lookAHEAD.
    requires body == M.VBody(crv, A0 as int)
    requires 0 <= (A0 as int) < |crv.f_look_types| && crv.f_look_types[A0 as int].Lookahead?
    requires 0 <= (A0 as int) < |crv.f_look_cdns|
    requires M.MatchedPosLA(crv, lk, A0 as int)
    requires var cp := AReg.get_cp(lk, A0 as int).value;
             0 <= cp <= |str| && LL.OracleOkSuffix(rer, qm, PIV.InpOfCp(str, cp))
    requires g2 in PIV.CapIds(body) && g2 !in PIV.CapIdsInLooks(body)
    requires var rf := M.FreshBodyMatch(crv, str, A0 as int, lk, ov, ncap, nlook, nquant);
             rf.Some?
             && g2 in PIV.GmOfLive(body, rf.value.capture_regs, rf.value.look_regs, rf.value.quant_regs)
    ensures var lsub := SubFirstLeafAt(rer, crv, str, A0 as int, lk);
            lsub.Some? && g2 in lsub.value
  {
    var l := A0 as int;
    var cp := AReg.get_cp(lk, l).value;                       // MatchedPosLA ==> Some
    var cdns := crv.f_look_cdns[l];
    var inp := PIV.InpOfCp(str, cp);
    var t := LFU.ComputeTr(rer, [LS.Areg(T.Translate(body))], inp, LG.Empty, WP.Forward);
    var Sb := LL.LkBodyGroups(T.Translate(body));

    // (1) FreshBodyMatch(A0, lk) unfolds to the from-FRESH FFindMatch over `bodycode`.
    var rf := M.FreshBodyMatch(crv, str, l, lk, ov, ncap, nlook, nquant);
    var looktype := crv.f_look_types[l];
    assert looktype.Lookahead?;
    assert LidDir(crv, l) == WP.Forward;                      // (L5 F7a)
    assert AI.capture_direction(looktype) == LAnc.Forward;
    assert CP.capture_regex(looktype, body) == body;
    assert M.VBody(crv, l) == body;
    var ctxc := AI.cp_context(cp, str, LAnc.Forward);
    var rfExplicit := AI.FFindMatch(bodycode, str,
                                    AI.FInitState(bodycode, cp, AReg.init_regs(ncap), AReg.init_regs(nlook),
                                                  AReg.init_regs(nquant), 0, ctxc), ov, LAnc.Forward, cdns).0;
    assert rf == rfExplicit;

    // (2) ReplayCapIsBodyLeafNested (from-fresh actual regs so `ra == rf`).
    var cap0 := AReg.init_regs(ncap);
    var lk0 := AReg.init_regs(nlook);
    var qt0 := AReg.init_regs(nquant);
    RL.AInitLaws(ncap); RL.AInitLaws(nquant);
    assert CM.RegsAgreeInside(cap0, AReg.init_regs(ncap), PIV.CaptureRegs(body));
    var bestT := M.ReplayCapIsBodyLeafNested(rer, qm, body, bodycode, endl, ngroups, str, cp,
                                             cap0, lk0, qt0, ov, cdns, ncap, nlook, nquant);
    var ra := AI.FFindMatch(bodycode, str,
                            AI.FInitState(bodycode, cp, cap0, lk0, qt0, 0, ctxc), ov, LAnc.Forward, cdns).0;
    assert ra == rfExplicit == rf;                            // same expression from fresh
    assert ra.Some?;                                          // rf.Some?

    // (3) bestT.value.1 == GmOfLive(body, fresh) carries g2; g2 is DIRECT so it
    //     survives into the spec first leaf FirstLeaf(t).value.1.
    assert bestT.Some? && LT.FirstLeaf(t, inp).Some?;
    assert bestT.value.1 == PIV.GmOfLive(body, rf.value.capture_regs, rf.value.look_regs, rf.value.quant_regs);
    assert g2 in bestT.value.1;
    M.LkBodyGroupsEqCapIdsInLooks(body);                     // Sb == CapIdsInLooks(body)
    assert g2 !in Sb;
    assert LL.GmAgreeOutside(bestT.value.1, LT.FirstLeaf(t, inp).value.1, Sb);
    assert g2 in LT.FirstLeaf(t, inp).value.1;

    // (4) FirstLeaf(t).value.1 IS SubFirstLeafAt(A0, lk).value (definitional).
    assert LT.FirstLeaf(t, inp) == LT.TreeRes(t, LG.Empty, inp, WP.Forward);
    var lsub := SubFirstLeafAt(rer, crv, str, l, lk);
    assert lsub.Some? && lsub.value == LT.FirstLeaf(t, inp).value.1;
  }

  /** (FORWARD direct bridge — the REVERSE of `FreshBodyDirectInSubFirstLeaf`,
      with VALUES) A DIRECTLY-owned capture `g2` present in a top lookAHEAD `A0`'s
      sub-first-leaf `SubFirstLeafAt(A0, lk)` is LIVE in the FRESH body match at
      the same recorded position, with the SAME value. Same keystone chain
      (`M.ReplayCapIsBodyLeafNested` + `GmAgreeOutside` at a direct `g2`), read in
      the spec-to-engine direction. Feeds the forward membership recursion's BASE. */
  lemma SubFirstLeafDirectInFresh(
    rer: LW.RegExpRecord, qm: AR.QMap, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
    A0: nat, lk: AReg.Regs, body: R.regex, bodycode: RB.code, endl: nat, ngroups: nat,
    g2: nat, ncap: int, nlook: int, nquant: int)
    requires PSM.StaticOkNestedRE(qm, body, bodycode, endl)
    requires EL.NegBehindLookFreeRE(body)
    requires PSM.SizesOkRE(body, ncap, nlook, nquant)
    requires qm.ov == ov && !rer.ignoreCase && !rer.multiline
    requires bodycode == CP.compile_to_bytecode(body)
    requires T.TransWf(body)
    requires body == M.VBody(crv, A0 as int)
    requires 0 <= (A0 as int) < |crv.f_look_types| && crv.f_look_types[A0 as int].Lookahead?
    requires 0 <= (A0 as int) < |crv.f_look_cdns|
    requires M.MatchedPosLA(crv, lk, A0 as int)
    requires var cp := AReg.get_cp(lk, A0 as int).value;
             0 <= cp <= |str| && LL.OracleOkSuffix(rer, qm, PIV.InpOfCp(str, cp))
    requires g2 in PIV.CapIds(body) && g2 !in PIV.CapIdsInLooks(body)
    requires M.FreshBodyMatch(crv, str, A0 as int, lk, ov, ncap, nlook, nquant).Some?
    requires var lsub := SubFirstLeafAt(rer, crv, str, A0 as int, lk);
             lsub.Some? && g2 in lsub.value
    ensures var rf := M.FreshBodyMatch(crv, str, A0 as int, lk, ov, ncap, nlook, nquant);
            g2 in PIV.GmOfLive(body, rf.value.capture_regs, rf.value.look_regs, rf.value.quant_regs)
            && SubFirstLeafAt(rer, crv, str, A0 as int, lk).value[g2]
               == PIV.GmOfLive(body, rf.value.capture_regs, rf.value.look_regs, rf.value.quant_regs)[g2]
  {
    var l := A0 as int;
    var cp := AReg.get_cp(lk, l).value;
    var cdns := crv.f_look_cdns[l];
    var inp := PIV.InpOfCp(str, cp);
    var t := LFU.ComputeTr(rer, [LS.Areg(T.Translate(body))], inp, LG.Empty, WP.Forward);
    var Sb := LL.LkBodyGroups(T.Translate(body));

    // (1) FreshBodyMatch unfolds to the from-FRESH FFindMatch over `bodycode`.
    var rf := M.FreshBodyMatch(crv, str, l, lk, ov, ncap, nlook, nquant);
    var looktype := crv.f_look_types[l];
    assert looktype.Lookahead?;
    assert LidDir(crv, l) == WP.Forward;                      // (L5 F7a)
    assert AI.capture_direction(looktype) == LAnc.Forward;
    assert CP.capture_regex(looktype, body) == body;
    assert M.VBody(crv, l) == body;
    var ctxc := AI.cp_context(cp, str, LAnc.Forward);
    var rfExplicit := AI.FFindMatch(bodycode, str,
                                    AI.FInitState(bodycode, cp, AReg.init_regs(ncap), AReg.init_regs(nlook),
                                                  AReg.init_regs(nquant), 0, ctxc), ov, LAnc.Forward, cdns).0;
    assert rf == rfExplicit;

    // (2) ReplayCapIsBodyLeafNested at fresh actual regs (ra == rf).
    var cap0 := AReg.init_regs(ncap);
    var lk0 := AReg.init_regs(nlook);
    var qt0 := AReg.init_regs(nquant);
    RL.AInitLaws(ncap); RL.AInitLaws(nquant);
    assert CM.RegsAgreeInside(cap0, AReg.init_regs(ncap), PIV.CaptureRegs(body));
    var bestT := M.ReplayCapIsBodyLeafNested(rer, qm, body, bodycode, endl, ngroups, str, cp,
                                             cap0, lk0, qt0, ov, cdns, ncap, nlook, nquant);
    var ra := AI.FFindMatch(bodycode, str,
                            AI.FInitState(bodycode, cp, cap0, lk0, qt0, 0, ctxc), ov, LAnc.Forward, cdns).0;
    assert ra == rfExplicit == rf;
    assert ra.Some?;

    // (3) SubFirstLeafAt unfolds to FirstLeaf(t); g2 is DIRECT, so it transports
    //     into bestT.1 == GmOfLive(body, rf) with the SAME value.
    assert LT.FirstLeaf(t, inp) == LT.TreeRes(t, LG.Empty, inp, WP.Forward);
    var lsub := SubFirstLeafAt(rer, crv, str, l, lk);
    assert bestT.Some? && LT.FirstLeaf(t, inp).Some?;
    assert lsub.Some? && lsub.value == LT.FirstLeaf(t, inp).value.1;
    assert bestT.value.1 == PIV.GmOfLive(body, rf.value.capture_regs, rf.value.look_regs, rf.value.quant_regs);
    M.LkBodyGroupsEqCapIdsInLooks(body);
    assert g2 !in Sb;
    assert LL.GmAgreeOutside(bestT.value.1, LT.FirstLeaf(t, inp).value.1, Sb);
    assert g2 in LT.FirstLeaf(t, inp).value.1;
    assert g2 in bestT.value.1 && bestT.value.1[g2] == LT.FirstLeaf(t, inp).value.1[g2];
  }

  /** For a LOOKBEHIND lid, `SubFirstLeafAt` unfolds (`LidDir == Backward`) to
      the explicit backward leaf `FG.BackLeafAt(body, cp)` at the recorded cp. */
  lemma SubFirstLeafAtIsBackLeaf(rer: LW.RegExpRecord, crv: CP.FCompiled, str: string, l: int,
                                 lk: AReg.Regs, body: R.regex)
    requires body == M.VBody(crv, l) && T.TransWf(body)
    requires 0 <= l < |crv.f_look_types| && crv.f_look_types[l].Lookbehind?
    requires AReg.get_cp(lk, l).Some? && 0 <= AReg.get_cp(lk, l).value <= |str|
    ensures SubFirstLeafAt(rer, crv, str, l, lk)
         == FG.BackLeafAt(rer, body, str, AReg.get_cp(lk, l).value)
  {
    assert LidDir(crv, l) == WP.Backward;
  }

  /** LB twin of `FreshBodyDirectInSubFirstLeaf`: a DIRECT group of the body live
      in the fresh BACKWARD body match lands in `SubFirstLeafAt`. */
  lemma FreshBodyDirectInSubFirstLeafLB(
    rer: LW.RegExpRecord, qm: AR.QMap, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
    A0: nat, lk: AReg.Regs, body: R.regex, g2: nat, ncap: int, nlook: int, nquant: int)
    requires T.TransWf(body) && NR.NestedFragmentRE(body) && EL.NegBehindLookFreeRE(body)
    requires NR.NoNulledPlusRE(body)   // §2.5b interim: all stamps false
    requires FST.LBOnlyLooksRE(body)
    requires PIV.CapUnique(body) && PIV.QuantUnique(body) && LTB.LookUnique(body)
    requires PSM.SizesOkRE(body, ncap, nlook, nquant)
    requires !rer.ignoreCase && !rer.multiline
    requires |ov| == |str| + 1
    requires qm.ov == ov && AR.LmapOk(body, qm) && OE.OracleColsOk(rer, qm, str)
    requires body == M.VBody(crv, A0 as int)
    requires 0 <= (A0 as int) < |crv.f_look_types| && crv.f_look_types[A0 as int].Lookbehind?
    requires 0 <= (A0 as int) < |crv.f_look_cdns|
    requires M.MatchedPosLA(crv, lk, A0 as int)
    requires var cp := AReg.get_cp(lk, A0 as int).value; 0 <= cp <= |str|
    requires g2 in PIV.CapIds(body) && g2 !in PIV.CapIdsInLooks(body)
    requires var rf := M.FreshBodyMatch(crv, str, A0 as int, lk, ov, ncap, nlook, nquant);
             rf.Some?
             && g2 in PIV.GmOfLive(body, rf.value.capture_regs, rf.value.look_regs, rf.value.quant_regs)
    ensures var lsub := SubFirstLeafAt(rer, crv, str, A0 as int, lk);
            lsub.Some? && g2 in lsub.value
  {
    FG.LBOnlyEquiv(body); EL.NegLooksFromLBOnly(body);   // §2.2: the flip route keeps NR.NegLooksLookFreeRE
    FG.FreshBodyDirectInBackLeaf(rer, qm, crv, str, ov, A0, lk, body, g2, ncap, nlook, nquant);
    SubFirstLeafAtIsBackLeaf(rer, crv, str, A0 as int, lk, body);
  }

  /** LB twin of `SubFirstLeafDirectInFresh`: a DIRECT group present in
      `SubFirstLeafAt` is live in the fresh BACKWARD body match, with the leaf's
      ordered range = `SwapRange` of the backward match's reversed read. */
  lemma SubFirstLeafDirectInFreshLB(
    rer: LW.RegExpRecord, qm: AR.QMap, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
    A0: nat, lk: AReg.Regs, body: R.regex, g2: nat, ncap: int, nlook: int, nquant: int)
    requires T.TransWf(body) && NR.NestedFragmentRE(body) && EL.NegBehindLookFreeRE(body)
    requires NR.NoNulledPlusRE(body)   // §2.5b interim: all stamps false
    requires FST.LBOnlyLooksRE(body)
    requires PIV.CapUnique(body) && PIV.QuantUnique(body) && LTB.LookUnique(body)
    requires PSM.SizesOkRE(body, ncap, nlook, nquant)
    requires !rer.ignoreCase && !rer.multiline
    requires |ov| == |str| + 1
    requires qm.ov == ov && AR.LmapOk(body, qm) && OE.OracleColsOk(rer, qm, str)
    requires body == M.VBody(crv, A0 as int)
    requires 0 <= (A0 as int) < |crv.f_look_types| && crv.f_look_types[A0 as int].Lookbehind?
    requires 0 <= (A0 as int) < |crv.f_look_cdns|
    requires M.MatchedPosLA(crv, lk, A0 as int)
    requires var cp := AReg.get_cp(lk, A0 as int).value; 0 <= cp <= |str|
    requires g2 in PIV.CapIds(body) && g2 !in PIV.CapIdsInLooks(body)
    requires M.FreshBodyMatch(crv, str, A0 as int, lk, ov, ncap, nlook, nquant).Some?
    requires var lsub := SubFirstLeafAt(rer, crv, str, A0 as int, lk);
             lsub.Some? && g2 in lsub.value
    ensures var rf := M.FreshBodyMatch(crv, str, A0 as int, lk, ov, ncap, nlook, nquant);
            var gmb := PIV.GmOfLive(body, rf.value.capture_regs, rf.value.look_regs, rf.value.quant_regs);
            g2 in gmb
            && SubFirstLeafAt(rer, crv, str, A0 as int, lk).value[g2] == LBV.SwapRange(gmb[g2])
  {
    FG.LBOnlyEquiv(body); EL.NegLooksFromLBOnly(body);   // §2.2: the flip route keeps NR.NegLooksLookFreeRE
    SubFirstLeafAtIsBackLeaf(rer, crv, str, A0 as int, lk, body);
    FG.BackLeafDirectInFresh(rer, qm, crv, str, ov, A0, lk, body, g2, ncap, nlook, nquant);
  }

  /** (R2 — the crossing DISCHARGES the deep gate-pass requires) Ties rung 1 to the
      deep gate-pass: at a positive-lookAHEAD gate crossing (`l`'s cp just written
      as `cp`, body groups cleared coming in), the DEEP carrier's crossing
      obligation — every group of `l`'s sub-first-leaf `SubFirstLeafAt(l, th')` is
      in the new leaf `gm2 == LkResult` — holds, straight from
      `LkResultLandsSubFirstLeaf`. `SubFirstLeafAt(l, th')` unfolds to exactly the
      spec-tree first leaf at the just-written cp (position tie DEFINITIONAL), and
      `M.TranslateDefGroupsEqCapIds` matches `CapIds(body(l)) == DefGroups(r1)`. So
      `LookNestBackTGatePassTopDeep`'s crossing `requires` is NOT vacuous — it is
      produced at every real crossing, exactly as the direct carrier's is at
      LiftSim:21522-21605. This is the concrete seam that would slot the deep
      carrier into the `LiftInvRec` step. */
  lemma DeepGateReqFromCrossing(
    rer: LW.RegExpRecord, re: R.regex, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
    S: set<LG.GroupId>, gm: LG.GroupMap, gm2: LG.GroupMap, lk: L.Lookaround, r1: L.Regex,
    tlk: LT.Tree, th': AI.Thread, l: int, cp: nat, body: R.regex, ncap: int, nlook: int, nquant: int)
    requires cp <= |str|
    requires l >= 0 && (l as nat) in LTB.LookIds(re)
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
    ensures var lsub := SubFirstLeafAt(rer, crv, str, l, th'.look_regs);
            lsub.Some? ==>
              forall g: LG.GroupId ::
                g in S && g in PIV.CapIds(NI.LookBodyOfRE(re, l as nat)) ==>
                  (g in lsub.value ==> g in gm2 && gm2[g] == lsub.value[g])
                  && (g in gm2 ==> g in lsub.value)
    // the off-body frame: the crossing leaves every other region verbatim.
    ensures LL.GmAgreeOutside(gm2, gm, PIV.CapIds(NI.LookBodyOfRE(re, l as nat)))
  {
    var inp := PIV.InpOfCp(str, cp);
    var Sr1 := set g | g in L.DefGroups(r1);
    // (1) SubFirstLeafAt(l, th') unfolds to the spec first leaf of `tlk` at `cp`.
    assert SubFirstLeafAt(rer, crv, str, l, th'.look_regs)
        == (var res := LT.TreeRes(tlk, LG.Empty, inp, L.LkDir(lk));
            if res.Some? then Some(res.value.1) else None)
    by {
      assert M.VBody(crv, l) == body;
      assert T.Translate(body) == r1;
      assert LidDir(crv, l) == L.LkDir(lk);
    }
    // (2) rung 1: the from-Empty first leaf and gm2 agree BOTH ways on Sr1.
    LkResultLandsSubFirstLeaf(rer, lk, r1, inp, tlk, gm, Sr1);
    // (3) CapIds(body(l)) == DefGroups(r1) == Sr1.
    M.TranslateDefGroupsEqCapIds(body);
    assert PIV.CapIds(NI.LookBodyOfRE(re, l as nat)) == Sr1;
    // (4) off-body frame from the LkResult confinement.
    LkResultAgreeOutsideNested(rer, lk, r1, inp, tlk, gm);
    assert LL.GmAgreeOutside(gm2, gm, Sr1);
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

  // NOTE on CheckNullable / Fail / NegCheckOracle / WriteOracle: the L3a MAIN
  // code should pin each as either absent (WriteOracle — NR.NoWriteInstrRE;
  // likely CheckNullable under NonNullable plus-fragment bodies) or
  // tree-trivial (Fail → Mismatch; NegCheckOracle → the negative gate, whose
  // bodies are capture-free so B's merge is value-empty). FILL: prove the
  // absence from the code shape (NI.CodeShapeAt) where possible instead of an
  // inversion lemma; otherwise mirror TtLkAtCheckOracle.

  // ---- (G) GateAheadClear preservation bricks --------------------------------

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

  lemma TopLkDefsListActsCons(x: LS.Action, cont: LS.Actions)
    ensures TopLkDefsListActs([x] + cont)
         == (if x.Areg? then TopLkDefsList(x.r) else []) + TopLkDefsListActs(cont)
  { assert ([x] + cont)[0] == x && ([x] + cont)[1..] == cont; }

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
      TopLkDefsListSubDefGroups(r1);
      forall i, j | 0 <= i < |[id]| && 0 <= j < |TopLkDefsList(r1)|
        ensures [id][i] != TopLkDefsList(r1)[j]
      {
        if [id][i] == TopLkDefsList(r1)[j] {
          assert id in TopLkDefsList(r1);
          assert id in L.DefGroups(r1);
          assert id in (set gx | gx in [id]) * (set gx | gx in L.DefGroups(r1));
        }
      }
      M.NoDupFromDisjoint([id], TopLkDefsList(r1));
      assert TopLkDefsList(r) == [id] + TopLkDefsList(r1);
    case Quantified(_, _, _, _) =>
    case Epsilon =>
    case Character(_) =>
    case AnchorR(_) =>
    case Backreference(_) =>
  }

  // ---- THE (C1,C2,C3) WALK-DEFS CARRIER (2026-08-07 session 5) ---------------
  // Replaces `NoDupSeq(AllDefsActs(acts))` in `WalkPairLk`/`TtLk`'s actions
  // disjunct — which is FALSE after any quantifier unfold (`[Areg r1, ...,
  // Areg(Quantified(..,r1))]` duplicates `DefGroups(r1)`, so the old carrier
  // made the invariant vacuous for grouped quantifiers). C1 is the CheckOracle
  // merge consumer (pending-vs-merged disjointness via `RegexTopGateSubTopLk`);
  // C2 the per-action structural NoDup; C3 the rightward quantifier freshness
  // that makes the UNFOLD self-maintaining: the unfolding `Quantified`'s OWN C3
  // clause is exactly the freshness of its body against the tail's top-level
  // looks, and `QuantsRightClearFromNoDup` re-establishes C3 for the copy.

  ghost function TopLkSetActs(acts: LS.Actions): set<LG.GroupId> {
    set g | g in TopLkDefsListActs(acts)
  }

  /** C3, per-list: each action against the top-level look groups to its right. */
  ghost predicate QuantsClearActs(acts: LS.Actions) {
    forall i | 0 <= i < |acts| && acts[i].Areg? ::
      QuantsRightClear(acts[i].r, TopLkSetActs(acts[i + 1..]))
  }

  /** C3 from structural NoDup + body-freshness — the unfold's re-establishment
      workhorse: a dup-free-defs regex whose groups avoid `R` is
      `QuantsRightClear` at `R`. */
  lemma QuantsRightClearFromNoDup(r: L.Regex, R: set<LG.GroupId>)
    requires M.NoDupSeq(L.DefGroups(r))
    requires forall g :: g in L.DefGroups(r) ==> g !in R
    ensures QuantsRightClear(r, R)
    decreases r
  {
    match r
    case Sequence(a, b) =>
      assert L.DefGroups(r) == L.DefGroups(a) + L.DefGroups(b);
      M.NoDupConcat(L.DefGroups(a), L.DefGroups(b));
      TopLkDefsListSubDefGroups(b);
      var Rb := (set g | g in TopLkDefsList(b)) + R;
      forall g | g in L.DefGroups(a) ensures g !in Rb {
        assert g in L.DefGroups(r);
        if g in TopLkDefsList(b) {
          assert g in L.DefGroups(b);
          assert g in (set gx | gx in L.DefGroups(a)) * (set gx | gx in L.DefGroups(b));
        }
      }
      QuantsRightClearFromNoDup(a, Rb);
      forall g | g in L.DefGroups(b) ensures g !in R { assert g in L.DefGroups(r); }
      QuantsRightClearFromNoDup(b, R);
    case Disjunction(a, b) =>
      assert L.DefGroups(r) == L.DefGroups(a) + L.DefGroups(b);
      M.NoDupConcat(L.DefGroups(a), L.DefGroups(b));
      forall g | g in L.DefGroups(a) ensures g !in R { assert g in L.DefGroups(r); }
      QuantsRightClearFromNoDup(a, R);
      forall g | g in L.DefGroups(b) ensures g !in R { assert g in L.DefGroups(r); }
      QuantsRightClearFromNoDup(b, R);
    case Group(id, rb) =>
      assert L.DefGroups(r) == [id] + L.DefGroups(rb);
      M.NoDupConcat([id], L.DefGroups(rb));
      forall g | g in L.DefGroups(rb) ensures g !in R { assert g in L.DefGroups(r); }
      QuantsRightClearFromNoDup(rb, R);
    case Quantified(_, _, _, r1) =>
      assert L.DefGroups(r) == L.DefGroups(r1);
    case _ =>
  }

  /** A gate pending in a chosen `Disjunction` arm's list is pending in the
      folded list (the arm folds into the `Disjunction` top-gate; tail shared). */
  lemma GatePendingDisjBack(acts: LS.Actions, r1: L.Regex, r2: L.Regex, arm: L.Regex,
                            lk: L.Lookaround, rr: L.Regex)
    requires |acts| > 0 && acts[0] == LS.Areg(L.Disjunction(r1, r2))
    requires arm == r1 || arm == r2
    requires GatePending([LS.Areg(arm)] + acts[1..], lk, rr)
    ensures GatePending(acts, lk, rr)
  {
    var na := [LS.Areg(arm)] + acts[1..];
    var i :| 0 <= i < |na| && na[i].Areg? && RegexTopGate(na[i].r, lk, rr);
    if i == 0 {
      assert RegexTopGate(L.Disjunction(r1, r2), lk, rr);
      assert acts[0].Areg? && RegexTopGate(acts[0].r, lk, rr);
    } else {
      assert na[i] == acts[1..][i - 1] == acts[i];
      assert acts[i].Areg? && RegexTopGate(acts[i].r, lk, rr);
    }
  }

  /** `GateAheadClear` across a `Disjunction` arm choice. */
  lemma GateAheadClearDisjArm(acts: LS.Actions, r1: L.Regex, r2: L.Regex, arm: L.Regex,
                              gmt: LG.GroupMap)
    requires |acts| > 0 && acts[0] == LS.Areg(L.Disjunction(r1, r2)) && GateAheadClear(acts, gmt)
    requires arm == r1 || arm == r2
    ensures GateAheadClear([LS.Areg(arm)] + acts[1..], gmt)
  {
    forall lk: L.Lookaround, rr: L.Regex | GatePending([LS.Areg(arm)] + acts[1..], lk, rr)
      ensures forall g :: g in L.DefGroups(rr) ==> g !in gmt
    { GatePendingDisjBack(acts, r1, r2, arm, lk, rr); }
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

  // ==========================================================================
  // (R2 — DEEP CARRIER wiring) rep-predicate twins + register-inert / SetQuant
  // step twins for the DEEP carrier `LookNestBackTTopDeep`. Exact clones of the
  // `LookNestBackRepCTop`/`LookNestBackTRegSameTop`/`LookNestBackTSetQuantNestedTop`
  // family with the DIRECT landed set `GmOfLive(body(lid), FreshBodyMatch(lid))`
  // replaced by the DEEP `SubFirstLeafAt(lid)`. `SubFirstLeafAt` /
  // `MatchedPosLA` / `LookPathDom` read only `th.look_regs`/`th.quant_regs` —
  // EXACTLY as `FreshBodyMatch`/the direct carrier do — so every preservation
  // argument ports verbatim (`gm` congruence via `get_cp`).
  // ==========================================================================

  ghost predicate LookNestBackRepCTopDeep(rer: LW.RegExpRecord, re: R.regex, crv: CP.FCompiled,
                                          str: string, ov: LOr.OracleView,
                                          S: set<LG.GroupId>, tl: seq<(LT.Tree, LG.GroupMap)>,
                                          vl: seq<AI.Thread>, ncap: int, nlook: int, nquant: int) {
    |tl| == |vl|
    && forall i | 0 <= i < |tl| ::
      LookNestBackTTopDeep(rer, re, crv, str, ov, S, tl[i].1, vl[i], ncap, nlook, nquant)
  }

  ghost predicate LookNestBackRepBTopDeep(rer: LW.RegExpRecord, re: R.regex, crv: CP.FCompiled,
                                          str: string, ov: LOr.OracleView,
                                          S: set<LG.GroupId>, tl: seq<(LT.Tree, LG.GroupMap)>,
                                          bl: seq<(AI.Thread, RC.char_expectation)>,
                                          ncap: int, nlook: int, nquant: int) {
    |tl| == |bl|
    && forall i | 0 <= i < |tl| ::
      LookNestBackTTopDeep(rer, re, crv, str, ov, S, tl[i].1, bl[i].0, ncap, nlook, nquant)
  }

  /** DEEP twin of `LookNestBackTRegSameTop` — register-inert step. Both banks
      untouched, `gmt` grows; the deep carrier reads only `th.look_regs`/
      `th.quant_regs` (via `SubFirstLeafAt`/`MatchedPosLA`/`LookPathDom`), so it is
      preserved for free (as the direct twin). */
  lemma LookNestBackTRegSameTopDeep(rer: LW.RegExpRecord, re: R.regex, crv: CP.FCompiled, str: string,
                                    ov: LOr.OracleView, S: set<LG.GroupId>, gmt: LG.GroupMap, gmt': LG.GroupMap,
                                    th: AI.Thread, th': AI.Thread,
                                    ncap: int, nlook: int, nquant: int)
    requires LookNestBackTTopDeep(rer, re, crv, str, ov, S, gmt, th, ncap, nlook, nquant)
    requires th'.look_regs == th.look_regs && th'.quant_regs == th.quant_regs
    // REGION FRAME: inside-S entries survive verbatim (the step touches only
    // outside-S groups on the gm side).
    requires forall g: LG.GroupId :: g in S ==>
                                       (g in gmt <==> g in gmt') && (g in gmt ==> gmt'[g] == gmt[g])
    ensures LookNestBackTTopDeep(rer, re, crv, str, ov, S, gmt', th', ncap, nlook, nquant)
  {
  }

  /** DEEP twin of `LookNestBackTSetQuantNestedTop` — an off-path SetQuant clock
      re-stamp. The `LookPathDom`-break / off-path-congruence argument is IDENTICAL
      (it depends only on the look/quant clocks, not on the landed set); the landed
      set `SubFirstLeafAt(lid, th'.look_regs) == SubFirstLeafAt(lid, th.look_regs)`
      since `th'.look_regs == th.look_regs`, and `g in CapIds(body(lid))` is disjoint
      from `CapIds(QidBody(re, qn))` by `LookBodyQidBodyDisjoint`, so the survivor
      `g in gmt` transports to `g in gmt'`. */
  lemma LookNestBackTSetQuantNestedTopDeep(rer: LW.RegExpRecord, re: R.regex, crv: CP.FCompiled,
                                           str: string, ov: LOr.OracleView,
                                           S: set<LG.GroupId>, gmt: LG.GroupMap, gmt': LG.GroupMap,
                                           th: AI.Thread, th': AI.Thread, qn: nat,
                                           ncap: int, nlook: int, nquant: int)
    requires NR.NestedFragmentRE(re) && PIV.CapUnique(re) && PIV.QuantUnique(re)
    requires LTB.LookUnique(re)
    requires LookNestBackTTopDeep(rer, re, crv, str, ov, S, gmt, th, ncap, nlook, nquant)
    requires qn in PIV.QuantIds(re) && qn in PIV.QuantIdsOutsideLooks(re)
    requires th'.look_regs == th.look_regs
    requires forall j: int :: j != qn as int ==>
                                AI.get_idx(th'.quant_regs.a_clk, j) == AI.get_idx(th.quant_regs.a_clk, j)
    requires forall j: int ::
               AI.get_idx(th.look_regs.a_clk, j) < AI.get_idx(th'.quant_regs.a_clk, qn as int)
    // REGION FRAME off the reset quant's body: those regions survive verbatim.
    requires forall g: LG.GroupId :: g in S && g !in PIV.CapIds(PIV.QidBody(re, qn)) ==>
                                       (g in gmt <==> g in gmt') && (g in gmt ==> gmt'[g] == gmt[g])
    ensures LookNestBackTTopDeep(rer, re, crv, str, ov, S, gmt', th', ncap, nlook, nquant)
  {
    NI.TopLookIdsIn(re);
    forall lid: nat | lid in NI.TopLookIds(re)
                      && M.MatchedPosLA(crv, th'.look_regs, lid as int)
                      && NI.LookPathDom(re, AI.get_idx(th'.look_regs.a_clk, lid as int), th'.quant_regs.a_clk, lid)
      ensures var lsub := SubFirstLeafAt(rer, crv, str, lid as int, th'.look_regs);
              lsub.Some? ==>
                forall g: LG.GroupId ::
                  g in S && g in PIV.CapIds(NI.LookBodyOfRE(re, lid)) ==>
                    (g in lsub.value ==> g in gmt' && gmt'[g] == lsub.value[g])
                    && (g in gmt' ==> g in lsub.value)
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
        var lsub := SubFirstLeafAt(rer, crv, str, lid as int, th'.look_regs);
        forall g: LG.GroupId |
          lsub.Some? && g in S && g in PIV.CapIds(NI.LookBodyOfRE(re, lid))
          ensures (g in lsub.value ==> g in gmt' && gmt'[g] == lsub.value[g])
                  && (g in gmt' ==> g in lsub.value)
        {
          assert g !in PIV.CapIds(PIV.QidBody(re, qn)) by {
            if g in PIV.CapIds(PIV.QidBody(re, qn)) {
              assert g in PIV.CapIds(NI.LookBodyOfRE(re, lid)) * PIV.CapIds(PIV.QidBody(re, qn));
            }
          }
        }
      }
    }
  }

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

  // ==========================================================================
  // (E4) THE ENDPOINT ASSEMBLY — from `BestTieLk`'s four tie directions and
  // the genuine-start engine facts, the winning leaf's gm IS the live
  // denotation of the FLookLoop-reconstructed registers, and the synthetic
  // thread carrying them is well-formed. The last lemma before the theorem.
  // ==========================================================================

  // ==========================================================================
  // (E4 NESTED) THE ENDPOINT ASSEMBLY under look NESTING. Consumes the nested
  // best-tie `BestTieLkNested` (which DROPS `GmtTieInside`) and closes the
  // whole-regex value theorem `leaf.1 == NormGm(GmOfLive(re, res.0, res.1, res.2))`.
  //
  // KEY RETARGET vs. the depth-1 endpoint: the value reads the RECONSTRUCTED look
  // bank `res.1` (NOT `thread.look_regs`) — under nesting `FLookLoop` writes the
  // inner-look banks, so `res.1 != thread.look_regs` inside `LookIdSet(re)`. On
  // OUTSIDE-`S` groups the two coincide (`PIV.GmOfLiveLookIndepNested`), which is
  // how the outside half still rides the winning-thread's `GmtTieOutside`.
  //
  // WHAT IS DERIVED GREEN HERE: the entire OUTSIDE-`S` half —
  //   BestTieLkNested ⟹ GmtTieOutside(re, thread, leafgm, S)
  //     --[GmOfLiveLookIndepNested: thread.look_regs ~ res.1 outside S]-->
  //   leafgm ~ GmOfLive(re, thread.cap, res.1, thread.quant) outside S
  //     --[OutsideLookValueBridgeNested: cap/quant frame res.0/res.2 ~ thread]-->
  //   leafgm ~ GmOfLive(re, res.0, res.1, res.2) outside S
  //   --[L3aValueBridgeNested]--> leaf.1 == NormGm(GmOfLive(re, res.0, res.1, res.2)).
  //
  // WHAT REMAINS (TODO C4 — the genuinely-novel INSIDE glue + nested FLookLoop
  // plumbing), stated as the residual `requires`:
  //  (a) recon_outer cap frame + quant frame + synthetic-`res` well-formedness —
  //      the nested FLookLoop scaffolding (`M.FLookLoopFullCoversFromTables`
  //      supplies recon_outer/recon_inner; the quant frame + `CapRegWf(res.0)` +
  //      `QuantRegsFinal` need the nested `FLookLoopQuantFrame`/`FLookLoopValueLiftFull`
  //      table-side-condition preamble — mechanical but large).
  //  (b) INSIDE-`S` FORWARD value: `leaf.1[g] == NormRange(GmOfLive(re,res0,res1,res2)[g])`.
  //      The 3-component chain (`FLookLoopFullCoversFromTables` -> `res.0` carries `g`
  //      at its innermost owner's fresh value; `OuterLeafInnerGEqOwnerBody` -> `leaf[g]`
  //      == owner-body spec sub-result; `LkReplayMatchesSpecNested` -> owner-fresh ==
  //      owner-sub-result). This chain needs (i) the SPEC tree `t` with `leaf ==
  //      FirstLeaf(t, inp)` threaded in — `BestTieLkNested` does NOT carry it (unlike
  //      the depth-1 `GmtTieInside`); and (ii) nested `LookPath*` ownership lemmas
  //      (`LookPathCompose/Decompose/PresentAgree`), which currently exist only for
  //      `LookBehindFragmentRE` in `NestInv.dfy`.
  //  (c) INSIDE-`S` REVERSE: `g in GmOfLive(re,res0,res1,res2) ==> g in leaf.1`, fed
  //      by the KEPT carrier `LookNestBackT` (in `BestTieLkNested`) — but the depth-1
  //      reverse block routes through `LookPathDecompose`/`LookPathDomIntro`/
  //      `LookFreeNoLookIdsN`, all `LookBehindFragmentRE`-gated; nested twins pending.
  // ==========================================================================

  /** (§2.5b F-c) No action stack is represented at the nulled-exit stamp: it is
      reached only from the CIN head fork's skip arm, and every layout arm opens
      with a different instruction (a forced copy's clock-mark writes `false`,
      the CIN head is a Fork). */
  lemma ActionsRepNotAtTrueStamp(rer: LW.RegExpRecord, qm: AR.QMap, acts: LS.Actions, code: RB.code,
                                 pc: nat, q: int)
    requires AR.ActionsRepL(rer, qm, acts, code, pc)
    requires NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(q, true))
    ensures false
    decreases ATR.MsizeA(acts)
  {
    hide NUL.NonNullableL, NUL.CINullableL, NUL.NoNulledPlusL, AR.NfaRepCinL, AR.NfaRepStarCinL;
    if |acts| == 0 {
      // ActionsRepL([]) pins Accept
    } else if exists pcmid: nat :: AR.ActionRepL(rer, qm, acts[0], code, pc, pcmid) && AR.ActionsRepL(rer, qm, acts[1..], code, pcmid) {
      var pcmid: nat :| AR.ActionRepL(rer, qm, acts[0], code, pc, pcmid) && AR.ActionsRepL(rer, qm, acts[1..], code, pcmid);
      assert acts == [acts[0]] + acts[1..];
      var cont := acts[1..];
      match acts[0]
      case Acheck(_) =>   // pins EndLoop / backward Fork
      case Aclose(_) =>   // pins SetRegisterToCP
      case Areg(r0) =>
        match r0
        case Epsilon =>
          assert pcmid == pc;
          assert ATR.MsizeA(cont) < ATR.MsizeA(acts);
          ActionsRepNotAtTrueStamp(rer, qm, cont, code, pc, q);
        case Sequence(r1, r2) =>
          assert AR.NfaRepL(rer, qm, L.Sequence(r1, r2), code, pc, pcmid);
          var e1: nat :| AR.NfaRepL(rer, qm, r1, code, pc, e1) && AR.NfaRepL(rer, qm, r2, code, e1, pcmid);
          var na := [LS.Areg(r1), LS.Areg(r2)] + cont;
          assert na == [LS.Areg(r1)] + ([LS.Areg(r2)] + cont);
          AR.ActionsRepLCons(rer, qm, LS.Areg(r2), cont, code, e1, pcmid);
          AR.ActionsRepLCons(rer, qm, LS.Areg(r1), [LS.Areg(r2)] + cont, code, pc, e1);
          assert LS.ActionsRegexSize(acts) == RegSz(r1) + RegSz(r2) + 1 + LS.ActionsRegexSize(cont);
          assert LS.ActionsRegexSize(na) == RegSz(r1) + RegSz(r2) + LS.ActionsRegexSize(cont);
          assert ATR.MsizeA(na) < ATR.MsizeA(acts);
          ActionsRepNotAtTrueStamp(rer, qm, na, code, pc, q);
        case Quantified(greedy, min, delta, r1) =>
          assert AR.NfaRepL(rer, qm, L.Quantified(greedy, min, delta, r1), code, pc, pcmid);
          if min > 0 {
            if min == 1 && delta.Inf? && greedy && !NUL.NonNullableL(r1) {
              var emC, e1C := AR.NfaRepLCinInv(rer, qm, greedy, min, r1, code, pc, pcmid);
              assert emC == pc;   // the head is the Fork
            } else {
              QuantHeadSQCPin(rer, qm, greedy, min, delta, r1, code, pc, pcmid);   // a `false` clock-mark
            }
          } else if delta == LN.NN(0) {
            var em: nat :| AR.NfaRepMinL(rer, qm, 0, r1, code, pc, em)
                           && AR.NfaRepOptL(rer, qm, 0, greedy, r1, code, em, pcmid);
            NfaRepMinLHeadPin(rer, qm, 0, r1, code, pc, em);
            NfaRepOptLHeadPin(rer, qm, 0, greedy, r1, code, em, pcmid);
            assert pcmid == pc;
            assert ATR.MsizeA(cont) < ATR.MsizeA(acts);
            ActionsRepNotAtTrueStamp(rer, qm, cont, code, pc, q);
          } else {
            QuantHeadPinsForkOrSQC(rer, qm, greedy, min, delta, r1, code, pc, pcmid);
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
                AR.NfaRepLStarLoopViews(rer, qm, greedy, r1, code, pc, pcmid);
                if NUL.NonNullableL(r1) {
                  var em: nat :| NR.GetPcRE(code, pc) == Some(if greedy then RB.Fork(em, pc + 1) else RB.Fork(pc + 1, em));
                } else {
                  var emC, e1C := AR.NfaRepLStarCinInv(rer, qm, r1, code, pc, pcmid);
                }
              }
            case NN(kx) =>
              var em: nat :| AR.NfaRepMinL(rer, qm, 0, r1, code, pc, em)
                             && AR.NfaRepOptL(rer, qm, kx, greedy, r1, code, em, pcmid);
              NfaRepMinLHeadPin(rer, qm, 0, r1, code, pc, em);
              NfaRepOptLHeadPin(rer, qm, kx, greedy, r1, code, em, pcmid);
          }
        case Character(_) =>
        case Disjunction(_, _) =>
        case Group(_, _) =>
        case LookaroundR(_, _) =>
        case AnchorR(_) =>
        case Backreference(_) =>
    } else {
      var pcstart: nat :| NR.GetPcRE(code, pc) == Some(RB.Jmp(pcstart)) && AR.ActionsRepL(rer, qm, acts, code, pcstart);
    }
  }

  lemma TtLkAtAnchorCoreRec(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                            tb: LT.Tree, pc: nat, b: BS.LoopBool, acts: LS.Actions, a: R.anchor)
    requires AR.ActionsRepL(rer, qm, acts, code, pc)
    requires EL.PikeLkActionsRec(acts)
    requires CW.BoolTreeLkX(rer, acts, inp, b, tb)
    requires NR.GetPcRE(code, pc) == Some(RB.AnchorAssertion(a))
    ensures tb.AnchorPass? || tb == LT.Mismatch
    ensures tb.AnchorPass? ==> TtLkRec(rer, qm, code, inp, tb.t, pc + 1, ATR.EaOf(b))
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
        assert CW.BoolTreeLkX(rer, cont, inp, b, tb);
        assert ATR.MsizeA(cont) < ATR.MsizeA(acts);
        TtLkAtAnchorCoreRec(rer, qm, code, inp, tb, pc, b, cont, a);
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
        assert CW.BoolTreeLkX(rer, na, inp, b, tb);
        assert LS.ActionsRegexSize(acts) == RegSz(r1) + RegSz(r2) + 1 + LS.ActionsRegexSize(cont);
        assert LS.ActionsRegexSize(na) == RegSz(r1) + RegSz(r2) + LS.ActionsRegexSize(cont);
        assert ATR.MsizeA(na) < ATR.MsizeA(acts);
        TtLkAtAnchorCoreRec(rer, qm, code, inp, tb, pc, b, na, a);
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
          assert CW.BoolTreeLkX(rer, cont, inp, b, tb);
          assert ATR.MsizeA(cont) < ATR.MsizeA(acts);
          TtLkAtAnchorCoreRec(rer, qm, code, inp, tb, pc, b, cont, a);
        } else {
          assert acts[0] == LS.Areg(L.Quantified(greedy, min, delta, r1));
          assert AR.NfaRepL(rer, qm, L.Quantified(greedy, min, delta, r1), code, pc, pcmid);
          QuantHeadPinsForkOrSQC(rer, qm, greedy, min, delta, r1, code, pc, pcmid);
        }
      case AnchorR(la) =>
        var a2: R.anchor :| NR.GetPcRE(code, pc) == Some(RB.AnchorAssertion(a2)) && T.TrAnchor(a2) == la;
        assert pcmid == pc + 1;
        if LS.AnchorSatisfied(rer, la, inp) {
          assert tb.AnchorPass? && CW.BoolTreeLkX(rer, cont, inp, b, tb.t);
          assert AR.ActionsRepL(rer, qm, cont, code, pc + 1);
          assert TtLkRec(rer, qm, code, inp, tb.t, pc + 1, g);
        } else {
          assert tb == LT.Mismatch;
        }
      case Character(_) =>   // pins Consume — not AnchorAssertion
      case Disjunction(_, _) =>   // pins Fork — not AnchorAssertion
      case Group(_, _) =>   // pins SetRegisterToCP — not AnchorAssertion
      case LookaroundR(_, _) =>   // pins CheckOracle/NegCheckOracle — not AnchorAssertion
      case Backreference(_) =>   // NfaRepL false
  }

  lemma TtLkAtAnchorRec(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                        tb: LT.Tree, pc: nat, ea: bool, a: R.anchor)
    requires TtLkRec(rer, qm, code, inp, tb, pc, ea)
    requires NR.GetPcRE(code, pc) == Some(RB.AnchorAssertion(a))
    ensures tb.AnchorPass? || tb == LT.Mismatch
    ensures tb.AnchorPass? ==> TtLkRec(rer, qm, code, inp, tb.t, pc + 1, ea)
  {
    var acts: LS.Actions, b: BS.LoopBool :|
      AR.ActionsRepL(rer, qm, acts, code, pc)
      && EL.PikeLkActionsRec(acts)
      && ATR.EaOf(b) == ea
      && CW.BoolTreeLkX(rer, acts, inp, b, tb);
    TtLkAtAnchorCoreRec(rer, qm, code, inp, tb, pc, b, acts, a);
  }

  lemma ActionsTreeRepLkRERec(rer: LW.RegExpRecord, qm: AR.QMap, acts: LS.Actions, code: RB.code,
                              pc: nat, inp: LC.Input, b: BS.LoopBool, t: LT.Tree)
    returns (tcan: LT.Tree)
    requires EL.PikeLkActionsRec(acts)
    requires AR.ActionsRepL(rer, qm, acts, code, pc)
    requires WO.WalkOk(acts, code, pc, ATR.EaOf(b))
    requires CW.BoolTreeLkX(rer, acts, inp, b, t)
    ensures TreeRepLkRE(rer, qm, code, inp, tcan, pc, ATR.EaOf(b))
    ensures CE.ProgErase(tcan) == CE.ProgErase(t)
  {
    ATR.ActionsRepLToFuel(rer, qm, acts, code, pc);
    var n: nat :| ATR.ActionsRepFuelL(rer, qm, acts, code, pc, n);
    tcan := ActionsTreeRepLkFRec(rer, qm, acts, code, pc, inp, b, t, n);
  }

  /** (deep carrier, per lid) The `LookNestBackTTopDeep` clause at a top
      lookbehind lid transports back through the flip: `SubFirstLeafAt` of the
      mirrored world is the `MirrorGm` of the backward sub-leaf (F2 at the lid
      body), so key membership is preserved and value equality comes back
      through `MirrorRange` injectivity. */
  lemma {:isolate_assertions} LookNestBackTTopDeepLidFlip(
    rer: LW.RegExpRecord, qm: AR.QMap, body: R.regex, crv: CP.FCompiled, str: string,
    ov: LOr.OracleView, gmt: LG.GroupMap, th: AI.Thread, lid: nat,
    ncap: int, nlook: int, nquant: int)
    requires T.TransWf(body) && NR.NestedFragmentRE(body) && EL.NegBehindLookFreeRE(body)
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
    requires LookNestBackTTopDeep(rer, FST.FXR(body), FG.MirrorTables(crv), LC.Reverse(str),
                                  MIR.MirrorView(ov, |str|), PIV.CapIdsInLooks(body),
                                  TRM.MirrorGm(gmt, |str|), MIR.MirrorThread(th, |str|), ncap, nlook, nquant)
    ensures var lsub := SubFirstLeafAt(rer, crv, str, lid as int, th.look_regs);
            lsub.Some? ==>
              forall g: LG.GroupId ::
                g in PIV.CapIdsInLooks(body) && g in PIV.CapIds(NI.LookBodyOfRE(body, lid)) ==>
                  (g in lsub.value ==> g in gmt && gmt[g] == lsub.value[g])
                  && (g in gmt ==> g in lsub.value)
  {
    FG.LBOnlyEquiv(body); EL.NegLooksFromLBOnly(body);   // §2.2: the flip route keeps NR.NegLooksLookFreeRE
    // (§2.5b/z3 4.14) recursive nullability predicates + the CIN disjunct's
    // triggered existential storm the solver; all uses here are opaque.
    hide NUL.NonNullableL, NUL.CINullableL, NUL.NoNulledPlusL, AR.NfaRepCinL;
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
    var lkF := thF.look_regs;
    assert lkF == MIR.MirrorRegs(th.look_regs, n);
    var cp: nat := AReg.get_cp(th.look_regs, l).value;
    assert 0 <= cp <= n;
    assert AReg.get_cp(lkF, l).Some? && AReg.get_cp(lkF, l).value == n - cp;
    var mcpN: nat := n - cp;
    var inp := PIV.InpOfCp(str, cp);
    var inpF := PIV.InpOfCp(rstr, mcpN);

    // ---- sub-body facts needed on the spec side ----
    M.TransWfLookBodyOfRE(body, lid);
    M.CapUniqueLookBodyOfRE(body, lid);
    NI.LookBodyOfFragmentNested(body, lid);
    FG.LookBodySubFactsLB(body, lid);
    FST.TranslateFlipXRev(r1);

    // ---- lsub is the explicit backward leaf of r1 at cp ----
    SubFirstLeafAtIsBackLeaf(rer, crv, str, l, th.look_regs, r1);
    var lsub := SubFirstLeafAt(rer, crv, str, l, th.look_regs);
    assert lsub == FG.BackLeafAt(rer, r1, str, cp);
    var tB := LFU.ComputeTr(rer, [LS.Areg(T.Translate(r1))], inp, LG.Empty, WP.Backward);
    var rb := LT.TreeRes(tB, LG.Empty, inp, WP.Backward);
    assert lsub == (if rb.Some? then Some(rb.value.1) else None);

    // ---- lsubF is the forward leaf of FXR(r1) at n - cp ----
    var lsubF := SubFirstLeafAt(rer, crvF, rstr, l, lkF);
    assert M.VBody(crvF, l) == FST.FXR(r1);
    assert LidDir(crvF, l) == WP.Forward;
    var tF := LFU.ComputeTr(rer, [LS.Areg(T.Translate(FST.FXR(r1)))], inpF, LG.Empty, WP.Forward);
    var resF := LT.TreeRes(tF, LG.Empty, inpF, WP.Forward);
    assert lsubF == (if resF.Some? then Some(resF.value.1) else None);

    // ---- F2 at r1: the leaves mirror ----
    FST.TranslateGroupOkLB(r1);
    FST.TranslateNegBodiesGroupFree(r1);
    FK.TranslateDefGroupsNoDupK(r1);
    LBV.InpOfCpSwap(str, cp, n);
    assert inpF == SD.SwapInput(inp);
    MIR.ReverseLen(str[..cp]);
    assert |inp.pref| + |inp.next| == n;
    NI.NoNulledPlusLookBody(body, lid);   // §2.5b interim: NoNulledPlusRE(r1)
    NUL.TransNoNulledPlus(r1);            // §2.5b interim: NoNulledPlusL(Translate(r1))
    FD.BackBodyGmTieFlip(rer, T.Translate(r1), inp, n);
    assert tF == LFU.ComputeTr(rer, [LS.Areg(FM.FlipRevL(T.Translate(r1)))], SD.SwapInput(inp),
                               LG.Empty, WP.Forward);
    assert (rb.None? <==> resF.None?);

    // ---- instantiate the flipped deep clause at lid ----
    FG.TopLookIdsFXR(body);
    FG.LookIdsFXR(body);
    assert lid in NI.TopLookIds(reF) && lid in LTB.LookIds(reF);
    assert M.MatchedPosLA(crvF, lkF, l);
    assert thF.look_regs.a_clk == th.look_regs.a_clk && thF.quant_regs.a_clk == th.quant_regs.a_clk;
    FG.LookPathDomFXR(body, AI.get_idx(th.look_regs.a_clk, l), th.quant_regs.a_clk, lid);
    assert NI.LookPathDom(reF, AI.get_idx(thF.look_regs.a_clk, l), thF.quant_regs.a_clk, lid);
    FG.LookBodyOfREFXR(body, lid);
    assert NI.LookBodyOfRE(reF, lid) == FST.FXR(r1);
    FG.CapIdsFXR(r1);
    assert lsubF.Some? ==>
        forall g: LG.GroupId ::
          g in S && g in PIV.CapIds(NI.LookBodyOfRE(reF, lid)) ==>
            (g in lsubF.value ==> g in gmtF && gmtF[g] == lsubF.value[g])
            && (g in gmtF ==> g in lsubF.value);

    if lsub.Some? {
      assert rb.Some? && resF.Some?;
      assert TRM.GmInBounds(rb.value.1, n) && resF.value.1 == TRM.MirrorGm(rb.value.1, n);
      assert lsubF.Some? && lsubF.value == TRM.MirrorGm(lsub.value, n);
      TRM.MirrorGmAt(gmt, n);
      TRM.MirrorGmAt(lsub.value, n);
      forall g: LG.GroupId | g in S && g in PIV.CapIds(r1)
        ensures (g in lsub.value ==> g in gmt && gmt[g] == lsub.value[g])
                && (g in gmt ==> g in lsub.value)
      {
        assert g in PIV.CapIds(NI.LookBodyOfRE(reF, lid));
        if g in lsub.value {
          assert g in lsubF.value;
          assert g in gmtF && gmtF[g] == lsubF.value[g];
          assert g in gmt;
          assert TRM.MirrorRange(gmt[g], n) == TRM.MirrorRange(lsub.value[g], n);
          FG.MirrorRangeInj(gmt[g], lsub.value[g], n);
        }
        if g in gmt {
          assert g in gmtF;
          assert g in lsubF.value;
          assert g in lsub.value;
        }
      }
    }
  }

  /** (perf) The FORWARD BASE arm of `DeepFindRec`, extracted so its assertions are
      checked in a small context (same treatment as `DeepFindRecLB`).
      Mutually recursive with `DeepFindRec` on `(|LookIds(host)|, arm)`. */
  lemma DeepFindRecFwdBase(
    rer: LW.RegExpRecord, qm: AR.QMap, crv: CP.FCompiled, str: string, ast: R.regex, re: R.regex,
    ov: LOr.OracleView, res0: AReg.Regs, res1: AReg.Regs, res2: AReg.Regs,
    host: R.regex, A: nat, owner: nat, g2: nat, ncap: int, nlook: int, nquant: int)
    // ---- whole-regex statics (fixed through the recursion) ----
    requires T.TransWf(re) && NR.NestedFragmentRE(re) && NR.L5ScopeRE(re) && L5ScopeV1RE(re)
    requires M.LooksNoNulledPlusRE(re)   // (§2.5b F-c) look bodies stay stamp-free
    requires PIV.CapUnique(re) && PIV.QuantUnique(re) && LTB.LookUnique(re)
    requires LTB.LookTablesOk(re, crv)
    requires |crv.f_look_types| == |crv.f_look_ast|
    requires forall x: nat :: x in LTB.LookIds(re) ==> 1 <= x <= R.max_lookaround(ast)
    requires forall x: nat :: x in LTB.LookIds(re) ==> (x as int) in qm.looks
    requires nlook == R.max_lookaround(ast) + 1
    requires qm.ov == ov && !rer.multiline && !rer.ignoreCase && |ov| == |str| + 1
    requires forall l: int :: l in qm.looks ==> l >= 0
    requires M.OracleSufAllO(rer, qm, str)
    requires GateStaticsOkNested(qm, re, crv, ncap, nlook, nquant)
    requires M.FrameEntryAllO(crv, re, ast)
    // ---- global res-side facts (fixed) ----
    requires |res1.a_cp| == nlook && |res1.a_clk| == nlook
    requires CM.LookCpSetWithClk(res1) && CM.LookCpsLE(res1, |str|)
    requires CM.LookCpsOracleTrue(res1, ov)
    requires M.FLookLoopChildLinkOk(crv, str, res1, 1, R.max_lookaround(ast), ov, ncap, nlook, nquant)
    // ---- the OWNER package (A1/A2's conclusions at g2's innermost owner) ----
    requires g2 in PIV.CapIdsInLooks(re)
    requires owner in LTB.LookIds(re)
    requires g2 in PIV.CapIds(NI.LookBodyOfRE(re, owner))
    requires g2 !in PIV.CapIdsInLooks(NI.LookBodyOfRE(re, owner))
    requires var rfO := M.FreshBodyMatch(crv, str, owner as int, res1, ov, ncap, nlook, nquant);
             rfO.Some? && g2 in PIV.GmOfLive(NI.LookBodyOfRE(re, owner),
                                             rfO.value.capture_regs, rfO.value.look_regs, rfO.value.quant_regs)
    // ---- per-level data ----
    requires A in LTB.LookIds(re)
    requires host == NI.LookBodyOfRE(re, A)
    requires M.MatchedPosLA(crv, res1, A as int)
    requires g2 in PIV.CapIds(host)
    requires PIV.PathPresentLk(host, res0.a_clk, res1.a_clk, res2.a_clk, -1, g2)
    ensures var lsub := SubFirstLeafAt(rer, crv, str, A as int, res1);
            lsub.Some? && g2 in lsub.value
    requires !crv.f_look_types[A as int].Lookbehind?
    requires g2 !in PIV.CapIdsInLooks(host)
    decreases |LTB.LookIds(host)|, 0
  {
    // (2026-08-25) this lemma takes the L4-perf OPAQUE bundles (`117b6aa`) but its
    // body reads their foralls (`FrameEntryOk` at A, `OracleOkSuffix` at cps) —
    // reveal them. (Never re-verified after the perf pass; failed 3 asserts.)
    reveal M.OracleSufAllO(), M.FrameEntryAllO();
    var maxlook := R.max_lookaround(ast);
    var cpA := AReg.get_cp(res1, A as int).value;
    RL.AAsArraysLaws(res1);
    assert AI.get_idx(res1.a_cp, A as int) >= 0 && cpA == AI.get_idx(res1.a_cp, A as int);
    assert 0 <= cpA <= |str|;                                    // LookCpsLE(res1)
    var inpA := PIV.InpOfCp(str, cpA);
    var bodycode := CP.compile_to_bytecode(host);

    // ---- the row at A: la_A + host tie + statics ----
    assert 1 <= A <= maxlook && (A as int) in qm.looks;
    assert GateStaticAtNested(qm, re, crv, A as int, ncap, nlook, nquant);   // GateStaticsOkNested
    var laA: R.lookaround, bA: R.regex :|
      LTB.LookEntryOk(crv, A as int, laA, bA)
      && T.TransWf(bA) && NR.NestedFragmentRE(bA)
      && EL.NegBehindLookFreeRE(bA)
      && (laA.Lookbehind? ==> NR.LBOnlyLooksRE(bA))
      && (!laA.Lookbehind? ==> L5ScopeV1RE(bA))
      && qm.looks[A as int].0 == T.TrLookaround(laA)
      && qm.looks[A as int].1 == T.Translate(bA)
      && (set g: LG.GroupId | g in L.DefGroups(T.Translate(bA))) <= PIV.CapIdsInLooks(re)
      && var bc := CP.compile_to_bytecode(bA);
      |bc| >= 1
      && PSM.StaticOkNestedRE(qm, bA, bc, |bc| - 1)
      && PSM.SizesOkRE(bA, ncap, nlook, nquant)
      && ((laA.NegLookbehind? || laA.NegLookahead?) ==> NR.CaptureFreeRE(bA));
    NI.LookBodyOfTablesTie(re, crv, A);
    var laT: R.lookaround :| LTB.LookEntryOk(crv, A as int, laT, NI.LookBodyOfRE(re, A));
    assert bA == host by { assert crv.f_look_ast[A as int] == bA == host; }
    assert host == M.VBody(crv, A as int);
    var endlH: nat := |bodycode| - 1;
    assert PSM.StaticOkNestedRE(qm, host, bodycode, endlH);
    assert crv.f_look_types[A as int] == laA;
    assert (laA.Lookahead? || laA.Lookbehind?) by {
      assert AI.capture_type(crv.f_look_types[A as int]);        // MatchedPosLA
    }
    assert !laA.Lookbehind? by { assert crv.f_look_types[A as int] == laA; }
    assert laA.Lookahead?;
    assert M.FrameEntryOk(crv, laA, host,
                          PIV.CaptureRegsSet(PIV.CapIdsInLooks(re)), M.LookIdSet(re));
    assert PIV.CapUnique(host) && PIV.QuantUnique(host) && LTB.LookUnique(host)
           && LTB.LookTablesOk(host, crv);                          // FrameEntryOk

    // ==== BASE: g2 DIRECT in host — A is THE innermost-direct owner ====
    M.InnermostOwnerUnique(re, g2, owner, A);
    assert owner == A;
    var rfO := M.FreshBodyMatch(crv, str, A as int, res1, ov, ncap, nlook, nquant);
    assert rfO.Some?
           && g2 in PIV.GmOfLive(host, rfO.value.capture_regs, rfO.value.look_regs, rfO.value.quant_regs);
    assert LL.OracleOkSuffix(rer, qm, PIV.InpOfCp(str, cpA));
    FreshBodyDirectInSubFirstLeaf(rer, qm, crv, str, ov, A, res1, host, bodycode,
                                  endlH, 0, g2, ncap, nlook, nquant);
  }

  /** The L4 scope is a special case of the L5 scope. */
  lemma L4ScopeImpliesL5(raw: R.raw_regex)
    requires T.Latin1Wf(raw)
    requires L4Scope(raw)
    ensures L5Scope(raw)
  {
    NoPosImpliesL5ScopeV1(R.lazy_prefix(R.annotate(raw)));
  }

  /** THE EXECUTABLE-SCOPE BRIDGE for L5: `L5Scope` from the raw syntactic predicates
      (`L4ScopeFromRaw` with `NoPosLookbehindRaw` replaced by `L5ScopeRaw`). */
  lemma L5ScopeFromRawFull(raw: R.raw_regex)
    requires T.Latin1Wf(raw)
    requires L5ScopeV1RE(R.lazy_prefix(R.annotate(raw)))
    requires EL.NegBehindLookFreeRaw(raw)
    ensures L5Scope(raw)
  {
    var ast := R.annotate(raw);
    var re := R.lazy_prefix(ast);
    assert ast == R.annotate_regex(R.Raw_capture(raw), 0, 1, 1).0;
    // TransWf
    T.AnnotateWf(raw);
    // the L5 scope (positive lookbehinds with LB-only bodies), from the raw predicate
    assert L5ScopeV1RE(re);                                  // hypothesis
    // NegLooksLookFree
    assert EL.NegBehindLookFreeRaw(R.Raw_capture(raw));
    EL.AnnotateNegBehindLookFree(R.Raw_capture(raw), 0, 1, 1);
    assert EL.NegBehindLookFreeRE(ast);
    assert EL.NegBehindLookFreeRE(re);
  }

  /** (2026-11-05) `OracleColumnNested`'s lookahead row, engine -> spec, with a
      NARROW contract (memory `dafny-batch-memory-hogs`, cause 2: in the column
      lemma's context even this direction's one-line steps took 900 s). */
  lemma ColumnAheadBitToRun(body: R.regex, lid: int, str: string, ovf: LOr.OracleView, cp: nat,
                            cdnsb: LCdn.cdns, initcap: AReg.Regs, initlook: AReg.Regs, initquant: AReg.Regs)
    requires NR.NestedFragmentRE(body) && LTB.LookUnique(body)
    requires forall y: nat :: y in LTB.LookIds(body) ==> 1 <= y
    requires cp <= |str| && |ovf| == |str| + 1
    requires ORc.ReachesWriteV(CP.compile_to_write(R.lazy_prefix(OMV.XRev(R.remove_capture(body))), lid),
                               LC.Reverse(str), MIR.MirrorView(ovf, |str|), 0, lid, |str| - cp)
    ensures var code := CP.compile_to_bytecode(body);
            var s := AI.FInitState(code, cp, initcap, initlook, initquant, 0,
                                   AI.cp_context(cp, str, LAnc.Forward));
            AI.FFindMatch(code, str, s, ovf, LAnc.Forward, cdnsb).0.Some?
  {
    // only lemma postconditions are needed; unfolding FFindMatch/MatchesV blew
    // this lemma to 21 GB at one worker (2026-11-05)
    hide *;
    var n := |str|;
    var rcb := R.remove_capture(body);
    var x := OMV.XRev(rcb);
    var rstr := LC.Reverse(str);
    var mv := MIR.MirrorView(ovf, n);
    SD.ReverseLength(str);
    OMV.RemoveCaptureNestedFragment(body);
    OMV.XRevNestedFragment(rcb);
    var i := ODV.ReachesWriteVToMatchesV(x, lid, rstr, mv, n - cp);
    OMV.MatchesVMirror(rcb, str, ovf, cp, n - i);
    assert n - (n - i) == i;
    assert OBV.MatchesV(rcb, str, ovf, cp, n - i);
    OMV.MatchesVRemoveCapture(body, str, ovf, cp, n - i);
    assert OBV.MatchesV(body, str, ovf, cp, n - i);
    OAV.AcceptRunCharacterizationV(body, str, ovf, cp, cdnsb, initcap, initlook, initquant, 0);
  }

  /** (2026-11-05) `OracleColumnNested`'s lookahead row, spec -> engine, with a
      NARROW contract (memory `dafny-batch-memory-hogs`, cause 2: the assumed
      context made the column lemma's last call a 900 s batch at one worker). */
  lemma ColumnAheadSpecToBit(body: R.regex, lid: int, str: string, ovf: LOr.OracleView,
                             cp: nat, j: int)
    requires NR.NestedFragmentRE(body)
    requires cp <= |str| && |ovf| == |str| + 1
    requires OBV.MatchesV(body, str, ovf, cp, j)
    ensures ORc.ReachesWriteV(CP.compile_to_write(R.lazy_prefix(OMV.XRev(R.remove_capture(body))), lid),
                              LC.Reverse(str), MIR.MirrorView(ovf, |str|), 0, lid, |str| - cp)
  {
    var n := |str|;
    var rcb := R.remove_capture(body);
    var x := OMV.XRev(rcb);
    var rstr := LC.Reverse(str);
    var mv := MIR.MirrorView(ovf, n);
    SD.ReverseLength(str);
    OMV.RemoveCaptureNestedFragment(body);
    OMV.XRevNestedFragment(rcb);
    OBV.MatchesVBounds(body, str, ovf, cp, j);
    MatchesVUpper(body, str, ovf, cp, j);
    OMV.MatchesVRemoveCapture(body, str, ovf, cp, j);
    OMV.MatchesVMirror(rcb, str, ovf, cp, j);
    assert OBV.MatchesV(x, rstr, mv, n - j, n - cp);
    OBV.MatchesVToReachesWriteV(x, lid, rstr, mv, n - j, n - cp);
  }

  /** THE NESTED COLUMN SPEC, one row at one column. Given the oracle truth of
      the row's INNER rows (the body's own rows, from the initial input), the
      final view's bit at `(cp, lid)` is exactly the spec walk of the row's
      body at `cp` in the row's direction. */
  // (2026-09-06) `{:isolate_assertions}` REMOVED: it split this lemma into 1070
  // assertion-sized queries whose AGGREGATE exceeded the gate's 900 s budget,
  // which is how it presented as a "time out" — see the isolate_assertions
  // policy. The hide below does the real work.
  lemma OracleColumnNested(rer: LW.RegExpRecord, top: R.regex, crv: CP.FCompiled,
                                                 str: string, sub: R.regex, lid: int,
                                                 lk: L.Lookaround, r1: L.Regex, cp: nat)
    requires !rer.ignoreCase && !rer.multiline
    requires crv == CP.FFullCompilation(top)
    requires NR.NestedFragmentRE(top) && LTB.LidsWellNested(top) && LTB.LookUnique(top)
    requires forall x: nat :: x in LTB.LookIds(top) ==> 1 <= x
    requires NR.NestedFragmentRE(sub) && NR.L5ScopeRE(sub) && EL.NegBehindLookFreeRE(sub)   // (L5 F7g) lifted
    requires M.LooksNoNulledPlusRE(sub)   // (§2.5b F-c) look bodies stay stamp-free
    requires T.TransWf(sub) && LTB.LookUnique(sub) && PIV.CapUnique(sub) && PIV.QuantUnique(sub)
    requires LTB.LookTablesOk(sub, crv)
    requires LTB.LookIds(sub) <= LTB.LookIds(top)
    requires cp <= |str|
    requires lid >= 0 && (lid as nat) in LTB.LookIds(sub)
    requires lid in OE.LmOf(sub) && OE.LmOf(sub)[lid] == (lk, r1)
    requires T.TransWf(NI.LookBodyOfRE(sub, lid as nat))     // well-formedness of the QmOfRE/LmOf below
    requires var body := NI.LookBodyOfRE(sub, lid as nat);
             LL.OracleOkSuffix(rer, AR.QMap(M.QmOfRE(body), OE.LmOf(body), AI.FBuildOracle(crv, str), M.BodiesOfRE(body)),
                               LC.InitInput(str))
    ensures LOr.view_get_oracle(AI.FBuildOracle(crv, str), cp, lid)
       <==> LT.TreeRes(LFU.ComputeTr(rer, [LS.Areg(r1)], T.InputAt(str, cp), LG.Empty, L.LkDir(lk)),
                       LG.Empty, T.InputAt(str, cp), L.LkDir(lk)).Some?
  {
    // (2026-09-06) the hypotheses mention these recursive predicates on `top`/`sub`
    // throughout; their unfolding is a matching loop (cf. the annotate family in
    // MainTheorem's extraction lemmas).
    hide NR.NestedFragmentRE, NR.L5ScopeRE, EL.NegBehindLookFreeRE, NR.NoNulledPlusRE, LTB.LidsWellNested, LTB.LookUnique;
    // (§2.5b/z3 4.14) recursive nullability predicates + the CIN disjunct's
    // triggered existential storm the solver; all uses here are opaque.
    hide NUL.NonNullableL, NUL.CINullableL, NUL.NoNulledPlusL, AR.NfaRepCinL;
    var n := |str|;
    var ovf := AI.FBuildOracle(crv, str);
    var lidn: nat := lid as nat;
    assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
    M.LookBodyFactsL5(sub, crv, lidn);
    assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
    LookBodyRowL5(sub, crv, lidn);
    var body := NI.LookBodyOfRE(sub, lidn);
    var la: R.lookaround :| LTB.LookEntryOk(crv, lid, la, body)
                            && OE.LmOf(sub)[lid] == (T.TrLookaround(la), T.Translate(body))
                            && (la.Lookbehind? ==> NR.LBOnlyLooksRE(body))
                            && (la.NegLookbehind? ==> NR.LookFreeRE(body));
    assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
    assert lk == T.TrLookaround(la) && r1 == T.Translate(body);
    assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
    assert lidn in LTB.LookIds(top);
    assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
    LTB.LookIdsLeMax(top);
    assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
    assert 1 <= lid <= R.max_lookaround(top);

    // ---- the bit IS the corrected V-target against the final view ----------
    assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
    OB.FBuildOracleViewLen(crv, str);
    assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
    assert |ovf| == n + 1;
    assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
    OB.FBuildOracleCorrectAboveNested(top, str);
    var bit := LOr.view_get_oracle(ovf, cp, lid);
    assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
    assert bit == OB.LidReachesVFinal(crv, str, ovf, lid, cp);
    reveal OB.LidReachesVFinal();
    var bc := AI.get_code_v(crv.f_look_build_bc, lid);
    assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
    assert bc == CP.compile_to_write(CP.oracle_regex(la, body), lid);   // LookEntryOk row
    assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
    assert crv.f_look_types[lid] == la;
    var rcb := R.remove_capture(body);
    assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
    OMV.RemoveCaptureNestedFragment(body);
    var inp := T.InputAt(str, cp);
    assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
    assert PIV.InpOfCp(str, cp) == inp by { LS.ReverseLength(str[..cp]); }
    assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
    SD.ReverseLength(str);
    var rstr := LC.Reverse(str);
    assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
    assert |rstr| == n;

    assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
    if la.Lookahead? || la.NegLookahead? {
      // ---- lookAHEAD row: backward build, mirrored; spec walk is FORWARD ----
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert L.LkDir(lk) == WP.Forward;
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert OB.LidDir(crv, lid) == LAnc.Backward;
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert CP.oracle_regex(la, body) == R.lazy_prefix(R.reverse_regex(rcb));
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      OB.CompileToWriteSwap(R.lazy_prefix(R.reverse_regex(rcb)), lid);
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      OB.SwapAnchorsLazyPrefix(R.reverse_regex(rcb));
      var x := OMV.XRev(rcb);
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert MIR.SwapAnchorsCode(bc) == CP.compile_to_write(R.lazy_prefix(x), lid);
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      OMV.XRevNestedFragment(rcb);
      var mv := MIR.MirrorView(ovf, n);
      var mcp := MIR.Mirror(cp, n);
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert mcp == n - cp;
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert bit == ORc.ReachesWriteV(CP.compile_to_write(R.lazy_prefix(x), lid), rstr, mv, 0, lid, mcp);

      // engine run of the body at cp against the FINAL view <==> a gated span
      var codeb := CP.compile_to_bytecode(body);
      var cdnsb := LCdn.compile_cdns(body);
      var ncapb := R.imax(0, 2 * R.max_group(body) + 2);
      var nlookb := R.imax(0, R.max_lookaround(body) + 1);
      var nquantb := R.imax(0, R.max_quant(body) + 1);
      var inits := AI.FInitState(codeb, cp, AReg.init_regs(ncapb), AReg.init_regs(nlookb),
                                 AReg.init_regs(nquantb), 0, AI.cp_context(cp, str, LAnc.Forward));
      var r := AI.FFindMatch(codeb, str, inits, ovf, LAnc.Forward, cdnsb).0;
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert forall y: nat :: y in LTB.LookIds(body) ==> 1 <= y;
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      OAV.AcceptRunCharacterizationV(body, str, ovf, cp, cdnsb, AReg.init_regs(ncapb),
                                     AReg.init_regs(nlookb), AReg.init_regs(nquantb), 0);
      // (AcceptRunCharacterizationV's postcondition `r.Some? <==> exists j :: MatchesV(...)`
      //  stays available as an assumption; a standalone assert of it timed out — dropped.)

      // spec side: the engine run at cp IS the body's first leaf (inner rows)
      var qmb := AR.QMap(M.QmOfRE(body), OE.LmOf(body), ovf, M.BodiesOfRE(body));
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      OracleOkSuffixAtCp(rer, qmb, str, cp);
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      NR.CompileToBytecodeRepNested(body);
      var endlb: nat := CP.compile(body, 0, CP.Progress).1 as nat;
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      CompileStutterTameRENested(body);
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      M.QmOfREEntries(body);
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      M.BodiesOfREEntries(body);   // §2.5b: the bodies table entries
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      M.QmapOkFromEntries(body, qmb);
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      OE.LmapOkOfLmOf(body, qmb);
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      M.LooksNoNulledPlusBody(sub, lid as nat);   // §2.5b interim: NoNulledPlusRE(body)
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert PSM.StaticOkNestedRE(qmb, body, codeb, endlb);
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert PSM.SizesOkRE(body, ncapb, nlookb, nquantb);
      var bestT := M.BodyTreeAtCpNested(rer, qmb, body, codeb, endlb, 0, str, cp, ovf, cdnsb,
                                        ncapb, nlookb, nquantb);
      var t := LFU.ComputeTr(rer, [LS.Areg(T.Translate(body))], inp, LG.Empty, WP.Forward);
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert (bestT.None? <==> r.None?) && (bestT.None? <==> LT.FirstLeaf(t, inp).None?);
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert LT.FirstLeaf(t, inp) == LT.TreeRes(t, LG.Empty, inp, WP.Forward);

      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      if bit {
        // (2026-11-05) engine -> spec as a narrow-contract lemma: in this context
        // even the one-line steps of this direction took 900 s at one worker.
        ColumnAheadBitToRun(body, lid, str, ovf, cp, cdnsb, AReg.init_regs(ncapb),
                            AReg.init_regs(nlookb), AReg.init_regs(nquantb));
        assert {:split_here} true;
        assert r.Some?;
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert LT.TreeRes(t, LG.Empty, inp, WP.Forward).Some?;
      }
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      if LT.TreeRes(t, LG.Empty, inp, WP.Forward).Some? {
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert r.Some?;
        var j: int :| OBV.MatchesV(body, str, ovf, cp, j);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        // (2026-11-05) the rest of this direction is a narrow-contract lemma: here
        // the final call's batch alone hit the 900 s limit at one worker although
        // every precondition was already asserted (the assumed context, not the call).
        ColumnAheadSpecToBit(body, lid, str, ovf, cp, j);
        assert x == OMV.XRev(R.remove_capture(body)) && mv == MIR.MirrorView(ovf, n);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert bit;
      }
    assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
    } else if la.NegLookbehind? {
      // ---- negative lookBEHIND row: forward build, look-free body; spec walk BACKWARD ----
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert la.NegLookbehind?;
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert NR.LookFreeRE(body);
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert L.LkDir(lk) == WP.Backward;
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert OB.LidDir(crv, lid) == LAnc.Forward;
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert CP.oracle_regex(la, body) == R.lazy_prefix(rcb);
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert bit == ORc.ReachesWriteV(CP.compile_to_write(R.lazy_prefix(rcb), lid), str, ovf, 0, lid, cp);
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      OS.TranslateLookFreeGroupOk(body);
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      if bit {
        var i := ODV.ReachesWriteVToMatchesV(rcb, lid, str, ovf, cp);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        OMV.MatchesVRemoveCapture(body, str, ovf, i, cp);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        MatchesVLookFree(body, str, ovf, i, cp);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        OS.MatchesTransfer(rer, body, str, i, cp);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        SD.SpanDualityComplete(rer, T.Translate(body), str, i, cp, LG.Empty);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert SD.SuccActs(rer, [LS.Areg(T.Translate(body))], inp, LG.Empty, WP.Backward);
      }
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      if SD.SuccActs(rer, [LS.Areg(T.Translate(body))], inp, LG.Empty, WP.Backward) {
        var i := SD.SpanDualitySound(rer, T.Translate(body), str, cp, LG.Empty);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        OS.MatchesTransfer(rer, body, str, i, cp);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        MatchesVLookFree(body, str, ovf, i, cp);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        OMV.MatchesVRemoveCapture(body, str, ovf, i, cp);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        OBV.MatchesVToReachesWriteV(rcb, lid, str, ovf, i, cp);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert bit;
      }
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert SD.SuccActs(rer, [LS.Areg(r1)], inp, LG.Empty, WP.Backward)
          == LT.TreeRes(LFU.ComputeTr(rer, [LS.Areg(r1)], inp, LG.Empty, WP.Backward),
                        LG.Empty, inp, WP.Backward).Some?;
    assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
    } else {
      // ---- (L5 F7g) POSITIVE lookBEHIND row (lookbehind-only nested body): the
      //      gate-side CAPSTONE `OE.OracleColumnSpecNested` — the final view's bit
      //      IS the body's BACKWARD walk at cp. Its whole-string column premise
      //      for the body's own rows comes from the inner-rows induction hypothesis.
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert la.Lookbehind?;
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert NR.LBOnlyLooksRE(body);
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert L.LkDir(lk) == WP.Backward;
      var qmb := AR.QMap(M.QmOfRE(body), OE.LmOf(body), ovf, M.BodiesOfRE(body));
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      OE.LmapOkOfLmOf(body, qmb);
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert OE.OracleColsOk(rer, qmb, str) by {
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        forall c: nat | c <= |str| ensures LL.OracleOkSuffix(rer, qmb, PIV.InpOfCp(str, c)) {
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          OracleOkSuffixAtCp(rer, qmb, str, c);
        }
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        SufForallToColsOk(rer, qmb, str);
      }
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      FG.LBOnlyEquiv(body);
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      FST.TranslateGroupOkLB(body);
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      OE.OracleColumnSpecNested(rer, qmb, top, str, lid, la, body, cp);
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert bit <==> SD.SuccActs(rer, [LS.Areg(T.Translate(body))], inp, LG.Empty, WP.Backward);
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert SD.SuccActs(rer, [LS.Areg(r1)], inp, LG.Empty, WP.Backward)
          == LT.TreeRes(LFU.ComputeTr(rer, [LS.Areg(r1)], inp, LG.Empty, WP.Backward),
                        LG.Empty, inp, WP.Backward).Some?;
    }
  }

  /** THE NESTED ORACLE ENTRY: the oracle truth of every row of `sub` (a look
      body of — or all of — the compiled regex `top`), from the initial input,
      by recursion on the nesting (each row's inner rows first, then the row's
      own column spec `OracleColumnNested`). At `sub == lazy_prefix(top)` this is
      exactly `MainTheoremL4`'s former hypothesis. */
  /** (L5 F7g) THE NESTED ORACLE ENTRY under the L5 scope (positive lookbehinds
      with lookbehind-only bodies admitted — their column is `OracleColumnNested`'s
      new arm). (the L4-scope wrapper has been retired). */
  lemma OracleOkRowsL5(rer: LW.RegExpRecord, top: R.regex, crv: CP.FCompiled,
                                             str: string, sub: R.regex)
    requires !rer.ignoreCase && !rer.multiline
    requires crv == CP.FFullCompilation(top)
    requires NR.NestedFragmentRE(top) && LTB.LidsWellNested(top) && LTB.LookUnique(top)
    requires forall x: nat :: x in LTB.LookIds(top) ==> 1 <= x
    requires NR.NestedFragmentRE(sub) && NR.L5ScopeRE(sub) && EL.NegBehindLookFreeRE(sub)   // (L5 F7g) lifted
    requires M.LooksNoNulledPlusRE(sub)   // (§2.5b F-c) look bodies stay stamp-free
    requires T.TransWf(sub) && LTB.LookUnique(sub) && PIV.CapUnique(sub) && PIV.QuantUnique(sub)
    requires LTB.LookTablesOk(sub, crv)
    requires LTB.LookIds(sub) <= LTB.LookIds(top)
    ensures LL.OracleOkSuffix(rer, AR.QMap(M.QmOfRE(sub), OE.LmOf(sub), AI.FBuildOracle(crv, str), M.BodiesOfRE(sub)),
                              LC.InitInput(str))
    decreases |LTB.LookIds(sub)|
  {
    var n := |str|;
    var ovf := AI.FBuildOracle(crv, str);
    var qm := AR.QMap(M.QmOfRE(sub), OE.LmOf(sub), ovf, M.BodiesOfRE(sub));
    OE.LmOfDom(sub);
    OE.InitInputAt(str);
    forall inp: LC.Input | inp == LC.InitInput(str) || SSx.IsStrictSuffix(inp, LC.InitInput(str), WP.Forward)
      ensures LL.OracleOkAt(rer, qm, inp)
    {
      var cp: nat;
      if inp == LC.InitInput(str) {
        cp := 0;
      } else {
        assert SSx.StrictSuffixForward(inp, T.InputAt(str, 0).next, T.InputAt(str, 0).pref);
        OE.SuffixIsInputAt(str, 0, inp);
        var m: nat :| 0 < m <= n && inp == T.InputAt(str, m);
        cp := m;
      }
      assert inp == T.InputAt(str, cp) && cp <= n;
      T.ReverseProps(str[..cp]);
      assert TREP.CpOf(inp) == cp;
      forall lid: int, lk: L.Lookaround, r1: L.Regex | lid in qm.looks && qm.looks[lid] == (lk, r1)
        ensures LOr.view_get_oracle(qm.ov, TREP.CpOf(inp), lid)
           <==> LT.TreeRes(LFU.ComputeTr(rer, [LS.Areg(r1)], inp, LG.Empty, L.LkDir(lk)),
                           LG.Empty, inp, L.LkDir(lk)).Some?
      {
        assert lid >= 0 && (lid as nat) in LTB.LookIds(sub);
        var lidn: nat := lid as nat;
        M.LookBodyFactsL5(sub, crv, lidn);
        LookBodyRowL5(sub, crv, lidn);
        var body := NI.LookBodyOfRE(sub, lidn);
        // the inner rows first (strictly fewer look ids: the owner's own id is gone)
        LookIdNotInOwnBody(sub, lidn);
        SubsetCardLt(LTB.LookIds(body), LTB.LookIds(sub), lidn);
        M.LooksNoNulledPlusBody(sub, lidn);   // §2.5b interim: NoNulledPlusRE(body)
        OracleOkRowsL5(rer, top, crv, str, body);
        // then this row's column
        OracleColumnNested(rer, top, crv, str, sub, lid, lk, r1, cp);
      }
    }
  }

}
