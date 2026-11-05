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
    requires AR.NoTrueStamps(code)   // §2.5b stage 2a: look-body code is stamp-free
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

  /** TOP-LEVEL establishment: `GateStaticsOk` from the compile tables + qm
      well-formedness (`qm.looks`' domain within `re`'s lids is the caller's
      obligation — true by qm's construction). */
  lemma GateStaticsFromTables(qm: AR.QMap, re: R.regex, crv: CP.FCompiled,
                              ncap: int, nlook: int, nquant: int)
    requires T.TransWf(re) && AR.QmapOk(re, qm) && AR.LmapOk(re, qm)
    requires NR.NoNulledPlusRE(re)   // §2.5b interim
    requires NR.LookBehindFragmentRE(re) && PIV.CapUnique(re) && PIV.QuantUnique(re)
    requires LTB.LookTablesOk(re, crv)
    requires PSM.SizesOkRE(re, ncap, nlook, nquant)
    requires forall l: int :: l in qm.looks ==>
                                l >= 0 && (l as nat) in LTB.LookIds(re) && l < nlook
    ensures GateStaticsOk(qm, re, crv, ncap, nlook, nquant)
  {
    GateStaticsSweepRE(qm, re, re, crv, ncap, nlook, nquant);
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
    requires NR.NoNulledPlusRE(re)   // §2.5b interim
    requires NR.NestedFragmentRE(re) && NR.NegLooksLookFreeRE(re) && L5ScopeV1RE(re)
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
      GateStaticsSweepRENested(qm, re0, body, crv, ncap, nlook, nquant);
      if lid >= 0 {
        // the node's own bundle
        assert LTB.LookEntryOk(crv, lid, la, body);
        assert T.TransWf(body) && NR.NestedFragmentRE(body)
               && NR.NegLooksLookFreeRE(body);
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
      `NR.NegLooksLookFreeRE` pin the positive-lookahead-nesting scope). Proves
      `GateStaticsOkNested` is DISCHARGEABLE for the nested fragment — the
      "requires-side" of the non-vacuity claim. Off `GateStaticsFromTables`. */
  lemma GateStaticsFromTablesNested(qm: AR.QMap, re: R.regex, crv: CP.FCompiled,
                                    ncap: int, nlook: int, nquant: int)
    requires T.TransWf(re) && AR.QmapOk(re, qm) && AR.LmapOk(re, qm)
    requires NR.NoNulledPlusRE(re)   // §2.5b interim
    requires NR.NestedFragmentRE(re) && NR.NegLooksLookFreeRE(re) && L5ScopeV1RE(re)
    requires PIV.CapUnique(re) && PIV.QuantUnique(re)
    requires LTB.LookTablesOk(re, crv)
    requires PSM.SizesOkRE(re, ncap, nlook, nquant)
    requires forall l: int :: l in qm.looks ==>
                                l >= 0 && (l as nat) in LTB.LookIds(re) && l < nlook
    ensures GateStaticsOkNested(qm, re, crv, ncap, nlook, nquant)
  {
    GateStaticsSweepRENested(qm, re, re, crv, ncap, nlook, nquant);
  }

  /** (L4 NESTED) the depth-1 gate-static package embeds in the nested one:
      `GateStaticAt ⟹ GateStaticAtNested` on look-free bodies. Confirms
      `GateStaticAtNested` is a genuine WEAKENING (every depth-1 caller feeds the
      nested chain) and that the two coincide at `NestDepth(body) == 0`. The
      look-free body's nested facts come from `LookFreePlusIsNestedRE`/
      `LookFreeNegLooksLookFree`/`LookFreeNoPosLookbehindRE`, and its
      `StaticOkNestedRE` from `PSM.StaticOkRENestedFromRE`. */
  lemma GateStaticAtImpliesNested(qm: AR.QMap, re: R.regex, crv: CP.FCompiled, l: int,
                                  ncap: int, nlook: int, nquant: int)
    requires GateStaticAt(qm, re, crv, l, ncap, nlook, nquant)
    ensures GateStaticAtNested(qm, re, crv, l, ncap, nlook, nquant)
  {
    var la: R.lookaround, body: R.regex :|
      LTB.LookEntryOk(crv, l, la, body)
      && T.TransWf(body) && NR.LookFreeRE(body)
      && qm.looks[l].0 == T.TrLookaround(la)
      && qm.looks[l].1 == T.Translate(body)
      && (set g: LG.GroupId | g in L.DefGroups(T.Translate(body))) <= PIV.CapIdsInLooks(re)
      && var bodycode := CP.compile_to_bytecode(body);
      |bodycode| >= 1
      && PSM.StaticOkRE(qm, body, bodycode, |bodycode| - 1)
      && PSM.SizesOkRE(body, ncap, nlook, nquant)
      && ((la.NegLookbehind? || la.NegLookahead?) ==> NR.CaptureFreeRE(body));
    var bodycode := CP.compile_to_bytecode(body);
    // look-free body ⟹ the nested-fragment side conditions
    NR.LookFreeIsPlusFragmentRE(body);      // PlusFragmentRE(body) (StaticOkRE ⟹ LookBehindFragmentRE(body))
    NR.LookFreePlusIsNestedRE(body);        // NestedFragmentRE(body)
    NR.LookFreeNegLooksLookFree(body);      // NegLooksLookFreeRE(body)
    LookFreeNoPosLookbehindRE(body);        // NoPosLookbehindRE(body)
    NoPosImpliesL5ScopeV1(body);            // L5ScopeV1RE(body)  (s6 widening)
    NR.LookFreeLBOnly(body);                // LBOnlyLooksRE(body)
    PSM.StaticOkRENestedFromRE(qm, body, bodycode, |bodycode| - 1);  // StaticOkNestedRE(body)
    assert GateStaticAtNested(qm, re, crv, l, ncap, nlook, nquant);
  }

  lemma GateStaticsOkImpliesNested(qm: AR.QMap, re: R.regex, crv: CP.FCompiled,
                                   ncap: int, nlook: int, nquant: int)
    requires GateStaticsOk(qm, re, crv, ncap, nlook, nquant)
    ensures GateStaticsOkNested(qm, re, crv, ncap, nlook, nquant)
  {
    forall l: int | l in qm.looks
      ensures 0 <= l < nlook && GateStaticAtNested(qm, re, crv, l, ncap, nlook, nquant)
    {
      GateStaticAtImpliesNested(qm, re, crv, l, ncap, nlook, nquant);
    }
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
    requires NR.NegLooksLookFreeRE(body)
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
    requires NR.NegLooksLookFreeRE(body)
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
    requires T.TransWf(body) && NR.NestedFragmentRE(body) && NR.NegLooksLookFreeRE(body)
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
    FG.FreshBodyDirectInBackLeaf(rer, qm, crv, str, ov, A0, lk, body, g2, ncap, nlook, nquant);
    SubFirstLeafAtIsBackLeaf(rer, crv, str, A0 as int, lk, body);
  }

  /** LB twin of `SubFirstLeafDirectInFresh`: a DIRECT group present in
      `SubFirstLeafAt` is live in the fresh BACKWARD body match, with the leaf's
      ordered range = `SwapRange` of the backward match's reversed read. */
  lemma SubFirstLeafDirectInFreshLB(
    rer: LW.RegExpRecord, qm: AR.QMap, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
    A0: nat, lk: AReg.Regs, body: R.regex, g2: nat, ncap: int, nlook: int, nquant: int)
    requires T.TransWf(body) && NR.NestedFragmentRE(body) && NR.NegLooksLookFreeRE(body)
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
    SubFirstLeafAtIsBackLeaf(rer, crv, str, A0 as int, lk, body);
    FG.BackLeafDirectInFresh(rer, qm, crv, str, ov, A0, lk, body, g2, ncap, nlook, nquant);
  }

  /** (R2 — DIRECT-case per-`g2` package assembler) Given the RECONSTRUCTED-bank
      facts that A1/A2 (`M.FLookLoopInLookLiveOwnerMatched` / `M.FreshBodyDirect
      Member`) deliver for a res0-live inside-look capture `g2` whose innermost
      owner is a TOP look `A0` — `MatchedPosLA(res1, A0)` + a fresh body match of
      `A0` carrying `g2` LIVE — this assembles EXACTLY the `DescentProducerTop
      OwnersDeep` per-`g2` existential body ON THE WINNING THREAD'S BANKS, for the
      DIRECT case (`g2` directly owned by `A0`). The res1→thread.look_regs transport
      is the committed reconciliation: `MatchedPosLAFreshBodyCpCong` moves both
      `MatchedPosLA` and `FreshBodyMatch` across the top-look POSITION agreement
      (`get_cp(res1, A0) == get_cp(thread.look_regs, A0)`, produced by
      `M.FLookLoopTopLookCpStableFull`), and `FreshBodyDirectInSubFirstLeaf` lands
      the transported live `g2` in `SubFirstLeafAt(A0, thread.look_regs)`.

      SOLE ENGINE RESIDUAL (a `requires` here): the gate-crossing dominance
      `LookPathDom(re, thread.look_regs.a_clk[A0], thread.quant_regs.a_clk, A0)` on
      the winning thread's banks — the "winning thread crossed A0's gate and
      dominates" reverse connective, which no lemma yet establishes (`LookNestOkTTop`
      proves the CLOCK-set + `LookPathPresent` + dominance ingredients only under a
      `gmt`-witness guard, circular for the res0-live descent; deriving it non-
      circularly is the owed reverse of `FLookLoopAncestorClockChain`). Everything
      ELSE in the package is discharged green here. */
  lemma DescentPackageDirectFromRes1(
    rer: LW.RegExpRecord, qm: AR.QMap, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
    re: R.regex, S: set<LG.GroupId>, thread: AI.Thread, res1: AReg.Regs,
    A0: nat, g2: nat, body: R.regex, bodycode: RB.code, endl: nat, ngroups: nat,
    ncap: int, nlook: int, nquant: int)
    requires S == PIV.CapIdsInLooks(re)
    requires A0 in NI.TopLookIds(re) && A0 in LTB.LookIds(re)
    requires body == NI.LookBodyOfRE(re, A0) && body == M.VBody(crv, A0 as int)
    requires g2 in S && g2 in PIV.CapIds(body) && g2 !in PIV.CapIdsInLooks(body)   // DIRECT
    // ---- body facts for the landing bridge ----
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
    // ---- res1 <-> thread.look_regs POSITION reconciliation at the top look A0
    //      (produced by M.FLookLoopTopLookCpStableFull) ----
    requires AReg.get_cp(res1, A0 as int) == AReg.get_cp(thread.look_regs, A0 as int)
    requires var cp := AReg.get_cp(res1, A0 as int).value;
             0 <= cp <= |str| && LL.OracleOkSuffix(rer, qm, PIV.InpOfCp(str, cp))
    // ---- SOLE OWED ENGINE RESIDUAL: gate-crossing dominance on thread banks ----
    requires NI.LookPathDom(re, AI.get_idx(thread.look_regs.a_clk, A0 as int), thread.quant_regs.a_clk, A0)
    ensures A0 in NI.TopLookIds(re) && A0 in LTB.LookIds(re)
            && g2 in PIV.CapIds(NI.LookBodyOfRE(re, A0))
            && M.MatchedPosLA(crv, thread.look_regs, A0 as int)
            && NI.LookPathDom(re, AI.get_idx(thread.look_regs.a_clk, A0 as int), thread.quant_regs.a_clk, A0)
            && var lsub := SubFirstLeafAt(rer, crv, str, A0 as int, thread.look_regs);
            lsub.Some? && g2 in lsub.value
  {
    // (1) transport MatchedPosLA + FreshBodyMatch from res1 onto thread.look_regs.
    M.MatchedPosLAFreshBodyCpCong(crv, str, A0 as int, res1, thread.look_regs, ov, ncap, nlook, nquant);
    assert M.MatchedPosLA(crv, thread.look_regs, A0 as int);
    assert M.FreshBodyMatch(crv, str, A0 as int, res1, ov, ncap, nlook, nquant)
        == M.FreshBodyMatch(crv, str, A0 as int, thread.look_regs, ov, ncap, nlook, nquant);
    // the fresh body match on thread.look_regs carries g2 live (transported).
    var rf := M.FreshBodyMatch(crv, str, A0 as int, thread.look_regs, ov, ncap, nlook, nquant);
    assert rf.Some?
           && g2 in PIV.GmOfLive(body, rf.value.capture_regs, rf.value.look_regs, rf.value.quant_regs);
    // cp agreement transports the oracle-suffix / bound side condition to thread.look_regs.
    assert AReg.get_cp(thread.look_regs, A0 as int) == AReg.get_cp(res1, A0 as int);
    // (2) land g2 in SubFirstLeafAt(A0, thread.look_regs) via the DIRECT bridge.
    FreshBodyDirectInSubFirstLeaf(rer, qm, crv, str, ov, A0, thread.look_regs, body, bodycode,
                                  endl, ngroups, g2, ncap, nlook, nquant);
    // (3) g2 in CapIds(LookBodyOfRE(re, A0)) == CapIds(body); LookPathDom is the owed input.
    assert g2 in PIV.CapIds(NI.LookBodyOfRE(re, A0));
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
    // (§2.5b/z3 4.14) recursive nullability predicates + the CIN disjunct's
    // triggered existential storm the solver; all uses here are opaque.
    hide NUL.NonNullableL, NUL.CINullableL, NUL.NoNulledPlusL, AR.NfaRepCinL;
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

  /** Fueled core of `TtLkAtSetQuant`: peel the transparent prefix; the real head
      is an `Areg(Quantified(min>0))` whose first `SetQuantToClock` stamps a
      `Reset`, and the continuation `[Areg(r1),Areg(Quantified(min-1))]+cont` is
      represented at `pc+1` by `QuantForcedContRep` (the do-while seam is now
      satisfiable — `WalkOk` was dropped from `TtLk`). */
  lemma TtLkAtSetQuantCore(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                           tb: LT.Tree, pc: nat, b: BS.LoopBool, acts: LS.Actions, q: int)
    requires AR.NoTrueStamps(code)   // §2.5b stage 2a: look-body code is stamp-free
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
    requires AR.NoTrueStamps(code)   // §2.5b stage 2a: look-body code is stamp-free
    requires TtLk(rer, qm, code, inp, tb, pc, ea)
    requires NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(q, false))
    ensures tb.GroupActionT? && tb.g.Reset?
    ensures TtLk(rer, qm, code, inp, tb.t, pc + 1, ea)
  {
    if (exists acts: LS.Actions, b: BS.LoopBool ::
          AR.ActionsRepL(rer, qm, acts, code, pc)
          && EL.PikeLkActions(acts)
          && ATR.EaOf(b) == ea
          && EL.BoolTreeLk(rer, acts, inp, b, tb)) {
      var acts: LS.Actions, b: BS.LoopBool :|
        AR.ActionsRepL(rer, qm, acts, code, pc)
        && EL.PikeLkActions(acts)
        && ATR.EaOf(b) == ea
        && EL.BoolTreeLk(rer, acts, inp, b, tb);
      TtLkAtSetQuantCore(rer, qm, code, inp, tb, pc, b, acts, q);
    } else {
      // the SQC see-through disjunct gives the shape + child directly
      var q0: int :| NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(q0, false))
                     && q0 in qm.quants
                     && tb.GroupActionT? && tb.g == LG.Reset(qm.quants[q0])
                     && TtLk(rer, qm, code, inp, tb.t, pc + 1, ea);
    }
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
    requires AR.NoTrueStamps(code)   // §2.5b stage 2a: look-body code is stamp-free
    requires AR.ActionsRepL(rer, qm, acts, code, pc)
    requires EL.PikeLkActions(acts)
    requires EL.BoolTreeLk(rer, acts, inp, b, tb)
    requires NR.GetPcRE(code, pc) == Some(RB.Fork(x, y))
    ensures x >= 0 && y >= 0
    ensures tb.Choice? || tb.Progress? || tb == LT.Mismatch
    decreases ATR.MsizeA(acts)
  {
    // (§2.5b/z3 4.14) recursive nullability predicates + the CIN disjunct's
    // triggered existential storm the solver; all uses here are opaque.
    hide NUL.NonNullableL, NUL.CINullableL, NUL.NoNulledPlusL, AR.NfaRepCinL;
    var pcmid: nat :| AR.ActionRepL(rer, qm, acts[0], code, pc, pcmid) && AR.ActionsRepL(rer, qm, acts[1..], code, pcmid);
    assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
    EL.PikeLkActionsTail(acts);
    assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
    assert acts == [acts[0]] + acts[1..];
    assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
    EL.PikeLkActionsConsIff(acts[0], acts[1..]);
    var cont := acts[1..];
    match acts[0]
    case Acheck(strcheck) =>
      // EndLoop != Fork, so the BackForkAt disjunct: pcmid == pc; BoolTreeLk ⇒ Progress / Mismatch
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert AR.BackForkAt(code, pc);
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert x >= 0 && y >= 0;
    case Aclose(_) =>   // pins SetRegisterToCP — not Fork
    case Areg(r0) =>
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert EL.PikeLkRegex(r0);
      match r0
      case Epsilon =>
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert pcmid == pc;
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert EL.BoolTreeLk(rer, cont, inp, b, tb);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert ATR.MsizeA(cont) < ATR.MsizeA(acts);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        TtLkAtForkCore(rer, qm, code, inp, tb, pc, b, cont, x, y);
      case Sequence(r1, r2) =>
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert acts[0] == LS.Areg(L.Sequence(r1, r2));
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert AR.NfaRepL(rer, qm, L.Sequence(r1, r2), code, pc, pcmid);
        var e1: nat :| AR.NfaRepL(rer, qm, r1, code, pc, e1) && AR.NfaRepL(rer, qm, r2, code, e1, pcmid);
        var na := [LS.Areg(r1), LS.Areg(r2)] + cont;
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert na == [LS.Areg(r1)] + ([LS.Areg(r2)] + cont);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        AR.ActionsRepLCons(rer, qm, LS.Areg(r2), cont, code, e1, pcmid);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        AR.ActionsRepLCons(rer, qm, LS.Areg(r1), [LS.Areg(r2)] + cont, code, pc, e1);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert AR.ActionsRepL(rer, qm, na, code, pc);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert EL.PikeLkActions(na) by {
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          EL.PikeLkActionsConsIff(LS.Areg(r2), cont);
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          EL.PikeLkActionsConsIff(LS.Areg(r1), [LS.Areg(r2)] + cont);
        }
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert EL.BoolTreeLk(rer, na, inp, b, tb);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert LS.ActionsRegexSize(acts) == RegSz(r1) + RegSz(r2) + 1 + LS.ActionsRegexSize(cont);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert LS.ActionsRegexSize(na) == RegSz(r1) + RegSz(r2) + LS.ActionsRegexSize(cont);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert ATR.MsizeA(na) < ATR.MsizeA(acts);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        TtLkAtForkCore(rer, qm, code, inp, tb, pc, b, na, x, y);
      case Disjunction(r1, r2) =>
        // Fork(pc+1, e1+1) ⇒ x,y >= 0; BoolTreeLk ⇒ tb.Choice?
        var e1: nat :| NR.GetPcRE(code, pc) == Some(RB.Fork(pc + 1, e1 + 1))
                       && AR.NfaRepL(rer, qm, r1, code, pc + 1, e1)
                       && NR.GetPcRE(code, e1) == Some(RB.Jmp(pcmid))
                       && AR.NfaRepL(rer, qm, r2, code, e1 + 1, pcmid);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert x == pc + 1 && y == e1 + 1;
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert tb.Choice?;
      case Quantified(greedy, min, delta, r1) =>
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert acts[0] == LS.Areg(L.Quantified(greedy, min, delta, r1));
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert AR.NfaRepL(rer, qm, L.Quantified(greedy, min, delta, r1), code, pc, pcmid);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        if min == 0 && delta == LN.NN(0) {
          var em: nat :| AR.NfaRepMinL(rer, qm, 0, r1, code, pc, em)
                         && AR.NfaRepOptL(rer, qm, 0, greedy, r1, code, em, pcmid);
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          NfaRepMinLHeadPin(rer, qm, 0, r1, code, pc, em);
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          NfaRepOptLHeadPin(rer, qm, 0, greedy, r1, code, em, pcmid);
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          assert pcmid == pc;
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          assert AR.ActionsRepL(rer, qm, cont, code, pc);
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          assert EL.BoolTreeLk(rer, cont, inp, b, tb);
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          assert ATR.MsizeA(cont) < ATR.MsizeA(acts);
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          TtLkAtForkCore(rer, qm, code, inp, tb, pc, b, cont, x, y);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        } else if min > 0 {
          // §2.5a: the STRONG head fact -- `min > 0` pins a clock-mark, which
          // refutes the `Fork` we are sitting at. `QuantHeadPinsForkOrSQC`'s
          // `Fork? || SetQuantToClock?` is too weak here.
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          assert min > 0 && delta.Inf? && greedy ==> NUL.NonNullableL(r1) by {   // §2.5b: stamp-free code
            if min > 0 && delta.Inf? && greedy && !NUL.NonNullableL(r1) {
              var emC, e1C := AR.NfaRepLCinInv(rer, qm, greedy, min, r1, code, pc, pcmid);
              var qidC: int :| NR.GetPcRE(code, e1C + 2) == Some(RB.SetQuantToClock(qidC, true));
              assert NR.GetPcRE(code, e1C + 2) != Some(RB.SetQuantToClock(qidC, true));
            }
          }
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          QuantHeadMinPosPinsSQC(rer, qm, greedy, min, delta, r1, code, pc, pcmid);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
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
              AR.NfaRepLStarLoopViews(rer, qm, greedy, r1, code, pc, pcmid);
              if NUL.NonNullableL(r1) {
                var em: nat :| NR.GetPcRE(code, pc) == Some(if greedy then RB.Fork(em, pc + 1) else RB.Fork(pc + 1, em));
              } else {
                var emC, e1C := AR.NfaRepLStarCinInv(rer, qm, r1, code, pc, pcmid);
              }
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
    requires AR.NoTrueStamps(code)   // §2.5b stage 2a: look-body code is stamp-free
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

  lemma QuantsRightClearMono(r: L.Regex, R: set<LG.GroupId>, R2: set<LG.GroupId>)
    requires QuantsRightClear(r, R) && R2 <= R
    ensures QuantsRightClear(r, R2)
    decreases r
  {
    match r
    case Sequence(a, b) =>
      QuantsRightClearMono(a, (set g | g in TopLkDefsList(b)) + R,
                           (set g | g in TopLkDefsList(b)) + R2);
      QuantsRightClearMono(b, R, R2);
    case Disjunction(a, b) =>
      QuantsRightClearMono(a, R, R2); QuantsRightClearMono(b, R, R2);
    case Group(_, rb) => QuantsRightClearMono(rb, R, R2);
    case Quantified(_, _, _, _) =>
    case _ =>
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
  lemma {:isolate_assertions} L3aEndpointAssembly(
    ast: R.regex, re: R.regex, crv: CP.FCompiled, code: RB.code, endl: nat,
    str: string, ov: LOr.OracleView, S: set<LG.GroupId>,
    thread: AI.Thread, leaf: LT.Leaf,
    inits: AI.VmState, cap: AReg.Regs, look: AReg.Regs, quant: AReg.Regs, cdn: LCdn.cdns,
    ncap: int, nlook: int, nquant: int)
    requires T.TransWf(ast) && T.TransWf(re) && re == R.lazy_prefix(ast)
    requires NR.LookBehindFragmentRE(re) && LTB.LookUnique(re)
    requires PIV.QuantUnique(re) && PIV.CapUnique(re)
    requires NR.NoNulledPlusRE(re)   // §2.5b interim: all stamps false
    requires crv == CP.FFullCompilation(ast)
    requires LTB.LookTablesOk(re, crv)
    requires code == CP.compile_to_bytecode(re)
    requires NR.NfaRepRE(re, code, 0, endl) && |code| == endl + 1
    requires NR.GetPcRE(code, endl) == Some(RB.Accept)
    requires forall pc: nat, q: int, b: bool ::
               NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(q, b)) ==> !b
    requires S == PIV.CapIdsInLooks(re)
    requires forall lx: nat :: lx in LTB.LookIds(re) ==> 1 <= lx
    requires ncap == 2 * R.max_group(ast) + 2 && ncap == 2 * R.max_group(re) + 2
    requires nlook == R.max_lookaround(ast) + 1 && nlook == R.max_lookaround(re) + 1
    requires nquant == R.max_quant(ast) + 1 && nquant == R.max_quant(re) + 1
    requires cap == AReg.init_regs(ncap) && look == AReg.init_regs(nlook) && quant == AReg.init_regs(nquant)
    requires inits == AI.FInitState(code, 0, cap, look, quant, 0, AI.cp_context(0, str, LAnc.Forward))
    requires AI.FFindMatch(code, str, inits, ov, LAnc.Forward, cdn).0 == Some(thread)
    requires BestTieLk(re, crv, str, ov, S, Some(leaf), Some(thread), ncap, nlook, nquant)
    // L3b: the leaf value is ORDERED (spec GMClose ordering) — supplied by the
    // caller via FirstLeafOrdered; lets the NormRange conversion collapse.
    requires M.OrderedGm(leaf.1)
    ensures var res := AI.FLookLoop(crv, str, 1, R.max_lookaround(ast),
                                    thread.capture_regs, thread.look_regs, thread.quant_regs, ov);
            res.1 == thread.look_regs
            && leaf.1 == PIV.NormGm(PIV.GmOfLive(re, res.0, thread.look_regs, res.2))
            && CM.ThreadRegsWf(AI.Thread(thread.pc, res.0, res.1, res.2, thread.exit_allowed),
                               ncap, nlook, nquant)
            && M.QuantRegsFinal(AI.Thread(thread.pc, res.0, res.1, res.2, thread.exit_allowed))
  {
    // (§2.5b/z3 4.14) recursive nullability predicates + the CIN disjunct's
    // triggered existential storm the solver; all uses here are opaque.
    hide NUL.NonNullableL, NUL.CINullableL, NUL.NoNulledPlusL, AR.NfaRepCinL;
    // (2026-08-29 E3) the preamble is an OPAQUE block: only the facts below reach the arm's VC.
    var maxlook := *;
    var lk := *;
    var leafgm := *;
    var result := *;
    var ctx0 := *;
    var SqOut := *;
    var ScOut := *;
    var pre := *;
    var Sreg := *;
    var Sq := *;
    opaque
      ensures (forall l: int :: 1 <= l <= maxlook && AReg.get_cp(lk, l).Some? ==>
                                      CM.RegsAgreeInside(thread.capture_regs, AReg.init_regs(ncap), PIV.CaptureRegs(M.VBody(crv, l))))
      ensures (forall l: int :: 1 <= l <= maxlook && AReg.get_cp(lk, l).Some? ==>
                                      CM.RegsAgreeInside(thread.quant_regs, AReg.init_regs(nquant), LKC.QIdsInt(M.VBody(crv, l))))
      ensures (forall l1: int, l2: int ::
                1 <= l1 <= maxlook && 1 <= l2 <= maxlook && l1 != l2
                && AReg.get_cp(lk, l1).Some? && AReg.get_cp(lk, l2).Some? ==>
                  LKC.QIdsInt(M.VBody(crv, l1)) * LKC.QIdsInt(M.VBody(crv, l2)) == {})
      ensures (forall l: int :: 0 <= l < nlook && AReg.get_cp(lk, l).Some? ==> 1 <= l <= maxlook && (l as nat) in LTB.LookIds(re))
      ensures (forall l: int :: 1 <= l <= maxlook && AReg.get_cp(lk, l).Some? ==> M.cp_ctx_ok(crv, str, lk, l))
      ensures (forall l: int :: 1 <= l <= maxlook && AReg.get_cp(lk, l).Some? ==>
                     exists la: R.lookaround, body: R.regex ::
                       LTB.LookEntryOk(crv, l, la, body)
                       && NR.LookFreeRE(body) && NR.PlusFragmentRE(body)
                       && NR.NoNulledPlusRE(body)
                       && PIV.CapUnique(body) && PIV.QuantUnique(body)
                       && PIV.CaptureRegs(body) <= Sreg
                       && (forall q: nat :: q in PIV.QuantIds(body) ==> q in PIV.QuantIdsInLooks(ast))
                       && ((la.NegLookbehind? || la.NegLookahead?) ==> NR.CaptureFreeRE(body)))
      ensures (forall l1: int, l2: int :: (1 <= l1 <= maxlook && 1 <= l2 <= maxlook && l1 != l2
              && AReg.get_cp(lk, l1).Some? && AReg.get_cp(lk, l2).Some?) ==> (PIV.CaptureRegs(M.VBody(crv, l1)) * PIV.CaptureRegs(M.VBody(crv, l2)) == {}))
      ensures (maxlook == R.max_lookaround(ast))
      ensures (lk == thread.look_regs)
      ensures (leafgm == leaf.1)
      ensures (result == AI.FFindMatch(code, str, inits, ov, LAnc.Forward, cdn).0)
      ensures (ctx0 == AI.cp_context(0, str, LAnc.Forward))
      ensures (inits.context.nextchar == AI.get_char(str, 0) && inits.cp == 0)
      ensures (inits.active == [AI.init_thread(cap, look, quant)]
                   && inits.blocked == [] && inits.bestmatch.None?)
      ensures (M.VmQuantFinal(inits))
      ensures (CM.ThreadRegsWf(thread, ncap, nlook, nquant) && M.QuantRegsFinal(thread))
      ensures (SqOut == set q: nat | q in PIV.QuantIdsOutsideLooks(re) :: q as int)
      ensures (ScOut == PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(re)))
      ensures (CM.RegsAgreeOutside(thread.quant_regs, quant, SqOut))
      ensures (CM.RegsAgreeOutside(thread.capture_regs, cap, ScOut))
      ensures (pre == R.Re_quant(R.NonNullable, 0, R.CountedQuant(0, None, false), R.Re_character(R.Dot)))
      ensures (re == R.Re_con(pre, ast))
      ensures (PIV.CapIdsInLooks(re) == PIV.CapIdsInLooks(ast))
      ensures (PIV.QuantIdsInLooks(re) == PIV.QuantIdsInLooks(ast))
      ensures (Sreg == PIV.CaptureRegsSet(PIV.CapIdsInLooks(ast)))
      ensures (Sq == set q: nat | q in PIV.QuantIdsInLooks(ast) :: q as int)
      ensures (forall lx: nat :: lx in LTB.LookIds(re) ==> 1 <= lx <= maxlook)
      ensures (forall c: nat :: c in PIV.CapIdsInLooks(re) ==>
                                      CP.start_reg(c as int) !in ScOut && CP.end_reg(c as int) !in ScOut)
      ensures (forall c: nat :: c in PIV.CapIdsInLooks(ast) ==>
                                      AI.get_idx(thread.capture_regs.a_cp, CP.start_reg(c as int)) == -1
                                      && AI.get_idx(thread.capture_regs.a_clk, CP.start_reg(c as int)) == -1
                                      && AI.get_idx(thread.capture_regs.a_cp, CP.end_reg(c as int)) == -1
                                      && AI.get_idx(thread.capture_regs.a_clk, CP.end_reg(c as int)) == -1)
      ensures (NR.LookBehindFragmentRE(ast) && PIV.QuantUnique(ast))
      ensures (PIV.CapIds(re) == PIV.CapIdsOutsideLooks(re) + PIV.CapIdsInLooks(re))
      ensures (PIV.CapIdsOutsideLooks(re) * PIV.CapIdsInLooks(re) == {})
      ensures (PIV.QuantIdsOutsideLooks(re) * PIV.QuantIdsInLooks(re) == {})
    {
      maxlook := R.max_lookaround(ast);
      lk := thread.look_regs;
      leafgm := leaf.1;
      result := AI.FFindMatch(code, str, inits, ov, LAnc.Forward, cdn).0;
      ctx0 := AI.cp_context(0, str, LAnc.Forward);
      assert inits.context.nextchar == AI.get_char(str, 0) && inits.cp == 0;
      assert |inits.processed.true_set| == RB.size(code) && |inits.processed.false_set| == RB.size(code);
      assert inits.active == [AI.init_thread(cap, look, quant)]
             && inits.blocked == [] && inits.bestmatch.None?;
  
      // ---- winning-thread wf + genuine-start engine facts -------------------
      CM.RegsClocksLEInit(ncap, 0);
      CM.RegsClocksLEInit(nlook, 0);
      CM.RegsClocksLEInit(nquant, 0);
      CM.FInitStateClocksLE(code, 0, cap, look, quant, 0, ctx0);
      CM.FInitStateRegsWf(code, 0, ncap, nlook, nquant, 0, ctx0);
      assert M.VmQuantFinal(inits) by {
        var th0 := AI.init_thread(cap, look, quant);
        assert M.QuantRegsFinal(th0) by {
          forall k ensures AI.get_idx(quant.a_cp, k) < 0 && AI.get_idx(quant.a_clk, k) >= -1 {
            if 0 <= k < |quant.a_cp| { assert quant.a_cp[k] == -1; }
            if 0 <= k < |quant.a_clk| { assert quant.a_clk[k] == -1; }
          }
        }
        forall t2 | t2 in inits.active ensures M.QuantRegsFinal(t2) { assert t2 == th0; }
      }
      M.FFindMatchThreadFacts(code, str, inits, ov, LAnc.Forward, cdn, ncap, nlook, nquant);
      assert {:split_here} true;   // (E3) section-1 sub-batch
      assert CM.ThreadRegsWf(thread, ncap, nlook, nquant) && M.QuantRegsFinal(thread);
  
      // rows / cp-context / stamps / init frames
      M.LookRowsFromTablesL3a(ast, re, crv, code, str, ov, cdn, inits, cap, look, quant,
                              nlook, endl, result);
      M.MainMatchCpCtxOk(crv, code, str, inits, cap, look, quant, nlook, ov, cdn, result);
      M.MainMatchLookClkSet(code, str, inits, cap, look, quant, nlook, ov, cdn, result);
      M.MainMatchBodyQuantsInit(re, code, endl, str, inits, cap, look, quant, ov, cdn, result);
      M.MainMatchInsideCapsInit(re, code, endl, str, inits, cap, look, quant, ov, cdn, result);
      SqOut := set q: nat | q in PIV.QuantIdsOutsideLooks(re) :: q as int;
      ScOut := PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(re));
      assert CM.RegsAgreeOutside(thread.quant_regs, quant, SqOut);
      assert CM.RegsAgreeOutside(thread.capture_regs, cap, ScOut);
  
      // set splits + prefix invisibility
      PIV.CapIdsSplit(re); PIV.QuantIdsSplit(re);
      PIV.CapIdsLooksDisjoint(re); PIV.QuantIdsLooksDisjoint(re);
      pre := R.Re_quant(R.NonNullable, 0, R.CountedQuant(0, None, false), R.Re_character(R.Dot));
      assert re == R.Re_con(pre, ast);
      assert PIV.CapIdsInLooks(re) == PIV.CapIdsInLooks(ast);
      assert PIV.QuantIdsInLooks(re) == PIV.QuantIdsInLooks(ast);
      Sreg := PIV.CaptureRegsSet(PIV.CapIdsInLooks(ast));
      Sq := set q: nat | q in PIV.QuantIdsInLooks(ast) :: q as int;
      LTB.LookIdsLeMax(re);
      assert forall lx: nat :: lx in LTB.LookIds(re) ==> 1 <= lx <= maxlook;
  
      // inside-look slots are never outside-look slots (parity + disjointness)
      assert {:split_here} true;   // (E3) section-1 sub-batch
      assert forall c: nat :: c in PIV.CapIdsInLooks(re) ==>
                                CP.start_reg(c as int) !in ScOut && CP.end_reg(c as int) !in ScOut
      by {
        forall c: nat | c in PIV.CapIdsInLooks(re)
          ensures CP.start_reg(c as int) !in ScOut && CP.end_reg(c as int) !in ScOut
        {
          if CP.start_reg(c as int) in ScOut {
            if CP.start_reg(c as int) in (set cid | cid in PIV.CapIdsOutsideLooks(re) :: CP.start_reg(cid as int)) {
              var cid: nat :| cid in PIV.CapIdsOutsideLooks(re) && CP.start_reg(cid as int) == CP.start_reg(c as int);
              assert cid == c;
              assert c in PIV.CapIdsOutsideLooks(re) * PIV.CapIdsInLooks(re);
            } else {
              var cid: nat :| cid in PIV.CapIdsOutsideLooks(re) && CP.end_reg(cid as int) == CP.start_reg(c as int);
              assert 2 * (cid as int) + 1 == 2 * (c as int);
            }
            assert false;
          }
          if CP.end_reg(c as int) in ScOut {
            if CP.end_reg(c as int) in (set cid | cid in PIV.CapIdsOutsideLooks(re) :: CP.end_reg(cid as int)) {
              var cid: nat :| cid in PIV.CapIdsOutsideLooks(re) && CP.end_reg(cid as int) == CP.end_reg(c as int);
              assert cid == c;
              assert c in PIV.CapIdsOutsideLooks(re) * PIV.CapIdsInLooks(re);
            } else {
              var cid: nat :| cid in PIV.CapIdsOutsideLooks(re) && CP.start_reg(cid as int) == CP.end_reg(c as int);
              assert 2 * (cid as int) == 2 * (c as int) + 1;
            }
            assert false;
          }
        }
      }
      // hence: the winning thread's inside-look capture slots are exactly INIT
      assert {:split_here} true;   // (E3) section-1 sub-batch
      assert forall c: nat :: c in PIV.CapIdsInLooks(ast) ==>
                                AI.get_idx(thread.capture_regs.a_cp, CP.start_reg(c as int)) == -1
                                && AI.get_idx(thread.capture_regs.a_clk, CP.start_reg(c as int)) == -1
                                && AI.get_idx(thread.capture_regs.a_cp, CP.end_reg(c as int)) == -1
                                && AI.get_idx(thread.capture_regs.a_clk, CP.end_reg(c as int)) == -1
      by {
        forall c: nat | c in PIV.CapIdsInLooks(ast)
          ensures AI.get_idx(thread.capture_regs.a_cp, CP.start_reg(c as int)) == -1
                  && AI.get_idx(thread.capture_regs.a_clk, CP.start_reg(c as int)) == -1
                  && AI.get_idx(thread.capture_regs.a_cp, CP.end_reg(c as int)) == -1
                  && AI.get_idx(thread.capture_regs.a_clk, CP.end_reg(c as int)) == -1
        {
          assert c in PIV.CapIdsInLooks(re);
          RL.AInitLaws(ncap);
        }
      }
  
      // per-body unset entries for the value lifts
      assert {:split_here} true;   // (E3) section-1 sub-batch
      assert forall l: int :: 1 <= l <= maxlook && AReg.get_cp(lk, l).Some? ==>
                                CM.RegsAgreeInside(thread.capture_regs, AReg.init_regs(ncap), PIV.CaptureRegs(M.VBody(crv, l)))
      by {
        forall l: int | 1 <= l <= maxlook && AReg.get_cp(lk, l).Some?
          ensures CM.RegsAgreeInside(thread.capture_regs, AReg.init_regs(ncap), PIV.CaptureRegs(M.VBody(crv, l)))
        {
          var la: R.lookaround, body: R.regex :|
            LTB.LookEntryOk(crv, l, la, body)
            && NR.LookFreeRE(body) && NR.PlusFragmentRE(body)
            && PIV.CapUnique(body) && PIV.QuantUnique(body)
            && PIV.CaptureRegs(body) <= Sreg
            && (forall q: nat :: q in PIV.QuantIds(body) ==> q in PIV.QuantIdsInLooks(ast))
            && ((la.NegLookbehind? || la.NegLookahead?) ==> NR.CaptureFreeRE(body));
          assert body == M.VBody(crv, l);
          forall k: int | k in PIV.CaptureRegs(body)
            ensures AI.get_idx(thread.capture_regs.a_cp, k) == AI.get_idx(AReg.init_regs(ncap).a_cp, k)
                    && AI.get_idx(thread.capture_regs.a_clk, k) == AI.get_idx(AReg.init_regs(ncap).a_clk, k)
          {
            var c: nat :| c in PIV.CapIds(body)
                          && (k == CP.start_reg(c as int) || k == CP.end_reg(c as int));
            assert c in PIV.CapIdsInLooks(ast) by {
              assert CP.start_reg(c as int) in PIV.CaptureRegs(body);
              assert CP.start_reg(c as int) in Sreg;
              if CP.start_reg(c as int) in (set cid | cid in PIV.CapIdsInLooks(ast) :: CP.start_reg(cid as int)) {
                var cid: nat :| cid in PIV.CapIdsInLooks(ast) && CP.start_reg(cid as int) == CP.start_reg(c as int);
                assert cid == c;
              } else {
                var cid: nat :| cid in PIV.CapIdsInLooks(ast) && CP.end_reg(cid as int) == CP.start_reg(c as int);
                assert 2 * (cid as int) + 1 == 2 * (c as int);
                assert false;
              }
            }
            RL.AInitLaws(ncap);
          }
        }
      }
      assert {:split_here} true;   // (E3) section-1 sub-batch
      assert forall l: int :: 1 <= l <= maxlook && AReg.get_cp(lk, l).Some? ==>
                                CM.RegsAgreeInside(thread.quant_regs, AReg.init_regs(nquant), LKC.QIdsInt(M.VBody(crv, l)))
      by {
        forall l: int | 1 <= l <= maxlook && AReg.get_cp(lk, l).Some?
          ensures CM.RegsAgreeInside(thread.quant_regs, AReg.init_regs(nquant), LKC.QIdsInt(M.VBody(crv, l)))
        {
          var la: R.lookaround, body: R.regex :|
            LTB.LookEntryOk(crv, l, la, body)
            && NR.LookFreeRE(body) && NR.PlusFragmentRE(body)
            && PIV.CapUnique(body) && PIV.QuantUnique(body)
            && PIV.CaptureRegs(body) <= Sreg
            && (forall q: nat :: q in PIV.QuantIds(body) ==> q in PIV.QuantIdsInLooks(ast))
            && ((la.NegLookbehind? || la.NegLookahead?) ==> NR.CaptureFreeRE(body));
          assert body == M.VBody(crv, l);
          forall k: int | k in LKC.QIdsInt(body)
            ensures AI.get_idx(thread.quant_regs.a_cp, k) == AI.get_idx(AReg.init_regs(nquant).a_cp, k)
                    && AI.get_idx(thread.quant_regs.a_clk, k) == AI.get_idx(AReg.init_regs(nquant).a_clk, k)
          {
            assert k >= 0 && (k as nat) in PIV.QuantIds(body);
            assert (k as nat) in PIV.QuantIdsInLooks(ast);
            assert k !in SqOut by {
              if k in SqOut {
                var q2: nat :| q2 in PIV.QuantIdsOutsideLooks(re) && q2 as int == k;
                assert q2 in PIV.QuantIdsOutsideLooks(re) * PIV.QuantIdsInLooks(re);
              }
            }
            RL.AInitLaws(nquant);
          }
        }
      }
      // pairwise quant disjointness across matched lids
      assert {:split_here} true;   // (E3) section-1 sub-batch
      assert forall l1: int, l2: int ::
          1 <= l1 <= maxlook && 1 <= l2 <= maxlook && l1 != l2
          && AReg.get_cp(lk, l1).Some? && AReg.get_cp(lk, l2).Some? ==>
            LKC.QIdsInt(M.VBody(crv, l1)) * LKC.QIdsInt(M.VBody(crv, l2)) == {}
      by {
        forall l1: int, l2: int |
          1 <= l1 <= maxlook && 1 <= l2 <= maxlook && l1 != l2
          && AReg.get_cp(lk, l1).Some? && AReg.get_cp(lk, l2).Some?
          ensures LKC.QIdsInt(M.VBody(crv, l1)) * LKC.QIdsInt(M.VBody(crv, l2)) == {}
        {
          assert (l1 as nat) in LTB.LookIds(re) && (l2 as nat) in LTB.LookIds(re);
          OE.LmOfDom(re);
          assert l1 in OE.LmOf(re) && l2 in OE.LmOf(re);
          var la1, b1, la2, b2 := M.LmOfBodiesDisjoint(re, crv, l1, l2);
          assert b1 == M.VBody(crv, l1) && b2 == M.VBody(crv, l2);
          forall k: int | k in LKC.QIdsInt(b1) * LKC.QIdsInt(b2) ensures false {
            assert (k as nat) in PIV.QuantIds(b1) * PIV.QuantIds(b2);
          }
        }
      }
  
      // (E3) exported facts for the lifts/FORWARD/REVERSE sections (lemma posts + call-site preconditions)
      assert NR.LookBehindFragmentRE(ast) && PIV.QuantUnique(ast);
      assert PIV.CapIds(re) == PIV.CapIdsOutsideLooks(re) + PIV.CapIdsInLooks(re);
      assert PIV.CapIdsOutsideLooks(re) * PIV.CapIdsInLooks(re) == {};
      assert PIV.QuantIdsOutsideLooks(re) * PIV.QuantIdsInLooks(re) == {};
      assert forall l: int :: 0 <= l < nlook && AReg.get_cp(lk, l).Some? ==> 1 <= l <= maxlook && (l as nat) in LTB.LookIds(re);
      assert forall l: int :: 1 <= l <= maxlook && AReg.get_cp(lk, l).Some? ==> M.cp_ctx_ok(crv, str, lk, l);
      assert forall l: int :: 1 <= l <= maxlook && AReg.get_cp(lk, l).Some? ==>
               exists la: R.lookaround, body: R.regex ::
                 LTB.LookEntryOk(crv, l, la, body)
                 && NR.LookFreeRE(body) && NR.PlusFragmentRE(body)
                 && NR.NoNulledPlusRE(body)
                 && PIV.CapUnique(body) && PIV.QuantUnique(body)
                 && PIV.CaptureRegs(body) <= Sreg
                 && (forall q: nat :: q in PIV.QuantIds(body) ==> q in PIV.QuantIdsInLooks(ast))
                 && ((la.NegLookbehind? || la.NegLookahead?) ==> NR.CaptureFreeRE(body));
      // (E3) the two-lid capture-register disjointness (FLookLoopValueLift's precondition), proved once here
      forall l1: int, l2: int |
        1 <= l1 <= maxlook && 1 <= l2 <= maxlook && l1 != l2
        && AReg.get_cp(lk, l1).Some? && AReg.get_cp(lk, l2).Some?
        ensures PIV.CaptureRegs(M.VBody(crv, l1)) * PIV.CaptureRegs(M.VBody(crv, l2)) == {}
      {
        assert (l1 as nat) in LTB.LookIds(re) && (l2 as nat) in LTB.LookIds(re);
        OE.LmOfDom(re);
        assert l1 in OE.LmOf(re) && l2 in OE.LmOf(re);
        var la1, b1, la2, b2 := M.LmOfBodiesDisjoint(re, crv, l1, l2);
        assert b1 == M.VBody(crv, l1) && b2 == M.VBody(crv, l2);
        PIV.CaptureRegsDisjoint(b1, b2);
      }
    }
    assert {:split_here} true;   // (E3) section boundary: its own assertion batch
    // ---- run the lifts and frames ----------------------------------------
    // (2026-08-29 E3) the preamble is an OPAQUE block: only the facts below reach the arm's VC.
    var qtF := *;
    var res := *;
    var res0 := *;
    var res2 := *;
    opaque
      ensures (forall l: int :: 1 <= l <= maxlook && AReg.get_cp(lk, l).Some? ==>
                     exists la: R.lookaround, body: R.regex ::
                       LTB.LookEntryOk(crv, l, la, body)
                       && NR.LookFreeRE(body) && NR.PlusFragmentRE(body)
                       && NR.NoNulledPlusRE(body)
                       && PIV.CapUnique(body) && PIV.QuantUnique(body)
                       && PIV.CaptureRegs(body) <= Sreg
                       && (forall q: nat :: q in PIV.QuantIds(body) ==> q in PIV.QuantIdsInLooks(ast))
                       && ((la.NegLookbehind? || la.NegLookahead?) ==> NR.CaptureFreeRE(body)))
      ensures (forall l: int :: 1 <= l <= maxlook && AReg.get_cp(lk, l).Some? ==> CM.RegsAgreeInside(thread.capture_regs, AReg.init_regs(ncap), PIV.CaptureRegs(M.VBody(crv, l))))
      ensures (forall l1: int, l2: int :: 1 <= l1 <= maxlook && 1 <= l2 <= maxlook && l1 != l2 && AReg.get_cp(lk, l1).Some? && AReg.get_cp(lk, l2).Some? ==> PIV.CaptureRegs(M.VBody(crv, l1)) * PIV.CaptureRegs(M.VBody(crv, l2)) == {})
      ensures (forall l: int :: 1 <= l <= maxlook && AReg.get_cp(lk, l).Some? ==> M.cp_ctx_ok(crv, str, lk, l))
      ensures (qtF == thread.quant_regs)
      ensures ((forall k :: AI.get_idx(qtF.a_cp, k) < 0) && (forall k :: AI.get_idx(qtF.a_clk, k) >= -1))
      ensures (ncap >= 0 && nlook >= 0 && nquant >= 0)
      ensures (NR.LookBehindFragmentRE(ast) && PIV.QuantUnique(ast))
      ensures ((forall k :: AI.get_idx(qtF.a_cp, k) < 0) && (forall k :: AI.get_idx(qtF.a_clk, k) >= -1))
      ensures (|qtF.a_cp| == nquant && |qtF.a_clk| == nquant)
      ensures (|thread.capture_regs.a_cp| == ncap && |thread.capture_regs.a_clk| == ncap && PIV.CapRegWf(thread.capture_regs))
      ensures (|lk.a_cp| == nlook && |lk.a_clk| == nlook)
      ensures (res == AI.FLookLoop(crv, str, 1, maxlook, thread.capture_regs, lk, qtF, ov))
      ensures (res0 == res.0)
      ensures (res2 == res.2)
      ensures (res.1 == lk)
      ensures (CM.RegsAgreeOutside(res0, thread.capture_regs, Sreg))
      ensures (CM.RegsAgreeOutside(res2, qtF, Sq))
      ensures (M.FLookLoopValueOk(crv, str, res0, 1, maxlook, lk, ov, ncap, nlook, nquant))
      ensures (M.FLookLoopQuantValueOk(crv, str, res2, 1, maxlook, lk, ov, ncap, nlook, nquant))
      ensures (PIV.CapRegWf(res0) && |res0.a_cp| == ncap && |res0.a_clk| == ncap)
      ensures (|res2.a_cp| == nquant && |res2.a_clk| == nquant)
      ensures ((forall k :: AI.get_idx(res2.a_cp, k) < 0) && (forall k :: AI.get_idx(res2.a_clk, k) >= -1))
      ensures (forall c: nat :: c in PIV.CapIdsOutsideLooks(re) ==>
                                      AI.get_idx(res0.a_cp, CP.start_reg(c as int)) == AI.get_idx(thread.capture_regs.a_cp, CP.start_reg(c as int))
                                      && AI.get_idx(res0.a_clk, CP.start_reg(c as int)) == AI.get_idx(thread.capture_regs.a_clk, CP.start_reg(c as int)))
      ensures (forall q: nat :: q in PIV.QuantIdsOutsideLooks(re) ==>
                                      AI.get_idx(res2.a_clk, q as int) == AI.get_idx(qtF.a_clk, q as int))
    {
      qtF := thread.quant_regs;
      assert (forall k :: AI.get_idx(qtF.a_cp, k) < 0) && (forall k :: AI.get_idx(qtF.a_clk, k) >= -1);
      // (E3) pins: FLookLoopValueLift's preconditions, one assert each
      assert ncap >= 0 && nlook >= 0 && nquant >= 0;
      assert NR.LookBehindFragmentRE(ast) && PIV.QuantUnique(ast);
      assert (forall k :: AI.get_idx(qtF.a_cp, k) < 0) && (forall k :: AI.get_idx(qtF.a_clk, k) >= -1);
      assert |qtF.a_cp| == nquant && |qtF.a_clk| == nquant;
      assert |thread.capture_regs.a_cp| == ncap && |thread.capture_regs.a_clk| == ncap && PIV.CapRegWf(thread.capture_regs);
      assert |lk.a_cp| == nlook && |lk.a_clk| == nlook;
      assert forall l: int :: 1 <= l <= maxlook && AReg.get_cp(lk, l).Some? ==>
               exists la: R.lookaround, body: R.regex ::
                 LTB.LookEntryOk(crv, l, la, body)
                 && NR.LookFreeRE(body) && NR.PlusFragmentRE(body)
                 && NR.NoNulledPlusRE(body)
                 && PIV.CapUnique(body) && PIV.QuantUnique(body)
                 && PIV.CaptureRegs(body) <= Sreg
                 && (forall q: nat :: q in PIV.QuantIds(body) ==> q in PIV.QuantIdsInLooks(ast))
                 && ((la.NegLookbehind? || la.NegLookahead?) ==> NR.CaptureFreeRE(body));
      assert forall l: int :: 1 <= l <= maxlook && AReg.get_cp(lk, l).Some? ==> CM.RegsAgreeInside(thread.capture_regs, AReg.init_regs(ncap), PIV.CaptureRegs(M.VBody(crv, l)));
      assert forall l1: int, l2: int :: 1 <= l1 <= maxlook && 1 <= l2 <= maxlook && l1 != l2 && AReg.get_cp(lk, l1).Some? && AReg.get_cp(lk, l2).Some? ==> PIV.CaptureRegs(M.VBody(crv, l1)) * PIV.CaptureRegs(M.VBody(crv, l2)) == {};
      assert forall l: int :: 1 <= l <= maxlook && AReg.get_cp(lk, l).Some? ==> M.cp_ctx_ok(crv, str, lk, l);
      assert {:split_here} true;   // (E3) lifts sub-batch: pins | lifts
      M.FLookLoopValueLift(crv, str, 1, maxlook, thread.capture_regs, lk, qtF, ov,
                           ast, Sreg, ncap, nlook, nquant);
      M.FLookLoopQuantValueLift(crv, str, 1, maxlook, thread.capture_regs, lk, qtF, ov,
                                ast, Sq, ncap, nlook, nquant);
      M.FLookLoopCaptureFrame(crv, str, 1, maxlook, thread.capture_regs, lk, qtF, ov, ast, Sreg);
      M.FLookLoopQuantFrame(crv, str, 1, maxlook, thread.capture_regs, lk, qtF, ov, ast, Sq);
      res := AI.FLookLoop(crv, str, 1, maxlook, thread.capture_regs, lk, qtF, ov);
      res0 := res.0;
      res2 := res.2;
      assert res.1 == lk;
      assert CM.RegsAgreeOutside(res0, thread.capture_regs, Sreg);
      assert CM.RegsAgreeOutside(res2, qtF, Sq);
      assert M.FLookLoopValueOk(crv, str, res0, 1, maxlook, lk, ov, ncap, nlook, nquant);
      assert M.FLookLoopQuantValueOk(crv, str, res2, 1, maxlook, lk, ov, ncap, nlook, nquant);
      assert PIV.CapRegWf(res0) && |res0.a_cp| == ncap && |res0.a_clk| == ncap;
      assert |res2.a_cp| == nquant && |res2.a_clk| == nquant;
      assert (forall k :: AI.get_idx(res2.a_cp, k) < 0) && (forall k :: AI.get_idx(res2.a_clk, k) >= -1);
  
      // outside-look agreements (for the transports and the value bridge)
      assert {:split_here} true;   // (E3) lifts sub-batch: lifts | frame asserts
      assert forall c: nat :: c in PIV.CapIdsOutsideLooks(re) ==>
                                AI.get_idx(res0.a_cp, CP.start_reg(c as int)) == AI.get_idx(thread.capture_regs.a_cp, CP.start_reg(c as int))
                                && AI.get_idx(res0.a_clk, CP.start_reg(c as int)) == AI.get_idx(thread.capture_regs.a_clk, CP.start_reg(c as int))
      by {
        forall c: nat | c in PIV.CapIdsOutsideLooks(re)
          ensures AI.get_idx(res0.a_cp, CP.start_reg(c as int)) == AI.get_idx(thread.capture_regs.a_cp, CP.start_reg(c as int))
                  && AI.get_idx(res0.a_clk, CP.start_reg(c as int)) == AI.get_idx(thread.capture_regs.a_clk, CP.start_reg(c as int))
        {
          assert CP.start_reg(c as int) !in Sreg by {
            if CP.start_reg(c as int) in Sreg {
              if CP.start_reg(c as int) in (set cid | cid in PIV.CapIdsInLooks(ast) :: CP.start_reg(cid as int)) {
                var cid: nat :| cid in PIV.CapIdsInLooks(ast) && CP.start_reg(cid as int) == CP.start_reg(c as int);
                assert cid == c;
                assert c in PIV.CapIdsOutsideLooks(re) * PIV.CapIdsInLooks(re);
              } else {
                var cid: nat :| cid in PIV.CapIdsInLooks(ast) && CP.end_reg(cid as int) == CP.start_reg(c as int);
                assert 2 * (cid as int) + 1 == 2 * (c as int);
              }
              assert false;
            }
          }
        }
      }
      assert forall q: nat :: q in PIV.QuantIdsOutsideLooks(re) ==>
                                AI.get_idx(res2.a_clk, q as int) == AI.get_idx(qtF.a_clk, q as int)
      by {
        forall q: nat | q in PIV.QuantIdsOutsideLooks(re)
          ensures AI.get_idx(res2.a_clk, q as int) == AI.get_idx(qtF.a_clk, q as int)
        {
          assert (q as int) !in Sq by {
            if (q as int) in Sq {
              var q2: nat :| q2 in PIV.QuantIdsInLooks(ast) && q2 as int == q as int;
              assert q2 == q;
              assert q in PIV.QuantIdsOutsideLooks(re) * PIV.QuantIdsInLooks(re);
            }
          }
        }
      }
    }
    assert {:split_here} true;   // (E3) section boundary: its own assertion batch

    // ---- FORWARD: every leaf-present inside-S group is reconstructed ------
    assert GmtTieInside(crv, str, ov, thread, leafgm, S, ncap, nlook, nquant);
    assert LookNestOkT(re, S, leafgm, thread);
    assert LookNestBackT(re, crv, str, ov, S, leafgm, thread, ncap, nlook, nquant);
    opaque
      ensures forall g: LG.GroupId :: g in S && g in leafgm ==>
                g in PIV.GmOfLive(re, res0, lk, res2)
                && leafgm[g] == PIV.NormRange(PIV.GmOfLive(re, res0, lk, res2)[g])
    {
      forall g: LG.GroupId | g in S && g in leafgm
        ensures g in PIV.GmOfLive(re, res0, lk, res2)
                && leafgm[g] == PIV.NormRange(PIV.GmOfLive(re, res0, lk, res2)[g])
      {
        var l: int :| 0 <= l < nlook
                      && g in PIV.CapIds(M.VBody(crv, l))
                      && M.MatchedPosLA(crv, lk, l)
                      && var rf0 := M.FreshBodyMatch(crv, str, l, lk, ov, ncap, nlook, nquant);
                      rf0.Some?
                      && var gmb := PIV.GmOfLive(M.VBody(crv, l), rf0.value.capture_regs,
                                                 rf0.value.look_regs, rf0.value.quant_regs);
                      var looktype := if 0 <= l < |crv.f_look_types| then crv.f_look_types[l] else R.Lookahead;
                      g in gmb && leafgm[g] == (if looktype.Lookbehind? then LBV.SwapRange(gmb[g]) else gmb[g]);
        var rf := M.FreshBodyMatch(crv, str, l, lk, ov, ncap, nlook, nquant);
        assert AReg.get_cp(lk, l).Some?;
        assert l >= 0 && (l as nat) in LTB.LookIds(re);
        assert 1 <= l <= maxlook;
        var la: R.lookaround, body: R.regex :|
          LTB.LookEntryOk(crv, l, la, body)
          && NR.LookFreeRE(body) && NR.PlusFragmentRE(body)
          && PIV.CapUnique(body) && PIV.QuantUnique(body)
          && PIV.CaptureRegs(body) <= Sreg
          && (forall q: nat :: q in PIV.QuantIds(body) ==> q in PIV.QuantIdsInLooks(ast))
          && ((la.NegLookbehind? || la.NegLookahead?) ==> NR.CaptureFreeRE(body));
        assert body == M.VBody(crv, l);
        NI.LookBodyOfTablesTie(re, crv, l as nat);
        var la2: R.lookaround :| LTB.LookEntryOk(crv, l, la2, NI.LookBodyOfRE(re, l as nat));
        assert NI.LookBodyOfRE(re, l as nat) == body;
        NR.PlusIsLookBehindFragmentRE(body);
        assert g in PIV.CapIds(re);
        assert M.cp_ctx_ok(crv, str, lk, l);
        NI.NoNulledPlusLookBody(re, l as nat);   // §2.5b interim: NoNulledPlusRE(body)
        FreshBodyMatchCapWf(crv, str, l, lk, ov, ncap, nlook, nquant, body);
        // carrier forward at l
        assert NI.LookPathPresent(re, thread.capture_regs.a_clk, qtF.a_clk, -1, l as nat)
               && AI.get_idx(lk.a_clk, l) >= 0
               && AI.get_idx(lk.a_clk, l) >= NI.MxAtLidLk(re, qtF.a_clk, -1, l as nat) by {
          assert g in S && g in leafgm && g in PIV.CapIds(NI.LookBodyOfRE(re, l as nat));
        }
        // outer transport to the reconstructed banks
        NI.LookPathPresentAgree(re, thread.capture_regs.a_clk, qtF.a_clk,
                                res0.a_clk, res2.a_clk, -1, l as nat);
        assert NI.LookPathPresent(re, res0.a_clk, res2.a_clk, -1, l as nat);
        assert AI.get_idx(lk.a_clk, l) >= NI.MxAtLidLk(re, res2.a_clk, -1, l as nat);
        // body side on the fresh banks, transported to the reconstructed banks
        assert CM.RegsAgreeInside(res0, rf.value.capture_regs, PIV.CaptureRegs(body));
        PIV.BodyPathPresentLk(body, rf.value.capture_regs, rf.value.look_regs, rf.value.quant_regs, g);
        assert CM.RegsAgreeInside(res2, rf.value.quant_regs, LKC.QIdsInt(body));
        NI.LookFreeNoLookIdsN(body);
        assert forall c: nat :: c in PIV.CapIds(body) ==>
                                  AI.get_idx(AReg.as_arrays(rf.value.capture_regs).1, CP.start_reg(c as int))
                                  == AI.get_idx(res0.a_clk, CP.start_reg(c as int)) by {
          forall c: nat | c in PIV.CapIds(body)
            ensures AI.get_idx(AReg.as_arrays(rf.value.capture_regs).1, CP.start_reg(c as int))
                 == AI.get_idx(res0.a_clk, CP.start_reg(c as int))
          {
            assert CP.start_reg(c as int) in PIV.CaptureRegs(body);
          }
        }
        assert forall q: nat :: q in PIV.QuantIds(body) ==>
                                  AI.get_idx(AReg.as_arrays(rf.value.quant_regs).1, q as int)
                                  == AI.get_idx(res2.a_clk, q as int) by {
          forall q: nat | q in PIV.QuantIds(body)
            ensures AI.get_idx(AReg.as_arrays(rf.value.quant_regs).1, q as int)
                 == AI.get_idx(res2.a_clk, q as int)
          {
            assert (q as int) in LKC.QIdsInt(body);
          }
        }
        NI.PathPresentLkAgree(body,
                              AReg.as_arrays(rf.value.capture_regs).1, AReg.as_arrays(rf.value.look_regs).1,
                              AReg.as_arrays(rf.value.quant_regs).1,
                              res0.a_clk, lk.a_clk, res2.a_clk, -1, g);
        assert PIV.PathPresentLk(body, res0.a_clk, lk.a_clk, res2.a_clk, -1, g);
        NI.LookPathCompose(re, body, res0.a_clk, lk.a_clk, res2.a_clk, -1, l as nat, g);
        assert PIV.PathPresentLk(re, res0.a_clk, lk.a_clk, res2.a_clk, -1, g);
        assert PIV.MxAtGidLk(re, res0.a_clk, lk.a_clk, res2.a_clk, -1, g)
            == PIV.MxAtGidLk(body, res0.a_clk, lk.a_clk, res2.a_clk, -1, g);
        assert AI.get_idx(res0.a_clk, CP.start_reg(g as int))
            == AI.get_idx(AReg.as_arrays(rf.value.capture_regs).1, CP.start_reg(g as int)) by {
          assert CP.start_reg(g as int) in PIV.CaptureRegs(body);
        }
        assert AI.get_idx(res0.a_clk, CP.start_reg(g as int))
            >= PIV.MxAtGidLk(re, res0.a_clk, lk.a_clk, res2.a_clk, -1, g) by {
          assert PIV.MxAtGidLk(body,
                               AReg.as_arrays(rf.value.capture_regs).1, AReg.as_arrays(rf.value.look_regs).1,
                               AReg.as_arrays(rf.value.quant_regs).1, -1, g)
              == PIV.MxAtGidLk(body, res0.a_clk, lk.a_clk, res2.a_clk, -1, g);
        }
        assert AReg.as_arrays(res0).1 == res0.a_clk && AReg.as_arrays(lk).1 == lk.a_clk
               && AReg.as_arrays(res2).1 == res2.a_clk;
        InsidePresentResBridge(re, body, crv, str, ov, thread, leafgm, res0, res2, l,
                               ncap, nlook, nquant, g);
        // InsidePresentResBridge gives the LOOK-TYPE swap; leaf-orderedness turns it
        // into the POSITIONAL NormRange.
        var looktype := if 0 <= l < |crv.f_look_types| then crv.f_look_types[l] else R.Lookahead;
        assert leafgm[g].endIdx.Some? ==> leafgm[g].startIdx <= leafgm[g].endIdx.value;  // OrderedGm
        NormRangeFromSwap(PIV.GmOfLive(re, res0, lk, res2)[g], leafgm[g], looktype.Lookbehind?);
      }
    }
    assert {:split_here} true;   // (E3) section boundary: its own assertion batch

    // ---- REVERSE: the reconstruction invents no group the leaf lacks ------
    opaque
      ensures forall g: LG.GroupId :: g in S && g in PIV.GmOfLive(re, res0, lk, res2) ==> g in leafgm
    {
      forall g: LG.GroupId | g in S && g in PIV.GmOfLive(re, res0, lk, res2)
        ensures g in leafgm
      {
        NI.CapIdsInLooksHasOwner(re, g);
        var lid: nat :| lid in LTB.LookIds(re) && g in PIV.CapIds(NI.LookBodyOfRE(re, lid));
        var LB := NI.LookBodyOfRE(re, lid);
        NI.LookBodyOfTablesTie(re, crv, lid);
        var laT: R.lookaround :| LTB.LookEntryOk(crv, lid as int, laT, LB);
        assert M.VBody(crv, lid as int) == LB;
        assert 1 <= lid <= maxlook;
        NI.LookBodyOfFragment(re, lid);
        NR.PlusIsLookBehindFragmentRE(LB);
        assert g in PIV.CapIds(re);
        if AReg.get_cp(lk, lid as int).None? {
          // untouched owner: the slot is still INIT, so g cannot be present
          var SpM := set lm: int, k: int |
            1 <= lm <= maxlook && AReg.get_cp(lk, lm).Some? && k in PIV.CaptureRegs(M.VBody(crv, lm)) :: k;
          M.FLookLoopCaptureFrame(crv, str, 1, maxlook, thread.capture_regs, lk, qtF, ov, ast, SpM);
          assert CM.RegsAgreeOutside(res0, thread.capture_regs, SpM);
          assert CP.start_reg(g as int) !in SpM by {
            if CP.start_reg(g as int) in SpM {
              var lm: int :| 1 <= lm <= maxlook && AReg.get_cp(lk, lm).Some?
                             && CP.start_reg(g as int) in PIV.CaptureRegs(M.VBody(crv, lm));
              assert (lm as nat) in LTB.LookIds(re);
              NI.LookBodyOfTablesTie(re, crv, lm as nat);
              var laM: R.lookaround :| LTB.LookEntryOk(crv, lm, laM, NI.LookBodyOfRE(re, lm as nat));
              assert M.VBody(crv, lm) == NI.LookBodyOfRE(re, lm as nat);
              var c: nat :| c in PIV.CapIds(M.VBody(crv, lm))
                            && (CP.start_reg(g as int) == CP.start_reg(c as int)
                                || CP.start_reg(g as int) == CP.end_reg(c as int));
              assert c == g by {
                if CP.start_reg(g as int) == CP.end_reg(c as int) {
                  assert 2 * (g as int) == 2 * (c as int) + 1;
                }
              }
              assert (lm as nat) == lid by {
                if (lm as nat) != lid {
                  NI.LookBodiesCapsDisjoint(re, lid, lm as nat);
                  assert g in PIV.CapIds(NI.LookBodyOfRE(re, lid))
                              * PIV.CapIds(NI.LookBodyOfRE(re, lm as nat));
                }
              }
              assert AReg.get_cp(lk, lid as int).Some?;
              assert false;
            }
          }
          assert AI.get_idx(res0.a_cp, CP.start_reg(g as int))
              == AI.get_idx(thread.capture_regs.a_cp, CP.start_reg(g as int));
          assert g in PIV.CapIdsInLooks(ast);
          assert AI.get_idx(res0.a_cp, CP.start_reg(g as int)) == -1;
          assert AReg.as_arrays(res0).0 == res0.a_cp;
          M.GmOfLiveInsideLookAbsentEq(re, LB, res0, lk, res2, res0, lk, res2, g);
          assert false;
        } else {
          var la: R.lookaround, body: R.regex :|
            LTB.LookEntryOk(crv, lid as int, la, body)
            && NR.LookFreeRE(body) && NR.PlusFragmentRE(body)
            && PIV.CapUnique(body) && PIV.QuantUnique(body)
            && PIV.CaptureRegs(body) <= Sreg
            && (forall q: nat :: q in PIV.QuantIds(body) ==> q in PIV.QuantIdsInLooks(ast))
            && ((la.NegLookbehind? || la.NegLookahead?) ==> NR.CaptureFreeRE(body));
          assert body == LB;
          // L3b: the matched lid is a POSITIVE capturing look — lookAHEAD or lookBEHIND
          // (negatives are capture-free, so g in CapIds(body) refutes them). This pin keeps
          // the MatchedPosLA VC cheap; without it the SMT search blows up (2 timeouts).
          assert la.Lookahead? || la.Lookbehind? by {
            if !(la.Lookahead? || la.Lookbehind?) {
              assert NR.CaptureFreeRE(body);
              PIV.CaptureFreeNoCapIds(body);
              assert g in PIV.CapIds(body);
            }
          }
          assert M.MatchedPosLA(crv, lk, lid as int) by {
            assert 0 <= (lid as int) < |crv.f_look_types|;
            assert crv.f_look_types[lid as int] == la;
            assert AReg.get_cp(lk, lid as int).Some?;
            assert la.Lookahead? || la.Lookbehind?;
          }
          assert forall c: nat :: c in PIV.CapIds(re) && AI.get_idx(res0.a_clk, CP.start_reg(c as int)) < 0
                                  ==> AI.get_idx(res0.a_cp, CP.start_reg(c as int)) < 0;
          PIV.GmOfLivePresenceExtractLk(re, res0, lk, res2, g);
          assert AReg.as_arrays(res0).1 == res0.a_clk && AReg.as_arrays(lk).1 == lk.a_clk
                 && AReg.as_arrays(res2).1 == res2.a_clk && AReg.as_arrays(res0).0 == res0.a_cp;
          assert PIV.PathPresentLk(re, res0.a_clk, lk.a_clk, res2.a_clk, -1, g);
          NI.LookPathDecompose(re, LB, res0.a_clk, lk.a_clk, res2.a_clk, -1, lid, g);
          assert NI.LookPathPresent(re, res0.a_clk, res2.a_clk, -1, lid);
          var lcv := AI.get_idx(lk.a_clk, lid as int);
          assert lcv >= 0 && lcv >= NI.MxAtLidLk(re, res2.a_clk, -1, lid);
          NI.LookPathPresentAgree(re, res0.a_clk, res2.a_clk,
                                  thread.capture_regs.a_clk, qtF.a_clk, -1, lid);
          assert NI.LookPathPresent(re, thread.capture_regs.a_clk, qtF.a_clk, -1, lid);
          assert lcv >= NI.MxAtLidLk(re, qtF.a_clk, -1, lid);
          NI.LookPathDomIntro(re, thread.capture_regs.a_clk, qtF.a_clk, -1, lid, lcv);
          assert NI.LookPathDom(re, lcv, qtF.a_clk, lid);
          var rf := M.FreshBodyMatch(crv, str, lid as int, lk, ov, ncap, nlook, nquant);
          assert rf.Some? by {
            if rf.None? {
              assert CM.RegsAgreeInside(res0, AReg.init_regs(ncap), PIV.CaptureRegs(LB));
              assert CP.start_reg(g as int) in PIV.CaptureRegs(LB);
              RL.AInitLaws(ncap);
              assert AI.get_idx(res0.a_cp, CP.start_reg(g as int)) == -1;
              assert AI.get_idx(res0.a_cp, CP.start_reg(g as int)) >= 0;
            }
          }
          assert CM.RegsAgreeInside(res0, rf.value.capture_regs, PIV.CaptureRegs(LB));
          assert CM.RegsAgreeInside(res2, rf.value.quant_regs, LKC.QIdsInt(LB));
          NI.LookFreeNoLookIdsN(LB);
          assert forall c: nat :: c in PIV.CapIds(LB) ==>
                                    AI.get_idx(res0.a_clk, CP.start_reg(c as int))
                                    == AI.get_idx(AReg.as_arrays(rf.value.capture_regs).1, CP.start_reg(c as int)) by {
            forall c: nat | c in PIV.CapIds(LB)
              ensures AI.get_idx(res0.a_clk, CP.start_reg(c as int))
                   == AI.get_idx(AReg.as_arrays(rf.value.capture_regs).1, CP.start_reg(c as int))
            {
              assert CP.start_reg(c as int) in PIV.CaptureRegs(LB);
            }
          }
          assert forall q: nat :: q in PIV.QuantIds(LB) ==>
                                    AI.get_idx(res2.a_clk, q as int)
                                    == AI.get_idx(AReg.as_arrays(rf.value.quant_regs).1, q as int) by {
            forall q: nat | q in PIV.QuantIds(LB)
              ensures AI.get_idx(res2.a_clk, q as int)
                   == AI.get_idx(AReg.as_arrays(rf.value.quant_regs).1, q as int)
            {
              assert (q as int) in LKC.QIdsInt(LB);
            }
          }
          NI.PathPresentLkAgree(LB, res0.a_clk, lk.a_clk, res2.a_clk,
                                AReg.as_arrays(rf.value.capture_regs).1, AReg.as_arrays(rf.value.look_regs).1,
                                AReg.as_arrays(rf.value.quant_regs).1, -1, g);
          assert PIV.PathPresentLk(LB,
                                   AReg.as_arrays(rf.value.capture_regs).1, AReg.as_arrays(rf.value.look_regs).1,
                                   AReg.as_arrays(rf.value.quant_regs).1, -1, g);
          assert CP.start_reg(g as int) in PIV.CaptureRegs(LB);
          assert AI.get_idx(AReg.as_arrays(rf.value.capture_regs).1, CP.start_reg(g as int))
              == AI.get_idx(res0.a_clk, CP.start_reg(g as int));
          assert AI.get_idx(AReg.as_arrays(rf.value.capture_regs).0, CP.start_reg(g as int))
              == AI.get_idx(res0.a_cp, CP.start_reg(g as int));
          assert AI.get_idx(res0.a_cp, CP.start_reg(g as int)) >= 0;
          assert AI.get_idx(AReg.as_arrays(rf.value.capture_regs).1, CP.start_reg(g as int))
              >= PIV.MxAtGidLk(LB,
                               AReg.as_arrays(rf.value.capture_regs).1, AReg.as_arrays(rf.value.look_regs).1,
                               AReg.as_arrays(rf.value.quant_regs).1, -1, g) by {
            assert AI.get_idx(res0.a_clk, CP.start_reg(g as int))
                >= PIV.MxAtGidLk(re, res0.a_clk, lk.a_clk, res2.a_clk, -1, g);
            assert PIV.MxAtGidLk(re, res0.a_clk, lk.a_clk, res2.a_clk, -1, g)
                == PIV.MxAtGidLk(LB, res0.a_clk, lk.a_clk, res2.a_clk, -1, g);
            assert PIV.MxAtGidLk(LB, res0.a_clk, lk.a_clk, res2.a_clk, -1, g)
                == PIV.MxAtGidLk(LB,
                                 AReg.as_arrays(rf.value.capture_regs).1, AReg.as_arrays(rf.value.look_regs).1,
                                 AReg.as_arrays(rf.value.quant_regs).1, -1, g);
          }
          PIV.GmOfLiveKeepsPresentLk(LB, rf.value.capture_regs, rf.value.look_regs,
                                     rf.value.quant_regs, g);
          assert g in PIV.GmOfLive(LB, rf.value.capture_regs, rf.value.look_regs, rf.value.quant_regs);
          assert g in leafgm by {
            assert M.MatchedPosLA(crv, lk, lid as int)
                   && NI.LookPathDom(re, AI.get_idx(lk.a_clk, lid as int), qtF.a_clk, lid);
          }
        }
      }
    }
    assert {:split_here} true;   // (E3) section boundary: its own assertion batch

    // ---- assemble ---------------------------------------------------------
    WinningGmtTieOutside(re, thread, leafgm,
                         PIV.GmOfLive(re, thread.capture_regs, thread.look_regs, thread.quant_regs), S);
    assert forall k: int :: k !in PIV.CaptureRegsSet(PIV.CapIdsInLooks(re)) ==>
                              AI.get_idx(AReg.as_arrays(res0).0, k) == AI.get_idx(AReg.as_arrays(thread.capture_regs).0, k)
                              && AI.get_idx(AReg.as_arrays(res0).1, k) == AI.get_idx(AReg.as_arrays(thread.capture_regs).1, k)
    by {
      assert PIV.CaptureRegsSet(PIV.CapIdsInLooks(re)) == Sreg;
    }
    assert forall q: nat :: q in PIV.QuantIdsOutsideLooks(re) ==>
                              AI.get_idx(AReg.as_arrays(res2).1, q as int) == AI.get_idx(AReg.as_arrays(thread.quant_regs).1, q as int);
    L3aValueBridge(re, thread, leafgm, res0, res2, S);
    assert leafgm == PIV.NormGm(PIV.GmOfLive(re, res0, lk, res2));
    assert CM.ThreadRegsWf(AI.Thread(thread.pc, res0, res.1, res2, thread.exit_allowed),
                           ncap, nlook, nquant);
    assert M.QuantRegsFinal(AI.Thread(thread.pc, res0, res.1, res2, thread.exit_allowed));
  }

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
  lemma L3aEndpointAssemblyNested(
    ast: R.regex, re: R.regex, crv: CP.FCompiled, code: RB.code, endl: nat,
    str: string, ov: LOr.OracleView, S: set<LG.GroupId>,
    thread: AI.Thread, leaf: LT.Leaf, ncap: int, nlook: int, nquant: int)
    requires T.TransWf(re) && NR.NestedFragmentRE(re) && NR.NegLooksLookFreeRE(re)
    requires PIV.CapUnique(re) && PIV.QuantUnique(re) && LTB.LookUnique(re)
    requires S == PIV.CapIdsInLooks(re)
    requires R.max_lookaround(re) == R.max_lookaround(ast)
    // L3b: the leaf value is ORDERED (spec GMClose ordering) — lets the NormRange
    // conversion collapse on the outside/forward groups.
    requires M.OrderedGm(leaf.1)
    // the nested best-match tie (GmtTieInside dropped; GmtTieOutside + the two
    // LookNest carriers kept).
    requires BestTieLkNested(re, crv, str, ov, S, Some(leaf), Some(thread), ncap, nlook, nquant)
    // ---- the depth-general FLookLoop reconstruction + residual (TODO C4) ----
    requires var res := AI.FLookLoop(crv, str, 1, R.max_lookaround(ast),
                                     thread.capture_regs, thread.look_regs, thread.quant_regs, ov);
             // (a) recon_outer cap frame — FLookLoop writes captures only inside look bodies
             //     (supplied by M.FLookLoopFullCoversFromTables).
             (forall k: int :: k !in PIV.CaptureRegsSet(PIV.CapIdsInLooks(re)) ==>
                                 AI.get_idx(AReg.as_arrays(res.0).0, k) == AI.get_idx(AReg.as_arrays(thread.capture_regs).0, k)
                                 && AI.get_idx(AReg.as_arrays(res.0).1, k) == AI.get_idx(AReg.as_arrays(thread.capture_regs).1, k))
             // (a) quant frame outside looks (nested FLookLoopQuantFrame).
             && (forall q: nat :: q in PIV.QuantIdsOutsideLooks(re) ==>
                                    AI.get_idx(AReg.as_arrays(res.2).1, q as int) == AI.get_idx(AReg.as_arrays(thread.quant_regs).1, q as int))
             // (b) INSIDE-S FORWARD value chain (spec tree + nested LookPath* + Range↔GmOfLive).
             && (forall g: LG.GroupId :: g in S && g in leaf.1 ==>
                                           g in PIV.GmOfLive(re, res.0, res.1, res.2)
                                           && leaf.1[g] == PIV.NormRange(PIV.GmOfLive(re, res.0, res.1, res.2)[g]))
             // (c) INSIDE-S REVERSE (LookNestBackT + nested LookPathDecompose/DomIntro).
             && (forall g: LG.GroupId :: g in S && g in PIV.GmOfLive(re, res.0, res.1, res.2) ==> g in leaf.1)
             // (a) synthetic-res well-formedness (nested FLookLoopValueLiftFull).
             && CM.ThreadRegsWf(AI.Thread(thread.pc, res.0, res.1, res.2, thread.exit_allowed), ncap, nlook, nquant)
             && M.QuantRegsFinal(AI.Thread(thread.pc, res.0, res.1, res.2, thread.exit_allowed))
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

    // ---- OUTSIDE S (derived green) ----------------------------------------
    // BestTieLkNested ⟹ GmtTieOutside(re, thread, leafgm, S).
    assert GmtTieOutside(re, thread, leafgm, S);
    var gmThread := PIV.GmOfLive(re, thread.capture_regs, thread.look_regs, thread.quant_regs);
    var gmBest := PIV.GmOfLive(re, thread.capture_regs, res.1, thread.quant_regs);
    // look-bank independence OUTSIDE CapIdsInLooks(re): move thread.look_regs -> res.1.
    PIV.GmOfLiveLookIndepNested(re, thread.capture_regs, thread.look_regs, res.1, thread.quant_regs);
    M.LkBodyGroupsEqCapIdsInLooks(re);                     // LkBodyGroups(Translate(re)) == S
    assert forall g: nat :: g !in LL.LkBodyGroups(T.Translate(re)) ==>
                              (g in leafgm <==> g in gmBest) && (g in leafgm ==> leafgm[g] == gmBest[g])
    by {
      forall g: nat | g !in LL.LkBodyGroups(T.Translate(re))
        ensures (g in leafgm <==> g in gmBest) && (g in leafgm ==> leafgm[g] == gmBest[g])
      {
        assert g !in S;
        // GmtTieOutside: leafgm ~ gmThread off S; LookIndep: gmThread ~ gmBest off S.
        assert (g in leafgm <==> g in gmThread) && (g in leafgm ==> leafgm[g] == gmThread[g]);
        assert (g in gmThread <==> g in gmBest) && (g in gmThread ==> gmThread[g] == gmBest[g]);
      }
    }
    OutsideLookValueBridgeNested(re, thread.capture_regs, res.0, res.1, thread.quant_regs, res.2,
                                 gmBest, leafgm);
    assert forall g: LG.GroupId :: g !in S ==>
                                     (g in leafgm <==> g in PIV.GmOfLive(re, res.0, res.1, res.2))
                                     && (g in leafgm ==> leafgm[g] == PIV.GmOfLive(re, res.0, res.1, res.2)[g]);

    // ---- assemble (outside frame + the TODO-C4 inside premises) -----------
    assert synthetic.look_regs == res.1;
    L3aValueBridgeNested(re, synthetic, leafgm, res.0, res.2, S);
    assert leafgm == PIV.NormGm(PIV.GmOfLive(re, res.0, res.1, res.2));
  }

  lemma TtLkAtJmpRec(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                     tb: LT.Tree, pc: nat, ea: bool, x: int)
    requires TtLkRec(rer, qm, code, inp, tb, pc, ea)
    requires NR.GetPcRE(code, pc) == Some(RB.Jmp(x))
    ensures x >= 0 && TtLkRec(rer, qm, code, inp, tb, x as nat, ea)
  {
    var acts: LS.Actions, b: BS.LoopBool :|
      AR.ActionsRepL(rer, qm, acts, code, pc)
      && EL.PikeLkActionsRec(acts)
      && ATR.EaOf(b) == ea
      && EL.BoolTreeLk(rer, acts, inp, b, tb);
    ActionsRepLThruJmp(rer, qm, acts, code, pc, x);   // x >= 0 && ActionsRepL(acts, code, x)
    // same (acts, b) witness TtLkRec at x — only the pc moved
  }

  lemma TtLkAtAcceptCoreRec(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                            tb: LT.Tree, pc: nat, b: BS.LoopBool, acts: LS.Actions)
    requires AR.ActionsRepL(rer, qm, acts, code, pc)
    requires EL.PikeLkActionsRec(acts)
    requires EL.BoolTreeLk(rer, acts, inp, b, tb)
    requires NR.GetPcRE(code, pc) == Some(RB.Accept)
    ensures tb == LT.Match
    decreases ATR.MsizeA(acts)
  {
    if |acts| == 0 {
      // BoolTreeLk([], inp, b, tb) ⟹ tb == Match
    } else if exists pcmid: nat :: AR.ActionRepL(rer, qm, acts[0], code, pc, pcmid) && AR.ActionsRepL(rer, qm, acts[1..], code, pcmid) {
      var pcmid: nat :| AR.ActionRepL(rer, qm, acts[0], code, pc, pcmid) && AR.ActionsRepL(rer, qm, acts[1..], code, pcmid);
      EL.PikeLkActionsRecTail(acts);
      assert acts == [acts[0]] + acts[1..];
      EL.PikeLkActionsRecConsIff(acts[0], acts[1..]);
      var cont := acts[1..];
      match acts[0]
      case Acheck(_) =>   // pins EndLoop or a backward Fork — not Accept
      case Aclose(_) =>   // pins SetRegisterToCP — not Accept
      case Areg(r) =>
        assert EL.PikeLkRegexRec(r);
        match r
        case Epsilon =>
          assert pcmid == pc;
          assert EL.BoolTreeLk(rer, cont, inp, b, tb);
          assert ATR.MsizeA(cont) < ATR.MsizeA(acts);
          TtLkAtAcceptCoreRec(rer, qm, code, inp, tb, pc, b, cont);
        case Sequence(r1, r2) =>
          assert acts[0] == LS.Areg(L.Sequence(r1, r2));
          assert AR.NfaRepL(rer, qm, L.Sequence(r1, r2), code, pc, pcmid);   // == ActionRepL(acts[0],..)
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
          TtLkAtAcceptCoreRec(rer, qm, code, inp, tb, pc, b, na);
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
            TtLkAtAcceptCoreRec(rer, qm, code, inp, tb, pc, b, cont);
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

  lemma TtLkAtAcceptRec(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                        tb: LT.Tree, pc: nat, ea: bool)
    requires TtLkRec(rer, qm, code, inp, tb, pc, ea)
    requires NR.GetPcRE(code, pc) == Some(RB.Accept)
    ensures tb == LT.Match
  {
    var acts: LS.Actions, b: BS.LoopBool :|
      AR.ActionsRepL(rer, qm, acts, code, pc)
      && EL.PikeLkActionsRec(acts)
      && ATR.EaOf(b) == ea
      && EL.BoolTreeLk(rer, acts, inp, b, tb);
    TtLkAtAcceptCoreRec(rer, qm, code, inp, tb, pc, b, acts);
  }

  lemma TtLkAtConsumeCoreRec(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                             tb: LT.Tree, pc: nat, b: BS.LoopBool, acts: LS.Actions, ce: RC.char_expectation)
    requires AR.ActionsRepL(rer, qm, acts, code, pc)
    requires EL.PikeLkActionsRec(acts)
    requires EL.BoolTreeLk(rer, acts, inp, b, tb)
    requires NR.GetPcRE(code, pc) == Some(RB.Consume(ce))
    ensures tb.Read? || tb == LT.Mismatch
    ensures tb.Read? ==> exists nextinp ::
                AR.ReadCharE(ce, inp) == Some((tb.c, nextinp))
                && TtLkRec(rer, qm, code, nextinp, tb.t, pc + 1, true)
    ensures tb == LT.Mismatch ==> AR.ReadCharE(ce, inp) == None
    decreases ATR.MsizeA(acts)
  {
    var g := ATR.EaOf(b);
    // empty_bc needs Accept, jump_bc needs Jmp — neither is Consume, so cons_bc.
    var pcmid: nat :| AR.ActionRepL(rer, qm, acts[0], code, pc, pcmid) && AR.ActionsRepL(rer, qm, acts[1..], code, pcmid);
    EL.PikeLkActionsRecTail(acts);
    assert acts == [acts[0]] + acts[1..];
    EL.PikeLkActionsRecConsIff(acts[0], acts[1..]);
    var cont := acts[1..];
    match acts[0]
    case Acheck(_) =>   // pins EndLoop / backward Fork — not Consume
    case Aclose(_) =>   // pins SetRegisterToCP — not Consume
    case Areg(r) =>
      assert EL.PikeLkRegexRec(r);
      match r
      case Epsilon =>
        assert pcmid == pc;
        assert EL.BoolTreeLk(rer, cont, inp, b, tb);
        assert ATR.MsizeA(cont) < ATR.MsizeA(acts);
        TtLkAtConsumeCoreRec(rer, qm, code, inp, tb, pc, b, cont, ce);
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
        TtLkAtConsumeCoreRec(rer, qm, code, inp, tb, pc, b, na, ce);
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
          TtLkAtConsumeCoreRec(rer, qm, code, inp, tb, pc, b, cont, ce);
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
            assert TtLkRec(rer, qm, code, pair.1, tb.t, pc + 1, true) by {
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

  lemma TtLkAtConsumeRec(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                         tb: LT.Tree, pc: nat, ea: bool, ce: RC.char_expectation)
    requires TtLkRec(rer, qm, code, inp, tb, pc, ea)
    requires NR.GetPcRE(code, pc) == Some(RB.Consume(ce))
    ensures tb.Read? || tb == LT.Mismatch
    ensures tb.Read? ==> exists nextinp ::
                AR.ReadCharE(ce, inp) == Some((tb.c, nextinp))
                && TtLkRec(rer, qm, code, nextinp, tb.t, pc + 1, true)
    ensures tb == LT.Mismatch ==> AR.ReadCharE(ce, inp) == None
  {
    var acts: LS.Actions, b: BS.LoopBool :|
      AR.ActionsRepL(rer, qm, acts, code, pc)
      && EL.PikeLkActionsRec(acts)
      && ATR.EaOf(b) == ea
      && EL.BoolTreeLk(rer, acts, inp, b, tb);
    TtLkAtConsumeCoreRec(rer, qm, code, inp, tb, pc, b, acts, ce);
  }

  lemma TtLkAtSetRegCoreRec(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                            tb: LT.Tree, pc: nat, b: BS.LoopBool, acts: LS.Actions, r: int)
    requires AR.ActionsRepL(rer, qm, acts, code, pc)
    requires EL.PikeLkActionsRec(acts)
    requires EL.BoolTreeLk(rer, acts, inp, b, tb)
    requires NR.GetPcRE(code, pc) == Some(RB.SetRegisterToCP(r))
    ensures tb.GroupActionT?
    ensures (tb.g.Open? && r == CP.start_reg(tb.g.g as int))
            || (tb.g.Close? && r == CP.end_reg(tb.g.g as int))
    ensures TtLkRec(rer, qm, code, inp, tb.t, pc + 1, ATR.EaOf(b))
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
      // ActionRepL(Aclose(gid)) pins SetRegisterToCP(end_reg(gid)), pcmid == pc+1
      assert pcmid == pc + 1 && r == CP.end_reg(gid as int);
      assert tb.GroupActionT? && tb.g == LG.Close(gid) && EL.BoolTreeLk(rer, cont, inp, b, tb.t);
      assert TtLkRec(rer, qm, code, inp, tb.t, pc + 1, g);
    case Areg(r0) =>
      assert EL.PikeLkRegexRec(r0);
      match r0
      case Epsilon =>
        assert pcmid == pc;
        assert EL.BoolTreeLk(rer, cont, inp, b, tb);
        assert ATR.MsizeA(cont) < ATR.MsizeA(acts);
        TtLkAtSetRegCoreRec(rer, qm, code, inp, tb, pc, b, cont, r);
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
        TtLkAtSetRegCoreRec(rer, qm, code, inp, tb, pc, b, na, r);
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
        assert EL.PikeLkActionsRec(ga) by {
          EL.PikeLkActionsRecConsIff(LS.Aclose(gid), cont);
          EL.PikeLkActionsRecConsIff(LS.Areg(r1), [LS.Aclose(gid)] + cont);
        }
        assert TtLkRec(rer, qm, code, inp, tb.t, pc + 1, g);
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
          TtLkAtSetRegCoreRec(rer, qm, code, inp, tb, pc, b, cont, r);
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

  lemma TtLkAtSetRegRec(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                        tb: LT.Tree, pc: nat, ea: bool, r: int)
    requires TtLkRec(rer, qm, code, inp, tb, pc, ea)
    requires NR.GetPcRE(code, pc) == Some(RB.SetRegisterToCP(r))
    ensures tb.GroupActionT?
    ensures (tb.g.Open? && r == CP.start_reg(tb.g.g as int))
            || (tb.g.Close? && r == CP.end_reg(tb.g.g as int))
    ensures TtLkRec(rer, qm, code, inp, tb.t, pc + 1, ea)
  {
    var acts: LS.Actions, b: BS.LoopBool :|
      AR.ActionsRepL(rer, qm, acts, code, pc)
      && EL.PikeLkActionsRec(acts)
      && ATR.EaOf(b) == ea
      && EL.BoolTreeLk(rer, acts, inp, b, tb);
    TtLkAtSetRegCoreRec(rer, qm, code, inp, tb, pc, b, acts, r);
  }

  lemma TtLkAtSetQuantCoreRec(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                              tb: LT.Tree, pc: nat, b: BS.LoopBool, acts: LS.Actions, q: int)
    requires AR.NoTrueStamps(code)   // §2.5b stage 2a: look-body code is stamp-free
    requires AR.ActionsRepL(rer, qm, acts, code, pc)
    requires EL.PikeLkActionsRec(acts)
    requires EL.BoolTreeLk(rer, acts, inp, b, tb)
    requires NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(q, false))
    ensures tb.GroupActionT? && tb.g.Reset?
    ensures TtLkRec(rer, qm, code, inp, tb.t, pc + 1, ATR.EaOf(b))
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
        TtLkAtSetQuantCoreRec(rer, qm, code, inp, tb, pc, b, cont, q);
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
        TtLkAtSetQuantCoreRec(rer, qm, code, inp, tb, pc, b, na, q);
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
          assert EL.PikeLkRegexRec(r1) && EL.PikeLkRegexRec(quant1);
          assert EL.PikeLkActionsRec(contActs) by {
            EL.PikeLkActionsRecConsIff(LS.Areg(quant1), cont);
            EL.PikeLkActionsRecConsIff(LS.Areg(r1), [LS.Areg(quant1)] + cont);
          }
          assert TtLkRec(rer, qm, code, inp, tb.t, pc + 1, g);
        } else if delta == LN.NN(0) {
          var em: nat :| AR.NfaRepMinL(rer, qm, 0, r1, code, pc, em)
                         && AR.NfaRepOptL(rer, qm, 0, greedy, r1, code, em, pcmid);
          NfaRepMinLHeadPin(rer, qm, 0, r1, code, pc, em);
          NfaRepOptLHeadPin(rer, qm, 0, greedy, r1, code, em, pcmid);
          assert pcmid == pc;
          assert AR.ActionsRepL(rer, qm, cont, code, pc);
          assert EL.BoolTreeLk(rer, cont, inp, b, tb);
          assert ATR.MsizeA(cont) < ATR.MsizeA(acts);
          TtLkAtSetQuantCoreRec(rer, qm, code, inp, tb, pc, b, cont, q);
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
            NfaRepOptLHeadPin(rer, qm, kx, greedy, r1, code, em, pcmid);   // kx>0 ⇒ Fork at pc
        }
      case Character(_) =>   // pins Consume — not SetQuantToClock
      case Disjunction(_, _) =>   // pins Fork — not SetQuantToClock
      case Group(_, _) =>   // pins SetRegisterToCP — not SetQuantToClock
      case LookaroundR(_, _) =>   // pins CheckOracle/NegCheckOracle — not SetQuantToClock
      case AnchorR(_) =>   // pins AnchorAssertion — not SetQuantToClock
      case Backreference(_) =>   // NfaRepL false
  }

  lemma TtLkAtSetQuantRec(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                          tb: LT.Tree, pc: nat, ea: bool, q: int)
    requires AR.NoTrueStamps(code)   // §2.5b stage 2a: look-body code is stamp-free
    requires TtLkRec(rer, qm, code, inp, tb, pc, ea)
    requires NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(q, false))
    ensures tb.GroupActionT? && tb.g.Reset?
    ensures TtLkRec(rer, qm, code, inp, tb.t, pc + 1, ea)
  {
    if (exists acts: LS.Actions, b: BS.LoopBool ::
          AR.ActionsRepL(rer, qm, acts, code, pc)
          && EL.PikeLkActionsRec(acts)
          && ATR.EaOf(b) == ea
          && EL.BoolTreeLk(rer, acts, inp, b, tb)) {
      var acts: LS.Actions, b: BS.LoopBool :|
        AR.ActionsRepL(rer, qm, acts, code, pc)
        && EL.PikeLkActionsRec(acts)
        && ATR.EaOf(b) == ea
        && EL.BoolTreeLk(rer, acts, inp, b, tb);
      TtLkAtSetQuantCoreRec(rer, qm, code, inp, tb, pc, b, acts, q);
    } else {
      // the SQC see-through disjunct gives the shape + child directly
      var q0: int :| NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(q0, false))
                     && q0 in qm.quants
                     && tb.GroupActionT? && tb.g == LG.Reset(qm.quants[q0])
                     && TtLkRec(rer, qm, code, inp, tb.t, pc + 1, ea);
    }
  }

  lemma TtLkAtCheckOracleCoreRec(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                                 tb: LT.Tree, pc: nat, b: BS.LoopBool, acts: LS.Actions, lid: int)
    requires AR.ActionsRepL(rer, qm, acts, code, pc)
    requires EL.PikeLkActionsRec(acts)
    requires EL.BoolTreeLk(rer, acts, inp, b, tb)
    requires NR.GetPcRE(code, pc) == Some(RB.CheckOracle(lid))
    requires LL.OracleOkAt(rer, qm, inp)
    ensures lid in qm.looks
    ensures var (lk, r1) := qm.looks[lid];
            (LOr.view_get_oracle(qm.ov, TR_CpOf(inp), lid) ==>
               tb.LK? && tb.lk == lk
               && EL.LkGateOk(rer, lk, r1, inp, tb.tlk, true)
               && TtLkRec(rer, qm, code, inp, tb.t, pc + 1, ATR.EaOf(b)))
            && (!LOr.view_get_oracle(qm.ov, TR_CpOf(inp), lid) ==>
                  tb.LKFail? && tb.lk == lk
                  && EL.LkGateOk(rer, lk, r1, inp, tb.tlk, false))
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
        TtLkAtCheckOracleCoreRec(rer, qm, code, inp, tb, pc, b, cont, lid);
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
        TtLkAtCheckOracleCoreRec(rer, qm, code, inp, tb, pc, b, na, lid);
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
          TtLkAtCheckOracleCoreRec(rer, qm, code, inp, tb, pc, b, cont, lid);
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
          assert TtLkRec(rer, qm, code, inp, tb.t, pc + 1, g);
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

  lemma TtLkAtCheckOracleRec(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                             tb: LT.Tree, pc: nat, ea: bool, lid: int)
    requires TtLkRec(rer, qm, code, inp, tb, pc, ea)
    requires NR.GetPcRE(code, pc) == Some(RB.CheckOracle(lid))
    requires LL.OracleOkAt(rer, qm, inp)
    ensures lid in qm.looks
    ensures var (lk, r1) := qm.looks[lid];
            (LOr.view_get_oracle(qm.ov, TR_CpOf(inp), lid) ==>
               tb.LK? && tb.lk == lk
               && EL.LkGateOk(rer, lk, r1, inp, tb.tlk, true)
               && TtLkRec(rer, qm, code, inp, tb.t, pc + 1, ea))
            && (!LOr.view_get_oracle(qm.ov, TR_CpOf(inp), lid) ==>
                  tb.LKFail? && tb.lk == lk
                  && EL.LkGateOk(rer, lk, r1, inp, tb.tlk, false))
  {
    var acts: LS.Actions, b: BS.LoopBool :|
      AR.ActionsRepL(rer, qm, acts, code, pc)
      && EL.PikeLkActionsRec(acts)
      && ATR.EaOf(b) == ea
      && EL.BoolTreeLk(rer, acts, inp, b, tb);
    TtLkAtCheckOracleCoreRec(rer, qm, code, inp, tb, pc, b, acts, lid);
  }

  lemma TtLkAtAnchorCoreRec(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                            tb: LT.Tree, pc: nat, b: BS.LoopBool, acts: LS.Actions, a: R.anchor)
    requires AR.ActionsRepL(rer, qm, acts, code, pc)
    requires EL.PikeLkActionsRec(acts)
    requires EL.BoolTreeLk(rer, acts, inp, b, tb)
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
        assert EL.BoolTreeLk(rer, cont, inp, b, tb);
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
        assert EL.BoolTreeLk(rer, na, inp, b, tb);
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
          assert EL.BoolTreeLk(rer, cont, inp, b, tb);
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
          assert tb.AnchorPass? && EL.BoolTreeLk(rer, cont, inp, b, tb.t);
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
      && EL.BoolTreeLk(rer, acts, inp, b, tb);
    TtLkAtAnchorCoreRec(rer, qm, code, inp, tb, pc, b, acts, a);
  }

  lemma TtLkAtEndLoopCoreRec(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                             tb: LT.Tree, pc: nat, b: BS.LoopBool, acts: LS.Actions)
    requires AR.ActionsRepL(rer, qm, acts, code, pc)
    requires EL.PikeLkActionsRec(acts)
    requires EL.BoolTreeLk(rer, acts, inp, b, tb)
    requires NR.GetPcRE(code, pc) == Some(RB.EndLoop)
    ensures ATR.EaOf(b) ==> tb.Progress? && TtLkRec(rer, qm, code, inp, tb.t, pc + 1, true)
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
        assert TtLkRec(rer, qm, code, inp, tb.t, pc + 1, true);
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
        TtLkAtEndLoopCoreRec(rer, qm, code, inp, tb, pc, b, cont);
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
        TtLkAtEndLoopCoreRec(rer, qm, code, inp, tb, pc, b, na);
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
          TtLkAtEndLoopCoreRec(rer, qm, code, inp, tb, pc, b, cont);
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

  lemma TtLkAtEndLoopRec(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                         tb: LT.Tree, pc: nat, ea: bool)
    requires TtLkRec(rer, qm, code, inp, tb, pc, ea)
    requires NR.GetPcRE(code, pc) == Some(RB.EndLoop)
    ensures ea ==> tb.Progress? && TtLkRec(rer, qm, code, inp, tb.t, pc + 1, true)
    ensures !ea ==> tb == LT.Mismatch
  {
    var acts: LS.Actions, b: BS.LoopBool :|
      AR.ActionsRepL(rer, qm, acts, code, pc)
      && EL.PikeLkActionsRec(acts)
      && ATR.EaOf(b) == ea
      && EL.BoolTreeLk(rer, acts, inp, b, tb);
    TtLkAtEndLoopCoreRec(rer, qm, code, inp, tb, pc, b, acts);
  }

  lemma TtLkAtForkCoreRec(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                          tb: LT.Tree, pc: nat, b: BS.LoopBool, acts: LS.Actions, x: int, y: int)
    requires AR.NoTrueStamps(code)   // §2.5b stage 2a: look-body code is stamp-free
    requires AR.ActionsRepL(rer, qm, acts, code, pc)
    requires EL.PikeLkActionsRec(acts)
    requires EL.BoolTreeLk(rer, acts, inp, b, tb)
    requires NR.GetPcRE(code, pc) == Some(RB.Fork(x, y))
    ensures x >= 0 && y >= 0
    ensures tb.Choice? || tb.Progress? || tb == LT.Mismatch
    decreases ATR.MsizeA(acts)
  {
    var pcmid: nat :| AR.ActionRepL(rer, qm, acts[0], code, pc, pcmid) && AR.ActionsRepL(rer, qm, acts[1..], code, pcmid);
    EL.PikeLkActionsRecTail(acts);
    assert acts == [acts[0]] + acts[1..];
    EL.PikeLkActionsRecConsIff(acts[0], acts[1..]);
    var cont := acts[1..];
    match acts[0]
    case Acheck(strcheck) =>
      // EndLoop != Fork, so the BackForkAt disjunct: pcmid == pc; BoolTreeLk ⇒ Progress / Mismatch
      assert AR.BackForkAt(code, pc);
      assert x >= 0 && y >= 0;
    case Aclose(_) =>   // pins SetRegisterToCP — not Fork
    case Areg(r0) =>
      assert EL.PikeLkRegexRec(r0);
      match r0
      case Epsilon =>
        assert pcmid == pc;
        assert EL.BoolTreeLk(rer, cont, inp, b, tb);
        assert ATR.MsizeA(cont) < ATR.MsizeA(acts);
        TtLkAtForkCoreRec(rer, qm, code, inp, tb, pc, b, cont, x, y);
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
        TtLkAtForkCoreRec(rer, qm, code, inp, tb, pc, b, na, x, y);
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
          TtLkAtForkCoreRec(rer, qm, code, inp, tb, pc, b, cont, x, y);
        } else if min > 0 {
          // §2.5a: the STRONG head fact -- `min > 0` pins a clock-mark, which
          // refutes the `Fork` we are sitting at. `QuantHeadPinsForkOrSQC`'s
          // `Fork? || SetQuantToClock?` is too weak here.
          assert min > 0 && delta.Inf? && greedy ==> NUL.NonNullableL(r1) by {   // §2.5b: stamp-free code
            if min > 0 && delta.Inf? && greedy && !NUL.NonNullableL(r1) {
              var emC, e1C := AR.NfaRepLCinInv(rer, qm, greedy, min, r1, code, pc, pcmid);
              var qidC: int :| NR.GetPcRE(code, e1C + 2) == Some(RB.SetQuantToClock(qidC, true));
              assert NR.GetPcRE(code, e1C + 2) != Some(RB.SetQuantToClock(qidC, true));
            }
          }
          QuantHeadMinPosPinsSQC(rer, qm, greedy, min, delta, r1, code, pc, pcmid);
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
              AR.NfaRepLStarLoopViews(rer, qm, greedy, r1, code, pc, pcmid);
              if NUL.NonNullableL(r1) {
                var em: nat :| NR.GetPcRE(code, pc) == Some(if greedy then RB.Fork(em, pc + 1) else RB.Fork(pc + 1, em));
              } else {
                var emC, e1C := AR.NfaRepLStarCinInv(rer, qm, r1, code, pc, pcmid);
              }
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

  lemma TtLkAtForkRec(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                      tb: LT.Tree, pc: nat, ea: bool, x: int, y: int)
    requires AR.NoTrueStamps(code)   // §2.5b stage 2a: look-body code is stamp-free
    requires TtLkRec(rer, qm, code, inp, tb, pc, ea)
    requires NR.GetPcRE(code, pc) == Some(RB.Fork(x, y))
    ensures x >= 0 && y >= 0
    ensures tb.Choice? || tb.Progress? || tb == LT.Mismatch
  {
    var acts: LS.Actions, b: BS.LoopBool :|
      AR.ActionsRepL(rer, qm, acts, code, pc)
      && EL.PikeLkActionsRec(acts)
      && ATR.EaOf(b) == ea
      && EL.BoolTreeLk(rer, acts, inp, b, tb);
    TtLkAtForkCoreRec(rer, qm, code, inp, tb, pc, b, acts, x, y);
  }

  lemma ActionsTreeRepLkRERec(rer: LW.RegExpRecord, qm: AR.QMap, acts: LS.Actions, code: RB.code,
                              pc: nat, inp: LC.Input, b: BS.LoopBool, t: LT.Tree)
    returns (tcan: LT.Tree)
    requires AR.NoTrueStamps(code)   // §2.5b stage 2a: look-body code is stamp-free
    requires EL.PikeLkActionsRec(acts)
    requires AR.ActionsRepL(rer, qm, acts, code, pc)
    requires WO.WalkOk(acts, code, pc, ATR.EaOf(b))
    requires EL.BoolTreeLk(rer, acts, inp, b, t)
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

  /** (BRICK D4) The per-body DISCHARGE bridge: reduces one body's `LocalTopFeed`
      to that body's `LookNestOkTTop` (main thread at `re`, or the look's replay
      tower at a look body) plus the reconstruction frames — a per-top-look loop
      over `TopAncestorClockReconStep`. The remaining obligations are exactly:
        - the recon_outer capture/quant frames + top-look-clock stability
          (mechanical — the clock twins of the value-side `FLookLoopFullCovers*`);
        - the GUARD BRIDGE (the value-coupled piece): a reconstructed-bank live
          witness for `l`'s body implies a `gmt` live witness (from the value tie
          `LookNestBackTTop`/`GmtTie`) — taken here as a hypothesis. */
  lemma LocalTopFeedFromNestOkT(host: R.regex, S: set<LG.GroupId>, gmt: LG.GroupMap, th: AI.Thread,
                                rcc: seq<int>, rlc: seq<int>, rqc: seq<int>)
    requires LTB.LookUnique(host)
    requires LookNestOkTTop(host, S, gmt, th)
    // recon_outer frames (global) + top-look-clock stability (per top look)
    requires forall c: nat :: c in PIV.CapIdsOutsideLooks(host) ==>
                                AI.get_idx(rcc, CP.start_reg(c as int)) == AI.get_idx(th.capture_regs.a_clk, CP.start_reg(c as int))
    requires forall q: nat :: q in PIV.QuantIdsOutsideLooks(host) ==>
                                AI.get_idx(rqc, q as int) == AI.get_idx(th.quant_regs.a_clk, q as int)
    requires forall l: nat :: l in NI.TopLookIds(host) ==>
                                AI.get_idx(rlc, l as int) == AI.get_idx(th.look_regs.a_clk, l as int)
    // GUARD BRIDGE (value-coupled): reconstructed-bank live witness ==> gmt witness
    requires forall l: nat :: l in LTB.LookIds(host) && l in NI.TopLookIds(host)
                              && (exists g2: nat :: g2 in PIV.CapIds(NI.LookBodyOfRE(host, l)) && AI.get_idx(rcc, CP.start_reg(g2)) >= 0)
                              ==> (exists g3: LG.GroupId :: g3 in S && g3 in gmt && g3 in PIV.CapIds(NI.LookBodyOfRE(host, l)))
    ensures LocalTopFeed(host, rcc, rlc, rqc)
  {
    forall l: nat | l in LTB.LookIds(host) && l in NI.TopLookIds(host)
                    && (exists g2: nat :: g2 in PIV.CapIds(NI.LookBodyOfRE(host, l)) && AI.get_idx(rcc, CP.start_reg(g2)) >= 0)
      ensures NI.LookPathPresentLk(host, rcc, rlc, rqc, -1, l)
              && AI.get_idx(rlc, l as int) >= 0
              && AI.get_idx(rlc, l as int) >= NI.MxAtLidLk(host, rqc, -1, l)
    {
      // gmt live witness (guard bridge) -> LookNestOkTTop delivers th-bank presence at l
      assert exists g3: LG.GroupId :: g3 in S && g3 in gmt && g3 in PIV.CapIds(NI.LookBodyOfRE(host, l));
      assert NI.LookPathPresent(host, th.capture_regs.a_clk, th.quant_regs.a_clk, -1, l)
             && AI.get_idx(th.look_regs.a_clk, l as int) >= 0
             && AI.get_idx(th.look_regs.a_clk, l as int) >= NI.MxAtLidLk(host, th.quant_regs.a_clk, -1, l);
      // reconcile onto the reconstructed banks
      TopAncestorClockReconStep(host, rcc, rlc, rqc,
                                th.capture_regs.a_clk, th.look_regs.a_clk, th.quant_regs.a_clk, l);
    }
  }

  /** (BRICK D6) The host==re BASE-EVIDENCE PRODUCER: `LocalTopFeed(re, res0.a_clk,
      res1.a_clk, res2.a_clk)` with the two MECHANICAL clock frames DISCHARGED via
      the D6 twins. Consumes the FromTables recon_outer frames DIRECTLY
      (`RegsAgreeOutside`, which the `M.FLookLoop{Full,Quant}CoversFromTables`
      capstones already emit) and the `LookNestOkTTop` carrier (available from
      `BestTieLkNestedTop`), leaving only the two value/engine-coupled residuals as
      hypotheses: TOP-LOOK-CLOCK stability (the whole-loop tight look frame) and the
      GUARD BRIDGE. This is the exact base-evidence witness the `re` arm of
      `AllBodyTopFeeds` needs; the body-host arms need their per-body replay-tower
      analogues (the deferred engine half). */
  lemma LocalTopFeedAtReFromFrames(
    re: R.regex, S: set<LG.GroupId>, gmt: LG.GroupMap, th: AI.Thread,
    res0: AReg.Regs, res1: AReg.Regs, res2: AReg.Regs)
    requires LTB.LookUnique(re) && PIV.CapUnique(re) && PIV.QuantUnique(re)
    requires LookNestOkTTop(re, S, gmt, th)
    // recon_outer frames straight from FromTables (a_clk faces via the twins)
    requires CM.RegsAgreeOutside(res0, th.capture_regs, PIV.CaptureRegsSet(PIV.CapIdsInLooks(re)))
    requires CM.RegsAgreeOutside(res2, th.quant_regs, (set q: nat | q in PIV.QuantIdsInLooks(re) :: q as int))
    // TOP-LOOK-CLOCK stability (whole-loop tight look frame — owed)
    requires forall l: nat :: l in NI.TopLookIds(re) ==>
                                AI.get_idx(AReg.as_arrays(res1).1, l as int) == AI.get_idx(th.look_regs.a_clk, l as int)
    // GUARD BRIDGE (value-coupled — owed): recon-bank live witness ==> gmt witness
    requires forall l: nat :: l in LTB.LookIds(re) && l in NI.TopLookIds(re)
                              && (exists g2: nat :: g2 in PIV.CapIds(NI.LookBodyOfRE(re, l)) && AI.get_idx(res0.a_clk, CP.start_reg(g2)) >= 0)
                              ==> (exists g3: LG.GroupId :: g3 in S && g3 in gmt && g3 in PIV.CapIds(NI.LookBodyOfRE(re, l)))
    ensures LocalTopFeed(re, res0.a_clk, AReg.as_arrays(res1).1, res2.a_clk)
  {
    CapClkFrameOutsideLooksTwin(re, res0, th.capture_regs);
    QuantClkFrameOutsideLooksTwin(re, res2, th.quant_regs);
    LocalTopFeedFromNestOkT(re, S, gmt, th, res0.a_clk, AReg.as_arrays(res1).1, res2.a_clk);
  }

  /** `AllBodyTopFeeds` descends into a look body: the body's own base evidence is
      the outer hypothesis at that body, and the body's sub-bodies coincide with
      `re`'s (`LookBodyCompose`). */
  lemma AllBodyTopFeedsDescend(re: R.regex, rcc: seq<int>, rlc: seq<int>, rqc: seq<int>, A0: nat)
    requires LTB.LookUnique(re)
    requires A0 in LTB.LookIds(re)
    requires AllBodyTopFeeds(re, rcc, rlc, rqc)
    ensures AllBodyTopFeeds(NI.LookBodyOfRE(re, A0), rcc, rlc, rqc)
  {
    var bA := NI.LookBodyOfRE(re, A0);
    assert LocalTopFeed(bA, rcc, rlc, rqc);          // AllBodyTopFeeds(re) at a := A0
    forall a2: nat | a2 in LTB.LookIds(bA)
      ensures LocalTopFeed(NI.LookBodyOfRE(bA, a2), rcc, rlc, rqc)
    {
      NI.LookBodyCompose(re, A0, a2);                // a2 in LookIds(re) & bodies coincide
      assert LocalTopFeed(NI.LookBodyOfRE(re, a2), rcc, rlc, rqc);   // AllBodyTopFeeds(re) at a := a2
    }
  }

  /** (BRICK D4 CAPSTONE) The whole-loop ancestor look-clock chain: for ANY captured
      inner look `owner` (at any nesting depth), the RECONSTRUCTED banks carry the
      ancestor chain SET+DOMINATING — feeds (i)/(ii) of `M.ReconInnerGmOfLiveClose`.
      Assembled by peeling `owner`'s outermost top-level ancestor `A0` off the chain
      (`AncestorChainPeelStep`), taking `A0`'s feed from the base evidence at `re`
      and `owner`'s within-`bA0` feed from the recursion (nesting strictly drops one
      look id). The remaining engine obligation is `AllBodyTopFeeds` — the per-body
      base evidence: `TopAncestorClockReconStep` reconciles each body's
      `LookNestOkTTop` (main thread at `re`, replay tower at each look body) onto the
      reconstructed banks. */
  lemma FLookLoopAncestorClockChain(re: R.regex, rcc: seq<int>, rlc: seq<int>, rqc: seq<int>,
                                                          owner: nat, g: nat)
    requires NR.NestedFragmentRE(re) && NR.NegLooksLookFreeRE(re) && LTB.LookUnique(re)
    requires owner in LTB.LookIds(re)
    // the LIVE captured group whose owner this is (its owner's-body membership +
    // reconstructed-bank liveness discharge each ancestor's base-evidence guard)
    requires g in PIV.CapIds(NI.LookBodyOfRE(re, owner))
    requires AI.get_idx(rcc, CP.start_reg(g)) >= 0
    requires AllBodyTopFeeds(re, rcc, rlc, rqc)
    ensures NI.LookPathPresentLk(re, rcc, rlc, rqc, -1, owner)
    ensures AI.get_idx(rlc, owner as int) >= 0
    ensures AI.get_idx(rlc, owner as int) >= NI.MxAtLidLk(re, rqc, -1, owner)
    decreases |LTB.LookIds(re)|
  {
    assert LocalTopFeed(re, rcc, rlc, rqc);
    if owner in NI.TopLookIds(re) {
      // base: owner is top-level in re; g in owner's body + g live discharge the guard
      assert g in PIV.CapIds(NI.LookBodyOfRE(re, owner)) && AI.get_idx(rcc, CP.start_reg(g)) >= 0;
    } else {
      var A0 := TopAncestorExists(re, owner);
      NI.TopLookIdsIn(re);
      assert A0 in LTB.LookIds(re);
      var bA0 := NI.LookBodyOfRE(re, A0);
      // g sits in A0's body too: owner nests in bA0, and g is in owner's-body caps
      NI.LookBodyCompose(re, A0, owner);        // owner in LookIds(re); bodies compose
      assert NI.LookBodyOfRE(re, owner) == NI.LookBodyOfRE(bA0, owner);
      NI.LookBodyCapsIn(bA0, owner);            // CapIds(LookBodyOfRE(bA0,owner)) <= CapIds(bA0)
      assert g in PIV.CapIds(bA0);
      // A0's feed from LocalTopFeed(re): guard discharged by the g-witness in bA0
      assert g in PIV.CapIds(NI.LookBodyOfRE(re, A0)) && AI.get_idx(rcc, CP.start_reg(g)) >= 0;
      assert NI.LookPathPresentLk(re, rcc, rlc, rqc, -1, A0)
             && AI.get_idx(rlc, A0 as int) >= 0
             && AI.get_idx(rlc, A0 as int) >= NI.MxAtLidLk(re, rqc, -1, A0);
      // body facts + strict measure decrease
      NI.LookBodyOfFragmentNested(re, A0);      // NestedFragmentRE(bA0) & NegLooksLookFreeRE(bA0)
      LookBodyLookUnique(re, A0);               // LookUnique(bA0)
      NI.LookBodyLookIdsIn(re, A0);             // LookIds(bA0) <= LookIds(re)
      LookIdNotInOwnBody(re, A0);               // A0 !in LookIds(bA0)
      assert A0 in LTB.LookIds(re) && A0 !in LTB.LookIds(bA0) && LTB.LookIds(bA0) <= LTB.LookIds(re);
      SubsetCardLt(LTB.LookIds(bA0), LTB.LookIds(re), A0);
      assert |LTB.LookIds(bA0)| < |LTB.LookIds(re)|;
      // recurse for owner within bA0 (same live g: g in LookBodyOfRE(bA0,owner))
      assert g in PIV.CapIds(NI.LookBodyOfRE(bA0, owner));
      AllBodyTopFeedsDescend(re, rcc, rlc, rqc, A0);
      FLookLoopAncestorClockChain(bA0, rcc, rlc, rqc, owner, g);
      // stitch
      AncestorChainPeelStep(re, rcc, rlc, rqc, A0, owner);
    }
  }

  /** (BRICK D-11 descent — TOP-OWNER PRODUCER) The reverse-recon descent
      conclusion assembled for every recon-live capture whose descent bottoms out
      at a TOP look (the depth-1 shape, and the top-ancestor slice of the general
      descent): from the per-`g2` backward-carrier package — `g2`'s top ancestor
      `A0` matched + dominating on the carrier thread's banks, and `A0`'s FRESH
      body match carrying `g2` LIVE — the SIM carrier `LookNestBackTTop` lands each
      `g2` in `gmt`. Produces EXACTLY the conclusion `GuardBridgeFromDescent` /
      `ReverseCFromDescent` consume as a `requires`. The remaining obligation is
      the per-`g2` package itself: matched/dominating is the reverse-liveness
      connective `M.FLookLoopInLookLiveOwnerMatched` transported onto the carrier
      banks, and the fresh-body membership is the (A2) producer (see the D-11
      residual note). At depth 1 every innermost owner is top, so this IS the full
      descent; at depth >= 2 it covers the top-ancestor case and leaves the
      leaf-to-parent-leaf compose-up for a deeper owner. */
  lemma DescentProducerTopOwners(
    re: R.regex, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
    S: set<LG.GroupId>, gmt: LG.GroupMap, thread: AI.Thread, res0: AReg.Regs,
    ncap: int, nlook: int, nquant: int)
    requires S == PIV.CapIdsInLooks(re)
    requires LookNestBackTTop(re, crv, str, ov, S, gmt, thread, ncap, nlook, nquant)
    // per recon-live inside-look g2: a TOP ancestor A0 matched + dominating on the
    // carrier thread's banks, whose FRESH body match carries g2 LIVE. (The (A1)
    // connective transported onto the carrier banks + the (A2) fresh-membership.)
    requires forall g2: nat :: g2 in S && AI.get_idx(res0.a_clk, CP.start_reg(g2)) >= 0 ==>
                                 exists A0: nat ::
                                   A0 in NI.TopLookIds(re) && A0 in LTB.LookIds(re)
                                   && g2 in PIV.CapIds(NI.LookBodyOfRE(re, A0))
                                   && M.MatchedPosLA(crv, thread.look_regs, A0 as int)
                                   && NI.LookPathDom(re, AI.get_idx(thread.look_regs.a_clk, A0 as int), thread.quant_regs.a_clk, A0)
                                   && var rf := M.FreshBodyMatch(crv, str, A0 as int, thread.look_regs, ov, ncap, nlook, nquant);
                                   rf.Some?
                                   && g2 in PIV.GmOfLive(NI.LookBodyOfRE(re, A0), rf.value.capture_regs,
                                                         rf.value.look_regs, rf.value.quant_regs)
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
        && var rf := M.FreshBodyMatch(crv, str, A0 as int, thread.look_regs, ov, ncap, nlook, nquant);
        rf.Some?
        && g2 in PIV.GmOfLive(NI.LookBodyOfRE(re, A0), rf.value.capture_regs,
                              rf.value.look_regs, rf.value.quant_regs);
      DescentLandTop(re, crv, str, ov, S, gmt, thread, A0, g2, ncap, nlook, nquant);
    }
  }

  /** (DEEP reverse-recon — MATCHED + DOMINANT for a deep g2's top ancestor) The
      DEEP-case analogue of the res1-side facts `DescentPackageDirectFull` gets from
      A1 for a DIRECT g2: for a deep-nested live capture `g2` whose OUTERMOST top
      ancestor is `A0`, both existential gate conjuncts on the WINNING thread's
      banks — `MatchedPosLA(A0)` and `LookPathDom(A0)`. Dominance comes from the
      liveness connective `NI.LookPathDomFromLivenessThread` directly; matched comes
      from `A0`'s look clock being SET on the reconstructed banks (`LocalTopFeed` at
      `A0`, whose live-witness guard `g2` discharges) reconciled onto the thread
      banks (`get_idx(res1.a_clk,A0)==get_idx(thread.look_regs.a_clk,A0)`), then the
      reverse look-bank invariant `M.TopLookMatchedFromDom`. A1 delivers only the
      INNERMOST owner matched, so `A0`-matched needs exactly this clock-set route.
      Everything but the deep LANDING (`g2 in SubFirstLeafAt(A0)`) of the deep
      per-`g2` existential is produced here. */
  lemma DeepTopAncestorMatchedDom(
    crv: CP.FCompiled, re: R.regex, thread: AI.Thread,
    res0: AReg.Regs, res1: AReg.Regs, res2: AReg.Regs, A0: nat, g2: nat)
    requires NR.NestedFragmentRE(re) && PIV.CapUnique(re) && LTB.LookUnique(re)
    requires g2 in PIV.CapIdsInLooks(re)
    requires A0 in NI.TopLookIds(re) && A0 in LTB.LookIds(re)
    requires g2 in PIV.CapIds(NI.LookBodyOfRE(re, A0))
    requires forall c: nat :: c in PIV.CapIds(re) && AI.get_idx(res0.a_clk, CP.start_reg(c)) < 0
                              ==> AI.get_idx(res0.a_cp, CP.start_reg(c)) < 0
    requires g2 in PIV.GmOfLive(re, res0, res1, res2)
    requires AI.get_idx(res0.a_clk, CP.start_reg(g2)) >= 0            // res0-live (LocalTopFeed guard)
    requires AllBodyTopFeeds(re, res0.a_clk, AReg.as_arrays(res1).1, res2.a_clk)
    // reconciliation res -> thread at the TOP look A0.
    requires AI.get_idx(res1.a_clk, A0 as int) == AI.get_idx(thread.look_regs.a_clk, A0 as int)
    requires forall q: nat :: q in PIV.QuantIdsOutsideLooks(re) ==>
                                AI.get_idx(res2.a_clk, q as int) == AI.get_idx(thread.quant_regs.a_clk, q as int)
    // winning-thread reverse look-bank invariant + fragment static.
    requires CM.LookCpSetWithClk(thread.look_regs)
    requires |thread.look_regs.a_cp| == |thread.look_regs.a_clk|
    requires 0 <= (A0 as int) < |crv.f_look_types| && crv.f_look_types[A0 as int].Lookahead?
    ensures M.MatchedPosLA(crv, thread.look_regs, A0 as int)
    ensures NI.LookPathDom(re, AI.get_idx(thread.look_regs.a_clk, A0 as int), thread.quant_regs.a_clk, A0)
  {
    // (1) dominance from the liveness connective.
    NI.LookPathDomFromLivenessThread(re, res0, res1, res2, thread, g2, A0);
    // (2) A0's look clock is SET on the reconstructed banks (LocalTopFeed at A0).
    assert LocalTopFeed(re, res0.a_clk, AReg.as_arrays(res1).1, res2.a_clk);   // from AllBodyTopFeeds
    assert AReg.as_arrays(res1).1 == res1.a_clk;                               // definitional
    assert exists g3: nat :: g3 in PIV.CapIds(NI.LookBodyOfRE(re, A0))
                             && AI.get_idx(res0.a_clk, CP.start_reg(g3)) >= 0;  // witness g2
    assert AI.get_idx(res1.a_clk, A0 as int) >= 0;                            // LocalTopFeed at A0
    assert AI.get_idx(thread.look_regs.a_clk, A0 as int) >= 0;                // reconciliation
    // (3) matched via the reverse look-bank invariant.
    M.TopLookMatchedFromDom(crv, re, thread, A0);
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
    requires NR.NoNulledPlusRE(re)   // §2.5b interim: all stamps false
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
    // ---- the fragment's no-quant scope for g2 ----
    requires M.GNotUnderQuantL(T.Translate(re), g2)
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
      && NR.NegLooksLookFreeRE(bA)
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
    requires NR.NegLooksLookFreeRaw(raw)
    requires NR.LookBodiesNoCapUnderQuantRaw(raw)
    requires NR.QuantsLookCapFreeRaw(raw)
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

  /** L4 PERF: the g-INDEPENDENT half of the fresh-wf side condition, hoisted
      into a MINIMAL context. `SizesOkRE(body)`, `cp_ctx_ok` and `TransWf(body)`
      depend only on `owner0` (and `res1`), never on the capture `g`, yet the
      `forall g { forall owner0 { ... } }` in ProduceOwnerForall re-proved them
      per-g inside a ~5000-fact context -- and the `cp_ctx_ok` VC alone timed
      out there. Proven ONCE here (no a-h, no OwnerForallO in scope), it is
      cited per-(owner0,g) in the g-loop, which then only owes GNotUnderQuantL. */
  lemma FreshWfGIndep(
    qm: AR.QMap, crv: CP.FCompiled, str: string, re: R.regex, ov: LOr.OracleView,
    res1: AReg.Regs, ncap: int, nlook: int, nquant: int)
    requires LTB.LookTablesOk(re, crv)
    requires GateStaticsOkNested(qm, re, crv, ncap, nlook, nquant)
    requires forall x: nat :: x in LTB.LookIds(re) ==> (x as int) in qm.looks
    requires M.LookInvO(res1, ov, str)
    ensures forall owner0: nat ::
              owner0 in LTB.LookIds(re) ==>
                var body := NI.LookBodyOfRE(re, owner0);
                PSM.SizesOkRE(body, ncap, nlook, nquant)
                && (AReg.get_cp(res1, owner0).Some? ==> M.cp_ctx_ok(crv, str, res1, owner0))
                && T.TransWf(body)
  {
    reveal M.LookInvO();
    forall owner0: nat | owner0 in LTB.LookIds(re)
      ensures var body := NI.LookBodyOfRE(re, owner0);
              PSM.SizesOkRE(body, ncap, nlook, nquant)
              && (AReg.get_cp(res1, owner0).Some? ==> M.cp_ctx_ok(crv, str, res1, owner0))
              && T.TransWf(body)
    {
      var body := NI.LookBodyOfRE(re, owner0);
      assert (owner0 as int) in qm.looks && GateStaticAtNested(qm, re, crv, owner0 as int, ncap, nlook, nquant);
      var laO: R.lookaround, bO: R.regex :| LTB.LookEntryOk(crv, owner0 as int, laO, bO)
                                            && T.TransWf(bO) && PSM.SizesOkRE(bO, ncap, nlook, nquant);
      assert bO == body by {
        NI.LookBodyOfTablesTie(re, crv, owner0);
        var laT: R.lookaround :| LTB.LookEntryOk(crv, owner0 as int, laT, body);
        assert crv.f_look_ast[owner0 as int] == bO == body;
      }
      if AReg.get_cp(res1, owner0).Some? {
        assert M.cp_ctx_ok(crv, str, res1, owner0) by {
          assert CM.LookCpsLE(res1, |str|);
          var cpv := AReg.get_cp(res1, owner0).value;
          // get_cp Some => the slot is in range and holds a non-negative cp
          // (definitional; mirrors MainMatchCpCtxOk's cp>=0 derivation).
          assert 0 <= (owner0 as int) < |res1.a_cp|
                 && cpv == AI.get_idx(res1.a_cp, owner0 as int)
                 && cpv >= 0;
          assert cpv <= |str|;   // LookCpsLE
          assert AI.cp_context(cpv, str, LAnc.Forward).nextchar == AI.get_char(str, cpv);
        }
      }
    }
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
    requires NR.NestedFragmentRE(sub) && NR.L5ScopeRE(sub) && NR.NegLooksLookFreeRE(sub)   // (L5 F7g) lifted
    requires NR.NoNulledPlusRE(sub)   // §2.5b interim: all stamps false
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
    hide NR.NestedFragmentRE, NR.L5ScopeRE, NR.NegLooksLookFreeRE, NR.NoNulledPlusRE, LTB.LidsWellNested, LTB.LookUnique;
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
                            && ((la.NegLookahead? || la.NegLookbehind?) ==> NR.LookFreeRE(body));
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
      NI.NoNulledPlusLookBody(sub, lid as nat);   // §2.5b interim: NoNulledPlusRE(body)
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
    requires NR.NestedFragmentRE(sub) && NR.L5ScopeRE(sub) && NR.NegLooksLookFreeRE(sub)   // (L5 F7g) lifted
    requires NR.NoNulledPlusRE(sub)   // §2.5b interim: all stamps false
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
        NI.NoNulledPlusLookBody(sub, lidn);   // §2.5b interim: NoNulledPlusRE(body)
        OracleOkRowsL5(rer, top, crv, str, body);
        // then this row's column
        OracleColumnNested(rer, top, crv, str, sub, lid, lk, r1, cp);
      }
    }
  }

}
