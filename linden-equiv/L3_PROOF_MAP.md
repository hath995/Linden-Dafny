# L3 Proof Map — what is proved, and how each piece reaches the goal

*Generated 2026-08-04 from a full signature sweep of `src/Equiv/LiftSim.dfy` (module
`LindenElkLiftSim`) plus the reused infrastructure in `MainTheorem`/`PikeSimRE`/`PikeTreeLk`.*

**Verification status of `LiftSim.dfy`: `159 verified, 0 errors`.**
Everything below marked **PROVED** has a real body that Dafny checks. Only **7 lemmas** are
bodyless (their `ensures` is currently assumed). That is the entire remaining surface.

*(2026-08-04 update — LiftStepC foundation landed, `163 verified, 0 errors`:*
- *`SeenRepLk` — formerly a `true` stub — now has its real body (verbatim mirror of
  `PIV.SeenInclusionRE` with `TtLk`).*
- *Seen-tracking toolkit banked: `InitialSeenRepLk` / `AddSeenRepLk` / `SeenGrowSeenRepLk` /
  `SkipSeenRepLk` (ports of PIV's Initial/Add/SeenGrow/Skip inclusion lemmas) — what
  `LiftStepC`'s recursion invokes at each skip/active/match/blocked step.*
- *`LiftInvC` STRENGTHENED with the `SeenRepLk` conjunct (B-side seen ↔ VM processed, needed so
  `ActiveRepLk` survives a skip); `LiftInitC` re-proved (init seen vacuous via `InitialSeenRepLk`;
  added `requires vms.processed == init_bpcset`).*
- *So the 7 bodyless lemmas remain, but `LiftStepC` now has a correct invariant to preserve and
  its seen bricks are proved. NEW dependency found: `LiftStepC`'s skip case needs `TtLkSameTree`
  (the B-head tree at a re-processed `(pc,ea)` must equal the one already in `bseen`).)*

*(2026-08-05 update — the ERASED-CANONICAL pivot, `167 verified, 0 errors`:*
- ***`TtLkSameTree` as originally stated is FALSE.*** *At a do-while's backward fork, both
  `[Areg(star)]+cont` (loop-view `NfaRepL`) and `[Acheck(s), Areg(star)]+cont` (zero-width
  `Acheck` at a `BackForkAt` pc) are representable; their `BoolTreeLk` trees differ by a
  `Progress` wrapper. Real desync: in `(a+)+` first- vs re-traversal threads reach the same
  fork in the same ε-phase with different trees. `Progress` is leaf-transparent, so the fix is
  a QUOTIENT by `Progress`-erasure — machine-A's guard-planting canonicalization, transplanted.*
- *NEW, all PROVED first-try: `ProgErase` (the quotient map), `ProgEraseLeavesEq` (leaves
  invariant under erasure — memo-soundness), `ETreeRepLk` (the erased canonical LK tree, a
  least predicate keyed on `(code,pc,inp,b)` alone — `TR.TreeRepRE`'s rules with LK nodes KEPT
  and the two Progress-producing rules turned into stutters), `ETreeRepLkDeterm` (least-lemma
  mirror of `TreeRepDetermRE` — termination free by ordinal induction; this DISCHARGES the
  skip-case uniqueness need, replacing the false lemma).*
- *`TtLkSameTree` restated (bodyless, no callers): `ensures ProgErase(t1) == ProgErase(t2)`.*
- *Remaining for the skip machinery (build order): (a) the INIT bridge
  `ActionsRepFuelL + WalkOk + BoolTreeLk ⟹ ETreeRepLk(ProgErase(t))` — mirror of the PROVEN
  `ActionsTreeRepFRE` skeleton, simpler (no tstar construction/leaf-agreement), reusing the
  proven `CheckErase` toolkit (`BoolCheckInsert`/`BoolFlagLift`/`ShieldedActs`); WalkOk is fine
  init-only (`WalkOkEntry`); (b) re-key `PikeTreeLk`'s `pts_skip`/seen on erased trees,
  re-prove `PikeTreeLkComputesFirstLeaf` via `ProgEraseLeavesEq`; (c) carry the canonical tie
  `ETreeRepLk(ProgErase(tb_i), th_i.pc, th_i.exit_allowed)` per active head in `LiftInvC` +
  restate `SeenRepLk` on erased trees + tiny per-instruction `ETreeRepLkAt*` inversions
  (instruction-pinned, Fork arms now free via `e_choice`/`e_plus`); (d) resume `LiftStepC`.)*

*(2026-08-05 session 2 — the bridge LANDED; then the PLANTED pivot (supersedes (b)/(c) above):*
- *THE BRIDGE VERIFIED FIRST TRY (4285 assertion batches, 0 errors): `ActionsETreeRepFLk`
  (fueled, `{:isolate_assertions}`) + `AtBackForkETreeLk` (fused-fork companion) +
  `ActionsETreeRepLk` (wrapper). Supporting: `ProgErase` moved to `CheckErase.dfy` (whole file
  32/0) and `BoolCheckInsert` strengthened with `ensures ProgErase(tstar) == ProgErase(t)`
  (verified free — insertion is Progress-only).*
- *DESIGN CATCH: the erased-memo re-key of `PikeTreeLk` (step (b) above) is UNSOUND for
  lockstep — memoizing `ProgErase(head)` makes B wrongly skip the queued child `x` of a
  processed `Progress(x)` (the VM processes it at pc+1). Erased keys conflate stutter-pcs; the
  `Progress` wrapper IS the pc-discriminator.*
- *CORRECT DESIGN (machine-A's, in full): B runs the PLANTED canonical tree — unique per
  `(pc, ea)` AND stutter-discriminating — so `PikeTreeLk`'s exact-tree memo is UNCHANGED (its
  29/0 stands untouched). New+verified first-try: `TreeRepLkRE` (planted canonical LK least
  predicate, `TreeRepRE` rules verbatim with LK kept) + `TreeRepLkDetermRE` (least-lemma
  determinism — closes B's skip in lockstep). `ProgErase`/`ProgEraseLeavesEq` remain the
  ENDPOINT glue (`FirstLeaf(tcan) == FirstLeaf(t)`); the erased bridge is the SKELETON of the
  remaining planted constructor. Value layer unaffected: planted subtrees are `BoolTreeLk`
  trees of check-INSERTED stacks, so all proven cores still apply.*
- *(b′) DONE (commit `b6a5b59`, first try, 4291/0): the bridge CONVERTED into the value-returning
  planted constructor — `ActionsTreeRepLkF(...) returns (tcan)` + `AtBackForkTreeLkF` (companion,
  `ensures TreeRepLkRE(Progress(tcstar), pc, true)`) + `ActionsTreeRepLkRE` wrapper, ensuring
  `TreeRepLkRE(tcan, pc, EaOf(b))` and `ProgErase(tcan) == ProgErase(t)`. Machine B's canonical
  tree machinery is COMPLETE: construct `tcan` once at entry (WalkOkEntry), leaf-equal to the spec
  tree, unique per `(pc, ea)`, exact-tree memo unchanged.*
- *Remaining (task #15 → #11): (c′) LiftInvC: B runs `tcan` from init, per-head canonical tie
  `TreeRepLkRE(tb_i, pc_i, ea_i)`, `SeenRepLk` restated with `TreeRepLkRE` (+ re-prove the 4 seen
  bricks), skip via `TreeRepLkDetermRE`, steps via small `TreeRepLkRE`-At* inversions (Fork arms
  free via `tr_choice`/`tr_plus`); (d′) resume `LiftStepC`.)*

*(2026-08-07 update — (c′) COMPLETE, (d′) STRUCTURALLY COMPLETE (commits `11b405c..fd9c5cb`):*
- *(c′) LANDED, all first-try. KEY DESIGN CORRECTION: `tcan` is NOT `BoolTreeLk`-representable
  (the `min>0` forced-copy rule fixes the guardless continuation, so the planted first-arrival
  `Progress` at a backfork exists under NO action stack — the old note's "WalkPairLk for tcan via
  check-inserted stacks" is unrealizable). The fix: `ThreadRepLkC` = canonical tie
  `TreeRepLkRE(tcan, pc, ea)` + an ERASURE EXISTENTIAL (`exists traw :: ProgErase(traw) ==
  ProgErase(tcan) && ThreadRepLk(traw, gm, th)`) — the value layer rides raw witnesses, every
  proven core applies verbatim. `ActiveRepLkC`/`BlockedRepLkC` likewise; `SeenRepLk` + 4 bricks
  re-keyed on `TreeRepLkRE`; 5th brick `StutterSeenRepLk` added; `LiftInv` re-keyed canonical and
  gains `IsblockedRepLk` (Consume-dedup skip) + `ContextOkRE` (anchor/char branch alignment);
  `LiftInvC` = `PikeInvFullRE` + inp-link + `LiftInv`; `LiftInit`/`LiftInitC` construct and
  return `tcan` (`ActionsTreeRepLkRE` + `WalkOkEntry`), ensuring `ProgErase(tcan)==ProgErase(t)`
  (the endpoint FirstLeaf glue). The `TreeRepLkREAt*` inversion tier (10 lemmas): ALL EMPTY-BODY
  — instruction-gated rules collapse the disjunction; Fork arms free.*
- *(d′) `LiftStepC` FILLED (machine A whole-phase via `PSM.InvariantPreservationRE`, machine B via
  `LiftAdvanceEpsilon`, inp-link via both invariants' `InpOfCp` pins). `LiftAdvanceEpsilon`
  FILLED — the dispatcher mirrors `FAdvanceEpsilon` case-for-case over a new `LiftPreserve*Lk`
  case tier (+ `TrcLk` closure kit, `TreeRepLkREInRange`, `IsblockedGrowLk`, `WalkPairLkAtJmp`,
  `LiftDropDeadHeadLk`); `WriteOracle`/`CheckNullable`/`Fail` refuted by the canonical tie.
  CASES PROVEN (7): **Skip** (THE payoff — `TreeRepLkDetermRE` + `NoStutterCycle`), Stutter
  (Jmp/BeginLoop), Accept (BestTieLk straight from the head payload), EndLoopKill, AnchorKill,
  AnchorPass (the pass-case TEMPLATE: canonical inversion pins head+child; the erasure tie pins
  the raw witness's shape and transports the child pairing through `ThreadRepLkStepAnchor`),
  + the shared dead-head brick. CASES BODILESS (8): ConsumeAdd/ConsumeDrop, SetReg (needs the
  GmOfLive↔GMUpdate value tie), SetQuant (the NoDup research gap), Fork (branch pairing;
  backward = 2 B steps), GatePass (thread the per-lid static look-table package into the proven
  `ThreadRepLkStepCheckOracle`), NegGatePass, GateKill (bit⟺functional-verdict via the oracle
  column), EndLoopPass (needs a WalkPairLk-level EndLoop peel core — Anchor's core is the
  template).)*

*(2026-08-07 session 2 — FIVE MORE CASES PROVEN, all first-try (commits `6593664..e5b3a49`):
**11 of 15** ε-phase case lemmas now have real bodies. NEW: `GatePolarityRE`(+Min/Opt — the
static sweep: a `CheckOracle`/`NegCheckOracle` pc's lid is in `qm.looks` with the matching
polarity; `LookCheckIdsRE`'s skeleton, sourced from `NfaRepRE`'s polarity split + `LmapOk`),
`SeenAddProcessedSlotRepLk` (6th seen brick: mark a slot processed whose tree is already
memoized), `WalkPairLkAtEndLoop`/`Core` (the EndLoop peel with invariant threading — the guard
consumes with gm unchanged), `WalkPairLkAtNegCheckOracle`/`Core` (the negative gate's peel; the
passing merge is the IDENTITY so no AfterMerge). PROVEN: **GateKill** (both polarities — polarity
pin + `OracleOkAt` turn the failing bit into a `None` verdict = the canonical `LKFail` branch),
**ConsumeDrop** (pts_skip via `IsblockedRepLk`; the Consume rules are flag-independent so the
recorded flag transfers), **EndLoopPass** (`Progress` unwrap; the guard is erasure-transparent
on both sides), **NegGatePass** (identity merge; `LkResultGmIndep` moves the verdict to the
running map). REMAINING 4 bodiless: ConsumeAdd (BlockedRepLkC snoc through the `MatchingBlocked`
filter — mirror `PreserveConsumeAdd`), SetReg (GmOfLive↔GMUpdate tie), SetQuant (research gap),
Fork, GatePass. **GATEPASS DESIGN FINDING**: it SPLITS in two — (a) capturing positive
LOOKAHEAD: the proven `ThreadRepLkStepCheckOracle` applies, but its wiring needs (i) a per-lid
STATICS BUNDLE predicate (body/bodycode/`StaticOkRE`/`SizesOkRE`/`crv.f_look_*` indexing —
`LookRowsFromTablesL3a`-shaped) added to `LiftAdvanceEpsilon`+`LiftStepC` requires, and (ii) the
head thread's look-regs LENGTH (`ASize(look_regs) == nlook` — source per-active-thread as a
requires the dispatcher re-establishes inline, or from `PikeInvFullRE`'s `CM.VmRegsWf` at the
composite level); (b) CAPTURE-FREE positive looks (all lookbehinds + capture-free lookaheads —
`LkDir` may be Backward, so the core does NOT apply): the merge is the IDENTITY (a capture-free
body's `TreeRes` leaf map is its input map), but the `a_cp[l]` write still happens — needs a
small new inside-tie-across-the-write lemma (owner-split, `RL.ASetLaws`; `GateStepValue`'s
Case B is the exact pattern).)*

*(2026-08-07 session 3 — ConsumeAdd PROVEN (12/15) + THE COMPOSITE RESTRUCTURE (commits
`900ac92..20133c6`): `LiftAdvanceEpsilon` now CARRIES `ptsA` and steps machine A per worklist
step by the PROVEN `PSM.Preserve*Case` lemmas (exact mirror of `InvariantPreservationRE`'s body)
alongside machine B — so `PikeInvFullRE`'s per-thread facts (`ThreadNestRE`, backbones,
`LooksCapUnset`, `EaColdOkRE`) are available at EVERY intermediate state. This is what the
SetReg fill needs (`GmOfLiveOpenGMOpen`'s MxAtGid/PathPresent hypotheses) and the GatePass fill
too; the interim hand-threaded `PSM.BBOf` layer was subsumed and removed. `LiftStepC` is now a
single call. New: `BlockedRepLkCSnoc`. Remaining bodiless cases: SetReg (mirror
`PSM.PreserveOpenCase`'s hypothesis-discharge recipe, th-facts passed from the dispatcher's
`PikeInvFullRE`), GatePass/its statics bundle, Fork, SetQuant (research gap).)*

*(2026-08-07 session 4 — SETREG + GATEPASS PROVEN (14/15) (commits `7c25e8e`, `99939aa`):
**`LiftPreserveSetRegLk`** — the dispatcher's SetReg case runs `PSM.OpenStepThreadRE`/
`CloseStepThreadRE` on `ptsA`'s head (the composite-restructure payoff) and hands the
register-level gm effect (`GmOfLive` across the write == `GMOpen`/`GMClose` keyed by `reg`
parity, gid = `reg/2`) to the case lemma as a requires; inside, the written gid is OUTSIDE-look
(`CaptureWriteIdsOutsideRE` + parity pin + `CapIdsLooksDisjoint`) hence outside
`S == CapIdsInLooks(re)` (NEW requires threaded through `LiftAdvanceEpsilon`/`LiftStepC`), so
both value maps move by the SAME `GMUpdate` at cp: outside tie pointwise, inside witnesses
verbatim.
**`LiftPreserveGatePassLk`** — canonical LK head (verdict from the walk lemma's `LkGateOk`;
`tlk` pinned functionally `== ComputeTr` on BOTH layers ⟹ merged maps coincide), split by the
lid's static flavour via the NEW **`GateStaticsOk`** per-lid bundle (LookEntryOk row +
`qm.looks[l]` == the row's translation + body `StaticOkRE`/`SizesOkRE` + inside-look
confinement + capture-free for non-Lookahead flavours; threaded as a requires, to be
ESTABLISHED at composite entry from `FFullCompilation` — still owed): capturing Lookahead →
proven `ThreadRepLkStepCheckOracle` (qt := th.quant_regs, ngroups := 0 unconstrained);
positive Lookbehind → capture-free identity-agreement merge (`LkResultAgreeOutside` over the
empty set) + `GmtTieOutsideAfterGate` + Case-B witness carry across the l-only look-reg write;
negatives refuted by `GatePolarityRE`. `WalkPairLkAtCheckOracle(Core)` EXTENDED with the gate's
own `GateAheadClear` instance (pending at the real head ⟹ body groups absent from gm).
New threading: `!rer.ignoreCase` + `GateStaticsOk` + `S == CapIdsInLooks(re)` on
`LiftAdvanceEpsilon`/`LiftStepC`; `ThreadRegsWf` handed down at the pass case.
REMAINING ε-cases: Fork + SetQuant — BOTH now blocked on the SAME star-transient design gap
(the free-star iteration arm parks a thread at the `SetQuantToClock`/`BeginLoop` pcs where NO
`ActionsRepL` exists, so `ThreadRepLk`'s raw erasure witness is UNSATISFIABLE there; candidate
fix: add instruction-gated SQC-Reset see-through disjuncts to `WalkPairLk` mirroring the
BeginLoop stutter disjunct) + the quantifier-NoDup gap (iteration-arm acts duplicate
`DefGroups(r1)`; option D: static `LmOfBodiesDisjoint` + `GMReset` re-arm). Also still owed:
the `GateStaticsOk` establishment lemma (compile-side sweep).)*

*(2026-08-07 session 5 — THE QUANTIFIER GAP IS CLOSED (carrier redesign) + SETQUANT PROVEN
(15/16). FINDING: the old `NoDupSeq(AllDefsActs)` walk carrier was FALSE after any quantifier
unfold (the forced copy duplicates `DefGroups(r1)`), so `LiftPreserveForkLk`/`SetQuantLk` were
FALSE AS STATED and LiftInv was vacuous mid-loop for ANY grouped quantifier (`(a)*` suffices).
FIX (all PROVEN, no debt): (1) carrier REPLACED by `WalkDefsOk` = (C1) `NoDupSeq(
TopLkDefsListActs)` — `TopLkDefsList` REDEFINED to also carry `Group` ids ([gid] +) so the
Open-crossing freshness stays derivable; (C2) per-action `NoDupSeq(DefGroups)`; (C3)
`QuantsClearActs` — per-action `QuantsRightClear(r, TopLkSet(rights))`, Sequence widens the
left arm's R, Quantified STOPS with its own clause `DG(body) ∩ R = ∅` — THE UNFOLD'S OWN
freshness fact, which is why preservation closes (incl. NESTED quantifiers):
`QuantsRightClearFromNoDup` re-establishes C3 for the copy from C2 + the folded node's clause.
Bricks: `WalkDefsOk{Tail,SeqExpand,GroupExpand,Entry,Unfold}` (Unfold takes `mid ∈ {[],
[Acheck]}` — forced-copy and star-arm shapes). CheckOracle merge req-4 now derives from C1
(`RegexTopGateSubTopLk` + `TopLkDefsListMemberSub`) — simpler than the old NoDupConcat route.
(2) SQC SEE-THROUGH disjuncts added to `WalkPairLk` AND `TtLk` (star/backfork iteration arms
park threads AT the `SetQuantToClock` pc where no `ActionsRepL` exists): instruction-gated,
child at `GMUpdate(Reset(qm.quants[q]), ·)`; `WalkPairLkImpliesTtLk`/`TtLkAtSetQuant`
restructured for the third disjunct; all other inversion wrappers auto-refute it.
(3) **`LiftPreserveSetQuantLk` PROVEN** (first try): canonical `TreeRepLkREAtSetQuant` refutes
`bq`; raw layer via NEW `WalkPairLkAtSetQuant(Core)` (forced-copy actions route with
`QuantHeadSQCPin` + `QuantForcedContRep` + Reset-re-established GateAheadClear + the Unfold
brick ∥ see-through route); value ties: both maps shed the same `GMReset(qm.quants[q], ·)`
(A-side effect via `PSM.ResetStepThreadRE`), inside witnesses carry verbatim (look regs
untouched). Dispatcher effect derivations extracted to `DispatchSetRegEffect`/
`DispatchResetEffect` (the dispatcher's single VC had hit the 900s limit).
REMAINING ε-case: **Fork only.** FORWARD forks (Disjunction + star arms) are closeable with
today's machinery — the star arm chains SQC-disjunct → BeginLoop-absorber (any incoming flag)
→ the arm list at `CannotExit`. The BACKWARD (do-while) arm has NO BeginLoop absorber: the arm
thread runs the body at `exit_allowed == true` while `BoolTreeLk`'s iteration tree is built at
`CannotExit` — needs ONE new fact, `BoolTreeLk` FLAG-SHIELD for NonNullable bodies (every
path to the guard crosses a Read, which re-arms the flag; `NUL.NonNullableL(r1)` is available
at the seam). That shield + a `WalkPairLkAtForkCore` (Disjunction arms via sub-multiset C1;
star arms via the disjunct chain + `WalkDefsOkUnfold` with `mid=[Acheck]`; backward via
Acheck-peel recursion + the shield; `ea` pinned by the dispatcher from `EaColdOkRE`) is the
whole remaining ε-surface.)*

*(2026-08-07 session 6 — THE ε-PHASE IS COMPLETE (commits `98696ea..8ec8e3e`, full sweep
**4592 verified, 0 errors**): **`LiftPreserveForkLk` PROVEN** (forward one B step; backward
two, `ea` pinned from `EaColdOkRE`; `WalkPairLkAtForkCore` = the full branch pairing —
Disjunction via `DisjArm` bricks, star arms via the SQC-chain with the BeginLoop absorber,
the do-while loop-view via the shield); **`BoolTreeLkGuardShield` PROVEN** (the NonNullable
head at index 0 shields every `Acheck` — `CE.ShieldedActs` witness j=0 — so the proven
`CE.BoolFlagLift` closes it): ZERO bodiless walk debt remains. **`GateStaticsOk`
ESTABLISHED**: `GateStaticAt` factoring + `PlusFragmentIsLBF`/`LookFreeNoLids` +
`GateStaticsSweepRE` (all per-lid facts descend definitionally; body compile statics via
`CompileToBytecodeRepLookBehind`+`CompileStutterTameRE`) + `GateStaticsFromTables` (requires:
compile tables via `LTB.FFullCompilationLookOk` + the qm-domain bound, both dischargeable at
MainTheorem integration). REMAINING L3a: the 4 top-level drivers (`LiftConsume` /
`LiftFindMatch` / `LiftEndpoint` / `L3aCompositeClose`), then the MainTheorem else-branch
rewrite; prune dead `TtLkSameTree`.)*

*(2026-08-08 session 7 — **THE COMPOSITE SPINE IS COMPLETE** (commit `644582c`, full sweep
**4599 verified, 0 errors**): `BlockedRepLkC` strengthened to a REACTIVATABLE payload
(`WalkPairLk` at the advanced input via the new `WalkPairLkAtConsume(Core)`; ConsumeAdd/Snoc
rewired); `BlockedToActiveLkC`; **`LiftFindMatchC` PROVEN first try** (whole-search composite
mirroring `PSM.FindMatchSimRE`, both machines in lockstep, consume phase re-establishing both
invariants); **`L3aCompositeClose` PROVEN first try** (`LiftInitC` → `LiftFindMatchC` →
`PikeTreeLkComputesFirstLeaf(tcan)` via the new `PikeSubtreeLkEraseIff` + FirstLeaf glue).
The pre-composite `LiftConsume`/`LiftFindMatch`/`LiftEndpoint` scaffolds DELETED. LiftSim.dfy
now has NO bodiless lemmas except the dead restated `TtLkSameTree`. REMAINING FOR L3: only the
MainTheorem else-branch integration per the (F) recipe — discharge `L3aCompositeClose`'s
requires (`GateStaticsFromTables` + `LTB.FFullCompilationLookOk` + qm-domain + genuine-start
vms fields), hook `L3aValueBridge` into `MainExtraction`, delete `LkBodyGroupsEmpty`/
`FilterUnmoved`/L1 `LookRowsFromTables`, whole-package verify.)*

---

## 0. The goal

Prove `MainTheorem` for **capturing positive lookaheads (L3)**: the engine's reconstructed
capture array equals the ECMAScript spec tree's first-leaf capture array.

The endpoint is **`M.MainExtraction`** (`MainTheorem.dfy:4766`, PROVED). It already discharges
the top-level spec obligation *given* two facts about the winning thread `thread` and the spec
tree `t`:

1. `leaf.1 == PIV.GmOfLive(re, thread.capture_regs, thread.look_regs, thread.quant_regs)`
   — the spec tree's first-leaf group-map equals the thread's live capture map, **and**
2. `FFullMatch == filter_reset(annotate(raw), thread caps…, res.0/1/2)` — the engine result is
   the reconstructed unfold (this is `M.FBuildCaptureUnfoldL3a`, `:4736`, PROVED).

So **all of L3 reduces to establishing fact (1) for the winning thread**, where — this is the
L3-specific twist — the capture map must carry the *merged look-body values*, reconstructed by
`FLookLoop` (`res.0`), not the raw thread registers. The whole campaign is the machinery that
produces fact (1).

---

## 1. Architecture — the thread-anchored composite

`LiftInvC` (`LiftSim.dfy:4040`, PROVED as a definition) is the settled top-level invariant:

```
LiftInvC  :=  PSM.PikeInvFullRE(ptsA, vms)                    // machine-A: VM ↔ tstar, PROVEN engine
           ⊕  ( ActiveRepLk(ptsB, vms.active)                 // machine-B: LK-tree ↔ VM thread (index-wise)
              & BestTieLk & OracleOkSuffix )
```

Two tree machines advance in lockstep over the *same* VM worklist:

- **Machine A** (`ptsA`/tstar): the gate-transparent Pike tree. Rides the **already-proven**
  engine simulation — `PSM.PikeInvFullRE` (`PikeSimRE.dfy:831`), `PSM.InvariantPreservationRE`
  (`:2461`), `PSM.FindMatchSimRE` (`:3041`). Supplies VM run / termination / well-formedness /
  the outside-lookahead winning tie for free. **We never re-prove the engine.**
- **Machine B** (`ptsB`): the **LK-aware** Pike tree, `PTL.PikeTreeStepLk` (`PikeTreeLk.dfy:71`),
  whose nodes carry lookaround results. Its endpoint `PTL.PikeTreeLkComputesFirstLeaf` (`:885`,
  PROVED) pins a completed B-trace to `FirstLeaf(t)` — the spec tree's first leaf.

The B-tree pairs with the VM thread **index-wise via `ThreadRepLk`/`ActiveRepLk`**, never with
the tstar tree (that "leaf-agreement" route was a dead end — `ActionsTreeRepFRE` erases the LK
head). Each thread carries a `WalkPairLk` walk plus two value ties: `GmtTieOutside` (groups
outside looks) and `GmtTieInside` (groups inside looks — the L3 content).

---

## 2. What is PROVED, organized by contribution to fact (1)

### A. The value crux — one gate's inside-look value step
This is the heart of L3: it proves that crossing a positive lookahead ties the thread's
`a_cp[l]` write to the LK-node value merge, and that the merged value equals the spec's fresh
look replay.

| Lemma | line | role |
|---|---|---|
| **`GateStepValue`** | 526 | **THE CRUX.** At a `CheckOracle(l)` crossing (thread write `a_cp[l]:=cp`, map `gm→gm2`), lifts `GmtTieInside` across the gate. Instantiates the keystone `M.LkReplayMatchesSpec` (`MainTheorem.dfy:4253`); owner-splits `g∈S` by lid. Position tie is automatic (`cp` is both the write and the gate's input). |
| `LkResultAgreeOutside` | 439 | a positive gate's merged map differs from `gm` **only** on `DefGroups(r1)` — the frame that lets `GateStepValue` carry non-owned groups unchanged. |
| `GmtTieOutsideAfterGate` | 1107 | the outside-`S` value frame across a gate (chains `LkResultAgreeOutside` + `PIV.GmOfLiveLookIndep`). |

### B. The value assembly — winning leaf ⇒ reconstructed captures
Turns "the ties hold at the winning leaf" into fact (1) itself.

| Lemma | line | role |
|---|---|---|
| `WinningGmtTieOutside` | 3841 | outside-`S` half — essentially free from `BestMatchRE` + `FirstLeafAgreeOutside`. |
| `InsidePresentResBridge` | 3895 | inside-`S` present-value equality: `leafgm[g] == GmOfLive(re, res0, res2)[g]` via `GmtTieInside` + `M.GmOfLiveInsideLookPresentEq`. Uses reconstructed `res2` (quant clocks), not raw thread clocks. |
| **`L3aValueBridge`** | 3956 | **the assembler:** `GmtTieOutside` + `OutsideLookValueBridge` (outside) + packaged inside-present + reverse/absent ⇒ `leafgm == GmOfLive(re, res0, look, res2)` = **fact (1)**. |
| `FreshBodyMatchCapWf` | 3865 | discharges thread register well-formedness (`FreshMatchWf`). |

### C. Per-instruction walk inversions — `TtLkAt*` (all 10, PROVED)
Given the B-walk `WalkPairLk`/`TtLk` at a pc, these read off the B-tree's shape and relocate the
walk to the continuation, per VM instruction:

`TtLkAtJmp`(1016) · `TtLkAtBeginLoop`(1038) · `TtLkAtAccept`(1334,+Core 1210) ·
`TtLkAtConsume`(1487,+Core 1353) · `TtLkAtSetReg`(1654,+Core 1558) ·
`TtLkAtSetQuant`(1851,+Core 1746) · `TtLkAtCheckOracle`(1977,+Core 1877) ·
`TtLkAtAnchor`(2784,+Core 2702) · `TtLkAtEndLoop`(2889,+Core 2803) · `TtLkAtFork`(3027,+Core 2908).

Support: `NfaRepMinLHeadPin`/`NfaRepOptLHeadPin`/`NfaRepLAtJmpTransparent`/`ActionsRepLThruJmp`
(867–990), `QuantHeadPins*` (1290/1442/1508), `QuantForcedContRep` (1679), `BoolTreeLkDeterm`
(315, the same-`acts` determinism core).

### D. Per-instruction B-machine cores — carry the invariant through a step
The `WalkPairLkAt*` cores thread `GateAheadClear` through each step; the `ThreadRepLkStep*`
preserve one thread's full pairing.

| PROVED | line | note |
|---|---|---|
| `WalkPairLkAtBeginLoop` / `ThreadRepLkStepBeginLoop` | 1060 / 1085 | BeginLoop is walk-absorbed (stutter). |
| **`WalkPairLkAtCheckOracleCore` / `…CheckOracle` / `ThreadRepLkStepCheckOracle`** | 2042 / 2226 / **1147** | **the gate core** — self-contained; invokes `GateStepValue` for the inside tie, `GmtTieOutsideAfterGate` for the outside frame. |
| `WalkPairLkAtAnchorCore` / `…Anchor` / `ThreadRepLkStepAnchor` | 2258 / 2358 / 2380 | the peel-based non-gate template. |
| `WalkPairLkAtSetRegCore` / `…SetReg` | 2499 / 2653 | group open/close ↔ `GMUpdate`. |
| `WalkPairLkAtAccept`, `WalkPairLkAtFork`, `WalkPairLkImpliesTtLk` | 2425 / 2687 / 2401 | shape cores via the `WalkPairLk⟹TtLk` bridge. |

### E. Invariant machinery (PROVED)
- **`GateAheadClear`** family (the absence invariant that feeds `GateStepValue`): `AfterReset`
  (3053), `AfterOutside` (3071), `AfterMerge` (3110), `Mono` (2439), `AfterOpen` (2451),
  `Tail`/`SeqExpand` (3153/3188), plus `GatePending*` and `RegexTopGateSub{Defs,LkBody,TopLk}`.
- **NoDup converter chain** (the group-uniqueness reduction; last five added 2026-08-04):
  `TranslateDefGroupsNoDup` (3578) · `NoDupAltCon` (3553) · `NoDupAllDefsTail` (2019) ·
  `TopLkDefsListSubDefGroups` (3353) · `TopLkNoDupFromDefGroups` (3375) ·
  `TopLkDefsListActsSubAllDefs` (3439) · `TopLkNoDupFromAllDefs` (3456) ·
  `QuantUnfoldTopLkNoDup` (3503).

### F. Entry, endpoint plumbing, tree computation (PROVED)
- `LiftInit` (660) — the standalone initial pairing.
- **`LiftInitC` (4066) — the *composite* initial pairing. PROVED** *(its inline `BODILESS`
  comment is stale — the body is present and verifies).*
- `PikeSubtreeLkComputeTr` (3813) + `ComputePikeSubtreeLk` (3689) + `TranslateNoBackref`
  (3666) — the LK-aware fuel induction computing the B-tree.

---

## 3. What remains — the entire uncovered surface

### 3a. Bodyless lemmas (7) — `ensures` currently assumed
These are the **simulation drivers** that thread the proven per-instruction cores (§C/§D)
through the worklist recursion and the whole run. They are *engineering* (mirror the proven
machine-A analogs), not new semantics — **except** where noted.

*(2026-08-07: `LiftStepC` and `LiftAdvanceEpsilon` are now FILLED — the remaining surface is
the 8 bodiless `LiftPreserve*Lk` ε-phase case lemmas (see the update note above) plus the rows
still marked bodiless below.)*

| bodyless | line | what it must do | mirror |
|---|---|---|---|
| ~~`LiftStepC`~~ | — | **FILLED 2026-08-07** (A whole-phase driver ∥ B recursion). | `PSM.InvariantPreservationRE` (`:2461`) |
| `L3aCompositeClose` | 4155 | **top-level:** drive `LiftInitC → LiftStepC* → PTS_final`, yielding `BestTieLk(FirstLeaf(t), result)` for the winner — the single sim output feeding §B. | `PSM.FindMatchSimRE` (`:3041`) + `PTL.PikeTreeLkComputesFirstLeaf` |
| ~~`LiftAdvanceEpsilon`~~ | — | **FILLED 2026-08-07** (dispatcher over the `LiftPreserve*Lk` tier; 7 cases proven, 8 bodiless). | `AI.FAdvanceEpsilon` |
| `LiftConsume` | 758 | consume/next-char phase (`pts_nextchar`, blocked→active). | `FConsume` |
| `LiftFindMatch` | 774 | whole-run driver (standalone). | `FFindMatch` |
| `LiftEndpoint` | 800 | endpoint extraction to `FirstLeaf`. | — |
| `TtLkSameTree` | ~865 | RESTATED 2026-08-05 (exact-tree version FALSE): now `ensures ProgErase(t1)==ProgErase(t2)`. The skip case no longer routes through it — the canonical determinism + tie close the skip directly (DONE in `LiftPreserveSkipLk`); this wrapper is now likely DEAD — prune at cleanup. | — |

*Note the two driver layers:* the **composite** spine (`LiftInitC`✓ → `LiftStepC` → `L3aCompositeClose`)
is the settled top; the **standalone** `LiftAdvanceEpsilon/Consume/FindMatch/Endpoint` is the
per-phase implementation the composite step consumes. Filling `LiftStepC`/`L3aCompositeClose`
is the shortest path to the goal, since §B is already proved and takes over at `BestTieLk`.

### 3b. Stubbed predicate (1)
- **`SeenRepLk`** (275) — body is `true`. Makes the seen/skip (memoization) tracking vacuous.
  Must be made real (mirror `PIV.SeenInclusionRE`) before a driver's `pts_skip` case is sound.

### 3c. The one research gap — quantifier NoDup
The proven gate core (§D) consumes a `NoDupSeq(AllDefsActs)` invariant that `WalkPairLk` carries,
`LiftInit(C)` establishes, and the non-quantifier cores preserve. It **breaks only at a
quantifier unfold** (`[Areg(r1), Areg(Quantified(min-1,r1))]` duplicates `DefGroups(r1)`), which
is exercised by the not-yet-built `WalkPairLkAtSetQuant` / Fork-iteration cores inside
`LiftAdvanceEpsilon`. The converter chain (§E) reduces this to
`NoDupSeq(TopLkDefsListActs)`, whose remaining obligation is a walk-structural fact — "reachable
`acts` have distinct top-level pending-gate lids" — that does **not** self-maintain and needs an
acts↔re correspondence that is currently absent (forced-copy quantifiers duplicate lids, so the
naive "distinct positions → distinct lids" is false). **Recommended next attempt (option D):**
source the gate's absence hypothesis locally from static `M.LmOfBodiesDisjoint`
(`MainTheorem.dfy:4421`, all re-looks pairwise-disjoint) + the quantifier `GMReset`, sidestepping
the correspondence. See the `linden-l3-campaign` memory for the full analysis.

---

## 4. Reused proven infrastructure (not our obligations — already green)

- **Engine simulation:** `PSM.PikeInvFullRE` (831), `PSM.InvariantPreservationRE` (2461),
  `PSM.FindMatchSimRE` (3041), `PSM.PreserveForkCase` (1119), `PSM.PreserveSkipCase` (861),
  `PSM.PreserveOraclePass` (2036), `PSM.InitialPikeInvFullRE` (3237).
- **Spec tree machine:** `PTL.PikeTreeStepLk` (71), `PTL.PikeTreeLkComputesFirstLeaf` (885).
- **Value keystone + assembly (MainTheorem):** `LkReplayMatchesSpec` (4253), `MainExtraction`
  (4766), `FBuildCaptureUnfoldL3a` (4736), `FirstLeafValueConfined` (1563), `FirstLeafClosed`
  (1273), `OutsideLookValueBridge` (1139), `GmOfLiveInsideLook{Present,Absent}Eq` (1215/1182),
  `FLookLoop{Capture,Quant,Filter}Frame` (2936/3020/2861), `LookRowsFromTablesL3a` (4583),
  `LmOfBodiesDisjoint` (4421), `LmOfInvL3a` (4349).
- **Static uniqueness / compiler adherence:** `PIV.CapUnique`/`CapIds` (1281/1264),
  `PIV.LookCheckIdsRE` (3650, + Min/Opt), `LTB.LookUnique`/`LookIds` (LookTables 54/37),
  `M.TranslateDefGroupsEqCapIds` (1080).

---

## 5. Bottom line

The **hard semantic content of L3 is proved**: the per-gate value step (`GateStepValue`), the
full value assembly to fact (1) (`L3aValueBridge` & co.), all 10 per-instruction walk
inversions, the per-instruction B-machine cores for every non-quantifier instruction, the
`GateAheadClear` invariant machinery, and the NoDup converter chain — 159 verified conditions.

What is **left is the driver assembly** (7 bodyless lemmas — mostly "run the proven cores through
the recursion," shortest path via `LiftStepC`/`L3aCompositeClose`), making **`SeenRepLk`** real,
and the **quantifier-NoDup** research gap that blocks the `SetQuant`/Fork-iteration cores. None of
the *proved* pieces depend on the research gap — it only gates extending the simulation over
capturing-look quantifiers.
