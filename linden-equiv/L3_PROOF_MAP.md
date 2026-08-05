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
- *Remaining (task #15): (b′) convert the bridge to the value-returning planted constructor
  `ActionsTreeRepLkF(...) returns (tcan)` ensuring `TreeRepLkRE(tcan, pc, EaOf(b))` and
  `ProgErase(tcan) == ProgErase(t)`; (c′) LiftInvC: B runs `tcan` from init, per-head canonical
  tie `TreeRepLkRE(tb_i, pc_i, ea_i)`, `SeenRepLk` restated with `TreeRepLkRE`, skip via
  `TreeRepLkDetermRE`, steps via small `TreeRepLkRE`-At* inversions; (d′) resume `LiftStepC`.)*

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

| bodyless | line | what it must do | mirror |
|---|---|---|---|
| `LiftStepC` | 4131 | one ε-phase of the **composite**: step `ptsB` by `TrcPikeTreeLk`, preserve `LiftInvC` across `FAdvanceEpsilon`. | `PSM.InvariantPreservationRE` (`:2461`) |
| `L3aCompositeClose` | 4155 | **top-level:** drive `LiftInitC → LiftStepC* → PTS_final`, yielding `BestTieLk(FirstLeaf(t), result)` for the winner — the single sim output feeding §B. | `PSM.FindMatchSimRE` (`:3041`) + `PTL.PikeTreeLkComputesFirstLeaf` |
| `LiftAdvanceEpsilon` | 739 | per-ε-phase over the *standalone* `LiftInv`; worklist recursion dispatching the §C/§D cores. | `AI.FAdvanceEpsilon` |
| `LiftConsume` | 758 | consume/next-char phase (`pts_nextchar`, blocked→active). | `FConsume` |
| `LiftFindMatch` | 774 | whole-run driver (standalone). | `FFindMatch` |
| `LiftEndpoint` | 800 | endpoint extraction to `FirstLeaf`. | — |
| `TtLkSameTree` | ~865 | RESTATED 2026-08-05 (exact-tree version FALSE): now `ensures ProgErase(t1)==ProgErase(t2)`. The skip case no longer routes through it — `ETreeRepLkDeterm` (PROVED) + the canonical-tie invariant close the skip directly; this wrapper needs the init bridge. | — |

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
