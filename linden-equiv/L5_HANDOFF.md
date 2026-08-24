# L5 HANDOFF — nested capturing lookBEHIND

**Branch:** `l4-nesting` (NEVER merge to main / push to origin — not authorized).
**Predecessors:** L4 (nested capturing lookAHEAD, COMPLETE — `FULL_DEPTH_K_HANDOFF.md`); L3b (depth-1
capturing lookbehind, COMPLETE — `L3B_HANDOFF.md`). Running log: `L4_L5_ROADMAP.md` (read its
END sections). This file is the L5-specific resume artifact; on conflict, the roadmap's latest dated
section wins.

**Verify** (from `linden-equiv/`):
```
dafny verify --standard-libraries \
  --library=deps/{linden-engine,linden-engine-model,linden-reasoning,linden-semantics-core,linden-warblre,regex-engine}.doo \
  --allow-warnings --verification-time-limit=250 --filter-symbol=<Mod.Sym> src/Equiv/<F>.dfy
```
`deps/*.doo` are gitignored/rebuildable; commit only `.dfy`. Cross-project (linden-reasoning) rebuild
recipe: `cd linden-reasoning && lem build && lem pack && cp linden-reasoning-*.doo
../linden-equiv/deps/linden-reasoning.doo`. Filter-symbol is a PREFIX match (one flag only); "0
verified" usually means a wrong module name (`LindenElk*`). Commit at each green rung
(`[[linden-commit-cadence]]`).

---

## 1. WHAT L5 IS

L5 = a **positive lookBEHIND whose body may contain nested capturing lookarounds**, e.g.
`(?<=a(?<=b)(c))`. Two independent obligations for such a look at column `cp`:
- **GATE** — does the lookbehind PASS? (oracle correctness) — **DONE, green.**
- **CAPTURES** — what does its body capture? (the value tie) — **NOT DONE. The real remaining work.**

The current forward-only gate is `NoPosLookbehindRaw` (NfaRepRE.dfy:615) / `FwdPosLooksL`
(MainTheorem.dfy:2178) = "positive looks are forward-only". L5 lifts it to admit positive
lookbehinds. The engine/tables are ALREADY direction-generic (FLookLoop / FFindMatchPlus /
oracle_regex / LookEntryOk run nested lookbehinds backward today); the restriction is a proof gate,
not an engine limitation.

---

## 2. STATUS SUMMARY

| Piece | Status |
|---|---|
| (A) SPAN/SUCCESS side — `Bwd*`/`SpanDuality*LB`/`GroupOkLB` (linden-reasoning) | ✅ green |
| GATE side — oracle correctness for nested lookbehind (`OracleColumnSpecNested`) | ✅ green |
| T1 — `GmOfLiveXRev` bridge; T2a — `BackwardReplayMirrorNested` (engine mirror) | ✅ green |
| CAPTURES — the value tie (`LkReplayMatchesSpecLBNested`) | ❌ **the wall (see §4, §5)** |
| Tree-mirror attempt (TreeMirrorLk.dfy bricks 1-3) | ⚠️ **VACUOUS — dead-end (see §4)** |
| Integration — lift `NoPosLookbehindRE`, drop `assert false`, API | ❌ not started |

---

## 3. THE GATE SIDE — COMPLETE (green)

Direct-backward oracle route, NO mirror/simulation. The nested-lookbehind GATE is oracle
correctness, unblocked by (A). Chain (all green, `OracleEntry.dfy` full-file 43/0):
- `MatchesV` (OracleBridgeV, from L4 V-work): nesting-aware span predicate; treats a nested look as a
  zero-width ORACLE gate `view_get_oracle(ov, i, lid)`, direction-generic.
- **`MatchesVTransfer`** — `MatchesV(re) <==> MatchesL(Translate(re))` for `GroupOkLB` bodies. Look
  case = `MatchesV`=oracle bit; `LL.OracleOkAt` (direction-generic, `LkDir`; `LL.OracleOkAtGet`
  instantiates its per-lid forall) equates bit to the body BACKWARD walk; `SpanDuality{Complete,
  Sound}LB` equates walk to a body span = `MatchesL`'s lookbehind clause. `LookGateSpec` writes the
  gate chain WITNESS-BASED (never `oracle <==> ∃m` in bulk — trigger friction).
- **`RecorderHitVBackWalk`** — RecorderHitV(body) <==> backward walk.
- **`FBuildOracleCorrectAtNested`** — oracle bit <==> `ReachesWriteV` (nested oracle-build), off
  `FBuildOracleCorrectAboveNested` + `LidReachesVFinal` (+ `LookTablesLidDirForwardNested`).
- **`OracleColumnSpecNested`** (the CAPSTONE) — for a nested-lookbehind body, oracle bit at (cp,lid)
  <==> `Translate(body)` BACKWARD walk from cp succeeds. Direct-backward analogue of the look-free
  `OS.OracleColumnSpec`; what §6.5 `OracleOk`/`StaticOkRE` consumes for a nested column.

This does NOT need the captures. It is the finished half of L5.

---

## 4. ⚠️ THE TREE-MIRROR ATTEMPT (this session) IS A VACUOUS DEAD-END

A large spec-side "nested tree mirror" was built in **`src/Equiv/TreeMirrorLk.dfy`** (module
`LindenElkTreeMirrorLk`, ~1900 lines, verifies 100/0) — DO NOT trust its mirror lemmas.

**It is VACUOUS for nested bodies, PROVEN by `GateAgreeIsFalse` (verified, in the file).** The
mirror's central premise `GateAgree(rer, lk, r1, inp2)` compares `backward-walk(r1)@inp2` to
`backward-walk(RevL(r1))@SwapInput(inp2)`. **`SD.SwapInput` merely swaps pref<->next**, so the
RevL-side backward read hits `inp2.next[0]` (char AFTER the point) while the original hits
`inp2.pref[0]` (char BEFORE) — OPPOSITE SIDES. Disproved at `Input(['b'],['a'])`: LHS reads 'a'
(Some), RHS reads 'b' (None). Therefore `RegLookGatesMirror`/`ActsLookGatesMirror` are FALSE for any
nested capturing lookbehind, and every lemma gated on them is vacuous:
- **VACUOUS (green only because the premise can't hold):** `TreeMirrorRelLk`, `TreeResMirrorLk`,
  `InnerGateAgree`, `LookGateAgree`, `ComputeTreeReverseLk`/`ComputeTrReverseLk` (the "builder"),
  `RegLookGatesMirrorDischarge`, `OracleColsOkRE`, `LookGateDischargeOne`, `BackBodyGmTieNested`.

**Root cause:** built on the `ComputeTr` RE-WALK tree. The RE-WALK tree canNOT mirror for nested looks
(the documented dead-end `4b829b9`): a nested lookbehind is walked in its intrinsic `LkDir`=Backward
on BOTH sides (RevL is NO-FLIP), reading opposite sides of the point. Note `LkGateOk` in `BoolTreeLk`
ALSO re-walks (it is `ComputeTr`+`LkResult`, NOT the oracle) — so `BoolTreeLk` does NOT mirror either.
The ONLY tree whose inner gates are position-consistent oracle bits is the ENGINE tree
(`tstar`/`TreeRepRE`), and its mirror IS the engine mirror T2a.

**SOUND / REUSABLE from TreeMirrorLk.dfy** (mirror-independent, general ComputeTr-tree facts — keep):
- `ComputeTrGateStable` (+ `LookGateStableAt`) — every LK node's gate is gm-constant.
- `ComputeTrGActsOutside` (+ `RegOpensOutside`/`ActsOpensOutside`) — surface Opens avoid a set.
- `ComputeTrCloseDiscLk` (+ `StackInvLk`, the `PikeLkActionsRec` twin of CD's `StackInv`/`ClosesActs`
  machinery + the LK case) — LK-aware close discipline.
- `TreeResGmInBounds`, `ConfinedLeafAgree`/`ConfinedNoGid`, `MirrorGmAgreeOutside`,
  `RegOpensOutsideFromNoDup`, `NoDupGSuffix`/`NoDupGNotBoth`, `LkBodyGroupsRevL`,
  `RevLPreservesPikeLkRec`, `GroupFreeLIsPikeLkRec`, `LkBodyGroupsSubDefsLocal`, `AdvanceInputNLen`,
  `GMUpdateInBounds`.
- The relation/fold `TreeMirrorRelLk`/`TreeResMirrorLk` and the establishments are correct AS
  MACHINERY; they just can't be instantiated for the nested mirror. If the correct route re-uses a
  fold over the ENGINE/checked tree, these confinement/close-discipline/bounds facts may port.

---

## 5. THE CORRECT CAPTURES ROUTE (the genuine remaining work = "the wall")

`LkReplayMatchesSpecLBNested` — the per-lookaround value keystone. Nested analogue of the depth-1
`LookBehindKeystone.dfy:LkReplayMatchesSpecLB` (which required `LookFreeRE`). It is NOT a widening of
the L3b mirror keystone — it is a **DIRECT engine-backward ↔ spec-backward tie**:
- **SURFACE gids** (`DefGroups(tr) \ LkBodyGroups(tr)`): reconciled by the engine mirror T2a
  (`BackwardReplayMirrorNested`, BackValue.dfy — the oracle-gated mirror at the ENGINE level, which
  DOES hold for nested because the engine reads position-indexed oracle bits, not re-walks).
- **INNER-look gids** (`LkBodyGroups(tr)`): reconstructed by the direction-generic BACKWARD ORACLE at
  ORIGINAL positions (no RevL mirror) — the L4 `recon_inner`/`FLookLoop` pattern.

The load-bearing missing piece is a **`WP.Backward` twin of the L4 forward capture apparatus**
(`BodyTreeAtCpNested` MainTheorem.dfy:3836 is the template) that ties the backward engine run `raB`
of `reverse_regex(body)` (oracle `ov`) to the backward SPEC tree's first leaf. Forward-tied pieces
needing a backward analogue:
- `BooleanCorrectLkRec`/`EncodeEqualLkRec` (EntryLk.dfy) — model the VM boolean tree `BoolTreeLk` at
  `IsTree(..,Forward)`. **`BoolTreeLk` hardcodes `WP.Forward` (ReadChar) and has ~378 consumers** →
  either parameterize by `dir` (big ripple) or add `*Back` twins.
- `ActionsTreeRepRENested`/`TreeRepRE` (ActionsTreeRepRE.dfy) — the engine↔checked-tree correspondence.
- `FindMatchBodyAtCpNested` (MainTheorem.dfy:3620, `LAnc.Forward`) — the engine sim
  (`FindMatchSimRENested`).
- The closedness ladder `ClosedBelow`/`FirstLeafClosedRec` (MainTheorem.dfy ~2190) — 9 forward
  `least lemma`s over the FORWARD `BoolTreeLk`; `FwdPosActsL`-gated. Direction-symmetric in principle
  (group open/close balance) but forward-tied. The reusable `ComputeTrCloseDiscLk`/`GActsOutsideSin`
  (§4) may help here.
- First stone already green: `BackwardBodyConfinedTree` (LookLeaves.dfy) — backward spec tree of a
  nested body is `LkConfinedTreeK(_, LkBodyGroups)`, direction-generic confinement at Backward.

This backward-simulation stack is LARGE and INVASIVE (multi-session). Do NOT attempt any RevL/
ComputeTr/`MatchesLReverse` mirror for the inner looks — proven dead (`GateAgreeIsFalse`, `4b829b9`).

---

## 6. INTEGRATION (after the captures keystone lands)

Intertwined at `MainTheorem` (it needs BOTH oracle AND capture correctness for a positive lookbehind),
so captures + integration do not complete independently.
1. WIRE `OracleColumnSpecNested` (gate, §3) into `OracleOk`/`StaticOkRE` for nested lookbehind columns
   — the L1/§6.5 chain; the look-free path uses `OS.OracleColumnSpec`, point the nested path at
   `OracleColumnSpecNested`.
2. WIRE `LkReplayMatchesSpecLBNested` (captures, §5) into `M.LkReplayMatchesSpec` consumers
   (LiftSim.dfy — `GateStepValueLB`, and the many `LkReplayMatchesSpec*` sites).
3. LIFT `NoPosLookbehindRE`/`FwdPosLooksL` through `OracleColumnNested`/`OracleOkRowsNested`
   (LiftSim.dfy:27337/27494, the nested depth-induction `decreases |LookIds|`, gated by
   `M.NoPosLookbehindRE(sub)`) up to `MainTheorem`.
4. DROP the dead `assert false` (LiftSim.dfy ~22441). §18 opaque-at-source perf pass on `MainTheorem`
   (15-20 min/verify). API: `ApiMatch` (`Supported = SupportedL3 || SupportedL4 || ...`), `ApiReasoning`.

---

## 7. KEY FILES

| File | Role |
|---|---|
| `linden-reasoning/src/Equiv/SpanDuality.dfy` | (A) `GroupOkLB`, `Bwd*` LookaroundR arm, `SpanDuality{Complete,Sound}LB`, `RevL`/`RevRE` (recurse into looks), `MatchesLReverse` (look-FREE only — dead for nested) |
| `src/Equiv/OracleEntry.dfy` | GATE side (§3): `MatchesVTransfer`, `RecorderHitVBackWalk`, `OracleColumnSpecNested`, `OracleColsOk` |
| `src/Equiv/OracleBuild.dfy` | `FBuildOracleCorrectAtNested`, `LookTablesLidDirForwardNested` |
| `src/Equiv/BackValue.dfy` | T2a `BackwardReplayMirrorNested` (engine mirror, holds nested) |
| `src/Equiv/BackGmMirror.dfy` | T1 `GmOfLiveXRev` |
| `src/Equiv/LookBehindKeystone.dfy` | depth-1 `LkReplayMatchesSpecLB` (template for §5), `LBEngineLeaf`, `RevREStaticOk` |
| `src/Equiv/LookBehindValue.dfy` | depth-1 `BackBodyGmTie` (look-free mirror), `SwapGm`, `InpOfCpSwap` |
| `src/Equiv/MainTheorem.dfy` | `BodyTreeAtCpNested` (fwd template for §5), `LkReplayMatchesSpecNested`, closedness ladder, `FwdPosLooksL` |
| `src/Equiv/LookLeaves.dfy` | `OracleOkAt`/`OracleOkSuffix`, `LkBodyGroups`, `LkConfinedTreeK`, `BackwardBodyConfinedTree`, `ComputeTrLkConfinedK` |
| `src/Equiv/TreeMirrorLk.dfy` | ⚠️ mirror lemmas VACUOUS (§4); establishments/confinement SOUND & reusable |
| `src/Equiv/LiftSim.dfy` | wire-in points: `OracleColumnNested`/`OracleOkRowsNested` (27337/27494), the `assert false` (~22441) |

---

## 8. ONE-LINE RESUME

Gate side of L5 is DONE (`OracleColumnSpecNested`). The captures value tie is the WALL: a
`WP.Backward` twin of L4's forward `BodyTreeAtCpNested` sim stack (surface via engine mirror T2a,
inner via backward oracle at original positions). The tree-mirror shortcut attempted this session is a
proven dead-end (`GateAgreeIsFalse`) — do not revisit it. Reuse the sound establishments in
TreeMirrorLk.dfy; build the backward sim next.
