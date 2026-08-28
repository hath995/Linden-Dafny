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
| F0 — the KIND-FLIP wedge (`FlipRev.dfy`: `FlipCompileToBytecode`, cured witness) | ✅ green (18/0) |
| F1 — the FLIP tree mirror (`FlipMirror.dfy`: builder + Someness + VALUE fold) | ✅ green (32/0) |
| F1c+F2 — `CloseDiscF` establishment + **`BackBodyGmTieFlip`** (`FlipDisc.dfy`) | ✅ green (14/0) |
| F3 — mirror-oracle transport `MirrorOracleColsOk` (`FlipOracle.dfy`) | ✅ green (8/0) |
| F4 — statics of the flip-reversed body (`FlipStatics.dfy` + `FlipXRevStaticOkNested`) | ✅ green (39/0) |
| **F5 — CAPTURES keystone `LkReplayMatchesSpecLBNested` (`FlipKeystone.dfy`)** | ✅ **green (1201/0)** |
| **F6 — the keystone in `raB`'s OWN registers + the D5 arm's consumer atoms (`FlipGate.dfy`; `ThreadRepLkStepCheckOracleRecLB` in LiftSim)** | ✅ **green (1294/0 + 407/0; F6c LiftSim 2/0)** |
| **F7a — `SubFirstLeafAt` direction-generic (`LidDir`) + totality guards; F7b — per-lid LB engine↔spec ties (`FlipGate` value half + LiftSim wrappers)** | ✅ **green (all 24 `SubFirstLeafAt` consumers by prefix sweeps, ≤8 in parallel: `SubFirstLeaf` 3/0, `LookNestBackT` 23/0, `Descent` 16/0, `BodyReplayGmtIsSubFirstLeaf` 2/0, `FreshBodyDirectInSubFirstLeaf` 2/0, `DeepGateReqFromCrossing` 2/0, `GatePassDeepRepStep` 2/0, `LiftInvRec` 1/0, `LookNestBackRepBTopDeep` 1/0, `FreshBodyMatchGmOuter` 2/0, `GNotUnderQuantLLookBody` 2/0, `ForwardMemberOne` 1046/0, `LiftPreserveGatePassLkRec` 1623/0, `ReverseCDeepFull` 626/0, `DeepFindRec` 1751/0, `ForwardFindRec` 2663/0, 0 timeouts)** |
| F7c-1/2/3 — scope lift (`L5ScopeRE`), ten LB `FLookLoop*` frames, `FreshBodyDirectMember` dispatch, statics tower, **the layer-6 LB body-replay carrier `LookNestBackTFromBodyReplayLB` (flip-transport)**; F7d oracle plumbing; F7e-1 closedness; F7g-oracle | ✅ **green (s3/s4; `LookNestBackTFromBodyReplayLB` 1886/0)** |
| **F7c-4 descent dispatch (layers 7–9) → `GateStaticAtNested` hub flip → F7f (the three D5 LB arms) → F7e-2 (L5 closedness ladder, `FlipClosed.dfy`) → API (`MainTheoremL5`, `SupportedL5`)** | ✅ **ALL GREEN (s5, 2026-08-27; §5.7.2): `DeepFindRec` 3565/0, `ForwardFindRec` 4748/0, `LiftPreserveGatePassLkRec` 2243/0, carriers 1900/0, `MainTheoremL5` 4502/0, F7e-2 ladder 10 syms, API `MatchCorrect` 2/0** |
| **Whole-file sweep (s6, 2026-08-28; §5.7.3)** — wf-only on all 51 files, FULL-file on every non-LiftSim file, LiftSim full minus giants + giants by chain; forward-arm split of the two descent giants | ✅ **wf 51/51 green; full-file 49/49 non-LiftSim green (`MainTheorem` 8734/0); split arms 4/4 green first try; LiftSim full-minus-giants + giants chain: see §5.7.3** |
| Tree-mirror attempt (TreeMirrorLk.dfy bricks 1-3) | ⚠️ **VACUOUS — dead-end (see §4)** |
| Integration — lift `NoPosLookbehindRE`, drop `assert false`, API | ✅ done (s5): the hub, the composite chain and the descent are `NR.L5ScopeRE`-scoped; the D5 arm has no `assert false`; `MainTheoremL4` is a wrapper of `MainTheoremL5`; `Supported = L3 ∨ L4 ∨ L5`. Left: the NoPos-versions retirement (`LookBodyRowNested`/`OracleOkRowsNested`/`OracleColumnNested` L4 wrappers) — cosmetic |

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

**DEEPER root cause (identified 2026-08-24, see §5.0): the NO-FLIP itself.** The re-walk tree fails
to mirror only under the kind-PRESERVING reversal; under the kind-FLIPPING reversal (lookbehind <->
lookahead, the classical duality) the mirrored sub-walk reads the SAME chars and the tree mirror is
TRUE — `FlipGateAgreeAtDeadEndWitness` (FlipRev.dfy, green) proves the flip agreement at the exact
`GateAgreeIsFalse` witness. The no-flip constraint was inherited from the engine's `reverse_regex`,
but the bytecode is look-kind-blind (`FlipCompileToBytecode`), so the inheritance was an illusion.

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

## 5. THE CORRECT CAPTURES ROUTE — **THE FLIP ROUTE** (validated 2026-08-24, F0 green)

### 5.0 The diagnosis that unlocks it

Every mirror attempt died on ONE inherited constraint: "the spec reversal must keep look KINDS,
because the engine's `reverse_regex` does" (`RevL`/`XRev` keep `Lookbehind` a `Lookbehind`). Under
string reversal a kind-preserving inner look re-walks in the SAME intrinsic direction over the
swapped window and reads the OPPOSITE side of the point — `GateAgreeIsFalse`. **But the constraint
is an illusion: the MAIN BYTECODE IS LOOK-KIND-BLIND.** `CP.compile`'s lookaround case
(Compiler.dfy:160-165) emits the identical single `CheckOracle(lid)` for Lookahead AND Lookbehind
(`NegCheckOracle` for both negatives) — only POSITIVITY reaches the instruction stream; the body
lives in the tables; even label layout is kind-independent (proof-side twin NfaRepRE.dfy:1539-1545).
So the spec-side reversal is FREE to flip `Lookbehind <-> Lookahead` — the CLASSICAL reversal
duality, under which the mirrored look walks the OTHER direction over the swapped window and reads
the SAME chars. `SD.ReadCharSwap` (SpanDuality.dfy:531) is already exactly this transport at the
char level — **the look-free mirror `TM.ComputeTreeReverse` was the flip mirror all along**,
restricted to bodies with nothing to flip; the vacuous LK case was the one alien addition that
didn't follow the lemma's own transport pattern.

**F0 = `src/Equiv/FlipRev.dfy` (green, 18/0) machine-checks the wedge:**
- `FlipLk`/`FlipL`/`FlipRE` (kind-only flips; lids/structure untouched), involutions,
  `FlipLkLaws` (`LkDir` flips, `Positivity` preserved), `FlipReverseComm`/`FlipSwapAnchorsComm`,
  `FlipTransWf`/`TranslateFlip` (`Translate(FlipRE(r)) == FlipL(Translate(r))`).
- **`FlipCompile`/`FlipCompileToBytecode`/`FlipCompileToWrite`** — `compile(FlipRE(r)) ==
  compile(r)` exactly. The engine cannot distinguish a regex from its flip.
- **`FlipGateAgreeAtDeadEndWitness`** — the FLIP gate agreement is TRUE at the exact
  `GateAgreeIsFalse` witness (`Input(['b'],['a'])`, same kind, same body), and
  `FlipGateAgreeCharacter` at EVERY input for a Character body. The dead-end was the missing flip,
  not the mirror idea.

### 5.1 Why the forward keystone is reusable as-is (verified against code)

- `BodyTreeAtCpNested` (MainTheorem.dfy:3836) requires ONLY `StaticOkNestedRE` +
  `NegLooksLookFreeRE(body)` + `SizesOkRE` + `compile_to_bytecode` + **SEMANTIC**
  `LL.OracleOkSuffix` (no build-level facts, no `FFindMatch` hypothesis — it constructs the run).
  **NO `NoPosLookbehind`/`FwdPos*` premise.** Same for `FindMatchBodyAtCpNested` (:3620) and
  `LkReplayMatchesSpecNested` (:9642) — the `la.Lookahead?` at :9657 restricts only the OUTER
  replay direction.
- `FwdPosLooksL`/`FwdPosActsL` (:2174-2188) appear as `requires` in EXACTLY three lemmas — the
  closedness ladder (`BodyLeafClosedFromBelow`:2216, `FirstLeafClosedRecAux`:2257,
  `FirstLeafClosedRec`:2630) — whose single caller is `MainExtractionNested`:10280 (top-level).
  Nothing in the keystone chain touches it.
- `OracleOkAt` (LookLeaves.dfy:1685) is direction-generic (`L.LkDir(lk)` per lid). The nested-LB
  bits it needs are EXACTLY what the green gate side (`OracleColumnSpecNested`) supplies.
- The depth-1 LB keystone discharges `OracleOkSuffix` for the reversed body VACUOUSLY
  (`RevREStaticOk` builds `qm'.looks == map[]`, LookBehindKeystone.dfy:273). That trick — not the
  simulation — is the precise nested break point, and the flip repairs it: with FLIPPED kinds in the
  mirrored looks-map, `OracleOkAt` under `MirrorView(ov)` becomes TRUE (`MirrorViewGet`: the bit at
  `n-cp` IS `ov[cp]`; the flipped walk reads the same chars as the original walk at `cp`).
- **Depth-1 consistency check:** on look-free bodies `FlipRE` is the identity, so the flip route
  DEGENERATES exactly to the proven `LkReplayMatchesSpecLB` architecture. It is the unique
  generalization that restricts to the working depth-1 proof.

### 5.2 The keystone chain (surface gids)

For a positive lookbehind body at cp (raB = backward replay of `compile(reverse_regex(body))`,
original `str`/`ov`/positions — the exact run `GateStepValueLB` ties):

```
raB  == MirrorThread of ==>  rfF                         [T2a BackwardReplayMirrorNested, green]
rfF runs compile(XRev(body)) over rstr with MirrorView(ov)
     == the SAME bytecode as ==>  compile(FlipRE(XRev(body)))        [F0 FlipCompileToBytecode]
rfF  == fwd keystone @ FlipRE(XRev(body)) ==>  FirstLeaf(tF') surface [L4 chain, §5.1: its looks
        are Lookahead-flavoured after the flip; OracleOkSuffix(qm'') from F3]
FirstLeaf(tF')  == FLIP spec tree mirror ==>  MirrorGm(FirstLeaf(tB))  [F1/F2 — the one new mirror]
FirstLeaf(tB) = the spec backward tree's leaf = LkResult side of the keystone.
```

INNER-look gids (`LkBodyGroups`): NOT through any mirror — the direction-generic
`recon_inner`/`FLookLoop` reconstruction at ORIGINAL positions (the L4
`LkReplayMatchesSpecNestedFull` seam), recursing on `NestDepth` through the keystone at strictly
smaller bodies (innermost owner holds each gid as a SURFACE group of its own body).

### 5.3 Work items (F-bricks)

| # | Item | Size |
|---|---|---|
| **F0** | `FlipRev.dfy` — flips, involutions, `TranslateFlip`, **`FlipCompileToBytecode`**, cured witness | ✅ DONE (18/0) |
| **F1** | The FLIP spec tree mirror (the crux): `FlipRevL(tr) := FlipL(RevL(tr))`; `TreeMirrorRelF` = `TM.TreeMirrorRel` cases + REAL LK/LKFail cases (`lkm == FlipLk(lk)`, **FULL sub-tree recursion** — sub-walks read the same chars, so inner captures mirror too); builder `ComputeTreeReverseF` (copy of TM.ComputeTreeReverse:123-268's fuel recursion; the `LookaroundR` case recurses the body sub-walk through the SAME lemma — for the v1 GroupOkLB scope every inner sub-walk stays Backward↔Forward, no direction-parametrization); fold `TreeResMirrorF` (TreeResMirror:241 shape + LK case, EXACT `MirrorGm` equality — needs a FULL-tree `CloseDiscLkFull` variant established by the TreeMirrorLk fuel pattern). **NO gate hypothesis anywhere** — unlike the vacuous `ComputeTrReverseLk` there is nothing to assume; the LK case is PROVEN. Lives in linden-equiv (reuse TreeMirrorLk's sound establishments); **no linden-reasoning edits**. | M–L |
| **F2** | `BackBodyGmTieFlip` — compose F1 builder+fold at Empty gm: None-iff + `FirstLeaf(tF') == MirrorGm(FirstLeaf(tB), n)` (full-gm; surface is a corollary) | M |
| **F3** | `MirrorOracleOkNested` — `OracleOkSuffix(rer, qm'', ·)` for `qm''` = (looks of `FlipRE(XRev(body))`, view `MirrorView(ov)`) from the ORIGINAL `OracleOkSuffix` + `MirrorViewGet` + F2's None-iff + `InpOfCpSwap` + `TranslateFlip`/`TranslateRevRE`. **Non-circular** (F1/F2 are oracle-free). This kills the B5 circularity that sank the old route. | S–M |
| **F4** | `FlipXRevStaticOkNested` — `StaticOkNestedRE(qm'', FlipRE(XRev(body)), bc', endl')` from body facts (nested `RevREStaticOk` analogue): F0 compile lemmas + `XRevNestedFragment` (OracleMirrorV:187) + flip preservation of fragment/`CapUnique`/`QuantUnique`/`SizesOk`/`StutterTame`/`NegLooksLookFree`; plus `GmOfLiveFlip` (`GmOfLive(FlipRE(r),X)==GmOfLive(r,X)`, the `FilterReset*` pattern from `GmOfLiveXRev`) | M |
| **F5** | `LkReplayMatchesSpecLBNested` — the keystone assembly, copying `LkReplayMatchesSpecLB`:395's proof shape: T2a + F0 + `LkReplayMatchesSpecNested`/`ReplayCapIsBodyLeafNested` @ `FlipRE(XRev(body))` on `rstr`/`MirrorView(ov)` (surface tie; `MirrorRegs(init)==init` so the fresh run aligns) + F2 (transport back to tB) + `GmOfLiveXRev`+`GmOfLiveFlip`+`GmOfLiveMirror`+`RawMirrorMirrorSwap` (readout normalization, as depth-1) + `ComputeTrGmIndepLkRec`+`TreeResGmFrameRec` (gmMain framing). Conclusion: None-iff + surface `GmAgreeOn` (`S = DefGroups \ LkBodyGroups`) | L |
| **F6** | `GateStepValueLBNested` (copy `GateStepValueLB` LiftSim.dfy:2824's shape) into the D5 dead arm (LiftSim.dfy:22436-22441); inner gids via the direction-generic recon_inner seam (`NestDepth` recursion through F5 at smaller bodies; L4 R1–R3b innermost-owner machinery is direction-generic) | M–L |
| **F7** | Integration: closedness-ladder LB case (the ONLY `FwdPos*` surface, §5.1 — discharge the LB LK sub-leaf's closedness by transporting across F1's mirror (`ClosedGm` is `MirrorGm`-invariant) or from the keystone's engine tie); lift `NoPosLookbehind*` to the v1 fragment; wire `OracleColumnSpecNested` (§3) into `OracleOk`; drop the `assert false`; §18 perf pass; API | L |

**Order: F1 (crux, do FIRST) → F2 → F3 → F4 → F5 → F6 → F7.**

### 5.4 Scope (v1) + anti-vacuity discipline

**v1 fragment:** positive lookbehinds whose bodies are `NestedFragmentRE` + `NegLooksLookFreeRE`
with ALL nested looks lookbehind-flavoured (`Translate(body)` in `SD.GroupOkLB`) — exactly the
scope the GREEN gate side already has (`OracleColumnSpecNested` requires `la.Lookbehind? ||
la.NegLookbehind?` per look + `GroupOkLB` body; `MatchesL`'s look clause is lookbehind-only,
SpanDuality.dfy:120-128). Covers the headline `(?<=a(?<=b)(c))`. Mixed nesting (lookaheads inside
lookbehinds and vice versa) is a LATER rung: it needs a `MatchesL` lookahead clause
(linden-reasoning spec extension), the Forward↔Backward twin orientation of F1, and the gate-side
extension — the flip machinery generalizes (mutual induction over {Fwd,Bwd} × depth).

**Anti-vacuity discipline (the lesson of §4): every F1/F2 mirror lemma ships WITH a concrete
instantiation witness** (e.g. body shape `a(?<=b)(c)`) proving its hypotheses satisfiable, the way
F0 ships `FlipGateAgreeAtDeadEndWitness`. A mirror lemma with an unwitnessed hypothesis is not a
result. F1's statements should carry NO agreement hypothesis at all (None-iff and the relation are
CONCLUSIONS).

### 5.6 EXECUTION STATE (2026-08-24 session 2) — F0–F3 ALL GREEN; F4/F5 scouted

**Landed (each committed on green):**
- **F0** `FlipRev.dfy` 18/0 (`e40be03`) — flips, `FlipCompileToBytecode`, cured witness.
- **F1** `FlipMirror.dfy` 32/0 (`4e859b6`, `88d3cfa`) — `FlipRevL`/`FlipRevActs`/`GroupOkLBActs`;
  `TreeMirrorRelF` (LK/LKFail cases: original side pinned LB-flavoured, kinds `FlipLk`-related,
  FULL sub-tree recursion); `TreeResSomeMirrorF` (success of related trees agrees at ANY gm pair —
  the gate verdict, oracle-free); fuel transport (`RegexFuelFlipRev` handles looks via
  `WorstInputSwap`); **`ComputeTreeReverseF`/`ComputeTrReverseF`** (the builder — the `LookaroundR`
  arm is PROVEN, one missing pointwise assert on first verify, else first-try);
  `FlipMirrorSatisfiableNested` (anti-vacuity witness); `CloseDiscF`/`AvoidsCR`/`CloseDiscFWiden`/
  `GActsIn`/`GActsInAvoids`/`TreeResPreservesOpen`; **`TreeResMirrorF`** (the VALUE fold — EXACT
  `MirrorGm` leaf equality, INNER captures included).
- **F1c+F2** `FlipDisc.dfy` 14/0 (`88d3cfa`-next) — `ComputeTreeGActsIn`, `ComputeTreeCloseDiscF`
  (TML establishment + extended LK case: fresh sub-establishment at `{}` + `GActsIn`/disjointness ⇒
  `AvoidsCR` ⇒ `CloseDiscFWiden`), `ComputeTrCloseDiscF`, `GroupOkLBNegFreePikeLk`,
  `NegBodiesGroupFree`, **`BackBodyGmTieFlip`** (F2 — the sound replacement for the vacuous
  `BackBodyGmTieNested`).
- **F3** `FlipOracle.dfy` 8/0 — `FlipQmTie`/`QmBodiesLBOk`, `MirrorOracleOkAtCp`,
  **`MirrorOracleColsOk`** (MirrorView IS correct for the flipped looks-map — the B5 circularity is
  dead), `ColsOkToSuffix` (columns ⇒ the `OracleOkSuffix` the keystone consumes).

**F4+F5 LANDED (2026-08-24 session 2, cont.):**
- **F4** `FlipStatics.dfy` 39/0 (`aa27401`) — exactly the ingredient list below, all green:
  `XRevIsRevRENested`, `TranslateFlipXRev`, the Flip*/XRV* preservation family (incl.
  `FlipNullable`/`OMV.XRevNullable` for the quantifier arm of `NestedFragmentRE`), `FXRStructural`,
  `FXRCompileFacts`, `FlipLooksMap`/`FlipLooksMapTie`/`LmapOkFlipXRev`, `OracleOkAtSubmap`,
  `GmOfLiveFlip`/`GmOfLiveFXR`, `LBOnlyLooksRE` + `TranslateGroupOkLB`/`TranslateNegBodiesGroupFree`,
  `LkBodyGroupsFlipL`.
- **F5** `FlipKeystone.dfy` 1201/0 **first try** (`{:isolate_assertions}`) — `FlipXRevStaticOkNested`
  (the M-half of F4: `StaticOkNestedRE(qm'', FXR(body), …)` with `qm''.looks == FlipLooksMap(LmOf(body))`),
  `LmOfBodiesLBOk`, `LmapOkEntriesMatchLmOf`, `TranslateDefGroupsNoDupK` (LiftSim-local copy),
  `LBEngineLeafFlip` (engine half), `RawMirrorAgreeOutside`, and **`LkReplayMatchesSpecLBNested`**.
  Its signature (the F6 consumer contract): premises = body structural facts (`TransWf`,
  `NestedFragmentRE`, `NegLooksLookFreeRE`, `LBOnlyLooksRE`, `CapUnique`, `QuantUnique`,
  `LTB.LookUnique`, `SizesOkRE`), `rer` flags, `n == |str| && cp <= n && |ov| == n+1`, a site table
  `qm` with `qm.ov == ov && LmapOk(body, qm) && OE.OracleColsOk(rer, qm, str)` (**ALL columns** — the
  backward body reads positions ≤ cp, so a from-cp `OracleOkSuffix` is NOT enough; the site has
  whole-string correctness via `OracleOkFromColumns`/`OracleSufAllO`), `RegsAgreeInside(cap, init,
  CaptureRegs(body))`, qt sizes, `la.Lookbehind?`, `tlk == ComputeTr(...gmMain, Backward)`,
  `GmAgreeOn(gmMain, Empty, DefGroups)`. Conclusion: the depth-1 keystone's shape with `bcF :=
  compile(FST.FXR(body))` and SURFACE `S = DefGroups \ LkBodyGroups`.

**F6 LANDED (2026-08-25):**
- **F6a+F6b** `FlipGate.dfy` (`LindenElkFlipGate`, includes `FlipKeystone.dfy`; **1294/0 first try**,
  4 min): `BackFreshCoreNested` (the T2a+F0 core: `rfF == MirrorThread(raB)`, caps involution via
  `LBK.BackCapsInRange`+`MIR.MirrorRegsInvol`, wf via `M.FFindMatchRegsWf` on the backward run
  (NO fragment premise needed — `FreshMatchWfLB`'s `PlusFragmentRE` was never used) +
  `M.FreshMatchWfNested` at `FXR(body)`, `PIV.GmOfLiveClkCong` readout congruence);
  **`BackFreshBodyGmTieNested`** (F6a — the nested twin of `LBK.BackFreshBodyGmTie`:
  `SwapGm(LkResult.value) ~ GmOfLive(body, raB.*)` on the SURFACE gids; premises = F5's minus the
  cap/lk/qt banks); `CapIdsInLooksFXR` (`CapIdsInLooks(FXR(body)) == CapIdsInLooks(body)` via
  `LkBodyGroupsEqCapIdsInLooks` + `LkBodyGroupsFlipL` + `TML.LkBodyGroupsRevL`);
  **`FreshBodyMatchGmOuterLBNested`** (F6b — the nested-backward twin of LiftSim's
  `FreshBodyMatchGmOuter`: `raB.caps` shares its CLOCK bank with `rfF.caps` (`MirrorRegs` keeps
  `a_clk`), `M.MainMatchInsideCapsInitNested` at `FXR(body)` keeps the inside-look start slots at
  init, then `PIV.GmOfLiveInsideLookAbsent`; `MainMatchInsideCapsInitNested` is Forward-only, hence
  the mirror route).
- **(E4) coverage** `GateCrossCoverageLBNested` (**407/0 first try**): every body group LIVE in
  `raB` lands in the passing gate's `LkResult` — inner gids never live (F6b), surface via F6a
  (`SwapGm` keeps keys). The LB twin of the `la.Lookahead?` (E4) block in
  `LiftPreserveGatePassLkRec` (its `M.LkReplayMatchesSpecNested` + `FreshBodyMatchGmOuter` use).
- **F6c** `ThreadRepLkStepCheckOracleRecLB` (LiftSim:21125): the VERBATIM body of the Forward nested
  gate step with `L.LkDir(lk) == WP.Backward` / `la.Lookbehind?` — the nested `*Rec` path carries NO
  inside tie at the gate (`GmtTieInside` is dropped there; captures are consumed at the endpoint),
  and both ingredients (`WalkPairLkAtCheckOracleRec`, `GmtTieOutsideAfterGateNested`) are
  direction-generic — **green (2/0, filter-symbol, 3.5 min)**.

**F7a + F7b LANDED (2026-08-25, session 2):**
- **F7a** LiftSim: `LidDir(crv, l)` (`Lookbehind` ⇒ Backward, else Forward) and `SubFirstLeafAt`
  walks the lid's body tree in `LidDir`; `DeepGateReqFromCrossing`/`GatePassDeepRepStep` require
  `L.LkDir(lk) == LidDir(crv, l)` (direction-generic); `BodyReplayGmtIsSubFirstLeaf` takes
  `LidDir == Forward`; seven lookahead unfold sites discharge `LidDir == Forward` by one
  `LookBodyFactsNested`/`LookEntryOk` line each. ALL 24 `SubFirstLeafAt` consumers re-verified by
  prefix sweeps (all 24 `SubFirstLeafAt` consumers by prefix sweeps, ≤8 in parallel: `SubFirstLeaf` 3/0, `LookNestBackT` 23/0, `Descent` 16/0, `BodyReplayGmtIsSubFirstLeaf` 2/0, `FreshBodyDirectInSubFirstLeaf` 2/0, `DeepGateReqFromCrossing` 2/0, `GatePassDeepRepStep` 2/0, `LiftInvRec` 1/0, `LookNestBackRepBTopDeep` 1/0, `FreshBodyMatchGmOuter` 2/0, `GNotUnderQuantLLookBody` 2/0, `ForwardMemberOne` 1046/0, `LiftPreserveGatePassLkRec` 1623/0, `ReverseCDeepFull` 626/0, `DeepFindRec` 1751/0, `ForwardFindRec` 2663/0, 0 timeouts).
- **F7b** `FlipGate.dfy`: `BackLeafAt` (the explicit backward leaf), `LkResultIsBackLeaf`,
  `FreshBodyMatchLBUnfold`, **`FreshBodyDirectInBackLeaf`**, **`BackLeafDirectInFresh`** (values through
  `SwapRange`) — `BackLeaf` 380/0, `LkResultIsBackLeaf` 2/0, `FreshBody` 682/0. LiftSim now
  `include`s `FlipGate.dfy` (`FG`/`FST` imports; resolution +~15 s) and carries the thin wrappers
  `SubFirstLeafAtIsBackLeaf`, `FreshBodyDirectInSubFirstLeafLB`, `SubFirstLeafDirectInFreshLB`
  (2/0 each).
- **⚠️ AUDIT FINDINGS (pre-existing, all fixed this session; see also `FULL_DEPTH_K_HANDOFF.md`
  end note):** (1) `SubFirstLeafAt` and the predicates `LookNestBackTTop`/`LookNestBackTTopDeep`
  FAILED their own well-formedness checks on HEAD (`InpOfCp`/`Translate` and `NI.LookPathDom`
  preconditions) — never individually verified; per-symbol runs of a top lemma do NOT wf-check
  helper functions/predicates. Fixed with totality guards (`if 0 <= cp <= |str| && TransWf(body)`;
  `lid in LookIds(re)` conjunct). (2) **`ReverseCDeepFull` AND `DeepFindRec` (the L4 endpoint's reverse-membership
  wrapper and its deep per-g landing kernel) have been BROKEN since the perf commit `117b6aa`**:
  `DeepFindRec`'s requires were switched to the opaque `M.OracleSufAllO`/`M.FrameEntryAllO` bundles,
  but neither its own body (which reads `FrameEntryOk`/`OracleOkSuffix` from them — no `reveal`
  anywhere; 3 failed asserts + 6 timeouts) nor `ReverseCDeepFull`'s call site (unfolded foralls)
  was re-verified — fixed with `reveal M.OracleSufAllO(), M.FrameEntryAllO();` in both
  (`ReverseCDeepFull` 626/0, `DeepFindRec` 1751/0). (3) **`ForwardFindRec` had three real defects**:
  it called the DEPTH-1 `FreshBodyMatchCapWf` (requires `LookBehindFragmentRE && PlusFragmentRE`) on a
  NESTED host — an unprovable precondition; a subset-form `:|` from `GateStaticAtNested` (timeouts);
  and `T.Translate(bodyA1)` used one line before `TransWf(bodyA1)` was asserted. Fixed: new
  `FreshBodyMatchCapWfNested` (either direction; the LB arm is fragment-free), full-conjunct `:|`,
  hoisted assert (2663/0, 0 timeouts; HEAD baseline 2351 verified, 0 errors, 23 timeouts at the same three sites).
  (3) The two bodyless (admitted, `{:axiom}`-less) lemmas `TtLkSameTree`/`TtLkSameTreeRec` were
  DEAD (zero callers; superseded by the proven quotient `ETreeRepLkDeterm`) — deleted. `src/Equiv`
  has NO `assume`/`{:axiom}`/`{:verify false}`/`{:extern}`. Recommendation: a full-file LiftSim
  verify (or a complete prefix sweep) before any "green" claim is repeated.

**F7c–F7g — see §5.7.**

### 5.7 F7 — THE REAL PICTURE (scouted 2026-08-25; the "Forward-hardwired deep carrier" is RESOLVED as of s4: F7a made it direction-generic, F7c-3 proved its LB body-replay twin)

F6 scouting established what the LiftSim D5 dead arm (`LiftPreserveGatePassLkRec`, LiftSim:22333;
its three `assert false` LB arms at :22500 gate step / :22668 (E4) coverage / :22720 (E4 DEEP))
actually consumes, and which of it is direction-generic:

| D5 obligation | direction status | LB atom |
|---|---|---|
| gate step: continuation walk + outside frame (`ThreadRepLkStepCheckOracleRec` :21065) | GENERIC (`WalkPairLkAtCheckOracleRec` is oracle-bit based; `GmtTieOutsideAfterGateNested` takes `L.LkDir(lk)`); no inside tie in the nested `*Rec` path | `ThreadRepLkStepCheckOracleRecLB` (:21125, F6c) |
| (E4) KEY-level crossing coverage, carrier `LookNestBackTTop` (:13981) | GENERIC (dispatches through `M.FreshBodyMatch` on `f_look_types`) | `FG.GateCrossCoverageLBNested` (F6) |
| (E4 DEEP) VALUE-level crossing coverage, carrier `LookNestBackTTopDeep` (:9279) | **Forward-HARDWIRED**: `SubFirstLeafAt` (:9230) builds `ComputeTr(..., WP.Forward)`/`TreeRes(..., WP.Forward)` for EVERY lid; `DeepGateReqFromCrossing` (:9707) pins `LkDir(lk) == Forward` to identify it; `LookNestBackTFromBodyReplay` (:24208) requires `la.Lookahead?` + `NoPosLookbehindRE(body)` | none yet — F7a |

`SubFirstLeafAt` has 72 uses in ~25 LiftSim lemmas/predicates (incl. `LiftInvRec` :529 via
`LookNestBackTTopDeep`, `BodyReplayGmtIsSubFirstLeaf` :9248, `FreshBodyDirectInSubFirstLeaf` :9411,
`SubFirstLeafDirectInFresh` :9490, and the descent stack `DescentPackageDirectFull`/`ForwardFindRec`/
`DeepFindRec`/`ReverseCDeepFull`/`DescentProducerTopOwners*`). So F7 is a direction-generalization
pass over the deep carrier + the scope lift, multi-session. Plan, in order:

- ~~**F7a**~~ ✅ DONE — `SubFirstLeafAt` → per-lid direction `dir(l) := if crv.f_look_types[l].Lookbehind? then
  WP.Backward else WP.Forward` (the deep carrier's value equality is SPEC-to-SPEC — both sides are
  ordered spec maps — so NO `SwapGm` enters here). Re-verify the ~25 consumers: most already state
  `tlk == ComputeTr(..., L.LkDir(lk))`, so their proofs swap `LkDir(lk) == Forward` for
  `LkDir(lk) == dir(l)` (`LookEntryOk` pins `la == f_look_types[l]`). `GatePassDeepRepStep` (:22281)
  and `DeepGateReqFromCrossing` then become generic (drop their Forward `requires`).
- ~~**F7b**~~ ✅ DONE (`FG.FreshBodyDirectInBackLeaf`/`FG.BackLeafDirectInFresh` + LiftSim wrappers; `LookNestBackTFromBodyReplay`'s LB twin is F7c/F7f work) — LB twins of the endpoint's per-lid engine↔spec ties `LookNestBackTFromBodyReplay`,
  `FreshBodyDirectInSubFirstLeaf`, `SubFirstLeafDirectInFresh`: the Forward ones consume
  `M.LkReplayMatchesSpecNested` + `FreshBodyMatchGmOuter`; the LB ones consume F6a
  `FG.BackFreshBodyGmTieNested` (with `SwapGm`/`SwapRange`, exactly `GmtTieInside`'s Lookbehind
  arm) + F6b `FG.FreshBodyMatchGmOuterLBNested`.
- **F7c** (IN PROGRESS 2026-08-25 s3 — groundwork green, see the ledger below) scope predicate + lifts: replace `M.NoPosLookbehindRE(re)` (MainTheorem:15963; ~25
  `requires` sites at 14065–17954, `LookBodyFactsNested` :16006's `!la0.Lookbehind?` pin,
  `LookRowsFromTablesNested` :17006, LiftSim `L4Scope` :26577, `SupportedL4` ApiMatch:69) by an L5
  scope "positive lookbehinds allowed iff their bodies are `FST.LBOnlyLooksRE` (+ the v1 fragment)",
  with the per-lid dispatch `la.Lookahead? ⇒ forward keystone | la.Lookbehind? ⇒ F6`.
- ~~**F7d**~~ ✅ DONE (2026-08-25 s3: `SufAllToColsOk`/`SufForallToColsOk`/`OracleColsOkRestrict` + `requires OE.OracleColsOk(rer, qm, str)` threaded through `L3aCompositeCloseRec → LiftFindMatchCRec → LiftStepCRec → LiftAdvanceEpsilonRec → LiftPreserveGatePassLkRec` and both body-replay carriers; supplied at `MainTheoremL4` (hoisted `OracleSufAllO`) and at `DeepFindRec`/`ForwardFindRec` for `qmB` — all 12 re-verified green: bridges 1/0, 2/0, 2/0; `LiftStepCRec` 2/0, `L3aCompositeCloseRec` 2/0, both carriers 2/0, `LiftFindMatchCRec` 2/0, `LiftAdvanceEpsilonRec` 2/0, `LiftPreserveGatePassLkRec` 1623/0, `DeepFindRec` 1757/0, `ForwardFindRec` 2669/0, **`MainTheoremL4` 4729/0 (single-shot, 46 min)**) — all-columns oracle plumbing: F5/F6 need `OE.OracleColsOk(rer, qm, str)` (the backward body
  reads positions ≤ cp) whereas the lift invariant carries only the from-cp `LL.OracleOkSuffix`.
  Thread the whole-string fact (available at the top via `OracleOkFromColumns`/`OracleSufAllO`) as an
  extra `requires` down to `LiftPreserveGatePassLkRec` and the endpoint ties.
- **F7e** ✅ PART 1 DONE (2026-08-25 s3, `FlipClosed.dfy`): **`BackBodyLeafClosedFromBelow`** — the Backward twin of
  `BodyLeafClosedFromBelow`: a positive lookbehind's from-`gmR` body sub-leaf is closed under the FORWARD
  `ClosedBelow(rer, D)` at the FLIPPED instance (F1 builder `ComputeTrReverseF` + the general-gm fold
  `TreeResMirrorF` under `ComputeTrCloseDiscF`; closedness is `MirrorGm`-invariant) + side lemmas
  (`NoDupSeqFlipRevL`, `NestDepthFlipRevL`, `FlipRevLFwdPos`, `FlipRevLPikeLkRec`, `MirrorGmClosedIff`) —
  `BackBodyLeafClosedFromBelow` 486/0 + side lemmas 14/0, all first try. PART 2 (next): the L5 ladder `FirstLeafClosedRecAuxL5` (copy of the 370-line least lemma with
  `L5PosActsL` and the LB arm calling part 1) + `FirstLeafClosedRecL5`, in `FlipClosed.dfy` (MainTheorem
  cannot see FlipDisc), consumed by the L5 twin of `MainExtractionNested`.
  ORIGINAL SIZING — closedness ladder LB case (`BodyLeafClosedFromBelow` :2212, `FirstLeafClosedRecAux` :2254,
  `FirstLeafClosedRec` :2627 — the ONLY `FwdPos*` surface; single caller `MainExtractionNested`
  :10224): transport `ClosedGm` across F1's mirror or derive it from the keystone's engine tie.
- **F7f** the D5 arm itself: replace the three `assert false` with F6c + `GateCrossCoverageLBNested`
  + the F7a-generalized `GatePassDeepRepStep`; site statics: `LBOnlyLooksRE(body)` from the F7c
  scope, `LmapOk(body, qm)` from `StaticOkNestedRE`, `LookUnique(body)` via `LookBodyLookUnique`.
- **F7g** ✅ ORACLE HALF DONE (2026-08-25 s3): `OracleColumnNested` lifted to `NR.L5ScopeRE` with its new
  POSITIVE-LOOKBEHIND arm = `OE.OracleColumnSpecNested` (the §3 capstone; `GroupOkLB` from the L5 dispatch's
  `LBOnlyLooksRE` via `FG.LBOnlyEquiv`+`FST.TranslateGroupOkLB`, whole-string columns of the body's rows
  from the inner-rows IH via `OracleOkSuffixAtCp`+`SufForallToColsOk`); `LookBodyRowL5`; **`OracleOkRowsL5`**
  (the nested oracle entry under the L5 scope; `OracleOkRowsNested` kept as the L4 wrapper) — `LookBodyRowL5` 2/0, `OracleOkRows*` 752/0, `OracleColumnNested` 1348/0, all first try.
  REMAINING: §18 opaque-at-source perf pass on `MainTheorem`; `SupportedL5`/`ApiReasoning`.

#### F7c LEDGER (2026-08-25, session 3) — bottom-up over the `NoPosLookbehindRE` call graph

Scope (GREEN): `NR.LBOnlyLooksRE`/`NR.L5ScopeRE` (+ raw twins `LBOnlyLooksRaw`/`L5ScopeRaw`,
`AnnotateLBOnlyLooks`/`AnnotateL5Scope`, `LBOnlyImpliesL5Scope`, `LookFreeLBOnly`) in NfaRepRE;
`M.NoPosImpliesL5Scope`, **`M.LookBodyFactsL5`** (the per-lid dispatch: `exists la :: LookEntryOk
&& (la.Lookbehind? ==> LBOnlyLooksRE(body))` + `L5ScopeRE(body)`), `LSIM.L5ScopeFromRaw`,
`FG.LBOnlyEquiv` (`FST.LBOnlyLooksRE <==> NR.LBOnlyLooksRE`). Verification (all first try except one requires typo): NfaRepRE `L5Scope` 2/0, `LBOnly` 3/0, `AnnotateL` 6/0, `LookFreeLBOnly` 1/0; MainTheorem `NoPosImpliesL5Scope` 1/0, `LookBodyFactsL5` 2/0, `FreshBodyDirectMember*` 8/0, `DOrdFromTables` 1/0, `DOrdQuantFromTables` 1/0, `LookRowsStaticNested` 1/0, `FLookLoopQuantCoversFromTables` 2/0, `EndpointQuantValueOk` 2/0; FlipGate `LBOnlyEquiv` 1/0; LiftSim `L5ScopeFromRaw` 1/0.

The 40 `NoPosLookbehindRE`-dependent symbols form 10 layers (leaves first). Status per layer
(✅ lifted to `L5ScopeRE`; 🔧 mechanical, pending; ❌ needs a real LOOKBEHIND arm):
| layer | symbols | status / what the LB arm needs |
|---|---|---|
| 1 | `LookBodyFactsNested` | ✅ twin `LookBodyFactsL5` (old kept for NoPos callers) |
| 1 | `GateStaticAtNested` (LiftSim:5569, the HUB: `M.NoPosLookbehindRE(body)` inside its exists) / `GateStaticsOkNested` / `L4Scope` | ❌ definition change ⇒ every `:|` that lists the conjunct (LiftSim 5843, 22559, 25685, 25982, 26182, 26689) and every consumer that passes `NoPos(body)` to a callee must move in the SAME step ⇒ only after layers 6–9 have LB arms |
| 1 | `LookBodyRowNested` (LiftSim:27507), `NoPosLookbehindFwdPosL` (F7e) | 🔧 / ❌ (closedness ladder) |
| 2 | `DOrdFromTables`, `DOrdQuantFromTables`, `FreshBodyDirectMemberFrom{Present,Membership,AncSet}` | ✅ lifted (only body facts used) |
| 2 | `FrameEntryOkFromTables` | ✅ DONE (s4): `FrameEntryOk`'s lookahead clause DROPPED (a tautology of `capture_type` once the frames dispatch); the TEN nested `FLookLoop*` frames now DISPATCH per kind — the lookbehind arm replays `reverse_regex(body)` BACKWARD through 17 `...LB` helper twins (`ReplayPlusFrameNestedLB`, `ReplayPlus{Capture,Look,LookDirect,Quant}Frame*LB`, `FFindMatchPlusOvStableNestedLB`, `ReplayThreadWfLBNested`, `ReplayLookCpOkNestedLB`, `ReplayLid{Cap,Look,Quant}AgreeFreshNestedLB`, `ReplayCapAgreeFreshLBNested`) + `Reverse{CapIdsOutsideLooks,CapIdsInLooks,DirectLookIds,QuantIdsOutsideLooks,IdSets,NestedPackage}` + three Backward engine twins in ClockMono (`FFindMatchLook{CpOk,CpSet,OracleTrue}B`) — all first try except one missed dispatch: twins 15×(1–2)/0; frames `CaptureFrameNested` 252/0, `QuantFrameNested` 333/0, `GRegUnsetFrame` 276/0, `LookCpSet` 1/0, `LookOracleTrue` 1/0, `ValueLiftOuter` 1007/0, `ValueLiftFull` 1021/0, `ChildLinkLift` 987/0, `QuantValueLiftFull` 1104/0; ClockMono twins 2/0 each. ORIGINAL: `FrameEntryOk`'s clause `capture_type(la) ==> la.Lookahead?` (MainTheorem:11187) must become `la.Lookbehind? ==> LBOnlyLooksRE(body)`; consumed by the TEN nested `FLookLoop*` frame lemmas (`FLookLoopCaptureFrameNested`, `FLookLoopQuantFrameNested`, `FLookLoopValueLift{Outer,Full}`, `FLookLoopChildLinkLift`, `FLookLoopLookCpSet`, `FLookLoopLookOracleTrue`, `FLookLoopGRegUnsetFrame`, `FLookLoopQuantValueLiftFull`, `ReplayPlusQuantFrameNestedOuter`) which derive `capture_direction == Forward` — each needs the BACKWARD replay arm (`capture_regex = reverse_regex(body)`, `FFindMatchPlus(.., Backward, ..)`; the L3b depth-1 FLookLoop already has this shape — port it to the nested frame) |
| 2 | `GateStaticsSweepRENested`, `LiftPreserveGatePassLkRec` (F7f), `MainExtractionNested` (F7e), `OracleColumnNested` (F7g: LB arm = `OracleColumnSpecNested`) | ❌ |
| 3 | `FreshBodyDirectMember` | ✅ DONE (s4): lifted to `L5ScopeRE`, dispatches on the owner's kind; LB arm = `FreshBodyMatchAncSetLB` (over `FFindMatchAncSetB`, the Backward twin of the 55-line `FFindMatchAncSet` — its step lemmas were already direction-generic) + `AncSetInvREReverse`/`ReverseAncCaps`/`ReverseSizesOk`, wf via the fragment-blind `FFindMatchRegsWf`; caller `ProduceOwnerForall` bridged — `FreshBodyDirectMember` 8/0; `FFindMatchAncSetB` 2/0, `FreshBodyMatchAncSetLB` 2/0, `ReverseAncCaps` 2/0, `AncSetInvREReverse` 1/0, `ReverseSizesOk`/`ReverseMaxGroup`/`ReverseMaxQuant` 1/0. ORIGINAL: pins `la0.Lookahead?` for `FreshBodyMatchAncSet`/`FreshMatchWfNested` (forward fresh run); LB arm = backward twins (`FreshBodyMatchLBUnfold` + `FFindMatchRegsWf` for wf; `AncSetInvRE` of the BACKWARD run of `reverse_regex(body)` is NEW) |
| 3 | `LookRowsStaticNested`, `OracleOkRowsNested` (→ `OracleOkRowsL5`) | ✅ lifted (s3/s4) |
| 3 | `GateStaticsFromTablesNested`, `LiftAdvanceEpsilonRec` | ❌ gated on the hub / the D5 arm |
| 4–5 | `LookRowsFromTablesNested`, `Endpoint{ChildLinkOk,LookInv,QuantValueOk,TopLookFrame,ValueOk}`, `FLookLoop{Full,Quant}CoversFromTables`, `ProduceOwnerForall`, `FrameEntryOkFromTables` | ✅ lifted to `L5ScopeRE` (s4; `MainTheoremL4` bridges with `NoPosImpliesL5Scope`) — `FrameEntryOkFromTables` 1/0, `LookRowsStaticNested` 1/0, `LookRowsFromTablesNested` 2/0, the five `Endpoint*` 2/0 each, both `FLookLoop*CoversFromTables` 2/0, `ProduceOwnerForall` 433/0, **`MainTheoremL4` 4811/0 (single-shot, 41 min)** |
| 4–5 | `LiftFindMatchCRec`, `LiftStepCRec`, `L3aCompositeCloseRec` | ❌ gated on the D5 arm (they carry `LiftPreserveGatePassLkRec`'s scope) |
| 6 | `LookNestBackTFromBodyReplay` (191 l.; `LookNestOkTFromBodyReplay` is its presence-only projection, same hypotheses, no descent call sites) → **`LookNestBackTFromBodyReplayLB`** (LiftSim, after the forward carrier) | ✅ **DONE (s4, 2026-08-26) — THE FLIP-TRANSPORT**: apply the FORWARD carrier at `FXR(body)` over `Reverse(str)` with `MirrorView(ov)`, the F3/F4 flipped oracle table (`FK.FlipXRevStaticOkNested` + `FO.MirrorOracleColsOk`/`ColsOkToSuffix`, then `GateStaticsFromTablesNested` in the flipped world — `NoPosLookbehindFXR` makes `FXR(body)` L4-scoped, so the UNLIFTED hub applies) and the MIRRORED look tables (`FG.MirrorTables`: `FlipLkRE` kinds, `FXR` asts, rows recompiled; `LookTablesOkFXR`). Both `FFindMatchPlus` runs reduce to plain runs (`NoTrueQuantStampNested` + `FNulledPlusIdentity`, either direction); T2a via `FG.BackFreshCoreNested` gives `rfF == MirrorThread(raB)`; F2 (`FD.BackBodyGmTieFlip` + `TranslateFlipXRev` + `InpOfCpSwap`) gives `leafF == MirrorGm(rb)`. Per top lid the three carriers transport back: PRESENCE by congruence (`LookNestOkTTopFlip`: `TopLookIds`/`LookBodyOfRE`/`CapIds`/`LookPathPresent`/`MxAtLidLk` are `FXR`-invariant, clocks untouched by `MirrorRegs`); KEY carrier (`LookNestBackTTopLidFlip` over `FreshMatchLidFlip` = the row facts `LookRowLBOnly` + `GetCpMirror` + F6 core AT THE LID BODY + `BGM.GmOfLiveMirror`/`PIV.GmOfLiveClkCong` — same key set, `MirrorGm` same keys); DEEP carrier (`LookNestBackTTopDeepLidFlip`: `SubFirstLeafAt` of the mirrored world is `MirrorGm` of the backward sub-leaf `FG.BackLeafAt` by F2 at the lid body, values back through `MirrorRangeInj`). Bank invariants on the backward winner from the Backward ClockMono twins (+ new `FFindMatchLookClkSetB`). FlipGate structural brick: `FXR{Alt,Con,Quant,Capture,Look}` distribution, `LookIds/LookUnique/TopLookIds/CapIds/LookBodyOfRE/LookPathDom/LookPathPresent/MxAtLidLk/LmOf`-`FXR` invariance, `NestedCdnsEmpty`, `NoPosLookbehindFXR`, `LookBodySubFactsLB`, `LmapOkLookBody`. GREEN: FlipGate 24 syms, ClockMono 1, LiftSim `LookNestOkTTopFlip` 2/0, `LookNestBackTTopLidFlip` 276/0, `LookNestBackTTopDeepLidFlip` 694/0, `FreshMatchLidFlip` 588/0, **`LookNestBackTFromBodyReplayLB` 1886/0**. Site hypotheses of the LB twin: L5 body facts + `LookUnique` + `SizesOkRE` + `bodycodeB == compile(reverse_regex(body))` + `LmapOk(body, qm) && OracleColsOk(rer, qm, str)` + `LookTablesOk(body, crv) && |f_look_types| == |f_look_ast|` + `LookIds(body) < nlook` — NO `GateStaticsOkNested`/`StaticOkNestedRE` at the site (built internally for the flipped world). Ensures: `rf.Some? <==> TreeRes(t_B, Empty, inp, Backward).Some?` + the three carriers at `TreeRes(..).value.1` + the bank invariants. ORIGINAL scouting note: the carrier IS the forward lift simulation of the body, so the LB twin could not re-run the lift backward. |
| 7–9 | `DeepFindRec`, `ForwardFindRec`, `ForwardMemberOne`, `ReverseCDeepFull`, `MainTheoremL4DeepConclude` | ❌ each has 1–3 `la.Lookahead?` dispatch sites; LB arms consume F7b (`FreshBodyDirectInSubFirstLeafLB`/`SubFirstLeafDirectInFreshLB`), `FreshBodyMatchCapWfNested` (either direction, done), and the layer-6 LB carriers |

Order for the next sessions: ~~FrameEntryOk clause + the ten FLookLoop nested frames~~ → ~~`FreshBodyDirectMember`~~ → ~~layer-6 carriers~~ (all ✅ s4) → **descent dispatch (layers 7–9: the `la.Lookahead?` sites in `DeepFindRec`/`ForwardFindRec`/`ForwardMemberOne`/`ReverseCDeepFull`/`MainTheoremL4DeepConclude` get LB arms calling `LookNestBackTFromBodyReplayLB` + the F7b wrappers)** → hub
`GateStaticAtNested` flip + `L4Scope`→`L5Scope` → F7e-2/F7f/F7g-API.

#### 5.7.1 F7c-4 — the descent dispatch, SCOUTED (2026-08-26 s4, after F7c-3; line numbers at HEAD `6056280`)

The five descent lemmas still carry `requires M.NoPosLookbehindRE(re)` and each proves `la.Lookahead?`
for the owner lid from it. Sites (all in LiftSim):

| lemma (range) | `la.Lookahead?` sites and what they feed |
|---|---|
| `DeepFindRec` (26338–26621; 1742 syms, ~23 min) | owner `A`: `:|` off the hub 26394–26405 (reads `NoPosLookbehindRE(bA)`), `assert laA.Lookahead?` 26413–26418 (via `M.LookBodyFactsNested`); BASE arm `FreshBodyDirectInSubFirstLeaf` 26433; DEEP arm inner `A1`: `assert la1.Lookahead?` 26462–26475 (negatives killed by `CaptureFreeNoCapIds`, `assert false` 26475); carrier `LookNestBackTFromBodyReplay(rer, qmB, laA, host, bodycode, endlH, 0, crv, str, cpA, ov, cdnA, crv.f_plus_bc, ..)` 26520 over the body-restricted `qmB` (26500–26518: `QmapOkLooksIrrel`, `LmapOkRestrict`, `OracleOkSuffixRestrict`, `GateStaticsFromTablesNested(qmB, host, crv)`, `SufAllToColsOk`+`OracleColsOkRestrict`), then `rfP := FFindMatchPlus(bodycode, host, .., Forward, cpA, ..)` and `LookNestBackTTopDeep(rer, host, ..)` at `gmtH := FirstLeaf(t, inpA).value.1` |
| `ForwardFindRec` (26643–27083; 2669 syms, ~26 min at 600 s) | `assert laA.Lookahead?` 26714–26719; carrier 26747 with `t := ComputeTr(.., inpA, Empty, Forward)` 26749; BASE `SubFirstLeafDirectInFresh` 26818; DEEP inner `A1`: hub `:|` 26897–26910, `assert la1.Lookahead?` 26917–26925, and `la1G.Lookahead?` 26965–26979 (for `FirstLeaf(t1, inp1).Some?`) |
| `ForwardMemberOne` (27094–27295; 1046 syms, ~15 min) | `assert laA0.Lookahead?` 27181–27191 (negatives via `CaptureFreeNoCapIds`) |
| `ReverseCDeepFull` (27334–27460; 584 syms, ~10 min) | `assert laA0.Lookahead?` 27423–27433 |
| `MainTheoremL4DeepConclude` (27731–27803) + `MainTheoremL4` | only the `requires` (27735) and `27842: assert M.NoPosLookbehindRE(re); // L4Scope` — the API scope lift |

The LB arm at each owner-lid site, ingredient by ingredient (everything exists as of s4):
1. KIND: `assert laA.Lookahead? || laA.Lookbehind?` (from `MatchedPosLA`'s `capture_type` + the negatives killed exactly as today) and `laA.Lookbehind? ==> FST.LBOnlyLooksRE(host)` via **`M.LookBodyFactsL5(re, crv, A)`** (needs `NR.L5ScopeRE(re)` — the lifted `requires`; `FG.LBOnlyEquiv` bridges `NR.LBOnlyLooksRE`).
2. ENGINE RUN: `FLookLoop` runs `FFindMatchPlus(compile(reverse_regex(host)), host, plus_bc, str, ov, Backward, cpA, ..)` for a lookbehind lid; `M.FreshBodyMatch` unfolds per `f_look_types[A]` — **`FG.FreshBodyMatchLBUnfold`** (F7b) is the spelled-out form.
3. SPEC LEAF: the consumer's `SubFirstLeafAt(rer, crv, str, A, res1)` IS the backward leaf — **`SubFirstLeafAtIsBackLeaf`** (F7b) — i.e. `TreeRes(ComputeTr(.., inpA, Empty, Backward), Empty, inpA, Backward).value.1`; that is exactly the `rb.value.1` the LB carrier speaks about.
4. CARRIER: **`LookNestBackTFromBodyReplayLB(rer, qmB, laA, host, compile(reverse_regex(host)), crv, str, cpA, ov, cdnA, crv.f_plus_bc, ncap, nlook, nquant)`**. Its site hypotheses are a SUBSET of what the forward call site already builds — `LmapOk(host, qmB)`, `OracleColsOk(rer, qmB, str)`, `LookTablesOk(host, crv)` (from `FrameEntryOk`), `LookUnique/CapUnique/QuantUnique(host)`, `SizesOkRE(host)` — plus two small ones to supply: `|crv.f_look_types| == |crv.f_look_ast|` (a table-SHAPE fact; find where `MainTheoremL4` establishes the `FCompiled` shape and thread it, or derive it from `LookTablesOk`+`LookEntryOk` per lid if the tables are exactly `maxlook+1` long) and `forall l in LookIds(host) :: l < nlook` (from the forward site's `GateStaticsOkNested(qmB, host, crv)` — `0 <= l < nlook` for `l in qmB.looks = LookIds(host)` — or from `LookBodyLookIdsIn` + the outer bound). NOTE: the LB carrier does NOT need `StaticOkNestedRE(qmB, host, ..)` / `GateStaticsOkNested(qmB, host, crv, ..)` at the site — it builds the flipped world's statics internally through the UNLIFTED hub, because `FXR(host)` has no positive lookbehinds. That is why the descent dispatch does NOT wait for the hub flip (see 6).
5. BASE arms: **`FreshBodyDirectInSubFirstLeafLB`** / **`SubFirstLeafDirectInFreshLB`** (F7b wrappers). ⚠️ The delicate point: the forward `SubFirstLeafDirectInFresh` gives VALUE EQUALITY leaf↔`GmOfLive`; the LB twin gives `lsub[g2] == LBV.SwapRange(gmb[g2])` (the engine reads the backward run's registers reversed). Whatever the site does with that value downstream (the `gmt`-tie into `GmtTieInside`'s Lookbehind arm, which already expects the swap) must be checked per consumer — this is the only place where a genuinely new proof step (not a dispatch) is expected.
6. DEEP arms (inner `A1` of an LB `host`): under `LBOnlyLooksRE(host)` every inner lid is lookbehind-flavoured, so the inner `assert la1.Lookahead?` blocks become `la1.Lookbehind?` blocks and `FirstLeaf(t1, inp1).Some?` becomes the backward `TreeRes(.., Backward).Some?` — supplied by the LB carrier's None-iff at `A1` (or `FG.FreshBodyDirectInBackLeaf`'s Some-ness). The deep carrier predicate itself is already direction-generic (F7a), so the per-`g2` deep package (`DescentProducerTopOwnersDeep`) needs no change of STATEMENT.
7. THE HUB: `GateStaticAtNested` (5572–5587) still carries `M.NoPosLookbehindRE(body)` in its `exists`; for a positive-lookbehind lid whose body itself nests a positive lookbehind (LB depth ≥ 2) that conjunct is FALSE, so `GateStaticsOkNested(qm, re, crv)` — a `requires` of every descent lemma — is unsatisfiable on the full L5 fragment until the hub says `NR.L5ScopeRE(body)`. The descent dispatch is therefore PROVABLE NOW (it only reads the hub's other conjuncts) but only USEFUL end-to-end after the hub flip; the flip is a definition change + re-sweep of its `:|` restatement sites (5894, 22611, 26394, 26698, 26897, 27409) + `GateStaticsSweepRENested` (5863) / `GateStaticsFromTablesNested` (5924) / `LookFreeNoPosLookbehindRE` (5930) / `L4Scope` (27469, 27500–27501, 27842) — and it is ENTANGLED with F7f: the D5 arm `LiftPreserveGatePassLkRec` (22516) reads the hub's NoPos conjunct at 22611 to kill its three LB `assert false` arms (22631/22667/22835 comments), so flipping the hub re-opens those arms. Their fillings are exactly the F6/F7b/F7c-3 atoms: gate step = `ThreadRepLkStepCheckOracleRecLB` (F6c, green), (E4) KEY coverage = `FG.GateCrossCoverageLBNested` (F6), (E4 DEEP) landing = `LkResultIsBackLeaf` + `SubFirstLeafAtIsBackLeaf` (F7b) with the `gmMain`-framing of the tree.

Recommended order: (i) descent dispatch arms in `ReverseCDeepFull` → `ForwardMemberOne` → `DeepFindRec` → `ForwardFindRec` (smallest first; keep `requires NR.L5ScopeRE(re)` + `GateStaticsOkNested` as-is), each verified detached with a Monitor (a LiftSim batch launched from a plain Bash call dies at the tool's 10-min timeout — `setsid nohup runm600.sh … & disown`, ≤8 dafny processes); (ii) the hub flip + its `:|` re-sweep; (iii) F7f (the three D5 LB arms); (iv) `MainTheoremL4DeepConclude`/`MainTheoremL4`/`L4Scope`→`L5Scope`, `SupportedL5`, `ApiReasoning`; (v) F7e-2 (closedness ladder LB case) and `LookBodyRowNested`/`OracleColumnNested` NoPos-versions retirement (28255/28258/28614). The 35 remaining `M.NoPosLookbehindRE` sites in LiftSim (`grep -n "M.NoPosLookbehindRE(" src/Equiv/LiftSim.dfy`) are the checklist; the two forward carriers' own `requires` (24249, 24397) STAY — they are the forward carriers, the LB twin is separate.

**F4/F5 scouting results (the ingredient list that was executed above, kept for reference):**
- Put F4+F5 in one `FlipKeystone.dfy` including `MainTheorem.dfy` + `FlipOracle.dfy` (+
  `BackGmMirror.dfy` for `GmOfLiveXRev`), template = `RevREStaticOk`+`LBEngineLeaf`+
  `LkReplayMatchesSpecLB` (LookBehindKeystone.dfy:254/291/395).
- `StaticOkNestedRE` conjuncts for `re' := FlipRE(XRev(body))`, per ingredient: fragment —
  `OMV.XRevNestedFragment` (OracleMirrorV:187) + a new `FlipNestedFragment` (needs `FlipCaptureFree`);
  Cap/QuantUnique — `LBV.CapUniqueRevRE`/`QuantUniqueRevRE` (no LookFree requires! RevRE is
  recursive now) via **`XRevIsRevRENested`** (`SwapAnchorsRegex∘reverse_regex == SD.RevRE`,
  unconditional — `MIR.SwapAnchor` and `SD.SwapAnchorRE` are IDENTICAL maps, so it's a clean
  structural induction; THIS unlocks all RevRE-preservation lemmas for XRev) + new
  `FlipCapUnique`/`FlipQuantUnique` (via `FlipCapIds`/`FlipQuantIds` — CapUnique/QuantUnique are
  CapIds/QuantIds-set based, PikeInvRE:1281/1624); TransWf — `FlipTransWf` (F0) + `RevRETransWf`;
  Qmap/Lmap — `M.QmOfREEntries`+`M.QmapOkFromEntries` (M-level) and for looks DO NOT relate LmOf
  maps structurally — construct `qm''.looks := FlipLooksMap(qmB.looks)` (pointwise map comprehension:
  `lid ↦ (FlipLk(·), FlipRevL(·))`) so `FlipQmTie` holds BY CONSTRUCTION, then prove
  `LmapOkFlipXRev` (LmapOk(body,qm) ⇒ LmapOk(FXR(body), qm'') — pure conjunction recursion, NO
  LookUnique needed, Re_con order-swap harmless) via `TranslateFlipXRev`
  (`Translate(FlipRE(XRev(r))) == FlipRevL(Translate(r))` = `XRevIsRevRENested` +
  `SD.TranslateRevRE` + F0 `TranslateFlip`); NfaRep/Accept/len — instantiate
  `NR.CompileToBytecodeRepNested` (NfaRepRE:2656) DIRECTLY at `re'` (no flip-transfer needed);
  StutterTame — `CompileStutterTameRENested` is LiftSim-LOCAL (:5790) — copy its ~short proof into
  the keystone file (do NOT include LiftSim); Sizes — `LBV.MaxGroupRevRE`/`MaxQuantRevRE` + new
  `FlipMaxGroup`/`FlipMaxQuant` (`SizesOkRE` = max_group/max_quant bounds, PikeSimRE:172).
- The original-side restricted map `qmB := QMap(qm.quants, OE.LmOf(body), qm.ov)`:
  `OE.LmapOkOfLmOf(body, qmB)` EXISTS (used LiftSim:26881/27430); `OracleColsOk(qmB, str)` from the
  site's oracle facts via a trivial `OracleOkAtSubmap` (pointwise-submap forall instantiation);
  `QmBodiesLBOk(qmB)` from a new v1-scope predicate `LBOnlyLooksRE(body)` + bridges:
  `TranslateGroupOkLB` (new, structural; RegElk has no backref node) and negatives via
  `OS.TranslateGroupFree` (OracleSpec:208, requires CaptureFree+LookFree ✓ = the fragment's
  negative arm); `NoDupG(DefGroups(Translate(body)))` from CapUnique via
  `M.TranslateDefGroupsEqCapIds` (the GateStepValueLB pattern).
- F5 assembly then follows depth-1 `LkReplayMatchesSpecLB`'s proof shape verbatim with:
  T2a `BackwardReplayMirrorNested` + `CompileToBytecodeSwap` + F0 `FlipCompileToBytecode` (present
  the mirrored bytecode as `compile(FlipRE(XRev(body)))`) + `M.ReplayCapIsBodyLeafNested` @ `re'`
  on `rstr`/`MirrorView(ov)` (premises from F4; oracle premise from F3's
  `MirrorOracleColsOk`+`ColsOkToSuffix`) + F2 `BackBodyGmTieFlip` (transport FirstLeaf back to tB)
  + `GmOfLiveXRev` + new `GmOfLiveFlip` (FilterReset* pattern) + `GmOfLiveMirror` +
  `RawMirrorMirrorSwap` + `ComputeTrGmIndepLk(Rec)` + `TreeResGmFrameRec` (gmMain framing) —
  conclusion None-iff + surface `GmAgreeOn` (S = DefGroups \ LkBodyGroups) in the LB direction.


#### 5.7.2 s5 EXECUTION (2026-08-27) — F7c-4 + hub flip + F7f + F7e-2 + API: ALL GREEN

**What landed (this order, all per-symbol green):**
1. **F7c-4 the descent dispatch** — drafted by another model (session OOM-froze the machine; no logs), reviewed and
   fixed here. Its draft: `L5ScopeRE(re)` + `|f_look_types| == |f_look_ast|` on the five descent lemmas; full LB arms
   (BASE+DEEP) in `DeepFindRec`/`ForwardFindRec` via `LookNestBackTFromBodyReplayLB` + the F7b wrappers; kind dispatch
   in `ForwardMemberOne`/`ReverseCDeepFull` with `LidDir`/`TreeRes` in place of `FirstLeaf`; the value tie of
   `ForwardFindRec`/`ForwardMemberOne`/`L3aEndpointAssemblyNestedFull2`'s (F) clause restated as a **`NormRange`
   equality** (`NormSwapCong` absorbs the LB `SwapRange` — the "genuinely new step" §5.7.1 item 5 predicted; the
   only consumer needed just the Norm-form). **Review findings:** (a) five `M.LookBodyFactsNested(re, …)` calls
   left in `ForwardFindRec`'s forward arm — its `requires NoPosLookbehindRE(re)` is NOT derivable from
   `L5ScopeRE(re)` (fixed: `LookBodyFactsL5` + the lid's own direction `LidDir(crv, A1)` at the inner hop — an
   inner lid of a lookAHEAD body may be a lookbehind under L5); (b) suspected gaps that were NOT gaps: the missing
   (γ) `rb.Some?` block in `DeepFindRec`'s LB DEEP arm (Z3 closes it from the revealed oracle bundle) and the
   carrier's `l < nlook` precondition (`LookBodyFactsL5` supplies `LookIds(body) <= LookIds(re)`).
2. **The hub flip — the hub is KIND-SPLIT** (final state, commit `029e04e`; LiftSim `GateStaticAtNested`):
   `(la.Lookbehind? ==> NR.LBOnlyLooksRE(body)) && (!la.Lookbehind? ==> M.NoPosLookbehindRE(body))`, mirrored
   by the v1 scope predicate `L5ScopeV1RE` (and `L5Scope(raw)`, `SupportedL5`). History: the conjunct
   `M.NoPosLookbehindRE(body)` was first replaced by the recursive `NR.L5ScopeRE(body)` — with that predicate (and
   its `LBOnlyLooksRE`) inside the `exists`, five VCs of `DeepFindRec` (both arms) timed out at 600 s although the
   same lemma had been green 2 h earlier; dropping the conjunct outright re-opened the same cliff. The lookahead
   lids' `NoPosLookbehindRE(body)` is the pruning fact that keeps the descent giants tractable — NEVER just drop it
   (`SUPPORTED_FRAGMENT.md` §2.1). Per lid the facts are read by `M.LookBodyFactsL5` (which also supplies
   `LookIds(body) <= LookIds(re)` and `L5ScopeRE(body)`). Bridges `M.NoPosImpliesL5Scope` where the unlifted L4 world
   feeds an L5-scoped lemma (the two forward carriers' `L3aCompositeCloseRec` calls, `L4ScopeImpliesL5`).
3. **F7f**: `LiftPreserveGatePassLkRec` → `requires NR.L5ScopeRE(re)`; the per-lid dispatch
   `la.Lookbehind? ==> FST.LBOnlyLooksRE(body)` (`M.LookBodyFactsL5` + `FG.LBOnlyEquiv`); gate step =
   `ThreadRepLkStepCheckOracleRecLB` (F6c); (E4) KEY coverage = `FG.FreshBodyMatchLBUnfold` +
   `FG.GateCrossCoverageLBNested` (F6) at `gmMain = gm`; (E4 DEEP) = the direction-generic `GatePassDeepRepStep`
   pinned by `L.LkDir(lk) == LidDir(crv, l)` (no arm split). The composite chain
   `LiftAdvanceEpsilonRec → LiftStepCRec → LiftFindMatchCRec → L3aCompositeCloseRec` lifted to `NR.L5ScopeRE`.
4. **F7e-2** (`FlipClosed.dfy`): `L5PosLooksL`/`L5PosActsL`/`ClosedBelowL5` (+ `FwdPosImpliesL5Pos`,
   `ClosedBelowL5Mono`: the L5 ladder hypothesis restricts to the forward `M.ClosedBelow` that
   `BackBodyLeafClosedFromBelow` consumes), `BodyLeafClosedFromBelowL5`, the 370-line
   `least lemma FirstLeafClosedRecAuxL5` (a programmatic copy of `M.FirstLeafClosedRecAux`; the only edit is the
   direction split at the positive-lookaround case), `ClosedBelowAllL5`, `FirstLeafClosedRecL5` — 10 syms, all
   first try (52 s for the ladder).
5. **API**: `M.MainExtractionNested` split into the scope-free `M.MainExtractionFromClosed` (closedness as the
   hypothesis) + the L4 wrapper; LiftSim `L5ScopeL5PosL` (`NR.L5ScopeRE ⇒ FC.L5PosLooksL`, via
   `FST.TranslateGroupOkLB`), `MainExtractionL5`, `L5Scope(raw)` + `L4ScopeImpliesL5` + `L5ScopeFromRawFull`;
   **`MainTheoremL4` renamed `MainTheoremL5` under `L5Scope` (3 site changes: the scope assert, `OracleOkRowsL5`,
   `MainExtractionL5`) with a thin `MainTheoremL4` wrapper**; ApiMatch `SupportedL5` (= `SupportedL4` with
   `NR.L5ScopeRaw`), `Supported = L3 ∨ L4 ∨ L5`, `MatchCorrect` dispatches to `MainTheoremL5`.

**Verification (s5):** hub-flip group `GateStatic*` 12/0; chain 2/0 ×4; `FreshWfGIndep` 79/0; `ReverseCDeepFull`
540/0; `ForwardMemberOne` 868/0; `MainTheoremL4DeepConclude` 440/0; `L3aEndpointAssemblyNestedFull2` 180/0;
`DeepFindRec` 3565/0; `ForwardFindRec` 4748/0; `LiftPreserveGatePassLkRec` 2243/0; `*TFromBodyReplay` (both
forward carriers + the LB carrier) 1900/0; `MainTheoremL5` 4502/0; FlipClosed L5 ladder 10 syms; MainTheorem
`MainExtraction*` 6/0; LiftSim `L5Scope*` 6/0, `L4ScopeImpliesL5` 2/0, `MainExtractionL5` 2/0; ApiMatch
`MatchCorrect` 2/0.

**Process facts learned (see the memory note `linden-dafny-memory-cap`):** all dafny/z3 now run in the user slice
`dafny.slice` (MemoryMax=80G, no swap) through in-place launcher wrappers; a giant LiftSim lemma is ~18 GB of
dafny + **~4.6 GB per z3 worker** (16 workers alone OOM'd at 80G; `CORES=10` fits), so giants run ONE at a time;
small lemmas' cost is the ~4.5-min resolution + Boogie per-split overhead, not z3 (`ReverseCDeepFull`: 540 batches,
4.1 min of z3 total, max 5 s) — group them by name fragment (`--filter-symbol` is a substring match; the `MOD.`
prefix makes it a prefix match on the local name) and use `--error-limit 0`; `--log-format text` + `vcprof.py`
give the per-batch profile. Launcher: `~/.local/bin/runm600.sh`.

**Next:** (v) retire the NoPos-versions (`LookBodyRowNested`/`OracleOkRowsNested`/`OracleColumnNested` L4
wrappers) — cosmetic; the remaining `M.NoPosLookbehindRE` sites are the two forward carriers' own `requires`
(by design), `LookFreeNoPosLookbehindRE`, `L4Scope`/`L4ScopeFromRaw` and the NoPos wrappers. Then PERF: split
`DeepFindRec`/`ForwardFindRec` into per-arm lemmas (an edit re-verifies one arm; arms verify as separate dafny
processes) and shrink the per-VC context with `hide`/opaque — the per-batch profiles (`*.vclog`) say whether a few
slow VCs or the sheer count dominate.

#### 5.7.3 s6 (2026-08-28) — THE WHOLE-FILE SWEEP + the forward-arm split

**Sweep harness.** `dafny verify --boogie '/proc:*well-formedness*' FILE` (Boogie filters match the VERBOSE
name `Foo (well-formedness)`) verifies only the well-formedness procedures of a whole file; Dafny 4.11 only
loads `.doo` libraries whose manifest records the same `boogie = [...]`, so the sweep runs against
manifest-patched scratch copies of the six deps + the two embedded `DafnyStandardLibraries*.doo` (memory note
`linden-wf-sweep-harness`; scripts `patchdeps.py`/`wfrun.sh`/`fullrun.sh`/`giantchain.sh`, re-creatable). The
same trick with `/noProc:<giant>*` gives a FULL-file LiftSim run that skips the per-symbol-verified giants.

**What it found at HEAD `8d7c8c2` (all fixed, `7478f10` + the split commit):**
1. `ApiMatch.dfy` did not RESOLVE — `SupportedL5` (compiled) called the ghost `LSIM.L5ScopeV1RE`; the v1
   re-wiring post-dated the recorded "MatchCorrect 2/0". `L5ScopeV1RE` and `M.NoPosLookbehindRE` (purely
   structural) are now compiled predicates. `ApiMatch` 6/0, `ApiReasoning` 16/0, full-file.
2. `LookNestOkTTop` (LiftSim) called `LookBodyOfRE`/`LookPathPresent` outside `lid in LookIds(re)` — the same
   hole class as the 08-25 `LookNestBackTTop` fix; guarded the same way (antecedent conjunct).
3. `BackGmMirror.ZeroSetCapRevRE`: `SD.RevRE` now recurses into look bodies (the L5 (A)-side change), so
   `case _` no longer covered `Re_lookaround`. Arm added; 36/0 full-file.

**Coverage after the sweep.** wf-only: all 51 files green (LiftSim 1366/0 in 12.5 min, MainTheorem 295/0).
FULL-file (every symbol): all 47 non-LiftSim/non-Api files green — `MainTheorem` 8734/0 (26 min),
`ActionsTreeRepRE` 9810/0, `FlipGate` 2425/0, `NfaRepRE` 2177/0, `LookBehindKeystone` 1356/0,
`FlipKeystone` 1201/0, `FlipClosed` 513/0, the rest ≤ 304 — plus the two Api files. LiftSim: full-file
minus the four giants (`DeepFindRec*`, `ForwardFindRec*`, `LiftPreserveGatePassLkRec`, `MainTheoremL5`) —
first attempt OOM-killed at 89 min (my stacking; see the memory-cap note), re-queued as the LAST stage of the serialized
queue below — if this line still says so, read `scratchpad/q3/summary.txt` of session 4b2a334e (or just re-run it:
`fullrun.sh` with `/noProc:{DeepFindRec,ForwardFindRec,LiftPreserveGatePassLkRec,MainTheoremL5}*`) — PENDING_LIFTSIM_FULL.
The giants at the guard text `011ed62`: `LiftPreserveGatePassLkRec` 2243/0 (21.9 min), the split arms + parents below;
`MainTheoremL5` 4447/0 (40.7 min) at the WIDENED text (§ below). **A REAL HOLE: `ActionsTreeRepLkFRec`** (LiftSim:20261, 850 lines, C3.6 part 1 `9f4f08a` 2026-08-17) failed
per-symbol too (4265/1): its `min == 1` quantifier seam called the DEPTH-1 `CE.BoolCheckInsert` (requires
`PikeLkActions(pre)`) where only the recursive `PikeLkActionsRec(pre)` holds — the Rec twin `CE.BoolCheckInsertK`
(identical contract, `LkConfinedTreeK`) was never wired in at that one site. The lemma sits UNDER `MainTheoremL5`
(`ActionsTreeRepLkRERec` → `LiftInitCRec` → the composite chain), so every "MainTheoremL4/L5 green" record since
08-17 relied on an unverified link. One-token fix applied; re-verified 4266/0 (22.6 min, CORES=4) on the widened, warning-free text.

**The forward-arm split** (`split_fwd.py`, the LB-split pattern): `ForwardFindRec` = setup + kind dispatch
(`ForwardFindRecLB` | `ForwardFindRecFwdBase` | `ForwardFindRecFwdDeep`), likewise `DeepFindRec`; the sub-lemmas
re-derive the setup and the forward prefix, `decreases (|LookIds(host)|, 0)`, `requires !f_look_types[A].Lookbehind?`
+ the arm condition (`g !in`/`in CapIdsInLooks(host)`). All four arms green FIRST TRY at CORES=4:
`ForwardFindRecFwdDeep` 1839/0 (17.8 min), `ForwardFindRecFwdBase` 1281/0 (13.6 min), `DeepFindRecFwdDeep`
1458/0 (14 min), `DeepFindRecFwdBase` 332/0 (6.8 min). Before: `ForwardFindRec` 4748 VCs in 4.3 h (it only
fit the 80G cap at CORES=2). Parents (dispatch + the `:|` setup): `ForwardFindRec` 644/0 (8.5 min), `DeepFindRec` 708/0 (8.3 min).
`ForwardFindRecLB` (the LB arm from s5) turned out to OOM-kill the 80G slice ALONE at CORES=4 (it had only ever been
verified inside the 4.3-h CORES=2 `ForwardFindRec` prefix run), so it got the same treatment: `ForwardFindRecLBBase` /
`ForwardFindRecLBDeep` (`split_lb.py`; measure ladder `ForwardFindRec` 2 > `ForwardFindRecLB` 1 > sub-arms 0, the
forward arms stay at 0). q4 result: `ForwardFindRecLBDeep` (190-line arm) OOM-KILLS the 80G cap ALONE at CORES=4 (1019 s in, no proof
errors) — the LB DEEP arm has a z3-memory monster (the flip-carrier hop: `LookNestBackTFromBodyReplayLB` +
`FreshBodyMatchLBUnfold` at the inner lid); it only ever verified inside the CORES=2 `ForwardFindRec` run (s5).
Verified at the widened text at CORES=2 (worktree of `l4-nesting`, 22:28–23:42): `ForwardFindRecLBDeep` 1808/0
(2 h 03 min — the memory monster is somewhere in the LB DEEP hop; a `.vclog` at CORES=1 would name it),
`ForwardFindRecLBBase` 1399/0 (44 min), the `ForwardFindRecLB` parent 459/0 (7.6 min, CORES=4). Carriers on the
widened text: `LookNestOkTFromBodyReplay` 2/0, `LookNestBackTFromBodyReplay` + `…LB` 1879/0 (17 min).

**The `(?=x(?<=y))` widening (s6, applied after the split):** `L5ScopeV1RE` is now `opaque` and its lookahead arm
recurses (`(Lookbehind? ==> LBOnlyLooksRE(r1)) && L5ScopeV1RE(r1)` — i.e. it coincides with `NR.L5ScopeRE`; opacity
is what keeps the hub's `exists` from unfolding the recursion, the s5 timeout cliff); the hub `GateStaticAtNested`,
the sweep, and all 13 `:|` restatements carry `(!la.Lookbehind? ==> L5ScopeV1RE(body))` in place of `NoPos(body)`;
the two forward carriers `requires L5ScopeV1RE(body)` (bridge `L5ScopeV1ImpliesL5`); `reveal L5ScopeV1RE()` in the
three V1 structural lemmas + the sweep; `GateStaticAtImpliesNested` adds `NoPosImpliesL5ScopeV1(body)`. `SupportedL5`
is unchanged in text and now covers `(?=x(?<=y))`. Green so far: hub `GateStatic*` 12/0, `L5Scope*` 9/0,
`L4ScopeImpliesL5` 2/0, **`MainTheoremL5` 4447/0** (all first try). Consumer re-verification on the widened text is the
serialized queue (session scratchpad `q1`/`q2`/`q3`): q1 = `ForwardFindRecLB`, `ActionsTreeRepLkFRec`, the four
forward arms, both parents, `LiftPreserveGatePassLkRec` (one at a time); q2 = `ReverseCDeepFull`, `ForwardMemberOne`,
`MainTheoremL4DeepConclude`, `FreshWfGIndep`, the composite chain (4),
`L3aEndpointAssemblyNestedFull2`, `OracleOkRowsL5`; q3 = LiftSim full-file minus the giants — OOM-killed ALONE at CORES=4 after 81 min (no proof errors before the kill; a
whole-file LiftSim process does not fit the 80G cap), replaced by q7 = the same run in FIVE name chunks (Boogie
`/proc:A*`…, `Lif*`, other `L*`, `T*`+`W*`, the rest) at CORES=2; q4 = the `ForwardFindRecLB` sub-arms; q5 = `ActionsTreeRepLkFRec`; q6 = the three
`*TFromBodyReplay` carriers (a bare `TFromBodyReplay` in `runm600.sh` matches NOTHING — the launcher prefixes `MOD.`,
which makes the substring a prefix of the local name; group carriers as `LookNestBackTFromBodyReplay` + `LookNestOkTFromBodyReplay`). `DeepFindRecLB` ran in
the giants2 chain on the widened text. ALL of q1/q2 green (see the `1df90be` commit message for the counts); q4/q5/q6 green as listed above except
`ActionsTreeRepLkFRec` 4266/0. The widening is committed (`1df90be`).

**Next (user decision 2026-08-28): the GENERIC GATE — `lem pack` at the workspace root.** Split `src/Equiv` into
one lem package per file (49; generator `gen_pkgs.py` in the session scratchpad: import graph → `[dependencies]`,
external modules → the six deps, `cores = "4"` on the 7 heavy files, `verification-time-limit = "900"` — >900 is
unpublishable), widen `lem-workspace.toml` members, `lem lock`, then `LEM_BUILD_TIMEOUT=0 lem pack` (the Lemmata
session added that env override; the declared limit + 10 min is the default local wall clock). Not `lem verify`.
`LindenElkLiftSim` stays ONE package (a package cannot split a module) — hours in one dafny process; the follow-up
E2 is to refactor it into layer modules so the gate becomes incremental. Memory note `linden-lem-pack-gate`.

### 5.5 The shelved fallback (do not start unless F1 fails on a witnessed obstacle)

The old plan — a `WP.Backward` twin of the forward sim stack (`BoolTreeLk`(~378 consumers)/
`ActionsTreeRepRENested`/`FindMatchBodyAtCpNested`/the 9-lemma closedness ladder) — remains sound
but is strictly dominated: multi-session, invasive, high regression risk. Keep as fallback only.

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
| `src/Equiv/ClockMono.dfy` | Backward twins of the look-bank invariants `FFindMatchLookCpOkB`/`FFindMatchLookCpSetB`/`FFindMatchLookOracleTrueB` (F7c-2) + `FFindMatchLookClkSetB` (F7c-3) |
| `src/Equiv/BackGmMirror.dfy` | T1 `GmOfLiveXRev` |
| `src/Equiv/LookBehindKeystone.dfy` | depth-1 `LkReplayMatchesSpecLB` (template for §5), `LBEngineLeaf`, `RevREStaticOk` |
| `src/Equiv/LookBehindValue.dfy` | depth-1 `BackBodyGmTie` (look-free mirror), `SwapGm`, `InpOfCpSwap` |
| `src/Equiv/MainTheorem.dfy` | `BodyTreeAtCpNested` (fwd template for §5), `LkReplayMatchesSpecNested`, closedness ladder, `FwdPosLooksL` |
| `src/Equiv/LookLeaves.dfy` | `OracleOkAt`/`OracleOkSuffix`, `LkBodyGroups`, `LkConfinedTreeK`, `BackwardBodyConfinedTree`, `ComputeTrLkConfinedK` |
| `src/Equiv/TreeMirrorLk.dfy` | ⚠️ mirror lemmas VACUOUS (§4); establishments/confinement SOUND & reusable |
| `src/Equiv/FlipRev.dfy` | **F0 (green 18/0)**: `FlipLk`/`FlipL`/`FlipRE`, `TranslateFlip`, `FlipCompileToBytecode` (the wedge), `FlipGateAgree*` (cured witness) |
| `src/Equiv/FlipGate.dfy` | **F6 (green 1294/0 + 407/0)**: `BackFreshCoreNested`, `BackFreshBodyGmTieNested` (F6a), `CapIdsInLooksFXR`, `FreshBodyMatchGmOuterLBNested` (F6b), `GateCrossCoverageLBNested` (E4); F7b value half `BackLeafAt`/`LkResultIsBackLeaf`/`FreshBodyMatchLBUnfold`/`FreshBodyDirectInBackLeaf`/`BackLeafDirectInFresh`; `LBOnlyEquiv`; **F7c-3 structural brick** `FXR{Alt,Con,Quant,Capture,Look}`, `*FXR` invariance lemmas, `NestedCdnsEmpty`, `NoPosLookbehindFXR`, `LmOfFXR`, **`MirrorTables`**/`LookTablesOkFXR`; per-lid helpers `LookBodySubFactsLB`, `LmapOkLookBody`, `LookRowLBOnly`, `GetCpMirror`, `MirrorRangeInj` |
| `src/Equiv/LiftSim.dfy` | wire-in points (HEAD `6056280`): `GateStepValueLB` (the depth-1 template for F6), the D5 `assert false` arms (`LiftPreserveGatePassLkRec` 22516; arms near 22631/22667/22835), `ThreadRepLkStepCheckOracleRecLB` (F6c); F7a `LidDir`/`SubFirstLeafAt` (9263); F7b wrappers `SubFirstLeafAtIsBackLeaf`/`FreshBodyDirectInSubFirstLeafLB`/`SubFirstLeafDirectInFreshLB` (~9620); the forward carriers `LookNestOkTFromBodyReplay` (24231) / `LookNestBackTFromBodyReplay` (24375); **F7c-3** `FreshMatchLidFlip`, `LookNestOkTTopFlip`, `LookNestBackTTopLidFlip`, `LookNestBackTTopDeepLidFlip`, **`LookNestBackTFromBodyReplayLB`** (24582–25216); the descent stack `DeepFindRec` (26338) / `ForwardFindRec` (26643) / `ForwardMemberOne` (27094) / `ReverseCDeepFull` (27334) / `MainTheoremL4DeepConclude` (27731); `OracleColumnNested`/`OracleOkRowsNested`/`OracleOkRowsL5` (~28250–28620) |

---

## 8. ONE-LINE RESUME

Gate side of L5 is DONE (`OracleColumnSpecNested`). The captures route is the **FLIP route** (§5):
the bytecode is look-kind-blind (`FlipCompileToBytecode`, FlipRev.dfy, green), so the T2a-mirrored
forward run IS a run of the kind-FLIPPED regex, whose looks are Lookahead-flavoured — the EXISTING
L4 forward keystone applies, and the spec side closes with the FLIP tree mirror (TRUE where the
no-flip one is `GateAgreeIsFalse`-vacuous; the flip agreement is proven at that exact witness).
**F0–F5 are ALL GREEN — the captures keystone `LkReplayMatchesSpecLBNested` is PROVEN**
(`FlipRev.dfy` 18/0, `FlipMirror.dfy` 32/0, `FlipDisc.dfy` 14/0, `FlipOracle.dfy` 8/0,
`FlipStatics.dfy` 39/0, `FlipKeystone.dfy` 1201/0). **F6 is GREEN too** (`FlipGate.dfy` 1294/0 +
407/0: the keystone in `raB`'s own registers, inner-gids-absent, (E4) coverage; LiftSim
`ThreadRepLkStepCheckOracleRecLB`). **F7a+F7b are GREEN** (the deep carrier is direction-generic via
`LidDir`; the per-lid LB engine↔spec ties exist as `FG.*` + LiftSim wrappers). Next: **F7c** (scope
lift replacing `NoPosLookbehindRE`, ~37 requires sites, real consumers listed in §5.7) → F7d–F7g.
Audit this session fixed three pre-existing LiftSim holes (§5.6 ⚠️). No backward `BoolTreeLk` twin
stack; that plan is shelved (§5.5).
**F7c-3 is GREEN (s4, 2026-08-26): the layer-6 LB body-replay carrier `LookNestBackTFromBodyReplayLB` (1886/0) — the flip-transport of the forward carrier at `FXR(body)` over `Reverse(str)` with `FG.MirrorTables(crv)`; per-lid transports `LookNestOkTTopFlip`/`LookNestBackTTopLidFlip`/`LookNestBackTTopDeepLidFlip` over `FreshMatchLidFlip`. NEXT: the descent dispatch (§5.7 layers 7–9), then the `GateStaticAtNested` hub flip.**
**s5 (2026-08-27): F7c-4 + the hub flip + F7f + F7e-2 + the API are ALL GREEN — L5 is END-TO-END:
`MainTheoremL5` (4502/0) under `L5Scope` (positive lookbehinds with lookbehind-only bodies), `ApiMatch.SupportedL5`
+ `MatchCorrect` 2/0; `MainTheoremL4` is now a wrapper. Ledger §5.7.2. Left: NoPos-wrapper retirement (cosmetic)
and the perf pass (split the giant descent lemmas, `hide`).**
