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
| CAPTURES — the keystone assembly (`LkReplayMatchesSpecLBNested`) | ❌ **remaining: F4–F7, §5.3/§5.6** |
| Tree-mirror attempt (TreeMirrorLk.dfy bricks 1-3) | ⚠️ **VACUOUS — dead-end (see §4)** |
| Integration — lift `NoPosLookbehindRE`, drop `assert false`, API | ❌ not started (F6–F7) |

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

**F4/F5 scouting results (verified ingredient list, next session starts here):**
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
| `src/Equiv/BackGmMirror.dfy` | T1 `GmOfLiveXRev` |
| `src/Equiv/LookBehindKeystone.dfy` | depth-1 `LkReplayMatchesSpecLB` (template for §5), `LBEngineLeaf`, `RevREStaticOk` |
| `src/Equiv/LookBehindValue.dfy` | depth-1 `BackBodyGmTie` (look-free mirror), `SwapGm`, `InpOfCpSwap` |
| `src/Equiv/MainTheorem.dfy` | `BodyTreeAtCpNested` (fwd template for §5), `LkReplayMatchesSpecNested`, closedness ladder, `FwdPosLooksL` |
| `src/Equiv/LookLeaves.dfy` | `OracleOkAt`/`OracleOkSuffix`, `LkBodyGroups`, `LkConfinedTreeK`, `BackwardBodyConfinedTree`, `ComputeTrLkConfinedK` |
| `src/Equiv/TreeMirrorLk.dfy` | ⚠️ mirror lemmas VACUOUS (§4); establishments/confinement SOUND & reusable |
| `src/Equiv/FlipRev.dfy` | **F0 (green 18/0)**: `FlipLk`/`FlipL`/`FlipRE`, `TranslateFlip`, `FlipCompileToBytecode` (the wedge), `FlipGateAgree*` (cured witness) |
| `src/Equiv/LiftSim.dfy` | wire-in points: `GateStepValueLB` (2824, the depth-1 template for F6), `OracleColumnNested`/`OracleOkRowsNested` (27337/27494), the D5 `assert false` (~22441) |

---

## 8. ONE-LINE RESUME

Gate side of L5 is DONE (`OracleColumnSpecNested`). The captures route is the **FLIP route** (§5):
the bytecode is look-kind-blind (`FlipCompileToBytecode`, FlipRev.dfy, green), so the T2a-mirrored
forward run IS a run of the kind-FLIPPED regex, whose looks are Lookahead-flavoured — the EXISTING
L4 forward keystone applies, and the spec side closes with the FLIP tree mirror (TRUE where the
no-flip one is `GateAgreeIsFalse`-vacuous; the flip agreement is proven at that exact witness).
**F0–F3 are ALL GREEN** (`FlipRev.dfy` 18/0, `FlipMirror.dfy` 32/0, `FlipDisc.dfy` 14/0,
`FlipOracle.dfy` 8/0 — builder with a PROVEN look case, exact-`MirrorGm` value fold,
`BackBodyGmTieFlip`, non-circular `MirrorOracleColsOk`). Next: **F4+F5** in a `FlipKeystone.dfy`
(include MainTheorem) — the verified ingredient list is in §5.6; then F6/F7 integration. No
backward `BoolTreeLk` twin stack; that plan is shelved (§5.5).
