# Full-depth-k nested CAPTURING — HANDOFF (banked 2026-08-18)

Branch **`l4-nesting`**. Every commit below is verified green (per-`--filter-symbol`).
Companion logs: `RECON_INNER_HANDOFF.md`, `L4_L5_ROADMAP.md`. Do NOT merge to main / push (never authorized).

## 0. Bottom line
Full-depth-k nested-lookaround **MATCHING** was already end-to-end (pre-`7610cdb`). This campaign built
full-depth-k nested **CAPTURING** to within ONE precisely-characterized gap. Everything is green except
the final endpoint close for depth-≥2 captures, which provably needs a **recursive per-body composite
simulation** (§4). Scope of the fragment: nested FORWARD capturing lookaheads (`NoPosLookbehindRE`),
captures NOT under a quantifier inside looks (`GNotUnderQuantL`).

## 1. What is DONE and green (the whole machine minus one gap)

### recon_inner components (MainTheorem.dfy / NestInv.dfy) — the value building blocks
- **Engine reconstruction** (premise-free, all depths): `M.FLookLoopFullCoversFromTables` (capture) +
  `M.FLookLoopQuantCoversFromTables` (quant, C4e) — `res0`/`res2` carry each nested capture/quant at its
  innermost owner's fresh-match value.
- **Spec owner↔tree correspondence** (turnkey, general branching): `M.OuterLeafInnerGEqOwnerBody`.
- **Per-owner tie**: `M.LkReplayMatchesSpecNested`.
- Commits: R1 `4cb73aa`, R2 `e3375dd`, R3 `2580012`, R3b `eb75141`, A `2ae7a92`, B `d6fc655`,
  B' `53db9ea`, B'' `ed12289`, R↔L `351bd51`, C4e quant `9213951`.

### Brick C — the whole-regex endpoint (LiftSim.dfy), all green except the §4 gap
- **C1+C2** `0b2db74` — nested composite-sim invariants (`ThreadRepLkNested`/`BestTieLkNested`… =
  depth-1 MINUS the `GmtTieInside` conjunct) + `LookNestOkTGatePassNested` (disjoint-or-nested carrier).
- **C3** `330ea5f` + **C3.5** `174efd8` — the `GmtTieInside`-free preservation/dispatcher/consume tier,
  flipped to `StaticOkNestedRE` input.
- **C3.6** `4add9c9` — the recursive walk-tower (`WalkPairLkRec`/`ThreadRepLkRec` + ~90 `*Rec` lemmas) →
  **`L3aCompositeCloseRec` ensures `BestTieLkNested` for genuinely-nested input.**
- **C4** `3ce1268` — `L3aValueBridgeNested` + `OutsideLookValueBridgeNested` + `L3aEndpointAssemblyNested`:
  the endpoint assembly, **OUTSIDE-`S` half fully proven**; inside-`S` as `TODO(C4)` premises.
- **C4b** `63aff0c` — inside-`S` **membership algebra** (look-clock-aware): `NI.LookPathPresentLk` +
  `LookPathCompose/DecomposeNested`, `GmOfLivePresenceExtractLkNested`, `GmOfLiveKeepsPresentLkNested`.
  (Corrected: the naive same-signature `LookPath*Nested` twins are PROVABLY FALSE — depth-1 predicates
  don't track ancestor look clocks.)
- **C4c** `d140d10` — the **forward capstone** `M.ReconInnerGmOfLiveClose`: closes `g in GmOfLive(re,
  res0,res1,res2)` + value from THREE explicit feeds — (i)/(ii) the ancestor look-clock chain on the
  reconstructed banks, (iii) the quant reconcile. Plus `ReconBodyPathPresentLk`/`PathPresentLkLcIndep`/
  `FLookLoopLidLookClkStable`.
- **C4e** `9213951` — feed (iii) discharged: `FLookLoopQuantCoversFromTables` supplies the quant
  reconcile premise-free (per-owner outside-look granularity, mirroring the capture side).

## 2. What the endpoint is reduced to
`M.ReconInnerGmOfLiveClose` (C4c) needs feeds (i)/(ii)/(iii). **(iii) is now supplied (C4e).** The
ABSENT half of the inside dichotomy is `PIV.GmOfLiveInsideLookAbsentEq` (fragment-agnostic, already
green). So the ONLY missing content is feeds **(i)/(ii)** — the reconstructed-bank ancestor look-clock
chain — for owners at **nesting depth ≥ 2**. (Depth-1 owners: dischargeable now from the main thread's
`LookNestOkT` in `BestTieLkNested`, but that adds nothing over existing depth-1 capturing.)

## 3. Scope caveats (the fragment being closed)
- **Lookahead-only capturing** (`NoPosLookbehindRE`) — capturing lookbehinds excluded; so the final
  `Supported` (C5, not built) becomes a DISJUNCTION, not a superset of today's.
- **`GNotUnderQuantL`** — a capture directly under a quantifier inside a look is excluded (a quantifier
  emits a spine `Reset(DefGroups)` touching the group; proven necessary by brick B').

## 4. THE SINGLE REMAINING GAP (feeds (i)/(ii)) — a recursive per-body composite sim
C4d proved (grounded in the already-green `PIV.GmOfLiveInsideLookAbsent`, PikeInvRE.dfy:3122) that the
lighter engine-clock-monotonicity path CANNOT supply (i)/(ii):
- A fresh body match writes only OUTSIDE-look capture registers (`M.MainMatchInsideCapsInit`), so every
  inside-look group is ABSENT from that replay's `GmOfLive` → `LookNestOkT(body, GmOfLive(body,rf), rf)`
  is VACUOUSLY TRUE (useless).
- The non-vacuous `LookNestOkT(body, leafgm_body, rf)` couples `rf`'s execution to the BODY's SPEC leaf
  group map — produced ONLY by the composite sim (`L3aCompositeCloseNested → BestTieLkNested`,
  LiftSim.dfy carrier `LookNestOkT` :12919, header note :12909-12918).
- Each ancestor look `l_j`'s `res1` clock is stamped by the engine replay of `l_j`'s PARENT body
  (`FFindMatchPlus(bodycode_of_parent)`) → establishing its set+dominating clause needs a `LookNestOkT`
  about THAT replay coupled to THAT body's spec map → a per-body composite sim → recursion (depth ≥ 2).

**Minimal statement to resume with:** a per-body recursive analog of `L3aCompositeCloseNested`, invoked
on each matched positive-lookahead's fresh body replay `rf = FFindMatchPlus(bodycode, …)`, delivering
`BestTieLkNested(body, …, rf, …) ⊇ LookNestOkT(body, S_body, leafgm_body, rf)`, threaded up the
`FLookLoop` lid-loop (mirror `M.FLookLoopValueLiftFull`, :10915, final-`res1`-keyed) and stitched across
levels with `NI.LookPathComposeNested` (:5500) to assemble
`LookPathPresentLk(re, res0.a_clk, res1.a_clk, res2.a_clk, -1, owner)` = feed (i)/(ii). The `*Rec` walk
tower (C3.6: `LiftInvRec`/`TtLkRec`/`PikeLkActionsRec`, carries `LookNestRepC`) is the skeleton — the
residual is wiring it to EMIT each replay's `LookNestOkT` and threading it recursively. This is
PHASE-SIZED (comparable to the composite-sim build itself). Sharp boundary: needed ONLY for depth ≥ 2.

## 5. After the gap closes
- **Endpoint close**: feed (i)/(ii) [the recursive sim] + (iii) [C4e] + capstone `ReconInnerGmOfLiveClose`
  → discharge `L3aEndpointAssemblyNested`'s `TODO(C4)` premises → `L3aEndpointAssemblyNestedFull`
  (value theorem unconditional for nested input). Thread the spec tree `t` (leaf == FirstLeaf(t,inp)).
- **C5 (top wiring)**: `MainTheoremL4` (copy `MainTheoremL3` LiftSim:12076-analog, swap
  `L3aCompositeClose→Rec`, endpoint→`Nested(Full)`, raw gate) + `MainExtractionNested` + widen `Supported`
  (ApiMatch.dfy:54) to a `NestedFragmentRaw` DISJUNCTION + `MatchCorrect` dispatch. Then
  `ApiMatch.MatchCorrect` covers nested capturing end-to-end.

## 6. Process notes
- Verify: `dafny verify --standard-libraries --library=deps/{linden-engine,linden-engine-model,linden-reasoning,linden-semantics-core,linden-warblre,regex-engine}.doo --allow-warnings --verification-time-limit=250 --filter-symbol=<Mod.Sym> src/Equiv/<F>.dfy` from `linden-equiv/`. Modules: MainTheorem→`LindenElkMain`, NestInv→`LindenElkNestInv`, LiftSim→`LindenElkLiftSim`, PikeInvRE→`LindenElkPikeInv`, PikeSimRE→`LindenElkPikeSim`.
- `deps/*.doo` untracked; rebuild by copying versioned `.doo` from each dep project dir. `.gitignore`
  ignores a `deps` symlink (worktree hazard). Integrate agent branches via `.dfy`-only
  `git show/diff … | git apply --3way`, never cherry-pick whole commits (avoids the deps-symlink trap).
- Two latent soundness bugs were caught + fixed this campaign: R31b's vacuous owner descent; the
  hyp-(g) depth-3 failure (fixed via the tight `DirectLidSet` frame). Trust the current green code.

## 7. SESSION-2 PROGRESS (2026-08-18) — forward chain green; endpoint conditional on ONE descent
The §4 "recursive per-body composite sim" gap was BUILT as the D-brick arc (D1–D6, all green, `b0caf59`):
the FORWARD value chain is green and `L3aEndpointAssemblyNestedFull` (LiftSim:16294) ensures
`leaf.1 == NormGm(GmOfLive(re,res))` for nested input — **CONDITIONAL** on residual `requires`.
Banked since: `a987d34` premise-3 (`M.FLookLoopTopLookClkStableFull`, third clock twin);
`2f88043` D8 (`LookNestBackTFromBodyReplay` backward per-body carrier + `GuardBridgeFromDescent` +
`ReverseCFromDescent` — both endpoint engine residuals reduced to ONE hypothesis, the DESCENT
CONCLUSION); `427d8b2` D9 (`M.FLookLoopInLookLiveOwnerMatched` = connective (A1): res0-live ⟹ innermost
owner MatchedPosLA).

**The DESCENT CONCLUSION** (the single producer still owed, task #35):
`forall g2 :: g2 in CapIdsInLooks(re) && res0-live(g2) ==> g2 in gmt` (PRESENCE-only; gmt = leaf.1 from
`BestTieLkNestedTop`). D11 (in flight, branch `brickD-11`) builds it as the reverse-mirror of the green
`FLookLoopAncestorClockChain` (LiftSim:23904, `decreases |LookIds|`): compose per-body backward carriers
`LookNestBackTTop`(top, green)/`LookNestBackTFromBodyReplay`(per-body, green) UP the nesting via
`NI.LookPathComposeNested`, using (A1) + `FLookLoopFullCoversInLooks` for the per-level (A2) tie.
A scout confirmed the LITERAL position correspondence (`get_cp(res.1,owner)==spec-cp`) is NOT needed —
the sim carries it as the presence invariant `LookNestBackTTop`; route through carriers, not raw positions.

**REMAINING MAP after D11 (~3 more bricks to `ApiMatch.MatchCorrect`):**
1. D11 descent producer → discharges endpoint reverse-(c) + `AllBodyTopFeeds` re-arm guard bridge.
2. Forward-existence residual (LiftSim:16325-44): the VALUE tie `leaf.1[g]==NormRange(LiveRange(res.0,g))`
   (spec value == engine reconstructed value). Owed separately — the forward value carrier (depth-1
   `GmtTieInside`) was DROPPED for the nested tier, so this needs the recon_inner spec-tie
   `M.LkReplayMatchesSpecNestedFull` (proven modulo its inner recursive premise, MainTheorem:8957) driven
   recursively, OR a rebuilt forward value carrier. Likely its own brick.
3. `AllBodyTopFeeds` body-arms: `LocalTopFeed(body(a),…)` per look a — the descent producer is general
   over `re` so it applies to each body(a); wire `LocalTopFeedFromNestOkT`(:23507) with the per-body
   fwd carrier (D1) + bwd carrier (D8) + `GuardBridgeFromDescent`. Depends on D11.
4. Endpoint UNCONDITIONAL + C5 (`MainTheoremL4` + `Supported` disjunction + `MatchCorrect`) per §5.
