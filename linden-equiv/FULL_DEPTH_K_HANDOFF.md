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

**The DESCENT CONCLUSION** (what both consumers need):
`forall g2 :: g2 in CapIdsInLooks(re) && res0-live(g2) ==> g2 in gmt` (PRESENCE-only; gmt = leaf.1 from
`BestTieLkNestedTop`). `ffdabee` D11 built its **position-free half** GREEN — the reverse-mirror of the
green `FLookLoopAncestorClockChain` (LiftSim:23904): `DescentLandTop` (level step, instantiates the
`LookNestBackTTop` carrier), `ReconLiveTopAncestor` (top-ancestor peel), `DescentProducerTopOwners` (emits
the target from a per-`g2` backward-carrier package), `DescentProducerWiringCheck` (confirms it discharges
`GuardBridgeFromDescent`+`ReverseCFromDescent` verbatim). **At DEPTH 1 this is the COMPLETE descent.**

## 8. THE ISOLATED KERNEL (banked, user chose to STOP here 2026-08-19) — R1 + R2
D11 proved (by reading defs) that depth-≥2 nested CAPTURING reduces to exactly TWO facts, and that they
are the **SHARED FRONTIER of BOTH the forward and the backward chains** — `L3aEndpointAssemblyNestedFull`
(backward reverse-(c) + `AllBodyTopFeeds` re-arm) AND `ReconInnerForwardWired`/`ReconBodyPathPresentLk`
(MainTheorem:11080, forward-existence VALUE tie) all take the SAME per-`g2` fresh-membership package as an
unproven hypothesis. So this is ONE kernel, not several bricks:

- **R1 (TRACTABLE, not yet built):** `res0`-live DIRECT `g2` at its innermost owner `l''` ⟹
  `g2 in PIV.GmOfLive(body(l''), FreshBodyMatch(l''))`. Route: (A1) `M.FLookLoopInLookLiveOwnerMatched`
  gives `l''` matched; `FLookLoopFullCoversInLooks` gives `res0 ~ fresh` on `{g2}` (so fresh's clock set);
  then a NEW structural lemma "DIRECT, not-under-quant group: clock-set ⟹ `PathPresentLk`" (mirror
  `PikeInvRE.LookFreePathPresentLk`/`BodyPathPresentLk` :2287 but restricted to `g2`'s own LOOK-FREE PATH,
  NOT whole-body `LookFreeRE`) + the `FilterAbsenceExtract` (:2333) contrapositive ⟹ `GmOfLive` membership.
  (D11 missed this by only trying the existing membership lemmas, which take `PathPresentLk` as INPUT.)
- **R2 (THE WALL, not built):** presence-only `g2 in leaf_{A0} ==> g2 in leaf` — inner sub-look spec leaf
  ⟹ parent spec leaf, for a DEEP `g2` (innermost owner `A1` nested inside top ancestor `A0`; the top
  carrier can't land deep `g2` since `GmOfLiveInsideLookAbsent` puts `g2 ∉ GmOfLive(body(A0), fresh_{A0})`,
  and the nested carrier `LookNestBackTFromBodyReplay` lands it only in `leaf_{A0}`). The only bridge,
  `M.OuterLeafInnerGEqOwnerBody` (:8378), is keyed on the descent-recorded position `inpo` and gives
  outer→inner. Closing R2 needs the **position correspondence** `get_cp(res.1,A0)==spec-A0-cp` in the
  "sub-leaf embeds in parent leaf" form — the tie the sim ARCHITECTURE DELIBERATELY DROPS (`GmtTieInside`
  dropped at the nested tier, C1). Scout + source comments (MainTheorem:4741-4796: sim "carries no history
  to express it"; `LookCpSpecMatch` :4710 gets oracle-uniqueness but NOT path-uniqueness) confirm this is
  NOT a small lemma: it needs either a direct position-correspondence proof (path-history the sim omits) or
  a depth-k SIM REBUILD re-carrying the inner value/presence tie. **This is the fundamental wall.**

**To RESUME depth-≥2 capturing:** build R1 (tractable, banks progress + narrows to R2), then attack R2 via
either (a) augment the composite sim to track which gate-crossing is on the winning first-leaf path (adds
the missing path-uniqueness half of `LookCpSpecMatch`), or (b) a standalone position-correspondence
capstone. R1's conclusion + R2's conclusion together discharge the per-`g2` package that D11's
`DescentProducerTopOwners` (backward) AND the forward-existence residual both consume — closing BOTH.
Then: endpoint UNCONDITIONAL + C5 (`MainTheoremL4` + `Supported` disjunction + `MatchCorrect`) per §5.

**What IS shipped (depth-k, banked green on `l4-nesting`):** full-depth-k nested-lookahead MATCHING
(end-to-end, pre-existing); the entire depth-k CAPTURING FORWARD value chain (green, conditional endpoint
`L3aEndpointAssemblyNestedFull`); depth-1 nested capturing (complete). The depth-≥2 capturing NOVELTY is
gated solely on R1+R2 above.

## 9. BOTH WALLS DISSOLVED (2026-08-20) — remaining work is MECHANICAL WIRING, no conceptual gap
§8's "R1 tractable / R2 the fundamental wall" is SUPERSEDED. Applying the fragment hypotheses (which prior
wall-verdicts omitted) collapsed BOTH:
- **R1 built green** (`94c4509`): `DirectPathPresentLk`/`DirectMxAtGidLkEq`/`DirectBodyPathPresentLk`/
  `DirectBodyKeepsPresentLk` (PikeInvRE) — direct-group membership keyed on directness (look case vacuous).
- **(A2) — the residual R1 bottomed out on — DISSOLVED green** (`7e71f38`,`df56cc1`,`efc3a5f`): the fresh
  match's own path-presence. Prior agents called it the R2 wall via a counterexample with `g` UNDER A
  QUANTIFIER — which `M.GNotUnderQuantL` (fragment hyp) FORBIDS. In-fragment `MxAtGid(body,·,g)==-1`
  (`MxAtGidNoQuant`) so dominance is free, and `PathPresent` collapses to "ancestor captures set", a MONOTONE
  register invariant `AncSetInvRE` (raw capture regs are never cleared — only `SetRegisterToCP` writes caps;
  `Reset` writes quants). Step-preservation both green: `AncSetFrameStart` (non-Open), `AncSetOpenStep` (Open,
  via `NI.NestInvOpenSite`). `AncSetToMemberNested` closes R1's `g in GmOfLive(body,rf)`.
- **R2 — DISSOLVED green** (`753d07d`,`d93380e`,`1d260f8`,`1a2a557`, LiftSim): NOT a path-history wall. The
  position tie is DEFINITIONAL at the gate crossing (`CheckOracle` writes `a_cp[l]:=cp`; `gm2=LkResult`
  formed at that same `cp`). Deep captures are IN `gm2` ("untracked, not absent"). `LkResultLandsSubFirstLeaf`
  is the crux (the fact scouts said needs path history): at a positive-look crossing with body groups cleared,
  `gm2==LkResult` agrees with the look body's own first-leaf on EVERY body group (deep incl.), via
  `M.LookBodyLeafValue`/`TreeLeavesFrameInside` — pure spec-tree, no oracle/replay/history. Plus
  `SubFirstLeafAt`(fn)+`LookNestBackTTopDeep`(pred)+`LookNestBackTGatePassTopDeep`+`DescentLandTopDeep`+
  `DescentProducerTopOwnersDeep` (unified producer landing EVERY recon-live cap, direct or deep) +
  `DeepGateReqFromCrossing`.

**REMAINING = mechanical wiring (every step has a proven green discharge; NO conceptual unknowns):**
1. **(A2) wiring** — add `AncSetInvRE(re, t.capture_regs.a_clk)` as a `PSM.PikeInvFullRE` conjunct; discharge
   entry (vacuous), all non-Open cases (`AncSetFrameStart`), Open cases (`AncSetOpenStep`); read off
   `bestmatch` in `FindMatchBodyAtCpNested`. + small bridge `GNotUnderQuantL(Translate(body),g) ⟹
   PIV.AncQuants(body,g)=={}`. (Big all-or-nothing edit — the conjunct reddens PikeSimRE until all ~8 cases
   re-discharged, but each discharge is one of the two green lemmas.)
2. **R2 wiring** — thread `LookNestBackTTopDeep` alongside `LookNestBackTTop` in `BestTieLkNestedTop` (:355)
   → `L3aCompositeCloseRec` (:22878) → `LiftFindMatchCRec`/`LiftInvRec` + step lemmas; gate step via
   `DeepGateReqFromCrossing`; deep clones of `LookNestBackTRegSame`/`LookNestBackTSetQuant` (mechanical —
   `SubFirstLeafAt` depends only on `look_regs[lid]`, exactly like `FreshBodyMatch`).
3. **Descent assembly** — feed `DescentProducerTopOwnersDeep` the per-`g2` `SubFirstLeafAt(A0)` membership
   (direct: `Sout` of `LkReplayMatchesSpecNested`; deep: `LookNestBackTFromBodyReplay`(body(A0)) + inner
   recursion of `DescentProducerTopOwnersDeep`). Its green consumers `GuardBridgeFromDescent`/
   `ReverseCFromDescent` then discharge the endpoint reverse-(c)+`AllBodyTopFeeds`. Forward-existence VALUE
   residual uses the SAME (A2)+deep-embedding machinery.
4. **Endpoint UNCONDITIONAL + C5** (`MainTheoremL4` + `Supported` `NestedFragmentRaw` disjunction +
   `MatchCorrect`) per §5.
