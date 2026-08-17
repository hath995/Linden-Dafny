# recon_inner sub-campaign — HANDOFF (2026-08-15)

Branch: **`l4-nesting`** · clean HEAD at handoff: **`e2a7ceb`** · all committed work verified green.
This doc lets you resume cold. Companion running log: `L4_L5_ROADMAP.md` (last two dated sections).

---

## 0. One-paragraph situation

We are completing **L4 = nested lookarounds** in the Linden-Dafny verified regex engine. The
whole match-verdict + oracle-build + sim halves for arbitrary nesting depth are already done
(commits up to `7610cdb`). The remaining piece was **capturing group VALUES recorded strictly
inside nested look bodies** — the `recon_inner` sub-campaign. Its two mathematically novel halves
are now **PROVEN and whole-file-certified green**; what remains is **structural glue** to discharge
the per-look seam and wire it to the top (that glue = W6 endpoint territory). Two glue bricks were
in flight when work was halted; they have **partial committed progress on side branches** (§5).

---

## 1. The seam (the target)

`M.LkReplayMatchesSpecNestedFull` — MainTheorem.dfy:6059 (`M` = module `LindenElkMain`). It reduces
the full-`DefGroups` value keystone for a nested positive lookAHEAD to two premises over a
reconstructed register bank `(reccap, reclk, recqt)`:
- **recon_outer**: `GmOfLive(body, reccap,…)` agrees with the fresh body match `GmOfLive(body, rf,…)`
  on the OUTER groups `Sout = DefGroups(tr) \ LkBodyGroups(tr)`.
- **recon_inner**: on `LkBodyGroups(tr)` (groups inside nested looks), `GmOfLive(body, reccap,…)`
  agrees with the spec `LkResult(la, tlk, gmMain, inp).value`.

Base case `M.LkReplayMatchesSpecNestedFullBase` (6158, look-free body) is unconditional. Discharging
these two premises for nested bodies is `recon_inner`.

Architectural key (why this is the last hard thing): a lookaround compiles to a SINGLE
`CheckOracle` leaf, so a fresh body match `rf` records NONE of its body's inner-look captures — those
values are rebuilt by the engine's `FLookLoop` pass (Interpreter.dfy:560) via the inner lids' own
iterations, threaded through the look bank. So `recon_inner` = "the FLookLoop reconstruction matches
the spec on inner groups."

---

## 2. DONE and committed on `l4-nesting` (all verified green)

All additive; integrated by extracting `.dfy`-only patches (never cherry-pick whole commits — see §6).

| Commit | Brick | Content | In-tree verify |
|---|---|---|---|
| `4cb73aa` | **R1** (NestInv + MainTheorem) | `InnermostOwnerDirect` (g resolves to an owner lid holding it DIRECTLY), `NestDepthLookBodyDrops`, `NestedGWriteFrame`, `VBodyEqLookBody` (`LookTablesOk ⟹ VBody(crv,l)==LookBodyOfRE(re,l)`) | green (2/0 each) |
| `e3375dd` | **R2** (MainTheorem) | `FLookLoopCaptureFrameNested` (frame: writes only inside S; look bank GROWS by inner a_cp → `RegsAgreeOutside(res.1, lk, Slook)`, NOT `res.1==lk`), `FLookLoopValueLiftOuter`/`FLookLoopValueOkOuter` (per matched look, res.0 carries fresh match on OUTER caps `CaptureRegsSet(CapIdsOutsideLooks(body))`) + supporting stack. Per-lid bridge = `ReplayLidCapAgreeFreshNested`. Scope: capturing looks Lookahead-only. | green (191/0, 630/0) |
| `2580012` | **R3** (MainTheorem) | `FLookLoopValueLiftFull` / `FLookLoopValueOkFull` (whole-loop, re-keyed on the FINAL look bank `res.1` so inner-owner coverage is retained), `FLookLoopFullCoversInLooks` (every `g in CapIdsInLooks(re)` whose owner is matched is carried in `res.0` at its innermost owner's fresh value). Adds hyp **(h)** well-nested-lids + `FLookLoopLidCpStable` (a_cp[lid] stability). **This is the ENGINE side of recon_inner.** | green (636/0, 2/0) |
| `eb75141` | **R3b** (MainTheorem) | Pure-spec composition toolkit: `TreeResGValueFramed` (TreeRes leaf value at group g depends on incoming gm only through gm[g]; NO confinement), `TreeResGIndepWhenWritten` (maps differing only at g: if g written on winning path, leaf values AGREE at g — owning look pins it), `TreeResLkNodeGValue` (matched look node's leaf value at g == the look SUB-TREE's TreeRes value at g), + `AgreeOffG`/`GDefBeforeClose`/`GNotWritten` predicates + frame helpers. **This is the SPEC side of recon_inner.** | green (4/0,2/0,2/0,2/0) |
| `7609621`, `e2a7ceb` | docs | roadmap log | — |
| `adca767` | chore | `.gitignore` a `deps` SYMLINK (worktree hazard fix, §6) | — |

**Whole-file certification at `e2a7ceb`:**
- `MainTheorem.dfy` → **4507 verified, 0 errors**
- `NestInv.dfy` → **167 verified, 0 errors**

Both novel obstacles cleared. `recon_inner` is proven at the register level (values ARE
reconstructed) and the spec level (the reconstruction matches the spec's group-value structure).

---

## 3. What REMAINS to discharge the seam (the glue — tasks #30 then #15/W6)

Three bricks (see task #30):

1. **FLookLoop bank instantiation (R30a)** — discharge hypotheses (a)-(h) of
   `FLookLoopFullCoversInLooks` / `FLookLoopCaptureFrameNested` from the compilation tables, i.e. a
   nested analogue of `M.LookRowsFromTablesL3a` (MainTheorem.dfy:6739). Requires `NestedFragmentRE(re)`
   instead of `LookBehindFragmentRE`; produces `NegLooksLookFreeRE(body)` per lid + the well-nesting
   (D-ord)/(f)/(g)/(h) facts from `LTB.LidsWellNested`/`SpecRegexLidsWellNested` +
   `NI.LookBodiesCapsDisjointOrNested` (NestInv:4486). Output: a premise-free
   `FLookLoopFullCoversFromTables`. → yields recon_outer + engine side of recon_inner. Mostly
   mechanical (mirror `LookRowsFromTablesL3a`).

2. **Regex↔spec-tree owner-node correspondence (R30b) — THE crux.** A structural lemma:
   `TreeRes(tlk, gm, inp, Forward).value.1[g] == <owner look's LkResult value at g>` for
   `g in LkBodyGroups(Translate(body))`, where `tlk = ComputeTr(Translate(body))` and the owner look's
   sub-tree is `ComputeTr(Translate(LookBodyOfRE(body, owner)))`. Best framing: tree induction reusing
   R3b's `TreeResLkNodeGValue` to peel one LK layer + recurse into the sub-tree for deeper nesting
   (measure: NestDepth via `NI.NestDepthLookBodyDrops`), with continuation-doesn't-write-g from group
   uniqueness. Templates: `M.TreeResGmFrameRec` (5808, LK case), `M.BodyTreeAtCpNested` (3103, its
   proof navigates `tlk` structure via `ComputeTr`/`BooleanCorrectLkRec`/`ActionsTreeRepRENested`).

3. **Assembly** — instantiate reccap := FLookLoop over the body's inner lids (seeded from `rf`, whose
   look bank already carries inner a_cp from gate crossings); chain per inner g:
   `reccap[g]` = owner fresh value (brick 1 / `FLookLoopFullCoversInLooks`) = owner-standalone
   `LkResult[g]` (`M.LkReplayMatchesSpecNested`, 5964 — g is an OUTER group of the owner's body, so it
   applies) = outer `LkResult[g]` (brick 2). recon_outer from `FLookLoopCaptureFrameNested`. Then call
   the seam → premise-free `LkReplayMatchesSpecNestedFullClosed`.

After #30: **W6 (task #15)** wires the closed keystone into the whole-regex value bridge — nested
`GmtTieInside` (LiftSim.dfy:191, currently flat/depth-1), `L3aValueBridge` (LiftSim:10753),
`L3aEndpointAssembly` (LiftSim:11496), `MainTheoremL3` (LiftSim:12076) — and widens the `Supported`
gate `LookBehindFragmentRaw → NestedFragmentRaw` (ApiMatch.dfy:54). This is a substantial integration.

---

## 4. Position-correctness note (a subtlety for brick 3)

The owner's fresh match runs at the a_cp recorded when `rf` crossed the owner's `CheckOracle` gate.
Tying that recorded a_cp to the spec tree's evaluation position of the owner look is the match-level
correctness already proven by `M.BodyTreeAtCpNested` / `M.FindMatchBodyAtCpNested` (3103/2887). Brick
3 must thread this; it is not new math but needs care.

---

## 5. IN-FLIGHT PARTIAL WORK (preserved on side branches — NOT integrated, NOT re-verified in-tree)

Two agents were mid-flight when halted; their commits are preserved on branches (do not delete):

- **`recon-r30a`** (worktree `.claude/jobs/942c133e/tmp/wt-r30a`, but note that dir is job-scoped):
  - `27743c5` "recon R30a: NoPosLookbehindRE + LookBodyFactsNested" — early helpers toward the
    nested tables-discharge. Status: agent commits after local green, but **re-verify before trusting**.
- **`recon-r30b`** (worktree `…/wt-r30b`) — substantial progress on the crux (brick 2):
  - `8300a38` "TreeResLkNodeGValueFresh (single-layer outer-leaf==owner-fresh-sub at g)"
  - `404f0c4` "TreeResGSpineValue + GWriteOnlyInLooks (multi-layer descent engine)"
  - `9893d7b` "strengthen TreeResGSpineValue with structural-decrease ensures (tsub < t)"
  - Status: the last commit may be WIP (it was mid-strengthening when killed). **Re-verify each
    symbol in-tree before trusting/integrating.** `TreeResGSpineValue` + `GWriteOnlyInLooks` look like
    the multi-layer descent engine for brick 2 — likely the highest-value partial to salvage.

To inspect: `git log --oneline l4-nesting..recon-r30a` / `..recon-r30b`; the transcripts are at
`/tmp/claude-1000/.../tasks/a210bde41091bb1c3.output` (R30a) and `ade6d51deffbce0e0.output` (R30b)
but they are large JSONL — grep, don't cat.

To salvage a branch's work: extract the `.dfy`-only diff and re-verify (see §6), do NOT cherry-pick.

---

## 6. Process / gotchas (IMPORTANT)

- **Toolchain / verify one symbol** (from `linden-equiv/`):
  ```
  /home/aaron/.local/share/lemmata/toolchains/4.11.0/dafny/dafny verify \
    --standard-libraries \
    --library=deps/linden-engine.doo --library=deps/linden-engine-model.doo \
    --library=deps/linden-reasoning.doo --library=deps/linden-semantics-core.doo \
    --library=deps/linden-warblre.doo --library=deps/regex-engine.doo \
    --allow-warnings --verification-time-limit=250 \
    --filter-symbol=LindenElkMain.<Symbol> src/Equiv/MainTheorem.dfy
  ```
  `--allow-warnings` is required (pre-existing trigger/indentation warnings). Green =
  "Dafny program verifier finished with N verified, 0 errors". **Passing multiple `--filter-symbol`
  is unreliable — verify ONE symbol per invocation.** Modules: MainTheorem→`LindenElkMain`,
  NestInv→`LindenElkNestInv`.

- **`deps/` is untracked build artifacts** (`linden-equiv/deps/*.doo`), regenerable by copying the
  versioned `.doo` from each dependency project dir (e.g. `linden-engine/linden-engine-1.0.2.doo` →
  `deps/linden-engine.doo`; also `-model`, `-reasoning`, `-semantics-core`(1.0.2), `-warblre`(1.0.3),
  `regex-engine`(1.0.1)).

- **deps-symlink hazard (bit us once, now fixed):** worktree agents symlink `linden-equiv/deps` to the
  primary checkout; `git add -A` staged that symlink and a cherry-pick then OVERWROTE the real `deps/`
  with a self-referential link. `.gitignore` now ignores a `deps` symlink (commit `adca767`).
  **Rules:** agents `git add <specific .dfy>`, never `-A`; **integrate agent commits by
  `git show <c> -- <path> | git apply --3way --index` (`.dfy`-only), never `git cherry-pick`.**

- **Integration recipe used throughout:** create worktree off `l4-nesting` HEAD (NOT the Agent tool's
  auto-worktree — its baseRef defaults to `origin/main` which LACKS all L4 work); symlink deps;
  dispatch general-purpose agent with the verify command + additive/commit-per-lemma discipline;
  on return, `git diff <base> <tip> -- <file> | git apply --3way --index`, re-verify the key symbols
  in-tree, commit with the two trailers, retire the worktree (`git worktree remove -f`).

- Commit trailers (every commit):
  ```
  Co-Authored-By: Claude Opus 4.8 <noreply@anthropic.com>
  Claude-Session: https://claude.ai/code/session_01FtE81STsH2MdZmoktrRS2j
  ```
  Do NOT merge to main, do NOT push to origin (never authorized).

---

## 7. Task map

- **#26** recon_inner (umbrella): engine + spec halves DONE; remainder = #30.
- **#27 / #28 / #29** R1 / R2 / R3+R3b: **completed**.
- **#30** seam discharge glue (bricks 1-3 of §3): **in_progress** (partial on `recon-r30a`/`recon-r30b`).
- **#15** W6 endpoint + `Supported` widening: pending (after #30).
- **#11** W2 (`GmtTieInside` owner→innermost rewiring): folds into W6.

---

## 8. Resume checklist

1. `git worktree list`; confirm `l4-nesting` at `e2a7ceb` (or later), clean.
2. Salvage §5 partials: for each of `recon-r30a`/`recon-r30b`, extract `.dfy`-only diff, re-verify
   each new symbol in-tree, keep what's green (esp. `TreeResGSpineValue`/`GWriteOnlyInLooks` for
   brick 2). Drop any WIP/red tail.
3. Finish brick 2 (owner-node correspondence) — the crux; then brick 1 (tables-discharge, mechanical);
   then brick 3 (assembly → `LkReplayMatchesSpecNestedFullClosed`).
4. Full-file re-certify `MainTheorem.dfy` (whole-file, no filter) before declaring done.
5. Then W6 (#15).

---

## RESUME PROGRESS (2026-08-17) — bricks 1 & 2 landed; remaining = brick-3 assembly (W6)

Resumed from the halt: salvaged both in-flight partials green, then finished bricks 1 & 2.
Branch `l4-nesting` HEAD `1967b78` (pending full-file re-cert). New commits since the halt:

- **`e08ef38` (salvage R30a+R30b):** `NoPosLookbehindRE`, `LookBodyFactsNested` (sub-body facts);
  `GWriteOnlyInLooks`, `TreeResLkNodeGValueFresh`, `TreeResGSpineValue` (spec descent — but see below).
- **`4919254` (R31b, brick 2 = owner-node correspondence):** CORRECTS a subtlety — the salvaged
  `TreeResGSpineValue` returns the structurally DEEPEST matched look, NOT g's owner (value holds by
  pass-through). Sound owner-finder added: `GOwnerWF` + `GOwnerWFImpliesSpine`, `TreeResGOwnerDescent`
  (sound iterate-to-innermost-owner), `TreeResGOwnerFresh` (Empty-map form), `ComputeTrSingleLookUnfold`
  (atomic `ComputeTr(single look)==LK(lk,ComputeTr(body),Match)`), `SingleLookOuterLeafIsOwnerBody`
  (**depth-2 single-direct-owner spec identity CLOSED**).
- **`1967b78` (R31a, brick 1 = tables-discharge, COMPLETE, depth<=2):** `LookRowsFromTablesNested`
  (produces all (a)-(h) from the compilation tables) + `FLookLoopFullCoversFromTables` (PREMISE-FREE:
  recon_outer + recon_inner engine coverage) + 22 supporting lemmas. Mirrors `LookRowsFromTablesL3a`.

### The two scope findings (both converge at depth 2)
1. **(g) caps at depth 2.** R2/R3's hypothesis (g) `LookIds(b1)*LookIds(b2)=={}` is FALSE at depth>=3
   (`l1>l2>l3` shares l3), CONFIRMED essential. `FLookLoopFullCoversFromTables` carries `NestDepth<=2`.
   Full depth-k needs (g) weakened to "disjoint-or-nested" + R2/R3 (630/636 VC) re-proven.
2. **General multi-layer 2b is a mini-campaign.** `TreeResGOwnerFresh` gives an ABSTRACT owner subtree;
   pinning it to `ComputeTr(Translate(LookBodyOfRE(body,owner)))` GENERALLY needs a regex-tracking
   descent threading `EL.BoolTreeLk` (a nested `BodyTreeAtCpNested`) + handle the `GOwnerWF` caveat
   (quantified capturing lookarounds duplicating the owner body). Depth-2 single-owner IS closed.

### recon_inner COMPONENT INVENTORY (all proven & green, reusable)
- Engine reconstruction: `FLookLoopValueLiftFull`/`FLookLoopFullCoversInLooks` (R3) +
  `FLookLoopFullCoversFromTables` (R31a, premise-free, depth<=2).
- Spec composition/descent: R3b toolkit + `TreeResGOwnerDescent`/`TreeResGOwnerFresh`/
  `SingleLookOuterLeafIsOwnerBody` (R31b).
- Per-owner tie: existing `LkReplayMatchesSpecNested` (5964).

### REMAINING = brick-3 assembly = W6 (task #30 -> #15)
Chain, for inside-look `g`: `GmOfLive(re,res.0,…)[g]` == owner fresh value (R31a) == owner
`LkResult[g]` (`LkReplayMatchesSpecNested`, supplying its engine hyps + the position match
`res.1[owner]`==spec owner-eval position via `BodyTreeAtCpNested`) == outer/winning leaf`[g]`
(R31b spec identity). This IS the whole-regex nested inside-look value bridge = nested
`GmtTieInside`/`L3aValueBridge`/`L3aEndpointAssembly`/`MainTheoremL3`, + `Supported` widening
`LookBehindFragmentRaw->NestedFragmentRaw`. Substantial W6 integration; depth-2 first, then the two
full-depth-k follow-ons above.

---

## FULL-DEPTH-K PUSH (2026-08-17) — components ALL PROVEN; brick C = the endpoint (composite-sim territory)

User chose "full depth-k". Every reusable COMPONENT is now proven & green on `l4-nesting` (HEAD `351bd51`).
Scope of the fragment being closed: nested FORWARD capturing lookaheads (`NoPosLookbehindRE`), captures
NOT under a quantifier inside looks (`GNotUnderQuantL` — a quantifier emits a spine `Reset(DefGroups)`
touching the group, proven necessary).

### DONE (commits, all whole-file-certified green)
- **A** `2ae7a92` — ENGINE reconstruction DEPTH-GENERAL. Finding: the disjoint-or-nested trichotomy is
  insufficient for (f) look-stability at depth≥3; real fix = a TIGHT `DirectLidSet` frame replacing (g)
  with ordered `l1<l2 ==> DirectLookIds(b1)*LookIds(b2)=={}`. Re-proved `FLookLoopValueLiftOuter` 693/0,
  `FLookLoopValueLiftFull` 699/0; `FLookLoopFullCoversFromTables` is premise-free at ALL depths (cap gone).
- **B** `d6fc655` — spec owner↔tree for the LINEAR lookahead-chain fragment, all depths.
- **B'** `53db9ea` — general-branching VALUE HALF (`OuterLeafGOwnerSubtree`) + `ComputeTrGOwnerWF2`
  (side cond `GNotUnderQuantL`). FINDING: R31b's `TreeResGOwnerDescent/Fresh` were VACUOUS
  (`GOwnerWF<==>GNotWritten`) — replaced by the live `GOwnerWF2`/`TreeResGOwnerDescentV/FreshV`.
- **B''** `ed12289` — ACTION-SPACE owner-naming descent (`ComputeTrOwnerNamed`/`Acts`,
  `ComputeTrAllLkBodiesNamed`). Insight: push the owner look to the action HEAD → each peel is atomic;
  ComputeTr(build)/TreeRes(eval) position alignment falls out for free.
- **R↔L** `351bd51` — TURNKEY `OuterLeafInnerGEqOwnerBody`: outer leaf[g] == NAMED owner body
  `ComputeTr(Translate(LookBodyOfRE(body,owner)))` sub-result at g, general branching all depths.
  Via `TranslateOwnerBodyIsRR` (R↔L identity). **The spec side of recon_inner is COMPLETE.**

### recon_inner FULL-DEPTH-K COMPONENT INVENTORY (all proven)
1. Engine: `M.FLookLoopFullCoversFromTables` (premise-free, depth-general) — res.0[g] == innermost-owner
   fresh value for every g in CapIdsInLooks(re).
2. Spec: `M.OuterLeafInnerGEqOwnerBody` (turnkey, general branching) — winning leaf[g] == owner body
   spec sub-result[g].
3. Tie: `M.LkReplayMatchesSpecNested` (existing) — owner fresh value[g] == owner body spec sub-result[g].
   Chain: leaf[g] == owner sub-result[g] == owner fresh[g] == res.0[g]. recon_outer from
   `FLookLoopCaptureFrameNested`.

### REMAINING = brick C (task #33) — the whole-regex endpoint. IT IS COMPOSITE-SIM TERRITORY, not a quick assembly.
Endpoint chain (scout, single-caller linear): `ApiMatch.MatchCorrect(:75) -> LSIM.MainTheoremL3
(LiftSim:12076) -> {L3aCompositeClose(:11411), L3aEndpointAssembly(:11496), MainExtraction(MainTheorem)}`,
`L3aEndpointAssembly -> L3aValueBridge(:10753)`. Each has exactly ONE caller ⇒ **additive nested variants**
(`MainTheoremL4`/`L3aEndpointAssemblyNested`/`L3aValueBridgeNested` + widened `Supported` at ApiMatch:55)
disturb zero existing callers. `L3aValueBridge` + `MainExtraction` are structure-agnostic (only the
fragment NAME caps them).
THE HARD PART: `GmtTieInside` (LiftSim:191) — its flat single-owner existential + single `FreshBodyMatch`
is FALSE for a nested g (an outer look's fresh match records no inner captures), AND during the MAIN walk
inner a_cp is never recorded. So the nested `BestTieLk` must DROP `GmtTieInside` and establish inner-group
agreement POST-HOC at the endpoint via components 1-3 above. That means a nested composite sim
(`ThreadRepLk`-minus-`GmtTieInside` variant of `LiftInitC`/`LiftFindMatchC`/the ~24 `LiftPreserve*`) that
produces (match-verdict + `GmtTieOutside` only). The nested MATCH sim is already proven
(`FindMatchSimRENested` #20) and `GmtTieOutside` is depth-agnostic (outer captures recorded directly), so
the nested composite sim is FEASIBLE but LARGE. Then `L3aEndpointAssemblyNested` swaps the flat
`FLookLoop*` reconstruction for `FLookLoopFullCoversFromTables` and closes inner groups via
`OuterLeafInnerGEqOwnerBody` + `LkReplayMatchesSpecNested`, and `MainTheoremL4` widens the raw gate.

Bottom line: full depth-k CAPTURING is component-complete; brick C is a bounded-but-major final
integration (a nested composite-sim endpoint), comparable to an earlier campaign phase.
