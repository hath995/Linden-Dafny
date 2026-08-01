# L3a Final Assembly — Handoff (updated 2026-08-01)

**Goal:** finish proving `MainTheorem` (and thus flip `Supported`) for **capturing
positive lookaheads** — `(?=(a))`, `(?=(a))*`, etc. — so the engine's answer is
shown to equal the ECMAScript tree semantics' first-leaf capture array, *including
the reconstructed lookahead group captures*.

**Branch:** `l3a-value-assembly` (tip `5bb7329`). All lemmas below are committed and
individually verified.

**Dafny:** 4.11.0 at `C:\Users\Aaron-pc\Downloads\dafny-4.11.0-x64-windows-2022\dafny\Dafny.exe`
(the `/c/Program Files/dafny` one is 4.10 and CANNOT load the 4.11 `.doo` deps).

**Per-symbol verify** (fast; whole-file `MainTheorem` ≈ 15-20 min). Substring match;
also surfaces resolution-time warnings (`allow-warnings = false`, so `set g | g in <seq>`
trigger warnings FAIL — use index-triggered quantifiers / `NoDupPrepend` helpers):
```
"$DAFNY" verify src/Equiv/<File>.dfy --standard-libraries \
  --library=deps/linden-engine-model.doo --library=deps/linden-engine.doo \
  --library=deps/linden-reasoning.doo --library=deps/linden-semantics-core.doo \
  --library=deps/linden-warblre.doo --library=deps/regex-engine.doo \
  --verification-time-limit=900 --filter-symbol=<Name>
```
Files touched by the assembly: `MainTheorem.dfy`, `ClockMono.dfy`, `PikeInvRE.dfy`,
`LookLeaves.dfy`, `OracleEntry.dfy`.

---

## 0. Current package state

Whole-file `MainTheorem` = **2679 verified, 7 errors**. The 7 errors are the SAME
three PRE-EXISTING dead lemmas throughout the campaign (they predate this session):

- `LkBodyGroupsEmpty` (`MainTheorem.dfy:3236`) — asserts `LkBodyGroups(Translate(re)) == {}`.
  FALSE once lookaheads capture. It is the `S == {}` shortcut inside `MainTheorem`'s else
  branch (the `var S := LL.LkBodyGroups(...)` / `assert S == {}` block at ~2631).
- `FilterUnmoved` (`:4133`) — the L1 "the replay can't move the answer" lemma; only true for
  capture-free bodies.
- `LookRowsFromTables` (L1, `:4320`) — its ensures demands `CaptureFreeRE(body)` for EVERY
  matched lid; false for a capturing lookahead. **`LookRowsFromTablesL3a` replaces it.**

**These three become DEAD when the else-branch is rewritten to the L3a path — delete them
(or scope their `requires` to capture-free lookaheads). Do NOT try to "fix" them.**
`MainTheorem`'s body "verifies" today only because Dafny TRUSTS `LkBodyGroupsEmpty`'s
(now-false) `ensures S == {}`.

---

## 1. WHAT IS DONE — the assembly is ~90% built & verified

All of the following are committed on `l3a-value-assembly` and green in isolation. The
ONLY thing not built is the single gate in §2.

### 1a. Bundle producers (the value lift's per-lid hypotheses)
- **`LmOfInvL3a`** (`MainTheorem.dfy`) — extends `OE.LmOfInv`, threading `CapUnique(re)` to
  add `CapUnique(body)` + `CapIds(body) <= CapIdsInLooks(re)`; body pinned to the table row
  via `LookEntryOk` (== `VBody(crv,l)`). Helper `LookEntryBody`.
- **`LmOfBodiesDisjoint`** + `AltConBodiesSplit` — distinct lookaround ids own DISJOINT
  CapIds (look-free bodies never nest; `CapUnique` separates alt/con siblings).
- **`LookRowsFromTablesL3a`** — produces, over `S = CaptureRegsSet(CapIdsInLooks(ast))`, the
  full `FLookLoopCaptureFrame` / `FLookLoopValueLift` per-lid bundle (`LookEntryOk`,
  `LookFreeRE`, `PlusFragmentRE`, `CapUnique(body)`, `QuantUnique(body)`, `CaptureRegs(body)
  <= S`, quant-in-looks, `non-lookahead ==> CaptureFreeRE`) PLUS the pairwise-disjoint forall.
  Full fragment (capture-free lookbehinds included).

### 1b. The value lift now covers the WHOLE fragment (a latent-bug fix, NOT in the old plan)
- **`FLookLoopValueLift`** dropped its (unsatisfiable-for-lookbehinds) "lookahead-only"
  requires. A matched capture-free positive LOOKBEHIND is now stepped through as the
  IDENTITY (backward replay writes no captures — `ReplayFrames`; `MatchedPosLA` is false, so
  the value conclusion is `ValueOkSkipLid`). New helper **`FFindMatchPlusOvStableLB`**
  (lookbehind oracle-stability for `compile_to_bytecode(reverse_regex(body))`; reversal
  preserves look-free/plus-fragment/quant-unique). Result register lengths via the
  direction-generic `FFindMatchRegsWf`. **This was silently broken for any `Supported`
  pattern with a capture-free lookbehind** — `Supported` = `LookBehindFragmentRaw` admits them.

### 1c. (E) — the INSIDE-look ENGINE value bridge  `GmOfLive(re,res.0)[g] == GmOfLive(body,rf)[g]`
- **`GmOfLiveInsideLookAbsentEq`** (fully self-contained): an unset inside-look `g` is absent
  BOTH sides (`FilterCaptureNeg`; `res.0 == rf` on `CaptureRegs(body)`).
- **`GmOfLiveInsideLookPresentEq`**: present case — each side is the raw `LiveRange` of its
  own bank (`GmOfLiveKeepsPresentLk` ×2), banks agree on `g`'s registers ⇒ equal. Takes the
  path-presence conditions as EXPLICIT hypotheses.
- **`BodyPathPresentLk`** (+ `LookFreePathPresentLk`, `LookFreeMxAtGidLkEq`,
  `LookFreeCapIdsInLooksEmpty`, all in `PikeInvRE.dfy`) — discharges the BODY half of
  `GmOfLiveInsideLookPresentEq`'s path hypotheses: `g` present in a LOOK-FREE body's
  `GmOfLive` is path-present there (`GmOfLivePresenceExtract` applies — a look-free body has
  no inside-look captures — lifted to the look-aware `PathPresentLk`/`MxAtGidLk`). **Leaves
  only the RE-side (outer-path) hypothesis, which is part of the §2 gate.**

### 1d. (S-ii) core — the value-confinement least-lemma
- **`FirstLeafValueConfined`** (`MainTheorem.dfy`) — value analogue of `FirstLeafClosed`:
  proves `ValConf(gm,acts,leaf,S)` = a SETTLED inside-look `S`-group (present in `gm`, its
  look no longer pending) keeps its `gm` value into the final leaf. Cleaner than
  `FirstLeafClosed`: drops `LkClosedInGm`; LK case rides `LL.GmConfinedLeaves`; quant-`GMReset`
  case rides the new `DefGroupsInLkOrOutside` split (`QuantSettledNotReset`). Carries the
  same invariants as `FirstLeafClosed` (reuses `TailInv`/`SubInv`/`QuantSubInv`/
  `QuantSubInvCheck`) plus `S * OuterDefsActs == {}`. Helpers: `ValConf`, `ConfineStep`,
  `QuantConfBridge`, `QuantCheckConfBridge`.

### 1e. (S-i) — the cp-bound half  (discharges `cp_ctx_ok` entirely, no exact position)
- **`CM.FFindMatchLookCpOk`** (`ClockMono.dfy`) — a PARALLEL induction on `FFindMatch`
  (`VmLookCpOk` + `FAdvanceEpsilonLookCpOk` + `FConsumeLookCpOk` + `SetRegLookCpLE`, cloning
  the `FFindMatchLookFrame` trio) proving a forward match records only look cps `<= |str|`.
  Does NOT touch `PikeInvFullRE` → zero risk to the green PikeSim proofs.
- **`MainMatchCpCtxOk`** (`MainTheorem.dfy`) — bridges it to the value lift's `cp_ctx_ok`
  hypothesis on the winning thread (`get_cp` Some ⇒ `a_cp[l] >= 0`; `<= |str|` from the
  bound; `cp_context` forward nextchar definitional). **`cp_ctx_ok` is fully discharged.**

### 1f. Pre-session machinery (still green, don't rebuild)
`FirstLeafClosed`/`FirstLeafClosedNoLk` (closedness least-lemma + `LkClosedInGm`/
`OuterLkDisjoint` invariants), `TA_NoDup`/`NoDupPrepend`/`SpecRegexOuterLkDisjoint`
(group-id uniqueness → `OuterLkDisjoint`, wired into `MainExtraction`), `LookBodyLeafValue`,
`LkBodyGroupsEqCapIdsInLooks`, `TranslateDefGroupsEqCapIds`, `OutsideLookValueBridge`
(outside-`S` half), `FLookLoopValueLift`→`FLookLoopValueOk`, `FLookLoopCaptureFrame`,
`FLookLoopQuantFrame`, `ReplayCapIsBodyLeaf`, **keystone `LkReplayMatchesSpec`**,
`TreeResGmFrame`, `TreeLeavesFrameInside`, `FBuildCaptureUnfoldL3a`, `ReplayThreadWfLA`,
`FreshMatchWf`, `FirstLeafAgreeOutside`, `BodyTreeAtCp`/`FindMatchBodyAtCp`,
`EL.ComputeTrGmIndepLk`/`ComputeTrNoLK`/`TranslateNoLkBr`, the `LeavesAgreeAtOutside(S)`
checked-tree reframe, `PIV.GmOfLiveFrameOutside`/`GmOfLiveKeepsPresentLk`/
`FilterAtLookaroundMatched`/`GmOfLiveInsideLookAbsent`/`GmOfLivePresenceExtract`.

---

## 2. THE ONE REMAINING GATE — the winning-thread↔tree POSITION/STRUCTURE correspondence

Everything else is done. This single research build is the last thing between the assembled
machinery and a green `MainTheorem`. It has TWO faces that are the SAME augmentation:

### (S-i) exact position:  `look_regs.a_cp[l] == CpOf(inp_l)`
For inside-look group `g` owned by lid `l`, the keystone runs `FreshBodyMatch` at
`cp = a_cp[l]` and produces the value at `InpOfCp(str, cp)`; the (S-ii) extraction produces
the tree LK node at `inp_l` (t's first-leaf-path position of lid `l`'s LK node). They compose
ONLY if `cp == CpOf(inp_l)`.

### (E) RE-side:  `PathPresentLk(re, res.0.clk, look.clk, res.2.clk, -1, g)` for inside-look `g`
Refined into three parts:
- **INNER (body) path present — DONE** (`BodyPathPresentLk` on `rf`; `res.0 == rf` on
  `CaptureRegs(body)` so the body-reg reads agree).
- **look matched — `look.clk[l] >= 0 && >= mx`.** `>= 0` is a cheap parallel frame (clone the
  cp-bound; a "look clk set when cp set" invariant). `>= mx` needs clock monotonicity vs the
  ENCLOSING quant clocks — coupled to the outer structure.
- **OUTER ancestors of the lookaround present in `res.0`** (== main caps outside inside-look)
  — the hard winning-thread fact.

**Both faces reduce to: augment the winning-thread↔tree correspondence to carry, for
inside-look groups, (a) the look POSITION and (b) the OUTER-path structure.** Today
`BestMatchRE` (`PikeInvRE.dfy:5512`) carries only `GmOfLive` (`ThreadTracksGm`), which reads
look CLOCKS/values — never look POSITIONS, and has no per-inside-look outer-path handle.

### Why tstar alone doesn't give it (pinned)
The CheckOracle write (`Interpreter.dfy:315-318` fwd, `:702-705` bwd) sets `a_cp[l] := s.cp`
as a STUTTER, and the checked tree tstar is GATE-TRANSPARENT (`TreeRepRE` CheckOracle rule
`TreeRepRE.dfy:151`: the tree at the gate pc IS the continuation; `TreeThreadRE.dfy:99` lists
CheckOracle in `StuttersRE`). So "tstar's gate position" is a CODE-pc notion, not a
tree-node on tstar. The LK node lives only in the SPEC tree `t`.

### The oracle-uniqueness intuition (the shape of the proof)
Both `a_cp[l]` and `CpOf(inp_l)` are positions where the oracle for `l` is TRUE
(`OracleOkSuffix`: `view_get_oracle(ov, cp, l) <==> spec look l matches at InpOfCp(str,cp)`).
On the priority-first winning path the look is crossed at a UNIQUE position (its LAST
iteration for a quantified look), so the two coincide — PROVIDED the engine and spec follow
CORRESPONDING paths past the look. `LeavesAgreeAtOutside(tstar,t,S)` (`LookLeaves.dfy:642`)
already gives LEAF-position agreement (`[i].0 == [i].0` for all gm) + gm agreement outside S;
the missing piece is lifting that to the INTERMEDIATE LK-node position.

### Build plan (dedicated session; PARALLEL where possible to limit blast radius)
1. **Cheap frames first (safe, cp-bound style):** a "look clk set when cp set" parallel frame
   (gives `look.clk[l] >= 0` for matched `l`).
2. **SPEC-side (ii):** `GatePos(tstar,l) == inp_l` — tstar's gate position (code-pc's input)
   == t's LK-node position. Either extend `ActionsTreeRepFRE` (615-line `{:isolate_assertions}`,
   fragile) to assert position agreement at LK nodes, OR a parallel structural lemma on the
   ComputeTr walk (positions at OUTSIDE-inside-look nodes agree because the pre-look
   consumption is identical). A truncation trick may reduce it to `LeavesAgreeAtOutside` on
   the tree truncated at lid `l`'s LK node.
3. **SIM-side (i):** `a_cp[l] (winning thread) == GatePos(tstar,l)` + the OUTER-path presence
   — augment `PikeInvFullRE`/`FindMatchSimRE` (or a parallel sim) to track look positions and
   inside-look outer structure. The cp-bound trio (`FFindMatchLookCpOk`) is the template for
   the FAdvanceEpsilon-side reasoning. WARNING: mutating `PikeInvFullRE`/`FindMatchSimRE`
   re-verifies huge lemmas (10-20 min each) and can break green PikeSim proofs.
4. Transport to the winning thread (`BestMatchRE` / `FirstLeaf(tstar)`), compose (i)+(ii).

**Scale/risk:** comparable to `ThreadTracksGm` itself. This is THE piece to schedule as a
dedicated focused effort with a clean run.

---

## 3. Also still to build (the wiring, AFTER the §2 gate)

- **(S-ii) EXISTENTIAL-EXTRACTION layer** — turns `FirstLeafValueConfined` (vacuous at the
  top-level `gm==Empty`) into per-inside-look-`g` values: for each `g in leaf.1`, produce the
  owning look's `(r1, gmn, inpn)` with the RESET `GmAgreeOn(gmn, Empty, DefGroups(r1))` and
  `leaf.1[g] == TreeLeaves(ComputeTr([Areg(r1)], inpn, Empty, LkDir), gmn, inpn, LkDir)[0].1[g]`.
  The tree's LK-node tlk is ALWAYS Empty-context (BoolTreeLk builds it with `LG.Empty`), so the
  keystone (which takes tlk+gmMain and internally does `ComputeTrGmIndepLk` to reduce
  gmMain→Empty) applies with `gmMain = gmn`. It is an existential-in-a-least-lemma (hard in
  Dafny) PLUS a "reset holds at each LK node" fact (the look's OWN body groups are ABSENT in
  gm at its LK node — first-encounter never set them; a re-run's quant `GMReset(DefGroups(r1))`
  cleared them; `DomLkDisjoint` is NOT globally carriable but holds AT LK nodes). `inpn` is what
  the §2 exact-position half matches to `a_cp[l]`.
- **Else-branch rewrite of `MainTheorem`** (`{:isolate_assertions}`, ~15-20 min verify):
  replace the `S == {}` block (~2631) + the L1 `FBuildCaptureUnfold` (`:4513`) call with
  `res := FLookLoop(...)`; `FBuildCaptureUnfoldL3a`; the value bridge (outside-`S`
  `OutsideLookValueBridge` + inside-`S` (E)+(S-ii)+keystone+§2); `ReplayThreadWfLA`/
  `FreshMatchWf` for the synthetic thread's `ThreadRegsWf`+`QuantRegsFinal`; feed a SYNTHETIC
  thread carrying `res.0/res.1/res.2` into the EXISTING `MainExtraction` (its precond is
  `leaf.1 == GmOfLive(re, thread.caps, ...)`). Then delete `LkBodyGroupsEmpty`/`FilterUnmoved`/
  L1 `LookRowsFromTables`.
- **Flip is already done** at the predicate level (`LookBehindFragmentRE`/`Raw` widened,
  `Supported` flipped); once `MainTheorem` is green the whole package verifies and
  `Supported`/`MatchCorrect` cover capturing lookaheads.

---

## 4. Suggested order

1. §2 gate — the position/structure correspondence (the research core; its own session).
2. (S-ii) extraction layer (§3) — uses the gate's `inpn`↔`a_cp[l]`.
3. Else-branch rewrite + delete dead lemmas + whole-package verify.

The memory file `l3-captures-in-lookarounds.md` has the running log with more detail on every
lemma above and the soundness argument (the `GMReset` = JS capture-clear insight that makes
the fresh-based engine reference match the gm-threaded spec).
