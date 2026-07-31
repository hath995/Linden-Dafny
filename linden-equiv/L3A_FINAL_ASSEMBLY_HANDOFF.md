# L3a Final Assembly — Handoff

**Goal:** finish proving `MainTheorem` (and thus flip `Supported`) for **capturing
positive lookaheads** — `(?=(a))`, `(?=(a))*`, etc. — so the engine's answer is
shown to equal the ECMAScript tree semantics' first-leaf capture array, *including
the reconstructed lookahead group captures*.

**Branches:**
- `l3a-widen-fragment` — `FirstLeafClosed` invariant swap, group-id uniqueness
  discharge, fragment predicate flip. All committed, individually verified.
- `l3a-value-assembly` (off `l3a-widen-fragment`, tip `f0d68c4`) — the value
  assembly. 5 new lemmas, all individually verified. **This is the working branch.**

**Dafny:** 4.11.0 at `C:\Users\Aaron-pc\Downloads\dafny-4.11.0-x64-windows-2022\dafny\Dafny.exe`
(the `/c/Program Files/dafny` one is 4.10 and CANNOT load the 4.11 `.doo` deps).

**Per-symbol verify command** (fast iteration; whole-file is ~15-20 min):
```
"$DAFNY" verify src/Equiv/MainTheorem.dfy --standard-libraries \
  --library=deps/linden-engine-model.doo --library=deps/linden-engine.doo \
  --library=deps/linden-reasoning.doo --library=deps/linden-semantics-core.doo \
  --library=deps/linden-warblre.doo --library=deps/regex-engine.doo \
  --verification-time-limit=900 --filter-symbol=<Name>
```
Note `--filter-symbol` matches by substring and surfaces ALL resolution-time
warnings in the file, so it doubles as a warning check. The package manifest sets
`allow-warnings = false`, so trigger warnings (from `set g | g in <seq>`) FAIL the
build — use index-triggered quantifiers, or dedicated `NoDupPrepend`/`NoDupFromDisjoint`
style helpers (see `4ce2bde`).

---

## 0. Current package state (IMPORTANT)

Whole-file `MainTheorem` verify = **2384 verified, 7 errors**. The 7 errors are
PRE-EXISTING (they predate this session's work) and localize to exactly two
lemmas that the *already-widened RE-level fragment* made false:

- `LkBodyGroupsEmpty` (`MainTheorem.dfy` ~2660) — asserts `LkBodyGroups(Translate(re)) == {}`
  for any `LookBehindFragmentRE(re)`. FALSE once lookaheads may capture. Called at the
  `S := LkBodyGroups(...)` / `assert S == {}` shortcut inside `MainTheorem` (~2050).
- `FilterUnmoved` (~3420) — the L1 "the replay can't move the answer" lemma; only true
  for capture-free bodies.

`MainTheorem`'s body "verifies" only because Dafny TRUSTS `LkBodyGroupsEmpty`'s
(now-false) `ensures S == {}`. **These two lemmas become DEAD once the else-branch
is rewritten to the L3a path — delete them (or scope their `requires` to capture-free
lookaheads).** Do not try to "fix" them; they are the `S == {}` shortcut that the
whole assembly replaces.

The task list's markings of §4b / value-lift / "final assembly" as *complete* were
**inaccurate** — those are built *machinery*, never wired into `MainTheorem`.

---

## 1. The final goal, decomposed

`MainTheorem`'s `else` branch (result `Some(thread)`) must establish, for the
overall regex `re = lazy_prefix(annotate(raw))`, spec tree `t`, and winning
thread's registers:

```
FirstLeaf(t).value.1  ==  GmOfLive(re, res.0, res.1, res.2)
```
where `res = AI.FLookLoop(crv, str, 1, maxlook, thread.capture_regs, thread.look_regs,
thread.quant_regs, ov1)` is the capture-reconstruction pass' output.

Then feed a **synthetic thread** carrying `res` caps into the EXISTING `MainExtraction`
(whose precondition is `leaf.1 == GmOfLive(re, thread.caps, ...)` and whose body is
otherwise unchanged — it already calls the fixed `FirstLeafClosed`). And use
`FBuildCaptureUnfoldL3a` (already built, `MainTheorem.dfy` ~3580) to get
`FFullMatch == filter_reset(ast, res.0, res.1, res.2, -1)`.

Prove the map equality **by group `g`**, split on inside/outside look:

### Outside-look groups (`g !in CapIdsInLooks(re)`) — DONE
`OutsideLookValueBridge` (committed `f0d68c4`) proves it, from:
- `ft` agrees `gmBest = GmOfLive(re, thread.caps, look, thread.qt)` outside the tree
  set `S = LkBodyGroups(Translate(re))` — this is `FirstLeafAgreeOutside(tstar, t, S)`
  composed with `BestMatchRE` (`FirstLeaf(tstar).1 == GmOfLive(re, thread.caps,...)`).
- `res.0`/`res.2` agree `thread.caps`/`thread.qt` OUTSIDE the inside-look
  registers/quants — `FLookLoopCaptureFrame` (`res.0 ~ cap` outside `S_reg`, `res.1 == lk`)
  and `FLookLoopQuantFrame` (`res.2 ~ qt` outside `QuantIdsInLooks`).
- The set identity `LkBodyGroups(Translate(re)) == CapIdsInLooks(re)`
  (`LkBodyGroupsEqCapIdsInLooks`, committed `ac572e1`).
- `PIV.GmOfLiveFrameOutside` (`GmOfLive(res.0) ~ GmOfLive(thread.caps)` outside `CapIdsInLooks`).

### Inside-look groups (`g in CapIdsInLooks(re)`) — THE REMAINING WORK
Two sub-pieces, (E) engine value + (S) spec value; both reduce to the per-lid body
first-leaf, and the ONLY hard blocker is the **position correspondence** in (S).

---

## 2. Inside-look bridge, in full

For an inside-look group `g` owned by lookahead lid `l` (body `= VBody(crv, l)`,
flavour `la`), want `FirstLeaf(t).1[g] == GmOfLive(re, res.0, res.1, res.2)[g]`.

### (E) Engine value — `GmOfLive(re, res.0)[g] == body first-leaf value`
Route A (via raw-range reader):
- `PIV.GmOfLiveKeepsPresentLk(re, res.0, look, res.2, g)` gives
  `GmOfLive(re, res.0)[g] == LiveRange(res.0.a_cp, res.0.a_clk, g)` — reads `res.0`'s
  raw range. **Requires** `PathPresentLk(re, cc, lc, qc, -1, g)` + clock/value set +
  `MxAtGidLk` bound. **New chain needed:** establish `PathPresentLk` for `res.0`'s
  reconstructed inside-look group from FLookLoop's write clocks. (Look at how the
  reconstruction sets `res.0`'s start/end clocks; the reset-mx bound should hold
  because the look's clock dominates the body's writes.)
Route B (via lookaround transparency):
- `PIV.FilterAtLookaroundMatched(lid, la, r1, cr, cc, lc, qc, M)` — for a MATCHED look
  (`lc[lid] >= 0 && >= M`), `filter_capture(Re_lookaround(...)) == filter_capture(r1, ...)`.
  Reduces `GmOfLive(re, res.0)[g]` (walking `re` to the lookaround) to the body's own
  `filter_capture(body, res.0)[g]`. Needs a structural walk of `re` to reach `g`'s
  lookaround (like the `FilterCaptureOutside`/`FilterCaptureFrameAt` family).
- Then `res.0` on `CaptureRegs(body)` `== FreshBodyMatch(crv, str, l, ...)` caps
  (`FLookLoopValueOk`, the ensures of `FLookLoopValueLift`), so
  `filter_capture(body, res.0)[g] == GmOfLive(body, FreshBodyMatch)[g]`.

Either route ends at: `GmOfLive(re, res.0)[g] == GmOfLive(body, FreshBodyMatch(l))[g]`.
`FreshBodyMatch` is `FFindMatch(compile_to_bytecode(body), from FRESH regs at cp =
look_regs.a_cp[l], ov, Forward)`.

### (S) Spec value + THE POSITION CORRESPONDENCE (the one hard blocker)
Want `FirstLeaf(t).1[g] == GmOfLive(body, FreshBodyMatch(l))[g]`.

Compose:
1. **Keystone `LkReplayMatchesSpec`** (`MainTheorem.dfy` ~3360, ALREADY PROVEN) — given
   `cp`, `gmMain`, `tlk == ComputeTr(Translate(body), InpOfCp(str,cp), gmMain, Forward)`,
   and `GmAgreeOn(gmMain, Empty, DefGroups(Translate(body)))` — gives:
   `GmAgreeOn(LkResult(TrLookaround(la), tlk, gmMain, InpOfCp(str,cp)).value,
             GmOfLive(body, FreshBodyMatch(l)), DefGroups(Translate(body)))`.
   **Use `gmMain = Empty`** (so `GmAgreeOn(Empty,Empty,S)` is trivial): then
   `tlk = ComputeTr(Translate(body), InpOfCp(str,cp), Empty, Forward)` and the keystone
   ties `GmOfLive(body, FreshBodyMatch(l))` to `LkResult(..., Empty, InpOfCp(str,cp))`.
2. **Spec tree threading** — `FirstLeaf(t).1[g] == LkResult(la_g, tlk_g, gmMain_g,
   inp_g).value[g]` where `(tlk_g, gmMain_g, inp_g)` is the actual context of lid `l`'s
   LK node on `t`'s priority-first path. `TreeRes`'s LK rule
   (`TreeRes(LK(lk,tlk,t1),gm,inp,dir)` positive = `TreeRes(t1, LkResult-gm, inp, dir)`)
   threads the body's leaf gm into the continuation; `g` (confined to the body) survives
   to the leaf unchanged (outer actions never touch `g`, by `OuterLkDisjoint` /
   uniqueness). This threading is provable by a **value-carrying analogue of
   `FirstLeafClosed`** (same least-lemma frame, carry the per-look value not closedness).
3. **THE BLOCKER — position + reset match:** to collapse step-2's
   `LkResult(..., gmMain_g, inp_g)` onto step-1's `LkResult(..., Empty, InpOfCp(str,cp))`
   need:
   - **(S-i) POSITION:** `inp_g == InpOfCp(str, cp)`, i.e. the engine's recorded
     `look_regs.a_cp[l]` == the input position of lid `l`'s LK node on `t`'s first-leaf
     path. **This is the research core; see §3.**
   - **(S-ii) RESET:** `GmAgreeOn(gmMain_g, Empty, DefGroups(Translate(body)))`, i.e. the
     body's own groups are UNSET in `gmMain_g`. TRUE because the JS `RepeatMatcher`
     reset (`GMReset(DefGroups(r1))` in the quantifier's iteration — see `FirstLeafClosed`'s
     Quant cases: `gm2 = GMReset(gidl, gm) = gm - gidl`, which REMOVES the body groups)
     clears them each iteration, and a first-encounter look never set them. Provable as a
     tree-traversal invariant (`DomLkDisjoint` holds AT LK nodes though not globally — see
     §4). Given (S-ii), `ComputeTrGmIndepLk` (`EL`, look-free body ⇒ tree gm-independent) +
     `TreeResGmFrame` (`MainTheorem` ~3320, look-free tree ⇒ `S`-agreeing gms give
     `S`-agreeing leaves) collapse `gmMain_g -> Empty` on the body's groups.

Given (S-i)+(S-ii): `FirstLeaf(t).1[g] == LkResult(..., Empty, InpOfCp(str,cp)).value[g]
== GmOfLive(body, FreshBodyMatch(l))[g] == GmOfLive(re, res.0)[g]`. Done.

---

## 3. (S-i) The position correspondence — the research core

**Exact mechanism (pinned):** in `FAdvanceEpsilon`'s `CheckOracle(l)` case
(regex-engine.doo), a thread that passes lid `l`'s gate does
```
look_regs := R.set_reg(t.look_regs, l, Some(s1.cp), s1.clock)
```
So `look_regs.a_cp[l]` == the thread's `cp` at gate-pass == operationally the lookahead's
match position. On the WINNING thread (`result`, `== FirstLeaf(tstar)`'s thread), that cp
is the position where lid `l`'s gate sits on `tstar`'s priority-first path.

**Why it's not already available:** the PikeSim invariant `ThreadTracksGm(re, th, gm) ==
(gm == GmOfLive(re, th.caps, th.look_regs, th.quant_regs))` (`PikeInvRE.dfy:5468`, used by
`ActiveRepRE`/`BlockedRepRE`/`BestMatchRE`) tracks only `GmOfLive`, which consults look
CLOCKS (`a_clk`) for the match boolean, NEVER look POSITIONS (`a_cp`). So `look_regs.a_cp[l]`
is operationally correct but formally UNCONSTRAINED by any existing invariant. A grep of
`PikeInvRE`/`PikeSimRE` for a `look_regs`↔tree-position lemma finds nothing (only
`PathPresentLk`, which is about capture presence given the banks — no position link).

**What to build:** a look-position-tracking invariant threaded through the simulation,
parallel to `ThreadTracksGm`. Concretely something like:
```
LookPosTracksTree(rer, qm, code, inp, th, tree):
   forall l :: th.look_regs.a_cp[l].Some? ==>
     <the LK-l node on `tree`'s pc-path is at input position th.look_regs.a_cp[l]>
```
and prove it holds through `InitialPikeInvFullRE` (base: fresh regs, all `a_cp` unset →
vacuous) + `FindMatchSimRE` (`PSM`, the position loop) + the step lemmas
`FAdvanceEpsilon`/`FConsume` (the `CheckOracle` case is where `a_cp[l]` is written to the
current cp, which equals the LK node's position because `TreeThreadRE` places the thread's
pc at that LK node at that input position). Then, from `BestMatchRE`, transport it to the
winning thread and `bestT = FirstLeaf(tstar)`, and via the `tstar`↔`t` position agreement
(`LeavesAgreeAtOutside` gives leaf-position agreement; LK-node positions are outside-`S`
data determined by the pre-look path, so they agree) get `inp_g == InpOfCp(str, look_regs.a_cp[l])`.

**Scale/risk:** this is a MAJOR, non-incremental build — comparable to `ThreadTracksGm`
itself. Modifying/strengthening the load-bearing `FindMatchSimRE`/`InitialPikeInvFullRE`
re-verifies huge lemmas (10-20 min each) and can break the existing green PikeSim proofs.
**Do it as a PARALLEL tracking invariant proven alongside (not by mutating) the existing
one where possible**, and in one coherent stroke — not chipped at. This is THE piece to
schedule as a dedicated focused effort.

---

## 4. (S-ii) The reset invariant / value least-lemma

Build a value-carrying analogue of `FirstLeafClosed` (which lives at `MainTheorem.dfy`
~1055, a `least lemma` over `acts`). `FirstLeafClosed` proves `ClosedGm(leaf.1)` carrying
invariants `LkClosedInGm(gm, acts)` (pending inside-look groups, if present, are CLOSED) +
`OuterLkDisjoint(acts)` (outer-defined groups disjoint from inside-look groups). Clone its
frame; instead of closedness, carry the per-look VALUE.

Key facts already proven and reusable:
- `LookBodyLeafValue` (committed `750ccc0`): when body groups are UNSET in `gm`
  (`GmAgreeOn(gm, Empty, S)`), the body leaf from `gm` agrees on `S = DefGroups(r1)` with
  the body leaf from `Empty`. (Trivial `TreeLeavesFrameInside`.)
- `LookBodyLeafOpenSub` (~1035): the closedness LK-case payoff, uses `gmR = map g | g in gm
  && g in S :: gm[g]` (gm's closed `S`-groups). For the VALUE case you want the STRONGER
  hypothesis that gm's `S`-groups are ABSENT (not just closed) — establishable at the LK
  node from the reset. Do NOT add that hypothesis to `LookBodyLeafOpenSub` (it would break
  `FirstLeafClosed`'s use); use `LookBodyLeafValue` (separate).

**Invariant subtlety (documented, resolved):** `DomLkDisjoint(gm, acts)` (`dom(gm) ∩
LkBodyGroupsActs(acts) == {}`, i.e. NO pending inside-look group is set in gm) is NOT
globally maintainable: after a look inside a quantifier runs, `sub[0].1` has the look's
groups CLOSED and the continuation still contains the quantifier (which re-includes the
look), so `DomLkDisjoint` fails in the window [after look-exit, before next reset]. BUT
there are NO LK nodes in that window, and the quantifier's `GMReset(DefGroups)` restores
absence before the next LK node. So `DomLkDisjoint` holds AT EVERY LK NODE, which is all
(S-ii) needs. Carry `LkClosedInGm`+`OuterLkDisjoint` as in `FirstLeafClosed` and derive
`GmAgreeOn(gm, Empty, DefGroups(r1))` locally at each LK node from the just-applied reset
(the Quant cases of `FirstLeafClosed` already thread `GMReset(gidl, gm) = gm - gidl` before
reaching the body — the body's groups are removed at that point).

---

## 5. Also still to build

- **`LookRowsFromTablesL3a`** — capturing variant of `LookRowsFromTables` (~3455). The L1
  version's `ensures` has `NR.CaptureFreeRE(body)` for EVERY matched lid; the L3a value-lift
  (`FLookLoopValueLift`, `FLookLoopCaptureFrame`) instead need, per matched lid: `LookEntryOk`,
  `LookFreeRE(body)`, `PlusFragmentRE(body)`, `CapUnique(body)`, `QuantUnique(body)`,
  `CaptureRegs(body) <= S_reg`, pairwise-DISJOINT `CaptureRegs` across distinct lids,
  `cp_ctx_ok(crv, str, lk, l)`, `(la.Lookbehind? || la.NegLookbehind? || la.NegLookahead?)
  ==> CaptureFreeRE(body)`, and capturing⇒`la.Lookahead?`. Derive the extra facts from the
  look tables (`LTB.*`, `OE.LmOfInv`) + `CapUnique(re)` (pairwise disjoint from unique cap ids
  ⇒ disjoint `CaptureRegs` via `PIV.CaptureRegsDisjoint`). Mechanical but a real chunk.
- **Else-branch rewrite** of `MainTheorem` (`{:isolate_assertions}`, ~15-20 min verify):
  replace the `S == {}` block (~2050) and the L1 `FBuildCaptureUnfold` (~2170) with:
  `res := FLookLoop(...)`; `FBuildCaptureUnfoldL3a`; the value bridge (outside-S
  `OutsideLookValueBridge` + inside-S §2); `ReplayThreadWfLA`/`FreshMatchWf` for the
  synthetic thread's `ThreadRegsWf`+`QuantRegsFinal`; `MainExtraction(raw, str, t,
  synthetic-thread, leaf)`. Then delete `LkBodyGroupsEmpty`/`FilterUnmoved`.
- **Flip is already done** at the predicate level (`c76508b`); once `MainTheorem` is green
  the whole package verifies and `Supported`/`MatchCorrect` cover capturing lookaheads.

---

## 6. Suggested order

1. `LookRowsFromTablesL3a` (self-contained, verifiable now).
2. (E) engine value — pick Route A or B, build `PathPresentLk`-for-reconstruction or the
   `filter_capture` reduction. Verifiable now (no positions).
3. (S-ii) the value least-lemma / reset invariant. Verifiable now (pure spec-side).
4. (S-i) the position-correspondence invariant — the big dedicated build (§3).
5. Compose (E)+(S) into the inside-look bridge; wire the else-branch; delete dead lemmas;
   whole-package verify.

Steps 1-3 are real verified increments that shrink what step 4 must carry. Step 4 is the
one research-grade piece and should be its own focused session.

---

## 7. Inventory of what's already built & verified (don't rebuild)

On `l3a-value-assembly` / `l3a-widen-fragment` (all green in isolation):
- `FirstLeafClosed` (`least lemma`) + `FirstLeafClosedNoLk` — closedness of the priority
  leaf, with the `LkClosedInGm`+`OuterLkDisjoint` invariants that survive quantified
  capturing lookaheads. `QuantSubInv`/`QuantSubInvCheck`/`TailInv`/`SubInv` thread them.
- `TA_NoDup`/`NoDupPrepend`/`NoDupFromDisjoint`/`SpecRegexOuterLkDisjoint` — group-id
  uniqueness (annotate/`RD.TA` counter structure) ⇒ `OuterLkDisjoint([Areg(SpecRegex(raw))])`,
  wired into `MainExtraction`.
- `LookBodyLeafValue`, `TranslateDefGroupsEqCapIds`, `LkBodyGroupsEqCapIdsInLooks`,
  `OutsideLookValueBridge` — §1 outside-S + set correspondence.
- Machinery (built earlier this campaign, verified): `FLookLoopValueLift`→`FLookLoopValueOk`,
  `FLookLoopCaptureFrame`, `FLookLoopQuantFrame`, `ReplayCapIsBodyLeaf`, `LkReplayMatchesSpec`
  (keystone), `TreeResGmFrame`, `TreeLeavesFrameInside`, `FBuildCaptureUnfoldL3a`,
  `ReplayThreadWfLA`, `FreshMatchWf`, `FirstLeafAgreeOutside` (`LookLeaves`),
  `EL.ComputeTrGmIndepLk`/`ComputeTrNoLK`/`TranslateNoLkBr`, the `LeavesAgreeAtOutside(S)`
  checked-tree reframe (`ActionsTreeRepRE` with `S` param), `PIV.GmOfLiveFrameOutside`,
  `PIV.GmOfLiveKeepsPresentLk`, `PIV.FilterAtLookaroundMatched`, `PIV.GmOfLiveInsideLookAbsent`.

**The memory file `l3-captures-in-lookarounds.md` has the running log with more detail on
each of these and the soundness argument (the `GMReset` = JS capture-clear insight that
makes the fresh-based engine reference match the gm-threaded spec).**
