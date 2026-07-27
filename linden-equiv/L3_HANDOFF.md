# L3 Handoff — captures inside positive lookarounds

Status as of 2026-07-27. Everything below is **committed on `main`**.
Companion memory: `l3-captures-in-lookarounds` (has the same anchors at finer grain).

---

## 0. The milestone ladder

| Level | Scope | State |
|-------|-------|-------|
| L1 | capture-free, non-nested **lookbehinds** | ✅ done |
| L2 | capture-free, non-nested **lookaheads**, full plus-fragment bodies | ✅ done (star restriction lifted this session) |
| **L3** | **capture groups INSIDE positive lookaround bodies** | 🔨 in progress (this doc) |
| L4 | nesting (lookarounds inside lookarounds) | groundwork only |

`ApiMatch.Supported` currently gates on `NR.LookBehindFragmentRaw` (a misnomer —
it admits BOTH flavours; rename pending). L3 bodies are still required
capture-free. L3 removes that.

### Commits this session (all on `main`)
```
387600b  L2: lift the star-shape restriction on lookahead bodies
9cf0d47  L3-0: widen SpanDuality span duality to GroupOkL (capturing bodies)
7d1659d  L3a: the capture-bank frame + classification pair
5261ef7  L3a: whole-bytecode lift + capture in/outside-looks disjointness
d9feca7  L3a: the FFindMatch-level replay capture frame
6380c24  Propagate L3-0 to linden-equiv: OracleColumnSpec gets GroupFreeIsGroupOk
4d92f6e  L3a: the full FFindMatchPlus replay capture frame
```

---

## 1. The big picture (read this first)

**The executable engine needs ZERO changes.** `capture_regex(Lookahead) == body`
(Compiler.dfy:268), replayed by `FLookLoop` (Interpreter.dfy:560) via
`FFindMatchPlus`, already KEEPS the replay's capture registers. L3 is 100% a
proof effort: reframe the equivalence proof's "the capture pass is the identity"
argument into "it writes exactly the body's group ids, matching the tree's
`LkResult` gm".

**The tree spec is already correct.** `LkResult(lk, t, gm, inp)` (Semantics.dfy:92)
for a positive lookaround returns `Some(pair.1)` = the body's best-leaf group map,
and the `IsTree` LK rule (Semantics.dfy:272) threads that as the continuation's
starting gm. `TreeResSomeGmIndep`/`SuccActsGmIndep` (SpanDuality) already prove the
threaded map can't change match SUCCESS.

**Two proofs break, and only two:**

1. **`PIV.GmOfLiveLookIndep` (PikeInvRE:~3290) / `FilterCaptureLookIndep` (~3256)
   are literally FALSE for capturing bodies.** Today `GmOfLive` IGNORES the look
   register bank; that holds only because, for a capture-free body,
   `filter_capture`'s three lookaround branches (Interpreter.dfy:1015-1019 —
   matched→`filter_capture(r1,-1)` KEEP, unmatched/stale→`filter_all(r1)` RESET)
   all collapse to the identity. With captures they DIVERGE, so the look clock
   genuinely gates the body's captures. **This is the research-risk piece** (§4c):
   the `CheckOracle` `look_regs` write goes from invisible to load-bearing.

2. **`MainTheorem.FLookLoopFilterFrame` (~1381) proves the FLookLoop pass is
   filter-IDENTITY** — which for capturing bodies is genuinely false (the body's
   groups DO change). Needs the reconstruction (§4b).

**The oracle BIT is unaffected** by captures: `oracle_regex` uses
`remove_capture(body)` (group-free), so the existing chain characterizes it.
Captures don't change match existence. L3's spec work is the CAPTURE
reconstruction, not the bit.

---

## 2. L3-0 (DONE): SpanDuality widened to `GroupOkL`

`linden-reasoning/src/Equiv/SpanDuality.dfy`, whole file 122 verified. The
`Bwd*`/`Fwd*` span duality now admits capture groups (`GroupOkL`). Recipe:

- `requires NoBackrefActs(cont)` threaded through `BwdComplete`/`Quant`/`Free`/
  `BwdSound`/`Quant` (top-level `cont==[]` vacuous; recursion preserves via
  `NoBackrefActsCons`; `GroupOkIsNoBackref` bridges body → NoBackrefL).
- **Group case:** `ComputeTr([Areg(Group(gid,r1))]+cont) == GroupActionT(Open(gid),
  ComputeTr([Areg(r1),Aclose(gid)]+cont, GMOpen(...)))` (FunctionalSemantics.dfy:145).
  Recurse on `[Aclose(gid)]+cont` under `gmO`; `Aclose` resumes cont under
  `GMClose(...)`, shifted back to `gm` by `SuccActsGmIndep`. `MatchesL(Group)==MatchesL(r1)`.
- **Quantifier (the crux):** each iteration resets `DefGroups(r1)`, so the iterate
  subtree is built under `gm' = GMReset(gidl, gm)` (FunctionalSemantics.dfy:134,141).
  Recurse under `gm'`, convert cont's success `gm<->gm'` via `SuccActsGmIndep`, and
  the `GroupActionT(Reset(gidl))` node threads the map back
  (`TreeRes(GroupActionT(Reset),gm) == TreeRes(t, GMReset(gidl,gm))`). Dropped the
  `GroupFreeDefGroups`/`GMResetNil`/`GMUpdateResetNil` no-op collapse.
- **Fwd\*** trivial: `SuccReverse`/`SuccActsReverse` were already `GroupOkActs`;
  swapped the gate and `RevLGroupFree`→`RevLGroupOk`.

**Propagation to linden-equiv done (commit 6380c24):** `linden-reasoning` repacked
to 1.0.1 (`cd linden-reasoning && lem pack`, 328 verified), its `.doo` hand-copied
into `linden-equiv/deps/`; `OracleColumnSpec` (lookbehind) got the missing
`SD.GroupFreeIsGroupOk(T.Translate(body))` (OracleColumnSpecLookahead already had it).
See §5 for the `.doo` durability caveat.

---

## 3. L3a (IN PROGRESS): the engine capture pass

Sub-structure of the whole L3a proof:

```
fragment change (drop CaptureFreeRE(body) for lookaheads)
  |
  +-- FRAME direction: FLookLoop writes only the body groups (outer groups unchanged)
  |     [capture-bank frame + classification]  ✅ DONE
  |     [ReplayCaptureFrame / ReplayPlusCaptureFrame per-replay]  ✅ DONE
  |     [FLookLoopCaptureFrame loop induction]  <-- NEXT (§4a)
  |
  +-- RECONSTRUCTION: the written VALUES == tree LkResult gm  <-- §4b (deep)
  |
  +-- GmOfLive reframe: replace the false GmOfLiveLookIndep  <-- §4c (research)
        then reframe FBuildCaptureUnfold/FilterUnmoved from identity to tracking
        then flip the fragment + Supported
```

### 3.1 What's proved (all first-try)

**Capture-bank frame** (`ClockMono.dfy`) — a faithful clone of the quant-write frame,
with `SetRegisterToCP` the write case:
- `CaptureWritesInside(c, S)`, `VmCapturesAgree(s, cap0, S)`
- `FAdvanceEpsilonCapWriteFrame` / `FConsumeCapWriteFrame` / `FFindMatchCapWriteFrame`
  (a whole search agrees with its start bank outside `S`)
- `CaptureBytecodeClassified(body)`: `CaptureWritesInside(compile_to_bytecode(body),
  CaptureRegs(body))` (the shape FLookLoop replays for a lookahead).

**Classification + disjointness** (`PikeInvRE.dfy`):
- `CaptureRegs(re)` (the group start/end register ids of `re`), `CaptureRegsMono`
- `CaptureWriteIdsRE` / `Min` / `Opt` (every `SetRegisterToCP` in a compiled block
  targets `CaptureRegs(re)`; mirror of `QuantWriteIdsRE`, `Re_capture` is the write case)
- `CapIdsOutsideLooks` / `CapIdsInLooks` / `CapIdsSplit` / `CapIdsLooksDisjoint`
  (a look body's own groups are disjoint from the outer groups the main filter reads,
  under `CapUnique`) + `CaptureRegsDisjoint` (id-disjoint ⇒ register-disjoint, parity arg).

**Per-replay frame** (`MainTheorem.dfy`):
- `ReplayCaptureFrame`: the FFindMatch part of a lookahead replay changes captures
  only within `CaptureRegs(body)`.
- `NoTrueQuantStamp(body)`: `compile_to_bytecode(body)` has no `SetQuantToClock(_,true)`
  (lifts `NI.CodeShapeAt`'s `!bb`; capture-independent).
- **`ReplayPlusCaptureFrame`**: the WHOLE `FFindMatchPlus` changes captures only within
  `CaptureRegs(body)`.

### 3.2 The two findings that killed the feared deep work

The `FReconstructPlus` half of the replay looked like it needed an `FNullInterp`
frame + a `ReconstructNulled`-mode classification. Both are UNNEEDED:

1. **`FNulledPlusIdentity` (MainTheorem:319) is CAPTURE-AGNOSTIC.** It requires only
   `forall k :: qt.a_cp[k] < 0` (= `QuantRegsFinal`'s first conjunct), no
   capture-freeness, and its proof is purely structural. When the replay is
   `QuantRegsFinal`, every `Re_quant` takes the `get_cp==None` branch, so `plus_bc`
   NEVER runs → `FReconstructPlus` is the identity even with captures.
2. **`NI.CodeShapeAt` (NestInv.dfy:2100) already handles capturing bodies** — it
   requires `CapUnique`+`QuantUnique` (NOT `CaptureFree`) and ensures BOTH the
   `SetRegisterToCP`→`CapIds` classification AND `!bb` on every `SetQuantToClock`.

So `ReplayPlusCaptureFrame = ReplayCaptureFrame + NoTrueQuantStamp +
FFindMatchQuantFinalAny (⇒ QuantRegsFinal) + FNulledPlusIdentity (⇒ identity)`.

---

## 4. The remaining work (in order)

### 4a. FLookLoop capture induction — NEXT, tractable

Add `FLookLoopCaptureFrame` in `MainTheorem.dfy`, mirroring `FLookLoopFilterFrame`
(:1381) structurally but carrying a capture frame instead of `FilterUnmoved`'s
identity:

- Fix `S = CaptureRegsSet(CapIdsInLooks(mainast))` (define a set-of-ids → register
  set; note `CaptureRegs(re) == CaptureRegsSet(CapIds(re))`). Ensure
  `RegsAgreeOutside(FLookLoop(...).0, cap, S)`.
- Per matched positive lookahead lid: `ReplayPlusCaptureFrame` gives the replay's
  cap agrees with the pre-replay cap outside `CaptureRegs(body_lid)`; that is `⊆ S`
  because `CapIds(body_lid) ⊆ CapIdsInLooks(mainast)` (needs a small lemma, the
  capture analogue of the quant precondition `q in QuantIds(body) ⇒ q in
  QuantIdsInLooks(mainast)` that `FLookLoopFilterFrame` already carries — establish
  it from `LookEntryOk` + the fragment). Compose `RegsAgreeOutside` across iterations.
- The negative / non-capture / unmatched branches leave cap unchanged (trivially
  agree). The lookbehind branch is out of scope for L3a (lookahead-first).

Then the outer filter reads only `CapIdsOutsideLooks` registers (disjoint from `S`
by `CaptureRegsDisjoint` + `CapIdsLooksDisjoint`), so the OUTER groups' filter output
is preserved. The INNER groups (in `S`) now carry the reconstructed values — which is
the point, and their correctness is §4b.

### 4b. The reconstruction theorem — deep

The replay's WRITTEN VALUES on `CaptureRegs(body)` must equal the tree's
`LkResult(lk, tlk, gm, inp).value` on those ids. `FLookLoop` replays
`capture_regex(Lookahead)==body` FORWARD via `FFindMatchPlus` from the recorded cp —
the SAME engine the main match uses — so this is "apply `MainExtraction`/`PikeSim` to
the body as a standalone sub-match". The spec half consumes L3-0's `GroupOkL` span
duality (now available in linden-equiv). Likely the single deepest new object.

### 4c. The GmOfLive reframe — research risk

`PIV.GmOfLiveLookIndep`/`FilterCaptureLookIndep` are false; replace "look bank
invisible" with "the `CheckOracle` `look_regs` write records EXACTLY the cp the
spec's `LkResult` reads", reproving `ThreadTracksGm` with a look-bank-dependent
denotation. Then reframe `FBuildCaptureUnfold` (MainTheorem:1605) /
`FLookLoopFilterFrame` / `FilterUnmoved` from identity to tracking, widen the
fragment (drop `CaptureFreeRE(body)` for lookarounds), and flip `Supported`.

---

## 5. Sharp edges / gotchas

- **The `.doo` propagation is LOCAL and non-durable.** `lem pack` in a member
  produces `member-x.y.z.doo` at the package root but does NOT reach the resolver
  store, so `lem lock` in a consumer keeps the old version. Working flow (no publish):
  `cd linden-reasoning && lem pack`, then `cp linden-reasoning/linden-reasoning-1.0.1.doo
  linden-equiv/deps/linden-reasoning.doo`, then per-file verify. `deps/` is
  git-untracked (regenerated from the lock), so the hand-copy is a LOCAL working
  artifact; a `lem restore`/`ci` REVERTS it. Fully durable propagation needs
  `lem publish` of 1.0.1 (an upload). `lem pack` treats WARNINGS as fatal (missing
  `{:trigger}`, exists-indentation) — per-file `dafny verify` does NOT surface these.
- **`MainTheorem` is fragile** — requires `{:isolate_assertions}` (~10min). Adding a
  widely-unfolded predicate case or changing a shared predicate can push a marginal VC
  over 900s. This session, simplifying `LookBehindFragmentRE` sent `CompileNfaRepRE`'s
  `NfaRepRE`-fold batches into a matching loop (242M rlimit). **Recipe:**
  `assert <goal> by { hide *; reveal <fn>; <restate the exact facts already proven above>; }`
  collapses the axiom space. See `dafny-timeout-is-not-always-cost` memory.
- **Verify-benching:** never overlap Z3-heavy runs when timing matters — and that
  includes intra-run batch contention on big files. Use `--cores 2` for truer timings.
  Per-file verify has a ~12s floor (load the 6 `.doo` libraries).
- **`lem test` can't see locally-packed `.doo`** — runtime Go smoke on `(?=(a))b` is
  deferred until that's fixed; treat "proved + package verify green" as the end state.

---

## 6. Verify recipe

Toolchain: **Dafny 4.11.0** at
`C:\Users\Aaron-pc\AppData\Local\lemmata\toolchains\4.11.0\dafny\Dafny.exe`
(the PATH `dafny` is 4.10 and CANNOT load the 4.11 `.doo`s).

Single-file / single-symbol (fast iteration), run from the package dir:
```
Dafny.exe verify src/Equiv/<File>.dfy \
  --standard-libraries \
  --library deps/linden-engine-model.doo --library deps/linden-engine.doo \
  --library deps/linden-reasoning.doo --library deps/linden-semantics-core.doo \
  --library deps/linden-warblre.doo --library deps/regex-engine.doo \
  --cores 2 --verification-time-limit 250 --filter-symbol <Lemma>
```
(linden-reasoning uses only its 3 deps: semantics-core, warblre, regex-engine.)

Long runs: detach to a log + poll, don't block on the 10-min tool cap.

Standing merge-time TODO: a full-package re-verify (all L2/L3a additions are
self-contained, but belt-and-suspenders), and remember `deps/linden-reasoning.doo`
in linden-equiv is the hand-copied 1.0.1 (§5).
