# §2.5 HANDOFF — nullable unbounded quantifiers (`(a?)+`, `{n,}` with a nullable body)

**Status (2026-08-30): SCOUTED, not started.** Predecessor rung: L5 + the `(?=x(?<=y)` widening,
COMPLETE and packaged on `main` (`da03fe0`) — `L5_HANDOFF.md`. Branch: work on `lem-split`.
Gate: `LEM_BUILD_TIMEOUT=0 lem pack --jobs 3` from the repo root.

---

## 1. THE HEADLINE — §2.5 IS TWO RUNGS, NOT ONE

`Compiler.dfy:104-156` gives an unbounded `min > 0` quantifier **four** different schemes, selected
by the annotator's nullability `nul` and `quant.greedy`:

| body nullability | greedy | scheme | proof status |
|---|---|---|---|
| `NonNullable` | either | **do-while** — `repeat_min(min-1)`, stamp, body, BACKWARD fork | ✅ in the fragment today |
| `CINullable` | greedy | end-fork + `SetQuantToClock(qid, true)` | ❌ §2.5b |
| `CDNullable` | greedy | end-fork + **`CheckNullable(qid)`** + `SetQuantToClock(qid, true)` | ❌ §2.5b |
| `CINullable`/`CDNullable` | **lazy** | the **GENERIC** scheme — `repeat_min(min)` then the ordinary star loop | ❌ **§2.5a — cheap** |

The fragment predicates (`PlusFragmentRE`/`Raw`, `NestedFragmentRE`/`Raw`, `NfaRepRE`'s `Re_quant`
arm, `AR.NfaRepL`'s `Inf` arm) all currently write the unbounded-`min>0` case as
`min > 0 && nul == NonNullable` + the do-while layout, which excludes rows 2–4 in one stroke.

### §2.5a — LAZY nullable `+`/`{n,}` (`(a?)+?`, `(a?){2,}?`) — the cheap half

**Nothing nullability-specific is involved.** The compiler's generic branch emits, at `nextl`:

```
repeat_min(min, qid, r1)                        -- min forced copies, each [SetQuantToClock(qid,false); body]
min_f:   Fork(min_f+1, iter_f+2)  (lazy: swapped)
min_f+1: SetQuantToClock(qid, false)
min_f+2: BeginLoop
         body                                   -- compile(r1, min_f+3) .. iter_f
iter_f:  EndLoop
iter_f+1: Jmp(min_f)
```

which is **exactly `NfaRepMinRE(min, …)` followed by the existing STAR arm shape at `em == min_f`**
(the star arm's `Jmp(pc1)` back-edge lands on its own fork; here `pc1 == min_f`).

The spec agrees definitionally: `ComputeIsTree.dfy:64-75` unfolds `Quantified(greedy, min, delta, r1)`
with `min > 0` as `[Areg(r1), Areg(Quantified(greedy, min-1, delta, r1))] + cont` under a
`GMReset(DefGroups(r1))` — **`min` forced copies with NO `Acheck`** — and then, at `min == 0` with
`delta == Inf`, as the star `[Areg(r1), Acheck(inp), Areg(Quantified(greedy,0,Inf,r1))] + cont`.
So `Quantified(g, min>0, Inf, r1)` = `min` copies then the star, on BOTH sides, with the engine's
`BeginLoop`/`EndLoop` pair sitting exactly where the spec's `Acheck` is.

**Why this needs no nullability hypothesis, unlike the do-while.** The do-while arm needs
`NUL.NonNullableL(r1)` for one reason only: at its `min == 1` SEAM
(`ActionsTreeRepRE.dfy:243-300`) the spec walk has *no* check after the last forced body while the
code's backward fork re-enters the loop, so the proof must MANUFACTURE one with
`CE.BoolCheckInsert`, whose `CE.ConsumesBeforeAreg(pre)` hypothesis is precisely non-nullability.
The generic scheme has the real `BeginLoop`/`EndLoop` check in the code, so there is no seam and no
insertion — the star arm applies verbatim.

**Work items (in order):**
1. `linden-equiv-nfa-rep-re/src/NfaRepRE.dfy`
   - `NfaRepRE`'s `Re_quant` else-branch (`NfaRepRE.dfy:1657-1667`): add the disjunct
     `nul != R.NonNullable && !q.greedy && q.min > 0 && ∃em :: NfaRepMinRE(min, qid, r1, c, pc1, em) && <star shape at em>`.
     Guard-disjoint from the do-while disjunct (`nul == R.NonNullable`), so existing inversions stay valid
     as long as their callers supply `nul == NonNullable || q.greedy`.
   - fragment predicates `PlusFragmentRE`/`PlusFragmentRaw`/`NestedFragmentRE`/`NestedFragmentRaw`
     (lines ~302-345, ~797-816, ~1267-1291): admit `min > 0 && max == None && !greedy` with
     nullability unconstrained.
   - `FreshCorrectRE` (and its nested twins) `Re_quant` arm (`NfaRepRE.dfy:1768-1806`): its `else`
     branch currently ASSUMES the do-while; add the generic dispatch.
   - the `CompileNfa*RE` layout lemmas (`NfaRepRE.dfy:2240-2300`): the matching arm.
2. `linden-equiv-actions-rep-re/src/ActionsRepRE.dfy`
   - `NfaRepL`'s `Inf` arm (`ActionsRepRE.dfy:251-262`): the same new disjunct, guarded
     `!NUL.NonNullableL(r1) && !greedy` (disjoint from the do-while's `NUL.NonNullableL(r1)` guard).
   - new `NfaRepLGenInv` / `NfaRepLGenIntro` twins of `NfaRepLPlusInv` / `NfaRepLPlusIntro`.
   - the `Translate` agreement at lines ~445-484 / ~845-884 (both copies).
3. `linden-equiv-actions-tree-rep-re/src/ActionsTreeRepRE.dfy`
   - a new extracted arm lemma beside the four existing ones (`…QuantArmMinPos`,
     `…QuantArmZeroNN`, `…QuantArmZeroInf`, and the `Nested` triple): the min>0 GENERIC case —
     forced copy recursion identical to the existing `min > 1` branch, but terminating at `min == 0`
     into the **star** arm instead of the do-while seam. Both the `FRE` and `FRENested` families.
4. `linden-equiv-main-theorem` / `linden-equiv/src/Equiv/ApiMatch.dfy`: widen the `+`/`{n,}` gate in
   `SupportedL3/L4/L5` once the layers below are green.

**Expected cost:** medium-small; every ingredient exists (`NfaRepMinRE`/`NfaRepMinL` from the bounded
case, the whole star arm from `*`). No new mathematics.

### §2.5b — GREEDY nullable `+`/`{n,}` (`(a?)+`) — the expensive half

Three things all break at once, which is why this is the real §2.5:

1. **`CheckNullable(qid)` has no representation.** `TreeRepRE.dfy:289` and `GenStepRE.dfy:103` map it
   to `false`, and the sweep predicates (`OS.NoCheckNullable`, and ~10 `!i.CheckNullable?` conjuncts
   in `NfaRepRE.dfy:2988-4157`) exclude it everywhere. It needs a tree-rep arm tied to the `cdns`
   table (`cdn_get(s.cdn, qid)` — `build_cdn_v` / `compile_cdns`), i.e. an engine↔spec correspondence
   for *context-dependent nullability at a position*, which does not exist yet in any form.
2. **`QuantRegsFinal` dies.** `MainTheorem.dfy:117-131` rests on "fragment code only ever emits
   `SetQuantToClock(q, false)`", hence every quant VALUE stays negative, hence
   `M.FNulledPlusIdentity` (`MainTheorem.dfy:323`) makes `AI.FNulledPlus`/`FReconstructPlus` the
   identity. The greedy-nullable schemes emit `SetQuantToClock(qid, true)`, which stamps a real cp.
   `FNulledPlusIdentity` has **~15 call sites** across `lift-sim-{core,carriers,deep,forward,main}`
   and `main-theorem`; each becomes a real reconstruction obligation.
3. **`FNulledPlus`'s spec correspondence is the actual new theorem.**
   `Interpreter.dfy:418-491` (`FNulledPlus`/`FNulledChildren`/`FReconstructPlus`, driven by
   `compile_reconstruct_nulled` into `f_plus_bc`, written by `FCompileExtra` only when
   `nul != NonNullable && quant.greedy` — `Compiler.dfy:313-316`) replays the final *nulled*
   iteration under the `ReconstructNulled` compile mode to recover the captures the skipped empty
   iteration would have written. Its spec counterpart is the ECMAScript rule that a `+` whose last
   iteration matched empty still resets/writes its groups. Nothing about this is proven today.

Order: do §2.5a first — it is independent and it exercises the fragment-widening plumbing (steps 1–2,
4) that §2.5b will reuse.

---

## 2. WHAT IS *NOT* AFFECTED

* `f_plus_bc` stays empty for the whole §2.5a fragment (`FCompileExtra` writes it only under
  `nul != NonNullable && quant.greedy` — `Compiler.dfy:313-316`), so `FNulledPlusIdentity` and every
  `QuantRegsFinal` argument survive §2.5a untouched.
* The `cdns` table is consulted ONLY by `CheckNullable`, which §2.5a never emits.
* Bounded `{m,n}` with a nullable body is ALREADY in the fragment (nullability is unconstrained
  there) — `a{0,3}` with `a` nullable verifies today. §2.5 is strictly about `max == None`.
