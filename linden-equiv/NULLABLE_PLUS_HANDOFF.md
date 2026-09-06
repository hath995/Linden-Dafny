# §2.5 HANDOFF — nullable unbounded quantifiers (`(a?)+`, `{n,}` with a nullable body)

**Status (2026-08-30): §2.5a DONE AND GATED. §2.5 AS A WHOLE IS HALF DONE — and the done half is
the cheaper, rarer one.** Of the three schemes a NULLABLE unbounded quantifier can compile to, this
rung closed exactly one (the lazy/GENERIC one). The two GREEDY schemes are §2.5b and are still out.
`(a?)+?` verifies; **`(a?)+` does not** — and the greedy form is far more common in real regexes.

* Branch `nullable-plus` off `da03fe0`, 25 commits ending `ac148e1`. Never pushed, never merged.
* Gate: `LEM_BUILD_TIMEOUT=0 lem pack --jobs 3` from the repo root — **61/61 green, rc=0, 18m 11s**
  incremental. No timing regression: `main-theorem` 641 obligations in a 2m 33s level,
  `lift-sim-core` 274 in 2m 59s, and `nest-inv` is FASTER than before the rung (the `NestInvGenRE`
  factoring removed three pre-existing 900 s timeouts in that file).
* Fragment gate is `q.min > 0 && q.max == None && !q.greedy && nul != R.NonNullable` — the
  `!q.greedy` is what holds §2.5b out. Non-vacuity pinned by `NullablePlusWitness.dfy`.
* Predecessor rung: L5 + the `(?=x(?<=y))` widening — `L5_HANDOFF.md`.
* **Next rung: §2.5b**, sized LARGER than §2.5a — see § WHAT §2.5b ACTUALLY COSTS at the end.

---

## 1. THE HEADLINE — §2.5 IS TWO RUNGS, NOT ONE

`Compiler.dfy:104-156` gives an unbounded `min > 0` quantifier **four** different schemes, selected
by the annotator's nullability `nul` and `quant.greedy`:

| body nullability | greedy | scheme | proof status |
|---|---|---|---|
| `NonNullable` | either | **do-while** — `repeat_min(min-1)`, stamp, body, BACKWARD fork | ✅ in the fragment today |
| `CINullable` | greedy | end-fork + `SetQuantToClock(qid, true)` | ❌ §2.5b |
| `CDNullable` | greedy | end-fork + **`CheckNullable(qid)`** + `SetQuantToClock(qid, true)` | ❌ §2.5b |
| `CINullable`/`CDNullable` | **lazy** | the **GENERIC** scheme — `repeat_min(min)` then the ordinary star loop | ✅ **§2.5a — DONE 2026-08-30** |

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

---

## 3. PROGRESS LOG

### 2026-08-30 — §2.5a layers 1–2 COMPLETE (branch `nullable-plus`, off `da03fe0`)

| commit | what | whole-file |
|---|---|---|
| `7d12d13` | layer 1 — `NfaRepRE`'s GENERIC arm + fragment widening | 209/0 |
| `8a09053` | layer 1b — lean fragment (matching-loop fix) + sectioning | 217/0 |
| `1cc8a01` | layer 1c — `TransWf` pins the annotation (`linden-reasoning`) | 390/0 |
| `0487147` | layer 2 — `ActionsRepRE`: `NfaRepL`'s GENERIC arm + the bridge | 54/0 |
| `ffde5d9` | drop the superseded `NullAnnotOkRE` | 215/0 |

**Layer 1 — `NfaRepRE.dfy`.**
* The unbounded `min > 0` arm is a two-way **`if` on `nul`**, not a disjunction — the arms are
  disjoint by construction, so every consumer holding `nul == NonNullable` still sees only the
  do-while and needed no change.
* The GENERIC arm is `NfaRepMinRE(min, …, em)` followed by the STAR arm's shape verbatim at `em`
  (the star's `Jmp` back-edge lands on its own fork, so `pc1 == em` lines up exactly).
* Fragment predicates (`Plus`/`LookBehind`/`Nested` × `{RE,Raw}`) admit
  `min > 0 && max == None && !greedy`, and **nothing more** — see the axiom-weight finding below.
  `Raw_quant`'s guard weakened from `(q.Plus? || q.LazyPlus?) ==>` to `q.Plus? ==>`.
* New `NfaRepREGenIntro` / `NfaRepREGenInv`; `NfaRepREPlusInv` gained `requires nul == R.NonNullable`.
* Generic arms added to `FreshCorrect{,Nested}RE`, `CompileNfaRep{,Nested}RE`, `NfaRepExtendRE`,
  `NfaRepIncrRE`, and the five instruction sweeps. In the sweeps the loop's own five instructions
  (Fork/SetQuantToClock/BeginLoop at `em..em+2`, EndLoop/Jmp at `e1..e1+1`) are all of the harmless
  kind, so `pc <= em + 2` replaces the do-while's `pc == em`.

### ⚠️ FINDING 1 — the fragment axiom must stay free of `R.nullable`

The bridge needs `R.nullable(r1) != NonNullable`. Putting it in the fragment predicates is NOT
viable. Measured on whole-file `NfaRepRE.dfy`:

| fragment `Re_quant` case | result |
|---|---|
| `… && nul != NonNullable && R.nullable(r1) != NonNullable` | `CompileNfaRepRE` TIMEOUT |
| `… && R.nullable(r1) != NonNullable` alone | `CompileNfaRepRE` TIMEOUT |
| lean (only `!q.greedy`) | **215 verified, 0 errors** |

It is a MATCHING LOOP, not a missing fact: `--isolate-assertions` closes all **1009** obligations
individually, and the profile shows one batch burning 628M resources and still timing out at 900 s.
`LookBehindFragmentRE`/`NestedFragmentRE` are unfolded by every lemma in the file — the `Re_alt` arm
already carried a `hide *` collapsed context with a comment about exactly this fragility.

**Resolution: `T.TransWf` carries it instead** (`1cc8a01`), since every bridge caller already passes
`TransWf` and nothing new has to be threaded through LiftSim:

```dafny
case Re_quant(nul, _, q, r1) => QuantWf(q) && nul == R.nullable(r1) && TransWf(r1)
```

Cost across all of `linden-reasoning`: **one** new obligation. `AnnotateRegexWf` needed nothing
(`annotate_regex` literally writes `Re_quant(nullable(ar1), …)`). `RevRETransWf` needed the new
`RevRENullable` — `RevRE` keeps the annotation but reverses the body, so reversal must not change
nullability; it doesn't, because the only non-structural case is `Re_con`, where reversal swaps the
operands and `null_and` is commutative (`NonNullable` absorbs from either side; the CD/CI
combinations are symmetric).

The REJECTED alternative, for the record: a standalone `NullAnnotOkRE` predicate required by the
bridge lemmas. It keeps the hot axiom lean too, but needs a new precondition on 6 bridge lemmas + 2
entry lemmas and then 6 call sites across `main-theorem`, `lift-sim-carriers` and `lift-sim-main` —
a cascade toward LiftSim's giants. Written, measured against the `TransWf` route, and deleted (`ffde5d9`).

**Layer 2 — `ActionsRepRE.dfy`.**
* `NfaRepL`'s `Inf` arm: two GUARD-DISJOINT disjuncts (`NonNullableL(r1)` → do-while,
  `!NonNullableL(r1) && !greedy` → generic), the generic body in a new **`NfaRepGenL`**
  (`decreases r1, min + 3` — above `NfaRepMinL`'s `r1, min + 2` and `NfaRepL`'s `r1, 1`).
* **`TransNullableAgree`**: `NUL.TransNonNullable` is only the forward half; the bridge needs the
  converse, so this proves the biconditional by plain structural induction (the two definitions are
  constructor-for-constructor mirrors).
* `NfaRepLGenIntro` / `NfaRepLGenInv`; `NfaRepLPlusInv` gained `requires NUL.NonNullableL(r1)`;
  both bridge arms and `NfaRepIncrL`'s `Inf` arm case-split.
* Note the spec-side fragment cannot supply the discriminator: `EL.PikeLkRegex{,Rec}` put NO
  condition on `Quantified` (`case Quantified(_, _, _, r1) => PikeLkRegexRec(r1)`). L-side consumers
  read nullability OFF `NfaRepL`'s arm — which is why only the bridge needs the RE→L transfer.

### ⚠️ FINDING 2 — a Dafny 4.11 translator bug (expect it again in layers 3+)

The GENERIC arm's `exists` needs an EXPLICIT `{:trigger}`. Without one Dafny emits an ill-formed
Boogie axiom and crashes: `Boogie program had 44 resolution errors: undeclared identifier: _t#0#1`,
then a core dump. Bisected (add conjuncts one at a time to the working do-while arm) to a SINGLE
conjunct — the loop back-edge `NR.GetPcRE(c, e1 + 1) == Some(RB.Jmp(em))`, whose jump target is an
existentially-bound variable. The star arm has the identical shape and is fine only because its
target is the PARAMETER `pc1`.

Does NOT help: `if-then-else` vs guard-disjoint disjuncts; hoisting the existential into its own
predicate; the projection form (`.Some? && .value.Jmp? && .value.jl == em`); swapping binder order;
fixing the `decreases` metric. **`dafny resolve` issues NO trigger warning** — the crash is the only
symptom. If a representation predicate starts crashing Boogie translation after an edit, do not
chase the logic: bisect to the new conjunct and pin its trigger.

### 2026-08-30 (cont.) — layer 3 COMPLETE; the remaining work is MAPPED

| commit | package | whole-file |
|---|---|---|
| `136ce79` | `walk-ok` — the do-while seam gated on `NonNullableL` | 35/0 |
| `4ee087a` | `actions-tree-rep-re` — the GENERIC min>0 arm | 60/0 |
| (next) | `flip-rev` — `FlipRENullable` | 19/0 |

**Layer 3a — `WalkOk` had to change too.** `WalkOkRegF`'s `Quantified` case special-cased
`delta.Inf? && min == 1` into the do-while SEAM form (the walk with an `Acheck` spliced in),
UNCONDITIONALLY. That bakes the do-while shape into `WalkOk`, so it could not describe a GENERIC
`min == 1`, whose walk is the plain `[Areg(r1), Areg(star)] + cont`. The two layouts are
indistinguishable from the code at `pc` (both show `SetQuantToClock`), so the gate must be the same
discriminator as everywhere else: `NUL.NonNullableL(r1)`. `WalkOkQuantForced` weakened accordingly;
`WalkOkQuantSeam` gained `requires NonNullableL(r1)`.

**Layer 3 — `ActionsTreeRepRE`**, four sites in two kinds. `ATR_QuantMin{,Nested}` got the real arm,
modelled on the BOUNDED `NN(kx)` case (same shape: one forced copy, then `quant1` via an intro
lemma) rather than the do-while; at `min == 1`, `NfaRepMinL(0, …)` forces `eb == em` and the loop at
`em` IS `NfaRepL`'s star arm verbatim, so the branch just stops.
`AtBackForkTreeRep{,Nested}` are refutations — a `min > 0` head pins a clock-mark against the pinned
`Fork`, and the generic layout refutes identically.

### THE REMAINING WORK — precisely bounded

Only two kinds of site can break. Everything that merely CONSUMES `TransWf`/`WalkOk` is unaffected
(the hypotheses only got stronger).

**(a) Constructions that must re-establish `TransWf`** — i.e. prove their rewrite preserves the
nullability annotation, the way `RevRENullable` / `FlipRENullable` do:

| site | expected cost |
|---|---|
| `flip-statics` — `T.TransWf(XRV(r))`, `T.TransWf(FXR(r))` (×3) | FREE-ish: `XRevIsRevRENested` already proves `XRV == RevRE`, and `FXR = FlipRE ∘ XRV`, so it composes from `RevRENullable` + `FlipRENullable` |
| `flip-gate` — `T.TransWf(FST.FXR(body))` | same composition |
| `oracle-spec` — `T.TransWf(R.remove_capture(re))`, `T.TransWf(SD.RevRE(re))` | `RevRE` done; `remove_capture` needs its own preservation lemma (`nullable(Re_capture(c,r1)) == nullable(r1)`, so it should be structural) |
| `lift-sim-{core,forward,gate}`, `main-theorem`, `oracle-entry` — `LookBodyOfRE`, `QidBody`, `body`, `core`, `sub` | expected FREE: these EXTRACT sub-regexes, so `TransWf` is inherited structurally and the new conjunct rides along |

**(b) Lemmas that INVERT the unbounded arm** and so need the generic branch.

> **SUPERSEDED — the count below was wrong.** It came from a `grep ... | head`, which truncated at
> ten lines that all happened to be `LiftSimCore`. The real fallout was **8 packages**; see
> *§ FINAL STATE* at the end of this document for the true list. The `LiftSimCore` table is still
> accurate as far as it goes. Note that even the corrected grep missed one package
> (`walk-ok-entry`) — only `lem pack` found it. **Do not trust a source grep for this question; run
> the pack.**

```
linden-equiv-lift-sim-core/src/LiftSimCore.dfy
  1382  AR.NfaRepLPlusInv      1480  WO.WalkOkQuantSeam
  1881  AR.NfaRepLPlusInv      5732  WO.WalkOkQuantSeam
  2602  NR.NfaRepREPlusInv
  3719  AR.NfaRepLPlusInv      3779  AR.NfaRepLPlusInv
  5634  AR.NfaRepLPlusInv
```

`LiftSimCore` duplicates the `ActionsTreeRep` quantifier logic, so each site takes the SAME generic
branch already written in `ATR_QuantMin` — mechanical, but on a file that needs `PAR=1 CORES=4` and
tens of minutes per run (`[[linden-dafny-memory-cap]]`). Budget this as the bulk of the rung.

Then **layer 4**: widen the `+`/`{n,}` gate in `ApiMatch.SupportedL3/L4/L5`, and update
`SUPPORTED_FRAGMENT.md` §2.5/§3 (§2.5 splits into 2.5a DONE / 2.5b open).

### ⚠️ THE GATE WAS BROKEN INDEPENDENTLY OF THIS RUNG (since RESOLVED — see § FINAL STATE)

`lem pack` / a multi-package `lem build` currently fails at `verifying linden.equiv-mirror` with
`module WarblreRegExpRecord does not exist`: lem stages `linden-semantics-core`'s SOURCES as
`--library` without `linden-warblre`'s, so semantics-core's own imports cannot resolve. This is a
transitive-dependency staging bug on the Lemmata side, NOT a proof failure and NOT caused by §2.5a
(`linden-equiv-mirror` is untouched). A single-package `lem build` works (`nfa-rep-re`: 215/0,
"build OK against 6 dependencies"). Until it is fixed, whole-workspace verification has to be done
by hand, package by package, in dependency order.

Working-tree hygiene: the `lemmata.toml`/`.lock` drift (four version DOWNGRADES plus one bump,
inconsistent with the 47 equiv locks) was reverted to the committed state, which is what fixed the
earlier `lemmata.lock is stale` failure.

---

## § FINAL STATE (2026-08-30)

### The reusable artifact: SEVEN layout-baked predicates

The campaign's central finding is that exactly seven predicates hard-code ONE compiler scheme for
the unbounded `min > 0` case. Every one of them had to grow a second arm, and every consumer that
INVERTS one of them had to grow a matching branch. Widening any future scheme means touching this
same list and nothing else:

| predicate | package |
|---|---|
| `NfaRepRE`  | `linden-equiv-nfa-rep-re` |
| `NfaRepL`   | `linden-equiv-actions-rep-re` |
| `WalkOkRegF`| `linden-equiv-walk-ok` |
| `InBlock`   | `linden-equiv-oracle-decomp` |
| `InBlockV`  | `linden-equiv-oracle-decomp-v` |
| `NestInvRE` | `linden-equiv-nest-inv` |
| `ColdF`†    | `linden-equiv-nest-inv` |

† `ColdF` turned out NOT to need extension — it is stated over bytecode, not regex shape — but its
two propagation lemmas (`ColdPropagatesF{,Nested}`) and the two `BeginLoopColdSafeAt{,Nested}`
lemmas that consume it DO, because the generic scheme puts a `BeginLoop` at `em + 2` where the
do-while has none. Listing it here because "is this predicate layout-baked?" is the question a
future rung has to ask, and the answer for `ColdF` is a genuinely useful *no*.

### THE ONE PACKAGE THAT IS *NOT* THE PATTERN

**Eleven packages** were touched in total: `nfa-rep-re`, `actions-rep-re`, `walk-ok`,
`actions-tree-rep-re`, `lift-sim-core`, `oracle-decomp{,-v}`, `oracle-bridge{,-v}`, `pike-inv-re`,
`main-theorem`, `linden-reasoning`, plus the four that only `lem pack` found — `nest-inv`,
`walk-ok-entry`, `tree-thread-re`, `lift-sim-oracle`, `lift-sim-chain`.

`linden-equiv-walk-ok-entry` was found by `lem pack`, not by grep, and it is the one place where the
generic scheme needs a genuinely new argument rather than a shifted copy. `WalkOkPlusChainF` bottoms
out at `k == 1` in the **SEAM** — the guaranteed last forced iteration, with the walk guard's
progress check (`Acheck`) inserted at the stamp. The generic scheme has **no seam**: its code puts a
real `BeginLoop`/`EndLoop` exactly where the spec's `Acheck` would sit. So there is nothing to
insert, and the whole chain takes `WalkOkRegF`'s plain forced-copy branch instead.

The new `WalkOkGenChainF{,Nested}` closes the seam case with `AR.TransNullableAgree` (from
`nul != NonNullable`, derive `!NonNullableL(tr1)`), and its `k == 0` bottom re-uses the star arm
against `Re_quant(nul, qid, CountedQuant(0, None, greedy), r1)` — **the star regex the block at `em`
actually compiles**. That trick is worth remembering: the generic tail is not merely *shaped like* a
star, it IS one, so any lemma stated over `NfaRepRE(re, …)` can be applied to it directly by naming
that regex.

`WalkOkPlusChainF{,Nested}` correspondingly gained `requires R.nullable(r1) == R.NonNullable`.

### THE ONE PATTERN

Every generic arm in the campaign is the same rewrite. The generic scheme is

```
  NfaRepMinRE(min, …, pcb, em)          -- `min` forced copies
  em     : Fork(e1 + 2, em + 1)         -- LAZY fork (skip first)
  em + 1 : SetQuantToClock(qid, false)
  em + 2 : BeginLoop
  em + 3 .. e1 : the body
  e1     : EndLoop
  e1 + 1 : Jmp(em)                      -- back to the FORK, not the block head
  pce == e1 + 2
```

which is **the ordinary star arm shifted from `pcb` to `em`, with a Min chain in front**. So every
proof obligation splits into "the chain's" (delegate to the existing `…Min` helper) and "the star's"
(copy the star arm verbatim, `pcb ↦ em`). The two places this bites:

1. **The back edge is `Jmp(em)`, not `Jmp(pcb)`** — advance lemmas must land on the fork, not the
   block head. `NestInvAdvance` is the one that cares.
2. **`em + 2` is a `BeginLoop`** — the do-while has no `BeginLoop` at all, so any lemma that case-
   splits on `BeginLoop` sites needs a new case. This is what broke both `BeginLoopColdSafeAt`
   twins; the symptom was `assert em + 3 <= p < e1` failing, and the fix was the star arm's own
   Cold-sink argument (`ColdPropagatesF` into the body, then `!BackForkAt(c, e1)`, `assert false`).

### THE FACTORING TRADE — IT CUTS BOTH WAYS

Factoring a fat arm into a named predicate with an explicit `{:trigger}` is the fix for the timeouts
below, but it has a second, opposite effect that cost three packages this rung:

* **The win:** consumers that were TIMING OUT get fast, because they no longer inline the arm.
* **The cost:** consumers whose proofs were **EMPTY** — relying on Dafny to unfold the arm itself to
  reach a contradiction — start FAILING, because the trigger stops that unfolding.

The second kind is invisible to grep: those proofs never mention the predicate you changed. Only a
full `lem pack` finds them. Three instances:

| package | site | the fact that had to be named |
|---|---|---|
| `tree-thread-re` | `NfaRepLTransparentAtBeginLoop`, `Quantified` case (an empty arm) | `NfaRepLGenInv` then `NfaRepMinL(min>0)` pins `SetQuantToClock` ≠ `BeginLoop` |
| `lift-sim-oracle` | `TtLkAtForkCore{,Rec}`, ×2 | `min > 0` pins a clock-mark, refuting the `Fork` |
| `lift-sim-chain` | `WalkPairLkAtForkCore…`, ×2 | same |

The last two share one new lemma, `QuantHeadMinPosPinsSQC` in `LiftSimCore`: **for `min > 0` the
head at `pc` is ALWAYS a clock-mark, never a `Fork`** — true of all three schemes, since every
`min > 0` layout begins with a forced-copy chain. Its older sibling `QuantHeadPinsForkOrSQC` only
gives `Fork? || SetQuantToClock?`, which cannot refute a `Fork` the caller is sitting at. That
weaker form is fine for callers proving "not a `SetRegisterToCP`" and wrong for callers at a fork.

### PERFORMANCE: inline size, not logical content

Three separate 900 s timeouts this rung, all the same cause and all the same fix — **a fat arm
inlined into a hot predicate**, never the arm's logic:

| symptom | fix | after |
|---|---|---|
| `CompileNfaRepRE` 628 M resources / 900 s | move annotation consistency out of the fragment axiom into `TransWf`; use a datatype FIELD comparison (`nul != R.NonNullable`), never a recursive call (`R.nullable(r1)`), in a hot predicate | 215/0 |
| `NfaRepL` consumers timing out | factor the generic body into `NfaRepGenL` + explicit `{:trigger}` | 54/0 |
| `NestInvOpenSite` / `NestInvAdvance` / `NestInvFrameOddOpt` each 900 s | factor the 12-conjunct generic arm into `NestInvGenRE` | 21.7 s / 31.4 s / 69.5 s |

The `NestInvGenRE` factoring is worth copying wholesale: predicate + `NestInvGenREInv` (inversion,
returns `em, e1` and the site claims) + `NestInvGenREIntro` (the dual). With those two helpers, each
of the nine consumer arms is ~15 lines and no consumer ever unfolds the existential itself.

Two Dafny findings, both recorded in memory:
* A **recursive function call** in a hot predicate creates a matching loop; a **datatype field
  comparison** costs nothing.
* Dafny 4.11 **crashes** (Boogie `undeclared identifier: _t#0#1`, core dump, no trigger warning) on
  `GetPcRE(c, e1 + 1) == Some(RB.Jmp(em))` with `em` existentially bound. An explicit `{:trigger}`
  is the only fix. → `[[dafny-auto-trigger-crash]]`

### The pack gate

The "module `WarblreRegExpRecord` does not exist" failure above was working-tree drift in the
`lemmata.toml`/`.lock` files, not a Lemmata bug; with those reverted, `LEM_BUILD_TIMEOUT=0 lem pack
--jobs 3` runs clean. Levels 0–4 (17 members) pack in ~9 min against a 59-min full-workspace
baseline — **no regression from §2.5a**.

`linden-equiv-nest-inv/lemmata.toml` now pins `cores = "2"`: `NestInv.dfy` is 7 k lines and a
whole-file run at `--cores=4` OOMs against the 80 G `dafny.slice` cap.

---

## § WHAT §2.5b ACTUALLY COSTS — read this before sizing it

**Do not size §2.5b as "another §2.5a".** §2.5a was cheap for one specific reason: the GENERIC
scheme's tail **is the ordinary star loop**, so every obligation was the star arm with `pcb ↦ em`
and a forced-copy chain in front. None of that carries over. The greedy schemes are a different
shape, and three things break at once:

**(1) Two layouts, not one — and a NEW INSTRUCTION.**

```
  CIN greedy:  min_code, [Fork(min_f+1, body_f+2), SetQuantToClock(qid,false), BeginLoop],
               body_code, [EndLoop, Fork(min_f+1, body_f+3), SetQuantToClock(qid, true)]
  CDN greedy:  min_code, [Fork(min_f+1, body_f+2), SetQuantToClock(qid,false), BeginLoop],
               body_code, [EndLoop, Fork(min_f+1, body_f+4), CheckNullable(qid),
                           SetQuantToClock(qid, true)]
```

The tail is an **end-fork**, not a back-`Jmp`: the loop re-entry target is `min_f + 1` (the stamp),
and the fall-through runs off the end of the block. `CheckNullable(qid)` appears in the CDN case and
**no layout predicate in the campaign models it** — §2.5a added no new instruction at all, it reused
the star's.

**(2) `SetQuantToClock(qid, true)` — the `true` flag, used here for the first time.**

Both greedy schemes end by stamping with `b == true`. This is load-bearing elsewhere:
`NI.CodeShapeAt` currently *proves* `forall pc, q, b :: GetPcRE(code,pc) == Some(SetQuantToClock(q,b)) ==> !b`,
and `MainTheoremL3` consumes exactly that fact in its `forall` block over the whole code. Weakening
it means re-proving every consumer of the "all stamps are false" invariant. §2.5a deliberately did
NOT disturb this — `FCompileExtraPlusFrame` proves the extra-instruction set stays empty across the
whole §2.5a fragment, which is why the flag survived untouched.

**(3) A SECOND compilation path.** `Compiler.dfy`'s `else // ReconstructNulled` branch has its own
dedicated arms for CIN-greedy (`[SetQuantToClock(qid,true)]`) and CDN-greedy
(`[CheckNullable(qid), SetQuantToClock(qid,true)]`). §2.5a's generic case falls through to the
shared default there, so the rung never touched `ReconstructNulled`. §2.5b must.

**Where to start.** The seven layout-baked predicates are the same list as always (see
§ FINAL STATE); extend them, then `lem pack` and let it enumerate the consumers — do NOT estimate
by grep, that failed four times in §2.5a. Expect all three failure modes again, and expect the
`SetQuantToClock(_, true)` weakening to be the hard part rather than the layout arms.

---

## § 2.5b PROGRESS LOG (campaign started 2026-08-30, branch `nullable-plus-greedy` off `nullable-plus`)

**SCOPE DECISION: §2.5b is being landed as §2.5b-CIN — the greedy CI-nullable schemes only.**
CDN-greedy (`CheckNullable`) stays fully out (no representation, no fragment admission); it is a
third pass through the same predicates plus the whole cdns correspondence, deferred.

**ARCHITECTURE OF THE RUNG — two stages:**

1. **The LAYOUT + INTERIM stage (this log):** every layout-baked predicate gets the CIN-GREEDY
   end-fork arm for real; the mid-parse SOUNDNESS invariant (`InBlock`/`InBlockV`) gets the real
   CIN arm including the NULLED-EXIT theorem; but the all-stamps-false layer survives via an
   INTERIM GATE CONJUNCT: `SupportedL3/4/5` now carry `NR.NoNulledPlusRaw(pattern)`, and the
   stamps-false consumers take `NR.NoNulledPlusRE(...)` hypotheses discharged by the new
   `NI.StampFalseAt` sweep (split out of `CodeShapeAt`, which LOST its `!bb` claim). The
   TREE-correspondence tower (ActionsTreeRep/TreeThread/PikeSim/LiftSim) refutes its CIN branches
   from the interim hypothesis where a real arm would need the reconstruction theorem.
2. **The RECONSTRUCTION stage (NOT STARTED):** the FNulledPlus/FReconstructPlus correspondence —
   the engine's stamp-true + replay equals the spec's empty mandatory iteration. Its landing
   deletes the interim conjunct and replaces the refutation branches with real arms. THE PRIORITY
   SUBTLETY to prove: the engine explores [body's consuming paths, then the stamp path] while the
   spec explores body paths in priority order WITH empty ones live (no Acheck on the mandatory
   iteration); the results agree because all empty body-paths yield identical continuation
   configurations (no backrefs) and GMReset erases a superseded empty iteration's writes.

**KEY NEW FACTS (this stage):**
* The CIN end-fork layout (`em: Fork(em+1, e1+2); em+1: SQC(qid,false); em+2: BeginLoop; body;
  e1: EndLoop; e1+1: Fork(em+1, e1+3); e1+2: SQC(qid,true); pce == e1+3`) — both re-entry arms
  land ON THE STAMP `em+1`, and the head fork's skip arm crosses the stamp-true INSIDE the block
  (a genuinely new in-block forward edge; the end fork is a new `BackForkAt`).
* The fragment predicates' CIN disjunct pins ANNOTATION CONSISTENCY:
  `q.greedy && nul == R.CINullable && R.nullable(r1) == R.CINullable`. The equality (unlike
  §2.5a's measured-fatal inequality) verifies fine — 207/0 whole-file. It is LOAD-BEARING twice:
  `ColdNNF` (else a zero-width path could CROSS a "NonNullable" quant via the skip arm) and the
  nulled exits in `BlockStep`/`BlockStepV`.
* `CINullableMatchesEmpty{,V}`: a CI-nullable fragment regex matches the empty span at EVERY
  position (the semantic content of CI); discharges the stamp-true exit in the soundness sweep.
* `NUL.CINullableL` + `TransCINullable` (biconditional) mirror the NonNullable story; `NfaRepCinL`
  ties BOTH stamps to ONE existential qid.
* Cold analysis: the CIN loop body is a Cold sink exactly like the star's (EndLoop wall), so the
  new back fork at `e1+1` is unreachable zero-width from inside; only the skip arm carries Cold
  across the block.

**COMMITS (all whole-file green at commit time):**
| commit | package(s) | result |
|---|---|---|
| `d1fb40d` | nfa-rep-re layer 1 + CINullableL (linden-reasoning) | 221/0, 7/0 |
| (next) | actions-rep-re layer 2 | 59/0 |
| (next) | NoNulledPlusRE/Raw + OracleBridge CinLoopPath | 4/0, 36/0 |
| (next) | OracleDecomp CIN + nulled exit; OracleBridgeV | 86/0, 35/0 |

**DONE AND COMMITTED (whole-file green each):** nfa-rep-re (layer 1 + `NoNulledPlusRE` alias to
the canonical `NUL.NoNulledPlusRE_`, 226/0), actions-rep-re (59/0, `NfaRepCinL`), linden-reasoning
(`CINullableL`/`TransCINullable`/`NoNulledPlusL`/`TransNoNulledPlus` + SpanDuality
`RevLNonNullable`/`RevLNoNulledPlus`), oracle-bridge (36/0 `CinLoopPath`), oracle-bridge-v (35/0),
oracle-decomp (86/0 — `CinShape`/`CinTail` + **the NULLED-EXIT theorem** via
`CINullableMatchesEmpty`), oracle-decomp-v (73/0), oracle-accept-v (22/0), nest-inv (239/0 —
`NestInvCinRE` family, `StampFalseAt` split out of `CodeShapeAt` which LOST `!bb`,
`NoNulledPlusLookBody`), pike-inv-re (304/0), entry-lk (50/0 — **`PikeLkRegex{,Rec}` carry the
interim conjunct**: Quantified case + BOTH look arms), tree-thread-re (9/0), walk-ok-entry (47/0 —
`WalkOkCinChainF{,Nested}`, trivial k==1 bottom), tree-mirror-lk (100/0), flip-statics
(`NoNulledPlusXRV/FXR/FlipRE`, 3/0).

**THREADED, PACK-PENDING:** MainTheorem (`NoTrueQuantStamp{,Nested}` via `NI.StampFalseAt` + 44
caller lemmas + 3 sweeps CIN-branched), LookCapture, ApiMatch gates (`NoNulledPlusRaw` on
SupportedL3/4/5), LiftSimCore (three head lemmas that are FALSE for CIN@min==1 —
`QuantHeadMinPosPinsSQC`/`QuantForcedContRep`/`QuantHeadSQCPin` — carry the per-node conjunct;
five layout pins got real CIN branches; four construction arms refute via `assert !greedy` from
PikeLk), actions-tree-rep-re (four `assert !greedy` refutations), the 13 shared-statics
FindRec/tower lemmas + six `NoTrueQuantStampNested` call-site derivations.

**EXPECTED NEXT FALLOUT (pack waves):** the per-lid forall hypotheses in the FLookLoop family
(main-theorem/lift-sims) need `NoNulledPlusRE(body)` in their conjunct lists, discharged at the
top from the gate via `NI.NoNulledPlusLookBody`/`NR.NoNulledPlusReverse`/`FST.NoNulledPlusFXR`;
plus whatever check-erase / tree-rep-re / gen-step-re / pike-sim-re dispatchers hit the CIN arm
(judge each: layout classification → real branch; tree correspondence → interim refutation).
Driver: `LEM_BUILD_TIMEOUT=0 lem pack --jobs 3` at root, fix the first red member, repeat.
Dev loop: verify against SIBLING SOURCES (`--library=../pkg/src/File.dfy`, exclude the stale
.doo — works, resolution is package-blind).

**INTERIM STAGE COMPLETE — WHOLE WORKSPACE PACKED 61/61 (2026-09-02, `LEM_BUILD_TIMEOUT=0 lem pack
--jobs 3`, `/usr/bin/lem` 0.1.21).** Last two members after the lift-sim rounds: `lift-sim-main` packed in
26m 11s (the two `{:isolate_assertions}` keystones `ForwardMemberOne`/`MainTheoremL5`; lem reports 8
obligations) and the top `linden-equiv` in 4m 17s (28 obligations) after ONE fix: `TypedCaptureAlt`
(`ApiReasoning.dfy`, untouched since E2) timed out at 900 s under z3 4.14 as a single batch although every
obligation isolates (366/0); three `assert {:split_here} true;` → 5 batches, 4 s solver time. Nothing
in the interim stage is gated by anything but `NoNulledPlusRaw` on `SupportedL3/4/5`.

---

## § 2.5b STAGE 2 — RECONSTRUCTION DESIGN (written 2026-09-02, before any stage-2 code)

**The theorem to land:** for a CIN-greedy `r1+` (`min > 0`, `max == None`, `greedy`,
`nullable(r1) == CINullable`), the engine's *skip arm + `SetQuantToClock(qid, true)` +
`FReconstructPlus`* computes what the spec's *empty mandatory iteration* computes. Landing it
deletes the interim conjuncts (`NoNulledPlusRaw` on `SupportedL3/4/5`, ~60 `// §2.5b interim`
sites, four `assert !greedy` refutations in actions-tree-rep-re) and the ~55
`M.FNulledPlusIdentity` call sites become a real reconstruction lemma.

### The facts the design rests on (all read from the sources, none proven yet)

* Engine layout (`Compiler.dfy:114-121`), `min_f` = head fork, `e1` = EndLoop:
  `Fork(min_f+1, e1+2)`; `min_f+1: SQC(qid,false)`; `BeginLoop`; body; `e1: EndLoop`;
  `e1+1: Fork(min_f+1, e1+3)`; `e1+2: SQC(qid,true)`; `e1+3` = exit. The head fork is reached
  ONCE; the end fork re-enters at the stamp. So `SQC(qid,true)` runs exactly when the loop was
  skipped at entry = the mandatory iteration was NULLED at `cp`. Empty body paths die at
  `EndLoop` (`exit_allowed == false`), i.e. the engine explores [consuming body paths, then the
  stamp-true skip]. The spec (`Semantics.dfy:246-252`, `tree_quant_forced`) explores
  `Reset(gidl); [Areg(r1), Areg(Q(greedy,0,delta,r1))] + cont` — body paths in priority order
  WITH empty ones live (no `Acheck` on the mandatory iteration).
* `FReconstructPlus` (`Interpreter.dfy:418-505`): walks the AST; for each quant with
  `get_cp(qt, qid) == Some(start_cp)` (last stamp was `true`) runs the NULL INTERPRETER
  (`FNullInterp` = one `FAdvanceEpsilon`, no consumption) over `compile_reconstruct_nulled(r1)`
  from `start_cp` with the thread's CURRENT registers and clock `get_clock(qt, qid)`, then
  `FNulledChildren` on the body at the SAME cp. ReconstructNulled code: characters → `Fail`;
  captures → `SetRegisterToCP`; lookarounds → `CheckOracle`; nested quant: `min == 0` → `[]`,
  NonNullable → `Fail`, CIN-greedy → `[SQC(qid',true)]`, else `SQC(qid',false)` + body. So the
  null interpreter finds THE TOP-PRIORITY EMPTY PATH of `r1` at `start_cp` and applies its
  group writes (all at `start_cp`) + nested stamps. Pipeline order (`FBuildCapture`):
  `FFindMatchPlus` (match + reconstruct) → `FLookLoop` (look-capture replays, each itself an
  `FFindMatchPlus`) → `filter_reset`.
* `filter_capture` reads ONLY CLOCKS (`quant_clocks`), never quant cp values — so the
  `bb == true` stamp is invisible to `GmOf`/`GmOfLive`/every PikeSim invariant; only
  `FNulledPlus` reads `a_cp`. `PikeSimRE.ResetStepThreadRE` requires `SQC(qid0, false)` only
  because it was written that way (its conclusion is clock-based).
* The tower's tree relation: `TreeRepRE(qm, t, code, pc, inp, b)` (code → Linden tree; `qm.ov`
  carries the oracle; `tr_reset` currently only for `bb == false`), `ActionsTreeRep*` conclude
  `LL.LeavesAgreeAtOutside(tstar, t, inp, S)` (LEAF-LIST agreement outside the look-confined
  groups `S`), consumed at 7 sites (LiftSimCarriers 222/496/656, LiftSimMain 548, MainTheorem
  3725/3815/3893) which immediately lift to `FirstLeafAgreeOutside` (Hd-level).

### The priority argument (spec-level, checked by hand — this is rung A's theorem)

Let `t1` = tree of `[Areg(r1)]` at `(inp, GMReset(gidl, gm))`, leaves `ℓ` in priority order;
`I` = leaves of the star's iteration arm `Reset(gidl); [Areg(r1), Acheck(inp), Areg(star)] + cont`
= concat over CONSUMING `ℓ` of `Block(ℓ)` (Acheck kills the empty ones);
`C(ℓ)` = leaves of `cont` at `(inp, gm_ℓ)` for an EMPTY `ℓ`.
* `Leaves(T_plus)` = for `ℓ` in order: consuming → `Block(ℓ)`; empty → `I ++ C(ℓ)`
  (an empty mandatory iteration continues into the star at the same `inp`; its
  `GMReset(gidl, gm_ℓ) == GMReset(gidl, gm)` since `ℓ` only wrote `gidl`).
* `Leaves(T_cin)` = `I ++ C(ℓ_e1)` where `T_cin := Choice(Reset(gidl); T_iter, Reset(gidl);
  Chain(ℓ_e1); T_cont)` is the engine's shape and `ℓ_e1` = the FIRST empty leaf.
* `Hd` agrees: if `I ≠ []` both heads are `Hd(I)` (every empty `ℓ` re-emits `I` first, and the
  first consuming block with a leaf is `I`'s head); if `I == []`, both are `Hd(C(ℓ_e1))`, because
  `|C(ℓ)|` is gm-independent (no backrefs: the tree of `cont` does not depend on the incoming
  gm, `IsTree` threads gm only into `Backreference`), so `C(ℓ_e1) == []` ⟹ every `C(ℓ) == []`.
* The LISTS differ (duplicated blocks), so the relation MUST weaken to Hd-level:
  `ResAgreeAtOutside(t1, t2, inp, S)` := ∀gm: `TreeRes` both None or both Some with equal
  position and `GmAgreeOutside(·, ·, S)`. It composes under Choice/Read/Progress/GroupActionT/
  AnchorPass/LK exactly like `LeavesAgreeAtOutside` (`LookLeaves.dfy:889-944` is the family to
  mirror) and the 7 consumers already only use the Hd-level consequence.
* `Chain(ℓ_e1)`: the virtual chain is the GROUP-ACTION SEQUENCE of the first empty path,
  `FirstEmptyPathL(rer, r1, inp): Option<seq<GroupAction>>`, defined by recursion on `r1` in
  priority order (Epsilon `[]`; Character `None`; Disjunction first-Some; Sequence concat;
  `Group(g, r)` → `Open(g) :: path(r) ++ [Close(g)]`; `Quantified` with `min > 0` →
  `Reset(DefGroups(r)) :: path(r) ++ path(min-1)`, `min == 0` → `[]` (an empty iteration dies at
  the star's `Acheck`, so the skip is the first empty path for greedy AND lazy); anchors/lookarounds
  → `[]` or `None` by the spec's verdict at `inp`). Every action is at `Idx(inp)`. This is exactly
  the recursion `compile(r1, ·, ReconstructNulled)` + the null interpreter follow (rung E), and it
  sidesteps the "characterize the leaf's gm" lemma a set-based `Open/Close` chain would need.
* CI-nullability is exactly the soundness condition: the skip arm needs SOME empty leaf to exist
  at every `inp` (`CINullableMatchesEmpty`, already proven for the interim stage).

### The rungs

| rung | package(s) | content |
|---|---|---|
| **A** | look-leaves (+ linden-reasoning) | `ResAgreeAtOutside` + congruence family + `LeavesAgree ⟹ ResAgree`; `FirstEmptyPathL` + `CINullableL ⟹ Some` + `FirstEmptyLeafIsPath` (the first leaf of `[Areg(r1)]`'s tree at position `inp` exists and its gm is the path's fold, outside the look-confined `S`); **the priority theorem** `ResAgree(T_plus, T_cin)` for CI-nullable `r1`, incl. the gm-independence of `cont`'s tree shape. Pure spec, no engine, no giants — proves the idea before the tower is touched. |
| **B** | tree-rep-re, actions-rep-re | `tr_reset` for `SQC(qid, true)` producing `Reset(gidl); Chain(FirstEmptyPath(qm.body[qid], inp, qm.ov)); tc` (oracle-bit version of `FirstEmptyPathL`, tied by `OracleOk`) — the QMap must carry the CIN BODY regex per qid (and `rer`/oracle for `NulledLeaf`); determinism lemma; `NfaRepL` already has the CIN layout arm. |
| **C** | actions-tree-rep-re (+ the 4 LiftSimCore tree giants `ActionsTreeRepLkF{,Rec}`, `AtBackForkTreeLkF{,Rec}`) | conclusions switched to `ResAgreeAtOutside`; the real CIN arm: head fork = `tr_choice`, loop arm = star iteration (`tr_plus` at the backward end fork), skip arm = rung B's virtual chain + rung A's theorem; drop the 4 `assert !greedy`. |
| **D** | pike-sim-re, tree-thread-re, pike-inv-re | `ResetStepThreadRE{,Nested}` generalised to `bb ∈ {false,true}`; the simulation readout becomes reconstruction-aware: `GmOfR(ast, regs) := GmOf(ast, Recon(ast, regs))` with `Recon` = the register effect of `FNulledPlus`; commutation of `Recon` with every non-nulled write (it only writes `gidl`/nested stamps of true-stamped quants and reads only `a_cp`, the oracle and the clock); the `SQC(true)` step yields `GMReset ⊕ NulledLeaf` = rung B's virtual node. If `ThreadTracksGm` is the only place `GmOfLive` is unfolded, the change is contained there. |
| **E** | new: `linden-equiv-nulled-recon` | THE ENGINE-SIDE CORRESPONDENCE: `FNullInterp(compile_reconstruct_nulled(r1))` from `cp` = `NulledLeaf`'s writes. Needs a layout predicate for ReconstructNulled-mode code (no loops; `Consume → Fail`), a `TreeRepRE` instance for it (the epsilon closure of one phase = the existing PikeSim theory with no consumption), and its `ActionsTreeRep` vs `[Areg(r1)]` restricted to position-`inp` leaves. Also: `FNullInterp` leaves `ov` unchanged (no `WriteOracle`), ignores `cdn` (no `CheckNullable` in CIN-only code), nested CIN quants re-stamped at the same `cp` then `FNulledChildren` — matches the spec's nested `Reset` + nested empty path. |
| **F** | main-theorem, lift-sim-*, look-capture, flip-*, look-behind-keystone | replace `FNulledPlusIdentity` sites by `FReconstructPlus(thread) == Recon`-readout facts; the Backward direction (lookbehind capture replays run `FFindMatchPlus` with `dir == Backward` — `RevRE`/`XRV`/`FlipRE` keep the annotation; reconstruction commutes with the mirror since all its writes are at one position); nulled plus INSIDE a look body (the `FLookLoop` replay reconstructs — `CheckOracle` in reconstruct code stamps look regs so the later look replays fire); the QuantRegsFinal family retires. |
| **G** | ApiMatch, nest-inv, entry-lk, … | drop `NoNulledPlusRaw`/`NoNulledPlusRE`/`NoNulledPlusL` conjuncts (~60 sites), `StampFalseAt` sweep retires; `NullablePlusWitness` gets a CIN-greedy witness; repack 61/61; `SUPPORTED_FRAGMENT.md` §2.5 row flips. |

Order: A → B → C → E (independent of D, can go in parallel via a worktree) → D → F → G. Rung A
is the go/no-go: if `ResAgree(T_plus, T_cin)` does not verify as stated, the tower is untouched.
CDN-greedy (`CheckNullable`) stays out of scope for all of this.

### STAGE 2 PROGRESS LOG

**2026-09-02 — RUNG A LANDED (spec-level priority theorem), new member `linden-equiv-nulled-plus`
(module `LindenElkNulledPlus`, depends on look-leaves/entry-lk/check-erase + the spec).** Contents, all
verified (per-symbol `CinPlusPriority` 13 batches / 0 errors, ~30 s solver; the member packs whole-file):
* `ResAgreeAtOutside(t1, t2, inp, S)` — the Hd-level relation — `ResFromLeavesOutside` + the
  `RA*Outside` congruence family (Refl/Sym/Trans/Progress/Read/Group/Anchor/Choice), mirroring
  `LL.LAAt*Outside`.
* `FirstEmptyPathA(rer, acts, inp): Option<seq<GroupAction>>` (mirrors `FS.ComputeTree`'s cases,
  `decreases ActionsFuel`, the spec verdict `LkVerdictL` for gates) + `FirstEmptyPathL`; `ApplyPath`,
  `Chain` (the virtual `GroupActionT` chain), `CINullableEmptyPathA` (CI-nullable ⟹ Some),
  `EmptyPathNeedsCont`, `PathActionsIn`/`ApplyPathOutside` (the path only touches the stack's groups).
* `EmptyLeavesA` — THE leaf characterization: every leaf of an `IsTree` tree at `inp` is `inp` or a
  strict suffix of it; a leaf AT `inp` exists iff the stack has an empty path; the FIRST one's map is
  `ApplyPath(path, Idx(inp), gm)` outside the look-confined `S` (`FirstAt` = first index at `inp`).
* `CinPlusPriority(rer, r1, cont, inp, gm, S, tplus, titer, tcont)`: for `PikeLkRegexRec(r1)`,
  `PikeLkActionsRec(cont)`, `CINullableL(r1)`, look bodies in `S`, and IsTree trees `tplus` of
  `[Areg(Q(true,1,Inf,r1))] + cont` at `gm`, `titer` of the star iteration `[Areg(r1), Acheck(inp),
  Areg(Q(true,0,Inf,r1))] + cont` at `GMReset(gidl, gm)`, `tcont` of `cont` at `gm`:
  `TreeRes(Choice(Reset(gidl); titer, Reset(gidl); Chain(FirstEmptyPathL(r1), tcont)), gm, inp)` and
  `TreeRes(tplus, gm, inp)` are both None or both Some with equal position and maps agreeing outside `S`.
  Proof = `EQ.LeavesConcat` (Linden's flat-map theorem) on `[Areg(r1)] + rest` and `[Areg(r1)] +
  [Acheck(inp)] + rest`, split at the first empty leaf; the check-chunk lemma `ChkChunk` (past `inp`
  the `Acheck` is a pass-through, at `inp` it kills), `EmptyLeafChunk` (the star at an empty leaf =
  the gm-independent iteration tree from the reset map + the gm-independent continuation),
  `LL.TreeLeavesFrameOutside` for the "up to S" transfers, and the P/Q head argument.
* Stated PER `gm` on `IsTree` trees. The `∀gm` form for the ATR site follows from
  `EL.ComputeTreeGmIndepLkRec` once `PikeLkRegex{,Rec}` admits the plus (its interim conjunct is
  exactly what excludes `Q(true,1,Inf,r1)` today) — that flip is rung C's first step.

**Verification lessons (this rung):** `EL.NoLkBrL` means look-AND-backref-free — use
`PikeLkActionsRec` + `ComputeTreeGmIndepLkRec`/`ComputeTrConfinedRec` for gm-independence and
confinement of look bodies; `IsTree` writes the star as `NoISub(delta,1)` while `ComputeTree`/`BoolTreeLk`
use `NoiPred(delta)` (assert equality); `:|`-bound `seq<Leaf>` locals need explicit types or Dafny reports
"type of the receiver is not fully determined"; sequence associativity (`I1 + (I3 + C)`) and `[] + I3`
are 60 s+ for z3 4.14 — state them; the two `TreeLeavesFrameOutside` quantified conclusions in the
context made the head-comparison batch storm although every assertion isolates — scope them into
`assert <instance> by { … }` blocks and `split_here` the case analysis.

**Next: rung B** — `TreeRepRE`'s `SQC(qid, true)` rule: `t == GroupActionT(Reset(gidl), Chain(p, tc))`
with `p == FirstEmptyPath(qm.bodies[qid], inp, qm.ov)` (an oracle-bit twin of `FirstEmptyPathL`, tied by
`OracleOk`) and `TreeRepRE(qm, tc, code, pc + 1, inp, b)`; `TreeRepDetermRE` extends trivially (the chain
is a function of `(qm, inp)`). The `QMap` needs a `bodies: map<int, L.Regex>` field (`QmapOk` pins
`qm.bodies[qid] == T.Translate(r1)`), built by a `M.BodiesOfRE(re)` twin of `M.QmOfRE`. Constructor sites
to touch (12): LiftSimCarriers 148/829/1123, LiftSimMain 453, LiftSimForward 214/319/905, LiftSimDeep 229,
FlipKeystone 209/212/285, LookBehindKeystone 287 — i.e. a field addition re-packs the whole lift-sim
band (~2.5 h of pack time): start it at the beginning of a session. Do rung E's spec-side half
(`FirstEmptyPath` over oracle bits + `OracleOk ⟹ == FirstEmptyPathL`) in the same rung, since the
`TreeRepRE` rule needs the oracle-bit version.

**2026-09-02 (evening) — RUNG B LANDED (commit `2ca414a` + tie fix `d0b0ac8`), RUNG C IN PROGRESS.**
Scope decision: stage 2 is being landed as **stage 2a = CIN-greedy `+` in the MAIN regex, outside
lookaround bodies, forward direction**; nulled plus inside look bodies and the lookbehind replay
direction are stage 2b (same rungs on the Lk tower + a mirror argument). The user confirmed the
engine is NOT to be changed (RegElk-faithful); §2.6 flags/Unicode is a won't-do for them.

Rung B (done): `AR.QMap.bodies: map<int, R.regex>` (`QmapOk` pins `qm.bodies[qid] == r1`;
`AR.StampBodyOk(qm, qid, r1)` = body in the table, `TransWf`, translates to `r1`, `LmapOk` — carried
by the CIN layout arm `NfaRepCinL` and discharged by `TransNfaRep` from `QmapOk`+`LmapOk`);
`TR.FirstEmptyPathR(qm, re, inp)` (oracle-bit twin of `FirstEmptyPathL`: anchors via `is_satisfied`
at `CtxOf(inp)`, lookarounds via the bit at `CpOf(inp)`, forced quantifiers = `RepeatPath(min,
Reset(gidl) :: p1)`); `TR.ChainT`/`PeelT` and the rule **tr_stamp** in `TreeRepRE`:
`SetQuantToClock(qid, true)` ↦ `GroupActionT(Reset(gidl), ChainT(p, tc))` with `p =
FirstEmptyPathR(qm, qm.bodies[qid], inp).value` and `tc` at `pc + 1` (determinism + PikeSubtree
extended; `GenStepRE`'s StepSpec has the `bb` case); `M.BodiesOfRE` + `BodiesOfREEntries` +
`QmapOkFromEntries`'s bodies hypothesis; ~25 constructor sites; `QmapOkLooksIrrel` also pins bodies.
Spec tie in the NEW file `linden-equiv-nulled-plus/src/NulledPlusTie.dfy` (module
`LindenElkNulledPlusTie` — kept out of `NulledPlus.dfy` because importing AR/TR there bloated
`CinPlusPriority`'s context into a timeout): `FirstEmptyPathAComp` (compositional in the
continuation, measure `RSizeL(r), MinOfL(r)`), `FirstEmptyPathLQuant`, `LkVerdictLBit`,
`FirstEmptyPathRL` (`!rer.multiline && TransWf(re) && LmapOk(re, qm) && OracleOkAt(rer, qm, inp)
==> FirstEmptyPathR(qm, re, inp) == FirstEmptyPathL(rer, Translate(re), inp)`).

Rung C (in progress, all per-file/per-symbol green so far except where noted):
* `AR.NfaRepStarCinL` — the star's CIN LOOP VIEW (residual `r1*` seen from the CIN loop's backward
  end fork `Fork(em+1, e1+3)` at `pc1 == e1+1`: clock-mark, BeginLoop, body, EndLoop, stamp at
  `e1+2`, exit `e1+3`), third disjunct of `NfaRepL`'s star arm guarded by `CINullableL(r1) &&
  greedy`; `NfaRepLStarCinIntro/Inv`, `NfaRepLStarLoopViews` (the case split every loop-view
  inversion now takes), `AR.NoTrueStamps(c)` + `NoTrueStampsRefutesStarCin/Cin` (look-body code).
* `WO.WalkOkRegF`: CIN head arm (a `min > 0` quantifier at a `Fork`: iteration at `x+2` with the flag
  dropped, continuation at `y+1` past the stamp) and the CIN loop-view conjunct (`skiparm == pc + 2
  ==> iteration at iterarm + 2, false`); `WalkOkFAtBeginLoop` (the old loop-view conjunct lands on
  the BeginLoop, vacuous there); destructors `WalkOkQuantCinHead`, `WalkOkLoopViewCin`;
  `WalkOkEntry`: `WalkOkCinRestF{,Nested}` (the CIN loop's rest at its EndLoop, KNOT at smaller fuel)
  and the CIN chain's `k == 1` bottom now establishes the head arm.
* `EL.PikeLkRegex{,Rec}` FLIPPED: the quantifier conjunct is gone; POSITIVE look bodies carry
  `NUL.NoNulledPlusL(r1)` (negative already did). `TranslateFragmentPikeLkRec` still takes
  `NoNulledPlusRE(re)` (weaken at rung G). Transport lemmas `FlipLPikeLkRec`, `RevLPreservesPikeLkRec`
  push the new look-arm conjunct through.
* NEW `NulledPlusBool.dfy` (module `LindenElkNulledPlusBool`): the ENCODING INVARIANT the construction
  threads — `EncOk(acts, inp, b) := exists b2 :: BoolEncoding(b2, inp, acts) && (b2 != b ==> b2 ==
  CannotExit && b == CanExit && ShieldedActs(acts))` (the only flag mismatch the construction creates
  is the do-while lift on a shielded stack, where both flags' trees coincide by `BoolFlagLiftRec`);
  step lemmas `EncOkTailReg/TailCheck/Expand/Read/Iter/IterLift/ConsPlus`, `Encodable`;
  `BoolTreeLkDetermNP` (copy of LiftSimCore's); THE BRIDGE `EncTreeIsTree` (`PikeLkActionsRec &&
  EncOk && BoolTreeLk(b, t) ==> IsTree at EVERY gm`); `BoolTreeLkEmptyPathSub` (the location lemma:
  when `r` has an empty path, a `BoolTreeLk` tree of `cont` sits inside `[Areg(r)] + cont`'s —
  PSize-smaller, confinement inherited); `RACongChainOutside`, `ChainTEqChain`;
  `CinPlusPriorityBool` (rung A on `BoolTreeLk` trees, ∀gm via the bridge); readouts
  `RAFirstLeafOutside`, `RAFirstLeafEmpty`, `EncOkNoChecks`.
* `ActionsTreeRepRE.dfy` (both towers): every family lemma now `requires LL.LkActsInS(acts, S)` and
  `requires NB.EncOk(acts, inp, b)` (AtBackFork: `BS.CanExit`) and concludes
  `NP.ResAgreeAtOutside(tstar, t, inp, S)` (the `LL.LAAt*` congruences → `NP.RA*`; the LK gate and
  seam steps go through `NP.ResFromLeavesOutside`); the four `assert !greedy` are gone: NEW
  `ATR_QuantCin{,Nested}` (extracted, E3-sectioned) = forced copies (as the do-while) + at `min == 1`
  the head-fork core: `tstar = Choice(Reset; subi, Reset; ChainT(p, subc))`, `subi` from the
  iteration list at `em+3`/CannotExit (its spec tree `ti` and the continuation's `tcont` located
  inside `tc` by `BoolTreeLkEmptyPathSub`), `subc` at `pcmid`, tr_stamp with `p` tied by
  `FirstEmptyPathRL`, relation by `CinPlusPriorityBool` + congruences; `ATR_QuantStar` and
  `AtBackForkTreeRep{,Nested}` take the CIN loop view (iteration at CannotExit from `em+3`, exit at
  `pc+2`, tr_plus at the backward fork); the min>0 refutation at a backward fork uses `NfaRepIncrL`
  to see the CIN head fork is forward. STATUS: per-file 56/0 apart from `ATR_QuantMin{,Nested}`
  timeouts (fixed by the extraction) and the fork refutation (fixed) — re-verification running.
* Lk tower (look bodies, stage 2a keeps them stamp-free): `AR.NoTrueStamps(code)` threaded as a
  `requires` through 30 lemmas (LiftSimCore giants ×4, `QuantHeadMinPosPinsSQC`/`QuantForcedContRep`/
  `QuantHeadSQCPin`, LiftSimOracle `ActionsTreeRepLkRE{,Rec}`/`TtLkAt*`, LiftSimChain
  `WalkPairLkAt*`, LiftSimGate `LiftInit{,C,CNested}`) and DERIVED in 9 LiftSimGate lemmas from
  `PSM.StaticOk{,Nested}RE` via LiftSimCore's `NoTrueStampsFromStatic{,Nested}RE` (`NI.StampFalseAt`);
  the `assert !greedy by {conjunct}` sites refute via `NfaRepLCinInv` + the stamp; every star
  loop-view inversion (14 sites) takes `NfaRepLStarLoopViews` and refutes/handles the CIN view.
* Consumers (LiftSimCarriers 222/496/656, LiftSimMain 548, MainTheorem ×3): `NB.EncOkNoChecks` for
  the entry stack, `NB.RAFirstLeafOutside`/`RAFirstLeafEmpty` for the readout.
* Dev loop: `scratchpad/devverify.sh PKG [dafny args]` with `DIRTY="<short names>"` passes SOURCE
  files for the dirty packages in the target's transitive deps and `deps/*.doo` for the rest
  (`deps.txt` = the workspace dependency lists; any package whose source constructs `AR.QMap` must be
  dirty once rung B is in, else its stale `.doo` fails to re-resolve).
Next: finish rung C verification (ATR file, LiftSimCore/Chain/Oracle/Gate per-symbol on the touched
lemmas), commit, then `LEM_BUILD_TIMEOUT=0 lem pack --jobs 3` in a WORKTREE (root `lem lock` first for
the new deps), then rung D.

### RUNGS D + E — DESIGN NOTES (written 2026-09-02 night, after rung C; nothing of this is coded)

**Where the stamp shows up in the simulation.** `PikeInvFullRE` pairs every VM thread with a tree
`t` (`TT.TreeThreadRE` at the thread's `(pc, exit_allowed)`) and a map `gm` with
`PIV.ThreadTracksGm(re, th, gm) := gm == GmOfLive(re, caps, look, quant)` (clock-filtered readout).
After rung B the tree at a `SetQuantToClock(qid, true)` pc is `GroupActionT(Reset(gidl), ChainT(p, tc))`
and the tree machine takes `|p| + 1` steps for the VM's one; the tree-side `gm` gains the chain's
writes, the VM's registers do not. So the readout must become
`GmOfLiveR(re, qm, str, caps, look, quant) := GmOfLive(...) ⊕ (the chains of the LIVE stamps)` where
"live" follows `filter_capture`'s clock traversal (a stamp whose quant clock is below an enclosing
quant's clock is stale and hidden, exactly like its captures — see the `((a?)+x|c)+` on "xc" trace in
the design section: a stale inner stamp reconstructs at old clocks and is filtered out). Define it by
the same AST recursion as `filter_capture` with the `maxclock` threshold: at `Re_quant(qid)`: if
`quant_clock < maxclock` skip; else if `a_cp[qid] == Some(cp)` apply
`ApplyPath(TR.FirstEmptyPathR(qm, body, T.InputAt(str, cp)), cp, ·)` then recurse into the body with
`maxclock := quant_clock`. Rung E ties this to the engine (`FNulledPlus`).

**Rung D obligations (PikeSimRE step lemmas, one per instruction, + `ThreadTracksGm`):**
* `SetQuantToClock(qid, true)` — NEW step lemma (`StampStepThreadRE`): VM writes
  `quant[qid] := (Some(cp), clock)`; tree side takes the Reset + chain steps (state it with `TrcRE`,
  the transitive closure, not `PikeTreeStep`); `GmOfLiveR(th') == ApplyPath(p, idx, GMReset(gidl,
  GmOfLiveR(th)))` because the new stamp is live (its clock is the max) and nested stale stamps
  inside `gidl` are hidden by the reset. Uses `TR.PeelChainT` + the tree machine's GroupActionT steps.
* `SetQuantToClock(qid, false)`: clears the stamp (`a_cp := None`) and resets `gidl` by clock —
  `GmOfLiveR(th') == GMReset(gidl, GmOfLiveR(th))`: outside `gidl` nothing changes (the stamp's
  chain only wrote `gidl` groups — `NP.PathActionsIn`/`ApplyPathOutside` from rung A), inside
  everything is hidden either way.
* `SetRegisterToCP(reg)` / `CheckOracle(lid)`: the write is OUTSIDE every live stamp's `gidl`
  (`ApplyPath` commutes), which needs the NESTING FACT below.
* Everything else (Consume/EndLoop/Anchor/Fork/Jmp/NegCheckOracle): no register change.
* THE NESTING FACT: `a_cp[qid] == Some(_)` (live) ⟹ `pc` is not inside `qid`'s block
  `[em+1, e1+2]` — every entry into the block passes the clock-mark at `em+1` (`SetQuantToClock(qid,
  false)`, clearing the stamp) or IS the stamp (which exits to `e1+3`); no jump lands inside a block
  from outside (`NfaRepRE` structure, as `NI.NestTopRE`/`EaColdOkRE` already exploit). Add it to
  `NI.ThreadNestRE` (`StampsOutsideRE(re, code, pc, quant_regs)`) with per-instruction preservation.
* The Lk tower (look bodies, `NoTrueStamps`) must keep working unchanged: `GmOfLiveR == GmOfLive`
  when no `a_cp` is set (`VmQuantFinal`, MainTheorem:130, is exactly that for the current gate) —
  prefer DEFINING `GmOfLiveR` so that it is syntactically `GmOfLive` under `forall k :: a_cp[k] < 0`
  (an `if NoStamps(quant) then GmOfLive(...) else ...`), so the ~300 `GmOfLive` sites in the LiftSim
  band need at most a `NoStamps` fact in scope rather than edits. Measure before committing to this:
  `GmOfLive` is mentioned in 18 files.
* The final readout (`FFindMatchPlus` = `FFindMatch` then `FReconstructPlus`): the best thread's
  `GmOfLiveR` is the spec's first leaf (from the invariant); rung E turns `FReconstructPlus`'s
  registers into `GmOfLiveR`'s value; the ~55 `M.FNulledPlusIdentity` sites become
  `GmOf(FReconstructPlus(th).regs) == GmOfLiveR(th)` (rung F). `VmQuantFinal`/`StampFalseAt` retire
  from the main-pass chain (they stay for look bodies).

**Rung E obligations (new member `linden-equiv-nulled-recon`):**
* `FNulledPlus(re, cap, lk, qt, plus_bcv, str, ov, dir)` walks the AST: for each quant with
  `a_cp[qid] == Some(cp)` it runs ONE `FAdvanceEpsilon` (`FNullInterp`) over
  `plus_bcv[qid] == compile_reconstruct_nulled(body)` from `FInitState(rc, cp, cap, lk, qt,
  start_clock = quant clock, ctx)` and then `FNulledChildren(body, …)` at the same `cp` for the
  nested stamps the run re-set. ReconstructNulled code is LOOP-FREE (chars → `Fail`, quantifiers →
  a clock-mark or the stamp or `Fail`, captures → the two `SetRegisterToCP`, looks → the gates), so
  the epsilon closure is a DFS over a DAG in priority order (Fork pushes the left arm first), with
  the `processed` dedup only dropping threads whose future is already known to fail (control flow
  depends on `pc`/`ea`/`cp`/`ov` only — no backrefs).
* Layout predicate `NfaRepNulledRE(r, c, pc1, pc2)` (ReconstructNulled mirror of `NfaRepRE`) +
  compiler adherence for `compile(r, l, ReconstructNulled)`; `tr_fail` (`Fail ↦ Mismatch`) is the
  only new `TreeRepRE` rule the code needs if the PikeSim machinery is reused; otherwise a
  standalone DFS semantics `RunNulled(c, pc, regs, cp, clock): Option<Regs>` with (i)
  `FAdvanceEpsilon` from one thread == `RunNulled` (the dedup argument), (ii) `RunNulled` over
  `NfaRepNulledRE` code == the fold of `TR.FirstEmptyPathR(qm, r, inp)` (structural induction with a
  continuation, like the ATR but tree-free). (ii) also needs: the accepted thread's writes carry
  clocks `> start_clock` (the closure increments the clock per processed thread), so
  `filter_capture` keeps them; nested CIN-greedy quants get `SetQuantToClock(qid', true)` at the
  same `cp` and their chains are added by `FNulledChildren` — matching `FirstEmptyPathR`'s
  `RepeatPath(min, Reset :: p1)` up to `ApplyPath` (repeated resets at one index are idempotent —
  a small lemma, `RepeatPathApply`).
* `ov` is unchanged by the null interpreter (no `WriteOracle` in reconstruct code); `cdn` is unused
  (no `CheckNullable`: CDN-greedy stays out of the fragment — add the fragment conjunct
  `NoCdnPlusRE` at rung G when `NoNulledPlusRaw` is weakened).
* Statement to land: `GmOfLive(re, FNulledPlus(re, cap, lk, qt, …).regs) == GmOfLiveR(re, qm, str,
  cap, lk, qt)` for threads satisfying the nesting fact and `StaticOk` (so `plus_bcv` is the
  canonical table `FFullCompilation(ast).f_plus_bc`, `M.FFullCompilationFacts`).

Order for the next session: E(ii)+(i) first as a standalone member (it is the riskiest piece and
independent of D), then D's nesting fact in NestInv, then D's step lemmas, then F, then G.

### 2026-09-03 — RUNG E CODED (new member `linden-equiv-nulled-recon`, in the scratchpad `wip/` until green); the D/E design REFINED; the pack gate fought through two infrastructure walls

**State of the tree.** `nullable-plus-greedy` = `723a253` (rung C complete + the walk-ok fix the pack
caught: `WalkOkLoopViewCin` lacked the explicit `WalkOk` asserts — per-symbol runs had verified ONE
symbol, the full file 40/0 after the fix). The rung-E member is NOT in the tree yet (it lives in
`<scratchpad>/wip/linden-equiv-nulled-recon`, stashed out of the main checkout so the gate pack can
run there); its `lemmata.toml` deps: reasoning, semantics-core, warblre, regex-engine,
equiv-actions-rep-re, equiv-nfa-rep-re, equiv-tree-rep-re, equiv-nulled-plus, equiv-pike-inv-re.
Restore into the tree with `git stash pop` (stash "wip nulled-recon + 63-member lock") once the pack
is green, then `lem lock` at the root (63 members) + `lem restore` in the member.

**Pack-gate walls (both solved, see memory `linden-dafny-memory-cap`):**
1. The toolchain dafny wrapper has forced z3 4.14.1 since 08-31; base members last verified under
   4.12.1 (`semantics-core`: `FlatMap.FlatMapApp` timeout + `StrictSuffix.dfy:262` "might not
   hold"; `oracle-sweep`: `AdvanceOvIndep` timeout) fail when REBUILT under 4.14. They only pass as
   "cached, unchanged" in the main checkout → run the gate in `~/code/Linden-Dafny` itself (a fresh
   worktree rebuilds them and fails). Open item: make those three proofs 4.14-robust.
2. `lem pack --jobs 1` passes no `--cores` (dafny defaults to 16 workers) and `--jobs 3` passes
   `--cores:16`; PikeInvRE's z3 workers reach 18 GB each → OOM at the 80G slice cap, reported as
   `dafny build exited 143 with no diagnostics`. The wrapper now pins `--cores:$DAFNY_MAX_CORES`
   (the gate uses 2); `pack/run_pack_main.sh` in the scratchpad is the launcher.

**Rung E, file 1 — `NulledRecon.dfy` (module `LindenElkNulledRecon`), 77/78 green (the last
obligation = the alt arm of `CompileNfaRepNulledRE`, being isolated with `hide *`):**
* `NfaRepNulledRE(re, c, pc1, pc2)` — the ReconstructNulled layout (mirror of `compile(_, _,
  ReconstructNulled)`: chars/NonNullable-forced quants → `Fail`; CIN-greedy `+` → `SQC(qid,true)`;
  CDN → `CheckNullable`+stamp (excluded by `NoCdnPlusRE`); generic forced quant → ONE
  `SQC(qid,false)` + body; captures/alt/con/lookarounds as in Progress mode) + `NfaRepNulledExtend`,
  `FreshNulledRE`, `CompileNfaRepNulledRE`, `CompileReconstructNulledLayout` (= region `[0,n)` +
  `Accept`), `RegionShapeRE`/`ReconstructCodeShape` (forward-only, no Consume/loop/oracle-write).
* `NulledWrites(qm, re, inp): Option<seq<Write>>` (`Write = WCap(reg) | WLook(lid) | WQuant(qid,b)`)
  — the register writes of the first accepting path, twin of `TR.FirstEmptyPathR` (nested CIN `+`
  contributes its stamp only; `FNulledChildren` chains its path later).
* `RegsFrom(rg, ws, cp, rg0, clk0, C)` = ∃ strictly increasing clocks in `(clk0, C]` with
  `rg == ApplyWrites(ws, cp, clks, rg0)`.
* THE DEDUP ARGUMENT, structural not global: `NulledRunRE` — from the region's head thread the
  closure reaches the region's exit with `ws + NulledWrites` applied (or no thread at all when
  `NulledWrites` is `None`), every pending alternative left inside the region being JUNK:
  `Dead(c, pc, B)` (every enabled path dies before `B`) or `Junk(c, pc, q)` (dies before `q` or
  lands exactly on `q`) for an already-processed `q <= exit`. `RestOk` bounds the pending list by
  the region HEAD (`th.pc >= pc2 || JunkOk(.., pc1) || Junk(.., pc1)`), which is what makes the
  con/capture/quant cases inherit without a "push-in" lemma; `JunkSkip` runs junk to exhaustion
  (marks only `[lo, hi)`, never accepts); `RestOkShift` transfers the bound to a later head. The
  alt-None case is the only place junk sits in FRONT of the next real thread (JunkSkip there).
* `NullInterpNulled`: one `FNullInterp` over `compile_reconstruct_nulled(re)` from a single
  thread accepts iff `NulledWrites.Some?`, keeps `ov`, and the accepting thread's registers are
  `RegsFrom(NulledWrites)`.
  Engine facts used: `init_thread` has `exit_allowed == false`; `get_instr` out of range is `Fail`;
  the end fork of the CIN scheme is `Fork(em+1, e1+3)` (the stamp is reached ONLY from the head
  fork's skip arm — the design section's "end fork re-enters at the stamp" was wrong).

**Rung E, file 2 — `NulledReconRegs.dfy` (module `LindenElkNulledReconRegs`, written, unverified):**
register sets (`CapRegsOf/QuantRegsOf/LookRegsOf`, `Inner*Regs` = what `FNulledChildren` may touch),
`ApplyWrites` pointwise algebra (`ApplyWritesFrame/OnTargets/Merge`, `NulledWritesTargets`),
`filter_capture` algebra WITHOUT fragment hypotheses (`FilterKeepsNonStart`, `FilterAtStartDep`: the
start slot of an outside-look capture depends only on that slot + the subterm's start/quant clocks),
`QidCinPlus`/`PlusTableOk` (the canonical table: CIN-greedy bodies' reconstruct code, `[]`
otherwise — `FCompileExtra` fills exactly those), `FNulledChildrenFrame`/`ReconAtFrame` (only
inner registers move, `ov` kept), `PathGroupsR`/`ResetGroupsR` (the groups the first empty path
captures / resets), `NulledWritesIffPath` (+ `NonNullableNoPath`, `CINullablePath`),
`FilterHiddenAfterChildren` (an off-path subtree whose clocks are `< K` stays all-absent at `K` even
after stale same-position stamps are re-run: their writes sit under their own stale quant node),
and THE ENGINE READOUT `EngineReadout` (+ per-arm lemmas `EngineReadoutCapture/Quant/Alt/Con`):
after `NulledWrites` at clocks `> K` and `FNulledChildren`, `filter_capture` at `K` reads a capture
as present iff it is in `PathGroupsR`, with range `[cp, cp)` and end clock ≥ start clock. The
induction never commutes a write past `FNulledChildren`: outside writes are pushed into the
subterm's INITIAL bank (`ApplyWritesOutsideCommute`, `MergeOn` + `MergeOnApply`).

**Rung E, file 3 — `NulledReconReadout.dfy` (module `LindenElkNulledReconReadout`, partial):**
`QChainFresh` (quant-clock-only chain freshness), `QLive` (stamp set + chain fresh, outside looks),
`StampApply` (= `ApplyPath(FirstEmptyPathR(body), cp, GMReset(gidl, gm))`), `LiveStampsGm` (the
`filter_capture` quant-threshold traversal with the stamp rule; captures always recursed, look
bodies never), `GmOfLiveR(re, qm, str, caps, look, quant) := LiveStampsGm(re, .., -1,
GmOfLive(..))`, `LiveStampsGmNoStamps`/`GmOfLiveRNoStamps` (= `GmOfLive` under no stamps: the
look-body tower is untouched), the SPEC READOUT `PathFoldR` (R1): `ApplyPath(FirstEmptyPathR.value,
cp, gm) == (gm - ResetGroupsR) + PathMap(PathGroupsR, cp)` with `RepeatPathEffect` (repeated
`Reset :: p` at one index = one copy). TODO: the top-level `ReconReadout` theorem
`GmOfLive(re, FNulledPlus(re, regs).regs) == GmOfLiveR(re, qm, str, regs)` — induction over `re`
mirroring `FNulledPlus`/`filter_capture`/`LiveStampsGm` in present mode; at a stamped quant reached
present: `EngineReadout` (via `StampReadout` = the `FNulledPlus` Some-branch) + `PathFoldR`; stale
stamped quant: hidden both sides; hidden capture: `LiveStampsGmStaleIdentity` (no chain-fresh stamp
inside, from invariant I1'' below); alt/con: frames.

**Rung D design, REFINED (supersedes the D notes above where they differ):**
* Liveness is CAPTURE-BLIND (`QChainFresh` reads quant clocks only), so the tree's `Open`/`Close`
  steps commute with `LiveStampsGm` trivially; the mark `SQC(Q,false)` and the stamp `SQC(A,true)`
  steps are GroupMap-algebra (`GMReset`/`ApplyPath` commute outside `gidl`, `PathIn`); `CheckOracle`
  is look-independent as before.
* Three per-thread invariant conjuncts (to add next to `ThreadTracksGm`):
  (I1'') `QLive(A) ==> PathPresentQ(re, cc, qc, -1, A)` (the capture ancestors of a live stamp are
  present — makes the capture-blind readout agree with `filter_capture`; established at the stamp
  from NestInv's ancestor claims via a `NestInvStampTrueSite` lemma mirroring `NestInvResetSite`;
  preserved: an Open at C makes no stamp inside C live (they were not `PathPresentQ` before);
  (I2) `QLive(A) ==> every capture/look/quant clock inside body(A) < qc[A]` (needed by
  `EngineReadout`'s `RegsStale`; true at the stamp by `ThreadClocksLE`);
  (I3) POSITIONAL: `qcp[A] >= 0 ==> pc is not in A's post-mark interior` — must be threaded through
  `NI.NestInvRE` as a `qcp` parameter with the claim `get_idx(qcp, qid) < 0` at BeginLoop / body /
  EndLoop / end-fork sites of every quant arm (NestInvStamp establishes it at the mark; NestInvAdvance
  carries it; the true-stamp step exits the block). This is the big mechanical job of rung D.
* `ThreadTracksGm(re, qm, str, th, gm) := gm == GmOfLiveR(re, qm, str, caps, look, quant)` (+ the
  three conjuncts); `ActiveRepRE/BlockedRepRE/BestMatchRE` gain `str`; PikeSimRE step lemmas get a
  NEW `StampStepThreadRE` (`SQC(qid,true)`: VM writes `(Some(cp), clk)`, tree takes `|p|+1` steps via
  `TR.PeelChainT`, readout = `ApplyPath(p, idx, GMReset(gidl, GmOfLiveR(th)))`).
* Rung F then is `GmOfLive(FReconstructPlus(th).regs) == GmOfLiveR(th)` = `ReconReadout` at the
  best thread (+ `GmOfLiveEqGmOf`); the ~55 `FNulledPlusIdentity` sites keep working for look
  bodies (`NoTrueStamps` → `GmOfLiveRNoStamps`). Watch: reconstruction also SETS look registers
  for lookarounds on the nulled path (`CheckOracle` in reconstruct code) — the L4/L5 look-capture
  replay must accept that, or stage 2a adds "no lookaround inside a CIN-greedy plus body".

**Dev loop for the member (until it is in the tree):** `wip/verify.sh` (file 1 against the
nulled-plus `.doo` snapshot + actions-rep-re/tree-rep-re SOURCES), `wip/verify2.sh FILE` (files 2/3
against `wip/doo2` = the pike-inv-re closure restaged AFTER the pack rebuilt pike-inv-re — the old
`.doo` embeds the pre-rung-B `AR.QMap` and will not resolve against the new sources). Keep dev jobs
at 2 cores while the pack runs.

**Later the same day (07:30):** file 1 is FULLY green (`CompileNfaRepNulledRE`'s alt arm needed the
`compile` unfolding moved into `CompileAltShape`, the assembly into `AltAssemble` under `hide *`, and
three more `split_here` between the recursive calls — each assertion was fast in isolation; the batch
was the problem). Files 2/3 are in the fix loop (register/readout checks ~10 min each at 2 cores).
PikeInvRE under the enlarged library: `CaptureWriteIdsOutsideRENested` reached 70 GB in ONE z3
un-split (1.9 GB with `assert {:split_here} true;` per arm — patched in the main tree, uncommitted);
a second hog exists (pack died again at 2 workers) — being located with `scratchpad/piv/profile.sh`
(one worker, `--progress Batch`, RSS sampler that kills dafny AND its z3 children above 55 GB; kill the
children — an orphaned z3 kept 55 GB of the slice after its dafny died).
**Hypotheses rung F must discharge for `ReconReadout`** (all on the annotated main regex `re` and
the best thread's registers): `T.TransWf`, `PIV.CapUnique`, `PIV.QuantUnique`, `NRR.LookUnique`
(NEW predicate: lookaround ids pairwise distinct — needed because writes to the same look register
would not commute in the con/alt readout; derive it from the annotation like `QuantUnique`),
`NRC.NoCdnPlusRE`, `NRR.PlusTableOk(re, plus_bcv)` (from `FFullCompilation`'s `f_plus_bc`), `ov ==
qm.ov`, `NRR.WfRegs`/`NRR.CapValWf` (value set <==> clock set) / `NRR.Covers` / `NRR.LookCapsAbsent` /
`OnlyCapIdsSet`, and `StampsLocal(qm, re, str, rg, -1)` (= the rung-D invariants I1''/I2 plus
"stamped ⟹ CIN plus, in range, body in `qm.bodies`").


### 2026-09-04 — the PACK OOM ROOT-CAUSED AND FIXED (`FilterResetFrame` family); RUNG D STARTED (`NestStampRE`, the positional stamp invariant)

**The pack gate was NOT failing on a proof — it was failing on solver MEMORY.** `lem pack` reported
`dafny build exited 143 with no diagnostics` on `linden.equiv-pike-inv-re` (SIGKILL: the 80 G
`dafny.slice` cap). Profiling one worker with an RSS sampler (`scratchpad/piv/`) pinned it on ONE
batch of `LindenElkPikeInv.FilterResetFrameNested` (batch 2 of 6) growing past 47 GB, with the
twin `FilterResetFrame` right behind it — while EVERY assertion of the same lemma verifies in under
a second under `--isolate-assertions` (166/166 at a 60 s limit). Pure batch/context blow-up under
z3 4.14, exactly the shape [[dafny-hot-predicate-inline-cost]] describes.

**The fix (commit below): every match arm is its own lemma.** `FilterResetFrameNested` and
`FilterResetFrame` are now three-line dispatchers over `FRFNestedLook/FRFNestedCap/FRFNestedQuant`
and `FRFLook/FRFCap/FRFQuant` (`decreases r, 1` on the parent, `decreases r, 0` on the arms, so the
mutual recursion parent -> arm -> parent(child) is accepted). Result: the whole
`FilterResetFrame*` family verifies **8/0 in ~10 s at a 1.3 GB peak** (was 47.8 GB and rising).
`FilterResetFrame` was ALSO given the `hide NR.LookBehindFragmentRE` its `*Nested` twin has — and
that made `FRFQuant` a 25 GB hog on its own (the un-hidden lemma verifies whole in 7 s), so the hide
was reverted: hiding a fragment predicate is a fix for `NestedFragmentRE`, not a general rule.
A REAL hole surfaced once the memory noise was gone: `FilterResetFrameSeqNested` had inherited
yesterday's `hide NR.NestedFragmentRE` with no matching reveal, so five `*Nested` callee
preconditions were unprovable — fixed with one
`assert NR.NestedFragmentRE(r1) && NR.NestedFragmentRE(r2) by { reveal NR.NestedFragmentRE; }`.

**Rung D, piece 1: `NestStampRE` — the positional stamp invariant (new file
`linden-equiv-nest-inv/src/NestStamp.dfy`, module `LindenElkNestStamp`).**
The readout `GmOfLiveR` replaces a LIVE stamp's body groups wholesale by the reconstruction chain,
so a capture write must never land inside a live stamp's body — and that is a POSITIONAL fact, not
a clock fact (checked: no clock argument can give it; a stale-set stamp inside an enclosing loop is
killed by `QChainFresh`, but a stamp set on THIS pass is not).

* Design decision: a stamp-only MIRROR of `NI.NestInvRE` rather than a `qcp` parameter threaded
  through it. `NestInvRE` is the hot predicate whose inline size already forced `NestInvGenRE`/
  `NestInvCinRE` out of line and whose 440 call sites span five packages; the mirror reads NO
  register bank, so every capture/look write is the SAME edge for it (one `NestStampAdvanceRE`
  covers all of them) and the existing 140 lemmas stay untouched and cached.
* Contents: `NestStampRE` + `NestStampMinRE`/`NestStampOptRE`/`NestStampGenRE`/`NestStampCinRE`
  (claims placed exactly where `NestInvRE` claims `qc[qid] >= mx`, plus the whole forced-copy chain
  past its first mark) and `NestStampTopRE`; Inv/Intro for the two named arms; entry lemmas
  (UNCONDITIONAL — every block-head site is a fork/mark/capture-open, which claim nothing);
  `StampsWeaken` monotonicity (clearing stamps only strengthens the invariant, which is what makes
  the clock-mark step nearly free); `StampEdgeRE` (= `NI.StepEdgeRE` widened to the capture OPEN
  write) + `NestStampAdvanceRE`; `NestStampQuantWriteRE` for BOTH `SetQuantToClock` steps (the mark
  clears `qid0`, which is what the post-mark sites claim; the true stamp sets it and EXITS the block
  at `e1 + 3`, and every enclosing claim is about a different quantifier by `QuantUnique`); and the
  payoff `NestStampOpenSiteRE`: a capture open site is in `CapIds(re)` and outside
  `CapIds(QidBody(re, A))` for every STAMPED `A`.
* Layering note (this is why the mirror lives in nest-inv, not pike-inv-re): `nest-inv` DEPENDS on
  `pike-inv-re`, so `GmOfLiveR` and the `LiveStampsGm`-commutation lemmas must move DOWN into
  `pike-inv-re` (they use only `AR`/`TR`/`NP`/`filter_capture`, all already in its closure), stated
  with the abstract hypothesis "the written group is outside every stamped quantifier's body";
  `pike-sim-re` (above both) discharges that hypothesis with `NestStampOpenSiteRE`. The rung-E
  definitions `QChainFresh`/`QLive`/`StampApply`/`LiveStampsGm`/`GmOfLiveR` currently live in
  `linden-equiv-nulled-recon` (which is ABOVE pike-inv-re) and have to be moved down first — that is
  the next step (D0), after which `ThreadTracksGm` becomes `gm == GmOfLiveR(re, qm, str, ...)`.

**Later (2026-09-05, commit `070841c`): the same treatment for the `LookBehindFragmentRE` twin.**
With the `*Nested* twin fixed the pack went `exited 143` (OOM) -> 312 verified / 2 time outs ->
309 verified / 1 time out, the survivor being the UN-extracted `FilterResetFrame`: 900 s+ in the
whole-file run although it verified per-symbol in seconds, and all 100 of its assertions isolate in
25 s TOTAL — batching, not a missing fact. It is now `FRFLook`/`FRFCap`/`FRFQuant` per arm, with
`FRFQuant` dispatching to `FRFQuantSame`/`FRFQuantOther` (both branches in ONE VC was still 900 s+),
`FRFBodyReset` for the body reasoning, `hide NR.LookBehindFragmentRE` + ONE reveal for the child, and
the two explicit `filter_capture` unfoldings the twin has had since 09-03. Termination is
three-level: parent `decreases r, 2`, arms `r, 1`, branch lemmas `r, 0`. Green: FRF* 18/0,
`FilterResetFrame` family 8/0, both in seconds — and **`linden.equiv-pike-inv-re` PACKS: 320
obligations, 5m 27s** (it had not packed since the z3 4.14 switch).

**Recipe, for the next hog** (also in memory `dafny-batch-memory-hogs`): profile with `--cores=1
--progress Batch` + an RSS sampler to name the lemma and batch; then (1) one lemma per match arm,
(2) if an arm still times out, one lemma per BRANCH, (3) if it still times out, state the content on
the CHILD alone. `--isolate-assertions` is the diagnostic that tells you which of these you need (all
assertions fast => batching), never the fix. Do NOT run dev verification while `lem pack` runs: they
share the 80 G slice and the loser is SIGTERM'd (RC=143).

**2026-09-05, the layer above: `nest-inv` had to be made 4.14-robust too (commits `bf7944b`,
`ccdc65e`).** Changing `pike-inv-re` invalidates the cached artifact of EVERY member above it, so
`nest-inv` was rebuilt for the first time since the z3 4.14 switch — and OOMed the slice twice, on
two different symbols (`NestInvOpenSite`, then `NestInvStamp` at 31.8 GB). Rather than chase them one
11-minute pack run at a time, `{:split_here}` is now on ALL 352 match arms of the file's LEMMAS
(predicates untouched — it is a statement, not an expression). Whole file at one worker: **611
verified, 0 errors, 37 min, peak z3 18.5 GB**, nothing above 30 GB; the member packs in 20m 22s
(241 obligations). `NestStamp.dfy` moved to its own member `linden-equiv-nest-stamp` (per-file
layout, 64 members) — note this does NOT keep `nest-inv` cached, since the invalidation comes from
pike-inv-re, but it keeps the new work isolated.

**Expect the same for every member above pike-inv-re** (pike-sim-re, the lift-sim band,
main-theorem, ...): they have all been passing as "cached, unchanged" under 4.14 and are being
rebuilt for the first time now. The tool is the profile script `scratchpad/ni/full.sh` (one worker,
`--progress Batch`, an RSS sampler that names any symbol crossing 30 GB and kills only that worker so
the run continues) — one pass enumerates the whole file's hogs.

**2026-09-05, what the cache was hiding (commits `24e81b1`, `e4c1c40`, `ef798dd`).** Every member
above pike-inv-re is being rebuilt for the first time since the z3 4.14 switch AND since rung C, and
the sweep found both perf and CORRECTNESS problems:
* `oracle-entry` — a "hang" (4 h elapsed, 35 s CPU, z3 child idle) that was really a 56.8 GB z3
  worker OOM-killed by the slice, leaving dafny blocked on a dead solver. `OracleOkFromColumns`'s
  doubly-nested `forall` is now `OracleOkAtLid` (one position, one lookaround) + `OracleOkAtCp`
  (one position): 47/0 in under 100 s. **An OOM inside the cgroup presents as a HANG, not a kill** —
  check CPU TIME of dafny AND its z3 children, not just that the process exists
  (`scratchpad/pack/watchdog.sh`).
* `pike-sim-re` — `PreserveForkCase{,Nested}` timed out at 900 s in the gate while passing standalone
  in under 100 s (the second worker tips it); split prefix / forward arm / backward arm. 155/0.
* `tree-mirror-lk` — **TEN REAL ERRORS, not timeouts.** Rung C removed the §2.5b interim quantifier
  conjunct from `EL.PikeLkRegexRec`, but `QuantMinHelper` and `QuantStackInvLk` still REQUIRED
  `min > 1 && delta.Inf? && greedy ==> NonNullableL(r1)`, which no caller can supply any more. The
  bodies never needed it (`PikeLkRegexRec(q1)` follows from `r1`'s under the flipped definition);
  dropping both requires gives 100/0. The member had been "green" on a stale artifact since 09-02 —
  the same class of gap as [[linden-per-symbol-wf-gap]], one level up: a CACHED MEMBER proves nothing
  about the sources it was built from once a dependency's definitions change.

**2026-09-06 — main-theorem's six gate time outs, all fixed** (commits `4fb9c84`, `1677a5d`,
`900f1e2`, `3ebbebe`). 645 verified / 0 errors / 6 time outs -> all green; peak z3 8.3 GB, so these
were SLOW QUERIES, not memory hogs. Three causes:
* **duplication**: `FFullCompilationFacts` and `MainExtraction` were verbatim copies of siblings with
  strictly weaker hypotheses (`*Nested` twin; `MainExtractionFromClosed`, 82 of 84 statements) —
  delegate, 900 s -> 0.29 s, ~80 lines deleted. Dropping the register half also made
  `NegLooksLookFreeRE` unnecessary in `FromClosed`, which is what allowed the delegation.
* **assumed context**: NEW `CapArrayFromRegs` holds the 76-line register/filter half with NO
  tree/spec machinery in its contract — the same statements were >900 s inside
  `MainExtractionFromClosed` and are under 100 s there. `hide` cannot fix this; only a narrower
  contract can.
* **matching loop**: `R.annotate`/`R.max_group`/`R.max_lookaround`/`R.max_quant` in the hypotheses —
  hiding them took `assert CM.ThreadRegsWf(thread, ncap, ...)`, a VERBATIM restatement of the
  lemma's own `requires`, from >900 s to instant.
* the three `FLookLoop*` giants needed none of that — 188 per-step `{:split_here}`, 225/0.

### 2026-09-06 — **THE GATE IS GREEN: `workspace packed: 64 members`, `PACK rc=0`**

First clean pack since 09-03, and the first in which EVERY member was actually rebuilt under z3 4.14
(they had been passing as "cached, unchanged"). Rung D piece 1 (`linden-equiv-nest-stamp`) and rung E
(`linden-equiv-nulled-recon`) are therefore gate-verified, not just per-symbol green.

Getting there took 22 commits, almost all of them proof-ENGINEERING rather than proof content: one
`pike-inv-re` change invalidated the whole tower above it, and every member above it then had to be
made 4.14-robust. Two REAL defects fell out of that sweep — a `hide` with no matching reveal in
`FilterResetFrameSeqNested`, and rung C's stale interim conjunct in `tree-mirror-lk` (ten
unprovable preconditions, "green" on a cached artifact for three days).

**The playbook, in the order to try it** (also in memory `dafny-batch-memory-hogs` and
`dafny-isolate-assertions-policy`):
1. `grep` the named lemma for `{:isolate_assertions}` and REMOVE it — four lemmas this sweep
   (`OracleColumnNested`, `DeepFindRecLB`, `ForwardFindRecFwdDeep`, `ReverseCDeepFull`) timed out
   BECAUSE of it: it splits the body into ~1000 assertion queries whose AGGREGATE blows the 900 s
   budget while no single assertion is slow.
2. Diff the lemma against its `*Nested`/`*FromX` twin — twice the body was a verbatim copy of a
   sibling with strictly weaker hypotheses, and delegating fixed it (900 s -> 0.29 s).
3. Per-step `{:split_here}`. Granularity is the knob: 1 batch times out, ~1000 times out in
   aggregate, 100-200 works. NEVER insert one directly before a `case` arm (parse error).
4. If a batch is a VERBATIM restatement of a `requires` and still slow, the cost is the assumed
   context: `hide` the RECURSIVE FUNCTIONS THE HYPOTHESES MENTION (`R.annotate`, `R.max_group`,
   `NR.NestedFragmentRE`, ...), not the ones the goal mentions.
5. If that is not enough, EXTRACT the work into a lemma that never sees the heavy machinery
   (`CapArrayFromRegs`, `OracleOkAtLid`, `FRFBodyResetNested`). `hide` cannot shrink an assumed
   context; only a narrower contract can.

**Next: rung D0** — move `QChainFresh`/`QLive`/`StampApply`/`LiveStampsGm`/`GmOfLiveR` down from
`nulled-recon` into `LindenElkPikeInv`, then `ThreadTracksGm := GmOfLiveR`, the commutation algebra,
and the PikeSimRE step lemmas. Note that touching `pike-inv-re` again re-triggers the whole
tower rebuild — but every member above it is now 4.14-robust, so it should be a clean ~2 h pack.
