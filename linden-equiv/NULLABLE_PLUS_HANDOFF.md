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
