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

### 2026-11-04 — **RUNG D1: the simulation invariant is reconstruction-aware** (`ThreadTracksGm := GmOfLiveR`)

**Environment change first: `dafny.slice` is now 24 GiB** (was 80; a vLLM server holds the rest of
the box). Every dev run is ONE z3 worker under a sampler that kills the run at 21 GiB
(`<scratchpad>/dv.sh`; multi-range driver `dvmulti.sh`). Peaks this session: pike-inv-re new
section 2.4 GiB, nest-stamp new lemmas 6.6 GiB, pike-sim-re ranges ≤ 2.5 GiB once the stamp
invariant went opaque (see the hog below). A gate pack must run with `DAFNY_MAX_CORES=1`.

**Also recorded only in commit messages until now (2026-09-06):** D0 (`6472689`, `404b0de`: the
readout defs moved into `LindenElkPikeInv`, gate 64/2224/rc=0) and the Open commutation
(`3319066`, `LiveStampsGmOpenCommute`, forcing `QuantUnique` and `StampBodiesOk`).

**What D1 is.** The per-thread tie is now the reconstruction-aware readout, and every register
step carries it. The interim gate (`NoNulledPlusRE` in `StaticOkRE`, `StampFalseAt`) is UNCHANGED,
so a TRUE stamp is still unreachable in the simulation — D2 adds that step. Layer by layer:

* **pike-inv-re** — `ThreadTracksGm(re, qm, str, th, gm) := T.TransWf(re) && gm == TieGm(…)`, `TieGm`
  the OPAQUE wrapper of `GmOfLiveR` (copied registers get the tie by congruence; `TieGmLiveCong`
  for the look-bank write);
  `ActiveRepRE`/`BlockedRepRE` gain `str`, `BestMatchRE` gains `qm, str` (it is `ThreadTracksGm` of
  the best thread). Bridges: `ThreadTracksGmNoStamps`, `BestMatchRENoStamps`, `InitNoStamps`.
  THE GENERAL COMMUTATION ALGEBRA (the readout only ever overrides groups of stamped bodies, and
  WHICH stamps it applies depends on the quant banks only — never on the map):
  `GMUpdateCommute` (disjoint actions commute) → `ApplyPathActCommute` → `StampApplyActCommute` →
  `LiveStampsGmActCommute` (any action disjoint from every stamped body passes through;
  `StampedDisjoint`) → `LiveStampsGmPathCommute`, `LiveStampsGmCloseCommute`; absorption
  `ResetAbsorbsAct/Path`, `LiveStampsGmResetAbsorb` (a reset covering a subterm's groups erases its
  readout); `LiveStampsGmCong`, `LiveStampsGmAllStale`; and the two QUANT WRITES —
  **`LiveStampsGmMark`** (the clock mark: readout of the reset = reset of the readout) and
  **`LiveStampsGmStamp`** (the true stamp: the readout gains exactly `StampApply` under the new
  bank; needs `QChainFresh` under the new clocks, `q0` outside looks, `NoStampedAbove`, the chain's
  `p.Some?`). `QmapOkBodyAtQid` + `QmapOkStampBodies` make `StampBodiesOk` STATIC (from `QmapOk`).
* **nest-stamp** — `NestStampCapSite{Min,Opt,RE}` (register-generic copy of the open-site family:
  Open AND Close sites are outside every stamped body) and `NestStampQuantSite{Min,Opt,RE}`
  (`PIV.NoStampedAbove` at every `SetQuantToClock(q0, _)` site), with top wrappers.
* **pike-sim-re** — `ThreadNestRE` carries the stamp invariant as the OPAQUE `StampTopRE`;
  the six register step lemmas (`Open/Close/ResetStepThreadRE{,Nested}`) are now gm-FREE (they state
  `GmOfLive(after) == GMUpdate(a, GmOfLive(before))`; `LiftSimCore`'s dispatchers want exactly
  that) and advance `StampTopRE`; narrow readout lemmas `ReadoutCapWriteRE` (Open/Close) and
  `ReadoutMarkRE` (the mark) are the one call each Preserve case spends on the readout.
  `BlockedRepSnocRE`/`BlockedToActiveRE` gain `str`; new dep `linden.equiv-nest-stamp`.
* **consumers** — call sites rewritten mechanically (`<scratchpad>/addargs.py`, paren-aware);
  `MainTheorem`'s three `ReplayCapIsBodyLeaf*` bridge `BestMatchRE` back to `GmOfLive` with the new
  `FreshBestNoStamps` (`FFindMatchQuantFinalAny` under the interim gate) + `PIV.BestMatchRENoStamps`.

**Two hogs, one fix (AGENTS.md §2.4 in action).** (1) `NST.NestStampTopRE` TRANSPARENT inside
`ThreadNestRE` took `OpenStepThreadRENested` past 10 GiB in one batch (its non-nested twin passed):
the stamp invariant is a recursive existential predicate the size of `NI.NestInvRE`. (2) `GmOfLiveR`
TRANSPARENT inside the tie took `PreserveForkCaseNested`'s forward arm from 13 GiB to 23.8 GiB in
five seconds (`LiveStampsGm` is recursive over the regex; the nested-fragment context unfolds it
eagerly). Both now sit behind opaque wrappers (`StampTopRE` in pike-sim-re, `TieGm` in pike-inv-re),
revealed only in the narrow helpers. Result: pike-sim-re 23 694/0 in three ranges. **Any new
per-thread conjunct of this size goes in opaque.** Watch item: the Fork cases' backward-arm batch
(`PreserveForkCase{,Nested}`, batch 5) still peaks at 13.3 GiB, which fits one worker but not two;
split it before raising `DAFNY_MAX_CORES`.

**Next: D2 — the true-stamp step.** (1) nest-inv-level site lemmas for `SetQuantToClock(q, true)`
(twins of `NI.NestInvResetSite` → `PathPresentQ` + outside-looks, and of `NI.NestInvStamp` → the
block exit at `e1 + 3`; only the CIN arm's `e1 + 2` is a base case, so the copies are short — put
them in nest-stamp to keep nest-inv's 37-minute file cached); (2) pike-inv-re: `PathPresentQ ⟹
QChainFresh` after the write; (3) pike-sim-re: `StampStepThreadRE` (GenStep's `tr_stamp` clause),
`ReadoutStampRE` (narrow, `LiveStampsGmStamp`), `ChainStepsRE` (`TrcRE` through `ChainT(p, tc)` —
`PikeTreeStep`'s `pts_active` is allowed on seen trees, and `SeenInclusionRE` is monotone in the
seen set, so the extra chain trees are harmless), `PreserveStampCase{,Nested}`; `PreserveResetCase`
dispatches on `bq` and ensures `TrcRE`, and its `NI.StampFalseAt` call retires. Then F, then G.

### 2026-11-04 (night) — **RUNG D2: the true stamp in the simulation; PikeSim is GATE-FREE** (`dc67c94`)

`SetQuantToClock(qid, true)`: the VM writes `(Some(cp), clk)` and falls through; the tree takes
`|p| + 1` steps (`Reset(gidl)`, then the chain of the body's first empty path); the tie gains exactly
that chain. Every piece verified first or second run, one z3 worker:

* **nest-stamp** (clock side, nest-inv untouched): `TrueStampSite*` (twin of `NI.NestInvResetSite`,
  generated from its source: every FALSE mark becomes a contradiction, the CIN arm's `e1 + 2` is the
  base case) and `TrueStampBack*` — the thread is RE-POSITIONED to the CIN end fork `e1 + 1` under
  `qc[q0 := clk]` (no claim outside q0's block reads q0's clock; the end fork's own claim holds for the
  fresh clock), so `NestInvTopTrueStamp` finishes with the already-verified `NI.NestInvAdvance` along
  the end fork's exit edge. This avoided a 450-line twin of `NI.NestInvStamp`. 3854/0, 11 GB peak
  (`TrueStampBackRE`'s first batch — split the `Re_empty` arm if it ever grows).
* **pike-inv-re**: `PathPresentQChainFresh` (the stamp is LIVE when set).
* **pike-sim-re**: `StampStepThreadRE{,Nested}`, `ReadoutStampRE`, `ChainStepsRE` (`TrcRE` through
  `ChainT`; `pts_active` is allowed on seen trees and both inclusions are monotone in the seen set),
  `PreserveStampCase{,Nested}`, `PreserveMarkCase{,Nested}` (the gate-free mark) and the dispatcher
  `PreserveQuantCase{,Nested}` (`TrcRE`). **`InvariantPreservationRE{,Nested}` dispatch through it and
  every pike-sim-re lemma now requires `StaticCoreRE` = `StaticOkRE` without `NoNulledPlusRE`** —
  except `PreserveResetCase{,Nested}`, kept as gated wrappers (lift-sim-gate chains them with
  `TrcCons`). Whole file 27 432/0 in three ranges, peak 3.8 GB.
* Hog: the `StaticCoreRE` context took `PreserveForkCase`'s forward-arm batch past 21 GB; per-step
  `{:split_here}` in both arms of both Fork cases took it to 3.6 GB (the D1 watch item, 13.3 GB, is
  gone with it).

**What D does NOT yet give** (rung F): the FINAL readout. `BestMatchRE` now ties the best thread's
registers to the tree's leaf through `TieGm`/`GmOfLiveR`; turning that into the engine's answer needs
`GmOfLive(FReconstructPlus(th).regs) == GmOfLiveR(th)` (rung E's `ReconReadout` top-level theorem,
still TODO in `NulledReconReadout.dfy`) at the best thread, then the `FNulledPlusIdentity` sites.
The lift-sim band's own ties (`GmtTieOutside`, look bodies) are F as well. G drops the gate conjuncts.

### 2026-11-05 — **THE GATE IS GREEN WITH D1 + D2: `workspace packed: 64 members`, `PACK rc=0`, at ONE z3 worker under the 24 GB slice**

Four pack runs (`DAFNY_MAX_CORES=1 LEM_BUILD_TIMEOUT=0 lem pack --jobs 1` in the main checkout,
under `<scratchpad>/pack1.sh`: watchdog kills the pack above 22 GiB or after 25 min without solver
CPU — a cgroup OOM presents as a HANG). Every member above pike-inv-re was rebuilt; total ≈ 11 h of
single-worker time. Each stop was a PERFORMANCE hog, never a wrong proof, and each fix is a commit:

| stop | symbol | cause | fix | after |
|---|---|---|---|---|
| nest-stamp, 23.8 GB | `NestStampQuantWriteRE` (rung D piece 1, 09-04 — passed the 80 GB slice unmeasured) | arms heavy in one VC | one lemma per arm, the quant arm one per scheme (`QWQ*`), ladder 2/1/0 | 9.9 GB (`b0aa59f`) |
| main-theorem, 23.9 GB | `FAdvanceEpsilonAncSet` (546 lines, no split) + `FConsumeAncSet`, `LookCheckDirectREGen` | one batch per lemma | split per arm / per `assert … by` | 5.3 GB (`60e3c71`) |
| lift-sim-oracle, 900 s | `OracleColumnNested`'s lookahead row | the ASSUMED context (each fix moved the slow batch one line) | both directions out as narrow helpers; `hide *` in the engine-side one | 142 s, 5.7 GB (`eae20d8`) |

Lessons (also in memory `dafny-batch-memory-hogs`): measure PEAK MEMORY per member at one worker
whenever the slice shrinks — the 80 GB cap had hidden two 20 GB batches since September; the pack's
`.doo` library inputs make z3 behave differently from a dev run against SOURCES (main-theorem: 12 GB
in dev, 22+ GB in the pack), so verify fixes against the freshly packed `.doo` deps
(`<scratchpad>/freshlibs.sh`); `--filter-symbol` is single-valued and a trailing dot means "ends
with"; never wait on `pgrep -f` of a string your own shell contains.

**State:** `nullable-plus-greedy`, rung D COMPLETE (D0, D1, D2) and gate-verified. The interim gate
conjuncts are still in place outside pike-sim-re (rung G). **Next: rung F** — the final readout.

### 2026-11-05 (cont.) — **RUNG F BEGUN: F-a (live-stamp invariant) + F-b (THE FINAL READOUT) landed**

**Correction to the plan above.** The main theorem does NOT read machine A's tie: `MainTheoremL5`
goes `L3aCompositeCloseRec` → `BestTieLkNestedTop` → `GmtTieOutside`, all on machine **B** (the
lift-sim band's LK-aware tree, `TreeRepLkRE`/`TtLk`, still `GmOfLive`, still gated: no `tr_stamp`,
`AR.NoTrueStamps(main code)` required by the B constructions). Rung D made machine A
reconstruction-aware; the final readout needs, in addition, the B machine (F-c below) — OR, for
lookaround-free regexes, no B machine at all (F-d0 below). And rung E's `ReconReadout` was already
PROVED (the "TODO" comment in `NulledReconReadout.dfy` §4 is stale).

**F-a (`3c4b16e`) — new member `linden-equiv-stamp-live`** (deps regex-engine + pike-inv-re):
`SL.StampLiveOk(re, cc, qc, qcp)` = every SET stamp is outside looks, has a STALE body (all
capture/quant clocks inside `QidBody` below the stamp's clock — rung E's `RegsStale`) and, while its
chain is fresh, PRESENT capture ancestors (`PathPresentQ`): exactly `NRO.StampsLocal`'s per-stamp
facts. Pure register algebra; the positional input arrives at the write sites
(`NST.NestStampTop{Cap,Quant}Site`, `NST.TrueStampSite`) and the clock discipline (every write's clock
is above every stored one). Key lemma `QChainFreshAncGe`: a mark of an ENCLOSING quantifier makes a
stamp's chain stale for good. pike-sim-re: `ThreadNestRE` carries `SL.StampLiveOk` (opaque atom),
narrow helpers `StampLive{Cap,Mark,Stamp}RE` (one call per Preserve case), and `PikeInvFullRE`
records `BestLiveRE` (StampLiveOk + LooksCapUnset) for the best thread at Accept. **`BestLiveRE`
must be opaque**: transparent, its quantifier in every `PikeInvFullRE` unfolding took
`PreserveForkCaseNested`'s backward-arm batch past 12 GB (2.7 GB opaque). Whole file 235/0, 206 s,
6.0 GB, one worker, against packed `.doo` deps.

**F-b (`be74322`) — new member `linden-equiv-final-readout`** (leaf):
* `FinalVm.dfy` — VM-only `FFindMatch` induction (`CM.FFindMatchLookCpOk`'s shape):
  `FV.RegsFinalOk(t, |str|, Q)` = every set quant cp is a true-stamp record on a qid of `Q`, inside
  the string; capture values set exactly with their clocks (`NRR.CapValWf`). Under the gate `Q == {}`
  and this is `M.QuantRegsFinal`'s value half.
* `FinalReadout.dfy` — `TrueStampCin*`/`TrueStampsInCin` (the true-stamp inventory, twin of
  `NI.StampFalseAt` without the gate: `Q = CinQids(re)`); `FCompileExtraPlus`/`PlusTableOkFull`
  (`FFullCompilation(ast).f_plus_bc` is rung E's canonical table — needs `NoCdnPlusRE(ast)`:
  `FCompileExtra` fills CDN-greedy slots too); `LookUniqueBridge` (`LTB.LookUnique ⟹ NRR.LookUnique`);
  and **`FinalReadout`**: from `PSM.BestLiveRE`, `FV.RegsFinalOk`, `QmapOk`, `Covers`/`WfRegs`/
  `OnlyCapIdsSet`: `GmOfLive(lazy_prefix(ast), FReconstructPlus(best, ast, ...).regs) ==
  GmOfLiveR(lazy_prefix(ast), qm, str, best.regs)`, view untouched (the prefix quantifier, qid 0,
  `min == 0`, is never stamped). 25/0, 37 s, first run.

**Next — two routes, both rung F:**
* **F-d0 (recommended next): a LOOKAROUND-FREE main theorem, machine A only.** For `S =
  CapIdsInLooks(re) = {}` machine A suffices: `M.FindMatchBodyAtCp{,Nested}` already pins A's best to
  `FirstLeaf(tstar)` (swap `StaticOkRE` for `StaticCoreRE` — `FindMatchSimRE` is gate-free since D2 —
  and export `BestLiveRE` from `FindMatchSimRE`); rung C's `ResAgreeAtOutside(tstar, t, inp, S)` with
  `S = {}` is FULL first-leaf agreement (`NB.RAFirstLeafOutside`); `BestMatchRE` + `TieGm` give
  `GmOfLiveR(best) == leaf.1`; F-b gives `GmOfLive(rt) == GmOfLiveR(best)`; `FLookLoop` is the
  identity without looks. Gated spec-side lemmas to replace by gate-free twins IN A NEW MEMBER (do not
  edit entry-lk et al. — they sit low and would rebuild the whole band): `EL.TranslateFragmentPikeLkRec`
  (takes `NoNulledPlusRE` only because rung C left it), `M.MainExtractionL5`'s `QuantRegsFinal` (only
  the clock half `>= -1` is needed for `FilterResetLazyPrefix`), `M.FFindMatchThreadFacts` (gate →
  `FV.FFindMatchRegsFinal`). Fragment: `NoLookRaw ∧ NoCdnPlusRaw` (+ the L5 statics). This is the
  first end-to-end CIN-greedy theorem and exercises D+E+F-a+F-b together.
* **F-c: machine B stamp-aware** (lookarounds elsewhere in the regex). The C+D template on the B
  side: (c1) `tr_stamp` in `TreeRepLkRE`/`ETreeRepLk`/`TtLk` + determinism; (c2) the CIN arm in
  `ActionsTreeRepLkRE{,Rec}` and the four LiftSimCore giants (`ActionsTreeRepLkF{,Rec}`,
  `AtBackForkTreeLkF{,Rec}`), dropping `AR.NoTrueStamps(main code)`; (c3) the tcan↔t endpoint glue
  weakens from `ProgErase(tcan) == ProgErase(t)` to a first-leaf agreement — rung A's
  `CinPlusPriority` only gives agreement OUTSIDE `S` (it needs `LkBodiesInS(r1, S)` and `LkActsInS(cont,
  S)`); inside-`S` values at the endpoint need either a rung-A strengthening for LOOK-FREE CIN bodies
  (the chain then equals the empty leaf's actions exactly) or the stage-2a fragment conjunct "no
  lookaround inside a CIN-greedy body"; (c4) the B stamp step (Reset + `ChainT` steps under
  `PikeTreeStepLk`; `GmtTieOutside := TieGm`; the S-carriers are untouched when the stamped body is
  look-free); (c5) `MainTheoremL5` consumes F-b. Size: comparable to rungs C + D together.
* Then G (drop the gate conjuncts, CIN-greedy witness, `SUPPORTED_FRAGMENT.md`).

**Gate status:** pike-sim-re changed, so every member above it (main-theorem, flip-closed/gate/
keystone, look-behind-keystone, the lift-sim band, linden-equiv) must be re-verified; not yet
re-packed (≈ 11 h at one worker). Spot check of the six lift-sim-gate lemmas that rebuild
`PikeInvFullRE` by hand (`LiftAdvanceEpsilon{,Nested,Rec}`, `LiftFindMatchC{,Nested,Rec}`): see the
next entry.

### 2026-11-05 (late) — **F-d0 LANDED: `(a?)+` IS SUPPORTED** (lookaround-free patterns, no gate)

* **`LindenElkMainCin.MainTheoremCin(raw, str)`** (new member `linden-equiv-main-cin`, `c1da4ff`):
  `NestedFragmentRaw ∧ Latin1Wf ∧ LookFreeRaw ⟹ MatcherSpec(raw, str, Normalize(FFullMatch(raw, str)))`
  — the first end-to-end theorem with the greedy CI-nullable plus IN and no `NoNulledPlusRaw`.
  Machine A + rung C (`S = {}` ⟹ first-leaf equality) + rung D (`FindMatchSimRENested` now also
  ensures `BestLiveRE` of the winner) + F-b (`FinalReadout`, now also giving `ThreadRegsWf` of the
  reconstructed thread via `FinalRegs.dfy`'s `CapValGe` induction and the unchanged prefix clock).
  Gate-free twins in the member: `TranslateFragmentPikeLkRecCin`, `MainExtractionFromClosedCin`/
  `MainExtractionCin` (only the prefix quantifier's clock `>= -1` was ever needed),
  `NestedNoCdn`, `NestedLookFreeLB`, `LookFreeFacts`. MainCin.dfy 43/0, 120 s, 3.9 GB.
* **API** (`linden-equiv`): `SupportedCin` joins `Supported`; `MatchCorrect` dispatches to
  `MainTheoremCin`. `NullablePlusWitness`: `GreedyNullablePlusIsSupported` (`(a?)+`) and
  `GreedyNullablePlusWithLookIsStillOut` (`(?=a)(a?)+`). ApiMatch 6/0, witness 7/0, ApiReasoning
  19/0. `SUPPORTED_FRAGMENT.md` rows updated.
* Perf lessons: inside a ~500-line theorem, (1) a register-frame argument with set-comprehension
  witnesses and (2) restating facts in `R.annotate(raw)` form (even under `hide *`) were 300 s
  batches; narrow helper lemmas (`OnlyCapIdsFromFrame`, `CoversLookFree`) and an adapter that takes
  the caller's names (`MainExtractionCinAt`, body `hide *; call`) made each 1–3 s.
* Strengthening `NRR.CapValWf` with `a_cp >= -1` broke two rung-E batches (`EngineReadoutAlt`
  failure, `EngineReadoutCon` timeout) — reverted; the bound lives in `FinalRegs.dfy` instead.

**NOT yet pack-gated.** Changed: stamp-live (new), pike-sim-re, final-readout (new), main-cin (new),
linden-equiv; everything above pike-sim-re rebuilds (main-theorem, flip-closed/gate/keystone,
look-behind-keystone, the lift-sim band, linden-equiv) — ≈ 11 h at one worker. Spot checks done
against the new pike-sim-re: lift-sim-gate `LiftAdvanceEpsilon{,Rec}`, `LiftFindMatchC{,Nested,Rec}`
green; `LiftAdvanceEpsilonNested` (`{:isolate_assertions}`) 1579/2167 with 0 errors before a 30-min
wall.

**Next:** the gate pack; then F-c (machine B, for lookarounds next to a CIN plus) and G (drop the
gate from `SupportedL3/4/5` once F-c lands; retire `FNulledPlusIdentity`/`QuantRegsFinal` from the
main pass).

### 2026-11-06 — **THE GATE IS GREEN WITH RUNG F (F-a, F-b, F-d0): `workspace packed: 67 members`, `PACK rc=0`** — `(a?)+` is verified

Five pack runs (`<scratchpad>/pack1.sh`, one z3 worker, 24 GB slice); every member above
pike-sim-re rebuilt, plus the three new members (stamp-live, final-readout, main-cin). Each stop
was performance or tooling, never a wrong proof:

| run | stop | cause | fix |
|---|---|---|---|
| 1 | pike-sim-re, 22.7 GB at 5 min | `PreserveForkCaseNested`'s active-correspondence batch (the D2 watch item) — only with the PACKED `.doo` inputs | narrow lemma `ActiveRepCons2` at the 4 Fork sites (`6d61f38`): 2.7 GB |
| 2 | lift-sim-gate, z3 OOM-KILLED by the cgroup at 17 GB → dafny HUNG 1.5 h | `LiftPreserveGatePassLkNested` (isolated) obligation #888; `LiftPreserveSetRegLk{,Nested}` one-VC 900 s timeout | GatePass requires only `NI.NestTopRE` instead of `PSM.ThreadNestRE`; SetReg per-section splits (`1f4e773`) |
| 3 | lift-sim-gate, 1 timeout | `LiftAdvanceEpsilonNested`: the narrowed requires' call-site check | explicit `NestTopRE` assert at the call (`0fbcdaa`): 2171/0 |
| 4 | lift-sim-carriers, killed by MY watchdog | false "hang": a new member's dafny restarts the session CPU sum near zero | watchdog re-bases on a drop |
| 5 | — | `workspace packed: 67 members`, rc=0, peak 7.5 GB | |

Per-member (rebuilt): pike-sim-re 202 (3 m), final-readout 34, main-theorem 649 (26 m), flip-*,
look-behind-keystone, lift-sim-core 276 (26 m), oracle 177 (37 m), chain 175 (25 m), gate 131
(1 h 21 m), carriers 10 (30 m), deep 8 (23 m), forward 10 (15 m), main 8 (58 m), **main-cin 17
(2 m)**, linden-equiv 29 (4 m).

Watchdog lessons (in `pack1.sh` now): a cgroup OOM kill of z3 leaves dafny waiting forever with
stray GC ticks — watch `memory.events`' `oom_kill` and treat any increment as fatal; "CPU progress"
must be a threshold (>= 60 s per 25 min) and must re-base when the process set changes.

**State:** `nullable-plus-greedy` at the commit after `0fbcdaa` (this entry), nothing pushed.
`API.Supported` includes `SupportedCin` (lookaround-free, no nulled-plus gate); `SupportedL3/4/5`
keep `NoNulledPlusRaw`. **Next:** F-c (machine B stamp-aware: lookarounds next to a CIN plus), then
G (drop the gate from L3/4/5, retire `FNulledPlusIdentity`/`QuantRegsFinal` on the main pass).

### 2026-11-06 (cont.) — **F-c DESIGN: machine B stays CHAIN-FREE; outside-S values come from machine A**

The plan in the 2026-11-05 (cont.) entry (B stamp-aware with `tr_stamp` chains, `GmtTieOutside :=
TieGm`) would re-prove every Rec-tier step lemma against `GmOfLiveR` — rung D again, on the B side.
It is not needed. Scope: the **Rec tier only** (the `MainTheoremL5` path); L3/L4 keep the gate and
`Supported` gains an L5-CIN disjunct.

* **B's tree at the stamp is a plain `Reset`.** `TreeRepLkRE`'s `tr_reset` fires for
  `SetQuantToClock(q, _)`, either flag. On the VM side `filter_capture` reads only quant CLOCKS,
  so `GmOfLive` sees `SQC(q, true)` exactly like `SQC(q, false)`: the B step at the stamp is the
  existing Reset step and `GmtTieOutside` (plain `GmOfLive`) is untouched. B's best leaf then lacks
  the CIN chains — it is right INSIDE `S` (look groups), not outside.
* **B's raw walk is engine-shaped:** `CW.BoolTreeLkX` = `EL.BoolTreeLk` except at a CIN-greedy
  plus at `min == 1` (`CW.CinPlusL`, opaque), where the tree is
  `Choice(Reset(gidl); ti, Reset(gidl); tc)` (`ti` = iteration stack at `CannotExit`, `tc` = the
  continuation) — exactly the code tree's shape at the head fork, so the giants keep
  `ProgErase(tcan) == ProgErase(tX)` (STRUCTURAL CIN arm, no rung A inside the giants).
  `WalkPairLkRec`/`TtLkRec` switch to `BoolTreeLkX` and their SQC see-through takes both flags.
* **Glue (spec only, new member `linden-equiv-cin-walk`):** `CinWalkX` builds `tX` from the spec
  tree `t` with `ResAgreeAtOutside(tX, t, inp, G)`, `G` ⊇ every CIN body's groups (rung A with
  `S = {}` — needs the CIN body's positive looks capture-free — then `Chain` dropped outside `G`).
  `G ∩ S = {}` because CIN pluses never sit in look bodies (`PikeLkRegexRec`) and ids are unique,
  so `FirstLeaf(tX)` and `FirstLeaf(t)` agree on position and INSIDE `S`.
* **Final assembly:** outside `S` from machine A exactly as F-d0 (`FindMatchSimRENested`,
  `TieGm`, rung C's `ResAgreeAtOutside(tstar, t, inp, S)`, F-b `FinalReadout`); inside `S` from B's
  carriers (`LookNestOkTTop`/`LookNestBackTTop{,Deep}`), moved from the VM best to
  `rp = FReconstructPlus(best)` — they read only `look_regs` and the capture/quant clocks of the
  looks' ANCESTORS, none of which a look-free CIN body owns.
* Fragment (new `SupportedL5Cin`): `SupportedL5` minus `NoNulledPlusRaw`, plus "no greedy
  nullable plus inside a look body, and every greedy nullable plus body is look-free".
* Rung A side fix: `NP.CinPlusPriority{,Bool}` drop `LkActsInS(cont, S)` (never used in the
  body) so the theorem runs at `S = {}` next to capturing looks in the continuation.

Work list: (1) cin-walk member (`BoolTreeLkX`, determinism, `CinWalkX`); (2) `TreeRepLkRE`
stamp-as-Reset; (3) Rec giants (`ActionsTreeRepLkFRec`/`AtBackForkTreeLkFRec`) on `BoolTreeLkX`
with the CIN head + CIN loop-view arms, `NoTrueStamps` dropped; (4) the 18 Rec-tier
`NoTrueStamps` lemmas (`WalkPairLkAt{SetQuant,Fork}*Rec`, `TtLkAt{SetQuant,Fork}*Rec`,
`QuantHead*`, `LiftPreserve{SetQuant,Fork}LkRec`, `LiftInitCRec`, `ActionsTreeRepLkRERec`) and
the rest of the Rec tier on `BoolTreeLkX`; (5) `L3aCompositeCloseRec` with the glue; (6)
`MainTheoremL5Cin` + `SupportedL5Cin` (downstream twins without `QuantRegsFinal`).

**F-c progress (2026-11-06, same day):**
* (1) DONE `33a7d25`: member `linden-equiv-cin-walk` (`CW.BoolTreeLkX`, `BoolTreeLkXDeterm`, `CinWalkX`
  glue, later also `BoolFlagLiftRecX`, `BoolCheckInsertKX` — the do-while seam's check insertion —
  `CinGreedyL` shape lemmas, `NoNulledPlusCinOk`). Rung A's priority lemmas run at `S = {}`.
* (2)-(5) CODED, per-symbol verification running (uncommitted):
  - LiftSimCore: `TreeRepLkRE` `tr_reset` for both flags; `TtLkRec` on `BoolTreeLkX` + stamp
    see-through; `QuantHead*` lemmas generalized (exclude only the CIN head at `min == 1`; CIN
    forced copies proven); the Rec giants on `BoolTreeLkX` with `NoTrueStamps` dropped and the CIN
    arms as their own lemmas `LkCinQuantRec` (forced copy + head fork) and `LkCinLoopViewRec` (end
    fork); `BoolTreeLkXPikeSubtree`; `DispatchStampEffectNested` (B's stamp step = the Reset step;
    `GmOfLive` effect from machine A's `StampStepThreadRENested`); the Dispatch helpers take
    `StaticCoreNestedRE`.
  - LiftSimOracle: `TtLkAt*Rec` on `BoolTreeLkX`; CIN head refuted at SQC, a Choice at the Fork;
    `TtLkAtSetQuantRec` takes the flag; `ActionsRepNotAtTrueStamp` (no stack sits at the stamp).
  - LiftSimChain: `WalkPairLkRec` on `BoolTreeLkX` + stamp see-through; `WalkPairLkAtSetQuantRec`
    takes the flag; CIN arms `WalkPairLkCinHeadArmsRec` / `WalkPairLkCinLoopViewArmsRec`;
    `GateAheadClearReset`.
  - LiftSimGate: the whole Rec region on `PSM.StaticCoreNestedRE` (gate-free); the SQC dispatch
    handles `bq` (stamp effect, machine A via `PSM.PreserveQuantCaseNested` + `TrcTrans`);
    `LiftInitCRec` takes the engine-shaped root walk + `PikeLkRegexRec` as a hypothesis;
    `L3aCompositeCloseRecG(…, G)` returns B's leaf with the `CinWalkX` agreement outside `G`;
    `L3aCompositeCloseRec` is now its gated wrapper at `G = {}` (callers unchanged).
* (6) OPEN — the endpoint is gated deeper than planned: main-theorem's `Endpoint*` producers
  (`EndpointValueOk` & co., ~15 lemmas from MainTheorem.dfy:18007) require `NoNulledPlusRE(re)`
  and conclude quant finality `∀k a_cp[k] < 0` of the VM winner; the look-body replay lemmas
  (`ReplayPlus*Frame*`) consume it for ALL k although a body replay reads only the body's qids.
  Route: weaken finality to `FV.RegsFinalOk(·, |str|, CinQids(re))` (+ CIN qids outside looks), or
  run the endpoint on a synthetic winner with the CIN `a_cp`s cleared (`GmOfLive` reads clocks
  only, so every B tie transfers) after a frame lemma "FLookLoop ignores outside-look registers".
* (6) PLAN (synthetic winner; no main-theorem lift lemma changes): the engine answers
  `filter_reset(FLookLoop(rp))`, `rp = FReconstructPlus(best)`. Let `rp0` = `rp` with every quant
  `a_cp` cleared. (a) gate-free twins of the run-level fact producers (`LookRowsStaticNested`,
  `LookRowsDynamicNested`, `FStabilityNested` — check what each uses the gate for; quant finality
  becomes F-d0's `FV.FFindMatchRegsFinal`); (b) `FReconstructPlus` frame for look-free CIN bodies:
  look regs unchanged, captures written only on CIN-body groups, quants only on CIN-body qids;
  (c) the VM never reads quant `a_cp` (only `FNulledPlus` does, and only for its own body's qids;
  `filter_reset` reads clocks) ⟹ `FLookLoop(rp)` and `FLookLoop(rp0)` agree on captures, looks
  and quant clocks ⟹ same `filter_reset`; (d) the `FLookLoop*Lift` lemmas are already stated on
  raw `(cap, lk, qt)` with full finality — apply them to `rp0` through thread-level copies of
  `Endpoint*`; (e) `ProduceOwnerForall`/`MainTheoremL4DeepConclude` on `rp0` with the SPEC leaf:
  outside `S` from machine A (+ rung C + F-b), inside `S` from B's carriers (they read look regs and
  look-ancestor clocks only) and the `CinWalkX` glue; (f) `MainTheoremL5Cin`, `SupportedL5Cin`,
  witness `(?=a)(a?)+`.
* (6) PIECES LANDED IN SOURCE (uncommitted until the queue/pack confirms):
  - final-readout `QuantCpIrrel.dfy` (23/0): `QAgree/TAgree/SAgree` (quant banks agree on clocks
    and outside `D` on values) preserved by `FAdvanceEpsilon`/`FConsume`/`FFindMatch`,
    `FNulledPlus`/`FNulledChildren` (if `QidsOf(reg) * D == {}`), `FFindMatchPlus`, `FLookLoop`
    (`LookAstsAvoid(crv, D)`), and `filter_reset` reads clocks only.
  - final-readout `ReconFrame.dfy` (8/0): `FNulledPlusFrameQ` — the reconstruction moves only the
    bodies of STAMPED quantifiers (`CapsQ/LooksQ/QuantsQ(r, Q)`, `StampsIn(r, rg, Q)`).
  - main-theorem: `LooksNoNulledPlusRE` (STRUCTURAL look-bodies-only gate) + `FromFull`/`Body`
    descent lemmas, swept through 21 lemmas (9 keep the full gate and call `FromFull`);
    `WinRegsOk` (opaque thread bundle) + `WinRegsOkFromRun` (gated) and THREAD-LEVEL producers
    `Endpoint{Value,QuantValue,ChildLink,LookInv,TopLookFrame}OkRegs(…, th, …)`; the old
    producers are now thin wrappers.
  - deep/forward/carriers/main: `requires M.LooksNoNulledPlusRE(re)` + `M.LooksNoNulledPlusBody`;
    MainTheoremL3/L5 call `M.LooksNoNulledPlusFromFull(re)`.
  - PENDING (`<scratchpad>/deferred_gate_sweep.py`, apply once no queued dev run reads the
    Oracle/Chain sources against main-theorem's old `.doo`): the same sweep in Oracle
    (`GateStaticsSweepRENested`, `GateStaticsFromTablesNested`, `DeepFindRecFwdBase`,
    `L3aEndpointAssembly`) and Chain (`ProduceOwnerForall`). Until then the workspace does NOT
    resolve consistently (Forward/Deep call Oracle lemmas that still want the full gate).
* (6) c6 CODED (2026-11-06 night, RESOLVES against the swept stack; verification queued):
  - final-readout `CinLookPaths.dfy` (new): `AncCapRegs`/`AncQuants` (a look's ancestor
    registers), `LookPathFrame`/`LookPathDomFrame`/`LookPathPresentLkFrame` (the look-path
    predicates read only those), `AncAvoidQ` (ancestors avoid `CapsQ`/`QuantsQ` of look-free
    CIN bodies), `QsOutside` (the reconstruction's write sets lie outside every look),
    `QsAvoidLookBody`, `FinalReadoutFrame` (`FReconstructPlus(th)` agrees with `th` outside
    `CapsQ/LooksQ/QuantsQ(re, CinQids(re))`).
  - final-readout `FinalRegs`: `QClkGe` (quant clocks >= -1) threaded through
    `ApplyWritesValGe`/`FCValGe`/`ReconAtValGe`/`FPValGe`; `FinalReadout` ensures it of `rp`.
  - NEW member `linden-equiv-main-cin-lk` (`MainCinLk.dfy`, module `LindenElkMainCinLk`):
    `TranslateCinOk` (glue side condition at `G = CapIdsOutsideLooks(re)`, `G * S == {}`);
    `ClearQuantCps(th, D)` — the synthetic winner `rp0 = ClearQuantCps(rp, QIdsOuter(re))`;
    `TieTransport` (B's carriers at `(bleaf, best)` -> `(FirstLeaf(t), rp0)` through
    `ClkFrame` + `AncFrame`); `WinRegsOkG` + `WinRegsOkGFromRun` (gate-free run facts) +
    `WinRegsOkRecon` (-> `M.WinRegsOk(rp0)`); `ProduceOwnerForallRegs` (thread twin);
    `LookAstsAvoidOuter` + `AnswerSynthetic` (`QCI.FLookLoopAgree` at `D = QIdsOuter(re)`);
    `TranslateFragmentPikeLkRecLk`, `MainExtractionL5Lk` (look-bodies gate twins);
    `ReadoutAtWinner`, `EndpointAtRp0`, and **`MainTheoremL5Cin`** — hypotheses
    `NestedFragmentRaw`, `Latin1Wf`, `L5Scope` + RE-level `M.LooksNoNulledPlusRE` and
    `RF.CinBodiesLookFreeRE` on `lazy_prefix(annotate(raw))`.
  - deferred sweep extended: `OracleColumnNested`/`OracleOkRowsL5` take the looks gate
    (`<scratchpad>/deferred_gate_sweep.py`; scratch-applied copies in `<scratchpad>/sw/`).
  - G then = `SupportedL5Cin` (executable twins of the two RE-level predicates) + witness.
* (6) RECIPE for `MainTheoremL5Cin` (new member, e.g. `linden-equiv-main-cin-lk`): copy
  `MainTheoremL5`; statics with `StaticCoreNestedRE` + `PikeLkRegexRec` (twin of
  `EL.TranslateFragmentPikeLkRec` from "no nulled plus in look bodies") + `GateStaticsFromTablesNested`
  (looks gate); B: `L3aCompositeCloseRecG(…, G := CIN bodies' groups)` → `bleaf`; A:
  `PSM.FindMatchSimRENested` + rung C's ATR (`ResAgreeAtOutside(tstar, t, inp, S)`) + F-b
  `FinalReadout` → outside-S values of `rp = FReconstructPlus(best)`; `rp0` = `rp` with quant
  `a_cp` cleared; `WinRegsOk(rp0)` from gate-free run facts of `best` (`LookRowsStaticNested`,
  `LookRowsDynamicNested`, `FStabilityNested`, `MainMatchBodyQuantsInitNested`,
  `CM.FFindMatchLook{Frame,ClkSet,CpSet,OracleTrue}`, `FV.FFindMatchRegsFinal`) transported by
  `FNulledPlusFrameQ` (look regs equal; captures/quants move only in CIN bodies, which are
  look-free and outside looks); `Endpoint*Regs(rp0)`; a thread twin of `ProduceOwnerForall`;
  `BestTieLkNestedTop(…, FirstLeaf(t), Some(rp0))` from A (outside S) + B's carriers (inside S,
  through the glue); `MainTheoremL4DeepConclude(rp0, FirstLeaf(t))`; answer equality
  `filter_reset(FLookLoop(rp)) == filter_reset(FLookLoop(rp0))` by `QuantCpIrrel` with
  `D = CinQids`; a gate-free twin of `MainExtractionL5` (only quant clocks `>= -1` needed, as F-d0).

### 2026-11-06 (night) — **F-c + G VERIFIED (per-symbol): `MainTheoremL5Cin` green; `(?=a)(a?)+` is SUPPORTED**

Dev runs at one z3 worker under the 24 GB slice (`--verification-time-limit=300`):
* `LindenElkMainCinLk` whole module **63/0** in 432 s, peak 5.1 GB. `MainTheoremL5Cin` takes 14
  batches; all are ≤ 10 s except the extraction batch (2:37, 312 M resources).
* `LindenElkCinLookPaths` 22/0, `LindenElkFinalRegs` 6/0, `FinalReadout` 5/0.
* `LindenRegexApi.MatchCorrect` 2/0, `NullablePlusWitness` 7/0 (G:
  `GreedyNullablePlusWithLookIsSupported`).
* Chain Rec lemmas (22 runs) green; gate `LiftPreserveAnchorPassLkRec` 2/0 after its such-that
  named `CW.BoolTreeLkX` (it still said `EL.BoolTreeLk`).
* main-theorem `FreshBodyDirectMember*` 8/0 in 69 s, after `hide LooksNoNulledPlusRE;` in its body.
  Without it the recursive gate in context blew the whole-module run to 20.6 GB.

Fixes found by the runs:
* **Recursive ghost gates in context are memory bombs.** Twice so far:
  `FreshBodyDirectMember` (20.6 GB) and `MainTheoremL5Cin` batch 6 (> 19 GB). Fix both times:
  `hide M.LooksNoNulledPlusRE, RF.CinBodiesLookFreeRE;` at the head of the body. The facts stay
  as ground terms and callees take them verbatim. Do this in ANY new lemma carrying them.
* `NoNulledPlusNoCin` / `CinQidsOuter` need `T.TransWf` (`counted_quantifier.min` is an `int`;
  `QuantWf` gives `min >= 0`).
* `CinWalk.NoNulledPlusCinOk`: `NotCinGreedy` only at `min > 0` (guarded).
* **Deferred sweep APPLIED** to the real Oracle/Chain sources (identical to the `sw/` copies). The
  weakened `GateStaticsFromTablesNested` needed `M.LooksNoNulledPlusFromFull(host)` at three
  callers: Carriers `ForwardFindRecFwdBase`, Deep `DeepFindRecFwdDeep`, Forward
  `ForwardFindRecFwdDeep`. Carriers `LookNestBackTFromBodyReplayLB` needed
  `FST.NoNulledPlusFXR(body); M.LooksNoNulledPlusFromFull(reF)`.

Pending: per-symbol checks of the swept Oracle/Chain lemmas and their callers (Carriers, Deep,
Forward, Main); `CinWalk.NoNulledPlusCinOk` re-run; the whole main-theorem module at TL = 900;
then THE GATE (`lem pack --jobs 1`, 69 members with cin-walk + main-cin-lk).

#### 2026-11-07 — post-sweep per-symbol pass: what the swept callers needed

Green so far: `CinWalk` 1/0. Oracle `GateStatics*` 7/0, `OracleColumnNested` 84/0,
`OracleOkRowsL5` 2/0, `DeepFindRecFwdBase` 2/0. Carriers `ForwardFindRecFwdBase` and
`LookNestBackTFromBodyReplayLB` 2/0 each. Deep `ForwardFindRecLBBase` 87/0. Forward
`ReverseCDeepFull` 40/0. Main `ForwardMemberOne` 568/0 and `MainTheoremL4DeepConclude` 2/0.
main-theorem whole module 989/0 apart from `LookRowsDynamicNested`.

* **The gate swap goes in lemma contracts only where the callees allow it.**
  * Oracle `L3aEndpointAssembly` and Chain `ProduceOwnerForall` call main-theorem lemmas that still
    require the FULL `NR.NoNulledPlusRE(re)`:
    * `LookRowsFromTablesL3a`
    * `LookRowsFromTablesNested`
  * A precondition error at Oracle 2861 showed this. Both lemmas keep the full gate. Their body head
    derives the looks gate (`M.LooksNoNulledPlusFromFull(re)`) and then hides it.
  * The depth-1/L3a feeders keep the full gate. That is the next rung (porting the F-c endpoint to
    `SupportedL3`).
* **`hide M.LooksNoNulledPlusRE;` at the body head of every swept lemma that only passes the gate
  on.** There are 16 sites:
  * Carriers ×2, Deep ×4, Forward ×5, Main ×3
  * `L3aEndpointAssembly` and `ProduceOwnerForall`
  * Without it, `ProduceOwnerForall` went over 19 GB.
  * Do NOT hide it in the structurally recursive `GateStaticsSweepRENested`, which unfolds it.
* **main-theorem `LookRowsDynamicNested`**: `hide LooksNoNulledPlusRE;` alone did not fix it. The
  (c') batch still timed out at 300 s.
  * Fix: move the per-row step out into `LookRowCapsUntouched`.
  * Run in isolation, that lemma had ONE stuck obligation:
    `forall k :: k in CaptureRegs(body) ==> k !in Sc` (pure set algebra; the solver expands the
    comprehensions).
  * Fix for that obligation: state the two ground equalities, then `hide *` (AGENTS §2.9).
  * Results: the lemma takes 0.28 s, and `LookRowsDynamicNested` is 5/0 in 58 s.
* **The hub instance `GateStaticAtNested(qm, re, crv, A1, …)` timed out at 900 s** in three
  lemmas:
  * Deep `DeepFindRecLB`, the A1 hop
  * Forward `ForwardFindRecFwdDeep`, the A1 hop
  * Forward `ForwardFindRecLBDeep`, the opaque preamble's row at A

  It is a bare forall instance of `GateStaticsOkNested`, but Dafny inlines the goal, so Z3 has to
  re-prove the hub's existential. Fix (AGENTS §2.9):
  `assert GateStaticAtNested(…) by { hide *; reveal GateStaticsOkNested; }`. In `DeepFindRecLB`
  the following pick also gets its own `split_here`.
  * After the fix: 140/0, 11/0 and 170/0. Every batch is under 2 min.

All green, per-symbol, at one z3 worker:
* Chain `ProduceOwnerForall`: 314/0, peak 9.3 GB (was > 19 GB).
* Oracle `L3aEndpointAssembly`: 2503/0 in 1934 s.
  * PACK RISK: the `FLookLoopCaptureFrame(…, SpM)` precondition at Oracle 3318 is one isolated
    obligation that took 2:04 and 3:45 in two runs, and timed out at 300 s in a third.
  * The call is the same as at HEAD. It is under the 900 s limit.
* `MainTheoremL3`: 1744/0 in 1806 s.
* `MainTheoremL5`: 2824/0 in 2960 s.

Next: commit, then THE GATE.

### 2026-11-07 — **THE GATE IS GREEN WITH F-c + G: `workspace packed: 69 members`, `PACK rc=0`** (`71719ef`, one z3 worker)

Five perf commits after `27fdfe0` got it there; no proof content changed:
* `8e2c9ba` hide the recursive gates in the two FromTables covers lemmas.
* `6622d96` `LkCinQuantRec` under the pack memory cap.
* `6854ad0` `L3aEndpointAssembly`'s frame-call precondition, witnessed.
* `866e94d` `WalkPairLkCinHeadArmsRec`'s iteration-list rep in a cut context.
* `71719ef` `LiftPreserveGatePassLkRec` picks the per-lid package verbatim.

### 2026-11-08 — **§2.3/§2.4 CLOSED: captures under quantifiers at any look depth** (branch `cap-under-quant`, `01b869f`)

Chosen over the recorded next rung (F-c on depth-1 `SupportedL3`). `SupportedL4/L5/L5Cin` lost
`LookBodiesNoCapUnderQuantRaw` and `QuantsLookCapFreeRaw`. See `SUPPORTED_FRAGMENT.md` §2.3/§2.4 for the
argument. New witnesses: `(?=(?=(a)*))`, `((?=(?=(a))))*`, `(?=(a)*)(a?)+`.

* **The owner package no longer goes through the spec.** `ProduceOwnerForallRes` reads it off the
  result banks of the look loop (`M.LookInvO`, `M.Res0LiveO`, `M.ValueOkO`, `M.QuantValueOkO`). It
  replaces `ProduceOwnerForall` and `ProduceOwnerForallRegs`.
* **Machine B's Rec tier never needed the scope condition**, so `L3aCompositeCloseRecG` is unchanged.
* **Dead code left in place:** core `GNotUnderQuantLLookBody`, oracle `FreshWfGIndep`, M's
  `FreshBodyDirectMember` and `GNotUnderQuantL` family, NI `PathPresentLkDirectAgree` and
  `LookPathDomNoAncQuants`.
* **`SupportedL3` is subsumed by `SupportedL5` now.** Proved in the 2026-11-08 retirement entry below.
* **Perf fixes that were needed:**
  * `DeepFindRecFwdDeep`'s hub pick timed out at 300 s. `MatchedPosFromHub` picks with the FULL
    conjunct list under `hide *; reveal GateStaticsOkNested`. A partial conjunct list does not close.
  * `MainTheoremL5Cin`'s engine-pipeline batch (`lazy_prefix` and `max_quant` unfolding around the
    `seq(…)` seed) timed out at 900 s with 2 G resources after a change elsewhere in the lemma.
    Moving the size fact to `FFullCompilationLookLens` with those two hidden made the whole theorem
    15/0 with no batch over 9 s.

Per-symbol, one z3 worker: `MainTheoremL5` 2887/0 in 2911 s, peak 6.9 GB. `DeepFindRecFwdDeep` 890/0
in 708 s. `ForwardMemberOne` 566/0. `ForwardFindRec*` 183/0. `MainTheoremL5Cin` 15/0.

**Gate:** `workspace packed: 69 members`, `PACK rc=0`, 906 obligations in the 11 rebuilt members, 4h 42m at one z3 worker, peak 13.4 GB (`01b869f`, 2026-11-08).

### 2026-11-08 — **`MainTheoremL3` RETIRED: `SupportedL3 ⇒ SupportedL5`** (branch `cap-under-quant`, `77fb1f5`, `4868508`, `9af0d18`)

`API.SupportedL3ImpliesL5` (`77fb1f5`) proves every depth-1 pattern is in `SupportedL5`.
`MatchCorrect` calls it first, so depth-1 patterns go through `MainTheoremL5`. `Supported` is unchanged.
`API.DepthOneCinIsL5Cin` shows a depth-1 pattern is in `SupportedL5Cin` when its looks hold no nulled
plus and its CIN bodies are lookaround-free.

* **The retirement is partial.** `MainTheoremL3`, `L3aEndpointAssembly` and the code only they reached
  are gone from the lift-sim band (1,821 lines deleted over carriers, chain, core, gate, oracle).
  `L3aEndpointAssemblyNestedFull2` stays: `LiftSimMain` still calls it.
* **The base packages keep their unused code, because they do not rebuild in the 24 GB slice.** The
  first deletion (`4868508`) also touched 11 base packages, which forced `nfa-rep-re`'s first rebuild
  since 2026-08-31 (80 GB cap). It was OOM-killed at 21.8 GB (rc=143, 456 s into the gate). `9af0d18`
  restored all 11 from `77fb1f5`, so they stay cached.
* **Any rung that touches `nfa-rep-re`, including §2.2, must first split it to fit the slice.** Other
  base members last built around 2026-08-30 (the `oracle-*` group) may have the same problem, and they
  have not been rebuilt under z3 4.14.
* **Deletion rule:** a name may be deleted only if nothing that STAYS refers to it. Reachability from
  the theorems is not enough, because unreachable code that stays must still resolve. Applying only
  reachability broke the resolve with 6 errors.
* **The unused code in the lift-sim band went next** (`63ab620`): 212 declarations, 14,116 lines over
  carriers, chain, core, gate and oracle, deletion only. Six of them carried `{:isolate_assertions}`.

**Gate:** `workspace packed: 69 members`, `PACK rc=0`, 887 obligations in the 11 rebuilt members
(58 cached), 3h 45m at one z3 worker, peak 12.8 GB (`9af0d18`, 2026-11-09). That is 57 minutes less
than `01b869f`.

**Gate after the band prune:** `workspace packed: 69 members`, `PACK rc=0`, 533 obligations in the 11
rebuilt members (58 cached), 2h 03m at one z3 worker, peak 7.5 GB (`63ab620`, 2026-11-09). `lift-sim-gate`
fell from 1h 22m to 8m 32s. `lift-sim-main` is now the slowest at 52m 49s.

### 2026-11-09 — **§2.2 step A: looks inside negative lookahead bodies** (branch `neg-look-nest`, `21b2cc8`)

`(?!a(?=b))` is supported; `(?<!a(?<=b))` is not yet. What changed and what step B needs are in
`SUPPORTED_FRAGMENT.md` §2.2.

**Not gated by `lem pack`.** `lem` went from 0.1.21 to 0.1.23 at 09:57 on 2026-11-09. Its build identity is part of the
cache key, so every member would rebuild, and that rebuild stops at `semantics-core`: `FlatMapApp` times out and
`StrictSuffix:262` fails under z3 4.14.1. `oracle-sweep` (`AdvanceOvIndep`) has the same problem and `nfa-rep-re` runs
out of memory in the 24 GB slice. All of these predate the upgrade and were hidden by the cache. apt now offers only
0.1.23, so the plan is to fix them and do one full rebuild.

**What was checked instead.** Whole-package `dafny build -t:lib` with the pack's flags (`--verification-time-limit=900
--cores 1`), against each dependency's fresh `.doo`. All 40 affected members pass with 0 errors and no warnings:
* the five lower ones, built by `lem` at 09:39-09:51 (`entry-lk`, `check-erase`, `look-leaves`, `nulled-plus`, `cin-walk`);
* the 35 above them, 3,127 obligations, 4h 28m at one z3 worker, peak 20.0 GB.

Slowest: `lift-sim-main` 1h 03m, `nest-inv` 37m 33s (the 20.0 GB peak), `actions-tree-rep-re` 21m 51s (18.4 GB).

**Lessons from this rung.**
* A timeout hid a missing fact. `LookNestBackTFromBodyReplayLB` burned 900 s because the flip route proves only
  `NR.NegLooksLookFreeRE` of the mirrored body, while the forward carrier now wants `EL.NegBehindLookFreeRE`. With
  `NegBehindFromNegLooks` it takes 28 s.
* A termination check can unfold the secondary measure. `hide MsizeA` at the lemma head, when every recursive call
  decreases on the first component, took `ATR_QuantCin` from out of memory to 6.3 GB.
* Keep every `:|` off the hub on the hub's full conjunct list. The pick in `DeepFindRecLB` had dropped
  `NR.NoNulledPlusRE`, and restoring it took that batch from over 900 s to 24 s.
* Near the limit, unrelated edits move batches. `ComputeTrOwnerNamedActs` and `LiftPreserveForkLkRec` needed only
  `split_here` per branch, and their slowest batches are now 38 s and 5 s.

### 2026-11-10 — **Full rebuild under `lem` 0.1.23 and z3 4.14.1: gate green** (branch `neg-look-nest`, `3aa83bc`)

**Gate:** `workspace packed: 69 members`, `PACK rc=0`, 5,521 obligations, 68 members rebuilt from source and
`linden.warblre` cached from an earlier 0.1.23 pack, 5h 01m at one z3 worker, peak 20.5 GB (`nest-inv`). This gates §2.2
step A as well, and no member depends any more on a result from before the upgrade.
Slowest: `lift-sim-main` 52m, `nest-inv` 37m 36s, `actions-tree-rep-re` 20m 37s, `main-theorem` 19m 55s.

**What it took.** Eleven base packages did not verify from scratch under z3 4.14.1: `semantics-core`, `engine-model`,
`engine`, `reasoning`, `mirror`, `flip-mirror`, `flip-rev`, `oracle-sweep`, `oracle-build`, `oracle-spec`, `nfa-rep-re`.
Most were timeouts or memory kills. All are fixed in `3aa83bc` with no `{:isolate_assertions}`, and `regex-engine/` is
unchanged. `nfa-rep-re` now takes 448 s and 5.8 GB, so it no longer needs splitting, and the base-package prune that
`9af0d18` restored (see above) can be redone.

**Lessons from this rung.**
* `split_here` does not split the lemma's exit. A postcondition checked at a join lands in "assertions until first
  split" with every branch at once. Name the postcondition as a predicate and assert it at the end of each leaf branch.
* A one-step unfolding helper proved away from the caller's context is cheap. The same unfolding with `start == |prev|`
  in context ran out of memory.
* Sequence goals in big contexts hang z3 at low resource counts: use `assert X by { hide *; }` or a separate
  associativity lemma.
* Diagnose with `dafny verify --resource-limit 300e6 --progress Batch` per symbol, which names the batch instead of
  filling the slice. `build -t:lib` prints no batch progress.
* A labeled `requires` on `CompileNfaRep` crashes Boogie (null reference in `Program.Resolve`).

### 2026-11-10 — **§2.2 step B: lookbehinds inside negative lookbehind bodies** (branch `neg-look-nest`)

`(?<!a(?<=b))` is supported. `(?<!a(?=a))` stays out, the same restriction a positive lookbehind has. What changed is in
`SUPPORTED_FRAGMENT.md` §2.2. All 19 changed packages verify in dependency order.

**Gate green on `f3746ba`:** `workspace packed: 69 members, 3443 obligations verified`, PACK rc=0, 4h 24m 51s at one z3
worker. 40 members rebuilt and 29 came from cache. Peak 20,467 MiB in `nest-inv`, under the watchdog's 22 GiB kill limit
and the 24 GiB slice. The slowest member is `lift-sim-main` (53m 30s), then `nest-inv` (37m 32s).

**Lessons from this rung.**
* Dropping a hypothesis can make a batch run away. `FreshBodyMatchGmOuterLBNested` hit the 900 s limit, and two batches
  in `lift-sim-deep` took the build past 21 GiB (17 minutes and 6 GB before). The fixes were `hide FST.FXR`, moving a
  `:|` pick into `GateStaticPick`, and a `hide *` with five small reveals.
* `hide *` inside `assert E by { ... }` also applies to the well-formedness check of `E`. Reveal what `E`'s function
  preconditions need.
* A `--no-verify` `.doo` is accepted by `dafny verify` and refused by a verifying `dafny build`. It is good for resolve
  checks and per-symbol runs, and it cannot stand in for a dependency of a real build.
* `--filter-symbol` is a `dafny verify` option and `dafny build` rejects it. It matches by substring, so `DeepFindRec`
  also selects `DeepFindRecLB`.
