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
