# The verified fragment — what `Match` is guaranteed to get right

> Verification status (2026-08-30): the entire equivalence — `linden.equiv` and its 60 dependency packages —
> verifies under `lem pack` (61/61, 59 min at `--jobs 3`, no `{:isolate_assertions}`), on `main` (`a1044d1`).

Status 2026-08-28 (post whole-file sweep), branch `l4-nesting`. Entry point: `ApiMatch.MatchCorrect(pattern, str)`:

```dafny
lemma MatchCorrect(pattern: R.raw_regex, str: string)
  requires Supported(pattern)
  ensures LES.MatcherSpec(pattern, str, Match(pattern, str))
```

`Match` runs the compiled RegElk engine and normalizes the result into the JS-style capture array.
`MatcherSpec` is the ECMAScript **backtracking tree semantics** (Linden). So the guarantee is not
"same yes/no answer" but "same match AND the same capture array, group by group".

`Supported(p) == SupportedL3(p) || SupportedL4(p) || SupportedL5(p)` (`ApiMatch.dfy`).

---

## 1. What is in scope

Everything below is verified for **case-sensitive, single-line, Latin-1** patterns
(`TheRer(raw) == RER(false, false, false, NGroups(raw))`: `ignoreCase = multiline = dotAll = false`;
`T.Latin1Wf(pattern)`).

| Construct | Status |
|---|---|
| literals, `.`, `\w`-style groups, `[...]` / `[^...]` classes | ✅ (Latin-1 alphabet) |
| anchors (`^`, `$`, `\b`, …) | ✅ |
| alternation, concatenation | ✅ |
| capture groups, arbitrarily nested | ✅ |
| `*`, `?`, `{m,n}`, lazy variants | ✅ |
| `+`, `{n,}` (n>0, unbounded) | ✅ non-nullable body (any greediness); ✅ **nullable body when LAZY** (`(a?)+?`, §2.5a, 2026-08-30); ✅ **CI-nullable body when GREEDY** (`(a?)+`, `(a\|)+`) **in lookaround-free patterns** (§2.5b, `SupportedCin`, 2026-11-05). ❌ greedy nullable plus **together with a lookaround** (`(?=a)(a?)+`, rung F-c); ❌ context-dependent-nullable greedy body (CDN, `CheckNullable`) |
| positive lookahead `(?=…)`, capturing, nested to any depth | ✅ (L4) |
| **positive lookbehind `(?<=…)`, capturing, nested to any depth** | ✅ (L5, 2026-08-28) — a lookbehind's body may contain **only lookbehinds**; a lookahead's body may contain positive lookbehinds (`(?=x(?<=y))`, the s6 widening — see §2.1) |
| negative `(?!…)` / `(?<!…)` | ✅ **only with a look-free, capture-free body** |
| backreferences | ❌ not in the AST at all |

Newly provable at L5 (was impossible before): `(?<=a(?<=b)(c))`, `(?<=(x)(?<=(y)))` — capturing
lookbehinds nested inside capturing lookbehinds, **including the reversed-span capture values**
(the engine records a lookbehind's span backwards; the spec leaf is ordered — the tie is the
`NormRange`/`SwapRange` normalization).

The three fragments in one line each:

* **L3** — depth-1 lookaround only (`NR.LookBehindFragmentRaw`).
* **L4** — nested capturing **lookaheads**, no positive lookbehind anywhere (`NR.NoPosLookbehindRaw`).
* **L5** — nested capturing **lookbehinds** too, under `LSIM.L5ScopeV1RE` (see §2.1).

`SupportedL4 ⇒ SupportedL5` semantically (`LSIM.L4ScopeImpliesL5`); `MainTheoremL4` is now a thin
wrapper over `MainTheoremL5`. L3 is a separate proof (`MainTheoremL3`) kept for the depth-1 path.

---

## 2. What is still OUT of scope, and why

### 2.1 A positive lookbehind inside a **lookahead** body — `(?=x(?<=y))` — WIDENED 2026-08-28 (s6), CLOSED 2026-08-30

Status: **in scope and shipped.** The scope predicate, the gate hub, the carriers, the descent arms and
`MainTheoremL5` are green on the widened text, and — the stronger statement — the whole workspace packs
(`lem pack`, 61/61 members, no `{:isolate_assertions}` anywhere, every lemma under the 900 s limit; s8,
`L5_HANDOFF.md` §5.7.5). No PENDING marker remains. Kept here as the record of what the widening changed.

The ORIGINAL v1 L5 scope was:

```
Re_lookaround(_, la, body) =>
     (la.Lookbehind?  ==> NR.LBOnlyLooksRE(body))     // a lookbehind's body: lookbehinds only
  && (!la.Lookbehind? ==> M.NoPosLookbehindRE(body))  // a lookahead's body: no positive lookbehind
```

This mirrors the gate hub `LSIM.GateStaticAtNested`, whose per-lid conjunct is **kind-split** in
exactly the same shape. The reason is **performance, not soundness**: the hub's
`M.NoPosLookbehindRE(body)` conjunct is the pruning fact that keeps the giant descent lemmas
(`DeepFindRec`, `ForwardFindRec`) tractable. Dropping it — or replacing it with the recursive
`NR.L5ScopeRE(body)` — made previously-green lemmas time out at 900 s (see `L5_HANDOFF.md` §5.7.2).
**Widening the scope here means giving lookahead lids the LB-only fact as well, which re-opens that
cliff.** It is now more tractable than it was, because the pattern that fixed it exists:
split the arm into its own lemma (`DeepFindRecLB`, `ForwardFindRecLB`), extract shared blocks
(`BackFreshPlusIsPlain`), and make every `:|` off the hub list its FULL conjunct list.

### 2.2 Nested looks inside a **negative** look body — `(?!a(?=b))`, `(?<!a(?<=b))`

Required by `NR.NegLooksLookFreeRaw`: a negative look's body must be **look-free**. (It must also be
capture-free — that part comes from `NR.NestedFragmentRaw` and is not the obstacle, since a negative
look contributes nothing to the group map anyway.)

**Why look-free is currently required.** The spec-side fragment predicate `EL.PikeLkRegexRec` keeps
negative looks in their depth-1 shape: a negative gate's body must translate to a **group-free** spec
regex (`SD.GroupFreeL`). And `GroupFreeL` is defined to be **false on every `LookaroundR` node**,
irrespective of what the body contains:

```dafny
ghost predicate GroupFreeL(r: L.Regex) {          // linden-reasoning SpanDuality.dfy:56
  ...
  case Group(_, _)      => false
  case LookaroundR(_, _) => false                 // <-- any gate at all disqualifies it
  case Backreference(_) => false
}
```

so "capture-free body" is *not* enough to get `GroupFreeL`; the bridge lemma
`OS.TranslateGroupFree` demands `CaptureFreeRE && LookFreeRE`. The consumer is
`EL.TranslateFragmentPikeLkRec` (EntryLk.dfy:906), whose negative arm discharges exactly that.

Downstream, this "no gates inside a negative body" property is what lets the whole depth-k machinery
treat a negative look as an **opaque boolean leaf**: one `CheckOracle` instruction, no lid frames, no
child links, no oracle columns for anything inside it, and no contribution to the group-map
confinement arguments (`LkResultAgreeOutsideNested`, `GmtTieOutside`).

**What lifting it would take.** Three layers, in order:
1. `SD.GroupFreeL` (or a new `GateOkNegL`) must accept `LookaroundR` whose body is itself group-free —
   a change in *linden-reasoning*, with its span-duality consumers re-proven.
2. `EL.PikeLkRegexRec`'s negative arm must recurse instead of demanding group-freeness, and
   `BoolTreeLk`'s negative gate must evaluate a body that itself contains gates (i.e. the oracle must
   carry columns for lids inside negative bodies — the oracle builder already assigns them lids, so
   this is mostly about the invariants, not the engine).
3. The nested static package (`GateStaticAtNested`'s negative arm, currently
   `(la.NegLookbehind? || la.NegLookahead?) ==> NR.CaptureFreeRE(body)`) and the frame lemmas would
   need the negative-body case of the depth-k tower.

Note this is **orthogonal** to §2.1: it is a spec-side fragment restriction inherited from L3/L4, not
a consequence of the L5 work.

### 2.3 / 2.4 — CAPTURE-UNDER-QUANTIFIER conditions. **Narrower than previously documented (corrected 2026-08-30)**

Both conditions are conjuncts of `SupportedL4` / `SupportedL5` **only**; neither appears in
`SupportedL3`, which is just `NR.LookBehindFragmentRaw(p) && T.Latin1Wf(p)`. Since
`Supported == SupportedL3 || SupportedL4 || SupportedL5`, a DEPTH-1 pattern takes the L3 disjunct and
never meets them. The previous text named two patterns as out of scope that in fact verify today:

| pattern | | status |
|---|---|---|
| `(?=(a)*)` — capture under a quantifier inside a look body | §2.3's own example | ✅ **`SupportedL3`, verified** |
| `((?=(a)))*` — capturing look inside a quantifier body | §2.4's own example | ✅ **`SupportedL3`, verified** |
| `(?=(?=(a)*))` / `((?=(?=(a))))*` | the nested forms | ❌ out — nesting forces L4/L5 |

Pinned by `src/Equiv/NullablePlusWitness.dfy` (4 lemmas each way), so the prose cannot drift from the
predicates again.

**So the honest statement of each gap is a CONJUNCTION**, not a single condition:

* **§2.3** (`NR.LookBodiesNoCapUnderQuantRaw`) — a capture under a quantifier inside a look body,
  **in a pattern that requires L4/L5** (the look body itself contains looks, or a positive
  lookbehind is present).
* **§2.4** (`NR.QuantsLookCapFreeRaw`) — a capturing look inside a quantifier body, same proviso.

**Why the split falls exactly there.** Both conditions exist to feed the DEPTH-K DESCENT in
`lift-sim-*`: `M.GNotUnderQuantL` gives `PIV.AncQuants(body, g) == {}`, which makes
`M.MxAtGidNoQuant` collapse the clock-dominance threshold `PIV.MxAtGidLk` to `-1`, so
`FilterKeepsPresentLk`'s obligation `cc[start(g)] >= MxAtGidLk(...)` is FREE from a merely set
(`>= 0`) clock. `M.PathPresentNoQuantFromAncCapsSet` says so in as many words — *"the whole
clock/path algebra collapses to 'ancestor captures are set'"*. The depth-1 path never enters that
descent, so it never incurs the hypothesis.

The underlying engine rule is `AI.filter_capture` (`Interpreter.dfy:992`), which threads a
`maxclock`: at `Re_quant` a stamp below it clears the whole body, and at `Re_capture` a start clock
below it clears the group. A capture under a quantifier survives iff its write-clock is at least the
quantifier's last-iteration stamp — that is how `(a)*` on `"ab"` ends with group 1 = `"b"`.

### Widening §2.3/§2.4 to L4/L5 — FEASIBLE, and the argument already exists

The general dominance fact is NOT the collapse, and the main pass already proves it:
`PS.MxAtGidLE` — *"every stored register clock is `<= S`, so a fresh stamp `S+1` beats
`PIV.MxAtGid`'s threshold for any group id"* — discharges `clk >= MxAtGid` at the Open/Close write
sites (`PikeSimRE.dfy:503,606`) for ANY capture, quantifier ancestors included, with no `AncQuants`
hypothesis. And a look body's captures are reconstructed by a full `AI.FFindMatchPlus` replay of
`capture_regex(la, body)`, whose final thread satisfies that same PikeSim invariant.

So the fact needed is provable by machinery that exists; the descent simply took a shortcut. Scope:

1. **The crux / main unknown — the replay invariant is VALUE-ONLY.** `M.FLookLoopValueOkFull` carries
   `CM.RegsAgreeInside(res0, rf.capture_regs, …)` — register agreement, not the path/clock facts. The
   dominance must be re-derived at each carrier from the replay's PikeSim invariant, or that
   invariant strengthened and re-threaded through `FLookLoop`. Settle this first: it decides the size.
2. Replace `M.PathPresentNoQuantFromAncCapsSet` with a general producer (its `PIV.PathPresentIntro`
   obligations are then real per-ancestor clock facts, not vacuous/free).
3. Sweep the **32** `requires GNotUnderQuantL / AncQuants == {}` sites across 10 files, including the
   `lift-sim-{core,carriers,deep,forward,chain,oracle}` giants (tens of minutes per run).

**Estimate: larger than §2.5a, smaller than §2.5b.** §2.5a was cheap because the engine's
`BeginLoop`/`EndLoop` already sat exactly where the spec's `Acheck` was — no new argument at all.
§2.5b needs a `CheckNullable`/`cdns` correspondence that exists in NO form. This one sits between:
the argument exists and needs porting into the look-body replay.

### 2.5 Nullable unbounded quantifiers — SPLIT; §2.5a DONE 2026-08-30, §2.5b-CIN DONE for lookaround-free patterns 2026-11-05

`R.nullable`/`raw_nullable` and `quant.greedy` select one of FOUR compiler schemes for an
unbounded `min > 0` quantifier (`Compiler.dfy:104-156`), not one:

| body | greedy | scheme | status |
|---|---|---|---|
| `NonNullable` | either | do-while (min-1 copies, stamp, body, backward fork) | ✅ always was |
| nullable | **lazy** | the GENERIC scheme — `repeat_min(min)` then the ordinary star loop | ✅ **§2.5a, DONE** |
| `CINullable` | greedy | end-fork + `SetQuantToClock(qid, true)` | ✅ **lookaround-free patterns** (`SupportedCin` → `MCIN.MainTheoremCin`, 2026-11-05, branch `nullable-plus-greedy`); ❌ next to a lookaround (machine B of the lift-sim band is not stamp-aware: rung F-c, `NULLABLE_PLUS_HANDOFF.md`) — `SupportedL3/4/5` keep `NoNulledPlusRaw` |
| `CDNullable` | greedy | end-fork + **`CheckNullable(qid)`** | ❌ out of scope for §2.5b-CIN (no representation) |

**§2.5a (done).** `(a?)+?`, `(a?){2,}?` and friends verify. Nothing nullability-specific was
needed: the generic scheme's output IS `NfaRepMinRE(min, …)` followed by the STAR arm's shape, and
the spec unfolds `Quantified(g, min>0, Inf, r1)` into `min` forced copies (no `Acheck`) then the
star (`ComputeIsTree.dfy:64-75`) — so the engine's `BeginLoop`/`EndLoop` sits exactly where the
spec's check is. The do-while needs `NonNullableL` ONLY to manufacture a check at its `min == 1`
seam via `CE.BoolCheckInsert` (whose `ConsumesBeforeAreg` hypothesis *is* non-nullability); the
generic scheme has the real one in the code, so it needs no such hypothesis.
Non-vacuity is pinned by `src/Equiv/NullablePlusWitness.dfy`.

**§2.5b-CIN for lookaround-free patterns (done 2026-11-05).** `API.SupportedCin(p) :=
NestedFragmentRaw(p) && Latin1Wf(p) && LookFreeRaw(p)` — no nulled-plus gate — is proved by
`LindenElkMainCin.MainTheoremCin`: machine A's simulation (rung D, reconstruction-aware readout
`GmOfLiveR`) pins the best thread to the checked tree's first leaf, which equals the spec tree's
first leaf (rung C, `ResAgreeAtOutside` with `S = {}`), and the engine's `FReconstructPlus` reads out
exactly that readout (rung E's `ReconReadout`, discharged at the best thread by rung F-b's
`FinalReadout`). `(a?)+` is pinned as supported and `(?=a)(a?)+` as still out by
`NullablePlusWitness.dfy`. The CDN-greedy scheme (`CheckNullable`) stays out (the nested fragment's
`Plus` arm excludes `CDNullable` bodies). The history below is kept as the design record.

**§2.5b (the design record) — the expensive half.** Three things break at once for the GREEDY nullable schemes:
1. **`CheckNullable` has no representation.** `TreeRepRE.dfy:289` / `GenStepRE.dfy:103` map it to
   `false`, and ~10 `NoCheckNullable` conjuncts exclude it from the sweeps. It needs a tree-rep arm
   tied to the `cdns` table (`build_cdn_v`/`compile_cdns`) — an engine↔spec correspondence for
   *context-dependent nullability at a position*, which exists in no form today.
2. **`QuantRegsFinal` dies.** `MainTheorem.dfy:117-131` rests on "fragment code only ever emits
   `SetQuantToClock(q, false)`", which makes `M.FNulledPlusIdentity` collapse `AI.FNulledPlus`. The
   greedy-nullable schemes emit `SetQuantToClock(qid, true)`. (§2.5a does NOT disturb this:
   `FCompileExtra` writes `f_plus_bc` only under `nul != NonNullable && quant.greedy`, so the table
   stays empty across the whole §2.5a fragment — proved in `FCompileExtraPlusFrame`.)
3. **`FNulledPlus`'s spec correspondence is the actual new theorem** (`Interpreter.dfy:418-491`).

### 2.6 Flags and alphabet

`MatcherSpec` is instantiated at `RER(false, false, false, NGroups(raw))`. So **`i`, `m`, `s` are out**,
as is any non-Latin-1 input (`T.Latin1Wf`). Named groups and sticky/global flags do not exist in the
AST. Lifting `ignoreCase`/`multiline` is a separate campaign: both appear as `rer` fields threaded
through hundreds of lemmas that currently assume `!rer.ignoreCase && !rer.multiline`.

### 2.7 Backreferences — excluded BY DESIGN

`R.raw_regex` has no backreference constructor (the spec side has `L.Backreference`; the RegElk AST
does not). This is deliberate and permanent: RegElk is a Pike/NFA-style engine with a linear-time
guarantee, and backreferences are not expressible in that model. This one is not "future work".

### 2.8 The shape of everything else

**Modulo §2.7, every restriction listed above is proof work, not an engine or semantic obstacle.**
The engine already implements the constructs; it is the *fragment predicates in the proof* that are
narrower than the engine. Concretely checkable evidence:

* Lookarounds inside NEGATIVE bodies are already compiled and already get oracle lids —
  `CP.FCompileExtra` recurses into `body` at every `Re_lookaround` node regardless of the look's kind,
  and `FBuildLids` builds their oracle columns. §2.2 is `SD.GroupFreeL`/`EL.PikeLkRegexRec` being
  depth-1 for negative gates, nothing more.
* Nullable plus already has its engine machinery (`f_plus_bc`, `AI.FNulledPlus`,
  `AI.FReconstructPlus`) — §2.5 is the missing spec correspondence.
* `ignoreCase` / `multiline` are fields of the `RegExpRecord` that both sides already thread; the
  proofs simply pin them to `false` (`!rer.ignoreCase && !rer.multiline` appears as a hypothesis
  throughout). §2.6 is a mechanical widening — very large, but not novel mathematics.

So the honest statement of the end state is: **a linear-time, backreference-free ECMAScript regex
engine, verified against the ECMAScript backtracking tree semantics, capture values included** — with
the current fragment a strict subset of that target, and every gap between here and there being
proof engineering of known shape.

---

## 3. Ranking the remaining work

| Gap | Effort | Notes |
|---|---|---|
| ~~§2.1 lookbehind inside lookahead~~ | — | **DONE 2026-08-30** (s8: packaged, no isolation) |
| §2.3 / §2.4 capture-under-quant **for L4/L5 patterns** | medium–large | depth-1 already covered; port `MxAtGidLE`-style dominance into the look-body replay, then sweep 32 hypothesis sites |
| ~~§2.5a lazy nullable plus~~ | — | **DONE 2026-08-30** (branch `nullable-plus`) |
| §2.5b greedy nullable plus **next to a lookaround** (lookaround-free: **DONE 2026-11-05**) | large — rung F-c: machine B (lift-sim band) stamp-aware, the C+D template on the B side | TWO end-fork layouts (CIN/CDN), the new `CheckNullable` instruction, the first `SetQuantToClock(qid, **true**)` (breaks the all-stamps-false invariant `NI.CodeShapeAt` proves and `MainTheoremL3` consumes), a second path in `ReconstructNulled`, plus `QuantRegsFinal` and `FNulledPlus`'s unproven spec tie. The §2.5a shift-to-`em` rewrite does NOT carry over — see `NULLABLE_PLUS_HANDOFF.md` § WHAT §2.5b ACTUALLY COSTS |
| §2.2 nested looks in negative bodies | large | touches linden-reasoning's `GroupFreeL` and `BoolTreeLk` |
| §2.6 flags (`i`, `m`) / Unicode | very large | new campaign |
| §2.7 backreferences | **by design** | absent from the engine AST; incompatible with a Pike/NFA engine |

Hygiene item, independent of the above: **per-symbol verification never well-formedness-checks helper
functions/predicates**. CLOSED BY CONSTRUCTION 2026-08-30: the gate is now the whole-workspace `lem pack`
(61 packages, whole-file, dependency-ordered, warning-free, 900 s per batch) — see
`docs/LEMMATA_IN_PROOF_DEVELOPMENT.md`; the E3 loop in `AGENTS.md` is how a lemma that will not pack gets
sectioned. Earlier step, DONE 2026-08-28: a whole-file well-formedness sweep of all 51 files plus
FULL-file verification of every file except `LiftSim.dfy` (whose four giants keep their per-symbol
records; the rest of the file runs whole with the giants excluded) — see `L5_HANDOFF.md` §5.7.3. The
sweep found a resolution error in `ApiMatch.dfy` (`SupportedL5` called a ghost predicate), a wf hole
in `LookNestOkTTop`, and a lemma broken by the `RevRE` change (`ZeroSetCapRevRE`); all fixed.
