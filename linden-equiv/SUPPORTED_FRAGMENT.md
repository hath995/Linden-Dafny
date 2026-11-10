# The verified fragment — what `Match` is guaranteed to get right

> Verification status (2026-11-10): the entire equivalence — `linden.equiv` and its 67 dependency packages —
> verifies under `lem pack` with `lem` 0.1.23 and z3 4.14.1 (68/68, one z3 worker), through §2.2 step B and the
> collapse of `Supported` to one predicate, on branch `supported-collapse` (`66f9651`).

Entry point: `ApiMatch.MatchCorrect(pattern, str)`:

```dafny
lemma MatchCorrect(pattern: R.raw_regex, str: string)
  requires Supported(pattern)
  ensures LES.MatcherSpec(pattern, str, Match(pattern, str))
```

`Match` runs the compiled RegElk engine and normalizes the result into the JS-style capture array.
`MatcherSpec` is the ECMAScript **backtracking tree semantics** (Linden). So the guarantee is not
"same yes/no answer" but "same match AND the same capture array, group by group".

`Supported(p)` is one executable predicate (`ApiMatch.dfy`), and it is exactly the precondition of the one theorem
behind `MatchCorrect`, `MCL.MainTheoremL5Cin`. Its conjuncts are `NR.NestedFragmentRaw`, `T.Latin1Wf`,
`LSIMCOR.L5ScopeV1RE`, `EL.NegBehindLBOnlyRaw`, `MCL.LooksNoNulledPlusX` and `MCL.CinBodiesLookFreeX`.

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
| `+`, `{n,}` (n>0, unbounded) | ✅ non-nullable body (any greediness); ✅ **nullable body when LAZY** (`(a?)+?`, §2.5a, 2026-08-30); ✅ **CI-nullable body when GREEDY** (`(a?)+`, `(a\|)+`) **in lookaround-free patterns** (§2.5b, `SupportedCin`, 2026-11-05) **and next to lookarounds** (`(?=a)(a?)+`, §2.5b F-c, `SupportedL5Cin`, 2026-11-06) provided no look body holds a greedy nullable plus and every such plus has a lookaround-free body. ❌ greedy nullable plus **inside a look body** (`(?=(a?)+)`) or **with a lookaround in its body**; ❌ context-dependent-nullable greedy body (CDN, `CheckNullable`) |
| positive lookahead `(?=…)`, capturing, nested to any depth | ✅ (L4) |
| **positive lookbehind `(?<=…)`, capturing, nested to any depth** | ✅ (L5, 2026-08-28) — a lookbehind's body may contain **only lookbehinds**; a lookahead's body may contain positive lookbehinds (`(?=x(?<=y))`, the s6 widening — see §2.1) |
| **captures under a quantifier inside a look body, and capturing looks inside a quantifier, at any look depth** (`(?=(?=(a)*))`, `((?=(?=(a))))*`) | ✅ (§2.3/§2.4, 2026-11-08) |
| negative `(?!…)` / `(?<!…)` | ✅ capture-free body. A negative **lookahead**'s body may contain looks (`(?!a(?=b))`, §2.2 step A, 2026-11-09). A negative **lookbehind**'s body may contain lookbehinds (`(?<!a(?<=b))`, §2.2 step B, 2026-11-10). ❌ a lookahead inside a lookbehind body, either polarity (`(?<!a(?=a))`) |
| backreferences | ❌ not in the AST at all |

Newly provable at L5 (was impossible before): `(?<=a(?<=b)(c))`, `(?<=(x)(?<=(y)))` — capturing
lookbehinds nested inside capturing lookbehinds, **including the reversed-span capture values**
(the engine records a lookbehind's span backwards; the spec leaf is ordered — the tie is the
`NormRange`/`SwapRange` normalization).

The three fragments in one line each:

* **L3** — depth-1 lookaround only (`NR.LookBehindFragmentRaw`).
* **L4** — nested capturing **lookaheads**, no positive lookbehind anywhere (`NR.NoPosLookbehindRaw`).
* **L5** — nested capturing **lookbehinds** too, under `LSIM.L5ScopeV1RE` (see §2.1).

These names are history. `Supported` was a disjunction of five sub-fragments, each with its own theorem, until
2026-11-10. Commit `b90740b` proves every disjunct implies the widest one, so collapsing `Supported` to that one
predicate lost no pattern. `MainTheoremL3`, `L4`, `L5` and `MainTheoremCin` are gone, and sections below that name
`SupportedL3/L4/L5/Cin/L5Cin` describe the state at the time.

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

### 2.2 Nested looks inside a **negative** look body — `(?!a(?=b))` DONE 2026-11-09, `(?<!a(?<=b))` DONE 2026-11-10

| pattern | status |
|---|---|
| `(?!a(?=b))` — looks inside a negative **lookahead** body | ✅ step A |
| `(?<!a(?<=b))` — lookbehinds inside a negative **lookbehind** body | ✅ step B |
| `(?<!a(?=a))` — a lookahead inside a negative **lookbehind** body | ❌ the same restriction as a positive lookbehind |

The only look-related condition left is `EL.NegBehindLBOnlyRaw`: a negative lookbehind's body may contain only
lookbehinds. Every negative body must also be capture-free, at any depth (`NR.NestedFragmentRaw`). All three rows are
pinned by `Frag22_*` in `src/Equiv/NullablePlusWitness.dfy`.

**How step A went.** The plan recorded here before the rung expected a change to `SD.GroupFreeL` in
*linden-reasoning*. It was not needed, and neither `linden-reasoning` nor `nfa-rep-re` changed.
* `EL.PikeLkRegexRec` now recurses into look bodies at either polarity. A negative body must define no groups
  (`EL.NegBodyNoDefs`). That conjunct is opaque, because inlining `L.DefGroups` into this hot predicate
  blew up `actions-tree-rep-re`.
* The tower's polarity branches only ever needed deep capture-freeness, so they stand unchanged.
* A negative gate that passes has no body leaves, so it needs no group-map neutrality (`LL.LAAtGatePassNeg`).

**How step B went.** The scope is now `la.NegLookbehind? ==> NR.LBOnlyLooksRE(body)`, the same restriction as a
positive lookbehind. Again neither `linden-reasoning` nor `nfa-rep-re` changed.
* The oracle column's separate look-free arm for negative lookbehinds is gone. Both lookbehind polarities go
  through `OE.OracleColumnSpecNested`.
* The flip route no longer needs `NR.NegLooksLookFreeRE`. The flip of a lookbehind-only body holds only lookaheads,
  so the scope condition is vacuous there (`NegBehindLBOnlyFXR`), and a negative body needs only `DefGroups == []`
  (`FD.NegBodiesGroupFree`).
* Three proof batches ran away under z3 4.14.1 once the context changed, with no change to the claims:
  `hide FST.FXR` in `FreshBodyMatchGmOuterLBNested`, the helper `GateStaticPick`, and a `hide *` in
  `ForwardFindRecLBBase`.

### 2.3 / 2.4 — CAPTURE-UNDER-QUANTIFIER conditions — CLOSED 2026-11-08

`NR.LookBodiesNoCapUnderQuantRaw` and `NR.QuantsLookCapFreeRaw` are gone from `Supported`. Depth-1 patterns never
met them; nested ones no longer do.

| pattern | | status |
|---|---|---|
| `(?=(a)*)` — capture under a quantifier inside a look body | §2.3, depth 1 | ✅ |
| `((?=(a)))*` — capturing look inside a quantifier body | §2.4, depth 1 | ✅ |
| `(?=(?=(a)*))` | §2.3, nested | ✅ (2026-11-08) |
| `((?=(?=(a))))*` | §2.4, nested | ✅ (2026-11-08) |
| `(?=(a)*)(a?)+` | §2.3 next to a greedy nullable plus | ✅ (2026-11-08) |

Pinned by `src/Equiv/NullablePlusWitness.dfy`.

**What the conditions were for.** The depth-k descent in `lift-sim-*` used `M.GNotUnderQuantL` to get
`PIV.AncQuants(body, g) == {}`, which collapsed the clock-dominance threshold `PIV.MxAtGidLk` to `-1`
and made `FilterKeepsPresentLk`'s obligation free. The engine rule is `AI.filter_capture`
(`Interpreter.dfy:992`): a capture under a quantifier survives iff its write-clock is at least the
quantifier's last-iteration stamp, which is how `(a)*` on `"ab"` ends with group 1 = `"b"`.

**Why no new invariant was needed.** The plan recorded here before the rung named the replay invariant
being value-only as the crux. It was not an obstacle. The dominance is already in the winner's
readout: the group is in `GmOfLive`, so `PIV.PathPresentLk` holds on the reconstructed banks, and
`FLookLoop`'s value lifts (`M.ValueOkO`, `M.QuantValueOkO`, both of which carry clocks) transport it
to the body's replay. The new lemmas are `ReverseLookDomOnFresh` and `PathPresentLkDirectAgreeQ`
(core), `OwnerPkgFromPresence` and `ProduceOwnerForallRes` (chain).

### 2.5 Nullable unbounded quantifiers — SPLIT; §2.5a DONE 2026-08-30, §2.5b-CIN DONE for lookaround-free patterns 2026-11-05 and next to lookarounds 2026-11-06

`R.nullable`/`raw_nullable` and `quant.greedy` select one of FOUR compiler schemes for an
unbounded `min > 0` quantifier (`Compiler.dfy:104-156`), not one:

| body | greedy | scheme | status |
|---|---|---|---|
| `NonNullable` | either | do-while (min-1 copies, stamp, body, backward fork) | ✅ always was |
| nullable | **lazy** | the GENERIC scheme — `repeat_min(min)` then the ordinary star loop | ✅ **§2.5a, DONE** |
| `CINullable` | greedy | end-fork + `SetQuantToClock(qid, true)` | ✅ **lookaround-free patterns** (2026-11-05); ✅ **next to lookarounds** (`MCL.MainTheoremL5Cin`, 2026-11-06) when the plus sits outside every look body and its own body is lookaround-free; ❌ inside a look body, or with a lookaround in its body |
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
`Plus` arm excludes `CDNullable` bodies).

**§2.5b-CIN next to lookarounds (rung F-c, done 2026-11-06).** `API.SupportedL5Cin(p)` is
`SupportedL5(p)` with `NoNulledPlusRaw` replaced by two executable checks on the annotated regex:
`MCL.LooksNoNulledPlusX` (no look body holds a greedy nullable plus) and `MCL.CinBodiesLookFreeX`
(every greedy CI-nullable plus has a lookaround-free body). It is proved by
`LindenElkMainCinLk.MainTheoremL5Cin` (member `linden-equiv-main-cin-lk`). The captures split at
`S = CapIdsInLooks(re)`:
* **Outside the looks** the values come from machine A (`FindMatchSimRENested`, no gate) plus rung C
  (`ResAgreeAtOutside`) and rung F-b (`FinalReadout`).
* **Inside the looks** they come from machine B, which now runs chain-free on the engine-shaped walk
  `CW.BoolTreeLkX` (member `linden-equiv-cin-walk`). There the stamp is a plain `Reset`.
* **The two halves meet at a synthetic winner.** `rp0` is `FReconstructPlus(best)` with the
  quantifier code points outside the looks cleared. Its readout and its answer are unchanged
  (`ClearQuantCpsGm`, `AnswerSynthetic`).
* **Rung G.** `(?=a)(a?)+` is pinned as supported by `NullablePlusWitness.dfy`.

The history below is kept as the design record.

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
  and `FBuildLids` builds their oracle columns. §2.2 is closed. What remains is a lookahead inside a
  lookbehind body, the same restriction at either polarity.
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
| ~~§2.3 / §2.4 capture-under-quant for L4/L5 patterns~~ | — | **DONE 2026-11-08** (branch `cap-under-quant`) |
| ~~§2.5a lazy nullable plus~~ | — | **DONE 2026-08-30** (branch `nullable-plus`) |
| §2.5b greedy nullable plus **inside a look body / with a lookaround in its body** (lookaround-free: **DONE 2026-11-05**; next to lookarounds: **DONE 2026-11-06**) | large — the look-body replay would need the reconstruction readout (rung E) at every look depth; machine B's look-path frame (`CinLookPaths`) assumes the CIN bodies own no look-path registers | TWO end-fork layouts (CIN/CDN), the new `CheckNullable` instruction, the first `SetQuantToClock(qid, **true**)` (breaks the all-stamps-false invariant `NI.CodeShapeAt` proves and `MainTheoremL3` consumes), a second path in `ReconstructNulled`, plus `QuantRegsFinal` and `FNulledPlus`'s unproven spec tie. The §2.5a shift-to-`em` rewrite does NOT carry over — see `NULLABLE_PLUS_HANDOFF.md` § WHAT §2.5b ACTUALLY COSTS |
| ~~§2.2 nested looks in negative bodies~~ | — | negative lookahead: **DONE 2026-11-09**, negative lookbehind: **DONE 2026-11-10** (branch `neg-look-nest`) |
| lookahead inside a lookbehind body, either polarity (`(?<=a(?=b))`, `(?<!a(?=a))`) | not yet sized | excluded by `L5ScopeV1RE` and `EL.NegBehindLBOnlyRaw` |
| captures inside a negative look body (`(?!(a))`) | not yet sized | excluded by the `CaptureFree` arm of `NR.NestedFragmentRaw` |
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
