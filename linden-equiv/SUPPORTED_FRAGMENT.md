# The verified fragment — what `Match` is guaranteed to get right

> Verification status (2026-11-11): the entire equivalence — `linden.equiv` and its dependency packages —
> verifies under `lem pack` with `lem` 0.1.23 and z3 4.14.1 (72/72 members, one member at a time, at most two
> z3 workers each), through the full-depth look nesting of §2.1a and the negative-body captures of §2.2a, on
> branch `endgame` (`fd68916`). No `{:isolate_assertions}` remains anywhere in shipped code.

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
`MCL.BehindBodiesNoNulledPlusX` (no LOOKBEHIND body holds a greedy nullable plus; lookahead bodies may, §2.5c) and
`MCL.CinBodiesLookFreeX`. The two look-nesting scope conjuncts (`LSIMCOR.L5ScopeV1RE`, `EL.NegBehindLBOnlyRaw`)
were deleted on 2026-11-11 (§2.1a): no condition on which kind of look may sit inside which remains.
`NR.NestedFragmentRaw` no longer asks a negative look's body to be capture-free (§2.2a).

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
| `+`, `{n,}` (n>0, unbounded) | ✅ non-nullable body (any greediness); ✅ **nullable body when LAZY** (`(a?)+?`, §2.5a, 2026-08-30); ✅ **CI-nullable body when GREEDY** (`(a?)+`, `(a\|)+`) **in lookaround-free patterns** (§2.5b, `SupportedCin`, 2026-11-05) **and next to lookarounds** (`(?=a)(a?)+`, §2.5b F-c, `SupportedL5Cin`, 2026-11-06) provided every such plus has a lookaround-free body; ✅ **greedy CI-nullable plus inside a LOOKAHEAD body**, either polarity (`(?=(a?)+b)`, `(?!(a?)+b)`, §2.5c, 2026-11-12). ❌ greedy nullable plus **inside a LOOKBEHIND body** (`(?<=(a?)+)`, G3b) or **with a lookaround in its body** (G4); ❌ context-dependent-nullable greedy body (CDN, `CheckNullable`) |
| positive lookahead `(?=…)`, capturing, nested to any depth | ✅ (L4) |
| **positive lookbehind `(?<=…)`, capturing, nested to any depth** | ✅ (L5, 2026-08-28) |
| **any look inside any look, all four kinds, to any depth** (`(?<=a(?=a))`, `(?<=(?=(a))a)`, `(?<!a(?=a))`, `(?=(?<=a(?=a)))`) | ✅ (§2.1a, 2026-11-11). Before this a lookbehind's body, positive or negative, could hold only lookbehinds |
| **captures under a quantifier inside a look body, and capturing looks inside a quantifier, at any look depth** (`(?=(?=(a)*))`, `((?=(?=(a))))*`) | ✅ (§2.3/§2.4, 2026-11-08) |
| negative `(?!…)` / `(?<!…)` | ✅ any body the rest of the fragment allows, including capture groups (`(?!(a))`, `(?<!(a))`, `(?<!a(?=(a)))`, §2.2a, 2026-11-11). The result agrees with the spec, which leaves those groups undefined (ECMAScript: a negative look that passes has no body match). The witnesses show only that the patterns are `Supported` |
| backreferences | ❌ not in the AST at all |

Newly provable at L5 (was impossible before): `(?<=a(?<=b)(c))`, `(?<=(x)(?<=(y)))` — capturing
lookbehinds nested inside capturing lookbehinds, **including the reversed-span capture values**
(the engine records a lookbehind's span backwards; the spec leaf is ordered — the tie is the
`NormRange`/`SwapRange` normalization).

The three fragments in one line each:

* **L3** — depth-1 lookaround only (`NR.LookBehindFragmentRaw`).
* **L4** — nested capturing **lookaheads**, no positive lookbehind anywhere (`NR.NoPosLookbehindRaw`).
* **L5** — nested capturing **lookbehinds** too, at first under `LSIM.L5ScopeV1RE` (see §2.1), a scope
  predicate that was deleted on 2026-11-11 (§2.1a).

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

### 2.1a A lookahead inside a **lookbehind** body — `(?<=a(?=a))` — CLOSED 2026-11-11

Status: **in scope and shipped** (branch `endgame`, `eacf6ec`, `lem pack` 72/72). This was the last condition
on look nesting. `LSIMCOR.L5ScopeV1RE` and `EL.NegBehindLBOnlyRaw` are deleted from `Supported`, and the gate
hub `LSIM.GateStaticAtNested` no longer carries a kind-split scope conjunct.

| pattern | what it pins |
|---|---|
| `(?<=a(?=a))` | a lookahead inside a positive lookbehind |
| `(?<=(?=(a))a)` | a **capturing** lookahead inside a positive lookbehind |
| `(?<!a(?=a))` | a lookahead inside a negative lookbehind (was `Frag22_NegBehindAheadStillOut`, now `Frag22_NegBehindAheadIn`) |
| `(?=(?<=a(?=a)))` | the mixed body one level down, under a lookahead |

The witnesses are in `src/Equiv/LookNestWitness.dfy` and `src/Equiv/NullablePlusWitness.dfy`.

**Why it had been out.** A lookbehind row is proved by mirroring: the engine runs the reversed body backwards,
and the proof flips it into a forward run on the reversed string. The mirror lemmas were stated for
lookbehind-only bodies, where every inner look flips to a lookahead and the flipped body is uniform. A
lookahead inside the body flips to a lookbehind, so the flipped body is mixed, and three places assumed it
was not: the oracle column for a lookbehind row, the flip mirror of the body's tree, and the descent arms
that walk from a lookbehind into its inner looks.

**How it went.** Neither `linden-reasoning` nor the engine changed.
* **Oracle column.** The lookbehind branch of `OracleColumnNested` used `OE.OracleColumnSpecNested`, which
  goes through the spec-side `SD.MatchesL` and has no lookahead clause for backward bodies. It now takes the
  route the lookahead branch always took, in the mirrored world: bit ⇔ `MatchesV` ⇔ mirrored `MatchesV`
  (`OMV.MatchesVMirror`, which never had a fragment premise) ⇔ the flipped body's forward tree has a leaf ⇔
  the backward tree has a leaf. The new leaf package is `linden-equiv-mirror-world`.
* **Flip mirror.** The tree mirror relation and its closedness lemma are direction-generic: the look arm no
  longer pins the inner look's direction.
* **Descent.** The lookbehind arms of `DeepFindRec` and `ForwardFindRec` take a mixed host. The two lemmas
  that still needed `{:isolate_assertions}` there (`DeepFindRecFwdDeep`, `LookNestBackTTopDeepLidFlip`) were
  rewritten without it.
* The hub's two scope conjuncts turned out to be threading only: no gate step consumed
  `NegBehindLBOnlyRE(body)`.

### 2.2 Nested looks inside a **negative** look body — DONE 2026-11-09 / 11-10; the lookahead-in-lookbehind row DONE 2026-11-11

| pattern | status |
|---|---|
| `(?!a(?=b))` — looks inside a negative **lookahead** body | ✅ step A |
| `(?<!a(?<=b))` — lookbehinds inside a negative **lookbehind** body | ✅ step B |
| `(?<!a(?=a))` — a lookahead inside a negative **lookbehind** body | ✅ §2.1a |

No look-related scope condition is left, and a negative body may hold capture groups (§2.2a). All three rows
are pinned by `Frag22_*` in `src/Equiv/NullablePlusWitness.dfy`.

**How step A went.** The plan recorded here before the rung expected a change to `SD.GroupFreeL` in
*linden-reasoning*. It was not needed, and neither `linden-reasoning` nor `nfa-rep-re` changed.
* `EL.PikeLkRegexRec` now recurses into look bodies at either polarity. A negative body must define no groups
  (`EL.NegBodyNoDefs`). That conjunct is opaque, because inlining `L.DefGroups` into this hot predicate
  blew up `actions-tree-rep-re`. (`EL.NegBodyNoDefs` was deleted on 2026-11-11, §2.2a.)
* The tower's polarity branches only ever needed deep capture-freeness, so they stand unchanged.
* A negative gate that passes has no body leaves, so it needs no group-map neutrality (`LL.LAAtGatePassNeg`).

**How step B went.** The scope is now `la.NegLookbehind? ==> NR.LBOnlyLooksRE(body)`, the same restriction as a
positive lookbehind. Again neither `linden-reasoning` nor `nfa-rep-re` changed.
* The oracle column's separate look-free arm for negative lookbehinds is gone. Both lookbehind polarities go
  through `OE.OracleColumnSpecNested`.
* The flip route no longer needs `NR.NegLooksLookFreeRE`. The flip of a lookbehind-only body holds only lookaheads,
  so the scope condition is vacuous there (`NegBehindLBOnlyFXR`), and a negative body needs only `DefGroups == []`
  (`FD.NegBodiesGroupFree`, deleted on 2026-11-11, §2.2a).
* Three proof batches ran away under z3 4.14.1 once the context changed, with no change to the claims:
  `hide FST.FXR` in `FreshBodyMatchGmOuterLBNested`, the helper `GateStaticPick`, and a `hide *` in
  `ForwardFindRecLBBase`.

### 2.2a Capture groups inside a negative look body — `(?!(a))` — CLOSED 2026-11-11

Status: **in scope and shipped** (branch `endgame`, `fd68916`, `lem pack` 72/72). Witnesses: `(?!(a))`, `(?<!(a))`,
`(?<!a(?=(a)))` (`LookNestWitness.CaptureInNegativeLookIsSupported`, `src/Equiv/LookNestWitness.dfy`). The
witness proves `Supported(p)` only; that the groups come out undefined follows from `MatchCorrect` and the
spec's negative look being a bare gate, and is not pinned by a concrete `Match` result lemma.

The semantics is simple and the engine already had it: a negative look that passes has no body match, so
the spec leaves every group defined inside it undefined. `NegCheckOracle` never writes a look register, the
compiler's capture replay for a negative look is the empty regex, and `filter_capture` clears every group
under a look whose record is unset.

**Why it had been out.** The proof used "negative bodies are capture-free" as a shortcut in two ways. On the
spec side, `EL.PikeLkRegexRec` required a negative body to define no groups. On the engine side, seven descent
sites argued "this group sits under a look whose record is set, and negative bodies have no groups, so the
look is positive".

**How it went.**
* **Engine side.** One invariant on the look bank replaces the shortcut: *a look record that is set belongs
  to a positive look* (`LB.LookSetIn(look_regs, LB.PosLookIds(re))`, package `linden-equiv-look-bank`). It
  holds because only `CheckOracle` writes the look bank. It is a conjunct of `M.WinRegsOk` and of its
  gate-free twin `MCL.WinRegsOkG`, and `M.LookPosO(res1, crv)` is threaded as a premise through the descent.
  `M.MatchedPosFromBank` replaces the hub's `CaptureFreeRE` clause at the five `res1` sites, and
  `M.FreshReplayLookPos` + `MatchedPosFromBank` at the two fresh-replay sites.
* **Spec side.** No new case was needed. `PikeLkRegexRec`'s look arm is now just the recursive call,
  `EL.NegBodyNoDefs` and `FD.NegBodiesGroupFree` are deleted, and `LL.LkBodiesInS` no longer distinguishes
  look kinds (its look arm is the opaque `LL.LookBodyInS`).
* `NR.NestedFragmentRE/Raw`'s look arm is the recursive call for all four kinds. `nfa-rep-re` changed, so
  this was a full rebuild of the tower.
* **Cost.** No claim changed beyond the above, but the bare recursive look arms made z3's automatic induction
  hypothesis loop in seven lemmas, which now carry `{:induction false}`, and pushed two single-batch lemmas
  (`ComputeTreeGBodyOK`, `WalkPairLkAtSetQuantCoreRec`) past 900 s until they were split per match arm.

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

### 2.5c A greedy CI-nullable plus inside a LOOKAHEAD body — `(?=(a?)+b)` — CLOSED 2026-11-12 (G3a)

The engine replays a look body with `FFindMatchPlus` (`AI.FLookLoop`), the same match-then-reconstruct
function the top level uses, with the same `f_plus_bc` table. The proof now follows that replay at every
lookahead row, at any depth:
* **The row.** A lookahead row's value is the fresh plus replay `M.FreshBodyMatchPlus`, reconstructed at the
  row (`RowReconAt`, member `linden-equiv-plus-at`) and tied to the running look loop by two congruences
  (`ReconAgree`, `LookLoopAgreeFrom`). Lookbehind rows keep their stamp-free twins.
* **Machine A at a body** (`linden-equiv-machine-a`): the fresh plus winner's readout against the body's spec
  leaf (`ReadoutAtWinnerAt`, `MachineAAt`); the gate tier's crossing (E4) and the oracle pair use it.
* **The two machines at a body** (`linden-equiv-two-machines`, `TwoMachinesAt`): machine B's tie moved to the
  reconstructed winner, which is what the band's look carriers name.
* **The gate.** `M.LookBodiesPlusGateRE`: lookbehind bodies nulled-plus-free, lookahead bodies in the CIN
  fragment, recursively. The executable twin is `MCL.BehindBodiesNoNulledPlusX` plus `MCL.CinBodiesLookFreeX`
  (`BehindBodiesGateSound`).
Witnesses: `NullablePlusWitness.G3a_PlusInLookahead` (`(?=(a?)+b)`, `(?!(a?)+b)`).
Still out: a greedy nullable plus in a lookbehind body (G3b), a lookaround inside a greedy nullable plus's
body (G4), CDN-greedy pluses (G5).

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
  and `FBuildLids` builds their oracle columns. §2.2 and §2.1a are closed: no restriction on look nesting
  remains.
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
| §2.5b greedy nullable plus **inside a look body / with a lookaround in its body** (lookaround-free: **DONE 2026-11-05**; next to lookarounds: **DONE 2026-11-06**; inside a LOOKAHEAD body: **DONE 2026-11-12**, §2.5c; inside a lookbehind body: G3b; a look in its body: G4) | large — the look-body replay would need the reconstruction readout (rung E) at every look depth; machine B's look-path frame (`CinLookPaths`) assumes the CIN bodies own no look-path registers | TWO end-fork layouts (CIN/CDN), the new `CheckNullable` instruction, the first `SetQuantToClock(qid, **true**)` (breaks the all-stamps-false invariant `NI.CodeShapeAt` proves and `MainTheoremL3` consumes), a second path in `ReconstructNulled`, plus `QuantRegsFinal` and `FNulledPlus`'s unproven spec tie. The §2.5a shift-to-`em` rewrite does NOT carry over — see `NULLABLE_PLUS_HANDOFF.md` § WHAT §2.5b ACTUALLY COSTS |
| ~~§2.2 nested looks in negative bodies~~ | — | negative lookahead: **DONE 2026-11-09**, negative lookbehind: **DONE 2026-11-10** (branch `neg-look-nest`) |
| ~~lookahead inside a lookbehind body, either polarity~~ | — | **DONE 2026-11-11** (§2.1a, branch `endgame`, `eacf6ec`) |
| ~~captures inside a negative look body~~ | — | **DONE 2026-11-11** (§2.2a, `fd68916`) |
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
