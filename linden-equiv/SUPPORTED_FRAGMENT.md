# The verified fragment — what `Match` is guaranteed to get right

Status 2026-08-28, branch `l4-nesting`. Entry point: `ApiMatch.MatchCorrect(pattern, str)`:

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
| `+`, `{n,}` (n>0, unbounded) | ✅ **only with a non-nullable body** |
| positive lookahead `(?=…)`, capturing, nested to any depth | ✅ (L4) |
| **positive lookbehind `(?<=…)`, capturing, nested to any depth** | ✅ (L5, 2026-08-28) — body may contain **only lookbehinds** |
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

### 2.1 A positive lookbehind inside a **lookahead** body — `(?=x(?<=y))`

The v1 L5 scope is `LSIM.L5ScopeV1RE`:

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

### 2.3 A capture under a quantifier **inside a look body** — `(?=(a)*)`

`NR.LookBodiesNoCapUnderQuantRaw`. The engine's clock/dominance argument for reconstructing a capture
value inside a look body assumes the capture is not re-entered by a loop
(`M.GNotUnderQuantL`, `PIV.AncQuants(body, g) == {}`). Every descent lemma carries it as a hypothesis.

### 2.4 A capturing look inside a **quantifier** body — `((?=(a)))*`

`NR.QuantsLookCapFreeRaw`. Same clock argument from the other side: a quantifier may not re-run a gate
that writes captures.

### 2.5 Nullable unbounded quantifiers — `(a?)+`

`NR.NestedFragmentRaw` requires a non-nullable body for `+`/`{n,}`. (`a*` with a nullable body is
fine — `min == 0`.) The engine has "nulled plus" reconstruction machinery (`f_plus_bc`,
`FNulledPlus`); extending the fragment here means proving its spec correspondence.

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
| §2.1 lookbehind inside lookahead | medium | pure perf engineering; the fix pattern is known (§5.7.2) |
| §2.3 / §2.4 capture-under-quant conditions | medium–large | needs a real clock/dominance argument, not a dispatch |
| §2.5 nullable plus | medium | machinery exists (`FNulledPlus`), correspondence unproven |
| §2.2 nested looks in negative bodies | large | touches linden-reasoning's `GroupFreeL` and `BoolTreeLk` |
| §2.6 flags (`i`, `m`) / Unicode | very large | new campaign |
| §2.7 backreferences | **by design** | absent from the engine AST; incompatible with a Pike/NFA engine |

Hygiene item, independent of the above: **per-symbol verification never well-formedness-checks helper
functions/predicates** — a whole-file prefix sweep of `LiftSim.dfy` / `MainTheorem.dfy` /
`FlipClosed.dfy` is what would make "green" airtight (this gap hid three real holes earlier in the
campaign).
