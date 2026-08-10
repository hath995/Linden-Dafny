# L3b Handoff — captures inside positive LOOKBEHINDS (updated 2026-08-10)

**Goal:** extend `MainTheoremL3`/`ApiMatch.Supported` (L3a: capturing positive
lookaheads, DONE — see `L3_PROOF_MAP.md`) to also admit **captures inside
positive lookbehinds** — `(?<=(a))`, `(?<=(ab))c`, etc. — closing the last
capturing-lookaround gap before L4 (nesting).

**Branch:** `l3b-backward-value`, off `l3a-liftsim-scaffold`. Two commits so
far, both self-contained proof files, no existing file edited yet:

```
c01f9bf L3b item 4b: TreeMirror.dfy — the PRIORITY-AWARE tree-level reversal PROVEN
d2b2cb2 L3b item 4a: BackValue.dfy — the backward capture replay transported to a forward run
```

This is a monorepo (`Linden-Dafny`) — `linden-equiv/` and `linden-reasoning/`
share one git history/branch; `git log` from either subdirectory shows both
commits.

**Source doc:** `LOOKAROUND_CAMPAIGN.md` §4.5.1 lists the six work items in
dependency order. This handoff supersedes that outline where the two now
differ (item 4 turned out to split into an engine half and a spec half, and a
**new item 0** was discovered — see §2 below). The running narrative log (the
"why", session by session) is in the `linden-l3-campaign` memory
(`~/.claude/projects/-home-aaron-code/memory/linden-l3-campaign.md`,
**session 10** is the L3b entry — read that section first if you want the
blow-by-blow instead of this summary).

**Task list:** this session tracked the six §4.5.1 items as tasks #1–#6 (task
tool). #4 (the backward value crux) is `in_progress` — its engine half and
spec half are both proved; what remains is the assembly (§3 below). #1, #2,
#3, #5, #6 are still `pending` and untouched.

---

## 0. Verify recipes

**`linden-equiv/` files** (BackValue.dfy lives here):
```
cd linden-equiv
"$DAFNY" verify src/Equiv/<File>.dfy --standard-libraries \
  --library=deps/linden-engine-model.doo --library=deps/linden-engine.doo \
  --library=deps/linden-reasoning.doo --library=deps/linden-semantics-core.doo \
  --library=deps/linden-warblre.doo --library=deps/regex-engine.doo \
  --verification-time-limit=900 --filter-symbol=<Name>
```

**`linden-reasoning/` files** (TreeMirror.dfy lives here — smaller dep set):
```
cd linden-reasoning
"$DAFNY" verify src/Equiv/<File>.dfy --standard-libraries \
  --library=deps/linden-semantics-core.doo --library=deps/linden-warblre.doo \
  --library=deps/regex-engine.doo \
  --verification-time-limit=600 --filter-symbol=<Name>
```

`$DAFNY` = `~/.local/share/lemmata/toolchains/4.11.0/dafny/dafny` (4.11.0;
the PATH `dafny` is 4.10 and cannot load these `.doo`s).

**IMPORTANT — the dependency bridge.** `linden-equiv/deps/linden-reasoning.doo`
is a SNAPSHOT. If a `linden-reasoning` file changes (as it did here —
`TreeMirror.dfy` is new) and a `linden-equiv` proof needs to see it, rebuild
and copy:
```
cd linden-reasoning
"$DAFNY" build -t:lib dfyconfig.toml --no-verify
cp linden-reasoning-*.doo ../linden-equiv/deps/linden-reasoning.doo   # check the actual output name
```
`lem restore` reverts this — don't run it until the bridge is no longer
needed, or re-copy afterward. (Not yet done this session — `BackValue.dfy`
didn't need `TreeMirror.dfy` yet; the assembly lemma in §3 will.)

---

## 1. What's proved

### `linden-equiv/src/Equiv/BackValue.dfy` (5 verified, 0 errors)

The **engine** half: transports a lookbehind's backward capture replay to a
forward run, via `Mirror.dfy`'s existing state isomorphism.

| Lemma | Role |
|---|---|
| `SwapRevIsRevRE(r)` | For look-free `r`: `OBu.SwapAnchorsRegex(R.reverse_regex(r)) == SD.RevRE(r)` — the engine's own anchor-swap-of-reversal IS SpanDuality's `RevRE` (engine reversal + anchor swap combined). |
| `CompileToBytecodeSwap(r)` | `MIR.SwapAnchorsCode(CP.compile_to_bytecode(r)) == CP.compile_to_bytecode(OBu.SwapAnchorsRegex(r))` — `CompileSwap` capped at `[Accept]` instead of `[WriteOracle(lid)]` (the L2 form). |
| `FInitStateMirrorAt(c, str, cp, ...)` | The mirrored FInitState at an **arbitrary** `cp` (not just `init_cp`) — the capture replay anchors at the recorded gate position, unlike an oracle build which starts at position 0/`\|str\|`. |
| **`BackwardReplayMirror(body, str, cp, cap, lk, qt, ov, cdn, n)`** | **THE PAYOFF.** `FFindMatch(compile_to_bytecode(reverse_regex(body)), str, @cp, Backward)` mirrors `FFindMatch(compile_to_bytecode(SD.RevRE(body)), Reverse(str), @(n-cp), Forward)` — same match/no-match, winning thread's registers correspond **value-for-value** under `v |-> n-v` (`MirrorThread`/`MirrorRegs`). Works for ANY start registers (not just fresh/init), which item 3/4's assembly will need. |

**Key discovery:** `Mirror.dfy`'s `FFindMatchMirror` (already proved, L2 era)
ALREADY carries full register values through the isomorphism — its `ensures`
clause states `MirrorThread`/`MirrorRegs` equalities, not just match/no-match.
§4.5.4's flagged worry ("`Mirror` may need to STRENGTHEN its ensures with the
capture-register value correspondence") was unfounded. **Nothing in
`Mirror.dfy` changed or needs to.**

### `linden-reasoning/src/Equiv/TreeMirror.dfy` (6 verified, 0 errors)

The **spec** half — "the genuinely new proof" `LOOKAROUND_CAMPAIGN.md`
flagged as having no existing scaffolding.

| Lemma | Role |
|---|---|
| `GroupActionMirror(ga, gam)` | `Open`/`Close` equal; `Reset` payloads equal **as sets** (`RevL` permutes `DefGroups`, doesn't preserve seq order). |
| `TreeMirrorRel(t, tm)` | Backward tree `t` and forward tree `tm` correspond: same shape, same `Choice` order (**priority**), same `Read` chars, `AnchorPass` payloads related by `SwapAnchorL`, `GroupActionT` payloads by `GroupActionMirror`. No `LK`/`LKFail`/`ReadBackRef` cases (the fragment excludes them). |
| **`ComputeTreeReverse`/`ComputeTrReverse`** | **THE THEOREM.** For a `GroupOkActs` stack (Groups allowed, no lookarounds/backrefs — exactly an L3b lookbehind body after `Translate`): the backward `ComputeTree`/`ComputeTr` and the forward one over `RevActs(acts)`/`SwapInput(inp)` run out of fuel together and, when they complete, produce `TreeMirrorRel` trees — **at any pair of group maps**, including totally unrelated ones. |

**Why group maps can be unrelated:** a `GroupOkActs` tree never *reads* the
map to decide its shape (only `Backreference`, excluded by `GroupOkL`, would
do that) — this is the same fact `SpanDuality.TreeResSomeGmIndep`/
`ComputeTreeGroupOkGmIndep` already use. So `ComputeTreeReverse` needs no map
correspondence to *build* the two trees; the map correspondence is a
downstream question about *folding* leaves (§3, step 1).

**Proof shape:** fuel-parallel structural induction, case-for-case with
`SD.RevActs`. `SD.SeqListReverse` is the load-bearing alignment ("the spec
ALREADY reverses concatenation order when scanning backward" — exactly what
`RevL` does structurally). Every swap-layer primitive `TreeMirrorRel`
consumes was already banked in `SpanDuality.dfy` (`ReadCharSwap`,
`IsStrictSuffixSwap`, `AnchorSatisfiedSwap`, `RevLDefGroupsSet`,
`ActionsFuelReverse`) — this file assembles them at the tree level, which is
exactly what `SpanDuality.dfy`'s own "(4) CONCATENATION ORDER" status note
(written before L3 existed) predicted was "tractable" and left as the one
open assembly.

**Solver notes for anyone continuing this file:** `SD.RevActs` of a 2- or
3-element literal seq needs an explicit `assert SD.RevActs([...]) == [...]`
— Dafny won't unfold the sequence comprehension through the recursive calls
otherwise. The `GreedyChoice`/forced-copy cases need the reset-wrapped
`TreeMirrorRel` fact asserted by name (`GroupActionT(Reset(...), ...)`) right
after the two recursive calls, not left implicit — see the `Quantified` case
for the pattern.

---

## 2. THE FINDING THAT CHANGES THE PLAN — lookbehind capture spans are stored reversed, by design

Ran the engine's functional model directly (no proof, just execution — see
`/tmp/.../scratchpad/lbtest/lbtest.dfy` if you want to reproduce, or just
trust the corpus below):

```
(?<=(a))b     on "ab"   =>  [1, 2, 1, 0]     -- group 1 = (1, 0)
(?<=(ab))c    on "abc"  =>  [2, 3, 2, 0]     -- group 1 = (2, 0)
a(?=(b))      on "ab"   =>  [0, 1, 1, 2]     -- group 1 = (1, 2)  (forward, in order)
```

A capturing lookbehind's raw register bank holds the group's **end position
in the start slot and start position in the end slot** — the backward replay
writes `start_reg` first (bytecode order is fixed; only the scan direction
and `cp` reverse), so the register that's *conventionally* "start" ends up
holding the *numerically later* position.

This is not a bug and not new — `regex-engine/tests/engine/
OCamlBugRegressions.dfy`'s header says the expected arrays are the "RAW
outputs of the ORIGINAL OCaml RegElk engine ... INCLUDING register quirks
(**reversed lookbehind capture spans**, stale end registers)". It's
documented, pinned by cross-engine regression tests, and has always been
true — L1/L2 never noticed because neither admits capturing lookbehinds.

**Consequence for `MainTheoremL3b`.** The spec side normalizes: `GMClose`
(`Groups.dfy`) always produces `Range(startIdx, Some(endIdx))` with
`startIdx <= endIdx`, swapping if needed. `CapArrayOfLeaf` (`linden-reasoning/
Spec.dfy`) reads a `Range` in that already-ordered form. So:

- `PIV.GmOfLive`'s `RangeFromArr`/`LiveRange` (`PikeInvRE.dfy`), which read
  `CP.start_reg(gid)`/`CP.end_reg(gid)` **positionally, with no ordering
  fixup**, will — for a lookbehind-owned group — construct a `Range` with
  `startIdx > endIdx.value`. That is **not** what `GMClose` ever produces on
  the spec side.
- The **existing** `Normalize`/`NormalizeArr` (`linden-reasoning/Spec.dfy`)
  only absorbs the *stale-end-register* quirk (`arr[j-1] < 0 ==> -1` at odd
  indices) — nothing in it swaps a reversed pair back into order.
- So `MatcherSpec(raw, str, Normalize(FFullMatch(raw, str)))` — the exact
  statement `MainTheoremL3` (and hence `L3b`'s goal) proves — is **currently
  false** for any pattern with a capturing lookbehind, under today's
  `Normalize`.

**This is architecturally sanctioned, not a wrong turn.** `NormalizeArr` is
*declared* to be the quirk-absorption layer between the engine's raw output
convention and the spec's clean one; it already has one clause for exactly
this kind of purpose. It needs a second clause.

**The fix — new item 0, ahead of everything else in §4.5.1's numbered list:**
widen `NormalizeArr` with a per-group reversed-pair swap for lookbehind-owned
groups (`if arr[start] > arr[start+1] (and both >= 0) then swap`, gated
correctly against the existing stale-end-register clause — check the
interaction order). This is a no-op for every group NOT owned by a
lookbehind (forward pairs are already ordered), so it doesn't disturb
`MainTheorem`'s existing (L1/L2/L3a) proofs — but the equality lemma at
`MainExtraction` that currently reads `NormalizeArr`'s single clause will
need the new disjunct threaded through, and every internal value tie for a
lookbehind-owned group (the whole §3 chain below) must be stated
**orientation-aware**: the engine bank holds `(e, s)`, the spec leaf holds
`Range(s, Some(e))` — pick ONE canonical orientation for the intermediate
lemmas (recommend: state everything in spec orientation, i.e. carry the
"decided range mirror" below into `BackwardReplayMirror`'s consumers rather
than into `BackValue.dfy` itself, which is direction-agnostic and shouldn't
know about group semantics).

**The decided range mirror** (for the leaf-fold lemma in §3 step 1): under
the register mirror `v |-> n - v` (`Mirror.dfy`'s `MirrorRegs`, `n = |str|`),
an OPEN range `Range(s, None) |-> Range(n-s, None)`; a CLOSED range
`Range(s, Some(e)) |-> Range(n-e, Some(n-s))`. This is an involution. It
lines up with `GMClose` on both sides of the reversal **provided every
`Close` fires on a currently-OPEN-or-ABSENT group** (a closed-and-present
group breaks it — `GMClose` reads only `startIdx`, ignoring a prior `endIdx`,
so re-closing an already-closed group silently overwrites rather than
extending). Open-or-absent holds under unique group ids (an enclosing gid is
never in an inner quantifier's `DefGroups`, so no `Reset` can leave it
half-closed then re-close it), but the `TreeRes` induction that proves the
leaf-fold lemma needs this **threaded as an invariant**, not assumed — see
§3 step 1's `CloseDisc` sketch.

---

## 3. The remaining chain for item 4 (the backward value crux) — in order

This is what stands between "two transport lemmas proved" and item 4 (task
#4) being `completed`. Items 1–3, 5, 6 (tasks #1, #2, #3, #5, #6) are
essentially unblocked by this and can proceed in parallel once item 4's
final lemma (`LkReplayMatchesSpecLB`, step 3 below) has a stated signature —
they mostly consume its `ensures`, not its proof.

1. **`TreeResMirror`** (new, linden-reasoning, next to `TreeMirror.dfy`): over
   `TreeMirrorRel`-related trees plus a `CloseDisc` invariant (sketch: a
   predicate on `(t, O)` where `O` is the set of group ids open at the walk's
   current point — `Close(g)` requires `g in O`, `Open(g)` adds it,
   `Reset(gs)` removes `gs`, everything else recurses unchanged — established
   for `ComputeTr`'s output by a side induction that needs the body's group
   ids to be `NoDup`, which `TranslateDefGroupsNoDup`-style facts already
   supply upstream in `LiftSim.dfy`'s converter chain; a linden-reasoning-
   local variant may be needed since that lemma currently lives in
   linden-equiv), prove: `TreeRes`/`FirstLeaf` mirror — `None` iff `None`;
   `Some` implies the endpoint inputs are `SwapInput`-related and the leaf
   group maps are related by the **decided range mirror** from §2, pointwise
   per group.

2. **`GmOfLive` commutation** (linden-equiv, likely `PikeInvRE.dfy` or a new
   small file): `PIV.GmOfLive(body, MirrorRegs(cap, n), ...)` vs
   `PIV.GmOfLive(SD.RevRE(body)-as-engine-regex, cap, ...)` — `filter_reset`
   only reads **clocks** (`a_clk`) to decide presence/reset, and `MirrorRegs`
   only remaps `a_cp` (see `Mirror.dfy:513`, `MirrorRegs` leaves clocks
   alone) — so the filter's *shape* (which gids survive) should transport for
   free per-gid; what needs an actual argument is that `RangeFromArr`'s
   readout after filtering matches the decided range mirror once you unfold
   `start_reg`/`end_reg` swap under `Mirror`. This is the piece that
   reconciles the ENGINE-side value with the register mirror from
   `BackValue.dfy`, so the assembly in step 3 can hand it to
   `TreeResMirror`'s (spec-side) range mirror and get equality, not just
   correspondence-up-to-swap.

3. **`LkReplayMatchesSpecLB`** (linden-equiv `MainTheorem.dfy`, sibling to
   the L3a keystone `LkReplayMatchesSpec` at :4479) — the assembly:
   - `BackValue.BackwardReplayMirror` (engine registers/match, done) at
     `(body, str, cp, cap, lk, qt, ov, cdns, n=|str|)`;
   - `MainTheorem.ReplayCapIsBodyLeaf` (L3a, already proved, direction-
     generic per its own doc) instantiated at `(SD.RevRE(body), Reverse(str),
     n-cp)` — needs the **statics** to transport: `RevRETransWf`
     (linden-reasoning, exists), `NR.Reverse*` family (`ReversePlusFragmentRE`
     etc., `NfaRepRE.dfy`, exist for L1's `reverse_regex` — audit whether they
     also hold for `SD.RevRE`/`OBu.SwapAnchorsRegex(reverse_regex(·))`, since
     `SwapRevIsRevRE` only proves the two ARE equal for look-free bodies, it
     doesn't reprove the fragment facts under the new name);
   - `SD.TranslateRevRE` (linden-reasoning, exists) to move `T.Translate` of
     the reversed/swapped body to `RevL(T.Translate(body))` on the spec side;
   - steps 1–2 above to fold `TreeResMirror`'s leaf correspondence back
     through `Empty -> gmMain` (the L3a keystone's `ComputeTrGmIndepLk`-style
     transfer is direction-generic already per its own comment — confirm,
     don't re-derive) and the `LkResult(Backward)` fold (`LS.LkResult` at
     `LkDir(lk) == Backward`, mirroring the L3a keystone's final `assert
     L.Positivity(...) && L.LkDir(...) == WP.Forward` line but for
     `Lookbehind`).
   - **Ensures shape to aim for** (mirror `LkReplayMatchesSpec`'s signature,
     `la.Lookbehind?` instead of `la.Lookahead?`, and note the value tie is
     stated through the §2 range mirror rather than raw equality on
     `CaptureRegs(body)`):
     ```
     (ra.None? <==> LS.LkResult(T.TrLookaround(la), tlk, gmMain, inp).None?)
     && (ra.Some? ==> ... GmAgreeOn(..., <range-mirrored version of
          PIV.GmOfLive(body, ra.value.capture_regs, ...)>, S))
     ```

Once `LkReplayMatchesSpecLB` exists with that shape, task #4 is `completed`
and the remaining tasks are:

- **#1** (fragment flip): `NfaRepRE.LookBehindFragmentRE`'s `Re_lookaround`
  clause (`:532`, currently `(la.Lookahead? || CaptureFreeRE(r1)) &&
  LookFreeRE(r1) && PlusFragmentRE(r1)`) becomes `(la.Lookahead? ||
  la.Lookbehind? || CaptureFreeRE(r1)) && ...` — plus the `Raw` counterpart
  (`:563`) and the item-0 `NormalizeArr` widening from §2, which is really
  part of this item's "flip" since it's a fragment-predicate-adjacent
  spec change.
- **#2** (`FreshBodyMatch`/`MatchedPosLA` direction dispatch,
  `MainTheorem.dfy:3076–3096`): `MatchedPosLA` already tests
  `AI.capture_type(...)` — only its extra `.Lookahead?` conjunct
  (`:3079`) needs to drop (or become `.Lookahead? || .Lookbehind?`).
  `FreshBodyMatch` hard-codes `LAnc.Forward` (`:3095`) and needs a
  `capture_direction`-dispatched twin using `LkReplayMatchesSpecLB`'s
  bytecode/cp convention.
- **#3** (backward bisim wrappers): `CM.FFindMatchCapRel`/`ThreadRel` are
  already direction-generic per the campaign doc — audit which
  `ReplayLidCapAgreeFresh`-style wrapper (`MainTheorem.dfy` — the ones
  called at `:3665` in the existing Lookahead branch) needs a literal
  Backward-instantiated twin vs. just widening its `dir` parameter.
- **#5** (value lifts): `MainTheorem.dfy:3765–3816` is the CURRENT
  capture-free-identity lookbehind branch inside `FLookLoopValueLift` —
  replace with the real value case using #2–#4, following the `Lookahead?`
  branch immediately above (`:3648–3764`) as the induction skeleton (same
  shape: replay, frame, IH-at-suffix, assemble). `FLookLoopQuantValueLift`
  (session 8b, `MainTheorem.dfy`) needs the mirror treatment for the quant
  bank.
- **#6** (gate + endpoint): `LiftSim.dfy`'s `LiftPreserveGatePassLk`
  (`:4200`) lookbehind half currently routes through
  `LkResultAgreeOutside` over the empty set (capture-free assumption,
  `L3_PROOF_MAP.md` §"GATEPASS DESIGN FINDING" case (b)) — becomes
  value-carrying via #4's keystone, following case (a)'s (Lookahead)
  wiring (`ThreadRepLkStepCheckOracle`) as the template. The endpoint's
  per-g owner dispatch (`InsidePresentResBridge`/`L3aValueBridge`,
  `LiftSim.dfy:10353`/`3956`) gains a `Lookbehind?` arm parallel to the
  existing `Lookahead?` one.

---

## 4. Quick-reference: what NOT to re-derive

- Mirror.dfy's state isomorphism (register values, priority, view/oracle
  mirror) — proved, direction-agnostic, unchanged this session.
- `SpanDuality.dfy`'s swap-layer primitives (`ReadCharSwap`,
  `IsStrictSuffixSwap`, `AnchorSatisfiedSwap`, `SeqListReverse`,
  `RevLDefGroupsSet`, `ActionsFuelReverse`, `RevRE`/`TranslateRevRE`,
  `GroupOkL`/`GroupOkActs`) — all exist, all consumed by `TreeMirror.dfy`
  as-is, none needed strengthening.
- L3a's `ReplayCapIsBodyLeaf`, `ComputeTrGmIndepLk`,
  `CM.FFindMatchCapRel`/`ThreadRel` — direction-generic per their own
  documentation; the job is instantiating/dispatching them, not reproving.
- The oracle side of lookbehinds (L1) is untouched by any of this — L3b is
  purely about the CAPTURE-RECONSTRUCTION pass, which runs after the
  (already-correct) oracle build.
