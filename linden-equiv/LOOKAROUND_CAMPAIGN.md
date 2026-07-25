# The Lookaround Campaign

Goal: extend the pinnacle equivalence (`MainTheorem` / `ApiMatch.Supported`)
from the plus fragment to patterns containing lookarounds, starting with
**capture-free, non-nested lookbehinds** (`(?<=...)`, `(?<!...)`) — milestone
**L1** of the ladder in §4.

This document records the campaign's design, the work completed so far, and —
in enough detail that another person could carry it on — the intended proof
structure for everything that remains.

Status (2026-07-25):

| Phase | Content | State |
|---|---|---|
| A | Lookbehind fragment vocabulary + per-lid table adherence | **DONE** (`7f3efe2`) |
| C1 | Build-sweep frame & oracle-independence lemmas | **DONE** (`9523567`) |
| C1.5 | Build-code classification + the sweep's configuration graph | **DONE** (`6b7b92a`) |
| C2 (half) | Sweep soundness: every written bit has a reachable `WriteOracle` | **DONE** (`634434a`) |
| C2 (half) | Sweep completeness: every reachable `WriteOracle` gets written | **DONE** — §6.1: `NoAccept`, `AdvanceReachComplete`, `FConsumeReachComplete`, the `ReachF` inversions (`ReachInProc`/`ReachFLeEnd`/`ReachBeyondNeedsConsume`), `FindMatchReachComplete`, and `SweepCharacterization` all verify |
| C3 | `FBuildLids` assembly: the per-lid oracle characterization | **DONE** — §6.2: `OracleBuild.dfy` (`LidBuildOk`/`AllLidsBuildOk`, `FBuildLidsCharacterized`, `FBuildOracleCorrect`, per-lookaround `FBuildOracleCorrectAt` — the §6.3 bridge's interface) |
| C4 | Bridge: reachability ⟺ a body match ending at cp | **DONE** — §6.3: forward (`MatchesToPath`/`MatchesToReachesWrite`, OracleBridge.dfy) AND decomposition (`InBlock` mid-parse invariant, `BlockStep`, `ProgReachInv`, `ReachesWriteToMatches`, OracleDecomp.dfy); capstone **`OracleColumnCharacterized`**: bit(cp, lid) ⟺ ∃i ≤ cp: body matches str[i..cp) |
| C5 | Spec-side duality: forward span match ⟺ backward walk | **DONE (both directions)** — §6.4: `SpanDuality.dfy` (linden-reasoning, 55 verified): `SpanDualityComplete` (a span match ending at cp makes the backward walk succeed; `BwdComplete`+`BwdCompleteQuant`/`BwdCompleteFree`, rightmost-span peeling, `Acheck` guards taking only consuming spans) and `SpanDualitySound` (a successful backward walk yields a span match; `BwdSound`+`BwdSoundQuant`, with the free-layer induction founded on strict `Acheck` progress via `SSLengthLt` where `delta == Inf` has no structural measure). What remains of C5 is glue in linden-equiv: the `OB.Matches ⟺ MatchesL(Translate·)` transfer via `CharSemAgree`/`AnchorSemAgree`, then the OracleOk-shaped corollary chaining `OracleColumnCharacterized`: `SuccActs([Areg(r)]+cont, InputAt(str,j), Backward) ⟺ ∃i: MatchesL(r,str,i,j) ∧ SuccActs(cont, InputAt(str,i), Backward)`; then the `OB.Matches ⟺ MatchesL(Translate·)` transfer in linden-equiv via `CharSemAgree`/`AnchorSemAgree` |
| B | The `lm` + `ov` threading sweep through the tree-rep/sim layers | **DONE** — §6.5 |
| D | Entry construction, `StaticOkRE` conjunct, `Supported` flip, smoke | **DONE (smoke deferred)** — §6.6 |

Earlier campaign steps (recorded in git history, sessions of 2026-07-19):
`NfaRepRE`'s `Re_lookaround` arm already carries the real single-instruction
rep; `NestInv`'s lookaround arm and `ColdF`'s oracle edges are in; the
VM-level `FAdvanceEpsilon*` lemma families in `ClockMono`/`PikeSimRE`/
`MainTheorem` already have full `CheckOracle`/`NegCheckOracle` cases.

## 1. How lookarounds work in the engine (regex-engine)

A lookaround in the **main** bytecode is ONE zero-width instruction:
`CheckOracle(lid)` (positive) or `NegCheckOracle(lid)` (negative)
(`Compiler.dfy:160`). It passes or kills the thread on the oracle bit
`view_get_oracle(ov, cp, lid)`; a passing positive also records
`look_regs[lid] := cp` for later capture reconstruction.

Everything else lives in five per-lid tables filled by the `FCompileExtra`
fold (`Compiler.dfy:303`): `f_look_types` (flavour), `f_look_ast` (body),
`f_look_cdns`, `f_look_build_bc`, `f_look_capture_bc`. The build bytecode is

```
f_look_build_bc[lid] == compile_to_write(oracle_regex(la, body), lid)
```

which ends in `WriteOracle(lid)` instead of `Accept` — a *recorder*: on
reaching it the thread writes the bit at the **current** cp and dies, so one
sweep records **every** position where the oracle regex completes.

`oracle_regex` (`Compiler.dfy:255`) and `oracle_direction`
(`Interpreter.dfy:38`) are the crux of the whole plan:

| flavour | build regex | build direction |
|---|---|---|
| `Lookahead`/`NegLookahead` | `lazy_prefix(reverse_regex(remove_capture(body)))` | **Backward** |
| `Lookbehind`/`NegLookbehind` | `lazy_prefix(remove_capture(body))` | **Forward** |

`FBuildLids` (`Interpreter.dfy:525`) runs one `FFindMatch` sweep per lid,
from `maxlook` DOWN to 1 (annotate numbers outer lookarounds lower, bodies at
`l+1`, so inner lookarounds have HIGHER lids and are built first — a nested
lookaround's `CheckOracle` can consult already-built bits). The main pass
then runs against the finished oracle; `FLookLoop` afterwards replays
`f_look_capture_bc` to reconstruct captures inside positive lookarounds.

## 2. How lookarounds work in the spec (linden-semantics-core)

`IsTree`'s `LookaroundR` rules (`Semantics.dfy:272`): a positive tree is
`LK(lk, tlk, tc)` where `tlk` is the body's tree walked in `LkDir(lk)`
(**Forward** for lookaheads, **Backward** for lookbehinds), and the
continuation `tc` is walked under `LkResult(lk, tlk, gm, inp).value` — the
sub-match's group map feeds the continuation. The failing tree is
`LKFail(lk, tlk)`. `BoolTree` (`BooleanSemantics.dfy:90`) and `PikeSubset`
(`PikeSubset.dfy:38`) currently exclude lookarounds outright.

Note the direction chiasm: for a LOOKBEHIND the engine's build pass runs
**forward** over the un-reversed body while the spec walks the body
**backward** from cp. Those meet at §6.4's duality.

## 3. The three structural insights the plan exploits

1. **Lookbehinds first.** Their build passes run FORWARD on the un-reversed
   body, so the entire existing forward pipeline (rep, sim, WalkOk, Cold)
   applies to the build bytecode unchanged. Lookaheads are the ones that
   need backward execution + a reversal theorem — deferred to L2. This
   inverts the folk expectation ("lookbehind is the hard one").

2. **Capture-free lookarounds are leaf-transparent.** For a capture-free
   body, positive `LkResult` returns the group map **unchanged** (the body's
   tree writes no groups; its `Reset` nodes reset the empty `DefGroups`), so
   `TreeLeaves(LK(lk, tlk, tc)) == TreeLeaves(tc)`, and `LKFail`'s leaves
   are `[]` (Mismatch-like). The LK wrapper behaves exactly like an ANCHOR
   whose satisfaction is the oracle bit: the checked tree the engine walks
   can drop it, and `LeavesAgree` absorbs the difference — the same move
   that dissolved the do-while guard in the plus campaign. No `tlk` needs to
   live in `TreeRepRE`, dodging tlk-determinism entirely.

3. **Classified build code is register-free in control.** L1 build bytecode
   contains no `CheckOracle`/`NegCheckOracle` (look-free body), no
   `CheckNullable` (plus-fragment body — nullable-plus schemes excluded), and
   its only `WriteOracle` is the final recorder (`CompileToWriteClassified`).
   Hence a thread's control flow depends only on `(pc, exit_allowed, cp)`:
   registers are written, never read. Consequences, all proven in
   `OracleSweep.dfy` / `OracleReach.dfy`:
   - the sweep's behaviour is independent of the oracle view and cdn table
     (each `FBuildOracle` column is a function of build bytecode + string);
   - a sweep writes only its own lid column ⇒ for NON-NESTED lookarounds the
     `FBuildLids` lid-induction degenerates into per-lid independence;
   - the Pike processed-set dedup (drop duplicate `(pc, exit_allowed)`
     threads, losing only registers) preserves **reachability** — so the
     oracle statement is about a register-free configuration graph
     (`ReachF`), an EXISTENCE statement, far weaker than the priority
     (first-leaf) theorem the main pass needed.

## 4. The milestone ladder

- **L1 — capture-free, non-nested LOOKBEHINDS** (this campaign): bodies in
  the plus fragment, look-free, capture-free. Forward-only; LK
  leaf-transparent.
- **L2 — capture-free, non-nested LOOKAHEADS**: adds backward execution of
  the build passes + the reversal theorem (`Backward ∘ reverse_regex ≡
  Forward`). Sub-choice: parameterize the rep/sim by direction (mechanical,
  wide) vs. prove the reversal once at the tree level and keep the pipeline
  forward (preferable if tractable). The big one.
- **L3 — captures inside positive lookarounds**: `FLookLoop`/`capture_regex`
  reconstruction correctness + LkResult-fed gm in the extraction. Lookbehind
  capture passes run Backward (needs L2's direction work); lookAHEAD
  captures run Forward, so L3a can precede full L2.
- **L4 — nesting**: the lid-induction over `FBuildLids` with "oracle correct
  above lid" as hypothesis; mostly assembly once L1/L2 exist. (The
  sweep-frame lemmas already support it: a build for lid only reads columns
  of higher lids, only writes its own.)

## 5. Completed work — inventory

All in `linden-equiv/src/Equiv/` unless noted; every file verifies clean
per-file (see §7 for the command).

**Phase A (`7f3efe2`) — fragment vocabulary, NfaRepRE.dfy:**
- `CaptureFreeRE/Raw`, `LookFreeRE/Raw`; `LookBehindFragmentRE/Raw` = the
  plus-fragment shapes + lookbehind leaves with capture-free, look-free,
  plus-fragment bodies; embeddings `PlusIsLookBehindFragmentRE/Raw`.
- `AnnotateCaptureFree`, `AnnotateLookFree`, `AnnotateLookBehindFragment`,
  `SpecRegexLookBehindFragment` (annotation/lazy_prefix preserve it all).
- `RemoveCaptureFreeId` (`remove_capture` is identity on capture-free) and
  the keystone `OracleRegexPlusFragment`: a lookbehind's build regex is
  `lazy_prefix(body)` and stays in the PLUS fragment — the license to reuse
  the forward pipeline on build code.
- The compile-adherence family (`FreshCorrectRE/Min/Opt`,
  `CompileNfaRepRE/Min/Opt` — the `{:isolate_assertions}` crutches) widened
  in place from `PlusFragmentRE` to `LookBehindFragmentRE` (one trivial
  `Re_lookaround` case each); new entry `CompileToBytecodeRepLookBehind`;
  `CompileToBytecodeRepPlus` kept its signature (routes via the embedding),
  so **no downstream file changed**.

**Phase A (`7f3efe2`) — LookTables.dfy (new):**
- `LookIds`/`LookUnique` (lid analogue of `CapUnique`), `AnnotateLookUnique`
  (annotate's monotonic lid counter ⇒ unique ids in `[l, l')`),
  `LookIdsLeMax`.
- `LookEntryOk`/`LookTablesOk` (per-lid row adherence over all five tables),
  frame lemmas (`FCompileExtraLookFrame`, `LookTablesOkFrame`), the fold
  theorem `FCompileExtraLookOk` (uniqueness tames clobbering), and the
  corollary the oracle theorem consumes: `FFullCompilationLookOk(r)`.

**Phase C1 (`9523567`) — CompileToWriteRep (NfaRepRE.dfy) + OracleSweep.dfy (new):**
- `CompileToWriteRep`: `compile_to_write` adherence — `NfaRepRE` from 0 with
  `WriteOracle(l)` at the end label.
- Classification predicates `NoOracleReads`, `NoCheckNullable`,
  `WritesOnlyLid`; view plumbing `SameShape`/`Submap`/`ViewSetFacts`.
- `AdvanceOracleFrame`/`FindMatchOracleFrame`: a build run only ADDS bits,
  only in column `lid`, and per epsilon closure only at the current cp.
- `AdvanceMonoAny`/`MonoAny`: unconditional monotonicity + shape
  preservation, for any code.
- `AdvanceOvIndep`/`FindMatchOvIndep`: under the classification, two runs
  from `SameModCdn` states with any same-shape views evolve their threads
  IDENTICALLY (equal results) and preserve cellwise view agreement.
  **Statement lesson:** the relational invariant must be *cellwise agreement
  preservation* (`CellAgree(ov1,ov2,c,l) ==> CellAgree(ov1',ov2',c,l)`), NOT
  "same new bits" — the latter is false at cells where the inputs already
  differ, the former composes with no monotonicity glue.

**Phase C1.5 (`6b7b92a`) — classification + configuration graph:**
- `NoOracleInstrRE/MinRE/OptRE` (NfaRepRE.dfy): no position inside a
  look-free plus-fragment `NfaRepRE` block holds any of
  `CheckOracle`/`NegCheckOracle`/`WriteOracle`/`CheckNullable` (mirror of
  `StarFragmentNoAnchorInstr`, extended over the three quantifier schemes
  via `NfaRepREQuantInv`/`NfaRepREPlusInv` + the `NfaRepIncr*` lemmas).
- Corollary `CompileToWriteClassified(re, lid)`: the whole build program is
  classified; its only `WriteOracle` is the final recorder.
- `OracleReach.dfy`: `CtxAt`, `EpsEdge` (mirrors `FAdvanceEpsilon`'s control
  flow: `Jmp`; `Fork` both arms; `Set*` fall-through; `BeginLoop` clears the
  exit flag; `EndLoop` requires it; `AnchorAssertion` gated on
  `is_satisfied` at `CtxAt`; oracle/cdn instructions edge-free;
  `Accept`/`WriteOracle`/`Fail` terminal), `ConsumeEdge` (successor
  `(pc+1, true, cp+1)` — consuming re-arms the flag), `least predicate
  ReachF` from `(0, false, cp0)` (`init_thread` starts `exit_allowed ==
  false`), `ReachesWrite`, `ReachFGeStart`.

**Phase C2 soundness (`634434a`) — OracleReach.dfy:**
- `ActiveOk`/`BlockedOk`: active threads' configs are reachable (guarded
  behind `pc >= 0` — negative-pc threads read `Fail` and die claim-free);
  blocked entries sit reachably on their recorded `Consume`.
- `AdvanceReachSound`: one closure keeps the frontier config-sound, touches
  no other column, and every bit it adds in column `lid` is testified by
  `ReachesWrite` at the closure's cp. Carries two structural ensures the
  engine doesn't state: the closure always ends `active == []`, and (in
  `FConsumeReach`) `FConsume` drains `blocked` to `[]`.
- `FindMatchReachSound`: whole-run soundness.

**Phase C2 completeness (PR #1, `b79ea0a`, external contribution) —
OracleReach.dfy:** `NoAccept` classification, the worklist invariant
`ClosureInv` (EpsEdge-closure into P ∪ A, blocked-entry coverage keyed on
`isblocked`, write coverage) with `AdvanceReachComplete`,
`FConsumeReachComplete`, the `ReachF` inversions
(`ReachInProc`/`ReachFLeEnd`/`ReachBeyondNeedsConsume`),
`FindMatchReachComplete`, and **`SweepCharacterization`** — a classified
`NoAccept` run sets exactly the old bits plus the `ReachesWrite` positions,
for arbitrary initial registers.

**Phase C3 (`80f9e13`) — OracleBuild.dfy:** `LidBuildOk`/`AllLidsBuildOk`
(every lid's build row is empty or classified-and-forward; gap lids ride
the seed frame with the same formula), `FBuildLidsCharacterized` (the
lid-descending induction: `SweepCharacterization` per column,
`FindMatchOracleFrame` commuting the rest), **`FBuildOracleCorrect`** (each
`FBuildOracle` column holds EXACTLY its build bytecode's `ReachesWrite`
positions) and per-lookaround **`FBuildOracleCorrectAt`** in
`lazy_prefix(body)` form.

**Phase C4 (`642737b`..`dce5aac`) — OracleBridge.dfy + OracleDecomp.dfy:**
the span predicate `Matches`/`MatchesIter` + algebra; the lazy-prefix
"start anywhere" walker; the forward direction `MatchesToPath`
(+`StarLoopPath`/`MinChainPath`/`OptChainPath`/`DoWhilePath`) capped by
`MatchesToReachesWrite`; the decomposition direction via the mid-parse
invariant `InBlock` (+`InMin`/`InOpt`, `*Shape` pin packages, named tail
predicates with inversion/intro helpers), `BlockStep`
(+`BlockStepMin`/`BlockStepOpt`), the program sweep `ProgReachInv`, and
`ReachesWriteToMatches`; capstone **`OracleColumnCharacterized`** — the
oracle bit at `(cp, lid)` iff the body matches some span ending at `cp`.

**Phase C5 spec-side core (`869b7a3`..`3a92f43`) —
linden-reasoning/SpanDuality.dfy:** the direction-free Linden span
predicate `MatchesL`/`IterL` + algebra, `GroupFreeL` (capture-free bodies
translate group-free, the group map is constant), `SuccActs`, the
backward-walk plumbing at `InputAt` positions, and BOTH duality directions:
**`SpanDualityComplete`** and **`SpanDualitySound`** — the backward walk
from `cp` succeeds iff the regex matches some span ending at `cp`.

**MainTheorem regression, found and fixed (`dacecd6`):** the campaign's new
`NfaRepRE`-module predicates perturbed the pinnacle lemma's marginal Z3
search; the runaway was ONE semantically trivial batch (the
`ThreadRegsWf` bridge at the `MainExtraction` call). Fix: the bridge closes
inside `assert ... by { hide *; ... }` (context collapse ⇒ congruence),
the call's preconditions are split into individual asserts, and
`MainTheorem` carries `{:isolate_assertions}` (935 small batches, worker-
friendly). Reusable recipe: a trivial assert that runs away in a huge
context wants `by { hide *; restate the exact facts; }`.

## 6. The remaining proof plan (L1)

### 6.1 C2 completeness — every reachable `WriteOracle` gets written [DONE — PR #1]

The Pike worklist argument, at existence level. Two prerequisites, then two
lemmas mirroring the soundness pair.

**Prerequisite (i): `NoAccept`.** The closure early-exits on `Accept`
(`active := []` with threads still queued), which would break completeness.
Build code contains no `Accept` (`compile` never emits it; only
`compile_to_bytecode` appends one). Add `!i.Accept?` to the
`NoOracleInstrRE/MinRE/OptRE` ensures and a `NoAccept(c)` conjunct to
`CompileToWriteClassified` — a trivial re-verify of those lemmas.

**Prerequisite (ii): blocked dedup is complete for existence.** `add_thread`
skips a thread when `pc_mem(isblocked, t.pc)` — keyed by pc alone, ignoring
`exit_allowed`. This is fine: the earlier blocked entry at the same pc has
the same instruction (hence the same `ce`), and the consume successor is
`(pc+1, true, cp+1)` REGARDLESS of the blocked thread's flag (consuming
re-arms it) — `ReachF`'s consume disjunct already accepts either flag value.

**Lemma `AdvanceReachComplete`** (induction mirroring `FAdvanceEpsilon`,
same skeleton as the five existing induction families). State, writing
`P(s)` for the configs in `s.processed` (via `bpc_mem`) and `A(s)` for the
configs of `s.active` threads with `pc >= 0`:

- requires the classification (+ `NoAccept`) and the worklist invariant on
  entry:
  1. every `EpsEdge`-successor (at `s.cp`) of a config in `P(s)` is in
     `P(s) ∪ A(s)`;
  2. every `Consume`-config in `P(s)` has `pc_mem(s.isblocked, pc)` and a
     blocked entry at that pc;
  3. every `WriteOracle(lid)`-config in `P(s)` already has its bit:
     `view_get_oracle(ov, s.cp, lid)`.
- ensures, for the result `(s', ov')`:
  - `P(s') ⊇ P(s) ∪ A(s)` (every queued thread gets processed — the skip
    branch only fires when the config is already in `P`);
  - invariants 1–3 hold of `s'` with `A(s') = ∅` — so `P(s')` is
    `EpsEdge`-CLOSED, every processed `Consume` config is represented in
    `s'.blocked`, and every processed `WriteOracle` config's bit is set in
    `ov'`.

Each instruction case pushes its successors onto `active` before recursing,
which is exactly what keeps invariant 1: a config moves from `A` to `P` and
its successors enter `A`. The `Accept` case is unreachable (`NoAccept`).

**Corollary (per position):** entry configs of position `cp` ⊆ `A` at the
closure's start ⇒ `P(s') ⊇ ReachAt(cp)` := every config `ReachF`-reachable
at `cp`. (Every element of `ReachAt(cp)` is `EpsEdge*`-reachable from an
entry config of `cp`, by inversion of `ReachF`'s three disjuncts; closedness
+ containment of the entry configs gives the sweep.)

**Lemma `FConsumeReachComplete`:** every blocked entry whose expectation
accepts the character at `cp` yields an active thread at `(pc+1)` —
`FConsume` adds ALL accepted entries (no dedup), so the new active list
covers every consume-entry config of position `cp+1`.

**Lemma `FindMatchReachComplete`** (induction along positions): requires the
run enters position `s.cp` with `A` covering the entry configs of `s.cp`
(initially: `{(0, false)}` at `cp0`), and bits already set for all
`ReachesWrite` positions `< s.cp`; ensures `∀ cp2:
ReachesWrite(c, str, cp0, lid, cp2) ==> view_get_oracle(ov', cp2, lid)`.
Two termination edges need care:
- *blocked empty after a closure*: then no `Consume` config in
  `ReachAt(s.cp)` accepted, so position `s.cp + 1` has no entry configs and
  (by an inversion lemma on `ReachF`, in the style of `ReachFGeStart`)
  `ReachAt(cp')` is empty for every `cp' > s.cp` — nothing left to write.
- *string end* (`nextchar == None`): `is_accepted(None, ce)` is false for
  consume expectations, so `ConsumeEdge` is false at `|str|` and the same
  inversion applies. (Check `Charclasses.is_accepted`'s `None` case when
  writing this; if some expectation accepts `None` the claim needs the
  in-bounds guard `cp < |str|` in `ConsumeEdge` instead — either works.)

**Characterization (soundness + completeness):**

```
lemma SweepCharacterization(c, str, ov, lid, cdn)   // c classified + NoAccept
  ... run FFindMatch from FInitState(c, 0, ..., cp_context(0, str, Forward)) ...
  ensures forall cp ::
    view_get_oracle(ov', cp, lid)
      == view_get_oracle(ov, cp, lid) || ReachesWrite(c, str, 0, lid, cp)
```

### 6.2 C3 — `FBuildLids` assembly [DONE — OracleBuild.dfy]

Instantiate per lid, for a `LookBehindFragmentRE` main regex `re` with
`LookUnique(re)`, `fc := FFullCompilation(re)`:

- `FFullCompilationLookOk(re)` identifies `f_look_build_bc[lid]` as
  `compile_to_write(oracle_regex(la, body), lid)`;
- `OracleRegexPlusFragment` + `RemoveCaptureFreeId` reduce the build regex
  to `lazy_prefix(body)`, in the plus fragment and look-free (`lazy_prefix`
  adds only a dot-star head);
- `CompileToWriteClassified` classifies the build code;
- `oracle_direction(Lookbehind/NegLookbehind) == Forward`,
  `init_cp(Forward, |str|) == 0`;
- `SweepCharacterization` characterizes the lid's own column;
- `FindMatchOracleFrame` (other lids' sweeps don't touch this column) and
  `FindMatchOvIndep` (this sweep doesn't care what the other columns hold)
  let the per-lid results commute across the `FBuildLids` recursion;
- `init_view` starts every column all-false.

Target:

```
lemma FBuildOracleCorrect(re, str)      // LookBehindFragmentRE + LookUnique
  ensures forall lid, cp ::
    (lid, la, body) a lookaround of re ==>
      view_get_oracle(FBuildOracle(FFullCompilation(re), str), cp, lid)
        == ReachesWrite(compile_to_write(lazy_prefix(body), lid), str, 0, lid, cp)
```

(Statement via `LookTablesOk`-style recursion over `re`, or via a
`LookAt(re, lid)` lookup function — either is fine; the recursion mirrors
`LookTablesOk` and avoids inventing a partial lookup.)

### 6.3 C4 — the bridge: `ReachesWrite` ⟺ a body match ending at cp [DONE — OracleBridge.dfy + OracleDecomp.dfy]

Relate the configuration graph to walks of the compiled block. Target
(engine-level, still spec-free):

```
ReachesWrite(compile_to_write(lazy_prefix(body), lid), str, 0, lid, cp)
  <==>  exists i :: 0 <= i <= cp && BodyMatch(body, str, i, cp)
```

where `BodyMatch` is a NEW existence-level predicate "some walk of `body`'s
compiled block consumes exactly `str[i..cp)`" — recommended definition: an
inductive predicate over the REGEX structure (engine-free in its statement),
e.g. `Matches(body, str, i, cp)` defined structurally (character consumes
one; con splits; alt either; quant iterates with the fragment's bounds;
anchors test `CtxAt`). Then prove both directions against `ReachF`:

- **Reach ⇒ match** (path decomposition): a `ReachF` derivation is a path;
  paths through an `NfaRepRE` block factor through the block structure.
  Prove by induction on the derivation, generalizing over the block
  decomposition the way `NoOracleInstrRE` generalizes over it (the same
  Min/Opt companions will be needed). Within one position the reachable
  config graph cannot cycle without consuming — the `BeginLoop`-clears /
  `EndLoop`-requires flag discipline kills epsilon-only iterations — which
  is what makes the induction well-founded (measure: `cp`, then derivation
  size).
- **Match ⇒ reach** (path construction): structural induction on
  `Matches`, building the `ReachF` derivation through the block; the
  `lazy_prefix` head contributes the "start anywhere ≤ cp" existential
  (i dot-steps then enter the body block).

This is the one remaining piece with real engineering risk. If the direct
path decomposition fights back, the fallback is to piggyback the existing
tree machinery: relate `ReachF` at the write-pc to a `TreeThreadRE`-style
walk and reuse `WalkOk`'s vocabulary — heavier but well-trodden.

`Matches` should be placed so that §6.4 can consume it: it mentions only the
RegElk AST and `str`, so it can live in linden-equiv next to the bridge, or
in linden-reasoning if stated over the TRANSLATED body (see below —
stating it over the Linden `Regex` via `T.Translate(body)` skips one
transfer lemma).

### 6.4 C5 — spec-side duality (linden-reasoning; engine-free) [DONE — SpanDuality.dfy + OracleSpec.dfy]

**Done:** `MatchesL` + `SpanDualityComplete`/`SpanDualitySound` (see §5), and
the glue, in linden-equiv's NEW `src/Equiv/OracleSpec.dfy` (12 green):

- `MatchesTransfer`/`IterTransfer` — `OB.Matches(re, str, i, j) <==>
  SD.MatchesL(rer, T.Translate(re), str, i, j)`, structural induction
  discharged by `T.CharSemAgree` (!ignoreCase) and `T.AnchorSemAgree`
  (!multiline). Hypotheses: `T.TransWf(re)` and `0 <= i && j <= |str|` — the
  span must lie inside the string, since outside it the engine's context
  functions read `None` while `MatchesL` pins its positions to `0..|str|`.
  NO capture-/look-freedom needed (captures translate to `Group`, which both
  predicates see through; lookarounds have no rule on either side).
- `QuantBoundsAgree` (per-`k`, not a trigger-less `forall`),
  `CtxAtIsCpContext`, `TranslateGroupFree`.
- `OracleColumnSpec` — THE chain: for an L1 lookbehind,
  `view_get_oracle(FBuildOracle(FFullCompilation(re), str), cp, lid) <==>
  SuccActs(rer, [Areg(Translate(body))], InputAt(str, cp), gm, Backward)`.

Note the dependency bridge: linden-equiv's `deps/linden-reasoning.doo` must be
rebuilt whenever linden-reasoning changes (`dafny build -t:lib dfyconfig.toml
--no-verify` in linden-reasoning, copy the `.doo` in — any plain `lem restore`
reverts it). The original plan for this section follows.

The spec walks a lookbehind body BACKWARD from cp (`LkDir(LookBehind) ==
Backward`); the engine characterization speaks of forward matches ending at
cp. Needed, for capture-free, backreference-free, lookaround-free bodies:

```
(exists i :: MatchesSpan(rer, r, str, i, cp, Forward))
  <==>  exists tlk :: IsTree(rer, [Areg(r)], InputAt(str, cp), gm, Backward, tlk)
                      && TreeRes(tlk, gm, InputAt(str, cp), Backward).Some?
```

where `MatchesSpan(rer, r, str, i, j, dir)` is the existence-level "r
matches the span [i, j)" — for capture-free bodies gm is irrelevant
(leaf-transparency, §3.2), so both sides are booleans of `(r, str, i, cp)`.

Proof shape: define `MatchesSpan` once and prove
`MatchesSpan(.., Forward) <==> MatchesSpan(.., Backward)` by structural
induction on `r` — `Sequence` swaps its components' spans, `Disjunction` is
pointwise, `Quantified` needs a span-concatenation helper, `Character`
reads `str[j-1]` vs `str[i]`, anchors test the same `CtxAt`. Then relate
`MatchesSpan(.., Backward)` to the `IsTree`-existence via the standard
tree-construction lemmas (`ComputeTree` handles both directions already).
Everything is engine-independent — it belongs in linden-reasoning (new
file, e.g. `src/Equiv/SpanDuality.dfy`), keeping linden-equiv's heavy files
out of it.

Finally connect §6.3's `Matches` (RegElk AST) to `MatchesSpan` (Linden
`Regex`) through `T.Translate` — a mechanical transfer in the style of
`TransNfaRep` (or avoid it by defining `Matches` over the translated body
from the start).

### 6.5 Phase B — the `lm` + `ov` threading sweep [DONE — the simulation carries lookaround gates]

**The ripple was avoided entirely by BUNDLING, not by adding parameters.**
`AR.QMap` stopped being a bare map and became the record of static tables the
Linden-side layer consults:

```
datatype QMap = QMap(quants: map<int, LG.GroupSet>,
                     looks:  map<int, (L.Lookaround, L.Regex)>,
                     ov:     LOr.OracleView)
```

Every layer already threads one `qm: AR.QMap`, so adding `looks`/`ov` as
FIELDS cost ~66 mechanical edits (`qm[qid]` → `qm.quants[qid]`, `qid in qm` →
`qid in qm.quants`) instead of ~1000 new argument positions across
`NfaRepL`/`TreeRepRE`/`TreeThreadRE`/`StepSpec`/`PikeSimRE`/`PikeInvRE`/
`MainTheorem`. The oracle view belongs with the tables for a real reason: the
main pass never writes it (the build passes ran first), so it is exactly as
static as `quants` is, and `CpOf(inp) == |inp.pref|` supplies the column
index without threading the string.

Landed on that base (all first-try green):

- `LmapOk(re, qm)` (ActionsRepRE) — the `QmapOk` of the lid namespace: every
  `Re_lookaround(lid, la, body)` has `qm.looks[lid] == (TrLookaround(la),
  Translate(body))`. Plus `PositiveL`, `LookFreeLmapOk`,
  `PlusFragmentLookFree`, `PlusFragmentLmapOk` (lookaround-free regexes
  constrain no row, so the narrower fragments get `LmapOk` for free).
- `NfaRepL`'s `LookaroundR` arm: `false` → `pc2 == pc1 + 1 && exists lid ::
  GetPcRE(c, pc1) == Some(CheckOracle(lid) / NegCheckOracle(lid)) && lid in
  qm.looks && qm.looks[lid] == (lk, r1)` — the quantifier idiom for erased ids.
- `TransNfaRep`/`Min`/`Opt` widened from `PlusFragmentRE` to
  `LookBehindFragmentRE` + `LmapOk`, with the new `Re_lookaround` case; the
  narrow entry points (`CompileToBytecodeActionsRep{Plus,Quant,Anchor}`) KEEP
  their signatures by routing through `PlusIsLookBehindFragmentRE` +
  `PlusFragmentLmapOk`, so no downstream client changed.
- `TreeRepRE` gained ONE new disjunct carrying all four gate rules
  (`tr_lk`/`tr_lkfail`/`tr_neglk`/`tr_neglkfail`), gated on
  `view_get_oracle(qm.ov, CpOf(inp), lid)` with the negative flavour passing
  on a CLEAR bit; `CpOf(inp) == |inp.pref|` is the column index.
  LEAF-TRANSPARENT: the pass rule carries the SAME tree to `pc+1` (the `LK`
  wrapper is dissolved, exactly like the do-while's `Progress` guard), which
  is what keeps `TreeRepPikeSubtree` true. `TreeRepDetermRE` and
  `TreeRepPikeSubtree` gained the matching cases.
  **PERFORMANCE LESSON — write the rule instruction-first, with NO
  `exists lid`.** The first version used four disjuncts each existentially
  quantifying `lid`; that made `ActionsTreeRepRE` (3.8k assertion batches)
  go from 7m52s to >15min, because every proof obligation mentioning
  `TreeRepRE` now carried those quantifiers. Restating it as
  `match GetPcRE(code, pc) case Some(CheckOracle(lid)) => if bit then ...
  else t == Mismatch ...` — the instruction pins `lid`, so no quantifier is
  needed — brought it back to 8m33s (+9%, the honest cost of the new rules).
  Same measured, same green.
- `StepSpec`/`GenStepRE` (GenStepRE.dfy) gained real oracle cases.
- `MainTheorem`: `QmOfRE` now returns the bare quant map and the record is
  built at the use site as `AR.QMap(QmOfRE(re), LmOfRE(re), ov)`; NEW
  `LmOfRE` mirrors `QmOfRE` for the lid namespace (its `LmapOk` discharge
  needs a `LT.LookUnique` analogue of `PIV.QuantUnique` — deferred to §6.6,
  since the current gate is lookaround-free and `PlusFragmentLmapOk` applies).
- `PikeSimRE`'s two oracle cases can no longer derive `false` from `StepSpec`
  (the tree layer now HAS oracle rules); they derive it from the fragment gate
  instead, via the new `NoOracleInstrAt` (`StaticOkRE` still admits only
  `NR.PlusFragmentRE`, which compiles no oracle instruction).

**Stage 2 (DONE): the simulation preservation cases.** `StaticOkRE`'s gate is
now `NR.LookBehindFragmentRE(re) && AR.QmapOk(re, qm) && AR.LmapOk(re, qm)`,
and the two oracle cases of `InvariantPreservationRE` are real. What it took,
in dependency order:

- **NestInv**: `StepEdgeRE` gained the two gate edges (zero-width
  fall-through, like an anchor — the `look_regs` write is invariant-neutral
  because `NestInvRE` reads capture and quant clocks only), and
  `ColdPropagatesF` its lookaround case. 80 green.
- **PikeInvRE** (158 green): the whole `filter_capture` family widened to the
  lookbehind fragment. Every one of those inductions needed the same case —
  a lookaround node is TRANSPARENT to both filters when its body is
  capture-free — so it is packaged once as `FilterAtLookaround`, with
  `CaptureFreeNoCapIds` and `CaptureFreeQidBody` for the id-set side
  conditions. Two `Re_alt`/`Re_con` disjointness facts that used to be found
  automatically needed explicit `assert c !in CapIds(r1) by { ... }` hints
  after the widening.
- **The oracle view is static** — the fact that lets `qm.ov` carry it:
  `NR.NoWriteInstrRE` (new family in NfaRepRE, the `NoOracleInstrRE` skeleton
  with the gates ADMITTED and only `WriteOracle`/`CheckNullable` excluded) +
  `CM.NoWriteOracleCode`/`CM.FAdvanceEpsilonOvStable` (an epsilon phase over
  write-free code returns the view it was given) + `PSM.StaticOkNoWrite`.
  `qm.ov == ov` is then a hypothesis of `InvariantPreservationRE` and
  `FindMatchSimRE` that survives every position of the search.
- **The stutter machinery** absorbed the gates: `TT.StuttersRE` and
  `PIV.StutterSuccIs` gained `CheckOracle`/`NegCheckOracle` (successor
  `pc+1`), `StutterChainSource`'s ensures grew two shapes, and
  `StutterChainForwardOrFork` two cases. `StutterTameRE` needed nothing — it
  constrains `Jmp` targets only.
- **PikeSimRE** (107 green, first try): `OracleStepThreadRE` (inversion at a
  gate: the tree survives INTACT at `pc+1`, or is `Mismatch`),
  `PreserveOraclePass` (a tree-side STUTTER — `pts` is unchanged while the VM
  advances and writes `look_regs`; `ThreadTracksGm` survives by
  `PIV.GmOfLiveLookIndep`, the seen-inclusion by `PIV.StutterInclusionRE`),
  and `PreserveOracleKill` (the `PreserveAnchorKill` shape). Both flavours of
  gate go through the same two lemmas via a `pos: bool` parameter.

The original stage-2 design notes follow (they held up):

- **The pass case is a tree-side STUTTER.** Leaf-transparency means the tree
  does not step while the VM advances `pc` — the same shape as `Jmp`/
  `BeginLoop` (`PreserveStutterCase`), not as `AnchorAssertion`. So
  `TT.StuttersRE` and `PIV.StutterSuccIs` should gain
  `CheckOracle`/`NegCheckOracle` (successor `pc+1`); `StutterTameRE` stays
  trivially true for them (it constrains only `Jmp` targets), and
  `StutterChainSource`'s ensures grows two shapes. `GenStepRE`'s oracle cases
  then become unreachable-by-`requires` but stay as true statements.
- **The kill case mirrors `PreserveAnchorKill`**: the checked tree is
  `Mismatch`, the thread dies, the tree is consumed into `seen`.
- **The one genuinely new obligation — the `look_regs` write — is DONE**
  (PikeInvRE.dfy, 154 green). The engine's `CheckOracle` pass also does
  `look_regs[lid] := cp`, so `ThreadTracksGm` has to survive it: `GmOfLive`
  reads `look` through `AI.filter_reset` -> `filter_capture`, whose
  `Re_lookaround` branch either `filter_all`s the body or recurses into it,
  and for CAPTURE-FREE bodies both alternatives are the IDENTITY on
  `cap_regs`. Landed as `FilterAllCaptureFree`, `FilterCaptureCaptureFree`,
  `FilterCaptureLookIndep` (hypothesis `NR.LookBehindFragmentRE`, whose
  lookaround arm carries `CaptureFreeRE(body)`) and the consequence
  `GmOfLiveLookIndep`. This is the L1 shape of what the campaign scoping
  called "the `GmOfLive` look-clock branch"; at L3 (captures INSIDE
  lookarounds) it stops being the identity.
- The `ClockMono`/`BB*` bookkeeping for the write is already in place
  (`RegsClocksLESet`/`SetRegLens` handle `look_regs` — the VM-level oracle
  cases were oracle-aware from the start).

The original plan for this section follows.

Do these TOGETHER — they ripple through the same heavy files
(`PikeSimRE` 3.0k, `PikeInvRE` 3.6k, `MainTheorem` 1.3k), and two separate
sweeps would re-verify them twice.

- **`LMap`** (ActionsRepRE.dfy): `type LMap = map<int, (L.Lookaround,
  L.Regex)>`, `LmapOk(re, lm)` mirroring `QmapOk` — for every
  `Re_lookaround(lid, la, body)` in `re`: `lid in lm && lm[lid] ==
  (TrLookaround(la), Translate(body))`. `NfaRepL` gains `lm` and its
  `LookaroundR(lk, r1)` arm mirrors the quantifier idiom for erased ids:

  ```
  pc2 == pc1 + 1
  && exists lid: int ::
       GetPcRE(c, pc1) == Some(if positive(lk) then CheckOracle(lid) else NegCheckOracle(lid))
       && lid in lm && lm[lid] == (lk, r1)
  ```

  Ripple: `NfaRepMinL`/`NfaRepOptL`/`ActionsRepL` signatures, the
  `TransNfaRep` family (new lookaround case discharging the arm from
  `NfaRepRE`'s + `LmapOk`), and every downstream mention.

- **`ov` in the tree-rep layer**: `TreeRepRE` gains `ov: LOr.OracleView`;
  new disjuncts `tr_lk` / `tr_lkfail` shaped exactly like
  `tr_anchorpass`/`tr_anchorfail` but gated on
  `LOr.view_get_oracle(ov, CpOf(inp), lid)` — per §3.2 the tree carries the
  CONTINUATION only (LK dropped; leaf-transparent). `StepSpec`/`GenStepRE`
  replace the `case Some(_) => false` catch-all's `CheckOracle`/
  `NegCheckOracle` members with real anchor-like cases; `TreeThreadRE`,
  `WalkOk` (zero-width pass edges, carrying the guard bit `g` unchanged like
  anchors), `ActionsTreeRepRE` (construction case), and the `PikeSimRE`
  `assert false` oracle cases (`PikeSimRE.dfy` ~:2300) become real cases
  modeled on the `AnchorAssertion` case directly below them
  (`PreserveCheckOraclePass/Kill` helpers).

- **`StaticOkRE` conjunct** (PikeSimRE.dfy:98): add `OracleOk(re, ov, str)`
  — for every lookaround `(lid, la, body)` of `re` and every cp:
  `view_get_oracle(ov, cp, lid) <==> `(the §6.4 spec-side statement for
  `la`, negatives included — the BIT encodes the positive body-match
  question for both flavours; `NegCheckOracle` inverts at the gate)`. The
  main pass never writes the oracle, so this is frame-stable across the
  simulation (like the rest of `StaticOkRE`). It is DISCHARGED at the
  assembly (§6.6) by chaining `FBuildOracleCorrect` (§6.2) + the bridge
  (§6.3) + the duality (§6.4).

### 6.6 Phase D — entry construction, Supported flip, smoke [boolean layer DONE]

**Done (EntryLk.dfy, 20 green):** `BoolTreeLk` — the boolean semantics widened
with a lookaround gate rule — and the faithfulness direction
`IsTree ==> BoolTreeLk` (`ComputeBoolTreeLk`/`EncodeEqualLk`/`BooleanCorrectLk`),
which is the only direction the entry uses. Plus `PikeLkRegex`/`PikeLkActions`,
`TranslateFragmentPikeLk`, and the group-map machinery the gate case needs:
`ComputeTreeGmIndep`/`ComputeTrGmIndep` (a group-free walk never consults the
map, so its tree is map-independent) and `LkResultGmIndep` (success is
map-independent for free, by `ResGroupMapIndep`).

**A LOAD-BEARING NEGATIVE RESULT — do not widen `BS.BoolTree` in
linden-engine-model.** The rule was written there first and verified there.
But `BoolTree`'s body is unfolded by every consumer, and linden-engine's
`PikeEquiv.GenerateActiveF` sits right at the solver's limit: ANY extra case
tipped it over. Measured: PikeEquiv green in 4m51s before, one 300s timeout
after, in three formulations — the rule stated with `IsTree`, with `ComputeTr`,
and sealed behind an `{:opaque}` payload predicate. `{:isolate_assertions}` on
`GenerateActiveF` localized the failure to a single precondition batch (983/984
green) but did not fix it, and a `{ hide *; ... }` block around that call made
it worse. Hence the copy in linden-equiv: the dependency packages stay
bit-for-bit unchanged and the cost lands in the package that wants the feature.
(`lem pack` at the workspace root is the way to propagate a dependency change
when one IS wanted — it rebuilds each member's `.doo` in dependency order, and
fails the member whose build exceeds its 10-minute cap.)

**The entry's tables and the oracle discharge are DONE** (OracleEntry.dfy, 24
green):

- `LmOf(re)` — the lookaround table (lid -> translated flavour and body), with
  `LmOfDom`, `LmOfInv` (every row IS a node of `re`, carrying its table row, its
  lookBEHIND flavour and its L1 body facts) and `LmapOkOfLmOf`. The descent
  needs `IsLookSub` + refl/trans/child plumbing, and `LookFreeLmOfEmpty`: an L1
  body is look-FREE, so a lid can only belong to its own node.
- `OracleOkFromColumns` — `OS.OracleColumnSpec` instantiated at every row and
  every column gives the construction's `LL.OracleOkSuffix` from the initial
  input. `SuffixIsInputAt` lines the indexings up: every input the forward walk
  can still reach IS a string position.

**The capture pass ("the look pass is the identity") is HALF done.** MainTheorem
used to get this free from `max_lookaround == 0`; at L1 it is true but must be
proved, because `FLookLoop` replays `compile_to_bytecode(capture_regex(la,
body))` for every positive lookaround that matched and takes the replay's
registers. What the answer (`filter_reset` over the main ast) can see:

| register bank | why the replay cannot change the answer | status |
|---|---|---|
| capture | a capture-free body compiles no `SetRegisterToCP` | DONE — `NR.NoCaptureInstrRE` family + `CM.FFindMatchCapFrame` |
| look | `filter_capture` ignores look clocks when bodies are capture-free | DONE — `PIV.FilterCaptureLookIndep` |
| quant | written only at the body's own ids, which the filter never consults | frames DONE (`CM.FFindMatchQuantFrame`); classification + filter frame REMAIN |

(i)-(iii) are now DONE as well:

- `PIV.QuantWriteIdsRE` + Min/Opt companions — every `SetQuantToClock` inside a
  compiled block targets one of that regex's own quant ids (needs
  `QuantUnique`: without it a node's own id could be negative and so not in
  `QuantIds`).
- `PIV.QuantIdsOutsideLooks` + `FilterCaptureQcFrameOutside` /
  `FilterCaptureFullOutside` — `filter_capture` reads quant clocks only at ids
  OUTSIDE lookaround bodies, because it reaches a lookaround node and stops
  (both branches are the identity for a capture-free body). Mutual measure:
  per-slot at `(r, 0)`, whole-sequence at `(r, 1)`.
- `PIV.CaptureRegexFragment` (with `ReverseCaptureFree`/`ReverseLookFree`/
  `ReverseQuantIds`/`ReverseQuantUnique`/`ReverseNullable`/`ReversePlusFragment`)
  — a lookbehind's capture regex is itself an L1 body, with quant ids contained
  in the body's. Reversal only swaps concatenation order and rebuilds nodes
  with their own ids, so every fragment property is node-local; nullability is
  reversal-invariant, which is what the plus fragment's side conditions need.

REMAINING: (iv) the `FLookLoop` induction over lid and the widened
`FBuildCaptureUnfold`. Two supporting facts it will want: `QuantUnique(re) ==>
QuantIdsOutsideLooks(re)` is disjoint from the ids inside lookaround bodies
(so the frame's "agree outside S" meets the filter's "reads only outside
looks"), and "a set `look_regs[lid]` implies `lid` is a real node id" (only a
`CheckOracle(lid)` writes that slot, and those exist only for nodes).
`FReconstructPlus` needs nothing new — `FNulledPlusIdentity` already covers it
for all-negative quant values, which `QuantRegsFinal` supplies.

**Remaining:**

- **Leaf-transparency lemmas** (linden-semantics-core or linden-reasoning):
  capture-free positive `LkResult(lk, tlk, gm, inp) == Some(gm)` when
  `TreeRes(tlk, ...).Some?`; `TreeLeaves(LK(lk, tlk, tc)) ==
  TreeLeaves(tc)`; `TreeLeaves(LKFail(lk, tlk)) == []`. Watch the
  linden-semantics-core verify budget (it sits close to the worker wall) —
  prefer landing these in linden-reasoning if they state cleanly there.
- **Entry construction**: `BoolTree` (linden-engine-model,
  `BooleanSemantics.dfy:90`) gains an LK-as-boolean-gate rule for
  capture-free lookarounds (shape-level, gm-free), or the construction
  consumes the ov-bit directly like an anchor — follow whatever the anchors
  campaign did at this spot, it is the same move.
- **MainTheorem assembly**: widen the top-level gates
  (`NR.PlusFragmentRaw` → `NR.LookBehindFragmentRaw` at
  `MainTheorem.dfy:963` and the interior `PlusFragmentRE` gates), insert
  `FBuildOracleCorrect` + bridge + duality to discharge `OracleOk`, and let
  the (now real) oracle sim cases carry the rest.
- **Supported flip** (`ApiMatch.dfy:42`): `NR.PlusFragmentRaw(pattern)` →
  `NR.LookBehindFragmentRaw(pattern)` (keep `Latin1Wf`). `ApiReasoning`/
  `Patterns` clients inherit it.
- **Smoke**: DEFERRED, not done. `lem test` does not pick up locally
  changed `.doo` files produced by `lem pack` (user, 2026-07-25, unfixed),
  so a Go smoke test cannot validate a widening made in an upstream
  package. NOTE the residual risk: lookbehind compiles *gate* instructions
  (`CheckOracle`/`NegCheckOracle`) into the bytecode, and no runtime test
  has ever executed that path — the plus campaign's `a+` smoke does not
  cover it. Run `(?<=a)b` / `(?<!a)b` once `lem` is fixed.

### 6.6 OUTCOME (2026-07-25) — L1 IS DONE

`MainTheorem` gates on `NR.LookBehindFragmentRaw` and `ApiMatch.Supported`
follows it. MainTheorem 47 verified / 0 errors / 58s; whole package
**7184 verified, 0 errors, 21m08s**.

The three vacuity crutches are replaced by real discharges:
`OE.LmapOkOfLmOf` (was `AR.PlusFragmentLmapOk`), `OE.OracleOkFromColumns`
(was `qm.looks == map[]`), and `LookRowsFromTables` feeding the wide
`FBuildCaptureUnfold` (was the `NoGateMainCode`/`LookRegsUntouched`
vacuity path — all three of those lemmas are now deleted).
`LookStaticPackage` bundles the static facts into one minimal context;
`LTB.SpecRegexLookUnique` supplies lid uniqueness; `OE.LmOfInv` also
yields the quant half of the row hypothesis.

Still OUT of the fragment: lookahead, captures inside bodies, nested
lookarounds, non-plus-fragment bodies.

**Two traps this phase hit, both worth re-reading before the next widening:**

1. `assert R.max_lookaround(ast) == 0` survived the gate flip. True under
   the plus gate, FALSE under the wide one — Z3 spent 900s failing to
   prove it, which read exactly like a context-cost timeout. Two rounds of
   VC-shrinking refactors were spent on the wrong diagnosis.
   `{:isolate_assertions}` completed the lemma in 9m29s with 1421
   per-assertion results and named the culprit outright; removing it took
   the lemma to **55s**. Profile FIRST after a semantic change.
2. `FCompileExtraFrame`'s `case Re_lookaround(_, _, _) =>` was empty —
   sound only while the plus gate made it unreachable. **An empty match
   case is a silent unreachability assumption, and widening a gate is
   precisely what invalidates it.** Audit empty cases on every widening.

## 7. Practical notes

**Per-file verify** (do this, not whole-project runs, during development):

```
Dafny.exe verify src/Equiv/<file>.dfy \
  --library deps/linden-engine-model.doo --library deps/linden-engine.doo \
  --library deps/linden-reasoning.doo --library deps/linden-semantics-core.doo \
  --library deps/linden-warblre.doo --library deps/regex-engine.doo \
  --standard-libraries --verification-time-limit 180 --cores 8
```

Dafny 4.11 (PATH `dafny` is 4.10 and cannot load the 4.11 `.doo`s):
`$env:USERPROFILE\.vscode\extensions\dafny-lang.ide-vscode-3.5.4\out\resources\4.11.0\github\dafny\Dafny.exe`.
Full workspace: `lem build` at the repo root (~8 min, ~14 GB).

**Module homes** (for new files' imports — these cost a round-trip each when
guessed): `get_instr`/`size` = `Bytecode`; `build_cdn_v`/`cdn_get`/
`init_cdn`/type `cdns` = `Cdn`; `is_accepted` = `Charclasses`;
`update_context`/`is_satisfied`/`direction`/`char_context` = `Anchors`;
`compile_cdns` = `Cdn` (not `Compiler`); `set_reg` = `Array_Regs` (NOT
`AI.R` — qualified access does not reach a refining module's import);
`view_*_oracle`/`OracleView`/`init_view` = `Oracle`; everything VM
(`VmState`, `FAdvanceEpsilon`, `FFindMatch`, `FConsume`, `bpc_*`,
`init_*set`, `add_thread`, `incr_cp`, `cp_offset`, `get_char`,
`cp_context`, `unprocessed`, `UnprocessedAdd`) = `ArrayInterp` (`AI`).

**Style/solver gotchas encountered:**
- `exists eb: bool :: P(eb)` inside a least predicate gets no trigger (and
  warnings fail the build) — expand booleans by hand: `P(false) || P(true)`.
- `least lemma` gives the fixpoint induction for free (`ReachFGeStart`
  verified with an empty body) — prefer it over manual `ORDINAL` plumbing.
- Relational two-run lemmas: state view effects as cellwise agreement
  preservation, not new-bits equality (§5, C1).
- The engine's function ensures are minimal; structural facts you need
  (closure ends `active == []`, `FConsume` drains `blocked`) must be carried
  as extra ensures on your own lemmas.
- The induction skeletons for anything over `FAdvanceEpsilon` are in
  `OracleSweep.dfy`/`OracleReach.dfy` (and `ClockMono.dfy`) — copy a
  skeleton, don't re-derive the 15-case match.
- The `CompileNfaRep*` family and `ActionsTreeRepFRE` carry
  `{:isolate_assertions}`; `MainTheorem` carries `hide` on recursive
  predicates. These are load-bearing (removal has blown builds up 3×) — add
  cases, keep the attributes.
- `lem` compat cannot merge "module moved to a dependency" — decomposing a
  published package forces fresh package names. Keep the campaign inside
  linden-equiv until it's done; split (if the worker budget demands it —
  1.0.3 verified at 452s of the 900s wall) only at publish time. The
  churn-free split candidates are NestInv + ClockMono + CheckErase +
  RegsLaws (~5.1k lines, already oracle-aware).
