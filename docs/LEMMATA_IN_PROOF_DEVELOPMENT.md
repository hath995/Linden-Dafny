# Lemmata (`lem`) in proof development — what it did for Linden-Dafny, and how to use it

Written 2026-08-30 after the E2/E3 campaign: the L5 regex-equivalence proof (the Linden/RegElk
tree semantics against the regex engine, nested capturing lookarounds included) went from "a
30k-line monolith that verified only with `{:isolate_assertions}`, per-symbol, over hours" to
**61 namespaced packages that `lem pack` verifies in dependency order, 61/61 green, no isolation,
every lemma under the 900 s limit**. This note records what the package manager contributed to
that — as a tool for proof engineering, not just distribution — and the workflow we would use again.

## 1. What `lem` gave the proof

### 1.1 A verification gate that cannot be argued with
`LEM_BUILD_TIMEOUT=0 lem pack` at the workspace root verifies every member whole-file, in
dependency order, with each member's own `[options]` (`cores`, `verification-time-limit = 900`),
refuses a `.doo` if the source emits any warning, and reuses members whose build identity has not
changed. That single command replaced five ad-hoc verification scripts and — more importantly —
replaced *per-symbol green* as the definition of done. Per-symbol runs (`--filter-symbol`) had let
two things hide for weeks: a callee body that was broken (`ActionsTreeRepLkFRec`, 11 days) and a
lemma that had only ever "verified" in a 2-hour isolated run (`ForwardFindRecLBDeep`, which
turned out to contain two false assertions). Whole-package verification under a fixed time limit
is what surfaced both.

### 1.2 Packages as the unit of proof cost
Splitting `linden-equiv` per module (47 packages) and `LiftSim` into eight *bands* (core, oracle,
chain, gate, carriers, deep, forward, main — a DAG computed from the module's lemma-call graph
with tree-sitter) did not make Z3 faster per lemma (`.doo` splitting alone changes nothing), but it
made cost *legible*: `lem pack` prints one line per member with its obligation count and time,
levels run in parallel (`--jobs N`), and a member that cannot pack under 900 s names the lemma at
fault. The forward band (LBDeep) and the main band (`MainTheoremL5`) were the two that never
packed; everything else had been green for days. That ranking is what focused the E3 work.

### 1.3 Dependency hygiene as a proof-quality signal
`lem publish` warns when a declared dependency is *proven unused*; `lem lock` re-keys the whole
workspace and validates dependency names locally; the `.doo` manifest rejects mismatched Boogie
options. Each of these caught a real mistake during the split (an import that was only ever a
name, a stale `--boogie` flag, a sibling floating at the wrong depth). A proof that is packaged
per module is forced to say exactly what it depends on — which is also the information you need
when a lemma's context is too large.

### 1.4 Reproducibility of the environment
The toolchain pin (`[toolchain] dafny = ">= 4.11.0"`), the cgroup-wrapped launcher, and the
per-member `cores` mean a member's verification time is a property of the package, not of who ran
it. The registry worker re-verifies with the *same* Dafny version the release was built with. When
publishing failed (the worker could not install 4.11.0 — a permissions problem on its side, reported
to the Lemmata session), the failure was precise and reproducible, not "it worked on my machine".

## 2. The troubleshooting workflow (what we would do again)

1. **Make `lem pack` the gate.** Keep `verification-time-limit ≤ 900` in every manifest (the
   registry rejects more) and never ship `{:isolate_assertions}`; it is a diagnostic.
2. **Read the pack output as a profile.** Members that fail or sit near the limit are the work
   list. For finer grain, run the member whole-file with `--log-format text` and rank scopes with
   `tools/e3/e3profile.py` (resource count first, time second).
3. **For a slow lemma, run the E3 loop** (details in `AGENTS.md`): section it with opaque blocks
   + `assert {:split_here} true;` (`tools/e3/e3opaque.py`), then `--isolate-assertions
   --verification-time-limit=60` to list the obligations that do not close, restate the hidden
   facts, `hide *`/`reveal` the trivially-true-but-slow ones, and re-pack the band. Expect most
   "slow" obligations to be *missing facts* (they present as timeouts in this theory mix).
4. **When an obligation never closes, distrust the claim.** Probe it standalone (a 10-line
   lemma against the same `.doo` deps — `lem restore` gives you exactly that closure) and probe
   `assert false;` at the lemma head. This is how the two false assertions in LBDeep were found;
   the package boundary made the standalone probe a one-minute experiment.
5. **Keep the bands' manifests honest.** After a rename or a toolchain change, delete every
   member's `deps/` before packing (stale `.doo`s produce "Duplicate module name" for every module)
   and regenerate the tracked `dfyconfig.toml` from the new closures (`tools/e2/regen_dfyconfig.py`).
6. **Publish leaf-first and expect the registry to disagree.** `lem publish --yes` at the root
   publishes in dependency order and stops on the first rejection; the worker's verdict is the
   final arbiter of "verified". Report rejections with `lem status <pkg>` text.

## 3. Numbers (2026-08-29/30)

| | before | after |
|---|---|---|
| `ForwardFindRecLBBase` | isolated | 2:01 / 1 s / 0.8 s / 1.9 s |
| `FLookLoopChildLinkLift` | isolated | 2 s / 1 s / 3 s |
| `L3aEndpointAssembly` | > 900 s | 16 batches, 41 s |
| `LiftPreserveGatePassLk` | isolated | 3 s / 7 s / 23 s |
| `ForwardFindRecLBDeep` | 2 h 03 min isolated (two false asserts) | 11 batches, 2:04 |
| `MainTheoremL5` | > 900 s (never packed) | 10 batches, max 4:33 |
| workspace `lem pack` | forward + main never green | **61/61**, levels 5–13 min at `--jobs 2` |

## 3.1 Anecdote: the two-hour green that wasn't

`ForwardFindRecLBDeep` is the LB-DEEP arm of the descent (a capturing lookbehind nested inside a
lookbehind). Its record said "1808/0, verified isolated in 2 h 03 min at CORES=2" — the kind of
line that ends an argument. The forward *band* package, however, would not pack: as one VC the
lemma ran past 900 s; with opaque sections and `split_here` its preamble dropped from 900 s to
15 s and its tail to 2 s, but block 2 kept timing out no matter what was exported. An isolate pass
at 60 s listed the same handful of obligations every time (`ctxB.nextchar == get_char(str, cpA)`,
`FirstLeaf(t1, inp1) == TreeRes(t1, Empty, inp1, dir1)`, …); exporting everything, making the
preamble a plain section, giving the batch 900 s — nothing moved them. The package boundary made
the next experiment cheap: `lem restore` gives the exact `.doo` closure, so a ten-line standalone
lemma against the same dependencies took a minute — and refuted the first claim (a backward
context's `nextchar` is the character at `cp − 1`). `assert false;` at the lemma head was refuted in
seconds (the hypotheses are consistent), so these were false *claims*, copy-overs from the forward
twin, not a vacuous proof — and the recorded "green" could not have been an honest verification of
those lines. Fixed (`cpA − 1`; the sub-leaf stated as `SubFirstLeafAt` defines it, via `dir1`),
plus explicit proofs for two obligations that were merely slow (`capture_type`, the reversed-
fragment precondition) and `hide */reveal` for the trivially-true ones, the lemma verifies as 11
batches in **2:04** with 1 934 obligations closing individually at 300 s — and the band packs.

The lesson is not about this lemma. It is that *per-symbol, isolated, unlimited-time* verification
lets a false assertion sit in a "green" proof, and that a **package with a time budget** is the
instrument that exposes it: the failure to pack was the only signal we ever got.

## 3.2 Metrics

**Workspace.** 61 members (`linden.*`), 4 815 verified scopes; full rebuild after the namespace
rename: 22:37 → 00:17 (59 members, `--jobs 2`, `cores = 4` each) plus 00:33 → 00:45 for the last two
after one fix — **1 h 52 min wall for the whole L5 equivalence**, no isolation anywhere. Level
times 15 s – 15 min 43 s (level 19, the LiftSim bands). Largest members by scopes: main-theorem 641,
reasoning 389, pike-inv-re 304, lift-sim-core 272, nest-inv 226. `lem pack` reuse means a change
in one band re-verifies that band and its dependents only.

**The six lemmas.** 66 verification runs (batch + isolate) over ~6 hours to close them: LBDeep 26,
L3a 14, gate 11, LBBase 11, ChildLinkLift 4, MainTheoremL5 2. Isolate passes (60–300 s per
obligation): LBBase 1 238 obligations → 3 non-closing (all ensures-wf artefacts); LBDeep 1 820 →
19 non-closing, then 17, 8, 5, 2, 0 across the iterations; L3a 2 572 → 10. Every non-closing
obligation was a hidden fact, a well-formedness artefact of the export, or a false claim; none was
a genuinely expensive proof step.

| lemma | before | after |
|---|---|---|
| `ForwardFindRecLBBase` | `{:isolate_assertions}` | 2:01 / 1 s / 0.8 s / 1.9 s |
| `FLookLoopChildLinkLift` | `{:isolate_assertions}` | 2 s / 1 s / 3 s |
| `L3aEndpointAssembly` | > 900 s | 16 batches, 41 s |
| `LiftPreserveGatePassLk` | `{:isolate_assertions}` | 3 s / 7 s / 23 s |
| `ForwardFindRecLBDeep` | "1808/0 in 2 h 03 min" isolated; two false asserts | 11 batches, 2:04 |
| `MainTheoremL5` (the hub) | > 900 s as one VC; the main band never packed | 10 batches, max 4:33 |
| `ActionsTreeRepLkFRec` (core) | 539 s, one batch | 10 batches, 2:30 |
| `ActionsTreeRepLkF` (core) | 384 s | 10 batches, 2:41 |
| `DeepFindRecLB` (deep) | 257 s | 5 batches, 39 s |
| `MainTheoremL5` (round 2) | 279 s solver, one 4:33 batch | 24 batches, 44 s |
| `LookRowsDynamicNested` (main-theorem) | 900 s timeout in the profile (flaky at the pack limit) | 4 batches, 5.7 s |
| `CompileNfaRepNestedRE` (nfa-rep-re) | 251 s | 8 arms, 7 s |

## 3.3 The strategy this enabled
1. **Package = unit of proof cost.** Split a monolith along its lemma-call DAG (tree-sitter gives
   the graph); each band gets a `cores`/time budget and its own line in `lem pack`.
2. **Pack = the gate.** Whole-file, dependency-ordered, warning-free, time-limited; no per-symbol
   green counts. A member that will not pack names the lemma to work on.
3. **Restore = the probe bench.** A member's `deps/` is the exact closure a suspicious claim can be
   tested against in isolation, in a minute.
4. **Profile per band, not per project.** `--log-format text` on one member (< 30 min) ranks its
   scopes; the whole monolith cannot be profiled inside a sane time budget.
5. **Then the proof-engineering loop** (sections + `split_here`, isolate-at-60 s, restate hidden
   facts, `hide */reveal`, probe the claim) — `AGENTS.md` §2–3 — and re-pack.

## 4. What would make it better
- A per-scope profile in `lem pack` output (the text log's resource counts) would remove step 2.
- A `lem verify --isolate <member> --time-limit 60` shorthand for step 3.
- The worker's toolchain install must be able to provide the pinned Dafny (the 4.11.0 rejection).
- The Dafny text logger crashes under `--isolate-assertions` (a `System.Linq.Async` exception);
  until fixed, read timeouts from stdout.
