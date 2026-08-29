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

## 4. What would make it better
- A per-scope profile in `lem pack` output (the text log's resource counts) would remove step 2.
- A `lem verify --isolate <member> --time-limit 60` shorthand for step 3.
- The worker's toolchain install must be able to provide the pinned Dafny (the 4.11.0 rejection).
- The Dafny text logger crashes under `--isolate-assertions` (a `System.Linq.Async` exception);
  until fixed, read timeouts from stdout.
