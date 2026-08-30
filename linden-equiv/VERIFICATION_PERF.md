# Verification performance — what was measured (2026-08-28)

All numbers from this machine (32 cores, 125 GB, Dafny 4.11, all dafny/z3 inside the 80 GB
`dafny.slice` cgroup). Read this before attempting a restructure "to make verification faster".

## 1. Where the time goes

A `--filter-symbol` run splits into a fixed FRONT END (parse + typecheck of the file's whole include
closure) and the prover.

| measurement | time |
|---|---|
| `dafny resolve` on `LiftSim.dfy` (110k-line closure) | 188 s |
| `dafny verify` on it with **0 matching symbols** (resolve + Boogie translate) | 178 s |
| a real small lemma (`LookBodyRowL5`) | 239 s |

So Boogie translation is free, the front end is ~180-190 s, and a small lemma's own proving is ~50 s.

## 2. `.doo` packaging does NOT reduce it

| closure in scope (trivial consumer, everything as `.doo`) | front end |
|---|---|
| deps only | 6 s |
| + core layer (`MainTheorem` closure: 32 files, 70.7k lines) | 31-40 s |
| + flip layer (Flip*/LookBehind*/PikeTreeLk: 14 files) | 66-70 s |
| + `LiftSim` (ONE 29.7k-line module) | 192-199 s |

* Content costs the same as **source** or as **library**: LiftSim as source + 80k `.doo` = 183 s;
  LiftSim as `.doo` + a 4-line consumer = 192 s.
* A library is fully loaded **even when the dependent imports nothing from it** (6 s -> 31 s -> 66 s
  for a file with no imports at all).
* A full three-package split (core / flip / lift, built as layered `.doo`s) was implemented and
  measured end to end: **core 55->57 s, flip 44->43 s, lift 241->238 s**. No gain.

Why: Dafny's compilation unit is already the FILE'S OWN include closure, not the repository, and
`LiftSim.dfy` directly imports 41 of the 46 modules in its closure — there is no unused content to
remove. `.doo` deps still pay for themselves by not re-VERIFYING dependencies; that saving is already
banked in `deps/`.

## 3. Module `export` sets: a real but modest lever

Synthetic module, 6000 declarations, consumed by a 3-line file (floor = 0.71 s):

| library | consumer |
|---|---|
| everything exported | 5.79 s (5.1 s above floor) |
| `export provides` 300 names | 4.39 s (-27%) |
| `export provides` 2 names | 4.27 s (-29%) |

~28% off the *library-attributable* front end, and nearly independent of how many names are exported
(the saving is in not elaborating non-exported bodies). For `LiftSim` that is ~20 s of ~240 s (~8%),
because its own 29.7k-line module is source. Would require export sets on 46 modules plus fixing every
dependent that reaches into internals — not worth it at that ratio.

## 4. What DID work

| lever | gain |
|---|---|
| **parallelism** — small symbols are ~1.1 GB each, so PAR=10-12 CORES=2 | 11 symbols: **51 min -> 10 min (5x)** |
| **splitting a giant lemma's arm into its own lemma** (`DeepFindRecLB`, `ForwardFindRecLB`) + extracting shared blocks (`BackFreshPlusIsPlain`) | `DeepFindRec` **38 min -> 20 min** |
| **splitting the FORWARD arm too** (`{Deep,Forward}FindRec{FwdBase,FwdDeep}`, 2026-08-28; the parents are dispatch-only) | `ForwardFindRec` **4.3 h (CORES=2, the only config that fit the cap) -> FwdDeep 17.8 min + FwdBase 13.6 min at CORES=4** (1839 + 1281 VCs, each ~15 GB so they can run as two processes); `DeepFindRec` forward arms 14 min + 6.8 min (1458 + 332 VCs) |
| **whole-file well-formedness-only sweep** (Boogie `/proc:*well-formedness*` through manifest-patched `.doo` copies — see `linden-wf-sweep-harness` memory note) | all 51 files in ~15 min at PAR=4 (LiftSim 11 min, MainTheorem 2 min); it found 2 wf holes + 1 resolution error + 1 broken lemma that per-symbol runs had hidden |
| avoiding `--log-format text` | Dafny 4.11 `TextVerificationLogger` sums resource counts in Int32 and CRASHES (rc=134) on large lemmas |

Per-job memory scales with the LEMMA: trivial ~1.1 GB (PAR 10-12), medium ~8-13 GB (PAR <= 5),
giants 15-19 GB (PAR 1; `ForwardFindRec` needs CORES=2). A z3 worker on the worst descent VCs can reach
15+ GB: `ForwardFindRecLB` (410 lines) OOM-killed the 80G slice ALONE at CORES=4 (2026-08-28) and had to be
split like the forward arms; a whole-file LiftSim run needs ~35 GB and must run alone or beside ONE giant.

## 5. Opacity (`hide` / `opaque`) as a blanket setting: a wash (but see §6 — scoped, it is the lever)

`ReverseCDeepFull`, identical conditions: baseline 477 s / 552 VCs; hiding the 7 tree-recursive scope
predicates 436 s / 458 VCs (-9%); hiding all 15 (incl. `LookIds`/`CapIds`/`LookBodyOfRE`/`Translate`/
`GmOfLive`) 446 s. But on the giant `DeepFindRec`: 1341 s -> 1436 s (**+7%**, worse) despite 34% fewer
VCs. Direction depends on the lemma; not worth a declaration-level change.

Useful by-product — what the descent lemmas actually need unfolded: only `PSM.StaticOkNestedRE`/
`PSM.SizesOkRE`/`GateStaticAtNested`/`GateStaticsOkNested` (2 errors when hidden) and the clock
invariants `CM.LookCpSetWithClk`/`LookCpsLE`/`LookCpsOracleTrue`/`M.FLookLoopChildLinkOk` (1 error).
Everything else is a pass-through atom.


## 6. E3 (2026-08-29/30): what actually made the slow lemmas fast

Measured on the six lemmas that had needed `{:isolate_assertions}` or ran past 900 s, and on the twelve
profiled packages (details: `AGENTS.md`, `docs/LEMMATA_IN_PROOF_DEVELOPMENT.md`):

- **`assert {:split_here} true;` at section / match-arm boundaries** is the single biggest lever: one batch per
  section, earlier assertions assumed. `LookRowsDynamicNested` 900 s timeout → 5.7 s; `CompileNfaRepNestedRE`
  251 s → 7 s; `DeepFindRecLB` 257 s → 39 s; `MainTheoremL5` > 900 s → 44 s (24 batches). Dafny 4.11 opaque blocks
  do NOT split the VC; they only hide facts.
- **Missing facts present as timeouts, not errors** (Z3 rarely finds a counter-model here). An opaque block's
  exported `ensures` are wf-checked in the outer context, so a `.value` without its `.Some?`, a local that lost its
  `nat` type, or an unfold with preconditions each burns the whole limit. `--isolate-assertions
  --verification-time-limit=60` lists exactly the obligations to restate.
- **Scoped `hide *` + `reveal F` inside a `by` block** turns a trivially-true-but-slow fact (a one-step unfolding
  of `cp_context`) from 300 s into instant.
- **Every non-closing obligation was a hidden fact, an export artefact, or a false claim; none was a genuinely
  expensive proof step.** Two false assertions in `ForwardFindRecLBDeep` had been sitting behind a 2 h isolated
  "1808/0".
- Whole-workspace re-pack after the second round: 61/61 in 59 min at `--jobs 3` (level 19: 15:43 → 3:36).
