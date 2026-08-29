# AGENTS.md — Dafny proof-engineering playbook for Linden-Dafny

Lessons from the L5 / E3 campaign (2026-08-28/29, commit 1d2f65a on `lem-split`, mirrored to `l4-nesting`) on `linden-equiv` (Dafny 4.11, Boogie, Z3),
plus the techniques we adopted from the Dafny-VMC guidelines. Read this before touching a lemma
that verifies slowly or a package that packs over the 900 s time limit.

## 0. Ground rules

- **A verification job over 30 minutes has failed.** Kill it (the `watchdog.sh` pattern) and diagnose;
  never "wait it out". The registry worker kills builds at 15 min.
- `verification-time-limit` stays ≤ 900 in every manifest (the registry rejects more).
- `{:isolate_assertions}` / `--isolate-assertions` is a **diagnostic**, never the shipped proof. It
  re-encodes the whole context per assertion (memory × time multiplier) and hides the real problem.
- All dafny/z3 runs go through the cgroup-wrapped launchers (`dafny.slice`, 80 GB cap); one giant at a time.
- Per-symbol green (`--filter-symbol`) proves nothing about callees' bodies or helpers' well-formedness;
  only a full-file/package run (`lem pack`) is airtight.

## 1. How a slow lemma actually fails (what the timeouts meant)

Measured with `--isolate-assertions` + `--log-format text` (per-obligation resource counts):

1. **Unprovable goals present as timeouts, not errors.** In this theory mix Z3 rarely finds a
   counter-model; a goal that is simply missing a fact burns the whole time limit. "Batch times out"
   ≠ "batch is heavy" — first ask which fact is missing.
2. **Well-formedness of exported facts is checked in the *outer* context.** An opaque block's
   `ensures` are wf-checked where the block's internals are hidden: a `.value` without the `.Some?`
   before it, a `nat`-typed local that lost its annotation, an out-parameter assigned inside the
   block, a `FFindMatch(...)` unfolding whose preconditions need hidden facts — each is unprovable
   there → 300–900 s each. Three such obligations made a 46-statement preamble "cost 900 s";
   with them fixed the same preamble verifies in 4–11 s.
3. **Every real obligation was cheap.** 1 238 / 1 820 obligations of the two worst lemmas each cost
   ≤ 2.5 M resources (< 2 s). Volume was never the problem; hidden facts and wf artefacts were.
4. **A batch can loop where each obligation alone does not**: the union of ground terms enables
   instantiations no single goal triggers. Sub-splitting the section (`{:split_here}`) or hiding the
   quantified facts (opaque wrapper predicates) breaks it.

### 1.1 Measured results (2026-08-29, per-symbol, no isolation)

| Lemma | before | after |
|---|---|---|
| `ForwardFindRecLBBase` | `{:isolate_assertions}` | 4 batches: 2:01 / 1 s / 0.8 s / 1.9 s |
| `FLookLoopChildLinkLift` | `{:isolate_assertions}` | 3 batches: 2 s / 1 s / 3 s |
| `L3aEndpointAssembly` | > 900 s (one batch) | 16 batches, 40.7 s total |
| `LiftPreserveGatePassLk` | `{:isolate_assertions}` | 3 batches: 3 s / 7 s / 23 s |
| `ForwardFindRecLBDeep` | > 900 s (2 h 03 min isolated, with two false asserts) | 11 batches, 2:04 total |

## 2. The tools, in the order to reach for them

### 2.1 Opaque blocks (Dafny ≥ 4.10)
```dafny
var x: T := *;          // pre-declare the locals the rest of the proof needs
opaque
  ensures x == E && P(x) && Q     // ONLY these facts survive the block
{
  x := E; ... lemma calls ... asserts ...
}
```
- Hides the block's internal facts from everything after it (context shrinks for the rest).
- **Does NOT split the VC** — the lemma is still one assertion batch. Pair with `{:split_here}`.
- Locals: declare as `var x: T := *;` (definitely assigned, keeps the subset type). Keep the
  original type annotations (`nat`, `LG.GroupMap`, `seq<(LT.Tree, LG.GroupMap)>`), otherwise
  inference picks the base type and the exported ensures fail their subset checks.
- Out-parameters assigned inside a block: `out := *;` before the block and export `out == E`.
- Export facts **in source order** (the body was well-formed in that order); hoist only bare
  `x.Some?` facts. Export the definition of every local used downstream, multi-line ones included.
- Export lemma *postconditions* and call-site *preconditions* that later code needs by restating
  them as `assert`s inside the block — the generator only sees asserts and definitions.
- A `forall … ensures E { … }` *statement* is a fact too (`forall binders :: range ==> E`); export it.
  Facts whose identifiers are not referenced downstream are still needed by well-formedness
  (`FirstLeaf(t1, inp1).Some?` before `.value`), so `--export-all` a block when in doubt.
- Ordering is per block: defs-first suited `LBDeep`'s preamble, source order suited its block 2
  (`bodyA1 == LookBodyOfRE(re, A1)` must follow `A1 in LookIds(re)`). Try both; the wf errors say.
- Not every section should be opaque: when a later section needs a lemma *post* established in
  an earlier one, leave the earlier section a plain `{:split_here}` section (its facts stay visible)
  and make only the later, heavier sections opaque.
- Destructuring declarations (`var PTS(a, b, c) := s;`, `var (r, o) := f(...)`) become
  `var PTS(a', b', c') := s; a, b, c := a', b', c';` with `s == PT.PTS(a, b, c)` exported.
- The generator: `tools/e3/e3opaque.py FILE LEMMA END_MARKER [--from START_MARKER] [--export-forall]
  [--types 'x:T;y:U'] [--no-some name] [--apply]` (tree-sitter-dafny based; nested blocks supported).

### 2.2 `assert {:split_here} true;`
One line at each section boundary → one assertion batch per section, earlier assertions assumed.
Five batches of 1–20 s instead of one 900 s batch. Also splits a residual that loops as a whole.

### 2.3 `assert P by { ... }` scoping
Put carrier-lemma calls with large quantified postconditions inside a `by` block that asserts only
the instance you need; the quantifier never enters the outer context.

### 2.4 Opaque / nested-opaque wrapper predicates (the VMC "reveal only what you need")
```dafny
opaque predicate StaticsO(re) { TransWfO(re) && NestedO(re) && ScopeO(re) }   // each conjunct opaque too
lemma L(...) requires StaticsO(re) { ... assert X by { reveal NestedO(); } ... }
```
Ground fact stays in context for free; bodies are revealed only inside the `by` block that needs
them. Preferred over labeled `requires L: P` for facts that cross lemma boundaries (the recursive
descent `ForwardFindRec → LB → LBDeep → LBBase` passes them as ground facts).

### 2.5 Labeled requires
`requires L: P` + `reveal L;` inside a `by` block. Cheapest to try; hides the fact completely
(callees needing it must reveal). Use when the fact is local to one lemma.

### 2.6 Splitting lemmas
Extract a case arm / a section into its own lemma with an explicit measure ladder
(`decreases ..., n, 2` parent → `..., n, 1` → `..., n, 0` arms). Done for `ForwardFindRec{LB,LBDeep,
LBBase}`, `DeepFindRec{FwdBase,FwdDeep}`, `ATR_Quant{Min,NN,Star}`.

### 2.7 hide / reveal for functions
`hide M.FreshBodyMatch; hide AI.FFindMatch;` before an unfolding step keeps recursive function
bodies from expanding; `reveal` where the unfolding is the point. `opaque` on the declaration
(not `{:opaque}`) for predicates whose body should never leak.

### 2.8 Triggers and matching loops
Carriers quantified over lids built from recursive regex predicates (`LookNestOkTTop`,
`LookNestBackTTop[Deep]`) × recursive function unfolding (`compile_to_bytecode(reverse_regex(…))`)
loop. Guard with a cheap membership conjunct (`lid in LTB.LookIds(re) && ...`), scope the instance
(2.3), or wrap (2.4). Cast-free trigger terms (`var li: int := l as int; exists ... LookEntryOk(fc, li, ...)`)
for `exists` witnesses.

### 2.9 `hide *` + `reveal F` inside a `by` block (the strongest context cut)
```dafny
assert ctxB.nextchar == AI.get_char(str, cpA - 1) by {
  hide *; reveal AI.cp_context;
  assert ctxB == AI.cp_context(cpA, str, LAnc.Backward);
}
```
A one-step unfolding that a standalone probe proves instantly can still burn 300 s inside a big
lemma: Z3 saturates the context's quantifiers before it evaluates the goal. Hiding every function
body and revealing the one you need makes the goal a pure unfold again. Use it for every "trivially
true but slow" fact; prefer it over restating the fact as a lemma.

### 2.10 A false assertion that "verified" is the loudest signal you will get
`ForwardFindRecLBDeep` carried two copy-overs from its forward twin — `ctxB.nextchar ==
get_char(str, cpA)` (the backward context reads `cpA - 1`) and `FirstLeaf(t1, inp1) == TreeRes(t1,
Empty, inp1, dir1)` (a forward leaf equated with a backward one) — and a 2 h isolated run had been
recorded as 1808/0. Either the record was wrong or the context there was inconsistent; in both
cases the "slow" obligations downstream were unprovable, not slow. When an obligation never closes
in isolation, **check the claim itself with a 10-line standalone probe** before tuning anything, and
probe `assert false;` at the lemma head (refuted in seconds ⇒ the hypotheses are consistent).

## 3. Diagnosing (the loop that worked)

1. `dafny verify --filter-symbol=Mod.Lemma --verification-time-limit=300 --log-format 'text;LogFileName=…'`
   → per-batch outcome and duration. (Text logger crashes with `--isolate-assertions`; run that one
   without the logger and read the timeouts from stdout.)
2. `--isolate-assertions --verification-time-limit=60 --error-limit 0`: everything that does not
   close in 60 s is either a missing fact or one of the few genuinely heavy obligations. Fix the
   missing facts first (restate them inside the block); they are the majority.
3. Sub-split any residual that still times out as a batch though its obligations are cheap.
4. Only then treat what is left as heavy proof: wrapper predicates, by-scoping, lemma extraction.
5. `dafny resolve` after every generated edit (seconds) before any 15-minute run.

Pitfalls: `pkill -f` / `pgrep -f` match your own shell — anchor patterns (`^/home/.../dafny.real
verify .*Lemma`); `--boogie` options are rejected by `.doo` manifests (use manifest-patched scratch
deps for Boogie `/proc`, `/trace`); Dafny "starts at column" is 1-based, warning columns 0-based;
`.doo` error locations point into the serialized `program`, not source lines.

## 4. From the Dafny-VMC guidelines (adopted / not adopted)

Adopted: make functions opaque; name preconditions and reveal only when necessary; keep each
lemma under ~1 M resources as the target; split universally quantified / conjunctive / biconditional
lemmas into directional pieces; establish preconditions in `by` clauses; no
`vcs_split_on_every_assert`-style directives in shipped code; explicit types on the locals an
opaque block exports.
Not adopted (no verification benefit here, large churn): banning `import opened`; removing
postconditions from functions; retyping every local.

## 5. Package / build facts that matter for proof time

- `.doo` splitting alone does not speed verification; parallelism and lemma-arm splitting do.
- Band split of `LiftSim` into `core/oracle/chain/gate/carriers/deep/forward/main` packages; each
  packs under `lem pack` with `cores = "4"` (forward `"2"`), `verification-time-limit = "900"`.
- Warnings gate: any source warning refuses the `.doo` (`==>` parenthesization, missing triggers).
- Namespaces: `lem` ≥ 0.1.21, `[package] namespace = "linden"`, dotted unquoted dep keys, no
  `path` segment anywhere.
