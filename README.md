# Linden-Dafny

A machine-checked (Dafny) formalization of **ECMAScript regular-expression
semantics** and its **equivalence with the [RegElk](https://github.com/hath995/regex-engine)
engine**, developed as a [lem](#setup-with-lem) workspace of seven
independently-verified packages.

At the top sits `MainTheorem` (in `linden-equiv`): for a supported pattern and
any input, the RegElk engine's full-match result — the Node-compatible capture
array — is *exactly* the answer prescribed by the Linden backtracking-tree
reference semantics. Everything below it is the layered scaffolding that theorem
stands on: the ECMAScript primitive vocabulary, the reference semantics, the NFA
compilation, the Pike-VM ⇔ tree equivalence, and the engine-independent
reasoning API.

## Architecture

The project is split into a dependency DAG so that no single verification run
carries the whole proof — each package verifies against its dependencies'
proof-carrying `.doo` artifacts rather than re-checking their source.

```
  linden-warblre                 regex-engine
  (ECMAScript primitives)        (RegElk engine port: bytecode, compiler, interp)
        │                              │
        ▼                              │ (AST only)
  linden-semantics-core               │
  (backtracking-tree semantics)       │
        │            │                 │
        ▼            └───────────┐     │
  linden-engine-model            ▼     ▼
  (NFA bytecode compilation)  linden-reasoning
        │                     (engine-independent semantics API)
        ▼                          │
  linden-engine                    │
  (Pike VM ⇔ tree equivalence)     │
        │                          │
        └────────► linden-equiv ◄──┘
                   (pinnacle: RegElk ⇔ Linden + match API)
```

| Package | Role |
|---------|------|
| **linden-warblre** | ECMAScript primitive layer (numeric helpers, character classes, `RegExpRecord`). Leaf. Named after [Warblre](https://github.com/epfl-systemf/Warblre) (EPFL). |
| **regex-engine** | The [RegElk](https://github.com/hath995/regex-engine) regex engine (a Dafny port): bytecode, compiler, array interpreter, oracle. Leaf. |
| **linden-semantics-core** | The Linden backtracking-tree reference semantics + rewriting/properties. |
| **linden-engine-model** | NFA representation and bytecode compilation (the `CompileNfaRep*` layer). |
| **linden-engine** | Pike VM ⇔ backtracking-tree equivalence, functional Pike VM, correctness/termination. |
| **linden-reasoning** | Engine-**independent** semantics API: the translation bridge, capture content, typed-capture reasoning. A consumer wanting only the semantics never pulls the engine. |
| **linden-equiv** | The pinnacle: `MainTheorem` (RegElk ⇔ Linden, end to end) plus the engine-facing match API. |

## Repository layout

```
Linden-Dafny/
├── lem-workspace.toml        # workspace root: members, shared toolchain + options
├── linden-warblre/           # each member is an ordinary lem package
│   ├── lemmata.toml          #   manifest (name, version, deps)
│   ├── lemmata.lock          #   pinned dependency closure
│   ├── dfyconfig.toml        #   Dafny build config
│   └── src/ …
├── linden-semantics-core/
├── linden-engine-model/
├── linden-engine/
├── linden-reasoning/
├── linden-equiv/
└── regex-engine/
```

Every member is a self-contained lem package — it builds and verifies identically
whether standalone or as part of the workspace. The `lem-workspace.toml` groups
them so the whole graph locks, restores, verifies, and publishes as a set, in
dependency order.

## Setup with lem

This repository is driven by **lem** (the Lemmata verified package manager for
Dafny; registry at `registry.lemmata.sh`). lem carries its own hash-pinned Dafny toolchain
(this workspace requires **Dafny ≥ 4.11.0** with the standard libraries), so you
do **not** need a separate Dafny install to verify.

### 1. Install lem

Install the `lem` CLI following the Lemmata install instructions
(e.g. `scoop install lem` on Windows). Confirm it's on your `PATH`:

```sh
lem ls        # from a workspace root, lists members in dependency order
```

### 2. Clone

```sh
git clone https://github.com/hath995/Linden-Dafny
cd Linden-Dafny
```

`regex-engine` is now vendored **in-tree** (a first-class workspace member), so
there is nothing else to clone.

### 3. Lock + restore

Run these at the workspace root. They fan out over every member.

```sh
lem lock       # re-lock the set: internal edges float to siblings, external deps MVS-pinned
lem restore    # materialize each member's external dependency closure into its deps/
```

`lem restore` fetches only **external** dependencies (each as a verified `.doo`).
The **internal** edges between members are produced by the graph build itself, in
dependency order — nothing to fetch.

### 4. Verify

```sh
lem verify     # verify all members, dependencies-first, stop-on-first-failure
```

Each member is checked against its internal dependencies' freshly-built sibling
`.doo` (proof-carrying, so downstream stays fast) and its external deps from the
restored closure. To work on a single package, `cd` into it and run `lem verify`
there — a member subdirectory keeps its standalone single-package behavior.

### Building artifacts / publishing (maintainers)

```sh
lem pack       # build each member's publishable artifacts (.doo + source) into .lem-publish/
lem publish    # publish leaf-first to the registry; re-locks each internal edge to the
               #   just-published version as it goes
```

## Verification status

The full graph verifies green end to end:

| Member | Obligations | Time |
|--------|------------:|-----:|
| linden-warblre | 8 | 8s |
| linden-semantics-core | 210 | 40s |
| linden-engine-model | 72 | 1m 50s |
| linden-engine | 117 | 5m 17s |
| regex-engine | 180 | 22s |
| linden-reasoning | 206 | 43s |
| linden-equiv | 644 | 8m 55s |
| **Total** | **1437** | **~18m** |

`linden-equiv` is a genuinely heavy proof; a couple of its lemmas carry
`{:isolate_assertions}` and the pinnacle uses `hide` to keep the SMT solver off
an e-matching loop. Expect the full workspace verify to take on the order of
tens of minutes on a many-core machine.

## Provenance & license

- **Warblre** — the mechanized ECMAScript RegExp semantics whose definitions
  `linden-warblre` draws from — is by the [EPFL Systems & Formalisms lab](https://github.com/epfl-systemf/Warblre).
- **RegElk** — the regex engine `regex-engine` ports — informs the engine side of
  the equivalence.

See each package's `LICENSE` for its terms.
