# linden-equiv

The **pinnacle theorem**: the RegElk regex engine matches the Linden reference
semantics, end to end — plus the engine-facing match API built on it.

`MainTheorem` proves that, for a supported pattern and any input, the RegElk
engine's full-match result (the Node-compatible capture array) is exactly the
`MatcherSpec` answer the Linden backtracking-tree semantics prescribes. It
threads the whole pipeline together — the NFA representation, the actions/tree
representation, the Pike simulation invariant, and the first-leaf
correspondence — over the checked tree the engine actually walks. On top of it
sit the engine-face API theorems (`TypedCapture` / `NoMatchMeansAbsent` stated
on the engine's `Match`).

## Contents

- **Representation** — `LindenElkNfaRep`, `LindenElkActionsRep`,
  `LindenElkActionsTreeRep`, `LindenElkTreeRep`, `LindenElkTreeThread`,
  `LindenElkGenStep`, `LindenElkWalkOk(Entry)`, `LindenElkNestInv`,
  `LindenElkClockMono`, `LindenElkCheckErase`, `LindenElkRegsLaws`.
- **Simulation** — `LindenElkPikeSim`, `LindenElkPikeInv`.
- **Pinnacle** — `MainTheorem` (`MainTheorem` / `MainExtraction`).
- **API** — `LindenRegexApi` (`ApiMatch`), `LindenRegexReasoning`
  (`ApiReasoning`), `LindenRegexPatterns` (`Patterns`).

## Dependencies

- **`linden-reasoning`** — the translation bridge and semantics API.
- **`linden-engine`**, **`linden-engine-model`** — the Pike VM equivalence and NFA model.
- **`linden-semantics-core`**, **`linden-warblre`** — semantics and primitives.
- **`regex-engine`** — the RegElk engine (bytecode, compiler, interpreter).

## Related packages

Part of the [`linden-spec`](https://github.com/hath995/linden-spec) monorepo:

```
linden-warblre
  └─ linden-semantics-core
       ├─ linden-engine-model → linden-engine ─┐
       └─ linden-reasoning ────────────────────┤
              └─ linden-equiv   ← you are here (consumes both branches + regex-engine)
```

## A note on verification

`MainTheorem`/`MainExtraction` carry `hide T.TransWf, NR.PlusFragmentRE;`: those
recursive predicates are only needed as folded hypotheses, and leaving their
definitions visible triggers a Z3 e-matching loop on some solver builds. The
rep-compilation lemmas (`CompileNfaRep*`, `ActionsTreeRepF`) keep
`{:isolate_assertions}` — their monolithic VCs otherwise exceed the per-task
budget. The declared `verification-time-limit` is raised accordingly.

## Building

```
lem restore    # materialize the full dependency closure
lem build      # verify against the restored closure
```
