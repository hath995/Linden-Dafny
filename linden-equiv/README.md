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

Part of the [`Linden-Dafny`](https://github.com/hath995/Linden-Dafny) monorepo,
which decomposes the Linden reference specification and its RegElk-engine
equivalence proof into independently-verified layers:

```
linden-warblre  ·  regex-engine     two leaves: ECMAScript primitives · the RegElk engine
  └─ linden-semantics-core          backtracking-tree reference semantics
       ├─ linden-engine-model       NFA bytecode compilation
       │    └─ linden-engine        Pike VM ⇔ tree equivalence
       └─ linden-reasoning          engine-independent reasoning API   (+ regex-engine AST)
              └─ linden-equiv       RegElk engine ⇔ semantics — pinnacle (+ regex-engine)
```

You're in **`linden-equiv`**, the pinnacle — it consumes both engine branches
plus `regex-engine`.

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
