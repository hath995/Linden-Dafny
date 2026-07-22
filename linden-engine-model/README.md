# linden-engine-model

The **NFA bytecode-compilation model** — the base layer of the proof that the
RegElk Pike VM matches the Linden reference semantics.

This package establishes how a compiled regex's bytecode *represents* the
regex structurally (`NfaRep`): that `compile_to_bytecode` produces a
well-formed NFA whose control flow mirrors the AST. It is the lower half of the
engine correspondence — the piece the simulation/equivalence layer
(`linden-engine`) builds its invariant on top of. It contains one of the two
verification cost centers, `CompileNfaRep*`, isolated here so no single build
carries both.

## Contents

| Module | Role |
|--------|------|
| `NFA` | `compile_to_bytecode` and its structural correctness (`NfaRep`, `CompileNfaRep*`). |
| `BooleanSemantics` | The boolean (match / no-match) view of the tree walk. |
| `SeenSets` | The visited-thread bookkeeping for the linear-time simulation. |
| `PikeSubset` | The Pike-VM-compatible subset of the semantics. |

## Dependencies

- **`linden-semantics-core`** — the reference tree semantics (transitively `linden-warblre`).

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

You're in **`linden-engine-model`** (the NFA-compilation cost center).

## Building

```
lem restore    # materialize the dependency closure
lem build      # verify against the restored closure
```
