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

Part of the [`linden-spec`](https://github.com/hath995/linden-spec) monorepo:

```
linden-warblre
  └─ linden-semantics-core
       ├─ linden-engine-model       ← you are here
       │    └─ linden-engine        Pike VM ⇔ tree equivalence
       └─ linden-reasoning
              └─ linden-equiv
```

## Building

```
lem restore    # materialize the dependency closure
lem build      # verify against the restored closure
```
