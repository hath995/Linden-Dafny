# linden-engine

The **Pike VM ⇔ backtracking-tree equivalence** — the upper half of the
compiled-engine correspondence, proving the linear-time simulation computes the
same first leaf the reference semantics prescribes.

Built on `linden-engine-model`'s bytecode representation, this package carries
the simulation invariant (`PikeInv`/`PikeSim`) and the tree-representation
correspondence (`TreeRep`) up to `PikeEquiv`: that running the Pike VM's
thread-set simulation over the compiled bytecode yields exactly the priority
tree's first leaf. It also carries termination. This is the second verification
cost center (`TreeRep`/`PikeEquiv`), kept separate from the NFA layer.

## Contents

| Module | Role |
|--------|------|
| `TreeRep` | The engine's checked tree ⇔ the spec tree representation. |
| `PikeVM`, `PikeTree` | The Pike VM simulation over threads / the priority tree. |
| `PikeEquiv` | The equivalence: simulation result == tree first leaf. |
| `FunctionalPikeVM`, `Correctness` | The functional VM and its correctness. |
| `Termination` | Linear-time termination of the simulation. |

## Dependencies

- **`linden-engine-model`** — NFA bytecode compilation model
  (transitively `linden-semantics-core`, `linden-warblre`).

## Related packages

Part of the [`linden-spec`](https://github.com/hath995/linden-spec) monorepo:

```
linden-warblre
  └─ linden-semantics-core
       ├─ linden-engine-model
       │    └─ linden-engine        ← you are here
       └─ linden-reasoning
              └─ linden-equiv       consumes this to relate the RegElk engine
```

## Building

```
lem restore    # materialize the dependency closure
lem build      # verify against the restored closure
```
