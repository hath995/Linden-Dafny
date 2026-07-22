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

You're in **`linden-engine`** (the Pike-VM ⇔ tree cost center); `linden-equiv`
consumes it to relate the RegElk engine.

## Building

```
lem restore    # materialize the dependency closure
lem build      # verify against the restored closure
```
