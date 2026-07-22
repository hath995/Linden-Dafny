# linden-semantics-core

The **ECMAScript-faithful backtracking-tree semantics** for regular
expressions — the Linden reference spec's *meaning of a regex*, independent of
any engine.

A regex applied to an input string denotes a **priority tree** whose leaves are
the possible matches in ECMAScript disambiguation order; the first leaf is *the*
match a conforming engine must return. This package defines that tree, the
`GroupMap` capture semantics, and the rewriting/monotonicity theory used to
reason about it. Everything downstream — the compiled-engine equivalence and the
user-facing reasoning API — is proved *against this*.

## Contents

- **Semantics** — `Regex`, `Chars`, `Groups`, `Tree`, `Semantics`,
  `FunctionalSemantics`, `ComputeIsTree`, `StrictSuffix`, `FunctionalUtils`:
  the regex AST, the backtracking tree (`IsTree`), and its executable mirror.
- **Properties** — `Monotony`, `StrictlyNullable`: structural facts the tree
  proofs rely on.
- **Rewriting** — `Equivalence`, `FlatMap`, `LeavesEquivalence`: tree
  equivalences (leaves-preserving rewrites) that the engine correspondence uses.
- `Parameters`, `Inst`: the ECMAScript parameter instantiation.

## Dependencies

- **`linden-warblre`** — ECMAScript character/numeric primitives.

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

You're in **`linden-semantics-core`** — the semantics every downstream package
is proved against.

## Building

```
lem restore    # materialize linden-warblre from the registry
lem build      # verify against the restored closure
```
