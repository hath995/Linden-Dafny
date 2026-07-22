# linden-warblre

The **ECMAScript primitive layer** of the Linden reference regex specification —
the small, self-contained vocabulary every higher layer is built on.

Named after **[Warblre](https://github.com/epfl-systemf/Warblre)** (the
mechanized ECMAScript RegExp semantics it draws its definitions from), this
package defines the foundational data the rest of the Linden stack quantifies
over. It is a leaf: it depends on nothing but the Dafny standard libraries.

## Contents

| Module | What it provides |
|--------|------------------|
| `WarblreNumeric` | ECMAScript numeric primitives (code-point / integer helpers). |
| `WarblrePrimitives` | Character classes and the ECMAScript whitespace / line-terminator sets (`U+2028`, `U+2029`, `U+00A0`, `U+FEFF`, …). |
| `WarblreRegExpRecord` | The `RegExpRecord` — the ECMAScript spec's per-match configuration (flags, capture count). |

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

You're in **`linden-warblre`** — the leaf every higher layer builds on;
`regex-engine` (the RegElk engine) is the other leaf.

## Building

```
lem build      # verify (no dependencies to restore)
lem publish    # publish to the registry
```
