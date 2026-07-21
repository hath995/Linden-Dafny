# linden-reasoning

The **engine-independent regex reasoning API** — prove facts about what a
pattern *means* (its captures, its match content) directly against the Linden
semantics, without pulling in the engine-equivalence proof.

This is the layer a consumer uses when the **semantics is the spec** for their
production JavaScript engine: they reason about pattern behaviour over Linden
trees, and never touch the (heavy) RegElk ⇔ semantics equivalence. It provides
the RegElk→Linden translation bridge and a set of headline theorems —
`TypedCapture` (a capture group's set membership, index bounds, and character
content), `SemResult` ("what a conforming engine returns"), and negative-search
(`NoMatchMeansAbsent`).

## Contents

- **Bridge** — `LindenElkTranslate` (`Translate`), `LindenElkReduce`,
  `LindenElkTransfer`, `LindenElkSpec`, `LindenElkNullable`: the canonical
  RegElk-regex → Linden-regex translation and the raw/spec transfer lemmas that
  bypass the fuel wall.
- **API** — `CaptureContent`, `LindenSemanticsReasoning` (`SemanticsApi`):
  `TypedCaptureTree`/`TypedCaptureSem`, `SemResult`, `WholeMatchSem`,
  `NoMatchAnywhereSem`, and the pattern-combinator facts.

Only the regex **AST** (`RegElkRegex`, `Charclasses`) is imported from the
engine package — never its execution modules — so this layer stays
engine-independent.

## Dependencies

- **`regex-engine`** — the RegElk regex AST (surface pattern representation).
- **`linden-semantics-core`** — the reference tree semantics.
- **`linden-warblre`** — ECMAScript primitives.

## Related packages

Part of the [`linden-spec`](https://github.com/hath995/linden-spec) monorepo:

```
linden-warblre
  └─ linden-semantics-core
       ├─ linden-engine-model → linden-engine
       └─ linden-reasoning          ← you are here (engine-independent)
              └─ linden-equiv       adds the RegElk engine correspondence
```

## Building

```
lem restore    # materialize the dependency closure
lem build      # verify against the restored closure
```
