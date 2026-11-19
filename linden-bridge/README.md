# linden-bridge

The **RegElk → Linden bridge**: the definitions and shared facts that connect the RegElk
regex AST to the Linden backtracking-tree semantics. The reasoning API
([`linden.reasoning`](../linden-reasoning)) and every layer of the engine-equivalence proof
([`linden.equiv`](../linden-equiv)) build on it.

Use it directly if you want to state or prove your own facts that relate RegElk patterns to
the Linden semantics. If you want ready-made facts about what a particular pattern matches,
use `linden.reasoning`. If you want the verified matcher, use `linden.equiv`.

## Contents

- **`LindenElkTranslate`** (`Translate.dfy`): the canonical translation of a RegElk regex
  into a Linden regex, character-level agreement (`CharSemAgree`), and the well-formedness
  predicates: `Latin1Wf` (half of `linden.equiv`'s `Supported`) and `TransWf`.
- **`LindenElkSpec`** (`Spec.dfy`): the matcher specification `MatcherSpec`, the regexp
  record `TheRer`, and the spec regex `SpecRegex` that `linden.equiv`'s `MatchCorrect` is
  stated against.
- **`LindenElkNullable`** (`NullableFacts.dfy`): RegElk's nullability annotation compared
  with the semantics.
- **`LindenSpanDuality`**, **`LindenTreeMirror`**, **`LindenTreeResMirror`** and
  **`LindenCloseDisc`**: Linden-side span facts and the tree and leaf-value mirror used for
  lookbehinds.

Only the regex **AST** (`RegElkRegex`, `Charclasses`, `Anchors`) is imported from
`regex-engine`, never its execution modules.

## Dependencies

- **`regex-engine`**: the RegElk regex AST.
- **`linden-semantics-core`**: the reference tree semantics.
- **`linden-warblre`**: ECMAScript primitives.

## Building

```
lem restore    # materialize the dependency closure
lem build      # verify against the restored closure
```

Part of the [`Linden-Dafny`](https://github.com/hath995/Linden-Dafny) monorepo.
