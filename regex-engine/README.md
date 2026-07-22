# regex-engine (RegElk)

A **verified, linear-time** JavaScript regular-expression matcher in Dafny — a
port of the OCaml **[RegElk](https://github.com/LindenRegex/RegElk)** engine
(EPFL SYSTEMF; Aurèle Barrière & Clément Pit-Claudel). It compiles an
ECMAScript-style pattern to bytecode and runs it as a Thompson/PikeVM
simulation, returning Node-compatible capture arrays in time linear in the
pattern × input — no catastrophic backtracking.

This repository is the **engine**. Its match results are proved correct against
the ECMAScript tree semantics in a separate package — see
[Related packages](#related-packages).

## The pipeline

```
  "(a)(b*)"                     raw_regex              regex               code
  ──────────►  Parser.parse  ──────────►  annotate  ──────────►  Compiler  ──────────►  Interpreter
   pattern         (PEG)      AST (raw)   (+ ids,     AST (ids)   .compile   bytecode    (PikeVM)
    string                                 group 0)                                          │
                                                                                             ▼
                                                              Option<seq<int>>  ── JS capture array
                                                              (slots 2i / 2i+1 = group i start/end,
                                                               group 0 = whole match, -1 = unset)
```

Every match runs under an implicit `lazy_prefix` (`.*?`) wrapper and a group-0
capture that `annotate` adds, so matching is *unanchored, leftmost*, with
ECMAScript **priority disambiguation** (greedy/lazy order) — it returns *the*
correct match, not just *a* match.

## Modules (`src/Engine/`)

| Module | Role |
|--------|------|
| `Parser.dfy` | ECMA-262-style pattern parser (`parse(s): Option<raw_regex>`), built from `Std.Parsers` PEG combinators. |
| `Regex.dfy` | The `raw_regex`/`regex` AST; `annotate` (assigns capture/lookaround/quantifier ids, wraps group 0); `lazy_prefix` (the `.*?` search prefix); nullability analysis. |
| `Charclasses.dfy` | Character classes → sorted, disjoint code-point ranges (`char_expectation`); `\d`/`\w`/`\s`; chars `0..255`. |
| `Compiler.dfy` | Annotated `regex` → `Bytecode` `code`; 2 registers per group (`start_reg`/`end_reg`); per-lookaround oracle bytecode and per-`+` capture-reconstruction bytecode. |
| `Bytecode.dfy` | The VM instruction set (`Consume`, `Accept`, `Fork`, `Jmp`, `SetRegisterToCP`, oracle/CDN/anchor ops, …). |
| `Interpreter.dfy` | The Thompson/PikeVM: threads stepped in lockstep by string position — an epsilon-closure phase (`advance_epsilon`) and a string walk (`find_match`) — plus oracle building, CDN tables, and nulled-`+` capture reconstruction. Entry points `full_match` / `matcher`. |
| `Regs.dfy` | Three thread-register backends — `Array_Regs`, `List_Regs`, `Map_Regs` — the time/space tradeoffs of the paper's §4.6. |
| `Oracle.dfy` | The lookaround oracle: `[position, lookaround-id] → bool`, precomputed so lookarounds cost nothing at match time. |
| `Anchors.dfy` | The zero-width anchors `^ $ \b \B`, evaluated over a two-character context window; scan `direction` (forward / backward for lookbehind). |
| `Cdn.dfy` | Context-Dependent-Nullable formulas, so eager `+` over context-dependent-nullable bodies terminates correctly. |

The `Interpreter` is instantiated once per backend:

```dafny
module ArrayInterp refines Interpreter { import R = Array_Regs }
module ListInterp  refines Interpreter { import R = List_Regs  }
module MapInterp   refines Interpreter { import R = Map_Regs   }
```

## What is proved *here*

This package establishes the engine's **internal correctness**:

- **Imperative ≡ functional.** Every imperative method has a pure functional
  counterpart (prefixed `F`) and is proved equal to it — e.g.
  `full_match(raw, str)` provably returns `FFullMatch(raw, str)`, for **all
  three** register backends. `FFullMatch` is the single functional model the
  whole engine collapses to.
- **Termination.** The interpreter carries no `decreases *`: the epsilon phase
  terminates on a "(unprocessed pc-slots, active threads)" measure, and the
  string walk on remaining input. Linear-time matching is a proved property,
  not a hope.

What is **not** proved here — that `FFullMatch` computes the answer ECMAScript
*demands* — is the job of the `linden-regex` proof (see below).

## Supported features & limits

Compiled for guaranteed linear-time matching: characters/classes, `.`,
alternation, concatenation, capture groups, greedy/lazy `*` `?`, greedy `+` and
`{n,m}`, anchors, and lookarounds (via the oracle).

- **`LazyPlus` (`+?`)** is the one quantifier shape that cannot be compiled for
  linear matching.
- **Backreferences** are *not expressible* — the AST has no constructor for one.
  This is by design: backreference matching is NP-hard, incompatible with the
  linear-time guarantee.
- **Parser** limits (mirroring the OCaml source): no named groups, no unicode
  property escapes, no backreferences; unsupported escapes (`\x \u \k \p \P
  \<digit>`) are parsed as identity escapes.

## Using it

```dafny
import ArrayInterp   // or ListInterp / MapInterp

method Example() {
  var ro := Parser.parse("(a)(b*)");
  if ro.Some? {
    var res := ArrayInterp.full_match(ro.value, "abbb");
    // res == Some([0, 4, 0, 1, 1, 4])  -- whole match, group 1 "a", group 2 "bbb"
    print res, "\n";
  }
}
```

`Driver.dfy` is a small CLI port of the OCaml `main.ml`:
`matcher -regex "(b)|.*" -string "abc" [-array|-list|-tree]`.

## Tests (`tests/engine/`)

The engine is checked differentially against real reference oracles:

- `Tests.dfy` — the paper's `paper_tests`, expected arrays generated from
  **Node**'s `RegExp` (with the `d` indices flag); each case is run through all
  three backends.
- `Test262.dfy` — a ported subset of **tc39/test262** `RegExp` staging tests.
- `OCamlCrossCheck.dfy` — outputs captured from the **original OCaml RegElk**.
- `PropertyTests.dfy` — property-based tests (`DafnyCheck`) using the live
  **JavaScript** engine as a differential oracle.
- `AocRegexTests.dfy` — Advent-of-Code regex cases.

## Verifying & building

```powershell
# verify the whole engine (pinned Dafny 4.11.0)
Dafny.exe verify dfyconfig.toml --allow-warnings

# build the library artifact other packages depend on (deps/regex-engine.doo)
Dafny.exe build -t:lib dfyconfig.toml --allow-warnings
```

## Related packages

RegElk is one of three Dafny packages that together give an end-to-end
machine-checked JS regex matcher:

- **`regex-engine`** (this repo) — the linear-time engine.
- **`linden-semantics`** — the Linden/Warblre backtracking-tree ECMAScript
  reference semantics (the *specification*).
- **`linden-regex`** — the equivalence proof: RegElk's `FFullMatch` **is** the
  answer the semantics demand (`MainTheorem`), on the *star fragment*. It also
  exposes the verified `Match` API and worked examples.

## License & attribution

MIT (© 2026 Aaron Elligsen). A Dafny port of the OCaml **RegElk**
(<https://github.com/LindenRegex/RegElk>, © 2024 EPFL SYSTEMF; Aurèle Barrière
and Clément Pit-Claudel), likewise MIT-licensed. See `LICENSE`.
