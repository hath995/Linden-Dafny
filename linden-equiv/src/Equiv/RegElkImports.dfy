// Pulls the DafnyRegElk development into the LindenElk program.
// The RegElk engine now lives in the sibling `regex-engine` package, linked as
// a dependency (see lemmata.toml). Its modules (Charclasses, RegElkRegex,
// Bytecode, Anchors, Oracle, Cdn, Regs, Compiler, Interpreter, Parser) are in
// scope through the dependency's verified library, so no `include` is needed;
// files reference them directly with `import`.
