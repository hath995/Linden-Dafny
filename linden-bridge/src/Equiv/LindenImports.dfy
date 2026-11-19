// Pulls the DafnyLinden development into the LindenElk program.
// The Linden reference semantics now lives in the sibling `linden-semantics`
// package, linked as a dependency (see lemmata.toml). Its modules (Correctness,
// FunctionalUtils, and the whole Semantics chain) are in scope through the
// dependency's verified library, so no `include` is needed; files reference
// them directly with `import`.
