// Port of anchors.ml
// How to match the different anchors. Anchors need a two-character context:
// the characters just before and just after the current position.
/** Evaluating the four zero-width anchors (`^`, `$`, `\b`, `\B`) against a
    two-character window of context around the current position. */
module Anchors {
  import opened Std.Wrappers
  import opened Charclasses
  import opened RegElkRegex

  // algorithms can traverse the string forward or backward; this changes
  // the behaviour of the anchors.
  /** Which way the engine is currently scanning the input: `Forward` or
      `Backward` (lookbehinds and reversed regexes scan backward). */
  datatype direction = Forward | Backward

  // surrounding characters of a position (None at the begin/end of input).
  // NOTE: going backward, the index of nextchar is smaller than prevchar's.
  // Modelled immutably (the OCaml record is mutable, updated in place).
  /** The characters immediately before and after the current position
      (`None` at the start/end of input); everything anchors need to decide
      whether they hold. */
  datatype char_context = CharContext(prevchar: Option<char>, nextchar: Option<char>)

  /** Slides the context window one character forward: the old `nextchar`
      becomes the new `prevchar`, and `newchar` becomes the new `nextchar`. */
  function update_context(ctx: char_context, newchar: Option<char>): char_context {
    CharContext(ctx.nextchar, newchar)
  }

  /** Whether a `WordBoundary` anchor holds at `ctx`: true iff exactly one of
      the surrounding characters is an ASCII word character. */
  predicate is_boundary(ctx: char_context) {
    match (ctx.prevchar, ctx.nextchar)
    case (None, None) => false
    case (None, Some(c)) => is_ascii_word_character(c)
    case (Some(c), None) => is_ascii_word_character(c)
    // xor
    case (Some(prev), Some(next)) =>
      is_ascii_word_character(prev) != is_ascii_word_character(next)
  }

  /** Whether anchor `a` holds at a position with context `ctx`, when the
      engine is scanning in direction `dir` (`BeginInput`/`EndInput` swap
      roles when scanning `Backward`). */
  predicate is_satisfied(a: anchor, ctx: char_context, dir: direction) {
    match (a, dir)
    case (BeginInput, Forward) => ctx.prevchar == None
    case (BeginInput, Backward) => ctx.nextchar == None
    case (EndInput, Forward) => ctx.nextchar == None
    case (EndInput, Backward) => ctx.prevchar == None
    case (WordBoundary, _) => is_boundary(ctx)
    case (NonWordBoundary, _) => !is_boundary(ctx)
  }
}
