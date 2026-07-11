// Port of anchors.ml
// How to match the different anchors. Anchors need a two-character context:
// the characters just before and just after the current position.
module Anchors {
  import opened Std.Wrappers
  import opened Charclasses
  import opened RegElkRegex

  // algorithms can traverse the string forward or backward; this changes
  // the behaviour of the anchors.
  datatype direction = Forward | Backward

  // surrounding characters of a position (None at the begin/end of input).
  // NOTE: going backward, the index of nextchar is smaller than prevchar's.
  // Modelled immutably (the OCaml record is mutable, updated in place).
  datatype char_context = CharContext(prevchar: Option<char>, nextchar: Option<char>)

  function update_context(ctx: char_context, newchar: Option<char>): char_context {
    CharContext(ctx.nextchar, newchar)
  }

  predicate is_boundary(ctx: char_context) {
    match (ctx.prevchar, ctx.nextchar)
    case (None, None) => false
    case (None, Some(c)) => is_ascii_word_character(c)
    case (Some(c), None) => is_ascii_word_character(c)
    // xor
    case (Some(prev), Some(next)) =>
      is_ascii_word_character(prev) != is_ascii_word_character(next)
  }

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
