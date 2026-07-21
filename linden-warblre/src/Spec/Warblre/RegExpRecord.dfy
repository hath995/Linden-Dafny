// Mirror of Warblre/spec/RegExpRecord.v.
// Dropped Warblre's `unicode: unit` field (carries no information).
/** The regex's flags and shape, as ECMAScript's internal RegExp Record. */
module WarblreRegExpRecord {

  // Coq: Record RegExpRecord.type := make { ignoreCase; multiline; dotAll; unicode; capturingGroupsCount }.
  /** The compiled flags of a regex: `ignoreCase` (`i`), `multiline` (`m`), `dotAll` (`s`),
      and the total number of capturing groups (`capturingGroupsCount`). Threaded through the
      whole semantics (e.g. `Canonicalize` reads `ignoreCase`). */
  datatype RegExpRecord = RER(
    ignoreCase: bool,
    multiline: bool,
    dotAll: bool,
    capturingGroupsCount: nat
  )
}
