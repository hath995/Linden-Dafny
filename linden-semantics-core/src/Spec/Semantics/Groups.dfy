// Mirror of Semantics/Groups.v.
// Capture-group registers: a partial map from group ids to capture ranges.
// The whole Coq FMapList + CanonicalMaps proof-irrelevance apparatus (needed there only to get
// canonical/extensional map equality) is OBVIATED by Dafny's native `map`, which already has
// extensional equality. So `group_map := map<nat, Range>` and the operations are direct.

/** Capture-group state: which groups have captured what, as matching proceeds.

    Modelled directly on Dafny's native `map` (whose structural equality removes
    the need for Coq's canonical-map machinery). A `GroupMap` is threaded through
    the semantics and updated by `Open`/`Close`/`Reset` group actions. */
module Groups {
  import opened Std.Wrappers

  // Coq: group_id := nat (GroupId, an OrderedTypeWithLeibniz over Nat).
  /** A capture group's index (group 1 is `\1`, etc.). */
  type GroupId = nat

  // Coq: group_set := list group_id.
  /** A set of group ids (as a sequence), e.g. the groups reset per iteration. */
  type GroupSet = seq<GroupId>

  // Coq: Inductive groupaction := Open (g) | Close (g) | Reset (gl).
  /** A mutation of the capture state: `Open` a group here, `Close` it here, or
      `Reset` (clear) a set of groups (done at the start of each quantifier iteration). */
  datatype GroupAction = Open(g: GroupId) | Close(g: GroupId) | Reset(gl: GroupSet)

  // Coq: GroupMap.range = Range { startIdx: nat; endIdx: option nat }.
  // start inclusive, end exclusive; a group is "open" iff endIdx is None.
  /** One group's captured span: `startIdx` inclusive, `endIdx` exclusive. The
      group is still *open* (started but not yet closed) exactly when `endIdx` is `None`. */
  datatype Range = Range(startIdx: nat, endIdx: Option<nat>)

  // Coq: GroupMap.t := MapS.t range.
  /** The capture registers: a partial map from group id to its `Range`. */
  type GroupMap = map<GroupId, Range>

  // Coq: GroupMap.empty
  /** The initial capture state: nothing captured. */
  const Empty: GroupMap := map[]

  // Coq: GroupMap.find
  /** Look up group `gid`'s current `Range`, if it has one. */
  function Find(gid: GroupId, gm: GroupMap): Option<Range> {
    if gid in gm then Some(gm[gid]) else None
  }

  // Coq: GroupMap.add
  /** Set group `gid`'s range to `r`. */
  function Add(gid: GroupId, r: Range, gm: GroupMap): GroupMap {
    gm[gid := r]
  }

  // Coq: GroupMap.open currIdx gid := add gid (Range currIdx None).
  /** Begin capturing group `gid` at position `currIdx` (leaves it open). */
  function GMOpen(currIdx: nat, gid: GroupId, gm: GroupMap): GroupMap {
    gm[gid := Range(currIdx, None)]
  }

  // Coq: GroupMap.close currIdx gid gm. Assumes (does not check) gid maps to an open range;
  // swaps endpoints when startIdx > currIdx (for backward lookarounds).
  /** Finish capturing group `gid` at position `currIdx`. If the group was opened
      *after* `currIdx` (a backward lookbehind), the endpoints are swapped so the
      range stays well-formed. Assumes `gid` is currently open. */
  function GMClose(currIdx: nat, gid: GroupId, gm: GroupMap): GroupMap {
    match Find(gid, gm)
    case Some(Range(startIdx, _)) =>
      if startIdx <= currIdx then gm[gid := Range(startIdx, Some(currIdx))]
      else gm[gid := Range(currIdx, Some(startIdx))]
    case None => gm
  }

  // Coq: GroupMap.reset gl gm := fold_left (remove) gl gm. Map minus the set of keys.
  /** Clear every group in `gl` from the capture state (ECMAScript resets a
      quantifier body's captures before each iteration). */
  function GMReset(gl: GroupSet, gm: GroupMap): GroupMap {
    gm - (set g | g in gl)
  }

  // Coq: GroupMap.update op currIdx gm.
  /** Apply one `GroupAction` (`Open`/`Close`/`Reset`) at position `currIdx`. */
  function GMUpdate(op: GroupAction, currIdx: nat, gm: GroupMap): GroupMap {
    match op
    case Open(g) => GMOpen(currIdx, g, gm)
    case Close(g) => GMClose(currIdx, g, gm)
    case Reset(gs) => GMReset(gs, gm)
  }

  // Coq: GroupMap.eqb / EqDec_t — native structural `==` on maps suffices.
}
