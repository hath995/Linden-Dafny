// Port of oracle.ml
// The table storing, for each string position, whether each lookaround matches.
// Modelled as a mutable 2-D boolean array: dim0 = string positions (str_size+1),
// dim1 = lookaround ids.
/** The lookaround oracle: for each string position and lookaround id, whether
    that lookaround matches there. Backed by a mutable `oracle` (`array2<bool>`),
    with a pure `OracleView` used by the functional specification. */
module Oracle {
  /** The mutable table of lookaround results, indexed `[position, lookaround
      id]`: `str_size+1` positions by `look_nb` lookarounds. */
  type oracle = array2<bool>

  // ----- Pure view of the oracle (spec-only; the functional model of the
  // interpreter computes over OracleView instead of the mutable array2) -----
  /** A pure, immutable snapshot of an `oracle`'s contents (see `ViewOf`), used
      by the specification/functional model instead of reasoning directly about
      the mutable array. */
  type OracleView = seq<seq<bool>>

  /** Reads the current contents of oracle `o` into a pure `OracleView`. */
  function ViewOf(o: oracle): OracleView
    reads o
  {
    seq(o.Length0, i requires 0 <= i < o.Length0 reads o =>
      seq(o.Length1, j requires 0 <= j < o.Length1 reads o => o[i, j]))
  }

  /** The all-`false` `OracleView` for a string of length `str_size` and
      `look_nb` lookarounds — the initial oracle state. */
  function init_view(str_size: int, look_nb: int): OracleView
    requires str_size >= 0 && look_nb >= 0
  {
    seq(str_size + 1, i => seq(look_nb, j => false))
  }

  /** Whether lookaround `lid` was recorded as matching at position `cp` in
      view `ov`; out-of-range indices read as `false`. */
  function view_get_oracle(ov: OracleView, cp: int, lid: int): bool {
    if 0 <= cp < |ov| && 0 <= lid < |ov[cp]| then ov[cp][lid] else false
  }

  /** The view obtained from `ov` by recording lookaround `lid` as matching at
      position `cp`; out-of-range indices leave `ov` unchanged. */
  function view_set_oracle(ov: OracleView, cp: int, lid: int): OracleView {
    if 0 <= cp < |ov| && 0 <= lid < |ov[cp]| then ov[cp := ov[cp][lid := true]] else ov
  }

  /** `get_oracle` on the mutable array agrees with `view_get_oracle` on its
      `ViewOf` snapshot. */
  lemma GetOracleView(o: oracle, cp: int, lid: int)
    ensures get_oracle(o, cp, lid) == view_get_oracle(ViewOf(o), cp, lid)
  {}

  /** Allocates a fresh oracle sized for a string of length `str_size` and
      `look_nb` lookarounds, with every entry initialized to `false` (matching
      `init_view`). */
  method create_oracle(str_size: int, look_nb: int) returns (o: oracle)
    requires str_size >= 0
    requires look_nb >= 0
    ensures fresh(o)
    ensures o.Length0 == str_size + 1
    ensures o.Length1 == look_nb
    ensures ViewOf(o) == init_view(str_size, look_nb)
  {
    // explicit all-false init (observationally identical to the previous
    // auto-init; makes the contents available to specifications, matching
    // the OCaml original's Array.make default)
    o := new bool[str_size + 1, look_nb]((i, j) => false);
    var v := ViewOf(o);
    var w := init_view(str_size, look_nb);
    forall i | 0 <= i < |v| ensures v[i] == w[i] {
      assert forall j :: 0 <= j < |v[i]| ==> v[i][j] == w[i][j];
    }
    assert v == w;
  }

  // we only ever set to true; there is no reason to clear an entry.
  // Bounds-guarded write (memory-safe; in practice cp/lid are always in range).
  /** Records that lookaround `lid` matches at position `cp`, mutating `o` in
      place; out-of-range `(cp, lid)` is a no-op. Entries are only ever set to
      `true`, never cleared. */
  method set_oracle(o: oracle, cp: int, lid: int)
    modifies o
    ensures ViewOf(o) == view_set_oracle(old(ViewOf(o)), cp, lid)
  {
    ghost var w := view_set_oracle(ViewOf(o), cp, lid);
    if 0 <= cp < o.Length0 && 0 <= lid < o.Length1 {
      o[cp, lid] := true;
    }
    ghost var v := ViewOf(o);
    forall i | 0 <= i < |v| ensures v[i] == w[i] {
      assert forall j :: 0 <= j < |v[i]| ==> v[i][j] == w[i][j];
    }
    assert v == w;
  }

  // Total read: out-of-range positions read as `false`. Memory-safe by
  // construction; in practice cp/lid are always in range (cp in 0..|str|,
  // lid <= maxlook), so the guard is never the operative branch.
  /** Total read of `o` at `(cp, lid)`: out-of-range indices read as `false`
      rather than being undefined. */
  function get_oracle(o: oracle, cp: int, lid: int): bool
    reads o
  {
    if 0 <= cp < o.Length0 && 0 <= lid < o.Length1 then o[cp, lid] else false
  }
}
