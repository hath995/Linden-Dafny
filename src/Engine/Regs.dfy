// Port of regs.ml
// Thread register implementations: hold a (cp, clock) pair for each capture
// group / lookaround / quantifier key. Three implementations give the
// time/space tradeoffs of the paper's Section 4.6.
//
// The OCaml code mutates registers in place but copies at every Fork before
// threads diverge, so the observable behaviour is a functional snapshot. We
// therefore model Regs as immutable values: `copy` is the identity and there is
// no aliasing to reason about. The three distinct data structures (array,
// assoc-list, balanced map) are preserved.

/** Shared helpers for the `Regs` implementations: encoding an `Option<int>`
    register value as a plain `int`, using `-1` for `None` (real cp/clock
    values are always non-negative). */
module RegsCommon {
  import opened Std.Wrappers
  // several implementations represent None with -1; all real values are >= 0
  /** Encodes an optional register value as an `int`, using `-1` for `None`. */
  function int_of_opt(o: Option<int>): int {
    match o case None => -1 case Some(x) => x
  }
  /** Decodes an `int` produced by `int_of_opt` back into an `Option<int>`;
      negative values decode to `None`. */
  function opt_of_int(i: int): Option<int> {
    if i < 0 then None else Some(i)
  }
}

// The REGS signature (OCaml `module type REGS`).
/** The `Regs` interface (OCaml's `REGS` module type): an immutable,
    associative store mapping a register key (capture group / lookaround /
    quantifier id) to a `(current position, clock)` pair. `Array_Regs`,
    `List_Regs`, and `Map_Regs` are the three concrete implementations, giving
    the time/space tradeoffs discussed in the paper's Section 4.6. */
abstract module AbstractRegs {
  import opened Std.Wrappers
  /** The abstract type of a register store; concretized by each implementing
      module. */
  type Regs
  /** An empty register store sized for `size` keys, all initially unset. */
  function init_regs(size: int): Regs
  /** The store obtained from `r` by recording `(cp, clk)` at key `k`. */
  function set_reg(r: Regs, k: int, cp: Option<int>, clk: int): Regs
  /** The store obtained from `r` by unsetting key `k`. */
  function clear_reg(r: Regs, k: int): Regs
  /** The current-position value stored at key `k`, or `None` if unset. */
  function get_cp(r: Regs, k: int): Option<int>
  /** The clock value stored at key `k`, or `None` if unset. */
  function get_clock(r: Regs, k: int): Option<int>
  /** A snapshot of `r` safe to evolve independently — the identity here,
      since `Regs` is modelled as an immutable value (the OCaml original
      mutates in place but copies at every `Fork`). */
  function copy(r: Regs): Regs
  // OCaml to_arrays: (cp values, clock values), indexed by key, -1 = unset.
  /** Exports `r` as a pair of plain arrays (cp values, clock values) indexed
      by key, using `-1` for unset entries. */
  function as_arrays(r: Regs): (seq<int>, seq<int>)
  /** A human-readable name for this `Regs` implementation. */
  function name(): string
}

// Array_Regs: two arrays indexed by key. O(1) get/set, O(size) init/copy.
/** The array-backed `Regs`: two same-length arrays indexed directly by key.
    O(1) `get`/`set`, O(size) `init`/`copy`. */
module Array_Regs refines AbstractRegs {
  import opened RegsCommon

  /** The array-backed register store: parallel `a_cp`/`a_clk` arrays indexed
      by key, `-1` meaning unset. */
  datatype ARegs = ARegs(a_cp: seq<int>, a_clk: seq<int>)
  type Regs = ARegs

  function init_regs(size: int): Regs {
    var n := if size >= 0 then size else 0;
    ARegs(seq(n, i => -1), seq(n, i => -1))
  }
  function set_reg(r: Regs, k: int, cp: Option<int>, clk: int): Regs {
    if 0 <= k < |r.a_cp| && 0 <= k < |r.a_clk|
    then ARegs(r.a_cp[k := int_of_opt(cp)], r.a_clk[k := clk])
    else r
  }
  function clear_reg(r: Regs, k: int): Regs {
    if 0 <= k < |r.a_cp| && 0 <= k < |r.a_clk|
    then ARegs(r.a_cp[k := -1], r.a_clk[k := -1])
    else r
  }
  function get_cp(r: Regs, k: int): Option<int> {
    if 0 <= k < |r.a_cp| then opt_of_int(r.a_cp[k]) else None
  }
  function get_clock(r: Regs, k: int): Option<int> {
    if 0 <= k < |r.a_clk| then opt_of_int(r.a_clk[k]) else None
  }
  function copy(r: Regs): Regs { r }
  function as_arrays(r: Regs): (seq<int>, seq<int>) { (r.a_cp, r.a_clk) }
  function name(): string { "ArrayRegs" }
}

// List_Regs: an assoc-list (most-recent-first). O(1) set, O(n) get.
/** The assoc-list-backed `Regs`: writes prepend to a list (most-recent-first).
    O(1) `set`, O(n) `get`. */
module List_Regs refines AbstractRegs {
  import opened RegsCommon

  /** The assoc-list-backed register store: a most-recent-first list of
      `(key, cp, clock)` triples, plus the declared `size`. */
  datatype LRegs = LRegs(setlist: seq<(int, int, int)>, size: int)
  type Regs = LRegs

  function init_regs(size: int): Regs { LRegs([], size) }
  function set_reg(r: Regs, k: int, cp: Option<int>, clk: int): Regs {
    LRegs([(k, int_of_opt(cp), clk)] + r.setlist, r.size)
  }
  function clear_reg(r: Regs, k: int): Regs {
    LRegs([(k, -1, -1)] + r.setlist, r.size)
  }
  /** Scans `l` most-recent-first for the first entry at key `k`, returning
      its recorded cp value (or `None` if `k` never occurs). */
  function get_cp_rec(l: seq<(int, int, int)>, k: int): Option<int>
    decreases |l|
  {
    if |l| == 0 then None
    else if l[0].0 == k then opt_of_int(l[0].1)
    else get_cp_rec(l[1..], k)
  }
  function get_cp(r: Regs, k: int): Option<int> { get_cp_rec(r.setlist, k) }
  /** Scans `l` most-recent-first for the first entry at key `k`, returning
      its recorded clock value (or `None` if `k` never occurs). */
  function get_clock_rec(l: seq<(int, int, int)>, k: int): Option<int>
    decreases |l|
  {
    if |l| == 0 then None
    else if l[0].0 == k then opt_of_int(l[0].2)
    else get_clock_rec(l[1..], k)
  }
  function get_clock(r: Regs, k: int): Option<int> { get_clock_rec(r.setlist, k) }
  function copy(r: Regs): Regs { r }

  // faithful replication of the OCaml fill_array: scanning most-recent-first,
  // only write a slot that is still unset (-1).
  /** Faithful port of OCaml's `fill_array`: scans `l` most-recent-first,
      writing each key's `(cp, clock)` into `acp`/`aclk` only the first time
      that key is seen (later, i.e. older, writes to an already-set slot are
      ignored). */
  function fill(l: seq<(int, int, int)>, acp: seq<int>, aclk: seq<int>): (seq<int>, seq<int>)
    decreases |l|
  {
    if |l| == 0 then (acp, aclk)
    else
      var k := l[0].0; var cp := l[0].1; var clk := l[0].2;
      var acp' := if 0 <= k < |acp| && acp[k] == -1 then acp[k := cp] else acp;
      var aclk' := if 0 <= k < |aclk| && aclk[k] == -1 then aclk[k := clk] else aclk;
      fill(l[1..], acp', aclk')
  }
  function as_arrays(r: Regs): (seq<int>, seq<int>) {
    var n := if r.size >= 0 then r.size else 0;
    fill(r.setlist, seq(n, i => -1), seq(n, i => -1))
  }
  function name(): string { "ListRegs" }
}

// Map_Regs: a balanced map (the paper's "Balanced Tree"). O(log n) ops.
/** The balanced-map-backed `Regs` (the paper's "Balanced Tree" implementation).
    O(log n) operations. */
module Map_Regs refines AbstractRegs {
  import opened RegsCommon

  /** The map-backed register store: a `map` from key to `(cp, clock)`, plus
      the declared `size`. */
  datatype MRegs = MRegs(valmap: map<int, (int, int)>, size: int)
  type Regs = MRegs

  function init_regs(size: int): Regs { MRegs(map[], size) }
  function set_reg(r: Regs, k: int, cp: Option<int>, clk: int): Regs {
    MRegs(r.valmap[k := (int_of_opt(cp), clk)], r.size)
  }
  function clear_reg(r: Regs, k: int): Regs {
    MRegs(r.valmap - {k}, r.size)
  }
  function get_cp(r: Regs, k: int): Option<int> {
    if k in r.valmap then opt_of_int(r.valmap[k].0) else None
  }
  function get_clock(r: Regs, k: int): Option<int> {
    if k in r.valmap then opt_of_int(r.valmap[k].1) else None
  }
  function copy(r: Regs): Regs { r }
  function as_arrays(r: Regs): (seq<int>, seq<int>) {
    var n := if r.size >= 0 then r.size else 0;
    (seq(n, k => if k in r.valmap then r.valmap[k].0 else -1),
     seq(n, k => if k in r.valmap then r.valmap[k].1 else -1))
  }
  function name(): string { "MapRegs" }
}
