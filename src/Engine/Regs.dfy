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

module RegsCommon {
  import opened Std.Wrappers
  // several implementations represent None with -1; all real values are >= 0
  function int_of_opt(o: Option<int>): int {
    match o case None => -1 case Some(x) => x
  }
  function opt_of_int(i: int): Option<int> {
    if i < 0 then None else Some(i)
  }
}

// The REGS signature (OCaml `module type REGS`).
abstract module AbstractRegs {
  import opened Std.Wrappers
  type Regs
  function init_regs(size: int): Regs
  function set_reg(r: Regs, k: int, cp: Option<int>, clk: int): Regs
  function clear_reg(r: Regs, k: int): Regs
  function get_cp(r: Regs, k: int): Option<int>
  function get_clock(r: Regs, k: int): Option<int>
  function copy(r: Regs): Regs
  // OCaml to_arrays: (cp values, clock values), indexed by key, -1 = unset.
  function as_arrays(r: Regs): (seq<int>, seq<int>)
  function name(): string
}

// Array_Regs: two arrays indexed by key. O(1) get/set, O(size) init/copy.
module Array_Regs refines AbstractRegs {
  import opened RegsCommon

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
module List_Regs refines AbstractRegs {
  import opened RegsCommon

  datatype LRegs = LRegs(setlist: seq<(int, int, int)>, size: int)
  type Regs = LRegs

  function init_regs(size: int): Regs { LRegs([], size) }
  function set_reg(r: Regs, k: int, cp: Option<int>, clk: int): Regs {
    LRegs([(k, int_of_opt(cp), clk)] + r.setlist, r.size)
  }
  function clear_reg(r: Regs, k: int): Regs {
    LRegs([(k, -1, -1)] + r.setlist, r.size)
  }
  function get_cp_rec(l: seq<(int, int, int)>, k: int): Option<int>
    decreases |l|
  {
    if |l| == 0 then None
    else if l[0].0 == k then opt_of_int(l[0].1)
    else get_cp_rec(l[1..], k)
  }
  function get_cp(r: Regs, k: int): Option<int> { get_cp_rec(r.setlist, k) }
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
module Map_Regs refines AbstractRegs {
  import opened RegsCommon

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
