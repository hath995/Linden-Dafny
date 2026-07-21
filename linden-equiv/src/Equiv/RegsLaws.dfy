// Phase 4 prelude: algebraic laws of the register backends, needed by the
// clock/GroupMap denotation (GmAt / ThreadTracksGm / FilterResetDenotes).
//
// Stated directly against the concrete backends (no upstream patch needed).
// Array_Regs and Map_Regs satisfy all laws UNCONDITIONALLY (single-cell
// stores; negative stored values normalize to None on read, and as_arrays
// shows the raw cell, so `< 0 <==> None` holds).
//
// CAVEAT (documented finding): List_Regs does NOT satisfy the as_arrays laws
// unconditionally — fill is first-NON-(-1)-wins per slot while get_cp_rec is
// first-ENTRY-wins, so an entry with a -1 field (set_reg with cp == None,
// e.g. SetQuantToClock(qid, false)) can be shadowed in as_arrays by an OLDER
// non-negative entry for the same key. In the star fragment all quant sets
// are cp == None (uniform per key) and all cap/look sets are Some(cp >= 0),
// so the engine never exhibits the divergence; proving the List backend will
// need that uniformity as an engine invariant. Main-theorem work targets
// ArrayInterp first.
include "RegElkImports.dfy"

/** Algebraic laws of the register backends (`Array_Regs`, `Map_Regs`) underlying the
    clock/GroupMap denotation (`GmAt`, `ThreadTracksGm`, `FilterResetDenotes`): init/set/read
    behave uniformly across backends, with negative stored values normalizing to `None`.
    See the file header for the documented `List_Regs` caveat this module does not cover. */
module LindenElkRegsLaws {
  import opened Std.Wrappers
  import AR = Array_Regs
  import MR = Map_Regs

  // normalization shared by all backends: stored ints < 0 read as None
  /** Normalizes a stored register value: `Some(v)` with `v < 0` collapses to `None`,
      matching how every backend encodes "unset" as a negative sentinel. */
  function NormOpt(cp: Option<int>): Option<int> {
    match cp
    case None => None
    case Some(v) => if v >= 0 then Some(v) else None
  }

  // ===========================================================================
  // Array_Regs
  // ===========================================================================

  /** The logical register-file size of an `Array_Regs` value: the shorter of its two
      parallel arrays (checkpoint array and clock array). */
  function ASize(r: AR.Regs): int {
    if |r.a_cp| <= |r.a_clk| then |r.a_cp| else |r.a_clk|
  }

  /** `Array_Regs.init_regs` starts at the given size with every checkpoint and clock
      slot `None`. */
  lemma AInitLaws(n: int)
    ensures ASize(AR.init_regs(n)) == (if n >= 0 then n else 0)
    ensures forall k :: AR.get_cp(AR.init_regs(n), k) == None
    ensures forall k :: AR.get_clock(AR.init_regs(n), k) == None
  {}

  /** `Array_Regs.set_reg` touches only slot `k` — every other slot `k'` is unchanged,
      and slot `k` itself ends up holding the normalized `cp`/`clk` values. */
  lemma ASetLaws(r: AR.Regs, k: int, cp: Option<int>, clk: int)
    ensures ASize(AR.set_reg(r, k, cp, clk)) == ASize(r)
    ensures forall k' :: k' != k ==>
      AR.get_cp(AR.set_reg(r, k, cp, clk), k') == AR.get_cp(r, k')
      && AR.get_clock(AR.set_reg(r, k, cp, clk), k') == AR.get_clock(r, k')
    ensures 0 <= k < ASize(r) ==>
      AR.get_cp(AR.set_reg(r, k, cp, clk), k) == NormOpt(cp)
      && AR.get_clock(AR.set_reg(r, k, cp, clk), k) == (if clk >= 0 then Some(clk) else None)
  {}

  /** `Array_Regs.as_arrays` exposes exactly the backend's logical `get_cp`/`get_clock`
      contents, `None` encoded as a negative sentinel — the bridge the `GmAt` denotation
      relies on to read register state as plain arrays. */
  lemma AAsArraysLaws(r: AR.Regs)
    requires |r.a_cp| == |r.a_clk|   // maintained by init_regs/set_reg/clear_reg
    ensures var (cps, clks) := AR.as_arrays(r);
      |cps| == ASize(r) && |clks| == ASize(r)
      && (forall k :: 0 <= k < ASize(r) ==>
            (cps[k] < 0 <==> AR.get_cp(r, k) == None)
            && (cps[k] >= 0 ==> AR.get_cp(r, k) == Some(cps[k]))
            && (clks[k] < 0 <==> AR.get_clock(r, k) == None)
            && (clks[k] >= 0 ==> AR.get_clock(r, k) == Some(clks[k])))
  {}

  // ===========================================================================
  // Map_Regs
  // ===========================================================================

  /** The logical register-file size of a `Map_Regs` value: its `size` field, clamped to
      be non-negative. */
  function MSize(r: MR.Regs): int {
    if r.size >= 0 then r.size else 0
  }

  /** `Map_Regs.init_regs` starts at the given size with every checkpoint and clock slot
      `None` — the `Map_Regs` analogue of `AInitLaws`. */
  lemma MInitLaws(n: int)
    ensures MSize(MR.init_regs(n)) == (if n >= 0 then n else 0)
    ensures forall k :: MR.get_cp(MR.init_regs(n), k) == None
    ensures forall k :: MR.get_clock(MR.init_regs(n), k) == None
  {}

  /** `Map_Regs.set_reg` touches only slot `k` — every other slot `k'` is unchanged, and
      slot `k` ends up holding the normalized `cp`/`clk` values — the `Map_Regs` analogue
      of `ASetLaws`. */
  lemma MSetLaws(r: MR.Regs, k: int, cp: Option<int>, clk: int)
    ensures MSize(MR.set_reg(r, k, cp, clk)) == MSize(r)
    ensures forall k' :: k' != k ==>
      MR.get_cp(MR.set_reg(r, k, cp, clk), k') == MR.get_cp(r, k')
      && MR.get_clock(MR.set_reg(r, k, cp, clk), k') == MR.get_clock(r, k')
    ensures MR.get_cp(MR.set_reg(r, k, cp, clk), k) == NormOpt(cp)
    ensures MR.get_clock(MR.set_reg(r, k, cp, clk), k) == (if clk >= 0 then Some(clk) else None)
  {}

  /** `Map_Regs.as_arrays` exposes exactly the backend's logical `get_cp`/`get_clock`
      contents via a negative sentinel for `None` — the `Map_Regs` analogue of
      `AAsArraysLaws`. */
  lemma MAsArraysLaws(r: MR.Regs)
    ensures var (cps, clks) := MR.as_arrays(r);
      |cps| == MSize(r) && |clks| == MSize(r)
      && (forall k :: 0 <= k < MSize(r) ==>
            (cps[k] < 0 <==> MR.get_cp(r, k) == None)
            && (cps[k] >= 0 ==> MR.get_cp(r, k) == Some(cps[k]))
            && (clks[k] < 0 <==> MR.get_clock(r, k) == None)
            && (clks[k] >= 0 ==> MR.get_clock(r, k) == Some(clks[k])))
  {}
}
