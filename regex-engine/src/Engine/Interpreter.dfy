// Port of interpreter.ml
// A VM-based interpreter of the bytecode that handles thread priority,
// with all the paper's extensions (oracle building, CDN tables, nullable +
// reconstruction, capture reset filtering).
//
// Parameterized over the register implementation (OCaml functor `Interpreter(Regs)`).
// The mutable OCaml `thread` / pcset records are modelled as immutable values
// (Thread datatype, seq<bool> pcsets), so the only mutable heap state is the
// IState object and the oracle. Termination IS proven (no `decreases *`):
//  - advance_epsilon (epsilon closure): measure = (number of unprocessed
//    (pc,exit_allowed) slots, |active|) — each step marks a fresh slot or drops
//    a thread; see `unprocessed` / `count_false_set`.
//  - find_match (string walk): measure = |str|-cp (forward) / cp (backward),
//    guarded by the invariant `context.nextchar == get_char(str, cp[-1])`.
//  - consume: |blocked|; nulled_plus/children: structural on the AST.
/** The Thompson-style bytecode interpreter (the paper's RegElk engine): runs
    threads over `Bytecode` in lockstep by string position, tracking capture/
    lookaround/quantifier registers via the `AbstractRegs` backend `R`,
    building the lookaround `Oracle` and `Cdn` tables, and reconstructing
    captures lost to nulled `+` iterations. Instantiated once per `Regs`
    backend below (`ArrayInterp`, `ListInterp`, `MapInterp`). Every imperative
    method here has a pure functional counterpart (prefixed `F`) it is proved
    equal to, so all correctness reasoning happens over the pure values. */
abstract module Interpreter {
  import opened Std.Wrappers
  import opened Charclasses
  import opened RegElkRegex
  import opened Bytecode
  import opened Oracle
  import opened Cdn
  import opened Anchors
  import opened Compiler
  import R : AbstractRegs

  // * Direction helpers
  /** Which direction to scan the string when building lookaround `l`'s oracle
      entries: `Backward` for lookaheads, `Forward` for lookbehinds. */
  function oracle_direction(l: lookaround): direction {
    match l
    case Lookahead => Backward
    case NegLookahead => Backward
    case Lookbehind => Forward
    case NegLookbehind => Forward
  }
  // OCaml failwiths on negative lookarounds; only called when capture_type holds.
  /** Which direction to scan when reconstructing lookaround `l`'s capture
      groups: `Forward` for lookaheads, `Backward` for lookbehinds. Only
      meaningful for positive lookarounds (guarded by `capture_type`). */
  function capture_direction(l: lookaround): direction {
    match l
    case Lookahead => Forward
    case Lookbehind => Backward
    case _ => Forward
  }
  /** Whether lookaround `l` is positive (`Lookahead`/`Lookbehind`) and so has
      capture groups worth reconstructing. */
  function capture_type(l: lookaround): bool {
    match l
    case Lookahead => true
    case Lookbehind => true
    case _ => false
  }
  /** Moves position `cp` one step in direction `dir` (`+1` forward, `-1`
      backward). */
  function incr_cp(cp: int, dir: direction): int {
    match dir case Forward => cp + 1 case Backward => cp - 1
  }
  /** The starting position for a scan of direction `dir` over a string of
      length `str_size`: `0` forward, `str_size` backward. */
  function init_cp(dir: direction, str_size: int): int {
    match dir case Forward => 0 case Backward => str_size
  }
  /** The offset back to the character just consumed when advancing in
      direction `dir` (0 forward, 1 backward); used to read the right
      character into the context window after moving `cp`. */
  function cp_offset(dir: direction): int {
    match dir case Forward => 0 case Backward => 1
  }

  // * String access
  /** Total read of the character at position `cp` in `str`: `None` if out of
      range. */
  function get_char(str: string, cp: int): Option<char> {
    if 0 <= cp < |str| then Some(str[cp]) else None
  }

  // * Threads (immutable)
  /** An immutable snapshot of one VM thread: its program counter `pc`, its
      three register banks (`capture_regs`, `look_regs`, `quant_regs`), and
      `exit_allowed` (whether it may currently leave a quantifier loop without
      consuming). The mutable OCaml thread record becomes this immutable
      value, copied at every `Fork`. */
  datatype Thread = Thread(pc: int, capture_regs: R.Regs, look_regs: R.Regs,
                           quant_regs: R.Regs, exit_allowed: bool)

  /** The initial thread: `pc` 0, the given register banks, `exit_allowed =
      false`. */
  function init_thread(initcap: R.Regs, initlook: R.Regs, initquant: R.Regs): Thread {
    Thread(0, initcap, initlook, initquant, false)
  }

  // * PC Sets (immutable seq<bool>)
  /** A set of instruction labels represented as a bitmap, one entry per
      label. */
  type pcset = seq<bool>
  /** The empty `pcset` for a code of size `n` — every label absent. */
  function init_pcset(n: int): pcset { if n >= 0 then seq(n, i => false) else [] }
  /** Marks label `pc` present in `pcs` (a no-op if `pc` is out of range). */
  function pc_add(pcs: pcset, pc: Label): pcset {
    if 0 <= pc < |pcs| then pcs[pc := true] else pcs
  }
  /** Whether label `pc` is marked present in `pcs`. */
  function pc_mem(pcs: pcset, pc: Label): bool {
    0 <= pc < |pcs| && pcs[pc]
  }

  // adds (thread, char) at the head of blocked only if its pc isn't already in.
  /** Prepends `(t, x)` to the `blocked` list `current`, unless a thread
      already occupies `t.pc` in `inset` — per label, only the
      highest-priority thread survives to the consume phase. */
  function add_thread(t: Thread, x: char_expectation,
                      current: seq<(Thread, char_expectation)>, inset: pcset)
    : (seq<(Thread, char_expectation)>, pcset)
  {
    if pc_mem(inset, t.pc) then (current, inset)
    else ([(t, x)] + current, pc_add(inset, t.pc))
  }

  // * Boolean PC Sets (per exit_allowed value)
  /** Two `pcset`s, one per value of `exit_allowed`, tracking which `(pc,
      exit_allowed)` pairs have already been processed during one
      epsilon-closure pass (see `advance_epsilon`). */
  datatype Bpcset = Bpcset(true_set: pcset, false_set: pcset)
  /** The empty `Bpcset` for a code of size `n`. */
  function init_bpcset(n: int): Bpcset { Bpcset(init_pcset(n), init_pcset(n)) }
  /** Marks `(pc, exit_bool)` as processed in `b`. */
  function bpc_add(b: Bpcset, pc: Label, exit_bool: bool): Bpcset {
    if exit_bool then Bpcset(pc_add(b.true_set, pc), b.false_set)
    else Bpcset(b.true_set, pc_add(b.false_set, pc))
  }
  /** Whether `(pc, exit_bool)` has already been processed in `b`. */
  function bpc_mem(b: Bpcset, pc: Label, exit_bool: bool): bool {
    if exit_bool then pc_mem(b.true_set, pc) else pc_mem(b.false_set, pc)
  }

  // * Termination measure for advance_epsilon.
  // The epsilon-closure terminates because each (pc, exit_allowed) pair is
  // processed at most once: once added to `processed` it is never re-handled.
  // The measure is the number of still-unprocessed slots, lexicographically
  // paired with |active| (which strictly shrinks whenever a thread is dropped
  // without marking a fresh slot).
  /** How many entries of `s` are still `false` (unmarked); part of the
      termination measure for `advance_epsilon`'s epsilon closure. */
  function count_false(s: seq<bool>): nat
    decreases |s|
  {
    if |s| == 0 then 0 else (if s[0] then 0 else 1) + count_false(s[1..])
  }
  /** The number of `(pc, exit_allowed)` pairs not yet processed in `b`; the
      primary component of `advance_epsilon`'s termination measure. */
  function unprocessed(b: Bpcset): nat {
    count_false(b.true_set) + count_false(b.false_set)
  }

  // Flipping a slot to `true` never increases the false-count, and strictly
  // decreases it when that slot was previously `false`.
  /** Marking one slot of `s` as `true` never increases `count_false`, and
      strictly decreases it if that slot was previously `false` — the key
      fact making `advance_epsilon`'s epsilon closure terminate. */
  lemma count_false_set(s: seq<bool>, pc: int)
    requires 0 <= pc < |s|
    ensures count_false(s[pc := true]) <= count_false(s)
    ensures !s[pc] ==> count_false(s[pc := true]) == count_false(s) - 1
    decreases |s|
  {
    if pc == 0 {
      assert (s[pc := true])[1..] == s[1..];
    } else {
      assert (s[pc := true])[1..] == s[1..][pc - 1 := true];
      count_false_set(s[1..], pc - 1);
    }
  }

  // * Interpreter state (mutable)
  /** The interpreter's mutable per-scan state: the current position `cp`,
      the `active`/`blocked` thread queues, which `(pc, exit_allowed)` pairs
      and labels have been `processed`/marked `isblocked` this step, the best
      match found so far, the anchor `context`, a logical `clock`, and the
      current `cdn` table. Mirrored by the pure `VmState`/`StateOf`. */
  class IState {
    var cp: int
    var active: seq<Thread>                          // high-to-low priority
    var processed: Bpcset
    var blocked: seq<(Thread, char_expectation)>     // low-to-high priority
    var isblocked: pcset
    var bestmatch: Option<Thread>
    var context: char_context
    var clock: int
    var cdn: cdn_table

    /** Builds an `IState` directly from its already-computed fields. */
    constructor(cp_: int, active_: seq<Thread>, processed_: Bpcset,
                blocked_: seq<(Thread, char_expectation)>, isblocked_: pcset,
                bestmatch_: Option<Thread>, context_: char_context, clock_: int, cdn_: cdn_table)
      ensures cp == cp_ && active == active_ && processed == processed_ && blocked == blocked_
      ensures isblocked == isblocked_ && bestmatch == bestmatch_ && context == context_
      ensures clock == clock_ && cdn == cdn_
    {
      cp := cp_; active := active_; processed := processed_; blocked := blocked_;
      isblocked := isblocked_; bestmatch := bestmatch_; context := context_;
      clock := clock_; cdn := cdn_;
    }
  }

  /** The `char_context` (surrounding characters) at position `cp` in `str`
      when scanning in direction `dir`. */
  function cp_context(cp: int, str: string, dir: direction): char_context {
    var nextop := get_char(str, cp);
    var prevop := get_char(str, cp - 1);
    match dir
    case Forward => CharContext(prevop, nextop)
    case Backward => CharContext(nextop, prevop)
  }

  // ===========================================================================
  // Functional model (spec-only): pure mirrors of every interpreter method.
  // The imperative methods carry `ensures` tying them to these functions, so
  // all reasoning about the engine can be done over pure values. The oracle is
  // mirrored by OracleView (Oracle.dfy), the CDN build by build_cdn_v (Cdn.dfy),
  // and the compiled tables by FCompiled/CrView (Compiler.dfy).
  // ===========================================================================

  /** Pure, immutable mirror of `IState`, used by the functional model
      (`F`-prefixed functions) that every imperative method here is proved to
      match. */
  datatype VmState = VmSt(cp: int, active: seq<Thread>, processed: Bpcset,
                          blocked: seq<(Thread, char_expectation)>, isblocked: pcset,
                          bestmatch: Option<Thread>, context: char_context,
                          clock: int, cdn: cdn_table)

  /** Reads the current contents of `IState` `s` into a pure `VmState`
      snapshot. */
  function StateOf(s: IState): VmState
    reads s
  {
    VmSt(s.cp, s.active, s.processed, s.blocked, s.isblocked, s.bestmatch,
         s.context, s.clock, s.cdn)
  }

  /** Pure counterpart of `init_state`: the initial `VmState` for running code
      `c` from position `initcp` with the given registers/clock/context. */
  function FInitState(c: code, initcp: int, initcap: R.Regs, initlook: R.Regs,
                      initquant: R.Regs, initclk: int, initctx: char_context): VmState
  {
    VmSt(initcp, [init_thread(initcap, initlook, initquant)], init_bpcset(size(c)),
         [], init_pcset(size(c)), None, initctx, initclk, init_cdn())
  }

  /** `bpc_add` never increases `unprocessed`, and strictly decreases it when
      adding a genuinely new, in-range `(pc, eb)` pair. */
  lemma UnprocessedAdd(b: Bpcset, pc: Label, eb: bool)
    ensures unprocessed(bpc_add(b, pc, eb)) <= unprocessed(b)
    ensures !bpc_mem(b, pc, eb) && (eb ==> 0 <= pc < |b.true_set|) && (!eb ==> 0 <= pc < |b.false_set|)
            ==> unprocessed(bpc_add(b, pc, eb)) < unprocessed(b)
  {
    if eb {
      if 0 <= pc < |b.true_set| { count_false_set(b.true_set, pc); }
    } else {
      if 0 <= pc < |b.false_set| { count_false_set(b.false_set, pc); }
    }
  }

  /** Pure counterpart of `advance_epsilon`: repeatedly steps the
      highest-priority `active` thread along epsilon transitions (jumps,
      forks, register writes, oracle/anchor/CDN checks) until every thread
      has either blocked on a `Consume`, been dropped, or reached `Accept`. */
  function FAdvanceEpsilon(c: code, s: VmState, ov: OracleView, dir: direction): (VmState, OracleView)
    requires |s.processed.true_set| == size(c) && |s.processed.false_set| == size(c)
    ensures var (s', ov') := FAdvanceEpsilon(c, s, ov, dir);
      s'.cp == s.cp && s'.context == s.context
      && |s'.processed.true_set| == size(c) && |s'.processed.false_set| == size(c)
    decreases unprocessed(s.processed), |s.active|
  {
    if |s.active| == 0 then (s, ov)
    else
      var t := s.active[0];
      var ac := s.active[1..];
      var i := get_instr(c, t.pc);
      if bpc_mem(s.processed, t.pc, t.exit_allowed) then
        FAdvanceEpsilon(c, s.(active := ac), ov, dir)
      else
        var b0 := s.processed;
        var s1 := s.(clock := s.clock + 1, processed := bpc_add(b0, t.pc, t.exit_allowed));
        assert unprocessed(s1.processed) <= unprocessed(b0)
            && (0 <= t.pc < size(c) ==> unprocessed(s1.processed) < unprocessed(b0))
          by { UnprocessedAdd(b0, t.pc, t.exit_allowed); }
        match i
        case Consume(ce) =>
          var (nb, ni) := add_thread(t, ce, s1.blocked, s1.isblocked);
          FAdvanceEpsilon(c, s1.(blocked := nb, isblocked := ni, active := ac), ov, dir)
        case Accept =>
          (s1.(active := [], bestmatch := Some(t)), ov)
        case Jmp(x) =>
          FAdvanceEpsilon(c, s1.(active := [t.(pc := x)] + ac), ov, dir)
        case Fork(x, y) =>
          var newt := Thread(x, t.capture_regs, t.look_regs, t.quant_regs, t.exit_allowed);
          FAdvanceEpsilon(c, s1.(active := [newt, t.(pc := y)] + ac), ov, dir)
        case SetRegisterToCP(reg) =>
          var t' := t.(capture_regs := R.set_reg(t.capture_regs, reg, Some(s1.cp), s1.clock), pc := t.pc + 1);
          FAdvanceEpsilon(c, s1.(active := [t'] + ac), ov, dir)
        case SetQuantToClock(q, b) =>
          var ocp := if b then Some(s1.cp) else None;
          var t' := t.(quant_regs := R.set_reg(t.quant_regs, q, ocp, s1.clock), pc := t.pc + 1);
          FAdvanceEpsilon(c, s1.(active := [t'] + ac), ov, dir)
        case CheckOracle(l) =>
          if view_get_oracle(ov, s1.cp, l) then
            var t' := t.(pc := t.pc + 1, look_regs := R.set_reg(t.look_regs, l, Some(s1.cp), s1.clock));
            FAdvanceEpsilon(c, s1.(active := [t'] + ac), ov, dir)
          else
            FAdvanceEpsilon(c, s1.(active := ac), ov, dir)
        case NegCheckOracle(l) =>
          if view_get_oracle(ov, s1.cp, l) then
            FAdvanceEpsilon(c, s1.(active := ac), ov, dir)
          else
            FAdvanceEpsilon(c, s1.(active := [t.(pc := t.pc + 1)] + ac), ov, dir)
        case WriteOracle(l) =>
          FAdvanceEpsilon(c, s1.(active := ac), view_set_oracle(ov, s1.cp, l), dir)
        case BeginLoop =>
          FAdvanceEpsilon(c, s1.(active := [t.(exit_allowed := false, pc := t.pc + 1)] + ac), ov, dir)
        case EndLoop =>
          if t.exit_allowed then
            FAdvanceEpsilon(c, s1.(active := [t.(pc := t.pc + 1)] + ac), ov, dir)
          else
            FAdvanceEpsilon(c, s1.(active := ac), ov, dir)
        case CheckNullable(qid) =>
          if cdn_get(s1.cdn, qid) then
            FAdvanceEpsilon(c, s1.(active := [t.(pc := t.pc + 1)] + ac), ov, dir)
          else
            FAdvanceEpsilon(c, s1.(active := ac), ov, dir)
        case AnchorAssertion(a) =>
          if is_satisfied(a, s1.context, dir) then
            FAdvanceEpsilon(c, s1.(active := [t.(pc := t.pc + 1)] + ac), ov, dir)
          else
            FAdvanceEpsilon(c, s1.(active := ac), ov, dir)
        case Fail =>
          FAdvanceEpsilon(c, s1.(active := ac), ov, dir)
  }

  /** Pure counterpart of `consume`: feeds the next input character to every
      `blocked` thread, in priority order, reactivating (with `exit_allowed`
      set) those whose expectation it satisfies and dropping the rest. */
  function FConsume(s: VmState): VmState
    ensures var r := FConsume(s);
      r.cp == s.cp && r.context == s.context && r.processed == s.processed
      && r.clock == s.clock && r.cdn == s.cdn && r.bestmatch == s.bestmatch
    decreases |s.blocked|
  {
    if |s.blocked| == 0 then s
    else
      var t := s.blocked[0].0;
      var ce := s.blocked[0].1;
      var s1 := s.(blocked := s.blocked[1..]);
      var s2 := if is_accepted(s1.context.nextchar, ce)
                then s1.(active := [t.(exit_allowed := true, pc := t.pc + 1)] + s1.active)
                else s1;
      FConsume(s2)
  }

  /** Pure counterpart of `null_interp`: runs the epsilon closure alone (no
      character consumption) — used to find a nullable match when
      reconstructing a `+` quantifier's last, empty iteration. */
  function FNullInterp(c: code, s: VmState, ov: OracleView, dir: direction)
    : (Option<Thread>, VmState, OracleView)
    requires |s.processed.true_set| == size(c) && |s.processed.false_set| == size(c)
  {
    var (s', ov') := FAdvanceEpsilon(c, s, ov, dir);
    (s'.bestmatch, s', ov')
  }

  /** Pure counterpart of `find_match`: the main string-walking loop — build
      the CDN table, run the epsilon closure, then consume a character and
      repeat, until no threads remain or the string end is reached, returning
      the highest-priority accepting thread if any. */
  function FFindMatch(c: code, str: string, s: VmState, ov: OracleView, dir: direction, cdn: cdns)
    : (Option<Thread>, OracleView)
    requires |s.processed.true_set| == size(c) && |s.processed.false_set| == size(c)
    requires dir.Forward? ==> s.context.nextchar == get_char(str, s.cp)
    requires dir.Backward? ==> s.context.nextchar == get_char(str, s.cp - 1)
    decreases if dir.Forward? then |str| - s.cp else s.cp
  {
    var s0 := s.(cdn := build_cdn_v(cdn, s.cp, ov, s.context, dir));
    var (s1, ov1) := FAdvanceEpsilon(c, s0, ov, dir);
    if |s1.blocked| == 0 then (s1.bestmatch, ov1)
    else
      match s1.context.nextchar
      case None => (s1.bestmatch, ov1)
      case Some(_) =>
        var s2 := FConsume(s1);
        var s3 := s2.(processed := init_bpcset(size(c)), isblocked := init_pcset(size(c)),
                      cdn := init_cdn(), cp := incr_cp(s2.cp, dir));
        var newchar := get_char(str, s3.cp - cp_offset(dir));
        var s4 := s3.(context := update_context(s3.context, newchar));
        FFindMatch(c, str, s4, ov1, dir, cdn)
  }

  /** Total, bounds-guarded read of the `i`th code-table entry in `s`
      (out-of-range `i` reads as `[]`); the sequence-based counterpart of
      `get_code`. */
  function get_code_v(s: seq<code>, i: int): code {
    if 0 <= i < |s| then s[i] else []
  }

  /** Pure counterpart of `nulled_plus`: walks `reg`'s AST and, for every
      quantifier whose registers show it started an iteration
      (`R.get_cp(qt, qid)` is set), replays that iteration's bytecode with the
      null interpreter to reconstruct the captures a possibly-empty match
      would have set. */
  function FNulledPlus(reg: regex, cap: R.Regs, lk: R.Regs, qt: R.Regs,
                       plus_bcv: seq<code>, str: string, ov: OracleView, dir: direction)
    : (R.Regs, R.Regs, R.Regs, OracleView)
    decreases reg, 1
  {
    match reg
    case Re_empty => (cap, lk, qt, ov)
    case Re_character(_) => (cap, lk, qt, ov)
    case Re_anchor(_) => (cap, lk, qt, ov)
    case Re_lookaround(_, _, _) => (cap, lk, qt, ov)
    case Re_capture(_, r1) => FNulledPlus(r1, cap, lk, qt, plus_bcv, str, ov, dir)
    case Re_alt(r1, r2) =>
      var (c1, l1, q1, ov1) := FNulledPlus(r1, cap, lk, qt, plus_bcv, str, ov, dir);
      FNulledPlus(r2, c1, l1, q1, plus_bcv, str, ov1, dir)
    case Re_con(r1, r2) =>
      var (c1, l1, q1, ov1) := FNulledPlus(r1, cap, lk, qt, plus_bcv, str, ov, dir);
      FNulledPlus(r2, c1, l1, q1, plus_bcv, str, ov1, dir)
    case Re_quant(nul, qid, quanttype, body) =>
      match R.get_cp(qt, qid)
      case None => FNulledPlus(body, cap, lk, qt, plus_bcv, str, ov, dir)
      case Some(start_cp) =>
        var start_clock := opt_int(R.get_clock(qt, qid));
        var bytecode := get_code_v(plus_bcv, qid);
        var ctx := cp_context(start_cp, str, dir);
        var inits0 := FInitState(bytecode, start_cp, cap, lk, qt, start_clock, ctx);
        var subcdn := compile_cdns(body);
        var subtable := build_cdn_v(subcdn, start_cp, ov, ctx, dir);
        var inits := inits0.(cdn := subtable);
        var (result, _, ov1) := FNullInterp(bytecode, inits, ov, dir);
        var (ncap, nlk, nqt) := match result
                                case None => (cap, lk, qt)
                                case Some(w) => (w.capture_regs, w.look_regs, w.quant_regs);
        FNulledChildren(body, subtable, start_cp, ncap, nlk, nqt, plus_bcv, str, ov1, dir)
  }

  /** Pure counterpart of `nulled_children`: like `FNulledPlus`, but restricted
      to quantifiers nested inside a parent `+` that started at the same
      position `cp`, sharing the parent's already-computed CDN table
      `cdnt`. */
  function FNulledChildren(reg: regex, cdnt: cdn_table, cp: int, cap: R.Regs, lk: R.Regs, qt: R.Regs,
                           plus_bcv: seq<code>, str: string, ov: OracleView, dir: direction)
    : (R.Regs, R.Regs, R.Regs, OracleView)
    decreases reg, 0
  {
    match reg
    case Re_empty => (cap, lk, qt, ov)
    case Re_character(_) => (cap, lk, qt, ov)
    case Re_anchor(_) => (cap, lk, qt, ov)
    case Re_lookaround(_, _, _) => (cap, lk, qt, ov)
    case Re_capture(_, r1) => FNulledChildren(r1, cdnt, cp, cap, lk, qt, plus_bcv, str, ov, dir)
    case Re_alt(r1, r2) =>
      var (c1, l1, q1, ov1) := FNulledChildren(r1, cdnt, cp, cap, lk, qt, plus_bcv, str, ov, dir);
      FNulledChildren(r2, cdnt, cp, c1, l1, q1, plus_bcv, str, ov1, dir)
    case Re_con(r1, r2) =>
      var (c1, l1, q1, ov1) := FNulledChildren(r1, cdnt, cp, cap, lk, qt, plus_bcv, str, ov, dir);
      FNulledChildren(r2, cdnt, cp, c1, l1, q1, plus_bcv, str, ov1, dir)
    case Re_quant(nul, qid, quanttype, body) =>
      match R.get_cp(qt, qid)
      case None => FNulledChildren(body, cdnt, cp, cap, lk, qt, plus_bcv, str, ov, dir)
      case Some(start_cp) =>
        if start_cp == cp then
          var start_clock := opt_int(R.get_clock(qt, qid));
          var bytecode := get_code_v(plus_bcv, qid);
          var ctx := cp_context(cp, str, dir);
          var inits0 := FInitState(bytecode, cp, cap, lk, qt, start_clock, ctx);
          var inits := inits0.(cdn := cdnt);
          var (result, _, ov1) := FNullInterp(bytecode, inits, ov, dir);
          var (ncap, nlk, nqt) := match result
                                  case None => (cap, lk, qt)
                                  case Some(w) => (w.capture_regs, w.look_regs, w.quant_regs);
          FNulledChildren(body, cdnt, cp, ncap, nlk, nqt, plus_bcv, str, ov1, dir)
        else
          (cap, lk, qt, ov)
  }

  /** Pure counterpart of `reconstruct_plus_groups`: reconstructs every nulled
      `+`'s missing captures in `thread` via `FNulledPlus`, leaving its
      `pc`/`exit_allowed` unchanged. */
  function FReconstructPlus(thread: Thread, ast: regex, plus_bcv: seq<code>,
                            str: string, ov: OracleView, dir: direction): (Thread, OracleView)
  {
    var (cap, lk, qt, ov1) := FNulledPlus(ast, thread.capture_regs, thread.look_regs,
                                          thread.quant_regs, plus_bcv, str, ov, dir);
    (Thread(thread.pc, cap, lk, qt, thread.exit_allowed), ov1)
  }

  /** Pure counterpart of `find_match_plus`: runs `FFindMatch` from
      `start_cp` and, on a match, reconstructs nulled-plus captures via
      `FReconstructPlus`. */
  function FFindMatchPlus(c: code, ast: regex, plus_bcv: seq<code>, str: string, ov: OracleView,
                          dir: direction, start_cp: int, capture: R.Regs, look: R.Regs,
                          quant: R.Regs, start_clock: int, cdn: cdns): (Option<Thread>, OracleView)
  {
    var inits := FInitState(c, start_cp, capture, look, quant, start_clock,
                            cp_context(start_cp, str, dir));
    var (result, ov1) := FFindMatch(c, str, inits, ov, dir, cdn);
    match result
    case None => (None, ov1)
    case Some(thread) =>
      var (rt, ov2) := FReconstructPlus(thread, ast, plus_bcv, str, ov1, dir);
      (Some(rt), ov2)
  }

  /** Pure counterpart of the `build_oracle` loop body: builds oracle entries
      for lookaround ids down to 1 in decreasing order, starting from `lid`
      (so a lookaround can reference lookarounds nested inside it, which get
      lower ids). */
  function FBuildLids(crv: FCompiled, str: string, lid: int, ov: OracleView): OracleView
    decreases lid
  {
    if lid < 1 then ov
    else
      var bytecode := get_code_v(crv.f_look_build_bc, lid);
      var looktype := if 0 <= lid < |crv.f_look_types| then crv.f_look_types[lid] else Lookahead;
      var dir := oracle_direction(looktype);
      var lookcdn := if 0 <= lid < |crv.f_look_cdns| then crv.f_look_cdns[lid] else [];
      var initcp := init_cp(dir, |str|);
      var maxcap := max_group(crv.f_main_ast);
      var maxlook := max_lookaround(crv.f_main_ast);
      var maxquant := max_quant(crv.f_main_ast);
      var capture := R.init_regs(2 * maxcap + 2);
      var lookmem := R.init_regs(maxlook + 1);
      var quant := R.init_regs(maxquant + 1);
      var inits := FInitState(bytecode, initcp, capture, lookmem, quant, 0,
                              cp_context(initcp, str, dir));
      var (_, ov1) := FFindMatch(bytecode, str, inits, ov, dir, lookcdn);
      FBuildLids(crv, str, lid - 1, ov1)
  }

  /** Pure counterpart of `build_oracle`: the full lookaround oracle for
      `str`, built by running every lookaround's oracle-building bytecode via
      `FBuildLids`. */
  function FBuildOracle(crv: FCompiled, str: string): OracleView
  {
    var maxlook := max_lookaround(crv.f_main_ast);
    FBuildLids(crv, str, maxlook, init_view(|str|, maxlook + 1))
  }

  /** Pure counterpart of the `build_capture` lookaround loop: for each
      lookaround id from `lid` to `maxlook`, if it was recorded as matching
      (`R.get_cp(lk, lid)`), replays its capture-reconstruction bytecode via
      `FFindMatchPlus`. */
  function FLookLoop(crv: FCompiled, str: string, lid: int, maxlook: int,
                     cap: R.Regs, lk: R.Regs, qt: R.Regs, ov: OracleView)
    : (R.Regs, R.Regs, R.Regs, OracleView)
    decreases maxlook - lid
  {
    if lid > maxlook then (cap, lk, qt, ov)
    else
      var next := lid + 1;
      match R.get_cp(lk, lid)
      case None => FLookLoop(crv, str, next, maxlook, cap, lk, qt, ov)
      case Some(cp) =>
        var looktype := if 0 <= lid < |crv.f_look_types| then crv.f_look_types[lid] else Lookahead;
        if capture_type(looktype) then
          var bytecode := get_code_v(crv.f_look_capture_bc, lid);
          var dir := capture_direction(looktype);
          var lookcdn := if 0 <= lid < |crv.f_look_cdns| then crv.f_look_cdns[lid] else [];
          var lookast := if 0 <= lid < |crv.f_look_ast| then crv.f_look_ast[lid] else Re_empty;
          var (result, ov1) := FFindMatchPlus(bytecode, lookast, crv.f_plus_bc, str, ov, dir,
                                              cp, cap, lk, qt, 0, lookcdn);
          var (ncap, nlk, nqt) := match result
                                  case None => (cap, lk, qt)
                                  case Some(t) => (t.capture_regs, t.look_regs, t.quant_regs);
          FLookLoop(crv, str, next, maxlook, ncap, nlk, nqt, ov1)
        else
          FLookLoop(crv, str, next, maxlook, cap, lk, qt, ov)
  }

  /** Pure counterpart of `build_capture`: finds the main match with
      `FFindMatchPlus`, reconstructs every lookaround's captures with
      `FLookLoop`, then filters out registers reset by unmatched
      alternatives/quantifiers via `filter_reset`. */
  function FBuildCapture(crv: FCompiled, str: string, ov: OracleView): (Option<seq<int>>, OracleView)
  {
    var max_look := max_lookaround(crv.f_main_ast);
    var max_cap := max_group(crv.f_main_ast);
    var max_quant := max_quant(crv.f_main_ast);
    var capture := R.init_regs(2 * max_cap + 2);
    var look := R.init_regs(max_look + 1);
    var quant := R.init_regs(max_quant + 1);
    var (main_result, ov1) := FFindMatchPlus(crv.f_main_bc, crv.f_main_ast, crv.f_plus_bc, str, ov,
                                             Forward, 0, capture, look, quant, 0, crv.f_main_cdns);
    match main_result
    case None => (None, ov1)
    case Some(thread) =>
      var (cap, lk, qt, ov2) := FLookLoop(crv, str, 1, max_look, thread.capture_regs,
                                          thread.look_regs, thread.quant_regs, ov1);
      (Some(filter_reset(crv.f_main_ast, cap, lk, qt, -1)), ov2)
  }

  /** Pure counterpart of `matcher`: builds the oracle then the capture
      result for `str` against compiled regex `crv`. */
  function FMatcher(crv: FCompiled, str: string): Option<seq<int>>
  {
    var ov := FBuildOracle(crv, str);
    FBuildCapture(crv, str, ov).0
  }

  // THE functional characterization of the whole engine: full_match (each
  // register backend) provably returns exactly this.
  /** THE functional specification of the whole engine: annotates and fully
      compiles `raw`, then matches `str`. Every register backend's
      `full_match` is proved to return exactly this. */
  function FFullMatch(raw: raw_regex, str: string): Option<seq<int>>
  {
    FMatcher(FFullCompilation(annotate(raw)), str)
  }

  // ===========================================================================
  // End of functional model
  // ===========================================================================

  /** Allocates a fresh `IState` for running code `c` from position `initcp`,
      matching `FInitState`. */
  method init_state(c: code, initcp: int, initcap: R.Regs, initlook: R.Regs,
                    initquant: R.Regs, initclk: int, initctx: char_context) returns (s: IState)
    ensures fresh(s)
    ensures |s.processed.true_set| == size(c) && |s.processed.false_set| == size(c)
    ensures s.cp == initcp && s.context == initctx
    ensures StateOf(s) == FInitState(c, initcp, initcap, initlook, initquant, initclk, initctx)
  {
    s := new IState(initcp, [init_thread(initcap, initlook, initquant)],
                    init_bpcset(size(c)), [], init_pcset(size(c)), None, initctx, initclk, init_cdn());
  }

  // * advance all threads along epsilon transitions
  /** Imperative counterpart of `FAdvanceEpsilon`: repeatedly pops the
      highest-priority `active` thread and steps it along epsilon transitions
      — jumps, forks, register/quantifier-clock writes, oracle/negative-oracle
      checks, oracle writes, loop begin/end, CDN nullability checks, and
      anchor assertions — until `active` is empty. */
  method advance_epsilon(c: code, s: IState, o: oracle, dir: direction)
    requires |s.processed.true_set| == size(c) && |s.processed.false_set| == size(c)
    modifies s, o
    ensures s.cp == old(s.cp) && s.context == old(s.context)   // epsilon phase doesn't move cp
    ensures (StateOf(s), ViewOf(o)) == FAdvanceEpsilon(c, old(StateOf(s)), old(ViewOf(o)), dir)
    decreases unprocessed(s.processed), |s.active|
  {
    if |s.active| == 0 { return; }
    var t := s.active[0];
    var ac := s.active[1..];
    var i := get_instr(c, t.pc);
    if bpc_mem(s.processed, t.pc, t.exit_allowed) {
      // already handled: drop the lower-priority duplicate (|active| shrinks)
      s.active := ac;
      advance_epsilon(c, s, o, dir);
    } else {
      var b0 := s.processed;           // == processed at method entry
      s.clock := s.clock + 1;
      s.processed := bpc_add(b0, t.pc, t.exit_allowed);
      // marking a fresh slot strictly decreases `unprocessed` (whenever t.pc is
      // in range, which holds for every instruction except an out-of-range Fail,
      // and there |active| shrinks instead).
      if t.exit_allowed {
        if 0 <= t.pc < |b0.true_set| { count_false_set(b0.true_set, t.pc); }
      } else {
        if 0 <= t.pc < |b0.false_set| { count_false_set(b0.false_set, t.pc); }
      }
      match i {
        case Consume(ce) =>
          var (nb, ni) := add_thread(t, ce, s.blocked, s.isblocked);
          s.blocked := nb; s.isblocked := ni;
          s.active := ac;
          advance_epsilon(c, s, o, dir);
        case Accept =>
          s.active := [];
          s.bestmatch := Some(t);
        case Jmp(x) =>
          s.active := [t.(pc := x)] + ac;
          advance_epsilon(c, s, o, dir);
        case Fork(x, y) =>
          var newt := Thread(x, t.capture_regs, t.look_regs, t.quant_regs, t.exit_allowed);
          s.active := [newt, t.(pc := y)] + ac;
          advance_epsilon(c, s, o, dir);
        case SetRegisterToCP(reg) =>
          var t' := t.(capture_regs := R.set_reg(t.capture_regs, reg, Some(s.cp), s.clock), pc := t.pc + 1);
          s.active := [t'] + ac;
          advance_epsilon(c, s, o, dir);
        case SetQuantToClock(q, b) =>
          var ocp := if b then Some(s.cp) else None;
          var t' := t.(quant_regs := R.set_reg(t.quant_regs, q, ocp, s.clock), pc := t.pc + 1);
          s.active := [t'] + ac;
          advance_epsilon(c, s, o, dir);
        case CheckOracle(l) =>
          GetOracleView(o, s.cp, l);
          if get_oracle(o, s.cp, l) {
            var t' := t.(pc := t.pc + 1, look_regs := R.set_reg(t.look_regs, l, Some(s.cp), s.clock));
            s.active := [t'] + ac;
          } else {
            s.active := ac;
          }
          advance_epsilon(c, s, o, dir);
        case NegCheckOracle(l) =>
          GetOracleView(o, s.cp, l);
          if get_oracle(o, s.cp, l) {
            s.active := ac;
          } else {
            s.active := [t.(pc := t.pc + 1)] + ac;
          }
          advance_epsilon(c, s, o, dir);
        case WriteOracle(l) =>
          s.active := ac;
          set_oracle(o, s.cp, l);
          advance_epsilon(c, s, o, dir);
        case BeginLoop =>
          s.active := [t.(exit_allowed := false, pc := t.pc + 1)] + ac;
          advance_epsilon(c, s, o, dir);
        case EndLoop =>
          if t.exit_allowed {
            s.active := [t.(pc := t.pc + 1)] + ac;
          } else {
            s.active := ac;
          }
          advance_epsilon(c, s, o, dir);
        case CheckNullable(qid) =>
          if cdn_get(s.cdn, qid) {
            s.active := [t.(pc := t.pc + 1)] + ac;
          } else {
            s.active := ac;
          }
          advance_epsilon(c, s, o, dir);
        case AnchorAssertion(a) =>
          if is_satisfied(a, s.context, dir) {
            s.active := [t.(pc := t.pc + 1)] + ac;
          } else {
            s.active := ac;
          }
          advance_epsilon(c, s, o, dir);
        case Fail =>
          s.active := ac;
          advance_epsilon(c, s, o, dir);
      }
    }
  }

  // * consume the next character, advancing or killing blocked threads
  /** Imperative counterpart of `FConsume`: feeds the next input character to
      each `blocked` thread in priority order, reactivating those it
      satisfies. */
  method consume(s: IState)
    modifies s
    ensures s.cp == old(s.cp) && s.context == old(s.context) && s.processed == old(s.processed)
    ensures StateOf(s) == FConsume(old(StateOf(s)))
    decreases |s.blocked|
  {
    if |s.blocked| == 0 { return; }
    var t := s.blocked[0].0;
    var ce := s.blocked[0].1;
    s.blocked := s.blocked[1..];
    if is_accepted(s.context.nextchar, ce) {
      // t just consumed something, so exiting a loop is allowed again
      s.active := [t.(exit_allowed := true, pc := t.pc + 1)] + s.active;
    }
    consume(s);
  }

  // * Null interpreter: follow epsilon transitions only (for + reconstruction)
  /** Imperative counterpart of `FNullInterp`: runs `advance_epsilon` alone (no
      consuming) and returns the resulting best match, if any. */
  method null_interp(c: code, s: IState, o: oracle, dir: direction) returns (res: Option<Thread>)
    requires |s.processed.true_set| == size(c) && |s.processed.false_set| == size(c)
    modifies s, o
    ensures (res, StateOf(s), ViewOf(o)) == FNullInterp(c, old(StateOf(s)), old(ViewOf(o)), dir)
  {
    advance_epsilon(c, s, o, dir);   // terminating; null_interp is straight-line
    res := s.bestmatch;
  }

  // * Finding the top priority match: alternate advance_epsilon and consume
  /** Imperative counterpart of `FFindMatch`: the main matching loop over
      `str`, alternating `advance_epsilon` and `consume` while rebuilding the
      CDN table at each position, until the threads die out or the string end
      is reached. */
  method find_match(c: code, str: string, s: IState, o: oracle, dir: direction, cdn: cdns)
    returns (res: Option<Thread>)
    requires |s.processed.true_set| == size(c) && |s.processed.false_set| == size(c)
    // the context's next character is the one at the current position, so a
    // Some next-char witnesses that cp is strictly inside the string.
    requires dir.Forward? ==> s.context.nextchar == get_char(str, s.cp)
    requires dir.Backward? ==> s.context.nextchar == get_char(str, s.cp - 1)
    modifies s, o
    ensures (res, ViewOf(o)) == FFindMatch(c, str, old(StateOf(s)), old(ViewOf(o)), dir, cdn)
    decreases if dir.Forward? then |str| - s.cp else s.cp   // cp walks toward an end of the string
  {
    BuildCdnView(cdn, s.cp, o, s.context, dir);
    s.cdn := build_cdn(cdn, s.cp, o, s.context, dir);
    advance_epsilon(c, s, o, dir);
    if |s.blocked| == 0 {
      return s.bestmatch;       // no more surviving threads
    }
    match s.context.nextchar {
      case None => return s.bestmatch;   // reached the end of the string
      case Some(_) =>
        consume(s);
        s.processed := init_bpcset(size(c));
        s.isblocked := init_pcset(size(c));
        s.cdn := init_cdn();
        s.cp := incr_cp(s.cp, dir);
        var newchar := get_char(str, s.cp - cp_offset(dir));
        s.context := update_context(s.context, newchar);
        res := find_match(c, str, s, o, dir, cdn);
    }
  }

  // * Reconstructing Nullable + Values
  // reads a code entry from the plus-bytecode table (bounds-guarded read)
  /** Total, bounds-guarded read of the `i`th entry of code array `a`
      (out-of-range `i` reads as `[]`). */
  function get_code(a: array<code>, i: int): code reads a {
    if 0 <= i < a.Length then a[i] else []
  }
  function opt_int(o: Option<int>): int { match o case None => -1 case Some(x) => x }

  // goes through the regex; for each nulled +, replays it with the null interp.
  /** Imperative counterpart of `FNulledPlus`: walks `reg`, replaying each
      unresolved `+` iteration's bytecode via `null_interp` to reconstruct
      capture registers a nulled last iteration would have set. */
  method nulled_plus(reg: regex, cap: R.Regs, lk: R.Regs, qt: R.Regs,
                     plus_bc: array<code>, str: string, o: oracle, dir: direction)
    returns (cap2: R.Regs, lk2: R.Regs, qt2: R.Regs)
    modifies o
    ensures (cap2, lk2, qt2, ViewOf(o))
         == FNulledPlus(reg, cap, lk, qt, plus_bc[..], str, old(ViewOf(o)), dir)
    decreases reg          // structural recursion on the AST; null_interp terminates
  {
    match reg {
      case Re_empty => cap2, lk2, qt2 := cap, lk, qt;
      case Re_character(_) => cap2, lk2, qt2 := cap, lk, qt;
      case Re_anchor(_) => cap2, lk2, qt2 := cap, lk, qt;
      case Re_lookaround(_, _, _) => cap2, lk2, qt2 := cap, lk, qt;
      case Re_capture(_, r1) =>
        cap2, lk2, qt2 := nulled_plus(r1, cap, lk, qt, plus_bc, str, o, dir);
      case Re_alt(r1, r2) =>
        var c1, l1, q1 := nulled_plus(r1, cap, lk, qt, plus_bc, str, o, dir);
        cap2, lk2, qt2 := nulled_plus(r2, c1, l1, q1, plus_bc, str, o, dir);
      case Re_con(r1, r2) =>
        var c1, l1, q1 := nulled_plus(r1, cap, lk, qt, plus_bc, str, o, dir);
        cap2, lk2, qt2 := nulled_plus(r2, c1, l1, q1, plus_bc, str, o, dir);
      case Re_quant(nul, qid, quanttype, body) =>
        match R.get_cp(qt, qid) {
          case None =>
            cap2, lk2, qt2 := nulled_plus(body, cap, lk, qt, plus_bc, str, o, dir);
          case Some(start_cp) =>
            var start_clock := opt_int(R.get_clock(qt, qid));
            var bytecode := get_code(plus_bc, qid);
            var ctx := cp_context(start_cp, str, dir);
            var inits := init_state(bytecode, start_cp, cap, lk, qt, start_clock, ctx);
            var subcdn := compile_cdns(body);
            BuildCdnView(subcdn, start_cp, o, ctx, dir);
            var subtable := build_cdn(subcdn, start_cp, o, ctx, dir);
            inits.cdn := subtable;
            var result := null_interp(bytecode, inits, o, dir);
            var ncap, nlk, nqt := cap, lk, qt;
            match result {
              case None =>          // OCaml failwith "expected a nullable plus"
              case Some(w) => ncap, nlk, nqt := w.capture_regs, w.look_regs, w.quant_regs;
            }
            cap2, lk2, qt2 := nulled_children(body, subtable, start_cp, ncap, nlk, nqt, plus_bc, str, o, dir);
        }
    }
  }

  // children nulled while nulling a parent plus share the parent's CDN table
  /** Imperative counterpart of `FNulledChildren`: like `nulled_plus`, but only
      for quantifiers nested in a parent `+` that started at the same
      position `cp`, reusing the parent's CDN table `cdnt`. */
  method nulled_children(reg: regex, cdnt: cdn_table, cp: int, cap: R.Regs, lk: R.Regs, qt: R.Regs,
                         plus_bc: array<code>, str: string, o: oracle, dir: direction)
    returns (cap2: R.Regs, lk2: R.Regs, qt2: R.Regs)
    modifies o
    ensures (cap2, lk2, qt2, ViewOf(o))
         == FNulledChildren(reg, cdnt, cp, cap, lk, qt, plus_bc[..], str, old(ViewOf(o)), dir)
    decreases reg          // structural recursion on the AST; null_interp terminates
  {
    match reg {
      case Re_empty => cap2, lk2, qt2 := cap, lk, qt;
      case Re_character(_) => cap2, lk2, qt2 := cap, lk, qt;
      case Re_anchor(_) => cap2, lk2, qt2 := cap, lk, qt;
      case Re_lookaround(_, _, _) => cap2, lk2, qt2 := cap, lk, qt;
      case Re_capture(_, r1) =>
        cap2, lk2, qt2 := nulled_children(r1, cdnt, cp, cap, lk, qt, plus_bc, str, o, dir);
      case Re_alt(r1, r2) =>
        var c1, l1, q1 := nulled_children(r1, cdnt, cp, cap, lk, qt, plus_bc, str, o, dir);
        cap2, lk2, qt2 := nulled_children(r2, cdnt, cp, c1, l1, q1, plus_bc, str, o, dir);
      case Re_con(r1, r2) =>
        var c1, l1, q1 := nulled_children(r1, cdnt, cp, cap, lk, qt, plus_bc, str, o, dir);
        cap2, lk2, qt2 := nulled_children(r2, cdnt, cp, c1, l1, q1, plus_bc, str, o, dir);
      case Re_quant(nul, qid, quanttype, body) =>
        match R.get_cp(qt, qid) {
          case None =>
            cap2, lk2, qt2 := nulled_children(body, cdnt, cp, cap, lk, qt, plus_bc, str, o, dir);
          case Some(start_cp) =>
            if start_cp == cp {
              var start_clock := opt_int(R.get_clock(qt, qid));
              var bytecode := get_code(plus_bc, qid);
              var ctx := cp_context(cp, str, dir);
              var inits := init_state(bytecode, cp, cap, lk, qt, start_clock, ctx);
              inits.cdn := cdnt;
              var result := null_interp(bytecode, inits, o, dir);
              var ncap, nlk, nqt := cap, lk, qt;
              match result {
                case None =>        // OCaml failwith "expected a nullable children plus"
                case Some(w) => ncap, nlk, nqt := w.capture_regs, w.look_regs, w.quant_regs;
              }
              cap2, lk2, qt2 := nulled_children(body, cdnt, cp, ncap, nlk, nqt, plus_bc, str, o, dir);
            } else {
              cap2, lk2, qt2 := cap, lk, qt;
            }
        }
    }
  }

  /** Imperative counterpart of `FReconstructPlus`: reconstructs `thread`'s
      nulled-`+` captures via `nulled_plus`. */
  method reconstruct_plus_groups(thread: Thread, ast: regex, plus_bc: array<code>,
                                 str: string, o: oracle, dir: direction) returns (res: Thread)
    modifies o
    ensures (res, ViewOf(o)) == FReconstructPlus(thread, ast, plus_bc[..], str, old(ViewOf(o)), dir)
  {
    var cap, lk, qt := nulled_plus(ast, thread.capture_regs, thread.look_regs, thread.quant_regs,
                                   plus_bc, str, o, dir);
    res := Thread(thread.pc, cap, lk, qt, thread.exit_allowed);
  }

  // * Find a match AND reconstruct the corresponding plus groups
  /** Imperative counterpart of `FFindMatchPlus`: runs `find_match` from
      `start_cp`, then `reconstruct_plus_groups` on a match. */
  method find_match_plus(c: code, ast: regex, plus_bc: array<code>, str: string, o: oracle,
                         dir: direction, start_cp: int, capture: R.Regs, look: R.Regs,
                         quant: R.Regs, start_clock: int, cdn: cdns) returns (res: Option<Thread>)
    modifies o
    ensures (res, ViewOf(o)) == FFindMatchPlus(c, ast, plus_bc[..], str, old(ViewOf(o)), dir,
                                               start_cp, capture, look, quant, start_clock, cdn)
  {
    var initstate := init_state(c, start_cp, capture, look, quant, start_clock, cp_context(start_cp, str, dir));
    var result := find_match(c, str, initstate, o, dir, cdn);
    match result {
      case None => res := None;
      case Some(thread) =>
        var rt := reconstruct_plus_groups(thread, ast, plus_bc, str, o, dir);
        res := Some(rt);
    }
  }

  // * Filtering For Capture Reset (functional over register seqs)
  function set_idx(s: seq<int>, i: int, v: int): seq<int> {
    if 0 <= i < |s| then s[i := v] else s
  }
  function get_idx(s: seq<int>, i: int): int {
    if 0 <= i < |s| then s[i] else -1
  }

  /** Resets every capture-group start register found under `r` to unset
      (`-1`) — used when an alternative/quantifier body didn't end up on the
      winning path, so its captures must not leak into the result. */
  function filter_all(r: regex, regs: seq<int>): seq<int>
    decreases r
  {
    match r
    case Re_empty => regs
    case Re_character(_) => regs
    case Re_anchor(_) => regs
    case Re_alt(r1, r2) => filter_all(r2, filter_all(r1, regs))
    case Re_con(r1, r2) => filter_all(r2, filter_all(r1, regs))
    case Re_quant(_, _, _, r1) => filter_all(r1, regs)
    case Re_capture(cid, r1) => filter_all(r1, set_idx(regs, start_reg(cid), -1))
    case Re_lookaround(_, _, r1) => filter_all(r1, regs)
  }

  /** Walks `r`, comparing each capture/quantifier/lookaround's recorded clock
      against `maxclock` (the enclosing scope's threshold) to decide whether
      it belongs to the winning match or must be reset via `filter_all` —
      implements ECMAScript's per-iteration capture-reset semantics. */
  function filter_capture(r: regex, cap_regs: seq<int>, cap_clocks: seq<int>,
                          look_clocks: seq<int>, quant_clocks: seq<int>, maxclock: int): seq<int>
    decreases r
  {
    match r
    case Re_empty => cap_regs
    case Re_character(_) => cap_regs
    case Re_anchor(_) => cap_regs
    case Re_alt(r1, r2) =>
      var c1 := filter_capture(r1, cap_regs, cap_clocks, look_clocks, quant_clocks, maxclock);
      filter_capture(r2, c1, cap_clocks, look_clocks, quant_clocks, maxclock)
    case Re_con(r1, r2) =>
      var c1 := filter_capture(r1, cap_regs, cap_clocks, look_clocks, quant_clocks, maxclock);
      filter_capture(r2, c1, cap_clocks, look_clocks, quant_clocks, maxclock)
    case Re_quant(nul, qid, quant, r1) =>
      var quant_val := get_idx(quant_clocks, qid);
      if quant_val < maxclock then filter_all(r1, cap_regs)
      else filter_capture(r1, cap_regs, cap_clocks, look_clocks, quant_clocks, quant_val)
    case Re_capture(cid, r1) =>
      var start := get_idx(cap_clocks, start_reg(cid));
      if start < 0 then filter_all(r1, cap_regs)
      else if start < maxclock then filter_all(r1, set_idx(cap_regs, start_reg(cid), -1))
      else filter_capture(r1, cap_regs, cap_clocks, look_clocks, quant_clocks, maxclock)
    case Re_lookaround(lid, l, r1) =>
      var look_val := get_idx(look_clocks, lid);
      if look_val < 0 then filter_all(r1, cap_regs)
      else if look_val < maxclock then filter_all(r1, cap_regs)
      else filter_capture(r1, cap_regs, cap_clocks, look_clocks, quant_clocks, -1)
  }

  /** Top-level entry point for capture-reset filtering: reads `capture`/
      `look`/`quant`'s clocks and applies `filter_capture` to `r`, producing
      the final flat `(start, end)` register sequence for the match. */
  function filter_reset(r: regex, capture: R.Regs, look: R.Regs, quant: R.Regs, maxclock: int): seq<int> {
    var (cap_regs, cap_clocks) := R.as_arrays(capture);
    var (_, look_clocks) := R.as_arrays(look);
    var (_, quant_clocks) := R.as_arrays(quant);
    filter_capture(r, cap_regs, cap_clocks, look_clocks, quant_clocks, maxclock)
  }

  // * Building the Oracle (lookarounds by reverse order of their ids)
  /** Imperative counterpart of `FBuildOracle`: allocates a fresh oracle sized
      for `str` and `cr`'s lookarounds, then builds every lookaround's entries
      in decreasing id order via `find_match`. */
  method build_oracle(cr: CompiledRegex, str: string) returns (o: oracle)
    ensures fresh(o)
    ensures ViewOf(o) == FBuildOracle(CrView(cr), str)
  {
    ghost var crv := CrView(cr);
    var maxlook := max_lookaround(cr.main_ast);
    var maxcap := max_group(cr.main_ast);
    var maxquant := max_quant(cr.main_ast);
    o := create_oracle(|str|, maxlook + 1);
    var lid := maxlook;
    while lid >= 1
      invariant 0 <= lid <= maxlook
      invariant fresh(o)
      invariant CrView(cr) == crv
      invariant FBuildLids(crv, str, lid, ViewOf(o)) == FBuildOracle(crv, str)
      decreases lid
    {
      ghost var vpre := ViewOf(o);
      var bytecode := get_code(cr.look_build_bc, lid);
      var looktype := if 0 <= lid < cr.look_types.Length then cr.look_types[lid] else Lookahead;
      var direction := oracle_direction(looktype);
      var lookcdn := if 0 <= lid < cr.look_cdns.Length then cr.look_cdns[lid] else [];
      var initcp := init_cp(direction, |str|);
      var initctx := cp_context(initcp, str, direction);
      var capture := R.init_regs(2 * maxcap + 2);
      var lookmem := R.init_regs(maxlook + 1);
      var quant := R.init_regs(maxquant + 1);
      var initstate := init_state(bytecode, initcp, capture, lookmem, quant, 0, initctx);
      var _ := find_match(bytecode, str, initstate, o, direction, lookcdn);
      assert FBuildLids(crv, str, lid - 1, ViewOf(o)) == FBuildLids(crv, str, lid, vpre);
      lid := lid - 1;
    }
  }

  // * Finding the main match and reconstructing lookaround capture groups
  /** Imperative counterpart of `FBuildCapture`: finds the main match,
      reconstructs every recorded lookaround's captures in increasing id
      order, then applies `filter_reset` to produce the final capture
      registers. */
  method build_capture(cr: CompiledRegex, str: string, o: oracle) returns (res: Option<seq<int>>)
    modifies o
    ensures (res, ViewOf(o)) == FBuildCapture(CrView(cr), str, old(ViewOf(o)))
  {
    ghost var crv := CrView(cr);
    ghost var v0 := ViewOf(o);
    var max_look := max_lookaround(cr.main_ast);
    var max_cap := max_group(cr.main_ast);
    var max_quant := max_quant(cr.main_ast);
    var capture := R.init_regs(2 * max_cap + 2);
    var look := R.init_regs(max_look + 1);
    var quant := R.init_regs(max_quant + 1);
    var main_result := find_match_plus(cr.main_bc, cr.main_ast, cr.plus_bc, str, o, Forward, 0,
                                       capture, look, quant, 0, cr.main_cdns);
    match main_result {
      case None => res := None;
      case Some(thread) =>
        ghost var v1 := ViewOf(o);
        var cap := thread.capture_regs;
        var lk := thread.look_regs;
        var qt := thread.quant_regs;
        var lid := 1;
        while lid <= max_look
          invariant 1 <= lid <= max_look + 1
          invariant CrView(cr) == crv
          invariant FLookLoop(crv, str, lid, max_look, cap, lk, qt, ViewOf(o))
                 == FLookLoop(crv, str, 1, max_look, thread.capture_regs, thread.look_regs, thread.quant_regs, v1)
          decreases max_look - lid
        {
          ghost var vpre := ViewOf(o);
          ghost var cap0, lk0, qt0 := cap, lk, qt;
          match R.get_cp(lk, lid) {
            case None =>
            case Some(cp) =>
              var looktype := if 0 <= lid < cr.look_types.Length then cr.look_types[lid] else Lookahead;
              if capture_type(looktype) {
                var bytecode := get_code(cr.look_capture_bc, lid);
                var direction := capture_direction(looktype);
                var lookcdn := if 0 <= lid < cr.look_cdns.Length then cr.look_cdns[lid] else [];
                var lookast := if 0 <= lid < cr.look_ast.Length then cr.look_ast[lid] else Re_empty;
                var result := find_match_plus(bytecode, lookast, cr.plus_bc, str, o, direction, cp,
                                              cap, lk, qt, 0, lookcdn);
                match result {
                  case None =>      // OCaml failwith "result expected from the oracle"
                  case Some(t) => cap := t.capture_regs; lk := t.look_regs; qt := t.quant_regs;
                }
              }
          }
          assert FLookLoop(crv, str, lid + 1, max_look, cap, lk, qt, ViewOf(o))
              == FLookLoop(crv, str, lid, max_look, cap0, lk0, qt0, vpre);
          lid := lid + 1;
        }
        var match_capture := filter_reset(cr.main_ast, cap, lk, qt, -1);
        res := Some(match_capture);
    }
  }

  // * The Full Matcher
  /** Imperative counterpart of `FMatcher`: runs `build_oracle` then
      `build_capture` on already-compiled regex `cr` against `str`. */
  method matcher(cr: CompiledRegex, str: string) returns (res: Option<seq<int>>)
    ensures res == FMatcher(CrView(cr), str)
  {
    var o := build_oracle(cr, str);
    res := build_capture(cr, str, o);
  }

  /** Imperative counterpart of `FFullMatch`: the top-level entry point —
      annotates `raw`, fully compiles it, and matches `str`, returning the
      flat capture-register sequence on success. */
  method full_match(raw: raw_regex, str: string) returns (res: Option<seq<int>>)
    ensures res == FFullMatch(raw, str)
  {
    var re := annotate(raw);
    var cr := full_compilation(re);
    res := matcher(cr, str);
  }
}

// The three instantiations (OCaml: Interpreter(Array_Regs) etc.)
/** The `Interpreter` instantiated with the `Array_Regs` register backend. */
module ArrayInterp refines Interpreter { import R = Array_Regs }
/** The `Interpreter` instantiated with the `List_Regs` register backend. */
module ListInterp refines Interpreter { import R = List_Regs }
/** The `Interpreter` instantiated with the `Map_Regs` register backend. */
module MapInterp refines Interpreter { import R = Map_Regs }
