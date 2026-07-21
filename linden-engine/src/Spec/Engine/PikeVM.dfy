// Mirror of Engine/PikeVM.v.
// The PikeVM algorithm as a small-step relation over the bytecode NFA, with memoization of seen
// (pc, LoopBool) pairs. `pike_vm_step` is non-recursive (7 rules, deterministic) so it is a plain
// predicate; `epsilon_step` is the executable atomic step.

/** The PikeVM: Pike's parallel-thread NFA simulation over the bytecode compiled by `NFA.Compile`.
    Runs all threads in priority order at each input position, using `SeenSets`' `(pc, LoopBool)`
    memoization so each thread expands at most once per position — the mechanism behind linear-time
    matching. Proved equivalent to the tree semantics via `PikeEquiv`/`Correctness`. */
module PikeVM {
  import opened Std.Wrappers
  import opened WarblreRegExpRecord
  import opened WarblrePrimitives
  import opened Chars
  import opened Groups
  import opened Tree            // Leaf
  import opened NFA
  import opened BooleanSemantics  // LoopBool
  import Semantics                // AnchorSatisfied
  import opened SeenSets

  // Coq: thread := (label * group_map * LoopBool).
  /** A PikeVM thread: an instruction pointer `pc`, its captured groups `gm`, and the loop-progress
      flag `b` (see `LoopBool`) used by the `SeenPcs` dedup. */
  datatype Thread = Thr(pc: Label, gm: GroupMap, b: LoopBool)

  /** Retarget a thread's `pc`, keeping its captures and loop flag. */
  function UpdLabel(t: Thread, next: Label): Thread { Thr(next, t.gm, t.b) }
  /** Advance a thread to the next instruction, unchanged otherwise. */
  function AdvanceThread(t: Thread): Thread { Thr(t.pc + 1, t.gm, t.b) }
  /** Advance past a `Consume` and mark the thread `CanExit` — it just made progress. */
  function BlockThread(t: Thread): Thread { Thr(t.pc + 1, t.gm, CanExit) }
  /** Advance past a `SetRegOpen`, recording the group's start via `GMOpen`. */
  function OpenThread(t: Thread, gid: GroupId, idx: nat): Thread { Thr(t.pc + 1, GMOpen(idx, gid, t.gm), t.b) }
  /** Advance past a `SetRegClose`, recording the group's end via `GMClose`. */
  function CloseThread(t: Thread, gid: GroupId, idx: nat): Thread { Thr(t.pc + 1, GMClose(idx, gid, t.gm), t.b) }
  /** Advance past a `ResetRegs`, clearing the given groups via `GMReset`. */
  function ResetThread(t: Thread, gidl: seq<GroupId>): Thread { Thr(t.pc + 1, GMReset(gidl, t.gm), t.b) }
  /** Advance past a `BeginLoop`, marking the thread `CannotExit` — an iteration just started. */
  function BeginThread(t: Thread): Thread { Thr(t.pc + 1, t.gm, CannotExit) }
  /** A thread's captured groups. */
  function GmOf(t: Thread): GroupMap { t.gm }
  /** Whether `t`'s `(pc, b)` key is already memoized in `seen` (the dedup test). */
  predicate SeenThread(seen: SeenPcs, t: Thread) { Inseenpc(seen, t.pc, t.b) }
  /** Memoize `t`'s `(pc, b)` key in `seen`. */
  function AddThread(seen: SeenPcs, t: Thread): SeenPcs { AddSeenPcs(seen, t.pc, t.b) }

  // Coq: epsilon_result
  /** The outcome of one `EpsilonStep`: `EpsActive` spawns zero or more successor threads, `EpsMatch`
      reports a completed match, `EpsBlocked` means the thread is waiting to consume the next character. */
  datatype EpsilonResult = EpsActive(threads: seq<Thread>) | EpsMatch | EpsBlocked(t: Thread)
  /** No successor threads: this thread dies here. */
  function EpsDead(): EpsilonResult { EpsActive([]) }

  // Coq: epsilon_step
  /** The atomic instruction-execution step: runs the instruction at `t.pc` and reports its effect —
      control flow and group updates produce `EpsActive` successor(s), `Accept` produces `EpsMatch`,
      a readable `Consume` produces `EpsBlocked`, anything else (dead end) collapses to `EpsDead`.
      The bytecode-level analog of `PikeTree.TreeBfsStep`. */
  function EpsilonStep(rer: RegExpRecord, t: Thread, c: Code, i: Input): EpsilonResult {
    match GetPc(c, t.pc)
    case None => EpsDead()
    case Some(instr) =>
      (match instr
       case Accept => EpsMatch
       case Consume(cd) =>
         (match CheckRead(rer, cd, i, Forward) case CannotRead => EpsDead() case CanRead => EpsBlocked(BlockThread(t)))
       case Jmp(next) => EpsActive([UpdLabel(t, next)])
       case Fork(l1, l2) => EpsActive([UpdLabel(t, l1), UpdLabel(t, l2)])
       case SetRegOpen(gid) => EpsActive([OpenThread(t, gid, Idx(i))])
       case SetRegClose(gid) => EpsActive([CloseThread(t, gid, Idx(i))])
       case ResetRegs(gidl) => EpsActive([ResetThread(t, gidl)])
       case BeginLoop => EpsActive([BeginThread(t)])
       case EndLoop(next) =>
         (match t.b case CannotExit => EpsDead() case CanExit => EpsActive([UpdLabel(t, next)]))
       case KillThread => EpsDead()
       case CheckAnchor(a) =>
         // zero-width: satisfied continues at pc + 1, else the thread dies
         (if Semantics.AnchorSatisfied(rer, a, i) then EpsActive([UpdLabel(t, t.pc + 1)]) else EpsDead()))
  }

  // Coq: pike_vm_state
  /** The PikeVM's global state: `active` threads still to process at the current `inp`, `blocked`
      threads waiting for the next character, the `best` match found so far, and the `seen` dedup
      set — or `PVS_final` once a run has settled on its answer. */
  datatype PikeVmState =
    | PVS(inp: Input, active: seq<Thread>, best: Option<Leaf>, blocked: seq<Thread>, seen: SeenPcs)
    | PVS_final(best: Option<Leaf>)

  // Coq: pike_vm_initial_state
  /** The starting state for matching at `inp`: a single thread at `pc` 0 with empty captures,
      `CanExit`, nothing seen yet, and no blocked threads. */
  function PikeVmInitialState(inp: Input): PikeVmState {
    PVS(inp, [Thr(0, Empty, CanExit)], None, [], InitialSeenPcs)
  }

  // Coq: pike_vm_step (the 7-rule small-step relation; deterministic, so written functionally).
  /** The PikeVM's small-step transition. Pops the head of `active`: if it's already `SeenThread` it
      is dropped (`pvs_skip`), otherwise `EpsilonStep` fires and its result folds into the next state
      (`pvs_active`/`pvs_match`/`pvs_blocked`). Once `active` is empty, `blocked` becomes the new
      `active` at the next input position, or the run finishes (`pvs_nextchar`/`pvs_end`/`pvs_final`).
      This is Pike's classic priority-ordered, linear-time thread simulation. */
  predicate PikeVmStep(c: Code, rer: RegExpRecord, s1: PikeVmState, s2: PikeVmState) {
    match s1
    case PVS_final(_) => false
    case PVS(inp, active, best, blocked, seen) =>
      if |active| == 0 then
        if |blocked| == 0 then
          s2 == PVS_final(best)  // pvs_final
        else
          (match AdvanceInput(inp, Forward)
           case None => s2 == PVS_final(best)  // pvs_end
           case Some(inp2) => s2 == PVS(inp2, blocked, best, [], InitialSeenPcs))  // pvs_nextchar
      else
        var t := active[0];
        var rest := active[1..];
        if SeenThread(seen, t) then
          s2 == PVS(inp, rest, best, blocked, seen)  // pvs_skip
        else
          (match EpsilonStep(rer, t, c, inp)
           case EpsActive(nextactive) => s2 == PVS(inp, nextactive + rest, best, blocked, AddThread(seen, t))  // pvs_active
           case EpsMatch => s2 == PVS(inp, [], Some((inp, GmOf(t))), blocked, AddThread(seen, t))  // pvs_match
           case EpsBlocked(newt) => s2 == PVS(inp, rest, best, blocked + [newt], AddThread(seen, t)))  // pvs_blocked
  }

  // Coq: pikevm_deterministic (immediate from the functional encoding)
  /** `PikeVmStep` is a function in disguise: the successor state of `s0` is unique. */
  lemma PikevmDeterministic(c: Code, rer: RegExpRecord, s0: PikeVmState, s1: PikeVmState, s2: PikeVmState)
    requires PikeVmStep(c, rer, s0, s1)
    requires PikeVmStep(c, rer, s0, s2)
    ensures s1 == s2
  {}

  // Coq: pikevm_progress
  /** `PikeVmStep` is total: every state has a successor (built explicitly here), so the VM never
      gets stuck short of `PVS_final`. */
  lemma PikevmProgress(c: Code, rer: RegExpRecord, inp: Input, active: seq<Thread>, best: Option<Leaf>, blocked: seq<Thread>, seen: SeenPcs)
    returns (pvsNext: PikeVmState)
    ensures PikeVmStep(c, rer, PVS(inp, active, best, blocked, seen), pvsNext)
  {
    var s1 := PVS(inp, active, best, blocked, seen);
    if |active| == 0 {
      if |blocked| == 0 {
        pvsNext := PVS_final(best);
      } else {
        match AdvanceInput(inp, Forward)
        case None => pvsNext := PVS_final(best);
        case Some(inp2) => pvsNext := PVS(inp2, blocked, best, [], InitialSeenPcs);
      }
    } else {
      var t := active[0];
      var rest := active[1..];
      if SeenThread(seen, t) {
        pvsNext := PVS(inp, rest, best, blocked, seen);
      } else {
        match EpsilonStep(rer, t, c, inp)
        case EpsActive(nextactive) => pvsNext := PVS(inp, nextactive + rest, best, blocked, AddThread(seen, t));
        case EpsMatch => pvsNext := PVS(inp, [], Some((inp, GmOf(t))), blocked, AddThread(seen, t));
        case EpsBlocked(newt) => pvsNext := PVS(inp, rest, best, blocked + [newt], AddThread(seen, t));
      }
    }
  }
}
