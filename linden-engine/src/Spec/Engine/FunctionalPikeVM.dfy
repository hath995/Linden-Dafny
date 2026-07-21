// Mirror of Engine/FunctionalPikeVM.v.
// The PikeVM as a fuel-based executable function, and its correspondence to the small-step trc.
// The concrete execution Examples at the end of the Coq file are omitted (they require executable
// character matching, which is ghost in this port — Exist/ExistCanonicalized use `exists`).
include "PikeVM.dfy"
include "Correctness.dfy"

/** Makes the `PikeVM` small-step relation executable: `PikeVmFuncStep`/`PikeVmLoop` run it as a
    fuel-bounded function, `PikeVmMatch` is the top-level entry point, and the lemmas here connect the
    functional runs back to the relational `PikeVmStep`/`Correctness.TrcPikeVm` for correctness proofs. */
module FunctionalPikeVM {
  import opened Std.Wrappers
  import opened WarblreRegExpRecord
  import opened WarblrePrimitives
  import opened Chars
  import opened Regex           // Regex
  import opened Tree            // Leaf
  import opened NFA             // Compilation, Code
  import opened SeenSets
  import opened PikeVM
  import opened Correctness

  // Coq: pike_vm_func_step
  /** The unique successor state `PikeVM.PikeVmStep` would relate `pvs` to, computed directly as a
      function (the step relation is deterministic, so this is just its functional encoding). */
  function PikeVmFuncStep(c: Code, rer: RegExpRecord, pvs: PikeVmState): PikeVmState {
    match pvs
    case PVS_final(_) => pvs
    case PVS(inp, active, best, blocked, seen) =>
      if |active| == 0 then
        if |blocked| == 0 then PVS_final(best)
        else
          (match AdvanceInput(inp, Forward)
           case None => PVS_final(best)
           case Some(inp2) => PVS(inp2, blocked, best, [], InitialSeenPcs))
      else
        var t := active[0];
        var rest := active[1..];
        if SeenThread(seen, t) then PVS(inp, rest, best, blocked, seen)
        else
          (match EpsilonStep(rer, t, c, inp)
           case EpsActive(na) => PVS(inp, na + rest, best, blocked, AddThread(seen, t))
           case EpsMatch => PVS(inp, [], Some((inp, GmOf(t))), blocked, AddThread(seen, t))
           case EpsBlocked(newt) => PVS(inp, rest, best, blocked + [newt], AddThread(seen, t)))
  }

  // Coq: pike_vm_loop
  /** Drives `PikeVmFuncStep` up to `fuel` times, or until a `PikeVmState.PVS_final?` state is reached
      (whichever comes first). This is the actual runnable matcher loop. */
  function PikeVmLoop(c: Code, rer: RegExpRecord, pvs: PikeVmState, fuel: nat): PikeVmState
    decreases fuel
  {
    match pvs
    case PVS_final(_) => pvs
    case PVS(_, _, _, _, _) =>
      if fuel == 0 then pvs
      else PikeVmLoop(c, rer, PikeVmFuncStep(c, rer, pvs), fuel - 1)
  }

  // Coq: bytecode_fuel
  /** The fuel budget `PikeVmMatch` runs with: `O(|c| * n)` where `n` is the remaining input length.
      Large enough that `PikeVmLoop` always reaches a final state — this is what makes the VM's
      linear-time bound (`Termination.PikeVmReachesFinal`) concrete and checkable. */
  function BytecodeFuel(c: Code, inp: Input): nat {
    (4 * |c|) + 1 + (|NextStr(inp)| * (1 + 4 * |c|))
  }

  // Coq: matchres
  /** The result of running the VM to completion: `Finished(res)` if a `PikeVmState.PVS_final?` state
      was reached (`res` is the match, or `None` for no match), or `OutOfFuel` if the loop ran out of
      steps first. */
  datatype MatchRes = OutOfFuel | Finished(res: Option<Leaf>)

  // Coq: getres
  /** Reads the `MatchRes` off a `PikeVmState`: `Finished` if it is final, `OutOfFuel` otherwise. */
  function GetRes(pvs: PikeVmState): MatchRes {
    match pvs case PVS_final(best) => Finished(best) case _ => OutOfFuel
  }

  // Coq: pike_vm_match — the executable PikeVM.
  /** The top-level executable matcher: compiles `r` (`NFA.Compilation`), runs the VM loop from the
      initial state with `BytecodeFuel`, and reports the outcome. This is "run the regex on the
      string" as a plain function. */
  function PikeVmMatch(rer: RegExpRecord, r: Regex, inp: Input): MatchRes {
    var code := Compilation(r);
    GetRes(PikeVmLoop(code, rer, PikeVmInitialState(inp), BytecodeFuel(code, inp)))
  }

  // Coq: final_state
  /** Whether `pvs` is a `PikeVmState.PVS_final?` state (the loop has nothing left to do). */
  predicate FinalState(pvs: PikeVmState) { pvs.PVS_final? }

  // Coq: func_step_correct
  /** `PikeVmFuncStep` agrees with the relational `PikeVM.PikeVmStep`: either it produced a genuine
      step, or `pvs1` was already final (in which case the function is a no-op and there is no step
      to relate). */
  lemma FuncStepCorrect(c: Code, rer: RegExpRecord, pvs1: PikeVmState, pvs2: PikeVmState)
    requires PikeVmFuncStep(c, rer, pvs1) == pvs2
    ensures PikeVmStep(c, rer, pvs1, pvs2) || FinalState(pvs1)
  {}

  // Coq: func_step_not_final
  /** Specialization of `FuncStepCorrect` to a non-final `PVS(...)` state: `PikeVmFuncStep` always
      produces a genuine `PikeVM.PikeVmStep` from it (no need to consider the already-final case). */
  lemma FuncStepNotFinal(c: Code, rer: RegExpRecord, inp: Input, active: seq<Thread>, best: Option<Leaf>, blocked: seq<Thread>, seen: SeenPcs)
    ensures PikeVmStep(c, rer, PVS(inp, active, best, blocked, seen), PikeVmFuncStep(c, rer, PVS(inp, active, best, blocked, seen)))
  {}

  // Coq: loop_trc
  /** A `PikeVmLoop` run is a valid instance of `Correctness.TrcPikeVm` (the relational
      transitive-reflexive closure) — i.e. the executable loop is faithful to the small-step
      semantics it is computing. */
  lemma LoopTrc(c: Code, rer: RegExpRecord, pvs1: PikeVmState, pvs2: PikeVmState, fuel: nat)
    requires PikeVmLoop(c, rer, pvs1, fuel) == pvs2
    ensures TrcPikeVm(c, rer, pvs1, pvs2)
    decreases fuel
  {
    match pvs1
    case PVS_final(_) =>
      assert pvs2 == pvs1;
    case PVS(inp, active, best, blocked, seen) =>
      if fuel == 0 {
        assert pvs2 == pvs1;
      } else {
        var mid := PikeVmFuncStep(c, rer, pvs1);
        FuncStepNotFinal(c, rer, inp, active, best, blocked, seen);  // PikeVmStep(pvs1, mid)
        LoopTrc(c, rer, mid, pvs2, fuel - 1);                        // TrcPikeVm(mid, pvs2)
        // hence TrcPikeVm(pvs1, pvs2) with witness mid
      }
  }

  // Coq: pike_vm_match_correct
  /** If the executable `PikeVmMatch` finishes with `result`, that result is reachable via
      `Correctness.TrcPikeVm` from the initial state — connecting the runnable function to the
      relational correctness theorems (`Correctness.PikeVmCorrect`). */
  lemma PikeVmMatchCorrect(rer: RegExpRecord, r: Regex, inp: Input, result: Option<Leaf>)
    requires PikeVmMatch(rer, r, inp) == Finished(result)
    ensures TrcPikeVm(Compilation(r), rer, PikeVmInitialState(inp), PVS_final(result))
  {
    var code := Compilation(r);
    var fuel := BytecodeFuel(code, inp);
    var final := PikeVmLoop(code, rer, PikeVmInitialState(inp), fuel);
    assert GetRes(final) == Finished(result);
    assert final == PVS_final(result);
    LoopTrc(code, rer, PikeVmInitialState(inp), final, fuel);
  }
}
