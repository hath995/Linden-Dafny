// Port of bytecode.ml
// The bytecode the VM executes in lockstep (Thompson simulation).
/** The instruction set for the Thompson-style bytecode VM: a compiled `code`
    sequence that the engine's threads execute in lockstep to match a regex. */
module Bytecode {
  import opened Charclasses
  import opened RegElkRegex

  // NOTE: `label` is a reserved keyword in Dafny, so the OCaml `label`/`register`
  // synonyms become `Label`/`Register` here.
  /** An instruction index (offset into a `code` sequence). */
  type Label = int     // index into the instruction list
  /** A capture register index, holding a current-position offset written by
      `SetRegisterToCP`. */
  type Register = int  // capture register

  // when the next label isn't specified, control falls through to pc+1.
  /** One VM instruction.

      - `Consume(ce)` — advance past the current character if it matches `ce`,
        else kill the thread.
      - `Accept` — the thread has found a match.
      - `Jmp(jl)` — unconditional jump.
      - `Fork(fl1, fl2)` — spawn two threads, `fl1` with priority over `fl2`.
      - `SetRegisterToCP(reg)` — record the current position into register `reg`.
      - `SetQuantToClock(sq, sb)` — mark quantifier `sq`'s iteration on the
        clock; `sb` flags a nulled `+`.
      - `CheckOracle(col)` / `NegCheckOracle(ncl)` — consult the lookaround
        oracle at the current position, killing the thread on a negative (resp.
        positive) answer.
      - `WriteOracle(wol)` — on a match, record it in the oracle at the current
        position.
      - `BeginLoop` / `EndLoop` — bracket a quantifier's loop body, to forbid an
        epsilon-only (non-consuming) iteration.
      - `CheckNullable(cnq)` — checks that a `+` loop's body was nullable.
      - `AnchorAssertion(aa)` — checks anchor `aa` at the current position.
      - `Fail` — kills the current thread unconditionally. */
  datatype instruction =
    | Consume(ce: char_expectation)
    | Accept
    | Jmp(jl: Label)
    | Fork(fl1: Label, fl2: Label)
    | SetRegisterToCP(reg: Register)
    // last iteration of a quantifier; bool indicates a nulled +
    | SetQuantToClock(sq: quantid, sb: bool)
    | CheckOracle(col: lookid)    // checks oracle at CP, kills thread on failure
    | NegCheckOracle(ncl: lookid) // same, expects a negative answer
    | WriteOracle(wol: lookid)    // on a match, write to the oracle at CP
    | BeginLoop                   // start of loop (counter to forbid epsilon-only exit)
    | EndLoop                     // end of loop (fails if started without consuming)
    | CheckNullable(cnq: quantid) // checks that a + is nullable
    | AnchorAssertion(aa: anchor) // checks an anchor
    | Fail                        // kills the current thread

  // O(1) random access needed (each thread reads at a different pc).
  /** A compiled instruction sequence, as produced by `Compiler` and executed
      by the `Interpreter`/engine, indexed by `Label`. */
  type code = seq<instruction>

  // Total read: an out-of-range pc yields Fail (kills the thread), which is
  // memory-safe. In practice pc stays in range during simulation.
  /** Total read of the instruction at `pc`: out-of-range `pc` yields `Fail`
      (safely killing the thread) instead of being undefined. */
  function get_instr(c: code, pc: Label): instruction {
    if 0 <= pc < |c| then c[pc] else Fail
  }

  function size(c: code): int { |c| }

  // * Bytecode Properties: counting epsilon transitions
  /** How many epsilon (non-consuming) outgoing transitions instruction `i`
      has; used to reason about the bytecode's epsilon-transition structure. */
  function nb_epsilon_transition(i: instruction): int {
    match i
    case Fork(_, _) => 2
    case Jmp(_) => 1
    case CheckOracle(_) => 1
    case NegCheckOracle(_) => 1
    case CheckNullable(_) => 1
    case _ => 0
  }

  /** Total count of epsilon transitions across every instruction in `c`. */
  function nb_epsilon(c: code): int
    decreases |c|
  {
    if |c| == 0 then 0
    else nb_epsilon_transition(c[0]) + nb_epsilon(c[1..])
  }
}
