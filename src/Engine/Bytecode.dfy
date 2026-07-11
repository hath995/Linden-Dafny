// Port of bytecode.ml
// The bytecode the VM executes in lockstep (Thompson simulation).
module Bytecode {
  import opened Charclasses
  import opened RegElkRegex

  // NOTE: `label` is a reserved keyword in Dafny, so the OCaml `label`/`register`
  // synonyms become `Label`/`Register` here.
  type Label = int     // index into the instruction list
  type Register = int  // capture register

  // when the next label isn't specified, control falls through to pc+1.
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
  type code = seq<instruction>

  // Total read: an out-of-range pc yields Fail (kills the thread), which is
  // memory-safe. In practice pc stays in range during simulation.
  function get_instr(c: code, pc: Label): instruction {
    if 0 <= pc < |c| then c[pc] else Fail
  }

  function size(c: code): int { |c| }

  // * Bytecode Properties: counting epsilon transitions
  function nb_epsilon_transition(i: instruction): int {
    match i
    case Fork(_, _) => 2
    case Jmp(_) => 1
    case CheckOracle(_) => 1
    case NegCheckOracle(_) => 1
    case CheckNullable(_) => 1
    case _ => 0
  }

  function nb_epsilon(c: code): int
    decreases |c|
  {
    if |c| == 0 then 0
    else nb_epsilon_transition(c[0]) + nb_epsilon(c[1..])
  }
}
