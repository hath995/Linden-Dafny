// Lookaround campaign (L1), oracle theorem part C2: the configuration graph
// of a build sweep.
//
// For classified build code (no oracle reads, no CheckNullable — see
// CompileToWriteClassified), an executing thread's CONTROL FLOW depends only
// on (pc, exit_allowed, cp): registers are written but never read, and every
// branch tests either the instruction payload, the exit flag, the anchor
// context at cp, or the consumed character. So the run explores exactly the
// reachable part of a register-free configuration graph, and the Pike
// processed-set dedup — which drops duplicate (pc, exit_allowed) threads,
// losing only their registers — preserves reachability.
//
// ReachF is that graph's reachability predicate for a FORWARD run started at
// pc 0 (the shape of every L1 lookbehind build pass: FBuildLids runs
// compile_to_write(lazy_prefix(body), lid) forward from init_cp = 0). The
// oracle-correctness characterization to be proved against it:
//
//   view_get_oracle(ov', cp, lid) == view_get_oracle(ov, cp, lid)
//     || exists pc, eb :: ReachF(c, str, 0, pc, eb, cp)
//                         && get_instr(c, pc) == WriteOracle(lid)
//
// (soundness: every write comes from a live thread, whose config is
// reachable; completeness: the sweep processes every reachable config —
// the Pike worklist argument at existence level, next up).
include "OracleSweep.dfy"

/** The register-free configuration graph of a (Forward) build sweep:
    epsilon and consume edges over configurations `(pc, exit_allowed, cp)`,
    and its reachability predicate `ReachF`. */
module LindenElkOracleReach {
  import opened Std.Wrappers
  import AI = ArrayInterp
  import RB = Bytecode
  import LOr = Oracle
  import LAnc = Anchors
  import RC = Charclasses
  import OS = LindenElkOracleSweep

  /** The character context a Forward run holds at position `cp`. */
  function CtxAt(str: string, cp: int): LAnc.char_context {
    AI.cp_context(cp, str, LAnc.Forward)
  }

  /** One epsilon edge at position `cp`: configuration `(pc, eb)` steps to
      `(pc2, eb2)` without consuming. Mirrors `FAdvanceEpsilon`'s cases for
      classified code; oracle and cdn instructions have no edges (the sweep
      lemmas exclude them), and `Accept`/`WriteOracle`/`Fail`/failed checks
      are terminal. */
  ghost predicate EpsEdge(c: RB.code, str: string, cp: int, pc: nat, eb: bool, pc2: nat, eb2: bool) {
    match RB.get_instr(c, pc)
    case Jmp(x) => x >= 0 && pc2 == x && eb2 == eb
    case Fork(x, y) => ((x >= 0 && pc2 == x) || (y >= 0 && pc2 == y)) && eb2 == eb
    case SetRegisterToCP(_) => pc2 == pc + 1 && eb2 == eb
    case SetQuantToClock(_, _) => pc2 == pc + 1 && eb2 == eb
    case BeginLoop => pc2 == pc + 1 && eb2 == false
    case EndLoop => eb && pc2 == pc + 1 && eb2 == eb
    case AnchorAssertion(a) =>
      LAnc.is_satisfied(a, CtxAt(str, cp), LAnc.Forward) && pc2 == pc + 1 && eb2 == eb
    case _ => false
  }

  /** The consume edge out of `(pc, eb)` at position `cp`: the blocked thread
      survives iff the character at `cp` meets its expectation; its successor
      is `(pc + 1, true)` at `cp + 1` (consuming re-arms the exit flag). */
  ghost predicate ConsumeEdge(c: RB.code, str: string, cp: int, pc: nat) {
    match RB.get_instr(c, pc)
    case Consume(ce) => RC.is_accepted(AI.get_char(str, cp), ce)
    case _ => false
  }

  /** Reachable configurations of the Forward run of `c` over `str` started
      at pc 0, position `cp0`, with the initial thread's cleared exit flag
      (`init_thread` starts `exit_allowed == false`). */
  least predicate ReachF(c: RB.code, str: string, cp0: int, pc: nat, eb: bool, cp: int) {
    (pc == 0 && eb == false && cp == cp0)
    || (exists pc1: nat, eb1: bool ::
          ReachF(c, str, cp0, pc1, eb1, cp) && EpsEdge(c, str, cp, pc1, eb1, pc, eb))
    || (eb == true && pc > 0
        && (ReachF(c, str, cp0, pc - 1, false, cp - 1) || ReachF(c, str, cp0, pc - 1, true, cp - 1))
        && ConsumeEdge(c, str, cp - 1, pc - 1))
  }

  /** The target of the sweep characterization: some reachable configuration
      at `cp` sits on a `WriteOracle(lid)` — the abstract statement of "the
      build sweep records a bit at `cp`". */
  ghost predicate ReachesWrite(c: RB.code, str: string, cp0: int, lid: int, cp: int) {
    exists pc: nat, eb: bool ::
      ReachF(c, str, cp0, pc, eb, cp) && RB.get_instr(c, pc) == RB.WriteOracle(lid)
  }

  /** Reachability only visits positions at or after the start (Forward run) —
      a sanity bound used to keep cp arithmetic honest downstream. */
  least lemma ReachFGeStart(c: RB.code, str: string, cp0: int, pc: nat, eb: bool, cp: int)
    requires ReachF(c, str, cp0, pc, eb, cp)
    ensures cp >= cp0
  {
  }
}
