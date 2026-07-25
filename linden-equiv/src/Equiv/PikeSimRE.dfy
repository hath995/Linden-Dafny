// Phase 4b (final assembly): the FULL simulation invariant — PikeInvRE
// strengthened with the three engine backbones (clock bound, register wf,
// capture-value bound) and the per-thread positional invariant (NestTopRE).
// This is the exact package InvariantPreservationRE threads through
// FAdvanceEpsilon: every hypothesis of every write-site discharge lemma is a
// conjunct here or follows from one.
//
// Blocked threads carry their positional fact at pc+1 (the resume point),
// matching BlockedRepRE's convention — the Consume advance edge is applied at
// block time, when the registers are frozen.
include "NestInv.dfy"
include "ClockMono.dfy"

/** The final assembly of the Phase 4b invariant-preservation proof:
    `PikeInvFullRE` bundles `PikeInvRE` with the clock/register/capture
    backbones (`ClockMono`) and the per-thread positional invariant
    (`NestInv`), and `InvariantPreservationRE` / `FindMatchSimRE` show the
    RegElk PikeVM's execution (`FAdvanceEpsilon`/`FFindMatch`) simulates the
    Linden `PikeTree` step relation while preserving it — the capstone
    linking RegElk's engine to Linden's tree semantics. */
module LindenElkPikeSim {
  import opened Std.Wrappers
  import R = RegElkRegex
  import RB = Bytecode
  import CP = Compiler
  import NR = LindenElkNfaRep
  import AI = ArrayInterp
  import AReg = Array_Regs
  import LG = Groups
  import LT = Tree
  import LW = WarblreRegExpRecord
  import LC = Chars
  import LS = Semantics
  import BS = BooleanSemantics
  import PT = PikeTree
  import AR = LindenElkActionsRep
  import TT = LindenElkTreeThread
  import T = LindenElkTranslate
  import PS = PikeSubset
  import ATR = LindenElkActionsTreeRep
  import PIV = LindenElkPikeInv
  import NI = LindenElkNestInv
  import CM = LindenElkClockMono
  import SS = SeenSets
  import TR = LindenElkTreeRep
  import GS = LindenElkGenStep
  import TREP = LindenElkTreeRep
  import RC = Charclasses
  import WP = WarblrePrimitives
  import LOr = Oracle
  import LAnc = Anchors
  import LCdn = Cdn

  // =========================================================================
  // Reflexive-transitive closure of PikeTreeStep (local copy; connected to
  // Linden's TrcPikeTree at the outer-assembly layer).
  // =========================================================================
  /** Local reflexive-transitive closure of `PikeTree.PikeTreeStep`, used to
      record that the VM's `FAdvanceEpsilon`/`FFindMatch` execution
      corresponds to zero-or-more steps of the tree machine. */
  least predicate TrcRE(s1: PT.PikeTreeState, s2: PT.PikeTreeState) {
    s1 == s2 || (exists mid :: PT.PikeTreeStep(s1, mid) && TrcRE(mid, s2))
  }

  /** `TrcRE` is reflexive. */
  lemma TrcRefl(s: PT.PikeTreeState)
    ensures TrcRE(s, s)
  {}

  /** Prepending one `PikeTreeStep` to a `TrcRE` chain keeps it a `TrcRE` chain. */
  lemma TrcCons(s1: PT.PikeTreeState, mid: PT.PikeTreeState, s2: PT.PikeTreeState)
    requires PT.PikeTreeStep(s1, mid)
    requires TrcRE(mid, s2)
    ensures TrcRE(s1, s2)
  {}

  /** Appending one `PikeTreeStep` to the end of a `TrcRE` chain keeps it a
      `TrcRE` chain — the "snoc" companion to `TrcCons`. */
  least lemma TrcSnoc(s1: PT.PikeTreeState, mid: PT.PikeTreeState, s2: PT.PikeTreeState)
    requires TrcRE(s1, mid)
    requires PT.PikeTreeStep(mid, s2)
    ensures TrcRE(s1, s2)
  {
    if s1 == mid {
      TrcCons(s1, s2, s2);
    } else {
      var z :| PT.PikeTreeStep(s1, z) && TrcRE(z, mid);
      TrcSnoc(z, mid, s2);
      TrcCons(s1, z, s2);
    }
  }

  // The static side-condition package every preservation case carries.
  /** The compile-time side conditions every preservation lemma assumes: `re`
      is in the supported star fragment, uniquely captures/quantifies,
      translates soundly (`TransWf`), `qm` is consistent (`QmapOk`), and
      `code` is a well-formed compilation of `re` ending in `Accept`. */
  ghost predicate StaticOkRE(qm: AR.QMap, re: R.regex, code: RB.code, endl: nat) {
    NR.PlusFragmentRE(re) && PIV.CapUnique(re) && PIV.QuantUnique(re)
    && T.TransWf(re) && AR.QmapOk(re, qm)
    && NR.NfaRepRE(re, code, 0, endl)
    && NR.GetPcRE(code, endl) == Some(RB.Accept)
    && |code| == endl + 1
    && PIV.StutterTameRE(code)
  }

  // Inside a plus-fragment block there is no oracle instruction: the fragment
  // has no lookaround node, so the compiler emits no CheckOracle /
  // NegCheckOracle / WriteOracle / CheckNullable. Packaged against
  // `StaticOkRE`'s shape (Accept sits at `endl`, so any pc carrying another
  // instruction is strictly inside the block).
  /** A `StaticOkRE` code carries no oracle (or `CheckNullable`) instruction at
      any pc other than the final `Accept` — the plus fragment compiles none.
      The lookaround campaign's simulation cases are vacuous until the gate
      widens past `NR.PlusFragmentRE`. */
  lemma NoOracleInstrAt(re: R.regex, code: RB.code, endl: nat, pc: nat)
    requires NR.PlusFragmentRE(re)
    requires NR.NfaRepRE(re, code, 0, endl)
    requires NR.GetPcRE(code, endl) == Some(RB.Accept)
    requires |code| == endl + 1
    requires pc < |code|
    requires NR.GetPcRE(code, pc).Some?
    requires var i := NR.GetPcRE(code, pc).value;
      i.CheckOracle? || i.NegCheckOracle? || i.WriteOracle? || i.CheckNullable?
    ensures false
  {
    AR.PlusFragmentLookFree(re);
    assert pc != endl;                        // Accept is none of those
    assert pc < endl;                         // |code| == endl + 1
    NR.NoOracleInstrRE(re, code, 0, endl, pc);
  }

  // Register files sized to cover every compiled write.
  /** The register files (`ncap`/`nlook`/`nquant`) are sized large enough to
      hold every register `re`'s compilation can write. */
  ghost predicate SizesOkRE(re: R.regex, ncap: int, nlook: int, nquant: int) {
    ncap >= 2 * R.max_group(re) + 2 && nquant >= R.max_quant(re) + 1 && nlook >= 0
  }

  // The ea-at-backfork exclusion: a thread that may not exit never sits at a
  // Cold pc (one that reaches a do-while's backward fork zero-width), so at
  // the fork itself exit_allowed always holds and tr_plus applies. Reads and
  // reactivation re-arm the flag; BeginLoop mints false-threads only at loop
  // body heads, which are statically never Cold.
  /** Per-thread: `exit_allowed == false` implies the thread's pc is not Cold. */
  ghost predicate EaColdOkRE(code: RB.code, th: AI.Thread) {
    !th.exit_allowed && th.pc >= 0 ==> !NI.ColdRE(code, th.pc as nat)
  }

  /** ¬Cold steps across any single zero-width successor edge: were the
      successor Cold, the rule for `pc`'s instruction would make `pc` Cold. */
  lemma NotColdSucc(code: RB.code, pc: nat, pc2: nat)
    requires !NI.ColdRE(code, pc)
    requires match NR.GetPcRE(code, pc)
             case Some(Jmp(np)) => np >= 0 && pc2 == np as nat
             case Some(Fork(x, y)) => (x >= 0 && pc2 == x as nat) || (y >= 0 && pc2 == y as nat)
             case Some(SetQuantToClock(_, _)) => pc2 == pc + 1
             case Some(SetRegisterToCP(_)) => pc2 == pc + 1
             case Some(AnchorAssertion(_)) => pc2 == pc + 1
             case _ => false
    ensures !NI.ColdRE(code, pc2)
  {
    if NI.ColdRE(code, pc2) {
      var n: nat :| NI.ColdF(code, pc2, n);
      assert NI.ColdF(code, pc, n + 1);
    }
  }

  // =========================================================================
  // Backbone step frames: the three engine backbones plus the sign facts,
  // packaged, with one tiny lemma per successor-state shape. Kills the
  // per-case boilerplate in the preservation lemmas.
  // =========================================================================
  /** The three engine backbone facts bundled per VM state: register clocks
      bounded by the VM clock (`VmClocksLE`), registers well-formed
      (`VmRegsWf`), and capture values bounded (`VmCapsLE`), plus
      non-negativity of `clock`/`cp`. */
  ghost predicate BBOf(s: AI.VmState, ncap: int, nlook: int, nquant: int) {
    CM.VmClocksLE(s)
    && CM.VmRegsWf(s, ncap, nlook, nquant)
    && CM.VmCapsLE(s)
    && s.clock >= 0 && s.cp >= 0
  }

  // dropping the head thread
  /** `BBOf` survives dropping the head thread from `active` (used by the
      Skip/EndLoop-kill/Consume-drop cases). */
  lemma BBDropHead(s: AI.VmState, ncap: int, nlook: int, nquant: int)
    requires BBOf(s, ncap, nlook, nquant) && |s.active| > 0
    ensures BBOf(s.(active := s.active[1..]), ncap, nlook, nquant)
  {
    var s' := s.(active := s.active[1..]);
    forall t | t in s'.active ensures CM.ThreadClocksLE(t, s'.clock)
                                   && CM.ThreadRegsWf(t, ncap, nlook, nquant)
                                   && CM.RegsValsLE(t.capture_regs, s'.cp) {
      assert t in s.active;
    }
  }

  // the clock tick + processed add (FAdvanceEpsilon's s1)
  /** `BBOf` survives the clock tick and `processed`-set update that opens
      every non-skip preservation case. */
  lemma BBTick(s: AI.VmState, s1: AI.VmState, ncap: int, nlook: int, nquant: int)
    requires BBOf(s, ncap, nlook, nquant)
    requires |s.active| > 0
    requires s1 == s.(clock := s.clock + 1,
                      processed := AI.bpc_add(s.processed, s.active[0].pc, s.active[0].exit_allowed))
    ensures BBOf(s1, ncap, nlook, nquant)
  {
    forall t | t in s1.active ensures CM.ThreadClocksLE(t, s1.clock) {
      assert t in s.active;
      CM.ThreadClocksLEMono(t, s.clock, s1.clock);
    }
    forall tb | tb in s1.blocked ensures CM.ThreadClocksLE(tb.0, s1.clock) {
      assert tb in s.blocked;
      CM.ThreadClocksLEMono(tb.0, s.clock, s1.clock);
    }
    if s1.bestmatch.Some? { CM.ThreadClocksLEMono(s1.bestmatch.value, s.clock, s1.clock); }
  }

  // replacing the head with one successor thread
  /** `BBOf` survives replacing the head thread with one successor whose own
      backbone facts hold (Jmp/BeginLoop/Open/Close/Reset/EndLoop-pass). */
  lemma BBReplaceHead(s1: AI.VmState, th': AI.Thread, ncap: int, nlook: int, nquant: int)
    requires BBOf(s1, ncap, nlook, nquant) && |s1.active| > 0
    requires CM.ThreadClocksLE(th', s1.clock)
    requires CM.ThreadRegsWf(th', ncap, nlook, nquant)
    requires CM.RegsValsLE(th'.capture_regs, s1.cp)
    ensures BBOf(s1.(active := [th'] + s1.active[1..]), ncap, nlook, nquant)
  {
    var s' := s1.(active := [th'] + s1.active[1..]);
    forall t | t in s'.active ensures CM.ThreadClocksLE(t, s'.clock)
                                   && CM.ThreadRegsWf(t, ncap, nlook, nquant)
                                   && CM.RegsValsLE(t.capture_regs, s'.cp) {
      if t != th' { assert t in s1.active; }
    }
  }

  // replacing the head with two successor threads (Fork)
  /** `BBOf` survives replacing the head thread with two successor threads
      (the `Fork` case). */
  lemma BBTwoHead(s1: AI.VmState, th1: AI.Thread, th2: AI.Thread, ncap: int, nlook: int, nquant: int)
    requires BBOf(s1, ncap, nlook, nquant) && |s1.active| > 0
    requires CM.ThreadClocksLE(th1, s1.clock) && CM.ThreadClocksLE(th2, s1.clock)
    requires CM.ThreadRegsWf(th1, ncap, nlook, nquant) && CM.ThreadRegsWf(th2, ncap, nlook, nquant)
    requires CM.RegsValsLE(th1.capture_regs, s1.cp) && CM.RegsValsLE(th2.capture_regs, s1.cp)
    ensures BBOf(s1.(active := [th1, th2] + s1.active[1..]), ncap, nlook, nquant)
  {
    var s' := s1.(active := [th1, th2] + s1.active[1..]);
    forall t | t in s'.active ensures CM.ThreadClocksLE(t, s'.clock)
                                   && CM.ThreadRegsWf(t, ncap, nlook, nquant)
                                   && CM.RegsValsLE(t.capture_regs, s'.cp) {
      if t != th1 && t != th2 { assert t in s1.active; }
    }
  }

  // moving the head to the blocked list (Consume)
  /** `BBOf` survives moving the head thread to the blocked list (the
      `Consume` case). */
  lemma BBBlockHead(s1: AI.VmState, ce: RC.char_expectation, ncap: int, nlook: int, nquant: int)
    requires BBOf(s1, ncap, nlook, nquant) && |s1.active| > 0
    ensures BBOf(s1.(blocked := [(s1.active[0], ce)] + s1.blocked,
                     isblocked := AI.pc_add(s1.isblocked, s1.active[0].pc),
                     active := s1.active[1..]),
                 ncap, nlook, nquant)
  {
    var th := s1.active[0];
    var s' := s1.(blocked := [(th, ce)] + s1.blocked,
                  isblocked := AI.pc_add(s1.isblocked, th.pc),
                  active := s1.active[1..]);
    forall t | t in s'.active ensures CM.ThreadClocksLE(t, s'.clock)
                                   && CM.ThreadRegsWf(t, ncap, nlook, nquant)
                                   && CM.RegsValsLE(t.capture_regs, s'.cp) {
      assert t in s1.active;
    }
    forall tb | tb in s'.blocked ensures CM.ThreadClocksLE(tb.0, s'.clock)
                                      && CM.ThreadRegsWf(tb.0, ncap, nlook, nquant)
                                      && CM.RegsValsLE(tb.0.capture_regs, s'.cp) {
      if tb != (th, ce) { assert tb in s1.blocked; } else { assert tb.0 == th && th in s1.active; }
    }
  }

  // Accept: empty the active list, record the head as best
  /** `BBOf` survives emptying `active` and recording the head as
      `bestmatch` (the `Accept` case). */
  lemma BBAccept(s1: AI.VmState, ncap: int, nlook: int, nquant: int)
    requires BBOf(s1, ncap, nlook, nquant) && |s1.active| > 0
    ensures BBOf(s1.(active := [], bestmatch := Some(s1.active[0])), ncap, nlook, nquant)
  {
    assert s1.active[0] in s1.active;
  }

  // Per-thread positional fact: the thread's pc sits inside (or at the Accept
  // terminator of) the compiled block, with the nesting claims over its OWN
  // register clocks.
  /** A thread's positional invariant: its `pc` lies within the compiled
      block and `NestTopRE` holds of its own register clocks — the per-thread
      instance of the nesting invariant threaded by `PikeInvFullRE`. */
  ghost predicate ThreadNestRE(re: R.regex, code: RB.code, endl: nat, pc: int, th: AI.Thread)
    requires NR.NfaRepRE(re, code, 0, endl)
  {
    0 <= pc <= endl
    && NI.NestTopRE(re, code, endl, pc as nat, th.capture_regs.a_clk, th.quant_regs.a_clk)
  }

  // MxAt thresholds are always either the mx parameter or a stored quant
  // clock, so the clock backbone bounds them: a fresh stamp S+1 beats every
  // threshold. Discharges `clk >= MxAtGid/MxAtQid` at the write sites.
  /** Every stored register clock is `<= S`, so a fresh stamp `S+1` beats
      `PIV.MxAtGid`'s threshold for any group id — discharges the
      `clk >= MxAtGid` obligation at Open/Close write sites. */
  lemma MxAtGidLE(re: R.regex, cc: seq<int>, qc: seq<int>, mx: int, gid: nat, S: int)
    requires gid in PIV.CapIds(re)
    requires mx <= S
    requires forall k :: AI.get_idx(qc, k) <= S
    ensures PIV.MxAtGid(re, cc, qc, mx, gid) <= S
    decreases re
  {
    match re
    case Re_alt(r1, r2) =>
      if gid in PIV.CapIds(r1) { MxAtGidLE(r1, cc, qc, mx, gid, S); } else { MxAtGidLE(r2, cc, qc, mx, gid, S); }
    case Re_con(r1, r2) =>
      if gid in PIV.CapIds(r1) { MxAtGidLE(r1, cc, qc, mx, gid, S); } else { MxAtGidLE(r2, cc, qc, mx, gid, S); }
    case Re_quant(nul, qid, q, r1) => MxAtGidLE(r1, cc, qc, AI.get_idx(qc, qid), gid, S);
    case Re_capture(cid, r1) =>
      if cid >= 0 && (cid as nat) == gid {} else { MxAtGidLE(r1, cc, qc, mx, gid, S); }
    case Re_lookaround(lid, l, r1) => MxAtGidLE(r1, cc, qc, mx, gid, S);
  }

  /** The quantifier-clock analogue of `MxAtGidLE`: discharges
      `clk >= MxAtQid` at Reset write sites. */
  lemma MxAtQidLE(re: R.regex, cc: seq<int>, qc: seq<int>, mx: int, qid: nat, S: int)
    requires qid in PIV.QuantIds(re)
    requires mx <= S
    requires forall k :: AI.get_idx(qc, k) <= S
    ensures PIV.MxAtQid(re, cc, qc, mx, qid) <= S
    decreases re
  {
    match re
    case Re_alt(r1, r2) =>
      if qid in PIV.QuantIds(r1) { MxAtQidLE(r1, cc, qc, mx, qid, S); } else { MxAtQidLE(r2, cc, qc, mx, qid, S); }
    case Re_con(r1, r2) =>
      if qid in PIV.QuantIds(r1) { MxAtQidLE(r1, cc, qc, mx, qid, S); } else { MxAtQidLE(r2, cc, qc, mx, qid, S); }
    case Re_quant(nul, qid0, q, r1) =>
      if qid0 >= 0 && (qid0 as nat) == qid {} else { MxAtQidLE(r1, cc, qc, AI.get_idx(qc, qid0), qid, S); }
    case Re_capture(cid, r1) => MxAtQidLE(r1, cc, qc, mx, qid, S);
    case Re_lookaround(lid, l, r1) => MxAtQidLE(r1, cc, qc, mx, qid, S);
  }

  // At a Consume pc the tree is ea-INDEPENDENT: tr_read pins the whole node by
  // (ce, inp) and the continuation at (pc+1, nextinp, TRUE) — the loop flag
  // only matters at EndLoop nodes. Lets a dropped blocked thread (different
  // exit_allowed than the first blocker at that pc) reuse the first blocker's
  // seen-tree for pts_skip.
  /** At a `Consume` pc the represented tree only depends on `(ce, inp)`, not
      the loop flag (`ea`) — so two threads at the same `Consume` pc with
      different flags see the same tree. Lets a dropped (dedup'd) blocked
      thread reuse the first blocker's already-`seen` tree. */
  lemma ConsumeTreeEaIndep(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                           t1: LT.Tree, t2: LT.Tree, pc: nat, ea1: bool, ea2: bool)
    requires !rer.multiline
    requires TT.TreeThreadRE(rer, qm, code, inp, t1, pc, ea1)
    requires TT.TreeThreadRE(rer, qm, code, inp, t2, pc, ea2)
    requires NR.GetPcRE(code, pc).Some? && NR.GetPcRE(code, pc).value.Consume?
    ensures t1 == t2
  {
    TT.TreeThreadTreeRepRE(rer, qm, code, inp, t1, pc, ea1);
    TT.TreeThreadTreeRepRE(rer, qm, code, inp, t2, pc, ea2);
    var ce := NR.GetPcRE(code, pc).value.ce;
    // At a Consume pc only tr_read / tr_readfail can apply.
    if AR.ReadCharE(ce, inp).Some? {
      var (c, nextinp) := AR.ReadCharE(ce, inp).value;
      assert t1.Read? && t1.c == c && TR.TreeRepRE(qm, t1.t, code, pc + 1, nextinp, true);
      assert t2.Read? && t2.c == c && TR.TreeRepRE(qm, t2.t, code, pc + 1, nextinp, true);
      TR.TreeRepDetermRE(qm, code, pc + 1, nextinp, true, t1.t, t2.t);
    } else {
      assert t1 == LT.Mismatch && t2 == LT.Mismatch;
    }
  }

  // =========================================================================
  // Step helper: the OPEN case. At a SetRegisterToCP(even) instruction the
  // tree emits GroupActionT(Open(gid), _); the VM write tracks GMOpen, the
  // positional invariant advances, and the per-thread backbone facts carry.
  // Every hypothesis is a conjunct of PikeInvFullRE or a static compile fact.
  // =========================================================================
  /** The bundled per-thread step lemma for the `Open` case: pins the tree
      step to `GroupActionT(Open(gid), _)`, shows the register write denotes
      `GMOpen`, and carries the positional/backbone invariants to `pc+1` —
      the single fact `PreserveOpenCase` builds on. */
  lemma OpenStepThreadRE(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
                         inp: LC.Input, t: LT.Tree, gm: LG.GroupMap, th: AI.Thread, pc: nat,
                         sreg: int, cp: int, S: int)
    // static side conditions
    requires NR.PlusFragmentRE(re) && PIV.CapUnique(re)
    requires !rer.multiline
    requires NR.NfaRepRE(re, code, 0, endl)
    requires NR.GetPcRE(code, endl) == Some(RB.Accept)
    // the site
    requires th.pc >= 0 && pc == th.pc as nat && pc <= endl
    requires NR.GetPcRE(code, pc) == Some(RB.SetRegisterToCP(sreg))
    requires sreg % 2 == 0
    // per-thread invariant conjuncts
    requires TT.TreeThreadRE(rer, qm, code, inp, t, pc, th.exit_allowed)
    requires PIV.ThreadTracksGm(re, th, gm)
    requires NI.NestTopRE(re, code, endl, pc, th.capture_regs.a_clk, th.quant_regs.a_clk)
    requires CM.ThreadClocksLE(th, S)
    requires PIV.CapRegWf(th.capture_regs)
    requires CM.RegsValsLE(th.capture_regs, cp)
    requires |th.capture_regs.a_cp| >= 2 * R.max_group(re) + 2
    requires cp >= 0 && S >= 0
    // the tree step is an Open of the register's group
    ensures t.GroupActionT? && t.g.Open? && sreg == CP.start_reg(t.g.g as int)
    ensures TT.TreeThreadRE(rer, qm, code, inp, t.t, pc + 1, th.exit_allowed)
    // the successor thread tracks GMOpen
    ensures var caps' := AReg.set_reg(th.capture_regs, sreg, Some(cp), S + 1);
      t.GroupActionT? && t.g.Open? ==>
        PIV.GmOfLive(re, caps', th.look_regs, th.quant_regs) == LG.GMOpen(cp as nat, t.g.g, gm)
    // positional invariant at pc+1 with the written clocks
    ensures var caps' := AReg.set_reg(th.capture_regs, sreg, Some(cp), S + 1);
      pc + 1 <= endl && NI.NestTopRE(re, code, endl, pc + 1, caps'.a_clk, th.quant_regs.a_clk)
    // per-thread backbone facts carry to the successor
    ensures var caps' := AReg.set_reg(th.capture_regs, sreg, Some(cp), S + 1);
      CM.RegsClocksLE(caps', S + 1) && PIV.CapRegWf(caps') && CM.RegsValsLE(caps', cp)
      && |caps'.a_cp| == |th.capture_regs.a_cp| && |caps'.a_clk| == |th.capture_regs.a_clk|
  {
    var caps := th.capture_regs;
    var cc := caps.a_clk;
    var qc := th.quant_regs.a_clk;
    var ea := th.exit_allowed;
    var clk := S + 1;

    // The site is not a stutter and not the Accept terminator.
    assert !TT.StuttersRE(pc, code);
    assert pc < endl;

    // Tree step: StepSpec pins an Open (a Close would use the odd end reg).
    GS.GenStepRE(rer, qm, code, inp, t, pc, ea);
    assert t.GroupActionT? && !t.g.Reset?;
    if t.g.Close? {
      assert sreg == CP.end_reg(t.g.g as int);
      assert sreg == 2 * (t.g.g as int) + 1;
      assert false;                                   // parity
    }
    assert t.g.Open?;
    var gid: nat := t.g.g;
    assert sreg == CP.start_reg(gid as int) == 2 * (gid as int);

    // Positional facts at the site.
    assert NI.NestInvRE(re, code, 0, endl, pc, cc, qc, -1);
    NI.NestInvOpenSite(re, code, 0, endl, pc, cc, qc, -1, gid);
    assert gid in PIV.CapIds(re);

    // Register bounds.
    NI.CapIdsLEMaxGroup(re);
    assert gid <= R.max_group(re);
    assert 0 <= sreg < |caps.a_cp|;
    assert |caps.a_cp| == |caps.a_clk|;               // CapRegWf

    // Backbone-derived clock facts.
    assert forall k :: AI.get_idx(cc, k) <= S;        // ThreadClocksLE
    assert forall k :: AI.get_idx(qc, k) <= S;
    MxAtGidLE(re, cc, qc, -1, gid, S);
    assert clk >= PIV.MxAtGid(re, cc, qc, -1, gid);
    assert clk > AI.get_idx(cc, CP.end_reg(gid as int));

    // The gm effect: exactly GMOpen.
    PIV.GmOfLiveOpenGMOpen(re, caps, th.look_regs, th.quant_regs, gid, cp, clk);
    var caps' := AReg.set_reg(caps, sreg, Some(cp), clk);
    assert caps' == AReg.set_reg(caps, CP.start_reg(gid as int), Some(cp), clk);
    assert PIV.GmOfLive(re, caps', th.look_regs, th.quant_regs)
        == LG.GMOpen(cp as nat, gid, PIV.GmOfLive(re, caps, th.look_regs, th.quant_regs));

    // Positional invariant advances across the write.
    assert caps'.a_clk == cc[sreg := clk];
    NI.NestInvOpenWrite(re, code, 0, endl, pc, cc, caps'.a_clk, qc, -1, sreg, clk);
    assert NI.NestTopRE(re, code, endl, pc + 1, caps'.a_clk, qc);

    // Backbone facts for the successor registers.
    assert CM.RegsClocksLE(caps, clk);                // <= S <= S+1
    CM.RegsClocksLESet(caps, sreg, Some(cp), clk, clk);
    PIV.CapRegWfSet(caps, sreg, cp, clk);
    CM.RegsValsLESet(caps, sreg, cp, clk, cp);
  }

  // =========================================================================
  // Step helper: the CLOSE case. At a SetRegisterToCP(odd) instruction the
  // tree emits GroupActionT(Close(gid), _). No positional hypotheses at all:
  // the gm effect is total (GmOfLiveCloseGMClose), the write is invariant-
  // neutral (odd slot), and the pc-move is a plain fall-through.
  // =========================================================================
  /** The `Close`-case analogue of `OpenStepThreadRE`: the write is
      invariant-neutral (odd register), so unlike Open it needs no positional
      hypothesis at all — the gm effect (`GMClose`) is total. */
  lemma CloseStepThreadRE(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
                          inp: LC.Input, t: LT.Tree, gm: LG.GroupMap, th: AI.Thread, pc: nat,
                          ereg: int, cp: int, S: int)
    requires NR.PlusFragmentRE(re) && PIV.CapUnique(re)
    requires !rer.multiline && PIV.QuantUnique(re)
    requires NR.NfaRepRE(re, code, 0, endl)
    requires NR.GetPcRE(code, endl) == Some(RB.Accept)
    requires th.pc >= 0 && pc == th.pc as nat && pc <= endl
    requires NR.GetPcRE(code, pc) == Some(RB.SetRegisterToCP(ereg))
    requires ereg % 2 == 1
    requires TT.TreeThreadRE(rer, qm, code, inp, t, pc, th.exit_allowed)
    requires PIV.ThreadTracksGm(re, th, gm)
    requires NI.NestTopRE(re, code, endl, pc, th.capture_regs.a_clk, th.quant_regs.a_clk)
    requires CM.ThreadClocksLE(th, S)
    requires PIV.CapRegWf(th.capture_regs)
    requires CM.RegsValsLE(th.capture_regs, cp)
    requires |th.capture_regs.a_cp| >= 2 * R.max_group(re) + 2
    requires cp >= 0 && S >= 0
    ensures t.GroupActionT? && t.g.Close? && ereg == CP.end_reg(t.g.g as int)
    ensures TT.TreeThreadRE(rer, qm, code, inp, t.t, pc + 1, th.exit_allowed)
    ensures var caps' := AReg.set_reg(th.capture_regs, ereg, Some(cp), S + 1);
      t.GroupActionT? && t.g.Close? ==>
        PIV.GmOfLive(re, caps', th.look_regs, th.quant_regs) == LG.GMClose(cp as nat, t.g.g, gm)
    ensures var caps' := AReg.set_reg(th.capture_regs, ereg, Some(cp), S + 1);
      pc + 1 <= endl && NI.NestTopRE(re, code, endl, pc + 1, caps'.a_clk, th.quant_regs.a_clk)
    ensures var caps' := AReg.set_reg(th.capture_regs, ereg, Some(cp), S + 1);
      CM.RegsClocksLE(caps', S + 1) && PIV.CapRegWf(caps') && CM.RegsValsLE(caps', cp)
      && |caps'.a_cp| == |th.capture_regs.a_cp| && |caps'.a_clk| == |th.capture_regs.a_clk|
  {
    var caps := th.capture_regs;
    var cc := caps.a_clk;
    var qc := th.quant_regs.a_clk;
    var ea := th.exit_allowed;
    var clk := S + 1;

    assert !TT.StuttersRE(pc, code);
    assert pc < endl;

    // Tree step: StepSpec pins a Close (an Open would use the even start reg).
    GS.GenStepRE(rer, qm, code, inp, t, pc, ea);
    assert t.GroupActionT? && !t.g.Reset?;
    if t.g.Open? {
      assert ereg == CP.start_reg(t.g.g as int);
      assert ereg == 2 * (t.g.g as int);
      assert false;                                   // parity
    }
    assert t.g.Close?;
    var gid: nat := t.g.g;
    assert ereg == CP.end_reg(gid as int) == 2 * (gid as int) + 1;

    // Register bounds via the instruction inventory.
    NI.CodeShapeAt(re, code, 0, endl, pc);
    var g0: nat :| g0 in PIV.CapIds(re)
      && (ereg == CP.start_reg(g0) || ereg == CP.end_reg(g0));
    assert ereg == CP.end_reg(g0) by {
      if ereg == CP.start_reg(g0) { assert ereg == 2 * (g0 as int); assert false; }
    }
    assert g0 == gid;                                 // 2*g0+1 == 2*gid+1
    NI.CapIdsLEMaxGroup(re);
    assert gid <= R.max_group(re);
    assert 0 <= ereg < |caps.a_cp|;
    assert |caps.a_cp| == |caps.a_clk|;               // CapRegWf

    // The gm effect: exactly GMClose (total — no positional hypotheses).
    assert forall k :: AI.get_idx(caps.a_clk, k) <= clk;   // <= S < S+1
    PIV.GmOfLiveCloseGMClose(re, caps, th.look_regs, th.quant_regs, gid, cp, clk);
    var caps' := AReg.set_reg(caps, ereg, Some(cp), clk);
    assert caps' == AReg.set_reg(caps, CP.end_reg(gid as int), Some(cp), clk);
    assert PIV.GmOfLive(re, caps', th.look_regs, th.quant_regs)
        == LG.GMClose(cp as nat, gid, PIV.GmOfLive(re, caps, th.look_regs, th.quant_regs));

    // Positional invariant: the odd write is a pure frame, then fall through.
    assert caps'.a_clk == cc[ereg := clk];
    assert forall j :: j % 2 == 0 ==> AI.get_idx(caps'.a_clk, j) == AI.get_idx(cc, j);
    assert NI.NestInvRE(re, code, 0, endl, pc, cc, qc, -1);
    NI.NestInvFrameOdd(re, code, 0, endl, pc, cc, caps'.a_clk, qc, -1);
    assert NI.StepEdgeRE(code, pc, pc + 1);
    NI.NestInvAdvance(re, code, 0, endl, pc, pc + 1, caps'.a_clk, qc, -1);
    assert NI.NestTopRE(re, code, endl, pc + 1, caps'.a_clk, qc);

    // Backbone facts for the successor registers.
    assert CM.RegsClocksLE(caps, clk);
    CM.RegsClocksLESet(caps, ereg, Some(cp), clk, clk);
    PIV.CapRegWfSet(caps, ereg, cp, clk);
    CM.RegsValsLESet(caps, ereg, cp, clk, cp);
  }

  // =========================================================================
  // Step helper: the RESET case. At a SetQuantToClock(qid, false) instruction
  // the tree emits GroupActionT(Reset(qm.quants[qid]), _); the stamp write tracks
  // GMReset and re-arms the body's staleness for free.
  // =========================================================================
  /** The `Reset`-case analogue of `OpenStepThreadRE`/`CloseStepThreadRE`:
      pins the tree step to `GroupActionT(Reset(qm.quants[qid]), _)` and shows the
      quantifier-clock stamp write denotes `GMReset`. */
  lemma ResetStepThreadRE(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
                          inp: LC.Input, t: LT.Tree, gm: LG.GroupMap, th: AI.Thread, pc: nat,
                          qid0: int, S: int)
    requires NR.PlusFragmentRE(re) && PIV.CapUnique(re)
    requires !rer.multiline && PIV.QuantUnique(re)
    requires T.TransWf(re) && AR.QmapOk(re, qm)
    requires NR.NfaRepRE(re, code, 0, endl)
    requires NR.GetPcRE(code, endl) == Some(RB.Accept)
    requires th.pc >= 0 && pc == th.pc as nat && pc <= endl
    requires NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(qid0, false))
    requires TT.TreeThreadRE(rer, qm, code, inp, t, pc, th.exit_allowed)
    requires PIV.ThreadTracksGm(re, th, gm)
    requires NI.NestTopRE(re, code, endl, pc, th.capture_regs.a_clk, th.quant_regs.a_clk)
    requires CM.ThreadClocksLE(th, S)
    requires PIV.CapRegWf(th.capture_regs)
    requires |th.quant_regs.a_clk| >= R.max_quant(re) + 1
    requires |th.quant_regs.a_cp| == |th.quant_regs.a_clk|
    requires S >= 0
    ensures t.GroupActionT? && t.g.Reset? && qid0 in qm.quants && qm.quants[qid0] == t.g.gl
    ensures TT.TreeThreadRE(rer, qm, code, inp, t.t, pc + 1, th.exit_allowed)
    ensures var quant' := AReg.set_reg(th.quant_regs, qid0, None, S + 1);
      t.GroupActionT? && t.g.Reset? ==>
        PIV.GmOfLive(re, th.capture_regs, th.look_regs, quant') == LG.GMReset(t.g.gl, gm)
    ensures var quant' := AReg.set_reg(th.quant_regs, qid0, None, S + 1);
      pc + 1 <= endl && NI.NestTopRE(re, code, endl, pc + 1, th.capture_regs.a_clk, quant'.a_clk)
    ensures var quant' := AReg.set_reg(th.quant_regs, qid0, None, S + 1);
      CM.RegsClocksLE(quant', S + 1)
      && |quant'.a_cp| == |th.quant_regs.a_cp| && |quant'.a_clk| == |th.quant_regs.a_clk|
  {
    var caps := th.capture_regs;
    var quant := th.quant_regs;
    var cc := caps.a_clk;
    var qc := quant.a_clk;
    var ea := th.exit_allowed;
    var clk := S + 1;

    assert !TT.StuttersRE(pc, code);
    assert pc < endl;

    // Tree step: StepSpec's SetQuantToClock clause pins the Reset.
    GS.GenStepRE(rer, qm, code, inp, t, pc, ea);
    assert t.GroupActionT? && t.g.Reset? && qid0 in qm.quants && qm.quants[qid0] == t.g.gl;

    // Register bounds via the instruction inventory (also gives qid0 >= 0).
    NI.CodeShapeAt(re, code, 0, endl, pc);
    assert qid0 >= 0 && (qid0 as nat) in PIV.QuantIds(re);
    var qid: nat := qid0 as nat;
    NI.QuantIdsLEMaxQuant(re);
    assert qid <= R.max_quant(re);
    assert 0 <= qid0 < |quant.a_clk|;

    // Positional facts at the site.
    assert NI.NestInvRE(re, code, 0, endl, pc, cc, qc, -1);
    NI.NestInvResetSite(re, code, 0, endl, pc, cc, qc, -1, qid);
    assert PIV.PathPresentQ(re, cc, qc, -1, qid);

    // Backbone-derived clock facts.
    assert forall k :: AI.get_idx(cc, k) <= S;
    assert forall k :: AI.get_idx(qc, k) <= S;
    MxAtQidLE(re, cc, qc, -1, qid, S);
    assert clk >= PIV.MxAtQid(re, cc, qc, -1, qid);
    assert forall sg: nat :: (sg in PIV.CapIds(PIV.QidBody(re, qid))
      ==> AI.get_idx(cc, CP.start_reg(sg)) < clk);

    // The gm effect: exactly GMReset over qm's group list.
    PIV.GmOfLiveResetGMReset(re, qm, caps, th.look_regs, quant, qid, clk);
    var quant' := AReg.set_reg(quant, qid0, None, clk);
    assert quant' == AReg.set_reg(quant, qid, None, clk);
    assert PIV.GmOfLive(re, caps, th.look_regs, quant')
        == LG.GMReset(qm.quants[qid as int], PIV.GmOfLive(re, caps, th.look_regs, quant));
    assert qm.quants[qid as int] == t.g.gl;

    // Positional invariant advances across the stamp.
    assert quant'.a_clk == qc[qid0 := clk];
    NI.NestInvStamp(re, code, 0, endl, pc, cc, qc, quant'.a_clk, -1, qid0, clk);
    assert NI.NestTopRE(re, code, endl, pc + 1, cc, quant'.a_clk);

    // Backbone facts for the successor registers.
    assert CM.RegsClocksLE(quant, clk);
    CM.RegsClocksLESet(quant, qid0, None, clk, clk);
  }

  // =========================================================================
  // Step helper: the CONSUME case. StepSpec splits on whether the current
  // character matches: a Read tree (continuation at pc+1 with the loop flag
  // re-armed, on the advanced input) or Mismatch. The positional fact
  // advances to pc+1 either way — exactly the convention PikeInvFullRE uses
  // for blocked threads.
  // =========================================================================
  /** The bundled per-thread step lemma for `Consume`: the tree is a `Read`
      on a matching character (continuation at `pc+1` with the loop flag
      re-armed) or `Mismatch` — the positional fact advances to `pc+1` either
      way, matching `BlockedRepRE`'s convention for blocked threads. */
  lemma ConsumeStepThreadRE(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
                            inp: LC.Input, t: LT.Tree, th: AI.Thread, pc: nat, ce: RC.char_expectation)
    requires !rer.multiline
    requires NR.NfaRepRE(re, code, 0, endl)
    requires NR.GetPcRE(code, endl) == Some(RB.Accept)
    requires th.pc >= 0 && pc == th.pc as nat && pc <= endl
    requires NR.GetPcRE(code, pc) == Some(RB.Consume(ce))
    requires TT.TreeThreadRE(rer, qm, code, inp, t, pc, th.exit_allowed)
    requires NI.NestTopRE(re, code, endl, pc, th.capture_regs.a_clk, th.quant_regs.a_clk)
    ensures AR.ReadCharE(ce, inp).Some? ==>
      t.Read? && exists nextinp ::
        AR.ReadCharE(ce, inp) == Some((t.c, nextinp))
        && TT.TreeThreadRE(rer, qm, code, nextinp, t.t, pc + 1, true)
    ensures AR.ReadCharE(ce, inp).None? ==> t == LT.Mismatch
    ensures pc + 1 <= endl
         && NI.NestTopRE(re, code, endl, pc + 1, th.capture_regs.a_clk, th.quant_regs.a_clk)
  {
    var cc := th.capture_regs.a_clk;
    var qc := th.quant_regs.a_clk;
    assert !TT.StuttersRE(pc, code);
    assert pc < endl;
    GS.GenStepRE(rer, qm, code, inp, t, pc, th.exit_allowed);
    assert NI.NestInvRE(re, code, 0, endl, pc, cc, qc, -1);
    assert NI.StepEdgeRE(code, pc, pc + 1);
    NI.NestInvAdvance(re, code, 0, endl, pc, pc + 1, cc, qc, -1);
  }

  // =========================================================================
  // Step helper: the ENDLOOP case. With the loop flag armed the tree is a
  // Progress node continuing at pc+1 (flag stays true); unarmed it is
  // Mismatch (the thread dies — no successor facts needed).
  // =========================================================================
  /** The bundled per-thread step lemma for `EndLoop`: with the loop flag
      armed the tree is `Progress` continuing at `pc+1`; unarmed it is
      `Mismatch` and the thread dies. */
  lemma EndLoopStepThreadRE(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
                            inp: LC.Input, t: LT.Tree, th: AI.Thread, pc: nat)
    requires !rer.multiline
    requires NR.NfaRepRE(re, code, 0, endl)
    requires NR.GetPcRE(code, endl) == Some(RB.Accept)
    requires th.pc >= 0 && pc == th.pc as nat && pc <= endl
    requires NR.GetPcRE(code, pc) == Some(RB.EndLoop)
    requires TT.TreeThreadRE(rer, qm, code, inp, t, pc, th.exit_allowed)
    requires NI.NestTopRE(re, code, endl, pc, th.capture_regs.a_clk, th.quant_regs.a_clk)
    ensures th.exit_allowed ==>
      t.Progress? && TT.TreeThreadRE(rer, qm, code, inp, t.t, pc + 1, true)
      && pc + 1 <= endl
      && NI.NestTopRE(re, code, endl, pc + 1, th.capture_regs.a_clk, th.quant_regs.a_clk)
    ensures !th.exit_allowed ==> t == LT.Mismatch
  {
    var cc := th.capture_regs.a_clk;
    var qc := th.quant_regs.a_clk;
    assert !TT.StuttersRE(pc, code);
    assert pc < endl;
    GS.GenStepRE(rer, qm, code, inp, t, pc, th.exit_allowed);
    if th.exit_allowed {
      assert NI.NestInvRE(re, code, 0, endl, pc, cc, qc, -1);
      assert NI.StepEdgeRE(code, pc, pc + 1);
      NI.NestInvAdvance(re, code, 0, endl, pc, pc + 1, cc, qc, -1);
    }
  }

  /** The invariant's VM context IS the tree side's anchor context: the
      `cp_context` window at `cp` equals `CtxOf` of the corresponding Input. */
  lemma ContextOkIsCtxOf(str: string, cp: nat)
    requires cp <= |str|
    ensures AI.cp_context(cp, str, LAnc.Forward) == TREP.CtxOf(PIV.InpOfCp(str, cp))
  {
    var inp := PIV.InpOfCp(str, cp);
    T.ReverseProps(str[..cp]);
    assert |inp.pref| == cp;
    if cp > 0 {
      assert inp.pref[0] == str[..cp][cp - 1] == str[cp - 1];
    }
    if cp < |str| {
      assert inp.next[0] == str[cp];
    }
  }

  // =========================================================================
  // The bundled ANCHOR step: zero-width — satisfied continues at pc + 1 with
  // NOTHING else changed (registers, flag, input); unsatisfied is Mismatch.
  // =========================================================================
  /** One thread's `AnchorAssertion` step, bundled: on a satisfied anchor the
      tree is `AnchorPass` and the continuation thread sits at `pc + 1` with
      the same flag and registers; on an unsatisfied one the tree is
      `Mismatch`. */
  lemma AnchorStepThreadRE(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
                           inp: LC.Input, t: LT.Tree, th: AI.Thread, pc: nat, a: R.anchor)
    requires !rer.multiline
    requires NR.NfaRepRE(re, code, 0, endl)
    requires NR.GetPcRE(code, endl) == Some(RB.Accept)
    requires th.pc >= 0 && pc == th.pc as nat && pc <= endl
    requires NR.GetPcRE(code, pc) == Some(RB.AnchorAssertion(a))
    requires TT.TreeThreadRE(rer, qm, code, inp, t, pc, th.exit_allowed)
    requires NI.NestTopRE(re, code, endl, pc, th.capture_regs.a_clk, th.quant_regs.a_clk)
    ensures LAnc.is_satisfied(a, TREP.CtxOf(inp), LAnc.Forward) ==>
      t.AnchorPass? && TT.TreeThreadRE(rer, qm, code, inp, t.t, pc + 1, th.exit_allowed)
      && pc + 1 <= endl
      && NI.NestTopRE(re, code, endl, pc + 1, th.capture_regs.a_clk, th.quant_regs.a_clk)
    ensures !LAnc.is_satisfied(a, TREP.CtxOf(inp), LAnc.Forward) ==> t == LT.Mismatch
  {
    var cc := th.capture_regs.a_clk;
    var qc := th.quant_regs.a_clk;
    assert !TT.StuttersRE(pc, code);
    assert pc < endl;
    GS.GenStepRE(rer, qm, code, inp, t, pc, th.exit_allowed);
    if LAnc.is_satisfied(a, TREP.CtxOf(inp), LAnc.Forward) {
      assert NI.NestInvRE(re, code, 0, endl, pc, cc, qc, -1);
      assert NI.StepEdgeRE(code, pc, pc + 1);
      NI.NestInvAdvance(re, code, 0, endl, pc, pc + 1, cc, qc, -1);
    }
  }

  // isblocked inclusion: RegElk DEDUPS blocked threads by pc (add_thread's
  // isblocked pcset) where Linden appends unconditionally. A dropped blocked
  // thread is simulated by pts_skip, which needs its Read-tree in treeseen —
  // and the FIRST blocker at that pc put it there (pts_blocked adds to seen).
  // This conjunct records that fact for every pc in isblocked.
  /** Every pc recorded in the VM's `isblocked` set is covered by some
      already-`seen` tree thread-equivalent to it at that pc — lets a
      dedup-dropped blocked thread be simulated by the first blocker's tree. */
  ghost predicate IsblockedInclusionRE(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code,
                                       inp: LC.Input, treeseen: SS.SeenTrees, isblocked: AI.pcset)
  {
    forall pc0: nat :: AI.pc_mem(isblocked, pc0) ==>
      exists t: LT.Tree, b: bool ::
        SS.Inseen(treeseen, t) && TT.TreeThreadRE(rer, qm, code, inp, t, pc0, b)
  }

  // The full simulation invariant.
  /** THE full simulation invariant: `PikeInvRE` strengthened with the three
      backbones, the per-thread positional invariant (`ThreadNestRE`) for
      every active and blocked thread, and `IsblockedInclusionRE`. This is
      exactly the package `InvariantPreservationRE` threads through
      `FAdvanceEpsilon`. */
  ghost predicate PikeInvFullRE(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code,
                                endl: nat, ngroups: nat, str: string,
                                pts: PT.PikeTreeState, vms: AI.VmState,
                                ncap: int, nlook: int, nquant: int)
    requires NR.NfaRepRE(re, code, 0, endl)
  {
    PIV.PikeInvRE(rer, qm, re, code, ngroups, str, pts, vms)
    && CM.VmClocksLE(vms)
    && CM.VmRegsWf(vms, ncap, nlook, nquant)
    && CM.VmCapsLE(vms)
    && vms.clock >= 0 && vms.cp >= 0
    && (forall t | t in vms.active :: ThreadNestRE(re, code, endl, t.pc, t))
    && (forall tb | tb in vms.blocked :: ThreadNestRE(re, code, endl, tb.0.pc + 1, tb.0))
    && (forall t | t in vms.active :: EaColdOkRE(code, t))
    && (pts.PTS? ==> IsblockedInclusionRE(rer, qm, code, pts.inp, pts.seen, vms.isblocked))
  }

  // =========================================================================
  // Per-case preservation: the SKIP case. The head thread's (pc, ea) is
  // already processed; the VM drops it, and the tree side plays pts_skip —
  // the seen tree at (pc, ea) IS the head's tree (TtSameTreeRE), and the
  // stutter disjunct is killed by NoStutterCycle.
  // =========================================================================
  /** Per-case preservation for `Skip`: dropping an already-`processed` head
      thread corresponds to the tree side's `pts_skip`, using `TtSameTreeRE`
      and `NoStutterCycle` to identify the seen tree with the head's. */
  lemma PreserveSkipCase(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
                         ngroups: nat, str: string, pts: PT.PikeTreeState, vms: AI.VmState,
                         ncap: int, nlook: int, nquant: int)
    returns (pts1: PT.PikeTreeState)
    requires !rer.multiline
    requires StaticOkRE(qm, re, code, endl)
    requires pts.PTS?
    requires PikeInvFullRE(rer, qm, re, code, endl, ngroups, str, pts, vms, ncap, nlook, nquant)
    requires |vms.active| > 0
    requires AI.bpc_mem(vms.processed, vms.active[0].pc, vms.active[0].exit_allowed)
    ensures PT.PikeTreeStep(pts, pts1)
    ensures pts1.PTS?
    ensures PikeInvFullRE(rer, qm, re, code, endl, ngroups, str, pts1,
                          vms.(active := vms.active[1..]), ncap, nlook, nquant)
  {
    var PTS(inp, ta, best, tb, seen) := pts;
    var th := vms.active[0];
    var ea := th.exit_allowed;

    // Head correspondence.
    assert PIV.ActiveRepRE(rer, qm, re, code, inp, ta, vms.active);
    assert |ta| > 0 && th.pc >= 0;
    var pc: nat := th.pc as nat;
    var t := ta[0].0;
    var gm := ta[0].1;
    assert TT.TreeThreadRE(rer, qm, code, inp, t, pc, ea);
    assert PIV.ActiveRepRE(rer, qm, re, code, inp, ta[1..], vms.active[1..]);

    // The seen entry at (pc, ea) resolves to the LEFT disjunct: the stutter
    // disjunct would need a >=1-step chain pc ->+ pc, killed by tameness.
    assert PIV.SeenInclusionRE(rer, qm, code, inp, seen, vms.processed,
                               PIV.HdTreeOf(ta), PIV.HeadPcOf(vms.active));
    assert PIV.HdTreeOf(ta) == Some(t) && PIV.HeadPcOf(vms.active) == pc;
    assert SS.Inseen(seen, t) by {
      if exists ts: LT.Tree :: SS.Inseen(seen, ts) && TT.TreeThreadRE(rer, qm, code, inp, ts, pc, ea) {
        var ts: LT.Tree :| SS.Inseen(seen, ts) && TT.TreeThreadRE(rer, qm, code, inp, ts, pc, ea);
        TT.TtSameTreeRE(rer, qm, code, inp, ts, t, pc, ea);
      } else {
        var t': LT.Tree :| TT.StuttersRE(pc, code) && PIV.StutterChainTo(code, pc, pc)
          && PIV.HdTreeOf(ta) == Some(t') && TT.TreeThreadRE(rer, qm, code, inp, t', pc, ea);
        PIV.NoStutterCycle(code, pc);
        assert false;
      }
    }

    // The tree step: pts_skip.
    pts1 := PT.PTS(inp, ta[1..], best, tb, seen);
    assert PT.PikeTreeStep(pts, pts1);

    // The full invariant at the successor.
    var vms' := vms.(active := vms.active[1..]);
    BBDropHead(vms, ncap, nlook, nquant);
    PIV.SkipInclusionRE(rer, qm, code, inp, seen, vms.processed, t, pc,
                        PIV.HdTreeOf(ta[1..]), PIV.HeadPcOf(vms'.active));
    forall t2 | t2 in vms'.active ensures ThreadNestRE(re, code, endl, t2.pc, t2) {
      assert t2 in vms.active;
    }
    assert PikeInvFullRE(rer, qm, re, code, endl, ngroups, str, pts1, vms', ncap, nlook, nquant);
  }

  // =========================================================================
  // Per-case preservation: the STUTTER case (Jmp / BeginLoop). The VM ticks,
  // memoizes (pc, ea), and moves the head thread without touching registers;
  // the tree side takes NO step. StutterInclusionRE extends the seen chains.
  // =========================================================================
  /** Per-case preservation for the stutter instructions (`Jmp`/`BeginLoop`):
      the VM ticks and moves the head without touching registers or taking a
      tree step; `StutterInclusionRE` extends the seen-chain bookkeeping. */
  lemma PreserveStutterCase(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
                            ngroups: nat, str: string, pts: PT.PikeTreeState, vms: AI.VmState,
                            s1: AI.VmState, th': AI.Thread, vms2: AI.VmState,
                            ncap: int, nlook: int, nquant: int)
    requires StaticOkRE(qm, re, code, endl)
    requires pts.PTS?
    requires PikeInvFullRE(rer, qm, re, code, endl, ngroups, str, pts, vms, ncap, nlook, nquant)
    requires |vms.active| > 0
    requires !AI.bpc_mem(vms.processed, vms.active[0].pc, vms.active[0].exit_allowed)
    requires s1 == vms.(clock := vms.clock + 1,
                        processed := AI.bpc_add(vms.processed, vms.active[0].pc, vms.active[0].exit_allowed))
    requires vms.active[0].pc >= 0
    requires (exists x: int ::
                NR.GetPcRE(code, vms.active[0].pc as nat) == Some(RB.Jmp(x))
                && th' == vms.active[0].(pc := x))
          || (NR.GetPcRE(code, vms.active[0].pc as nat) == Some(RB.BeginLoop)
              && th' == vms.active[0].(exit_allowed := false, pc := vms.active[0].pc + 1))
    requires vms2 == s1.(active := [th'] + s1.active[1..])
    ensures PikeInvFullRE(rer, qm, re, code, endl, ngroups, str, pts, vms2, ncap, nlook, nquant)
  {
    var PTS(inp, ta, best, tb, seen) := pts;
    var th := vms.active[0];
    var ea := th.exit_allowed;
    var pc: nat := th.pc as nat;

    // Head correspondence.
    assert PIV.ActiveRepRE(rer, qm, re, code, inp, ta, vms.active);
    assert |ta| > 0;
    var t := ta[0].0;
    var gm := ta[0].1;
    assert TT.TreeThreadRE(rer, qm, code, inp, t, pc, ea);
    assert PIV.ActiveRepRE(rer, qm, re, code, inp, ta[1..], vms.active[1..]);
    assert PIV.ThreadTracksGm(re, th, gm);
    assert ThreadNestRE(re, code, endl, th.pc, th);
    assert pc < endl;                                   // Accept at endl is not a stutter

    // The tree survives the stutter at the successor (pc', ea').
    var pc': nat;
    if exists x: int :: NR.GetPcRE(code, pc) == Some(RB.Jmp(x)) && th' == th.(pc := x) {
      var x: int :| NR.GetPcRE(code, pc) == Some(RB.Jmp(x)) && th' == th.(pc := x);
      TT.TtAtJmp(rer, qm, code, inp, t, pc, ea, x);
      pc' := x as nat;
      assert TT.TreeThreadRE(rer, qm, code, inp, t, pc', th'.exit_allowed);
      assert PIV.StutterSuccIs(code, pc, pc');
    } else {
      TT.TtAtBeginLoop(rer, qm, code, inp, t, pc, ea);
      pc' := pc + 1;
      assert TT.TreeThreadRE(rer, qm, code, inp, t, pc', th'.exit_allowed);
      assert PIV.StutterSuccIs(code, pc, pc');
    }
    assert th'.pc == pc' as int;

    // Positional fact advances (registers unchanged).
    assert NI.StepEdgeRE(code, pc, pc');
    assert NI.NestInvRE(re, code, 0, endl, pc, th.capture_regs.a_clk, th.quant_regs.a_clk, -1);
    NI.NestInvAdvance(re, code, 0, endl, pc, pc', th.capture_regs.a_clk, th.quant_regs.a_clk, -1);
    assert ThreadNestRE(re, code, endl, th'.pc, th');

    // Backbones.
    BBTick(vms, s1, ncap, nlook, nquant);
    assert th in vms.active;
    CM.ThreadClocksLEMono(th, vms.clock, s1.clock);
    BBReplaceHead(s1, th', ncap, nlook, nquant);

    // Active correspondence: same (tree, gm) list against the moved head.
    assert PIV.ActiveRepRE(rer, qm, re, code, inp, ta, vms2.active) by {
      assert vms2.active[0] == th' && vms2.active[1..] == vms.active[1..];
      assert ta == [ta[0]] + ta[1..];
      assert PIV.ThreadTracksGm(re, th', gm);
    }

    // Seen inclusion: the stutter chain extends by one step.
    assert TT.StuttersRE(pc, code);
    assert PIV.HdTreeOf(ta) == Some(t) && PIV.HeadPcOf(vms.active) == pc;
    PIV.StutterInclusionRE(rer, qm, code, inp, seen, vms.processed, t, pc, ea, pc');
    assert PIV.HeadPcOf(vms2.active) == pc';

    // Remaining conjuncts.
    forall t2 | t2 in vms2.active ensures ThreadNestRE(re, code, endl, t2.pc, t2) {
      if t2 != th' { assert t2 in vms.active; }
    }
    forall tb2 | tb2 in vms2.blocked ensures ThreadNestRE(re, code, endl, tb2.0.pc + 1, tb2.0) {
      assert tb2 in vms.blocked;
    }
    forall t2 | t2 in vms2.active ensures EaColdOkRE(code, t2) {
      if t2 != th' { assert t2 in vms.active; }
      else if !th'.exit_allowed {
        if NR.GetPcRE(code, pc) == Some(RB.BeginLoop) {
          NI.BeginLoopColdSafeAt(re, code, 0, endl, pc);
          assert pc' == pc + 1;
        } else {
          assert !ea;
          assert !NI.ColdRE(code, pc);
          NotColdSucc(code, pc, pc');
        }
      }
    }
    assert PikeInvFullRE(rer, qm, re, code, endl, ngroups, str, pts, vms2, ncap, nlook, nquant);
  }

  // Growing the seen set preserves the isblocked inclusion (witness carries).
  /** Growing the `seen`-trees set (via `AddSeenTrees`) preserves
      `IsblockedInclusionRE` — the witness tree is still in the bigger set. */
  lemma IsblockedGrow(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                      treeseen: SS.SeenTrees, isblocked: AI.pcset, tx: LT.Tree)
    requires IsblockedInclusionRE(rer, qm, code, inp, treeseen, isblocked)
    ensures IsblockedInclusionRE(rer, qm, code, inp, SS.AddSeenTrees(treeseen, tx), isblocked)
  {
    forall pc0: nat | AI.pc_mem(isblocked, pc0)
      ensures exists t: LT.Tree, b: bool ::
        SS.Inseen(SS.AddSeenTrees(treeseen, tx), t) && TT.TreeThreadRE(rer, qm, code, inp, t, pc0, b)
    {
      var t: LT.Tree, b: bool :| SS.Inseen(treeseen, t) && TT.TreeThreadRE(rer, qm, code, inp, t, pc0, b);
      SS.InAdd(treeseen, t, tx);
    }
  }

  // =========================================================================
  // Per-case preservation: the ACCEPT case. The head's tree is Match; the VM
  // empties the active list and records the head as bestmatch; the tree side
  // plays pts_match with the head's gm (which the head's registers denote).
  // =========================================================================
  /** Per-case preservation for `Accept`: the head's tree is `Match`, so the
      VM's `bestmatch` recording corresponds to the tree side's `pts_match`. */
  lemma PreserveAcceptCase(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
                           ngroups: nat, str: string, pts: PT.PikeTreeState, vms: AI.VmState,
                           s1: AI.VmState, vms2: AI.VmState,
                           ncap: int, nlook: int, nquant: int)
    returns (pts1: PT.PikeTreeState)
    requires !rer.multiline
    requires StaticOkRE(qm, re, code, endl)
    requires pts.PTS?
    requires PikeInvFullRE(rer, qm, re, code, endl, ngroups, str, pts, vms, ncap, nlook, nquant)
    requires |vms.active| > 0
    requires !AI.bpc_mem(vms.processed, vms.active[0].pc, vms.active[0].exit_allowed)
    requires s1 == vms.(clock := vms.clock + 1,
                        processed := AI.bpc_add(vms.processed, vms.active[0].pc, vms.active[0].exit_allowed))
    requires vms.active[0].pc >= 0
    requires NR.GetPcRE(code, vms.active[0].pc as nat) == Some(RB.Accept)
    requires vms2 == s1.(active := [], bestmatch := Some(vms.active[0]))
    ensures PT.PikeTreeStep(pts, pts1)
    ensures pts1.PTS?
    ensures PikeInvFullRE(rer, qm, re, code, endl, ngroups, str, pts1, vms2, ncap, nlook, nquant)
  {
    var PTS(inp, ta, best, tb, seen) := pts;
    var th := vms.active[0];
    var ea := th.exit_allowed;
    var pc: nat := th.pc as nat;

    assert PIV.ActiveRepRE(rer, qm, re, code, inp, ta, vms.active);
    assert |ta| > 0;
    var t := ta[0].0;
    var gm := ta[0].1;
    assert TT.TreeThreadRE(rer, qm, code, inp, t, pc, ea);
    assert PIV.ThreadTracksGm(re, th, gm);

    // StepSpec at Accept: the tree is Match.
    assert !TT.StuttersRE(pc, code);
    GS.GenStepRE(rer, qm, code, inp, t, pc, ea);
    assert t == LT.Match;

    // The tree step: pts_match.
    assert PT.TreeBfsStep(t, gm, LC.Idx(inp)) == PT.StepMatch;
    pts1 := PT.PTS(inp, [], Some((inp, gm)), tb, SS.AddSeenTrees(seen, t));
    assert PT.PikeTreeStep(pts, pts1);

    // The full invariant at the successor.
    BBTick(vms, s1, ncap, nlook, nquant);
    BBAccept(s1, ncap, nlook, nquant);
    assert PIV.BestMatchRE(re, Some((inp, gm)), Some(th));
    assert PIV.ActiveRepRE(rer, qm, re, code, inp, [], []);
    PIV.AddInclusionRE(rer, qm, code, inp, seen, vms.processed, t, pc, ea,
                       PIV.HdTreeOf([]), PIV.HeadPcOf([]));
    IsblockedGrow(rer, qm, code, inp, seen, vms.isblocked, t);
    forall tb2 | tb2 in vms2.blocked ensures ThreadNestRE(re, code, endl, tb2.0.pc + 1, tb2.0) {
      assert tb2 in vms.blocked;
    }
    assert PikeInvFullRE(rer, qm, re, code, endl, ngroups, str, pts1, vms2, ncap, nlook, nquant);
  }

  // =========================================================================
  // Per-case preservation: the FORK case. The head's tree is a Choice; the VM
  // replaces the head with two threads sharing its registers; the tree side
  // plays pts_active with both branches carrying the unchanged gm.
  // =========================================================================
  /** Per-case preservation for `Fork`, split by direction: at a forward
      fork the head's tree is a `Choice` and the tree side plays one
      `pts_active`; at the do-while's backward fork the invariant pins
      `exit_allowed`, the checked tree is `Progress(Choice(..))`, and the
      tree side takes two steps (guard unwrap, then the split). */
  lemma PreserveForkCase(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
                         ngroups: nat, str: string, pts: PT.PikeTreeState, vms: AI.VmState,
                         s1: AI.VmState, x: int, y: int, vms2: AI.VmState,
                         ncap: int, nlook: int, nquant: int)
    returns (pts1: PT.PikeTreeState)
    requires !rer.multiline
    requires StaticOkRE(qm, re, code, endl)
    requires pts.PTS?
    requires PikeInvFullRE(rer, qm, re, code, endl, ngroups, str, pts, vms, ncap, nlook, nquant)
    requires |vms.active| > 0
    requires !AI.bpc_mem(vms.processed, vms.active[0].pc, vms.active[0].exit_allowed)
    requires s1 == vms.(clock := vms.clock + 1,
                        processed := AI.bpc_add(vms.processed, vms.active[0].pc, vms.active[0].exit_allowed))
    requires vms.active[0].pc >= 0
    requires NR.GetPcRE(code, vms.active[0].pc as nat) == Some(RB.Fork(x, y))
    requires vms2 == s1.(active :=
      [AI.Thread(x, vms.active[0].capture_regs, vms.active[0].look_regs, vms.active[0].quant_regs, vms.active[0].exit_allowed),
       vms.active[0].(pc := y)] + s1.active[1..])
    ensures TrcRE(pts, pts1)
    ensures pts1.PTS?
    ensures PikeInvFullRE(rer, qm, re, code, endl, ngroups, str, pts1, vms2, ncap, nlook, nquant)
  {
    var PTS(inp, ta, best, tb, seen) := pts;
    var th := vms.active[0];
    var ea := th.exit_allowed;
    var pc: nat := th.pc as nat;
    var cc := th.capture_regs.a_clk;
    var qc := th.quant_regs.a_clk;

    assert PIV.ActiveRepRE(rer, qm, re, code, inp, ta, vms.active);
    assert |ta| > 0;
    var t := ta[0].0;
    var gm := ta[0].1;
    assert TT.TreeThreadRE(rer, qm, code, inp, t, pc, ea);
    assert PIV.ActiveRepRE(rer, qm, re, code, inp, ta[1..], vms.active[1..]);
    assert PIV.ThreadTracksGm(re, th, gm);
    assert ThreadNestRE(re, code, endl, th.pc, th);
    assert !TT.StuttersRE(pc, code);
    assert pc < endl;

    // The step kernel; the Fork clause splits by direction.
    GS.GenStepRE(rer, qm, code, inp, t, pc, ea);
    assert x >= 0 && y >= 0;
    var th1 := AI.Thread(x, th.capture_regs, th.look_regs, th.quant_regs, ea);
    var th2 := th.(pc := y);
    assert vms2.active == [th1, th2] + vms.active[1..];

    // Positional facts advance along both arms (a backward arm lands on the
    // do-while's stamp site, covered by NestInvAdvance's do-while branches).
    assert NI.NestInvRE(re, code, 0, endl, pc, cc, qc, -1);
    assert NI.StepEdgeRE(code, pc, x as nat);
    NI.NestInvAdvance(re, code, 0, endl, pc, x as nat, cc, qc, -1);
    assert NI.StepEdgeRE(code, pc, y as nat);
    NI.NestInvAdvance(re, code, 0, endl, pc, y as nat, cc, qc, -1);
    assert ThreadNestRE(re, code, endl, th1.pc, th1) && ThreadNestRE(re, code, endl, th2.pc, th2);

    // Backbones.
    BBTick(vms, s1, ncap, nlook, nquant);
    assert th in vms.active;
    CM.ThreadClocksLEMono(th, vms.clock, s1.clock);
    BBTwoHead(s1, th1, th2, ncap, nlook, nquant);

    if x as nat > pc && y as nat > pc {
      // ---- a FORWARD fork: an alternation / optional-layer decision -------
      assert t.Choice?;
      assert TT.TreeThreadRE(rer, qm, code, inp, t.t1, x as nat, ea);
      assert TT.TreeThreadRE(rer, qm, code, inp, t.t2, y as nat, ea);
      var na := [(t.t1, gm), (t.t2, gm)];
      assert PT.TreeBfsStep(t, gm, LC.Idx(inp)) == PT.StepActive(na);
      pts1 := PT.PTS(inp, na + ta[1..], best, tb, SS.AddSeenTrees(seen, t));
      assert PT.PikeTreeStep(pts, pts1);
      TrcRefl(pts1);
      TrcCons(pts, pts1, pts1);

      // Active correspondence: two new head pairs, unchanged registers.
      assert PIV.ActiveRepRE(rer, qm, re, code, inp, na + ta[1..], vms2.active) by {
        assert PIV.ThreadTracksGm(re, th1, gm) && PIV.ThreadTracksGm(re, th2, gm);
        assert (na + ta[1..])[0] == (t.t1, gm) && (na + ta[1..])[1] == (t.t2, gm);
        assert (na + ta[1..])[1..] == [(t.t2, gm)] + ta[1..];
        assert ((na + ta[1..])[1..])[1..] == ta[1..];
        assert vms2.active[1..] == [th2] + vms.active[1..];
        assert (vms2.active[1..])[1..] == vms.active[1..];
      }

      // Seen inclusion + isblocked.
      PIV.AddInclusionRE(rer, qm, code, inp, seen, vms.processed, t, pc, ea,
                         PIV.HdTreeOf(na + ta[1..]), PIV.HeadPcOf(vms2.active));
      IsblockedGrow(rer, qm, code, inp, seen, vms.isblocked, t);

      // Remaining conjuncts.
      forall t2 | t2 in vms2.active ensures ThreadNestRE(re, code, endl, t2.pc, t2) {
        if t2 != th1 && t2 != th2 { assert t2 in vms.active; }
      }
      forall tb2 | tb2 in vms2.blocked ensures ThreadNestRE(re, code, endl, tb2.0.pc + 1, tb2.0) {
        assert tb2 in vms.blocked;
      }
      forall t2 | t2 in vms2.active ensures EaColdOkRE(code, t2) {
        if t2 != th1 && t2 != th2 { assert t2 in vms.active; }
        else if !ea {
          assert th in vms.active && EaColdOkRE(code, th);
          assert !NI.ColdRE(code, pc);
          NotColdSucc(code, pc, x as nat);
          NotColdSucc(code, pc, y as nat);
        }
      }
      assert PikeInvFullRE(rer, qm, re, code, endl, ngroups, str, pts1, vms2, ncap, nlook, nquant);
    } else {
      // ---- the do-while's BACKWARD fork -----------------------------------
      assert AR.BackForkAt(code, pc);
      // the invariant pins the flag: a false-thread never sits at a Cold pc
      assert ea by {
        if !ea {
          assert th in vms.active && EaColdOkRE(code, th);
          assert NI.ColdF(code, pc, 1);
          assert NI.ColdRE(code, pc);
        }
      }
      assert t.Progress? && t.t.Choice?;
      assert TT.TreeThreadRE(rer, qm, code, inp, t.t.t1, x as nat, true);
      assert TT.TreeThreadRE(rer, qm, code, inp, t.t.t2, y as nat, true);

      // Two tree-machine steps: unwrap the dissolved progress guard, then
      // split the Choice at the arms.
      var mta := [(t.t, gm)] + ta[1..];
      assert PT.TreeBfsStep(t, gm, LC.Idx(inp)) == PT.StepActive([(t.t, gm)]);
      assert [(t.t, gm)] + ta[1..] == mta;
      var mid := PT.PTS(inp, mta, best, tb, SS.AddSeenTrees(seen, t));
      assert PT.PikeTreeStep(pts, mid);
      var na := [(t.t.t1, gm), (t.t.t2, gm)];
      assert mta[0] == (t.t, gm) && mta[1..] == ta[1..];
      assert PT.TreeBfsStep(t.t, gm, LC.Idx(inp)) == PT.StepActive(na);
      pts1 := PT.PTS(inp, na + ta[1..], best, tb,
                     SS.AddSeenTrees(SS.AddSeenTrees(seen, t), t.t));
      assert PT.PikeTreeStep(mid, pts1);
      TrcRefl(pts1);
      TrcCons(mid, pts1, pts1);
      TrcCons(pts, mid, pts1);

      // Active correspondence: both arm threads run at exit_allowed == true.
      assert PIV.ActiveRepRE(rer, qm, re, code, inp, na + ta[1..], vms2.active) by {
        assert th1.exit_allowed == true && th2.exit_allowed == true;
        assert PIV.ThreadTracksGm(re, th1, gm) && PIV.ThreadTracksGm(re, th2, gm);
        assert (na + ta[1..])[0] == (t.t.t1, gm) && (na + ta[1..])[1] == (t.t.t2, gm);
        assert (na + ta[1..])[1..] == [(t.t.t2, gm)] + ta[1..];
        assert ((na + ta[1..])[1..])[1..] == ta[1..];
        assert vms2.active[1..] == [th2] + vms.active[1..];
        assert (vms2.active[1..])[1..] == vms.active[1..];
      }

      // Seen inclusion: the (pc, ea) slot resolves to t; the extra t.t only
      // grows the seen set.
      PIV.AddInclusionRE(rer, qm, code, inp, seen, vms.processed, t, pc, ea,
                         PIV.HdTreeOf(na + ta[1..]), PIV.HeadPcOf(vms2.active));
      PIV.SeenGrowInclusionRE(rer, qm, code, inp, SS.AddSeenTrees(seen, t),
                              AI.bpc_add(vms.processed, th.pc, ea), t.t,
                              PIV.HdTreeOf(na + ta[1..]), PIV.HeadPcOf(vms2.active));
      IsblockedGrow(rer, qm, code, inp, seen, vms.isblocked, t);
      IsblockedGrow(rer, qm, code, inp, SS.AddSeenTrees(seen, t), vms.isblocked, t.t);

      // Remaining conjuncts.
      forall t2 | t2 in vms2.active ensures ThreadNestRE(re, code, endl, t2.pc, t2) {
        if t2 != th1 && t2 != th2 { assert t2 in vms.active; }
      }
      forall tb2 | tb2 in vms2.blocked ensures ThreadNestRE(re, code, endl, tb2.0.pc + 1, tb2.0) {
        assert tb2 in vms.blocked;
      }
      forall t2 | t2 in vms2.active ensures EaColdOkRE(code, t2) {
        if t2 != th1 && t2 != th2 { assert t2 in vms.active; }
        // both arm threads carry exit_allowed == true: vacuous
      }
      assert PikeInvFullRE(rer, qm, re, code, endl, ngroups, str, pts1, vms2, ncap, nlook, nquant);
    }
  }

  // =========================================================================
  // Per-case preservation: the OPEN case (SetRegisterToCP, even register).
  // =========================================================================
  /** Per-case preservation for `SetRegisterToCP` on an even (start) register:
      wraps `OpenStepThreadRE` into a full `PikeInvFullRE`-to-`PikeInvFullRE`
      step, updating the successor's tracked `GroupMap` via `GMOpen`. */
  lemma PreserveOpenCase(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
                         ngroups: nat, str: string, pts: PT.PikeTreeState, vms: AI.VmState,
                         s1: AI.VmState, sreg: int, vms2: AI.VmState,
                         ncap: int, nlook: int, nquant: int)
    returns (pts1: PT.PikeTreeState)
    requires !rer.multiline
    requires StaticOkRE(qm, re, code, endl)
    requires SizesOkRE(re, ncap, nlook, nquant)
    requires pts.PTS?
    requires PikeInvFullRE(rer, qm, re, code, endl, ngroups, str, pts, vms, ncap, nlook, nquant)
    requires |vms.active| > 0
    requires !AI.bpc_mem(vms.processed, vms.active[0].pc, vms.active[0].exit_allowed)
    requires s1 == vms.(clock := vms.clock + 1,
                        processed := AI.bpc_add(vms.processed, vms.active[0].pc, vms.active[0].exit_allowed))
    requires vms.active[0].pc >= 0
    requires NR.GetPcRE(code, vms.active[0].pc as nat) == Some(RB.SetRegisterToCP(sreg))
    requires sreg % 2 == 0
    requires vms2 == s1.(active :=
      [vms.active[0].(capture_regs := AReg.set_reg(vms.active[0].capture_regs, sreg, Some(s1.cp), s1.clock),
                      pc := vms.active[0].pc + 1)] + s1.active[1..])
    ensures PT.PikeTreeStep(pts, pts1)
    ensures pts1.PTS?
    ensures PikeInvFullRE(rer, qm, re, code, endl, ngroups, str, pts1, vms2, ncap, nlook, nquant)
  {
    var PTS(inp, ta, best, tb, seen) := pts;
    var th := vms.active[0];
    var ea := th.exit_allowed;
    var pc: nat := th.pc as nat;

    assert PIV.ActiveRepRE(rer, qm, re, code, inp, ta, vms.active);
    assert |ta| > 0;
    var t := ta[0].0;
    var gm := ta[0].1;
    assert TT.TreeThreadRE(rer, qm, code, inp, t, pc, ea);
    assert PIV.ActiveRepRE(rer, qm, re, code, inp, ta[1..], vms.active[1..]);
    assert PIV.ThreadTracksGm(re, th, gm);
    assert ThreadNestRE(re, code, endl, th.pc, th);
    assert CM.ThreadClocksLE(th, vms.clock) && CM.ThreadRegsWf(th, ncap, nlook, nquant)
        && CM.RegsValsLE(th.capture_regs, vms.cp);

    // The bundled Open step.
    OpenStepThreadRE(rer, qm, re, code, endl, inp, t, gm, th, pc, sreg, vms.cp, vms.clock);
    var gid: nat := t.g.g;
    var caps' := AReg.set_reg(th.capture_regs, sreg, Some(vms.cp), vms.clock + 1);
    var th' := th.(capture_regs := caps', pc := th.pc + 1);
    assert vms2.active == [th'] + vms.active[1..];

    // The tree step: pts_active with the GMOpen-updated gm.
    var gm' := LG.GMUpdate(t.g, LC.Idx(inp), gm);
    var na := [(t.t, gm')];
    assert PT.TreeBfsStep(t, gm, LC.Idx(inp)) == PT.StepActive(na);
    pts1 := PT.PTS(inp, na + ta[1..], best, tb, SS.AddSeenTrees(seen, t));
    assert PT.PikeTreeStep(pts, pts1);

    // The successor thread tracks the updated gm.
    assert 0 <= vms.cp <= |str| && inp == PIV.InpOfCp(str, vms.cp);
    PIV.IdxInpOfCp(str, vms.cp);
    assert LC.Idx(inp) == vms.cp;
    assert gm' == LG.GMOpen(vms.cp as nat, gid, gm);
    assert PIV.ThreadTracksGm(re, th', gm') by {
      assert PIV.GmOfLive(re, caps', th.look_regs, th.quant_regs) == LG.GMOpen(vms.cp as nat, gid, gm);
    }

    // Backbones for the successor.
    BBTick(vms, s1, ncap, nlook, nquant);
    assert CM.ThreadClocksLE(th', s1.clock) by {
      assert CM.RegsClocksLE(caps', vms.clock + 1);
      CM.ThreadClocksLEMono(th, vms.clock, s1.clock);
    }
    assert CM.ThreadRegsWf(th', ncap, nlook, nquant);
    BBReplaceHead(s1, th', ncap, nlook, nquant);

    // Active correspondence.
    assert PIV.ActiveRepRE(rer, qm, re, code, inp, na + ta[1..], vms2.active) by {
      assert (na + ta[1..])[0] == (t.t, gm') && (na + ta[1..])[1..] == ta[1..];
      assert vms2.active[0] == th' && vms2.active[1..] == vms.active[1..];
    }

    // Seen inclusion + isblocked.
    PIV.AddInclusionRE(rer, qm, code, inp, seen, vms.processed, t, pc, ea,
                       PIV.HdTreeOf(na + ta[1..]), PIV.HeadPcOf(vms2.active));
    IsblockedGrow(rer, qm, code, inp, seen, vms.isblocked, t);

    // Remaining conjuncts.
    forall t2 | t2 in vms2.active ensures ThreadNestRE(re, code, endl, t2.pc, t2) {
      if t2 != th' { assert t2 in vms.active; }
    }
    forall tb2 | tb2 in vms2.blocked ensures ThreadNestRE(re, code, endl, tb2.0.pc + 1, tb2.0) {
      assert tb2 in vms.blocked;
    }
    forall t2 | t2 in vms2.active ensures EaColdOkRE(code, t2) {
      if t2 != th' { assert t2 in vms.active; }
      else if !t2.exit_allowed {
        assert !ea;
        assert th in vms.active && EaColdOkRE(code, th);
        assert !NI.ColdRE(code, pc);
        NotColdSucc(code, pc, pc + 1);
      }
    }
    assert PikeInvFullRE(rer, qm, re, code, endl, ngroups, str, pts1, vms2, ncap, nlook, nquant);
  }

  // =========================================================================
  // Per-case preservation: the CLOSE case (SetRegisterToCP, odd register).
  // =========================================================================
  /** Per-case preservation for `SetRegisterToCP` on an odd (end) register:
      wraps `CloseStepThreadRE` into a full invariant step, tracking
      `GMClose`. */
  lemma PreserveCloseCase(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
                          ngroups: nat, str: string, pts: PT.PikeTreeState, vms: AI.VmState,
                          s1: AI.VmState, ereg: int, vms2: AI.VmState,
                          ncap: int, nlook: int, nquant: int)
    returns (pts1: PT.PikeTreeState)
    requires !rer.multiline
    requires StaticOkRE(qm, re, code, endl)
    requires SizesOkRE(re, ncap, nlook, nquant)
    requires pts.PTS?
    requires PikeInvFullRE(rer, qm, re, code, endl, ngroups, str, pts, vms, ncap, nlook, nquant)
    requires |vms.active| > 0
    requires !AI.bpc_mem(vms.processed, vms.active[0].pc, vms.active[0].exit_allowed)
    requires s1 == vms.(clock := vms.clock + 1,
                        processed := AI.bpc_add(vms.processed, vms.active[0].pc, vms.active[0].exit_allowed))
    requires vms.active[0].pc >= 0
    requires NR.GetPcRE(code, vms.active[0].pc as nat) == Some(RB.SetRegisterToCP(ereg))
    requires ereg % 2 == 1
    requires vms2 == s1.(active :=
      [vms.active[0].(capture_regs := AReg.set_reg(vms.active[0].capture_regs, ereg, Some(s1.cp), s1.clock),
                      pc := vms.active[0].pc + 1)] + s1.active[1..])
    ensures PT.PikeTreeStep(pts, pts1)
    ensures pts1.PTS?
    ensures PikeInvFullRE(rer, qm, re, code, endl, ngroups, str, pts1, vms2, ncap, nlook, nquant)
  {
    var PTS(inp, ta, best, tb, seen) := pts;
    var th := vms.active[0];
    var ea := th.exit_allowed;
    var pc: nat := th.pc as nat;

    assert PIV.ActiveRepRE(rer, qm, re, code, inp, ta, vms.active);
    assert |ta| > 0;
    var t := ta[0].0;
    var gm := ta[0].1;
    assert TT.TreeThreadRE(rer, qm, code, inp, t, pc, ea);
    assert PIV.ActiveRepRE(rer, qm, re, code, inp, ta[1..], vms.active[1..]);
    assert PIV.ThreadTracksGm(re, th, gm);
    assert ThreadNestRE(re, code, endl, th.pc, th);
    assert CM.ThreadClocksLE(th, vms.clock) && CM.ThreadRegsWf(th, ncap, nlook, nquant)
        && CM.RegsValsLE(th.capture_regs, vms.cp);

    // The bundled Close step.
    CloseStepThreadRE(rer, qm, re, code, endl, inp, t, gm, th, pc, ereg, vms.cp, vms.clock);
    var gid: nat := t.g.g;
    var caps' := AReg.set_reg(th.capture_regs, ereg, Some(vms.cp), vms.clock + 1);
    var th' := th.(capture_regs := caps', pc := th.pc + 1);
    assert vms2.active == [th'] + vms.active[1..];

    // The tree step: pts_active with the GMClose-updated gm.
    var gm' := LG.GMUpdate(t.g, LC.Idx(inp), gm);
    var na := [(t.t, gm')];
    assert PT.TreeBfsStep(t, gm, LC.Idx(inp)) == PT.StepActive(na);
    pts1 := PT.PTS(inp, na + ta[1..], best, tb, SS.AddSeenTrees(seen, t));
    assert PT.PikeTreeStep(pts, pts1);

    // The successor thread tracks the updated gm.
    assert 0 <= vms.cp <= |str| && inp == PIV.InpOfCp(str, vms.cp);
    PIV.IdxInpOfCp(str, vms.cp);
    assert LC.Idx(inp) == vms.cp;
    assert gm' == LG.GMClose(vms.cp as nat, gid, gm);
    assert PIV.ThreadTracksGm(re, th', gm') by {
      assert PIV.GmOfLive(re, caps', th.look_regs, th.quant_regs) == LG.GMClose(vms.cp as nat, gid, gm);
    }

    // Backbones for the successor.
    BBTick(vms, s1, ncap, nlook, nquant);
    assert CM.ThreadClocksLE(th', s1.clock) by {
      assert CM.RegsClocksLE(caps', vms.clock + 1);
      CM.ThreadClocksLEMono(th, vms.clock, s1.clock);
    }
    assert CM.ThreadRegsWf(th', ncap, nlook, nquant);
    BBReplaceHead(s1, th', ncap, nlook, nquant);

    // Active correspondence.
    assert PIV.ActiveRepRE(rer, qm, re, code, inp, na + ta[1..], vms2.active) by {
      assert (na + ta[1..])[0] == (t.t, gm') && (na + ta[1..])[1..] == ta[1..];
      assert vms2.active[0] == th' && vms2.active[1..] == vms.active[1..];
    }

    // Seen inclusion + isblocked.
    PIV.AddInclusionRE(rer, qm, code, inp, seen, vms.processed, t, pc, ea,
                       PIV.HdTreeOf(na + ta[1..]), PIV.HeadPcOf(vms2.active));
    IsblockedGrow(rer, qm, code, inp, seen, vms.isblocked, t);

    // Remaining conjuncts.
    forall t2 | t2 in vms2.active ensures ThreadNestRE(re, code, endl, t2.pc, t2) {
      if t2 != th' { assert t2 in vms.active; }
    }
    forall tb2 | tb2 in vms2.blocked ensures ThreadNestRE(re, code, endl, tb2.0.pc + 1, tb2.0) {
      assert tb2 in vms.blocked;
    }
    forall t2 | t2 in vms2.active ensures EaColdOkRE(code, t2) {
      if t2 != th' { assert t2 in vms.active; }
      else if !t2.exit_allowed {
        assert !ea;
        assert th in vms.active && EaColdOkRE(code, th);
        assert !NI.ColdRE(code, pc);
        NotColdSucc(code, pc, pc + 1);
      }
    }
    assert PikeInvFullRE(rer, qm, re, code, endl, ngroups, str, pts1, vms2, ncap, nlook, nquant);
  }

  // =========================================================================
  // Per-case preservation: the RESET case (SetQuantToClock).
  // =========================================================================
  /** Per-case preservation for `SetQuantToClock`: wraps `ResetStepThreadRE`
      into a full invariant step, tracking `GMReset`. */
  lemma PreserveResetCase(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
                          ngroups: nat, str: string, pts: PT.PikeTreeState, vms: AI.VmState,
                          s1: AI.VmState, qid0: int, bq: bool, vms2: AI.VmState,
                          ncap: int, nlook: int, nquant: int)
    returns (pts1: PT.PikeTreeState)
    requires !rer.multiline
    requires StaticOkRE(qm, re, code, endl)
    requires SizesOkRE(re, ncap, nlook, nquant)
    requires pts.PTS?
    requires PikeInvFullRE(rer, qm, re, code, endl, ngroups, str, pts, vms, ncap, nlook, nquant)
    requires |vms.active| > 0
    requires !AI.bpc_mem(vms.processed, vms.active[0].pc, vms.active[0].exit_allowed)
    requires s1 == vms.(clock := vms.clock + 1,
                        processed := AI.bpc_add(vms.processed, vms.active[0].pc, vms.active[0].exit_allowed))
    requires vms.active[0].pc >= 0
    requires NR.GetPcRE(code, vms.active[0].pc as nat) == Some(RB.SetQuantToClock(qid0, bq))
    requires vms2 == s1.(active :=
      [vms.active[0].(quant_regs := AReg.set_reg(vms.active[0].quant_regs, qid0,
                                                 if bq then Some(s1.cp) else None, s1.clock),
                      pc := vms.active[0].pc + 1)] + s1.active[1..])
    ensures PT.PikeTreeStep(pts, pts1)
    ensures pts1.PTS?
    ensures PikeInvFullRE(rer, qm, re, code, endl, ngroups, str, pts1, vms2, ncap, nlook, nquant)
  {
    var PTS(inp, ta, best, tb, seen) := pts;
    var th := vms.active[0];
    var ea := th.exit_allowed;
    var pc: nat := th.pc as nat;

    assert PIV.ActiveRepRE(rer, qm, re, code, inp, ta, vms.active);
    assert |ta| > 0;
    var t := ta[0].0;
    var gm := ta[0].1;
    assert TT.TreeThreadRE(rer, qm, code, inp, t, pc, ea);
    assert PIV.ActiveRepRE(rer, qm, re, code, inp, ta[1..], vms.active[1..]);
    assert PIV.ThreadTracksGm(re, th, gm);
    assert ThreadNestRE(re, code, endl, th.pc, th);
    assert CM.ThreadClocksLE(th, vms.clock) && CM.ThreadRegsWf(th, ncap, nlook, nquant);

    // The compiled fragment only emits bq == false.
    assert pc < endl;
    NI.CodeShapeAt(re, code, 0, endl, pc);
    assert !bq;

    // The bundled Reset step.
    ResetStepThreadRE(rer, qm, re, code, endl, inp, t, gm, th, pc, qid0, vms.clock);
    var quant' := AReg.set_reg(th.quant_regs, qid0, None, vms.clock + 1);
    var th' := th.(quant_regs := quant', pc := th.pc + 1);
    assert vms2.active == [th'] + vms.active[1..];

    // The tree step: pts_active with the GMReset-updated gm.
    var gm' := LG.GMUpdate(t.g, LC.Idx(inp), gm);
    var na := [(t.t, gm')];
    assert PT.TreeBfsStep(t, gm, LC.Idx(inp)) == PT.StepActive(na);
    pts1 := PT.PTS(inp, na + ta[1..], best, tb, SS.AddSeenTrees(seen, t));
    assert PT.PikeTreeStep(pts, pts1);

    // The successor thread tracks the updated gm.
    assert gm' == LG.GMReset(t.g.gl, gm);
    assert PIV.ThreadTracksGm(re, th', gm') by {
      assert PIV.GmOfLive(re, th.capture_regs, th.look_regs, quant') == LG.GMReset(t.g.gl, gm);
    }

    // Backbones for the successor.
    BBTick(vms, s1, ncap, nlook, nquant);
    assert CM.ThreadClocksLE(th', s1.clock) by {
      assert CM.RegsClocksLE(quant', vms.clock + 1);
      CM.ThreadClocksLEMono(th, vms.clock, s1.clock);
    }
    assert CM.ThreadRegsWf(th', ncap, nlook, nquant);
    assert CM.RegsValsLE(th'.capture_regs, s1.cp);
    BBReplaceHead(s1, th', ncap, nlook, nquant);

    // Active correspondence.
    assert PIV.ActiveRepRE(rer, qm, re, code, inp, na + ta[1..], vms2.active) by {
      assert (na + ta[1..])[0] == (t.t, gm') && (na + ta[1..])[1..] == ta[1..];
      assert vms2.active[0] == th' && vms2.active[1..] == vms.active[1..];
    }

    // Seen inclusion + isblocked.
    PIV.AddInclusionRE(rer, qm, code, inp, seen, vms.processed, t, pc, ea,
                       PIV.HdTreeOf(na + ta[1..]), PIV.HeadPcOf(vms2.active));
    IsblockedGrow(rer, qm, code, inp, seen, vms.isblocked, t);

    // Remaining conjuncts.
    forall t2 | t2 in vms2.active ensures ThreadNestRE(re, code, endl, t2.pc, t2) {
      if t2 != th' { assert t2 in vms.active; }
    }
    forall tb2 | tb2 in vms2.blocked ensures ThreadNestRE(re, code, endl, tb2.0.pc + 1, tb2.0) {
      assert tb2 in vms.blocked;
    }
    forall t2 | t2 in vms2.active ensures EaColdOkRE(code, t2) {
      if t2 != th' { assert t2 in vms.active; }
      else if !t2.exit_allowed {
        assert !ea;
        assert th in vms.active && EaColdOkRE(code, th);
        assert !NI.ColdRE(code, pc);
        NotColdSucc(code, pc, pc + 1);
      }
    }
    assert PikeInvFullRE(rer, qm, re, code, endl, ngroups, str, pts1, vms2, ncap, nlook, nquant);
  }

  // =========================================================================
  // Blocked-list utilities for the Consume cases.
  // =========================================================================
  /** List algebra: reversing a list with one element prepended equals
      reversing the tail with that element appended. */
  lemma ReversePrepend<T>(p: T, bl: seq<T>)
    ensures LC.Reverse([p] + bl) == LC.Reverse(bl) + [p]
  {
    var s := [p] + bl;
    assert s[1..] == bl && s[0] == p;
  }

  /** The matching-blocked filter (`PIV.MatchingBlocked`) commutes with
      appending one more pair: the pair survives the filter iff it reads at
      the current input. */
  lemma MatchingBlockedSnoc(bl: seq<(AI.Thread, RC.char_expectation)>, p: (AI.Thread, RC.char_expectation),
                            inp: LC.Input)
    ensures PIV.MatchingBlocked(bl + [p], inp)
         == PIV.MatchingBlocked(bl, inp) + (if AR.ReadCharE(p.1, inp).Some? then [p] else [])
    decreases bl
  {
    if |bl| == 0 {
      assert bl + [p] == [p];
    } else {
      assert (bl + [p])[0] == bl[0] && (bl + [p])[1..] == bl[1..] + [p];
      MatchingBlockedSnoc(bl[1..], p, inp);
    }
  }

  // Appending one matching pair to both sides of the blocked correspondence.
  /** `BlockedRepRE` extends by one matching pair: appending a thread that
      reads a character and correctly continues at `pc+1` to both the tree
      list and the blocked list preserves the correspondence. */
  lemma BlockedRepSnocRE(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code,
                         inp: LC.Input, nextinp: LC.Input,
                         tl: seq<(LT.Tree, LG.GroupMap)>, bl: seq<(AI.Thread, RC.char_expectation)>,
                         tp: (LT.Tree, LG.GroupMap), p: (AI.Thread, RC.char_expectation))
    requires PIV.BlockedRepRE(rer, qm, re, code, inp, nextinp, tl, bl)
    requires p.0.pc + 1 >= 0
    requires exists c: char :: AR.ReadCharE(p.1, inp) == Some((c, nextinp))
    requires TT.TreeThreadRE(rer, qm, code, nextinp, tp.0, (p.0.pc + 1) as nat, true)
    requires PIV.ThreadTracksGm(re, p.0, tp.1)
    ensures PIV.BlockedRepRE(rer, qm, re, code, inp, nextinp, tl + [tp], bl + [p])
    decreases tl
  {
    if |tl| == 0 {
      assert |bl| == 0;
      assert tl + [tp] == [tp] && bl + [p] == [p];
      assert PIV.BlockedRepRE(rer, qm, re, code, inp, nextinp, [], []);
    } else {
      assert |bl| > 0;
      BlockedRepSnocRE(rer, qm, re, code, inp, nextinp, tl[1..], bl[1..], tp, p);
      assert (tl + [tp])[0] == tl[0] && (tl + [tp])[1..] == tl[1..] + [tp];
      assert (bl + [p])[0] == bl[0] && (bl + [p])[1..] == bl[1..] + [p];
    }
  }

  // =========================================================================
  // Per-case preservation: ENDLOOP with the loop flag armed — a Progress node
  // continuing at pc+1 with unchanged registers and gm.
  // =========================================================================
  /** Per-case preservation for `EndLoop` with the loop flag armed: the tree
      takes a `Progress` step to `pc+1` with unchanged registers/gm. */
  lemma PreserveEndLoopPass(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
                            ngroups: nat, str: string, pts: PT.PikeTreeState, vms: AI.VmState,
                            s1: AI.VmState, vms2: AI.VmState,
                            ncap: int, nlook: int, nquant: int)
    returns (pts1: PT.PikeTreeState)
    requires !rer.multiline
    requires StaticOkRE(qm, re, code, endl)
    requires pts.PTS?
    requires PikeInvFullRE(rer, qm, re, code, endl, ngroups, str, pts, vms, ncap, nlook, nquant)
    requires |vms.active| > 0
    requires !AI.bpc_mem(vms.processed, vms.active[0].pc, vms.active[0].exit_allowed)
    requires s1 == vms.(clock := vms.clock + 1,
                        processed := AI.bpc_add(vms.processed, vms.active[0].pc, vms.active[0].exit_allowed))
    requires vms.active[0].pc >= 0
    requires NR.GetPcRE(code, vms.active[0].pc as nat) == Some(RB.EndLoop)
    requires vms.active[0].exit_allowed
    requires vms2 == s1.(active := [vms.active[0].(pc := vms.active[0].pc + 1)] + s1.active[1..])
    ensures PT.PikeTreeStep(pts, pts1)
    ensures pts1.PTS?
    ensures PikeInvFullRE(rer, qm, re, code, endl, ngroups, str, pts1, vms2, ncap, nlook, nquant)
  {
    var PTS(inp, ta, best, tb, seen) := pts;
    var th := vms.active[0];
    var ea := th.exit_allowed;
    var pc: nat := th.pc as nat;

    assert PIV.ActiveRepRE(rer, qm, re, code, inp, ta, vms.active);
    assert |ta| > 0;
    var t := ta[0].0;
    var gm := ta[0].1;
    assert TT.TreeThreadRE(rer, qm, code, inp, t, pc, ea);
    assert PIV.ActiveRepRE(rer, qm, re, code, inp, ta[1..], vms.active[1..]);
    assert PIV.ThreadTracksGm(re, th, gm);
    assert ThreadNestRE(re, code, endl, th.pc, th);

    // The bundled EndLoop step (armed branch).
    EndLoopStepThreadRE(rer, qm, re, code, endl, inp, t, th, pc);
    var th' := th.(pc := th.pc + 1);
    assert vms2.active == [th'] + vms.active[1..];

    // The tree step: pts_active with the unchanged gm.
    var na := [(t.t, gm)];
    assert PT.TreeBfsStep(t, gm, LC.Idx(inp)) == PT.StepActive(na);
    pts1 := PT.PTS(inp, na + ta[1..], best, tb, SS.AddSeenTrees(seen, t));
    assert PT.PikeTreeStep(pts, pts1);

    // Backbones.
    BBTick(vms, s1, ncap, nlook, nquant);
    assert th in vms.active;
    CM.ThreadClocksLEMono(th, vms.clock, s1.clock);
    BBReplaceHead(s1, th', ncap, nlook, nquant);

    // Active correspondence + seen + isblocked + remaining conjuncts.
    assert PIV.ActiveRepRE(rer, qm, re, code, inp, na + ta[1..], vms2.active) by {
      assert (na + ta[1..])[0] == (t.t, gm) && (na + ta[1..])[1..] == ta[1..];
      assert vms2.active[0] == th' && vms2.active[1..] == vms.active[1..];
      assert PIV.ThreadTracksGm(re, th', gm);
    }
    PIV.AddInclusionRE(rer, qm, code, inp, seen, vms.processed, t, pc, ea,
                       PIV.HdTreeOf(na + ta[1..]), PIV.HeadPcOf(vms2.active));
    IsblockedGrow(rer, qm, code, inp, seen, vms.isblocked, t);
    forall t2 | t2 in vms2.active ensures ThreadNestRE(re, code, endl, t2.pc, t2) {
      if t2 != th' { assert t2 in vms.active; }
    }
    forall tb2 | tb2 in vms2.blocked ensures ThreadNestRE(re, code, endl, tb2.0.pc + 1, tb2.0) {
      assert tb2 in vms.blocked;
    }
    forall t2 | t2 in vms2.active ensures EaColdOkRE(code, t2) {
      if t2 != th' { assert t2 in vms.active; }
      else if !t2.exit_allowed {
        assert !ea;
        assert th in vms.active && EaColdOkRE(code, th);
        assert !NI.ColdRE(code, pc);
        NotColdSucc(code, pc, pc + 1);
      }
    }
    assert PikeInvFullRE(rer, qm, re, code, endl, ngroups, str, pts1, vms2, ncap, nlook, nquant);
  }

  // =========================================================================
  // Per-case preservation: ENDLOOP with the flag unarmed — the tree is
  // Mismatch and dies via an empty pts_active; the VM drops the thread.
  // =========================================================================
  /** Per-case preservation for `EndLoop` with the flag unarmed: the tree is
      `Mismatch` and the branch dies on both sides via an empty
      `pts_active`. */
  lemma PreserveEndLoopKill(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
                            ngroups: nat, str: string, pts: PT.PikeTreeState, vms: AI.VmState,
                            s1: AI.VmState, vms2: AI.VmState,
                            ncap: int, nlook: int, nquant: int)
    returns (pts1: PT.PikeTreeState)
    requires !rer.multiline
    requires StaticOkRE(qm, re, code, endl)
    requires pts.PTS?
    requires PikeInvFullRE(rer, qm, re, code, endl, ngroups, str, pts, vms, ncap, nlook, nquant)
    requires |vms.active| > 0
    requires !AI.bpc_mem(vms.processed, vms.active[0].pc, vms.active[0].exit_allowed)
    requires s1 == vms.(clock := vms.clock + 1,
                        processed := AI.bpc_add(vms.processed, vms.active[0].pc, vms.active[0].exit_allowed))
    requires vms.active[0].pc >= 0
    requires NR.GetPcRE(code, vms.active[0].pc as nat) == Some(RB.EndLoop)
    requires !vms.active[0].exit_allowed
    requires vms2 == s1.(active := s1.active[1..])
    ensures PT.PikeTreeStep(pts, pts1)
    ensures pts1.PTS?
    ensures PikeInvFullRE(rer, qm, re, code, endl, ngroups, str, pts1, vms2, ncap, nlook, nquant)
  {
    var PTS(inp, ta, best, tb, seen) := pts;
    var th := vms.active[0];
    var ea := th.exit_allowed;
    var pc: nat := th.pc as nat;

    assert PIV.ActiveRepRE(rer, qm, re, code, inp, ta, vms.active);
    assert |ta| > 0;
    var t := ta[0].0;
    var gm := ta[0].1;
    assert TT.TreeThreadRE(rer, qm, code, inp, t, pc, ea);
    assert PIV.ActiveRepRE(rer, qm, re, code, inp, ta[1..], vms.active[1..]);
    assert ThreadNestRE(re, code, endl, th.pc, th);

    // The bundled EndLoop step (unarmed branch): the tree is Mismatch.
    EndLoopStepThreadRE(rer, qm, re, code, endl, inp, t, th, pc);
    assert t == LT.Mismatch;

    // The tree step: an EMPTY pts_active — the branch dies on both sides.
    assert PT.TreeBfsStep(t, gm, LC.Idx(inp)) == PT.StepActive([]);
    pts1 := PT.PTS(inp, [] + ta[1..], best, tb, SS.AddSeenTrees(seen, t));
    assert PT.PikeTreeStep(pts, pts1);
    assert [] + ta[1..] == ta[1..];

    // The full invariant at the successor.
    BBTick(vms, s1, ncap, nlook, nquant);
    BBDropHead(s1, ncap, nlook, nquant);
    PIV.AddInclusionRE(rer, qm, code, inp, seen, vms.processed, t, pc, ea,
                       PIV.HdTreeOf(ta[1..]), PIV.HeadPcOf(vms2.active));
    IsblockedGrow(rer, qm, code, inp, seen, vms.isblocked, t);
    forall t2 | t2 in vms2.active ensures ThreadNestRE(re, code, endl, t2.pc, t2) {
      assert t2 in vms.active;
    }
    forall tb2 | tb2 in vms2.blocked ensures ThreadNestRE(re, code, endl, tb2.0.pc + 1, tb2.0) {
      assert tb2 in vms.blocked;
    }
    assert PikeInvFullRE(rer, qm, re, code, endl, ngroups, str, pts1, vms2, ncap, nlook, nquant);
  }

  // =========================================================================
  // Per-case preservation: ANCHOR with the check satisfied — the tree passes
  // through AnchorPass; the VM continues the thread at pc + 1 unchanged.
  // =========================================================================
  /** Per-case preservation for a satisfied `AnchorAssertion`: the tree node is
      `AnchorPass` (zero-width), and the VM successor thread differs only in
      `pc` — registers, flag, and group map all carry through. */
  lemma PreserveAnchorPass(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
                           ngroups: nat, str: string, pts: PT.PikeTreeState, vms: AI.VmState,
                           s1: AI.VmState, vms2: AI.VmState, a: R.anchor,
                           ncap: int, nlook: int, nquant: int)
    returns (pts1: PT.PikeTreeState)
    requires !rer.multiline
    requires StaticOkRE(qm, re, code, endl)
    requires pts.PTS?
    requires PikeInvFullRE(rer, qm, re, code, endl, ngroups, str, pts, vms, ncap, nlook, nquant)
    requires |vms.active| > 0
    requires !AI.bpc_mem(vms.processed, vms.active[0].pc, vms.active[0].exit_allowed)
    requires s1 == vms.(clock := vms.clock + 1,
                        processed := AI.bpc_add(vms.processed, vms.active[0].pc, vms.active[0].exit_allowed))
    requires vms.active[0].pc >= 0
    requires NR.GetPcRE(code, vms.active[0].pc as nat) == Some(RB.AnchorAssertion(a))
    requires LAnc.is_satisfied(a, vms.context, LAnc.Forward)
    requires vms2 == s1.(active := [vms.active[0].(pc := vms.active[0].pc + 1)] + s1.active[1..])
    ensures PT.PikeTreeStep(pts, pts1)
    ensures pts1.PTS?
    ensures PikeInvFullRE(rer, qm, re, code, endl, ngroups, str, pts1, vms2, ncap, nlook, nquant)
  {
    var PTS(inp, ta, best, tb, seen) := pts;
    var th := vms.active[0];
    var ea := th.exit_allowed;
    var pc: nat := th.pc as nat;

    assert PIV.ActiveRepRE(rer, qm, re, code, inp, ta, vms.active);
    assert |ta| > 0;
    var t := ta[0].0;
    var gm := ta[0].1;
    assert TT.TreeThreadRE(rer, qm, code, inp, t, pc, ea);
    assert PIV.ActiveRepRE(rer, qm, re, code, inp, ta[1..], vms.active[1..]);
    assert PIV.ThreadTracksGm(re, th, gm);
    assert ThreadNestRE(re, code, endl, th.pc, th);

    // The VM-side check IS the tree-side check (the invariant's context window).
    assert PIV.ContextOkRE(str, vms.cp, vms.context);
    ContextOkIsCtxOf(str, vms.cp as nat);
    assert vms.context == TREP.CtxOf(inp);
    assert LAnc.is_satisfied(a, TREP.CtxOf(inp), LAnc.Forward);

    // The bundled anchor step (satisfied branch).
    AnchorStepThreadRE(rer, qm, re, code, endl, inp, t, th, pc, a);
    var th' := th.(pc := th.pc + 1);
    assert vms2.active == [th'] + vms.active[1..];

    // The tree step: pts_active with the unchanged gm.
    var na := [(t.t, gm)];
    assert PT.TreeBfsStep(t, gm, LC.Idx(inp)) == PT.StepActive(na);
    pts1 := PT.PTS(inp, na + ta[1..], best, tb, SS.AddSeenTrees(seen, t));
    assert PT.PikeTreeStep(pts, pts1);

    // Backbones.
    BBTick(vms, s1, ncap, nlook, nquant);
    assert th in vms.active;
    CM.ThreadClocksLEMono(th, vms.clock, s1.clock);
    BBReplaceHead(s1, th', ncap, nlook, nquant);

    // Active correspondence + seen + isblocked + remaining conjuncts.
    assert PIV.ActiveRepRE(rer, qm, re, code, inp, na + ta[1..], vms2.active) by {
      assert (na + ta[1..])[0] == (t.t, gm) && (na + ta[1..])[1..] == ta[1..];
      assert vms2.active[0] == th' && vms2.active[1..] == vms.active[1..];
      assert PIV.ThreadTracksGm(re, th', gm);
    }
    PIV.AddInclusionRE(rer, qm, code, inp, seen, vms.processed, t, pc, ea,
                       PIV.HdTreeOf(na + ta[1..]), PIV.HeadPcOf(vms2.active));
    IsblockedGrow(rer, qm, code, inp, seen, vms.isblocked, t);
    forall t2 | t2 in vms2.active ensures ThreadNestRE(re, code, endl, t2.pc, t2) {
      if t2 != th' { assert t2 in vms.active; }
    }
    forall tb2 | tb2 in vms2.blocked ensures ThreadNestRE(re, code, endl, tb2.0.pc + 1, tb2.0) {
      assert tb2 in vms.blocked;
    }
    forall t2 | t2 in vms2.active ensures EaColdOkRE(code, t2) {
      if t2 != th' { assert t2 in vms.active; }
      else if !t2.exit_allowed {
        assert !ea;
        assert th in vms.active && EaColdOkRE(code, th);
        assert !NI.ColdRE(code, pc);
        NotColdSucc(code, pc, pc + 1);
      }
    }
    assert PikeInvFullRE(rer, qm, re, code, endl, ngroups, str, pts1, vms2, ncap, nlook, nquant);
  }

  // =========================================================================
  // Per-case preservation: ANCHOR with the check unsatisfied — the tree is
  // Mismatch and dies via an empty pts_active; the VM drops the thread.
  // =========================================================================
  /** Per-case preservation for an unsatisfied `AnchorAssertion`: the tree is
      `Mismatch` and the branch dies on both sides via an empty `pts_active`. */
  lemma PreserveAnchorKill(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
                           ngroups: nat, str: string, pts: PT.PikeTreeState, vms: AI.VmState,
                           s1: AI.VmState, vms2: AI.VmState, a: R.anchor,
                           ncap: int, nlook: int, nquant: int)
    returns (pts1: PT.PikeTreeState)
    requires !rer.multiline
    requires StaticOkRE(qm, re, code, endl)
    requires pts.PTS?
    requires PikeInvFullRE(rer, qm, re, code, endl, ngroups, str, pts, vms, ncap, nlook, nquant)
    requires |vms.active| > 0
    requires !AI.bpc_mem(vms.processed, vms.active[0].pc, vms.active[0].exit_allowed)
    requires s1 == vms.(clock := vms.clock + 1,
                        processed := AI.bpc_add(vms.processed, vms.active[0].pc, vms.active[0].exit_allowed))
    requires vms.active[0].pc >= 0
    requires NR.GetPcRE(code, vms.active[0].pc as nat) == Some(RB.AnchorAssertion(a))
    requires !LAnc.is_satisfied(a, vms.context, LAnc.Forward)
    requires vms2 == s1.(active := s1.active[1..])
    ensures PT.PikeTreeStep(pts, pts1)
    ensures pts1.PTS?
    ensures PikeInvFullRE(rer, qm, re, code, endl, ngroups, str, pts1, vms2, ncap, nlook, nquant)
  {
    var PTS(inp, ta, best, tb, seen) := pts;
    var th := vms.active[0];
    var ea := th.exit_allowed;
    var pc: nat := th.pc as nat;

    assert PIV.ActiveRepRE(rer, qm, re, code, inp, ta, vms.active);
    assert |ta| > 0;
    var t := ta[0].0;
    var gm := ta[0].1;
    assert TT.TreeThreadRE(rer, qm, code, inp, t, pc, ea);
    assert PIV.ActiveRepRE(rer, qm, re, code, inp, ta[1..], vms.active[1..]);
    assert ThreadNestRE(re, code, endl, th.pc, th);

    // The VM-side check IS the tree-side check.
    assert PIV.ContextOkRE(str, vms.cp, vms.context);
    ContextOkIsCtxOf(str, vms.cp as nat);
    assert !LAnc.is_satisfied(a, TREP.CtxOf(inp), LAnc.Forward);

    // The bundled anchor step (unsatisfied branch): the tree is Mismatch.
    AnchorStepThreadRE(rer, qm, re, code, endl, inp, t, th, pc, a);
    assert t == LT.Mismatch;

    // The tree step: an EMPTY pts_active — the branch dies on both sides.
    assert PT.TreeBfsStep(t, gm, LC.Idx(inp)) == PT.StepActive([]);
    pts1 := PT.PTS(inp, [] + ta[1..], best, tb, SS.AddSeenTrees(seen, t));
    assert PT.PikeTreeStep(pts, pts1);
    assert [] + ta[1..] == ta[1..];

    // The full invariant at the successor.
    BBTick(vms, s1, ncap, nlook, nquant);
    BBDropHead(s1, ncap, nlook, nquant);
    PIV.AddInclusionRE(rer, qm, code, inp, seen, vms.processed, t, pc, ea,
                       PIV.HdTreeOf(ta[1..]), PIV.HeadPcOf(vms2.active));
    IsblockedGrow(rer, qm, code, inp, seen, vms.isblocked, t);
    forall t2 | t2 in vms2.active ensures ThreadNestRE(re, code, endl, t2.pc, t2) {
      assert t2 in vms.active;
    }
    forall tb2 | tb2 in vms2.blocked ensures ThreadNestRE(re, code, endl, tb2.0.pc + 1, tb2.0) {
      assert tb2 in vms.blocked;
    }
    assert PikeInvFullRE(rer, qm, re, code, endl, ngroups, str, pts1, vms2, ncap, nlook, nquant);
  }

  // =========================================================================
  // Per-case preservation: CONSUME, not dedup-dropped. The VM blocks the head
  // unconditionally; the tree side blocks a Read (matching char) or dies via
  // an empty pts_active (mismatch) — the filter keeps the lists aligned.
  // =========================================================================
  /** Per-case preservation for `Consume` when the pc is NOT yet in
      `isblocked`: the VM blocks the head unconditionally; the tree either
      blocks a matching `Read` (paired via `BlockedRepSnocRE`) or dies as
      `Mismatch`, keeping the blocked correspondence aligned. */
  lemma PreserveConsumeAdd(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
                           ngroups: nat, str: string, pts: PT.PikeTreeState, vms: AI.VmState,
                           s1: AI.VmState, ce: RC.char_expectation, vms2: AI.VmState,
                           ncap: int, nlook: int, nquant: int)
    returns (pts1: PT.PikeTreeState)
    requires !rer.multiline
    requires StaticOkRE(qm, re, code, endl)
    requires pts.PTS?
    requires PikeInvFullRE(rer, qm, re, code, endl, ngroups, str, pts, vms, ncap, nlook, nquant)
    requires |vms.active| > 0
    requires !AI.bpc_mem(vms.processed, vms.active[0].pc, vms.active[0].exit_allowed)
    requires s1 == vms.(clock := vms.clock + 1,
                        processed := AI.bpc_add(vms.processed, vms.active[0].pc, vms.active[0].exit_allowed))
    requires vms.active[0].pc >= 0
    requires NR.GetPcRE(code, vms.active[0].pc as nat) == Some(RB.Consume(ce))
    requires !AI.pc_mem(s1.isblocked, vms.active[0].pc)
    requires vms2 == s1.(blocked := [(vms.active[0], ce)] + s1.blocked,
                         isblocked := AI.pc_add(s1.isblocked, vms.active[0].pc),
                         active := s1.active[1..])
    ensures PT.PikeTreeStep(pts, pts1)
    ensures pts1.PTS?
    ensures PikeInvFullRE(rer, qm, re, code, endl, ngroups, str, pts1, vms2, ncap, nlook, nquant)
  {
    var PTS(inp, ta, best, tb, seen) := pts;
    var th := vms.active[0];
    var ea := th.exit_allowed;
    var pc: nat := th.pc as nat;

    assert PIV.ActiveRepRE(rer, qm, re, code, inp, ta, vms.active);
    assert |ta| > 0;
    var t := ta[0].0;
    var gm := ta[0].1;
    assert TT.TreeThreadRE(rer, qm, code, inp, t, pc, ea);
    assert PIV.ActiveRepRE(rer, qm, re, code, inp, ta[1..], vms.active[1..]);
    assert PIV.ThreadTracksGm(re, th, gm);
    assert ThreadNestRE(re, code, endl, th.pc, th);

    // The bundled Consume step: Read or Mismatch by the current character.
    ConsumeStepThreadRE(rer, qm, re, code, endl, inp, t, th, pc, ce);

    // Shared backbone/bookkeeping.
    BBTick(vms, s1, ncap, nlook, nquant);
    BBBlockHead(s1, ce, ncap, nlook, nquant);
    IsblockedGrow(rer, qm, code, inp, seen, vms.isblocked, t);
    ReversePrepend((th, ce), vms.blocked);
    MatchingBlockedSnoc(LC.Reverse(vms.blocked), (th, ce), inp);

    // The new isblocked entry pc is covered by the freshly-seen head tree.
    assert IsblockedInclusionRE(rer, qm, code, inp, SS.AddSeenTrees(seen, t), vms2.isblocked) by {
      forall pc0: nat | AI.pc_mem(vms2.isblocked, pc0)
        ensures exists t0: LT.Tree, b0: bool ::
          SS.Inseen(SS.AddSeenTrees(seen, t), t0) && TT.TreeThreadRE(rer, qm, code, inp, t0, pc0, b0)
      {
        PIV.PcAddMemFwd(s1.isblocked, th.pc, pc0);
        if pc0 == pc {
          SS.InAdd(seen, t, t);
          assert SS.Inseen(SS.AddSeenTrees(seen, t), t) && TT.TreeThreadRE(rer, qm, code, inp, t, pc0, ea);
        } else {
          assert AI.pc_mem(vms.isblocked, pc0);
          var t0: LT.Tree, b0: bool :| SS.Inseen(seen, t0) && TT.TreeThreadRE(rer, qm, code, inp, t0, pc0, b0);
          SS.InAdd(seen, t0, t);
        }
      }
    }

    if AR.ReadCharE(ce, inp).Some? {
      // MATCHING: pts_blocked pairs the appended entries.
      var (c, nextinp0) := AR.ReadCharE(ce, inp).value;
      assert t.Read? && t.c == c;
      assert PT.TreeBfsStep(t, gm, LC.Idx(inp)) == PT.StepBlocked(t.t);
      pts1 := PT.PTS(inp, ta[1..], best, tb + [(t.t, gm)], SS.AddSeenTrees(seen, t));
      assert PT.PikeTreeStep(pts, pts1);

      // Blocked correspondence: the filter gains exactly the new pair.
      forall nextinp | LC.AdvanceInput(inp, WP.Forward) == Some(nextinp)
        ensures PIV.BlockedRepRE(rer, qm, re, code, inp, nextinp, tb + [(t.t, gm)],
                                 PIV.MatchingBlocked(LC.Reverse(vms2.blocked), inp))
      {
        assert nextinp == nextinp0;
        assert PIV.MatchingBlocked(LC.Reverse(vms2.blocked), inp)
            == PIV.MatchingBlocked(LC.Reverse(vms.blocked), inp) + [(th, ce)];
        BlockedRepSnocRE(rer, qm, re, code, inp, nextinp, tb,
                         PIV.MatchingBlocked(LC.Reverse(vms.blocked), inp), (t.t, gm), (th, ce));
      }
      assert |inp.next| > 0;                          // ReadCharE Some
      assert LC.AdvanceInput(inp, WP.Forward).Some?;

      PIV.AddInclusionRE(rer, qm, code, inp, seen, vms.processed, t, pc, ea,
                         PIV.HdTreeOf(ta[1..]), PIV.HeadPcOf(vms2.active));
      forall t2 | t2 in vms2.active ensures ThreadNestRE(re, code, endl, t2.pc, t2) {
        assert t2 in vms.active;
      }
      forall tb2 | tb2 in vms2.blocked ensures ThreadNestRE(re, code, endl, tb2.0.pc + 1, tb2.0) {
        if tb2 != (th, ce) { assert tb2 in vms.blocked; }
      }
      assert PikeInvFullRE(rer, qm, re, code, endl, ngroups, str, pts1, vms2, ncap, nlook, nquant);
    } else {
      // MISMATCH: the tree is Mismatch and dies; the doomed blocked thread is
      // invisible to the filter.
      assert t == LT.Mismatch;
      assert PT.TreeBfsStep(t, gm, LC.Idx(inp)) == PT.StepActive([]);
      pts1 := PT.PTS(inp, [] + ta[1..], best, tb, SS.AddSeenTrees(seen, t));
      assert PT.PikeTreeStep(pts, pts1);
      assert [] + ta[1..] == ta[1..];

      assert PIV.MatchingBlocked(LC.Reverse(vms2.blocked), inp)
          == PIV.MatchingBlocked(LC.Reverse(vms.blocked), inp);

      PIV.AddInclusionRE(rer, qm, code, inp, seen, vms.processed, t, pc, ea,
                         PIV.HdTreeOf(ta[1..]), PIV.HeadPcOf(vms2.active));
      forall t2 | t2 in vms2.active ensures ThreadNestRE(re, code, endl, t2.pc, t2) {
        assert t2 in vms.active;
      }
      forall tb2 | tb2 in vms2.blocked ensures ThreadNestRE(re, code, endl, tb2.0.pc + 1, tb2.0) {
        if tb2 != (th, ce) { assert tb2 in vms.blocked; }
      }
      assert PikeInvFullRE(rer, qm, re, code, endl, ngroups, str, pts1, vms2, ncap, nlook, nquant);
    }
  }

  // =========================================================================
  // Per-case preservation: CONSUME, dedup-DROPPED (the pc is already in
  // isblocked). The first blocker's tree covers this one (ea-independence),
  // so the tree side plays pts_skip; the new processed entry resolves LEFT.
  // =========================================================================
  /** Per-case preservation for `Consume` when the pc IS already in
      `isblocked` (RegElk dedups, Linden doesn't): the dropped thread is
      simulated by `pts_skip` using the first blocker's seen tree, via
      `ConsumeTreeEaIndep`. */
  lemma PreserveConsumeDrop(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
                            ngroups: nat, str: string, pts: PT.PikeTreeState, vms: AI.VmState,
                            s1: AI.VmState, ce: RC.char_expectation, vms2: AI.VmState,
                            ncap: int, nlook: int, nquant: int)
    returns (pts1: PT.PikeTreeState)
    requires !rer.multiline
    requires StaticOkRE(qm, re, code, endl)
    requires pts.PTS?
    requires PikeInvFullRE(rer, qm, re, code, endl, ngroups, str, pts, vms, ncap, nlook, nquant)
    requires |vms.active| > 0
    requires !AI.bpc_mem(vms.processed, vms.active[0].pc, vms.active[0].exit_allowed)
    requires s1 == vms.(clock := vms.clock + 1,
                        processed := AI.bpc_add(vms.processed, vms.active[0].pc, vms.active[0].exit_allowed))
    requires vms.active[0].pc >= 0
    requires NR.GetPcRE(code, vms.active[0].pc as nat) == Some(RB.Consume(ce))
    requires AI.pc_mem(s1.isblocked, vms.active[0].pc)
    requires vms2 == s1.(active := s1.active[1..])
    ensures PT.PikeTreeStep(pts, pts1)
    ensures pts1.PTS?
    ensures PikeInvFullRE(rer, qm, re, code, endl, ngroups, str, pts1, vms2, ncap, nlook, nquant)
  {
    var PTS(inp, ta, best, tb, seen) := pts;
    var th := vms.active[0];
    var ea := th.exit_allowed;
    var pc: nat := th.pc as nat;

    assert PIV.ActiveRepRE(rer, qm, re, code, inp, ta, vms.active);
    assert |ta| > 0;
    var t := ta[0].0;
    var gm := ta[0].1;
    assert TT.TreeThreadRE(rer, qm, code, inp, t, pc, ea);
    assert PIV.ActiveRepRE(rer, qm, re, code, inp, ta[1..], vms.active[1..]);

    // The first blocker at pc supplied the seen tree; ea-independence at a
    // Consume pc makes it THIS tree.
    assert IsblockedInclusionRE(rer, qm, code, inp, seen, vms.isblocked);
    assert AI.pc_mem(vms.isblocked, pc);
    var t0: LT.Tree, b0: bool :| SS.Inseen(seen, t0) && TT.TreeThreadRE(rer, qm, code, inp, t0, pc, b0);
    ConsumeTreeEaIndep(rer, qm, code, inp, t0, t, pc, b0, ea);
    assert SS.Inseen(seen, t);

    // The tree step: pts_skip.
    pts1 := PT.PTS(inp, ta[1..], best, tb, seen);
    assert PT.PikeTreeStep(pts, pts1);

    // The full invariant at the successor: the new processed entry resolves
    // LEFT (its tree is already seen); old entries via the skip promotion.
    BBTick(vms, s1, ncap, nlook, nquant);
    BBDropHead(s1, ncap, nlook, nquant);
    assert PIV.SeenInclusionRE(rer, qm, code, inp, seen, vms2.processed,
                               PIV.HdTreeOf(ta[1..]), PIV.HeadPcOf(vms2.active)) by {
      forall pc0: nat, bb0: bool | AI.bpc_mem(vms2.processed, pc0, bb0)
        ensures (exists t': LT.Tree :: SS.Inseen(seen, t')
                   && TT.TreeThreadRE(rer, qm, code, inp, t', pc0, bb0))
             || (TT.StuttersRE(pc0, code) && exists t': LT.Tree ::
                   PIV.StutterChainTo(code, pc0, PIV.HeadPcOf(vms2.active))
                   && PIV.HdTreeOf(ta[1..]) == Some(t')
                   && TT.TreeThreadRE(rer, qm, code, inp, t', pc0, bb0))
      {
        PIV.BpcAddMemFwd(vms.processed, th.pc, ea, pc0, bb0);
        if pc0 == pc && bb0 == ea {
          // the fresh entry: its tree is t, already seen.
        } else {
          assert AI.bpc_mem(vms.processed, pc0, bb0);
          if exists t': LT.Tree :: SS.Inseen(seen, t') && TT.TreeThreadRE(rer, qm, code, inp, t', pc0, bb0) {
          } else {
            // old right disjunct: the witness is the (now-skipped) head tree t,
            // which is seen — promote LEFT.
            var t': LT.Tree :| TT.StuttersRE(pc0, code) && PIV.StutterChainTo(code, pc0, pc)
              && PIV.HdTreeOf(ta) == Some(t') && TT.TreeThreadRE(rer, qm, code, inp, t', pc0, bb0);
            assert t' == t;
          }
        }
      }
    }
    forall t2 | t2 in vms2.active ensures ThreadNestRE(re, code, endl, t2.pc, t2) {
      assert t2 in vms.active;
    }
    forall tb2 | tb2 in vms2.blocked ensures ThreadNestRE(re, code, endl, tb2.0.pc + 1, tb2.0) {
      assert tb2 in vms.blocked;
    }
    assert PikeInvFullRE(rer, qm, re, code, endl, ngroups, str, pts1, vms2, ncap, nlook, nquant);
  }

  // =========================================================================
  // THE PRESERVATION INDUCTION. Walks FAdvanceEpsilon's own recursion; each
  // level exhibits zero-or-one PikeTreeStep via the matching case lemma and
  // chains the closure. Instructions outside the fragment are vacuous
  // (GenStepRE proves StepSpec, which is `false` for them).
  // =========================================================================
  /** THE preservation induction: walks `FAdvanceEpsilon`'s own recursion
      over the active-thread list, dispatching to the matching
      `Preserve*Case` lemma per instruction and chaining the `TrcRE` closure.
      Instructions outside the compiled star fragment are proven unreachable
      (`GenStepRE`'s `StepSpec` is `false` for them). */
  lemma InvariantPreservationRE(
      rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
      ngroups: nat, str: string, pts: PT.PikeTreeState, vms: AI.VmState,
      ov: LOr.OracleView, dir: LAnc.direction, ncap: int, nlook: int, nquant: int)
    returns (pts': PT.PikeTreeState)
    requires !rer.multiline
    requires StaticOkRE(qm, re, code, endl)
    requires SizesOkRE(re, ncap, nlook, nquant)
    requires pts.PTS?
    requires PikeInvFullRE(rer, qm, re, code, endl, ngroups, str, pts, vms, ncap, nlook, nquant)
    requires |vms.processed.true_set| == RB.size(code) && |vms.processed.false_set| == RB.size(code)
    requires dir == LAnc.Forward
    ensures TrcRE(pts, pts')
    ensures pts'.PTS?
    ensures PikeInvFullRE(rer, qm, re, code, endl, ngroups, str, pts',
                          AI.FAdvanceEpsilon(code, vms, ov, dir).0, ncap, nlook, nquant)
    decreases AI.unprocessed(vms.processed), |vms.active|
  {
    if |vms.active| == 0 {
      pts' := pts;
      return;
    }
    var th := vms.active[0];
    var ac := vms.active[1..];

    // Head bounds: the correspondence pins pc >= 0, the positional fact pins
    // pc <= endl < |code| — so the instruction fetch is in range.
    var PTS(inp, ta, best, tb, seen) := pts;
    assert PIV.ActiveRepRE(rer, qm, re, code, inp, ta, vms.active);
    assert |ta| > 0 && th.pc >= 0;
    assert ThreadNestRE(re, code, endl, th.pc, th);
    var pc: nat := th.pc as nat;
    assert pc <= endl < |code|;
    var i := RB.get_instr(code, th.pc);
    assert i == code[pc] && NR.GetPcRE(code, pc) == Some(i);
    var t := ta[0].0;
    var gm := ta[0].1;
    assert TT.TreeThreadRE(rer, qm, code, inp, t, pc, th.exit_allowed);

    if AI.bpc_mem(vms.processed, th.pc, th.exit_allowed) {
      var pts1 := PreserveSkipCase(rer, qm, re, code, endl, ngroups, str, pts, vms, ncap, nlook, nquant);
      pts' := InvariantPreservationRE(rer, qm, re, code, endl, ngroups, str,
                                      pts1, vms.(active := ac), ov, dir, ncap, nlook, nquant);
      TrcCons(pts, pts1, pts');
      return;
    }

    var s1 := vms.(clock := vms.clock + 1,
                   processed := AI.bpc_add(vms.processed, th.pc, th.exit_allowed));
    assert AI.unprocessed(s1.processed) <= AI.unprocessed(vms.processed)
        && (0 <= th.pc < RB.size(code) ==> AI.unprocessed(s1.processed) < AI.unprocessed(vms.processed))
      by { AI.UnprocessedAdd(vms.processed, th.pc, th.exit_allowed); }
    assert AI.unprocessed(s1.processed) < AI.unprocessed(vms.processed);
    assert |s1.processed.true_set| == RB.size(code) && |s1.processed.false_set| == RB.size(code);

    match i {
      case Consume(ce) =>
        var (nb, ni) := AI.add_thread(th, ce, s1.blocked, s1.isblocked);
        if AI.pc_mem(s1.isblocked, th.pc) {
          assert nb == s1.blocked && ni == s1.isblocked;
          var vms2 := s1.(blocked := nb, isblocked := ni, active := ac);
          assert vms2 == s1.(active := ac);
          var pts1 := PreserveConsumeDrop(rer, qm, re, code, endl, ngroups, str, pts, vms,
                                          s1, ce, vms2, ncap, nlook, nquant);
          pts' := InvariantPreservationRE(rer, qm, re, code, endl, ngroups, str,
                                          pts1, vms2, ov, dir, ncap, nlook, nquant);
          TrcCons(pts, pts1, pts');
        } else {
          assert nb == [(th, ce)] + s1.blocked && ni == AI.pc_add(s1.isblocked, th.pc);
          var vms2 := s1.(blocked := nb, isblocked := ni, active := ac);
          var pts1 := PreserveConsumeAdd(rer, qm, re, code, endl, ngroups, str, pts, vms,
                                         s1, ce, vms2, ncap, nlook, nquant);
          pts' := InvariantPreservationRE(rer, qm, re, code, endl, ngroups, str,
                                          pts1, vms2, ov, dir, ncap, nlook, nquant);
          TrcCons(pts, pts1, pts');
        }
      case Accept =>
        var vms2 := s1.(active := [], bestmatch := Some(th));
        var pts1 := PreserveAcceptCase(rer, qm, re, code, endl, ngroups, str, pts, vms,
                                       s1, vms2, ncap, nlook, nquant);
        pts' := pts1;
        TrcCons(pts, pts1, pts1);
        assert AI.FAdvanceEpsilon(code, vms, ov, dir).0 == vms2;
      case Jmp(x) =>
        var th' := th.(pc := x);
        var vms2 := s1.(active := [th'] + ac);
        PreserveStutterCase(rer, qm, re, code, endl, ngroups, str, pts, vms,
                            s1, th', vms2, ncap, nlook, nquant);
        pts' := InvariantPreservationRE(rer, qm, re, code, endl, ngroups, str,
                                        pts, vms2, ov, dir, ncap, nlook, nquant);
      case Fork(x, y) =>
        var newt := AI.Thread(x, th.capture_regs, th.look_regs, th.quant_regs, th.exit_allowed);
        var vms2 := s1.(active := [newt, th.(pc := y)] + ac);
        var pts1 := PreserveForkCase(rer, qm, re, code, endl, ngroups, str, pts, vms,
                                     s1, x, y, vms2, ncap, nlook, nquant);
        pts' := InvariantPreservationRE(rer, qm, re, code, endl, ngroups, str,
                                        pts1, vms2, ov, dir, ncap, nlook, nquant);
        TrcTrans(pts, pts1, pts');
      case SetRegisterToCP(reg) =>
        var th' := th.(capture_regs := AReg.set_reg(th.capture_regs, reg, Some(s1.cp), s1.clock),
                       pc := th.pc + 1);
        var vms2 := s1.(active := [th'] + ac);
        var pts1: PT.PikeTreeState;
        if reg % 2 == 0 {
          pts1 := PreserveOpenCase(rer, qm, re, code, endl, ngroups, str, pts, vms,
                                   s1, reg, vms2, ncap, nlook, nquant);
        } else {
          pts1 := PreserveCloseCase(rer, qm, re, code, endl, ngroups, str, pts, vms,
                                    s1, reg, vms2, ncap, nlook, nquant);
        }
        pts' := InvariantPreservationRE(rer, qm, re, code, endl, ngroups, str,
                                        pts1, vms2, ov, dir, ncap, nlook, nquant);
        TrcCons(pts, pts1, pts');
      case SetQuantToClock(q, bq) =>
        var ocp := if bq then Some(s1.cp) else None;
        var th' := th.(quant_regs := AReg.set_reg(th.quant_regs, q, ocp, s1.clock), pc := th.pc + 1);
        var vms2 := s1.(active := [th'] + ac);
        var pts1 := PreserveResetCase(rer, qm, re, code, endl, ngroups, str, pts, vms,
                                      s1, q, bq, vms2, ncap, nlook, nquant);
        pts' := InvariantPreservationRE(rer, qm, re, code, endl, ngroups, str,
                                        pts1, vms2, ov, dir, ncap, nlook, nquant);
        TrcCons(pts, pts1, pts');
      case CheckOracle(l) =>
        // The tree layer now HAS oracle rules (tr_lkpass/tr_lkfail), so the
        // contradiction no longer comes from StepSpec: it comes from the
        // fragment gate. `StaticOkRE` still admits only the plus fragment,
        // which compiles no oracle instruction anywhere in the block.
        NoOracleInstrAt(re, code, endl, pc);
        assert false;
        pts' := pts;
      case NegCheckOracle(l) =>
        NoOracleInstrAt(re, code, endl, pc);
        assert false;
        pts' := pts;
      case WriteOracle(l) =>
        assert !TT.StuttersRE(pc, code);
        GS.GenStepRE(rer, qm, code, inp, t, pc, th.exit_allowed);
        assert false;
        pts' := pts;
      case BeginLoop =>
        var th' := th.(exit_allowed := false, pc := th.pc + 1);
        var vms2 := s1.(active := [th'] + ac);
        PreserveStutterCase(rer, qm, re, code, endl, ngroups, str, pts, vms,
                            s1, th', vms2, ncap, nlook, nquant);
        pts' := InvariantPreservationRE(rer, qm, re, code, endl, ngroups, str,
                                        pts, vms2, ov, dir, ncap, nlook, nquant);
      case EndLoop =>
        if th.exit_allowed {
          var vms2 := s1.(active := [th.(pc := th.pc + 1)] + ac);
          var pts1 := PreserveEndLoopPass(rer, qm, re, code, endl, ngroups, str, pts, vms,
                                          s1, vms2, ncap, nlook, nquant);
          pts' := InvariantPreservationRE(rer, qm, re, code, endl, ngroups, str,
                                          pts1, vms2, ov, dir, ncap, nlook, nquant);
          TrcCons(pts, pts1, pts');
        } else {
          var vms2 := s1.(active := ac);
          var pts1 := PreserveEndLoopKill(rer, qm, re, code, endl, ngroups, str, pts, vms,
                                          s1, vms2, ncap, nlook, nquant);
          pts' := InvariantPreservationRE(rer, qm, re, code, endl, ngroups, str,
                                          pts1, vms2, ov, dir, ncap, nlook, nquant);
          TrcCons(pts, pts1, pts');
        }
      case CheckNullable(qid) =>
        assert !TT.StuttersRE(pc, code);
        GS.GenStepRE(rer, qm, code, inp, t, pc, th.exit_allowed);
        assert false;
        pts' := pts;
      case AnchorAssertion(a) =>
        if LAnc.is_satisfied(a, s1.context, dir) {
          var vms2 := s1.(active := [th.(pc := th.pc + 1)] + ac);
          var pts1 := PreserveAnchorPass(rer, qm, re, code, endl, ngroups, str, pts, vms,
                                         s1, vms2, a, ncap, nlook, nquant);
          pts' := InvariantPreservationRE(rer, qm, re, code, endl, ngroups, str,
                                          pts1, vms2, ov, dir, ncap, nlook, nquant);
          TrcCons(pts, pts1, pts');
        } else {
          var vms2 := s1.(active := ac);
          var pts1 := PreserveAnchorKill(rer, qm, re, code, endl, ngroups, str, pts, vms,
                                         s1, vms2, a, ncap, nlook, nquant);
          pts' := InvariantPreservationRE(rer, qm, re, code, endl, ngroups, str,
                                          pts1, vms2, ov, dir, ncap, nlook, nquant);
          TrcCons(pts, pts1, pts');
        }
      case Fail =>
        assert !TT.StuttersRE(pc, code);
        GS.GenStepRE(rer, qm, code, inp, t, pc, th.exit_allowed);
        assert false;
        pts' := pts;
    }
  }

  // =========================================================================
  // FConsume characterization: the survivors of the char check are exactly
  // the MATCHING FILTER of the (reversed) blocked list, resumed at pc+1 with
  // the loop flag re-armed, in discovery order. The double reversal (blocked
  // prepends during the phase, FConsume prepends survivors) cancels.
  // =========================================================================
  /** Turns a blocked list into the resumed active-thread list: re-arms
      `exit_allowed` and advances `pc` by one for every entry, in order. */
  ghost function ResumeAll(bl: seq<(AI.Thread, RC.char_expectation)>): seq<AI.Thread>
    decreases bl
  {
    if |bl| == 0 then []
    else [bl[0].0.(exit_allowed := true, pc := bl[0].0.pc + 1)] + ResumeAll(bl[1..])
  }

  /** Every resumed thread has its loop flag re-armed — the ea-at-backfork
      conjunct is vacuous for the whole resumed active list. */
  lemma ResumeAllEa(bl: seq<(AI.Thread, RC.char_expectation)>)
    ensures forall t | t in ResumeAll(bl) :: t.exit_allowed
    decreases bl
  {
    if |bl| > 0 { ResumeAllEa(bl[1..]); }
  }

  /** `ResumeAll` distributes over list append. */
  lemma ResumeAllApp(a: seq<(AI.Thread, RC.char_expectation)>, b: seq<(AI.Thread, RC.char_expectation)>)
    ensures ResumeAll(a + b) == ResumeAll(a) + ResumeAll(b)
    decreases a
  {
    if |a| == 0 {
      assert a + b == b;
    } else {
      assert (a + b)[0] == a[0] && (a + b)[1..] == a[1..] + b;
      ResumeAllApp(a[1..], b);
    }
  }

  /** Characterizes RegElk's `FConsume`: the survivors of the character check
      are exactly `ResumeAll` applied to the matching filter
      (`PIV.MatchingBlocked`) of the reversed blocked list — the double
      reversal (blocked list prepends, `FConsume` prepends survivors)
      cancels. */
  lemma FConsumeResumes(s: AI.VmState, inp: LC.Input)
    requires s.context.nextchar == (if |inp.next| == 0 then None else Some(inp.next[0]))
    ensures AI.FConsume(s)
         == s.(active := ResumeAll(PIV.MatchingBlocked(LC.Reverse(s.blocked), inp)) + s.active,
               blocked := [])
    decreases |s.blocked|
  {
    if |s.blocked| == 0 {
      assert LC.Reverse(s.blocked) == [];
      assert ResumeAll([]) + s.active == s.active;
    } else {
      var p := s.blocked[0];
      var t := p.0;
      var ce := p.1;
      var rest := s.blocked[1..];
      var s1 := s.(blocked := rest);
      // the char check agrees with ReadCharE on the same input position
      assert RC.is_accepted(s.context.nextchar, ce) <==> AR.ReadCharE(ce, inp).Some?;
      var s2 := if RC.is_accepted(s1.context.nextchar, ce)
                then s1.(active := [t.(exit_allowed := true, pc := t.pc + 1)] + s1.active)
                else s1;
      FConsumeResumes(s2, inp);
      // list algebra: Reverse prepend + filter snoc + ResumeAll append
      assert s.blocked == [p] + rest;
      ReversePrepend(p, rest);
      assert LC.Reverse(s.blocked) == LC.Reverse(rest) + [p];
      MatchingBlockedSnoc(LC.Reverse(rest), p, inp);
      if AR.ReadCharE(ce, inp).Some? {
        assert PIV.MatchingBlocked(LC.Reverse(s.blocked), inp)
            == PIV.MatchingBlocked(LC.Reverse(rest), inp) + [p];
        ResumeAllApp(PIV.MatchingBlocked(LC.Reverse(rest), inp), [p]);
        assert ResumeAll([p]) == [t.(exit_allowed := true, pc := t.pc + 1)];
        assert ResumeAll(PIV.MatchingBlocked(LC.Reverse(s.blocked), inp)) + s.active
            == ResumeAll(PIV.MatchingBlocked(LC.Reverse(rest), inp))
               + ([t.(exit_allowed := true, pc := t.pc + 1)] + s.active);
      } else {
        assert PIV.MatchingBlocked(LC.Reverse(s.blocked), inp)
            == PIV.MatchingBlocked(LC.Reverse(rest), inp) + [];
        assert PIV.MatchingBlocked(LC.Reverse(rest), inp) + []
            == PIV.MatchingBlocked(LC.Reverse(rest), inp);
      }
    }
  }

  // =========================================================================
  // Outer-loop sub-bricks.
  // =========================================================================
  // Transitivity via an explicit step-count witness (a least lemma cannot
  // carry a second, un-inducted closure hypothesis: body occurrences of the
  // focal predicate are prefix-rewritten).
  /** `TrcRE` indexed by an explicit step count `n` — needed because a
      `least lemma` cannot carry a second, un-inducted closure hypothesis
      alongside the focal predicate. */
  ghost predicate TrcN(a: PT.PikeTreeState, b: PT.PikeTreeState, n: nat)
    decreases n
  {
    (a == b && n == 0)
    || (n > 0 && exists z :: PT.PikeTreeStep(a, z) && TrcN(z, b, n - 1))
  }

  /** Every `TrcRE` chain has some finite step count witnessing it (`TrcN`). */
  least lemma TrcToN(a: PT.PikeTreeState, b: PT.PikeTreeState)
    requires TrcRE(a, b)
    ensures exists n: nat :: TrcN(a, b, n)
  {
    if a == b {
      assert TrcN(a, b, 0);
    } else {
      var z :| PT.PikeTreeStep(a, z) && TrcRE(z, b);
      TrcToN(z, b);
      var n: nat :| TrcN(z, b, n);
      assert TrcN(a, b, n + 1);
    }
  }

  /** A `TrcN` witness with an explicit count implies the plain closure `TrcRE`. */
  lemma TrcFromN(a: PT.PikeTreeState, b: PT.PikeTreeState, n: nat)
    requires TrcN(a, b, n)
    ensures TrcRE(a, b)
    decreases n
  {
    if a == b && n == 0 {
    } else {
      var z :| PT.PikeTreeStep(a, z) && TrcN(z, b, n - 1);
      TrcFromN(z, b, n - 1);
      TrcCons(a, z, b);
    }
  }

  /** `TrcN` is transitive, with the witnessed step counts adding. */
  lemma TrcNTrans(a: PT.PikeTreeState, b: PT.PikeTreeState, c: PT.PikeTreeState, n: nat, m: nat)
    requires TrcN(a, b, n)
    requires TrcN(b, c, m)
    ensures TrcN(a, c, n + m)
    decreases n
  {
    if a == b && n == 0 {
    } else {
      var z :| PT.PikeTreeStep(a, z) && TrcN(z, b, n - 1);
      TrcNTrans(z, b, c, n - 1, m);
      assert TrcN(a, c, (n - 1 + m) + 1);
    }
  }

  /** `TrcRE` is transitive (proved by round-tripping through the counted
      `TrcN`, since the least-fixpoint `TrcRE` can't be inducted on twice
      directly). */
  lemma TrcTrans(a: PT.PikeTreeState, b: PT.PikeTreeState, c: PT.PikeTreeState)
    requires TrcRE(a, b)
    requires TrcRE(b, c)
    ensures TrcRE(a, c)
  {
    TrcToN(a, b);
    TrcToN(b, c);
    var n: nat :| TrcN(a, b, n);
    var m: nat :| TrcN(b, c, m);
    TrcNTrans(a, b, c, n, m);
    TrcFromN(a, c, n + m);
  }

  // The epsilon phase always ends with an empty active list: every branch
  // either recurses or returns with active == [].
  /** `FAdvanceEpsilon` always terminates with an empty `active` list — every
      instruction case either recurses or returns with `active == []` (used
      to justify that the epsilon phase is fully drained before consuming a
      character). */
  lemma FAdvanceEpsilonActiveEmpty(c: RB.code, s: AI.VmState, ov: LOr.OracleView, dir: LAnc.direction)
    requires |s.processed.true_set| == RB.size(c) && |s.processed.false_set| == RB.size(c)
    ensures AI.FAdvanceEpsilon(c, s, ov, dir).0.active == []
    decreases AI.unprocessed(s.processed), |s.active|
  {
    if |s.active| == 0 { return; }
    var t := s.active[0];
    var ac := s.active[1..];
    if AI.bpc_mem(s.processed, t.pc, t.exit_allowed) {
      FAdvanceEpsilonActiveEmpty(c, s.(active := ac), ov, dir);
      return;
    }
    var b0 := s.processed;
    var s1 := s.(clock := s.clock + 1, processed := AI.bpc_add(b0, t.pc, t.exit_allowed));
    assert AI.unprocessed(s1.processed) <= AI.unprocessed(b0)
        && (0 <= t.pc < RB.size(c) ==> AI.unprocessed(s1.processed) < AI.unprocessed(b0))
      by { AI.UnprocessedAdd(b0, t.pc, t.exit_allowed); }
    match RB.get_instr(c, t.pc) {
      case Consume(ce) =>
        var (nb, ni) := AI.add_thread(t, ce, s1.blocked, s1.isblocked);
        FAdvanceEpsilonActiveEmpty(c, s1.(blocked := nb, isblocked := ni, active := ac), ov, dir);
      case Accept =>
      case Jmp(x) =>
        FAdvanceEpsilonActiveEmpty(c, s1.(active := [t.(pc := x)] + ac), ov, dir);
      case Fork(x, y) =>
        var newt := AI.Thread(x, t.capture_regs, t.look_regs, t.quant_regs, t.exit_allowed);
        FAdvanceEpsilonActiveEmpty(c, s1.(active := [newt, t.(pc := y)] + ac), ov, dir);
      case SetRegisterToCP(reg) =>
        var t' := t.(capture_regs := AReg.set_reg(t.capture_regs, reg, Some(s1.cp), s1.clock), pc := t.pc + 1);
        FAdvanceEpsilonActiveEmpty(c, s1.(active := [t'] + ac), ov, dir);
      case SetQuantToClock(q, bq) =>
        var ocp := if bq then Some(s1.cp) else None;
        var t' := t.(quant_regs := AReg.set_reg(t.quant_regs, q, ocp, s1.clock), pc := t.pc + 1);
        FAdvanceEpsilonActiveEmpty(c, s1.(active := [t'] + ac), ov, dir);
      case CheckOracle(l) =>
        if LOr.view_get_oracle(ov, s1.cp, l) {
          var t' := t.(pc := t.pc + 1, look_regs := AReg.set_reg(t.look_regs, l, Some(s1.cp), s1.clock));
          FAdvanceEpsilonActiveEmpty(c, s1.(active := [t'] + ac), ov, dir);
        } else {
          FAdvanceEpsilonActiveEmpty(c, s1.(active := ac), ov, dir);
        }
      case NegCheckOracle(l) =>
        if LOr.view_get_oracle(ov, s1.cp, l) {
          FAdvanceEpsilonActiveEmpty(c, s1.(active := ac), ov, dir);
        } else {
          FAdvanceEpsilonActiveEmpty(c, s1.(active := [t.(pc := t.pc + 1)] + ac), ov, dir);
        }
      case WriteOracle(l) =>
        FAdvanceEpsilonActiveEmpty(c, s1.(active := ac), LOr.view_set_oracle(ov, s1.cp, l), dir);
      case BeginLoop =>
        FAdvanceEpsilonActiveEmpty(c, s1.(active := [t.(exit_allowed := false, pc := t.pc + 1)] + ac), ov, dir);
      case EndLoop =>
        if t.exit_allowed {
          FAdvanceEpsilonActiveEmpty(c, s1.(active := [t.(pc := t.pc + 1)] + ac), ov, dir);
        } else {
          FAdvanceEpsilonActiveEmpty(c, s1.(active := ac), ov, dir);
        }
      case CheckNullable(qid) =>
        if LCdn.cdn_get(s1.cdn, qid) {
          FAdvanceEpsilonActiveEmpty(c, s1.(active := [t.(pc := t.pc + 1)] + ac), ov, dir);
        } else {
          FAdvanceEpsilonActiveEmpty(c, s1.(active := ac), ov, dir);
        }
      case AnchorAssertion(a) =>
        if LAnc.is_satisfied(a, s1.context, dir) {
          FAdvanceEpsilonActiveEmpty(c, s1.(active := [t.(pc := t.pc + 1)] + ac), ov, dir);
        } else {
          FAdvanceEpsilonActiveEmpty(c, s1.(active := ac), ov, dir);
        }
      case Fail =>
        FAdvanceEpsilonActiveEmpty(c, s1.(active := ac), ov, dir);
    }
  }

  // A state with nothing to run returns its bestmatch after one idle unfold.
  /** A VM state with nothing left to run (`active`/`blocked` both empty)
      returns its current `bestmatch` unchanged after one idle unfold of
      `FFindMatch` — the case where the tree side finalizes while remaining
      input has no live threads. */
  lemma FFindMatchInert(c: RB.code, str: string, s: AI.VmState, ov: LOr.OracleView,
                        dir: LAnc.direction, cdn: LCdn.cdns)
    requires |s.processed.true_set| == RB.size(c) && |s.processed.false_set| == RB.size(c)
    requires dir.Forward? ==> s.context.nextchar == AI.get_char(str, s.cp)
    requires dir.Backward? ==> s.context.nextchar == AI.get_char(str, s.cp - 1)
    requires s.active == [] && s.blocked == []
    ensures AI.FFindMatch(c, str, s, ov, dir, cdn).0 == s.bestmatch
  {
    var s0 := s.(cdn := LCdn.build_cdn_v(cdn, s.cp, ov, s.context, dir));
    assert AI.FAdvanceEpsilon(c, s0, ov, dir) == (s0, ov);   // empty active: base case
  }

  // Membership carries through Reverse and the matching filter.
  /** Membership is preserved by `LC.Reverse`. */
  lemma ReverseMembership<T>(bl: seq<T>, p: T)
    requires p in LC.Reverse(bl)
    ensures p in bl
    decreases bl
  {
    if |bl| > 0 {
      if p in LC.Reverse(bl[1..]) { ReverseMembership(bl[1..], p); }
      else { assert p == bl[0]; }
    }
  }

  /** Every pair surviving `PIV.MatchingBlocked`'s filter was already in the
      original list. */
  lemma MatchingBlockedSubset(bl: seq<(AI.Thread, RC.char_expectation)>, inp: LC.Input,
                              p: (AI.Thread, RC.char_expectation))
    requires p in PIV.MatchingBlocked(bl, inp)
    ensures p in bl
    decreases bl
  {
    if |bl| > 0 {
      if p in PIV.MatchingBlocked(bl[1..], inp) { MatchingBlockedSubset(bl[1..], inp, p); }
      else { assert p == bl[0]; }
    }
  }

  // The blocked correspondence at the CURRENT position IS the active
  // correspondence at the NEXT position, through ResumeAll.
  /** The blocked correspondence (`BlockedRepRE`) at the current input
      position becomes the active correspondence (`ActiveRepRE`) at the next
      position once resumed via `ResumeAll` — the bridge used when the VM
      consumes a character. */
  lemma BlockedToActiveRE(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code,
                          inp: LC.Input, nextinp: LC.Input,
                          tl: seq<(LT.Tree, LG.GroupMap)>, bl: seq<(AI.Thread, RC.char_expectation)>)
    requires PIV.BlockedRepRE(rer, qm, re, code, inp, nextinp, tl, bl)
    ensures PIV.ActiveRepRE(rer, qm, re, code, nextinp, tl, ResumeAll(bl))
    decreases tl
  {
    if |tl| == 0 {
      assert |bl| == 0;
    } else {
      assert |bl| > 0;
      BlockedToActiveRE(rer, qm, re, code, inp, nextinp, tl[1..], bl[1..]);
      var r := bl[0].0.(exit_allowed := true, pc := bl[0].0.pc + 1);
      assert ResumeAll(bl)[0] == r && ResumeAll(bl)[1..] == ResumeAll(bl[1..]);
      assert r.pc >= 0;
      assert TT.TreeThreadRE(rer, qm, code, nextinp, tl[0].0, r.pc as nat, r.exit_allowed);
      assert PIV.ThreadTracksGm(re, r, tl[0].1);
    }
  }

  // The positional facts transfer from the blocked convention (pc+1) to the
  // resumed threads.
  /** The positional invariant recorded at the blocked convention (`pc+1`)
      transfers to the resumed threads produced by `ResumeAll` (now literally
      at that `pc`). */
  lemma ResumeAllNest(re: R.regex, code: RB.code, endl: nat,
                      bl: seq<(AI.Thread, RC.char_expectation)>)
    requires NR.NfaRepRE(re, code, 0, endl)
    requires forall p | p in bl :: ThreadNestRE(re, code, endl, p.0.pc + 1, p.0)
    ensures forall t2 | t2 in ResumeAll(bl) :: ThreadNestRE(re, code, endl, t2.pc, t2)
    decreases bl
  {
    if |bl| > 0 {
      assert forall p | p in bl[1..] :: p in bl;
      ResumeAllNest(re, code, endl, bl[1..]);
      var r := bl[0].0.(exit_allowed := true, pc := bl[0].0.pc + 1);
      assert bl[0] in bl;
      assert ThreadNestRE(re, code, endl, bl[0].0.pc + 1, bl[0].0);
      assert ThreadNestRE(re, code, endl, r.pc, r);
      forall t2 | t2 in ResumeAll(bl) ensures ThreadNestRE(re, code, endl, t2.pc, t2) {
        if t2 != r {
          assert t2 in ResumeAll(bl[1..]);
        }
      }
    }
  }

  // =========================================================================
  // THE OUTER LOOP: FFindMatch simulates the PikeTree machine to a final
  // state whose best leaf the VM's bestmatch denotes. Per position: the cdn
  // update is invariant-invisible; the epsilon phase runs the induction; then
  // either both sides finish (pts_final), or the VM idles on dead positions
  // while the tree finalizes (FFindMatchInert), or both advance a character
  // (pts_nextchar) with the blocked filter becoming the next active list.
  // =========================================================================
  /** THE outer-loop simulation: `FFindMatch` (the whole PikeVM search)
      simulates the `PikeTree` machine to its final state, per input
      position — either both sides finish, the VM idles on a dead tail while
      the tree finalizes (`FFindMatchInert`), or both advance one character
      (`pts_nextchar`) with the blocked filter becoming the next active list.
      This is the theorem `FindMatchSimRE`/`InvariantPreservationRE` exist to
      establish. */
  lemma FindMatchSimRE(
      rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, endl: nat,
      ngroups: nat, str: string, pts: PT.PikeTreeState, vms: AI.VmState,
      ov: LOr.OracleView, dir: LAnc.direction, cdn: LCdn.cdns,
      ncap: int, nlook: int, nquant: int)
    returns (bestT: Option<LT.Leaf>)
    requires StaticOkRE(qm, re, code, endl)
    requires SizesOkRE(re, ncap, nlook, nquant)
    requires pts.PTS?
    requires !rer.multiline
    requires PikeInvFullRE(rer, qm, re, code, endl, ngroups, str, pts, vms, ncap, nlook, nquant)
    requires |vms.processed.true_set| == RB.size(code) && |vms.processed.false_set| == RB.size(code)
    requires dir == LAnc.Forward
    requires vms.context.nextchar == AI.get_char(str, vms.cp)
    ensures TrcRE(pts, PT.PTS_final(bestT))
    ensures PIV.BestMatchRE(re, bestT, AI.FFindMatch(code, str, vms, ov, dir, cdn).0)
    decreases |str| - vms.cp
  {
    var s0 := vms.(cdn := LCdn.build_cdn_v(cdn, vms.cp, ov, vms.context, dir));
    // The invariant never reads cdn.
    assert PikeInvFullRE(rer, qm, re, code, endl, ngroups, str, pts, s0, ncap, nlook, nquant);
    var pts1 := InvariantPreservationRE(rer, qm, re, code, endl, ngroups, str,
                                        pts, s0, ov, dir, ncap, nlook, nquant);
    var (s1, ov1) := AI.FAdvanceEpsilon(code, s0, ov, dir);
    assert PikeInvFullRE(rer, qm, re, code, endl, ngroups, str, pts1, s1, ncap, nlook, nquant);
    FAdvanceEpsilonActiveEmpty(code, s0, ov, dir);
    assert s1.active == [];
    assert s1.cp == s0.cp == vms.cp && s1.context == vms.context;

    assert pts1.PTS?;
    var inp1 := pts1.inp;
    var ta1 := pts1.active;
    var best1 := pts1.best;
    var tb1 := pts1.blocked;
    var seen1 := pts1.seen;
    assert PIV.ActiveRepRE(rer, qm, re, code, inp1, ta1, s1.active);
    assert ta1 == [];
    assert inp1 == PIV.InpOfCp(str, s1.cp);
    assert 0 <= s1.cp <= |str|;
    assert PIV.BestMatchRE(re, best1, s1.bestmatch);

    if |s1.blocked| == 0 {
      // Both sides are done: the blocked filter is trivially empty.
      assert LC.Reverse(s1.blocked) == [];
      assert tb1 == [] by {
        if LC.AdvanceInput(inp1, WP.Forward).Some? {
          var nextinp :| LC.AdvanceInput(inp1, WP.Forward) == Some(nextinp);
          assert PIV.BlockedRepRE(rer, qm, re, code, inp1, nextinp, tb1,
                                  PIV.MatchingBlocked(LC.Reverse(s1.blocked), inp1));
          assert PIV.MatchingBlocked([], inp1) == [];
        }
      }
      bestT := best1;
      assert PT.PikeTreeStep(pts1, PT.PTS_final(best1));
      TrcSnoc(pts, pts1, PT.PTS_final(best1));
      assert AI.FFindMatch(code, str, vms, ov, dir, cdn).0 == s1.bestmatch;
    } else if s1.context.nextchar.None? {
      // End of input: the invariant pins the tree's blocked list empty.
      assert AI.get_char(str, vms.cp).None?;
      assert vms.cp >= |str|;
      assert s1.cp == |str|;
      assert inp1.next == str[s1.cp..] == [];
      assert LC.AdvanceInput(inp1, WP.Forward).None?;
      assert tb1 == [];
      bestT := best1;
      assert PT.PikeTreeStep(pts1, PT.PTS_final(best1));
      TrcSnoc(pts, pts1, PT.PTS_final(best1));
      assert AI.FFindMatch(code, str, vms, ov, dir, cdn).0 == s1.bestmatch;
    } else {
      // A real character remains: consume it.
      assert AI.get_char(str, vms.cp).Some?;
      assert vms.cp < |str|;
      assert inp1.next == str[s1.cp..] && |inp1.next| > 0;
      assert s1.context.nextchar == Some(inp1.next[0]);
      FConsumeResumes(s1, inp1);
      var s2 := AI.FConsume(s1);
      var filter := PIV.MatchingBlocked(LC.Reverse(s1.blocked), inp1);
      assert ResumeAll(filter) + s1.active == ResumeAll(filter);
      assert s2 == s1.(active := ResumeAll(filter), blocked := []);
      var s3 := s2.(processed := AI.init_bpcset(RB.size(code)),
                    isblocked := AI.init_pcset(RB.size(code)),
                    cdn := LCdn.init_cdn(), cp := AI.incr_cp(s2.cp, dir));
      var newchar := AI.get_char(str, s3.cp - AI.cp_offset(dir));
      var s4 := s3.(context := LAnc.update_context(s3.context, newchar));
      assert s4.cp == vms.cp + 1;
      assert s4.context.nextchar == AI.get_char(str, s4.cp);
      assert AI.FFindMatch(code, str, vms, ov, dir, cdn)
          == AI.FFindMatch(code, str, s4, ov1, dir, cdn);

      // The advanced input.
      AdvanceInpOfCpBridge(str, vms.cp);
      var nextinp := PT.NextInp(inp1);
      assert nextinp == PIV.InpOfCp(str, vms.cp + 1);
      assert LC.AdvanceInput(inp1, WP.Forward) == Some(nextinp);
      assert PIV.BlockedRepRE(rer, qm, re, code, inp1, nextinp, tb1, filter);

      if |tb1| == 0 {
        // Every blocked thread was doomed: the VM idles from here on with the
        // same bestmatch; the tree finalizes now.
        assert |filter| == 0;
        assert s4.active == [] && s4.blocked == [];
        FFindMatchInert(code, str, s4, ov1, dir, cdn);
        assert AI.FFindMatch(code, str, s4, ov1, dir, cdn).0 == s4.bestmatch == s1.bestmatch;
        bestT := best1;
        assert PT.PikeTreeStep(pts1, PT.PTS_final(best1));
        TrcSnoc(pts, pts1, PT.PTS_final(best1));
      } else {
        // pts_nextchar: the filter becomes the next position's active list.
        var pts2 := PT.PTS(nextinp, tb1, best1, [], SS.InitialSeenTrees);
        assert PT.PikeTreeStep(pts1, pts2);

        // Re-establish the full invariant at (pts2, s4).
        BlockedToActiveRE(rer, qm, re, code, inp1, nextinp, tb1, filter);
        assert PIV.ActiveRepRE(rer, qm, re, code, nextinp, tb1, s4.active);
        CM.FConsumeClocksLE(s1);
        CM.FConsumeRegsWf(s1, ncap, nlook, nquant);
        CM.FConsumeCapsLE(s1);
        assert CM.VmClocksLE(s4) by {
          assert s4.active == s2.active && s4.blocked == s2.blocked
              && s4.bestmatch == s2.bestmatch && s4.clock == s2.clock;
        }
        assert CM.VmRegsWf(s4, ncap, nlook, nquant) by {
          assert s4.active == s2.active && s4.blocked == s2.blocked && s4.bestmatch == s2.bestmatch;
        }
        assert CM.VmCapsLE(s4) by {
          CM.VmCapsLEAdvance(s2, s4);
        }
        assert forall t2 | t2 in s4.active :: ThreadNestRE(re, code, endl, t2.pc, t2) by {
          forall p | p in filter ensures ThreadNestRE(re, code, endl, p.0.pc + 1, p.0) {
            MatchingBlockedSubset(LC.Reverse(s1.blocked), inp1, p);
            ReverseMembership(s1.blocked, p);
            assert p in s1.blocked;
          }
          ResumeAllNest(re, code, endl, filter);
        }
        PIV.InitialInclusionRE(rer, qm, code, nextinp, PIV.HdTreeOf(tb1),
                               PIV.HeadPcOf(s4.active), RB.size(code));
        assert IsblockedInclusionRE(rer, qm, code, nextinp, SS.InitialSeenTrees, s4.isblocked) by {
          forall pc0: nat | AI.pc_mem(s4.isblocked, pc0)
            ensures exists t0: LT.Tree, b0: bool ::
              SS.Inseen(SS.InitialSeenTrees, t0) && TT.TreeThreadRE(rer, qm, code, nextinp, t0, pc0, b0)
          {
            assert s4.isblocked[pc0] == false;
            assert false;
          }
        }
        assert forall t2 | t2 in s4.active :: EaColdOkRE(code, t2) by {
          ResumeAllEa(filter);
          assert s4.active == ResumeAll(filter);
        }
        assert PikeInvFullRE(rer, qm, re, code, endl, ngroups, str, pts2, s4, ncap, nlook, nquant);

        // Recurse and chain.
        bestT := FindMatchSimRE(rer, qm, re, code, endl, ngroups, str,
                                pts2, s4, ov1, dir, cdn, ncap, nlook, nquant);
        TrcSnoc(pts, pts1, pts2);
        TrcTrans(pts, pts2, PT.PTS_final(bestT));
        assert PIV.BestMatchRE(re, bestT, AI.FFindMatch(code, str, s4, ov1, dir, cdn).0);
      }
    }
  }

  // NextInp of the cp-input is the cp+1-input (wrapper collecting the bridges).
  /** `PT.NextInp` of the input at position `cp` is the input at `cp+1` —
      collects the `PIV`/`PT` advance-input bridging facts into one lemma. */
  lemma AdvanceInpOfCpBridge(str: string, cp: nat)
    requires cp < |str|
    ensures PT.NextInp(PIV.InpOfCp(str, cp)) == PIV.InpOfCp(str, cp + 1)
    ensures LC.AdvanceInput(PIV.InpOfCp(str, cp), WP.Forward) == Some(PIV.InpOfCp(str, cp + 1))
  {
    PIV.AdvanceInpOfCp(str, cp);
    PT.AdvanceNext(PIV.InpOfCp(str, cp), PIV.InpOfCp(str, cp + 1));
  }

  // Initial establishment: the search-entry state satisfies the full package.
  /** Establishes `PikeInvFullRE` at the search's entry state: the initial
      single thread with all-fresh (`-1`) registers satisfies every backbone
      and the positional invariant at `pc` 0, and `isblocked` is vacuously
      covered. */
  lemma InitialPikeInvFullRE(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code,
                             endl: nat, ngroups: nat, str: string, tree: LT.Tree, vms: AI.VmState,
                             ncap: int, nlook: int, nquant: int)
    requires NR.PlusFragmentRE(re) && T.TransWf(re) && !rer.ignoreCase && !rer.multiline && AR.QmapOk(re, qm)
    requires code == CP.compile_to_bytecode(re)
    requires NR.NfaRepRE(re, code, 0, endl)
    requires NR.GetPcRE(code, endl) == Some(RB.Accept)
    requires TT.TreeThreadRE(rer, qm, code, LC.InitInput(str), tree, 0, false)
    requires vms.cp == 0
    requires vms.clock == 0
    requires ncap >= 0 && nlook >= 0 && nquant >= 0
    requires vms.active == [AI.init_thread(AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant))]
    requires vms.blocked == []
    requires vms.bestmatch.None?
    requires vms.processed == AI.init_bpcset(|code|)
    requires vms.isblocked == AI.init_pcset(|code|)
    requires vms.context == AI.cp_context(0, str, LAnc.Forward)
    ensures PikeInvFullRE(rer, qm, re, code, endl, ngroups, str,
                          PT.PikeTreeInitialState(tree, LC.InitInput(str)), vms, ncap, nlook, nquant)
  {
    // Base correspondence (proven earlier).
    PIV.InitialPikeInvRE(rer, qm, re, code, ngroups, str, tree, vms, ncap, nlook, nquant);

    var th := AI.init_thread(AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant));

    // Clock backbone at the entry state.
    assert CM.VmClocksLE(vms) by {
      CM.RegsClocksLEInit(ncap, 0);
      CM.RegsClocksLEInit(nlook, 0);
      CM.RegsClocksLEInit(nquant, 0);
      forall t | t in vms.active ensures CM.ThreadClocksLE(t, vms.clock) {
        assert t == th;
      }
    }

    // Register wf.
    assert CM.VmRegsWf(vms, ncap, nlook, nquant) by {
      PIV.CapRegWfInit(ncap);
      assert CM.ThreadRegsWf(th, ncap, nlook, nquant);
      forall t | t in vms.active ensures CM.ThreadRegsWf(t, ncap, nlook, nquant) {
        assert t == th;
      }
    }

    // Capture-value bound.
    assert CM.VmCapsLE(vms) by {
      var r := AReg.init_regs(ncap);
      assert CM.RegsValsLE(r, 0) by {
        forall k ensures AI.get_idx(r.a_cp, k) <= 0 {
          if 0 <= k < |r.a_cp| { assert r.a_cp[k] == -1; }
        }
      }
      forall t | t in vms.active ensures CM.RegsValsLE(t.capture_regs, vms.cp) {
        assert t == th;
      }
    }

    // Positional invariant at pc 0 with all-fresh clocks.
    assert ThreadNestRE(re, code, endl, 0, th) by {
      var cc := th.capture_regs.a_clk;
      var qc := th.quant_regs.a_clk;
      assert forall k :: AI.get_idx(cc, k) < 0 by {
        forall k ensures AI.get_idx(cc, k) < 0 {
          if 0 <= k < |cc| { assert cc[k] == -1; }
        }
      }
      NI.NestTopInit(re, code, endl, cc, qc);
      NR.NfaRepIncrRE(re, code, 0, endl);
    }
    forall t | t in vms.active ensures ThreadNestRE(re, code, endl, t.pc, t) {
      assert t == th;
    }

    // ea-at-backfork: the entry pc is never Cold, so the initial false-thread
    // is admissible.
    assert forall t | t in vms.active :: EaColdOkRE(code, t) by {
      NI.NotColdEntryRE(re, code, endl);
      forall t | t in vms.active ensures EaColdOkRE(code, t) {
        assert t == th;
      }
    }

    // isblocked inclusion: the initial pcset is all-false, vacuous.
    var pts := PT.PikeTreeInitialState(tree, LC.InitInput(str));
    assert IsblockedInclusionRE(rer, qm, code, pts.inp, pts.seen, vms.isblocked) by {
      forall pc0: nat | AI.pc_mem(vms.isblocked, pc0)
        ensures exists t: LT.Tree, b: bool ::
          SS.Inseen(pts.seen, t) && TT.TreeThreadRE(rer, qm, code, pts.inp, t, pc0, b)
      {
        assert vms.isblocked[pc0] == false;   // init_pcset is all-false
        assert false;
      }
    }
  }
}
