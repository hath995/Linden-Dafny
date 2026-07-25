// Phase 4b (layer 6): the step-generation kernel — what each VM instruction
// does to a tree-thread.
//
// PIVOT (plus campaign): tree-threads are TreeRepRE-represented trees, and
// TreeRepRE is already instruction-keyed — so step generation is a direct
// INVERSION of the representation at the thread's pc (mirroring the case
// analysis of TreeRepDetermRE), not a BoolTree induction. The former fuel
// induction (GenStepF over action stacks) lives on only at the entry, inside
// ActionsTreeRepRE's construction.
//
// RegElk delta vs Linden's VM: Consume always blocks the thread (the read
// test happens later, in the consume phase), so the Consume case exposes the
// readability split. NEW: the Fork case splits by direction — only the
// do-while scheme emits a fork with a backward arm, where the checked tree
// is Progress(Choice(..)) when the thread may exit (tr_plus) and Mismatch
// when it may not (tr_plusfail).
include "TreeThreadRE.dfy"

/** The step-generation kernel (Phase 4b, layer 6): what each compiled VM
    instruction does to a tree-thread, read off the `TreeRepRE` disjunct the
    instruction at `pc` pins. */
module LindenElkGenStep {
  import opened Std.Wrappers
  import LW = WarblreRegExpRecord
  import LC = Chars
  import LG = Groups
  import L = Regex
  import LT = Tree
  import LS = Semantics
  import R = RegElkRegex
  import RB = Bytecode
  import CP = Compiler
  import NR = LindenElkNfaRep
  import AR = LindenElkActionsRep
  import RA = Anchors
  import T = LindenElkTranslate
  import TREP = LindenElkTreeRep
  import TT = LindenElkTreeThread
  import LOr = Oracle

  // What a tree-thread at a non-stuttering pc tells us, by instruction.
  /** What a tree-thread sitting at a non-stuttering `pc` implies, keyed on the
      instruction found there: e.g. `Accept` forces `Match`, a forward `Fork`
      forces `Choice` with both branches threaded onward, a BACKWARD-arm
      `Fork` (the do-while's) forces `Progress(Choice(..))` at `ea == true`
      (both branches threaded at `true`) and `Mismatch` at `ea == false`,
      `Consume` forces `Read` (or `Mismatch` if unreadable). False for
      instructions outside the fragment repertoire and for out-of-range pcs —
      a tree-thread can never sit there. */
  ghost predicate StepSpec(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                           t: LT.Tree, pc: nat, ea: bool)
  {
    match NR.GetPcRE(code, pc)
    case Some(Accept) => t == LT.Match
    case Some(Consume(ce)) =>
      (AR.ReadCharE(ce, inp).Some? ==>
         t.Read? && exists nextinp ::
           AR.ReadCharE(ce, inp) == Some((t.c, nextinp))
           && TT.TreeThreadRE(rer, qm, code, nextinp, t.t, pc + 1, true))
      && (AR.ReadCharE(ce, inp).None? ==> t == LT.Mismatch)
    case Some(Fork(x, y)) =>
      x >= 0 && y >= 0
      && if x as nat > pc && y as nat > pc then
           // forward fork: an alternation / optional-layer decision point
           t.Choice?
           && TT.TreeThreadRE(rer, qm, code, inp, t.t1, x as nat, ea)
           && TT.TreeThreadRE(rer, qm, code, inp, t.t2, y as nat, ea)
         else
           // backward-arm fork: the do-while's decision point; the checked
           // tree carries the dissolved progress guard with the Choice
           (ea ==> (t.Progress? && t.t.Choice?
                    && TT.TreeThreadRE(rer, qm, code, inp, t.t.t1, x as nat, true)
                    && TT.TreeThreadRE(rer, qm, code, inp, t.t.t2, y as nat, true)))
           && (!ea ==> t == LT.Mismatch)
    case Some(SetRegisterToCP(reg)) =>
      t.GroupActionT? && !t.g.Reset?
      && (t.g.Open? ==> reg == CP.start_reg(t.g.g as int))
      && (t.g.Close? ==> reg == CP.end_reg(t.g.g as int))
      && TT.TreeThreadRE(rer, qm, code, inp, t.t, pc + 1, ea)
    case Some(SetQuantToClock(qid, bb)) =>
      bb == false && t.GroupActionT? && t.g.Reset?
      && qid in qm.quants && qm.quants[qid] == t.g.gl
      && TT.TreeThreadRE(rer, qm, code, inp, t.t, pc + 1, ea)
    case Some(EndLoop) =>
      (ea ==> t.Progress? && TT.TreeThreadRE(rer, qm, code, inp, t.t, pc + 1, true))
      && (!ea ==> t == LT.Mismatch)
    case Some(AnchorAssertion(a)) =>
      (RA.is_satisfied(a, TREP.CtxOf(inp), RA.Forward) ==>
         t.AnchorPass? && t.a == T.TrAnchor(a)
         && TT.TreeThreadRE(rer, qm, code, inp, t.t, pc + 1, ea))
      && (!RA.is_satisfied(a, TREP.CtxOf(inp), RA.Forward) ==> t == LT.Mismatch)
    case Some(CheckOracle(lid)) =>
      // zero-width, like an anchor, but leaf-transparent: the continuation
      // tree IS the thread's tree (the LK wrapper is dissolved)
      (LOr.view_get_oracle(qm.ov, TREP.CpOf(inp), lid) ==>
         TT.TreeThreadRE(rer, qm, code, inp, t, pc + 1, ea))
      && (!LOr.view_get_oracle(qm.ov, TREP.CpOf(inp), lid) ==> t == LT.Mismatch)
    case Some(NegCheckOracle(lid)) =>
      // the negative gate passes on a CLEAR bit
      (!LOr.view_get_oracle(qm.ov, TREP.CpOf(inp), lid) ==>
         TT.TreeThreadRE(rer, qm, code, inp, t, pc + 1, ea))
      && (LOr.view_get_oracle(qm.ov, TREP.CpOf(inp), lid) ==> t == LT.Mismatch)
    case Some(Jmp(_)) => true        // excluded by !StuttersRE at use sites
    case Some(BeginLoop) => true     // excluded by !StuttersRE at use sites
    case Some(_) => false            // WriteOracle/CheckNullable/Fail:
                                     // unreachable in fragment-represented code
    case None => false               // out-of-range: a tree-thread pins an instr
  }

  // The step-generation theorem: inversion of TreeRepRE at the instruction.
  /** The step-generation theorem: any tree-thread at a non-stuttering `pc`
      satisfies `StepSpec` — by inverting which `TreeRepRE` disjunct the
      instruction at `pc` admits (mirrors `TreeRepDetermRE`'s case analysis). */
  lemma GenStepRE(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                  t: LT.Tree, pc: nat, ea: bool)
    requires !rer.multiline
    requires TT.TreeThreadRE(rer, qm, code, inp, t, pc, ea)
    requires !TT.StuttersRE(pc, code)
    ensures StepSpec(rer, qm, code, inp, t, pc, ea)
  {
    assert TREP.TreeRepRE(qm, t, code, pc, inp, ea);
    match NR.GetPcRE(code, pc)
    case Some(Accept) =>            // tr_match
    case Some(Consume(ce)) =>       // tr_read (Some) or tr_readfail (None)
      if AR.ReadCharE(ce, inp).Some? {
        var ce2, nextinp :| NR.GetPcRE(code, pc) == Some(RB.Consume(ce2))
          && AR.ReadCharE(ce2, inp) == Some((t.c, nextinp))
          && TREP.TreeRepRE(qm, t.t, code, pc + 1, nextinp, true);
        assert ce2 == ce;
      }
    case Some(Fork(x, y)) =>
      if x >= 0 && y >= 0 && x as nat > pc && y as nat > pc {
        // only tr_choice fits a forward fork
        var pcl: int, pcr: int :| NR.GetPcRE(code, pc) == Some(RB.Fork(pcl, pcr)) && pcl >= 0 && pcr >= 0
          && pcl as nat > pc && pcr as nat > pc
          && TREP.TreeRepRE(qm, t.t1, code, pcl as nat, inp, ea)
          && TREP.TreeRepRE(qm, t.t2, code, pcr as nat, inp, ea);
        assert pcl == x && pcr == y;
      } else if ea {
        // only tr_plus fits a backward-arm fork at ea == true
        var pcl: int, pcr: int :| NR.GetPcRE(code, pc) == Some(RB.Fork(pcl, pcr)) && pcl >= 0 && pcr >= 0
          && (pcl as nat <= pc || pcr as nat <= pc)
          && TREP.TreeRepRE(qm, t.t.t1, code, pcl as nat, inp, true)
          && TREP.TreeRepRE(qm, t.t.t2, code, pcr as nat, inp, true);
        assert pcl == x && pcr == y;
      } else {
        // only tr_plusfail fits a backward-arm fork at ea == false
        assert t == LT.Mismatch;
      }
    case Some(SetRegisterToCP(reg)) =>   // tr_open (even reg) xor tr_close (odd)
      assert t.GroupActionT?;
      // parity: start_reg(g) == 2g, end_reg(g) == 2g+1
      if t.g.Open? {
        assert reg == CP.start_reg(t.g.g as int);
      } else {
        assert t.g.Close? && reg == CP.end_reg(t.g.g as int);
      }
    case Some(SetQuantToClock(qid, bb)) =>   // tr_reset (only bb == false has a rule)
      var qid2: int :| NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(qid2, false))
        && qid2 in qm.quants && qm.quants[qid2] == t.g.gl
        && TREP.TreeRepRE(qm, t.t, code, pc + 1, inp, ea);
      assert qid2 == qid;
    case Some(EndLoop) =>            // tr_progress (ea) or tr_progressfail (!ea)
    case Some(AnchorAssertion(a)) => // tr_anchorpass or tr_anchorfail
      if RA.is_satisfied(a, TREP.CtxOf(inp), RA.Forward) {
        var a2: R.anchor :| NR.GetPcRE(code, pc) == Some(RB.AnchorAssertion(a2))
          && T.TrAnchor(a2) == t.a
          && RA.is_satisfied(a2, TREP.CtxOf(inp), RA.Forward)
          && TREP.TreeRepRE(qm, t.t, code, pc + 1, inp, ea);
        assert a2 == a;
      }
    case Some(CheckOracle(lid)) =>   // the gate rule, read off the instruction
    case Some(NegCheckOracle(lid)) =>
    case Some(Jmp(_)) =>             // excluded by !StuttersRE
    case Some(BeginLoop) =>          // excluded by !StuttersRE
    case Some(_) =>                  // no TreeRepRE disjunct: requires is false
    case None =>                     // no TreeRepRE disjunct: requires is false
  }
}
