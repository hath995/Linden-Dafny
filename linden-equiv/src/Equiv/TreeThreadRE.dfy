// Phase 4b (layer 5): TreeThreadRE — "this tree and this VM position are about
// to execute the same continuation".
//
// PIVOT (plus campaign): a tree-thread IS a TreeRepRE-represented tree. The
// engine never resets exit_allowed through the do-while back edge (only
// BeginLoop resets it), so the spec-side BoolTree flag (CannotExit at free
// iterations) and the VM flag genuinely diverge inside do-while bodies; a
// per-step BoolTree witness cannot track the VM there. TreeRepRE-represented
// trees are instruction-keyed and deterministic per (pc, inp, ea) — the
// canonical checked trees the whole simulation now carries. The BoolTree
// machinery runs exactly once, at the entry (ActionsTreeRepRE's construction),
// and MainTheorem takes a single LeavesAgree hop back to the spec tree.
include "ActionsTreeRepRE.dfy"

/** Phase 4b layer 5 — `TreeThreadRE`: "this tree and this VM position are
    about to run the same continuation" — now definitionally `TreeRepRE`
    (the checked, instruction-keyed representation), with the API lemmas
    of the old BoolTree-witness formulation reproved as inversions. */
module LindenElkTreeThread {
  import opened Std.Wrappers
  import LW = WarblreRegExpRecord
  import LC = Chars
  import LG = Groups
  import LT = Tree
  import LS = Semantics
  import BS = BooleanSemantics
  import PS = PikeSubset
  import R = RegElkRegex
  import RB = Bytecode
  import NR = LindenElkNfaRep
  import AR = LindenElkActionsRep
  import TR = LindenElkTreeRep
  import ATR = LindenElkActionsTreeRep
  import L = Regex
  import CP = Compiler

  /** Inverse of `ActionsTreeRepRE.EaOf`: builds the `LoopBool` a given
      `exit_allowed` bit corresponds to. */
  function LbOf(ea: bool): BS.LoopBool {
    if ea then BS.CanExit else BS.CannotExit
  }

  /** `EaOf` and `LbOf` are mutually inverse: `EaOf(LbOf(ea)) == ea`. */
  lemma LbEaRoundtrip(ea: bool)
    ensures ATR.EaOf(LbOf(ea)) == ea
  {}

  /** Tree `t` at VM position `pc` (loop-exit flag `ea`) is *about to run the
      same continuation* as the code from `pc` — definitionally: `t` is the
      `TreeRepRE`-represented (checked) tree at `(pc, inp, ea)`. The `rer`
      parameter is kept for API stability (representation is `rer`-free; the
      semantic ties live at the entry construction). */
  ghost predicate TreeThreadRE(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                               t: LT.Tree, pc: nat, ea: bool)
  {
    TR.TreeRepRE(qm, t, code, pc, inp, ea)
  }

  // A tree-thread is TreeRepRE-represented — now definitional.
  /** A tree-thread is `TreeRepRE`-represented (definitional after the pivot). */
  lemma TreeThreadTreeRepRE(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                            t: LT.Tree, pc: nat, ea: bool)
    requires !rer.multiline
    requires TreeThreadRE(rer, qm, code, inp, t, pc, ea)
    ensures TR.TreeRepRE(qm, t, code, pc, inp, ea)
  {}

  // At a fixed (pc, ea, inp), all tree-threads carry the same tree.
  /** At a fixed `(pc, ea, inp)`, every tree-thread carries the *same* tree —
      `TreeRepRE` determinism. */
  lemma TtSameTreeRE(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                     t1: LT.Tree, t2: LT.Tree, pc: nat, ea: bool)
    requires !rer.multiline
    requires TreeThreadRE(rer, qm, code, inp, t1, pc, ea)
    requires TreeThreadRE(rer, qm, code, inp, t2, pc, ea)
    ensures t1 == t2
  {
    TR.TreeRepDetermRE(qm, code, pc, inp, ea, t1, t2);
  }

  // ===========================================================================
  // Stutter steps: Jmp and BeginLoop keep the same tree
  // ===========================================================================

  /** Whether the instruction at `pc` is a pure stutter step (`Jmp` or
      `BeginLoop`) that a tree-thread can cross without consuming any tree
      node. */
  predicate StuttersRE(pc: nat, code: RB.code) {
    match NR.GetPcRE(code, pc)
    case Some(Jmp(_)) => true
    case Some(BeginLoop) => true
    case _ => false
  }

  // At a BeginLoop pc only the tr_begin rule can apply (every other TreeRepRE
  // disjunct pins a different instruction), so the thread steps to pc+1 with
  // the flag forced false — exactly what the VM's BeginLoop does.
  /** At a `BeginLoop` pc the representation must be `tr_begin` — inversion
      gives the step to `pc+1` with `ea` forced `false` (matching the VM). */
  lemma TtAtBeginLoop(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                      t: LT.Tree, pc: nat, ea: bool)
    requires TreeThreadRE(rer, qm, code, inp, t, pc, ea)
    requires NR.GetPcRE(code, pc) == Some(RB.BeginLoop)
    ensures TreeThreadRE(rer, qm, code, inp, t, pc + 1, false)
  {
  }

  // At a Jmp pc only the tr_jmp rule can apply, and the tree-thread survives
  // the jump with ea unchanged.
  /** At a `Jmp` pc the representation must be `tr_jmp` — inversion gives the
      thread at the jump target with `ea` unchanged. */
  lemma TtAtJmp(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                t: LT.Tree, pc: nat, ea: bool, np: int)
    requires TreeThreadRE(rer, qm, code, inp, t, pc, ea)
    requires NR.GetPcRE(code, pc) == Some(RB.Jmp(np))
    ensures np >= 0 && TreeThreadRE(rer, qm, code, inp, t, np as nat, ea)
  {
    var nextpc: int :| NR.GetPcRE(code, pc) == Some(RB.Jmp(nextpc)) && nextpc >= 0
      && TR.TreeRepRE(qm, t, code, nextpc as nat, inp, ea);
    assert nextpc == np;
  }

  // ===========================================================================
  // BeginLoop shape facts (kept: used to pin code shapes around star blocks)
  // ===========================================================================

  // A regex whose representation starts at a BeginLoop pc pins no instruction
  // there, so its span must be empty (only Epsilon / Sequences of Epsilons).
  /** An `NfaRepL` span starting on a `BeginLoop` instruction must be empty
      (`pc1 == pc2`): every non-`Epsilon`/`Sequence` regex shape pins a
      conflicting instruction at its start, so only `Epsilon` (and sequences
      of it) can begin there. */
  lemma NfaRepLTransparentAtBeginLoop(rer: LW.RegExpRecord, qm: AR.QMap, r: L.Regex, code: RB.code, pc1: nat, pc2: nat)
    requires AR.NfaRepL(rer, qm, r, code, pc1, pc2)
    requires NR.GetPcRE(code, pc1) == Some(RB.BeginLoop)
    ensures pc1 == pc2
    decreases r
  {
    match r
    case Epsilon =>
    case Character(_) =>      // pins Consume at pc1: contradiction
    case Disjunction(_, _) => // pins Fork
    case Sequence(r1, r2) =>
      var e1: nat :| AR.NfaRepL(rer, qm, r1, code, pc1, e1) && AR.NfaRepL(rer, qm, r2, code, e1, pc2);
      NfaRepLTransparentAtBeginLoop(rer, qm, r1, code, pc1, e1);
      NfaRepLTransparentAtBeginLoop(rer, qm, r2, code, e1, pc2);
    case Quantified(_, _, _, _) =>  // pins Fork or SetQuantToClock
    case Group(_, _) =>             // pins SetRegisterToCP
    case LookaroundR(_, _) =>
    case AnchorR(_) =>
    case Backreference(_) =>
  }

  // No ActionsRepL derivation starts at a BeginLoop instruction.
  /** No `ActionsRepL` derivation starts at a `BeginLoop` instruction: the
      empty/`Jmp` bottoms and every `Acheck`/`Aclose` head pin a different
      instruction, and a transparent `Areg` head is peeled at the same `pc`
      via `NfaRepLTransparentAtBeginLoop`, reducing to the same contradiction. */
  least lemma ActionsRepNotAtBeginLoop(rer: LW.RegExpRecord, qm: AR.QMap, acts: LS.Actions, code: RB.code, pc: nat)
    requires AR.ActionsRepL(rer, qm, acts, code, pc)
    requires NR.GetPcRE(code, pc) == Some(RB.BeginLoop)
    ensures false
  {
    if |acts| == 0 && NR.GetPcRE(code, pc) == Some(RB.Accept) {
      // Accept != BeginLoop
    } else if |acts| > 0 && exists pcmid: nat :: AR.ActionRepL(rer, qm, acts[0], code, pc, pcmid) && AR.ActionsRepL(rer, qm, acts[1..], code, pcmid) {
      var pcmid: nat :| AR.ActionRepL(rer, qm, acts[0], code, pc, pcmid) && AR.ActionsRepL(rer, qm, acts[1..], code, pcmid);
      match acts[0]
      case Acheck(_) =>   // pins EndLoop or a backward fork: contradiction
      case Aclose(_) =>   // pins SetRegisterToCP: contradiction
      case Areg(r) =>
        NfaRepLTransparentAtBeginLoop(rer, qm, r, code, pc, pcmid);
        assert pcmid == pc;
        ActionsRepNotAtBeginLoop(rer, qm, acts[1..], code, pc);
    } else {
      // jump_bc pins Jmp: contradiction
      var pcstart: nat :| NR.GetPcRE(code, pc) == Some(RB.Jmp(pcstart)) && AR.ActionsRepL(rer, qm, acts, code, pcstart);
    }
  }
}
