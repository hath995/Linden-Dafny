// Phase 4b (layer 7, in progress): the PikeTree↔RegElk-VM simulation invariant
// and its Init/Preservation — port of Linden PikeEquiv.dfy. PikeTree/PikeEquiv
// are CODE-FREE and already reachable through LindenImports (Correctness.dfy ->
// PikeEquiv.dfy -> PikeTree.dfy); we IMPORT them as verified artifacts rather
// than re-port (per PROGRESS.md's architectural finding).
//
// This first brick lands the stutter-tameness replacement for Linden's
// StutterWf, which is FALSE for RegElk: its star back-edge is a real Jmp(pc1)
// pointing BACKWARD to its own fork (Linden hides that back-edge inside
// EndLoop(start), so all of its Jmps are forward). The RegElk-correct statement
// is: every Jmp either points forward OR targets a Fork.
include "GenStepRE.dfy"
include "RegsLaws.dfy"

/** Phase 4b (layer 7): the PikeTree ↔ RegElk-VM simulation invariant
    (`PikeInvRE`) and its initial-state instance — port of Linden
    PikeEquiv.dfy. Assembles all the machinery the preservation induction (in
    `PikeSimRE.dfy`) consumes: jump-target tameness, stutter-chain
    reachability, the seen-inclusion invariant, list/blocked correspondences,
    and the whole `filter_all`/`filter_capture` algebra that lets an engine
    thread's registers denote a Linden `GroupMap` (`GmOf`/`GmOfLive`). RegElk
    deltas vs Linden are marked throughout (the star back-`Jmp`, the
    blocked-order reversal, the `cp` ↔ `Input` bridge). */
module LindenElkPikeInv {
  import opened Std.Wrappers
  import R = RegElkRegex
  import RB = Bytecode
  import CP = Compiler
  import NR = LindenElkNfaRep
  import LTB = LindenElkLookTables
  import PT = PikeTree
  import PE = PikeEquiv
  import SS = SeenSets
  import LT = Tree
  import LC = Chars
  import LW = WarblreRegExpRecord
  import AR = LindenElkActionsRep
  import TT = LindenElkTreeThread
  import AI = ArrayInterp
  import LG = Groups
  import RC = Charclasses
  import AReg = Array_Regs
  import RL = LindenElkRegsLaws
  import LS = Semantics
  import STS = StrictSuffix
  import WP = WarblrePrimitives
  import LES = LindenElkSpec
  import BS = BooleanSemantics
  import PS = PikeSubset
  import T = LindenElkTranslate
  import LAnc = Anchors
  import ATR = LindenElkActionsTreeRep
  import L = Regex

  // Every Jmp inside a fragment representation either points strictly forward or
  // targets a Fork instruction. (Port of Linden's CompileJumps, which proves the
  // strictly-forward half only; the Fork disjunct is the RegElk star delta.)
  /** Every `Jmp` inside a fragment representation either points strictly
      forward or targets a `Fork`. The Fork disjunct is the RegElk star delta —
      Linden's `CompileJumps` proves only the strictly-forward half. */
  /** `CompileJumpsRE` for forced-copy chains: chain heads are clock-mark
      instructions, so any `Jmp` sits inside a copy's body. */
  lemma CompileJumpsMinRE(k: nat, qid: R.quantid, r1: R.regex, code: RB.code, pc1: nat, pc2: nat, pc: nat, next: int)
    requires NR.NfaRepMinRE(k, qid, r1, code, pc1, pc2)
    requires pc1 <= pc < pc2
    requires NR.GetPcRE(code, pc) == Some(RB.Jmp(next))
    ensures pc < next
         || (next >= 0 && NR.GetPcRE(code, next as nat).Some? && NR.GetPcRE(code, next as nat).value.Fork?)
    decreases CP.rsize(r1), k + 2
  {
    assert k > 0 by { if k == 0 { assert pc1 == pc2; } }
    var e1: nat :| NR.GetPcRE(code, pc1) == Some(RB.SetQuantToClock(qid, false))
      && NR.NfaRepRE(r1, code, pc1 + 1, e1)
      && NR.NfaRepMinRE(k - 1, qid, r1, code, e1, pc2);
    NR.NfaRepIncrRE(r1, code, pc1 + 1, e1);
    NR.NfaRepIncrMinRE(k - 1, qid, r1, code, e1, pc2);
    if pc1 + 1 <= pc < e1 {
      CompileJumpsRE(r1, code, pc1 + 1, e1, pc, next);
    } else if pc >= e1 {
      CompileJumpsMinRE(k - 1, qid, r1, code, e1, pc2, pc, next);
    }
    // pc == pc1: SetQuantToClock != Jmp contradicts.
  }

  /** `CompileJumpsRE` for optional-layer chains: layer heads are
      Fork/clock-mark/BeginLoop/EndLoop, so any `Jmp` sits inside a body. */
  lemma CompileJumpsOptRE(k: nat, greedy: bool, qid: R.quantid, r1: R.regex, code: RB.code, pc1: nat, pc2: nat, pc: nat, next: int)
    requires NR.NfaRepOptRE(k, greedy, qid, r1, code, pc1, pc2)
    requires pc1 <= pc < pc2
    requires NR.GetPcRE(code, pc) == Some(RB.Jmp(next))
    ensures pc < next
         || (next >= 0 && NR.GetPcRE(code, next as nat).Some? && NR.GetPcRE(code, next as nat).value.Fork?)
    decreases CP.rsize(r1), k + 2
  {
    assert k > 0 by { if k == 0 { assert pc1 == pc2; } }
    var e1: nat :| NR.GetPcRE(code, pc1) == Some(if greedy then RB.Fork(pc1 + 1, pc2) else RB.Fork(pc2, pc1 + 1))
      && NR.GetPcRE(code, pc1 + 1) == Some(RB.SetQuantToClock(qid, false))
      && NR.GetPcRE(code, pc1 + 2) == Some(RB.BeginLoop)
      && NR.NfaRepRE(r1, code, pc1 + 3, e1)
      && NR.GetPcRE(code, e1) == Some(RB.EndLoop)
      && NR.NfaRepOptRE(k - 1, greedy, qid, r1, code, e1 + 1, pc2);
    NR.NfaRepIncrRE(r1, code, pc1 + 3, e1);
    NR.NfaRepIncrOptRE(k - 1, greedy, qid, r1, code, e1 + 1, pc2);
    if pc1 + 3 <= pc < e1 {
      CompileJumpsRE(r1, code, pc1 + 3, e1, pc, next);
    } else if pc >= e1 + 1 {
      CompileJumpsOptRE(k - 1, greedy, qid, r1, code, e1 + 1, pc2, pc, next);
    }
    // pc in {pc1, pc1+1, pc1+2, e1}: Fork/SetQuantToClock/BeginLoop/EndLoop != Jmp.
  }

  lemma CompileJumpsRE(re: R.regex, code: RB.code, pc1: nat, pc2: nat, pc: nat, next: int)
    requires NR.NfaRepRE(re, code, pc1, pc2)
    requires pc1 <= pc < pc2
    requires NR.GetPcRE(code, pc) == Some(RB.Jmp(next))
    ensures pc < next
         || (next >= 0 && NR.GetPcRE(code, next as nat).Some? && NR.GetPcRE(code, next as nat).value.Fork?)
    decreases CP.rsize(re), 1
  {
    match re
    case Re_empty =>            // pc1 == pc2: the range is empty, no such pc
    case Re_character(_) =>     // Consume at pc1: GetPc(pc) == Jmp contradicts
    case Re_lookaround(_, _, _) => // NfaRepRE false
    case Re_anchor(_) =>        // NfaRepRE false
    case Re_alt(r1, r2) =>
      var e1: nat :| NR.GetPcRE(code, pc1) == Some(RB.Fork(pc1 + 1, e1 + 1))
        && NR.NfaRepRE(r1, code, pc1 + 1, e1) && NR.GetPcRE(code, e1) == Some(RB.Jmp(pc2))
        && NR.NfaRepRE(r2, code, e1 + 1, pc2);
      NR.NfaRepIncrRE(r1, code, pc1 + 1, e1);
      NR.NfaRepIncrRE(r2, code, e1 + 1, pc2);
      if pc == pc1 {              // Fork, not Jmp: contradiction
      } else if pc < e1 {
        CompileJumpsRE(r1, code, pc1 + 1, e1, pc, next);
      } else if pc == e1 {        // Jmp(pc2) == Jmp(next) ==> next == pc2 > e1 == pc
      } else {
        CompileJumpsRE(r2, code, e1 + 1, pc2, pc, next);
      }
    case Re_con(r1, r2) =>
      var e1: nat :| NR.NfaRepRE(r1, code, pc1, e1) && NR.NfaRepRE(r2, code, e1, pc2);
      NR.NfaRepIncrRE(r1, code, pc1, e1);
      NR.NfaRepIncrRE(r2, code, e1, pc2);
      if pc < e1 {
        CompileJumpsRE(r1, code, pc1, e1, pc, next);
      } else {
        CompileJumpsRE(r2, code, e1, pc2, pc, next);
      }
    case Re_quant(nul, qid, q, r1) =>
      if q.max.Some? {
        var em := NR.NfaRepREQuantInv(nul, qid, q, r1, code, pc1, pc2);
        var mn := q.min as nat;
        var kx := (q.max.value - q.min) as nat;
        NR.NfaRepIncrMinRE(mn, qid, r1, code, pc1, em);
        NR.NfaRepIncrOptRE(kx, q.greedy, qid, r1, code, em, pc2);
        if pc < em {
          CompileJumpsMinRE(mn, qid, r1, code, pc1, em, pc, next);
        } else {
          CompileJumpsOptRE(kx, q.greedy, qid, r1, code, em, pc2, pc, next);
        }
        return;
      }
      if !(q.min == 0 && q.max == None) {
        // the do-while: no Jmp anywhere - heads are the clock-mark and the
        // backward fork, everything else is Min-chain or body content
        var em, e1 := NR.NfaRepREPlusInv(nul, qid, q, r1, code, pc1, pc2);
        var mn1 := (q.min - 1) as nat;
        NR.NfaRepIncrMinRE(mn1, qid, r1, code, pc1, em);
        NR.NfaRepIncrRE(r1, code, em + 1, e1);
        if pc < em {
          CompileJumpsMinRE(mn1, qid, r1, code, pc1, em, pc, next);
        } else if em + 1 <= pc < e1 {
          CompileJumpsRE(r1, code, em + 1, e1, pc, next);
        }
        // pc == em (SetQuantToClock) or pc == e1 (Fork): not a Jmp
        return;
      }
      var e1: nat :| NR.GetPcRE(code, pc1) == Some(if q.greedy then RB.Fork(pc1 + 1, e1 + 2) else RB.Fork(e1 + 2, pc1 + 1))
        && NR.GetPcRE(code, pc1 + 1) == Some(RB.SetQuantToClock(qid, false))
        && NR.GetPcRE(code, pc1 + 2) == Some(RB.BeginLoop)
        && NR.NfaRepRE(r1, code, pc1 + 3, e1)
        && NR.GetPcRE(code, e1) == Some(RB.EndLoop)
        && NR.GetPcRE(code, e1 + 1) == Some(RB.Jmp(pc1))
        && pc2 == e1 + 2;
      NR.NfaRepIncrRE(r1, code, pc1 + 3, e1);
      if pc1 + 3 <= pc < e1 {
        CompileJumpsRE(r1, code, pc1 + 3, e1, pc, next);
      } else if pc == e1 + 1 {
        // The back-Jmp: GetPc(pc) == Jmp(pc1) == Jmp(next) ==> next == pc1, and
        // GetPc(code, pc1) == Some(Fork(...)) discharges the Fork disjunct.
        assert next == pc1;
      }
      // pc ∈ {pc1, pc1+1, pc1+2, e1}: Fork/SetQuantToClock/BeginLoop/EndLoop
      // (all ≠ Jmp) contradict GetPc(pc) == Jmp.
    case Re_capture(cid, r1) =>
      var e1: nat :| NR.GetPcRE(code, pc1) == Some(RB.SetRegisterToCP(CP.start_reg(cid)))
        && NR.NfaRepRE(r1, code, pc1 + 1, e1)
        && NR.GetPcRE(code, e1) == Some(RB.SetRegisterToCP(CP.end_reg(cid)))
        && pc2 == e1 + 1;
      NR.NfaRepIncrRE(r1, code, pc1 + 1, e1);
      if pc1 + 1 <= pc < e1 {
        CompileJumpsRE(r1, code, pc1 + 1, e1, pc, next);
      }
      // pc ∈ {pc1, e1}: SetRegisterToCP ≠ Jmp contradicts.
  }

  // Code-level stutter-tameness: the property preservation needs in place of
  // Linden's StutterWf. BeginLoop (the other stuttering instruction) always
  // advances to pc+1, so only Jmp targets can misbehave — and CompileStutterTameRE
  // shows compiled fragment code never lets them.
  /** Code-level stutter-tameness (RegElk's replacement for Linden's
      `StutterWf`): every `Jmp` in `code` points forward or targets a `Fork`.
      `BeginLoop`, the only other stuttering instruction, always advances to
      `pc+1`, so `Jmp` targets are the only ones that can misbehave. */
  ghost predicate StutterTameRE(code: RB.code) {
    forall pc: nat :: pc < |code| ==>
      match NR.GetPcRE(code, pc)
      case Some(Jmp(next)) =>
        pc < next
        || (next >= 0 && NR.GetPcRE(code, next as nat).Some? && NR.GetPcRE(code, next as nat).value.Fork?)
      case _ => true
  }

  // Compiled fragment bytecode is stutter-tame.
  /** Compiled fragment bytecode is `StutterTameRE`. */
  lemma CompileStutterTameRE(re: R.regex)
    requires NR.LookBehindFragmentRE(re)
    ensures StutterTameRE(CP.compile_to_bytecode(re))
  {
    var code := CP.compile_to_bytecode(re);
    var endl := CP.compile(re, 0, CP.Progress).1;
    NR.CompileToBytecodeRepLookBehind(re);  // NfaRepRE(re, code, 0, endl), GetPc(endl)==Accept, |code|==endl+1
    forall pc: nat | pc < |code|
      ensures match NR.GetPcRE(code, pc)
              case Some(Jmp(next)) =>
                pc < next
                || (next >= 0 && NR.GetPcRE(code, next as nat).Some? && NR.GetPcRE(code, next as nat).value.Fork?)
              case _ => true
    {
      match NR.GetPcRE(code, pc)
      case Some(Jmp(n)) =>
        // code[endl] == Accept ≠ Jmp, so pc ≠ endl; with pc < |code| == endl+1
        // that gives pc < endl, the range CompileJumpsRE needs.
        assert pc < endl as nat;
        CompileJumpsRE(re, code, 0, endl as nat, pc, n);
      case _ =>
    }
  }

  // ===========================================================================
  // Stutter chains — the reachability relation that replaces Linden's
  // `pc < currentpc` in SeenInclusion's stuttering disjunct. RegElk's star
  // back-Jmp means "below" is not a total order on stutter-reachable pcs, so we
  // track the actual chain of stutter steps instead.
  // ===========================================================================

  // The single successor of a stuttering instruction: a Jmp goes to its (non-
  // negative) target, a BeginLoop falls through to pc+1. Any other instruction
  // has no stutter successor (false), which also pins pc as a stuttering pc.
  /** The single stutter successor of `pc`: a `Jmp` goes to its (non-negative)
      target, a `BeginLoop` falls through to `pc+1`; any other instruction has
      no successor (`false`), which also pins `pc` as a stuttering pc. */
  ghost predicate StutterSuccIs(code: RB.code, pc: nat, npc: nat) {
    match NR.GetPcRE(code, pc)
    case Some(Jmp(n)) => n >= 0 && npc == n
    case Some(BeginLoop) => npc == pc + 1
    case Some(CheckOracle(_)) => npc == pc + 1
    case Some(NegCheckOracle(_)) => npc == pc + 1
    case _ => false
  }

  // A chain of ≥1 stutter steps from pc to target (every node but target
  // stutters; consecutive nodes are linked by StutterSuccIs).
  /** A chain of ≥1 stutter steps from `pc` to `target` (every node but
      `target` stutters; consecutive nodes linked by `StutterSuccIs`). Replaces
      Linden's `pc < currentpc`, which is false for RegElk's star back-`Jmp`. */
  least predicate StutterChainTo(code: RB.code, pc: nat, target: nat) {
    StutterSuccIs(code, pc, target)
    || (exists mid: nat :: StutterSuccIs(code, pc, mid) && StutterChainTo(code, mid, target))
  }

  // The source of a stutter chain is itself a stuttering instruction (Jmp or
  // BeginLoop) — inversion of StutterSuccIs at the head.
  /** The source of a stutter chain is itself a stuttering instruction (`Jmp`
      or `BeginLoop`) — inversion of `StutterSuccIs` at the head. */
  lemma StutterChainSource(code: RB.code, pc: nat, target: nat)
    requires StutterChainTo(code, pc, target)
    ensures NR.GetPcRE(code, pc).Some?
         && (NR.GetPcRE(code, pc).value.Jmp? || NR.GetPcRE(code, pc).value.BeginLoop?
             || NR.GetPcRE(code, pc).value.CheckOracle? || NR.GetPcRE(code, pc).value.NegCheckOracle?)
  {}

  // A stutter chain in tame code either strictly increases the pc or ends on a
  // Fork. (The Fork is where a star back-Jmp lands; it cannot be an interior
  // node because interior nodes must themselves stutter.)
  /** In tame code a stutter chain either strictly increases the pc or ends on
      a `Fork` (where a star back-`Jmp` lands; a Fork can't be an interior node
      since interior nodes must themselves stutter). */
  least lemma StutterChainForwardOrFork(code: RB.code, pc: nat, target: nat)
    requires StutterTameRE(code)
    requires StutterChainTo(code, pc, target)
    ensures pc < target || (NR.GetPcRE(code, target).Some? && NR.GetPcRE(code, target).value.Fork?)
  {
    if StutterSuccIs(code, pc, target) {
      // one step
      match NR.GetPcRE(code, pc)
      case Some(Jmp(n)) =>
        assert pc < |code|;              // GetPc is Some ⟹ in range; unlocks StutterTameRE at pc
        assert target == n && n >= 0;
      case Some(BeginLoop) =>
        assert target == pc + 1;
      case Some(CheckOracle(_)) =>
        assert target == pc + 1;
      case Some(NegCheckOracle(_)) =>
        assert target == pc + 1;
    } else {
      var mid: nat :| StutterSuccIs(code, pc, mid) && StutterChainTo(code, mid, target);
      StutterChainForwardOrFork(code, mid, target);   // IH: mid < target || code[target] Fork
      if NR.GetPcRE(code, target).Some? && NR.GetPcRE(code, target).value.Fork? {
        // right disjunct holds directly
      } else {
        assert mid < target;
        // the first step is forward or lands on a Fork; mid stutters (it heads a
        // chain), so it can't be a Fork ⟹ the step is forward ⟹ pc < mid < target
        StutterChainSource(code, mid, target);
        match NR.GetPcRE(code, pc)
        case Some(Jmp(n)) =>
          assert pc < |code|;
          assert mid == n && n >= 0;
        case Some(BeginLoop) =>
          assert mid == pc + 1;
        case Some(CheckOracle(_)) =>
          assert mid == pc + 1;
        case Some(NegCheckOracle(_)) =>
          assert mid == pc + 1;
      }
    }
  }

  // Tame code has no stutter cycles: a chain pc ->* pc would have to strictly
  // increase (impossible) or end on a Fork — but its source pc stutters, so pc
  // is not a Fork. Contradiction.
  /** Tame code has no stutter cycles: a chain `pc ->* pc` would have to
      strictly increase (impossible) or end on a `Fork` — but its source `pc`
      stutters, so it is not a Fork. */
  lemma NoStutterCycle(code: RB.code, pc: nat)
    requires StutterTameRE(code)
    ensures !StutterChainTo(code, pc, pc)
  {
    if StutterChainTo(code, pc, pc) {
      StutterChainForwardOrFork(code, pc, pc);   // pc < pc (false) OR code[pc] is Fork
      StutterChainSource(code, pc, pc);          // code[pc] is Jmp or BeginLoop
      assert false;
    }
  }

  // Membership constructors for StutterChainTo, as NORMAL lemmas (proving a
  // least predicate by one-level unfold). Used inside StutterChainExtend, whose
  // `least` induction would otherwise reinterpret these calls as prefix
  // predicates and block the construction.
  /** `StutterChainTo` base constructor as a normal lemma (one-level unfold), so
      it stays usable inside `least`-induction contexts. */
  lemma StutterChain1(code: RB.code, pc: nat, target: nat)
    requires StutterSuccIs(code, pc, target)
    ensures StutterChainTo(code, pc, target)
  {}

  /** `StutterChainTo` cons constructor as a normal lemma — prepends a step to
      an existing chain. */
  lemma StutterChainCons(code: RB.code, pc: nat, mid: nat, target: nat)
    requires StutterSuccIs(code, pc, mid)
    requires StutterChainTo(code, mid, target)
    ensures StutterChainTo(code, pc, target)
  {}

  // Extend a stutter chain by one step at its target end.
  /** Extend a stutter chain by one step at its `target` end. */
  least lemma StutterChainExtend(code: RB.code, pc: nat, target: nat, nextt: nat)
    requires StutterChainTo(code, pc, target)
    requires StutterSuccIs(code, target, nextt)
    ensures StutterChainTo(code, pc, nextt)
  {
    if StutterSuccIs(code, pc, target) {
      // pc -> target is one step; target -> nextt extends it to a 2-step chain
      StutterChain1(code, target, nextt);            // StutterChainTo(code, target, nextt)
      StutterChainCons(code, pc, target, nextt);     // StutterChainTo(code, pc, nextt)
    } else {
      var mid: nat :| StutterSuccIs(code, pc, mid) && StutterChainTo(code, mid, target);
      StutterChainExtend(code, mid, target, nextt);  // IH: StutterChainTo(code, mid, nextt)
      StutterChainCons(code, pc, mid, nextt);        // StutterChainTo(code, pc, nextt)
    }
  }

  // ===========================================================================
  // Seen-inclusion: every memoized VM (pc, exit_allowed) either has a seen tree
  // that is tree-threaded there, or is a stutter pc reachable-by-a-stutter-chain
  // from the current pc, holding the current tree. RegElk delta vs Linden: the
  // second disjunct uses StutterChainTo (not `pc < currentpc`, which is false
  // for the star back-Jmp), and this layer drops the GroupMap side (deferred).
  // The VM `seen` set is the Phase-3 model's `processed: Bpcset`.
  // ===========================================================================

  /** The seen-inclusion invariant: every memoized VM `(pc, exit_allowed)`
      either has a seen tree tree-threaded there, or is a stutter pc reachable
      by a `StutterChainTo` from the current pc, holding the current tree.
      RegElk delta: the second disjunct uses `StutterChainTo` (not Linden's
      `pc < currentpc`, false for the star back-`Jmp`), and this layer drops the
      GroupMap side. The VM `seen` set is the Phase-3 model's `processed`. */
  ghost predicate SeenInclusionRE(
      rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
      treeseen: SS.SeenTrees, processed: AI.Bpcset, current: Option<LT.Tree>, currentpc: nat)
  {
    forall pc: nat, b: bool :: AI.bpc_mem(processed, pc, b) ==>
      (exists t: LT.Tree :: SS.Inseen(treeseen, t) && TT.TreeThreadRE(rer, qm, code, inp, t, pc, b))
      || (TT.StuttersRE(pc, code)
          && exists t: LT.Tree ::
               StutterChainTo(code, pc, currentpc) && current == Some(t)
               && TT.TreeThreadRE(rer, qm, code, inp, t, pc, b))
  }

  // ----- Bpcset membership algebra (bpc_add adds exactly one (pc, ex) slot) -----

  /** `pc_add` adds exactly one slot: membership after the add means `pc0` is
      the added pc or was already present. */
  lemma PcAddMemFwd(pcs: AI.pcset, pc: int, pc0: int)
    requires AI.pc_mem(AI.pc_add(pcs, pc), pc0)
    ensures pc0 == pc || AI.pc_mem(pcs, pc0)
  {}

  /** `pc_add` is monotone: prior membership survives the add. */
  lemma PcAddMono(pcs: AI.pcset, pc: int, pc0: int)
    requires AI.pc_mem(pcs, pc0)
    ensures AI.pc_mem(AI.pc_add(pcs, pc), pc0)
  {}

  /** `bpc_add` adds exactly the `(pc, ex)` slot: membership after the add means
      `(pc0, b0)` is that slot or was already present. */
  lemma BpcAddMemFwd(bp: AI.Bpcset, pc: int, ex: bool, pc0: int, b0: bool)
    requires AI.bpc_mem(AI.bpc_add(bp, pc, ex), pc0, b0)
    ensures (pc0 == pc && b0 == ex) || AI.bpc_mem(bp, pc0, b0)
  {
    if b0 { PcAddMemFwd(bp.true_set, pc, pc0); } else { PcAddMemFwd(bp.false_set, pc, pc0); }
  }

  /** `bpc_add` is monotone: prior `(pc0, b0)` membership survives the add. */
  lemma BpcAddMono(bp: AI.Bpcset, pc: int, ex: bool, pc0: int, b0: bool)
    requires AI.bpc_mem(bp, pc0, b0)
    ensures AI.bpc_mem(AI.bpc_add(bp, pc, ex), pc0, b0)
  {
    if b0 { PcAddMono(bp.true_set, pc, pc0); } else { PcAddMono(bp.false_set, pc, pc0); }
  }

  // ----- The four seen-inclusion bookkeeping lemmas (ports of Linden's) -----

  // initial_inclusion: the empty (all-false) processed set satisfies inclusion
  // vacuously.
  /** `initial_inclusion`: the empty (all-false) `processed` set satisfies
      `SeenInclusionRE` vacuously. */
  lemma InitialInclusionRE(
      rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
      current: Option<LT.Tree>, currentpc: nat, n: int)
    ensures SeenInclusionRE(rer, qm, code, inp, SS.InitialSeenTrees, AI.init_bpcset(n), current, currentpc)
  {
    forall pc: nat, b: bool | AI.bpc_mem(AI.init_bpcset(n), pc, b)
      ensures false
    {
      // init_pcset(n) is all-false, so no (pc, b) is a member
    }
  }

  // add_inclusion: after memoizing the current tree at (pc, b), inclusion still
  // holds — every entry resolves to the LEFT (seen-tree) disjunct.
  /** `add_inclusion`: after memoizing the current tree at `(pc, b)`,
      `SeenInclusionRE` still holds — every entry resolves to the LEFT
      (seen-tree) disjunct. */
  lemma AddInclusionRE(
      rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
      treeseen: SS.SeenTrees, processed: AI.Bpcset, t: LT.Tree, pc: nat, b: bool,
      nextcurrent: Option<LT.Tree>, nextpc: nat)
    requires SeenInclusionRE(rer, qm, code, inp, treeseen, processed, Some(t), pc)
    requires TT.TreeThreadRE(rer, qm, code, inp, t, pc, b)
    ensures SeenInclusionRE(rer, qm, code, inp, SS.AddSeenTrees(treeseen, t),
                            AI.bpc_add(processed, pc, b), nextcurrent, nextpc)
  {
    forall pc0: nat, b0: bool | AI.bpc_mem(AI.bpc_add(processed, pc, b), pc0, b0)
      ensures (exists t': LT.Tree :: SS.Inseen(SS.AddSeenTrees(treeseen, t), t')
                 && TT.TreeThreadRE(rer, qm, code, inp, t', pc0, b0))
           || (TT.StuttersRE(pc0, code) && exists t': LT.Tree ::
                 StutterChainTo(code, pc0, nextpc) && nextcurrent == Some(t')
                 && TT.TreeThreadRE(rer, qm, code, inp, t', pc0, b0))
    {
      BpcAddMemFwd(processed, pc, b, pc0, b0);
      if pc0 == pc && b0 == b {
        SS.InAdd(treeseen, t, t);            // Inseen(AddSeenTrees(treeseen, t), t)
      } else {
        assert AI.bpc_mem(processed, pc0, b0);
        if exists t': LT.Tree :: SS.Inseen(treeseen, t') && TT.TreeThreadRE(rer, qm, code, inp, t', pc0, b0) {
          var t': LT.Tree :| SS.Inseen(treeseen, t') && TT.TreeThreadRE(rer, qm, code, inp, t', pc0, b0);
          SS.InAdd(treeseen, t', t);
        } else {
          // old right disjunct: current == Some(t) forces the witness tree to be t,
          // now memoized ⟹ new LEFT disjunct.
          var t': LT.Tree :| TT.StuttersRE(pc0, code) && StutterChainTo(code, pc0, pc)
            && Some(t) == Some(t') && TT.TreeThreadRE(rer, qm, code, inp, t', pc0, b0);
          SS.InAdd(treeseen, t', t);
        }
      }
    }
  }

  // seen-grow inclusion: adding a tree to the seen set alone (no new
  // processed slot) preserves inclusion — the left witnesses survive the add
  // and the stuttering disjunct is untouched. The do-while fork's double
  // memoization (the guard and its Choice) uses this for the second tree.
  /** Growing only the seen set preserves `SeenInclusionRE`. */
  lemma SeenGrowInclusionRE(
      rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
      treeseen: SS.SeenTrees, processed: AI.Bpcset, extra: LT.Tree,
      current: Option<LT.Tree>, currentpc: nat)
    requires SeenInclusionRE(rer, qm, code, inp, treeseen, processed, current, currentpc)
    ensures SeenInclusionRE(rer, qm, code, inp, SS.AddSeenTrees(treeseen, extra),
                            processed, current, currentpc)
  {
    forall pc0: nat, b0: bool | AI.bpc_mem(processed, pc0, b0)
      ensures (exists t': LT.Tree :: SS.Inseen(SS.AddSeenTrees(treeseen, extra), t')
                 && TT.TreeThreadRE(rer, qm, code, inp, t', pc0, b0))
           || (TT.StuttersRE(pc0, code) && exists t': LT.Tree ::
                 StutterChainTo(code, pc0, currentpc) && current == Some(t')
                 && TT.TreeThreadRE(rer, qm, code, inp, t', pc0, b0))
    {
      if exists t': LT.Tree :: SS.Inseen(treeseen, t') && TT.TreeThreadRE(rer, qm, code, inp, t', pc0, b0) {
        var t': LT.Tree :| SS.Inseen(treeseen, t') && TT.TreeThreadRE(rer, qm, code, inp, t', pc0, b0);
        SS.InAdd(treeseen, t', extra);
      }
    }
  }

  // skip_inclusion: skipping an already-seen tree leaves inclusion intact (the
  // stuttering disjunct promotes to LEFT because the tree is already memoized).
  /** `skip_inclusion`: skipping an already-seen tree leaves `SeenInclusionRE`
      intact (the stuttering disjunct promotes to LEFT since the tree is already
      memoized). */
  lemma SkipInclusionRE(
      rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
      treeseen: SS.SeenTrees, processed: AI.Bpcset, tree: LT.Tree, currentpc: nat,
      current: Option<LT.Tree>, nextpc: nat)
    requires SeenInclusionRE(rer, qm, code, inp, treeseen, processed, Some(tree), currentpc)
    requires SS.Inseen(treeseen, tree)
    ensures SeenInclusionRE(rer, qm, code, inp, treeseen, processed, current, nextpc)
  {
    forall pc0: nat, b0: bool | AI.bpc_mem(processed, pc0, b0)
      ensures (exists t': LT.Tree :: SS.Inseen(treeseen, t')
                 && TT.TreeThreadRE(rer, qm, code, inp, t', pc0, b0))
           || (TT.StuttersRE(pc0, code) && exists t': LT.Tree ::
                 StutterChainTo(code, pc0, nextpc) && current == Some(t')
                 && TT.TreeThreadRE(rer, qm, code, inp, t', pc0, b0))
    {
      if exists t': LT.Tree :: SS.Inseen(treeseen, t') && TT.TreeThreadRE(rer, qm, code, inp, t', pc0, b0) {
      } else {
        // old right disjunct gives the tree == `tree`, which is already seen ⟹ LEFT
        var t': LT.Tree :| TT.StuttersRE(pc0, code) && StutterChainTo(code, pc0, currentpc)
          && Some(tree) == Some(t') && TT.TreeThreadRE(rer, qm, code, inp, t', pc0, b0);
        assert SS.Inseen(treeseen, t');   // t' == tree
      }
    }
  }

  // stutter_inclusion: a stuttering thread memoizes (pc, b); its tree (not yet
  // seen) is recorded in the RIGHT disjunct, and the current pc advances one
  // stutter step to nextpc. RegElk delta: the step is StutterSuccIs (possibly a
  // backward star Jmp), so we extend the chain rather than rely on pc < nextpc.
  /** `stutter_inclusion`: a stuttering thread memoizes `(pc, b)`; its (not yet
      seen) tree is recorded in the RIGHT disjunct and the current pc advances
      one stutter step. RegElk delta: the step is `StutterSuccIs` (possibly a
      backward star `Jmp`), so we extend the chain rather than rely on
      `pc < nextpc`. */
  lemma StutterInclusionRE(
      rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
      treeseen: SS.SeenTrees, processed: AI.Bpcset, t: LT.Tree, pc: nat, b: bool, nextpc: nat)
    requires StutterSuccIs(code, pc, nextpc)
    requires SeenInclusionRE(rer, qm, code, inp, treeseen, processed, Some(t), pc)
    requires TT.StuttersRE(pc, code)
    requires TT.TreeThreadRE(rer, qm, code, inp, t, pc, b)
    ensures SeenInclusionRE(rer, qm, code, inp, treeseen, AI.bpc_add(processed, pc, b), Some(t), nextpc)
  {
    forall pc0: nat, b0: bool | AI.bpc_mem(AI.bpc_add(processed, pc, b), pc0, b0)
      ensures (exists t': LT.Tree :: SS.Inseen(treeseen, t')
                 && TT.TreeThreadRE(rer, qm, code, inp, t', pc0, b0))
           || (TT.StuttersRE(pc0, code) && exists t': LT.Tree ::
                 StutterChainTo(code, pc0, nextpc) && Some(t) == Some(t')
                 && TT.TreeThreadRE(rer, qm, code, inp, t', pc0, b0))
    {
      BpcAddMemFwd(processed, pc, b, pc0, b0);
      if pc0 == pc && b0 == b {
        // RIGHT disjunct: the just-stuttered thread, one step from nextpc.
        assert StutterChainTo(code, pc, nextpc);   // base case: StutterSuccIs(code, pc, nextpc)
      } else {
        assert AI.bpc_mem(processed, pc0, b0);
        if exists t': LT.Tree :: SS.Inseen(treeseen, t') && TT.TreeThreadRE(rer, qm, code, inp, t', pc0, b0) {
        } else {
          var t': LT.Tree :| TT.StuttersRE(pc0, code) && StutterChainTo(code, pc0, pc)
            && Some(t) == Some(t') && TT.TreeThreadRE(rer, qm, code, inp, t', pc0, b0);
          StutterChainExtend(code, pc0, pc, nextpc);   // StutterChainTo(code, pc0, nextpc)
        }
      }
    }
  }

  // ===========================================================================
  // List correspondence: a list of trees is paired position-wise with a list of
  // VM threads, each tree tree-threaded at its thread's (pc, exit_allowed).
  // gm-free (like TreeThreadRE) — the GroupMap denotation is layered on later.
  // Port of Linden's ListTreeThread and its LttLenEq / LttApp structural lemmas.
  // ===========================================================================

  /** A list of trees paired position-wise with a list of VM threads, each tree
      tree-threaded at its thread's `(pc, exit_allowed)`. gm-free (like
      `TreeThreadRE`) — the GroupMap denotation is layered on later. Port of
      Linden's `ListTreeThread`. */
  ghost predicate ListTreeThreadRE(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                                   tl: seq<LT.Tree>, vl: seq<AI.Thread>)
    decreases tl
  {
    (|tl| == 0 && |vl| == 0)
    || (|tl| > 0 && |vl| > 0 && vl[0].pc >= 0
        && TT.TreeThreadRE(rer, qm, code, inp, tl[0], vl[0].pc as nat, vl[0].exit_allowed)
        && ListTreeThreadRE(rer, qm, code, inp, tl[1..], vl[1..]))
  }

  /** A `ListTreeThreadRE` pairing forces the two lists to have equal length. */
  lemma LttLenEqRE(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                   tl: seq<LT.Tree>, vl: seq<AI.Thread>)
    requires ListTreeThreadRE(rer, qm, code, inp, tl, vl)
    ensures |tl| == |vl|
    decreases tl
  {
    if |tl| > 0 { LttLenEqRE(rer, qm, code, inp, tl[1..], vl[1..]); }
  }

  /** `ListTreeThreadRE` is closed under concatenation of two pairings. */
  lemma LttAppRE(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                 tl1: seq<LT.Tree>, tl2: seq<LT.Tree>, vl1: seq<AI.Thread>, vl2: seq<AI.Thread>)
    requires ListTreeThreadRE(rer, qm, code, inp, tl1, vl1)
    requires ListTreeThreadRE(rer, qm, code, inp, tl2, vl2)
    ensures ListTreeThreadRE(rer, qm, code, inp, tl1 + tl2, vl1 + vl2)
    decreases tl1
  {
    LttLenEqRE(rer, qm, code, inp, tl1, vl1);
    if |tl1| == 0 {
      assert tl1 + tl2 == tl2 && vl1 + vl2 == vl2;
    } else {
      LttAppRE(rer, qm, code, inp, tl1[1..], tl2, vl1[1..], vl2);
      assert (tl1 + tl2)[0] == tl1[0] && (tl1 + tl2)[1..] == tl1[1..] + tl2;
      assert (vl1 + vl2)[0] == vl1[0] && (vl1 + vl2)[1..] == vl1[1..] + vl2;
    }
  }

  // ===========================================================================
  // GroupMap denotation (step 3): a thread's registers denote a Linden GroupMap
  // EXACTLY as the RegElk engine reads out its final answer — via the engine's
  // own `filter_reset` over the whole AST (threshold -1), which resolves the
  // deferred capture resets by clock. (Confirmed against Node's ECMAScript
  // behavior: e.g. /((a)|(b))*/ on "ab" gives g1="b", g2=undefined, g3="b" — a
  // group matched only in an earlier `*` iteration is reset; filter_capture's
  // `start_clock < maxclock ⟹ reset` implements exactly that.)
  //
  // Because GmOf is DEFINED by the engine's filter_reset, it matches the engine
  // by construction — no separate reset model to keep in sync. Group gid uses
  // the filtered array's registers 2*gid (start) / 2*gid+1 (end); present iff
  // start >= 0, open iff end < 0. -1 encodes None throughout.
  // ===========================================================================

  /** Reads group `gid`'s `Range` out of the filtered register array: start =
      register `2*gid`, end = register `2*gid+1` (`None` when negative). */
  ghost function RangeFromArr(filtered: seq<int>, gid: nat): LG.Range
    requires AI.get_idx(filtered, CP.start_reg(gid)) >= 0
  {
    var e := AI.get_idx(filtered, CP.end_reg(gid));
    LG.Range(AI.get_idx(filtered, CP.start_reg(gid)) as nat, if e >= 0 then Some(e as nat) else None)
  }

  /** The `GroupMap` a thread's registers denote, DEFINED as the engine's own
      answer: run `filter_reset` over the whole AST (threshold `-1`) — resolving
      deferred capture resets by clock — then read each present group's
      `RangeFromArr`. Because it's the engine's readout by construction, it
      matches the engine with no separate reset model to keep in sync. */
  ghost function GmOf(ast: R.regex, caps: AReg.Regs, look: AReg.Regs, quant: AReg.Regs): LG.GroupMap
  {
    var filtered := AI.filter_reset(ast, caps, look, quant, -1);
    map gid: nat | 0 <= gid < |filtered| && AI.get_idx(filtered, CP.start_reg(gid)) >= 0
      :: RangeFromArr(filtered, gid)
  }

  // ----- filter_reset never turns an absent (negative) register present, so a
  // capture array that starts all-negative stays all-negative. -----

  /** Writing `-1` at `j` keeps a negative slot `i` negative. */
  lemma SetIdxNeg(regs: seq<int>, j: int, i: int)
    requires AI.get_idx(regs, i) < 0
    ensures AI.get_idx(AI.set_idx(regs, j, -1), i) < 0
  {}

  /** `filter_all` never turns an absent (negative) register present. */
  lemma FilterAllNeg(r: R.regex, regs: seq<int>, i: int)
    requires AI.get_idx(regs, i) < 0
    ensures AI.get_idx(AI.filter_all(r, regs), i) < 0
    decreases r
  {
    match r
    case Re_empty =>
    case Re_character(_) =>
    case Re_anchor(_) =>
    case Re_alt(r1, r2) => FilterAllNeg(r1, regs, i); FilterAllNeg(r2, AI.filter_all(r1, regs), i);
    case Re_con(r1, r2) => FilterAllNeg(r1, regs, i); FilterAllNeg(r2, AI.filter_all(r1, regs), i);
    case Re_quant(_, _, _, r1) => FilterAllNeg(r1, regs, i);
    case Re_capture(cid, r1) =>
      SetIdxNeg(regs, CP.start_reg(cid), i);
      FilterAllNeg(r1, AI.set_idx(regs, CP.start_reg(cid), -1), i);
    case Re_lookaround(_, _, r1) => FilterAllNeg(r1, regs, i);
  }

  /** `filter_capture` never turns an absent (negative) register present. */
  lemma FilterCaptureNeg(r: R.regex, cr: seq<int>, cc: seq<int>, lc: seq<int>, qc: seq<int>, mx: int, i: int)
    requires AI.get_idx(cr, i) < 0
    ensures AI.get_idx(AI.filter_capture(r, cr, cc, lc, qc, mx), i) < 0
    decreases r
  {
    match r
    case Re_empty =>
    case Re_character(_) =>
    case Re_anchor(_) =>
    case Re_alt(r1, r2) =>
      FilterCaptureNeg(r1, cr, cc, lc, qc, mx, i);
      FilterCaptureNeg(r2, AI.filter_capture(r1, cr, cc, lc, qc, mx), cc, lc, qc, mx, i);
    case Re_con(r1, r2) =>
      FilterCaptureNeg(r1, cr, cc, lc, qc, mx, i);
      FilterCaptureNeg(r2, AI.filter_capture(r1, cr, cc, lc, qc, mx), cc, lc, qc, mx, i);
    case Re_quant(nul, qid, q, r1) =>
      var qv := AI.get_idx(qc, qid);
      if qv < mx { FilterAllNeg(r1, cr, i); } else { FilterCaptureNeg(r1, cr, cc, lc, qc, qv, i); }
    case Re_capture(cid, r1) =>
      var start := AI.get_idx(cc, CP.start_reg(cid));
      if start < 0 {
        FilterAllNeg(r1, cr, i);
      } else if start < mx {
        SetIdxNeg(cr, CP.start_reg(cid), i);
        FilterAllNeg(r1, AI.set_idx(cr, CP.start_reg(cid), -1), i);
      } else {
        FilterCaptureNeg(r1, cr, cc, lc, qc, mx, i);
      }
    case Re_lookaround(lid, l, r1) =>
      var lv := AI.get_idx(lc, lid);
      if lv < 0 { FilterAllNeg(r1, cr, i); }
      else if lv < mx { FilterAllNeg(r1, cr, i); }
      else { FilterCaptureNeg(r1, cr, cc, lc, qc, -1, i); }
  }

  // ----- filter_reset only rewrites START (even) registers, so a group's END
  // register (2*gid+1, odd) passes through unchanged. The frame property the
  // gm-effect lemmas rest on: writing/closing an end reg doesn't perturb the
  // reset resolution of any group. -----

  /** Writing at `k` leaves any other index `j` unchanged. */
  lemma SetIdxKeepsOther(regs: seq<int>, k: int, j: int)
    requires k != j
    ensures AI.get_idx(AI.set_idx(regs, k, -1), j) == AI.get_idx(regs, j)
  {}

  /** `filter_all` rewrites only START (even) registers, so an odd END register
      `j` passes through unchanged. */
  lemma FilterAllKeepsOdd(r: R.regex, regs: seq<int>, j: int)
    requires j % 2 == 1
    ensures AI.get_idx(AI.filter_all(r, regs), j) == AI.get_idx(regs, j)
    decreases r
  {
    match r
    case Re_empty =>
    case Re_character(_) =>
    case Re_anchor(_) =>
    case Re_alt(r1, r2) => FilterAllKeepsOdd(r1, regs, j); FilterAllKeepsOdd(r2, AI.filter_all(r1, regs), j);
    case Re_con(r1, r2) => FilterAllKeepsOdd(r1, regs, j); FilterAllKeepsOdd(r2, AI.filter_all(r1, regs), j);
    case Re_quant(_, _, _, r1) => FilterAllKeepsOdd(r1, regs, j);
    case Re_capture(cid, r1) =>
      SetIdxKeepsOther(regs, CP.start_reg(cid), j);   // start_reg(cid) == 2*cid is even ≠ odd j
      FilterAllKeepsOdd(r1, AI.set_idx(regs, CP.start_reg(cid), -1), j);
    case Re_lookaround(_, _, r1) => FilterAllKeepsOdd(r1, regs, j);
  }

  /** `filter_capture` rewrites only START (even) registers, so an odd END
      register `j` passes through unchanged. */
  lemma FilterCaptureKeepsOdd(r: R.regex, cr: seq<int>, cc: seq<int>, lc: seq<int>, qc: seq<int>, mx: int, j: int)
    requires j % 2 == 1
    ensures AI.get_idx(AI.filter_capture(r, cr, cc, lc, qc, mx), j) == AI.get_idx(cr, j)
    decreases r
  {
    match r
    case Re_empty =>
    case Re_character(_) =>
    case Re_anchor(_) =>
    case Re_alt(r1, r2) =>
      FilterCaptureKeepsOdd(r1, cr, cc, lc, qc, mx, j);
      FilterCaptureKeepsOdd(r2, AI.filter_capture(r1, cr, cc, lc, qc, mx), cc, lc, qc, mx, j);
    case Re_con(r1, r2) =>
      FilterCaptureKeepsOdd(r1, cr, cc, lc, qc, mx, j);
      FilterCaptureKeepsOdd(r2, AI.filter_capture(r1, cr, cc, lc, qc, mx), cc, lc, qc, mx, j);
    case Re_quant(nul, qid, q, r1) =>
      var qv := AI.get_idx(qc, qid);
      if qv < mx { FilterAllKeepsOdd(r1, cr, j); } else { FilterCaptureKeepsOdd(r1, cr, cc, lc, qc, qv, j); }
    case Re_capture(cid, r1) =>
      var start := AI.get_idx(cc, CP.start_reg(cid));
      if start < 0 {
        FilterAllKeepsOdd(r1, cr, j);
      } else if start < mx {
        SetIdxKeepsOther(cr, CP.start_reg(cid), j);
        FilterAllKeepsOdd(r1, AI.set_idx(cr, CP.start_reg(cid), -1), j);
      } else {
        FilterCaptureKeepsOdd(r1, cr, cc, lc, qc, mx, j);
      }
    case Re_lookaround(lid, l, r1) =>
      var lv := AI.get_idx(lc, lid);
      if lv < 0 { FilterAllKeepsOdd(r1, cr, j); }
      else if lv < mx { FilterAllKeepsOdd(r1, cr, j); }
      else { FilterCaptureKeepsOdd(r1, cr, cc, lc, qc, -1, j); }
  }

  /** `filter_all` writes only the START registers of `r`'s OWN groups, so any
      register `k` that is no group's start register passes through unchanged. */
  lemma FilterAllAgreeOutsideOwn(r: R.regex, regs: seq<int>, k: int)
    requires k >= 0
    requires forall g: nat :: g in CapIds(r) ==> CP.start_reg(g) != k
    ensures AI.get_idx(AI.filter_all(r, regs), k) == AI.get_idx(regs, k)
    decreases r
  {
    match r
    case Re_empty => case Re_character(_) => case Re_anchor(_) =>
    case Re_alt(r1, r2) => FilterAllAgreeOutsideOwn(r1, regs, k); FilterAllAgreeOutsideOwn(r2, AI.filter_all(r1, regs), k);
    case Re_con(r1, r2) => FilterAllAgreeOutsideOwn(r1, regs, k); FilterAllAgreeOutsideOwn(r2, AI.filter_all(r1, regs), k);
    case Re_quant(_, _, _, r1) => FilterAllAgreeOutsideOwn(r1, regs, k);
    case Re_capture(cid, r1) =>
      assert CP.start_reg(cid) != k by { if cid >= 0 { assert cid as nat in CapIds(r); } else { assert CP.start_reg(cid) == 2 * cid < 0; } }
      SetIdxKeepsOther(regs, CP.start_reg(cid), k);
      FilterAllAgreeOutsideOwn(r1, AI.set_idx(regs, CP.start_reg(cid), -1), k);
    case Re_lookaround(_, _, r1) => FilterAllAgreeOutsideOwn(r1, regs, k);
  }

  /** `filter_capture` writes only the START registers of `r`'s OWN groups, so any
      register `k` that is no group's start register passes through unchanged.
      The frame that makes lookaround-body filtering invisible to outside groups. */
  lemma FilterCaptureAgreeOutsideOwn(r: R.regex, cr: seq<int>, cc: seq<int>, lc: seq<int>, qc: seq<int>, mx: int, k: int)
    requires k >= 0
    requires forall g: nat :: g in CapIds(r) ==> CP.start_reg(g) != k
    ensures AI.get_idx(AI.filter_capture(r, cr, cc, lc, qc, mx), k) == AI.get_idx(cr, k)
    decreases r
  {
    match r
    case Re_empty => case Re_character(_) => case Re_anchor(_) =>
    case Re_alt(r1, r2) =>
      FilterCaptureAgreeOutsideOwn(r1, cr, cc, lc, qc, mx, k);
      FilterCaptureAgreeOutsideOwn(r2, AI.filter_capture(r1, cr, cc, lc, qc, mx), cc, lc, qc, mx, k);
    case Re_con(r1, r2) =>
      FilterCaptureAgreeOutsideOwn(r1, cr, cc, lc, qc, mx, k);
      FilterCaptureAgreeOutsideOwn(r2, AI.filter_capture(r1, cr, cc, lc, qc, mx), cc, lc, qc, mx, k);
    case Re_quant(nul, qid, q, r1) =>
      var qv := AI.get_idx(qc, qid);
      if qv < mx { FilterAllAgreeOutsideOwn(r1, cr, k); } else { FilterCaptureAgreeOutsideOwn(r1, cr, cc, lc, qc, qv, k); }
    case Re_capture(cid, r1) =>
      assert CP.start_reg(cid) != k by { if cid >= 0 { assert cid as nat in CapIds(r); } else { assert CP.start_reg(cid) == 2 * cid < 0; } }
      var start := AI.get_idx(cc, CP.start_reg(cid));
      if start < 0 {
        FilterAllAgreeOutsideOwn(r1, cr, k);
      } else if start < mx {
        SetIdxKeepsOther(cr, CP.start_reg(cid), k);
        FilterAllAgreeOutsideOwn(r1, AI.set_idx(cr, CP.start_reg(cid), -1), k);
      } else {
        FilterCaptureAgreeOutsideOwn(r1, cr, cc, lc, qc, mx, k);
      }
    case Re_lookaround(lid, l, r1) =>
      var lv := AI.get_idx(lc, lid);
      if lv < 0 { FilterAllAgreeOutsideOwn(r1, cr, k); }
      else if lv < mx { FilterAllAgreeOutsideOwn(r1, cr, k); }
      else { FilterCaptureAgreeOutsideOwn(r1, cr, cc, lc, qc, -1, k); }
  }

  /** `filter_all` is a POINTWISE frame at any `k`: since it only sets group start
      registers to `-1` (the same positions in both runs) and passes everything
      else through, two runs agreeing at `k` still agree at `k` after filtering.
      No branching on values, so no side conditions. */
  lemma FilterAllFrameOutside(r: R.regex, cr: seq<int>, cr': seq<int>, k: int)
    requires k >= 0 && AI.get_idx(cr, k) == AI.get_idx(cr', k)
    ensures AI.get_idx(AI.filter_all(r, cr), k) == AI.get_idx(AI.filter_all(r, cr'), k)
    decreases r
  {
    match r
    case Re_empty => case Re_character(_) => case Re_anchor(_) =>
    case Re_alt(r1, r2) =>
      FilterAllFrameOutside(r1, cr, cr', k);
      FilterAllFrameOutside(r2, AI.filter_all(r1, cr), AI.filter_all(r1, cr'), k);
    case Re_con(r1, r2) =>
      FilterAllFrameOutside(r1, cr, cr', k);
      FilterAllFrameOutside(r2, AI.filter_all(r1, cr), AI.filter_all(r1, cr'), k);
    case Re_quant(_, _, _, r1) => FilterAllFrameOutside(r1, cr, cr', k);
    case Re_capture(cid, r1) =>
      assert AI.get_idx(AI.set_idx(cr, CP.start_reg(cid), -1), k) == AI.get_idx(AI.set_idx(cr', CP.start_reg(cid), -1), k) by {
        if k == CP.start_reg(cid) {} else { SetIdxKeepsOther(cr, CP.start_reg(cid), k); SetIdxKeepsOther(cr', CP.start_reg(cid), k); }
      }
      FilterAllFrameOutside(r1, AI.set_idx(cr, CP.start_reg(cid), -1), AI.set_idx(cr', CP.start_reg(cid), -1), k);
    case Re_lookaround(_, _, r1) => FilterAllFrameOutside(r1, cr, cr', k);
  }

  /** THE P1 FRAME: `filter_capture` over the whole regex agrees on OUTSIDE-look
      registers when the inputs agree there. Two capture banks agreeing outside
      the inside-look register set `W` (and clocks likewise, quant clocks outside
      the inside-look quant ids, same `lc`) yield equal filtered values at every
      register `k` outside `W`. A lookaround body only writes its own (inside-`W`)
      registers, so it is invisible to `k` (`FilterCaptureAgreeOutsideOwn`); every
      other node branches on clocks that agree outside `W`, so both runs take the
      same branch. This lifts §4a's `RegsAgreeOutside(res.0, caps, S)` to
      `GmOfLive` on outside-look groups. */
  lemma FilterFrameOutside(re: R.regex, cr: seq<int>, cr': seq<int>, cc: seq<int>, cc': seq<int>,
                           lc: seq<int>, qc: seq<int>, qc': seq<int>, mx: int, W: set<int>)
    requires forall x: int :: x in W ==> x >= 0
    requires forall g: nat :: g in CapIdsInLooks(re) ==> CP.start_reg(g) in W
    requires forall g: nat :: g in CapIdsOutsideLooks(re) ==> CP.start_reg(g) !in W
    requires forall j: int :: j !in W ==> AI.get_idx(cr, j) == AI.get_idx(cr', j)
    requires forall j: int :: j !in W ==> AI.get_idx(cc, j) == AI.get_idx(cc', j)
    requires forall q: nat :: q in QuantIdsOutsideLooks(re) ==> AI.get_idx(qc, q) == AI.get_idx(qc', q)
    ensures forall k: int :: k >= 0 && k !in W ==>
      AI.get_idx(AI.filter_capture(re, cr, cc, lc, qc, mx), k) == AI.get_idx(AI.filter_capture(re, cr', cc', lc, qc', mx), k)
    decreases re
  {
    match re
    case Re_empty => case Re_character(_) => case Re_anchor(_) =>
    case Re_alt(r1, r2) =>
      FilterFrameOutside(r1, cr, cr', cc, cc', lc, qc, qc', mx, W);
      FilterFrameOutside(r2, AI.filter_capture(r1, cr, cc, lc, qc, mx), AI.filter_capture(r1, cr', cc', lc, qc', mx),
                         cc, cc', lc, qc, qc', mx, W);
    case Re_con(r1, r2) =>
      FilterFrameOutside(r1, cr, cr', cc, cc', lc, qc, qc', mx, W);
      FilterFrameOutside(r2, AI.filter_capture(r1, cr, cc, lc, qc, mx), AI.filter_capture(r1, cr', cc', lc, qc', mx),
                         cc, cc', lc, qc, qc', mx, W);
    case Re_quant(nul, qid, q, r1) =>
      var qv := AI.get_idx(qc, qid);
      assert qv == AI.get_idx(qc', qid) by { if qid >= 0 { assert qid as nat in QuantIdsOutsideLooks(re); } }   // same branch
      forall k: int | k >= 0 && k !in W
        ensures AI.get_idx(AI.filter_capture(re, cr, cc, lc, qc, mx), k) == AI.get_idx(AI.filter_capture(re, cr', cc', lc, qc', mx), k)
      {
        if qv < mx { FilterAllFrameOutside(r1, cr, cr', k); }
      }
      if qv >= mx { FilterFrameOutside(r1, cr, cr', cc, cc', lc, qc, qc', qv, W); }
    case Re_capture(cid, r1) =>
      assert CP.start_reg(cid) !in W by {
        if cid >= 0 { assert cid as nat in CapIdsOutsideLooks(re); } else { assert CP.start_reg(cid) == 2 * cid < 0; }
      }
      var start := AI.get_idx(cc, CP.start_reg(cid));
      assert start == AI.get_idx(cc', CP.start_reg(cid));   // start_reg(cid) !in W
      forall k: int | k >= 0 && k !in W
        ensures AI.get_idx(AI.filter_capture(re, cr, cc, lc, qc, mx), k) == AI.get_idx(AI.filter_capture(re, cr', cc', lc, qc', mx), k)
      {
        if start < 0 {
          FilterAllFrameOutside(r1, cr, cr', k);
        } else if start < mx {
          assert AI.get_idx(AI.set_idx(cr, CP.start_reg(cid), -1), k) == AI.get_idx(AI.set_idx(cr', CP.start_reg(cid), -1), k) by {
            if k == CP.start_reg(cid) {} else { SetIdxKeepsOther(cr, CP.start_reg(cid), k); SetIdxKeepsOther(cr', CP.start_reg(cid), k); }
          }
          FilterAllFrameOutside(r1, AI.set_idx(cr, CP.start_reg(cid), -1), AI.set_idx(cr', CP.start_reg(cid), -1), k);
        }
      }
      if start >= 0 && start >= mx { FilterFrameOutside(r1, cr, cr', cc, cc', lc, qc, qc', mx, W); }
    case Re_lookaround(lid, la, r1) =>
      var lv := AI.get_idx(lc, lid);
      forall k: int | k >= 0 && k !in W
        ensures AI.get_idx(AI.filter_capture(re, cr, cc, lc, qc, mx), k) == AI.get_idx(AI.filter_capture(re, cr', cc', lc, qc', mx), k)
      {
        assert forall g: nat :: g in CapIds(r1) ==> CP.start_reg(g) != k by {
          forall g: nat | g in CapIds(r1) ensures CP.start_reg(g) != k { assert g in CapIdsInLooks(re); }
        }
        if lv < 0 || lv < mx {
          FilterAllAgreeOutsideOwn(r1, cr, k);
          FilterAllAgreeOutsideOwn(r1, cr', k);
        } else {
          FilterCaptureAgreeOutsideOwn(r1, cr, cc, lc, qc, -1, k);
          FilterCaptureAgreeOutsideOwn(r1, cr', cc', lc, qc', -1, k);
        }
      }
  }

  // filter_reset preserves the register-array length.
  /** `filter_all` preserves the register-array length. */
  lemma FilterAllLen(r: R.regex, regs: seq<int>)
    ensures |AI.filter_all(r, regs)| == |regs|
    decreases r
  {
    match r
    case Re_empty => case Re_character(_) => case Re_anchor(_) =>
    case Re_alt(r1, r2) => FilterAllLen(r1, regs); FilterAllLen(r2, AI.filter_all(r1, regs));
    case Re_con(r1, r2) => FilterAllLen(r1, regs); FilterAllLen(r2, AI.filter_all(r1, regs));
    case Re_quant(_, _, _, r1) => FilterAllLen(r1, regs);
    case Re_capture(cid, r1) => FilterAllLen(r1, AI.set_idx(regs, CP.start_reg(cid), -1));
    case Re_lookaround(_, _, r1) => FilterAllLen(r1, regs);
  }

  /** `filter_capture` preserves the register-array length. */
  lemma FilterCaptureLen(r: R.regex, cr: seq<int>, cc: seq<int>, lc: seq<int>, qc: seq<int>, mx: int)
    ensures |AI.filter_capture(r, cr, cc, lc, qc, mx)| == |cr|
    decreases r
  {
    match r
    case Re_empty => case Re_character(_) => case Re_anchor(_) =>
    case Re_alt(r1, r2) =>
      FilterCaptureLen(r1, cr, cc, lc, qc, mx);
      FilterCaptureLen(r2, AI.filter_capture(r1, cr, cc, lc, qc, mx), cc, lc, qc, mx);
    case Re_con(r1, r2) =>
      FilterCaptureLen(r1, cr, cc, lc, qc, mx);
      FilterCaptureLen(r2, AI.filter_capture(r1, cr, cc, lc, qc, mx), cc, lc, qc, mx);
    case Re_quant(nul, qid, q, r1) =>
      var qv := AI.get_idx(qc, qid);
      if qv < mx { FilterAllLen(r1, cr); } else { FilterCaptureLen(r1, cr, cc, lc, qc, qv); }
    case Re_capture(cid, r1) =>
      var start := AI.get_idx(cc, CP.start_reg(cid));
      if start < 0 { FilterAllLen(r1, cr); }
      else if start < mx { FilterAllLen(r1, AI.set_idx(cr, CP.start_reg(cid), -1)); }
      else { FilterCaptureLen(r1, cr, cc, lc, qc, mx); }
    case Re_lookaround(lid, l, r1) =>
      var lv := AI.get_idx(lc, lid);
      if lv < 0 { FilterAllLen(r1, cr); }
      else if lv < mx { FilterAllLen(r1, cr); }
      else { FilterCaptureLen(r1, cr, cc, lc, qc, -1); }
  }

  // Even-index frame: filter_capture reads capture values not at all (only
  // clocks, at even start positions) and writes only even start positions, so
  // its output at any EVEN index depends on its inputs only through their EVEN
  // indices. Hence two runs whose (cr,cc) agree on all even indices agree on
  // every even output index.
  /** Even-index frame for `filter_all`: two inputs that agree on every even
      index produce outputs that agree on every even index (only even/start
      slots are read and written). */
  lemma FilterAllEvenFrame(r: R.regex, cr: seq<int>, cr': seq<int>)
    requires |cr| == |cr'|
    requires forall i :: 0 <= i < |cr| && i % 2 == 0 ==> cr[i] == cr'[i]
    ensures forall j :: j % 2 == 0 ==>
      AI.get_idx(AI.filter_all(r, cr), j) == AI.get_idx(AI.filter_all(r, cr'), j)
    decreases r
  {
    FilterAllLen(r, cr); FilterAllLen(r, cr');
    match r
    case Re_empty => case Re_character(_) => case Re_anchor(_) =>
    case Re_alt(r1, r2) =>
      FilterAllEvenFrame(r1, cr, cr');
      FilterAllLen(r1, cr); FilterAllLen(r1, cr');
      var a := AI.filter_all(r1, cr); var b := AI.filter_all(r1, cr');
      forall i | 0 <= i < |a| && i % 2 == 0 ensures a[i] == b[i] {
        assert AI.get_idx(a, i) == a[i]; assert AI.get_idx(b, i) == b[i];
      }
      FilterAllEvenFrame(r2, a, b);
    case Re_con(r1, r2) =>
      FilterAllEvenFrame(r1, cr, cr');
      FilterAllLen(r1, cr); FilterAllLen(r1, cr');
      var a := AI.filter_all(r1, cr); var b := AI.filter_all(r1, cr');
      forall i | 0 <= i < |a| && i % 2 == 0 ensures a[i] == b[i] {
        assert AI.get_idx(a, i) == a[i]; assert AI.get_idx(b, i) == b[i];
      }
      FilterAllEvenFrame(r2, a, b);
    case Re_quant(_, _, _, r1) => FilterAllEvenFrame(r1, cr, cr');
    case Re_capture(cid, r1) =>
      // set both at even start_reg(cid) to -1: still agree on even
      FilterAllEvenFrame(r1, AI.set_idx(cr, CP.start_reg(cid), -1), AI.set_idx(cr', CP.start_reg(cid), -1));
    case Re_lookaround(_, _, r1) => FilterAllEvenFrame(r1, cr, cr');
  }

  /** Even-index frame for `filter_capture`: inputs `(cr,cc)` and `(cr',cc')`
      that agree on every even index produce outputs agreeing on every even
      index. */
  lemma FilterCaptureEvenFrame(r: R.regex, cr: seq<int>, cr': seq<int>, cc: seq<int>, cc': seq<int>,
                               lc: seq<int>, qc: seq<int>, mx: int)
    requires |cr| == |cr'|
    requires forall i :: 0 <= i < |cr| && i % 2 == 0 ==> cr[i] == cr'[i]
    requires forall i :: i % 2 == 0 ==> AI.get_idx(cc, i) == AI.get_idx(cc', i)
    ensures forall j :: j % 2 == 0 ==>
      AI.get_idx(AI.filter_capture(r, cr, cc, lc, qc, mx), j)
        == AI.get_idx(AI.filter_capture(r, cr', cc', lc, qc, mx), j)
    decreases r
  {
    FilterCaptureLen(r, cr, cc, lc, qc, mx); FilterCaptureLen(r, cr', cc', lc, qc, mx);
    match r
    case Re_empty => case Re_character(_) => case Re_anchor(_) =>
    case Re_alt(r1, r2) =>
      FilterCaptureEvenFrame(r1, cr, cr', cc, cc', lc, qc, mx);
      FilterCaptureLen(r1, cr, cc, lc, qc, mx); FilterCaptureLen(r1, cr', cc', lc, qc, mx);
      var a := AI.filter_capture(r1, cr, cc, lc, qc, mx); var b := AI.filter_capture(r1, cr', cc', lc, qc, mx);
      forall i | 0 <= i < |a| && i % 2 == 0 ensures a[i] == b[i] {
        assert AI.get_idx(a, i) == a[i]; assert AI.get_idx(b, i) == b[i];
      }
      FilterCaptureEvenFrame(r2, a, b, cc, cc', lc, qc, mx);
    case Re_con(r1, r2) =>
      FilterCaptureEvenFrame(r1, cr, cr', cc, cc', lc, qc, mx);
      FilterCaptureLen(r1, cr, cc, lc, qc, mx); FilterCaptureLen(r1, cr', cc', lc, qc, mx);
      var a := AI.filter_capture(r1, cr, cc, lc, qc, mx); var b := AI.filter_capture(r1, cr', cc', lc, qc, mx);
      forall i | 0 <= i < |a| && i % 2 == 0 ensures a[i] == b[i] {
        assert AI.get_idx(a, i) == a[i]; assert AI.get_idx(b, i) == b[i];
      }
      FilterCaptureEvenFrame(r2, a, b, cc, cc', lc, qc, mx);
    case Re_quant(nul, qid, q, r1) =>
      var qv := AI.get_idx(qc, qid);
      if qv < mx { FilterAllEvenFrame(r1, cr, cr'); }
      else { FilterCaptureEvenFrame(r1, cr, cr', cc, cc', lc, qc, qv); }
    case Re_capture(cid, r1) =>
      // start clock read at even start_reg(cid) — equal by hypothesis, same branch
      var start := AI.get_idx(cc, CP.start_reg(cid));
      if start < 0 { FilterAllEvenFrame(r1, cr, cr'); }
      else if start < mx {
        FilterAllEvenFrame(r1, AI.set_idx(cr, CP.start_reg(cid), -1), AI.set_idx(cr', CP.start_reg(cid), -1));
      } else { FilterCaptureEvenFrame(r1, cr, cr', cc, cc', lc, qc, mx); }
    case Re_lookaround(lid, l, r1) =>
      var lv := AI.get_idx(lc, lid);
      if lv < 0 { FilterAllEvenFrame(r1, cr, cr'); }
      else if lv < mx { FilterAllEvenFrame(r1, cr, cr'); }
      else { FilterCaptureEvenFrame(r1, cr, cr', cc, cc', lc, qc, -1); }
  }

  // filter_all never stores a value below -1 (it only ever writes -1 or copies).
  /** `filter_all` never stores a value below `-1` (it only writes `-1` or
      copies). */
  lemma FilterAllGeqNeg1(r: R.regex, regs: seq<int>, i: int)
    requires AI.get_idx(regs, i) >= -1
    ensures AI.get_idx(AI.filter_all(r, regs), i) >= -1
    decreases r
  {
    match r
    case Re_empty => case Re_character(_) => case Re_anchor(_) =>
    case Re_alt(r1, r2) => FilterAllGeqNeg1(r1, regs, i); FilterAllGeqNeg1(r2, AI.filter_all(r1, regs), i);
    case Re_con(r1, r2) => FilterAllGeqNeg1(r1, regs, i); FilterAllGeqNeg1(r2, AI.filter_all(r1, regs), i);
    case Re_quant(_, _, _, r1) => FilterAllGeqNeg1(r1, regs, i);
    case Re_capture(cid, r1) =>
      if i == CP.start_reg(cid) {} else { SetIdxKeepsOther(regs, CP.start_reg(cid), i); }
      FilterAllGeqNeg1(r1, AI.set_idx(regs, CP.start_reg(cid), -1), i);
    case Re_lookaround(_, _, r1) => FilterAllGeqNeg1(r1, regs, i);
  }

  // ----- Discharge cornerstone: when every capture in a (lookaround-free)
  // subtree has a start clock below the reset threshold M, filter_capture clears
  // the subtree exactly as filter_all does. This is what makes SetQuantToClock's
  // freshly-stamped clock (which becomes M for its subtree, and by global clock
  // monotonicity exceeds every prior-iteration subgroup clock) reset all stale
  // descendants — discharging the reset-scope / no-exposure preconditions. -----
  /** Every lookaround in `r` has a look clock below `M` (stale vs the reset
      threshold). Covers every lid the filter reads, including negative ones. */
  ghost predicate LooksStale(r: R.regex, lc: seq<int>, M: int)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => LooksStale(r1, lc, M) && LooksStale(r2, lc, M)
    case Re_con(r1, r2) => LooksStale(r1, lc, M) && LooksStale(r2, lc, M)
    case Re_quant(_, _, _, r1) => LooksStale(r1, lc, M)
    case Re_capture(_, r1) => LooksStale(r1, lc, M)
    case Re_lookaround(lid, _, r1) => AI.get_idx(lc, lid) < M && LooksStale(r1, lc, M)
    case _ => true
  }

  /** `LooksStale` is monotone up in the threshold. */
  lemma LooksStaleMono(r: R.regex, lc: seq<int>, M: int, M2: int)
    requires LooksStale(r, lc, M) && M <= M2
    ensures LooksStale(r, lc, M2)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => LooksStaleMono(r1, lc, M, M2); LooksStaleMono(r2, lc, M, M2);
    case Re_con(r1, r2) => LooksStaleMono(r1, lc, M, M2); LooksStaleMono(r2, lc, M, M2);
    case Re_quant(_, _, _, r1) => LooksStaleMono(r1, lc, M, M2);
    case Re_capture(_, r1) => LooksStaleMono(r1, lc, M, M2);
    case Re_lookaround(lid, _, r1) => LooksStaleMono(r1, lc, M, M2);
    case _ =>
  }

  /** L3a: every capture INSIDE a lookaround body of `r` is unset in `cc` — the
      run invariant that the Pike VM never writes inside-look capture registers
      (look bodies compile to CheckOracle, so no SetRegisterToCP fires for them;
      see NestInvOpenSite's outside-look ensures). Discharges the stale-look
      collapse in `FilterCaptureAllStale` and the open/reset frames without any
      look-clock reasoning. */
  ghost predicate LooksCapUnset(r: R.regex, cc: seq<int>)
  {
    forall c: nat :: c in CapIdsInLooks(r) ==> AI.get_idx(cc, CP.start_reg(c)) < 0
  }

  /** Discharge cornerstone: when every capture in a subtree has a start clock
      below the reset threshold `M` AND every enclosing lookaround is stale
      (`LooksStale`), `filter_capture` clears the subtree exactly as `filter_all`
      does. This is what makes a freshly-stamped `SetQuantToClock` clock reset all
      stale descendants (L3a: capturing lookahead bodies included -- a stale look
      never takes its keep branch). */
  lemma FilterCaptureAllStale(r: R.regex, cr: seq<int>, cc: seq<int>, lc: seq<int>, qc: seq<int>, M: int)
    requires NR.LookBehindFragmentRE(r)
    // L3a: inside-look captures are UNSET (never written during the Pike run —
    // look bodies compile to CheckOracle, not inline). This replaces the old
    // LooksStale hypothesis: a matched look's keep branch keeps only UNSET body
    // captures, which filter to the same -1 as filter_all's reset.
    requires LooksCapUnset(r, cc)
    requires forall cid: nat :: cid in CapIds(r)
                               ==> AI.get_idx(cc, CP.start_reg(cid)) < M
                                   || AI.get_idx(cc, CP.start_reg(cid)) < 0
    requires forall k :: AI.get_idx(cr, k) >= -1
    requires forall cid: nat :: cid in CapIds(r) && AI.get_idx(cc, CP.start_reg(cid)) < 0
                               ==> AI.get_idx(cr, CP.start_reg(cid)) < 0
    ensures AI.filter_capture(r, cr, cc, lc, qc, M) == AI.filter_all(r, cr)
    decreases r
  {
    match r
    case Re_lookaround(lid, la, r1) =>
      // CapIdsInLooks(Re_lookaround) == CapIds(r1) are all unset, so BOTH filter
      // branches collapse to filter_all(r1, cr).
      NR.PlusIsLookBehindFragmentRE(r1);
      var lv := AI.get_idx(lc, lid);
      if lv < 0 || lv < M {
        // reset branch: filter_capture == filter_all(r1, cr) directly.
      } else {
        // keep branch: filter_capture(r1, cr, cc, lc, qc, -1) == filter_all(r1, cr).
        // CapIdsInLooks(Re_lookaround) == CapIds(r1) ⊇ CapIdsInLooks(r1), all unset.
        CapIdsSplit(r1);
        assert LooksCapUnset(r1, cc);
        FilterCaptureAllStale(r1, cr, cc, lc, qc, -1);
      }
    case Re_empty => case Re_character(_) => case Re_anchor(_) =>
    case Re_alt(r1, r2) =>
      FilterCaptureAllStale(r1, cr, cc, lc, qc, M);
      var cr2 := AI.filter_all(r1, cr);
      forall k ensures AI.get_idx(cr2, k) >= -1 { FilterAllGeqNeg1(r1, cr, k); }
      forall cid: nat | cid in CapIds(r2) && AI.get_idx(cc, CP.start_reg(cid)) < 0
        ensures AI.get_idx(cr2, CP.start_reg(cid)) < 0 { FilterAllNeg(r1, cr, CP.start_reg(cid)); }
      FilterCaptureAllStale(r2, cr2, cc, lc, qc, M);
    case Re_con(r1, r2) =>
      FilterCaptureAllStale(r1, cr, cc, lc, qc, M);
      var cr2 := AI.filter_all(r1, cr);
      forall k ensures AI.get_idx(cr2, k) >= -1 { FilterAllGeqNeg1(r1, cr, k); }
      forall cid: nat | cid in CapIds(r2) && AI.get_idx(cc, CP.start_reg(cid)) < 0
        ensures AI.get_idx(cr2, CP.start_reg(cid)) < 0 { FilterAllNeg(r1, cr, CP.start_reg(cid)); }
      FilterCaptureAllStale(r2, cr2, cc, lc, qc, M);
    case Re_quant(nul, qid, q, r1) =>
      var qv := AI.get_idx(qc, qid);
      if qv < M {
        // filter_capture takes filter_all(r1, cr); filter_all(r) == filter_all(r1, cr) too.
      } else {
        // maxclock rises to qv >= M; every cap clock is still < qv or < 0, and
        // inside-look caps are still unset (independent of the threshold).
        FilterCaptureAllStale(r1, cr, cc, lc, qc, qv);
      }
    case Re_capture(cid, r1) =>
      var start := AI.get_idx(cc, CP.start_reg(cid));
      if start < 0 {
        // gid unopened ⇒ its value is -1 (≥ -1 and < 0), so filter_all's
        // set_idx(cr, start_reg(cid), -1) is a no-op; both sides = filter_all(r1, cr).
        assert AI.get_idx(cr, CP.start_reg(cid)) < 0;
        assert AI.get_idx(cr, CP.start_reg(cid)) == -1;
        assert AI.set_idx(cr, CP.start_reg(cid), -1) == cr;
      }
      // else 0 ≤ start < M: filter_capture and filter_all both take
      // filter_all(r1, set_idx(cr, start_reg(cid), -1)) — identical.
  }

  // ----- Capture-id structure. Capture ids are assigned freshly by `annotate`,
  // hence unique across the AST; CapUnique captures exactly the disjointness
  // FilterOpenFrame needs (a group never nests inside itself, and alt/con
  // branches share no ids). -----
  /** All capture ids occurring in `r`. `annotate` assigns them freshly, so
      they are unique across the AST (`CapUnique`). */
  ghost function CapIds(r: R.regex): set<nat>
    decreases r
  {
    match r
    case Re_empty => {}
    case Re_character(_) => {}
    case Re_anchor(_) => {}
    case Re_alt(r1, r2) => CapIds(r1) + CapIds(r2)
    case Re_con(r1, r2) => CapIds(r1) + CapIds(r2)
    case Re_quant(_, _, _, r1) => CapIds(r1)
    case Re_capture(cid, r1) => (if cid >= 0 then {cid as nat} else {}) + CapIds(r1)
    case Re_lookaround(_, _, r1) => CapIds(r1)
  }

  /** Capture ids are pairwise distinct across `r`: a group never nests inside
      itself and `alt`/`con` branches share no ids. The disjointness
      `FilterOpenFrame` and the presence/absence extractors need. */
  ghost predicate CapUnique(r: R.regex)
    decreases r
  {
    match r
    case Re_empty => true
    case Re_character(_) => true
    case Re_anchor(_) => true
    case Re_alt(r1, r2) => CapUnique(r1) && CapUnique(r2) && CapIds(r1) * CapIds(r2) == {}
    case Re_con(r1, r2) => CapUnique(r1) && CapUnique(r2) && CapIds(r1) * CapIds(r2) == {}
    case Re_quant(_, _, _, r1) => CapUnique(r1)
    case Re_capture(cid, r1) => cid >= 0 && (cid as nat) !in CapIds(r1) && CapUnique(r1)
    case Re_lookaround(_, _, r1) => CapUnique(r1)
  }

  // filter_all / filter_capture only ever write START registers of ids IN the
  // subtree, so a register whose id is OUTSIDE the subtree passes through.
  /** `filter_all` writes only START registers of ids IN the subtree, so a
      register whose id is OUTSIDE the subtree passes through. */
  lemma FilterAllOutside(r: R.regex, regs: seq<int>, g: nat)
    requires g !in CapIds(r)
    ensures AI.get_idx(AI.filter_all(r, regs), CP.start_reg(g)) == AI.get_idx(regs, CP.start_reg(g))
    decreases r
  {
    match r
    case Re_empty => case Re_character(_) => case Re_anchor(_) =>
    case Re_alt(r1, r2) => FilterAllOutside(r1, regs, g); FilterAllOutside(r2, AI.filter_all(r1, regs), g);
    case Re_con(r1, r2) => FilterAllOutside(r1, regs, g); FilterAllOutside(r2, AI.filter_all(r1, regs), g);
    case Re_quant(_, _, _, r1) => FilterAllOutside(r1, regs, g);
    case Re_capture(cid, r1) =>
      SetIdxKeepsOther(regs, CP.start_reg(cid), CP.start_reg(g));   // cid ≠ g ⇒ 2cid ≠ 2g
      FilterAllOutside(r1, AI.set_idx(regs, CP.start_reg(cid), -1), g);
    case Re_lookaround(_, _, r1) => FilterAllOutside(r1, regs, g);
  }

  /** `filter_capture` writes only START registers of ids IN the subtree, so a
      register whose id is OUTSIDE the subtree passes through. */
  lemma FilterCaptureOutside(r: R.regex, cr: seq<int>, cc: seq<int>, lc: seq<int>, qc: seq<int>, mx: int, g: nat)
    requires NR.LookBehindFragmentRE(r)
    requires g !in CapIds(r)
    ensures AI.get_idx(AI.filter_capture(r, cr, cc, lc, qc, mx), CP.start_reg(g)) == AI.get_idx(cr, CP.start_reg(g))
    decreases r
  {
    match r
    case Re_lookaround(lid, la, r1) =>
      // L3a: the body may capture, but g is outside it, so `start_reg(g)` passes
      // through whichever branch the lookaround takes (it only writes r1's regs).
      assert forall g0: nat :: g0 in CapIds(r1) ==> CP.start_reg(g0) != CP.start_reg(g) by {
        forall g0: nat | g0 in CapIds(r1) ensures CP.start_reg(g0) != CP.start_reg(g) { assert g0 != g; }
      }
      var lv := AI.get_idx(lc, lid);
      if lv < 0 || lv < mx { FilterAllAgreeOutsideOwn(r1, cr, CP.start_reg(g)); }
      else { FilterCaptureAgreeOutsideOwn(r1, cr, cc, lc, qc, -1, CP.start_reg(g)); }
    case Re_empty => case Re_character(_) => case Re_anchor(_) =>
    case Re_alt(r1, r2) =>
      FilterCaptureOutside(r1, cr, cc, lc, qc, mx, g);
      FilterCaptureOutside(r2, AI.filter_capture(r1, cr, cc, lc, qc, mx), cc, lc, qc, mx, g);
    case Re_con(r1, r2) =>
      FilterCaptureOutside(r1, cr, cc, lc, qc, mx, g);
      FilterCaptureOutside(r2, AI.filter_capture(r1, cr, cc, lc, qc, mx), cc, lc, qc, mx, g);
    case Re_quant(nul, qid, q, r1) =>
      var qv := AI.get_idx(qc, qid);
      if qv < mx { FilterAllOutside(r1, cr, g); } else { FilterCaptureOutside(r1, cr, cc, lc, qc, qv, g); }
    case Re_capture(cid, r1) =>
      var start := AI.get_idx(cc, CP.start_reg(cid));
      if start < 0 { FilterAllOutside(r1, cr, g); }
      else if start < mx {
        SetIdxKeepsOther(cr, CP.start_reg(cid), CP.start_reg(g));
        FilterAllOutside(r1, AI.set_idx(cr, CP.start_reg(cid), -1), g);
      } else { FilterCaptureOutside(r1, cr, cc, lc, qc, mx, g); }
  }

  // MxAtGid: the maxclock filter_capture threads to gid's own capture node when
  // it descends in present mode (i.e. the innermost enclosing star's clock).
  // This is the threshold gid's subgroups must fall below to stay reset.
  /** The maxclock `filter_capture` threads to `gid`'s own capture node when it
      descends in present mode (the innermost enclosing star's clock) — the
      threshold `gid`'s subgroups must fall below to stay reset. */
  ghost function MxAtGid(r: R.regex, cc: seq<int>, qc: seq<int>, mx: int, gid: nat): int
    requires gid in CapIds(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => if gid in CapIds(r1) then MxAtGid(r1, cc, qc, mx, gid) else MxAtGid(r2, cc, qc, mx, gid)
    case Re_con(r1, r2) => if gid in CapIds(r1) then MxAtGid(r1, cc, qc, mx, gid) else MxAtGid(r2, cc, qc, mx, gid)
    case Re_quant(nul, qid, q, r1) => var qv := AI.get_idx(qc, qid); MxAtGid(r1, cc, qc, qv, gid)
    case Re_capture(cid, r1) => if cid == gid then mx else MxAtGid(r1, cc, qc, mx, gid)
    case Re_lookaround(lid, l, r1) => MxAtGid(r1, cc, qc, mx, gid)
  }

  // PathPresent: along the descent to gid's node, every enclosing quantifier and
  // capture is in filter_capture's PRESENT branch (so gid is actually reached in
  // capture mode, not cleared by an ancestor's filter_all).
  /** Along the descent to `gid`'s node, every enclosing quantifier and capture
      is in `filter_capture`'s PRESENT branch — so `gid` is actually reached in
      capture mode, not cleared by an ancestor's `filter_all`. */
  ghost predicate PathPresent(r: R.regex, cc: seq<int>, qc: seq<int>, mx: int, gid: nat)
    requires gid in CapIds(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => if gid in CapIds(r1) then PathPresent(r1, cc, qc, mx, gid) else PathPresent(r2, cc, qc, mx, gid)
    case Re_con(r1, r2) => if gid in CapIds(r1) then PathPresent(r1, cc, qc, mx, gid) else PathPresent(r2, cc, qc, mx, gid)
    case Re_quant(nul, qid, q, r1) => var qv := AI.get_idx(qc, qid); qv >= mx && PathPresent(r1, cc, qc, qv, gid)
    case Re_capture(cid, r1) =>
      if cid == gid then true
      else AI.get_idx(cc, CP.start_reg(cid)) >= 0 && AI.get_idx(cc, CP.start_reg(cid)) >= mx
           && PathPresent(r1, cc, qc, mx, gid)
    case Re_lookaround(lid, l, r1) => PathPresent(r1, cc, qc, mx, gid)
  }

  // ===========================================================================
  // L3a: the lookaround-AWARE variants of MxAtGid / PathPresent. For a capturing
  // lookaround body, filter_capture's lookaround rule is NOT the identity: a
  // MATCHED look (lv = lc[lid] >= mx) takes the `filter_capture(r1, .., -1)`
  // branch (mx RESET to -1), an unmatched look clears the body. So the mx that
  // reaches a group INSIDE a lookaround is -1, and presence requires the look to
  // have matched. These thread `lc` (absent from the L1/L2 versions).
  // ===========================================================================

  /** `MxAtGid` threaded through the lookaround `mx`-reset (a matched look resets
      `mx` to `-1` for its body). */
  ghost function MxAtGidLk(r: R.regex, cc: seq<int>, lc: seq<int>, qc: seq<int>, mx: int, gid: nat): int
    requires gid in CapIds(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => if gid in CapIds(r1) then MxAtGidLk(r1, cc, lc, qc, mx, gid) else MxAtGidLk(r2, cc, lc, qc, mx, gid)
    case Re_con(r1, r2) => if gid in CapIds(r1) then MxAtGidLk(r1, cc, lc, qc, mx, gid) else MxAtGidLk(r2, cc, lc, qc, mx, gid)
    case Re_quant(nul, qid, q, r1) => var qv := AI.get_idx(qc, qid); MxAtGidLk(r1, cc, lc, qc, qv, gid)
    case Re_capture(cid, r1) => if cid == gid then mx else MxAtGidLk(r1, cc, lc, qc, mx, gid)
    case Re_lookaround(lid, l, r1) => MxAtGidLk(r1, cc, lc, qc, -1, gid)
  }

  /** Lookaround-aware `PathPresent`: along the descent to `gid`, every quantifier
      and capture is present AND every enclosing lookaround MATCHED (`lc[lid] >=
      mx`, resetting `mx` to `-1` for its body). */
  ghost predicate PathPresentLk(r: R.regex, cc: seq<int>, lc: seq<int>, qc: seq<int>, mx: int, gid: nat)
    requires gid in CapIds(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => if gid in CapIds(r1) then PathPresentLk(r1, cc, lc, qc, mx, gid) else PathPresentLk(r2, cc, lc, qc, mx, gid)
    case Re_con(r1, r2) => if gid in CapIds(r1) then PathPresentLk(r1, cc, lc, qc, mx, gid) else PathPresentLk(r2, cc, lc, qc, mx, gid)
    case Re_quant(nul, qid, q, r1) => var qv := AI.get_idx(qc, qid); qv >= mx && PathPresentLk(r1, cc, lc, qc, qv, gid)
    case Re_capture(cid, r1) =>
      if cid == gid then true
      else AI.get_idx(cc, CP.start_reg(cid)) >= 0 && AI.get_idx(cc, CP.start_reg(cid)) >= mx
           && PathPresentLk(r1, cc, lc, qc, mx, gid)
    case Re_lookaround(lid, l, r1) =>
      AI.get_idx(lc, lid) >= 0 && AI.get_idx(lc, lid) >= mx && PathPresentLk(r1, cc, lc, qc, -1, gid)
  }

  /** THE P2 core: an L3a-present captured group's START register survives
      `filter_capture`. Every enclosing quantifier/capture takes its keep branch
      (`PathPresentLk`), every enclosing lookaround matched (so `FilterAtLookaround-
      Matched` takes the keep branch, `mx -> -1`), and at `gid`'s own node the
      clock is set and in scope (`cc[start] >= 0 && >= MxAtGidLk`) so it is kept.
      The capturing analog of the L1/L2 filter-presence machinery. */
  lemma FilterKeepsPresentLk(r: R.regex, cr: seq<int>, cc: seq<int>, lc: seq<int>, qc: seq<int>, mx: int, gid: nat)
    requires CapUnique(r)
    requires gid in CapIds(r)
    requires PathPresentLk(r, cc, lc, qc, mx, gid)
    requires AI.get_idx(cc, CP.start_reg(gid)) >= 0
    requires AI.get_idx(cc, CP.start_reg(gid)) >= MxAtGidLk(r, cc, lc, qc, mx, gid)
    ensures AI.get_idx(AI.filter_capture(r, cr, cc, lc, qc, mx), CP.start_reg(gid)) == AI.get_idx(cr, CP.start_reg(gid))
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      if gid in CapIds(r1) {
        assert gid !in CapIds(r2) by { if gid in CapIds(r2) { assert gid in CapIds(r1) * CapIds(r2); } }
        FilterKeepsPresentLk(r1, cr, cc, lc, qc, mx, gid);
        forall g0: nat | g0 in CapIds(r2) ensures CP.start_reg(g0) != CP.start_reg(gid) {}
        FilterCaptureAgreeOutsideOwn(r2, AI.filter_capture(r1, cr, cc, lc, qc, mx), cc, lc, qc, mx, CP.start_reg(gid));
      } else {
        forall g0: nat | g0 in CapIds(r1) ensures CP.start_reg(g0) != CP.start_reg(gid) {}
        FilterCaptureAgreeOutsideOwn(r1, cr, cc, lc, qc, mx, CP.start_reg(gid));
        FilterKeepsPresentLk(r2, AI.filter_capture(r1, cr, cc, lc, qc, mx), cc, lc, qc, mx, gid);
      }
    case Re_con(r1, r2) =>
      if gid in CapIds(r1) {
        assert gid !in CapIds(r2) by { if gid in CapIds(r2) { assert gid in CapIds(r1) * CapIds(r2); } }
        FilterKeepsPresentLk(r1, cr, cc, lc, qc, mx, gid);
        forall g0: nat | g0 in CapIds(r2) ensures CP.start_reg(g0) != CP.start_reg(gid) {}
        FilterCaptureAgreeOutsideOwn(r2, AI.filter_capture(r1, cr, cc, lc, qc, mx), cc, lc, qc, mx, CP.start_reg(gid));
      } else {
        forall g0: nat | g0 in CapIds(r1) ensures CP.start_reg(g0) != CP.start_reg(gid) {}
        FilterCaptureAgreeOutsideOwn(r1, cr, cc, lc, qc, mx, CP.start_reg(gid));
        FilterKeepsPresentLk(r2, AI.filter_capture(r1, cr, cc, lc, qc, mx), cc, lc, qc, mx, gid);
      }
    case Re_quant(nul, qid, q, r1) =>
      var qv := AI.get_idx(qc, qid);
      assert qv >= mx;   // PathPresentLk
      FilterKeepsPresentLk(r1, cr, cc, lc, qc, qv, gid);
    case Re_capture(cid, r1) =>
      var start := AI.get_idx(cc, CP.start_reg(cid));
      if cid == gid {
        assert start >= 0 && start >= mx;   // cc[start_reg(gid)] >= MxAtGidLk == mx here
        assert gid !in CapIds(r1) by { if gid in CapIds(r1) { } }   // CapUnique: cid !in CapIds(r1)
        forall g0: nat | g0 in CapIds(r1) ensures CP.start_reg(g0) != CP.start_reg(gid) {}
        FilterCaptureAgreeOutsideOwn(r1, cr, cc, lc, qc, mx, CP.start_reg(gid));
      } else {
        assert start >= 0 && start >= mx;   // PathPresentLk
        FilterKeepsPresentLk(r1, cr, cc, lc, qc, mx, gid);
      }
    case Re_lookaround(lid, l, r1) =>
      var lv := AI.get_idx(lc, lid);
      assert lv >= 0 && lv >= mx;   // PathPresentLk -> matched
      FilterAtLookaroundMatched(lid, l, r1, cr, cc, lc, qc, mx);
      FilterKeepsPresentLk(r1, cr, cc, lc, qc, -1, gid);
  }

  // Single-index frame: changing register arrays only at position start_reg(gid)
  // (whose id is OUTSIDE the subtree) leaves filter output unchanged everywhere
  // except that same position.
  /** Single-index frame for `filter_all`: two inputs that agree everywhere
      except `start_reg(gid)` (an id OUTSIDE the subtree) produce outputs that
      agree everywhere except that same position. */
  lemma FilterAllFrameAt(r: R.regex, A: seq<int>, B: seq<int>, gid: nat)
    requires gid !in CapIds(r)
    requires |A| == |B|
    requires forall j :: j != CP.start_reg(gid) ==> AI.get_idx(A, j) == AI.get_idx(B, j)
    ensures forall j :: j != CP.start_reg(gid)
                        ==> AI.get_idx(AI.filter_all(r, A), j) == AI.get_idx(AI.filter_all(r, B), j)
    decreases r
  {
    FilterAllLen(r, A); FilterAllLen(r, B);
    match r
    case Re_empty => case Re_character(_) => case Re_anchor(_) =>
    case Re_alt(r1, r2) =>
      FilterAllFrameAt(r1, A, B, gid);
      FilterAllLen(r1, A); FilterAllLen(r1, B);
      var a := AI.filter_all(r1, A); var b := AI.filter_all(r1, B);
      forall j | j != CP.start_reg(gid) ensures AI.get_idx(a, j) == AI.get_idx(b, j) {}
      FilterAllFrameAt(r2, a, b, gid);
    case Re_con(r1, r2) =>
      FilterAllFrameAt(r1, A, B, gid);
      FilterAllLen(r1, A); FilterAllLen(r1, B);
      var a := AI.filter_all(r1, A); var b := AI.filter_all(r1, B);
      forall j | j != CP.start_reg(gid) ensures AI.get_idx(a, j) == AI.get_idx(b, j) {}
      FilterAllFrameAt(r2, a, b, gid);
    case Re_quant(_, _, _, r1) => FilterAllFrameAt(r1, A, B, gid);
    case Re_capture(cid, r1) =>
      // cid ≠ gid, so set_idx at start_reg(cid) keeps the arrays agreeing off start_reg(gid).
      var A2 := AI.set_idx(A, CP.start_reg(cid), -1); var B2 := AI.set_idx(B, CP.start_reg(cid), -1);
      forall j | j != CP.start_reg(gid) ensures AI.get_idx(A2, j) == AI.get_idx(B2, j) {
        if j == CP.start_reg(cid) {} else { SetIdxKeepsOther(A, CP.start_reg(cid), j); SetIdxKeepsOther(B, CP.start_reg(cid), j); }
      }
      FilterAllFrameAt(r1, A2, B2, gid);
    case Re_lookaround(_, _, r1) => FilterAllFrameAt(r1, A, B, gid);
  }

  /** Single-index frame for `filter_capture`: inputs `(A,cc)` and `(B,cc')`
      that agree everywhere except `start_reg(gid)` produce outputs agreeing
      everywhere except that same position. */
  lemma FilterCaptureFrameAt(r: R.regex, A: seq<int>, B: seq<int>, cc: seq<int>, cc': seq<int>,
                             lc: seq<int>, qc: seq<int>, mx: int, gid: nat)
    requires NR.LookBehindFragmentRE(r)
    requires gid !in CapIds(r)
    requires |A| == |B|
    requires forall j :: j != CP.start_reg(gid) ==> AI.get_idx(A, j) == AI.get_idx(B, j)
    requires forall j :: j != CP.start_reg(gid) ==> AI.get_idx(cc, j) == AI.get_idx(cc', j)
    ensures forall j :: j != CP.start_reg(gid)
                        ==> AI.get_idx(AI.filter_capture(r, A, cc, lc, qc, mx), j)
                            == AI.get_idx(AI.filter_capture(r, B, cc', lc, qc, mx), j)
    decreases r
  {
    FilterCaptureLen(r, A, cc, lc, qc, mx); FilterCaptureLen(r, B, cc', lc, qc, mx);
    match r
    case Re_lookaround(lid, la, r1) =>
      // same `lc` -> same branch; both filters frame off `start_reg(gid)` (gid is
      // not one of r1's groups). L3a: works for capturing bodies too.
      NR.PlusIsLookBehindFragmentRE(r1);   // LookBehindFragmentRE(r1) from LookFree+PlusFragment
      var lv := AI.get_idx(lc, lid);
      if lv < 0 || lv < mx { FilterAllFrameAt(r1, A, B, gid); }
      else { FilterCaptureFrameAt(r1, A, B, cc, cc', lc, qc, -1, gid); }
    case Re_empty => case Re_character(_) => case Re_anchor(_) =>
    case Re_alt(r1, r2) =>
      FilterCaptureFrameAt(r1, A, B, cc, cc', lc, qc, mx, gid);
      FilterCaptureLen(r1, A, cc, lc, qc, mx); FilterCaptureLen(r1, B, cc', lc, qc, mx);
      var a := AI.filter_capture(r1, A, cc, lc, qc, mx); var b := AI.filter_capture(r1, B, cc', lc, qc, mx);
      forall j | j != CP.start_reg(gid) ensures AI.get_idx(a, j) == AI.get_idx(b, j) {}
      FilterCaptureFrameAt(r2, a, b, cc, cc', lc, qc, mx, gid);
    case Re_con(r1, r2) =>
      FilterCaptureFrameAt(r1, A, B, cc, cc', lc, qc, mx, gid);
      FilterCaptureLen(r1, A, cc, lc, qc, mx); FilterCaptureLen(r1, B, cc', lc, qc, mx);
      var a := AI.filter_capture(r1, A, cc, lc, qc, mx); var b := AI.filter_capture(r1, B, cc', lc, qc, mx);
      forall j | j != CP.start_reg(gid) ensures AI.get_idx(a, j) == AI.get_idx(b, j) {}
      FilterCaptureFrameAt(r2, a, b, cc, cc', lc, qc, mx, gid);
    case Re_quant(nul, qid, q, r1) =>
      var qv := AI.get_idx(qc, qid);
      if qv < mx { FilterAllFrameAt(r1, A, B, gid); }
      else { FilterCaptureFrameAt(r1, A, B, cc, cc', lc, qc, qv, gid); }
    case Re_capture(cid, r1) =>
      assert CP.start_reg(cid) != CP.start_reg(gid);   // cid ≠ gid (gid ∉ CapIds)
      var start := AI.get_idx(cc, CP.start_reg(cid));
      assert AI.get_idx(cc', CP.start_reg(cid)) == start;
      if start < 0 { FilterAllFrameAt(r1, A, B, gid); }
      else if start < mx {
        var A2 := AI.set_idx(A, CP.start_reg(cid), -1); var B2 := AI.set_idx(B, CP.start_reg(cid), -1);
        forall j | j != CP.start_reg(gid) ensures AI.get_idx(A2, j) == AI.get_idx(B2, j) {
          if j == CP.start_reg(cid) {} else { SetIdxKeepsOther(A, CP.start_reg(cid), j); SetIdxKeepsOther(B, CP.start_reg(cid), j); }
        }
        FilterAllFrameAt(r1, A2, B2, gid);
      } else {
        FilterCaptureFrameAt(r1, A, B, cc, cc', lc, qc, mx, gid);
      }
  }

  // BodyOf: gid's immediate capture body subtree (the r1 in Re_capture(gid, r1)).
  /** `gid`'s immediate capture body subtree (the `r1` in
      `Re_capture(gid, r1)`). */
  ghost function BodyOf(r: R.regex, gid: nat): R.regex
    requires gid in CapIds(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => if gid in CapIds(r1) then BodyOf(r1, gid) else BodyOf(r2, gid)
    case Re_con(r1, r2) => if gid in CapIds(r1) then BodyOf(r1, gid) else BodyOf(r2, gid)
    case Re_quant(nul, qid, q, r1) => BodyOf(r1, gid)
    case Re_capture(cid, r1) => if cid == gid then r1 else BodyOf(r1, gid)
    case Re_lookaround(lid, l, r1) => BodyOf(r1, gid)
  }

  // ----- Quant-id structure, mirroring CapIds/CapUnique/BodyOf/MxAtGid/
  // PathPresent for the GMReset discharge. -----
  /** All quantifier ids occurring in `r` (the quant-id analog of `CapIds`). */
  ghost function QuantIds(r: R.regex): set<nat>
    decreases r
  {
    match r
    case Re_empty => {}
    case Re_character(_) => {}
    case Re_anchor(_) => {}
    case Re_alt(r1, r2) => QuantIds(r1) + QuantIds(r2)
    case Re_con(r1, r2) => QuantIds(r1) + QuantIds(r2)
    case Re_quant(nul, qid, q, r1) => (if qid >= 0 then {qid as nat} else {}) + QuantIds(r1)
    case Re_capture(cid, r1) => QuantIds(r1)
    case Re_lookaround(lid, l, r1) => QuantIds(r1)
  }

  /** Quantifier ids are pairwise distinct across `r` (the quant-id analog of
      `CapUnique`). */
  ghost predicate QuantUnique(r: R.regex)
    decreases r
  {
    match r
    case Re_empty => true
    case Re_character(_) => true
    case Re_anchor(_) => true
    case Re_alt(r1, r2) => QuantUnique(r1) && QuantUnique(r2) && QuantIds(r1) * QuantIds(r2) == {}
    case Re_con(r1, r2) => QuantUnique(r1) && QuantUnique(r2) && QuantIds(r1) * QuantIds(r2) == {}
    case Re_quant(nul, qid, q, r1) => qid >= 0 && (qid as nat) !in QuantIds(r1) && QuantUnique(r1)
    case Re_capture(cid, r1) => QuantUnique(r1)
    case Re_lookaround(lid, l, r1) => QuantUnique(r1)
  }

  /** `qid`'s quantifier body subtree (the `r1` in `Re_quant(_, qid, _, r1)`) —
      the quant-id analog of `BodyOf`. Its `CapIds` are `qid`'s reset scope. */
  ghost function QidBody(r: R.regex, qid: nat): R.regex
    requires qid in QuantIds(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => if qid in QuantIds(r1) then QidBody(r1, qid) else QidBody(r2, qid)
    case Re_con(r1, r2) => if qid in QuantIds(r1) then QidBody(r1, qid) else QidBody(r2, qid)
    case Re_quant(nul, qid0, q, r1) => if qid0 >= 0 && (qid0 as nat) == qid then r1 else QidBody(r1, qid)
    case Re_capture(cid, r1) => QidBody(r1, qid)
    case Re_lookaround(lid, l, r1) => QidBody(r1, qid)
  }

  /** The maxclock threaded to `qid`'s quant node in present mode — the
      quant-id analog of `MxAtGid`. */
  ghost function MxAtQid(r: R.regex, cc: seq<int>, qc: seq<int>, mx: int, qid: nat): int
    requires qid in QuantIds(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => if qid in QuantIds(r1) then MxAtQid(r1, cc, qc, mx, qid) else MxAtQid(r2, cc, qc, mx, qid)
    case Re_con(r1, r2) => if qid in QuantIds(r1) then MxAtQid(r1, cc, qc, mx, qid) else MxAtQid(r2, cc, qc, mx, qid)
    case Re_quant(nul, qid0, q, r1) =>
      if qid0 >= 0 && (qid0 as nat) == qid then mx else var qv := AI.get_idx(qc, qid0); MxAtQid(r1, cc, qc, qv, qid)
    case Re_capture(cid, r1) => MxAtQid(r1, cc, qc, mx, qid)
    case Re_lookaround(lid, l, r1) => MxAtQid(r1, cc, qc, mx, qid)
  }

  /** Every enclosing quantifier and capture along the descent to `qid`'s node
      is in `filter_capture`'s present branch — the quant-id analog of
      `PathPresent`. */
  ghost predicate PathPresentQ(r: R.regex, cc: seq<int>, qc: seq<int>, mx: int, qid: nat)
    requires qid in QuantIds(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => if qid in QuantIds(r1) then PathPresentQ(r1, cc, qc, mx, qid) else PathPresentQ(r2, cc, qc, mx, qid)
    case Re_con(r1, r2) => if qid in QuantIds(r1) then PathPresentQ(r1, cc, qc, mx, qid) else PathPresentQ(r2, cc, qc, mx, qid)
    case Re_quant(nul, qid0, q, r1) =>
      if qid0 >= 0 && (qid0 as nat) == qid then true
      else var qv := AI.get_idx(qc, qid0); qv >= mx && PathPresentQ(r1, cc, qc, qv, qid)
    case Re_capture(cid, r1) =>
      AI.get_idx(cc, CP.start_reg(cid)) >= 0 && AI.get_idx(cc, CP.start_reg(cid)) >= mx && PathPresentQ(r1, cc, qc, mx, qid)
    case Re_lookaround(lid, l, r1) => PathPresentQ(r1, cc, qc, mx, qid)
  }

  // ===========================================================================
  // Ancestor sets + PathPresent introduction. The positional invariant will
  // naturally maintain per-ancestor freshness ("every enclosing capture/quant
  // is fresh w.r.t. ITS OWN MxAt threshold"); these lemmas assemble that into
  // the PathPresent/PathPresentQ form the discharge lemmas consume.
  // ===========================================================================

  // Capture ids strictly enclosing gid (the path's capture nodes above gid).
  /** Capture ids strictly enclosing `gid` (the capture nodes on the path above
      it). */
  ghost function AncCaps(r: R.regex, gid: nat): (res: set<nat>)
    requires gid in CapIds(r)
    ensures res <= CapIds(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => if gid in CapIds(r1) then AncCaps(r1, gid) else AncCaps(r2, gid)
    case Re_con(r1, r2) => if gid in CapIds(r1) then AncCaps(r1, gid) else AncCaps(r2, gid)
    case Re_quant(nul, qid, q, r1) => AncCaps(r1, gid)
    case Re_capture(cid, r1) =>
      if cid >= 0 && (cid as nat) == gid then {}
      else (if cid >= 0 then {cid as nat} else {}) + AncCaps(r1, gid)
    case Re_lookaround(lid, l, r1) => AncCaps(r1, gid)
  }

  // Quant ids enclosing gid.
  /** Quantifier ids enclosing `gid`. */
  ghost function AncQuants(r: R.regex, gid: nat): (res: set<nat>)
    requires gid in CapIds(r)
    ensures res <= QuantIds(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => if gid in CapIds(r1) then AncQuants(r1, gid) else AncQuants(r2, gid)
    case Re_con(r1, r2) => if gid in CapIds(r1) then AncQuants(r1, gid) else AncQuants(r2, gid)
    case Re_quant(nul, qid, q, r1) => (if qid >= 0 then {qid as nat} else {}) + AncQuants(r1, gid)
    case Re_capture(cid, r1) =>
      if cid >= 0 && (cid as nat) == gid then {} else AncQuants(r1, gid)
    case Re_lookaround(lid, l, r1) => AncQuants(r1, gid)
  }

  // Same for a target quant qid: capture/quant ids strictly enclosing it.
  /** Capture ids strictly enclosing quantifier `qid`. */
  ghost function AncCapsQ(r: R.regex, qid: nat): (res: set<nat>)
    requires qid in QuantIds(r)
    ensures res <= CapIds(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => if qid in QuantIds(r1) then AncCapsQ(r1, qid) else AncCapsQ(r2, qid)
    case Re_con(r1, r2) => if qid in QuantIds(r1) then AncCapsQ(r1, qid) else AncCapsQ(r2, qid)
    case Re_quant(nul, qid0, q, r1) =>
      if qid0 >= 0 && (qid0 as nat) == qid then {} else AncCapsQ(r1, qid)
    case Re_capture(cid, r1) => (if cid >= 0 then {cid as nat} else {}) + AncCapsQ(r1, qid)
    case Re_lookaround(lid, l, r1) => AncCapsQ(r1, qid)
  }

  /** Quantifier ids strictly enclosing quantifier `qid`. */
  ghost function AncQuantsQ(r: R.regex, qid: nat): (res: set<nat>)
    requires qid in QuantIds(r)
    ensures res <= QuantIds(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => if qid in QuantIds(r1) then AncQuantsQ(r1, qid) else AncQuantsQ(r2, qid)
    case Re_con(r1, r2) => if qid in QuantIds(r1) then AncQuantsQ(r1, qid) else AncQuantsQ(r2, qid)
    case Re_quant(nul, qid0, q, r1) =>
      if qid0 >= 0 && (qid0 as nat) == qid then {} else (if qid0 >= 0 then {qid0 as nat} else {}) + AncQuantsQ(r1, qid)
    case Re_capture(cid, r1) => AncQuantsQ(r1, qid)
    case Re_lookaround(lid, l, r1) => AncQuantsQ(r1, qid)
  }

  // Per-ancestor freshness assembles into PathPresent: if every enclosing
  // capture's start clock and every enclosing quant's stamp is >= its own MxAt
  // threshold, the whole descent is in the filter's present branch.
  /** Per-ancestor freshness assembles into `PathPresent`: if every enclosing
      capture's start clock and every enclosing quant's stamp is `>=` its own
      `MxAt` threshold, the whole descent is in the filter's present branch. */
  lemma PathPresentIntro(r: R.regex, cc: seq<int>, qc: seq<int>, mx: int, gid: nat)
    requires gid in CapIds(r)
    requires CapUnique(r) && QuantUnique(r)
    requires forall c: nat :: c in AncCaps(r, gid)
               ==> AI.get_idx(cc, CP.start_reg(c)) >= 0
                   && AI.get_idx(cc, CP.start_reg(c)) >= MxAtGid(r, cc, qc, mx, c)
    requires forall q: nat :: q in AncQuants(r, gid)
               ==> AI.get_idx(qc, q) >= MxAtQid(r, cc, qc, mx, q)
    ensures PathPresent(r, cc, qc, mx, gid)
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      if gid in CapIds(r1) {
        forall c: nat | c in AncCaps(r1, gid)
          ensures MxAtGid(r1, cc, qc, mx, c) == MxAtGid(r, cc, qc, mx, c) {}
        forall q: nat | q in AncQuants(r1, gid)
          ensures MxAtQid(r1, cc, qc, mx, q) == MxAtQid(r, cc, qc, mx, q)
        {
          assert q !in QuantIds(r2) by { if q in QuantIds(r2) { assert q in QuantIds(r1) * QuantIds(r2); } }
        }
        PathPresentIntro(r1, cc, qc, mx, gid);
      } else {
        forall c: nat | c in AncCaps(r2, gid)
          ensures MxAtGid(r2, cc, qc, mx, c) == MxAtGid(r, cc, qc, mx, c)
        {
          assert c !in CapIds(r1) by { if c in CapIds(r1) { assert c in CapIds(r1) * CapIds(r2); } }
        }
        forall q: nat | q in AncQuants(r2, gid)
          ensures MxAtQid(r2, cc, qc, mx, q) == MxAtQid(r, cc, qc, mx, q)
        {
          assert q !in QuantIds(r1) by { if q in QuantIds(r1) { assert q in QuantIds(r1) * QuantIds(r2); } }
        }
        PathPresentIntro(r2, cc, qc, mx, gid);
      }
    case Re_con(r1, r2) =>
      if gid in CapIds(r1) {
        forall c: nat | c in AncCaps(r1, gid)
          ensures MxAtGid(r1, cc, qc, mx, c) == MxAtGid(r, cc, qc, mx, c) {}
        forall q: nat | q in AncQuants(r1, gid)
          ensures MxAtQid(r1, cc, qc, mx, q) == MxAtQid(r, cc, qc, mx, q)
        {
          assert q !in QuantIds(r2) by { if q in QuantIds(r2) { assert q in QuantIds(r1) * QuantIds(r2); } }
        }
        PathPresentIntro(r1, cc, qc, mx, gid);
      } else {
        forall c: nat | c in AncCaps(r2, gid)
          ensures MxAtGid(r2, cc, qc, mx, c) == MxAtGid(r, cc, qc, mx, c)
        {
          assert c !in CapIds(r1) by { if c in CapIds(r1) { assert c in CapIds(r1) * CapIds(r2); } }
        }
        forall q: nat | q in AncQuants(r2, gid)
          ensures MxAtQid(r2, cc, qc, mx, q) == MxAtQid(r, cc, qc, mx, q)
        {
          assert q !in QuantIds(r1) by { if q in QuantIds(r1) { assert q in QuantIds(r1) * QuantIds(r2); } }
        }
        PathPresentIntro(r2, cc, qc, mx, gid);
      }
    case Re_quant(nul, qid, q, r1) =>
      assert qid >= 0;                       // QuantUnique
      var qv := AI.get_idx(qc, qid);
      assert (qid as nat) in AncQuants(r, gid);
      assert MxAtQid(r, cc, qc, mx, qid as nat) == mx;
      assert qv >= mx;
      forall c: nat | c in AncCaps(r1, gid)
        ensures MxAtGid(r1, cc, qc, qv, c) == MxAtGid(r, cc, qc, mx, c) {}
      forall q0: nat | q0 in AncQuants(r1, gid)
        ensures MxAtQid(r1, cc, qc, qv, q0) == MxAtQid(r, cc, qc, mx, q0)
      {
        assert q0 != qid as nat by {
          assert q0 in QuantIds(r1);
          assert (qid as nat) !in QuantIds(r1);   // QuantUnique
        }
      }
      PathPresentIntro(r1, cc, qc, qv, gid);
    case Re_capture(cid, r1) =>
      if cid >= 0 && (cid as nat) == gid {
        // base: PathPresent holds at gid's own node.
      } else {
        assert gid in CapIds(r1);
        if cid >= 0 {
          assert (cid as nat) in AncCaps(r, gid);
          assert MxAtGid(r, cc, qc, mx, cid as nat) == mx;
          assert AI.get_idx(cc, CP.start_reg(cid as nat)) >= 0;
          assert AI.get_idx(cc, CP.start_reg(cid as nat)) >= mx;
        }
        forall c: nat | c in AncCaps(r1, gid)
          ensures MxAtGid(r1, cc, qc, mx, c) == MxAtGid(r, cc, qc, mx, c)
        {
          assert c in CapIds(r1);
          // CapUnique: this node's id is not in its own body, so c != cid and
          // MxAtGid(r) descends into r1 with the same threshold.
          if cid >= 0 { assert (cid as nat) !in CapIds(r1); }
        }
        forall q0: nat | q0 in AncQuants(r1, gid)
          ensures MxAtQid(r1, cc, qc, mx, q0) == MxAtQid(r, cc, qc, mx, q0) {}
        PathPresentIntro(r1, cc, qc, mx, gid);
      }
    case Re_lookaround(lid, l, r1) =>
      forall c: nat | c in AncCaps(r1, gid)
        ensures MxAtGid(r1, cc, qc, mx, c) == MxAtGid(r, cc, qc, mx, c) {}
      forall q0: nat | q0 in AncQuants(r1, gid)
        ensures MxAtQid(r1, cc, qc, mx, q0) == MxAtQid(r, cc, qc, mx, q0) {}
      PathPresentIntro(r1, cc, qc, mx, gid);
  }

  // The quant-target analog: per-ancestor freshness assembles into PathPresentQ.
  /** The quant-target analog of `PathPresentIntro`: per-ancestor freshness
      assembles into `PathPresentQ`. */
  lemma PathPresentQIntro(r: R.regex, cc: seq<int>, qc: seq<int>, mx: int, qid: nat)
    requires qid in QuantIds(r)
    requires CapUnique(r) && QuantUnique(r)
    requires forall c: nat :: c in AncCapsQ(r, qid)
               ==> AI.get_idx(cc, CP.start_reg(c)) >= 0
                   && AI.get_idx(cc, CP.start_reg(c)) >= MxAtGid(r, cc, qc, mx, c)
    requires forall q: nat :: q in AncQuantsQ(r, qid)
               ==> AI.get_idx(qc, q) >= MxAtQid(r, cc, qc, mx, q)
    ensures PathPresentQ(r, cc, qc, mx, qid)
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      if qid in QuantIds(r1) {
        forall c: nat | c in AncCapsQ(r1, qid)
          ensures MxAtGid(r1, cc, qc, mx, c) == MxAtGid(r, cc, qc, mx, c) {}
        forall q: nat | q in AncQuantsQ(r1, qid)
          ensures MxAtQid(r1, cc, qc, mx, q) == MxAtQid(r, cc, qc, mx, q)
        {
          assert q !in QuantIds(r2) by { if q in QuantIds(r2) { assert q in QuantIds(r1) * QuantIds(r2); } }
        }
        PathPresentQIntro(r1, cc, qc, mx, qid);
      } else {
        forall c: nat | c in AncCapsQ(r2, qid)
          ensures MxAtGid(r2, cc, qc, mx, c) == MxAtGid(r, cc, qc, mx, c)
        {
          assert c !in CapIds(r1) by { if c in CapIds(r1) { assert c in CapIds(r1) * CapIds(r2); } }
        }
        forall q: nat | q in AncQuantsQ(r2, qid)
          ensures MxAtQid(r2, cc, qc, mx, q) == MxAtQid(r, cc, qc, mx, q)
        {
          assert q !in QuantIds(r1) by { if q in QuantIds(r1) { assert q in QuantIds(r1) * QuantIds(r2); } }
        }
        PathPresentQIntro(r2, cc, qc, mx, qid);
      }
    case Re_con(r1, r2) =>
      if qid in QuantIds(r1) {
        forall c: nat | c in AncCapsQ(r1, qid)
          ensures MxAtGid(r1, cc, qc, mx, c) == MxAtGid(r, cc, qc, mx, c) {}
        forall q: nat | q in AncQuantsQ(r1, qid)
          ensures MxAtQid(r1, cc, qc, mx, q) == MxAtQid(r, cc, qc, mx, q)
        {
          assert q !in QuantIds(r2) by { if q in QuantIds(r2) { assert q in QuantIds(r1) * QuantIds(r2); } }
        }
        PathPresentQIntro(r1, cc, qc, mx, qid);
      } else {
        forall c: nat | c in AncCapsQ(r2, qid)
          ensures MxAtGid(r2, cc, qc, mx, c) == MxAtGid(r, cc, qc, mx, c)
        {
          assert c !in CapIds(r1) by { if c in CapIds(r1) { assert c in CapIds(r1) * CapIds(r2); } }
        }
        forall q: nat | q in AncQuantsQ(r2, qid)
          ensures MxAtQid(r2, cc, qc, mx, q) == MxAtQid(r, cc, qc, mx, q)
        {
          assert q !in QuantIds(r1) by { if q in QuantIds(r1) { assert q in QuantIds(r1) * QuantIds(r2); } }
        }
        PathPresentQIntro(r2, cc, qc, mx, qid);
      }
    case Re_quant(nul, qid0, q, r1) =>
      assert qid0 >= 0;                     // QuantUnique
      if (qid0 as nat) == qid {
        // base: PathPresentQ holds at qid's own node.
      } else {
        assert qid in QuantIds(r1);
        var qv := AI.get_idx(qc, qid0);
        assert (qid0 as nat) in AncQuantsQ(r, qid);
        assert MxAtQid(r, cc, qc, mx, qid0 as nat) == mx;
        assert qv >= mx;
        forall c: nat | c in AncCapsQ(r1, qid)
          ensures MxAtGid(r1, cc, qc, qv, c) == MxAtGid(r, cc, qc, mx, c) {}
        forall q0: nat | q0 in AncQuantsQ(r1, qid)
          ensures MxAtQid(r1, cc, qc, qv, q0) == MxAtQid(r, cc, qc, mx, q0)
        {
          assert q0 != qid0 as nat by {
            assert q0 in QuantIds(r1);
            assert (qid0 as nat) !in QuantIds(r1);   // QuantUnique
          }
        }
        PathPresentQIntro(r1, cc, qc, qv, qid);
      }
    case Re_capture(cid, r1) =>
      if cid >= 0 {
        assert (cid as nat) in AncCapsQ(r, qid);
        assert MxAtGid(r, cc, qc, mx, cid as nat) == mx;
        assert AI.get_idx(cc, CP.start_reg(cid as nat)) >= 0;
        assert AI.get_idx(cc, CP.start_reg(cid as nat)) >= mx;
      }
      forall c: nat | c in AncCapsQ(r1, qid)
        ensures MxAtGid(r1, cc, qc, mx, c) == MxAtGid(r, cc, qc, mx, c)
      {
        if cid >= 0 { assert (cid as nat) !in CapIds(r1); }   // CapUnique
      }
      forall q0: nat | q0 in AncQuantsQ(r1, qid)
        ensures MxAtQid(r1, cc, qc, mx, q0) == MxAtQid(r, cc, qc, mx, q0) {}
      PathPresentQIntro(r1, cc, qc, mx, qid);
    case Re_lookaround(lid, l, r1) =>
      forall c: nat | c in AncCapsQ(r1, qid)
        ensures MxAtGid(r1, cc, qc, mx, c) == MxAtGid(r, cc, qc, mx, c) {}
      forall q0: nat | q0 in AncQuantsQ(r1, qid)
        ensures MxAtQid(r1, cc, qc, mx, q0) == MxAtQid(r, cc, qc, mx, q0) {}
      PathPresentQIntro(r1, cc, qc, mx, qid);
  }

  // ===========================================================================
  // Presence extraction: a group PRESENT in the filter output was reached in
  // capture mode with a fresh clock — i.e. the filter's descent IS PathPresent.
  // Converts gm-visible ancestor presence (via ThreadTracksGm) into
  // PathPresentIntro's per-ancestor capture hypotheses; only the quant
  // hypotheses (stamps not gm-visible) remain for the positional invariant.
  // ===========================================================================
  /** Presence extraction: a group PRESENT in the filter output was reached in
      capture mode with a fresh clock — i.e. the filter's descent to `gid` IS
      `PathPresent`, and `gid`'s own start clock/value are fresh and set. */
  lemma FilterPresenceExtract(r: R.regex, cr: seq<int>, cc: seq<int>, lc: seq<int>, qc: seq<int>,
                              mx: int, gid: nat)
    requires NR.LookBehindFragmentRE(r)
    requires CapUnique(r)
    requires gid in CapIds(r)
    requires gid !in CapIdsInLooks(r)   // L3a: presence extraction is for outside-look gids
    requires forall c: nat :: c in CapIds(r) && AI.get_idx(cc, CP.start_reg(c)) < 0
                             ==> AI.get_idx(cr, CP.start_reg(c)) < 0
    requires AI.get_idx(AI.filter_capture(r, cr, cc, lc, qc, mx), CP.start_reg(gid)) >= 0
    ensures PathPresent(r, cc, qc, mx, gid)
    ensures AI.get_idx(cc, CP.start_reg(gid)) >= 0
    ensures AI.get_idx(cc, CP.start_reg(gid)) >= MxAtGid(r, cc, qc, mx, gid)
    ensures AI.get_idx(cr, CP.start_reg(gid)) >= 0
    decreases r
  {
    match r
    case Re_empty => case Re_character(_) => case Re_anchor(_) =>
    case Re_lookaround(_, _, r1) =>
      assert gid in CapIdsInLooks(r);   // == CapIds(r1) ∋ gid, contradicts the outside-look requires
      assert false;
    case Re_alt(r1, r2) =>
      var c1 := AI.filter_capture(r1, cr, cc, lc, qc, mx);
      if gid in CapIds(r1) {
        assert gid !in CapIds(r2) by { if gid in CapIds(r2) { assert gid in CapIds(r1) * CapIds(r2); } }
        FilterCaptureOutside(r2, c1, cc, lc, qc, mx, gid);   // output == c1[start_reg(gid)]
        FilterPresenceExtract(r1, cr, cc, lc, qc, mx, gid);
      } else {
        assert gid in CapIds(r2) && gid !in CapIds(r1);
        // Consistency transfers to c1 on r2's registers (disjoint from r1's).
        forall c: nat | c in CapIds(r2) && AI.get_idx(cc, CP.start_reg(c)) < 0
          ensures AI.get_idx(c1, CP.start_reg(c)) < 0
        {
          assert c !in CapIds(r1) by { if c in CapIds(r1) { assert c in CapIds(r1) * CapIds(r2); } }
          FilterCaptureOutside(r1, cr, cc, lc, qc, mx, c);
        }
        FilterPresenceExtract(r2, c1, cc, lc, qc, mx, gid);
        FilterCaptureOutside(r1, cr, cc, lc, qc, mx, gid);   // c1[start_reg(gid)] == cr[...]
      }
    case Re_con(r1, r2) =>
      var c1 := AI.filter_capture(r1, cr, cc, lc, qc, mx);
      if gid in CapIds(r1) {
        assert gid !in CapIds(r2) by { if gid in CapIds(r2) { assert gid in CapIds(r1) * CapIds(r2); } }
        FilterCaptureOutside(r2, c1, cc, lc, qc, mx, gid);
        FilterPresenceExtract(r1, cr, cc, lc, qc, mx, gid);
      } else {
        assert gid in CapIds(r2) && gid !in CapIds(r1);
        forall c: nat | c in CapIds(r2) && AI.get_idx(cc, CP.start_reg(c)) < 0
          ensures AI.get_idx(c1, CP.start_reg(c)) < 0
        {
          assert c !in CapIds(r1) by { if c in CapIds(r1) { assert c in CapIds(r1) * CapIds(r2); } }
          FilterCaptureOutside(r1, cr, cc, lc, qc, mx, c);
        }
        FilterPresenceExtract(r2, c1, cc, lc, qc, mx, gid);
        FilterCaptureOutside(r1, cr, cc, lc, qc, mx, gid);
      }
    case Re_quant(nul, qid, q, r1) =>
      var qv := AI.get_idx(qc, qid);
      if qv < mx {
        // filter_all clears every capture start in the subtree: contradiction.
        FilterAllClearsStart(r1, cr, gid);
        assert false;
      } else {
        FilterPresenceExtract(r1, cr, cc, lc, qc, qv, gid);
      }
    case Re_capture(cid, r1) =>
      var start := AI.get_idx(cc, CP.start_reg(cid));
      if cid >= 0 && (cid as nat) == gid {
        assert gid !in CapIds(r1);                        // CapUnique
        if start < 0 {
          // unset clock ⟹ unset value (consistency); filter_all passes it through.
          FilterAllOutside(r1, cr, gid);
          assert AI.get_idx(cr, CP.start_reg(gid)) < 0;
          assert false;
        } else if start < mx {
          // stale: the filter itself cleared the start.
          var cr2 := AI.set_idx(cr, CP.start_reg(cid), -1);
          FilterAllOutside(r1, cr2, gid);
          assert AI.get_idx(cr2, CP.start_reg(gid)) <= -1;
          assert false;
        } else {
          // present branch: value passes through, thresholds established.
          FilterCaptureOutside(r1, cr, cc, lc, qc, mx, gid);
          assert MxAtGid(r, cc, qc, mx, gid) == mx;
        }
      } else {
        assert gid in CapIds(r1);
        if start < 0 {
          FilterAllClearsStart(r1, cr, gid);
          assert false;
        } else if start < mx {
          var cr2 := AI.set_idx(cr, CP.start_reg(cid), -1);
          FilterAllClearsStart(r1, cr2, gid);
          assert false;
        } else {
          // ancestor present branch: cid's own conditions + recurse.
          forall c: nat | c in CapIds(r1) && AI.get_idx(cc, CP.start_reg(c)) < 0
            ensures AI.get_idx(cr, CP.start_reg(c)) < 0 {}
          FilterPresenceExtract(r1, cr, cc, lc, qc, mx, gid);
        }
      }
  }

  // gm-level wrapper: a group present in the live denotation is PathPresent
  // with a fresh start clock. Combined with tree-side group discipline ("Open
  // only fires inside open ancestors"), this discharges PathPresentIntro's
  // AncCaps hypotheses straight from ThreadTracksGm.
  /** gm-level wrapper for `FilterPresenceExtract`: a group present in the live
      denotation (`GmOfLive`) is `PathPresent` with a fresh start clock —
      discharges `PathPresentIntro`'s `AncCaps` hypotheses from
      `ThreadTracksGm`. */
  lemma GmOfLivePresenceExtract(ast: R.regex, caps: AReg.Regs, look: AReg.Regs, quant: AReg.Regs, gid: nat)
    requires NR.LookBehindFragmentRE(ast)
    requires CapUnique(ast)
    requires gid in CapIds(ast)
    requires gid !in CapIdsInLooks(ast)   // L3a: presence extraction is for outside-look gids
    requires forall c: nat :: c in CapIds(ast) && AI.get_idx(caps.a_clk, CP.start_reg(c)) < 0
                             ==> AI.get_idx(caps.a_cp, CP.start_reg(c)) < 0
    requires gid in GmOfLive(ast, caps, look, quant)
    ensures PathPresent(ast, caps.a_clk, AReg.as_arrays(quant).1, -1, gid)
    ensures AI.get_idx(caps.a_clk, CP.start_reg(gid)) >= 0
    ensures AI.get_idx(caps.a_clk, CP.start_reg(gid))
              >= MxAtGid(ast, caps.a_clk, AReg.as_arrays(quant).1, -1, gid)
  {
    var (cr, cc) := AReg.as_arrays(caps);
    var (_, lc) := AReg.as_arrays(look);
    var (_, qc) := AReg.as_arrays(quant);
    var f := AI.filter_reset(ast, caps, look, quant, -1);
    assert f == AI.filter_capture(ast, cr, cc, lc, qc, -1);
    assert AI.get_idx(f, CP.start_reg(gid)) >= 0;
    FilterPresenceExtract(ast, cr, cc, lc, qc, -1, gid);
  }

  // ===========================================================================
  // Absence extraction: the dual. If gid's ancestors are all present (path in
  // capture mode) yet gid is ABSENT from the filter output, the failure is at
  // gid's own node — its start clock is stale or unset. This is exactly the
  // Open-site "stale-or-unset" hypothesis of GmOfLiveOpenGMOpen. Needs the
  // set-together consistency direction (fresh clock ⟹ set value): a fresh
  // clock with an unset value would fake absence.
  // ===========================================================================
  /** Absence extraction (dual of `FilterPresenceExtract`): if `gid`'s ancestors
      are all present (`PathPresent`) yet `gid` is ABSENT from the filter
      output, the failure is at `gid`'s own node — its start clock is stale or
      unset. Exactly the Open-site "stale-or-unset" hypothesis. */
  lemma FilterAbsenceExtract(r: R.regex, cr: seq<int>, cc: seq<int>, lc: seq<int>, qc: seq<int>,
                             mx: int, gid: nat)
    requires NR.LookBehindFragmentRE(r)
    requires CapUnique(r)
    requires gid in CapIds(r)
    requires gid !in CapIdsInLooks(r)   // L3a: absence extraction is for outside-look gids
    requires PathPresent(r, cc, qc, mx, gid)
    requires forall c: nat :: c in CapIds(r) && AI.get_idx(cc, CP.start_reg(c)) >= 0
                             ==> AI.get_idx(cr, CP.start_reg(c)) >= 0
    requires AI.get_idx(AI.filter_capture(r, cr, cc, lc, qc, mx), CP.start_reg(gid)) < 0
    ensures AI.get_idx(cc, CP.start_reg(gid)) < MxAtGid(r, cc, qc, mx, gid)
         || AI.get_idx(cc, CP.start_reg(gid)) < 0
    decreases r
  {
    match r
    case Re_empty => case Re_character(_) => case Re_anchor(_) =>
    case Re_lookaround(_, _, r1) => CaptureFreeNoCapIds(r1);   // gid in CapIds({}) is false
    case Re_alt(r1, r2) =>
      var c1 := AI.filter_capture(r1, cr, cc, lc, qc, mx);
      if gid in CapIds(r1) {
        assert gid !in CapIds(r2) by { if gid in CapIds(r2) { assert gid in CapIds(r1) * CapIds(r2); } }
        FilterCaptureOutside(r2, c1, cc, lc, qc, mx, gid);   // output == c1[start_reg(gid)]
        FilterAbsenceExtract(r1, cr, cc, lc, qc, mx, gid);
      } else {
        assert gid in CapIds(r2) && gid !in CapIds(r1);
        forall c: nat | c in CapIds(r2) && AI.get_idx(cc, CP.start_reg(c)) >= 0
          ensures AI.get_idx(c1, CP.start_reg(c)) >= 0
        {
          assert c !in CapIds(r1) by { if c in CapIds(r1) { assert c in CapIds(r1) * CapIds(r2); } }
          FilterCaptureOutside(r1, cr, cc, lc, qc, mx, c);
        }
        FilterAbsenceExtract(r2, c1, cc, lc, qc, mx, gid);
      }
    case Re_con(r1, r2) =>
      var c1 := AI.filter_capture(r1, cr, cc, lc, qc, mx);
      if gid in CapIds(r1) {
        assert gid !in CapIds(r2) by { if gid in CapIds(r2) { assert gid in CapIds(r1) * CapIds(r2); } }
        FilterCaptureOutside(r2, c1, cc, lc, qc, mx, gid);
        FilterAbsenceExtract(r1, cr, cc, lc, qc, mx, gid);
      } else {
        assert gid in CapIds(r2) && gid !in CapIds(r1);
        forall c: nat | c in CapIds(r2) && AI.get_idx(cc, CP.start_reg(c)) >= 0
          ensures AI.get_idx(c1, CP.start_reg(c)) >= 0
        {
          assert c !in CapIds(r1) by { if c in CapIds(r1) { assert c in CapIds(r1) * CapIds(r2); } }
          FilterCaptureOutside(r1, cr, cc, lc, qc, mx, c);
        }
        FilterAbsenceExtract(r2, c1, cc, lc, qc, mx, gid);
      }
    case Re_quant(nul, qid, q, r1) =>
      var qv := AI.get_idx(qc, qid);
      assert qv >= mx;                                    // PathPresent
      FilterAbsenceExtract(r1, cr, cc, lc, qc, qv, gid);
    case Re_capture(cid, r1) =>
      var start := AI.get_idx(cc, CP.start_reg(cid));
      if cid >= 0 && (cid as nat) == gid {
        assert gid !in CapIds(r1);                        // CapUnique
        assert MxAtGid(r, cc, qc, mx, gid) == mx;
        if start >= mx && start >= 0 {
          // present branch would expose the (set) value: contradiction.
          FilterCaptureOutside(r1, cr, cc, lc, qc, mx, gid);
          assert AI.get_idx(cr, CP.start_reg(gid)) >= 0;  // set-together consistency
          assert false;
        }
      } else {
        assert gid in CapIds(r1);
        assert start >= 0 && start >= mx;                 // PathPresent at ancestor cid
        FilterAbsenceExtract(r1, cr, cc, lc, qc, mx, gid);
      }
  }

  // gm-level wrapper: gid absent from the live denotation while PathPresent
  // holds ⟹ gid's own start clock is stale-or-unset — the exact Open-site
  // hypothesis. CapRegWf supplies the consistency direction.
  /** gm-level wrapper for `FilterAbsenceExtract`: `gid` absent from the live
      denotation while `PathPresent` holds ⟹ its start clock is stale-or-unset,
      the Open-site hypothesis. `CapRegWf` supplies the consistency direction. */
  lemma GmOfLiveAbsenceExtract(ast: R.regex, caps: AReg.Regs, look: AReg.Regs, quant: AReg.Regs, gid: nat)
    requires NR.LookBehindFragmentRE(ast)
    requires CapUnique(ast)
    requires gid in CapIds(ast)
    requires gid !in CapIdsInLooks(ast)   // L3a: absence extraction is for outside-look gids
    requires CapRegWf(caps)
    requires PathPresent(ast, caps.a_clk, AReg.as_arrays(quant).1, -1, gid)
    requires gid !in GmOfLive(ast, caps, look, quant)
    ensures AI.get_idx(caps.a_clk, CP.start_reg(gid))
              < MxAtGid(ast, caps.a_clk, AReg.as_arrays(quant).1, -1, gid)
         || AI.get_idx(caps.a_clk, CP.start_reg(gid)) < 0
  {
    var (cr, cc) := AReg.as_arrays(caps);
    var (_, lc) := AReg.as_arrays(look);
    var (_, qc) := AReg.as_arrays(quant);
    var f := AI.filter_reset(ast, caps, look, quant, -1);
    assert f == AI.filter_capture(ast, cr, cc, lc, qc, -1);
    FilterCaptureLen(ast, cr, cc, lc, qc, -1);
    // Absence at any gid means the output start slot is negative (out-of-range
    // start slots read as -1 via get_idx).
    assert AI.get_idx(f, CP.start_reg(gid)) < 0 by {
      if 0 <= gid < |f| {
        assert AI.get_idx(f, CP.start_reg(gid)) < 0;   // gid !in domain comprehension
      } else {
        assert CP.start_reg(gid) >= |f|;               // 2*gid >= gid >= |f|
      }
    }
    FilterAbsenceExtract(ast, cr, cc, lc, qc, -1, gid);
  }

  // annotate assigns capture ids by a monotonic left-to-right counter, so all
  // ids of annotate_regex(ra,c,l,q) lie in [c, c') and are unique.
  /** `annotate_regex` assigns capture ids by a monotonic left-to-right counter,
      so the ids of its output are unique and lie in `[c, c')`. */
  lemma AnnotateCapUnique(ra: R.raw_regex, c: int, l: int, q: int)
    requires c >= 0
    ensures var res := R.annotate_regex(ra, c, l, q);
      c <= res.1 && CapUnique(res.0)
      && (forall x: nat :: x in CapIds(res.0) ==> c <= x < res.1)
    decreases ra
  {
    match ra
    case Raw_empty => case Raw_character(_) => case Raw_anchor(_) =>
    case Raw_alt(r1, r2) =>
      var (ar1, c1, l1, q1) := R.annotate_regex(r1, c, l, q);
      AnnotateCapUnique(r1, c, l, q);
      AnnotateCapUnique(r2, c1, l1, q1);
    case Raw_con(r1, r2) =>
      var (ar1, c1, l1, q1) := R.annotate_regex(r1, c, l, q);
      AnnotateCapUnique(r1, c, l, q);
      AnnotateCapUnique(r2, c1, l1, q1);
    case Raw_quant(quant, r1) => AnnotateCapUnique(r1, c, l, q + 1);
    case Raw_count(quant, r1) => AnnotateCapUnique(r1, c, l, q + 1);
    case Raw_capture(r1) => AnnotateCapUnique(r1, c + 1, l, q);
    case Raw_lookaround(look, r1) => AnnotateCapUnique(r1, c, l + 1, q);
  }

  /** `annotate_regex` assigns quant ids by a monotonic counter, so they are
      unique and lie in `[q, q')` (the quant analog of `AnnotateCapUnique`). */
  lemma AnnotateQuantUnique(ra: R.raw_regex, c: int, l: int, q: int)
    requires q >= 0
    ensures var res := R.annotate_regex(ra, c, l, q);
      q <= res.3 && QuantUnique(res.0)
      && (forall x: nat :: x in QuantIds(res.0) ==> q <= x < res.3)
    decreases ra
  {
    match ra
    case Raw_empty => case Raw_character(_) => case Raw_anchor(_) =>
    case Raw_alt(r1, r2) =>
      var (ar1, c1, l1, q1) := R.annotate_regex(r1, c, l, q);
      AnnotateQuantUnique(r1, c, l, q);
      AnnotateQuantUnique(r2, c1, l1, q1);
    case Raw_con(r1, r2) =>
      var (ar1, c1, l1, q1) := R.annotate_regex(r1, c, l, q);
      AnnotateQuantUnique(r1, c, l, q);
      AnnotateQuantUnique(r2, c1, l1, q1);
    case Raw_quant(quant, r1) => AnnotateQuantUnique(r1, c, l, q + 1);
    case Raw_count(quant, r1) => AnnotateQuantUnique(r1, c, l, q + 1);
    case Raw_capture(r1) => AnnotateQuantUnique(r1, c + 1, l, q);
    case Raw_lookaround(look, r1) => AnnotateQuantUnique(r1, c, l + 1, q);
  }

  // The search regex ast = lazy_prefix(annotate(raw)) is capture- and
  // quant-unique: annotate's ids are unique and range-bounded (caps ⊆ [0,·),
  // quants ⊆ [1,·)), and the lazy prefix's own quant id 0 / capture-free body
  // (Dot) stay disjoint.
  /** The search regex `lazy_prefix(annotate(raw))` is capture-unique. */
  lemma SpecRegexCapUnique(raw: R.raw_regex)
    ensures CapUnique(R.lazy_prefix(R.annotate(raw)))
  {
    AnnotateCapUnique(R.Raw_capture(raw), 0, 1, 1);
  }

  /** The search regex `lazy_prefix(annotate(raw))` is quant-unique. */
  lemma SpecRegexQuantUnique(raw: R.raw_regex)
    ensures QuantUnique(R.lazy_prefix(R.annotate(raw)))
  {
    AnnotateQuantUnique(R.Raw_capture(raw), 0, 1, 1);
  }

  // Capture-register well-formedness: values are ≥ -1, and an absent clock (< 0)
  // implies an absent value (< 0). Maintained by init (all -1) and by
  // SetRegisterToCP (writes cp ≥ 0 with clock ≥ 0). Discharges the register-wf /
  // consistency hypotheses of GmOfLive{Open,Reset}Full.
  /** Capture-register well-formedness: values are `>= -1`, and clock/value are
      set together (an absent clock forces an absent value and vice versa).
      Maintained by init (all `-1`) and `SetRegisterToCP`; discharges the
      consistency hypotheses of the `GmOfLive` effect lemmas. */
  ghost predicate CapRegWf(caps: AReg.ARegs)
  {
    |caps.a_cp| == |caps.a_clk|
    && (forall k :: AI.get_idx(caps.a_cp, k) >= -1)
    && (forall k :: AI.get_idx(caps.a_clk, k) < 0 ==> AI.get_idx(caps.a_cp, k) < 0)
    // clock and value are set together (init both -1, set_reg writes both):
    && (forall k :: AI.get_idx(caps.a_clk, k) >= 0 ==> AI.get_idx(caps.a_cp, k) >= 0)
  }

  /** Fresh `init_regs` (all `-1`) are `CapRegWf`. */
  lemma CapRegWfInit(n: int)
    ensures CapRegWf(AReg.init_regs(n))
  {
    var caps := AReg.init_regs(n);
    assert caps.a_cp == AReg.init_regs(n).a_cp;
    assert caps.a_clk == AReg.init_regs(n).a_clk;
    assert |caps.a_cp| == |caps.a_clk|;
    assert forall i :: AI.get_idx(caps.a_cp, i) < 0;
    assert forall i :: AI.get_idx(caps.a_cp, i) >= -1;
    assert forall i :: AI.get_idx(caps.a_clk, i) < 0;
  }

  /** `set_reg` with a non-negative `cp` and `clk` preserves `CapRegWf`. */
  lemma CapRegWfSet(caps: AReg.ARegs, k: int, cp: int, clk: int)
    requires CapRegWf(caps)
    requires cp >= 0 && clk >= 0
    ensures CapRegWf(AReg.set_reg(caps, k, Some(cp), clk))
  {
    var caps' := AReg.set_reg(caps, k, Some(cp), clk);
    if 0 <= k < |caps.a_cp| && 0 <= k < |caps.a_clk| {
      assert caps'.a_cp == caps.a_cp[k := cp];
      assert caps'.a_clk == caps.a_clk[k := clk];
      assert |caps'.a_cp| == |caps'.a_clk|;
      forall j ensures AI.get_idx(caps'.a_cp, j) >= -1 {
        if 0 <= j < |caps'.a_cp| {
          if j == k { assert caps'.a_cp[j] == cp; }
          else { assert caps'.a_cp[j] == caps.a_cp[j]; assert AI.get_idx(caps.a_cp, j) == caps.a_cp[j]; }
        }
      }
      forall j ensures AI.get_idx(caps'.a_clk, j) < 0 ==> AI.get_idx(caps'.a_cp, j) < 0 {
        if 0 <= j < |caps'.a_clk| {
          if j == k { assert caps'.a_clk[j] == clk; }
          else {
            assert caps'.a_clk[j] == caps.a_clk[j] && caps'.a_cp[j] == caps.a_cp[j];
            assert AI.get_idx(caps.a_clk, j) == caps.a_clk[j] && AI.get_idx(caps.a_cp, j) == caps.a_cp[j];
          }
        }
      }
      forall j ensures AI.get_idx(caps'.a_clk, j) >= 0 ==> AI.get_idx(caps'.a_cp, j) >= 0 {
        if 0 <= j < |caps'.a_clk| {
          if j == k { assert caps'.a_cp[j] == cp; }
          else {
            assert caps'.a_clk[j] == caps.a_clk[j] && caps'.a_cp[j] == caps.a_cp[j];
            assert AI.get_idx(caps.a_clk, j) == caps.a_clk[j] && AI.get_idx(caps.a_cp, j) == caps.a_cp[j];
          }
        }
      }
    } else {
      assert caps' == caps;
    }
  }

  /** The capture ids of `qid`'s body are a subset of `r`'s capture ids. */
  lemma CapIdsQidBodySubset(r: R.regex, qid: nat)
    requires qid in QuantIds(r)
    ensures CapIds(QidBody(r, qid)) <= CapIds(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => if qid in QuantIds(r1) { CapIdsQidBodySubset(r1, qid); } else { CapIdsQidBodySubset(r2, qid); }
    case Re_con(r1, r2) => if qid in QuantIds(r1) { CapIdsQidBodySubset(r1, qid); } else { CapIdsQidBodySubset(r2, qid); }
    case Re_quant(nul, qid0, q, r1) => if qid0 >= 0 && (qid0 as nat) == qid {} else { CapIdsQidBodySubset(r1, qid); }
    case Re_capture(cid, r1) => CapIdsQidBodySubset(r1, qid);
    case Re_lookaround(lid, l, r1) => CapIdsQidBodySubset(r1, qid);
  }

  /** `filter_capture` never stores a value below `-1` (the `filter_capture`
      analog of `FilterAllGeqNeg1`). */
  lemma FilterCaptureGeqNeg1(r: R.regex, cr: seq<int>, cc: seq<int>, lc: seq<int>, qc: seq<int>, mx: int, i: int)
    requires NR.LookBehindFragmentRE(r)
    requires AI.get_idx(cr, i) >= -1
    ensures AI.get_idx(AI.filter_capture(r, cr, cc, lc, qc, mx), i) >= -1
    decreases r
  {
    match r
    case Re_lookaround(lid, la, r1) =>
      NR.PlusIsLookBehindFragmentRE(r1);
      var lv := AI.get_idx(lc, lid);
      if lv < 0 || lv < mx { FilterAllGeqNeg1(r1, cr, i); }
      else { FilterCaptureGeqNeg1(r1, cr, cc, lc, qc, -1, i); }
    case Re_empty => case Re_character(_) => case Re_anchor(_) =>
    case Re_alt(r1, r2) =>
      FilterCaptureGeqNeg1(r1, cr, cc, lc, qc, mx, i);
      FilterCaptureGeqNeg1(r2, AI.filter_capture(r1, cr, cc, lc, qc, mx), cc, lc, qc, mx, i);
    case Re_con(r1, r2) =>
      FilterCaptureGeqNeg1(r1, cr, cc, lc, qc, mx, i);
      FilterCaptureGeqNeg1(r2, AI.filter_capture(r1, cr, cc, lc, qc, mx), cc, lc, qc, mx, i);
    case Re_quant(nul, qid, q, r1) =>
      var qv := AI.get_idx(qc, qid);
      if qv < mx { FilterAllGeqNeg1(r1, cr, i); } else { FilterCaptureGeqNeg1(r1, cr, cc, lc, qc, qv, i); }
    case Re_capture(cid, r1) =>
      var start := AI.get_idx(cc, CP.start_reg(cid));
      if start < 0 { FilterAllGeqNeg1(r1, cr, i); }
      else if start < mx {
        if i == CP.start_reg(cid) {} else { SetIdxKeepsOther(cr, CP.start_reg(cid), i); }
        FilterAllGeqNeg1(r1, AI.set_idx(cr, CP.start_reg(cid), -1), i);
      } else { FilterCaptureGeqNeg1(r1, cr, cc, lc, qc, mx, i); }
  }

  // filter_all leaves any position that is not a capture-start of the subtree.
  /** `filter_all` leaves any position that is not a capture-start of the
      subtree unchanged. */
  lemma FilterAllKeepsNonStart(r: R.regex, Z: seq<int>, j: int)
    requires forall cid: nat :: cid in CapIds(r) ==> CP.start_reg(cid) != j
    ensures AI.get_idx(AI.filter_all(r, Z), j) == AI.get_idx(Z, j)
    decreases r
  {
    match r
    case Re_empty => case Re_character(_) => case Re_anchor(_) =>
    case Re_alt(r1, r2) => FilterAllKeepsNonStart(r1, Z, j); FilterAllKeepsNonStart(r2, AI.filter_all(r1, Z), j);
    case Re_con(r1, r2) => FilterAllKeepsNonStart(r1, Z, j); FilterAllKeepsNonStart(r2, AI.filter_all(r1, Z), j);
    case Re_quant(_, _, _, r1) => FilterAllKeepsNonStart(r1, Z, j);
    case Re_capture(cid, r1) =>
      if cid >= 0 { SetIdxKeepsOther(Z, CP.start_reg(cid), j); }
      FilterAllKeepsNonStart(r1, AI.set_idx(Z, CP.start_reg(cid), -1), j);
    case Re_lookaround(_, _, r1) => FilterAllKeepsNonStart(r1, Z, j);
  }

  // filter_capture and filter_all agree at every position that is NOT a
  // capture-start of the subtree (they can differ only there: filter_all clears
  // every start, filter_capture keeps the present ones).
  /** `filter_capture` and `filter_all` agree at every position that is NOT a
      capture-start of the subtree (they differ only there: `filter_all` clears
      every start, `filter_capture` keeps the present ones). */
  lemma FilterCaptureVsAll(r: R.regex, A: seq<int>, cc: seq<int>, lc: seq<int>, qc: seq<int>, M: int, j: int)
    requires NR.LookBehindFragmentRE(r)
    requires forall cid: nat :: cid in CapIds(r) ==> CP.start_reg(cid) != j
    ensures AI.get_idx(AI.filter_capture(r, A, cc, lc, qc, M), j) == AI.get_idx(AI.filter_all(r, A), j)
    decreases r
  {
    match r
    case Re_lookaround(lid, la, r1) =>
      NR.PlusIsLookBehindFragmentRE(r1);
      var lv := AI.get_idx(lc, lid);
      // reset: both sides == filter_all(r1, A)[j]; keep: recurse at mx=-1.
      if lv < 0 || lv < M {} else { FilterCaptureVsAll(r1, A, cc, lc, qc, -1, j); }
    case Re_empty => case Re_character(_) => case Re_anchor(_) =>
    case Re_alt(r1, r2) =>
      FilterCaptureVsAll(r1, A, cc, lc, qc, M, j);
      FilterCaptureVsAll(r2, AI.filter_capture(r1, A, cc, lc, qc, M), cc, lc, qc, M, j);
      FilterAllKeepsNonStart(r2, AI.filter_capture(r1, A, cc, lc, qc, M), j);
      FilterAllKeepsNonStart(r2, AI.filter_all(r1, A), j);
    case Re_con(r1, r2) =>
      FilterCaptureVsAll(r1, A, cc, lc, qc, M, j);
      FilterCaptureVsAll(r2, AI.filter_capture(r1, A, cc, lc, qc, M), cc, lc, qc, M, j);
      FilterAllKeepsNonStart(r2, AI.filter_capture(r1, A, cc, lc, qc, M), j);
      FilterAllKeepsNonStart(r2, AI.filter_all(r1, A), j);
    case Re_quant(nul, qid, q, r1) =>
      var qv := AI.get_idx(qc, qid);
      if qv < M {} else { FilterCaptureVsAll(r1, A, cc, lc, qc, qv, j); }
    case Re_capture(cid, r1) =>
      var start := AI.get_idx(cc, CP.start_reg(cid));
      if cid >= 0 { SetIdxKeepsOther(A, CP.start_reg(cid), j); }
      if start < 0 {
        FilterCaptureVsAll(r1, A, cc, lc, qc, M, j);   // unused branch shape; keep decreasing
        FilterAllKeepsNonStart(r1, A, j);
        FilterAllKeepsNonStart(r1, AI.set_idx(A, CP.start_reg(cid), -1), j);
      } else if start < M {
        // both == filter_all(r1, set_idx(A, start_reg(cid), -1))
      } else {
        FilterCaptureVsAll(r1, A, cc, lc, qc, M, j);
        FilterAllKeepsNonStart(r1, A, j);
        FilterAllKeepsNonStart(r1, AI.set_idx(A, CP.start_reg(cid), -1), j);
      }
  }

  // filter_all / filter_capture never READ capture values (only clocks), so the
  // output at position j is determined by the input at j alone.
  /** `filter_all` never reads capture values (only clocks), so its output at
      `j` is determined by the input at `j` alone. */
  lemma FilterAllCrPointwise(r: R.regex, X: seq<int>, Y: seq<int>, j: int)
    requires AI.get_idx(X, j) == AI.get_idx(Y, j)
    ensures AI.get_idx(AI.filter_all(r, X), j) == AI.get_idx(AI.filter_all(r, Y), j)
    decreases r
  {
    match r
    case Re_empty => case Re_character(_) => case Re_anchor(_) =>
    case Re_alt(r1, r2) => FilterAllCrPointwise(r1, X, Y, j); FilterAllCrPointwise(r2, AI.filter_all(r1, X), AI.filter_all(r1, Y), j);
    case Re_con(r1, r2) => FilterAllCrPointwise(r1, X, Y, j); FilterAllCrPointwise(r2, AI.filter_all(r1, X), AI.filter_all(r1, Y), j);
    case Re_quant(_, _, _, r1) => FilterAllCrPointwise(r1, X, Y, j);
    case Re_capture(cid, r1) =>
      if j == CP.start_reg(cid) {} else { SetIdxKeepsOther(X, CP.start_reg(cid), j); SetIdxKeepsOther(Y, CP.start_reg(cid), j); }
      FilterAllCrPointwise(r1, AI.set_idx(X, CP.start_reg(cid), -1), AI.set_idx(Y, CP.start_reg(cid), -1), j);
    case Re_lookaround(_, _, r1) => FilterAllCrPointwise(r1, X, Y, j);
  }

  /** `filter_capture` never reads capture values (only clocks), so its output
      at `j` is determined by the capture input at `j` alone. */
  lemma FilterCaptureCrPointwise(r: R.regex, X: seq<int>, Y: seq<int>, cc: seq<int>, lc: seq<int>, qc: seq<int>, M: int, j: int)
    requires NR.LookBehindFragmentRE(r)
    requires AI.get_idx(X, j) == AI.get_idx(Y, j)
    ensures AI.get_idx(AI.filter_capture(r, X, cc, lc, qc, M), j) == AI.get_idx(AI.filter_capture(r, Y, cc, lc, qc, M), j)
    decreases r
  {
    match r
    case Re_lookaround(lid, la, r1) =>
      NR.PlusIsLookBehindFragmentRE(r1);
      var lv := AI.get_idx(lc, lid);
      if lv < 0 || lv < M { FilterAllCrPointwise(r1, X, Y, j); }
      else { FilterCaptureCrPointwise(r1, X, Y, cc, lc, qc, -1, j); }
    case Re_empty => case Re_character(_) => case Re_anchor(_) =>
    case Re_alt(r1, r2) =>
      FilterCaptureCrPointwise(r1, X, Y, cc, lc, qc, M, j);
      FilterCaptureCrPointwise(r2, AI.filter_capture(r1, X, cc, lc, qc, M), AI.filter_capture(r1, Y, cc, lc, qc, M), cc, lc, qc, M, j);
    case Re_con(r1, r2) =>
      FilterCaptureCrPointwise(r1, X, Y, cc, lc, qc, M, j);
      FilterCaptureCrPointwise(r2, AI.filter_capture(r1, X, cc, lc, qc, M), AI.filter_capture(r1, Y, cc, lc, qc, M), cc, lc, qc, M, j);
    case Re_quant(nul, qid, q, r1) =>
      var qv := AI.get_idx(qc, qid);
      if qv < M { FilterAllCrPointwise(r1, X, Y, j); } else { FilterCaptureCrPointwise(r1, X, Y, cc, lc, qc, qv, j); }
    case Re_capture(cid, r1) =>
      var start := AI.get_idx(cc, CP.start_reg(cid));
      if start < 0 { FilterAllCrPointwise(r1, X, Y, j); }
      else if start < M {
        if j == CP.start_reg(cid) {} else { SetIdxKeepsOther(X, CP.start_reg(cid), j); SetIdxKeepsOther(Y, CP.start_reg(cid), j); }
        FilterAllCrPointwise(r1, AI.set_idx(X, CP.start_reg(cid), -1), AI.set_idx(Y, CP.start_reg(cid), -1), j);
      } else { FilterCaptureCrPointwise(r1, X, Y, cc, lc, qc, M, j); }
  }

  // Changing qc only at qid, where qid is NOT a quant id of the subtree, leaves
  // filter_capture unchanged (quant nodes read qc only at their own — other — ids).
  /** Changing `qc` only at `qid`, where `qid` is NOT a quant id of the subtree,
      leaves `filter_capture` unchanged (quant nodes read `qc` only at their own
      ids). */
  lemma FilterCaptureQcFrame(r: R.regex, cr: seq<int>, cc: seq<int>, lc: seq<int>, qc: seq<int>, qc': seq<int>, M: int, qid: nat, j: int)
    requires NR.LookBehindFragmentRE(r)
    requires qid !in QuantIds(r)
    requires forall q0: nat :: q0 in QuantIds(r) ==> AI.get_idx(qc, q0) == AI.get_idx(qc', q0)
    ensures AI.get_idx(AI.filter_capture(r, cr, cc, lc, qc, M), j) == AI.get_idx(AI.filter_capture(r, cr, cc, lc, qc', M), j)
    decreases r
  {
    match r
    case Re_lookaround(lid, la, r1) =>
      NR.PlusIsLookBehindFragmentRE(r1);
      var lv := AI.get_idx(lc, lid);
      // reset: both == filter_all(r1, cr)[j] (filter_all ignores qc); keep: recurse at -1.
      if lv < 0 || lv < M {} else { FilterCaptureQcFrame(r1, cr, cc, lc, qc, qc', -1, qid, j); }
    case Re_empty => case Re_character(_) => case Re_anchor(_) =>
    case Re_alt(r1, r2) =>
      FilterCaptureQcFrame(r1, cr, cc, lc, qc, qc', M, qid, j);
      forall j0 ensures AI.get_idx(AI.filter_capture(r1, cr, cc, lc, qc, M), j0) == AI.get_idx(AI.filter_capture(r1, cr, cc, lc, qc', M), j0)
      { FilterCaptureQcFrame(r1, cr, cc, lc, qc, qc', M, qid, j0); }
      var Y := AI.filter_capture(r1, cr, cc, lc, qc, M);
      var Y' := AI.filter_capture(r1, cr, cc, lc, qc', M);
      FilterCaptureQcFrame(r2, Y, cc, lc, qc, qc', M, qid, j);
      FilterCaptureCrPointwise(r2, Y', Y, cc, lc, qc', M, j);
    case Re_con(r1, r2) =>
      forall j0 ensures AI.get_idx(AI.filter_capture(r1, cr, cc, lc, qc, M), j0) == AI.get_idx(AI.filter_capture(r1, cr, cc, lc, qc', M), j0)
      { FilterCaptureQcFrame(r1, cr, cc, lc, qc, qc', M, qid, j0); }
      var Y := AI.filter_capture(r1, cr, cc, lc, qc, M);
      var Y' := AI.filter_capture(r1, cr, cc, lc, qc', M);
      FilterCaptureQcFrame(r2, Y, cc, lc, qc, qc', M, qid, j);
      FilterCaptureCrPointwise(r2, Y', Y, cc, lc, qc', M, j);
    case Re_quant(nul, qid0, q, r1) =>
      if qid0 >= 0 { assert (qid0 as nat) in QuantIds(r); }
      assert AI.get_idx(qc, qid0) == AI.get_idx(qc', qid0);   // qid0 ∈ QuantIds(r) (or <0 ⇒ both -1)
      var qv := AI.get_idx(qc, qid0);
      if qv < M {} else { FilterCaptureQcFrame(r1, cr, cc, lc, qc, qc', qv, qid, j); }
    case Re_capture(cid, r1) =>
      var start := AI.get_idx(cc, CP.start_reg(cid));
      if start < 0 { FilterCaptureQcFrame(r1, cr, cc, lc, qc, qc', M, qid, j); }
      else if start < M {}
      else { FilterCaptureQcFrame(r1, cr, cc, lc, qc, qc', M, qid, j); }
  }

  // filter_all drives every capture-start of the subtree negative (absent).
  /** `filter_all` drives every capture-start of the subtree negative (absent). */
  lemma FilterAllClearsStart(r: R.regex, Z: seq<int>, g: nat)
    requires CapUnique(r)
    requires g in CapIds(r)
    ensures AI.get_idx(AI.filter_all(r, Z), CP.start_reg(g)) < 0
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      if g in CapIds(r1) {
        FilterAllClearsStart(r1, Z, g);
        assert g !in CapIds(r2) by { if g in CapIds(r2) { assert g in CapIds(r1) * CapIds(r2); } }
        forall cid: nat | cid in CapIds(r2) ensures CP.start_reg(cid) != CP.start_reg(g) {}
        FilterAllKeepsNonStart(r2, AI.filter_all(r1, Z), CP.start_reg(g));
      } else { FilterAllClearsStart(r2, AI.filter_all(r1, Z), g); }
    case Re_con(r1, r2) =>
      if g in CapIds(r1) {
        FilterAllClearsStart(r1, Z, g);
        assert g !in CapIds(r2) by { if g in CapIds(r2) { assert g in CapIds(r1) * CapIds(r2); } }
        forall cid: nat | cid in CapIds(r2) ensures CP.start_reg(cid) != CP.start_reg(g) {}
        FilterAllKeepsNonStart(r2, AI.filter_all(r1, Z), CP.start_reg(g));
      } else { FilterAllClearsStart(r2, AI.filter_all(r1, Z), g); }
    case Re_quant(_, _, _, r1) => FilterAllClearsStart(r1, Z, g);
    case Re_capture(cid, r1) =>
      if cid == g {
        FilterAllKeepsNonStart(r1, AI.set_idx(Z, CP.start_reg(cid), -1), CP.start_reg(g));
      } else { FilterAllClearsStart(r1, AI.set_idx(Z, CP.start_reg(cid), -1), g); }
    case Re_lookaround(_, _, r1) => FilterAllClearsStart(r1, Z, g);
  }

  // ===========================================================================
  // FilterOpenFrame — the no-exposure discharge. Opening gid's start register
  // (present at cp with a fresh clock clk) perturbs filter_capture's output ONLY
  // at start_reg(gid): gid becomes cp, every other register is unchanged. The
  // subgroup-exposure that a naive open would cause is ruled out because gid's
  // body is all-stale relative to MxAtGid (the enclosing star's clock), so
  // filter_capture on the body degenerates to filter_all (FilterCaptureAllStale).
  // Stated relationally in (cr,cr') / (cc,cc') that agree off start_reg(gid).
  // ===========================================================================
  /** The no-exposure discharge: opening `gid`'s start register (present at `cp`
      with a fresh clock) perturbs `filter_capture`'s output ONLY at
      `start_reg(gid)` — `gid` becomes `cp`, every other register is unchanged.
      A naive open exposing `gid`'s subgroups is ruled out because its body is
      all-stale vs `MxAtGid`, so the body filter degenerates to `filter_all`. */
  lemma FilterOpenFrame(r: R.regex, cr: seq<int>, cr': seq<int>, cc: seq<int>, cc': seq<int>,
                        lc: seq<int>, qc: seq<int>, mx: int, gid: nat, cp: int, clk: int)
    requires NR.LookBehindFragmentRE(r)
    requires CapUnique(r)
    requires gid in CapIds(r)
    requires gid !in CapIdsInLooks(r)   // L3a: open frame is for outside-look gids
    requires cp >= 0 && clk >= 0
    requires clk >= MxAtGid(r, cc, qc, mx, gid)
    requires PathPresent(r, cc, qc, mx, gid)
    requires |cr| == |cr'|
    // gid's start register is UNSET or STALE (its clock is below the enclosing
    // star's stamp): first open of gid, or a star re-entry overwriting the
    // previous iteration's value. Either way the filter output at the start is
    // negative before the write.
    requires AI.get_idx(cc, CP.start_reg(gid)) < MxAtGid(r, cc, qc, mx, gid)
          || AI.get_idx(cc, CP.start_reg(gid)) < 0
    requires AI.get_idx(cr', CP.start_reg(gid)) == cp
    requires AI.get_idx(cc', CP.start_reg(gid)) == clk
    requires forall j :: j != CP.start_reg(gid) ==> AI.get_idx(cr', j) == AI.get_idx(cr, j)
    requires forall j :: j != CP.start_reg(gid) ==> AI.get_idx(cc', j) == AI.get_idx(cc, j)
    requires forall k :: AI.get_idx(cr, k) >= -1
    requires forall k :: AI.get_idx(cr', k) >= -1
    requires forall c: nat :: c in CapIds(r) && AI.get_idx(cc, CP.start_reg(c)) < 0 ==> AI.get_idx(cr, CP.start_reg(c)) < 0
    requires forall c: nat :: c in CapIds(r) && AI.get_idx(cc', CP.start_reg(c)) < 0 ==> AI.get_idx(cr', CP.start_reg(c)) < 0
    requires forall sg: nat :: sg in CapIds(BodyOf(r, gid))
                              ==> AI.get_idx(cc, CP.start_reg(sg)) < MxAtGid(r, cc, qc, mx, gid)
                                  || AI.get_idx(cc, CP.start_reg(sg)) < 0
    // L3a: every lookaround inside gid's body is stale at gid's birth stamp — the
    // body's looks haven't fired in this iteration, so a fresh open cannot keep
    // any inside-look captures (mirrors the sg capture-staleness above).
    requires LooksCapUnset(BodyOf(r, gid), cc)
    ensures AI.get_idx(AI.filter_capture(r, cr, cc, lc, qc, mx), CP.start_reg(gid)) < 0
    ensures AI.get_idx(AI.filter_capture(r, cr', cc', lc, qc, mx), CP.start_reg(gid)) == cp
    ensures forall j :: j != CP.start_reg(gid)
                        ==> AI.get_idx(AI.filter_capture(r, cr', cc', lc, qc, mx), j)
                            == AI.get_idx(AI.filter_capture(r, cr, cc, lc, qc, mx), j)
    decreases r
  {
    match r
    case Re_empty => case Re_character(_) => case Re_anchor(_) =>
    case Re_lookaround(_, _, r1) =>
      assert gid in CapIdsInLooks(r);   // == CapIds(r1) ∋ gid, contradicts the outside-look requires
      assert false;
    case Re_alt(r1, r2) =>
      var X := AI.filter_capture(r1, cr, cc, lc, qc, mx);
      var X' := AI.filter_capture(r1, cr', cc', lc, qc, mx);
      FilterCaptureLen(r1, cr, cc, lc, qc, mx); FilterCaptureLen(r1, cr', cc', lc, qc, mx);
      if gid in CapIds(r1) {
        assert MxAtGid(r, cc, qc, mx, gid) == MxAtGid(r1, cc, qc, mx, gid);
        assert BodyOf(r, gid) == BodyOf(r1, gid);
        FilterOpenFrame(r1, cr, cr', cc, cc', lc, qc, mx, gid, cp, clk);
        assert gid !in CapIds(r2) by { if gid in CapIds(r2) { assert gid in CapIds(r1) * CapIds(r2); } }
        FilterCaptureFrameAt(r2, X', X, cc', cc, lc, qc, mx, gid);
        FilterCaptureOutside(r2, X, cc, lc, qc, mx, gid);
        FilterCaptureOutside(r2, X', cc', lc, qc, mx, gid);
      } else {
        assert gid in CapIds(r2) && gid !in CapIds(r1);
        FilterCaptureFrameAt(r1, cr', cr, cc', cc, lc, qc, mx, gid);
        FilterCaptureOutside(r1, cr, cc, lc, qc, mx, gid);
        FilterCaptureOutside(r1, cr', cc', lc, qc, mx, gid);
        forall k ensures AI.get_idx(X, k) >= -1 { FilterCaptureGeqNeg1(r1, cr, cc, lc, qc, mx, k); }
        forall k ensures AI.get_idx(X', k) >= -1 { FilterCaptureGeqNeg1(r1, cr', cc', lc, qc, mx, k); }
        forall c: nat | c in CapIds(r2) && AI.get_idx(cc, CP.start_reg(c)) < 0
          ensures AI.get_idx(X, CP.start_reg(c)) < 0
        {
          assert c !in CapIds(r1) by { if c in CapIds(r1) { assert c in CapIds(r1) * CapIds(r2); } }
          FilterCaptureOutside(r1, cr, cc, lc, qc, mx, c);
        }
        forall c: nat | c in CapIds(r2) && AI.get_idx(cc', CP.start_reg(c)) < 0
          ensures AI.get_idx(X', CP.start_reg(c)) < 0
        {
          assert c !in CapIds(r1) by { if c in CapIds(r1) { assert c in CapIds(r1) * CapIds(r2); } }
          FilterCaptureOutside(r1, cr', cc', lc, qc, mx, c);
        }
        assert MxAtGid(r, cc, qc, mx, gid) == MxAtGid(r2, cc, qc, mx, gid);
        assert BodyOf(r, gid) == BodyOf(r2, gid);
        FilterOpenFrame(r2, X, X', cc, cc', lc, qc, mx, gid, cp, clk);
      }
    case Re_con(r1, r2) =>
      var X := AI.filter_capture(r1, cr, cc, lc, qc, mx);
      var X' := AI.filter_capture(r1, cr', cc', lc, qc, mx);
      FilterCaptureLen(r1, cr, cc, lc, qc, mx); FilterCaptureLen(r1, cr', cc', lc, qc, mx);
      if gid in CapIds(r1) {
        assert MxAtGid(r, cc, qc, mx, gid) == MxAtGid(r1, cc, qc, mx, gid);
        assert BodyOf(r, gid) == BodyOf(r1, gid);
        FilterOpenFrame(r1, cr, cr', cc, cc', lc, qc, mx, gid, cp, clk);
        assert gid !in CapIds(r2) by { if gid in CapIds(r2) { assert gid in CapIds(r1) * CapIds(r2); } }
        FilterCaptureFrameAt(r2, X', X, cc', cc, lc, qc, mx, gid);
        FilterCaptureOutside(r2, X, cc, lc, qc, mx, gid);
        FilterCaptureOutside(r2, X', cc', lc, qc, mx, gid);
      } else {
        assert gid in CapIds(r2) && gid !in CapIds(r1);
        FilterCaptureFrameAt(r1, cr', cr, cc', cc, lc, qc, mx, gid);
        FilterCaptureOutside(r1, cr, cc, lc, qc, mx, gid);
        FilterCaptureOutside(r1, cr', cc', lc, qc, mx, gid);
        forall k ensures AI.get_idx(X, k) >= -1 { FilterCaptureGeqNeg1(r1, cr, cc, lc, qc, mx, k); }
        forall k ensures AI.get_idx(X', k) >= -1 { FilterCaptureGeqNeg1(r1, cr', cc', lc, qc, mx, k); }
        forall c: nat | c in CapIds(r2) && AI.get_idx(cc, CP.start_reg(c)) < 0
          ensures AI.get_idx(X, CP.start_reg(c)) < 0
        {
          assert c !in CapIds(r1) by { if c in CapIds(r1) { assert c in CapIds(r1) * CapIds(r2); } }
          FilterCaptureOutside(r1, cr, cc, lc, qc, mx, c);
        }
        forall c: nat | c in CapIds(r2) && AI.get_idx(cc', CP.start_reg(c)) < 0
          ensures AI.get_idx(X', CP.start_reg(c)) < 0
        {
          assert c !in CapIds(r1) by { if c in CapIds(r1) { assert c in CapIds(r1) * CapIds(r2); } }
          FilterCaptureOutside(r1, cr', cc', lc, qc, mx, c);
        }
        assert MxAtGid(r, cc, qc, mx, gid) == MxAtGid(r2, cc, qc, mx, gid);
        assert BodyOf(r, gid) == BodyOf(r2, gid);
        FilterOpenFrame(r2, X, X', cc, cc', lc, qc, mx, gid, cp, clk);
      }
    case Re_quant(nul, qid, q, r1) =>
      var qv := AI.get_idx(qc, qid);
      assert qv >= mx;                                  // PathPresent
      assert MxAtGid(r, cc, qc, mx, gid) == MxAtGid(r1, cc, qc, qv, gid);
      assert BodyOf(r, gid) == BodyOf(r1, gid);
      FilterOpenFrame(r1, cr, cr', cc, cc', lc, qc, qv, gid, cp, clk);
    case Re_capture(cid, r1) =>
      if cid == gid {
        assert gid !in CapIds(r1);                      // CapUnique
        assert MxAtGid(r, cc, qc, mx, gid) == mx;
        var sclk := AI.get_idx(cc, CP.start_reg(cid));
        assert sclk < mx || sclk < 0;                   // unset or stale
        // f'-side (after the write): present branch, since cc'[start] == clk >= mx.
        assert AI.get_idx(cc', CP.start_reg(cid)) == clk;
        FilterCaptureOutside(r1, cr', cc', lc, qc, mx, gid);  // f'[start_reg(gid)] == cp
        assert BodyOf(r, gid) == r1;
        forall cidx: nat | cidx in CapIds(r1)
          ensures AI.get_idx(cc', CP.start_reg(cidx)) < mx || AI.get_idx(cc', CP.start_reg(cidx)) < 0
        {
          assert cidx != gid;
          assert CP.start_reg(cidx) != CP.start_reg(gid);
          assert AI.get_idx(cc', CP.start_reg(cidx)) == AI.get_idx(cc, CP.start_reg(cidx));
        }
        assert BodyOf(r, gid) == r1 && MxAtGid(r, cc, qc, mx, gid) == mx;
        // inside-look caps of the body are unset in cc (requires) and unchanged by
        // the open write (they differ from gid's start), so unset in cc' too.
        assert LooksCapUnset(r1, cc') by {
          CapIdsSplit(r1);
          forall c: nat | c in CapIdsInLooks(r1) ensures AI.get_idx(cc', CP.start_reg(c)) < 0 {
            assert c != gid && CP.start_reg(c) != CP.start_reg(gid);
            assert AI.get_idx(cc', CP.start_reg(c)) == AI.get_idx(cc, CP.start_reg(c));
          }
        }
        FilterCaptureAllStale(r1, cr', cc', lc, qc, mx);   // filter_capture(r1,cr',cc',mx) == filter_all(r1,cr')
        // f-side (before the write): two subcases, both land in a filter_all branch
        // whose input at start_reg(gid) is negative.
        if sclk < 0 {
          // UNSET: filter_all(r1, cr); value < 0 by clock/value consistency at gid.
          assert AI.get_idx(cr, CP.start_reg(gid)) < 0;   // consistency hypothesis, c := gid
          FilterAllOutside(r1, cr, gid);                  // f[start_reg(gid)] == cr[start_reg(gid)] < 0
          FilterAllFrameAt(r1, cr', cr, gid);             // filter_all(r1,cr'), filter_all(r1,cr) agree off gid
        } else {
          // STALE (0 <= sclk < mx): filter_all(r1, set_idx(cr, start_reg(gid), -1));
          // the filter itself clears the start.
          var cr2 := AI.set_idx(cr, CP.start_reg(cid), -1);
          assert AI.get_idx(cr2, CP.start_reg(gid)) <= -1;  // cleared (or out of range: get_idx gives -1)
          FilterAllOutside(r1, cr2, gid);                   // f[start_reg(gid)] == cr2[start_reg(gid)] < 0
          assert |cr2| == |cr'|;                            // set_idx preserves length
          forall j | j != CP.start_reg(gid)
            ensures AI.get_idx(cr', j) == AI.get_idx(cr2, j)
          {
            SetIdxKeepsOther(cr, CP.start_reg(cid), j);     // cr2[j] == cr[j] == cr'[j]
          }
          FilterAllFrameAt(r1, cr', cr2, gid);              // agree off start_reg(gid)
        }
      } else {
        assert gid in CapIds(r1);
        assert AI.get_idx(cc, CP.start_reg(cid)) >= mx && AI.get_idx(cc, CP.start_reg(cid)) >= 0;  // PathPresent
        assert AI.get_idx(cc', CP.start_reg(cid)) == AI.get_idx(cc, CP.start_reg(cid));   // cid != gid
        assert MxAtGid(r, cc, qc, mx, gid) == MxAtGid(r1, cc, qc, mx, gid);
        assert BodyOf(r, gid) == BodyOf(r1, gid);
        FilterOpenFrame(r1, cr, cr', cc, cc', lc, qc, mx, gid, cp, clk);
      }
  }

  // Base case (needed by InitialPikeInvRE): freshly-initialized registers denote
  // the empty GroupMap — the initial capture array is all -1, and filter_reset
  // keeps it so, hence no group is present.
  /** Base case: freshly-initialized (all `-1`) registers denote the empty
      `GroupMap` under `GmOf` — no group is present. */
  lemma GmOfInit(ast: R.regex, ncap: int, nlook: int, nquant: int)
    ensures GmOf(ast, AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant)) == LG.Empty
  {
    var caps := AReg.init_regs(ncap);
    var look := AReg.init_regs(nlook);
    var quant := AReg.init_regs(nquant);
    var filtered := AI.filter_reset(ast, caps, look, quant, -1);
    var (cr, cc) := AReg.as_arrays(caps);
    var (_, lc) := AReg.as_arrays(look);
    var (_, qc) := AReg.as_arrays(quant);
    assert cr == AReg.init_regs(ncap).a_cp;
    assert forall i :: AI.get_idx(cr, i) < 0;   // init a_cp is seq(_, -1)
    forall gid: nat | 0 <= gid < |filtered|
      ensures AI.get_idx(filtered, CP.start_reg(gid)) < 0
    {
      FilterCaptureNeg(ast, cr, cc, lc, qc, -1, CP.start_reg(gid));
    }
    assert GmOf(ast, caps, look, quant).Keys == {};
  }

  // ===========================================================================
  // GmOfLive — the intermediate denotation used by the simulation invariant.
  // Same as GmOf on the group START (reset-resolved value), but a group's END
  // counts ONLY if its end clock is at least its start clock (i.e. the group was
  // genuinely closed after being (re)opened this iteration). This gives
  // Range(start, None) for a mid-search OPEN group whose end register still holds
  // a prior star iteration's stale value — matching the tree machine's GMOpen.
  // On a COMPLETED (properly closed) match, GmOfLive == GmOf (GmOfLiveEqGmOf), so
  // the final capture-array answer still goes through GmOf/GmOfCapArrayBridge.
  // ===========================================================================

  /** `gid`'s `Range` under the LIVE reading: same start as `RangeFromArr`, but
      the end counts only if its clock is `>=` the start clock (the group was
      genuinely closed this iteration) — else the group reads as open. */
  ghost function LiveRange(f: seq<int>, cc: seq<int>, gid: nat): LG.Range
    requires AI.get_idx(f, CP.start_reg(gid)) >= 0
  {
    var endval := AI.get_idx(f, CP.end_reg(gid));
    var startclk := AI.get_idx(cc, CP.start_reg(gid));
    var endclk := AI.get_idx(cc, CP.end_reg(gid));
    LG.Range(AI.get_idx(f, CP.start_reg(gid)) as nat,
             if endval >= 0 && endclk >= startclk then Some(endval as nat) else None)
  }

  /** The intermediate denotation used by the simulation invariant: like `GmOf`
      on group starts, but a group's end counts only if genuinely closed this
      iteration (`LiveRange`), giving `Range(start, None)` for a mid-search OPEN
      group — matching the tree machine's `GMOpen`. On a completed match it
      coincides with `GmOf` (`GmOfLiveEqGmOf`). */
  ghost function GmOfLive(ast: R.regex, caps: AReg.Regs, look: AReg.Regs, quant: AReg.Regs): LG.GroupMap
  {
    var f := AI.filter_reset(ast, caps, look, quant, -1);
    var cc := AReg.as_arrays(caps).1;
    map gid: nat | 0 <= gid < |f| && AI.get_idx(f, CP.start_reg(gid)) >= 0
      :: LiveRange(f, cc, gid)
  }

  // GmOfLive has the same DOMAIN as GmOf (both present iff start >= 0); at init
  // that domain is empty.
  /** Freshly-initialized registers denote the empty `GroupMap` under `GmOfLive`
      too (its domain is empty at init). */
  lemma GmOfLiveInit(ast: R.regex, ncap: int, nlook: int, nquant: int)
    ensures GmOfLive(ast, AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant)) == LG.Empty
  {
    var caps := AReg.init_regs(ncap);
    var look := AReg.init_regs(nlook);
    var quant := AReg.init_regs(nquant);
    var filtered := AI.filter_reset(ast, caps, look, quant, -1);
    var (cr, cc) := AReg.as_arrays(caps);
    var (_, lc) := AReg.as_arrays(look);
    var (_, qc) := AReg.as_arrays(quant);
    assert cr == AReg.init_regs(ncap).a_cp;
    assert forall i :: AI.get_idx(cr, i) < 0;
    forall gid: nat | 0 <= gid < |filtered|
      ensures AI.get_idx(filtered, CP.start_reg(gid)) < 0
    {
      FilterCaptureNeg(ast, cr, cc, lc, qc, -1, CP.start_reg(gid));
    }
    assert GmOfLive(ast, caps, look, quant).Keys == {};
  }

  // ===========================================================================
  // The look bank does not steer the denotation (L1: capture-free lookaround
  // bodies). filter_capture consults the look CLOCKS only at a Re_lookaround
  // node, where it either filter_alls the body or recurses into it — and for a
  // capture-free body both alternatives are the identity on the capture
  // registers. So the engine's `look_regs[lid] := cp` write at a passing
  // CheckOracle leaves `GmOfLive` (hence `ThreadTracksGm`) untouched. This is
  // the L1 shape of the campaign's "GmOfLive look-clock branch"; at L3
  // (captures INSIDE lookarounds) it stops being the identity.
  // ===========================================================================

  // ==========================================================================
  // Quant clocks INSIDE lookaround bodies are invisible to the filter.
  //
  // The lookaround CAPTURE pass replays the body's bytecode and keeps the
  // resulting quant bank, so the clocks of the body's own quantifiers change.
  // They cannot move the answer: `filter_capture` reaches a lookaround node and
  // stops there (its body is capture-free, so both branches are the identity),
  // which means only the quant ids OUTSIDE lookaround bodies are ever read.
  // ==========================================================================

  // ==========================================================================
  // `reverse_regex` and the fragment. A lookbehind's CAPTURE regex is
  // `reverse_regex(body)` (Compiler.capture_regex), so everything the capture
  // pass is asked about the body has to survive the reversal — which it does,
  // since reversing only swaps concatenation order and rebuilds every node
  // with the same ids.
  // ==========================================================================

  /** Reversal keeps a regex capture-free. */
  lemma ReverseCaptureFree(r: R.regex)
    requires NR.CaptureFreeRE(r)
    ensures NR.CaptureFreeRE(R.reverse_regex(r))
    decreases r
  {
    match r
    case Re_alt(r1, r2) => ReverseCaptureFree(r1); ReverseCaptureFree(r2);
    case Re_con(r1, r2) => ReverseCaptureFree(r1); ReverseCaptureFree(r2);
    case Re_quant(_, _, _, r1) => ReverseCaptureFree(r1);
    case Re_lookaround(_, _, r1) => ReverseCaptureFree(r1);
    case _ =>
  }

  /** Reversal keeps a regex lookaround-free. */
  lemma ReverseLookFree(r: R.regex)
    requires NR.LookFreeRE(r)
    ensures NR.LookFreeRE(R.reverse_regex(r))
    decreases r
  {
    match r
    case Re_alt(r1, r2) => ReverseLookFree(r1); ReverseLookFree(r2);
    case Re_con(r1, r2) => ReverseLookFree(r1); ReverseLookFree(r2);
    case Re_quant(_, _, _, r1) => ReverseLookFree(r1);
    case Re_capture(_, r1) => ReverseLookFree(r1);
    case _ =>
  }

  /** Reversal preserves the quant ids (every node is rebuilt with its own). */
  lemma ReverseQuantIds(r: R.regex)
    ensures QuantIds(R.reverse_regex(r)) == QuantIds(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => ReverseQuantIds(r1); ReverseQuantIds(r2);
    case Re_con(r1, r2) => ReverseQuantIds(r1); ReverseQuantIds(r2);
    case Re_quant(_, _, _, r1) => ReverseQuantIds(r1);
    case Re_capture(_, r1) => ReverseQuantIds(r1);
    case Re_lookaround(_, _, r1) => ReverseQuantIds(r1);
    case _ =>
  }

  /** Reversal preserves quant-id uniqueness. */
  lemma ReverseQuantUnique(r: R.regex)
    requires QuantUnique(r)
    ensures QuantUnique(R.reverse_regex(r))
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      ReverseQuantUnique(r1); ReverseQuantUnique(r2);
      ReverseQuantIds(r1); ReverseQuantIds(r2);
    case Re_con(r1, r2) =>
      ReverseQuantUnique(r1); ReverseQuantUnique(r2);
      ReverseQuantIds(r1); ReverseQuantIds(r2);
    case Re_quant(_, _, _, r1) => ReverseQuantUnique(r1); ReverseQuantIds(r1);
    case Re_capture(_, r1) => ReverseQuantUnique(r1);
    case Re_lookaround(_, _, r1) => ReverseQuantUnique(r1);
    case _ =>
  }

  /** Reversal keeps a regex in the plus fragment (the quantifier shapes and
      the nullability side conditions are node-local, and `nullable` itself is
      reversal-invariant). */
  lemma ReversePlusFragment(r: R.regex)
    requires NR.PlusFragmentRE(r)
    ensures NR.PlusFragmentRE(R.reverse_regex(r))
    decreases r
  {
    ReverseNullable(r);
    match r
    case Re_alt(r1, r2) => ReversePlusFragment(r1); ReversePlusFragment(r2);
    case Re_con(r1, r2) => ReversePlusFragment(r1); ReversePlusFragment(r2);
    case Re_quant(nul, qid, q, r1) => ReversePlusFragment(r1); ReverseNullable(r1);
    case Re_capture(_, r1) => ReversePlusFragment(r1);
    case _ =>
  }

  /** Nullability is reversal-invariant. */
  lemma ReverseNullable(r: R.regex)
    ensures R.nullable(R.reverse_regex(r)) == R.nullable(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => ReverseNullable(r1); ReverseNullable(r2);
    case Re_con(r1, r2) => ReverseNullable(r1); ReverseNullable(r2);
    case Re_quant(_, _, _, r1) => ReverseNullable(r1);
    case Re_capture(_, r1) => ReverseNullable(r1);
    case Re_lookaround(_, _, r1) => ReverseNullable(r1);
    case _ =>
  }

  /** The composite the capture pass wants: the capture regex of an L1
      lookbehind is itself an L1 body — capture-free, look-free, plus
      fragment (hence lookbehind-fragment), with the same quant ids. */
  lemma CaptureRegexFragment(la: R.lookaround, body: R.regex)
    requires NR.CaptureFreeRE(body) && NR.LookFreeRE(body) && NR.PlusFragmentRE(body)
    ensures var cr := CP.capture_regex(la, body);
      NR.CaptureFreeRE(cr) && NR.LookFreeRE(cr) && NR.PlusFragmentRE(cr)
      && NR.LookBehindFragmentRE(cr)
      && QuantIds(cr) <= QuantIds(body)
  {
    if la.Lookahead? {
      // a lookAHEAD's capture regex is the body itself -- no reversal
      assert CP.capture_regex(la, body) == body;
      NR.PlusIsLookBehindFragmentRE(body);
    }
    if la.Lookbehind? {
      ReverseCaptureFree(body);
      ReverseLookFree(body);
      ReversePlusFragment(body);
      ReverseQuantIds(body);
      NR.PlusIsLookBehindFragmentRE(R.reverse_regex(body));
    } else {
      // NegLookbehind: the capture regex is `Re_empty`
    }
  }

  // ==========================================================================
  // Which quant ids a compiled block can write. Together with ClockMono's
  // quant frame this pins the lookaround capture pass: its replay writes only
  // the BODY's ids, and those are exactly the ones the filter never reads.
  // ==========================================================================

  /** Every `SetQuantToClock` inside a compiled block targets one of that
      regex's own quant ids. */
  lemma QuantWriteIdsRE(re: R.regex, code: RB.code, start: nat, endl: nat, pc: nat)
    requires NR.LookBehindFragmentRE(re) && QuantUnique(re)
    requires NR.NfaRepRE(re, code, start, endl)
    requires start <= pc < endl
    ensures NR.GetPcRE(code, pc).Some? && NR.GetPcRE(code, pc).value.SetQuantToClock? ==>
      var q := NR.GetPcRE(code, pc).value.sq;
      q >= 0 && (q as nat) in QuantIds(re)
    decreases CP.rsize(re), 1
  {
    match re
    case Re_empty =>
    case Re_character(_) =>
    case Re_anchor(_) =>
    case Re_lookaround(_, _, _) =>
    case Re_alt(r1, r2) =>
      var e1: nat :| NR.GetPcRE(code, start) == Some(RB.Fork(start + 1, e1 + 1))
        && NR.NfaRepRE(r1, code, start + 1, e1)
        && NR.GetPcRE(code, e1) == Some(RB.Jmp(endl))
        && NR.NfaRepRE(r2, code, e1 + 1, endl);
      NR.NfaRepIncrRE(r1, code, start + 1, e1);
      NR.NfaRepIncrRE(r2, code, e1 + 1, endl);
      if pc == start {
      } else if pc < e1 {
        QuantWriteIdsRE(r1, code, start + 1, e1, pc);
      } else if pc == e1 {
      } else {
        QuantWriteIdsRE(r2, code, e1 + 1, endl, pc);
      }
    case Re_con(r1, r2) =>
      var e1: nat :| NR.NfaRepRE(r1, code, start, e1) && NR.NfaRepRE(r2, code, e1, endl);
      NR.NfaRepIncrRE(r1, code, start, e1);
      NR.NfaRepIncrRE(r2, code, e1, endl);
      if pc < e1 {
        QuantWriteIdsRE(r1, code, start, e1, pc);
      } else {
        QuantWriteIdsRE(r2, code, e1, endl, pc);
      }
    case Re_capture(cid, r1) =>
      var e1: nat :| NR.GetPcRE(code, start) == Some(RB.SetRegisterToCP(CP.start_reg(cid)))
        && NR.NfaRepRE(r1, code, start + 1, e1)
        && NR.GetPcRE(code, e1) == Some(RB.SetRegisterToCP(CP.end_reg(cid)))
        && endl == e1 + 1;
      NR.NfaRepIncrRE(r1, code, start + 1, e1);
      if pc == start {
      } else if pc < e1 {
        QuantWriteIdsRE(r1, code, start + 1, e1, pc);
      } else {
      }
    case Re_quant(nul, qid, q, r1) =>
      if q.min == 0 && q.max == None {
        var e1: nat :| NR.GetPcRE(code, start) == Some(if q.greedy then RB.Fork(start + 1, e1 + 2) else RB.Fork(e1 + 2, start + 1))
          && NR.GetPcRE(code, start + 1) == Some(RB.SetQuantToClock(qid, false))
          && NR.GetPcRE(code, start + 2) == Some(RB.BeginLoop)
          && NR.NfaRepRE(r1, code, start + 3, e1)
          && NR.GetPcRE(code, e1) == Some(RB.EndLoop)
          && NR.GetPcRE(code, e1 + 1) == Some(RB.Jmp(start))
          && endl == e1 + 2;
        NR.NfaRepIncrRE(r1, code, start + 3, e1);
        if pc <= start + 2 {
        } else if pc < e1 {
          QuantWriteIdsRE(r1, code, start + 3, e1, pc);
        } else {
        }
      } else if q.max.Some? {
        var em := NR.NfaRepREQuantInv(nul, qid, q, r1, code, start, endl);
        NR.NfaRepIncrMinRE(q.min as nat, qid, r1, code, start, em);
        NR.NfaRepIncrOptRE((q.max.value - q.min) as nat, q.greedy, qid, r1, code, em, endl);
        if pc < em {
          QuantWriteIdsMinRE(q.min as nat, qid, r1, code, start, em, pc);
        } else {
          QuantWriteIdsOptRE((q.max.value - q.min) as nat, q.greedy, qid, r1, code, em, endl, pc);
        }
      } else {
        var em, e1 := NR.NfaRepREPlusInv(nul, qid, q, r1, code, start, endl);
        NR.NfaRepIncrMinRE((q.min - 1) as nat, qid, r1, code, start, em);
        NR.NfaRepIncrRE(r1, code, em + 1, e1);
        if pc < em {
          QuantWriteIdsMinRE((q.min - 1) as nat, qid, r1, code, start, em, pc);
        } else if pc == em {
        } else if pc < e1 {
          QuantWriteIdsRE(r1, code, em + 1, e1, pc);
        } else {
        }
      }
  }

  /** `QuantWriteIdsRE` for the forced-copy chain. */
  lemma QuantWriteIdsMinRE(k: nat, qid: R.quantid, r1: R.regex, code: RB.code, start: nat, endl: nat, pc: nat)
    requires NR.LookBehindFragmentRE(r1) && QuantUnique(r1)
    requires NR.NfaRepMinRE(k, qid, r1, code, start, endl)
    requires start <= pc < endl
    ensures NR.GetPcRE(code, pc).Some? && NR.GetPcRE(code, pc).value.SetQuantToClock? ==>
      var q := NR.GetPcRE(code, pc).value.sq;
      q == qid || (q >= 0 && (q as nat) in QuantIds(r1))
    decreases CP.rsize(r1), k + 2
  {
    if k == 0 { return; }
    var e1: nat :| NR.GetPcRE(code, start) == Some(RB.SetQuantToClock(qid, false))
      && NR.NfaRepRE(r1, code, start + 1, e1)
      && NR.NfaRepMinRE(k - 1, qid, r1, code, e1, endl);
    NR.NfaRepIncrRE(r1, code, start + 1, e1);
    NR.NfaRepIncrMinRE(k - 1, qid, r1, code, e1, endl);
    if pc == start {
    } else if pc < e1 {
      QuantWriteIdsRE(r1, code, start + 1, e1, pc);
    } else {
      QuantWriteIdsMinRE(k - 1, qid, r1, code, e1, endl, pc);
    }
  }

  /** `QuantWriteIdsRE` for the optional-layer chain. */
  lemma QuantWriteIdsOptRE(k: nat, greedy: bool, qid: R.quantid, r1: R.regex, code: RB.code, start: nat, endl: nat, pc: nat)
    requires NR.LookBehindFragmentRE(r1) && QuantUnique(r1)
    requires NR.NfaRepOptRE(k, greedy, qid, r1, code, start, endl)
    requires start <= pc < endl
    ensures NR.GetPcRE(code, pc).Some? && NR.GetPcRE(code, pc).value.SetQuantToClock? ==>
      var q := NR.GetPcRE(code, pc).value.sq;
      q == qid || (q >= 0 && (q as nat) in QuantIds(r1))
    decreases CP.rsize(r1), k + 2
  {
    if k == 0 { return; }
    var e1: nat :| NR.GetPcRE(code, start) == Some(if greedy then RB.Fork(start + 1, endl) else RB.Fork(endl, start + 1))
      && NR.GetPcRE(code, start + 1) == Some(RB.SetQuantToClock(qid, false))
      && NR.GetPcRE(code, start + 2) == Some(RB.BeginLoop)
      && NR.NfaRepRE(r1, code, start + 3, e1)
      && NR.GetPcRE(code, e1) == Some(RB.EndLoop)
      && NR.NfaRepOptRE(k - 1, greedy, qid, r1, code, e1 + 1, endl);
    NR.NfaRepIncrRE(r1, code, start + 3, e1);
    NR.NfaRepIncrOptRE(k - 1, greedy, qid, r1, code, e1 + 1, endl);
    if pc <= start + 2 {
    } else if pc < e1 {
      QuantWriteIdsRE(r1, code, start + 3, e1, pc);
    } else if pc == e1 {
    } else {
      QuantWriteIdsOptRE(k - 1, greedy, qid, r1, code, e1 + 1, endl, pc);
    }
  }

  // ==========================================================================
  // The capture-write CLASSIFICATION (L3a): the compiled code of a capturing
  // body writes capture registers only for the body's OWN group ids. Paired
  // with CM.FFindMatchCapWriteFrame, this pins FLookLoop's capture replay: it
  // touches only CaptureRegs(body), disjoint from the outer captures the main
  // filter reads. Mirror of QuantWriteIdsRE; here Re_capture is the write case.
  // ==========================================================================

  /** The capture REGISTER ids (start/end) of `re`'s own groups. */
  ghost function CaptureRegs(re: R.regex): set<int> {
    (set cid | cid in CapIds(re) :: CP.start_reg(cid))
    + (set cid | cid in CapIds(re) :: CP.end_reg(cid))
  }

  /** `CaptureRegs` is monotone in `CapIds`. */
  lemma CaptureRegsMono(sub: R.regex, re: R.regex)
    requires CapIds(sub) <= CapIds(re)
    ensures CaptureRegs(sub) <= CaptureRegs(re)
  {
    forall k | k in CaptureRegs(sub) ensures k in CaptureRegs(re) {
      if k in (set cid | cid in CapIds(sub) :: CP.start_reg(cid)) {
        var cid :| cid in CapIds(sub) && CP.start_reg(cid) == k;
      } else {
        var cid :| cid in CapIds(sub) && CP.end_reg(cid) == k;
      }
    }
  }

  /** The capture registers of an arbitrary SET of group ids (not just a
      regex's `CapIds`) -- lets us name `CaptureRegs(CapIdsInLooks(re))` etc. */
  ghost function CaptureRegsSet(ids: set<nat>): set<int> {
    (set cid | cid in ids :: CP.start_reg(cid)) + (set cid | cid in ids :: CP.end_reg(cid))
  }

  lemma CaptureRegsIsSet(re: R.regex)
    ensures CaptureRegs(re) == CaptureRegsSet(CapIds(re))
  {}

  lemma CaptureRegsSetMono(a: set<nat>, b: set<nat>)
    requires a <= b
    ensures CaptureRegsSet(a) <= CaptureRegsSet(b)
  {
    forall k | k in CaptureRegsSet(a) ensures k in CaptureRegsSet(b) {
      if k in (set cid | cid in a :: CP.start_reg(cid)) {
        var cid :| cid in a && CP.start_reg(cid) == k;
      } else {
        var cid :| cid in a && CP.end_reg(cid) == k;
      }
    }
  }

  /** Disjoint id sets give disjoint register sets (parity + injectivity). */
  lemma CaptureRegsSetDisjoint(a: set<nat>, b: set<nat>)
    requires a * b == {}
    ensures CaptureRegsSet(a) * CaptureRegsSet(b) == {}
  {
    forall k | k in CaptureRegsSet(a) ensures k !in CaptureRegsSet(b) {
      var ca :| ca in a && (k == CP.start_reg(ca) || k == CP.end_reg(ca));
      if k in CaptureRegsSet(b) {
        var cb :| cb in b && (k == CP.start_reg(cb) || k == CP.end_reg(cb));
        assert CP.start_reg(ca) == 2 * ca && CP.end_reg(ca) == 2 * ca + 1;
        assert CP.start_reg(cb) == 2 * cb && CP.end_reg(cb) == 2 * cb + 1;
        assert ca == cb;
        assert ca in a * b;
      }
    }
  }

  /** Every `SetRegisterToCP` inside a compiled block targets one of that
      regex's own capture registers. */
  lemma CaptureWriteIdsRE(re: R.regex, code: RB.code, start: nat, endl: nat, pc: nat)
    requires NR.LookBehindFragmentRE(re) && CapUnique(re)
    requires NR.NfaRepRE(re, code, start, endl)
    requires start <= pc < endl
    ensures NR.GetPcRE(code, pc).Some? && NR.GetPcRE(code, pc).value.SetRegisterToCP? ==>
      NR.GetPcRE(code, pc).value.reg in CaptureRegs(re)
    decreases CP.rsize(re), 1
  {
    match re
    case Re_empty =>
    case Re_character(_) =>
    case Re_anchor(_) =>
    case Re_lookaround(_, _, _) =>
    case Re_alt(r1, r2) =>
      var e1: nat :| NR.GetPcRE(code, start) == Some(RB.Fork(start + 1, e1 + 1))
        && NR.NfaRepRE(r1, code, start + 1, e1)
        && NR.GetPcRE(code, e1) == Some(RB.Jmp(endl))
        && NR.NfaRepRE(r2, code, e1 + 1, endl);
      NR.NfaRepIncrRE(r1, code, start + 1, e1);
      NR.NfaRepIncrRE(r2, code, e1 + 1, endl);
      if pc == start {
      } else if pc < e1 {
        CaptureWriteIdsRE(r1, code, start + 1, e1, pc);
        CaptureRegsMono(r1, re);
      } else if pc == e1 {
      } else {
        CaptureWriteIdsRE(r2, code, e1 + 1, endl, pc);
        CaptureRegsMono(r2, re);
      }
    case Re_con(r1, r2) =>
      var e1: nat :| NR.NfaRepRE(r1, code, start, e1) && NR.NfaRepRE(r2, code, e1, endl);
      NR.NfaRepIncrRE(r1, code, start, e1);
      NR.NfaRepIncrRE(r2, code, e1, endl);
      if pc < e1 {
        CaptureWriteIdsRE(r1, code, start, e1, pc);
        CaptureRegsMono(r1, re);
      } else {
        CaptureWriteIdsRE(r2, code, e1, endl, pc);
        CaptureRegsMono(r2, re);
      }
    case Re_capture(cid, r1) =>
      var e1: nat :| NR.GetPcRE(code, start) == Some(RB.SetRegisterToCP(CP.start_reg(cid)))
        && NR.NfaRepRE(r1, code, start + 1, e1)
        && NR.GetPcRE(code, e1) == Some(RB.SetRegisterToCP(CP.end_reg(cid)))
        && endl == e1 + 1;
      NR.NfaRepIncrRE(r1, code, start + 1, e1);
      assert cid >= 0 && (cid as nat) in CapIds(re);   // CapUnique
      if pc == start {
        assert CP.start_reg(cid) in CaptureRegs(re);
      } else if pc < e1 {
        CaptureWriteIdsRE(r1, code, start + 1, e1, pc);
        CaptureRegsMono(r1, re);
      } else {
        assert CP.end_reg(cid) in CaptureRegs(re);
      }
    case Re_quant(nul, qid, q, r1) =>
      if q.min == 0 && q.max == None {
        var e1: nat :| NR.GetPcRE(code, start) == Some(if q.greedy then RB.Fork(start + 1, e1 + 2) else RB.Fork(e1 + 2, start + 1))
          && NR.GetPcRE(code, start + 1) == Some(RB.SetQuantToClock(qid, false))
          && NR.GetPcRE(code, start + 2) == Some(RB.BeginLoop)
          && NR.NfaRepRE(r1, code, start + 3, e1)
          && NR.GetPcRE(code, e1) == Some(RB.EndLoop)
          && NR.GetPcRE(code, e1 + 1) == Some(RB.Jmp(start))
          && endl == e1 + 2;
        NR.NfaRepIncrRE(r1, code, start + 3, e1);
        if pc <= start + 2 {
        } else if pc < e1 {
          CaptureWriteIdsRE(r1, code, start + 3, e1, pc);
        } else {
        }
      } else if q.max.Some? {
        var em := NR.NfaRepREQuantInv(nul, qid, q, r1, code, start, endl);
        NR.NfaRepIncrMinRE(q.min as nat, qid, r1, code, start, em);
        NR.NfaRepIncrOptRE((q.max.value - q.min) as nat, q.greedy, qid, r1, code, em, endl);
        if pc < em {
          CaptureWriteIdsMinRE(q.min as nat, qid, r1, code, start, em, pc);
        } else {
          CaptureWriteIdsOptRE((q.max.value - q.min) as nat, q.greedy, qid, r1, code, em, endl, pc);
        }
      } else {
        var em, e1 := NR.NfaRepREPlusInv(nul, qid, q, r1, code, start, endl);
        NR.NfaRepIncrMinRE((q.min - 1) as nat, qid, r1, code, start, em);
        NR.NfaRepIncrRE(r1, code, em + 1, e1);
        if pc < em {
          CaptureWriteIdsMinRE((q.min - 1) as nat, qid, r1, code, start, em, pc);
        } else if pc == em {
        } else if pc < e1 {
          CaptureWriteIdsRE(r1, code, em + 1, e1, pc);
        } else {
        }
      }
  }

  /** `CaptureWriteIdsRE` for the forced-copy chain (the chain adds only
      SetQuantToClock, never SetRegisterToCP, so writes come from the body). */
  lemma CaptureWriteIdsMinRE(k: nat, qid: R.quantid, r1: R.regex, code: RB.code, start: nat, endl: nat, pc: nat)
    requires NR.LookBehindFragmentRE(r1) && CapUnique(r1)
    requires NR.NfaRepMinRE(k, qid, r1, code, start, endl)
    requires start <= pc < endl
    ensures NR.GetPcRE(code, pc).Some? && NR.GetPcRE(code, pc).value.SetRegisterToCP? ==>
      NR.GetPcRE(code, pc).value.reg in CaptureRegs(r1)
    decreases CP.rsize(r1), k + 2
  {
    if k == 0 { return; }
    var e1: nat :| NR.GetPcRE(code, start) == Some(RB.SetQuantToClock(qid, false))
      && NR.NfaRepRE(r1, code, start + 1, e1)
      && NR.NfaRepMinRE(k - 1, qid, r1, code, e1, endl);
    NR.NfaRepIncrRE(r1, code, start + 1, e1);
    NR.NfaRepIncrMinRE(k - 1, qid, r1, code, e1, endl);
    if pc == start {
    } else if pc < e1 {
      CaptureWriteIdsRE(r1, code, start + 1, e1, pc);
    } else {
      CaptureWriteIdsMinRE(k - 1, qid, r1, code, e1, endl, pc);
    }
  }

  /** `CaptureWriteIdsRE` for the optional-layer chain. */
  lemma CaptureWriteIdsOptRE(k: nat, greedy: bool, qid: R.quantid, r1: R.regex, code: RB.code, start: nat, endl: nat, pc: nat)
    requires NR.LookBehindFragmentRE(r1) && CapUnique(r1)
    requires NR.NfaRepOptRE(k, greedy, qid, r1, code, start, endl)
    requires start <= pc < endl
    ensures NR.GetPcRE(code, pc).Some? && NR.GetPcRE(code, pc).value.SetRegisterToCP? ==>
      NR.GetPcRE(code, pc).value.reg in CaptureRegs(r1)
    decreases CP.rsize(r1), k + 2
  {
    if k == 0 { return; }
    var e1: nat :| NR.GetPcRE(code, start) == Some(if greedy then RB.Fork(start + 1, endl) else RB.Fork(endl, start + 1))
      && NR.GetPcRE(code, start + 1) == Some(RB.SetQuantToClock(qid, false))
      && NR.GetPcRE(code, start + 2) == Some(RB.BeginLoop)
      && NR.NfaRepRE(r1, code, start + 3, e1)
      && NR.GetPcRE(code, e1) == Some(RB.EndLoop)
      && NR.NfaRepOptRE(k - 1, greedy, qid, r1, code, e1 + 1, endl);
    NR.NfaRepIncrRE(r1, code, start + 3, e1);
    NR.NfaRepIncrOptRE(k - 1, greedy, qid, r1, code, e1 + 1, endl);
    if pc <= start + 2 {
    } else if pc < e1 {
      CaptureWriteIdsRE(r1, code, start + 3, e1, pc);
    } else if pc == e1 {
    } else {
      CaptureWriteIdsOptRE(k - 1, greedy, qid, r1, code, e1 + 1, endl, pc);
    }
  }

  // ==========================================================================
  // The TIGHTER capture-write classification (L3a §4b): a compiled block's
  // SetRegisterToCP target only the OUTSIDE-look captures (CapIdsOutsideLooks) --
  // a lookaround node compiles to a single CheckOracle, so its body's captures
  // are NOT in this bytecode. Used to show the MAIN match never writes a look
  // body's own capture registers (they stay unset until FLookLoop replays them).
  // ==========================================================================

  lemma CaptureWriteIdsOutsideRE(re: R.regex, code: RB.code, start: nat, endl: nat, pc: nat)
    requires NR.LookBehindFragmentRE(re) && CapUnique(re)
    requires NR.NfaRepRE(re, code, start, endl)
    requires start <= pc < endl
    ensures NR.GetPcRE(code, pc).Some? && NR.GetPcRE(code, pc).value.SetRegisterToCP? ==>
      NR.GetPcRE(code, pc).value.reg in CaptureRegsSet(CapIdsOutsideLooks(re))
    decreases CP.rsize(re), 1
  {
    match re
    case Re_empty =>
    case Re_character(_) =>
    case Re_anchor(_) =>
    case Re_lookaround(_, _, _) =>
    case Re_alt(r1, r2) =>
      var e1: nat :| NR.GetPcRE(code, start) == Some(RB.Fork(start + 1, e1 + 1))
        && NR.NfaRepRE(r1, code, start + 1, e1)
        && NR.GetPcRE(code, e1) == Some(RB.Jmp(endl))
        && NR.NfaRepRE(r2, code, e1 + 1, endl);
      NR.NfaRepIncrRE(r1, code, start + 1, e1);
      NR.NfaRepIncrRE(r2, code, e1 + 1, endl);
      if pc == start {
      } else if pc < e1 {
        CaptureWriteIdsOutsideRE(r1, code, start + 1, e1, pc);
        CaptureRegsSetMono(CapIdsOutsideLooks(r1), CapIdsOutsideLooks(re));
      } else if pc == e1 {
      } else {
        CaptureWriteIdsOutsideRE(r2, code, e1 + 1, endl, pc);
        CaptureRegsSetMono(CapIdsOutsideLooks(r2), CapIdsOutsideLooks(re));
      }
    case Re_con(r1, r2) =>
      var e1: nat :| NR.NfaRepRE(r1, code, start, e1) && NR.NfaRepRE(r2, code, e1, endl);
      NR.NfaRepIncrRE(r1, code, start, e1);
      NR.NfaRepIncrRE(r2, code, e1, endl);
      if pc < e1 {
        CaptureWriteIdsOutsideRE(r1, code, start, e1, pc);
        CaptureRegsSetMono(CapIdsOutsideLooks(r1), CapIdsOutsideLooks(re));
      } else {
        CaptureWriteIdsOutsideRE(r2, code, e1, endl, pc);
        CaptureRegsSetMono(CapIdsOutsideLooks(r2), CapIdsOutsideLooks(re));
      }
    case Re_capture(cid, r1) =>
      var e1: nat :| NR.GetPcRE(code, start) == Some(RB.SetRegisterToCP(CP.start_reg(cid)))
        && NR.NfaRepRE(r1, code, start + 1, e1)
        && NR.GetPcRE(code, e1) == Some(RB.SetRegisterToCP(CP.end_reg(cid)))
        && endl == e1 + 1;
      NR.NfaRepIncrRE(r1, code, start + 1, e1);
      assert cid >= 0 && (cid as nat) in CapIdsOutsideLooks(re);   // CapUnique; Re_capture adds it outside
      if pc == start {
        assert CP.start_reg(cid) in CaptureRegsSet(CapIdsOutsideLooks(re));
      } else if pc < e1 {
        CaptureWriteIdsOutsideRE(r1, code, start + 1, e1, pc);
        CaptureRegsSetMono(CapIdsOutsideLooks(r1), CapIdsOutsideLooks(re));
      } else {
        assert CP.end_reg(cid) in CaptureRegsSet(CapIdsOutsideLooks(re));
      }
    case Re_quant(nul, qid, q, r1) =>
      // CapIdsOutsideLooks(Re_quant) == CapIdsOutsideLooks(r1)
      if q.min == 0 && q.max == None {
        var e1: nat :| NR.GetPcRE(code, start) == Some(if q.greedy then RB.Fork(start + 1, e1 + 2) else RB.Fork(e1 + 2, start + 1))
          && NR.GetPcRE(code, start + 1) == Some(RB.SetQuantToClock(qid, false))
          && NR.GetPcRE(code, start + 2) == Some(RB.BeginLoop)
          && NR.NfaRepRE(r1, code, start + 3, e1)
          && NR.GetPcRE(code, e1) == Some(RB.EndLoop)
          && NR.GetPcRE(code, e1 + 1) == Some(RB.Jmp(start))
          && endl == e1 + 2;
        NR.NfaRepIncrRE(r1, code, start + 3, e1);
        if pc <= start + 2 {
        } else if pc < e1 {
          CaptureWriteIdsOutsideRE(r1, code, start + 3, e1, pc);
        } else {
        }
      } else if q.max.Some? {
        var em := NR.NfaRepREQuantInv(nul, qid, q, r1, code, start, endl);
        NR.NfaRepIncrMinRE(q.min as nat, qid, r1, code, start, em);
        NR.NfaRepIncrOptRE((q.max.value - q.min) as nat, q.greedy, qid, r1, code, em, endl);
        if pc < em {
          CaptureWriteIdsOutsideMinRE(q.min as nat, qid, r1, code, start, em, pc);
        } else {
          CaptureWriteIdsOutsideOptRE((q.max.value - q.min) as nat, q.greedy, qid, r1, code, em, endl, pc);
        }
      } else {
        var em, e1 := NR.NfaRepREPlusInv(nul, qid, q, r1, code, start, endl);
        NR.NfaRepIncrMinRE((q.min - 1) as nat, qid, r1, code, start, em);
        NR.NfaRepIncrRE(r1, code, em + 1, e1);
        if pc < em {
          CaptureWriteIdsOutsideMinRE((q.min - 1) as nat, qid, r1, code, start, em, pc);
        } else if pc == em {
        } else if pc < e1 {
          CaptureWriteIdsOutsideRE(r1, code, em + 1, e1, pc);
        } else {
        }
      }
  }

  lemma CaptureWriteIdsOutsideMinRE(k: nat, qid: R.quantid, r1: R.regex, code: RB.code, start: nat, endl: nat, pc: nat)
    requires NR.LookBehindFragmentRE(r1) && CapUnique(r1)
    requires NR.NfaRepMinRE(k, qid, r1, code, start, endl)
    requires start <= pc < endl
    ensures NR.GetPcRE(code, pc).Some? && NR.GetPcRE(code, pc).value.SetRegisterToCP? ==>
      NR.GetPcRE(code, pc).value.reg in CaptureRegsSet(CapIdsOutsideLooks(r1))
    decreases CP.rsize(r1), k + 2
  {
    if k == 0 { return; }
    var e1: nat :| NR.GetPcRE(code, start) == Some(RB.SetQuantToClock(qid, false))
      && NR.NfaRepRE(r1, code, start + 1, e1)
      && NR.NfaRepMinRE(k - 1, qid, r1, code, e1, endl);
    NR.NfaRepIncrRE(r1, code, start + 1, e1);
    NR.NfaRepIncrMinRE(k - 1, qid, r1, code, e1, endl);
    if pc == start {
    } else if pc < e1 {
      CaptureWriteIdsOutsideRE(r1, code, start + 1, e1, pc);
    } else {
      CaptureWriteIdsOutsideMinRE(k - 1, qid, r1, code, e1, endl, pc);
    }
  }

  lemma CaptureWriteIdsOutsideOptRE(k: nat, greedy: bool, qid: R.quantid, r1: R.regex, code: RB.code, start: nat, endl: nat, pc: nat)
    requires NR.LookBehindFragmentRE(r1) && CapUnique(r1)
    requires NR.NfaRepOptRE(k, greedy, qid, r1, code, start, endl)
    requires start <= pc < endl
    ensures NR.GetPcRE(code, pc).Some? && NR.GetPcRE(code, pc).value.SetRegisterToCP? ==>
      NR.GetPcRE(code, pc).value.reg in CaptureRegsSet(CapIdsOutsideLooks(r1))
    decreases CP.rsize(r1), k + 2
  {
    if k == 0 { return; }
    var e1: nat :| NR.GetPcRE(code, start) == Some(if greedy then RB.Fork(start + 1, endl) else RB.Fork(endl, start + 1))
      && NR.GetPcRE(code, start + 1) == Some(RB.SetQuantToClock(qid, false))
      && NR.GetPcRE(code, start + 2) == Some(RB.BeginLoop)
      && NR.NfaRepRE(r1, code, start + 3, e1)
      && NR.GetPcRE(code, e1) == Some(RB.EndLoop)
      && NR.NfaRepOptRE(k - 1, greedy, qid, r1, code, e1 + 1, endl);
    NR.NfaRepIncrRE(r1, code, start + 3, e1);
    NR.NfaRepIncrOptRE(k - 1, greedy, qid, r1, code, e1 + 1, endl);
    if pc <= start + 2 {
    } else if pc < e1 {
      CaptureWriteIdsOutsideRE(r1, code, start + 3, e1, pc);
    } else if pc == e1 {
    } else {
      CaptureWriteIdsOutsideOptRE(k - 1, greedy, qid, r1, code, e1 + 1, endl, pc);
    }
  }

  /** Every `SetQuantToClock` inside a compiled block targets one of that
      regex's own quant ids. */
  lemma LookCheckIdsRE(re: R.regex, code: RB.code, start: nat, endl: nat, pc: nat)
    requires NR.LookBehindFragmentRE(re) && LTB.LookUnique(re)
    requires NR.NfaRepRE(re, code, start, endl)
    requires start <= pc < endl
    ensures NR.GetPcRE(code, pc).Some? && NR.GetPcRE(code, pc).value.CheckOracle? ==>
      var l := NR.GetPcRE(code, pc).value.col;
      l >= 0 && (l as nat) in LTB.LookIds(re)
    ensures NR.GetPcRE(code, pc).Some? && NR.GetPcRE(code, pc).value.NegCheckOracle? ==>
      var l := NR.GetPcRE(code, pc).value.ncl;
      l >= 0 && (l as nat) in LTB.LookIds(re)
    decreases CP.rsize(re), 1
  {
    match re
    case Re_empty =>
    case Re_character(_) =>
    case Re_anchor(_) =>
    case Re_lookaround(lid, la, r1) =>
      // the whole block is the single gate instruction, whose lid is this
      // node's own
      assert pc == start;
      assert lid >= 0;                                  // LookUnique
    case Re_alt(r1, r2) =>
      var e1: nat :| NR.GetPcRE(code, start) == Some(RB.Fork(start + 1, e1 + 1))
        && NR.NfaRepRE(r1, code, start + 1, e1)
        && NR.GetPcRE(code, e1) == Some(RB.Jmp(endl))
        && NR.NfaRepRE(r2, code, e1 + 1, endl);
      NR.NfaRepIncrRE(r1, code, start + 1, e1);
      NR.NfaRepIncrRE(r2, code, e1 + 1, endl);
      if pc == start {
      } else if pc < e1 {
        LookCheckIdsRE(r1, code, start + 1, e1, pc);
      } else if pc == e1 {
      } else {
        LookCheckIdsRE(r2, code, e1 + 1, endl, pc);
      }
    case Re_con(r1, r2) =>
      var e1: nat :| NR.NfaRepRE(r1, code, start, e1) && NR.NfaRepRE(r2, code, e1, endl);
      NR.NfaRepIncrRE(r1, code, start, e1);
      NR.NfaRepIncrRE(r2, code, e1, endl);
      if pc < e1 {
        LookCheckIdsRE(r1, code, start, e1, pc);
      } else {
        LookCheckIdsRE(r2, code, e1, endl, pc);
      }
    case Re_capture(cid, r1) =>
      var e1: nat :| NR.GetPcRE(code, start) == Some(RB.SetRegisterToCP(CP.start_reg(cid)))
        && NR.NfaRepRE(r1, code, start + 1, e1)
        && NR.GetPcRE(code, e1) == Some(RB.SetRegisterToCP(CP.end_reg(cid)))
        && endl == e1 + 1;
      NR.NfaRepIncrRE(r1, code, start + 1, e1);
      if pc == start {
      } else if pc < e1 {
        LookCheckIdsRE(r1, code, start + 1, e1, pc);
      } else {
      }
    case Re_quant(nul, qid, q, r1) =>
      if q.min == 0 && q.max == None {
        var e1: nat :| NR.GetPcRE(code, start) == Some(if q.greedy then RB.Fork(start + 1, e1 + 2) else RB.Fork(e1 + 2, start + 1))
          && NR.GetPcRE(code, start + 1) == Some(RB.SetQuantToClock(qid, false))
          && NR.GetPcRE(code, start + 2) == Some(RB.BeginLoop)
          && NR.NfaRepRE(r1, code, start + 3, e1)
          && NR.GetPcRE(code, e1) == Some(RB.EndLoop)
          && NR.GetPcRE(code, e1 + 1) == Some(RB.Jmp(start))
          && endl == e1 + 2;
        NR.NfaRepIncrRE(r1, code, start + 3, e1);
        if pc <= start + 2 {
        } else if pc < e1 {
          LookCheckIdsRE(r1, code, start + 3, e1, pc);
        } else {
        }
      } else if q.max.Some? {
        var em := NR.NfaRepREQuantInv(nul, qid, q, r1, code, start, endl);
        NR.NfaRepIncrMinRE(q.min as nat, qid, r1, code, start, em);
        NR.NfaRepIncrOptRE((q.max.value - q.min) as nat, q.greedy, qid, r1, code, em, endl);
        if pc < em {
          LookCheckIdsMinRE(q.min as nat, qid, r1, code, start, em, pc);
        } else {
          LookCheckIdsOptRE((q.max.value - q.min) as nat, q.greedy, qid, r1, code, em, endl, pc);
        }
      } else {
        var em, e1 := NR.NfaRepREPlusInv(nul, qid, q, r1, code, start, endl);
        NR.NfaRepIncrMinRE((q.min - 1) as nat, qid, r1, code, start, em);
        NR.NfaRepIncrRE(r1, code, em + 1, e1);
        if pc < em {
          LookCheckIdsMinRE((q.min - 1) as nat, qid, r1, code, start, em, pc);
        } else if pc == em {
        } else if pc < e1 {
          LookCheckIdsRE(r1, code, em + 1, e1, pc);
        } else {
        }
      }
  }

  /** `LookCheckIdsRE` for the forced-copy chain. */
  lemma LookCheckIdsMinRE(k: nat, qid: R.quantid, r1: R.regex, code: RB.code, start: nat, endl: nat, pc: nat)
    requires NR.LookBehindFragmentRE(r1) && LTB.LookUnique(r1)
    requires NR.NfaRepMinRE(k, qid, r1, code, start, endl)
    requires start <= pc < endl
    ensures NR.GetPcRE(code, pc).Some? && NR.GetPcRE(code, pc).value.CheckOracle? ==>
      var l := NR.GetPcRE(code, pc).value.col;
      l >= 0 && (l as nat) in LTB.LookIds(r1)
    ensures NR.GetPcRE(code, pc).Some? && NR.GetPcRE(code, pc).value.NegCheckOracle? ==>
      var l := NR.GetPcRE(code, pc).value.ncl;
      l >= 0 && (l as nat) in LTB.LookIds(r1)
    decreases CP.rsize(r1), k + 2
  {
    if k == 0 { return; }
    var e1: nat :| NR.GetPcRE(code, start) == Some(RB.SetQuantToClock(qid, false))
      && NR.NfaRepRE(r1, code, start + 1, e1)
      && NR.NfaRepMinRE(k - 1, qid, r1, code, e1, endl);
    NR.NfaRepIncrRE(r1, code, start + 1, e1);
    NR.NfaRepIncrMinRE(k - 1, qid, r1, code, e1, endl);
    if pc == start {
    } else if pc < e1 {
      LookCheckIdsRE(r1, code, start + 1, e1, pc);
    } else {
      LookCheckIdsMinRE(k - 1, qid, r1, code, e1, endl, pc);
    }
  }

  /** `LookCheckIdsRE` for the optional-layer chain. */
  lemma LookCheckIdsOptRE(k: nat, greedy: bool, qid: R.quantid, r1: R.regex, code: RB.code, start: nat, endl: nat, pc: nat)
    requires NR.LookBehindFragmentRE(r1) && LTB.LookUnique(r1)
    requires NR.NfaRepOptRE(k, greedy, qid, r1, code, start, endl)
    requires start <= pc < endl
    ensures NR.GetPcRE(code, pc).Some? && NR.GetPcRE(code, pc).value.CheckOracle? ==>
      var l := NR.GetPcRE(code, pc).value.col;
      l >= 0 && (l as nat) in LTB.LookIds(r1)
    ensures NR.GetPcRE(code, pc).Some? && NR.GetPcRE(code, pc).value.NegCheckOracle? ==>
      var l := NR.GetPcRE(code, pc).value.ncl;
      l >= 0 && (l as nat) in LTB.LookIds(r1)
    decreases CP.rsize(r1), k + 2
  {
    if k == 0 { return; }
    var e1: nat :| NR.GetPcRE(code, start) == Some(if greedy then RB.Fork(start + 1, endl) else RB.Fork(endl, start + 1))
      && NR.GetPcRE(code, start + 1) == Some(RB.SetQuantToClock(qid, false))
      && NR.GetPcRE(code, start + 2) == Some(RB.BeginLoop)
      && NR.NfaRepRE(r1, code, start + 3, e1)
      && NR.GetPcRE(code, e1) == Some(RB.EndLoop)
      && NR.NfaRepOptRE(k - 1, greedy, qid, r1, code, e1 + 1, endl);
    NR.NfaRepIncrRE(r1, code, start + 3, e1);
    NR.NfaRepIncrOptRE(k - 1, greedy, qid, r1, code, e1 + 1, endl);
    if pc <= start + 2 {
    } else if pc < e1 {
      LookCheckIdsRE(r1, code, start + 3, e1, pc);
    } else if pc == e1 {
    } else {
      LookCheckIdsOptRE(k - 1, greedy, qid, r1, code, e1 + 1, endl, pc);
    }
  }


  /** `QuantIds` that does NOT descend into lookaround bodies — the ids the
      filter can actually consult. */
  // ==========================================================================
  // Capture-id in/outside-looks split (L3a) — the capture analogue of the
  // quant split below. The capture pass replays a look body's OWN groups
  // (CapIdsInLooks), disjoint from the outer groups the main filter reads
  // (CapIdsOutsideLooks). Lifted to registers by CaptureRegsDisjoint.
  // ==========================================================================

  /** The capture ids OUTSIDE lookaround bodies — read by the main filter. */
  ghost function CapIdsOutsideLooks(r: R.regex): set<nat>
    decreases r
  {
    match r
    case Re_empty => {}
    case Re_character(_) => {}
    case Re_anchor(_) => {}
    case Re_alt(r1, r2) => CapIdsOutsideLooks(r1) + CapIdsOutsideLooks(r2)
    case Re_con(r1, r2) => CapIdsOutsideLooks(r1) + CapIdsOutsideLooks(r2)
    case Re_quant(_, _, _, r1) => CapIdsOutsideLooks(r1)
    case Re_capture(cid, r1) => (if cid >= 0 then {cid as nat} else {}) + CapIdsOutsideLooks(r1)
    case Re_lookaround(_, _, _) => {}
  }

  /** The capture ids INSIDE lookaround bodies — replayed by the capture pass. */
  ghost function CapIdsInLooks(r: R.regex): set<nat>
    decreases r
  {
    match r
    case Re_empty => {}
    case Re_character(_) => {}
    case Re_anchor(_) => {}
    case Re_alt(r1, r2) => CapIdsInLooks(r1) + CapIdsInLooks(r2)
    case Re_con(r1, r2) => CapIdsInLooks(r1) + CapIdsInLooks(r2)
    case Re_quant(_, _, _, r1) => CapIdsInLooks(r1)
    case Re_capture(_, r1) => CapIdsInLooks(r1)
    case Re_lookaround(_, _, r1) => CapIds(r1)
  }

  /** The two halves cover everything. */
  lemma CapIdsSplit(r: R.regex)
    ensures CapIds(r) == CapIdsOutsideLooks(r) + CapIdsInLooks(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => CapIdsSplit(r1); CapIdsSplit(r2);
    case Re_con(r1, r2) => CapIdsSplit(r1); CapIdsSplit(r2);
    case Re_quant(_, _, _, r1) => CapIdsSplit(r1);
    case Re_capture(_, r1) => CapIdsSplit(r1);
    case Re_lookaround(_, _, r1) =>
    case _ =>
  }

  /** ...and, with unique ids, they are disjoint. */
  lemma CapIdsLooksDisjoint(r: R.regex)
    requires CapUnique(r)
    ensures CapIdsOutsideLooks(r) * CapIdsInLooks(r) == {}
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      CapIdsLooksDisjoint(r1); CapIdsLooksDisjoint(r2);
      CapIdsSplit(r1); CapIdsSplit(r2);
      forall q: nat | q in CapIdsOutsideLooks(r) ensures q !in CapIdsInLooks(r) {
        if q in CapIdsOutsideLooks(r1) {
          assert q !in CapIdsInLooks(r1) by {
            if q in CapIdsInLooks(r1) { assert q in CapIdsOutsideLooks(r1) * CapIdsInLooks(r1); }
          }
          assert q in CapIds(r1);
          if q in CapIdsInLooks(r2) { assert q in CapIds(r2); assert q in CapIds(r1) * CapIds(r2); }
        } else {
          assert q in CapIdsOutsideLooks(r2);
          assert q !in CapIdsInLooks(r2) by {
            if q in CapIdsInLooks(r2) { assert q in CapIdsOutsideLooks(r2) * CapIdsInLooks(r2); }
          }
          assert q in CapIds(r2);
          if q in CapIdsInLooks(r1) { assert q in CapIds(r1); assert q in CapIds(r1) * CapIds(r2); }
        }
      }
    case Re_con(r1, r2) =>
      CapIdsLooksDisjoint(r1); CapIdsLooksDisjoint(r2);
      CapIdsSplit(r1); CapIdsSplit(r2);
      forall q: nat | q in CapIdsOutsideLooks(r) ensures q !in CapIdsInLooks(r) {
        if q in CapIdsOutsideLooks(r1) {
          assert q !in CapIdsInLooks(r1) by {
            if q in CapIdsInLooks(r1) { assert q in CapIdsOutsideLooks(r1) * CapIdsInLooks(r1); }
          }
          assert q in CapIds(r1);
          if q in CapIdsInLooks(r2) { assert q in CapIds(r2); assert q in CapIds(r1) * CapIds(r2); }
        } else {
          assert q in CapIdsOutsideLooks(r2);
          assert q !in CapIdsInLooks(r2) by {
            if q in CapIdsInLooks(r2) { assert q in CapIdsOutsideLooks(r2) * CapIdsInLooks(r2); }
          }
          assert q in CapIds(r2);
          if q in CapIdsInLooks(r1) { assert q in CapIds(r1); assert q in CapIds(r1) * CapIds(r2); }
        }
      }
    case Re_quant(_, _, _, r1) => CapIdsLooksDisjoint(r1);
    case Re_capture(cid, r1) =>
      CapIdsLooksDisjoint(r1);
      CapIdsSplit(r1);
      forall q: nat | q in CapIdsOutsideLooks(r) ensures q !in CapIdsInLooks(r) {
        if q == cid as nat {
          if q in CapIdsInLooks(r1) { assert q in CapIds(r1); }   // CapUnique: cid !in CapIds(r1)
        }
      }
    case Re_lookaround(_, _, r1) =>
    case _ =>
  }

  /** Disjoint capture ids give disjoint capture REGISTERS (start_reg/end_reg
      are injective and parity-separated). */
  lemma CaptureRegsDisjoint(a: R.regex, b: R.regex)
    requires CapIds(a) * CapIds(b) == {}
    ensures CaptureRegs(a) * CaptureRegs(b) == {}
  {
    forall k | k in CaptureRegs(a) ensures k !in CaptureRegs(b) {
      var ca :| ca in CapIds(a) && (k == CP.start_reg(ca) || k == CP.end_reg(ca));
      if k in CaptureRegs(b) {
        var cb :| cb in CapIds(b) && (k == CP.start_reg(cb) || k == CP.end_reg(cb));
        assert CP.start_reg(ca) == 2 * ca && CP.end_reg(ca) == 2 * ca + 1;
        assert CP.start_reg(cb) == 2 * cb && CP.end_reg(cb) == 2 * cb + 1;
        assert ca == cb;
        assert ca in CapIds(a) * CapIds(b);
      }
    }
  }

  ghost function QuantIdsOutsideLooks(r: R.regex): set<nat>
    decreases r
  {
    match r
    case Re_empty => {}
    case Re_character(_) => {}
    case Re_anchor(_) => {}
    case Re_alt(r1, r2) => QuantIdsOutsideLooks(r1) + QuantIdsOutsideLooks(r2)
    case Re_con(r1, r2) => QuantIdsOutsideLooks(r1) + QuantIdsOutsideLooks(r2)
    case Re_quant(_, qid, _, r1) =>
      (if qid >= 0 then {qid as nat} else {}) + QuantIdsOutsideLooks(r1)
    case Re_capture(_, r1) => QuantIdsOutsideLooks(r1)
    case Re_lookaround(_, _, _) => {}
  }

  /** The quant ids that live INSIDE lookaround bodies — the ones the capture
      pass rewrites and the filter never reads. */
  ghost function QuantIdsInLooks(r: R.regex): set<nat>
    decreases r
  {
    match r
    case Re_empty => {}
    case Re_character(_) => {}
    case Re_anchor(_) => {}
    case Re_alt(r1, r2) => QuantIdsInLooks(r1) + QuantIdsInLooks(r2)
    case Re_con(r1, r2) => QuantIdsInLooks(r1) + QuantIdsInLooks(r2)
    case Re_quant(_, _, _, r1) => QuantIdsInLooks(r1)
    case Re_capture(_, r1) => QuantIdsInLooks(r1)
    case Re_lookaround(_, _, r1) => QuantIds(r1)
  }

  /** The two halves cover everything. */
  lemma QuantIdsSplit(r: R.regex)
    ensures QuantIds(r) == QuantIdsOutsideLooks(r) + QuantIdsInLooks(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => QuantIdsSplit(r1); QuantIdsSplit(r2);
    case Re_con(r1, r2) => QuantIdsSplit(r1); QuantIdsSplit(r2);
    case Re_quant(_, _, _, r1) => QuantIdsSplit(r1);
    case Re_capture(_, r1) => QuantIdsSplit(r1);
    case Re_lookaround(_, _, r1) =>
    case _ =>
  }

  /** ...and, with unique ids, they are disjoint: an id used inside a
      lookaround body cannot also name a quantifier outside one. This is what
      lets the capture pass's quant writes (all inside a body) sit alongside the
      filter's reads (all outside). */
  lemma QuantIdsLooksDisjoint(r: R.regex)
    requires QuantUnique(r)
    ensures QuantIdsOutsideLooks(r) * QuantIdsInLooks(r) == {}
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      QuantIdsLooksDisjoint(r1); QuantIdsLooksDisjoint(r2);
      QuantIdsSplit(r1); QuantIdsSplit(r2);
      forall q: nat | q in QuantIdsOutsideLooks(r) ensures q !in QuantIdsInLooks(r) {
        if q in QuantIdsOutsideLooks(r1) {
          assert q !in QuantIdsInLooks(r1) by {                   // IH on r1
            if q in QuantIdsInLooks(r1) {
              assert q in QuantIdsOutsideLooks(r1) * QuantIdsInLooks(r1);
            }
          }
          assert q in QuantIds(r1);
          if q in QuantIdsInLooks(r2) {
            assert q in QuantIds(r2);
            assert q in QuantIds(r1) * QuantIds(r2);              // QuantUnique
          }
        } else {
          assert q in QuantIdsOutsideLooks(r2);
          assert q !in QuantIdsInLooks(r2) by {                   // IH on r2
            if q in QuantIdsInLooks(r2) {
              assert q in QuantIdsOutsideLooks(r2) * QuantIdsInLooks(r2);
            }
          }
          assert q in QuantIds(r2);
          if q in QuantIdsInLooks(r1) {
            assert q in QuantIds(r1);
            assert q in QuantIds(r1) * QuantIds(r2);              // QuantUnique
          }
        }
      }
    case Re_con(r1, r2) =>
      QuantIdsLooksDisjoint(r1); QuantIdsLooksDisjoint(r2);
      QuantIdsSplit(r1); QuantIdsSplit(r2);
      forall q: nat | q in QuantIdsOutsideLooks(r) ensures q !in QuantIdsInLooks(r) {
        if q in QuantIdsOutsideLooks(r1) {
          assert q !in QuantIdsInLooks(r1) by {                   // IH on r1
            if q in QuantIdsInLooks(r1) {
              assert q in QuantIdsOutsideLooks(r1) * QuantIdsInLooks(r1);
            }
          }
          assert q in QuantIds(r1);
          if q in QuantIdsInLooks(r2) {
            assert q in QuantIds(r2);
            assert q in QuantIds(r1) * QuantIds(r2);              // QuantUnique
          }
        } else {
          assert q in QuantIdsOutsideLooks(r2);
          assert q !in QuantIdsInLooks(r2) by {                   // IH on r2
            if q in QuantIdsInLooks(r2) {
              assert q in QuantIdsOutsideLooks(r2) * QuantIdsInLooks(r2);
            }
          }
          assert q in QuantIds(r2);
          if q in QuantIdsInLooks(r1) {
            assert q in QuantIds(r1);
            assert q in QuantIds(r1) * QuantIds(r2);              // QuantUnique
          }
        }
      }
    case Re_quant(nul, qid, q0, r1) =>
      QuantIdsLooksDisjoint(r1);
      QuantIdsSplit(r1);
      forall q: nat | q in QuantIdsOutsideLooks(r) ensures q !in QuantIdsInLooks(r) {
        if q == qid as nat {
          if q in QuantIdsInLooks(r1) { assert q in QuantIds(r1); }   // QuantUnique
        }
      }
    case Re_capture(_, r1) => QuantIdsLooksDisjoint(r1);
    case Re_lookaround(_, _, r1) =>
    case _ =>
  }

  /** THE frame: `filter_capture` reads quant clocks freely only OUTSIDE
      lookaround bodies; a capturing keep-branch look body also reads the body's
      (inside-look) quant clocks. So agreeing on `QuantIdsOutsideLooks` frames the
      output at every position OUTSIDE `W = CaptureRegsSet(CapIdsInLooks(r))`.
      (L2 had full equality — capture-free bodies read no clocks.) */
  lemma FilterCaptureQcFrameOutside(r: R.regex, cr: seq<int>, cc: seq<int>, lc: seq<int>,
                                    qc: seq<int>, qc2: seq<int>, M: int, j: int)
    requires NR.LookBehindFragmentRE(r)
    requires forall q0: nat :: q0 in QuantIdsOutsideLooks(r)
                               ==> AI.get_idx(qc, q0) == AI.get_idx(qc2, q0)
    ensures j !in CaptureRegsSet(CapIdsInLooks(r)) ==>
            AI.get_idx(AI.filter_capture(r, cr, cc, lc, qc, M), j)
         == AI.get_idx(AI.filter_capture(r, cr, cc, lc, qc2, M), j)
    decreases r, 1
  {
    if j !in CaptureRegsSet(CapIdsInLooks(r)) {
      match r
      case Re_alt(r1, r2) => QcFrameOutsideSeqStep(r, r1, r2, cr, cc, lc, qc, qc2, M, j);
      case Re_con(r1, r2) => QcFrameOutsideSeqStep(r, r1, r2, cr, cc, lc, qc, qc2, M, j);
      case Re_quant(nul, qid, q, r1) =>
        assert AI.get_idx(qc, qid) == AI.get_idx(qc2, qid);
        var qv := AI.get_idx(qc, qid);
        if qv < M { /* both filter_all(r1, cr): no qc read */ }
        else { FilterCaptureQcFrameOutside(r1, cr, cc, lc, qc, qc2, qv, j); }   // W(quant)==W(r1)
      case Re_capture(cid, r1) =>
        var start := AI.get_idx(cc, CP.start_reg(cid));
        if start < 0 { } else if start < M { }
        else { FilterCaptureQcFrameOutside(r1, cr, cc, lc, qc, qc2, M, j); }    // W(capture)==W(r1)
      case Re_lookaround(lid, la, r1) =>
        NR.PlusIsLookBehindFragmentRE(r1);
        assert forall cid: nat :: cid in CapIds(r1) ==> CP.start_reg(cid) != j by {
          forall cid: nat | cid in CapIds(r1) ensures CP.start_reg(cid) != j { StartRegInCaptureRegsSet(CapIds(r1), cid); }
        }
        LkValAtNonStart(lid, la, r1, cr, cc, lc, qc, M, j);
        LkValAtNonStart(lid, la, r1, cr, cc, lc, qc2, M, j);
      case _ =>
    }
  }

  /** Shared `alt`/`con` step for `FilterCaptureQcFrameOutside`: frame the prefix
      `r1` outside `W(r1)`, then compose with `FilterCaptureCrPointwise` +
      the suffix `r2` frame. */
  lemma QcFrameOutsideSeqStep(r: R.regex, r1: R.regex, r2: R.regex, cr: seq<int>, cc: seq<int>,
                              lc: seq<int>, qc: seq<int>, qc2: seq<int>, M: int, j: int)
    requires r == R.Re_alt(r1, r2) || r == R.Re_con(r1, r2)
    requires NR.LookBehindFragmentRE(r)
    requires forall q0: nat :: q0 in QuantIdsOutsideLooks(r)
                               ==> AI.get_idx(qc, q0) == AI.get_idx(qc2, q0)
    requires j !in CaptureRegsSet(CapIdsInLooks(r))
    ensures AI.get_idx(AI.filter_capture(r, cr, cc, lc, qc, M), j)
         == AI.get_idx(AI.filter_capture(r, cr, cc, lc, qc2, M), j)
    decreases r, 0
  {
    var Y  := AI.filter_capture(r1, cr, cc, lc, qc, M);
    var Y2 := AI.filter_capture(r1, cr, cc, lc, qc2, M);
    CaptureRegsSetMono(CapIdsInLooks(r1), CapIdsInLooks(r));
    CaptureRegsSetMono(CapIdsInLooks(r2), CapIdsInLooks(r));
    FilterCaptureFullOutside(r1, cr, cc, lc, qc, qc2, M);          // Y ~ Y2 outside W(r1); j!in W(r1)
    assert AI.get_idx(Y, j) == AI.get_idx(Y2, j);
    FilterCaptureQcFrameOutside(r2, Y2, cc, lc, qc, qc2, M, j);    // j!in W(r2) ==> f(r2,Y2,qc)[j]==f(r2,Y2,qc2)[j]
    FilterCaptureCrPointwise(r2, Y, Y2, cc, lc, qc, M, j);         // f(r2,Y,qc)[j]==f(r2,Y2,qc)[j]
  }

  /** The whole-sequence form of `FilterCaptureQcFrameOutside`: outputs agree at
      every position OUTSIDE `W = CaptureRegsSet(CapIdsInLooks(r))`. */
  lemma FilterCaptureFullOutside(r: R.regex, cr: seq<int>, cc: seq<int>, lc: seq<int>,
                                 qc: seq<int>, qc2: seq<int>, M: int)
    requires NR.LookBehindFragmentRE(r)
    requires forall q0: nat :: q0 in QuantIdsOutsideLooks(r)
                               ==> AI.get_idx(qc, q0) == AI.get_idx(qc2, q0)
    ensures forall i :: i !in CaptureRegsSet(CapIdsInLooks(r)) ==>
            AI.get_idx(AI.filter_capture(r, cr, cc, lc, qc, M), i)
         == AI.get_idx(AI.filter_capture(r, cr, cc, lc, qc2, M), i)
    decreases r, 2
  {
    forall i: int | i !in CaptureRegsSet(CapIdsInLooks(r))
      ensures AI.get_idx(AI.filter_capture(r, cr, cc, lc, qc, M), i)
           == AI.get_idx(AI.filter_capture(r, cr, cc, lc, qc2, M), i)
    {
      FilterCaptureQcFrameOutside(r, cr, cc, lc, qc, qc2, M, i);
    }
  }

  /** A capture-free regex has no capture ids. */
  lemma CaptureFreeNoCapIds(r: R.regex)
    requires NR.CaptureFreeRE(r)
    ensures CapIds(r) == {}
    decreases r
  {
    match r
    case Re_alt(r1, r2) => CaptureFreeNoCapIds(r1); CaptureFreeNoCapIds(r2);
    case Re_con(r1, r2) => CaptureFreeNoCapIds(r1); CaptureFreeNoCapIds(r2);
    case Re_quant(_, _, _, r1) => CaptureFreeNoCapIds(r1);
    case Re_lookaround(_, _, r1) => CaptureFreeNoCapIds(r1);
    case _ =>
  }

  /** A quantifier body inside a capture-free regex is itself capture-free. */
  lemma CaptureFreeQidBody(r: R.regex, qid: nat)
    requires NR.CaptureFreeRE(r) && qid in QuantIds(r)
    ensures NR.CaptureFreeRE(QidBody(r, qid))
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      if qid in QuantIds(r1) { CaptureFreeQidBody(r1, qid); } else { CaptureFreeQidBody(r2, qid); }
    case Re_con(r1, r2) =>
      if qid in QuantIds(r1) { CaptureFreeQidBody(r1, qid); } else { CaptureFreeQidBody(r2, qid); }
    case Re_quant(_, qid0, _, r1) =>
      if qid0 >= 0 && (qid0 as nat) == qid { } else { CaptureFreeQidBody(r1, qid); }
    case Re_lookaround(_, _, r1) => CaptureFreeQidBody(r1, qid);
    case _ =>
  }

  /** A group's start register belongs to `CaptureRegsSet(S)` iff the group is in
      `S` (parity: `start_reg` is even, `end_reg` odd, both injective). */
  lemma StartRegInCaptureRegsSet(S: set<nat>, g: nat)
    ensures (CP.start_reg(g) in CaptureRegsSet(S)) <==> (g in S)
  {
    if CP.start_reg(g) in CaptureRegsSet(S) {
      if CP.start_reg(g) in (set cid | cid in S :: CP.start_reg(cid)) {
        var c :| c in S && CP.start_reg(c) == CP.start_reg(g);
        assert 2 * c == 2 * g;
      } else {
        var c :| c in S && CP.end_reg(c) == CP.start_reg(g);
        assert 2 * c + 1 == 2 * g;   // parity contradiction
      }
    }
  }

  lemma EndRegInCaptureRegsSet(S: set<nat>, g: nat)
    ensures (CP.end_reg(g) in CaptureRegsSet(S)) <==> (g in S)
  {
    if CP.end_reg(g) in CaptureRegsSet(S) {
      if CP.end_reg(g) in (set cid | cid in S :: CP.start_reg(cid)) {
        var c :| c in S && CP.start_reg(c) == CP.end_reg(g);
        assert 2 * c == 2 * g + 1;   // parity contradiction
      } else {
        var c :| c in S && CP.end_reg(c) == CP.end_reg(g);
        assert 2 * c + 1 == 2 * g + 1;
      }
    }
  }

  /** THE P1 GmOfLive frame: on OUTSIDE-look groups, `GmOfLive` is unchanged when
      the capture bank (and its clocks) agree outside the inside-look registers,
      the look bank is the same, and the quant clocks agree at outside-look quant
      ids. Composes `FilterFrameOutside` (capture frame) with `FilterCaptureFull-
      Outside` (quant frame). The agreements are `requires` -- the caller supplies
      them from §4a (`RegsAgreeOutside(res.0, caps, S)`) and the FLookLoop quant
      frame. This is P1: it moves `GmOfLive(re, res.0, lk, res.2)` to `GmOfLive(re,
      caps, lk, qt)` on all outside-look groups. */
  lemma GmOfLiveFrameOutside(re: R.regex, cap: AReg.Regs, cap': AReg.Regs, look: AReg.Regs,
                             quant: AReg.Regs, quant': AReg.Regs)
    requires NR.LookBehindFragmentRE(re) && CapUnique(re)
    requires forall k: int :: k !in CaptureRegsSet(CapIdsInLooks(re)) ==>
      AI.get_idx(AReg.as_arrays(cap).0, k) == AI.get_idx(AReg.as_arrays(cap').0, k)
      && AI.get_idx(AReg.as_arrays(cap).1, k) == AI.get_idx(AReg.as_arrays(cap').1, k)
    requires forall q: nat :: q in QuantIdsOutsideLooks(re) ==>
      AI.get_idx(AReg.as_arrays(quant).1, q) == AI.get_idx(AReg.as_arrays(quant').1, q)
    ensures forall g: nat :: g !in CapIdsInLooks(re) ==>
      ((g in GmOfLive(re, cap, look, quant)) <==> (g in GmOfLive(re, cap', look, quant')))
      && (g in GmOfLive(re, cap, look, quant) ==>
          GmOfLive(re, cap, look, quant)[g] == GmOfLive(re, cap', look, quant')[g])
  {
    var W := CaptureRegsSet(CapIdsInLooks(re));
    var crA := AReg.as_arrays(cap).0;  var ccA := AReg.as_arrays(cap).1;
    var crB := AReg.as_arrays(cap').0; var ccB := AReg.as_arrays(cap').1;
    var lc := AReg.as_arrays(look).1;
    var qcA := AReg.as_arrays(quant).1; var qcB := AReg.as_arrays(quant').1;

    // structural requires of FilterFrameOutside
    CapIdsLooksDisjoint(re);
    assert forall g: nat :: g in CapIdsInLooks(re) ==> CP.start_reg(g) in W by {
      forall g: nat | g in CapIdsInLooks(re) ensures CP.start_reg(g) in W { StartRegInCaptureRegsSet(CapIdsInLooks(re), g); }
    }
    assert forall g: nat :: g in CapIdsOutsideLooks(re) ==> CP.start_reg(g) !in W by {
      forall g: nat | g in CapIdsOutsideLooks(re) ensures CP.start_reg(g) !in W {
        assert g !in CapIdsInLooks(re) by { if g in CapIdsInLooks(re) { assert g in CapIdsOutsideLooks(re) * CapIdsInLooks(re); } }
        StartRegInCaptureRegsSet(CapIdsInLooks(re), g);
      }
    }
    assert forall x: int :: x in W ==> x >= 0 by {
      forall x: int | x in W ensures x >= 0 {}
    }
    // swap quant' -> quant on the whole filter (quant frame), then cap frame.
    FilterCaptureFullOutside(re, crB, ccB, lc, qcB, qcA, -1);   // filter(crB,ccB,qcB)==filter(crB,ccB,qcA)
    FilterFrameOutside(re, crA, crB, ccA, ccB, lc, qcA, qcA, -1, W);   // filter(crA,ccA,qcA) ~ filter(crB,ccB,qcA) outside W

    var f1 := AI.filter_reset(re, cap, look, quant, -1);
    var f2 := AI.filter_reset(re, cap', look, quant', -1);
    assert f1 == AI.filter_capture(re, crA, ccA, lc, qcA, -1);
    assert f2 == AI.filter_capture(re, crB, ccB, lc, qcB, -1);

    forall g: nat | g !in CapIdsInLooks(re)
      ensures ((g in GmOfLive(re, cap, look, quant)) <==> (g in GmOfLive(re, cap', look, quant')))
           && (g in GmOfLive(re, cap, look, quant) ==>
               GmOfLive(re, cap, look, quant)[g] == GmOfLive(re, cap', look, quant')[g])
    {
      StartRegInCaptureRegsSet(CapIdsInLooks(re), g);
      EndRegInCaptureRegsSet(CapIdsInLooks(re), g);
      assert CP.start_reg(g) !in W && CP.end_reg(g) !in W;
      assert AI.get_idx(f1, CP.start_reg(g)) == AI.get_idx(f2, CP.start_reg(g));
      assert AI.get_idx(f1, CP.end_reg(g)) == AI.get_idx(f2, CP.end_reg(g));
      assert AI.get_idx(ccA, CP.start_reg(g)) == AI.get_idx(ccB, CP.start_reg(g));
      assert AI.get_idx(ccA, CP.end_reg(g)) == AI.get_idx(ccB, CP.end_reg(g));
    }
  }

  /** P2 value wrapper: for an L3a-present captured group, `GmOfLive` at `gid` is
      the RAW range read straight off the capture bank -- filtering keeps both its
      start (`FilterKeepsPresentLk`) and end (`FilterCaptureKeepsOdd`) registers.
      So `GmOfLive(re, res.0, ..)[g]` on inside-look groups is exactly the
      reconstruction the value-lift produced. */
  lemma GmOfLiveKeepsPresentLk(re: R.regex, cap: AReg.Regs, look: AReg.Regs, quant: AReg.Regs, gid: nat)
    requires NR.LookBehindFragmentRE(re) && CapUnique(re)
    requires gid in CapIds(re)
    requires PathPresentLk(re, AReg.as_arrays(cap).1, AReg.as_arrays(look).1, AReg.as_arrays(quant).1, -1, gid)
    requires AI.get_idx(AReg.as_arrays(cap).1, CP.start_reg(gid)) >= 0
    requires AI.get_idx(AReg.as_arrays(cap).0, CP.start_reg(gid)) >= 0   // value set (clock-set => value-set)
    requires AI.get_idx(AReg.as_arrays(cap).1, CP.start_reg(gid))
               >= MxAtGidLk(re, AReg.as_arrays(cap).1, AReg.as_arrays(look).1, AReg.as_arrays(quant).1, -1, gid)
    ensures gid in GmOfLive(re, cap, look, quant)
    ensures GmOfLive(re, cap, look, quant)[gid]
              == LiveRange(AReg.as_arrays(cap).0, AReg.as_arrays(cap).1, gid)
  {
    var cr := AReg.as_arrays(cap).0;  var cc := AReg.as_arrays(cap).1;
    var lc := AReg.as_arrays(look).1; var qc := AReg.as_arrays(quant).1;
    var f := AI.filter_reset(re, cap, look, quant, -1);
    assert f == AI.filter_capture(re, cr, cc, lc, qc, -1);
    FilterKeepsPresentLk(re, cr, cc, lc, qc, -1, gid);              // f[start_reg(gid)] == cr[start_reg(gid)]
    FilterCaptureKeepsOdd(re, cr, cc, lc, qc, -1, CP.end_reg(gid)); // f[end_reg(gid)] == cr[end_reg(gid)]
    assert AI.get_idx(f, CP.start_reg(gid)) == AI.get_idx(cr, CP.start_reg(gid));
    assert AI.get_idx(f, CP.end_reg(gid)) == AI.get_idx(cr, CP.end_reg(gid));
    // membership: f[start_reg(gid)] == cr[start_reg(gid)]; cr[start_reg(gid)] >= 0 needs the
    // "clock set => value set" consistency (a captured group has a set value).
    assert AI.get_idx(f, CP.start_reg(gid)) >= 0;
    assert LiveRange(f, cc, gid) == LiveRange(cr, cc, gid);
  }

  /** A lookaround node is TRANSPARENT to both filters when its body is
      capture-free (the L1 fragment's shape): every branch of
      `filter_capture`'s lookaround rule, and `filter_all`'s, returns the
      capture registers unchanged — which is why the look clocks cannot steer
      anything. */
  lemma FilterAtLookaround(lid: R.lookid, la: R.lookaround, r1: R.regex, cr: seq<int>,
                           cc: seq<int>, lc: seq<int>, qc: seq<int>, M: int)
    requires NR.CaptureFreeRE(r1)
    ensures AI.filter_capture(R.Re_lookaround(lid, la, r1), cr, cc, lc, qc, M) == cr
    ensures AI.filter_all(R.Re_lookaround(lid, la, r1), cr) == cr
  {
    FilterAllCaptureFree(r1, cr);
    FilterCaptureCaptureFree(r1, cr, cc, lc, qc, -1);
  }

  /** L3a: a MATCHED lookaround node KEEPS the body's captures. When the look
      clock `lv = get_idx(lc, lid)` is set (`>= 0`) and not stale (`>= M`),
      `filter_capture`'s lookaround rule takes the `filter_capture(r1, .., -1)`
      branch -- so the body's own group registers survive filtering. The
      capturing analog of `FilterAtLookaround` (which collapses for capture-free
      bodies because both branches are then the identity). */
  lemma FilterAtLookaroundMatched(lid: R.lookid, la: R.lookaround, r1: R.regex, cr: seq<int>,
                                  cc: seq<int>, lc: seq<int>, qc: seq<int>, M: int)
    requires AI.get_idx(lc, lid) >= 0 && AI.get_idx(lc, lid) >= M
    ensures AI.filter_capture(R.Re_lookaround(lid, la, r1), cr, cc, lc, qc, M)
         == AI.filter_capture(r1, cr, cc, lc, qc, -1)
  {}

  /** A capture-free regex has nothing to erase: `filter_all` is the identity. */
  lemma FilterAllCaptureFree(r: R.regex, regs: seq<int>)
    requires NR.CaptureFreeRE(r)
    ensures AI.filter_all(r, regs) == regs
    decreases r
  {
    match r
    case Re_alt(r1, r2) => FilterAllCaptureFree(r1, regs); FilterAllCaptureFree(r2, AI.filter_all(r1, regs));
    case Re_con(r1, r2) => FilterAllCaptureFree(r1, regs); FilterAllCaptureFree(r2, AI.filter_all(r1, regs));
    case Re_quant(_, _, _, r1) => FilterAllCaptureFree(r1, regs);
    case Re_lookaround(_, _, r1) => FilterAllCaptureFree(r1, regs);
    case _ =>
  }

  /** A capture-free regex filters nothing either — whatever the clocks say. */
  lemma FilterCaptureCaptureFree(r: R.regex, cap_regs: seq<int>, cap_clocks: seq<int>,
                                 look_clocks: seq<int>, quant_clocks: seq<int>, maxclock: int)
    requires NR.CaptureFreeRE(r)
    ensures AI.filter_capture(r, cap_regs, cap_clocks, look_clocks, quant_clocks, maxclock) == cap_regs
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      FilterCaptureCaptureFree(r1, cap_regs, cap_clocks, look_clocks, quant_clocks, maxclock);
      FilterCaptureCaptureFree(r2, cap_regs, cap_clocks, look_clocks, quant_clocks, maxclock);
    case Re_con(r1, r2) =>
      FilterCaptureCaptureFree(r1, cap_regs, cap_clocks, look_clocks, quant_clocks, maxclock);
      FilterCaptureCaptureFree(r2, cap_regs, cap_clocks, look_clocks, quant_clocks, maxclock);
    case Re_quant(_, qid, _, r1) =>
      FilterAllCaptureFree(r1, cap_regs);
      FilterCaptureCaptureFree(r1, cap_regs, cap_clocks, look_clocks, quant_clocks,
                               AI.get_idx(quant_clocks, qid));
    case Re_lookaround(lid, _, r1) =>
      FilterAllCaptureFree(r1, cap_regs);
      FilterCaptureCaptureFree(r1, cap_regs, cap_clocks, look_clocks, quant_clocks, -1);
    case _ =>
  }

  /** A lookaround node's filter output at a position that is NOT one of the
      body's capture-start registers equals the input there — whichever branch
      (matched-keep or stale-reset) the look clock selects. The pointwise core of
      the outside-`W` look-independence. */
  lemma LkValAtNonStart(lid: R.lookid, la: R.lookaround, r1: R.regex, cr: seq<int>,
                        cc: seq<int>, lc: seq<int>, qc: seq<int>, M: int, j: int)
    requires NR.LookBehindFragmentRE(r1)
    requires forall cid: nat :: cid in CapIds(r1) ==> CP.start_reg(cid) != j
    ensures AI.get_idx(AI.filter_capture(R.Re_lookaround(lid, la, r1), cr, cc, lc, qc, M), j)
         == AI.get_idx(cr, j)
  {
    var lv := AI.get_idx(lc, lid);
    if lv < 0 || lv < M {
      // reset branch: filter_all(r1, cr); non-start position passes through.
      FilterAllKeepsNonStart(r1, cr, j);
    } else {
      // keep branch: filter_capture(r1, cr, cc, lc, qc, -1); == filter_all(r1,cr) at non-start j.
      FilterCaptureVsAll(r1, cr, cc, lc, qc, -1, j);
      FilterAllKeepsNonStart(r1, cr, j);
    }
  }

  /** L3a: `filter_capture` reads the look bank ONLY at lookaround nodes, whose
      effect is confined to their body's capture registers. So two look banks
      produce filter outputs that agree at every position OUTSIDE
      `W = CaptureRegsSet(CapIdsInLooks(r))` (the inside-look capture registers).
      The old capture-free-body version had full equality; a capturing keep-branch
      body genuinely depends on `lc`, so the honest statement frames outside `W`. */
  lemma FilterCaptureLookIndep(r: R.regex, cap_regs: seq<int>, cap_clocks: seq<int>,
                               lc1: seq<int>, lc2: seq<int>, quant_clocks: seq<int>, maxclock: int)
    requires NR.LookBehindFragmentRE(r)
    ensures forall j :: j !in CaptureRegsSet(CapIdsInLooks(r)) ==>
      AI.get_idx(AI.filter_capture(r, cap_regs, cap_clocks, lc1, quant_clocks, maxclock), j)
      == AI.get_idx(AI.filter_capture(r, cap_regs, cap_clocks, lc2, quant_clocks, maxclock), j)
    decreases r
  {
    match r
    case Re_empty => case Re_character(_) => case Re_anchor(_) =>
    case Re_alt(r1, r2) =>
      var Y1 := AI.filter_capture(r1, cap_regs, cap_clocks, lc1, quant_clocks, maxclock);
      var Y2 := AI.filter_capture(r1, cap_regs, cap_clocks, lc2, quant_clocks, maxclock);
      FilterCaptureLookIndep(r1, cap_regs, cap_clocks, lc1, lc2, quant_clocks, maxclock);  // Y1~Y2 outside W(r1)
      FilterCaptureLookIndep(r2, Y2, cap_clocks, lc1, lc2, quant_clocks, maxclock);        // outside W(r2)
      forall j | j !in CaptureRegsSet(CapIdsInLooks(r))
        ensures AI.get_idx(AI.filter_capture(r2, Y1, cap_clocks, lc1, quant_clocks, maxclock), j)
             == AI.get_idx(AI.filter_capture(r2, Y2, cap_clocks, lc2, quant_clocks, maxclock), j)
      {
        CaptureRegsSetMono(CapIdsInLooks(r1), CapIdsInLooks(r));
        CaptureRegsSetMono(CapIdsInLooks(r2), CapIdsInLooks(r));
        assert AI.get_idx(Y1, j) == AI.get_idx(Y2, j);
        FilterCaptureCrPointwise(r2, Y1, Y2, cap_clocks, lc1, quant_clocks, maxclock, j);
      }
    case Re_con(r1, r2) =>
      var Y1 := AI.filter_capture(r1, cap_regs, cap_clocks, lc1, quant_clocks, maxclock);
      var Y2 := AI.filter_capture(r1, cap_regs, cap_clocks, lc2, quant_clocks, maxclock);
      FilterCaptureLookIndep(r1, cap_regs, cap_clocks, lc1, lc2, quant_clocks, maxclock);
      FilterCaptureLookIndep(r2, Y2, cap_clocks, lc1, lc2, quant_clocks, maxclock);
      forall j | j !in CaptureRegsSet(CapIdsInLooks(r))
        ensures AI.get_idx(AI.filter_capture(r2, Y1, cap_clocks, lc1, quant_clocks, maxclock), j)
             == AI.get_idx(AI.filter_capture(r2, Y2, cap_clocks, lc2, quant_clocks, maxclock), j)
      {
        CaptureRegsSetMono(CapIdsInLooks(r1), CapIdsInLooks(r));
        CaptureRegsSetMono(CapIdsInLooks(r2), CapIdsInLooks(r));
        assert AI.get_idx(Y1, j) == AI.get_idx(Y2, j);
        FilterCaptureCrPointwise(r2, Y1, Y2, cap_clocks, lc1, quant_clocks, maxclock, j);
      }
    case Re_quant(_, qid, _, r1) =>
      // CapIdsInLooks(quant)==CapIdsInLooks(r1); branch depends on quant clock, not lc.
      var qv := AI.get_idx(quant_clocks, qid);
      if qv < maxclock { /* both filter_all(r1, cap_regs): no lc read */ }
      else { FilterCaptureLookIndep(r1, cap_regs, cap_clocks, lc1, lc2, quant_clocks, qv); }
    case Re_capture(cid, r1) =>
      // CapIdsInLooks(capture)==CapIdsInLooks(r1); branch depends on start clock, not lc.
      var start := AI.get_idx(cap_clocks, CP.start_reg(cid));
      if start < 0 { /* both filter_all(r1, cap_regs) */ }
      else if start < maxclock { /* both filter_all(r1, set_idx(cap_regs, start_reg(cid), -1)) */ }
      else { FilterCaptureLookIndep(r1, cap_regs, cap_clocks, lc1, lc2, quant_clocks, maxclock); }
    case Re_lookaround(lid, la, r1) =>
      NR.PlusIsLookBehindFragmentRE(r1);
      forall j | j !in CaptureRegsSet(CapIdsInLooks(r))   // W == CaptureRegsSet(CapIds(r1))
        ensures AI.get_idx(AI.filter_capture(r, cap_regs, cap_clocks, lc1, quant_clocks, maxclock), j)
             == AI.get_idx(AI.filter_capture(r, cap_regs, cap_clocks, lc2, quant_clocks, maxclock), j)
      {
        assert forall cid: nat :: cid in CapIds(r1) ==> CP.start_reg(cid) != j by {
          forall cid: nat | cid in CapIds(r1) ensures CP.start_reg(cid) != j { StartRegInCaptureRegsSet(CapIds(r1), cid); }
        }
        LkValAtNonStart(lid, la, r1, cap_regs, cap_clocks, lc1, quant_clocks, maxclock, j);
        LkValAtNonStart(lid, la, r1, cap_regs, cap_clocks, lc2, quant_clocks, maxclock, j);
      }
  }

  /** THE consequence: on OUTSIDE-look groups, `GmOfLive` — and so
      `ThreadTracksGm` — is independent of the look register bank, so a
      `CheckOracle` pass's `look_regs` write cannot disturb their denotation.
      L3a: inside-look groups DO depend on the look bank (a matched look keeps its
      body captures); those are handled by the value-lift / P2, not here. */
  lemma GmOfLiveLookIndep(ast: R.regex, caps: AReg.Regs, look1: AReg.Regs, look2: AReg.Regs,
                          quant: AReg.Regs)
    requires NR.LookBehindFragmentRE(ast)
    ensures forall g: nat :: g !in CapIdsInLooks(ast) ==>
      ((g in GmOfLive(ast, caps, look1, quant)) <==> (g in GmOfLive(ast, caps, look2, quant)))
      && (g in GmOfLive(ast, caps, look1, quant) ==>
          GmOfLive(ast, caps, look1, quant)[g] == GmOfLive(ast, caps, look2, quant)[g])
  {
    var (cap_regs, cap_clocks) := AReg.as_arrays(caps);
    var lc1 := AReg.as_arrays(look1).1;
    var lc2 := AReg.as_arrays(look2).1;
    var qc := AReg.as_arrays(quant).1;
    var W := CaptureRegsSet(CapIdsInLooks(ast));
    FilterCaptureLookIndep(ast, cap_regs, cap_clocks, lc1, lc2, qc, -1);
    var f1 := AI.filter_reset(ast, caps, look1, quant, -1);
    var f2 := AI.filter_reset(ast, caps, look2, quant, -1);
    assert f1 == AI.filter_capture(ast, cap_regs, cap_clocks, lc1, qc, -1);
    assert f2 == AI.filter_capture(ast, cap_regs, cap_clocks, lc2, qc, -1);
    forall g: nat | g !in CapIdsInLooks(ast)
      ensures ((g in GmOfLive(ast, caps, look1, quant)) <==> (g in GmOfLive(ast, caps, look2, quant)))
           && (g in GmOfLive(ast, caps, look1, quant) ==>
               GmOfLive(ast, caps, look1, quant)[g] == GmOfLive(ast, caps, look2, quant)[g])
    {
      StartRegInCaptureRegsSet(CapIdsInLooks(ast), g);
      EndRegInCaptureRegsSet(CapIdsInLooks(ast), g);
      assert CP.start_reg(g) !in W && CP.end_reg(g) !in W;
      assert AI.get_idx(f1, CP.start_reg(g)) == AI.get_idx(f2, CP.start_reg(g));
      assert AI.get_idx(f1, CP.end_reg(g)) == AI.get_idx(f2, CP.end_reg(g));
    }
  }

  // On a properly closed match (every present group with a set end has
  // end_clock >= start_clock), the live denotation coincides with GmOf — so the
  // final answer, extracted via GmOf + GmOfCapArrayBridge, is unaffected.
  /** On a properly closed match (every present group with a set end has
      `end_clock >= start_clock`), `GmOfLive` coincides with `GmOf` — so the
      final answer, extracted via `GmOf`/`GmOfCapArrayBridge`, is unaffected. */
  lemma GmOfLiveEqGmOf(ast: R.regex, caps: AReg.Regs, look: AReg.Regs, quant: AReg.Regs)
    requires var f := AI.filter_reset(ast, caps, look, quant, -1);
             var cc := AReg.as_arrays(caps).1;
      forall g: nat :: 0 <= g < |f| && AI.get_idx(f, CP.start_reg(g)) >= 0
                       && AI.get_idx(f, CP.end_reg(g)) >= 0
        ==> AI.get_idx(cc, CP.end_reg(g)) >= AI.get_idx(cc, CP.start_reg(g))
    ensures GmOfLive(ast, caps, look, quant) == GmOf(ast, caps, look, quant)
  {
    var f := AI.filter_reset(ast, caps, look, quant, -1);
    var cc := AReg.as_arrays(caps).1;
    assert forall g: nat :: (0 <= g < |f| && AI.get_idx(f, CP.start_reg(g)) >= 0)
                            ==> LiveRange(f, cc, g) == RangeFromArr(f, g);
  }

  // ===========================================================================
  // gm-effect lemma for GMClose. Writing group gid's END register (an odd
  // index) to code point cp at clock clk closes gid in the live denotation:
  // domain unchanged, every other group unchanged, gid's range becomes
  // Range(start, Some(cp)). Mirrors Linden's GMClose. The clock precondition
  // (new end clock >= gid's start clock) is the clock-monotonicity fact that a
  // thread invariant will supply; here it makes the closed end "live".
  // ===========================================================================
  /** gm-effect lemma for GMClose (present case): writing `gid`'s END register
      to `cp` at clock `clk >= gid`'s start clock closes `gid` in the live
      denotation — domain unchanged, `gid`'s range becomes `Range(start,
      Some(cp))`, every other group unchanged. Mirrors Linden's `GMClose`. */
  lemma GmOfLiveClose(ast: R.regex, caps: AReg.Regs, look: AReg.Regs, quant: AReg.Regs,
                      gid: nat, cp: int, clk: int)
    requires |caps.a_cp| == |caps.a_clk|
    requires CP.end_reg(gid) < |caps.a_cp|
    requires cp >= 0
    requires AI.get_idx(AI.filter_reset(ast, caps, look, quant, -1), CP.start_reg(gid)) >= 0
    requires clk >= AI.get_idx(caps.a_clk, CP.start_reg(gid))
    ensures gid in GmOfLive(ast, caps, look, quant)
    ensures GmOfLive(ast, AReg.set_reg(caps, CP.end_reg(gid), Some(cp), clk), look, quant)
         == GmOfLive(ast, caps, look, quant)
            [gid := LG.Range(GmOfLive(ast, caps, look, quant)[gid].startIdx, Some(cp as nat))]
  {
    var caps' := AReg.set_reg(caps, CP.end_reg(gid), Some(cp), clk);
    var (cr, cc) := AReg.as_arrays(caps);
    var (cr', cc') := AReg.as_arrays(caps');
    var (_, lc) := AReg.as_arrays(look);
    var (_, qc) := AReg.as_arrays(quant);
    // set_reg at an in-range index unfolds to a single-index update.
    assert cr' == cr[CP.end_reg(gid) := cp];
    assert cc' == cc[CP.end_reg(gid) := clk];
    var f := AI.filter_capture(ast, cr, cc, lc, qc, -1);
    var f' := AI.filter_capture(ast, cr', cc', lc, qc, -1);
    assert f == AI.filter_reset(ast, caps, look, quant, -1);
    assert f' == AI.filter_reset(ast, caps', look, quant, -1);
    FilterCaptureLen(ast, cr, cc, lc, qc, -1);
    FilterCaptureLen(ast, cr', cc', lc, qc, -1);
    // parity: start regs even, end regs odd
    assert CP.end_reg(gid) % 2 == 1;
    assert CP.start_reg(gid) % 2 == 0;
    // cr,cr' and cc,cc' agree on every EVEN index (they differ only at the odd
    // end_reg(gid)), so f,f' agree on every even output index.
    assert forall i :: 0 <= i < |cr| && i % 2 == 0 ==> cr[i] == cr'[i];
    assert forall i :: i % 2 == 0 ==> AI.get_idx(cc, i) == AI.get_idx(cc', i);
    FilterCaptureEvenFrame(ast, cr, cr', cc, cc', lc, qc, -1);
    assert gid < |f|;

    var g0 := GmOfLive(ast, caps, look, quant);
    var g1 := GmOfLive(ast, caps', look, quant);
    var target := g0[gid := LG.Range(g0[gid].startIdx, Some(cp as nat))];

    // g0 and g1 share the same domain (start values agree on even indices).
    forall k: nat ensures (k in g0) <==> (k in g1) {
      assert CP.start_reg(k) % 2 == 0;
    }
    assert g0.Keys == g1.Keys;

    // Per-key value equality.
    forall k: nat | k in g1 ensures g1[k] == target[k] {
      assert CP.start_reg(k) % 2 == 0;
      assert CP.end_reg(k) % 2 == 1;
      FilterCaptureKeepsOdd(ast, cr, cc, lc, qc, -1, CP.end_reg(k));
      FilterCaptureKeepsOdd(ast, cr', cc', lc, qc, -1, CP.end_reg(k));
      if k == gid {
        // end value becomes cp, end clock becomes clk >= start clock ⇒ live.
        assert AI.get_idx(f', CP.end_reg(k)) == cp;
        assert AI.get_idx(cc', CP.end_reg(k)) == clk;
        assert AI.get_idx(cc', CP.start_reg(k)) == AI.get_idx(cc, CP.start_reg(k));
      } else {
        // gid ≠ k ⇒ end_reg(k) ≠ end_reg(gid): gid's write is invisible to k.
        assert CP.end_reg(k) != CP.end_reg(gid);
        assert CP.start_reg(k) != CP.end_reg(gid);
        assert AI.get_idx(cr', CP.end_reg(k)) == AI.get_idx(cr, CP.end_reg(k));
        assert AI.get_idx(cc', CP.end_reg(k)) == AI.get_idx(cc, CP.end_reg(k));
        assert AI.get_idx(cc', CP.start_reg(k)) == AI.get_idx(cc, CP.start_reg(k));
      }
    }
    assert g1 == target;
  }

  // ===========================================================================
  // Close-case completion: bounds and the absent case, giving a total interface
  // GmOfLiveCloseGMClose that matches Linden's GMClose with NO positional
  // hypotheses (only backbone facts: value bound <= cp, clock bound <= clk).
  // ===========================================================================

  // Filter outputs never exceed an input bound: every output value is either
  // the input value at that index or -1.
  /** `filter_all` never exceeds an input bound: every output value is the input
      at that index or `-1`. */
  lemma FilterAllLE(r: R.regex, regs: seq<int>, i: int, B: int)
    requires B >= -1
    requires AI.get_idx(regs, i) <= B
    ensures AI.get_idx(AI.filter_all(r, regs), i) <= B
    decreases r
  {
    match r
    case Re_empty => case Re_character(_) => case Re_anchor(_) =>
    case Re_alt(r1, r2) => FilterAllLE(r1, regs, i, B); FilterAllLE(r2, AI.filter_all(r1, regs), i, B);
    case Re_con(r1, r2) => FilterAllLE(r1, regs, i, B); FilterAllLE(r2, AI.filter_all(r1, regs), i, B);
    case Re_quant(_, _, _, r1) => FilterAllLE(r1, regs, i, B);
    case Re_capture(cid, r1) =>
      var regs2 := AI.set_idx(regs, CP.start_reg(cid), -1);
      assert AI.get_idx(regs2, i) <= B by {
        if i != CP.start_reg(cid) { SetIdxKeepsOther(regs, CP.start_reg(cid), i); }
      }
      FilterAllLE(r1, regs2, i, B);
    case Re_lookaround(_, _, r1) => FilterAllLE(r1, regs, i, B);
  }

  /** `filter_capture` never exceeds an input bound (the `filter_capture` analog
      of `FilterAllLE`). */
  lemma FilterCaptureLE(r: R.regex, cr: seq<int>, cc: seq<int>, lc: seq<int>, qc: seq<int>,
                        mx: int, i: int, B: int)
    requires B >= -1
    requires AI.get_idx(cr, i) <= B
    ensures AI.get_idx(AI.filter_capture(r, cr, cc, lc, qc, mx), i) <= B
    decreases r
  {
    match r
    case Re_empty => case Re_character(_) => case Re_anchor(_) =>
    case Re_alt(r1, r2) =>
      FilterCaptureLE(r1, cr, cc, lc, qc, mx, i, B);
      FilterCaptureLE(r2, AI.filter_capture(r1, cr, cc, lc, qc, mx), cc, lc, qc, mx, i, B);
    case Re_con(r1, r2) =>
      FilterCaptureLE(r1, cr, cc, lc, qc, mx, i, B);
      FilterCaptureLE(r2, AI.filter_capture(r1, cr, cc, lc, qc, mx), cc, lc, qc, mx, i, B);
    case Re_quant(nul, qid, q, r1) =>
      var qv := AI.get_idx(qc, qid);
      if qv < mx { FilterAllLE(r1, cr, i, B); }
      else { FilterCaptureLE(r1, cr, cc, lc, qc, qv, i, B); }
    case Re_capture(cid, r1) =>
      var start := AI.get_idx(cc, CP.start_reg(cid));
      if start < 0 { FilterAllLE(r1, cr, i, B); }
      else if start < mx {
        var cr2 := AI.set_idx(cr, CP.start_reg(cid), -1);
        assert AI.get_idx(cr2, i) <= B by {
          if i != CP.start_reg(cid) { SetIdxKeepsOther(cr, CP.start_reg(cid), i); }
        }
        FilterAllLE(r1, cr2, i, B);
      } else {
        FilterCaptureLE(r1, cr, cc, lc, qc, mx, i, B);
      }
    case Re_lookaround(lid, l, r1) =>
      var lv := AI.get_idx(lc, lid);
      if lv < 0 { FilterAllLE(r1, cr, i, B); }
      else if lv < mx { FilterAllLE(r1, cr, i, B); }
      else { FilterCaptureLE(r1, cr, cc, lc, qc, -1, i, B); }
  }

  // Every present group's recorded start position is bounded by the capture-
  // value bound (VmCapsLE's per-thread fact) -- GMClose's normal-case guard.
  /** Every present group's recorded start position is bounded by the capture-
      value bound (`VmCapsLE`'s per-thread fact) — GMClose's normal-case guard. */
  lemma GmOfLiveStartIdxLE(ast: R.regex, caps: AReg.Regs, look: AReg.Regs, quant: AReg.Regs, B: int)
    requires B >= -1
    requires forall k :: AI.get_idx(caps.a_cp, k) <= B
    ensures forall g: nat :: g in GmOfLive(ast, caps, look, quant)
              ==> GmOfLive(ast, caps, look, quant)[g].startIdx as int <= B
  {
    var f := AI.filter_reset(ast, caps, look, quant, -1);
    var (cr, cc) := AReg.as_arrays(caps);
    var (_, lc) := AReg.as_arrays(look);
    var (_, qc) := AReg.as_arrays(quant);
    forall g: nat | g in GmOfLive(ast, caps, look, quant)
      ensures GmOfLive(ast, caps, look, quant)[g].startIdx as int <= B
    {
      FilterCaptureLE(ast, cr, cc, lc, qc, -1, CP.start_reg(g), B);
    }
  }

  // Writing an ABSENT group's end register leaves the live denotation unchanged
  // (the filter never reads end registers or end clocks; gid stays absent; all
  // other groups' indices are untouched). Matches GMClose's None branch.
  /** Writing an ABSENT group's end register leaves the live denotation
      unchanged (the filter never reads end registers; `gid` stays absent).
      Matches GMClose's `None` branch. */
  lemma GmOfLiveCloseAbsent(ast: R.regex, caps: AReg.Regs, look: AReg.Regs, quant: AReg.Regs,
                            gid: nat, cp: int, clk: int)
    requires AI.get_idx(AI.filter_reset(ast, caps, look, quant, -1), CP.start_reg(gid)) < 0
    ensures GmOfLive(ast, AReg.set_reg(caps, CP.end_reg(gid), Some(cp), clk), look, quant)
         == GmOfLive(ast, caps, look, quant)
  {
    var caps' := AReg.set_reg(caps, CP.end_reg(gid), Some(cp), clk);
    if !(0 <= CP.end_reg(gid) < |caps.a_cp| && 0 <= CP.end_reg(gid) < |caps.a_clk|) {
      assert caps' == caps;
      return;
    }
    var (cr, cc) := AReg.as_arrays(caps);
    var (cr', cc') := AReg.as_arrays(caps');
    var (_, lc) := AReg.as_arrays(look);
    var (_, qc) := AReg.as_arrays(quant);
    assert cr' == cr[CP.end_reg(gid) := cp];
    assert cc' == cc[CP.end_reg(gid) := clk];
    var f := AI.filter_capture(ast, cr, cc, lc, qc, -1);
    var f' := AI.filter_capture(ast, cr', cc', lc, qc, -1);
    assert f == AI.filter_reset(ast, caps, look, quant, -1);
    assert f' == AI.filter_reset(ast, caps', look, quant, -1);
    FilterCaptureLen(ast, cr, cc, lc, qc, -1);
    FilterCaptureLen(ast, cr', cc', lc, qc, -1);
    assert CP.end_reg(gid) % 2 == 1;
    // Only the odd index end_reg(gid) differs, so even outputs agree.
    assert forall i :: 0 <= i < |cr| && i % 2 == 0 ==> cr[i] == cr'[i];
    assert forall i :: i % 2 == 0 ==> AI.get_idx(cc, i) == AI.get_idx(cc', i);
    FilterCaptureEvenFrame(ast, cr, cr', cc, cc', lc, qc, -1);

    var g0 := GmOfLive(ast, caps, look, quant);
    var g1 := GmOfLive(ast, caps', look, quant);

    forall k: nat ensures (k in g0) <==> (k in g1) {
      assert CP.start_reg(k) % 2 == 0;
    }
    assert g0.Keys == g1.Keys;

    forall k: nat | k in g1 ensures g1[k] == g0[k] {
      assert CP.start_reg(k) % 2 == 0;
      assert CP.end_reg(k) % 2 == 1;
      FilterCaptureKeepsOdd(ast, cr, cc, lc, qc, -1, CP.end_reg(k));
      FilterCaptureKeepsOdd(ast, cr', cc', lc, qc, -1, CP.end_reg(k));
      // k ≠ gid (gid is absent), so gid's end write is invisible to k.
      assert k != gid;
      assert CP.end_reg(k) != CP.end_reg(gid);
      assert CP.start_reg(k) != CP.end_reg(gid);
      assert AI.get_idx(cr', CP.end_reg(k)) == AI.get_idx(cr, CP.end_reg(k));
      assert AI.get_idx(cc', CP.end_reg(k)) == AI.get_idx(cc, CP.end_reg(k));
      assert AI.get_idx(cc', CP.start_reg(k)) == AI.get_idx(cc, CP.start_reg(k));
    }
    assert g1 == g0;
  }

  // The TOTAL Close interface: writing gid's end register mirrors Linden's
  // GMClose exactly, in both the present and absent cases. All hypotheses are
  // backbone facts (register wf, value bound <= cp, clock bound < clk) -- the
  // Close case of the simulation induction needs NO positional invariant.
  /** The TOTAL Close interface: writing `gid`'s end register mirrors Linden's
      `GMClose` exactly in both present and absent cases. All hypotheses are
      backbone facts (register wf, value bound `<= cp`, clock bound `<= clk`) —
      the Close case of the simulation needs NO positional invariant. */
  lemma GmOfLiveCloseGMClose(ast: R.regex, caps: AReg.Regs, look: AReg.Regs, quant: AReg.Regs,
                             gid: nat, cp: int, clk: int)
    requires |caps.a_cp| == |caps.a_clk|
    requires CP.end_reg(gid) < |caps.a_cp|
    requires cp >= 0
    requires forall k :: AI.get_idx(caps.a_cp, k) <= cp     // VmCapsLE at this thread
    requires forall k :: AI.get_idx(caps.a_clk, k) <= clk   // clock backbone at this thread
    ensures GmOfLive(ast, AReg.set_reg(caps, CP.end_reg(gid), Some(cp), clk), look, quant)
         == LG.GMClose(cp as nat, gid, GmOfLive(ast, caps, look, quant))
  {
    var gm := GmOfLive(ast, caps, look, quant);
    var f := AI.filter_reset(ast, caps, look, quant, -1);
    var (cr, cc) := AReg.as_arrays(caps);
    var (_, lc) := AReg.as_arrays(look);
    var (_, qc) := AReg.as_arrays(quant);
    FilterCaptureLen(ast, cr, cc, lc, qc, -1);
    if AI.get_idx(f, CP.start_reg(gid)) >= 0 {
      // PRESENT: GMClose's normal branch (startIdx <= cp by the value bound).
      assert gid < |f|;
      assert gid in gm;
      GmOfLiveStartIdxLE(ast, caps, look, quant, cp);
      assert gm[gid].startIdx as int <= cp;
      GmOfLiveClose(ast, caps, look, quant, gid, cp, clk);
      assert LG.GMClose(cp as nat, gid, gm)
          == gm[gid := LG.Range(gm[gid].startIdx, Some(cp as nat))];
    } else {
      // ABSENT: both sides are the identity.
      assert gid !in gm;
      GmOfLiveCloseAbsent(ast, caps, look, quant, gid, cp, clk);
      assert LG.GMClose(cp as nat, gid, gm) == gm;
    }
  }

  // ===========================================================================
  // gm-effect lemma for GMOpen. Writing group gid's START register (an even
  // index) to code point cp at a FRESH clock clk opens gid in the live
  // denotation: gid becomes present as Range(cp, None) (its stale end is read as
  // None because the fresh start clock exceeds the stale end clock), every other
  // group unchanged. Mirrors Linden's GMOpen.
  //
  // The `no-exposure` precondition is the deferred-reset proof obligation:
  // opening gid perturbs the reset resolution ONLY at gid's own start register.
  // In preservation it is discharged from clock monotonicity — the enclosing
  // star's SetQuantToClock(qid,false), executed at the top of THIS iteration,
  // stamped a clock exceeding every prior-iteration subgroup clock, so filter
  // already resets gid's subgroups and opening gid exposes none of them.
  // ===========================================================================
  /** gm-effect lemma for GMOpen: writing `gid`'s START register to `cp` at a
      FRESH clock opens `gid` as `Range(cp, None)` (its stale end reads `None`
      because the fresh start clock beats the stale end clock), every other
      group unchanged. Mirrors Linden's `GMOpen`. The `no-exposure` precondition
      is the deferred-reset obligation, discharged from clock monotonicity. */
  lemma GmOfLiveOpen(ast: R.regex, caps: AReg.Regs, look: AReg.Regs, quant: AReg.Regs,
                     gid: nat, cp: int, clk: int)
    requires |caps.a_cp| == |caps.a_clk|
    requires CP.start_reg(gid) < |caps.a_cp|
    requires cp >= 0
    requires clk > AI.get_idx(caps.a_clk, CP.end_reg(gid))   // fresh start clk beats stale end
    requires
      var f  := AI.filter_reset(ast, caps, look, quant, -1);
      var f' := AI.filter_reset(ast, AReg.set_reg(caps, CP.start_reg(gid), Some(cp), clk), look, quant, -1);
      AI.get_idx(f, CP.start_reg(gid)) < 0
      && AI.get_idx(f', CP.start_reg(gid)) == cp
      && (forall j :: j != CP.start_reg(gid) ==> AI.get_idx(f', j) == AI.get_idx(f, j))
    ensures gid !in GmOfLive(ast, caps, look, quant)
    ensures GmOfLive(ast, AReg.set_reg(caps, CP.start_reg(gid), Some(cp), clk), look, quant)
         == GmOfLive(ast, caps, look, quant)[gid := LG.Range(cp as nat, None)]
  {
    var caps' := AReg.set_reg(caps, CP.start_reg(gid), Some(cp), clk);
    var (cr, cc) := AReg.as_arrays(caps);
    var (cr', cc') := AReg.as_arrays(caps');
    var (_, lc) := AReg.as_arrays(look);
    var (_, qc) := AReg.as_arrays(quant);
    assert cr' == cr[CP.start_reg(gid) := cp];
    assert cc' == cc[CP.start_reg(gid) := clk];
    var f := AI.filter_reset(ast, caps, look, quant, -1);
    var f' := AI.filter_reset(ast, caps', look, quant, -1);
    FilterCaptureLen(ast, cr, cc, lc, qc, -1);
    FilterCaptureLen(ast, cr', cc', lc, qc, -1);
    assert CP.start_reg(gid) % 2 == 0;
    assert gid < |f|;

    var g0 := GmOfLive(ast, caps, look, quant);
    var g1 := GmOfLive(ast, caps', look, quant);
    var target := g0[gid := LG.Range(cp as nat, None)];

    // gid absent before (its filtered start value was < 0).
    assert gid !in g0;

    // Domains: g1 = g0's domain ∪ {gid}. For gid' ≠ gid the start value is
    // unchanged (no-exposure); gid itself is newly present at cp ≥ 0.
    forall k: nat ensures (k in g1) <==> (k in target) {
      assert CP.start_reg(k) % 2 == 0;
      if k != gid { assert CP.start_reg(k) != CP.start_reg(gid); }
    }
    assert g1.Keys == target.Keys;

    forall k: nat | k in g1 ensures g1[k] == target[k] {
      assert CP.start_reg(k) % 2 == 0;
      assert CP.end_reg(k) % 2 == 1;
      if k == gid {
        // start becomes cp at fresh clk; stale end clock < clk ⇒ end reads None.
        assert AI.get_idx(f', CP.start_reg(gid)) == cp;
        assert AI.get_idx(cc', CP.start_reg(gid)) == clk;
        assert CP.end_reg(gid) != CP.start_reg(gid);
        assert AI.get_idx(f', CP.end_reg(gid)) == AI.get_idx(f, CP.end_reg(gid));
        assert AI.get_idx(cc', CP.end_reg(gid)) == AI.get_idx(cc, CP.end_reg(gid));
        assert AI.get_idx(cc', CP.end_reg(gid)) < clk;   // freshness ⇒ end not live
      } else {
        // gid's single even write is invisible to every other group.
        assert CP.start_reg(k) != CP.start_reg(gid);
        assert CP.end_reg(k) != CP.start_reg(gid);
        assert AI.get_idx(f', CP.start_reg(k)) == AI.get_idx(f, CP.start_reg(k));
        assert AI.get_idx(f', CP.end_reg(k)) == AI.get_idx(f, CP.end_reg(k));
        assert AI.get_idx(cc', CP.start_reg(k)) == AI.get_idx(cc, CP.start_reg(k));
        assert AI.get_idx(cc', CP.end_reg(k)) == AI.get_idx(cc, CP.end_reg(k));
      }
    }
    assert g1 == target;
  }

  // GmOfLiveOpen with the no-exposure precondition DISCHARGED by FilterOpenFrame.
  // Now the obligations are clean structural + clock predicates (PathPresent,
  // clk ≥ MxAtGid, body-staleness, register wf) that the preservation induction's
  // clock-monotonicity invariant supplies — no opaque filter statement required.
  /** `GmOfLiveOpen` with the no-exposure precondition DISCHARGED by
      `FilterOpenFrame`: the obligations become clean structural + clock
      predicates (`PathPresent`, `clk >= MxAtGid`, body-staleness, register wf)
      that the preservation induction's clock-monotonicity invariant supplies. */
  lemma GmOfLiveOpenFull(ast: R.regex, caps: AReg.Regs, look: AReg.Regs, quant: AReg.Regs,
                         gid: nat, cp: int, clk: int)
    requires |caps.a_cp| == |caps.a_clk|
    requires CP.start_reg(gid) < |caps.a_cp|
    requires cp >= 0 && clk >= 0
    requires clk > AI.get_idx(caps.a_clk, CP.end_reg(gid))
    requires NR.LookBehindFragmentRE(ast) && CapUnique(ast) && gid in CapIds(ast)
    requires gid !in CapIdsInLooks(ast)   // L3a: Open fires for outside-look gids
    // gid's start register is UNSET or STALE relative to the enclosing star's
    // stamp — covers both the first open and a star re-entry (RegElk never
    // clears registers; staleness lives in the filter).
    requires AI.get_idx(caps.a_clk, CP.start_reg(gid))
               < MxAtGid(ast, caps.a_clk, AReg.as_arrays(quant).1, -1, gid)
          || AI.get_idx(caps.a_clk, CP.start_reg(gid)) < 0
    requires clk >= MxAtGid(ast, caps.a_clk, AReg.as_arrays(quant).1, -1, gid)
    requires PathPresent(ast, caps.a_clk, AReg.as_arrays(quant).1, -1, gid)
    requires forall k :: AI.get_idx(caps.a_cp, k) >= -1
    requires forall c: nat :: c in CapIds(ast) && AI.get_idx(caps.a_clk, CP.start_reg(c)) < 0
                             ==> AI.get_idx(caps.a_cp, CP.start_reg(c)) < 0
    requires forall sg: nat :: sg in CapIds(BodyOf(ast, gid))
                              ==> AI.get_idx(caps.a_clk, CP.start_reg(sg)) < MxAtGid(ast, caps.a_clk, AReg.as_arrays(quant).1, -1, gid)
                                  || AI.get_idx(caps.a_clk, CP.start_reg(sg)) < 0
    requires LooksCapUnset(BodyOf(ast, gid), caps.a_clk)
    ensures gid !in GmOfLive(ast, caps, look, quant)
    ensures GmOfLive(ast, AReg.set_reg(caps, CP.start_reg(gid), Some(cp), clk), look, quant)
         == GmOfLive(ast, caps, look, quant)[gid := LG.Range(cp as nat, None)]
  {
    var caps' := AReg.set_reg(caps, CP.start_reg(gid), Some(cp), clk);
    var (cr, cc) := AReg.as_arrays(caps);
    var (cr', cc') := AReg.as_arrays(caps');
    var (_, lc) := AReg.as_arrays(look);
    var (_, qc) := AReg.as_arrays(quant);
    assert cr' == cr[CP.start_reg(gid) := cp];
    assert cc' == cc[CP.start_reg(gid) := clk];
    // Relational hypotheses of FilterOpenFrame (agree off start_reg(gid)).
    forall j | j != CP.start_reg(gid) ensures AI.get_idx(cr', j) == AI.get_idx(cr, j) {}
    forall j | j != CP.start_reg(gid) ensures AI.get_idx(cc', j) == AI.get_idx(cc, j) {}
    forall k ensures AI.get_idx(cr', k) >= -1 {}
    forall c: nat | c in CapIds(ast) && AI.get_idx(cc', CP.start_reg(c)) < 0
      ensures AI.get_idx(cr', CP.start_reg(c)) < 0 {
      if c == gid {} else { assert CP.start_reg(c) != CP.start_reg(gid); }
    }
    FilterOpenFrame(ast, cr, cr', cc, cc', lc, qc, -1, gid, cp, clk);
    GmOfLiveOpen(ast, caps, look, quant, gid, cp, clk);
  }

  // The Open interface phrased against Linden's GMOpen (same hypotheses as
  // GmOfLiveOpenFull; GMOpen is the unguarded update, so the conclusion is a
  // direct restatement). The induction's Open case calls this.
  /** The Open interface phrased against Linden's `GMOpen` (same hypotheses as
      `GmOfLiveOpenFull`) — the induction's Open case calls this. */
  lemma GmOfLiveOpenGMOpen(ast: R.regex, caps: AReg.Regs, look: AReg.Regs, quant: AReg.Regs,
                           gid: nat, cp: int, clk: int)
    requires |caps.a_cp| == |caps.a_clk|
    requires CP.start_reg(gid) < |caps.a_cp|
    requires cp >= 0 && clk >= 0
    requires clk > AI.get_idx(caps.a_clk, CP.end_reg(gid))
    requires NR.LookBehindFragmentRE(ast) && CapUnique(ast) && gid in CapIds(ast)
    requires gid !in CapIdsInLooks(ast)   // L3a: Open fires for outside-look gids
    requires AI.get_idx(caps.a_clk, CP.start_reg(gid))
               < MxAtGid(ast, caps.a_clk, AReg.as_arrays(quant).1, -1, gid)
          || AI.get_idx(caps.a_clk, CP.start_reg(gid)) < 0
    requires clk >= MxAtGid(ast, caps.a_clk, AReg.as_arrays(quant).1, -1, gid)
    requires PathPresent(ast, caps.a_clk, AReg.as_arrays(quant).1, -1, gid)
    requires forall k :: AI.get_idx(caps.a_cp, k) >= -1
    requires forall c: nat :: c in CapIds(ast) && AI.get_idx(caps.a_clk, CP.start_reg(c)) < 0
                             ==> AI.get_idx(caps.a_cp, CP.start_reg(c)) < 0
    requires forall sg: nat :: sg in CapIds(BodyOf(ast, gid))
                              ==> AI.get_idx(caps.a_clk, CP.start_reg(sg)) < MxAtGid(ast, caps.a_clk, AReg.as_arrays(quant).1, -1, gid)
                                  || AI.get_idx(caps.a_clk, CP.start_reg(sg)) < 0
    requires LooksCapUnset(BodyOf(ast, gid), caps.a_clk)
    ensures GmOfLive(ast, AReg.set_reg(caps, CP.start_reg(gid), Some(cp), clk), look, quant)
         == LG.GMOpen(cp as nat, gid, GmOfLive(ast, caps, look, quant))
  {
    GmOfLiveOpenFull(ast, caps, look, quant, gid, cp, clk);
  }

  // ===========================================================================
  // FilterResetFrame — the reset-scope discharge (GMReset analog of
  // FilterOpenFrame). Stamping qid's quant clock to a fresh clk drives filter_
  // capture to reset EXACTLY qid's body captures gl = CapIds(QidBody(r,qid))
  // (their starts go negative) and leaves every other position unchanged. At
  // qid's node filter_capture(body, clk) degenerates to filter_all(body) (body
  // all-stale vs clk), which clears gl (FilterAllClearsStart); off gl the old
  // filter_capture(body, old) agrees with filter_all(body) (FilterCaptureVsAll);
  // the descent frames the rest via QcFrame + CrPointwise + Outside. Per-j.
  // ===========================================================================
  /** The reset-scope discharge (the GMReset analog of `FilterOpenFrame`):
      stamping `qid`'s quant clock to a fresh `clk` drives `filter_capture` to
      reset EXACTLY `qid`'s body captures `CapIds(QidBody(r,qid))` (their starts
      go negative) and leaves every other position unchanged. Stated per-`j`. */
  lemma FilterResetFrame(r: R.regex, A: seq<int>, cc: seq<int>, lc: seq<int>, qc: seq<int>, qc': seq<int>,
                         M: int, qid: nat, clk: int, j: int)
    requires NR.LookBehindFragmentRE(r) && CapUnique(r) && QuantUnique(r)
    requires qid in QuantIds(r)
    requires qid in QuantIdsOutsideLooks(r)   // L3a: reset frame is for outside-look quantifiers
    requires clk >= 0
    requires clk >= MxAtQid(r, cc, qc, M, qid)
    requires PathPresentQ(r, cc, qc, M, qid)
    requires forall q0: int :: q0 != qid ==> AI.get_idx(qc', q0) == AI.get_idx(qc, q0)
    requires AI.get_idx(qc', qid) == clk
    requires forall sg: nat :: sg in CapIds(QidBody(r, qid)) ==> AI.get_idx(cc, CP.start_reg(sg)) < clk
    // L3a: every lookaround inside qid's body is stale at the fresh reset stamp —
    // so a stale look never keeps captures the reset should clear.
    requires LooksCapUnset(QidBody(r, qid), cc)
    requires forall k :: AI.get_idx(A, k) >= -1
    requires forall c: nat :: c in CapIds(r) && AI.get_idx(cc, CP.start_reg(c)) < 0 ==> AI.get_idx(A, CP.start_reg(c)) < 0
    ensures (forall g: nat :: g in CapIds(QidBody(r, qid)) ==> CP.start_reg(g) != j)
            ==> AI.get_idx(AI.filter_capture(r, A, cc, lc, qc', M), j) == AI.get_idx(AI.filter_capture(r, A, cc, lc, qc, M), j)
    ensures (exists g: nat :: g in CapIds(QidBody(r, qid)) && CP.start_reg(g) == j)
            ==> AI.get_idx(AI.filter_capture(r, A, cc, lc, qc', M), j) < 0
    decreases r
  {
    match r
    case Re_lookaround(lid, la, r1) =>
      // qid is inside the look body, but the requires restricts to outside-look qids.
      assert qid in QuantIdsOutsideLooks(r);   // == {} for a lookaround node — contradiction
      assert false;
    case Re_capture(cid, r1) =>
      assert qid in QuantIds(r1);
      assert AI.get_idx(cc, CP.start_reg(cid)) >= M && AI.get_idx(cc, CP.start_reg(cid)) >= 0;  // PathPresentQ
      assert MxAtQid(r, cc, qc, M, qid) == MxAtQid(r1, cc, qc, M, qid);
      assert QidBody(r, qid) == QidBody(r1, qid);
      FilterResetFrame(r1, A, cc, lc, qc, qc', M, qid, clk, j);
    case Re_quant(nul, qid0, q, r1) =>
      if qid0 >= 0 && (qid0 as nat) == qid {
        // THE qid node. QidBody(r,qid) == r1 == body.
        assert QidBody(r, qid) == r1;
        assert MxAtQid(r, cc, qc, M, qid) == M;
        assert AI.get_idx(qc', qid0) == clk;
        var oldv := AI.get_idx(qc, qid0);
        // f' present branch (clk >= M) → filter_capture(r1, A, cc, qc', clk) == filter_all(r1, A).
        forall cidx: nat | cidx in CapIds(r1)
          ensures AI.get_idx(cc, CP.start_reg(cidx)) < clk || AI.get_idx(cc, CP.start_reg(cidx)) < 0 {}
        assert LooksCapUnset(r1, cc);   // == LooksCapUnset(QidBody(r,qid), cc) since QidBody(r,qid)==r1
        FilterCaptureAllStale(r1, A, cc, lc, qc', clk);
        // reset: any gl start is cleared by filter_all(r1, A).
        if exists g: nat :: g in CapIds(r1) && CP.start_reg(g) == j {
          var g: nat :| g in CapIds(r1) && CP.start_reg(g) == j;
          FilterAllClearsStart(r1, A, g);
        }
        // frame: off gl starts, the old filter agrees with filter_all(r1,A).
        if forall g: nat :: g in CapIds(r1) ==> CP.start_reg(g) != j {
          if oldv < M {} else { FilterCaptureVsAll(r1, A, cc, lc, qc, oldv, j); }
        }
      } else {
        assert qid in QuantIds(r1);
        var qv0 := AI.get_idx(qc, qid0);
        assert AI.get_idx(qc', qid0) == qv0;             // qid0 ≠ qid
        assert qv0 >= M;                                  // PathPresentQ
        assert MxAtQid(r, cc, qc, M, qid) == MxAtQid(r1, cc, qc, qv0, qid);
        assert QidBody(r, qid) == QidBody(r1, qid);
        FilterResetFrame(r1, A, cc, lc, qc, qc', qv0, qid, clk, j);
      }
    case Re_alt(r1, r2) => FilterResetFrameSeq(r, r1, r2, A, cc, lc, qc, qc', M, qid, clk, j);
    case Re_con(r1, r2) => FilterResetFrameSeq(r, r1, r2, A, cc, lc, qc, qc', M, qid, clk, j);
  }

  // Sequential (alt/con) handling for FilterResetFrame. Same filter structure:
  // thread A through r1, then r2. qid lives in one branch (QuantUnique).
  /** Sequential (`alt`/`con`) handling for `FilterResetFrame`: thread `A`
      through `r1` then `r2`; `qid` lives in exactly one branch (QuantUnique). */
  lemma FilterResetFrameSeq(r: R.regex, r1: R.regex, r2: R.regex, A: seq<int>, cc: seq<int>, lc: seq<int>,
                            qc: seq<int>, qc': seq<int>, M: int, qid: nat, clk: int, j: int)
    requires r == R.Re_alt(r1, r2) || r == R.Re_con(r1, r2)
    requires NR.LookBehindFragmentRE(r) && CapUnique(r) && QuantUnique(r)
    requires qid in QuantIds(r)
    requires qid in QuantIdsOutsideLooks(r)   // L3a: reset frame is for outside-look quantifiers
    requires clk >= 0
    requires clk >= MxAtQid(r, cc, qc, M, qid)
    requires PathPresentQ(r, cc, qc, M, qid)
    requires forall q0: int :: q0 != qid ==> AI.get_idx(qc', q0) == AI.get_idx(qc, q0)
    requires AI.get_idx(qc', qid) == clk
    requires forall sg: nat :: sg in CapIds(QidBody(r, qid)) ==> AI.get_idx(cc, CP.start_reg(sg)) < clk
    requires LooksCapUnset(QidBody(r, qid), cc)
    requires forall k :: AI.get_idx(A, k) >= -1
    requires forall c: nat :: c in CapIds(r) && AI.get_idx(cc, CP.start_reg(c)) < 0 ==> AI.get_idx(A, CP.start_reg(c)) < 0
    ensures (forall g: nat :: g in CapIds(QidBody(r, qid)) ==> CP.start_reg(g) != j)
            ==> AI.get_idx(AI.filter_capture(r2, AI.filter_capture(r1, A, cc, lc, qc', M), cc, lc, qc', M), j)
                == AI.get_idx(AI.filter_capture(r2, AI.filter_capture(r1, A, cc, lc, qc, M), cc, lc, qc, M), j)
    ensures (exists g: nat :: g in CapIds(QidBody(r, qid)) && CP.start_reg(g) == j)
            ==> AI.get_idx(AI.filter_capture(r2, AI.filter_capture(r1, A, cc, lc, qc', M), cc, lc, qc', M), j) < 0
    decreases r, 0
  {
    var X := AI.filter_capture(r1, A, cc, lc, qc, M);
    var X' := AI.filter_capture(r1, A, cc, lc, qc', M);
    FilterCaptureLen(r1, A, cc, lc, qc, M); FilterCaptureLen(r1, A, cc, lc, qc', M);
    // gl = CapIds(QidBody(r,qid)); it lies entirely inside the branch holding qid.
    if qid in QuantIds(r1) {
      assert qid !in QuantIds(r2) by { if qid in QuantIds(r2) { assert qid in QuantIds(r1) * QuantIds(r2); } }
      assert MxAtQid(r, cc, qc, M, qid) == MxAtQid(r1, cc, qc, M, qid);
      assert QidBody(r, qid) == QidBody(r1, qid);
      assert qid in QuantIdsOutsideLooks(r1) by {
        assert QuantIdsOutsideLooks(r) == QuantIdsOutsideLooks(r1) + QuantIdsOutsideLooks(r2)
          by { if r == R.Re_alt(r1, r2) {} else {} }
        QuantIdsSplit(r2);   // QuantIdsOutsideLooks(r2) ⊆ QuantIds(r2), and qid ∉ QuantIds(r2)
      }
      assert LooksCapUnset(QidBody(r1, qid), cc);      // == LooksCapUnset(QidBody(r,qid),..)
      CapIdsQidBodySubset(r1, qid);   // CapIds(QidBody(r1,qid)) ⊆ CapIds(r1)
      FilterResetFrame(r1, A, cc, lc, qc, qc', M, qid, clk, j);
      // r2: qid ∉ QuantIds(r2), gl ∩ CapIds(r2) = ∅.
      forall q0: nat | q0 in QuantIds(r2) ensures AI.get_idx(qc, q0) == AI.get_idx(qc', q0) {}
      if exists g: nat :: g in CapIds(QidBody(r, qid)) && CP.start_reg(g) == j {
        var g: nat :| g in CapIds(QidBody(r, qid)) && CP.start_reg(g) == j;
        assert g in CapIds(r1);
        assert g !in CapIds(r2) by { if g in CapIds(r2) { assert g in CapIds(r1) * CapIds(r2); } }
        FilterCaptureOutside(r2, X', cc, lc, qc', M, g);
      }
      if forall g: nat :: g in CapIds(QidBody(r, qid)) ==> CP.start_reg(g) != j {
        FilterCaptureQcFrame(r2, X', cc, lc, qc, qc', M, qid, j);
        FilterCaptureCrPointwise(r2, X', X, cc, lc, qc, M, j);
      }
    } else {
      assert qid in QuantIds(r2) && qid !in QuantIds(r1);
      // X' == X pointwise (qid ∉ QuantIds(r1)).
      forall j0 ensures AI.get_idx(X, j0) == AI.get_idx(X', j0)
      { FilterCaptureQcFrame(r1, A, cc, lc, qc, qc', M, qid, j0); }
      forall k ensures AI.get_idx(X, k) >= -1 { FilterCaptureGeqNeg1(r1, A, cc, lc, qc, M, k); }
      forall c: nat | c in CapIds(r2) && AI.get_idx(cc, CP.start_reg(c)) < 0
        ensures AI.get_idx(X, CP.start_reg(c)) < 0
      {
        assert c !in CapIds(r1) by { if c in CapIds(r1) { assert c in CapIds(r1) * CapIds(r2); } }
        FilterCaptureOutside(r1, A, cc, lc, qc, M, c);
      }
      assert MxAtQid(r, cc, qc, M, qid) == MxAtQid(r2, cc, qc, M, qid);
      assert QidBody(r, qid) == QidBody(r2, qid);
      assert qid in QuantIdsOutsideLooks(r2) by {
        assert QuantIdsOutsideLooks(r) == QuantIdsOutsideLooks(r1) + QuantIdsOutsideLooks(r2)
          by { if r == R.Re_alt(r1, r2) {} else {} }
        QuantIdsSplit(r1);   // QuantIdsOutsideLooks(r1) ⊆ QuantIds(r1), and qid ∉ QuantIds(r1)
      }
      assert LooksCapUnset(QidBody(r2, qid), cc);
      FilterResetFrame(r2, X, cc, lc, qc, qc', M, qid, clk, j);
      FilterCaptureCrPointwise(r2, X', X, cc, lc, qc', M, j);
    }
  }

  // ===========================================================================
  // gm-effect lemma for GMReset. Stamping quantifier qid's clock (a write to the
  // QUANT array — caps and thus cc are untouched) raises the reset threshold for
  // qid's subtree, so filter_reset removes exactly the groups of qid's scope gl.
  // GmOfLive(quant') == GmOfLive(quant) - gl. Mirrors Linden's
  // GMReset(gl, gm) == gm - gl, with gl == qm.quants[qid] (StepSpec).
  //
  // The reset-scope precondition (filter on quant' clears exactly gl's starts,
  // leaving every non-gl register untouched) is the deferred-reset obligation
  // for the quantifier: discharged in preservation from (a) the QMap↔AST scope
  // correspondence (gl = the capture ids syntactically under qid) and (b) clock
  // monotonicity (the fresh stamp exceeds every prior-iteration subgroup clock).
  // ===========================================================================
  /** gm-effect lemma for GMReset: stamping quantifier `qid`'s clock (a QUANT-
      array write, so captures are untouched) removes exactly `qid`'s scope `gl`
      from the live denotation: `GmOfLive(quant') == GmOfLive(quant) - gl`.
      Mirrors Linden's `GMReset(gl, gm) == gm - gl`. The reset-scope precondition
      is the deferred-reset obligation for the quantifier. */
  lemma GmOfLiveReset(ast: R.regex, caps: AReg.Regs, look: AReg.Regs, quant: AReg.Regs,
                      qid: nat, clk: int, gl: set<nat>)
    requires
      var f  := AI.filter_reset(ast, caps, look, quant, -1);
      var f' := AI.filter_reset(ast, caps, look, AReg.set_reg(quant, qid, None, clk), -1);
      (forall g: nat :: g in gl ==> AI.get_idx(f', CP.start_reg(g)) < 0)
      && (forall j :: (forall g: nat :: g in gl ==> CP.start_reg(g) != j)
                      ==> AI.get_idx(f', j) == AI.get_idx(f, j))
    ensures GmOfLive(ast, caps, look, AReg.set_reg(quant, qid, None, clk))
         == GmOfLive(ast, caps, look, quant) - gl
  {
    var quant' := AReg.set_reg(quant, qid, None, clk);
    var (cr, cc) := AReg.as_arrays(caps);
    var (_, lc) := AReg.as_arrays(look);
    var (_, qc) := AReg.as_arrays(quant);
    var f  := AI.filter_reset(ast, caps, look, quant, -1);
    var f' := AI.filter_reset(ast, caps, look, quant', -1);
    FilterCaptureLen(ast, cr, cc, lc, qc, -1);
    var (_, qc') := AReg.as_arrays(quant');
    FilterCaptureLen(ast, cr, cc, lc, qc', -1);

    var g0 := GmOfLive(ast, caps, look, quant);
    var g1 := GmOfLive(ast, caps, look, quant');
    var target := g0 - gl;

    // Same cap arrays ⇒ start clocks/ends read identically; only the filtered
    // START VALUES change, and only for gl's groups (which drop out).
    forall k: nat ensures (k in g1) <==> (k in target) {
      assert CP.start_reg(k) % 2 == 0;
      if k in gl {
        assert AI.get_idx(f', CP.start_reg(k)) < 0;   // reset ⇒ absent
      } else {
        assert forall g: nat :: g in gl ==> CP.start_reg(g) != CP.start_reg(k);
        assert AI.get_idx(f', CP.start_reg(k)) == AI.get_idx(f, CP.start_reg(k));
      }
    }
    assert g1.Keys == target.Keys;

    forall k: nat | k in g1 ensures g1[k] == target[k] {
      // k ∉ gl (else absent above); every register of k is untouched.
      assert k !in gl;
      assert forall g: nat :: g in gl ==> CP.start_reg(g) != CP.start_reg(k);
      assert forall g: nat :: g in gl ==> CP.start_reg(g) != CP.end_reg(k);
      assert AI.get_idx(f', CP.start_reg(k)) == AI.get_idx(f, CP.start_reg(k));
      assert AI.get_idx(f', CP.end_reg(k)) == AI.get_idx(f, CP.end_reg(k));
    }
    assert g1 == target;
  }

  // GmOfLiveReset with the reset-scope precondition DISCHARGED by FilterResetFrame,
  // for gl == CapIds(QidBody(ast, qid)) (qid's syntactic scope). Now the GMReset
  // effect lemma rests on clean structural + clock predicates that the clock-
  // monotonicity invariant supplies.
  /** `GmOfLiveReset` with the reset-scope precondition DISCHARGED by
      `FilterResetFrame`, for `gl == CapIds(QidBody(ast, qid))` (`qid`'s
      syntactic scope) — the effect now rests on clean structural + clock
      predicates the clock-monotonicity invariant supplies. */
  lemma GmOfLiveResetFull(ast: R.regex, caps: AReg.Regs, look: AReg.Regs, quant: AReg.Regs,
                          qid: nat, clk: int)
    requires NR.LookBehindFragmentRE(ast) && CapUnique(ast) && QuantUnique(ast)
    requires qid in QuantIds(ast)
    requires qid in QuantIdsOutsideLooks(ast)   // L3a: reset is for outside-look quantifiers
    requires qid < |AReg.as_arrays(quant).1|
    requires |AReg.as_arrays(quant).0| == |AReg.as_arrays(quant).1|
    requires clk >= 0
    requires clk >= MxAtQid(ast, caps.a_clk, AReg.as_arrays(quant).1, -1, qid)
    requires PathPresentQ(ast, caps.a_clk, AReg.as_arrays(quant).1, -1, qid)
    requires forall sg: nat :: sg in CapIds(QidBody(ast, qid)) ==> AI.get_idx(caps.a_clk, CP.start_reg(sg)) < clk
    requires LooksCapUnset(QidBody(ast, qid), caps.a_clk)
    requires forall k :: AI.get_idx(caps.a_cp, k) >= -1
    requires forall c: nat :: c in CapIds(ast) && AI.get_idx(caps.a_clk, CP.start_reg(c)) < 0
                             ==> AI.get_idx(caps.a_cp, CP.start_reg(c)) < 0
    ensures GmOfLive(ast, caps, look, AReg.set_reg(quant, qid, None, clk))
         == GmOfLive(ast, caps, look, quant) - CapIds(QidBody(ast, qid))
  {
    var gl := CapIds(QidBody(ast, qid));
    var quant' := AReg.set_reg(quant, qid, None, clk);
    var (cr, cc) := AReg.as_arrays(caps);
    var (_, lc) := AReg.as_arrays(look);
    var (_, qc) := AReg.as_arrays(quant);
    var (_, qc') := AReg.as_arrays(quant');
    assert qc' == qc[qid := clk];
    // qc' relation for FilterResetFrame.
    forall q0: int | q0 != qid ensures AI.get_idx(qc', q0) == AI.get_idx(qc, q0) {}
    // reset part: every gl start is driven negative.
    forall g: nat | g in gl
      ensures AI.get_idx(AI.filter_capture(ast, cr, cc, lc, qc', -1), CP.start_reg(g)) < 0
    {
      FilterResetFrame(ast, cr, cc, lc, qc, qc', -1, qid, clk, CP.start_reg(g));
    }
    // frame part: off gl starts, filter is unchanged.
    forall j | (forall g: nat :: g in gl ==> CP.start_reg(g) != j)
      ensures AI.get_idx(AI.filter_capture(ast, cr, cc, lc, qc', -1), j)
              == AI.get_idx(AI.filter_capture(ast, cr, cc, lc, qc, -1), j)
    {
      FilterResetFrame(ast, cr, cc, lc, qc, qc', -1, qid, clk, j);
    }
    GmOfLiveReset(ast, caps, look, quant, qid, clk, gl);
  }

  // ===========================================================================
  // Reset-case completion: connect the reset conclusion (gm minus the body's
  // CapIds) to Linden's GMReset over the QMap's group list. QmapOk pins
  // qm.quants[qid] == DefGroups(Translate(body)), and DefGroups enumerates exactly
  // CapIds -- so the two subtractions coincide.
  // ===========================================================================

  // DefGroups of the translation enumerates exactly the RegElk-side CapIds.
  /** `DefGroups` of the translation enumerates exactly the RegElk-side
      `CapIds` — links the two representations of a quant's reset scope. */
  lemma DefGroupsCapIds(re: R.regex)
    requires T.TransWf(re)
    ensures forall g: nat :: g in L.DefGroups(T.Translate(re)) <==> g in CapIds(re)
    decreases re
  {
    match re
    case Re_empty => case Re_character(_) => case Re_anchor(_) =>
    case Re_alt(r1, r2) => DefGroupsCapIds(r1); DefGroupsCapIds(r2);
    case Re_con(r1, r2) => DefGroupsCapIds(r1); DefGroupsCapIds(r2);
    case Re_quant(_, _, _, r1) => DefGroupsCapIds(r1);
    case Re_capture(cid, r1) =>
      DefGroupsCapIds(r1);
      assert L.DefGroups(T.Translate(re)) == [cid as nat] + L.DefGroups(T.Translate(r1));
    case Re_lookaround(_, _, r1) => DefGroupsCapIds(r1);
  }

  // At any quant node reachable by QidBody's descent, QmapOk pins qm's entry to
  // the body's group list. (No QuantUnique needed: QmapOk constrains EVERY
  // quant node, including the one QidBody selects.)
  /** At any quant node `QidBody` selects, `QmapOk` pins `qm.quants[qid]` to the body's
      group list, whose ids are exactly `CapIds(QidBody(re, qid))`. */
  lemma QmapOkAtQid(re: R.regex, qm: AR.QMap, qid: nat)
    requires T.TransWf(re)
    requires AR.QmapOk(re, qm)
    requires qid in QuantIds(re)
    ensures (qid as int) in qm.quants
    ensures (set g: nat {:autotriggers false} | g in qm.quants[qid as int]) == CapIds(QidBody(re, qid))
    decreases re
  {
    match re
    case Re_alt(r1, r2) =>
      if qid in QuantIds(r1) { QmapOkAtQid(r1, qm, qid); } else { QmapOkAtQid(r2, qm, qid); }
    case Re_con(r1, r2) =>
      if qid in QuantIds(r1) { QmapOkAtQid(r1, qm, qid); } else { QmapOkAtQid(r2, qm, qid); }
    case Re_quant(nul, qid0, q, r1) =>
      if qid0 >= 0 && (qid0 as nat) == qid {
        assert qid0 == qid as int;
        assert qm.quants[qid as int] == L.DefGroups(T.Translate(r1));
        DefGroupsCapIds(r1);
        assert QidBody(re, qid) == r1;
      } else {
        QmapOkAtQid(r1, qm, qid);
      }
    case Re_capture(cid, r1) => QmapOkAtQid(r1, qm, qid);
    case Re_lookaround(lid, l, r1) => QmapOkAtQid(r1, qm, qid);
  }

  // The TOTAL Reset interface: stamping quant qid mirrors Linden's GMReset over
  // gl == qm.quants[qid]. Remaining positional hypothesis: PathPresentQ (plus MxAtQid/
  // body-staleness bounds, dischargeable from the clock backbone since the
  // fresh stamp S+1 exceeds every stored clock <= S).
  /** The TOTAL Reset interface: stamping quant `qid` mirrors Linden's `GMReset`
      over `gl == qm.quants[qid]`. Remaining positional hypothesis: `PathPresentQ`
      (plus `MxAtQid`/body-staleness bounds, dischargeable from the clock
      backbone since the fresh stamp exceeds every stored clock). */
  lemma GmOfLiveResetGMReset(ast: R.regex, qm: AR.QMap, caps: AReg.Regs, look: AReg.Regs,
                             quant: AReg.Regs, qid: nat, clk: int)
    requires NR.LookBehindFragmentRE(ast) && CapUnique(ast) && QuantUnique(ast)
    requires T.TransWf(ast) && AR.QmapOk(ast, qm)
    requires qid in QuantIds(ast)
    requires qid in QuantIdsOutsideLooks(ast)   // L3a: reset is for outside-look quantifiers
    requires qid < |AReg.as_arrays(quant).1|
    requires |AReg.as_arrays(quant).0| == |AReg.as_arrays(quant).1|
    requires clk >= 0
    requires clk >= MxAtQid(ast, caps.a_clk, AReg.as_arrays(quant).1, -1, qid)
    requires PathPresentQ(ast, caps.a_clk, AReg.as_arrays(quant).1, -1, qid)
    requires forall sg: nat :: sg in CapIds(QidBody(ast, qid)) ==> AI.get_idx(caps.a_clk, CP.start_reg(sg)) < clk
    requires LooksCapUnset(QidBody(ast, qid), caps.a_clk)
    requires forall k :: AI.get_idx(caps.a_cp, k) >= -1
    requires forall c: nat :: c in CapIds(ast) && AI.get_idx(caps.a_clk, CP.start_reg(c)) < 0
                             ==> AI.get_idx(caps.a_cp, CP.start_reg(c)) < 0
    ensures (qid as int) in qm.quants
    ensures GmOfLive(ast, caps, look, AReg.set_reg(quant, qid, None, clk))
         == LG.GMReset(qm.quants[qid as int], GmOfLive(ast, caps, look, quant))
  {
    GmOfLiveResetFull(ast, caps, look, quant, qid, clk);
    QmapOkAtQid(ast, qm, qid);
    assert LG.GMReset(qm.quants[qid as int], GmOfLive(ast, caps, look, quant))
        == GmOfLive(ast, caps, look, quant) - (set g: nat {:autotriggers false} | g in qm.quants[qid as int]);
  }

  // ===========================================================================
  // Blocked correspondence: RegElk's blocked list holds threads parked AT a
  // Consume(ce) pc (un-advanced); the tree machine's blocked list holds the
  // post-Read continuation tree, threaded at the NEXT input, one pc past the
  // Consume, with the loop flag re-armed (ea = true). Grounded in GenStepRE's
  // verified Consume StepSpec. Positional pairing; the RegElk↔PikeTree ORDER
  // REVERSAL (RegElk blocked is low-to-high, prepended) is applied at the use
  // site in preservation, not baked into this predicate.
  // ===========================================================================

  /** Blocked correspondence: RegElk's blocked threads sit AT a `Consume(ce)` pc
      (un-advanced); the tree machine holds the post-`Read` continuation tree,
      threaded at the NEXT input, one pc past the `Consume`, loop flag re-armed
      (`ea = true`). gm-free; grounded in `GenStepRE`'s `Consume` `StepSpec`. */
  ghost predicate BlockedTreeThreadRE(
      rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input, nextinp: LC.Input,
      tl: seq<LT.Tree>, bl: seq<(AI.Thread, RC.char_expectation)>)
    decreases tl
  {
    (|tl| == 0 && |bl| == 0)
    || (|tl| > 0 && |bl| > 0 && bl[0].0.pc + 1 >= 0
        && (exists c: char :: AR.ReadCharE(bl[0].1, inp) == Some((c, nextinp)))
        && TT.TreeThreadRE(rer, qm, code, nextinp, tl[0], (bl[0].0.pc + 1) as nat, true)
        && BlockedTreeThreadRE(rer, qm, code, inp, nextinp, tl[1..], bl[1..]))
  }

  /** A `BlockedTreeThreadRE` pairing forces the two lists to have equal
      length. */
  lemma BlockedLenEqRE(
      rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input, nextinp: LC.Input,
      tl: seq<LT.Tree>, bl: seq<(AI.Thread, RC.char_expectation)>)
    requires BlockedTreeThreadRE(rer, qm, code, inp, nextinp, tl, bl)
    ensures |tl| == |bl|
    decreases tl
  {
    if |tl| > 0 { BlockedLenEqRE(rer, qm, code, inp, nextinp, tl[1..], bl[1..]); }
  }

  // ===========================================================================
  // Input <-> code-point bridge. RegElk tracks a code point `cp` into the
  // subject string; Linden tracks an Input(next, pref) with pref REVERSED
  // (input_str = rev(pref) ++ next). PikeInvRE relates the two via InpOfCp.
  // ===========================================================================

  /** The input ↔ code-point bridge: RegElk tracks a code point `cp`; Linden
      tracks an `Input(next, pref)` with `pref` reversed. `InpOfCp` builds the
      Linden `Input` at position `cp` of `str`. */
  ghost function InpOfCp(str: string, cp: nat): LC.Input
    requires cp <= |str|
  {
    LC.Input(str[cp..], LC.Reverse(str[..cp]))
  }

  /** `InpOfCp(str, cp)`'s index is exactly `cp`. */
  lemma IdxInpOfCp(str: string, cp: nat)
    requires cp <= |str|
    ensures LC.Idx(InpOfCp(str, cp)) == cp
  {
    LS.ReverseLength(str[..cp]);   // |Reverse(str[..cp])| == |str[..cp]| == cp
  }

  // Advancing one code point is advancing the Input one char forward.
  /** Advancing one code point is advancing the `Input` one char forward. */
  lemma AdvanceInpOfCp(str: string, cp: nat)
    requires cp < |str|
    ensures LC.AdvanceInput(InpOfCp(str, cp), WP.Forward) == Some(InpOfCp(str, cp + 1))
  {
    assert str[..cp + 1] == str[..cp] + [str[cp]];
    STS.ReverseSnoc(str[..cp], str[cp]);   // Reverse(str[..cp+1]) == [str[cp]] + Reverse(str[..cp])
    assert InpOfCp(str, cp).next[1..] == str[cp + 1..];
  }

  // ===========================================================================
  // GmOf ↔ final capture array bridge. RegElk's answer is
  // NormalizeArr(filter_reset(...)); MatcherSpec talks about CapArrayOfLeaf of a
  // leaf's GroupMap. Since GmOf IS the reading of filter_reset's array and
  // CapArrayOfLeaf ignores the leaf Input, the two agree for a completed
  // (closed) match. This is the denotation→answer link the main theorem needs.
  // ===========================================================================

  // Membership/value characterization of the GmOf map comprehension.
  /** Membership/value characterization of the `GmOf` map comprehension. */
  lemma GmOfMem(ast: R.regex, caps: AReg.Regs, look: AReg.Regs, quant: AReg.Regs, g: nat)
    ensures var f := AI.filter_reset(ast, caps, look, quant, -1);
      (g in GmOf(ast, caps, look, quant)) <==> (g < |f| && AI.get_idx(f, CP.start_reg(g)) >= 0)
    ensures var f := AI.filter_reset(ast, caps, look, quant, -1);
      g in GmOf(ast, caps, look, quant) ==> GmOf(ast, caps, look, quant)[g] == RangeFromArr(f, g)
  {}

  /** The GmOf ↔ final capture-array bridge: for a completed (closed) match,
      RegElk's answer `NormalizeArr(filter_reset(...))` equals `CapArrayOfLeaf`
      of the leaf whose `GroupMap` is `GmOf`. The denotation→answer link the
      main theorem needs. */
  lemma GmOfCapArrayBridge(ast: R.regex, caps: AReg.Regs, look: AReg.Regs, quant: AReg.Regs,
                           inp: LC.Input, ngroups: nat)
    requires var f := AI.filter_reset(ast, caps, look, quant, -1);
      |f| == 2 * ngroups
      && (forall i :: 0 <= i < |f| ==> f[i] >= -1)                                  // -1 encodes None
      && (forall g: nat :: 0 <= g < ngroups ==> (f[2 * g] >= 0 ==> f[2 * g + 1] >= 0))  // closed match
    ensures LES.NormalizeArr(AI.filter_reset(ast, caps, look, quant, -1))
         == LES.CapArrayOfLeaf((inp, GmOf(ast, caps, look, quant)), ngroups)
  {
    var f := AI.filter_reset(ast, caps, look, quant, -1);
    var gm := GmOf(ast, caps, look, quant);
    var na := LES.NormalizeArr(f);
    var ca := LES.CapArrayOfLeaf((inp, gm), ngroups);
    forall j | 0 <= j < 2 * ngroups
      ensures na[j] == ca[j]
    {
      var g: nat := j / 2;
      GmOfMem(ast, caps, look, quant, g);
      assert CP.start_reg(g) == 2 * g && CP.end_reg(g) == 2 * g + 1;
      assert AI.get_idx(f, 2 * g) == f[2 * g];             // 2*g < |f|
      assert AI.get_idx(f, 2 * g + 1) == f[2 * g + 1];     // 2*g+1 < |f|
      if j % 2 == 0 {
        assert j == 2 * g;
      } else {
        assert j == 2 * g + 1 && j - 1 == 2 * g;
      }
    }
    assert na == ca;
  }

  // ===========================================================================
  // TreeThreadRE constructors (normal-lemma membership intros for its three
  // disjuncts). Needed to build tree-threads from inside `least lemma` contexts
  // (where a bare `assert TreeThreadRE(...)` would reference the prefix
  // predicate) — the InitialPikeInvRE base and the preservation proof both build
  // tree-threads this way.
  // ===========================================================================

  // tt_eq is gone with the pivot: tree-threads are TreeRepRE-represented
  // (checked) trees, produced once at the entry by ActionsTreeRepRE's
  // construction — a spec BoolTree is no longer a tree-thread by itself.

  // tt_reset: a Reset node sitting on a SetQuantToClock(qid, false) marker.
  /** `tt_reset` constructor: a `Reset` node sitting on a
      `SetQuantToClock(qid, false)` marker is a `TreeThreadRE`. */
  lemma TreeThreadResetIntro(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                             t: LT.Tree, pc: nat, ea: bool, qid: int)
    requires t.GroupActionT? && t.g.Reset?
    requires NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(qid, false))
    requires qid in qm.quants && qm.quants[qid] == t.g.gl
    requires TT.TreeThreadRE(rer, qm, code, inp, t.t, pc + 1, ea)
    ensures TT.TreeThreadRE(rer, qm, code, inp, t, pc, ea)
  {}

  // tt_begin: a BeginLoop stutter re-arms the loop flag to false at pc+1.
  /** `tt_begin` constructor: a `BeginLoop` stutter re-arms the loop flag to
      `false` at `pc+1`. */
  lemma TreeThreadBeginIntro(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                             t: LT.Tree, pc: nat, ea: bool)
    requires NR.GetPcRE(code, pc) == Some(RB.BeginLoop)
    requires TT.TreeThreadRE(rer, qm, code, inp, t, pc + 1, false)
    ensures TT.TreeThreadRE(rer, qm, code, inp, t, pc, ea)
  {}

  // ===========================================================================
  // THE SIMULATION INVARIANT (PikeInvRE) and its initial-state instance.
  //
  // Active/blocked correspondences are gm-AWARE here: each VM thread's register
  // bank denotes (via GmOf) the GroupMap the tree machine pairs with the tree.
  // (TreeThreadRE stays gm-free; the gm tie is this extra GmOf conjunct.) Port
  // of Linden PikeEquiv's PikeInv, with the RegElk deltas established across this
  // file: StutterChainTo in SeenInclusion, blocked order reversal, cp↔Input.
  // ===========================================================================

  /** The head tree of an active `(tree, gm)` list (or `None` if empty). */
  function HdTreeOf(tl: seq<(LT.Tree, LG.GroupMap)>): Option<LT.Tree> {
    if |tl| == 0 then None else Some(tl[0].0)
  }
  /** The head thread's pc of a VM thread list (or `0` if empty/negative). */
  function HeadPcOf(vl: seq<AI.Thread>): nat {
    if |vl| == 0 || vl[0].pc < 0 then 0 else vl[0].pc as nat
  }

  // A VM thread bank denotes the tree's GroupMap (via the LIVE denotation, which
  // handles mid-search open groups; see GmOfLive).
  /** A VM thread's register bank denotes the tree's `GroupMap`, via the LIVE
      denotation `GmOfLive` (which handles mid-search open groups). */
  ghost predicate ThreadTracksGm(re: R.regex, th: AI.Thread, gm: LG.GroupMap) {
    gm == GmOfLive(re, th.capture_regs, th.look_regs, th.quant_regs)
  }

  // Active list: (tree, gm) paired with a thread, tree-threaded at the thread's
  // (pc, exit_allowed) and gm denoted by the thread's registers.
  /** Active-list correspondence: each `(tree, gm)` is paired with a thread,
      the tree tree-threaded at the thread's `(pc, exit_allowed)` and `gm`
      denoted by the thread's registers (`ThreadTracksGm`). */
  ghost predicate ActiveRepRE(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code,
                              inp: LC.Input, tl: seq<(LT.Tree, LG.GroupMap)>, vl: seq<AI.Thread>)
    decreases tl
  {
    (|tl| == 0 && |vl| == 0)
    || (|tl| > 0 && |vl| > 0 && vl[0].pc >= 0
        && TT.TreeThreadRE(rer, qm, code, inp, tl[0].0, vl[0].pc as nat, vl[0].exit_allowed)
        && ThreadTracksGm(re, vl[0], tl[0].1)
        && ActiveRepRE(rer, qm, re, code, inp, tl[1..], vl[1..]))
  }

  // Blocked list: parked at a Consume(ce) pc, post-Read tree threaded at pc+1 on
  // nextinp with the loop flag re-armed; gm denoted by the thread's registers.
  /** Blocked-list correspondence: gm-aware version of `BlockedTreeThreadRE` —
      each parked-at-`Consume` thread's post-`Read` tree is threaded at `pc+1`
      on `nextinp` with the loop flag re-armed, and `gm` denoted by its
      registers. */
  ghost predicate BlockedRepRE(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code,
                               inp: LC.Input, nextinp: LC.Input,
                               tl: seq<(LT.Tree, LG.GroupMap)>, bl: seq<(AI.Thread, RC.char_expectation)>)
    decreases tl
  {
    (|tl| == 0 && |bl| == 0)
    || (|tl| > 0 && |bl| > 0 && bl[0].0.pc + 1 >= 0
        && (exists c: char :: AR.ReadCharE(bl[0].1, inp) == Some((c, nextinp)))
        && TT.TreeThreadRE(rer, qm, code, nextinp, tl[0].0, (bl[0].0.pc + 1) as nat, true)
        && ThreadTracksGm(re, bl[0].0, tl[0].1)
        && BlockedRepRE(rer, qm, re, code, inp, nextinp, tl[1..], bl[1..]))
  }

  // best (a Leaf's GroupMap) ↔ bestmatch thread's denoted GroupMap. The leaf
  // Input is irrelevant (CapArrayOfLeaf drops it).
  /** best (a leaf's `GroupMap`) ↔ `bestmatch` thread's denoted `GroupMap`; the
      two options agree on presence and, when present, on the group map (the
      leaf's Input is irrelevant — `CapArrayOfLeaf` drops it). */
  ghost predicate BestMatchRE(re: R.regex, best: Option<LT.Leaf>, bestmatch: Option<AI.Thread>) {
    (best.None? <==> bestmatch.None?)
    && (best.Some? ==> bestmatch.Some? && best.value.1 == GmOfLive(re, bestmatch.value.capture_regs,
                                                                   bestmatch.value.look_regs, bestmatch.value.quant_regs))
  }

  // The blocked lists correspond through the MATCHING FILTER: RegElk blocks
  // threads UNCONDITIONALLY (the char check happens later, in FConsume),
  // while the tree machine only ever blocks Read trees — which exist exactly
  // when ReadCharE succeeds. A mismatch-doomed VM thread has no tree-side
  // counterpart (its tree is Mismatch, killed by an empty pts_active step),
  // so it is invisible to the correspondence; FConsume's is_accepted test
  // drops exactly the non-matching ones, realigning the lists at the next
  // position. At end of input the filter is empty for free.
  /** The sublist of RegElk's blocked threads whose char check succeeds at
      `inp`. RegElk blocks threads unconditionally (the check runs later in
      `FConsume`), while the tree machine only blocks `Read` trees — which exist
      exactly when `ReadCharE` succeeds. This filter realigns the two lists. */
  ghost function MatchingBlocked(bl: seq<(AI.Thread, RC.char_expectation)>, inp: LC.Input)
    : seq<(AI.Thread, RC.char_expectation)>
    decreases bl
  {
    if |bl| == 0 then []
    else (if AR.ReadCharE(bl[0].1, inp).Some? then [bl[0]] else []) + MatchingBlocked(bl[1..], inp)
  }

  /** **THE SIMULATION INVARIANT.** Ties a `PikeTree` state to a RegElk
      `VmState`: the code point tracks the tree `Input`, `bestmatch`/best
      agree (`BestMatchRE`), and the active and blocked lists correspond
      element-wise with matching group-map denotations (`ActiveRepRE`,
      `BlockedRepRE` over `MatchingBlocked`), while the seen set satisfies
      `SeenInclusionRE`. Port of Linden PikeEquiv's `PikeInv`, carrying every
      RegElk delta established across this file. This is the invariant the
      preservation induction in `PikeSimRE.dfy` maintains. */
  /** The VM's anchor context window is exactly the (prev, next) character
      pair at `cp` — what `AnchorAssertion` execution consults. */
  ghost predicate ContextOkRE(str: string, cp: int, ctx: LAnc.char_context) {
    ctx == AI.cp_context(cp, str, LAnc.Forward)
  }

  ghost predicate PikeInvRE(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, ngroups: nat,
                            str: string, pts: PT.PikeTreeState, vms: AI.VmState)
  {
    match pts
    case PTS_final(best) => BestMatchRE(re, best, vms.bestmatch)
    case PTS(inp, treeactive, best, treeblocked, treeseen) =>
      0 <= vms.cp <= |str|
      && inp == InpOfCp(str, vms.cp)
      && ContextOkRE(str, vms.cp, vms.context)
      && BestMatchRE(re, best, vms.bestmatch)
      && ActiveRepRE(rer, qm, re, code, inp, treeactive, vms.active)
      && (forall nextinp :: LC.AdvanceInput(inp, WP.Forward) == Some(nextinp) ==>
            BlockedRepRE(rer, qm, re, code, inp, nextinp, treeblocked,
                         MatchingBlocked(LC.Reverse(vms.blocked), inp)))
      && (LC.AdvanceInput(inp, WP.Forward) == None ==> treeblocked == [])
      && SeenInclusionRE(rer, qm, code, inp, treeseen, vms.processed, HdTreeOf(treeactive), HeadPcOf(vms.active))
  }

  // Initial state satisfies the invariant. The initial VM thread is at (0,
  // false) with all-init registers (denoting Empty via GmOfInit); the initial
  // tree is the boolean tree of [Areg(Translate(re))] at CannotExit; seen/blocked
  // are empty. (init_thread ea=false is correct: the lazy-prefix star exits via
  // Fork priority, not exit_allowed — see PROGRESS.md.)
  /** The initial state satisfies `PikeInvRE`: the initial VM thread is at
      `(0, false)` with all-init registers (denoting `Empty` via `GmOfInit`),
      the initial tree is the boolean tree of `[Areg(Translate(re))]` at
      `CannotExit`, and seen/blocked are empty. The base case of the whole
      simulation. */
  lemma InitialPikeInvRE(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, ngroups: nat,
                         str: string, tree: LT.Tree, vms: AI.VmState, ncap: int, nlook: int, nquant: int)
    requires NR.LookBehindFragmentRE(re) && T.TransWf(re) && !rer.ignoreCase && AR.QmapOk(re, qm)
    requires code == CP.compile_to_bytecode(re)
    requires TT.TreeThreadRE(rer, qm, code, LC.InitInput(str), tree, 0, false)
    requires vms.cp == 0
    requires vms.active == [AI.init_thread(AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant))]
    requires vms.blocked == []
    requires vms.bestmatch.None?
    requires vms.processed == AI.init_bpcset(|code|)
    requires vms.context == AI.cp_context(0, str, LAnc.Forward)
    ensures PikeInvRE(rer, qm, re, code, ngroups, str, PT.PikeTreeInitialState(tree, LC.InitInput(str)), vms)
  {
    var inp := LC.InitInput(str);
    var acts := [LS.Areg(T.Translate(re))];
    assert LC.Reverse(str[..0]) == [];
    assert inp == InpOfCp(str, 0);                     // Input(str, []) == Input(str[0..], Reverse(str[..0]))

    // Active correspondence for the singleton [(tree, Empty)] ~ [init_thread]:
    // TreeThreadRE(tree, 0, false) is the requires (the checked tree from the
    // entry construction).
    GmOfLiveInit(re, ncap, nlook, nquant);              // GmOfLive(re, init_regs...) == Empty
    var th := AI.init_thread(AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant));
    assert ActiveRepRE(rer, qm, re, code, inp, [(tree, LG.Empty)], [th]) by {
      assert ActiveRepRE(rer, qm, re, code, inp, [], []);
    }

    // Seen inclusion is vacuous at the empty (init_bpcset) processed set.
    InitialInclusionRE(rer, qm, code, inp, Some(tree), 0, |code|);
  }

  /** The cp-generalized base case: the initial state at an ARBITRARY start
      position `cp` (with fresh registers) satisfies `PikeInvRE`. `InitialPikeInvRE`
      is the `cp == 0` instance. The proof is the same and actually simpler — the
      incoming `inp` is `InpOfCp(str, cp)` directly, with no `InitInput` bridge.
      This is the entry invariant the lookaround body match at position `cp`
      needs (§4b): the body is simulated from a fresh thread at `cp`, not at 0. */
  lemma InitialPikeInvREAtCp(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, ngroups: nat,
                             str: string, cp: nat, tree: LT.Tree, vms: AI.VmState, ncap: int, nlook: int, nquant: int)
    requires NR.LookBehindFragmentRE(re) && T.TransWf(re) && !rer.ignoreCase && AR.QmapOk(re, qm)
    requires code == CP.compile_to_bytecode(re)
    requires cp <= |str|
    requires TT.TreeThreadRE(rer, qm, code, InpOfCp(str, cp), tree, 0, false)
    requires vms.cp == cp
    requires vms.active == [AI.init_thread(AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant))]
    requires vms.blocked == []
    requires vms.bestmatch.None?
    requires vms.processed == AI.init_bpcset(|code|)
    requires vms.context == AI.cp_context(cp, str, LAnc.Forward)
    ensures PikeInvRE(rer, qm, re, code, ngroups, str, PT.PikeTreeInitialState(tree, InpOfCp(str, cp)), vms)
  {
    var inp := InpOfCp(str, cp);
    var acts := [LS.Areg(T.Translate(re))];

    // Active correspondence for the singleton [(tree, Empty)] ~ [init_thread].
    GmOfLiveInit(re, ncap, nlook, nquant);              // GmOfLive(re, init_regs...) == Empty
    var th := AI.init_thread(AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant));
    assert ActiveRepRE(rer, qm, re, code, inp, [(tree, LG.Empty)], [th]) by {
      assert ActiveRepRE(rer, qm, re, code, inp, [], []);
    }

    // Seen inclusion is vacuous at the empty (init_bpcset) processed set.
    InitialInclusionRE(rer, qm, code, inp, Some(tree), 0, |code|);
  }
}
