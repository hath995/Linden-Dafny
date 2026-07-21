// Mirror of Engine/PikeEquiv.v.
// Simulation invariant between the PikeVM (bytecode) and PikeTree (tree) small-step semantics, and
// its preservation. The simulation/invariant DEFINITIONS are ported; the heavy theorems
// (generate_*, stutter_wf, seen_inclusion lemmas, and the two named theorems initial_pike_inv /
// invariant_preservation) are axiomatized — these are the development's hardest proofs.
include "PikeTree.dfy"
include "PikeVM.dfy"
include "TreeRep.dfy"

/** The simulation invariant between the bytecode `PikeVM` and the tree-walking `PikeTree`
    machines, and the proof that it is preserved step-by-step (`InvariantPreservation`,
    Theorem 14) — the technical core of the PikeVM≡PikeTree equivalence. */
module PikeEquiv {
  import opened Std.Wrappers
  import opened WarblreRegExpRecord
  import opened WarblrePrimitives
  import opened WarblreNumeric   // NoI, Inf
  import opened Chars
  import opened Groups
  import opened Regex           // Regex
  import opened Tree
  import opened Semantics       // Actions
  import opened BooleanSemantics  // BoolTree, LoopBool
  import opened NFA
  import opened PikeSubset
  import opened SeenSets
  import opened PikeTree
  import opened PikeVM
  import TR = TreeRep           // TR.TreeRep, TR.ActionsTreeRep, TR.TreeRepDeterm
  import FS = FunctionalSemantics   // FS.NoiPred

  // Coq: tree_thread — a (tree,gm) and a thread are about to execute the same actions. tt_begin
  // keeps the same tree at pc+1, so this is non-structural → least predicate.
  /** Relates a `(Tree, GroupMap)` pair to a bytecode `Thread`: they are "about to execute the
      same actions". `tt_eq` grounds this in a shared `BoolTree`/`ActionsRep` witness; `tt_reset`
      and `tt_begin` let the tree stay put while the thread's pc advances past a `ResetRegs` or
      `BeginLoop` instruction. */
  least predicate TreeThread(rer: RegExpRecord, code: Code, inp: Input, tg: (Tree, GroupMap), thr: Thread)
  {
    // tt_eq
    (thr.gm == tg.1 && exists acts: Actions ::
       BoolTree(rer, acts, inp, thr.b, tg.0) && ActionsRep(acts, code, thr.pc) && PikeActions(acts))
    // tt_reset
    || (tg.0.GroupActionT? && tg.0.g.Reset? && thr.gm == tg.1
        && GetPc(code, thr.pc) == Some(ResetRegs(tg.0.g.gl))
        && TreeThread(rer, code, inp, (tg.0.t, GMReset(tg.0.g.gl, tg.1)), Thr(thr.pc + 1, GMReset(tg.0.g.gl, tg.1), thr.b)))
    // tt_begin
    || (thr.gm == tg.1 && GetPc(code, thr.pc) == Some(BeginLoop)
        && TreeThread(rer, code, inp, tg, Thr(thr.pc + 1, tg.1, CannotExit)))
  }

  // Coq: list_tree_thread
  /** Pointwise `TreeThread` over parallel lists: the tree-level active/blocked list and the
      bytecode-level thread list represent the same pending work, entry for entry. */
  ghost predicate ListTreeThread(rer: RegExpRecord, code: Code, inp: Input, tl: seq<(Tree, GroupMap)>, vl: seq<Thread>)
    decreases tl
  {
    (|tl| == 0 && |vl| == 0)
    || (|tl| > 0 && |vl| > 0 && vl[0].gm == tl[0].1
        && TreeThread(rer, code, inp, tl[0], vl[0])
        && ListTreeThread(rer, code, inp, tl[1..], vl[1..]))
  }

  // Coq: head_pc
  /** The pc of the first thread in `threadactive`, or `0` if it is empty — used as the
      "currently being processed" position for `SeenInclusion`. */
  function HeadPc(threadactive: seq<Thread>): Label {
    if |threadactive| == 0 then 0 else threadactive[0].pc
  }

  // Coq: seen_inclusion
  /** Every bytecode pc memoized in `threadseen` corresponds to a tree already memoized in
      `treeseen` under `TreeThread` — except for a pc reached only by "stuttering" through
      `Stutters` instructions ahead of `current`, which isn't yet counted as explored. */
  ghost predicate SeenInclusion(rer: RegExpRecord, c: Code, inp: Input, treeseen: SeenTrees, threadseen: SeenPcs, current: Option<(Tree, GroupMap)>, currentpc: Label)
  {
    forall pc: Label, b: LoopBool :: Inseenpc(threadseen, pc, b) ==>
      (exists t: Tree, gm: GroupMap :: Inseen(treeseen, t) && TreeThread(rer, c, inp, (t, gm), Thr(pc, gm, b)))
      || (Stutters(pc, c) && exists t: Tree, gm: GroupMap :: pc < currentpc && current == Some((t, gm)) && TreeThread(rer, c, inp, (t, gm), Thr(pc, gm, b)))
  }

  // Coq: stutter_wf
  /** Compiled code has well-founded stuttering: whenever a `Stutters` instruction's
      `EpsilonStep` produces a single active successor, that successor's pc is strictly
      greater. Rules out infinite stutter loops in the simulation. */
  ghost predicate StutterWf(rer: RegExpRecord, code: Code) {
    forall pc: Label, gm: GroupMap, b: LoopBool, nextpc: Label, nextgm: GroupMap, nextb: LoopBool, inp: Input ::
      (Stutters(pc, code) && EpsilonStep(rer, Thr(pc, gm, b), code, inp) == EpsActive([Thr(nextpc, nextgm, nextb)]))
      ==> pc < nextpc
  }

  // Coq: pike_inv
  /** The full simulation invariant between a `PikeTreeState` and a `PikeVmState`: matching
      `best` results, `ListTreeThread` between the active/blocked lists, and `SeenInclusion`
      between the seen sets. Preserved by every step (`InvariantPreservation`). */
  ghost predicate PikeInv(rer: RegExpRecord, code: Code, pts: PikeTreeState, pvs: PikeVmState) {
    match pts
    case PTS_final(best) => pvs.PVS_final? && pvs.best == best
    case PTS(inp, treeactive, best, treeblocked, treeseen) =>
      pvs.PVS? && pvs.inp == inp && pvs.best == best
      && ListTreeThread(rer, code, inp, treeactive, pvs.active)
      && (forall nextinp :: AdvanceInput(inp, Forward) == Some(nextinp) ==> ListTreeThread(rer, code, nextinp, treeblocked, pvs.blocked))
      && (AdvanceInput(inp, Forward) == None ==> pvs.blocked == [] && treeblocked == [])
      && SeenInclusion(rer, code, inp, treeseen, pvs.seen, HdError(treeactive), HeadPc(pvs.active))
  }

  // Coq: tt_same_gm
  /** A `TreeThread` witness forces the tree-side and thread-side group maps to agree. */
  lemma TtSameGm(rer: RegExpRecord, t: Tree, gm1: GroupMap, pc: Label, gm2: GroupMap, b: LoopBool, code: Code, inp: Input)
    requires TreeThread(rer, code, inp, (t, gm1), Thr(pc, gm2, b))
    ensures gm1 == gm2
  {}

  // ===== Axiomatized (the simulation proof; the development's hardest). See PROGRESS.md. =====

  // Coq: compilation_stutter_wf — compiled code has well-founded stuttering (every stuttering
  // instruction whose epsilon-step produces a single active thread advances pc).
  /** Any `Compilation(r)` satisfies `StutterWf`: a `Jmp` target is always a strictly larger
      label (`CompileJumps`), and a `BeginLoop` always steps to `pc + 1`. */
  lemma CompilationStutterWf(rer: RegExpRecord, r: Regex, code: Code)
    requires Compilation(r) == code
    ensures StutterWf(rer, code)
  {
    var cc := Compile(r, 0).0;
    var frsh := Compile(r, 0).1;
    assert code == cc + [Accept];
    CompileNfaRep(r, cc, 0, frsh, []);
    assert [] + cc == cc;                 // NfaRep(r, cc, 0, frsh)
    FreshCorrect(r, 0, cc, frsh);         // frsh == |cc|
    forall pc: Label, gm: GroupMap, bl: LoopBool, nextpc: Label, nextgm: GroupMap, nextb: LoopBool, inp: Input
      | Stutters(pc, code) && EpsilonStep(rer, Thr(pc, gm, bl), code, inp) == EpsActive([Thr(nextpc, nextgm, nextb)])
      ensures pc < nextpc
    {
      match GetPc(code, pc) {
        case Some(Jmp(np)) =>
          // epsilon_step at Jmp gives [Thr(np,gm,bl)], so nextpc == np.
          GetFirst([Accept], cc);            // GetPc(code, |cc|) == Some(Accept)
          assert pc < |cc|;                  // pc points to a Jmp, not the trailing Accept
          GetPrev(cc, [Accept], pc, Jmp(np));   // GetPc(cc, pc) == Some(Jmp(np))
          CompileJumps(r, cc, 0, frsh, pc, np);
        case Some(BeginLoop) =>
          // epsilon_step at BeginLoop gives [Thr(pc+1, gm, CannotExit)], so nextpc == pc+1.
        case _ =>
          // KillThread → EpsDead (empty); non-stuttering instrs excluded by Stutters. Vacuous.
      }
    }
  }

  // Coq: initial_pike_inv (Theorem 13) — the initial PikeTree/PikeVM states satisfy pike_inv.
  /** Theorem 13: the initial `PikeTreeState` (holding `tree`) and the initial `PikeVmState`
      (holding `Compilation(r)`'s entry thread) satisfy `PikeInv`. */
  lemma InitialPikeInv(rer: RegExpRecord, r: Regex, inp: Input, tree: Tree, code: Code)
    requires BoolTree(rer, [Areg(r)], inp, CanExit, tree)
    requires Compilation(r) == code
    requires PikeRegex(r)
    ensures PikeInv(rer, code, PikeTreeInitialState(tree, inp), PikeVmInitialState(inp))
  {
    var cc := Compile(r, 0).0;
    var frsh := Compile(r, 0).1;
    assert code == cc + [Accept];
    CompileNfaRep(r, cc, 0, frsh, []);
    assert [] + cc == cc;                  // NfaRep(r, cc, 0, frsh)
    FreshCorrect(r, 0, cc, frsh);           // frsh == |cc|
    NfaRepExtend(r, cc, 0, frsh, [Accept]); // NfaRep(r, cc+[Accept]=code, 0, frsh)
    assert NfaRep(r, code, 0, frsh);
    GetFirst([Accept], cc);                 // GetPc(code, frsh) == Some(Accept)
    // ActionsRep([Areg r], code, 0): cons_bc with pcmid = frsh
    assert ActionsRep([], code, frsh);                 // empty_bc
    assert ActionRep(Areg(r), code, 0, frsh);          // == NfaRep(r, code, 0, frsh)
    assert [Areg(r)][0] == Areg(r) && [Areg(r)][1..] == [];
    assert ActionsRep([Areg(r)], code, 0);
    assert PikeActions([Areg(r)]);
    // TreeThread via tt_eq (witness acts = [Areg r])
    assert TreeThread(rer, code, inp, (tree, Empty), Thr(0, Empty, CanExit));
    // ListTreeThread for the singleton active lists
    assert ListTreeThread(rer, code, inp, [], []);
    assert [(tree, Empty)][1..] == [] && [Thr(0, Empty, CanExit)][1..] == [];
    assert ListTreeThread(rer, code, inp, [(tree, Empty)], [Thr(0, Empty, CanExit)]);
    // SeenInclusion holds vacuously (InitialSeenPcs is empty)
    assert SeenInclusion(rer, code, inp, InitialSeenTrees, InitialSeenPcs, HdError([(tree, Empty)]), HeadPc([Thr(0, Empty, CanExit)]));
  }

  // ===== Seen-inclusion lemmas (the set-membership bookkeeping of invariant_preservation). =====

  // Coq: initial_inclusion — empty seen sets satisfy the inclusion vacuously.
  /** `SeenInclusion` holds vacuously for the empty seen sets `InitialSeenTrees` /
      `InitialSeenPcs` — there is nothing to check membership against. */
  lemma InitialInclusion(rer: RegExpRecord, c: Code, inp: Input, current: Option<(Tree, GroupMap)>, currentpc: Label)
    ensures SeenInclusion(rer, c, inp, InitialSeenTrees, InitialSeenPcs, current, currentpc)
  {
    forall pc: Label, b: LoopBool | Inseenpc(InitialSeenPcs, pc, b)
      ensures false
    {
      InitialNothingPc(pc, b);
    }
  }

  // Coq: add_inclusion — after memoizing the current (tree, thread), the inclusion still holds.
  /** After memoizing the current `(t, gm)`/thread pair into both seen sets, `SeenInclusion`
      still holds for whatever comes next. */
  lemma AddInclusion(rer: RegExpRecord, c: Code, inp: Input, treeseen: SeenTrees, threadseen: SeenPcs,
                     t: Tree, pc: Label, gm: GroupMap, b: LoopBool, nextcurrent: Option<(Tree, GroupMap)>, nextpc: Label)
    requires SeenInclusion(rer, c, inp, treeseen, threadseen, Some((t, gm)), pc)
    requires TreeThread(rer, c, inp, (t, gm), Thr(pc, gm, b))
    ensures SeenInclusion(rer, c, inp, AddSeenTrees(treeseen, t), AddThread(threadseen, Thr(pc, gm, b)), nextcurrent, nextpc)
  {
    forall pc0: Label, b0: LoopBool | Inseenpc(AddThread(threadseen, Thr(pc, gm, b)), pc0, b0)
      ensures (exists t': Tree, gm': GroupMap :: Inseen(AddSeenTrees(treeseen, t), t') && TreeThread(rer, c, inp, (t', gm'), Thr(pc0, gm', b0)))
           || (Stutters(pc0, c) && exists t': Tree, gm': GroupMap :: pc0 < nextpc && nextcurrent == Some((t', gm')) && TreeThread(rer, c, inp, (t', gm'), Thr(pc0, gm', b0)))
    {
      assert AddThread(threadseen, Thr(pc, gm, b)) == AddSeenPcs(threadseen, pc, b);
      InpcAdd(threadseen, pc0, b0, pc, b);
      if (pc0, b0) == (pc, b) {
        InAdd(treeseen, t, t);   // Inseen(AddSeenTrees(treeseen,t), t)
        assert Inseen(AddSeenTrees(treeseen, t), t) && TreeThread(rer, c, inp, (t, gm), Thr(pc0, gm, b0));
      } else {
        assert Inseenpc(threadseen, pc0, b0);
        if exists t': Tree, gm': GroupMap :: Inseen(treeseen, t') && TreeThread(rer, c, inp, (t', gm'), Thr(pc0, gm', b0)) {
          var t', gm' :| Inseen(treeseen, t') && TreeThread(rer, c, inp, (t', gm'), Thr(pc0, gm', b0));
          InAdd(treeseen, t', t);   // Inseen(AddSeenTrees(treeseen,t), t')
        } else {
          // right disjunct: current == Some((t,gm)) forces the witness tree to be t
          var t', gm' :| pc0 < pc && Some((t, gm)) == Some((t', gm')) && TreeThread(rer, c, inp, (t', gm'), Thr(pc0, gm', b0));
          InAdd(treeseen, t', t);
        }
      }
    }
  }

  // Coq: skip_inclusion — skipping an already-seen tree leaves the inclusion intact (the right,
  // stuttering disjunct can be promoted to the left because the tree was already memoized).
  /** Skipping an already-seen tree (`Inseen(treeseen, tree)`) preserves `SeenInclusion`: any
      stuttering witness for the current tree can be promoted to the ordinary
      already-memoized case. */
  lemma SkipInclusion(rer: RegExpRecord, c: Code, inp: Input, treeseen: SeenTrees, threadseen: SeenPcs,
                      tree: Tree, gm: GroupMap, currentpc: Label, current: Option<(Tree, GroupMap)>, nextpc: Label)
    requires SeenInclusion(rer, c, inp, treeseen, threadseen, Some((tree, gm)), currentpc)
    requires Inseen(treeseen, tree)
    ensures SeenInclusion(rer, c, inp, treeseen, threadseen, current, nextpc)
  {
    forall pc: Label, b: LoopBool | Inseenpc(threadseen, pc, b)
      ensures (exists t': Tree, gm': GroupMap :: Inseen(treeseen, t') && TreeThread(rer, c, inp, (t', gm'), Thr(pc, gm', b)))
           || (Stutters(pc, c) && exists t': Tree, gm': GroupMap :: pc < nextpc && current == Some((t', gm')) && TreeThread(rer, c, inp, (t', gm'), Thr(pc, gm', b)))
    {
      if exists t': Tree, gm': GroupMap :: Inseen(treeseen, t') && TreeThread(rer, c, inp, (t', gm'), Thr(pc, gm', b)) {
      } else {
        // right disjunct gives current==Some((tree,gm)); but tree is already in treeseen ⇒ left disjunct
        var t', gm' :| pc < currentpc && Some((tree, gm)) == Some((t', gm')) && TreeThread(rer, c, inp, (t', gm'), Thr(pc, gm', b));
        assert Inseen(treeseen, t');   // t' == tree, which is seen
      }
    }
  }

  // Coq: stutter_inclusion — a stuttering thread memoizes a pc strictly below the current one, so the
  // tree (not yet memoized) is recorded in the right, stuttering disjunct.
  /** Recording a stuttering pc (one below `nextpc`) into `threadseen` preserves
      `SeenInclusion`, since the not-yet-memoized tree is captured by the stuttering disjunct. */
  lemma StutterInclusion(rer: RegExpRecord, c: Code, inp: Input, treeseen: SeenTrees, threadseen: SeenPcs,
                         t: Tree, gm: GroupMap, pc: Label, b: LoopBool, nextpc: Label)
    requires pc < nextpc
    requires SeenInclusion(rer, c, inp, treeseen, threadseen, Some((t, gm)), pc)
    requires Stutters(pc, c)
    requires TreeThread(rer, c, inp, (t, gm), Thr(pc, gm, b))
    ensures SeenInclusion(rer, c, inp, treeseen, AddSeenPcs(threadseen, pc, b), Some((t, gm)), nextpc)
  {
    forall pc0: Label, b0: LoopBool | Inseenpc(AddSeenPcs(threadseen, pc, b), pc0, b0)
      ensures (exists t': Tree, gm': GroupMap :: Inseen(treeseen, t') && TreeThread(rer, c, inp, (t', gm'), Thr(pc0, gm', b0)))
           || (Stutters(pc0, c) && exists t': Tree, gm': GroupMap :: pc0 < nextpc && Some((t, gm)) == Some((t', gm')) && TreeThread(rer, c, inp, (t', gm'), Thr(pc0, gm', b0)))
    {
      InpcAdd(threadseen, pc0, b0, pc, b);
      if (pc0, b0) == (pc, b) {
        // right disjunct: pc0 == pc < nextpc, current == Some((t,gm)), Stutters(pc), TT
        assert Stutters(pc0, c) && pc0 < nextpc && Some((t, gm)) == Some((t, gm)) && TreeThread(rer, c, inp, (t, gm), Thr(pc0, gm, b0));
      } else {
        assert Inseenpc(threadseen, pc0, b0);
        if exists t': Tree, gm': GroupMap :: Inseen(treeseen, t') && TreeThread(rer, c, inp, (t', gm'), Thr(pc0, gm', b0)) {
        } else {
          var t', gm' :| pc0 < pc && Some((t, gm)) == Some((t', gm')) && TreeThread(rer, c, inp, (t', gm'), Thr(pc0, gm', b0));
          // pc0 < pc < nextpc, current still Some((t,gm))
        }
      }
    }
  }

  // ----- list_tree_thread helpers -----
  /** `ListTreeThread` relates lists of equal length. */
  lemma LttLenEq(rer: RegExpRecord, code: Code, inp: Input, tl: seq<(Tree, GroupMap)>, vl: seq<Thread>)
    requires ListTreeThread(rer, code, inp, tl, vl)
    ensures |tl| == |vl|
    decreases tl
  {
    if |tl| > 0 { LttLenEq(rer, code, inp, tl[1..], vl[1..]); }
  }

  // Coq: ltt_app
  /** `ListTreeThread` is preserved by list concatenation on both sides. */
  lemma LttApp(rer: RegExpRecord, code: Code, inp: Input, tl1: seq<(Tree, GroupMap)>, tl2: seq<(Tree, GroupMap)>, vl1: seq<Thread>, vl2: seq<Thread>)
    requires ListTreeThread(rer, code, inp, tl1, vl1)
    requires ListTreeThread(rer, code, inp, tl2, vl2)
    ensures ListTreeThread(rer, code, inp, tl1 + tl2, vl1 + vl2)
    decreases tl1
  {
    if |tl1| == 0 {
      assert |vl1| == 0;
      assert tl1 + tl2 == tl2 && vl1 + vl2 == vl2;
    } else {
      LttApp(rer, code, inp, tl1[1..], tl2, vl1[1..], vl2);
      assert (tl1 + tl2)[0] == tl1[0] && (tl1 + tl2)[1..] == tl1[1..] + tl2;
      assert (vl1 + vl2)[0] == vl1[0] && (vl1 + vl2)[1..] == vl1[1..] + vl2;
    }
  }

  // ===== The remaining deep simulation kernel (relating tree_bfs_step to epsilon_step through the
  // tree_thread / bool_tree / actions_rep machinery). These invert tree_thread, induct on bool_tree,
  // and invert actions_rep; the NOSTUTTER hypothesis is what discards the jump chain. Axiomatized;
  // the main invariant_preservation theorem below is PROVED from them + the inclusion/ltt lemmas. =====

  // Bridge: a tree_thread induces a tree_rep at the same pc. tt_eq uses actions_tree_rep; tt_reset /
  // tt_begin recurse and apply tr_reset / tr_begin. (least lemma over the tree_thread derivation.)
  /** Bridges the two representation predicates: a `TreeThread` witness at `pc` induces a
      `TreeRep.TreeRep` at the same `pc` (`tt_eq` goes through `ActionsTreeRep`; `tt_reset`/
      `tt_begin` recurse and apply `TreeRep`'s matching stuttering rules). */
  least lemma TreeThreadTreeRep(rer: RegExpRecord, code: Code, inp: Input, t: Tree, gm: GroupMap, pc: Label, b: LoopBool)
    requires TreeThread(rer, code, inp, (t, gm), Thr(pc, gm, b))
    ensures TR.TreeRep(rer, t, code, pc, inp, b)
  {
    if exists acts: Actions :: BoolTree(rer, acts, inp, b, t) && ActionsRep(acts, code, pc) && PikeActions(acts) {
      var acts :| BoolTree(rer, acts, inp, b, t) && ActionsRep(acts, code, pc) && PikeActions(acts);
      TR.ActionsTreeRep(rer, acts, code, pc, inp, b, t);   // ⇒ TreeRep(t, code, pc, inp, b)
    } else if t.GroupActionT? && t.g.Reset? && GetPc(code, pc) == Some(ResetRegs(t.g.gl)) {
      // tt_reset disjunct holds (tt_eq ruled out; tt_begin needs GetPc==BeginLoop ≠ ResetRegs)
      TreeThreadTreeRep(rer, code, inp, t.t, GMReset(t.g.gl, gm), pc + 1, b);   // ⇒ TreeRep(t.t, .., pc+1, .., b)
      // tr_reset
    } else {
      // tt_begin disjunct (GetPc==BeginLoop)
      TreeThreadTreeRep(rer, code, inp, t, gm, pc + 1, CannotExit);   // ⇒ TreeRep(t, .., pc+1, .., CannotExit)
      // tr_begin
    }
  }

  // Coq: tt_same_tree — now PROVED (rests on ActionsTreeRep via the bridge + the proved TreeRepDeterm).
  /** Two `TreeThread` witnesses for the same thread state (`pc`, `b`) agree on the tree — via
      `TreeThreadTreeRep` plus `TreeRep.TreeRepDeterm`. */
  lemma TtSameTree(rer: RegExpRecord, code: Code, inp: Input, t1: Tree, gm1: GroupMap, t2: Tree, gm2: GroupMap, pc: Label, b: LoopBool)
    requires TreeThread(rer, code, inp, (t1, gm1), Thr(pc, gm1, b))
    requires TreeThread(rer, code, inp, (t2, gm2), Thr(pc, gm2, b))
    ensures t1 == t2
  {
    TreeThreadTreeRep(rer, code, inp, t1, gm1, pc, b);
    TreeThreadTreeRep(rer, code, inp, t2, gm2, pc, b);
    TR.TreeRepDeterm(rer, code, pc, inp, b, t1, t2);
  }

  // Fuel core of generate_active (tt_eq case): peel Epsilon/Sequence prefixes, then at the leading
  // atom construct the EpsActive step and the child tree_thread(s). Choice (Disjunction / star) builds
  // two children; the star's iter child is built via tt_begin ∘ tt_reset ∘ tt_eq.
  /** Fuel-indexed core of `GenerateActive`: peels `Epsilon`/`Sequence` prefixes, then at the
      leading atom shows the bytecode `EpsilonStep` produces active successor(s)
      `ListTreeThread`-related to the tree's `TreeBfsStep` children (a `Choice` for
      `Disjunction`/quantifier iteration, the latter built via `tt_begin ∘ tt_reset ∘ tt_eq`). */
  lemma GenerateActiveF(rer: RegExpRecord, acts: Actions, code: Code, pc: Label, inp: Input, b: LoopBool, t: Tree, gm: GroupMap, na: seq<(Tree, GroupMap)>, n: nat)
    requires PikeActions(acts)
    requires TR.ActionsRepFuel(acts, code, pc, n)
    requires BoolTree(rer, acts, inp, b, t)
    requires !Stutters(pc, code)
    requires TreeBfsStep(t, gm, Idx(inp)) == StepActive(na)
    ensures exists threadactive :: EpsilonStep(rer, Thr(pc, gm, b), code, inp) == EpsActive(threadactive)
                               && ListTreeThread(rer, code, inp, na, threadactive)
    decreases ActionsRegexSize(acts), n
  {
    if |acts| == 0 {
      assert t == Match;   // StepMatch ≠ StepActive ⇒ contradiction
    } else if exists pcstart: nat :: GetPc(code, pc) == Some(Jmp(pcstart)) && TR.ActionsRepFuel(acts, code, pcstart, n - 1) {
      assert Stutters(pc, code);
    } else {
      var cont := acts[1..];
      var pcmid: nat :| ActionRep(acts[0], code, pc, pcmid) && TR.ActionsRepFuel(cont, code, pcmid, n - 1);
      PikeActionsTail(acts);
      assert acts == [acts[0]] + cont;
      PikeActionsConsIff(acts[0], cont);
      match acts[0]
      case Acheck(strcheck) =>
        if b == CanExit {
          match t {
            case Progress(tc) =>
              FuelToActionsRepWrap(cont, code, pcmid, n - 1);
              assert TreeThread(rer, code, inp, (tc, gm), Thr(pcmid, gm, CanExit));   // tt_eq cont
              assert [(tc, gm)][1..] == [] && [Thr(pcmid, gm, CanExit)][1..] == [];
              assert ListTreeThread(rer, code, inp, [(tc, gm)], [Thr(pcmid, gm, CanExit)]);
            case _ =>
          }
        } else {
          assert t == Mismatch;
          assert GetPc(code, pc) == Some(EndLoop(pcmid));   // from ActionRep(Acheck, ..)
          assert na == [];
          assert ListTreeThread(rer, code, inp, [], []);
          assert EpsilonStep(rer, Thr(pc, gm, b), code, inp) == EpsActive([]);   // EndLoop + CannotExit ⇒ EpsDead
        }
      case Aclose(gid) =>
        match t {
          case GroupActionT(g, tc) =>
            var gmc := GMClose(Idx(inp), gid, gm);
            FuelToActionsRepWrap(cont, code, pc + 1, n - 1);
            assert TreeThread(rer, code, inp, (tc, gmc), Thr(pc + 1, gmc, b));   // tt_eq cont
            assert GMUpdate(Close(gid), Idx(inp), gm) == gmc;
            assert [(tc, gmc)][1..] == [] && [Thr(pc + 1, gmc, b)][1..] == [];
            assert ListTreeThread(rer, code, inp, [(tc, gmc)], [Thr(pc + 1, gmc, b)]);
          case _ =>
        }
      case Areg(r) =>
        assert PikeRegex(r);
        match r
        case Epsilon =>
          GenerateActiveF(rer, cont, code, pc, inp, b, t, gm, na, n - 1);
        case Character(cd) => {
          match ReadChar(rer, cd, inp, Forward) {
            case None =>
              assert t == Mismatch;
              CannotReadCorrect(inp, rer, cd, Forward);   // CheckRead == CannotRead
              assert GetPc(code, pc) == Some(Consume(cd));
              assert na == [];
              assert ListTreeThread(rer, code, inp, [], []);
              assert EpsilonStep(rer, Thr(pc, gm, b), code, inp) == EpsActive([]);
            case Some(pair) => assert t.Read?;   // StepBlocked ≠ StepActive ⇒ contradiction
          }
        }
        case AnchorR(a) => {
          // NfaRep(AnchorR) ⇒ GetPc(pc) == CheckAnchor(a), pcmid == pc + 1
          if Semantics.AnchorSatisfied(rer, a, inp) {
            match t {
              case AnchorPass(a2, tc) =>
                FuelToActionsRepWrap(cont, code, pc + 1, n - 1);
                assert TreeThread(rer, code, inp, (tc, gm), Thr(pc + 1, gm, b));   // tt_eq cont
                assert [(tc, gm)][1..] == [] && [Thr(pc + 1, gm, b)][1..] == [];
                assert ListTreeThread(rer, code, inp, [(tc, gm)], [Thr(pc + 1, gm, b)]);
              case _ =>
            }
          } else {
            assert t == Mismatch;
            assert GetPc(code, pc) == Some(CheckAnchor(a));
            assert na == [];
            assert ListTreeThread(rer, code, inp, [], []);
            assert EpsilonStep(rer, Thr(pc, gm, b), code, inp) == EpsActive([]);
          }
        }
        case Disjunction(r1, r2) => {
          PikeActionsConsIff(Areg(r1), cont);
          PikeActionsConsIff(Areg(r2), cont);
          var e1: nat :| GetPc(code, pc) == Some(Fork(pc + 1, e1 + 1)) && NfaRep(r1, code, pc + 1, e1)
                       && GetPc(code, e1) == Some(Jmp(pcmid)) && NfaRep(r2, code, e1 + 1, pcmid);
          match t {
            case Choice(ta, tb) =>
              FuelToActionsRepWrap(cont, code, pcmid, n - 1);
              var la := [Areg(r1)] + cont;
              assert ActionsRep(cont, code, e1);   // jump_bc (GetPc(e1)==Jmp(pcmid))
              assert la[0] == Areg(r1) && la[1..] == cont && ActionRep(Areg(r1), code, pc + 1, e1);
              assert ActionsRep(la, code, pc + 1);
              assert TreeThread(rer, code, inp, (ta, gm), Thr(pc + 1, gm, b));   // tt_eq la
              var lb := [Areg(r2)] + cont;
              assert lb[0] == Areg(r2) && lb[1..] == cont && ActionRep(Areg(r2), code, e1 + 1, pcmid);
              assert ActionsRep(lb, code, e1 + 1);
              assert TreeThread(rer, code, inp, (tb, gm), Thr(e1 + 1, gm, b));   // tt_eq lb
              assert [(ta, gm), (tb, gm)][1..] == [(tb, gm)] && [(tb, gm)][1..] == [];
              assert [Thr(pc + 1, gm, b), Thr(e1 + 1, gm, b)][1..] == [Thr(e1 + 1, gm, b)] && [Thr(e1 + 1, gm, b)][1..] == [];
              assert ListTreeThread(rer, code, inp, [(tb, gm)], [Thr(e1 + 1, gm, b)]);
              assert ListTreeThread(rer, code, inp, [(ta, gm), (tb, gm)], [Thr(pc + 1, gm, b), Thr(e1 + 1, gm, b)]);
            case _ =>
          }
        }
        case Sequence(r1, r2) => {
          PikeActionsConsIff(Areg(r2), cont);
          PikeActionsConsIff(Areg(r1), [Areg(r2)] + cont);
          assert NfaRep(Sequence(r1, r2), code, pc, pcmid);
          var e1: nat :| NfaRep(r1, code, pc, e1) && NfaRep(r2, code, e1, pcmid);
          TR.FuelToActionsRep(cont, code, pcmid, n - 1);
          var sa := [Areg(r1), Areg(r2)] + cont;
          assert sa == [Areg(r1)] + ([Areg(r2)] + cont);
          assert ActionRep(Areg(r2), code, e1, pcmid);
          assert ([Areg(r2)] + cont)[0] == Areg(r2) && ([Areg(r2)] + cont)[1..] == cont;
          assert ActionsRep([Areg(r2)] + cont, code, e1);
          assert ActionRep(Areg(r1), code, pc, e1) && sa[0] == Areg(r1) && sa[1..] == [Areg(r2)] + cont;
          assert ActionsRep(sa, code, pc);
          assert ActionsRegexSize(sa) < ActionsRegexSize(acts);
          TR.ActionsRepToFuel(sa, code, pc);
          var nn: nat :| TR.ActionsRepFuel(sa, code, pc, nn);
          GenerateActiveF(rer, sa, code, pc, inp, b, t, gm, na, nn);
        }
        case Quantified(greedy, min, delta, r1) => {
          var gidl := DefGroups(r1);
          if min > 0 {
            // FORCED iteration: the tree is GroupActionT(Reset(gidl), tc); the
            // VM's ResetRegs at pc spawns one successor at pc+1 with reset gm.
            var quant1 := Quantified(greedy, min - 1, delta, r1);
            var em: nat :| NfaRepMin(min, gidl, r1, code, pc, em)
              && (match delta
                  case Inf =>
                    exists e1: nat ::
                      GetPc(code, em) == Some(GreedyFork(greedy, em + 1, e1 + 1))
                      && GetPc(code, em + 1) == Some(BeginLoop)
                      && GetPc(code, em + 2) == Some(ResetRegs(gidl))
                      && NfaRep(r1, code, em + 3, e1)
                      && GetPc(code, e1) == Some(EndLoop(em))
                      && pcmid == e1 + 1
                  case NN(k) => NfaRepOpt(k, greedy, gidl, r1, code, em, pcmid));
            var eb: nat :| GetPc(code, pc) == Some(ResetRegs(gidl))
              && NfaRep(r1, code, pc + 1, eb)
              && NfaRepMin(min - 1, gidl, r1, code, eb, em);
            match delta {
              case Inf =>
                var e1: nat :| GetPc(code, em) == Some(GreedyFork(greedy, em + 1, e1 + 1))
                  && GetPc(code, em + 1) == Some(BeginLoop)
                  && GetPc(code, em + 2) == Some(ResetRegs(gidl))
                  && NfaRep(r1, code, em + 3, e1)
                  && GetPc(code, e1) == Some(EndLoop(em))
                  && pcmid == e1 + 1;
                NfaRepQuantIntroInf(greedy, min - 1, r1, code, eb, em, e1, pcmid);
              case NN(k) =>
                NfaRepQuantIntroNN(greedy, min - 1, k, r1, code, eb, em, pcmid);
            }
            assert NfaRep(quant1, code, eb, pcmid);
            match t {
              case GroupActionT(g, tc) =>
                var gmr := GMReset(gidl, gm);
                FuelToActionsRepWrap(cont, code, pcmid, n - 1);
                var lq := [Areg(quant1)] + cont;
                assert ActionRep(Areg(quant1), code, eb, pcmid) && lq[0] == Areg(quant1) && lq[1..] == cont;
                assert ActionsRep(lq, code, eb);
                var ia := [Areg(r1)] + lq;
                assert ActionRep(Areg(r1), code, pc + 1, eb) && ia[0] == Areg(r1) && ia[1..] == lq;
                assert ActionsRep(ia, code, pc + 1);
                assert ia == [Areg(r1), Areg(quant1)] + cont;
                TR.ActionsRepToFuel(ia, code, pc + 1);
                var ni: nat :| TR.ActionsRepFuel(ia, code, pc + 1, ni);
                TR.FuelToActionsRep(ia, code, pc + 1, ni);
                assert TreeThread(rer, code, inp, (tc, gmr), Thr(pc + 1, gmr, b));   // tt_eq ia
                assert GMUpdate(Reset(gidl), Idx(inp), gm) == gmr;
                assert [(tc, gmr)][1..] == [] && [Thr(pc + 1, gmr, b)][1..] == [];
                assert ListTreeThread(rer, code, inp, [(tc, gmr)], [Thr(pc + 1, gmr, b)]);
              case _ =>
            }
          } else if delta == NN(0) {
            // spent quantifier: no code (pcmid == pc); the tree is cont's tree
            var em: nat := NfaRepQuantInvNN(greedy, min, 0, r1, code, pc, pcmid);
            assert em == pc;
            assert pcmid == pc;
            assert ActionsRegexSize(cont) < ActionsRegexSize(acts);
            GenerateActiveF(rer, cont, code, pc, inp, b, t, gm, na, n - 1);
          } else if delta.NN? {
            // bounded layer: fork (pc+1, pcmid); the iterate continuation is
            // the NN(k-1) quantifier at e1+1; skip exits to the common pcmid
            var k := delta.n;
            var em: nat := NfaRepQuantInvNN(greedy, min, k, r1, code, pc, pcmid);
            assert em == pc;
            assert NfaRepOpt(k, greedy, gidl, r1, code, pc, pcmid);
            var quant := Quantified(greedy, 0, FS.NoiPred(delta), r1);
            assert quant == Quantified(greedy, 0, NN(k - 1), r1);
            var e1: nat :| GetPc(code, pc) == Some(GreedyFork(greedy, pc + 1, pcmid))
              && GetPc(code, pc + 1) == Some(BeginLoop)
              && GetPc(code, pc + 2) == Some(ResetRegs(gidl))
              && NfaRep(r1, code, pc + 3, e1)
              && GetPc(code, e1) == Some(EndLoop(e1 + 1))
              && NfaRepOpt(k - 1, greedy, gidl, r1, code, e1 + 1, pcmid);
            match t {
              case Choice(ta, tb) =>
                var itert := if greedy then ta else tb;
                var skipt := if greedy then tb else ta;
                match itert {
                  case GroupActionT(g, ti) =>
                    FuelToActionsRepWrap(cont, code, pcmid, n - 1);
                    assert TreeThread(rer, code, inp, (skipt, gm), Thr(pcmid, gm, b));   // tt_eq cont (skip)
                    PikeActionsConsIff(Areg(quant), cont);
                    PikeActionsConsIff(Acheck(inp), [Areg(quant)] + cont);
                    PikeActionsConsIff(Areg(r1), [Acheck(inp)] + ([Areg(quant)] + cont));
                    var lq := [Areg(quant)] + cont;
                    assert NfaRepMin(0, gidl, r1, code, e1 + 1, e1 + 1);
                    NfaRepQuantIntroNN(greedy, 0, k - 1, r1, code, e1 + 1, e1 + 1, pcmid);
                    assert ActionRep(Areg(quant), code, e1 + 1, pcmid) && lq[0] == Areg(quant) && lq[1..] == cont;
                    assert ActionsRep(lq, code, e1 + 1);
                    var lc := [Acheck(inp)] + lq;
                    assert ActionRep(Acheck(inp), code, e1, e1 + 1) && lc[0] == Acheck(inp) && lc[1..] == lq;
                    assert ActionsRep(lc, code, e1);
                    var ia := [Areg(r1)] + lc;
                    assert ActionRep(Areg(r1), code, pc + 3, e1) && ia[0] == Areg(r1) && ia[1..] == lc;
                    assert ActionsRep(ia, code, pc + 3);
                    assert ia == [Areg(r1), Acheck(inp), Areg(quant)] + cont;
                    TR.ActionsRepToFuel(ia, code, pc + 3);
                    var ni: nat :| TR.ActionsRepFuel(ia, code, pc + 3, ni);
                    var gmr := GMReset(gidl, gm);
                    TR.FuelToActionsRep(ia, code, pc + 3, ni);
                    assert TreeThread(rer, code, inp, (ti, gmr), Thr(pc + 3, gmr, CannotExit));   // tt_eq ia
                    assert TreeThread(rer, code, inp, (itert, gm), Thr(pc + 2, gm, CannotExit));   // tt_reset
                    assert TreeThread(rer, code, inp, (itert, gm), Thr(pc + 1, gm, b));            // tt_begin
                    assert [(ta, gm), (tb, gm)][1..] == [(tb, gm)] && [(tb, gm)][1..] == [];
                    if greedy {
                      assert ListTreeThread(rer, code, inp, [(tb, gm)], [Thr(pcmid, gm, b)]);
                      assert ListTreeThread(rer, code, inp, [(ta, gm), (tb, gm)], [Thr(pc + 1, gm, b), Thr(pcmid, gm, b)]);
                    } else {
                      assert ListTreeThread(rer, code, inp, [(tb, gm)], [Thr(pc + 1, gm, b)]);
                      assert ListTreeThread(rer, code, inp, [(ta, gm), (tb, gm)], [Thr(pcmid, gm, b), Thr(pc + 1, gm, b)]);
                    }
                  case _ =>
                }
              case _ =>
            }
          } else {
          // the plain star: fast-path shape, original proof
          var quant := Quantified(greedy, 0, FS.NoiPred(delta), r1);
          var e1: nat :| GetPc(code, pc) == Some(GreedyFork(greedy, pc + 1, e1 + 1)) && GetPc(code, pc + 1) == Some(BeginLoop)
                       && GetPc(code, pc + 2) == Some(ResetRegs(gidl)) && NfaRep(r1, code, pc + 3, e1)
                       && GetPc(code, e1) == Some(EndLoop(pc)) && pcmid == e1 + 1;
          match t {
            case Choice(ta, tb) =>
              var itert := if greedy then ta else tb;
              var skipt := if greedy then tb else ta;
              match itert {
                case GroupActionT(g, ti) =>
                  FuelToActionsRepWrap(cont, code, e1 + 1, n - 1);
                  assert TreeThread(rer, code, inp, (skipt, gm), Thr(e1 + 1, gm, b));   // tt_eq cont (skip)
                  // iter child: build ActionsRep([Areg r1, Acheck(inp), Areg quant]+cont, code, pc+3)
                  PikeActionsConsIff(Areg(quant), cont);
                  PikeActionsConsIff(Acheck(inp), [Areg(quant)] + cont);
                  PikeActionsConsIff(Areg(r1), [Acheck(inp)] + ([Areg(quant)] + cont));
                  var lq := [Areg(quant)] + cont;
                  assert ActionRep(Areg(quant), code, pc, pcmid) && lq[0] == Areg(quant) && lq[1..] == cont;
                  assert ActionsRep(lq, code, pc);
                  var lc := [Acheck(inp)] + lq;
                  assert ActionRep(Acheck(inp), code, e1, pc) && lc[0] == Acheck(inp) && lc[1..] == lq;
                  assert ActionsRep(lc, code, e1);
                  var ia := [Areg(r1)] + lc;
                  assert ActionRep(Areg(r1), code, pc + 3, e1) && ia[0] == Areg(r1) && ia[1..] == lc;
                  assert ActionsRep(ia, code, pc + 3);
                  assert ia == [Areg(r1), Acheck(inp), Areg(quant)] + cont;
                  TR.ActionsRepToFuel(ia, code, pc + 3);
                  var ni: nat :| TR.ActionsRepFuel(ia, code, pc + 3, ni);
                  var gmr := GMReset(gidl, gm);
                  // bool_tree free ⇒ BoolTree(ia, inp, CannotExit, ti); tt_eq at pc+3
                  TR.FuelToActionsRep(ia, code, pc + 3, ni);
                  assert TreeThread(rer, code, inp, (ti, gmr), Thr(pc + 3, gmr, CannotExit));   // tt_eq ia
                  assert TreeThread(rer, code, inp, (itert, gm), Thr(pc + 2, gm, CannotExit));   // tt_reset
                  assert TreeThread(rer, code, inp, (itert, gm), Thr(pc + 1, gm, b));            // tt_begin
                  assert [(ta, gm), (tb, gm)][1..] == [(tb, gm)] && [(tb, gm)][1..] == [];
                  if greedy {
                    assert ListTreeThread(rer, code, inp, [(tb, gm)], [Thr(e1 + 1, gm, b)]);
                    assert ListTreeThread(rer, code, inp, [(ta, gm), (tb, gm)], [Thr(pc + 1, gm, b), Thr(e1 + 1, gm, b)]);
                  } else {
                    assert ListTreeThread(rer, code, inp, [(tb, gm)], [Thr(pc + 1, gm, b)]);
                    assert ListTreeThread(rer, code, inp, [(ta, gm), (tb, gm)], [Thr(e1 + 1, gm, b), Thr(pc + 1, gm, b)]);
                  }
                case _ =>
              }
            case _ =>
          }
          }
        }
        case Group(gid, r1) => {
          PikeActionsConsIff(Aclose(gid), cont);
          PikeActionsConsIff(Areg(r1), [Aclose(gid)] + cont);
          var e1: nat :| GetPc(code, pc) == Some(SetRegOpen(gid)) && NfaRep(r1, code, pc + 1, e1)
                       && GetPc(code, e1) == Some(SetRegClose(gid)) && pcmid == e1 + 1;
          match t {
            case GroupActionT(g, tc) =>
              var gmo := GMOpen(Idx(inp), gid, gm);
              FuelToActionsRepWrap(cont, code, e1 + 1, n - 1);
              var lc := [Aclose(gid)] + cont;
              assert ActionRep(Aclose(gid), code, e1, e1 + 1) && lc[0] == Aclose(gid) && lc[1..] == cont;
              assert ActionsRep(lc, code, e1);
              var ga := [Areg(r1)] + lc;
              assert ActionRep(Areg(r1), code, pc + 1, e1) && ga[0] == Areg(r1) && ga[1..] == lc;
              assert ActionsRep(ga, code, pc + 1);
              assert ga == [Areg(r1), Aclose(gid)] + cont;
              TR.ActionsRepToFuel(ga, code, pc + 1);
              var ng: nat :| TR.ActionsRepFuel(ga, code, pc + 1, ng);
              TR.FuelToActionsRep(ga, code, pc + 1, ng);
              assert TreeThread(rer, code, inp, (tc, gmo), Thr(pc + 1, gmo, b));   // tt_eq ga
              assert GMUpdate(Open(gid), Idx(inp), gm) == gmo;
              assert [(tc, gmo)][1..] == [] && [Thr(pc + 1, gmo, b)][1..] == [];
              assert ListTreeThread(rer, code, inp, [(tc, gmo)], [Thr(pc + 1, gmo, b)]);
            case _ =>
          }
        }
    }
  }

  // Coq: generate_active — now PROVED. tt_reset gives a GroupActionT(Reset) step directly; tt_begin
  // contradicts !Stutters; tt_eq delegates to GenerateActiveF.
  /** At a non-stuttering pc, if the tree steps via `StepActive`, the bytecode's `EpsilonStep`
      produces `ListTreeThread`-related active successors. Handles `tt_reset` directly and
      delegates the `tt_eq` case to `GenerateActiveF`. */
  lemma GenerateActive(rer: RegExpRecord, code: Code, inp: Input, t: Tree, gm: GroupMap, pc: Label, b: LoopBool, treeactive: seq<(Tree, GroupMap)>)
    requires TreeBfsStep(t, gm, Idx(inp)) == StepActive(treeactive)
    requires !Stutters(pc, code)
    requires TreeThread(rer, code, inp, (t, gm), Thr(pc, gm, b))
    ensures exists threadactive :: EpsilonStep(rer, Thr(pc, gm, b), code, inp) == EpsActive(threadactive)
                               && ListTreeThread(rer, code, inp, treeactive, threadactive)
  {
    if exists acts: Actions :: BoolTree(rer, acts, inp, b, t) && ActionsRep(acts, code, pc) && PikeActions(acts) {
      var acts :| BoolTree(rer, acts, inp, b, t) && ActionsRep(acts, code, pc) && PikeActions(acts);
      TR.ActionsRepToFuel(acts, code, pc);
      var n: nat :| TR.ActionsRepFuel(acts, code, pc, n);
      GenerateActiveF(rer, acts, code, pc, inp, b, t, gm, treeactive, n);
    } else if t.GroupActionT? && t.g.Reset? && GetPc(code, pc) == Some(ResetRegs(t.g.gl)) {
      // tt_reset: t == GroupActionT(Reset(gl), tc); step resets the registers
      var gl := t.g.gl;
      var tc := t.t;
      var gmr := GMReset(gl, gm);
      assert TreeThread(rer, code, inp, (tc, gmr), Thr(pc + 1, gmr, b));   // tt_reset sub-thread
      assert TreeBfsStep(t, gm, Idx(inp)) == StepActive([(tc, GMUpdate(Reset(gl), Idx(inp), gm))]);
      assert GMUpdate(Reset(gl), Idx(inp), gm) == gmr;
      assert [(tc, gmr)][1..] == [] && [Thr(pc + 1, gmr, b)][1..] == [];
      assert ListTreeThread(rer, code, inp, [(tc, gmr)], [Thr(pc + 1, gmr, b)]);
    } else {
      assert GetPc(code, pc) == Some(BeginLoop);   // tt_begin ⇒ stuttering, contradiction
    }
  }

  // At a non-stuttering pc, a tree_rep of Match must be the tr_match rule (GetPc == Accept): the
  // stuttering rules tr_jmp/tr_begin are excluded, and no other rule produces a Match tree.
  /** At a non-stuttering pc, the only `TreeRep` rule that can produce `Match` is `tr_match`,
      so the instruction there must be `Accept`. */
  lemma TreeRepMatchInv(rer: RegExpRecord, code: Code, pc: Label, inp: Input, b: LoopBool)
    requires TR.TreeRep(rer, Match, code, pc, inp, b)
    requires !Stutters(pc, code)
    ensures GetPc(code, pc) == Some(Accept)
  {
    match GetPc(code, pc)
    case Some(Accept) =>
    case Some(Jmp(np)) => assert Stutters(pc, code);
    case Some(BeginLoop) => assert Stutters(pc, code);
    case _ => assert false;   // no tree_rep rule yields Match at this instruction
  }

  // Coq: generate_match — now PROVED (TreeThread⟹TreeRep + tr_match inversion + epsilon_step at Accept).
  /** At a non-stuttering pc, if the tree steps via `StepMatch` (so `t == Match`), the
      bytecode's `EpsilonStep` is `EpsMatch` — via `TreeThreadTreeRep` and `TreeRepMatchInv`. */
  lemma GenerateMatch(rer: RegExpRecord, code: Code, inp: Input, t: Tree, gm: GroupMap, pc: Label, b: LoopBool)
    requires TreeBfsStep(t, gm, Idx(inp)) == StepMatch
    requires !Stutters(pc, code)
    requires TreeThread(rer, code, inp, (t, gm), Thr(pc, gm, b))
    ensures EpsilonStep(rer, Thr(pc, gm, b), code, inp) == EpsMatch
  {
    assert t == Match;   // only Match yields StepMatch
    TreeThreadTreeRep(rer, code, inp, t, gm, pc, b);
    TreeRepMatchInv(rer, code, pc, inp, b);
  }

  // Coq: generate_blocked
  // Fuel core of generate_blocked: a tt_eq Read-tree at a non-stuttering pc peels Epsilon/Sequence
  // prefixes (↓ ActionsRegexSize, pc unchanged) until the leading Character (Consume) at pc, where it
  // constructs the EpsBlocked step and the child tt_eq at pc+1.
  /** Fuel-indexed core of `GenerateBlocked`: peels `Epsilon`/`Sequence` prefixes until the
      leading `Character`, where it shows the bytecode blocks with `EpsBlocked` and the
      continuation tree is `TreeThread`-related at `pc + 1` once the input advances. */
  lemma GenerateBlockedF(rer: RegExpRecord, acts: Actions, code: Code, pc: Label, inp: Input, b: LoopBool, c: char, nexttree: Tree, gm: GroupMap, n: nat)
    requires PikeActions(acts)
    requires TR.ActionsRepFuel(acts, code, pc, n)
    requires BoolTree(rer, acts, inp, b, Read(c, nexttree))
    requires !Stutters(pc, code)
    ensures EpsilonStep(rer, Thr(pc, gm, b), code, inp) == EpsBlocked(Thr(pc + 1, gm, CanExit))
    ensures forall nextinp :: AdvanceInput(inp, Forward) == Some(nextinp) ==> TreeThread(rer, code, nextinp, (nexttree, gm), Thr(pc + 1, gm, CanExit))
    ensures exists nextinp :: AdvanceInput(inp, Forward) == Some(nextinp)
    decreases ActionsRegexSize(acts), n
  {
    if |acts| == 0 {
      assert false;   // bool_tree([]) == Match ≠ Read
    } else if exists pcstart: nat :: GetPc(code, pc) == Some(Jmp(pcstart)) && TR.ActionsRepFuel(acts, code, pcstart, n - 1) {
      assert Stutters(pc, code);   // Jmp ⇒ stuttering, contradiction
    } else {
      var cont := acts[1..];
      var pcmid: nat :| ActionRep(acts[0], code, pc, pcmid) && TR.ActionsRepFuel(cont, code, pcmid, n - 1);
      PikeActionsTail(acts);
      assert acts == [acts[0]] + cont;
      PikeActionsConsIff(acts[0], cont);
      match acts[0]
      case Acheck(strcheck) =>      // Progress/Mismatch ≠ Read
      case Aclose(gid) =>           // GroupActionT ≠ Read
      case Areg(r) =>
        assert PikeRegex(r);
        match r
        case Epsilon =>
          GenerateBlockedF(rer, cont, code, pc, inp, b, c, nexttree, gm, n - 1);
        case Character(cd) => {
          match ReadChar(rer, cd, inp, Forward) {
            case None =>            // Mismatch ≠ Read
            case Some(pair) =>
              // bool_tree ⇒ pair.0 == c && BoolTree(cont, pair.1, CanExit, nexttree); GetPc(pc) == Consume(cd)
              ReadCharSuccessAdvance(rer, cd, inp, Forward, pair.0, pair.1);   // AdvanceInput == Some(pair.1)
              FuelToActionsRepWrap(cont, code, pc + 1, n - 1);                 // ActionsRep(cont, code, pc+1)
              forall nextinp | AdvanceInput(inp, Forward) == Some(nextinp)
                ensures TreeThread(rer, code, nextinp, (nexttree, gm), Thr(pc + 1, gm, CanExit))
              {
                assert nextinp == pair.1;
                assert TreeThread(rer, code, pair.1, (nexttree, gm), Thr(pc + 1, gm, CanExit));   // tt_eq, witness cont
              }
          }
        }
        case Disjunction(r1, r2) =>   // Choice ≠ Read
        case Sequence(r1, r2) =>
          PikeActionsConsIff(Areg(r2), cont);
          PikeActionsConsIff(Areg(r1), [Areg(r2)] + cont);
          assert NfaRep(Sequence(r1, r2), code, pc, pcmid);
          var e1: nat :| NfaRep(r1, code, pc, e1) && NfaRep(r2, code, e1, pcmid);
          TR.FuelToActionsRep(cont, code, pcmid, n - 1);
          var na := [Areg(r1), Areg(r2)] + cont;
          assert na == [Areg(r1)] + ([Areg(r2)] + cont);
          assert ActionRep(Areg(r2), code, e1, pcmid);
          assert ([Areg(r2)] + cont)[0] == Areg(r2) && ([Areg(r2)] + cont)[1..] == cont;
          assert ActionsRep([Areg(r2)] + cont, code, e1);
          assert ActionRep(Areg(r1), code, pc, e1);
          assert na[0] == Areg(r1) && na[1..] == [Areg(r2)] + cont;
          assert ActionsRep(na, code, pc);
          assert ActionsRegexSize(na) < ActionsRegexSize(acts);
          TR.ActionsRepToFuel(na, code, pc);
          var nn: nat :| TR.ActionsRepFuel(na, code, pc, nn);
          GenerateBlockedF(rer, na, code, pc, inp, b, c, nexttree, gm, nn);
        case Quantified(greedy, min, delta, r1) =>
          // min>0: GroupActionT ≠ Read; NN(k>0)/Inf: Choice ≠ Read;
          // NN(0): no code — the tree is cont's, which CAN block
          if min == 0 && delta == NN(0) {
            var gidl := DefGroups(r1);
            assert pcmid == pc by {
              var em: nat := NfaRepQuantInvNN(greedy, min, 0, r1, code, pc, pcmid);
              assert em == pc;
            }
            assert ActionsRegexSize(cont) < ActionsRegexSize(acts);
            GenerateBlockedF(rer, cont, code, pc, inp, b, c, nexttree, gm, n - 1);
          }
        case Group(gid, r1) =>      // GroupActionT ≠ Read
    }
  }

  // small wrapper so the fuel→actions_rep bridge is callable here
  /** Thin wrapper exposing `TreeRep.FuelToActionsRep` under this module's `ActionsRep` name. */
  lemma FuelToActionsRepWrap(acts: Actions, code: Code, pc: Label, n: nat)
    requires TR.ActionsRepFuel(acts, code, pc, n)
    ensures ActionsRep(acts, code, pc)
  { TR.FuelToActionsRep(acts, code, pc, n); }

  // Coq: generate_blocked — now PROVED. Invert tree_thread (tt_reset/tt_begin impossible for a Read at a
  // non-stuttering pc), then delegate the tt_eq case to GenerateBlockedF.
  /** At a non-stuttering pc, if the tree steps via `StepBlocked`, the bytecode's `EpsilonStep`
      blocks the thread at `pc + 1` and the blocked continuation is `TreeThread`-related once
      the input advances. Rules out `tt_reset`/`tt_begin` and delegates to `GenerateBlockedF`. */
  lemma GenerateBlocked(rer: RegExpRecord, code: Code, inp: Input, t: Tree, gm: GroupMap, pc: Label, b: LoopBool, nexttree: Tree)
    requires TreeBfsStep(t, gm, Idx(inp)) == StepBlocked(nexttree)
    requires !Stutters(pc, code)
    requires TreeThread(rer, code, inp, (t, gm), Thr(pc, gm, b))
    ensures EpsilonStep(rer, Thr(pc, gm, b), code, inp) == EpsBlocked(Thr(pc + 1, gm, CanExit))
         && (forall nextinp :: AdvanceInput(inp, Forward) == Some(nextinp) ==> TreeThread(rer, code, nextinp, (nexttree, gm), Thr(pc + 1, gm, CanExit)))
         && (exists nextinp :: AdvanceInput(inp, Forward) == Some(nextinp))
  {
    assert t.Read? && nexttree == t.t;   // only Read yields StepBlocked(nexttree)
    var c := t.c;
    assert t == Read(c, nexttree);
    if exists acts: Actions :: BoolTree(rer, acts, inp, b, t) && ActionsRep(acts, code, pc) && PikeActions(acts) {
      var acts :| BoolTree(rer, acts, inp, b, t) && ActionsRep(acts, code, pc) && PikeActions(acts);
      TR.ActionsRepToFuel(acts, code, pc);
      var n: nat :| TR.ActionsRepFuel(acts, code, pc, n);
      GenerateBlockedF(rer, acts, code, pc, inp, b, c, nexttree, gm, n);
    } else if t.GroupActionT? && t.g.Reset? && GetPc(code, pc) == Some(ResetRegs(t.g.gl)) {
      // t is Read, not GroupActionT: this branch is unreachable
    } else {
      assert GetPc(code, pc) == Some(BeginLoop);   // tt_begin ⇒ stuttering, contradiction
    }
  }

  // Fuel core of stutter_step's tt_eq case: at a stuttering pc, a tt_eq tree (bool_tree + actions_rep)
  // can only sit on a Jmp (the other instructions are non-stuttering). Epsilon/Sequence prefixes are
  // peeled (recursion ↓ ActionsRegexSize); jump_bc constructs the jumped tt_eq with the same tree.
  /** Fuel-indexed core of `StutterStep`'s `tt_eq` case: at a stuttering pc a `tt_eq` witness
      can only sit on a `Jmp` (other instructions don't stutter); peels `Epsilon`/`Sequence`
      prefixes and follows the jump to rebuild the `TreeThread` witness one pc further on. */
  lemma StutterStepF(rer: RegExpRecord, acts: Actions, code: Code, pc: Label, inp: Input, b: LoopBool, t: Tree, gm: GroupMap, n: nat)
    requires PikeActions(acts)
    requires TR.ActionsRepFuel(acts, code, pc, n)
    requires BoolTree(rer, acts, inp, b, t)
    requires Stutters(pc, code)
    ensures exists nextpc: Label, nextb: LoopBool ::
              EpsilonStep(rer, Thr(pc, gm, b), code, inp) == EpsActive([Thr(nextpc, gm, nextb)])
              && TreeThread(rer, code, inp, (t, gm), Thr(nextpc, gm, nextb))
    decreases ActionsRegexSize(acts), n
  {
    if |acts| == 0 {
      var pcstart: nat :| GetPc(code, pc) == Some(Jmp(pcstart)) && TR.ActionsRepFuel(acts, code, pcstart, n - 1);
      TR.FuelToActionsRep(acts, code, pcstart, n - 1);
      assert TreeThread(rer, code, inp, (t, gm), Thr(pcstart, gm, b));   // tt_eq, witness acts
    } else if exists pcmid: nat :: ActionRep(acts[0], code, pc, pcmid) && TR.ActionsRepFuel(acts[1..], code, pcmid, n - 1) {
      var cont := acts[1..];
      var pcmid: nat :| ActionRep(acts[0], code, pc, pcmid) && TR.ActionsRepFuel(cont, code, pcmid, n - 1);
      PikeActionsTail(acts);
      assert acts == [acts[0]] + cont;
      PikeActionsConsIff(acts[0], cont);
      match acts[0]
      case Acheck(strcheck) => assert GetPc(code, pc) == Some(EndLoop(pcmid));   // not stuttering ⇒ false
      case Aclose(gid) => assert GetPc(code, pc) == Some(SetRegClose(gid));
      case Areg(r) =>
        assert PikeRegex(r);
        match r
        case Epsilon =>
          StutterStepF(rer, cont, code, pc, inp, b, t, gm, n - 1);
        case Character(cd) => assert GetPc(code, pc) == Some(Consume(cd));
        case Disjunction(r1, r2) =>
          var e1: nat :| GetPc(code, pc) == Some(Fork(pc + 1, e1 + 1)) && NfaRep(r1, code, pc + 1, e1)
                       && GetPc(code, e1) == Some(Jmp(pcmid)) && NfaRep(r2, code, e1 + 1, pcmid);
        case Sequence(r1, r2) =>
          PikeActionsConsIff(Areg(r2), cont);
          PikeActionsConsIff(Areg(r1), [Areg(r2)] + cont);
          assert NfaRep(Sequence(r1, r2), code, pc, pcmid);
          var e1: nat :| NfaRep(r1, code, pc, e1) && NfaRep(r2, code, e1, pcmid);
          TR.FuelToActionsRep(cont, code, pcmid, n - 1);
          var na := [Areg(r1), Areg(r2)] + cont;
          assert na == [Areg(r1)] + ([Areg(r2)] + cont);
          assert ActionRep(Areg(r2), code, e1, pcmid);
          assert ([Areg(r2)] + cont)[0] == Areg(r2) && ([Areg(r2)] + cont)[1..] == cont;
          assert ActionsRep([Areg(r2)] + cont, code, e1);
          assert ActionRep(Areg(r1), code, pc, e1);
          assert na[0] == Areg(r1) && na[1..] == [Areg(r2)] + cont;
          assert ActionsRep(na, code, pc);
          assert ActionsRegexSize(na) < ActionsRegexSize(acts);
          TR.ActionsRepToFuel(na, code, pc);
          var nn: nat :| TR.ActionsRepFuel(na, code, pc, nn);
          StutterStepF(rer, na, code, pc, inp, b, t, gm, nn);
        case Quantified(greedy, min, delta, r1) =>
          var gidl := DefGroups(r1);
          if min > 0 {
            // head instruction is ResetRegs — not a stutter: contradiction
            var em: nat :| NfaRepMin(min, gidl, r1, code, pc, em)
              && (match delta
                  case Inf =>
                    exists e1: nat ::
                      GetPc(code, em) == Some(GreedyFork(greedy, em + 1, e1 + 1))
                      && GetPc(code, em + 1) == Some(BeginLoop)
                      && GetPc(code, em + 2) == Some(ResetRegs(gidl))
                      && NfaRep(r1, code, em + 3, e1)
                      && GetPc(code, e1) == Some(EndLoop(em))
                      && pcmid == e1 + 1
                  case NN(k) => NfaRepOpt(k, greedy, gidl, r1, code, em, pcmid));
            var eb: nat :| GetPc(code, pc) == Some(ResetRegs(gidl))
              && NfaRep(r1, code, pc + 1, eb)
              && NfaRepMin(min - 1, gidl, r1, code, eb, em);
            assert GetPc(code, pc) == Some(ResetRegs(gidl));   // not a stutter ⇒ false
          } else if delta == NN(0) {
            // no code: the stutter belongs to cont
            assert pcmid == pc by {
              var em: nat := NfaRepQuantInvNN(greedy, min, 0, r1, code, pc, pcmid);
              assert em == pc;
            }
            assert ActionsRegexSize(cont) < ActionsRegexSize(acts);
            StutterStepF(rer, cont, code, pc, inp, b, t, gm, n - 1);
          } else if delta.NN? {
            var k := delta.n;
            var em: nat := NfaRepQuantInvNN(greedy, min, k, r1, code, pc, pcmid);
            assert em == pc;
            assert NfaRepOpt(k, greedy, gidl, r1, code, pc, pcmid);
            var e1: nat :| GetPc(code, pc) == Some(GreedyFork(greedy, pc + 1, pcmid))
              && GetPc(code, pc + 1) == Some(BeginLoop)
              && GetPc(code, pc + 2) == Some(ResetRegs(gidl))
              && NfaRep(r1, code, pc + 3, e1)
              && GetPc(code, e1) == Some(EndLoop(e1 + 1))
              && NfaRepOpt(k - 1, greedy, gidl, r1, code, e1 + 1, pcmid);
            assert GetPc(code, pc) == Some(GreedyFork(greedy, pc + 1, pcmid));   // a Fork ⇒ not stuttering
          } else {
            var e1: nat :| GetPc(code, pc) == Some(GreedyFork(greedy, pc + 1, e1 + 1)) && GetPc(code, pc + 1) == Some(BeginLoop)
                         && GetPc(code, pc + 2) == Some(ResetRegs(gidl)) && NfaRep(r1, code, pc + 3, e1)
                         && GetPc(code, e1) == Some(EndLoop(pc)) && pcmid == e1 + 1;
            assert GetPc(code, pc) == Some(GreedyFork(greedy, pc + 1, e1 + 1));   // a Fork ⇒ not stuttering
          }
        case Group(gid, r1) =>
          var e1: nat :| GetPc(code, pc) == Some(SetRegOpen(gid)) && NfaRep(r1, code, pc + 1, e1)
                       && GetPc(code, e1) == Some(SetRegClose(gid)) && pcmid == e1 + 1;
          assert GetPc(code, pc) == Some(SetRegOpen(gid));
    } else {
      var pcstart: nat :| GetPc(code, pc) == Some(Jmp(pcstart)) && TR.ActionsRepFuel(acts, code, pcstart, n - 1);
      TR.FuelToActionsRep(acts, code, pcstart, n - 1);
      assert TreeThread(rer, code, inp, (t, gm), Thr(pcstart, gm, b));   // tt_eq, witness acts
    }
  }

  // Coq: stutter_step — now PROVED. Invert tree_thread; tt_reset (ResetRegs) contradicts Stutters,
  // tt_begin steps to pc+1, tt_eq delegates to StutterStepF.
  /** At a stuttering pc (`Stutters`), the bytecode's `EpsilonStep` advances to a single new
      pc with the *same* tree still `TreeThread`-related — i.e. stuttering instructions don't
      correspond to any tree-level step. Handles `tt_begin` directly, delegates `tt_eq` to
      `StutterStepF`. */
  lemma StutterStep(rer: RegExpRecord, code: Code, inp: Input, t: Tree, gm: GroupMap, pc: Label, b: LoopBool)
    requires TreeThread(rer, code, inp, (t, gm), Thr(pc, gm, b))
    requires Stutters(pc, code)
    ensures exists nextpc: Label, nextb: LoopBool ::
              EpsilonStep(rer, Thr(pc, gm, b), code, inp) == EpsActive([Thr(nextpc, gm, nextb)])
              && TreeThread(rer, code, inp, (t, gm), Thr(nextpc, gm, nextb))
  {
    if exists acts: Actions :: BoolTree(rer, acts, inp, b, t) && ActionsRep(acts, code, pc) && PikeActions(acts) {
      var acts :| BoolTree(rer, acts, inp, b, t) && ActionsRep(acts, code, pc) && PikeActions(acts);
      TR.ActionsRepToFuel(acts, code, pc);
      var n: nat :| TR.ActionsRepFuel(acts, code, pc, n);
      StutterStepF(rer, acts, code, pc, inp, b, t, gm, n);
    } else if t.GroupActionT? && t.g.Reset? && GetPc(code, pc) == Some(ResetRegs(t.g.gl)) {
      assert false;   // ResetRegs is not a stuttering instruction
    } else {
      // tt_begin: GetPc == BeginLoop; epsilon_step ⇒ [Thr(pc+1, gm, CannotExit)]
      assert GetPc(code, pc) == Some(BeginLoop);
      assert TreeThread(rer, code, inp, (t, gm), Thr(pc + 1, gm, CannotExit));
    }
  }

  // Coq: invariant_preservation (Theorem 14) — the PikeVM↔PikeTree simulation step. PROVED from the
  // deep kernel (generate_*/stutter_step/tt_same_tree) + the inclusion/ltt lemmas.
  /** Theorem 14, the simulation capstone: every `PikeVmStep` either has a matching
      `PikeTreeStep` that preserves `PikeInv`, or is a stutter step that preserves `PikeInv`
      with the tree state left unchanged. Built from `GenerateActive`/`GenerateMatch`/
      `GenerateBlocked`/`StutterStep`/`TtSameTree` plus the `*Inclusion`/`Ltt*` lemmas. */
  lemma InvariantPreservation(rer: RegExpRecord, code: Code, pts1: PikeTreeState, pvs1: PikeVmState, pvs2: PikeVmState)
    requires StutterWf(rer, code)
    requires PikeInv(rer, code, pts1, pvs1)
    requires PikeVmStep(code, rer, pvs1, pvs2)
    ensures (exists pts2 :: PikeTreeStep(pts1, pts2) && PikeInv(rer, code, pts2, pvs2))
         || PikeInv(rer, code, pts1, pvs2)
  {
    match pts1
    case PTS_final(bestf) =>
      assert pvs1.PVS_final?;   // PikeInv ⇒ pvs1 final ⇒ PikeVmStep(final,_) is false: vacuous
    case PTS(inp, treeactive, best, treeblocked, treeseen) =>
      assert pvs1.PVS? && pvs1.inp == inp && pvs1.best == best;
      var vmactive := pvs1.active;
      var vmblocked := pvs1.blocked;
      var vmseen := pvs1.seen;
      assert ListTreeThread(rer, code, inp, treeactive, vmactive);
      LttLenEq(rer, code, inp, treeactive, vmactive);
      if |vmactive| == 0 {
        assert |treeactive| == 0;
        if |vmblocked| == 0 {
          assert pvs2 == PVS_final(best);
          if AdvanceInput(inp, Forward) == None {
          } else {
            var ni :| AdvanceInput(inp, Forward) == Some(ni);
            LttLenEq(rer, code, ni, treeblocked, vmblocked);
          }
          assert |treeblocked| == 0;
          assert PikeTreeStep(pts1, PTS_final(best)) && PikeInv(rer, code, PTS_final(best), pvs2);
        } else {
          assert AdvanceInput(inp, Forward).Some?;
          var inp2 :| AdvanceInput(inp, Forward) == Some(inp2);
          assert pvs2 == PVS(inp2, vmblocked, best, [], InitialSeenPcs);
          assert ListTreeThread(rer, code, inp2, treeblocked, vmblocked);
          AdvanceNext(inp, inp2);            // NextInp(inp) == inp2
          var pts2 := PTS(inp2, treeblocked, best, [], InitialSeenTrees);
          assert PikeTreeStep(pts1, pts2);   // pts_nextchar
          InitialInclusion(rer, code, inp2, HdError(treeblocked), HeadPc(vmblocked));
          assert PikeInv(rer, code, pts2, pvs2);
        }
      } else {
        assert |treeactive| > 0;
        assert vmactive[0].gm == treeactive[0].1 && TreeThread(rer, code, inp, treeactive[0], vmactive[0]);
        assert ListTreeThread(rer, code, inp, treeactive[1..], vmactive[1..]);
        var thr0 := vmactive[0];
        var pc := thr0.pc;
        var b := thr0.b;
        var t := treeactive[0].0;
        var gm := treeactive[0].1;
        assert thr0 == Thr(pc, gm, b);
        assert TreeThread(rer, code, inp, (t, gm), Thr(pc, gm, b));
        var rest := vmactive[1..];
        assert HdError(treeactive) == Some((t, gm)) && HeadPc(vmactive) == pc;
        assert SeenInclusion(rer, code, inp, treeseen, vmseen, Some((t, gm)), pc);
        if SeenThread(vmseen, thr0) {
          assert pvs2 == PVS(inp, rest, best, vmblocked, vmseen);
          assert Inseenpc(vmseen, pc, b);
          // SeenInclusion at (pc,b): the right (stutter) disjunct needs pc < pc, impossible ⇒ left.
          var ts, gms :| Inseen(treeseen, ts) && TreeThread(rer, code, inp, (ts, gms), Thr(pc, gms, b));
          TtSameTree(rer, code, inp, ts, gms, t, gm, pc, b);   // ts == t
          assert Inseen(treeseen, t);
          var pts2 := PTS(inp, treeactive[1..], best, treeblocked, treeseen);
          assert PikeTreeStep(pts1, pts2);   // pts_skip
          SkipInclusion(rer, code, inp, treeseen, vmseen, t, gm, pc, HdError(treeactive[1..]), HeadPc(rest));
          assert PikeInv(rer, code, pts2, pvs2);
        } else {
          if Stutters(pc, code) {
            StutterStep(rer, code, inp, t, gm, pc, b);
            var nextpc, nextb :| EpsilonStep(rer, Thr(pc, gm, b), code, inp) == EpsActive([Thr(nextpc, gm, nextb)])
                              && TreeThread(rer, code, inp, (t, gm), Thr(nextpc, gm, nextb));
            assert pvs2 == PVS(inp, [Thr(nextpc, gm, nextb)] + rest, best, vmblocked, AddThread(vmseen, thr0));
            assert pc < nextpc;   // StutterWf
            // RIGHT disjunct: invariant preserved with pts1 unchanged.
            assert ListTreeThread(rer, code, inp, treeactive, [Thr(nextpc, gm, nextb)] + rest) by {
              assert ([Thr(nextpc, gm, nextb)] + rest)[0] == Thr(nextpc, gm, nextb);
              assert ([Thr(nextpc, gm, nextb)] + rest)[1..] == rest;
              assert treeactive == [treeactive[0]] + treeactive[1..];
            }
            StutterInclusion(rer, code, inp, treeseen, vmseen, t, gm, pc, b, HeadPc([Thr(nextpc, gm, nextb)] + rest));
            assert AddThread(vmseen, thr0) == AddSeenPcs(vmseen, pc, b);
            assert PikeInv(rer, code, pts1, pvs2);
          } else {
            match TreeBfsStep(t, gm, Idx(inp))
            case StepActive(na) => {
              GenerateActive(rer, code, inp, t, gm, pc, b, na);
              var threadactive :| EpsilonStep(rer, Thr(pc, gm, b), code, inp) == EpsActive(threadactive)
                               && ListTreeThread(rer, code, inp, na, threadactive);
              assert pvs2 == PVS(inp, threadactive + rest, best, vmblocked, AddThread(vmseen, thr0));
              var pts2 := PTS(inp, na + treeactive[1..], best, treeblocked, AddSeenTrees(treeseen, t));
              assert PikeTreeStep(pts1, pts2);   // pts_active
              LttApp(rer, code, inp, na, treeactive[1..], threadactive, rest);
              AddInclusion(rer, code, inp, treeseen, vmseen, t, pc, gm, b, HdError(na + treeactive[1..]), HeadPc(threadactive + rest));
              assert PikeInv(rer, code, pts2, pvs2);
            }
            case StepMatch => {
              GenerateMatch(rer, code, inp, t, gm, pc, b);
              assert pvs2 == PVS(inp, [], Some((inp, gm)), vmblocked, AddThread(vmseen, thr0));
              var pts2 := PTS(inp, [], Some((inp, gm)), treeblocked, AddSeenTrees(treeseen, t));
              assert PikeTreeStep(pts1, pts2);   // pts_match
              AddInclusion(rer, code, inp, treeseen, vmseen, t, pc, gm, b, HdError([]), HeadPc([]));
              assert ListTreeThread(rer, code, inp, [], []);
              assert PikeInv(rer, code, pts2, pvs2);
            }
            case StepBlocked(newt) => {
              GenerateBlocked(rer, code, inp, t, gm, pc, b, newt);
              assert pvs2 == PVS(inp, rest, best, vmblocked + [Thr(pc + 1, gm, CanExit)], AddThread(vmseen, thr0));
              var pts2 := PTS(inp, treeactive[1..], best, treeblocked + [(newt, gm)], AddSeenTrees(treeseen, t));
              assert PikeTreeStep(pts1, pts2);   // pts_blocked
              AddInclusion(rer, code, inp, treeseen, vmseen, t, pc, gm, b, HdError(treeactive[1..]), HeadPc(rest));
              // blocked clause: ListTreeThread(nextinp, treeblocked+[(newt,gm)], vmblocked+[Thr(pc+1,gm,CanExit)])
              forall nextinp | AdvanceInput(inp, Forward) == Some(nextinp)
                ensures ListTreeThread(rer, code, nextinp, treeblocked + [(newt, gm)], vmblocked + [Thr(pc + 1, gm, CanExit)])
              {
                assert ListTreeThread(rer, code, nextinp, treeblocked, vmblocked);
                assert TreeThread(rer, code, nextinp, (newt, gm), Thr(pc + 1, gm, CanExit));
                assert ListTreeThread(rer, code, nextinp, [(newt, gm)], [Thr(pc + 1, gm, CanExit)]);
                LttApp(rer, code, nextinp, treeblocked, [(newt, gm)], vmblocked, [Thr(pc + 1, gm, CanExit)]);
              }
              assert PikeInv(rer, code, pts2, pvs2);
            }
          }
        }
      }
  }
}
