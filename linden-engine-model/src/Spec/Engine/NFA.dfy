// Mirror of Engine/NFA.v.
// PikeVM bytecode, the compiler, and the representation predicates relating regexes/continuations
// to compiled code. The Coq Ltac (no_stutter/stutter/invert_rep) has no analog and is omitted.
include "PikeSubset.dfy"

/** The PikeVM bytecode language, the `Compile`r from `PikeRegex`-subset regexes to it, and the
    representation predicates (`NfaRep`, `ActionRep`, `ActionsRep`) proving the compiler produces
    code that faithfully implements a regex or action stack — the bridge `PikeVM` executes against. */
module NFA {
  import opened Std.Wrappers
  import opened WarblreNumeric
  import opened WarblrePrimitives
  import opened Chars
  import opened Groups
  import opened Regex
  import opened Semantics
  import opened PikeSubset

  /** A bytecode address: an index into a `Code`. */
  type Label = nat

  // Coq: Inductive bytecode.
  /** One PikeVM instruction. `Accept` succeeds; `Consume(cd)` matches one character; `Jmp`/`Fork`
      are control flow (`Fork` spawns a lower-priority second thread); `SetRegOpen`/`SetRegClose`/
      `ResetRegs` update capture groups; `BeginLoop`/`EndLoop` bracket a `Quantified` iteration and
      gate repetition via the thread's loop-progress flag (`LoopBool`); `KillThread` marks code for
      constructs outside the `PikeRegex` subset (lookarounds, anchors, backreferences). */
  datatype Bytecode =
    | Accept
    | Consume(cd: CharDescr)
    | Jmp(l: Label)
    | Fork(l1: Label, l2: Label)
    | SetRegOpen(gid: GroupId)
    | SetRegClose(gid: GroupId)
    | ResetRegs(gids: seq<GroupId>)
    | BeginLoop
    | EndLoop(l: Label)
    | KillThread
    | CheckAnchor(a: Anchor)

  /** A compiled program: a flat sequence of `Bytecode`, addressed by `Label`. */
  type Code = seq<Bytecode>

  // Coq: get_pc (nth_error)
  /** The instruction at `pc`, or `None` if `pc` runs off the end of `c`. */
  function GetPc(c: Code, pc: Label): Option<Bytecode> {
    if pc < |c| then Some(c[pc]) else None
  }

  // ----- get_pc lemmas -----
  lemma GetPrefix(c: Code, pc: Label, prev: Code)
    ensures GetPc(prev + c, |prev| + pc) == GetPc(c, pc)
  {
    if pc < |c| { assert (prev + c)[|prev| + pc] == c[pc]; }
  }

  lemma GetFirst(c: Code, prev: Code)
    ensures GetPc(prev + c, |prev|) == GetPc(c, 0)
  { GetPrefix(c, 0, prev); }

  lemma GetSuffix(c: Code, suffix: Code, pc: Label, i: Bytecode)
    requires GetPc(c, pc) == Some(i)
    ensures GetPc(c + suffix, pc) == Some(i)
  {
    assert pc < |c|;
    assert (c + suffix)[pc] == c[pc];
  }

  lemma GetPrev(prev: Code, suffix: Code, pc: Label, i: Bytecode)
    requires GetPc(prev + suffix, pc) == Some(i)
    requires pc < |prev|
    ensures GetPc(prev, pc) == Some(i)
  {
    assert (prev + suffix)[pc] == prev[pc];
  }

  // Coq: next_pcs
  /** The control-flow successor address(es) of instruction `b` at `pc`: none for `Accept`/
      `KillThread`, two for `Fork`, one otherwise. Used by `Termination`'s well-formedness argument. */
  function NextPcs(pc: Label, b: Bytecode): seq<Label> {
    match b
    case Consume(_) => [pc + 1]
    case CheckAnchor(_) => [pc + 1]
    case SetRegOpen(_) => [pc + 1]
    case SetRegClose(_) => [pc + 1]
    case ResetRegs(_) => [pc + 1]
    case BeginLoop => [pc + 1]
    case Accept => []
    case KillThread => []
    case Jmp(l) => [l]
    case EndLoop(l) => [l]
    case Fork(l1, l2) => [l1, l2]
  }

  // Coq: greedy_fork
  /** `Fork(l1, l2)` if `greedy` else `Fork(l2, l1)` — greedy vs. lazy is encoded purely as fork-branch
      order, the same trick as `Semantics.GreedyChoice`. */
  function GreedyFork(greedy: bool, l1: Label, l2: Label): Bytecode {
    if greedy then Fork(l1, l2) else Fork(l2, l1)
  }

  // Coq: compile (returns code and next frsh label).
  /** Compiles `r` into bytecode starting at label `frsh`, returning the code and the next free label.
      Non-`PikeRegex` constructs and bounded quantifiers compile to a single `KillThread`. Its
      correctness — that the emitted code actually implements `r` — is `CompileNfaRep`. */
  function Compile(r: Regex, frsh: Label): (Code, Label)
    decreases RegexSize(r), 1
  {
    match r
    case Epsilon => ([], frsh)
    case Character(cd) => ([Consume(cd)], frsh + 1)
    case Disjunction(r1, r2) =>
      (var c1 := Compile(r1, frsh + 1);
       var c2 := Compile(r2, c1.1 + 1);
       ([Fork(frsh + 1, c1.1 + 1)] + c1.0 + [Jmp(c2.1)] + c2.0, c2.1))
    case Sequence(r1, r2) =>
      (var c1 := Compile(r1, frsh);
       var c2 := Compile(r2, c1.1);
       (c1.0 + c2.0, c2.1))
    case Quantified(greedy, min, delta, r1) =>
      // general scheme: `min` forced copies, then an unbounded loop (Inf) or
      // `k` optional fork-guarded layers (NN(k)) — mirroring the tree
      // semantics' forced/free unrolling; min == 0 && Inf collapses to the
      // original star block exactly
      (var gidl := DefGroups(r1);
       var (mc, mf) := RepeatMin(min, gidl, r1, frsh);
       match delta
       case Inf =>
         (var c1 := Compile(r1, mf + 3);
          (mc + [GreedyFork(greedy, mf + 1, c1.1 + 1), BeginLoop, ResetRegs(gidl)] + c1.0 + [EndLoop(mf)], c1.1 + 1))
       case NN(k) =>
         (var (oc, of) := RepeatOpt(k, greedy, gidl, r1, mf);
          (mc + oc, of)))
    case Group(gid, r1) =>
      (var c1 := Compile(r1, frsh + 1);
       ([SetRegOpen(gid)] + c1.0 + [SetRegClose(gid)], c1.1 + 1))
    case LookaroundR(_, _) => ([KillThread], frsh + 1)
    case AnchorR(a) => ([CheckAnchor(a)], frsh + 1)
    case Backreference(_) => ([KillThread], frsh + 1)
  }

  /** The forced-minimum part of a counted quantifier: `min` back-to-back
      copies of the body, each entered through a `ResetRegs(gidl)` (the tree
      side's per-forced-iteration `Reset`). */
  function RepeatMin(min: nat, gidl: seq<GroupId>, r: Regex, frsh: Label): (Code, Label)
    decreases RegexSize(r), min + 2
  {
    if min == 0 then ([], frsh)
    else
      var c1 := Compile(r, frsh + 1);
      var (c2, f2) := RepeatMin(min - 1, gidl, r, c1.1);
      ([ResetRegs(gidl)] + c1.0 + c2, f2)
  }

  /** The optional part of a bounded quantifier: `nb` fork-guarded layers,
      each `[GreedyFork; BeginLoop; ResetRegs] body [EndLoop -> next layer]`;
      every fork's skip branch exits to the common end label. */
  function RepeatOpt(nb: nat, greedy: bool, gidl: seq<GroupId>, r: Regex, frsh: Label): (Code, Label)
    decreases RegexSize(r), nb + 2
  {
    if nb == 0 then ([], frsh)
    else
      var c1 := Compile(r, frsh + 3);
      var (c2, f2) := RepeatOpt(nb - 1, greedy, gidl, r, c1.1 + 1);
      ([GreedyFork(greedy, frsh + 1, f2), BeginLoop, ResetRegs(gidl)] + c1.0 + [EndLoop(c1.1 + 1)] + c2, f2)
  }

  // Coq: compilation
  /** The complete program for `r`: `Compile(r, 0)`'s code followed by a trailing `Accept`. This is
      what `PikeVM`/`PikeVmMatch` execute. */
  function Compilation(r: Regex): Code {
    Compile(r, 0).0 + [Accept]
  }

  // ----- nfa_rep (representation predicate) -----
  // Recursive on the regex (decreases r); ghost due to the existential intermediate labels.
  /** `r` is represented in `c` from `pc1` to `pc2`: executing that code region is exactly matching
      `r`. One clause per regex constructor, mirroring `Compile`; proved to hold of the compiler's
      actual output by `CompileNfaRep`. */
  /** `k` forced copies of `r1`'s block, each headed by `ResetRegs(gidl)` —
      the representation of `RepeatMin`'s output. */
  ghost predicate NfaRepMin(k: nat, gidl: seq<GroupId>, r1: Regex, c: Code, pc1: Label, pc2: Label)
    decreases RegexSize(r1), k + 2
  {
    if k == 0 then pc1 == pc2
    else
      var body := pc1 + 1;
      var rest := k - 1;
      exists e1: nat ::
        GetPc(c, pc1) == Some(ResetRegs(gidl))
        && NfaRep(r1, c, body, e1)
        && NfaRepMin(rest, gidl, r1, c, e1, pc2)
  }

  /** `k` optional fork-guarded layers of `r1`'s block — the representation of
      `RepeatOpt`'s output. Every layer's fork skips to the common `pc2`. */
  ghost predicate NfaRepOpt(k: nat, greedy: bool, gidl: seq<GroupId>, r1: Regex, c: Code, pc1: Label, pc2: Label)
    decreases RegexSize(r1), k + 2
  {
    if k == 0 then pc1 == pc2
    else exists e1: nat ::
      GetPc(c, pc1) == Some(GreedyFork(greedy, pc1 + 1, pc2))
      && GetPc(c, pc1 + 1) == Some(BeginLoop)
      && GetPc(c, pc1 + 2) == Some(ResetRegs(gidl))
      && NfaRep(r1, c, pc1 + 3, e1)
      && GetPc(c, e1) == Some(EndLoop(e1 + 1))
      && NfaRepOpt(k - 1, greedy, gidl, r1, c, e1 + 1, pc2)
  }

  ghost predicate NfaRep(r: Regex, c: Code, pc1: Label, pc2: Label)
    decreases RegexSize(r), 1
  {
    match r
    case Epsilon => pc1 == pc2
    case Character(cd) => pc2 == pc1 + 1 && GetPc(c, pc1) == Some(Consume(cd))
    case Disjunction(r1, r2) =>
      exists e1: nat ::
        GetPc(c, pc1) == Some(Fork(pc1 + 1, e1 + 1))
        && NfaRep(r1, c, pc1 + 1, e1)
        && GetPc(c, e1) == Some(Jmp(pc2))
        && NfaRep(r2, c, e1 + 1, pc2)
    case Sequence(r1, r2) =>
      exists e1: nat :: NfaRep(r1, c, pc1, e1) && NfaRep(r2, c, e1, pc2)
    case Quantified(greedy, min, delta, r1) =>
      // fast path: the plain star keeps its original direct shape (min == 0
      // makes the forced chain empty), so star-only proofs are unaffected
      if min == 0 && delta == Inf then
        exists e1: nat ::
          GetPc(c, pc1) == Some(GreedyFork(greedy, pc1 + 1, e1 + 1))
          && GetPc(c, pc1 + 1) == Some(BeginLoop)
          && GetPc(c, pc1 + 2) == Some(ResetRegs(DefGroups(r1)))
          && NfaRep(r1, c, pc1 + 3, e1)
          && GetPc(c, e1) == Some(EndLoop(pc1))
          && pc2 == e1 + 1
      else
        (match delta
         case Inf =>
           exists em: nat ::
             NfaRepMin(min, DefGroups(r1), r1, c, pc1, em)
             && exists e1: nat ::
               GetPc(c, em) == Some(GreedyFork(greedy, em + 1, e1 + 1))
               && GetPc(c, em + 1) == Some(BeginLoop)
               && GetPc(c, em + 2) == Some(ResetRegs(DefGroups(r1)))
               && NfaRep(r1, c, em + 3, e1)
               && GetPc(c, e1) == Some(EndLoop(em))
               && pc2 == e1 + 1
         case NN(k) =>
           exists em: nat ::
             NfaRepMin(min, DefGroups(r1), r1, c, pc1, em)
             && NfaRepOpt(k, greedy, DefGroups(r1), r1, c, em, pc2))
    case Group(gid, r1) =>
      exists e1: nat ::
        GetPc(c, pc1) == Some(SetRegOpen(gid))
        && NfaRep(r1, c, pc1 + 1, e1)
        && GetPc(c, e1) == Some(SetRegClose(gid))
        && pc2 == e1 + 1
    case LookaroundR(_, _) => pc2 == pc1 + 1 && GetPc(c, pc1) == Some(KillThread)
    case AnchorR(a) => pc2 == pc1 + 1 && GetPc(c, pc1) == Some(CheckAnchor(a))
    case Backreference(_) => pc2 == pc1 + 1 && GetPc(c, pc1) == Some(KillThread)
  }

  // Coq: action_rep
  /** Lifts `NfaRep` to a single `Semantics.Action`: `Areg` delegates to `NfaRep`; `Acheck` sits on an
      `EndLoop`; `Aclose` sits on a `SetRegClose`. */
  ghost predicate ActionRep(a: Action, c: Code, pc1: Label, pc2: Label) {
    match a
    case Areg(r) => NfaRep(r, c, pc1, pc2)
    case Acheck(_) => GetPc(c, pc1) == Some(EndLoop(pc2))
    case Aclose(gid) => pc2 == pc1 + 1 && GetPc(c, pc1) == Some(SetRegClose(gid))
  }

  // Coq: actions_rep. The jump_bc rule (a Jmp prefix, same continuation) is non-structural, so this
  // is a least predicate.
  /** An entire action stack `acts` is represented starting at `pc`: an empty stack sits on `Accept`,
      a non-empty stack chains `ActionRep` over its head with the tail represented at the midpoint,
      and any number of leading `Jmp`s may be skipped first. */
  least predicate ActionsRep(acts: Actions, c: Code, pc: Label) {
    (|acts| == 0 && GetPc(c, pc) == Some(Accept))                                    // empty_bc
    || (|acts| > 0 && exists pcmid: nat :: ActionRep(acts[0], c, pc, pcmid) && ActionsRep(acts[1..], c, pcmid))  // cons_bc
    || (exists pcstart: nat :: GetPc(c, pc) == Some(Jmp(pcstart)) && ActionsRep(acts, c, pcstart))               // jump_bc
  }

  // ----- stuttering -----
  // Coq: stutters
  /** Whether the instruction at `pc` is a "stutter": one that moves a thread to a new `pc` without
      consuming input or otherwise making tree-visible progress (`Jmp`, `BeginLoop`, `KillThread`).
      Central to `PikeEquiv`'s simulation, which must let the VM run ahead of the tree walker. */
  predicate Stutters(pc: Label, code: Code) {
    match GetPc(code, pc)
    case Some(Jmp(_)) => true
    case Some(BeginLoop) => true
    case Some(KillThread) => true
    case _ => false
  }

  lemma DoesStutter(pc: Label, code: Code)
    requires Stutters(pc, code)
    ensures GetPc(code, pc) == Some(BeginLoop)
         || (exists next: Label :: GetPc(code, pc) == Some(Jmp(next)))
         || GetPc(code, pc) == Some(KillThread)
  {}

  lemma DoesntStutterJmp(pc: Label, code: Code, next: Label)
    requires !Stutters(pc, code)
    requires GetPc(code, pc) == Some(Jmp(next))
    ensures false
  {}

  lemma DoesntStutterBegin(pc: Label, code: Code)
    requires !Stutters(pc, code)
    requires GetPc(code, pc) == Some(BeginLoop)
    ensures false
  {}

  lemma DoesntStutterKill(pc: Label, code: Code)
    requires !Stutters(pc, code)
    requires GetPc(code, pc) == Some(KillThread)
    ensures false
  {}

  // ===== Axiomatized (compilation correctness; long structural inductions). See PROGRESS.md. =====

  // Coq: fresh_correct
  /** Compiling `r` at `frsh` advances the label exactly by the size of the emitted code:
      `next == frsh + |l|`. Used to compute the label of whatever follows `r`'s block. */
  lemma FreshCorrect(r: Regex, frsh: Label, l: Code, next: Label)
    requires Compile(r, frsh) == (l, next)
    ensures frsh + |l| == next
    decreases RegexSize(r), 1
  {
    match r
    case Epsilon =>
    case Character(_) =>
    case AnchorR(_) =>
    case Backreference(_) =>
    case LookaroundR(_, _) =>
    case Disjunction(r1, r2) =>
      var c1 := Compile(r1, frsh + 1);
      var c2 := Compile(r2, c1.1 + 1);
      FreshCorrect(r1, frsh + 1, c1.0, c1.1);
      FreshCorrect(r2, c1.1 + 1, c2.0, c2.1);
    case Sequence(r1, r2) =>
      var c1 := Compile(r1, frsh);
      var c2 := Compile(r2, c1.1);
      FreshCorrect(r1, frsh, c1.0, c1.1);
      FreshCorrect(r2, c1.1, c2.0, c2.1);
    case Quantified(greedy, min, delta, r1) =>
      var gidl := DefGroups(r1);
      var (mc, mf) := RepeatMin(min, gidl, r1, frsh);
      FreshCorrectMin(min, gidl, r1, frsh, mc, mf);
      match delta {
        case Inf =>
          var c1 := Compile(r1, mf + 3);
          FreshCorrect(r1, mf + 3, c1.0, c1.1);
        case NN(k) =>
          var (oc, of) := RepeatOpt(k, greedy, gidl, r1, mf);
          FreshCorrectOpt(k, greedy, gidl, r1, mf, oc, of);
      }
    case Group(gid, r1) =>
      var c1 := Compile(r1, frsh + 1);
      FreshCorrect(r1, frsh + 1, c1.0, c1.1);
  }

  /** `FreshCorrect` for the forced-minimum chain. */
  lemma FreshCorrectMin(k: nat, gidl: seq<GroupId>, r: Regex, frsh: Label, l: Code, next: Label)
    requires RepeatMin(k, gidl, r, frsh) == (l, next)
    ensures frsh + |l| == next
    decreases RegexSize(r), k + 2
  {
    if k > 0 {
      var c1 := Compile(r, frsh + 1);
      FreshCorrect(r, frsh + 1, c1.0, c1.1);
      var (c2, f2) := RepeatMin(k - 1, gidl, r, c1.1);
      FreshCorrectMin(k - 1, gidl, r, c1.1, c2, f2);
    }
  }

  /** `FreshCorrect` for the optional-layer chain. */
  lemma FreshCorrectOpt(k: nat, greedy: bool, gidl: seq<GroupId>, r: Regex, frsh: Label, l: Code, next: Label)
    requires RepeatOpt(k, greedy, gidl, r, frsh) == (l, next)
    ensures frsh + |l| == next
    decreases RegexSize(r), k + 2
  {
    if k > 0 {
      var c1 := Compile(r, frsh + 3);
      FreshCorrect(r, frsh + 3, c1.0, c1.1);
      var (c2, f2) := RepeatOpt(k - 1, greedy, gidl, r, c1.1 + 1);
      FreshCorrectOpt(k - 1, greedy, gidl, r, c1.1 + 1, c2, f2);
    }
  }

  // Coq: nfa_rep_extend
  /** A representation is stable under appending more code: `NfaRep(r, c, ...)` still holds in
      `c + suffix`. Lets `CompileNfaRep` build up a whole program's representation block by block. */
  lemma NfaRepExtend(r: Regex, c: Code, start: Label, endl: Label, suffix: Code)
    requires NfaRep(r, c, start, endl)
    ensures NfaRep(r, c + suffix, start, endl)
    decreases RegexSize(r), 1
  {
    match r
    case Epsilon =>
    case Character(cd) =>
      GetSuffix(c, suffix, start, Consume(cd));
    case Disjunction(r1, r2) =>
      var e1: nat :| GetPc(c, start) == Some(Fork(start + 1, e1 + 1)) && NfaRep(r1, c, start + 1, e1) && GetPc(c, e1) == Some(Jmp(endl)) && NfaRep(r2, c, e1 + 1, endl);
      GetSuffix(c, suffix, start, Fork(start + 1, e1 + 1));
      GetSuffix(c, suffix, e1, Jmp(endl));
      NfaRepExtend(r1, c, start + 1, e1, suffix);
      NfaRepExtend(r2, c, e1 + 1, endl, suffix);
      assert GetPc(c + suffix, start) == Some(Fork(start + 1, e1 + 1)) && NfaRep(r1, c + suffix, start + 1, e1) && GetPc(c + suffix, e1) == Some(Jmp(endl)) && NfaRep(r2, c + suffix, e1 + 1, endl);
    case Sequence(r1, r2) =>
      var e1: nat :| NfaRep(r1, c, start, e1) && NfaRep(r2, c, e1, endl);
      NfaRepExtend(r1, c, start, e1, suffix);
      NfaRepExtend(r2, c, e1, endl, suffix);
      assert NfaRep(r1, c + suffix, start, e1) && NfaRep(r2, c + suffix, e1, endl);
    case Quantified(greedy, min, delta, r1) =>
      match delta {
        case Inf =>
          var em: nat :| NfaRepMin(min, DefGroups(r1), r1, c, start, em)
            && exists e1: nat ::
              GetPc(c, em) == Some(GreedyFork(greedy, em + 1, e1 + 1))
              && GetPc(c, em + 1) == Some(BeginLoop)
              && GetPc(c, em + 2) == Some(ResetRegs(DefGroups(r1)))
              && NfaRep(r1, c, em + 3, e1)
              && GetPc(c, e1) == Some(EndLoop(em))
              && endl == e1 + 1;
          var e1: nat :| GetPc(c, em) == Some(GreedyFork(greedy, em + 1, e1 + 1)) && GetPc(c, em + 1) == Some(BeginLoop) && GetPc(c, em + 2) == Some(ResetRegs(DefGroups(r1))) && NfaRep(r1, c, em + 3, e1) && GetPc(c, e1) == Some(EndLoop(em)) && endl == e1 + 1;
          NfaRepExtendMin(min, DefGroups(r1), r1, c, start, em, suffix);
          GetSuffix(c, suffix, em, GreedyFork(greedy, em + 1, e1 + 1));
          GetSuffix(c, suffix, em + 1, BeginLoop);
          GetSuffix(c, suffix, em + 2, ResetRegs(DefGroups(r1)));
          GetSuffix(c, suffix, e1, EndLoop(em));
          NfaRepExtend(r1, c, em + 3, e1, suffix);
          assert NfaRepMin(min, DefGroups(r1), r1, c + suffix, start, em)
              && GetPc(c + suffix, em) == Some(GreedyFork(greedy, em + 1, e1 + 1))
              && GetPc(c + suffix, em + 1) == Some(BeginLoop)
              && GetPc(c + suffix, em + 2) == Some(ResetRegs(DefGroups(r1)))
              && NfaRep(r1, c + suffix, em + 3, e1)
              && GetPc(c + suffix, e1) == Some(EndLoop(em))
              && endl == e1 + 1;
        case NN(k) =>
          var em: nat :| NfaRepMin(min, DefGroups(r1), r1, c, start, em)
            && NfaRepOpt(k, greedy, DefGroups(r1), r1, c, em, endl);
          NfaRepExtendMin(min, DefGroups(r1), r1, c, start, em, suffix);
          NfaRepExtendOpt(k, greedy, DefGroups(r1), r1, c, em, endl, suffix);
          assert NfaRepMin(min, DefGroups(r1), r1, c + suffix, start, em)
              && NfaRepOpt(k, greedy, DefGroups(r1), r1, c + suffix, em, endl);
        }
    case Group(gid, r1) =>
      var e1: nat :| GetPc(c, start) == Some(SetRegOpen(gid)) && NfaRep(r1, c, start + 1, e1) && GetPc(c, e1) == Some(SetRegClose(gid)) && endl == e1 + 1;
      GetSuffix(c, suffix, start, SetRegOpen(gid));
      GetSuffix(c, suffix, e1, SetRegClose(gid));
      NfaRepExtend(r1, c, start + 1, e1, suffix);
      assert GetPc(c + suffix, start) == Some(SetRegOpen(gid)) && NfaRep(r1, c + suffix, start + 1, e1) && GetPc(c + suffix, e1) == Some(SetRegClose(gid)) && endl == e1 + 1;
    case LookaroundR(_, _) =>
      GetSuffix(c, suffix, start, KillThread);
    case AnchorR(a) =>
      GetSuffix(c, suffix, start, CheckAnchor(a));
    case Backreference(_) =>
      GetSuffix(c, suffix, start, KillThread);
  }

  /** `NfaRepExtend` for the forced-minimum chain. */
  lemma NfaRepExtendMin(k: nat, gidl: seq<GroupId>, r: Regex, c: Code, start: Label, endl: Label, suffix: Code)
    requires NfaRepMin(k, gidl, r, c, start, endl)
    ensures NfaRepMin(k, gidl, r, c + suffix, start, endl)
    decreases RegexSize(r), k + 2
  {
    if k > 0 {
      var e1: nat :| GetPc(c, start) == Some(ResetRegs(gidl))
        && NfaRep(r, c, start + 1, e1)
        && NfaRepMin(k - 1, gidl, r, c, e1, endl);
      GetSuffix(c, suffix, start, ResetRegs(gidl));
      NfaRepExtend(r, c, start + 1, e1, suffix);
      NfaRepExtendMin(k - 1, gidl, r, c, e1, endl, suffix);
      assert GetPc(c + suffix, start) == Some(ResetRegs(gidl))
          && NfaRep(r, c + suffix, start + 1, e1)
          && NfaRepMin(k - 1, gidl, r, c + suffix, e1, endl);
    }
  }

  /** `NfaRepExtend` for the optional-layer chain. */
  lemma NfaRepExtendOpt(k: nat, greedy: bool, gidl: seq<GroupId>, r: Regex, c: Code, start: Label, endl: Label, suffix: Code)
    requires NfaRepOpt(k, greedy, gidl, r, c, start, endl)
    ensures NfaRepOpt(k, greedy, gidl, r, c + suffix, start, endl)
    decreases RegexSize(r), k + 2
  {
    if k > 0 {
      var e1: nat :| GetPc(c, start) == Some(GreedyFork(greedy, start + 1, endl))
        && GetPc(c, start + 1) == Some(BeginLoop)
        && GetPc(c, start + 2) == Some(ResetRegs(gidl))
        && NfaRep(r, c, start + 3, e1)
        && GetPc(c, e1) == Some(EndLoop(e1 + 1))
        && NfaRepOpt(k - 1, greedy, gidl, r, c, e1 + 1, endl);
      GetSuffix(c, suffix, start, GreedyFork(greedy, start + 1, endl));
      GetSuffix(c, suffix, start + 1, BeginLoop);
      GetSuffix(c, suffix, start + 2, ResetRegs(gidl));
      GetSuffix(c, suffix, e1, EndLoop(e1 + 1));
      NfaRepExtend(r, c, start + 3, e1, suffix);
      NfaRepExtendOpt(k - 1, greedy, gidl, r, c, e1 + 1, endl, suffix);
      assert GetPc(c + suffix, start) == Some(GreedyFork(greedy, start + 1, endl))
          && GetPc(c + suffix, start + 1) == Some(BeginLoop)
          && GetPc(c + suffix, start + 2) == Some(ResetRegs(gidl))
          && NfaRep(r, c + suffix, start + 3, e1)
          && GetPc(c + suffix, e1) == Some(EndLoop(e1 + 1))
          && NfaRepOpt(k - 1, greedy, gidl, r, c + suffix, e1 + 1, endl);
    }
  }

  // Coq: compile_nfa_rep — the compiler adheres to the representation predicate.
  /** Compiler soundness: the code `Compile(r, start)` emits, once placed after any `prev` prefix,
      satisfies `NfaRep(r, ...)`. This is what lets `PikeVM` trust that running compiled bytecode
      matches running the regex. */
  lemma {:isolate_assertions} CompileNfaRep(r: Regex, c: Code, start: Label, endl: Label, prev: Code)
    requires Compile(r, start) == (c, endl)
    requires start == |prev|
    ensures NfaRep(r, prev + c, start, endl)
    decreases RegexSize(r), 1
  {
    match r
    case Epsilon =>
      assert prev + c == prev;
    case Character(cd) =>
      GetFirst(c, prev);
    case AnchorR(_) =>
      GetFirst(c, prev);
    case Backreference(_) =>
      GetFirst(c, prev);
    case LookaroundR(_, _) =>
      GetFirst(c, prev);
    case Disjunction(r1, r2) =>
      var c1 := Compile(r1, start + 1);
      var c2 := Compile(r2, c1.1 + 1);
      var bc1, f1, bc2, f2 := c1.0, c1.1, c2.0, c2.1;
      assert c == [Fork(start + 1, f1 + 1)] + bc1 + [Jmp(f2)] + bc2 && endl == f2;
      FreshCorrect(r1, start + 1, bc1, f1);   // start + 1 + |bc1| == f1
      FreshCorrect(r2, f1 + 1, bc2, f2);
      // r1: compile at prev+[Fork], then extend with the Jmp+bc2 suffix
      var pre1 := prev + [Fork(start + 1, f1 + 1)];
      CompileNfaRep(r1, bc1, start + 1, f1, pre1);
      NfaRepExtend(r1, pre1 + bc1, start + 1, f1, [Jmp(f2)] + bc2);
      assert (pre1 + bc1) + ([Jmp(f2)] + bc2) == prev + c;
      // r2: compile at prev+[Fork]+bc1+[Jmp]
      var pre2 := prev + [Fork(start + 1, f1 + 1)] + bc1 + [Jmp(f2)];
      assert |pre2| == f1 + 1;
      CompileNfaRep(r2, bc2, f1 + 1, f2, pre2);
      assert pre2 + bc2 == prev + c;
      // GetPc facts
      GetFirst(c, prev);                                       // Fork at start
      assert prev + c == (prev + [Fork(start + 1, f1 + 1)] + bc1) + ([Jmp(f2)] + bc2);
      assert |prev + [Fork(start + 1, f1 + 1)] + bc1| == f1;
      GetFirst([Jmp(f2)] + bc2, prev + [Fork(start + 1, f1 + 1)] + bc1);  // Jmp at f1
      assert NfaRep(r1, prev + c, start + 1, f1) && NfaRep(r2, prev + c, f1 + 1, f2)
          && GetPc(prev + c, start) == Some(Fork(start + 1, f1 + 1))
          && GetPc(prev + c, f1) == Some(Jmp(f2));
    case Sequence(r1, r2) =>
      var c1 := Compile(r1, start);
      var c2 := Compile(r2, c1.1);
      var bc1, f1, bc2, f2 := c1.0, c1.1, c2.0, c2.1;
      assert c == bc1 + bc2 && endl == f2;
      FreshCorrect(r1, start, bc1, f1);   // start + |bc1| == f1
      CompileNfaRep(r1, bc1, start, f1, prev);
      NfaRepExtend(r1, prev + bc1, start, f1, bc2);
      assert (prev + bc1) + bc2 == prev + c;
      assert |prev + bc1| == f1;
      CompileNfaRep(r2, bc2, f1, f2, prev + bc1);
      assert (prev + bc1) + bc2 == prev + c;
      assert NfaRep(r1, prev + c, start, f1) && NfaRep(r2, prev + c, f1, f2);
    case Quantified(greedy, min, delta, r1) =>
      var gidl := DefGroups(r1);
      var (mc, mf) := RepeatMin(min, gidl, r1, start);
      FreshCorrectMin(min, gidl, r1, start, mc, mf);   // start + |mc| == mf
      CompileNfaRepMin(min, gidl, r1, mc, start, mf, prev);
      match delta {
        case Inf =>
          var c1 := Compile(r1, mf + 3);
          var bc1, f1 := c1.0, c1.1;
          var hdr := [GreedyFork(greedy, mf + 1, f1 + 1), BeginLoop, ResetRegs(gidl)];
          var blk := hdr + bc1 + [EndLoop(mf)];
          assert c == mc + blk && endl == f1 + 1;
          FreshCorrect(r1, mf + 3, bc1, f1);   // mf + 3 + |bc1| == f1
          NfaRepExtendMin(min, gidl, r1, prev + mc, start, mf, blk);
          assert (prev + mc) + blk == prev + c;
          var pre1 := prev + mc + hdr;
          assert |pre1| == mf + 3;
          CompileNfaRep(r1, bc1, mf + 3, f1, pre1);
          NfaRepExtend(r1, pre1 + bc1, mf + 3, f1, [EndLoop(mf)]);
          assert (pre1 + bc1) + [EndLoop(mf)] == prev + c;
          assert |prev + mc| == mf;
          GetFirst(blk, prev + mc);
          GetPrefix(blk, 1, prev + mc);
          GetPrefix(blk, 2, prev + mc);
          assert prev + c == (prev + mc + hdr + bc1) + [EndLoop(mf)];
          assert |prev + mc + hdr + bc1| == f1;
          GetFirst([EndLoop(mf)], prev + mc + hdr + bc1);   // EndLoop at f1
          assert NfaRepMin(min, gidl, r1, prev + c, start, mf)
              && GetPc(prev + c, mf) == Some(GreedyFork(greedy, mf + 1, f1 + 1))
              && GetPc(prev + c, mf + 1) == Some(BeginLoop)
              && GetPc(prev + c, mf + 2) == Some(ResetRegs(gidl))
              && NfaRep(r1, prev + c, mf + 3, f1)
              && GetPc(prev + c, f1) == Some(EndLoop(mf))
              && endl == f1 + 1;
        case NN(k) =>
          var (oc, of) := RepeatOpt(k, greedy, gidl, r1, mf);
          assert c == mc + oc && endl == of;
          NfaRepExtendMin(min, gidl, r1, prev + mc, start, mf, oc);
          assert (prev + mc) + oc == prev + c;
          assert |prev + mc| == mf;
          CompileNfaRepOpt(k, greedy, gidl, r1, oc, mf, of, prev + mc);
          assert NfaRepMin(min, gidl, r1, prev + c, start, mf)
              && NfaRepOpt(k, greedy, gidl, r1, prev + c, mf, of);
      }
    case Group(gid, r1) =>
      var c1 := Compile(r1, start + 1);
      var bc1, f1 := c1.0, c1.1;
      assert c == [SetRegOpen(gid)] + bc1 + [SetRegClose(gid)] && endl == f1 + 1;
      FreshCorrect(r1, start + 1, bc1, f1);   // start + 1 + |bc1| == f1
      var pre1 := prev + [SetRegOpen(gid)];
      assert |pre1| == start + 1;
      CompileNfaRep(r1, bc1, start + 1, f1, pre1);
      NfaRepExtend(r1, pre1 + bc1, start + 1, f1, [SetRegClose(gid)]);
      assert (pre1 + bc1) + [SetRegClose(gid)] == prev + c;
      GetFirst(c, prev);   // SetRegOpen at start
      assert prev + c == (prev + [SetRegOpen(gid)] + bc1) + [SetRegClose(gid)];
      assert |prev + [SetRegOpen(gid)] + bc1| == f1;
      GetFirst([SetRegClose(gid)], prev + [SetRegOpen(gid)] + bc1);   // SetRegClose at f1
      assert GetPc(prev + c, start) == Some(SetRegOpen(gid))
          && NfaRep(r1, prev + c, start + 1, f1)
          && GetPc(prev + c, f1) == Some(SetRegClose(gid))
          && endl == f1 + 1;
  }

  /** `CompileNfaRep` for the forced-minimum chain. */
  lemma CompileNfaRepMin(k: nat, gidl: seq<GroupId>, r: Regex, c: Code, start: Label, endl: Label, prev: Code)
    requires RepeatMin(k, gidl, r, start) == (c, endl)
    requires start == |prev|
    ensures NfaRepMin(k, gidl, r, prev + c, start, endl)
    decreases RegexSize(r), k + 2
  {
    if k == 0 {
      assert prev + c == prev;
    } else {
      var c1 := Compile(r, start + 1);
      var bc1, f1 := c1.0, c1.1;
      var (c2, f2) := RepeatMin(k - 1, gidl, r, f1);
      assert c == [ResetRegs(gidl)] + bc1 + c2 && endl == f2;
      FreshCorrect(r, start + 1, bc1, f1);
      FreshCorrectMin(k - 1, gidl, r, f1, c2, f2);
      var pre1 := prev + [ResetRegs(gidl)];
      assert |pre1| == start + 1;
      CompileNfaRep(r, bc1, start + 1, f1, pre1);
      NfaRepExtend(r, pre1 + bc1, start + 1, f1, c2);
      assert (pre1 + bc1) + c2 == prev + c;
      assert |prev + [ResetRegs(gidl)] + bc1| == f1;
      CompileNfaRepMin(k - 1, gidl, r, c2, f1, f2, prev + [ResetRegs(gidl)] + bc1);
      assert (prev + [ResetRegs(gidl)] + bc1) + c2 == prev + c;
      GetFirst(c, prev);
      assert GetPc(prev + c, start) == Some(ResetRegs(gidl))
          && NfaRep(r, prev + c, start + 1, f1)
          && NfaRepMin(k - 1, gidl, r, prev + c, f1, f2);
    }
  }

  /** `CompileNfaRep` for the optional-layer chain. */
  lemma {:isolate_assertions} CompileNfaRepOpt(k: nat, greedy: bool, gidl: seq<GroupId>, r: Regex, c: Code, start: Label, endl: Label, prev: Code)
    requires RepeatOpt(k, greedy, gidl, r, start) == (c, endl)
    requires start == |prev|
    ensures NfaRepOpt(k, greedy, gidl, r, prev + c, start, endl)
    decreases RegexSize(r), k + 2
  {
    if k == 0 {
      assert prev + c == prev;
    } else {
      var c1 := Compile(r, start + 3);
      var bc1, f1 := c1.0, c1.1;
      var (c2, f2) := RepeatOpt(k - 1, greedy, gidl, r, f1 + 1);
      var hdr := [GreedyFork(greedy, start + 1, f2), BeginLoop, ResetRegs(gidl)];
      assert c == hdr + bc1 + [EndLoop(f1 + 1)] + c2 && endl == f2;
      FreshCorrect(r, start + 3, bc1, f1);
      FreshCorrectOpt(k - 1, greedy, gidl, r, f1 + 1, c2, f2);
      var pre1 := prev + hdr;
      assert |pre1| == start + 3;
      CompileNfaRep(r, bc1, start + 3, f1, pre1);
      NfaRepExtend(r, pre1 + bc1, start + 3, f1, [EndLoop(f1 + 1)] + c2);
      assert (pre1 + bc1) + ([EndLoop(f1 + 1)] + c2) == prev + c;
      assert |prev + hdr + bc1 + [EndLoop(f1 + 1)]| == f1 + 1;
      CompileNfaRepOpt(k - 1, greedy, gidl, r, c2, f1 + 1, f2, prev + hdr + bc1 + [EndLoop(f1 + 1)]);
      assert (prev + hdr + bc1 + [EndLoop(f1 + 1)]) + c2 == prev + c;
      GetFirst(c, prev);
      GetPrefix(c, 1, prev);
      GetPrefix(c, 2, prev);
      assert prev + c == (prev + hdr + bc1) + ([EndLoop(f1 + 1)] + c2);
      assert |prev + hdr + bc1| == f1;
      GetFirst([EndLoop(f1 + 1)] + c2, prev + hdr + bc1);
      assert GetPc(prev + c, start) == Some(GreedyFork(greedy, start + 1, f2))
          && GetPc(prev + c, start + 1) == Some(BeginLoop)
          && GetPc(prev + c, start + 2) == Some(ResetRegs(gidl))
          && NfaRep(r, prev + c, start + 3, f1)
          && GetPc(prev + c, f1) == Some(EndLoop(f1 + 1))
          && NfaRepOpt(k - 1, greedy, gidl, r, prev + c, f1 + 1, f2);
    }
  }

  /** Introduction for the bounded-quantifier representation. */
  lemma NfaRepQuantIntroNN(greedy: bool, min: nat, k: nat, r1: Regex, c: Code, pc1: Label, em: nat, pc2: Label)
    requires NfaRepMin(min, DefGroups(r1), r1, c, pc1, em)
    requires NfaRepOpt(k, greedy, DefGroups(r1), r1, c, em, pc2)
    ensures NfaRep(Quantified(greedy, min, NN(k), r1), c, pc1, pc2)
  {
  }

  /** Introduction for the unbounded-quantifier representation (dispatches to
      the fast-path star arm when the forced chain is empty). */
  lemma NfaRepQuantIntroInf(greedy: bool, min: nat, r1: Regex, c: Code, pc1: Label, em: nat, e1: nat, pc2: Label)
    requires NfaRepMin(min, DefGroups(r1), r1, c, pc1, em)
    requires GetPc(c, em) == Some(GreedyFork(greedy, em + 1, e1 + 1))
    requires GetPc(c, em + 1) == Some(BeginLoop)
    requires GetPc(c, em + 2) == Some(ResetRegs(DefGroups(r1)))
    requires NfaRep(r1, c, em + 3, e1)
    requires GetPc(c, e1) == Some(EndLoop(em))
    requires pc2 == e1 + 1
    ensures NfaRep(Quantified(greedy, min, Inf, r1), c, pc1, pc2)
  {
    if min == 0 {
      assert em == pc1;   // the forced chain is empty: fast-path arm
    }
  }

  /** Inversion for the bounded-quantifier representation: recovers the
      forced/optional split point. */
  lemma NfaRepQuantInvNN(greedy: bool, min: nat, k: nat, r1: Regex, c: Code, pc1: Label, pc2: Label)
      returns (em: nat)
    requires NfaRep(Quantified(greedy, min, NN(k), r1), c, pc1, pc2)
    ensures NfaRepMin(min, DefGroups(r1), r1, c, pc1, em)
    ensures NfaRepOpt(k, greedy, DefGroups(r1), r1, c, em, pc2)
  {
    em :| NfaRepMin(min, DefGroups(r1), r1, c, pc1, em)
       && NfaRepOpt(k, greedy, DefGroups(r1), r1, c, em, pc2);
  }

  // Coq: nfa_rep_incr — a representation spans a non-decreasing label range.
  /** Any `NfaRep`-represented block has `start <= endl`: labels only increase across a regex's
      compiled region. */
  lemma NfaRepIncr(r: Regex, code: Code, start: Label, endl: Label)
    requires NfaRep(r, code, start, endl)
    ensures start <= endl
    decreases RegexSize(r), 1
  {
    match r
    case Epsilon =>
    case Character(_) =>
    case AnchorR(_) =>
    case Backreference(_) =>
    case LookaroundR(_, _) =>
    case Disjunction(r1, r2) =>
      var e1: nat :| GetPc(code, start) == Some(Fork(start + 1, e1 + 1)) && NfaRep(r1, code, start + 1, e1) && GetPc(code, e1) == Some(Jmp(endl)) && NfaRep(r2, code, e1 + 1, endl);
      NfaRepIncr(r1, code, start + 1, e1);
      NfaRepIncr(r2, code, e1 + 1, endl);
    case Sequence(r1, r2) =>
      var e1: nat :| NfaRep(r1, code, start, e1) && NfaRep(r2, code, e1, endl);
      NfaRepIncr(r1, code, start, e1);
      NfaRepIncr(r2, code, e1, endl);
    case Quantified(greedy, min, delta, r1) =>
      match delta {
        case Inf =>
          var em: nat :| NfaRepMin(min, DefGroups(r1), r1, code, start, em)
            && exists e1: nat ::
              GetPc(code, em) == Some(GreedyFork(greedy, em + 1, e1 + 1))
              && GetPc(code, em + 1) == Some(BeginLoop)
              && GetPc(code, em + 2) == Some(ResetRegs(DefGroups(r1)))
              && NfaRep(r1, code, em + 3, e1)
              && GetPc(code, e1) == Some(EndLoop(em))
              && endl == e1 + 1;
          var e1: nat :| GetPc(code, em) == Some(GreedyFork(greedy, em + 1, e1 + 1)) && GetPc(code, em + 1) == Some(BeginLoop) && GetPc(code, em + 2) == Some(ResetRegs(DefGroups(r1))) && NfaRep(r1, code, em + 3, e1) && GetPc(code, e1) == Some(EndLoop(em)) && endl == e1 + 1;
          NfaRepIncrMin(min, DefGroups(r1), r1, code, start, em);
          NfaRepIncr(r1, code, em + 3, e1);
        case NN(k) =>
          var em: nat :| NfaRepMin(min, DefGroups(r1), r1, code, start, em)
            && NfaRepOpt(k, greedy, DefGroups(r1), r1, code, em, endl);
          NfaRepIncrMin(min, DefGroups(r1), r1, code, start, em);
          NfaRepIncrOpt(k, greedy, DefGroups(r1), r1, code, em, endl);
      }
    case Group(gid, r1) =>
      var e1: nat :| GetPc(code, start) == Some(SetRegOpen(gid)) && NfaRep(r1, code, start + 1, e1) && GetPc(code, e1) == Some(SetRegClose(gid)) && endl == e1 + 1;
      NfaRepIncr(r1, code, start + 1, e1);
  }

  /** `NfaRepIncr` for the forced-minimum chain. */
  lemma NfaRepIncrMin(k: nat, gidl: seq<GroupId>, r: Regex, code: Code, start: Label, endl: Label)
    requires NfaRepMin(k, gidl, r, code, start, endl)
    ensures start <= endl
    decreases RegexSize(r), k + 2
  {
    if k > 0 {
      var e1: nat :| GetPc(code, start) == Some(ResetRegs(gidl))
        && NfaRep(r, code, start + 1, e1)
        && NfaRepMin(k - 1, gidl, r, code, e1, endl);
      NfaRepIncr(r, code, start + 1, e1);
      NfaRepIncrMin(k - 1, gidl, r, code, e1, endl);
    }
  }

  /** `NfaRepIncr` for the optional-layer chain. */
  lemma NfaRepIncrOpt(k: nat, greedy: bool, gidl: seq<GroupId>, r: Regex, code: Code, start: Label, endl: Label)
    requires NfaRepOpt(k, greedy, gidl, r, code, start, endl)
    ensures start <= endl
    decreases RegexSize(r), k + 2
  {
    if k > 0 {
      var e1: nat :| GetPc(code, start) == Some(GreedyFork(greedy, start + 1, endl))
        && GetPc(code, start + 1) == Some(BeginLoop)
        && GetPc(code, start + 2) == Some(ResetRegs(gidl))
        && NfaRep(r, code, start + 3, e1)
        && GetPc(code, e1) == Some(EndLoop(e1 + 1))
        && NfaRepOpt(k - 1, greedy, gidl, r, code, e1 + 1, endl);
      NfaRepIncr(r, code, start + 3, e1);
      NfaRepIncrOpt(k - 1, greedy, gidl, r, code, e1 + 1, endl);
    }
  }

  // Coq: compile_jumps — every Jmp in a representation targets a strictly greater label.
  /** Every `Jmp` inside an `NfaRep`-represented block targets a strictly later label — compiled code
      never jumps backward except via the dedicated `EndLoop`/`BeginLoop` pair. Used by `Termination`'s
      well-formedness argument. */
  lemma CompileJumps(r: Regex, code: Code, start: Label, endl: Label, pc: Label, next: Label)
    requires NfaRep(r, code, start, endl)
    requires start <= pc < endl
    requires GetPc(code, pc) == Some(Jmp(next))
    ensures pc < next
    decreases RegexSize(r), 1
  {
    match r
    case Epsilon =>
    case Character(_) =>
    case AnchorR(_) =>
    case Backreference(_) =>
    case LookaroundR(_, _) =>
    case Disjunction(r1, r2) =>
      var e1: nat :| GetPc(code, start) == Some(Fork(start + 1, e1 + 1)) && NfaRep(r1, code, start + 1, e1) && GetPc(code, e1) == Some(Jmp(endl)) && NfaRep(r2, code, e1 + 1, endl);
      NfaRepIncr(r1, code, start + 1, e1);
      NfaRepIncr(r2, code, e1 + 1, endl);
      if pc == start {
      } else if pc < e1 {
        CompileJumps(r1, code, start + 1, e1, pc, next);
      } else if pc == e1 {
        // GetPc(e1) == Jmp(endl) == Jmp(next) ⟹ next == endl; pc == e1 < endl
      } else {
        CompileJumps(r2, code, e1 + 1, endl, pc, next);
      }
    case Sequence(r1, r2) =>
      var e1: nat :| NfaRep(r1, code, start, e1) && NfaRep(r2, code, e1, endl);
      NfaRepIncr(r1, code, start, e1);
      NfaRepIncr(r2, code, e1, endl);
      if pc < e1 {
        CompileJumps(r1, code, start, e1, pc, next);
      } else {
        CompileJumps(r2, code, e1, endl, pc, next);
      }
    case Quantified(greedy, min, delta, r1) =>
      match delta {
        case Inf =>
          var em: nat :| NfaRepMin(min, DefGroups(r1), r1, code, start, em)
            && exists e1: nat ::
              GetPc(code, em) == Some(GreedyFork(greedy, em + 1, e1 + 1))
              && GetPc(code, em + 1) == Some(BeginLoop)
              && GetPc(code, em + 2) == Some(ResetRegs(DefGroups(r1)))
              && NfaRep(r1, code, em + 3, e1)
              && GetPc(code, e1) == Some(EndLoop(em))
              && endl == e1 + 1;
          var e1: nat :| GetPc(code, em) == Some(GreedyFork(greedy, em + 1, e1 + 1)) && GetPc(code, em + 1) == Some(BeginLoop) && GetPc(code, em + 2) == Some(ResetRegs(DefGroups(r1))) && NfaRep(r1, code, em + 3, e1) && GetPc(code, e1) == Some(EndLoop(em)) && endl == e1 + 1;
          NfaRepIncrMin(min, DefGroups(r1), r1, code, start, em);
          NfaRepIncr(r1, code, em + 3, e1);
          if pc < em {
            CompileJumpsMin(min, DefGroups(r1), r1, code, start, em, pc, next);
          } else if em + 3 <= pc < e1 {
            CompileJumps(r1, code, em + 3, e1, pc, next);
          }
          // em, em+1, em+2, e1 hold Fork/BeginLoop/ResetRegs/EndLoop: not Jmp
        case NN(k) =>
          var em: nat :| NfaRepMin(min, DefGroups(r1), r1, code, start, em)
            && NfaRepOpt(k, greedy, DefGroups(r1), r1, code, em, endl);
          NfaRepIncrMin(min, DefGroups(r1), r1, code, start, em);
          NfaRepIncrOpt(k, greedy, DefGroups(r1), r1, code, em, endl);
          if pc < em {
            CompileJumpsMin(min, DefGroups(r1), r1, code, start, em, pc, next);
          } else {
            CompileJumpsOpt(k, greedy, DefGroups(r1), r1, code, em, endl, pc, next);
          }
      }
    case Group(gid, r1) =>
      var e1: nat :| GetPc(code, start) == Some(SetRegOpen(gid)) && NfaRep(r1, code, start + 1, e1) && GetPc(code, e1) == Some(SetRegClose(gid)) && endl == e1 + 1;
      NfaRepIncr(r1, code, start + 1, e1);
      if start + 1 <= pc < e1 {
        CompileJumps(r1, code, start + 1, e1, pc, next);
      }
  }

  /** `CompileJumps` for the forced-minimum chain (it emits no `Jmp` of its
      own; only body regions can hold one). */
  lemma CompileJumpsMin(k: nat, gidl: seq<GroupId>, r: Regex, code: Code, start: Label, endl: Label, pc: Label, next: Label)
    requires NfaRepMin(k, gidl, r, code, start, endl)
    requires start <= pc < endl
    requires GetPc(code, pc) == Some(Jmp(next))
    ensures pc < next
    decreases RegexSize(r), k + 2
  {
    if k > 0 {
      var e1: nat :| GetPc(code, start) == Some(ResetRegs(gidl))
        && NfaRep(r, code, start + 1, e1)
        && NfaRepMin(k - 1, gidl, r, code, e1, endl);
      NfaRepIncr(r, code, start + 1, e1);
      NfaRepIncrMin(k - 1, gidl, r, code, e1, endl);
      if start + 1 <= pc < e1 {
        CompileJumps(r, code, start + 1, e1, pc, next);
      } else if e1 <= pc {
        CompileJumpsMin(k - 1, gidl, r, code, e1, endl, pc, next);
      }
      // pc == start holds ResetRegs: not Jmp
    }
  }

  /** `CompileJumps` for the optional-layer chain. */
  lemma CompileJumpsOpt(k: nat, greedy: bool, gidl: seq<GroupId>, r: Regex, code: Code, start: Label, endl: Label, pc: Label, next: Label)
    requires NfaRepOpt(k, greedy, gidl, r, code, start, endl)
    requires start <= pc < endl
    requires GetPc(code, pc) == Some(Jmp(next))
    ensures pc < next
    decreases RegexSize(r), k + 2
  {
    if k > 0 {
      var e1: nat :| GetPc(code, start) == Some(GreedyFork(greedy, start + 1, endl))
        && GetPc(code, start + 1) == Some(BeginLoop)
        && GetPc(code, start + 2) == Some(ResetRegs(gidl))
        && NfaRep(r, code, start + 3, e1)
        && GetPc(code, e1) == Some(EndLoop(e1 + 1))
        && NfaRepOpt(k - 1, greedy, gidl, r, code, e1 + 1, endl);
      NfaRepIncr(r, code, start + 3, e1);
      NfaRepIncrOpt(k - 1, greedy, gidl, r, code, e1 + 1, endl);
      if start + 3 <= pc < e1 {
        CompileJumps(r, code, start + 3, e1, pc, next);
      } else if e1 + 1 <= pc {
        CompileJumpsOpt(k - 1, greedy, gidl, r, code, e1 + 1, endl, pc, next);
      }
      // start..start+2 and e1 hold Fork/BeginLoop/ResetRegs/EndLoop: not Jmp
    }
  }
}
