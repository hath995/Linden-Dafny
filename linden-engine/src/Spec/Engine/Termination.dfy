// Phase 4 — PikeVM termination / linear-time bound. PROVED, axiom-free (see `dafny audit`).
// Result: the executable VM reaches a PVS_final state within BytecodeFuel+1 = O(|c|.n) steps
// (`PikeVmReachesFinal`), and — combined with the proved PikeVmMatchCorrect + PikeVmCorrect — always
// returns FirstLeaf(tree,inp) (capstone `PikeVmTotalCorrect`), i.e. TOTAL correctness. The only
// distance from PikeVmMatch's exact BytecodeFuel is a documented +1 (see PROGRESS.md "Phase 4").
//
// Strategy (a ranking/step-count argument, NOT a semantic simulation): the per-position measure
//   PosBudget(pvs, N) = 2*UnseenCount(seen, N) + |active|      (N = |code|)
// strictly decreases on every non-position-advancing step, because the (pc, LoopBool) seen-set
// dedup makes each distinct key expandable at most once. Position advances are bounded by the
// remaining input length. Verify with: --verification-time-limit 400.
include "FunctionalPikeVM.dfy"

/** Proves the executable `PikeVmLoop` (`FunctionalPikeVM`) always reaches a `PVS_final` state
    within `O(|code| * n)` steps, and combines this with `Correctness.PikeVmCorrect` into the
    capstone `PikeVmTotalCorrect`: the VM halts and returns the right answer. */
module Termination {
  import opened Std.Wrappers
  import opened WarblreNumeric      // NoI, Inf
  import opened WarblreRegExpRecord
  import opened WarblrePrimitives
  import opened Chars
  import opened Regex
  import opened Tree
  import opened NFA
  import opened BooleanSemantics   // LoopBool, CanExit, CannotExit
  import opened SeenSets
  import opened Semantics        // IsTree, Areg
  import opened Groups           // Empty
  import opened PikeSubset       // PikeRegex
  import opened PikeVM
  import opened Correctness      // TrcPikeVm, PikeVmCorrect
  import opened FunctionalPikeVM

  // ===== The seen-set as a finite key universe =====

  // All (pc, LoopBool) keys with pc < N. Finite (pc bounded, LoopBool is a 2-element datatype).
  /** The finite universe of `(pc, LoopBool)` memoization keys for code of length `N`; every key
      the seen-set (`SeenSets.SeenPcs`) can ever record lies in here. */
  ghost function KeyUniverse(N: nat): set<(Label, LoopBool)> {
    set pc: nat, b: LoopBool | pc < N :: (pc, b)
  }

  // The keys currently memoized. (`seen` is add-only-when-unseen, so it has distinct keys, but the
  // set-based measure below does not rely on that.)
  /** The set of `(pc, LoopBool)` keys already recorded in `seen`. */
  ghost function SeenSet(seen: SeenPcs): set<(Label, LoopBool)> {
    set k | k in seen
  }

  // Number of not-yet-seen keys in the universe. Decreases by exactly 1 whenever a fresh in-universe
  // key is memoized.
  /** How many `(pc, LoopBool)` keys (out of `KeyUniverse(N)`) `seen` has not yet recorded. */
  ghost function UnseenCount(seen: SeenPcs, N: nat): nat {
    |KeyUniverse(N) - SeenSet(seen)|
  }

  // Membership bridge: SeenThread <==> key in SeenSet.
  /** `PikeVM.SeenThread` agrees with membership in `SeenSet`. */
  lemma SeenThreadInSet(seen: SeenPcs, t: Thread)
    ensures SeenThread(seen, t) <==> (t.pc, t.b) in SeenSet(seen)
  {
    assert (t.pc, t.b) in SeenSet(seen) <==> (t.pc, t.b) in seen;
  }

  // Adding a fresh in-universe key drops UnseenCount by exactly 1.
  /** Memoizing a not-yet-seen, in-range thread's key strictly shrinks `UnseenCount` by 1 — the
      single fact that makes the seen-set dedup a valid termination measure. */
  lemma UnseenCountAddFresh(seen: SeenPcs, t: Thread, N: nat)
    requires t.pc < N
    requires !SeenThread(seen, t)
    ensures UnseenCount(AddThread(seen, t), N) == UnseenCount(seen, N) - 1
  {
    var key := (t.pc, t.b);
    SeenThreadInSet(seen, t);
    assert key in KeyUniverse(N);
    assert key !in SeenSet(seen);
    var U := KeyUniverse(N) - SeenSet(seen);
    assert key in U;
    // SeenSet(AddThread(seen,t)) == SeenSet(seen) + {key}
    assert AddThread(seen, t) == [key] + seen;
    assert SeenSet(AddThread(seen, t)) == SeenSet(seen) + {key};
    assert KeyUniverse(N) - SeenSet(AddThread(seen, t)) == U - {key};
    assert |U - {key}| == |U| - 1;
  }

  // ===== The per-position measure and its strict decrease =====

  /** The per-position termination measure: twice the unseen-key count plus the number of active
      threads. Strictly decreases on every step within a position (`PosBudgetDecreases`). */
  ghost function PosBudget(active: seq<Thread>, seen: SeenPcs, N: nat): nat {
    2 * UnseenCount(seen, N) + |active|
  }

  // CORE LEMMA. Any within-position step (|active| > 0: skip / expand / match / blocked — inp and
  // position never change) strictly decreases PosBudget, provided the head thread's pc is < N so its
  // key lives in the universe. This is the mathematical heart of termination: the dedup guarantees
  // monotone progress even though `active` can grow (Fork pushes 2).
  /** The core termination argument: every `PikeVmStep` that doesn't advance the input position
      strictly decreases `PosBudget`. */
  lemma PosBudgetDecreases(c: Code, rer: RegExpRecord, N: nat,
                           inp: Input, active: seq<Thread>, best: Option<Leaf>,
                           blocked: seq<Thread>, seen: SeenPcs, s2: PikeVmState)
    requires N == |c|
    requires |active| > 0
    requires active[0].pc < N
    requires PikeVmStep(c, rer, PVS(inp, active, best, blocked, seen), s2)
    ensures s2.PVS? && s2.inp == inp
    ensures PosBudget(s2.active, s2.seen, N) < PosBudget(active, seen, N)
  {
    var t := active[0];
    var rest := active[1..];
    assert active == [t] + rest;
    if SeenThread(seen, t) {
      // pvs_skip: active -> rest, seen unchanged.
      assert s2 == PVS(inp, rest, best, blocked, seen);
      // |rest| == |active| - 1
    } else {
      UnseenCountAddFresh(seen, t, N);   // UnseenCount drops by 1
      match EpsilonStep(rer, t, c, inp)
      case EpsActive(na) => {
        // pvs_active: active -> na + rest, seen -> AddThread(seen,t). |na| <= 2 (Fork is the max).
        assert s2 == PVS(inp, na + rest, best, blocked, AddThread(seen, t));
        EpsActiveFanout(rer, t, c, inp, na);   // |na| <= 2
        assert |na + rest| == |na| + |rest|;
      }
      case EpsMatch =>
        assert s2 == PVS(inp, [], Some((inp, GmOf(t))), blocked, AddThread(seen, t));
      case EpsBlocked(newt) =>
        assert s2 == PVS(inp, rest, best, blocked + [newt], AddThread(seen, t));
    }
  }

  // EpsilonStep produces at most 2 active successor threads (only Fork forks).
  /** `PikeVM.EpsilonStep` never spawns more than 2 successor threads (`Fork` is the only case
      producing more than one, and it produces exactly two). */
  lemma EpsActiveFanout(rer: RegExpRecord, t: Thread, c: Code, i: Input, na: seq<Thread>)
    requires EpsilonStep(rer, t, c, i) == EpsActive(na)
    ensures |na| <= 2
  {}

  // ===== The pc-boundedness invariant (needed so every processed key lives in the universe) =====

  /** Every thread in `ts` has a program counter within code of length `N`. */
  predicate ThreadsBounded(ts: seq<Thread>, N: nat) {
    forall k :: 0 <= k < |ts| ==> ts[k].pc < N
  }

  /** The PikeVM invariant maintained across `PikeVmStep`: all active and blocked threads' pcs stay
      within the code, so every processed key lies in `KeyUniverse(N)`. */
  predicate Inv(pvs: PikeVmState, N: nat) {
    match pvs
    case PVS_final(_) => true
    case PVS(inp, active, best, blocked, seen) =>
      ThreadsBounded(active, N) && ThreadsBounded(blocked, N)
  }

  // Well-formed code: every control-flow successor pc of an in-range instruction is in range. True of
  // any Compilation(r) (jump/fork/endloop targets are internal labels; +1 successors are never past
  // the trailing Accept). Proving CodeWfCompilation is the deep reachability lemma — see below.
  /** Every instruction's control-flow successors (`NFA.NextPcs`) stay inside the code — the
      well-formedness fact needed to keep `Inv` invariant across steps. */
  predicate CodeWf(c: Code) {
    forall pc :: 0 <= pc < |c| ==> forall l :: l in NextPcs(pc, c[pc]) ==> l < |c|
  }

  // Every active successor thread's pc is a control-flow successor of the processed pc.
  /** Every thread `EpsilonStep` puts into `EpsActive` has a pc among `NextPcs(t.pc, c[t.pc])`. */
  lemma EpsActivePcs(rer: RegExpRecord, t: Thread, c: Code, i: Input, na: seq<Thread>)
    requires t.pc < |c|
    requires EpsilonStep(rer, t, c, i) == EpsActive(na)
    ensures forall k :: 0 <= k < |na| ==> na[k].pc in NextPcs(t.pc, c[t.pc])
  {
    assert GetPc(c, t.pc) == Some(c[t.pc]);
  }

  // A blocked successor's pc is likewise a control-flow successor (Consume -> pc+1).
  /** The thread `EpsilonStep` produces in `EpsBlocked` likewise has a pc among `NextPcs`. */
  lemma EpsBlockedPc(rer: RegExpRecord, t: Thread, c: Code, i: Input, newt: Thread)
    requires t.pc < |c|
    requires EpsilonStep(rer, t, c, i) == EpsBlocked(newt)
    ensures newt.pc in NextPcs(t.pc, c[t.pc])
  {
    assert GetPc(c, t.pc) == Some(c[t.pc]);
  }

  // Invariant preservation, given well-formed code.
  /** `Inv` is preserved by `PikeVmStep`, given `CodeWf`. */
  lemma InvPreserved(c: Code, rer: RegExpRecord, N: nat, s1: PikeVmState, s2: PikeVmState)
    requires N == |c|
    requires CodeWf(c)
    requires Inv(s1, N)
    requires PikeVmStep(c, rer, s1, s2)
    ensures Inv(s2, N)
  {
    var PVS(inp, active, best, blocked, seen) := s1;
    if |active| == 0 {
      // finalize or advance; blocked (bounded) becomes the new active.
    } else {
      var t := active[0];
      var rest := active[1..];
      assert active == [t] + rest;
      assert t.pc < N;                       // from Inv(s1)
      assert ThreadsBounded(rest, N);
      if SeenThread(seen, t) {
      } else {
        match EpsilonStep(rer, t, c, inp)
        case EpsActive(na) => {
          EpsActivePcs(rer, t, c, inp, na);   // na pcs are NextPcs(t.pc, c[t.pc])
          assert ThreadsBounded(na, N) by { forall k | 0 <= k < |na| ensures na[k].pc < N { } }
          assert s2.active == na + rest;
          assert ThreadsBounded(na + rest, N);
        }
        case EpsMatch =>
        case EpsBlocked(newt) => {
          EpsBlockedPc(rer, t, c, inp, newt);
          assert newt.pc < N;
          assert s2.blocked == blocked + [newt];
          assert ThreadsBounded(blocked + [newt], N);
        }
      }
    }
  }

  // Every control target of every instruction in a compiled block is <= next (one past the block).
  // (Backward EndLoop targets frsh >= 0; forward targets and pc+1 successors are all <= next.)
  /** `NFA.Compile`'s output for `r` is well-formed within its own `[frsh, next)` block — every
      control-flow target lands at or before `next`. The structural building block for
      `CodeWfCompilation`. */
  /** `CompileWf` for the forced-minimum chain. */
  lemma CompileWfMin(k: nat, gidl: seq<GroupId>, r: Regex, frsh: Label, code: Code, next: Label)
    requires RepeatMin(k, gidl, r, frsh) == (code, next)
    ensures next == frsh + |code|
    ensures forall i, l {:autotriggers false} :: 0 <= i < |code| && l in NextPcs(frsh + i, code[i]) ==> l <= next
    decreases RegexSize(r), k + 2
  {
    FreshCorrectMin(k, gidl, r, frsh, code, next);
    if k > 0 {
      var c1 := Compile(r, frsh + 1);
      var bc1, f1 := c1.0, c1.1;
      var (c2, f2) := RepeatMin(k - 1, gidl, r, f1);
      assert code == [ResetRegs(gidl)] + bc1 + c2 && next == f2;
      FreshCorrect(r, frsh + 1, bc1, f1);
      FreshCorrectMin(k - 1, gidl, r, f1, c2, f2);
      CompileWf(r, frsh + 1, bc1, f1);
      CompileWfMin(k - 1, gidl, r, f1, c2, f2);
      forall i, l {:autotriggers false} | 0 <= i < |code| && l in NextPcs(frsh + i, code[i]) ensures l <= next {
        if i == 0 {                                   // ResetRegs -> frsh+1 <= next
        } else if i < 1 + |bc1| {
          assert code[i] == bc1[i - 1];
          assert frsh + i == (frsh + 1) + (i - 1);
        } else {
          assert code[i] == c2[i - 1 - |bc1|];
          assert frsh + i == f1 + (i - 1 - |bc1|);
        }
      }
    }
  }

  /** `CompileWf` for the optional-layer chain. */
  lemma CompileWfOpt(k: nat, greedy: bool, gidl: seq<GroupId>, r: Regex, frsh: Label, code: Code, next: Label)
    requires RepeatOpt(k, greedy, gidl, r, frsh) == (code, next)
    ensures next == frsh + |code|
    ensures forall i, l {:autotriggers false} :: 0 <= i < |code| && l in NextPcs(frsh + i, code[i]) ==> l <= next
    decreases RegexSize(r), k + 2
  {
    FreshCorrectOpt(k, greedy, gidl, r, frsh, code, next);
    if k > 0 {
      var c1 := Compile(r, frsh + 3);
      var bc1, f1 := c1.0, c1.1;
      var (c2, f2) := RepeatOpt(k - 1, greedy, gidl, r, f1 + 1);
      var hdr := [GreedyFork(greedy, frsh + 1, f2), BeginLoop, ResetRegs(gidl)];
      assert code == hdr + bc1 + [EndLoop(f1 + 1)] + c2 && next == f2;
      FreshCorrect(r, frsh + 3, bc1, f1);
      FreshCorrectOpt(k - 1, greedy, gidl, r, f1 + 1, c2, f2);
      CompileWf(r, frsh + 3, bc1, f1);
      CompileWfOpt(k - 1, greedy, gidl, r, f1 + 1, c2, f2);
      forall i, l {:autotriggers false} | 0 <= i < |code| && l in NextPcs(frsh + i, code[i]) ensures l <= next {
        if i == 0 {                                   // fork targets frsh+1, f2 (== next)
        } else if i == 1 {                            // BeginLoop
        } else if i == 2 {                            // ResetRegs
        } else if i < 3 + |bc1| {
          assert code[i] == bc1[i - 3];
          assert frsh + i == (frsh + 3) + (i - 3);
        } else if i == 3 + |bc1| {                    // EndLoop(f1+1) -> f1+1 <= next
          assert code[i] == EndLoop(f1 + 1);
        } else {
          assert code[i] == c2[i - 4 - |bc1|];
          assert frsh + i == (f1 + 1) + (i - 4 - |bc1|);
        }
      }
    }
  }

  lemma CompileWf(r: Regex, frsh: Label, code: Code, next: Label)
    requires Compile(r, frsh) == (code, next)
    ensures next == frsh + |code|
    ensures forall i, l {:autotriggers false} :: 0 <= i < |code| && l in NextPcs(frsh + i, code[i]) ==> l <= next
    decreases RegexSize(r), 1
  {
    FreshCorrect(r, frsh, code, next);   // next == frsh + |code|
    match r
    case Epsilon =>
    case Character(_) =>
    case AnchorR(_) =>
    case Backreference(_) =>
    case LookaroundR(_, _) =>
    case Disjunction(r1, r2) =>
      var c1 := Compile(r1, frsh + 1);
      var c2 := Compile(r2, c1.1 + 1);
      var bc1, f1, bc2, f2 := c1.0, c1.1, c2.0, c2.1;
      FreshCorrect(r1, frsh + 1, bc1, f1);          // f1 == frsh + 1 + |bc1|
      FreshCorrect(r2, f1 + 1, bc2, f2);            // f2 == f1 + 1 + |bc2|
      CompileWf(r1, frsh + 1, bc1, f1);
      CompileWf(r2, f1 + 1, bc2, f2);
      assert code == [Fork(frsh + 1, f1 + 1)] + bc1 + [Jmp(f2)] + bc2 && next == f2;
      forall i, l {:autotriggers false} | 0 <= i < |code| && l in NextPcs(frsh + i, code[i]) ensures l <= next {
        if i == 0 {                                  // Fork(frsh+1, f1+1); both <= f2
        } else if i < 1 + |bc1| {                    // in bc1 region: code[i] == bc1[i-1]
          assert code[i] == bc1[i - 1];
          assert frsh + i == (frsh + 1) + (i - 1);
        } else if i == 1 + |bc1| {                   // Jmp(f2); target f2 == next
          assert code[i] == Jmp(f2);
        } else {                                     // in bc2 region: code[i] == bc2[i-(2+|bc1|)]
          assert code[i] == bc2[i - (2 + |bc1|)];
          assert frsh + i == (f1 + 1) + (i - (2 + |bc1|));
        }
      }
    case Sequence(r1, r2) =>
      var c1 := Compile(r1, frsh);
      var c2 := Compile(r2, c1.1);
      var bc1, f1, bc2, f2 := c1.0, c1.1, c2.0, c2.1;
      FreshCorrect(r1, frsh, bc1, f1);              // f1 == frsh + |bc1|
      FreshCorrect(r2, f1, bc2, f2);
      CompileWf(r1, frsh, bc1, f1);
      CompileWf(r2, f1, bc2, f2);
      assert code == bc1 + bc2 && next == f2;
      forall i, l {:autotriggers false} | 0 <= i < |code| && l in NextPcs(frsh + i, code[i]) ensures l <= next {
        if i < |bc1| {
          assert code[i] == bc1[i];
        } else {
          assert code[i] == bc2[i - |bc1|];
          assert frsh + i == f1 + (i - |bc1|);
        }
      }
    case Quantified(greedy, min, delta, r1) =>
      var gidl := DefGroups(r1);
      var (mc, mf) := RepeatMin(min, gidl, r1, frsh);
      FreshCorrectMin(min, gidl, r1, frsh, mc, mf);   // mf == frsh + |mc|
      CompileWfMin(min, gidl, r1, frsh, mc, mf);
      match delta {
        case Inf =>
          var c1 := Compile(r1, mf + 3);
          var bc1, f1 := c1.0, c1.1;
          FreshCorrect(r1, mf + 3, bc1, f1);          // f1 == mf + 3 + |bc1|
          CompileWf(r1, mf + 3, bc1, f1);
          var hdr := [GreedyFork(greedy, mf + 1, f1 + 1), BeginLoop, ResetRegs(gidl)];
          assert code == mc + (hdr + bc1 + [EndLoop(mf)]) && next == f1 + 1;
          forall i, l {:autotriggers false} | 0 <= i < |code| && l in NextPcs(frsh + i, code[i]) ensures l <= next {
            if i < |mc| {                              // forced chain: targets <= mf <= next
              assert code[i] == mc[i];
            } else if i == |mc| {                      // fork targets mf+1, f1+1 (== next)
            } else if i == |mc| + 1 {                  // BeginLoop
            } else if i == |mc| + 2 {                  // ResetRegs
            } else if i < |mc| + 3 + |bc1| {           // bc1 region
              assert code[i] == bc1[i - |mc| - 3];
              assert frsh + i == (mf + 3) + (i - |mc| - 3);
            } else {                                   // EndLoop(mf) -> mf <= next
              assert code[i] == EndLoop(mf);
            }
          }
        case NN(k) =>
          var (oc, of) := RepeatOpt(k, greedy, gidl, r1, mf);
          FreshCorrectOpt(k, greedy, gidl, r1, mf, oc, of);   // of == mf + |oc|
          CompileWfOpt(k, greedy, gidl, r1, mf, oc, of);
          assert code == mc + oc && next == of;
          forall i, l {:autotriggers false} | 0 <= i < |code| && l in NextPcs(frsh + i, code[i]) ensures l <= next {
            if i < |mc| {
              assert code[i] == mc[i];
            } else {
              assert code[i] == oc[i - |mc|];
              assert frsh + i == mf + (i - |mc|);
            }
          }
      }
    case Group(gid, r1) =>
      var c1 := Compile(r1, frsh + 1);
      var bc1, f1 := c1.0, c1.1;
      FreshCorrect(r1, frsh + 1, bc1, f1);          // f1 == frsh + 1 + |bc1|
      CompileWf(r1, frsh + 1, bc1, f1);
      assert code == [SetRegOpen(gid)] + bc1 + [SetRegClose(gid)] && next == f1 + 1;
      forall i, l {:autotriggers false} | 0 <= i < |code| && l in NextPcs(frsh + i, code[i]) ensures l <= next {
        if i == 0 {                                  // SetRegOpen -> frsh+1 <= f1+1
        } else if i < 1 + |bc1| {                    // bc1 region
          assert code[i] == bc1[i - 1];
          assert frsh + i == (frsh + 1) + (i - 1);
        } else {                                     // SetRegClose at f1 -> f1+1 == next
          assert code[i] == SetRegClose(gid);
        }
      }
  }

  // Every control target in a compiled PROGRAM is in range: CodeWf(Compilation(r)). Discharges the
  // reachability obligation of the termination proof.
  /** `NFA.Compilation(r)` is always well-formed code (`CodeWf`) — every jump/fork/endloop target
      is a valid label, including the trailing `Accept`. */
  lemma CodeWfCompilation(r: Regex)
    ensures CodeWf(Compilation(r))
  {
    var block, next := Compile(r, 0).0, Compile(r, 0).1;
    CompileWf(r, 0, block, next);
    FreshCorrect(r, 0, block, next);                 // next == |block|
    var prog := Compilation(r);
    assert prog == block + [Accept];
    assert |prog| == |block| + 1;
    forall pc | 0 <= pc < |prog| ensures forall l :: l in NextPcs(pc, prog[pc]) ==> l < |prog| {
      if pc < |block| {
        assert prog[pc] == block[pc];
        // CompileWf: targets of block[pc] (at abs pc == 0 + pc) are <= next == |block| < |prog|
        assert forall l {:autotriggers false} :: l in NextPcs(0 + pc, block[pc]) ==> l <= next;
      } else {
        assert pc == |block|;
        assert prog[pc] == Accept;
        assert NextPcs(pc, Accept) == [];
      }
    }
  }

  // ===== The whole-run measure and loop termination =====

  // Membership in the key universe is exactly the pc bound.
  /** A key belongs to `KeyUniverse(N)` exactly when its pc component is below `N`. */
  lemma KeyUniverseMem(k: (Label, LoopBool), N: nat)
    ensures k in KeyUniverse(N) <==> k.0 < N
  {}

  // The key universe has exactly 2*N elements (N pcs x {CanExit, CannotExit}).
  /** `|KeyUniverse(N)| == 2*N` — used to bound `UnseenCount` and size `RunMeasure`. */
  lemma KeyUniverseCard(N: nat)
    ensures |KeyUniverse(N)| == 2 * N
  {
    if N == 0 {
      assert KeyUniverse(0) == {};
    } else {
      KeyUniverseCard(N - 1);
      var lo := KeyUniverse(N - 1);
      var newk := {(N - 1, CanExit), (N - 1, CannotExit)};
      assert |newk| == 2;
      forall k | k in KeyUniverse(N) ensures k in lo + newk {
        KeyUniverseMem(k, N);
        KeyUniverseMem(k, N - 1);
        if k.0 < N - 1 { } else { assert k.0 == N - 1; assert k.1 == CanExit || k.1 == CannotExit; }
      }
      forall k | k in lo + newk ensures k in KeyUniverse(N) {
        KeyUniverseMem(k, N);
        KeyUniverseMem(k, N - 1);
      }
      assert KeyUniverse(N) == lo + newk;
      assert lo !! newk by { KeyUniverseMem((N - 1, CanExit), N - 1); KeyUniverseMem((N - 1, CannotExit), N - 1); }
    }
  }

  /** `UnseenCount` is always at most `2*N`, since it counts a subset of `KeyUniverse(N)`. */
  lemma UnseenCountBound(seen: SeenPcs, N: nat)
    ensures UnseenCount(seen, N) <= 2 * N
  {
    KeyUniverseCard(N);
    assert KeyUniverse(N) - SeenSet(seen) <= KeyUniverse(N);
  }

  // Whole-run measure: per-position weight (4N+1) times remaining input, plus the in-position budget,
  // plus a +1 so that every non-final state has measure >= 1 (covers the finalize step).
  /** The whole-run termination measure: `PosBudget`-like accounting weighted by remaining input
      length, so it strictly decreases on both within-position steps and position advances
      (`RunMeasureDecreases`). Sized so `RunMeasure(initial) == BytecodeFuel + 1`. */
  ghost function RunMeasure(pvs: PikeVmState, N: nat): nat {
    match pvs
    case PVS_final(_) => 0
    case PVS(inp, active, best, blocked, seen) =>
      (4 * N + 1) * |NextStr(inp)| + 2 * UnseenCount(seen, N) + |active| + |blocked| + 1
  }

  // Every step strictly decreases RunMeasure (within-position via the dedup; position-advance because
  // the (4N+1) weight dominates the seen-set reset; finalize because a non-final state has measure >= 1).
  /** Every `PikeVmStep` strictly decreases `RunMeasure` — the single fact that drives
      `LoopReachesFinal`. */
  lemma RunMeasureDecreases(c: Code, rer: RegExpRecord, N: nat, s1: PikeVmState, s2: PikeVmState)
    requires N == |c|
    requires CodeWf(c)
    requires Inv(s1, N)
    requires PikeVmStep(c, rer, s1, s2)
    ensures RunMeasure(s2, N) < RunMeasure(s1, N)
  {
    var PVS(inp, active, best, blocked, seen) := s1;
    if |active| == 0 {
      if |blocked| == 0 {
        // finalize: s2 == PVS_final(best), RunMeasure(s2) == 0 < RunMeasure(s1) (>= 1).
      } else {
        match AdvanceInput(inp, Forward)
        case None =>   // s2 == PVS_final(best), measure 0 < RunMeasure(s1).
        case Some(inp2) => {
          assert s2 == PVS(inp2, blocked, best, [], InitialSeenPcs);
          var W := 4 * N + 1;
          var n := |NextStr(inp)|;
          assert |NextStr(inp2)| == n - 1;                 // Forward advance drops next[0]
          assert n >= 1;
          assert SeenSet(InitialSeenPcs) == {};
          assert UnseenCount(InitialSeenPcs, N) == |KeyUniverse(N)|;
          KeyUniverseCard(N);                              // |KeyUniverse(N)| == 2N
          UnseenCountBound(seen, N);                       // UnseenCount(seen,N) <= 2N
          assert W * (n - 1) == W * n - W;                 // distribute (help nonlinear)
          // RunMeasure(s2) = W*(n-1) + 2*2N + |blocked| + 1
          // RunMeasure(s1) = W*n + 2*UnseenCount(seen,N) + |blocked| + 1  (active empty)
          // Δ = -W + 2*(2N - UnseenCount(seen,N)) <= -(4N+1) + 4N = -1.
        }
      }
    } else {
      var t := active[0];
      var rest := active[1..];
      assert active == [t] + rest;
      assert t.pc < N;                                     // from Inv(s1)
      if SeenThread(seen, t) {
        assert s2 == PVS(inp, rest, best, blocked, seen);  // active -1
      } else {
        UnseenCountAddFresh(seen, t, N);                   // UnseenCount -1
        match EpsilonStep(rer, t, c, inp)
        case EpsActive(na) => {
          assert s2 == PVS(inp, na + rest, best, blocked, AddThread(seen, t));
          EpsActiveFanout(rer, t, c, inp, na);             // |na| <= 2
          assert |na + rest| == |na| + |rest|;
          // Δ = -2 (unseen) + (|na|-1) (active) <= -1.
        }
        case EpsMatch =>
          assert s2 == PVS(inp, [], Some((inp, GmOf(t))), blocked, AddThread(seen, t));
        case EpsBlocked(newt) => {
          assert s2 == PVS(inp, rest, best, blocked + [newt], AddThread(seen, t));
          assert |blocked + [newt]| == |blocked| + 1;
          // Δ = -2 (unseen) - 1 (active) + 1 (blocked) = -2.
        }
      }
    }
  }

  // The loop reaches a final state within any fuel that covers RunMeasure.
  /** `FunctionalPikeVM.PikeVmLoop` reaches a `PVS_final` state whenever `fuel` is at least
      `RunMeasure(pvs, N)` — the termination bound, still generic in the starting state. */
  lemma LoopReachesFinal(c: Code, rer: RegExpRecord, N: nat, pvs: PikeVmState, fuel: nat)
    requires N == |c|
    requires CodeWf(c)
    requires Inv(pvs, N)
    requires fuel >= RunMeasure(pvs, N)
    ensures PikeVmLoop(c, rer, pvs, fuel).PVS_final?
    decreases fuel
  {
    match pvs
    case PVS_final(_) =>   // PikeVmLoop returns pvs, already final.
    case PVS(inp, active, best, blocked, seen) => {
      assert RunMeasure(pvs, N) >= 1;    // non-final ==> measure >= 1
      assert fuel >= 1;
      var mid := PikeVmFuncStep(c, rer, pvs);
      FuncStepNotFinal(c, rer, inp, active, best, blocked, seen);   // PikeVmStep(pvs, mid)
      RunMeasureDecreases(c, rer, N, pvs, mid);                     // RunMeasure(mid) < RunMeasure(pvs)
      InvPreserved(c, rer, N, pvs, mid);                           // Inv(mid)
      LoopReachesFinal(c, rer, N, mid, fuel - 1);
      assert PikeVmLoop(c, rer, pvs, fuel) == PikeVmLoop(c, rer, mid, fuel - 1);
    }
  }

  // Initial-state invariant: the initial thread has pc 0 < |code|.
  /** `Inv` holds of `PikeVM.PikeVmInitialState` against `NFA.Compilation(r)`. */
  lemma InitialInv(r: Regex, inp: Input)
    ensures Inv(PikeVmInitialState(inp), |Compilation(r)|)
  {
    assert |Compilation(r)| == |Compile(r, 0).0| + 1;   // Compilation(r) = Compile(r,0).0 + [Accept]
  }

  // ===== Top-level result =====

  // The PikeVM reaches a final state within BytecodeFuel + 1 steps. This IS the O(|c|.n) linear-time
  // bound (BytecodeFuel = (4|c|+1)(n+1)). Modulo the CodeWfCompilation reachability axiom.
  //
  // NOTE (fuel off-by-one): under this measure RunMeasure(initial) = BytecodeFuel + 1, so the artifact's
  // exact BytecodeFuel is one step short of the worst case. Closing PikeVmMatch(...).Finished? for the
  // AS-DEFINED BytecodeFuel needs either a +1 bump to BytecodeFuel (harmless — it is our definition and
  // only affects the executable's budget; correctness needs only Finished) or a tighter (by 1) measure.
  /** The termination capstone: `PikeVmLoop`, started fresh on `Compilation(r)`, is guaranteed to
      finish within `BytecodeFuel(...) + 1` steps — the `O(|code| * n)` linear-time bound. */
  lemma PikeVmReachesFinal(rer: RegExpRecord, r: Regex, inp: Input, fuel: nat)
    requires fuel >= BytecodeFuel(Compilation(r), inp) + 1
    ensures PikeVmLoop(Compilation(r), rer, PikeVmInitialState(inp), fuel).PVS_final?
  {
    var code := Compilation(r);
    var N := |code|;
    CodeWfCompilation(r);
    InitialInv(r, inp);
    KeyUniverseCard(N);
    // RunMeasure(initial) = (4N+1)*n + 2*2N + 1 + 0 + 1 = (4N+1)(n+1) + 1 = BytecodeFuel + 1.
    assert SeenSet(InitialSeenPcs) == {};
    assert UnseenCount(InitialSeenPcs, N) == 2 * N;
    assert RunMeasure(PikeVmInitialState(inp), N) == BytecodeFuel(code, inp) + 1;
    LoopReachesFinal(code, rer, N, PikeVmInitialState(inp), fuel);
  }

  // CAPSTONE — total correctness. With fuel >= BytecodeFuel + 1 (= O(|c|.n)) the executable VM loop
  // always halts (never OutOfFuel) AND returns exactly the highest-priority leaf of the tree semantics.
  // This combines the new termination result with the already-proved PikeVmCorrect (Thm 16). Fully
  // axiom-free; the only distance from PikeVmMatch's exact BytecodeFuel is the documented +1.
  /** TOTAL correctness of the executable PikeVM: given sufficient fuel it both halts and returns
      `FirstLeaf(tree, inp)`, combining this file's termination bound with
      `Correctness.PikeVmCorrect`. */
  lemma PikeVmTotalCorrect(rer: RegExpRecord, r: Regex, inp: Input, tree: Tree, fuel: nat)
    requires PikeRegex(r)
    requires IsTree(rer, [Areg(r)], inp, Empty, Forward, tree)
    requires fuel >= BytecodeFuel(Compilation(r), inp) + 1
    ensures GetRes(PikeVmLoop(Compilation(r), rer, PikeVmInitialState(inp), fuel))
            == Finished(FirstLeaf(tree, inp))
  {
    var code := Compilation(r);
    PikeVmReachesFinal(rer, r, inp, fuel);
    var final := PikeVmLoop(code, rer, PikeVmInitialState(inp), fuel);
    assert final.PVS_final?;
    var result := final.best;
    assert final == PVS_final(result);
    LoopTrc(code, rer, PikeVmInitialState(inp), final, fuel);   // TrcPikeVm(init, PVS_final(result))
    PikeVmCorrect(rer, r, inp, tree, result);                    // result == FirstLeaf(tree, inp)
  }
}
