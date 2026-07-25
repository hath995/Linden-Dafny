// Phase +C3: WalkOk — the guard carrier for the checked-tree construction.
//
// The construction (ActionsTreeRepRE) must exclude one family of adversarial
// configurations: a bare star head sitting on a BACKWARD fork (the do-while's
// loop view) while the walk flag is CannotExit. There the spec tree is a cold
// Choice, the only representable tree is Mismatch (tr_plusfail), and their
// leaves genuinely differ — the lemma's ensures would be false. Such configs
// never arise from compiled code (every loop-view star is reached through an
// Acheck, which re-arms the flag), but the induction sees arbitrary
// rep-satisfying inputs, so the exclusion must be carried as a hypothesis.
//
// WalkOk(acts, c, pc, g) says: along every abstract walk of `acts` from `pc`
// (mirroring the construction's own case unfoldings, with flows read off the
// INSTRUCTION PAYLOADS so no existential witnesses can diverge), a loop-view
// star head is only reached when the guard bit `g` — "the flag is provably
// CanExit here" — is set. The bit evolves in lockstep with the walk flag:
// reads and passed checks set it, free iterations clear it, zero-width steps
// carry it. It is encoded as a fuel-indexed predicate quantified over all
// fuels (the greatest-fixpoint reading), so consuming one step is a single
// instantiation and establishing it for compiled code is a plain nat
// induction.
include "ActionsRepRE.dfy"

/** Phase +C3 — the `WalkOk` guard carrier: excludes cold loop-view star
    configurations from the checked-tree construction's inputs. Fuel-indexed
    with a forall-fuel wrapper; destructor lemmas per walk step. */
module LindenElkWalkOk {
  import opened Std.Wrappers
  import LC = Chars
  import LG = Groups
  import L = Regex
  import LN = WarblreNumeric
  import LS = Semantics
  import FS = FunctionalSemantics
  import RB = Bytecode
  import NR = LindenElkNfaRep
  import AR = LindenElkActionsRep

  /** A bare star: the only regex whose representation can sit on a backward
      fork (the do-while's loop view). */
  predicate IsBareStar(r: L.Regex) {
    r.Quantified? && r.min == 0 && r.delta.Inf?
  }

  /** One fuel level of the walk-guard predicate. `n == 0` demands nothing;
      each unfolding steps the abstract walk once, with flows keyed on the
      instruction payloads at `pc` (so they coincide with whatever witnesses
      the representation predicates produce). The single demand with content
      is the `g` conjunct in the loop-view branch of the star case. */
  ghost predicate WalkOkF(acts: LS.Actions, c: RB.code, pc: nat, g: bool, n: nat)
    decreases n, 1
  {
    n == 0 ||
    ((match NR.GetPcRE(c, pc)
      case Some(Jmp(np)) => np >= 0 ==> WalkOkF(acts, c, np as nat, g, n - 1)
      case _ => true)
     && (|acts| == 0 ||
         (var cont := acts[1..];
          match acts[0]
          case Acheck(_) =>
            (NR.GetPcRE(c, pc) == Some(RB.EndLoop) ==> WalkOkF(cont, c, pc + 1, true, n - 1))
            && (AR.BackForkAt(c, pc) ==> WalkOkF(cont, c, pc, true, n - 1))
          case Aclose(_) =>
            (match NR.GetPcRE(c, pc)
             case Some(SetRegisterToCP(_)) => WalkOkF(cont, c, pc + 1, g, n - 1)
             case _ => true)
          case Areg(r) => WalkOkRegF(r, cont, c, pc, g, n))))
  }

  /** The `Areg` head cases of `WalkOkF`, one per regex shape — each mirrors
      the corresponding list expansion the construction performs, guarded by
      the instruction that expansion pins (transparent shapes expand in place,
      unguarded). */
  ghost predicate WalkOkRegF(r: L.Regex, cont: LS.Actions, c: RB.code, pc: nat, g: bool, n: nat)
    requires n > 0
    decreases n, 0
  {
    match r
    case Epsilon => WalkOkF(cont, c, pc, g, n - 1)
    case Character(_) =>
      (match NR.GetPcRE(c, pc)
       case Some(Consume(_)) => WalkOkF(cont, c, pc + 1, true, n - 1)
       case _ => true)
    case AnchorR(_) =>
      (match NR.GetPcRE(c, pc)
       case Some(AnchorAssertion(_)) => WalkOkF(cont, c, pc + 1, g, n - 1)
       case _ => true)
    case Sequence(r1, r2) =>
      WalkOkF([LS.Areg(r1), LS.Areg(r2)] + cont, c, pc, g, n - 1)
    case Group(gid, r1) =>
      (match NR.GetPcRE(c, pc)
       case Some(SetRegisterToCP(_)) => WalkOkF([LS.Areg(r1), LS.Aclose(gid)] + cont, c, pc + 1, g, n - 1)
       case _ => true)
    case Disjunction(r1, r2) =>
      (match NR.GetPcRE(c, pc)
       case Some(Fork(x, y)) =>
         x >= 0 && y >= 0 ==>
           WalkOkF([LS.Areg(r1)] + cont, c, x as nat, g, n - 1)
           && WalkOkF([LS.Areg(r2)] + cont, c, y as nat, g, n - 1)
       case _ => true)
    case Quantified(greedy, min, delta, r1) =>
      if min > 0 then
        (match NR.GetPcRE(c, pc)
         case Some(SetQuantToClock(_, _)) =>
           if delta.Inf? && min == 1 then
             // the do-while seam: the walk enters the guaranteed last forced
             // iteration with the progress check inserted (any recorded input)
             forall chk: LC.Input ::
               WalkOkF([LS.Areg(r1), LS.Acheck(chk), LS.Areg(L.Quantified(greedy, 0, LN.Inf, r1))] + cont,
                       c, pc + 1, g, n - 1)
           else
             WalkOkF([LS.Areg(r1), LS.Areg(L.Quantified(greedy, min - 1, delta, r1))] + cont, c, pc + 1, g, n - 1)
         case _ => true)
      else if delta == LN.NN(0) then
        WalkOkF(cont, c, pc, g, n - 1)
      else
        (match NR.GetPcRE(c, pc)
         case Some(Fork(x, y)) =>
           x >= 0 && y >= 0 ==>
             var iterarm := (if greedy then x else y) as nat;
             var skiparm := (if greedy then y else x) as nat;
             var qnext := L.Quantified(greedy, 0, FS.NoiPred(delta), r1);
             if iterarm <= pc then
               // the LOOP VIEW: a bare star at the do-while's backward fork —
               // only admissible when the flag is provably CanExit. The
               // iteration fact is provided at TRUE: the construction lifts
               // the iteration's flag to CanExit (BoolFlagLift) before
               // recursing, so the lockstep bit is true there.
               g
               && (forall chk: LC.Input ::
                     WalkOkF([LS.Areg(r1), LS.Acheck(chk), LS.Areg(qnext)] + cont, c, iterarm + 1, true, n - 1))
               && WalkOkF(cont, c, skiparm, g, n - 1)
             else
               // a forward decision point: star fast path / bounded layer
               (forall chk: LC.Input ::
                  WalkOkF([LS.Areg(r1), LS.Acheck(chk), LS.Areg(qnext)] + cont, c, iterarm + 2, false, n - 1))
               && WalkOkF(cont, c, skiparm, g, n - 1)
         case _ => true)
    // the lookaround gate: one zero-width instruction, so the walk continues
    // at pc + 1 with the flag unchanged (the body is not walked here — it
    // lives in the per-lid build program). Guarded on the instruction, like
    // every other arm: at a pc holding something else there is nothing to say.
    case LookaroundR(_, _) =>
      (match NR.GetPcRE(c, pc)
       case Some(CheckOracle(_)) => WalkOkF(cont, c, pc + 1, g, n - 1)
       case Some(NegCheckOracle(_)) => WalkOkF(cont, c, pc + 1, g, n - 1)
       case _ => true)
    case Backreference(_) => true    // not pike: never walked
  }

  /** The walk guard at every fuel — the greatest-fixpoint reading of
      `WalkOkF`. This is what the construction threads: one hypothesis
      instantiation per step, `g` in lockstep with the walk flag. */
  ghost predicate WalkOk(acts: LS.Actions, c: RB.code, pc: nat, g: bool) {
    forall n: nat :: WalkOkF(acts, c, pc, g, n)
  }

  // ===========================================================================
  // Destructors: one walk step each
  // ===========================================================================

  lemma WalkOkJmp(acts: LS.Actions, c: RB.code, pc: nat, g: bool, np: int)
    requires WalkOk(acts, c, pc, g)
    requires NR.GetPcRE(c, pc) == Some(RB.Jmp(np)) && np >= 0
    ensures WalkOk(acts, c, np as nat, g)
  {
    forall n: nat {:trigger WalkOkF(acts, c, np as nat, g, n)} ensures WalkOkF(acts, c, np as nat, g, n) {
      assert WalkOkF(acts, c, pc, g, n + 1);
      if |acts| > 0 && acts[0].Areg? {
        assert WalkOkRegF(acts[0].r, acts[1..], c, pc, g, n + 1);
      }
    }
  }

  lemma WalkOkAcheckEndLoop(acts: LS.Actions, c: RB.code, pc: nat, g: bool)
    requires WalkOk(acts, c, pc, g)
    requires |acts| > 0 && acts[0].Acheck?
    requires NR.GetPcRE(c, pc) == Some(RB.EndLoop)
    ensures WalkOk(acts[1..], c, pc + 1, true)
  {
    forall n: nat {:trigger WalkOkF(acts[1..], c, pc + 1, true, n)} ensures WalkOkF(acts[1..], c, pc + 1, true, n) {
      assert WalkOkF(acts, c, pc, g, n + 1);
      if |acts| > 0 && acts[0].Areg? {
        assert WalkOkRegF(acts[0].r, acts[1..], c, pc, g, n + 1);
      }
    }
  }

  lemma WalkOkAcheckBackFork(acts: LS.Actions, c: RB.code, pc: nat, g: bool)
    requires WalkOk(acts, c, pc, g)
    requires |acts| > 0 && acts[0].Acheck?
    requires AR.BackForkAt(c, pc)
    ensures WalkOk(acts[1..], c, pc, true)
  {
    forall n: nat {:trigger WalkOkF(acts[1..], c, pc, true, n)} ensures WalkOkF(acts[1..], c, pc, true, n) {
      assert WalkOkF(acts, c, pc, g, n + 1);
      if |acts| > 0 && acts[0].Areg? {
        assert WalkOkRegF(acts[0].r, acts[1..], c, pc, g, n + 1);
      }
    }
  }

  lemma WalkOkAclose(acts: LS.Actions, c: RB.code, pc: nat, g: bool)
    requires WalkOk(acts, c, pc, g)
    requires |acts| > 0 && acts[0].Aclose?
    requires NR.GetPcRE(c, pc).Some? && NR.GetPcRE(c, pc).value.SetRegisterToCP?
    ensures WalkOk(acts[1..], c, pc + 1, g)
  {
    forall n: nat {:trigger WalkOkF(acts[1..], c, pc + 1, g, n)} ensures WalkOkF(acts[1..], c, pc + 1, g, n) {
      assert WalkOkF(acts, c, pc, g, n + 1);
      if |acts| > 0 && acts[0].Areg? {
        assert WalkOkRegF(acts[0].r, acts[1..], c, pc, g, n + 1);
      }
    }
  }

  lemma WalkOkEpsilon(acts: LS.Actions, c: RB.code, pc: nat, g: bool)
    requires WalkOk(acts, c, pc, g)
    requires |acts| > 0 && acts[0] == LS.Areg(L.Epsilon)
    ensures WalkOk(acts[1..], c, pc, g)
  {
    forall n: nat {:trigger WalkOkF(acts[1..], c, pc, g, n)} ensures WalkOkF(acts[1..], c, pc, g, n) {
      assert WalkOkF(acts, c, pc, g, n + 1);
      if |acts| > 0 && acts[0].Areg? {
        assert WalkOkRegF(acts[0].r, acts[1..], c, pc, g, n + 1);
      }
    }
  }

  lemma WalkOkCharacter(acts: LS.Actions, c: RB.code, pc: nat, g: bool)
    requires WalkOk(acts, c, pc, g)
    requires |acts| > 0 && acts[0].Areg? && acts[0].r.Character?
    requires NR.GetPcRE(c, pc).Some? && NR.GetPcRE(c, pc).value.Consume?
    ensures WalkOk(acts[1..], c, pc + 1, true)
  {
    forall n: nat {:trigger WalkOkF(acts[1..], c, pc + 1, true, n)} ensures WalkOkF(acts[1..], c, pc + 1, true, n) {
      assert WalkOkF(acts, c, pc, g, n + 1);
      if |acts| > 0 && acts[0].Areg? {
        assert WalkOkRegF(acts[0].r, acts[1..], c, pc, g, n + 1);
      }
    }
  }

  lemma WalkOkAnchor(acts: LS.Actions, c: RB.code, pc: nat, g: bool)
    requires WalkOk(acts, c, pc, g)
    requires |acts| > 0 && acts[0].Areg? && acts[0].r.AnchorR?
    requires NR.GetPcRE(c, pc).Some? && NR.GetPcRE(c, pc).value.AnchorAssertion?
    ensures WalkOk(acts[1..], c, pc + 1, g)
  {
    forall n: nat {:trigger WalkOkF(acts[1..], c, pc + 1, g, n)} ensures WalkOkF(acts[1..], c, pc + 1, g, n) {
      assert WalkOkF(acts, c, pc, g, n + 1);
      if |acts| > 0 && acts[0].Areg? {
        assert WalkOkRegF(acts[0].r, acts[1..], c, pc, g, n + 1);
      }
    }
  }

  /** `WalkOkAnchor` for the lookaround gate: zero-width, so the continuation's
      guard sits at `pc + 1` with the same flag. */
  lemma WalkOkLookaround(acts: LS.Actions, c: RB.code, pc: nat, g: bool)
    requires WalkOk(acts, c, pc, g)
    requires |acts| > 0 && acts[0].Areg? && acts[0].r.LookaroundR?
    requires NR.GetPcRE(c, pc).Some?
             && (NR.GetPcRE(c, pc).value.CheckOracle? || NR.GetPcRE(c, pc).value.NegCheckOracle?)
    ensures WalkOk(acts[1..], c, pc + 1, g)
  {
    forall n: nat {:trigger WalkOkF(acts[1..], c, pc + 1, g, n)} ensures WalkOkF(acts[1..], c, pc + 1, g, n) {
      assert WalkOkF(acts, c, pc, g, n + 1);
      if |acts| > 0 && acts[0].Areg? {
        assert WalkOkRegF(acts[0].r, acts[1..], c, pc, g, n + 1);
      }
    }
  }

  lemma WalkOkSeq(acts: LS.Actions, c: RB.code, pc: nat, g: bool, r1: L.Regex, r2: L.Regex)
    requires WalkOk(acts, c, pc, g)
    requires |acts| > 0 && acts[0] == LS.Areg(L.Sequence(r1, r2))
    ensures WalkOk([LS.Areg(r1), LS.Areg(r2)] + acts[1..], c, pc, g)
  {
    forall n: nat {:trigger WalkOkF([LS.Areg(r1), LS.Areg(r2)] + acts[1..], c, pc, g, n)} ensures WalkOkF([LS.Areg(r1), LS.Areg(r2)] + acts[1..], c, pc, g, n) {
      assert WalkOkF(acts, c, pc, g, n + 1);
      if |acts| > 0 && acts[0].Areg? {
        assert WalkOkRegF(acts[0].r, acts[1..], c, pc, g, n + 1);
      }
    }
  }

  lemma WalkOkGroup(acts: LS.Actions, c: RB.code, pc: nat, g: bool, gid: LG.GroupId, r1: L.Regex)
    requires WalkOk(acts, c, pc, g)
    requires |acts| > 0 && acts[0] == LS.Areg(L.Group(gid, r1))
    requires NR.GetPcRE(c, pc).Some? && NR.GetPcRE(c, pc).value.SetRegisterToCP?
    ensures WalkOk([LS.Areg(r1), LS.Aclose(gid)] + acts[1..], c, pc + 1, g)
  {
    forall n: nat {:trigger WalkOkF([LS.Areg(r1), LS.Aclose(gid)] + acts[1..], c, pc + 1, g, n)} ensures WalkOkF([LS.Areg(r1), LS.Aclose(gid)] + acts[1..], c, pc + 1, g, n) {
      assert WalkOkF(acts, c, pc, g, n + 1);
      if |acts| > 0 && acts[0].Areg? {
        assert WalkOkRegF(acts[0].r, acts[1..], c, pc, g, n + 1);
      }
    }
  }

  lemma WalkOkAlt(acts: LS.Actions, c: RB.code, pc: nat, g: bool, r1: L.Regex, r2: L.Regex, x: int, y: int)
    requires WalkOk(acts, c, pc, g)
    requires |acts| > 0 && acts[0] == LS.Areg(L.Disjunction(r1, r2))
    requires NR.GetPcRE(c, pc) == Some(RB.Fork(x, y)) && x >= 0 && y >= 0
    ensures WalkOk([LS.Areg(r1)] + acts[1..], c, x as nat, g)
    ensures WalkOk([LS.Areg(r2)] + acts[1..], c, y as nat, g)
  {
    forall n: nat {:trigger WalkOkF([LS.Areg(r1)] + acts[1..], c, x as nat, g, n)}
      ensures WalkOkF([LS.Areg(r1)] + acts[1..], c, x as nat, g, n) {
      assert WalkOkF(acts, c, pc, g, n + 1);
      assert WalkOkRegF(acts[0].r, acts[1..], c, pc, g, n + 1);
    }
    forall n: nat {:trigger WalkOkF([LS.Areg(r2)] + acts[1..], c, y as nat, g, n)}
      ensures WalkOkF([LS.Areg(r2)] + acts[1..], c, y as nat, g, n) {
      assert WalkOkF(acts, c, pc, g, n + 1);
      assert WalkOkRegF(acts[0].r, acts[1..], c, pc, g, n + 1);
    }
  }

  lemma WalkOkQuantForced(acts: LS.Actions, c: RB.code, pc: nat, g: bool,
                          greedy: bool, min: nat, delta: LN.NoI, r1: L.Regex)
    requires WalkOk(acts, c, pc, g)
    requires |acts| > 0 && acts[0] == LS.Areg(L.Quantified(greedy, min, delta, r1))
    requires min > 0 && !(delta.Inf? && min == 1)
    requires NR.GetPcRE(c, pc).Some? && NR.GetPcRE(c, pc).value.SetQuantToClock?
    ensures WalkOk([LS.Areg(r1), LS.Areg(L.Quantified(greedy, min - 1, delta, r1))] + acts[1..], c, pc + 1, g)
  {
    forall n: nat {:trigger WalkOkF([LS.Areg(r1), LS.Areg(L.Quantified(greedy, min - 1, delta, r1))] + acts[1..], c, pc + 1, g, n)} 
      ensures WalkOkF([LS.Areg(r1), LS.Areg(L.Quantified(greedy, min - 1, delta, r1))] + acts[1..], c, pc + 1, g, n) {
      assert WalkOkF(acts, c, pc, g, n + 1);
      if |acts| > 0 && acts[0].Areg? {
        assert WalkOkRegF(acts[0].r, acts[1..], c, pc, g, n + 1);
      }
    }
  }

  lemma WalkOkQuantSeam(acts: LS.Actions, c: RB.code, pc: nat, g: bool,
                        greedy: bool, r1: L.Regex, chk: LC.Input)
    requires WalkOk(acts, c, pc, g)
    requires |acts| > 0 && acts[0] == LS.Areg(L.Quantified(greedy, 1, LN.Inf, r1))
    requires NR.GetPcRE(c, pc).Some? && NR.GetPcRE(c, pc).value.SetQuantToClock?
    ensures WalkOk([LS.Areg(r1), LS.Acheck(chk), LS.Areg(L.Quantified(greedy, 0, LN.Inf, r1))] + acts[1..],
                   c, pc + 1, g)
  {
    forall n: nat {:trigger WalkOkF([LS.Areg(r1), LS.Acheck(chk), LS.Areg(L.Quantified(greedy, 0, LN.Inf, r1))] + acts[1..], c, pc + 1, g, n)}
      ensures WalkOkF([LS.Areg(r1), LS.Acheck(chk), LS.Areg(L.Quantified(greedy, 0, LN.Inf, r1))] + acts[1..],
                      c, pc + 1, g, n) {
      assert WalkOkF(acts, c, pc, g, n + 1);
      if |acts| > 0 && acts[0].Areg? {
        assert WalkOkRegF(acts[0].r, acts[1..], c, pc, g, n + 1);
      }
    }
  }

  lemma WalkOkQuantSpent(acts: LS.Actions, c: RB.code, pc: nat, g: bool,
                         greedy: bool, r1: L.Regex)
    requires WalkOk(acts, c, pc, g)
    requires |acts| > 0 && acts[0] == LS.Areg(L.Quantified(greedy, 0, LN.NN(0), r1))
    ensures WalkOk(acts[1..], c, pc, g)
  {
    forall n: nat {:trigger WalkOkF(acts[1..], c, pc, g, n)} ensures WalkOkF(acts[1..], c, pc, g, n) {
      assert WalkOkF(acts, c, pc, g, n + 1);
      if |acts| > 0 && acts[0].Areg? {
        assert WalkOkRegF(acts[0].r, acts[1..], c, pc, g, n + 1);
      }
    }
  }

  lemma WalkOkQuantLayer(acts: LS.Actions, c: RB.code, pc: nat, g: bool,
                         greedy: bool, delta: LN.NoI, r1: L.Regex, x: int, y: int, chk: LC.Input)
    requires WalkOk(acts, c, pc, g)
    requires |acts| > 0 && acts[0] == LS.Areg(L.Quantified(greedy, 0, delta, r1))
    requires delta != LN.NN(0)
    requires NR.GetPcRE(c, pc) == Some(RB.Fork(x, y)) && x >= 0 && y >= 0
    requires (if greedy then x else y) as nat > pc
    ensures var iterarm := (if greedy then x else y) as nat;
            var skiparm := (if greedy then y else x) as nat;
            var qnext := L.Quantified(greedy, 0, FS.NoiPred(delta), r1);
            WalkOk([LS.Areg(r1), LS.Acheck(chk), LS.Areg(qnext)] + acts[1..], c, iterarm + 2, false)
            && WalkOk(acts[1..], c, skiparm, g)
  {
    var iterarm := (if greedy then x else y) as nat;
    var skiparm := (if greedy then y else x) as nat;
    var qnext := L.Quantified(greedy, 0, FS.NoiPred(delta), r1);
    forall n: nat {:trigger WalkOkF([LS.Areg(r1), LS.Acheck(chk), LS.Areg(qnext)] + acts[1..], c, iterarm + 2, false, n)} 
      ensures WalkOkF([LS.Areg(r1), LS.Acheck(chk), LS.Areg(qnext)] + acts[1..], c, iterarm + 2, false, n) {
      assert WalkOkF(acts, c, pc, g, n + 1);
      assert WalkOkRegF(acts[0].r, acts[1..], c, pc, g, n + 1);
    }
    forall n: nat {:trigger WalkOkF(acts[1..], c, skiparm, g, n)} 
      ensures WalkOkF(acts[1..], c, skiparm, g, n) {
      assert WalkOkF(acts, c, pc, g, n + 1);
      assert WalkOkRegF(acts[0].r, acts[1..], c, pc, g, n + 1);
    }
    assert WalkOk([LS.Areg(r1), LS.Acheck(chk), LS.Areg(qnext)] + acts[1..], c, iterarm + 2, false);
    assert WalkOk(acts[1..], c, skiparm, g);
  }

  lemma WalkOkLoopView(acts: LS.Actions, c: RB.code, pc: nat, g: bool,
                       greedy: bool, delta: LN.NoI, r1: L.Regex, x: int, y: int, chk: LC.Input)
    requires WalkOk(acts, c, pc, g)
    requires |acts| > 0 && acts[0] == LS.Areg(L.Quantified(greedy, 0, delta, r1))
    requires delta != LN.NN(0)
    requires NR.GetPcRE(c, pc) == Some(RB.Fork(x, y)) && x >= 0 && y >= 0
    requires (if greedy then x else y) as nat <= pc
    ensures g == true
    ensures var iterarm := (if greedy then x else y) as nat;
            var skiparm := (if greedy then y else x) as nat;
            var qnext := L.Quantified(greedy, 0, FS.NoiPred(delta), r1);
            WalkOk([LS.Areg(r1), LS.Acheck(chk), LS.Areg(qnext)] + acts[1..], c, iterarm + 1, true)
            && WalkOk(acts[1..], c, skiparm, true)
  {
    assert WalkOkF(acts, c, pc, g, 1);
    assert WalkOkRegF(acts[0].r, acts[1..], c, pc, g, 1);
    var iterarm := (if greedy then x else y) as nat;
    var skiparm := (if greedy then y else x) as nat;
    var qnext := L.Quantified(greedy, 0, FS.NoiPred(delta), r1);
    forall n: nat {:trigger WalkOkF([LS.Areg(r1), LS.Acheck(chk), LS.Areg(qnext)] + acts[1..], c, iterarm + 1, true, n)} 
      ensures WalkOkF([LS.Areg(r1), LS.Acheck(chk), LS.Areg(qnext)] + acts[1..], c, iterarm + 1, true, n) {
      assert WalkOkF(acts, c, pc, g, n + 1);
      assert WalkOkRegF(acts[0].r, acts[1..], c, pc, g, n + 1);
    }
    forall n: nat {:trigger WalkOkF(acts[1..], c, skiparm, true, n)} 
      ensures WalkOkF(acts[1..], c, skiparm, true, n) {
      assert WalkOkF(acts, c, pc, g, n + 1);
      assert WalkOkRegF(acts[0].r, acts[1..], c, pc, g, n + 1);
    }
    assert WalkOk([LS.Areg(r1), LS.Acheck(chk), LS.Areg(qnext)] + acts[1..], c, iterarm + 1, true);
    assert WalkOk(acts[1..], c, skiparm, true);
  }
}
