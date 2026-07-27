// The PINNACLE assembly: MatcherSpec(raw, str, Normalize(FFullMatch(raw, str)))
// for StarFragmentRaw && Latin1Wf. Builds on FindMatchSimRE (the complete
// simulation) plus Linden's own PikeTree correctness tail; the remaining
// bricks are pipeline plumbing and the leaf-closedness extraction.
include "PikeSimRE.dfy"
include "WalkOkEntry.dfy"
include "LookCapture.dfy"
include "OracleEntry.dfy"

/** The top-level equivalence theorem: `MainTheorem` proves RegElk's compiled,
    executable engine (`FFullMatch`) agrees with the Linden/Warblre tree
    semantics (`MatcherSpec`) on the star fragment. Everything else in this
    module is either a small bridging fact or a piece of the final extraction
    (`MainExtraction`) that reads the engine's answer off the winning thread. */
module LindenElkMain {
  import opened Std.Wrappers
  import R = RegElkRegex
  import RB = Bytecode
  import CP = Compiler
  import NR = LindenElkNfaRep
  import AI = ArrayInterp
  import AReg = Array_Regs
  import LG = Groups
  import LT = Tree
  import LC = Chars
  import PT = PikeTree
  import CR = Correctness
  import PIV = LindenElkPikeInv
  import PSM = LindenElkPikeSim
  import LOr = Oracle
  import LAnc = Anchors
  import LCdn = Cdn
  import RC = Charclasses
  import AR = LindenElkActionsRep
  import EL = LindenElkEntryLk
  import RL = LindenElkRegsLaws
  import LKC = LindenElkLookCapture
  import LTB = LindenElkLookTables
  import SD = LindenSpanDuality
  import LL = LindenElkLookLeaves
  import OE = LindenElkOracleEntry
  import T = LindenElkTranslate
  import CM = LindenElkClockMono
  import NI = LindenElkNestInv
  import LES = LindenElkSpec
  import LFU = FunctionalUtils
  import PS = PikeSubset
  import ATR = LindenElkActionsTreeRep
  import LW = WarblreRegExpRecord
  import LS = Semantics
  import BS = BooleanSemantics
  import L = Regex
  import WP = WarblrePrimitives
  import LN = WarblreNumeric
  import LFS = FunctionalSemantics
  import TR = LindenElkTreeRep
  import CE = LindenElkCheckErase
  import WO = LindenElkWalkOk
  import WOE = LindenElkWalkOkEntry

  // ==========================================================================
  // Bridge: our local closure IS Linden's (identical definitions over the
  // same step relation).
  // ==========================================================================
  /** Bridges the two "many VM steps" closures: RegElk's local `PSM.TrcRE`
      transitive closure agrees with Linden's own `CR.TrcPikeTree`, since both
      close the same `PikeTreeStep` relation. */
  least lemma TrcREToLinden(x: PT.PikeTreeState, y: PT.PikeTreeState)
    requires PSM.TrcRE(x, y)
    ensures CR.TrcPikeTree(x, y)
  {
    if x == y {
    } else {
      var z :| PT.PikeTreeStep(x, z) && PSM.TrcRE(z, y);
      TrcREToLinden(z, y);
    }
  }

  // ==========================================================================
  // The lazy prefix is filter-transparent: its quant (id 0) is always in the
  // present branch (a stored clock is >= -1 == the top threshold) and its
  // body (Dot) contains no captures.
  // ==========================================================================
  /** The synthetic lazy-star prefix `R.lazy_prefix` that wraps every compiled
      fragment is filter-transparent: since its body is capture-free and its
      quant clock is always "in the present branch", `filter_reset` sees
      straight through it to the underlying `ast`. */
  lemma FilterResetLazyPrefix(ast: R.regex, caps: AReg.Regs, look: AReg.Regs, quant: AReg.Regs)
    requires AI.get_idx(AReg.as_arrays(quant).1, 0) >= -1   // quant 0's stored clock (init -1, stamps >= 0)
    ensures AI.filter_reset(R.lazy_prefix(ast), caps, look, quant, -1)
         == AI.filter_reset(ast, caps, look, quant, -1)
  {
    var (cr, cc) := AReg.as_arrays(caps);
    var (_, lc) := AReg.as_arrays(look);
    var (_, qc) := AReg.as_arrays(quant);
    var pre := R.Re_quant(R.NonNullable, 0, R.CountedQuant(0, None, false), R.Re_character(R.Dot));
    assert R.lazy_prefix(ast) == R.Re_con(pre, ast);
    var qv := AI.get_idx(qc, 0);
    assert qv >= -1;
    // present branch: filter_capture(Dot-body, ..., qv) == cap_regs (no captures).
    assert AI.filter_capture(pre, cr, cc, lc, qc, -1)
        == AI.filter_capture(R.Re_character(R.Dot), cr, cc, lc, qc, qv);
    assert AI.filter_capture(R.Re_character(R.Dot), cr, cc, lc, qc, qv) == cr;
  }

  // ==========================================================================
  // Quant-register finality: in fragment code every SetQuantToClock has
  // bq == false, so quant VALUES stay negative (get_cp None -- makes
  // FNulledPlus/FReconstructPlus the identity) and quant CLOCKS stay >= -1
  // (init -1, stamps are nonnegative clock values -- discharges
  // FilterResetLazyPrefix's hypothesis).
  // ==========================================================================
  /** A single thread's quant registers are in their terminal shape for
      fragment code: every quant slot's stored capture-point is unset
      (negative) and every quant clock is at least the initial `-1`. */
  ghost predicate QuantRegsFinal(t: AI.Thread) {
    (forall k :: AI.get_idx(t.quant_regs.a_cp, k) < 0)
    && (forall k :: AI.get_idx(t.quant_regs.a_clk, k) >= -1)
  }

  /** `QuantRegsFinal` lifted to a whole VM state: holds of every active
      thread, every blocked thread, and `bestmatch` if present. */
  ghost predicate VmQuantFinal(s: AI.VmState) {
    (forall t | t in s.active :: QuantRegsFinal(t))
    && (forall tb | tb in s.blocked :: QuantRegsFinal(tb.0))
    && (s.bestmatch.Some? ==> QuantRegsFinal(s.bestmatch.value))
  }

  /** `SetQuantToClock` (with `bq == false`, the only case fragment code
      emits) preserves `QuantRegsFinal` on the written thread. */
  lemma QuantRegsFinalSet(t: AI.Thread, q: int, clk: int)
    requires QuantRegsFinal(t)
    requires clk >= -1
    ensures QuantRegsFinal(t.(quant_regs := AReg.set_reg(t.quant_regs, q, None, clk)))
  {
    var r := t.quant_regs;
    var r2 := AReg.set_reg(r, q, None, clk);
    if 0 <= q < |r.a_cp| && 0 <= q < |r.a_clk| {
      assert r2.a_cp == r.a_cp[q := -1] && r2.a_clk == r.a_clk[q := clk];
      forall k ensures AI.get_idx(r2.a_cp, k) < 0 {
        if 0 <= k < |r.a_cp| && k != q {
          assert r2.a_cp[k] == r.a_cp[k];
          assert AI.get_idx(r.a_cp, k) == r.a_cp[k];
        }
      }
      forall k ensures AI.get_idx(r2.a_clk, k) >= -1 {
        if 0 <= k < |r.a_clk| && k != q {
          assert r2.a_clk[k] == r.a_clk[k];
          assert AI.get_idx(r.a_clk, k) == r.a_clk[k];
        }
      }
    } else {
      assert r2 == r;
    }
  }

  /** `FAdvanceEpsilon` preserves `VmQuantFinal`, given that fragment code's
      every `SetQuantToClock` has its `bq` flag `false`. Structural induction
      over the epsilon-closure fuel, one case per bytecode instruction. */
  lemma FAdvanceEpsilonQuantFinal(
      c: RB.code, s: AI.VmState, ov: LOr.OracleView, dir: LAnc.direction)
    requires |s.processed.true_set| == RB.size(c) && |s.processed.false_set| == RB.size(c)
    requires forall pc: nat, q: int, b: bool ::
      NR.GetPcRE(c, pc) == Some(RB.SetQuantToClock(q, b)) ==> !b
    requires s.clock >= -1
    requires VmQuantFinal(s)
    ensures VmQuantFinal(AI.FAdvanceEpsilon(c, s, ov, dir).0)
    decreases AI.unprocessed(s.processed), |s.active|
  {
    if |s.active| == 0 { return; }
    var t := s.active[0];
    var ac := s.active[1..];
    assert t in s.active;
    assert forall x | x in ac :: x in s.active;
    if AI.bpc_mem(s.processed, t.pc, t.exit_allowed) {
      FAdvanceEpsilonQuantFinal(c, s.(active := ac), ov, dir);
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
        var s2 := s1.(blocked := nb, isblocked := ni, active := ac);
        assert VmQuantFinal(s2) by {
          forall tb | tb in s2.blocked ensures QuantRegsFinal(tb.0) {
            assert tb == (t, ce) || tb in s.blocked;
          }
        }
        FAdvanceEpsilonQuantFinal(c, s2, ov, dir);
      case Accept =>
        assert QuantRegsFinal(t);
      case Jmp(x) =>
        var s2 := s1.(active := [t.(pc := x)] + ac);
        assert VmQuantFinal(s2) by {
          forall t2 | t2 in s2.active ensures QuantRegsFinal(t2) {
            if t2 != t.(pc := x) { assert t2 in s.active; }
          }
        }
        FAdvanceEpsilonQuantFinal(c, s2, ov, dir);
      case Fork(x, y) =>
        var newt := AI.Thread(x, t.capture_regs, t.look_regs, t.quant_regs, t.exit_allowed);
        var s2 := s1.(active := [newt, t.(pc := y)] + ac);
        assert VmQuantFinal(s2) by {
          forall t2 | t2 in s2.active ensures QuantRegsFinal(t2) {
            if t2 != newt && t2 != t.(pc := y) { assert t2 in s.active; }
          }
        }
        FAdvanceEpsilonQuantFinal(c, s2, ov, dir);
      case SetRegisterToCP(reg) =>
        var t2h := t.(capture_regs := AReg.set_reg(t.capture_regs, reg, Some(s1.cp), s1.clock), pc := t.pc + 1);
        var s2 := s1.(active := [t2h] + ac);
        assert VmQuantFinal(s2) by {
          forall t2 | t2 in s2.active ensures QuantRegsFinal(t2) {
            if t2 != t2h { assert t2 in s.active; }
          }
        }
        FAdvanceEpsilonQuantFinal(c, s2, ov, dir);
      case SetQuantToClock(q, bq) =>
        assert 0 <= t.pc < |c|;
        assert NR.GetPcRE(c, t.pc as nat) == Some(RB.SetQuantToClock(q, bq));
        assert !bq;
        var ocp := if bq then Some(s1.cp) else None;
        assert ocp == None;
        var t2h := t.(quant_regs := AReg.set_reg(t.quant_regs, q, ocp, s1.clock), pc := t.pc + 1);
        QuantRegsFinalSet(t, q, s1.clock);
        var s2 := s1.(active := [t2h] + ac);
        assert VmQuantFinal(s2) by {
          forall t2 | t2 in s2.active ensures QuantRegsFinal(t2) {
            if t2 != t2h { assert t2 in s.active; }
          }
        }
        FAdvanceEpsilonQuantFinal(c, s2, ov, dir);
      case CheckOracle(l) =>
        if LOr.view_get_oracle(ov, s1.cp, l) {
          var t2h := t.(pc := t.pc + 1, look_regs := AReg.set_reg(t.look_regs, l, Some(s1.cp), s1.clock));
          var s2 := s1.(active := [t2h] + ac);
          assert VmQuantFinal(s2) by {
            forall t2 | t2 in s2.active ensures QuantRegsFinal(t2) {
              if t2 != t2h { assert t2 in s.active; }
            }
          }
          FAdvanceEpsilonQuantFinal(c, s2, ov, dir);
        } else {
          FAdvanceEpsilonQuantFinal(c, s1.(active := ac), ov, dir);
        }
      case NegCheckOracle(l) =>
        if LOr.view_get_oracle(ov, s1.cp, l) {
          FAdvanceEpsilonQuantFinal(c, s1.(active := ac), ov, dir);
        } else {
          var s2 := s1.(active := [t.(pc := t.pc + 1)] + ac);
          assert VmQuantFinal(s2) by {
            forall t2 | t2 in s2.active ensures QuantRegsFinal(t2) {
              if t2 != t.(pc := t.pc + 1) { assert t2 in s.active; }
            }
          }
          FAdvanceEpsilonQuantFinal(c, s2, ov, dir);
        }
      case WriteOracle(l) =>
        FAdvanceEpsilonQuantFinal(c, s1.(active := ac), LOr.view_set_oracle(ov, s1.cp, l), dir);
      case BeginLoop =>
        var s2 := s1.(active := [t.(exit_allowed := false, pc := t.pc + 1)] + ac);
        assert VmQuantFinal(s2) by {
          forall t2 | t2 in s2.active ensures QuantRegsFinal(t2) {
            if t2 != t.(exit_allowed := false, pc := t.pc + 1) { assert t2 in s.active; }
          }
        }
        FAdvanceEpsilonQuantFinal(c, s2, ov, dir);
      case EndLoop =>
        if t.exit_allowed {
          var s2 := s1.(active := [t.(pc := t.pc + 1)] + ac);
          assert VmQuantFinal(s2) by {
            forall t2 | t2 in s2.active ensures QuantRegsFinal(t2) {
              if t2 != t.(pc := t.pc + 1) { assert t2 in s.active; }
            }
          }
          FAdvanceEpsilonQuantFinal(c, s2, ov, dir);
        } else {
          FAdvanceEpsilonQuantFinal(c, s1.(active := ac), ov, dir);
        }
      case CheckNullable(qid) =>
        if LCdn.cdn_get(s1.cdn, qid) {
          var s2 := s1.(active := [t.(pc := t.pc + 1)] + ac);
          assert VmQuantFinal(s2) by {
            forall t2 | t2 in s2.active ensures QuantRegsFinal(t2) {
              if t2 != t.(pc := t.pc + 1) { assert t2 in s.active; }
            }
          }
          FAdvanceEpsilonQuantFinal(c, s2, ov, dir);
        } else {
          FAdvanceEpsilonQuantFinal(c, s1.(active := ac), ov, dir);
        }
      case AnchorAssertion(a) =>
        if LAnc.is_satisfied(a, s1.context, dir) {
          var s2 := s1.(active := [t.(pc := t.pc + 1)] + ac);
          assert VmQuantFinal(s2) by {
            forall t2 | t2 in s2.active ensures QuantRegsFinal(t2) {
              if t2 != t.(pc := t.pc + 1) { assert t2 in s.active; }
            }
          }
          FAdvanceEpsilonQuantFinal(c, s2, ov, dir);
        } else {
          FAdvanceEpsilonQuantFinal(c, s1.(active := ac), ov, dir);
        }
      case Fail =>
        FAdvanceEpsilonQuantFinal(c, s1.(active := ac), ov, dir);
    }
  }

  // With every quant VALUE negative, FNulledPlus (hence FReconstructPlus) is
  // the identity: the Some(start_cp) branch is unreachable.
  /** With every quant value negative (`VmQuantFinal`), `AI.FNulledPlus` (hence
      `FReconstructPlus`) is the identity: the "restore the started capture"
      branch is never taken because no quant was ever entered with a stamped
      start. */
  lemma FNulledPlusIdentity(reg: R.regex, cap: AReg.Regs, lk: AReg.Regs, qt: AReg.Regs,
                            plus_bcv: seq<RB.code>, str: string, ov: LOr.OracleView,
                            dir: LAnc.direction)
    requires forall k :: AI.get_idx(qt.a_cp, k) < 0
    ensures AI.FNulledPlus(reg, cap, lk, qt, plus_bcv, str, ov, dir) == (cap, lk, qt, ov)
    decreases reg
  {
    match reg
    case Re_empty => case Re_character(_) => case Re_anchor(_) => case Re_lookaround(_, _, _) =>
    case Re_capture(_, r1) =>
      FNulledPlusIdentity(r1, cap, lk, qt, plus_bcv, str, ov, dir);
    case Re_alt(r1, r2) =>
      FNulledPlusIdentity(r1, cap, lk, qt, plus_bcv, str, ov, dir);
      FNulledPlusIdentity(r2, cap, lk, qt, plus_bcv, str, ov, dir);
    case Re_con(r1, r2) =>
      FNulledPlusIdentity(r1, cap, lk, qt, plus_bcv, str, ov, dir);
      FNulledPlusIdentity(r2, cap, lk, qt, plus_bcv, str, ov, dir);
    case Re_quant(nul, qid, quanttype, body) =>
      assert AReg.get_cp(qt, qid).None? by {
        if 0 <= qid < |qt.a_cp| {
          assert AI.get_idx(qt.a_cp, qid) == qt.a_cp[qid];
          assert qt.a_cp[qid] < 0;
        }
      }
      FNulledPlusIdentity(body, cap, lk, qt, plus_bcv, str, ov, dir);
  }

  // ==========================================================================
  // Top-level loop-flag irrelevance: with no Acheck anywhere in the action
  // list, the initial LoopBool is never consulted -- every Acheck the
  // semantics pushes comes with an explicit CannotExit reset, and Character
  // reads reset to CanExit. Bridges BooleanCorrect's CanExit tree to the
  // CannotExit form InitialPikeInvFullRE seeds (RegElk's ea == false).
  // ==========================================================================
  /** When an action stack contains no `Acheck`, `BooleanSemantics.BoolTree`'s
      initial loop-flag is irrelevant to the resulting tree — bridges the
      `CanExit`-seeded tree `BooleanCorrect` produces to the `CannotExit` form
      `InitialPikeInvFullRE` expects (RegElk always starts a match attempt
      with `exit_allowed == false`). */
  least lemma BoolTreeLbIrrel(rer: LW.RegExpRecord, acts: LS.Actions, inp: LC.Input,
                              b1: BS.LoopBool, b2: BS.LoopBool, t: LT.Tree)
    requires EL.BoolTreeLk(rer, acts, inp, b1, t)
    requires forall i :: 0 <= i < |acts| ==> !acts[i].Acheck?
    ensures EL.BoolTreeLk(rer, acts, inp, b2, t)
  {
    if |acts| == 0 {
      assert t == LT.Match;
    } else {
      var cont := acts[1..];
      assert forall i :: 0 <= i < |cont| ==> !cont[i].Acheck?;
      match acts[0]
      case Acheck(strcheck) =>
        assert false;
      case Aclose(gid) =>
        BoolTreeLbIrrel(rer, cont, inp, b1, b2, t.t);
      case Areg(r) =>
        match r
        case Epsilon =>
          BoolTreeLbIrrel(rer, cont, inp, b1, b2, t);
        case Character(cd) =>
          // both sides reset to CanExit: the continuation fact is shared.
          if LC.ReadChar(rer, cd, inp, WP.Forward).None? {
            assert t == LT.Mismatch;
          } else {
            var pair := LC.ReadChar(rer, cd, inp, WP.Forward).value;
            assert t.Read? && t.c == pair.0;
            assert EL.BoolTreeLk(rer, cont, pair.1, BS.CanExit, t.t);
          }
        case Disjunction(r1, r2) =>
          assert t.Choice?;
          assert forall i :: 0 <= i < |[LS.Areg(r1)] + cont| ==> !([LS.Areg(r1)] + cont)[i].Acheck?;
          assert forall i :: 0 <= i < |[LS.Areg(r2)] + cont| ==> !([LS.Areg(r2)] + cont)[i].Acheck?;
          BoolTreeLbIrrel(rer, [LS.Areg(r1)] + cont, inp, b1, b2, t.t1);
          BoolTreeLbIrrel(rer, [LS.Areg(r2)] + cont, inp, b1, b2, t.t2);
        case Sequence(r1, r2) =>
          assert forall i :: (0 <= i < |[LS.Areg(r1), LS.Areg(r2)] + cont|
            ==> !([LS.Areg(r1), LS.Areg(r2)] + cont)[i].Acheck?);
          BoolTreeLbIrrel(rer, [LS.Areg(r1), LS.Areg(r2)] + cont, inp, b1, b2, t);
        case Quantified(greedy, min, delta, r1) =>
          var gidl := L.DefGroups(r1);
          if min > 0 {
            assert t.GroupActionT?;
            var acts1 := [LS.Areg(r1), LS.Areg(L.Quantified(greedy, min - 1, delta, r1))] + cont;
            assert forall i :: 0 <= i < |acts1| ==> !acts1[i].Acheck?;
            BoolTreeLbIrrel(rer, acts1, inp, b1, b2, t.t);
          } else if delta == LN.NN(0) {
            BoolTreeLbIrrel(rer, cont, inp, b1, b2, t);
          } else {
            assert t.Choice?;
            var itert := if greedy then t.t1 else t.t2;
            var skipt := if greedy then t.t2 else t.t1;
            assert itert.GroupActionT?;
            // the iteration branch is at an explicit CannotExit: shared fact.
            assert EL.BoolTreeLk(rer, [LS.Areg(r1), LS.Acheck(inp), LS.Areg(L.Quantified(greedy, 0, LFS.NoiPred(delta), r1))] + cont,
                               inp, BS.CannotExit, itert.t);
            // the skip branch threads the flag: induct.
            BoolTreeLbIrrel(rer, cont, inp, b1, b2, skipt);
          }
        case Group(gid, r1) =>
          assert t.GroupActionT?;
          var acts1 := [LS.Areg(r1), LS.Aclose(gid)] + cont;
          assert forall i :: 0 <= i < |acts1| ==> !acts1[i].Acheck?;
          BoolTreeLbIrrel(rer, acts1, inp, b1, b2, t.t);
        case AnchorR(a) =>
          if LS.AnchorSatisfied(rer, a, inp) {
            assert t.AnchorPass?;
            BoolTreeLbIrrel(rer, cont, inp, b1, b2, t.t);
          } else {
            assert t == LT.Mismatch;
          }
        case LookaroundR(lk, r1) =>
          // the gate does not read the loop flag; recurse under it
          match t {
            case LK(lk2, tlk, tc) => BoolTreeLbIrrel(rer, cont, inp, b1, b2, tc);
            case _ =>
          }
        case Backreference(_) =>
          assert false;
    }
  }

  // ==========================================================================
  // Leaf gms are CLOSED: the open groups of the threaded gm are always
  // covered by the pending Aclose actions, and a Match leaf requires the
  // action list exhausted. This single fact delivers, pointwise, both
  // GmOfLiveEqGmOf's and GmOfCapArrayBridge's hypotheses at the final thread.
  // ==========================================================================
  /** The set of group ids that are open (started but not yet closed) in `gm`. */
  ghost function OpenOf(gm: LG.GroupMap): set<LG.GroupId> {
    set g | g in gm && gm[g].endIdx.None?
  }

  /** The set of group ids that some pending `Aclose` action in `acts` will
      still close. */
  ghost function PendingCloses(acts: LS.Actions): set<LG.GroupId> {
    set i | 0 <= i < |acts| && acts[i].Aclose? :: acts[i].gid
  }

  /** Every group recorded in `gm` has been closed — no group is left open. */
  ghost predicate ClosedGm(gm: LG.GroupMap) {
    forall g :: g in gm ==> gm[g].endIdx.Some?
  }

  /** The `GroupMap` of a `Match` leaf is always fully closed: whenever a
      tree's open groups are all covered by pending `Aclose` actions, its
      highest-priority leaf (`TreeRes`) leaves no group open. Grounds both
      `GmOfLiveEqGmOf`'s and `GmOfCapArrayBridge`'s hypotheses at the winning
      thread. */
  least lemma FirstLeafClosed(rer: LW.RegExpRecord, acts: LS.Actions, inp: LC.Input,
                              b: BS.LoopBool, t: LT.Tree, gm: LG.GroupMap, leaf: LT.Leaf)
    requires EL.BoolTreeLk(rer, acts, inp, b, t)
    requires EL.PikeLkActions(acts)
    requires OpenOf(gm) <= PendingCloses(acts)
    requires LT.TreeRes(t, gm, inp, WP.Forward) == Some(leaf)
    ensures ClosedGm(leaf.1)
  {
    if |acts| == 0 {
      assert t == LT.Match;
      assert leaf.1 == gm;
      assert PendingCloses(acts) == {};
      forall g | g in gm ensures gm[g].endIdx.Some? {
        if gm[g].endIdx.None? { assert g in OpenOf(gm); }
      }
    } else {
      var cont := acts[1..];
      assert forall i :: 0 <= i < |cont| ==> cont[i] == acts[i + 1];
      assert PendingCloses(cont) <= PendingCloses(acts);
      match acts[0]
      case Acheck(strcheck) =>
        if b == BS.CanExit {
          assert t.Progress?;
          assert PendingCloses(acts) == PendingCloses(cont);
          FirstLeafClosed(rer, cont, inp, BS.CanExit, t.t, gm, leaf);
        } else {
          assert t == LT.Mismatch;
          assert false;
        }
      case Aclose(gid) =>
        assert t.GroupActionT? && t.g == LG.Close(gid);
        var gm2 := LG.GMUpdate(t.g, LC.Idx(inp), gm);
        assert gm2 == LG.GMClose(LC.Idx(inp), gid, gm);
        assert OpenOf(gm2) <= PendingCloses(cont) by {
          forall g | g in OpenOf(gm2) ensures g in PendingCloses(cont) {
            assert g != gid;
            assert g in OpenOf(gm);
            assert g in PendingCloses(acts);
            var i :| 0 <= i < |acts| && acts[i].Aclose? && acts[i].gid == g;
            assert i != 0;
            assert cont[i - 1] == acts[i];
          }
        }
        FirstLeafClosed(rer, cont, inp, b, t.t, gm2, leaf);
      case Areg(r) =>
        match r
        case Epsilon =>
          assert PendingCloses(acts) == PendingCloses(cont);
          FirstLeafClosed(rer, cont, inp, b, t, gm, leaf);
        case Character(cd) =>
          if LC.ReadChar(rer, cd, inp, WP.Forward).None? {
            assert t == LT.Mismatch;
            assert false;
          } else {
            var pair := LC.ReadChar(rer, cd, inp, WP.Forward).value;
            assert t.Read?;
            assert pair.1 == LC.AdvanceInputP(inp, WP.Forward);
            assert PendingCloses(acts) == PendingCloses(cont);
            FirstLeafClosed(rer, cont, pair.1, BS.CanExit, t.t, gm, leaf);
          }
        case Disjunction(r1, r2) =>
          assert t.Choice?;
          var acts1 := [LS.Areg(r1)] + cont;
          var acts2 := [LS.Areg(r2)] + cont;
          assert PendingCloses(acts1) == PendingCloses(cont) == PendingCloses(acts2) by {
            assert forall i :: 0 <= i < |cont| ==> acts1[i + 1] == cont[i] && acts2[i + 1] == cont[i];
          }
          assert PendingCloses(acts) == PendingCloses(cont);
          if LT.TreeRes(t.t1, gm, inp, WP.Forward).Some? {
            FirstLeafClosed(rer, acts1, inp, b, t.t1, gm, leaf);
          } else {
            FirstLeafClosed(rer, acts2, inp, b, t.t2, gm, leaf);
          }
        case Sequence(r1, r2) =>
          var acts1 := [LS.Areg(r1), LS.Areg(r2)] + cont;
          assert PendingCloses(acts1) == PendingCloses(cont) by {
            assert forall i :: 0 <= i < |cont| ==> acts1[i + 2] == cont[i];
          }
          assert PendingCloses(acts) == PendingCloses(cont);
          FirstLeafClosed(rer, acts1, inp, b, t, gm, leaf);
        case Quantified(greedy, min, delta, r1) =>
          var gidl := L.DefGroups(r1);
          if min > 0 {
            assert t.GroupActionT? && t.g == LG.Reset(gidl);
            var gm2 := LG.GMUpdate(t.g, LC.Idx(inp), gm);
            assert gm2 == LG.GMReset(gidl, gm);
            assert OpenOf(gm2) <= OpenOf(gm);
            var acts1 := [LS.Areg(r1), LS.Areg(L.Quantified(greedy, min - 1, delta, r1))] + cont;
            assert PendingCloses(acts1) == PendingCloses(cont) by {
              assert forall i :: 0 <= i < |cont| ==> acts1[i + 2] == cont[i];
            }
            assert PendingCloses(acts) == PendingCloses(cont);
            FirstLeafClosed(rer, acts1, inp, b, t.t, gm2, leaf);
          } else if delta == LN.NN(0) {
            assert PendingCloses(acts) == PendingCloses(cont);
            FirstLeafClosed(rer, cont, inp, b, t, gm, leaf);
          } else {
            assert t.Choice?;
            var itert := if greedy then t.t1 else t.t2;
            var skipt := if greedy then t.t2 else t.t1;
            assert itert.GroupActionT? && itert.g == LG.Reset(gidl);
            assert PendingCloses(acts) == PendingCloses(cont);
            // Seqop picks t.t1 first: split on which branch the leaf came from.
            if LT.TreeRes(t.t1, gm, inp, WP.Forward).Some? {
              if greedy {
                var gm2 := LG.GMUpdate(itert.g, LC.Idx(inp), gm);
                assert gm2 == LG.GMReset(gidl, gm);
                assert OpenOf(gm2) <= OpenOf(gm);
                var acts1 := [LS.Areg(r1), LS.Acheck(inp), LS.Areg(L.Quantified(greedy, 0, LFS.NoiPred(delta), r1))] + cont;
                assert PendingCloses(acts1) == PendingCloses(cont) by {
                  assert forall i :: 0 <= i < |cont| ==> acts1[i + 3] == cont[i];
                }
                FirstLeafClosed(rer, acts1, inp, BS.CannotExit, itert.t, gm2, leaf);
              } else {
                FirstLeafClosed(rer, cont, inp, b, skipt, gm, leaf);
              }
            } else {
              if greedy {
                FirstLeafClosed(rer, cont, inp, b, skipt, gm, leaf);
              } else {
                var gm2 := LG.GMUpdate(itert.g, LC.Idx(inp), gm);
                assert gm2 == LG.GMReset(gidl, gm);
                assert OpenOf(gm2) <= OpenOf(gm);
                var acts1 := [LS.Areg(r1), LS.Acheck(inp), LS.Areg(L.Quantified(greedy, 0, LFS.NoiPred(delta), r1))] + cont;
                assert PendingCloses(acts1) == PendingCloses(cont) by {
                  assert forall i :: 0 <= i < |cont| ==> acts1[i + 3] == cont[i];
                }
                FirstLeafClosed(rer, acts1, inp, BS.CannotExit, itert.t, gm2, leaf);
              }
            }
          }
        case Group(gid, r1) =>
          assert t.GroupActionT? && t.g == LG.Open(gid);
          var gm2 := LG.GMUpdate(t.g, LC.Idx(inp), gm);
          assert gm2 == LG.GMOpen(LC.Idx(inp), gid, gm);
          var acts1 := [LS.Areg(r1), LS.Aclose(gid)] + cont;
          assert gid in PendingCloses(acts1) by { assert acts1[1].Aclose? && acts1[1].gid == gid; }
          assert OpenOf(gm2) <= PendingCloses(acts1) by {
            forall g | g in OpenOf(gm2) ensures g in PendingCloses(acts1) {
              if g != gid {
                assert g in OpenOf(gm);
                assert g in PendingCloses(acts);
                var i :| 0 <= i < |acts| && acts[i].Aclose? && acts[i].gid == g;
                assert i != 0;
                assert acts1[i + 1] == cont[i - 1] == acts[i];
              }
            }
          }
          FirstLeafClosed(rer, acts1, inp, b, t.t, gm2, leaf);
        case AnchorR(a) =>
          if LS.AnchorSatisfied(rer, a, inp) {
            assert t.AnchorPass?;
            assert PendingCloses(acts) == PendingCloses(cont);
            FirstLeafClosed(rer, cont, inp, b, t.t, gm, leaf);
          } else {
            assert t == LT.Mismatch;
            assert false;
          }
        case LookaroundR(lk, r1) =>
          // the gate is zero-width and, for an L1 (group-free) body, hands the
          // continuation the very map it was entered with — so the pending-
          // closes invariant carries straight through
          assert EL.PikeLkRegex(r) && SD.GroupFreeL(r1);
          match t {
            case LK(lk2, tlk, tc) =>
              assert PendingCloses(acts) == PendingCloses(cont);
              LL.ComputeTrGmNeutral(rer, r1, inp, LG.Empty, L.LkDir(lk));
              assert LL.GmNeutralTree(tlk);
              var sub := LT.TreeLeaves(tlk, gm, inp, L.LkDir(lk));
              LL.GmNeutralLeaves(tlk, gm, inp, L.LkDir(lk));
              LT.FirstTreeLeaf(tlk, gm, inp, L.LkDir(lk));
              if L.Positivity(lk) {
                assert |sub| > 0;              // else TreeRes(t, ..) would be None
                assert sub[0].1 == gm;
              }
              FirstLeafClosed(rer, cont, inp, b, tc, gm, leaf);
            case LKFail(lk2, tlk) =>
              assert false;                    // LKFail has no leaves
            case _ =>
          }
        case Backreference(_) =>
          assert false;
    }
  }

  // ==========================================================================
  // Final-thread facts: the register wf and quant finality of the RESULT
  // thread, composed over FFindMatch's position loop from the per-phase
  // preservation lemmas. What the extraction reads off the winning thread.
  // ==========================================================================
  /** Threads register well-formedness (`ThreadRegsWf`), clock monotonicity
      (from `ClockMono`), and `QuantRegsFinal` through `FFindMatch`'s whole
      scan of the input, so the winning thread — if any — satisfies all three
      at the end. */
  lemma FFindMatchThreadFacts(c: RB.code, str: string, s: AI.VmState, ov: LOr.OracleView,
                              dir: LAnc.direction, cdn: LCdn.cdns,
                              ncap: int, nlook: int, nquant: int)
    requires |s.processed.true_set| == RB.size(c) && |s.processed.false_set| == RB.size(c)
    requires dir == LAnc.Forward
    requires s.context.nextchar == AI.get_char(str, s.cp)
    requires forall pc: nat, q: int, b: bool ::
      NR.GetPcRE(c, pc) == Some(RB.SetQuantToClock(q, b)) ==> !b
    requires s.clock >= 0 && s.cp >= 0
    requires CM.VmClocksLE(s)
    requires CM.VmRegsWf(s, ncap, nlook, nquant)
    requires VmQuantFinal(s)
    ensures var r := AI.FFindMatch(c, str, s, ov, dir, cdn).0;
      r.Some? ==> CM.ThreadRegsWf(r.value, ncap, nlook, nquant) && QuantRegsFinal(r.value)
    decreases |str| - s.cp
  {
    var s0 := s.(cdn := LCdn.build_cdn_v(cdn, s.cp, ov, s.context, dir));
    assert CM.VmClocksLE(s0) && CM.VmRegsWf(s0, ncap, nlook, nquant) && VmQuantFinal(s0);
    CM.FAdvanceEpsilonClocksLE(c, s0, ov, dir);
    CM.FAdvanceEpsilonRegsWf(c, s0, ov, dir, ncap, nlook, nquant);
    FAdvanceEpsilonQuantFinal(c, s0, ov, dir);
    var (s1, ov1) := AI.FAdvanceEpsilon(c, s0, ov, dir);
    assert s1.cp == s.cp && s1.context == s.context;
    assert s1.clock >= s0.clock >= 0;

    if |s1.blocked| == 0 {
      assert AI.FFindMatch(c, str, s, ov, dir, cdn).0 == s1.bestmatch;
    } else if s1.context.nextchar.None? {
      assert AI.FFindMatch(c, str, s, ov, dir, cdn).0 == s1.bestmatch;
    } else {
      assert AI.get_char(str, s.cp).Some?;
      assert 0 <= s.cp < |str|;
      CM.FConsumeClocksLE(s1);
      CM.FConsumeRegsWf(s1, ncap, nlook, nquant);
      FConsumeQuantFinal(s1);
      var s2 := AI.FConsume(s1);
      var s3 := s2.(processed := AI.init_bpcset(RB.size(c)), isblocked := AI.init_pcset(RB.size(c)),
                    cdn := LCdn.init_cdn(), cp := AI.incr_cp(s2.cp, dir));
      var newchar := AI.get_char(str, s3.cp - AI.cp_offset(dir));
      var s4 := s3.(context := LAnc.update_context(s3.context, newchar));
      assert s4.cp == s.cp + 1;
      assert s4.context.nextchar == AI.get_char(str, s4.cp);
      assert CM.VmClocksLE(s4) by {
        assert s4.active == s2.active && s4.blocked == s2.blocked
            && s4.bestmatch == s2.bestmatch && s4.clock == s2.clock;
      }
      assert CM.VmRegsWf(s4, ncap, nlook, nquant) by {
        assert s4.active == s2.active && s4.blocked == s2.blocked && s4.bestmatch == s2.bestmatch;
      }
      assert VmQuantFinal(s4) by {
        assert s4.active == s2.active && s4.blocked == s2.blocked && s4.bestmatch == s2.bestmatch;
      }
      assert s4.clock == s2.clock == s1.clock >= 0;
      FFindMatchThreadFacts(c, str, s4, ov1, dir, cdn, ncap, nlook, nquant);
      assert AI.FFindMatch(c, str, s, ov, dir, cdn) == AI.FFindMatch(c, str, s4, ov1, dir, cdn);
    }
  }

  // ==========================================================================
  // The QMap builder: qid |-> DefGroups(Translate(body)), per quant node.
  // ==========================================================================
  /** Builds the quantifier half of the `AR.QMap` for `re`: maps each quant id
      to the capture groups defined by its body (`L.DefGroups` of the translated
      body), by walking `re`'s quant nodes. The lookaround half is built
      separately (`OE.LmOf`) and the two are paired at the assembly. */
  ghost function QmOfRE(re: R.regex): map<int, LG.GroupSet>
    requires T.TransWf(re)
    decreases re
  {
    match re
    case Re_empty => map[]
    case Re_character(_) => map[]
    case Re_anchor(_) => map[]
    case Re_alt(r1, r2) => QmOfRE(r1) + QmOfRE(r2)
    case Re_con(r1, r2) => QmOfRE(r1) + QmOfRE(r2)
    case Re_quant(nul, qid, q, r1) => QmOfRE(r1)[qid := L.DefGroups(T.Translate(r1))]
    case Re_capture(_, r1) => QmOfRE(r1)
    case Re_lookaround(_, _, r1) => QmOfRE(r1)
  }

  /** Builds the lookaround half of the `AR.QMap` for `re`: maps each
      lookaround id to its translated flavour and body — the link
      `CheckOracle(lid)` erases. (`LmapOk` for it needs lid uniqueness, the
      `LT.LookUnique` analogue of `PIV.QuantUnique`; the current top-level
      gate is lookaround-free, where `AR.PlusFragmentLmapOk` discharges
      `LmapOk` outright.) */
  /** `LmOf(lazy_prefix(ast))` is `LmOf(ast)`: the prefix is a quantified
      any-char, which registers no lookaround row. Lets the entry lemmas, which
      are stated about the compiled ast, apply to the table built for `re`. */
  lemma LmOfLazyPrefix(ast: R.regex)
    requires T.TransWf(R.lazy_prefix(ast)) && T.TransWf(ast)
    ensures OE.LmOf(R.lazy_prefix(ast)) == OE.LmOf(ast)
  {
    var pre := R.Re_quant(R.NonNullable, 0, R.CountedQuant(0, None, false),
                          R.Re_character(R.Dot));
    assert R.lazy_prefix(ast) == R.Re_con(pre, ast);
    OE.LookFreeLmOfEmpty(pre);
    assert map[] + OE.LmOf(ast) == OE.LmOf(ast);
  }


  /** `QmOfRE(re)`'s domain is exactly `re`'s quant ids (`PIV.QuantIds`). */
  lemma QmOfREDom(re: R.regex)
    requires T.TransWf(re) && PIV.QuantUnique(re)
    ensures forall k: int :: k in QmOfRE(re) <==> (k >= 0 && (k as nat) in PIV.QuantIds(re))
    decreases re
  {
    match re
    case Re_empty => case Re_character(_) => case Re_anchor(_) =>
    case Re_alt(r1, r2) => QmOfREDom(r1); QmOfREDom(r2);
    case Re_con(r1, r2) => QmOfREDom(r1); QmOfREDom(r2);
    case Re_quant(nul, qid, q, r1) => QmOfREDom(r1);
    case Re_capture(_, r1) => QmOfREDom(r1);
    case Re_lookaround(_, _, r1) => QmOfREDom(r1);
  }

  /** The body of any quant node inside a well-formed `re` (`T.TransWf`) is
      itself well-formed. */
  lemma TransWfQidBody(re: R.regex, qid: nat)
    requires T.TransWf(re)
    requires qid in PIV.QuantIds(re)
    ensures T.TransWf(PIV.QidBody(re, qid))
    decreases re
  {
    match re
    case Re_alt(r1, r2) =>
      if qid in PIV.QuantIds(r1) { TransWfQidBody(r1, qid); } else { TransWfQidBody(r2, qid); }
    case Re_con(r1, r2) =>
      if qid in PIV.QuantIds(r1) { TransWfQidBody(r1, qid); } else { TransWfQidBody(r2, qid); }
    case Re_quant(nul, qid0, q, r1) =>
      if qid0 >= 0 && (qid0 as nat) == qid {} else { TransWfQidBody(r1, qid); }
    case Re_capture(_, r1) => TransWfQidBody(r1, qid);
    case Re_lookaround(_, _, r1) => TransWfQidBody(r1, qid);
  }

  /** Each entry of `QmOfRE(re)` really is the def-groups of that quant id's
      body, provided quant ids are unique (`PIV.QuantUnique`). */
  lemma QmOfREEntries(re: R.regex)
    requires T.TransWf(re) && PIV.QuantUnique(re)
    ensures forall qid: nat :: qid in PIV.QuantIds(re) && T.TransWf(PIV.QidBody(re, qid)) ==>
      (qid as int) in QmOfRE(re)
      && QmOfRE(re)[qid as int] == L.DefGroups(T.Translate(PIV.QidBody(re, qid)))
    decreases re
  {
    match re
    case Re_empty => case Re_character(_) => case Re_anchor(_) =>
    case Re_alt(r1, r2) =>
      QmOfREEntries(r1); QmOfREEntries(r2);
      QmOfREDom(r1); QmOfREDom(r2);
      forall qid: nat | qid in PIV.QuantIds(re) && T.TransWf(PIV.QidBody(re, qid))
        ensures (qid as int) in QmOfRE(re)
             && QmOfRE(re)[qid as int] == L.DefGroups(T.Translate(PIV.QidBody(re, qid)))
      {
        if qid in PIV.QuantIds(r1) {
          assert qid !in PIV.QuantIds(r2) by {
            if qid in PIV.QuantIds(r2) { assert qid in PIV.QuantIds(r1) * PIV.QuantIds(r2); }
          }
          assert (qid as int) !in QmOfRE(r2);
        } else {
          assert qid in PIV.QuantIds(r2);
        }
      }
    case Re_con(r1, r2) =>
      QmOfREEntries(r1); QmOfREEntries(r2);
      QmOfREDom(r1); QmOfREDom(r2);
      forall qid: nat | qid in PIV.QuantIds(re) && T.TransWf(PIV.QidBody(re, qid))
        ensures (qid as int) in QmOfRE(re)
             && QmOfRE(re)[qid as int] == L.DefGroups(T.Translate(PIV.QidBody(re, qid)))
      {
        if qid in PIV.QuantIds(r1) {
          assert qid !in PIV.QuantIds(r2) by {
            if qid in PIV.QuantIds(r2) { assert qid in PIV.QuantIds(r1) * PIV.QuantIds(r2); }
          }
          assert (qid as int) !in QmOfRE(r2);
        } else {
          assert qid in PIV.QuantIds(r2);
        }
      }
    case Re_quant(nul, qid0, q, r1) =>
      QmOfREEntries(r1);
      QmOfREDom(r1);
      assert qid0 >= 0;                                 // QuantUnique
      forall qid: nat | qid in PIV.QuantIds(re) && T.TransWf(PIV.QidBody(re, qid))
        ensures (qid as int) in QmOfRE(re)
             && QmOfRE(re)[qid as int] == L.DefGroups(T.Translate(PIV.QidBody(re, qid)))
      {
        if (qid0 as nat) == qid {
          assert PIV.QidBody(re, qid) == r1;
        } else {
          assert qid in PIV.QuantIds(r1);
          assert (qid as int) != qid0;
        }
      }
    case Re_capture(_, r1) => QmOfREEntries(r1);
    case Re_lookaround(_, _, r1) => QmOfREEntries(r1);
  }

  /** Reconstructs `AR.QmapOk` for a candidate map `qm` from the pointwise
      entry facts `QmOfREEntries` establishes — the bridge from `QmOfRE`'s
      definition to the `QmapOk` precondition the simulation layer requires. */
  lemma QmapOkFromEntries(re: R.regex, qm: AR.QMap)
    requires T.TransWf(re) && PIV.QuantUnique(re)
    requires forall qid: nat :: qid in PIV.QuantIds(re) && T.TransWf(PIV.QidBody(re, qid)) ==>
      (qid as int) in qm.quants && qm.quants[qid as int] == L.DefGroups(T.Translate(PIV.QidBody(re, qid)))
    ensures AR.QmapOk(re, qm)
    decreases re
  {
    match re
    case Re_empty => case Re_character(_) => case Re_anchor(_) =>
    case Re_alt(r1, r2) =>
      forall qid: nat | qid in PIV.QuantIds(r1) && T.TransWf(PIV.QidBody(r1, qid))
        ensures (qid as int) in qm.quants && qm.quants[qid as int] == L.DefGroups(T.Translate(PIV.QidBody(r1, qid)))
      {
        assert qid in PIV.QuantIds(re);
        TransWfQidBody(re, qid);
        assert PIV.QidBody(re, qid) == PIV.QidBody(r1, qid);
      }
      QmapOkFromEntries(r1, qm);
      forall qid: nat | qid in PIV.QuantIds(r2) && T.TransWf(PIV.QidBody(r2, qid))
        ensures (qid as int) in qm.quants && qm.quants[qid as int] == L.DefGroups(T.Translate(PIV.QidBody(r2, qid)))
      {
        assert qid in PIV.QuantIds(re);
        TransWfQidBody(re, qid);
        assert qid !in PIV.QuantIds(r1) by {
          if qid in PIV.QuantIds(r1) { assert qid in PIV.QuantIds(r1) * PIV.QuantIds(r2); }
        }
        assert PIV.QidBody(re, qid) == PIV.QidBody(r2, qid);
      }
      QmapOkFromEntries(r2, qm);
    case Re_con(r1, r2) =>
      forall qid: nat | qid in PIV.QuantIds(r1) && T.TransWf(PIV.QidBody(r1, qid))
        ensures (qid as int) in qm.quants && qm.quants[qid as int] == L.DefGroups(T.Translate(PIV.QidBody(r1, qid)))
      {
        assert qid in PIV.QuantIds(re);
        TransWfQidBody(re, qid);
        assert PIV.QidBody(re, qid) == PIV.QidBody(r1, qid);
      }
      QmapOkFromEntries(r1, qm);
      forall qid: nat | qid in PIV.QuantIds(r2) && T.TransWf(PIV.QidBody(r2, qid))
        ensures (qid as int) in qm.quants && qm.quants[qid as int] == L.DefGroups(T.Translate(PIV.QidBody(r2, qid)))
      {
        assert qid in PIV.QuantIds(re);
        TransWfQidBody(re, qid);
        assert qid !in PIV.QuantIds(r1) by {
          if qid in PIV.QuantIds(r1) { assert qid in PIV.QuantIds(r1) * PIV.QuantIds(r2); }
        }
        assert PIV.QidBody(re, qid) == PIV.QidBody(r2, qid);
      }
      QmapOkFromEntries(r2, qm);
    case Re_quant(nul, qid0, q, r1) =>
      assert qid0 >= 0;                                 // QuantUnique
      assert (qid0 as nat) in PIV.QuantIds(re);
      assert PIV.QidBody(re, qid0 as nat) == r1;
      assert qid0 in qm.quants && qm.quants[qid0] == L.DefGroups(T.Translate(r1));
      forall qid: nat | qid in PIV.QuantIds(r1) && T.TransWf(PIV.QidBody(r1, qid))
        ensures (qid as int) in qm.quants && qm.quants[qid as int] == L.DefGroups(T.Translate(PIV.QidBody(r1, qid)))
      {
        assert qid in PIV.QuantIds(re);
        TransWfQidBody(re, qid);
        assert (qid0 as nat) != qid by { assert (qid0 as nat) !in PIV.QuantIds(r1); }
        assert PIV.QidBody(re, qid) == PIV.QidBody(r1, qid);
      }
      QmapOkFromEntries(r1, qm);
    case Re_capture(_, r1) =>
      forall qid: nat | qid in PIV.QuantIds(r1) && T.TransWf(PIV.QidBody(r1, qid))
        ensures (qid as int) in qm.quants && qm.quants[qid as int] == L.DefGroups(T.Translate(PIV.QidBody(r1, qid)))
      {
        assert qid in PIV.QuantIds(re);
        TransWfQidBody(re, qid);
        assert PIV.QidBody(re, qid) == PIV.QidBody(r1, qid);
      }
      QmapOkFromEntries(r1, qm);
    case Re_lookaround(_, _, r1) =>
      forall qid: nat | qid in PIV.QuantIds(r1) && T.TransWf(PIV.QidBody(r1, qid))
        ensures (qid as int) in qm.quants && qm.quants[qid as int] == L.DefGroups(T.Translate(PIV.QidBody(r1, qid)))
      {
        assert qid in PIV.QuantIds(re);
        TransWfQidBody(re, qid);
        assert PIV.QidBody(re, qid) == PIV.QidBody(r1, qid);
      }
      QmapOkFromEntries(r1, qm);
  }

  // ==========================================================================
  // Compile-pipeline frames for the fragment.
  // ==========================================================================
  /** `CP.FCompileExtra` (the lookaround-compilation pass) leaves the main
      ast/bytecode/cdns fields of an `FCompiled` untouched on fragment
      regexes (which contain no lookarounds). */
  lemma FCompileExtraFrame(r: R.regex, c: CP.FCompiled)
    requires NR.LookBehindFragmentRE(r)
    ensures CP.FCompileExtra(r, c).f_main_ast == c.f_main_ast
    ensures CP.FCompileExtra(r, c).f_main_bc == c.f_main_bc
    ensures CP.FCompileExtra(r, c).f_main_cdns == c.f_main_cdns
    decreases r
  {
    match r
    case Re_empty => case Re_character(_) => case Re_anchor(_) =>
    case Re_capture(_, r1) => FCompileExtraFrame(r1, c);
    case Re_alt(r1, r2) => FCompileExtraFrame(r1, c); FCompileExtraFrame(r2, CP.FCompileExtra(r1, c));
    case Re_con(r1, r2) => FCompileExtraFrame(r1, c); FCompileExtraFrame(r2, CP.FCompileExtra(r1, c));
    case Re_quant(nul, qid, quant, r1) =>
      var c1 := if quant.min > 0 && quant.max == None && nul != R.NonNullable && quant.greedy
                then c.(f_plus_bc := CP.upd(c.f_plus_bc, qid, CP.compile_reconstruct_nulled(r1)))
                else c;
      FCompileExtraFrame(r1, c1);
    case Re_lookaround(lid, la, body) =>
      // reachable under the widened gate: the five updates write only the LOOK
      // tables, and the recursion into `body` leaves the main fields alone too
      var c1 := c.(f_look_types := CP.upd(c.f_look_types, lid, la));
      var c2 := c1.(f_look_cdns := CP.upd(c1.f_look_cdns, lid, LCdn.compile_cdns(body)));
      var c3 := c2.(f_look_ast := CP.upd(c2.f_look_ast, lid, body));
      var c4 := c3.(f_look_build_bc :=
                      CP.upd(c3.f_look_build_bc, lid,
                             CP.compile_to_write(CP.oracle_regex(la, body), lid)));
      var c5 := c4.(f_look_capture_bc :=
                      CP.upd(c4.f_look_capture_bc, lid,
                             CP.compile_to_bytecode(CP.capture_regex(la, body))));
      NR.PlusIsLookBehindFragmentRE(body);
      FCompileExtraFrame(body, c5);
  }

  /** `CP.FCompileExtra` also leaves the plus-reconstruction bytecode table
      untouched on fragment regexes. */
  lemma FCompileExtraPlusFrame(r: R.regex, c: CP.FCompiled)
    requires NR.PlusFragmentRE(r)
    ensures CP.FCompileExtra(r, c).f_plus_bc == c.f_plus_bc
    decreases r
  {
    match r
    case Re_empty => case Re_character(_) => case Re_anchor(_) =>
    case Re_capture(_, r1) => FCompileExtraPlusFrame(r1, c);
    case Re_alt(r1, r2) => FCompileExtraPlusFrame(r1, c); FCompileExtraPlusFrame(r2, CP.FCompileExtra(r1, c));
    case Re_con(r1, r2) => FCompileExtraPlusFrame(r1, c); FCompileExtraPlusFrame(r2, CP.FCompileExtra(r1, c));
    case Re_quant(nul, qid, quant, r1) =>
      // plus fragment: an unbounded min > 0 quant carries the NonNullable
      // annotation, so the greedy-nullable-+ table update never fires
      assert quant.min > 0 && quant.max == None ==> nul == R.NonNullable;
      FCompileExtraPlusFrame(r1, c);
    case Re_lookaround(_, _, _) =>
  }

  /** A star-fragment regex (`NR.StarFragmentRE`) contains no lookarounds:
      `R.max_lookaround` is `0`. */
  lemma FragmentMaxLook(re: R.regex)
    requires NR.PlusFragmentRE(re)
    ensures R.max_lookaround(re) == 0
    decreases re
  {
    match re
    case Re_empty => case Re_character(_) => case Re_anchor(_) =>
    case Re_alt(r1, r2) => FragmentMaxLook(r1); FragmentMaxLook(r2);
    case Re_con(r1, r2) => FragmentMaxLook(r1); FragmentMaxLook(r2);
    case Re_quant(_, _, _, r1) => FragmentMaxLook(r1);
    case Re_capture(_, r1) => FragmentMaxLook(r1);
    case Re_lookaround(_, _, _) =>
  }

  // ==========================================================================
  // ======================  T H E   M A I N   T H E O R E M  ================
  // RegElk's functional engine meets the Linden/Warblre tree specification on
  // the star fragment. Every call below is a previously verified lemma.
  // ==========================================================================
  /** ==== THE PINNACLE CORRECTNESS THEOREM ====
      RegElk's compiled, executable matcher (`AI.FFullMatch`) agrees with the
      Linden/Warblre reference semantics (`LES.MatcherSpec`) on every
      star-fragment regex over Latin-1-well-formed input. Assembles the whole
      pipeline: compile the regex, run the simulation (`PSM.FindMatchSimRE`)
      to pin the winning VM thread to the spec's first leaf, then hand off to
      `MainExtraction` to show the two answers denote the same result. */
  // NO {:isolate_assertions}: with the `hide` bridges below (the ThreadRegsWf
  // restatement and the MainExtraction call), the monolithic VC verifies in
  // ~49s, against 6m35s for ~1200 isolated batches. The previous campaign left
  // this exact question open; measured, the bridges win.
  /** The static lookaround package: everything about the lookaround tables
      and the built oracle that `MainTheorem` consumes, derived in a MINIMAL
      context. `LmapOk`, `OracleOkSuffix` and `ActionsRepL` are large
      quantified predicates. Under the plus gate they were nearly free
      (`qm.looks == map[]` made the oracle hypothesis vacuous); once the gate
      admits real lookbehinds the main lemma has to DERIVE them, and doing that
      inline ran the VC past 900s. Established here, consumed as opaque facts
      there. */
  lemma LookStaticPackage(raw: R.raw_regex, str: string, qm: AR.QMap)
    requires NR.LookBehindFragmentRaw(raw) && T.Latin1Wf(raw)
    // listed first so the `qm` clause below is well-formed: QmOfRE / LmOf are
    // partial on TransWf, and a precondition cannot call AnnotateWf itself
    requires T.TransWf(R.annotate(raw)) && T.TransWf(R.lazy_prefix(R.annotate(raw)))
    requires qm == AR.QMap(QmOfRE(R.lazy_prefix(R.annotate(raw))),
                           OE.LmOf(R.lazy_prefix(R.annotate(raw))),
                           AI.FBuildOracle(CP.FFullCompilation(R.annotate(raw)), str))
    ensures var re := R.lazy_prefix(R.annotate(raw));
      AR.QmapOk(re, qm) && AR.LmapOk(re, qm)
      && LL.OracleOkSuffix(LES.TheRer(raw), qm, LC.InitInput(str))
      && AR.ActionsRepL(LES.TheRer(raw), qm, [LS.Areg(T.Translate(re))],
                        CP.compile_to_bytecode(re), 0)
  {
    var ast := R.annotate(raw);
    var re := R.lazy_prefix(ast);
    var rer := LES.TheRer(raw);
    T.AnnotateWf(raw);
    NR.SpecRegexLookBehindFragment(raw);
    LTB.SpecRegexLookUnique(raw);
    assert NR.LookBehindFragmentRE(ast);
    PIV.SpecRegexQuantUnique(raw);
    QmOfREEntries(re);
    QmapOkFromEntries(re, qm);
    OE.LmapOkOfLmOf(re, qm);
    LmOfLazyPrefix(ast);
    assert qm.looks == OE.LmOf(ast);
    OE.OracleOkFromColumns(rer, ast, str, qm);
    AR.CompileToBytecodeActionsRepLookBehind(rer, qm, re);
  }

  // {:isolate_assertions} is REQUIRED here, not a tuning knob. Admitting
  // lookaheads adds a second column-spec path and a second capture-regex
  // shape, and the combined VC runs past 900s. Isolated, every one of its
  // 1566 obligations passes and the lemma completes in ~10m. (Checked first
  // that no obligation FAILS -- twice in this campaign a widening turned a
  // true assertion false and presented as a timeout.)
  lemma {:isolate_assertions} MainTheorem(raw: R.raw_regex, str: string)
    requires NR.LookBehindFragmentRaw(raw)
    requires T.Latin1Wf(raw)
    ensures LES.MatcherSpec(raw, str, LES.Normalize(AI.FFullMatch(raw, str)))
  {
    hide T.TransWf, NR.PlusFragmentRE, NR.LookBehindFragmentRE, NR.CaptureFreeRE, NR.LookFreeRE, NR.LookBehindFragmentRaw, NR.CaptureFreeRaw, NR.LookFreeRaw, EL.PikeLkRegex, EL.LkGateOk, SD.GroupFreeL;
    var ast := R.annotate(raw);
    var re := R.lazy_prefix(ast);
    var rer := LES.TheRer(raw);
    var inp := LC.InitInput(str);
    var ngroups := LES.NGroups(raw);

    // ---- static packages -------------------------------------------------
    T.AnnotateWf(raw);                     // TransWf(ast) && TransWf(re)
    NR.SpecRegexLookBehindFragment(raw);   // LookBehindFragmentRE(re)
    LTB.SpecRegexLookUnique(raw);          // unique lids, all >= 1

    assert NR.LookBehindFragmentRE(ast);   // con component

    PIV.SpecRegexCapUnique(raw);           // CapUnique(re)
    PIV.SpecRegexQuantUnique(raw);         // QuantUnique(re)
    // the oracle view is part of the static table record; the main pass never
    // writes it (`crv` below is the same compilation, so `qm.ov == ov`)
    var qm := AR.QMap(QmOfRE(re), OE.LmOf(re), AI.FBuildOracle(CP.FFullCompilation(ast), str));
    // QmapOk / LmapOk / OracleOkSuffix / ActionsRepL, all at once and all
    // derived elsewhere -- see LookStaticPackage's comment
    LookStaticPackage(raw, str, qm);

    NR.CompileToBytecodeRepLookBehind(re);
    var code := CP.compile_to_bytecode(re);
    var next := CP.compile(re, 0, CP.Progress).1;
    var endl: nat := next as nat;
    assert NR.NfaRepRE(re, code, 0, endl)
        && NR.GetPcRE(code, endl) == Some(RB.Accept) && |code| == endl + 1;
    PIV.CompileStutterTameRE(re);
    assert PSM.StaticOkRE(qm, re, code, endl);


    // register file sizes: the lazy prefix adds no groups and quant id 0.
    var maxcap := R.max_group(ast);
    var maxquant := R.max_quant(ast);
    assert R.max_group(re) == maxcap;
    assert R.max_quant(re) == R.imax(0, maxquant) == maxquant;
    var ncap := 2 * maxcap + 2;
    var nlook := R.max_lookaround(ast) + 1;
    var nquant := maxquant + 1;
    assert PSM.SizesOkRE(re, ncap, nlook, nquant);
    assert ngroups == (maxcap + 1) as nat;

    // fragment code shape: every SetQuantToClock has b == false.
    forall pc: nat, q: int, b: bool | NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(q, b))
      ensures !b
    {
      if pc < endl {
        NI.CodeShapeAt(re, code, 0, endl, pc);
      } else if pc == endl {
      } else {
        assert pc >= |code|;
      }
    }

    // ---- the spec tree ---------------------------------------------------
    LFU.ComputeTrIsTree(rer, [LS.Areg(T.Translate(re))], inp, LG.Empty, WP.Forward);
    var t := LFU.ComputeTr(rer, [LS.Areg(T.Translate(re))], inp, LG.Empty, WP.Forward);
    assert LS.IsTree(rer, [LS.Areg(T.Translate(re))], inp, LG.Empty, WP.Forward, t);
    assert LES.SpecRegex(raw) == T.Translate(re);
    EL.TranslateFragmentPikeLk(re);        // PikeLkRegex(Translate(re))
    EL.BooleanCorrectLk(rer, T.Translate(re), inp, t);
    assert forall i :: 0 <= i < |[LS.Areg(T.Translate(re))]| ==> ![LS.Areg(T.Translate(re))][i].Acheck?;
    BoolTreeLbIrrel(rer, [LS.Areg(T.Translate(re))], inp, BS.CanExit, BS.CannotExit, t);

    // ---- the CHECKED tree the simulation runs on ---------------------------
    // The engine represents the checked variant of the spec walk (the
    // do-while's dissolved progress guards); build it once at the entry and
    // remember that its leaves — hence its first leaf — agree with t's.
    WOE.WalkOkEntry(re);
    assert EL.PikeLkActions([LS.Areg(T.Translate(re))]) by {
      assert [LS.Areg(T.Translate(re))] == [LS.Areg(T.Translate(re))] + [];
      assert EL.PikeLkActions([]);
      EL.PikeLkActionsConsIff(LS.Areg(T.Translate(re)), []);
    }
    assert WO.WalkOk([LS.Areg(T.Translate(re))], code, 0, ATR.EaOf(BS.CannotExit));
    assert LL.OracleOkSuffix(rer, qm, inp);
    var tstar := ATR.ActionsTreeRepRE(rer, qm, [LS.Areg(T.Translate(re))], code, 0, inp, BS.CannotExit, t);
    assert TR.TreeRepRE(qm, tstar, code, 0, inp, false);
    LL.LAAtFirstLeaf(tstar, t, inp);
    assert LT.FirstLeaf(tstar, inp) == LT.FirstLeaf(t, inp);

    // ---- the engine pipeline ---------------------------------------------
    var crv := CP.FFullCompilation(ast);
    FFullCompilationFacts(ast);
    assert crv.f_main_ast == ast && crv.f_main_bc == code && crv.f_main_cdns == LCdn.compile_cdns(ast);

    var ov := AI.FBuildOracle(crv, str);
    var capture := AReg.init_regs(ncap);
    var look := AReg.init_regs(nlook);
    var quant := AReg.init_regs(nquant);
    var ctx := AI.cp_context(0, str, LAnc.Forward);
    var inits := AI.FInitState(code, 0, capture, look, quant, 0, ctx);
    var fmres := AI.FFindMatch(code, str, inits, ov, LAnc.Forward, crv.f_main_cdns);
    var result := fmres.0;
    assert AI.FFindMatchPlus(code, ast, crv.f_plus_bc, str, ov, LAnc.Forward, 0,
                             capture, look, quant, 0, crv.f_main_cdns).0
        == (match result
            case None => None
            case Some(thread) => Some(AI.FReconstructPlus(thread, ast, crv.f_plus_bc, str, fmres.1, LAnc.Forward).0));


    // ---- the simulation (on the CHECKED tree) ------------------------------
    PSM.InitialPikeInvFullRE(rer, qm, re, code, endl, ngroups, str, tstar, inits, ncap, nlook, nquant);
    var pts0 := PT.PikeTreeInitialState(tstar, inp);
    assert ctx.nextchar == AI.get_char(str, 0);
    var bestT := PSM.FindMatchSimRE(rer, qm, re, code, endl, ngroups, str, pts0, inits,
                                    ov, LAnc.Forward, crv.f_main_cdns, ncap, nlook, nquant);
    assert PSM.TrcRE(pts0, PT.PTS_final(bestT));
    assert PIV.BestMatchRE(re, bestT, result);

    // ---- pin bestT to the semantic first leaf ------------------------------
    // The PikeTree tail runs on tstar; the LeavesAgree hop carries the answer
    // back to the spec tree t.
    TrcREToLinden(pts0, PT.PTS_final(bestT));
    TR.TreeRepPikeSubtree(qm, tstar, code, 0, inp, false);
    PT.InitPiketreeInv(tstar, inp);
    CR.PikeTreeTrcCorrect(pts0, PT.PTS_final(bestT), LT.FirstLeaf(tstar, inp));
    assert bestT == LT.FirstLeaf(tstar, inp);
    assert bestT == LT.FirstLeaf(t, inp);

    // ---- final-thread facts ------------------------------------------------
    CM.RegsClocksLEInit(ncap, 0);
    CM.RegsClocksLEInit(nlook, 0);
    CM.RegsClocksLEInit(nquant, 0);
    CM.FInitStateClocksLE(code, 0, capture, look, quant, 0, ctx);
    CM.FInitStateRegsWf(code, 0, ncap, nlook, nquant, 0, ctx);
    assert VmQuantFinal(inits) by {
      var th := AI.init_thread(capture, look, quant);
      assert QuantRegsFinal(th) by {
        forall k ensures AI.get_idx(quant.a_cp, k) < 0 && AI.get_idx(quant.a_clk, k) >= -1 {
          if 0 <= k < |quant.a_cp| { assert quant.a_cp[k] == -1; }
          if 0 <= k < |quant.a_clk| { assert quant.a_clk[k] == -1; }
        }
      }
      forall t2 | t2 in inits.active ensures QuantRegsFinal(t2) { assert t2 == th; }
    }
    FFindMatchThreadFacts(code, str, inits, ov, LAnc.Forward, crv.f_main_cdns, ncap, nlook, nquant);

    // ---- stage the engine pipeline (small definitional steps) --------------
    var bc := AI.FBuildCapture(crv, str, ov);
    assert AI.FMatcher(crv, str) == bc.0;
    assert AI.FFullMatch(raw, str) == bc.0;
    var fmp := AI.FFindMatchPlus(crv.f_main_bc, crv.f_main_ast, crv.f_plus_bc, str, ov,
                                 LAnc.Forward, 0, capture, look, quant, 0, crv.f_main_cdns);
    assert fmp == AI.FFindMatchPlus(code, ast, crv.f_plus_bc, str, ov,
                                    LAnc.Forward, 0, capture, look, quant, 0, crv.f_main_cdns);
    assert AI.FInitState(crv.f_main_bc, 0, capture, look, quant, 0,
                         AI.cp_context(0, str, LAnc.Forward)) == inits;
    assert fmp.0 == (match result
                     case None => None
                     case Some(thread) =>
                       Some(AI.FReconstructPlus(thread, ast, crv.f_plus_bc, str, fmres.1, LAnc.Forward).0));

    // ---- extraction --------------------------------------------------------
    assert R.max_group(crv.f_main_ast) == maxcap && R.max_quant(crv.f_main_ast) == maxquant;
    assert ncap == 2 * R.max_group(crv.f_main_ast) + 2;
    assert nquant == R.max_quant(crv.f_main_ast) + 1;
    // the capture pass runs for real; its row hypothesis comes from the
    // lookaround tables (LookRowsFromTables), discharged in its own context
    if result.None? {
      assert fmp.0 == None;
      FBuildCaptureUnfold(crv, str, ov, ncap, nlook, nquant, capture, look, quant, fmp);
      assert bc.0 == None;
      assert bestT.None?;
      assert LT.FirstLeaf(t, inp) == None;
      assert LES.Normalize(AI.FFullMatch(raw, str)) == None;
      assert LES.MatcherSpec(raw, str, None);
    } else {
      var thread := result.value;
      assert CM.ThreadRegsWf(thread, ncap, nlook, nquant) && QuantRegsFinal(thread);
      var caps := thread.capture_regs;
      var lk := thread.look_regs;
      var qt := thread.quant_regs;

      // FReconstructPlus is the identity on the fragment.
      FNulledPlusIdentity(ast, caps, lk, qt, crv.f_plus_bc, str, fmres.1, LAnc.Forward);
      assert AI.FReconstructPlus(thread, ast, crv.f_plus_bc, str, fmres.1, LAnc.Forward).0 == thread;
      assert fmp.0 == Some(thread);

      // the engine answer, via the unfold lemma -- called HERE, not before the
      // branch: its preconditions are about `fmp.0.value`, and only after the
      // reconstruct-identity above is that known to be `thread`. Called early,
      // the main VC re-derives reconstruction to reach them and runs away.
      LookRowsFromTables(ast, re, crv, code, str, ov, crv.f_main_cdns, inits,
                         capture, look, quant, nlook, endl, result);
      FBuildCaptureUnfold(crv, str, ov, ncap, nlook, nquant, capture, look, quant, fmp);
      assert bc.0 == Some(AI.filter_reset(crv.f_main_ast, caps, lk, qt, -1));
      assert AI.FFullMatch(raw, str) == Some(AI.filter_reset(ast, caps, lk, qt, -1));

      assert bestT.Some?;
      var leaf := bestT.value;
      assert leaf.1 == PIV.GmOfLive(re, caps, lk, qt);
      assert LT.FirstLeaf(t, inp) == Some(leaf);
      // restate MainExtraction's preconditions one by one, in its own terms:
      // under {:isolate_assertions} each becomes its own batch, keeping any
      // single Z3 search small (the monolithic call batch ran away)
      assert EL.BoolTreeLk(LES.TheRer(raw), [LS.Areg(LES.SpecRegex(raw))], LC.InitInput(str), BS.CannotExit, t);
      assert LS.IsTree(LES.TheRer(raw), [LS.Areg(LES.SpecRegex(raw))], LC.InitInput(str), LG.Empty, WP.Forward, t);
      assert CM.ThreadRegsWf(thread, 2 * R.max_group(R.annotate(raw)) + 2,
                             R.max_lookaround(R.annotate(raw)) + 1,
                             R.max_quant(R.annotate(raw)) + 1) by {
        // semantically the already-established line-1132 fact modulo the
        // `ast` let; with every definition hidden the solver has nothing to
        // unfold and closes by congruence (the open-context batch ran away
        // in ThreadRegsWf's register quantifiers)
        hide *;
        assert ast == R.annotate(raw);
        assert R.max_lookaround(ast) + 1 == nlook;
        assert CM.ThreadRegsWf(thread, ncap, nlook, nquant);
      }
      assert QuantRegsFinal(thread);
      assert leaf.1 == PIV.GmOfLive(R.lazy_prefix(R.annotate(raw)), thread.capture_regs,
                                    thread.look_regs, thread.quant_regs);
      assert LT.FirstLeaf(t, LC.InitInput(str)) == Some(leaf);
      assert AI.FFullMatch(raw, str)
          == Some(AI.filter_reset(R.annotate(raw), thread.capture_regs, thread.look_regs,
                                  thread.quant_regs, -1));
      // every precondition is restated verbatim just above, so with the axiom
      // space collapsed the call's check closes by congruence — without the
      // hide, this ONE batch ran away past 900s while all 1213 others passed
      { hide *; MainExtraction(raw, str, t, thread, leaf); }
    }
  }

  // FFullCompilation's main fields, derived in a MINIMAL context (the huge
  // FCompiled base literal must not leak into the main lemma's VCs).
  /** Pins down `CP.FFullCompilation`'s three fields that `MainTheorem` needs,
      computed in a minimal context so the large `FCompiled` base record
      doesn't leak into the caller's verification conditions. */
  lemma FFullCompilationFacts(ast: R.regex)
    requires NR.LookBehindFragmentRE(ast)
    ensures CP.FFullCompilation(ast).f_main_ast == ast
    ensures CP.FFullCompilation(ast).f_main_bc == CP.compile_to_bytecode(R.lazy_prefix(ast))
    ensures CP.FFullCompilation(ast).f_main_cdns == LCdn.compile_cdns(ast)
  {
    var nlook0 := R.max_lookaround(ast) + 1;
    var nquant0 := R.max_quant(ast) + 1;
    var base := CP.FCompiled(ast, CP.compile_to_bytecode(R.lazy_prefix(ast)), LCdn.compile_cdns(ast),
                             seq(nlook0, i => R.Lookahead), seq(nlook0, i => R.Re_empty),
                             seq(nlook0, i => []), seq(nlook0, i => []),
                             seq(nlook0, i => []), seq(nquant0, i => []));
    assert CP.FFullCompilation(ast) == CP.FCompileExtra(ast, base);
    FCompileExtraFrame(ast, base);
  }

  // ==========================================================================
  // The lookaround CAPTURE pass leaves the answer alone (L1).
  //
  // `FLookLoop` replays each matched positive lookaround's capture bytecode and
  // keeps the replay's registers. For capture-free bodies that cannot move
  // `filter_reset` over the main ast: the replay writes no capture register and
  // no look register, and the quant ids it does write live inside a lookaround
  // body, where the filter never reads them.
  // ==========================================================================

  /** `FFindMatchThreadFacts`' quant half, in BOTH directions — the lookbehind
      capture pass runs backward, so the forward-only version does not apply. */
  lemma FFindMatchQuantFinalAny(c: RB.code, str: string, s: AI.VmState, ov: LOr.OracleView,
                                dir: LAnc.direction, cdn: LCdn.cdns)
    requires |s.processed.true_set| == RB.size(c) && |s.processed.false_set| == RB.size(c)
    requires dir.Forward? ==> s.context.nextchar == AI.get_char(str, s.cp)
    requires dir.Backward? ==> s.context.nextchar == AI.get_char(str, s.cp - 1)
    requires forall pc: nat, q: int, b: bool ::
      NR.GetPcRE(c, pc) == Some(RB.SetQuantToClock(q, b)) ==> !b
    requires s.clock >= -1
    requires VmQuantFinal(s)
    ensures var r := AI.FFindMatch(c, str, s, ov, dir, cdn).0;
      r.Some? ==> QuantRegsFinal(r.value)
    decreases if dir.Forward? then |str| - s.cp else s.cp
  {
    var s0 := s.(cdn := LCdn.build_cdn_v(cdn, s.cp, ov, s.context, dir));
    assert VmQuantFinal(s0);
    FAdvanceEpsilonQuantFinal(c, s0, ov, dir);
    var (s1, ov1) := AI.FAdvanceEpsilon(c, s0, ov, dir);
    assert VmQuantFinal(s1);
    CM.FAdvanceEpsilonClockGrows(c, s0, ov, dir);
    if |s1.blocked| == 0 { return; }
    match s1.context.nextchar {
      case None =>
      case Some(_) =>
        var s2 := AI.FConsume(s1);
        FConsumeQuantFinal(s1);
        var s3 := s2.(processed := AI.init_bpcset(RB.size(c)), isblocked := AI.init_pcset(RB.size(c)),
                      cdn := LCdn.init_cdn(), cp := AI.incr_cp(s2.cp, dir));
        var newchar := AI.get_char(str, s3.cp - AI.cp_offset(dir));
        var s4 := s3.(context := LAnc.update_context(s3.context, newchar));
        assert VmQuantFinal(s4);
        FFindMatchQuantFinalAny(c, str, s4, ov1, dir, cdn);
    }
  }

  /** THE capture-pass frame: filtering the main ast over the registers
      `FLookLoop` returns gives what filtering over the registers it was handed
      gives. */
  lemma FLookLoopFilterFrame(crv: CP.FCompiled, str: string, lid: int, maxlook: int,
                             cap: AReg.Regs, lk: AReg.Regs, qt: AReg.Regs, ov: LOr.OracleView,
                             mainast: R.regex)
    requires NR.LookBehindFragmentRE(mainast) && PIV.QuantUnique(mainast)
    requires (forall k :: AI.get_idx(qt.a_cp, k) < 0)
          && (forall k :: AI.get_idx(qt.a_clk, k) >= -1)
    requires forall l: int :: lid <= l <= maxlook && AReg.get_cp(lk, l).Some? ==>
      exists la: R.lookaround, body: R.regex ::
        LTB.LookEntryOk(crv, l, la, body)
        && NR.CaptureFreeRE(body) && NR.LookFreeRE(body) && NR.PlusFragmentRE(body)
        && PIV.QuantUnique(body)
        && (forall q: nat :: q in PIV.QuantIds(body) ==> q in PIV.QuantIdsInLooks(mainast))
    ensures var res := AI.FLookLoop(crv, str, lid, maxlook, cap, lk, qt, ov);
      AI.filter_reset(mainast, res.0, res.1, res.2, -1)
        == AI.filter_reset(mainast, cap, lk, qt, -1)
    decreases maxlook - lid
  {
    if lid > maxlook { return; }
    var next := lid + 1;
    match AReg.get_cp(lk, lid)
    case None =>
      FLookLoopFilterFrame(crv, str, next, maxlook, cap, lk, qt, ov, mainast);
    case Some(cp) =>
      var looktype := if 0 <= lid < |crv.f_look_types| then crv.f_look_types[lid] else R.Lookahead;
      if !AI.capture_type(looktype) {
        FLookLoopFilterFrame(crv, str, next, maxlook, cap, lk, qt, ov, mainast);
      } else {
        var la: R.lookaround, body: R.regex :|
          LTB.LookEntryOk(crv, lid, la, body)
          && NR.CaptureFreeRE(body) && NR.LookFreeRE(body) && NR.PlusFragmentRE(body)
          && PIV.QuantUnique(body)
          && (forall q: nat :: q in PIV.QuantIds(body) ==> q in PIV.QuantIdsInLooks(mainast));
        // capture_type rules out only the NEGATIVE flavours; with lookaheads
        // in the fragment the positive one can be either
        assert looktype == la && (la.Lookbehind? || la.Lookahead?);
        var bytecode := AI.get_code_v(crv.f_look_capture_bc, lid);
        var dir := AI.capture_direction(looktype);
        var lookcdn := if 0 <= lid < |crv.f_look_cdns| then crv.f_look_cdns[lid] else [];
        var lookast := if 0 <= lid < |crv.f_look_ast| then crv.f_look_ast[lid] else R.Re_empty;
        assert bytecode == CP.compile_to_bytecode(CP.capture_regex(la, body));
        assert lookast == body;

        LKC.CaptureCodeClassified(la, body);
        var (result, ov1) := AI.FFindMatchPlus(bytecode, lookast, crv.f_plus_bc, str, ov, dir,
                                               cp, cap, lk, qt, 0, lookcdn);
        var inits := AI.FInitState(bytecode, cp, cap, lk, qt, 0, AI.cp_context(cp, str, dir));
        ReplayFrames(bytecode, str, inits, ov, dir, lookcdn, cap, lk, qt, la, body);
        var (res0, ovx) := AI.FFindMatch(bytecode, str, inits, ov, dir, lookcdn);
        assert result.Some? ==> res0.Some?;
        if result.Some? {
          var th := res0.value;
          assert QuantRegsFinal(th);
          FNulledPlusIdentity(lookast, th.capture_regs, th.look_regs, th.quant_regs,
                              crv.f_plus_bc, str, ovx, dir);
          assert result.value.capture_regs == th.capture_regs
              && result.value.look_regs == th.look_regs
              && result.value.quant_regs == th.quant_regs;
        }
        var ncap, nlk, nqt := if result.None? then cap else result.value.capture_regs,
                              if result.None? then lk else result.value.look_regs,
                              if result.None? then qt else result.value.quant_regs;
        FilterUnmoved(mainast, cap, lk, qt, ncap, nlk, nqt, body);
        FLookLoopFilterFrame(crv, str, next, maxlook, ncap, nlk, nqt, ov1, mainast);
      }
  }

  /** One replay's register facts, packaged: the capture and look banks come out
      untouched, the quant bank agrees outside the body's ids, and the result
      thread is still quant-final. */
  lemma ReplayFrames(bytecode: RB.code, str: string, inits: AI.VmState, ov: LOr.OracleView,
                     dir: LAnc.direction, lookcdn: LCdn.cdns,
                     cap: AReg.Regs, lk: AReg.Regs, qt: AReg.Regs,
                     la: R.lookaround, body: R.regex)
    requires NR.CaptureFreeRE(body) && NR.LookFreeRE(body) && NR.PlusFragmentRE(body)
    requires PIV.QuantUnique(body)
    requires bytecode == CP.compile_to_bytecode(CP.capture_regex(la, body))
    requires inits.active == [AI.init_thread(cap, lk, qt)]
    requires inits.blocked == [] && inits.bestmatch.None?
    requires |inits.processed.true_set| == RB.size(bytecode)
          && |inits.processed.false_set| == RB.size(bytecode)
    requires dir.Forward? ==> inits.context.nextchar == AI.get_char(str, inits.cp)
    requires dir.Backward? ==> inits.context.nextchar == AI.get_char(str, inits.cp - 1)
    requires inits.clock >= -1
    requires (forall k :: AI.get_idx(qt.a_cp, k) < 0)
          && (forall k :: AI.get_idx(qt.a_clk, k) >= -1)
    ensures var r := AI.FFindMatch(bytecode, str, inits, ov, dir, lookcdn).0;
      r.Some? ==>
        r.value.capture_regs == cap
        && r.value.look_regs == lk
        && CM.RegsAgreeOutside(r.value.quant_regs, qt, LKC.QIdsInt(body))
        && QuantRegsFinal(r.value)
  {
    LKC.CaptureCodeClassified(la, body);
    assert CM.VmCapsAre(inits, cap);
    assert CM.VmLooksAre(inits, lk);
    assert CM.VmQuantsAgree(inits, qt, LKC.QIdsInt(body)) by {
      assert CM.RegsAgreeOutside(qt, qt, LKC.QIdsInt(body));
    }
    assert VmQuantFinal(inits);
    CM.FFindMatchCapFrame(bytecode, str, inits, ov, dir, lookcdn, cap);
    CM.FFindMatchLookEq(bytecode, str, inits, ov, dir, lookcdn, lk);
    CM.FFindMatchQuantFrame(bytecode, str, inits, ov, dir, lookcdn, qt, LKC.QIdsInt(body));
    FFindMatchQuantFinalAny(bytecode, str, inits, ov, dir, lookcdn);
  }

  /** L3a — the CAPTURING replay's frame direction: for a lookAHEAD with a
      capturing body (`capture_regex(Lookahead)==body`, run Forward), the
      replay's `FFindMatch` changes the capture bank only within
      `CaptureRegs(body)` (the body's own groups). Contrast `ReplayFrames`,
      which for a capture-free body gets the bank UNTOUCHED. Built from the
      capture-write frame + the whole-bytecode classification. */
  lemma ReplayCaptureFrame(bytecode: RB.code, str: string, inits: AI.VmState, ov: LOr.OracleView,
                           dir: LAnc.direction, lookcdn: LCdn.cdns,
                           cap: AReg.Regs, lk: AReg.Regs, qt: AReg.Regs,
                           la: R.lookaround, body: R.regex)
    requires NR.LookBehindFragmentRE(body) && PIV.CapUnique(body)
    requires la.Lookahead? && dir == LAnc.Forward
    requires bytecode == CP.compile_to_bytecode(body)
    requires inits.active == [AI.init_thread(cap, lk, qt)]
    requires inits.blocked == [] && inits.bestmatch.None?
    requires |inits.processed.true_set| == RB.size(bytecode)
          && |inits.processed.false_set| == RB.size(bytecode)
    requires inits.context.nextchar == AI.get_char(str, inits.cp)
    ensures var r := AI.FFindMatch(bytecode, str, inits, ov, dir, lookcdn).0;
      r.Some? ==> CM.RegsAgreeOutside(r.value.capture_regs, cap, PIV.CaptureRegs(body))
  {
    CM.CaptureBytecodeClassified(body);
    assert CM.VmCapturesAgree(inits, cap, PIV.CaptureRegs(body)) by {
      assert CM.RegsAgreeOutside(cap, cap, PIV.CaptureRegs(body));
    }
    CM.FFindMatchCapWriteFrame(bytecode, str, inits, ov, dir, lookcdn, cap, PIV.CaptureRegs(body));
  }

  /** A plus-fragment body's compiled code never STAMPS a quantifier true
      (`SetQuantToClock(_, true)`) -- the `!bb` half of `CodeShapeAt`, lifted to
      the whole `compile_to_bytecode`. Capture-independent (the quant structure
      is the same whether or not the body captures). Feeds `FFindMatchQuantFinalAny`. */
  lemma NoTrueQuantStamp(body: R.regex)
    requires NR.LookBehindFragmentRE(body) && PIV.CapUnique(body) && PIV.QuantUnique(body)
    ensures var code := CP.compile_to_bytecode(body);
      forall pc: nat, q: int, b: bool ::
        NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(q, b)) ==> !b
  {
    var code := CP.compile_to_bytecode(body);
    var next := CP.compile(body, 0, CP.Progress).1;
    NR.CompileToBytecodeRepLookBehind(body);
    var endl := next as nat;
    forall pc: nat, q: int, b: bool | NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(q, b))
      ensures !b
    {
      assert pc < |code|;
      if pc < endl {
        NI.CodeShapeAt(body, code, 0, endl, pc);
      } else {
        assert pc == endl;
        assert NR.GetPcRE(code, endl) == Some(RB.Accept);
      }
    }
  }

  /** L3a — the FULL replay capture frame: a capturing lookAHEAD's whole
      `FFindMatchPlus` (= `FFindMatch` then `FReconstructPlus`) changes the
      capture bank only within `CaptureRegs(body)`. The `FReconstructPlus` half
      is the IDENTITY even with captures: the replay result is `QuantRegsFinal`
      (`FFindMatchQuantFinalAny`, capture-independent via `NoTrueQuantStamp`), so
      every plus's cp is negative and `FNulledPlus` never runs the reconstruct
      code (`FNulledPlusIdentity`, which is itself capture-agnostic). So the
      change is entirely `ReplayCaptureFrame`'s. */
  lemma ReplayPlusCaptureFrame(bytecode: RB.code, str: string, ov: LOr.OracleView, dir: LAnc.direction,
                               lookcdn: LCdn.cdns, plus_bcv: seq<RB.code>, cp: int,
                               cap: AReg.Regs, lk: AReg.Regs, qt: AReg.Regs, la: R.lookaround, body: R.regex)
    requires NR.LookBehindFragmentRE(body) && PIV.CapUnique(body) && PIV.QuantUnique(body)
    requires la.Lookahead? && dir == LAnc.Forward
    requires bytecode == CP.compile_to_bytecode(body)
    requires AI.cp_context(cp, str, dir).nextchar == AI.get_char(str, cp)
    requires (forall k :: AI.get_idx(qt.a_cp, k) < 0)
          && (forall k :: AI.get_idx(qt.a_clk, k) >= -1)
    ensures var r := AI.FFindMatchPlus(bytecode, body, plus_bcv, str, ov, dir, cp, cap, lk, qt, 0, lookcdn).0;
      r.Some? ==> CM.RegsAgreeOutside(r.value.capture_regs, cap, PIV.CaptureRegs(body))
  {
    var inits := AI.FInitState(bytecode, cp, cap, lk, qt, 0, AI.cp_context(cp, str, dir));
    ReplayCaptureFrame(bytecode, str, inits, ov, dir, lookcdn, cap, lk, qt, la, body);
    NoTrueQuantStamp(body);
    assert VmQuantFinal(inits) by {
      assert QuantRegsFinal(AI.init_thread(cap, lk, qt));
    }
    FFindMatchQuantFinalAny(bytecode, str, inits, ov, dir, lookcdn);
    var (res0, ovx) := AI.FFindMatch(bytecode, str, inits, ov, dir, lookcdn);
    if res0.Some? {
      var th := res0.value;
      assert QuantRegsFinal(th);
      FNulledPlusIdentity(body, th.capture_regs, th.look_regs, th.quant_regs, plus_bcv, str, ovx, dir);
    }
  }

  /** The filter cannot see the difference the replay makes. */
  lemma FilterUnmoved(mainast: R.regex, cap: AReg.Regs, lk: AReg.Regs, qt: AReg.Regs,
                      ncap: AReg.Regs, nlk: AReg.Regs, nqt: AReg.Regs, body: R.regex)
    requires NR.LookBehindFragmentRE(mainast) && PIV.QuantUnique(mainast)
    requires ncap == cap
    requires nlk == lk
    requires CM.RegsAgreeOutside(nqt, qt, LKC.QIdsInt(body))
    requires forall q: nat :: q in PIV.QuantIds(body) ==> q in PIV.QuantIdsInLooks(mainast)
    ensures AI.filter_reset(mainast, ncap, nlk, nqt, -1)
         == AI.filter_reset(mainast, cap, lk, qt, -1)
  {
    PIV.QuantIdsLooksDisjoint(mainast);
    var cr := AReg.as_arrays(cap).0;
    var cc := AReg.as_arrays(cap).1;
    forall q0: nat | q0 in PIV.QuantIdsOutsideLooks(mainast)
      ensures AI.get_idx(AReg.as_arrays(nqt).1, q0) == AI.get_idx(AReg.as_arrays(qt).1, q0)
    {
      assert q0 !in LKC.QIdsInt(body) by {
        if q0 in LKC.QIdsInt(body) {
          assert q0 in PIV.QuantIds(body);
          assert q0 in PIV.QuantIdsInLooks(mainast);
          assert q0 in PIV.QuantIdsOutsideLooks(mainast) * PIV.QuantIdsInLooks(mainast);
        }
      }
    }
    PIV.FilterCaptureFullOutside(mainast, cr, cc, AReg.as_arrays(nlk).1,
                                 AReg.as_arrays(nqt).1, AReg.as_arrays(qt).1, -1);

  }

  /** Under the widened gate the look bank really can be written. Every slot
      the main pass sets names a lookaround id of `re`, and `LmOfInv` turns that
      id into its table row -- which the fragment forces to be an L1 lookbehind.
      This is exactly the capture pass's row hypothesis, discharged in its own
      context so the reasoning never lands in `MainTheorem`'s VC. */
  lemma LookRowsFromTables(ast: R.regex, re: R.regex, crv: CP.FCompiled, code: RB.code,
                           str: string, ov: LOr.OracleView, cdn: LCdn.cdns,
                           inits: AI.VmState, cap: AReg.Regs, look: AReg.Regs,
                           quant: AReg.Regs, nlook: int, endl: nat,
                           result: Option<AI.Thread>)
    requires T.TransWf(ast) && T.TransWf(re) && re == R.lazy_prefix(ast)
    requires NR.LookBehindFragmentRE(re) && LTB.LookUnique(re) && PIV.QuantUnique(re)
    requires crv == CP.FFullCompilation(ast)
    requires code == CP.compile_to_bytecode(re)
    requires NR.NfaRepRE(re, code, 0, endl) && |code| == endl + 1
    requires NR.GetPcRE(code, endl) == Some(RB.Accept)
    requires nlook == R.max_lookaround(ast) + 1 && look == AReg.init_regs(nlook)
    requires |inits.processed.true_set| == RB.size(code)
          && |inits.processed.false_set| == RB.size(code)
    requires inits.context.nextchar == AI.get_char(str, inits.cp)
    requires inits.active == [AI.init_thread(cap, look, quant)]
    requires inits.blocked == [] && inits.bestmatch.None?
    requires result == AI.FFindMatch(code, str, inits, ov, LAnc.Forward, cdn).0
    ensures result.Some? ==>
      forall l: int :: 1 <= l <= R.max_lookaround(ast)
                       && AReg.get_cp(result.value.look_regs, l).Some? ==>
        exists la: R.lookaround, body: R.regex ::
          LTB.LookEntryOk(crv, l, la, body)
          && NR.CaptureFreeRE(body) && NR.LookFreeRE(body) && NR.PlusFragmentRE(body)
          && PIV.QuantUnique(body)
          && (forall q: nat :: q in PIV.QuantIds(body) ==> q in PIV.QuantIdsInLooks(ast))
  {
    var S: set<int> := set x: nat | x in LTB.LookIds(re) :: x as int;
    // the code only gates on ids `re` actually owns
    forall pc: nat | pc < |code|
      ensures (code[pc].CheckOracle? ==> code[pc].col in S)
           && (code[pc].NegCheckOracle? ==> code[pc].ncl in S)
    {
      assert NR.GetPcRE(code, pc) == Some(code[pc]);
      if pc != endl { PIV.LookCheckIdsRE(re, code, 0, endl, pc); }
    }
    assert CM.LookChecksInside(code, S);
    assert CM.VmLooksAgree(inits, look, S) by {
      assert CM.RegsAgreeOutside(look, look, S);
    }
    CM.FFindMatchLookFrame(code, str, inits, ov, LAnc.Forward, cdn, look, S);

    // the lazy prefix owns no lookaround, so `re`'s ids are `ast`'s
    var pre := R.Re_quant(R.NonNullable, 0, R.CountedQuant(0, None, false),
                          R.Re_character(R.Dot));
    assert re == R.Re_con(pre, ast);
    assert LTB.LookIds(pre) == {};
    assert LTB.LookIds(re) == LTB.LookIds(ast);
    assert PIV.QuantUnique(ast) && LTB.LookUnique(ast);
    assert NR.LookBehindFragmentRE(ast);
    LTB.FFullCompilationLookOk(ast);
    OE.LmOfDom(ast);
    RL.AInitLaws(nlook);

    if result.Some? {
      forall l: int | 1 <= l <= R.max_lookaround(ast)
                      && AReg.get_cp(result.value.look_regs, l).Some?
        ensures exists la: R.lookaround, body: R.regex ::
          LTB.LookEntryOk(crv, l, la, body)
          && NR.CaptureFreeRE(body) && NR.LookFreeRE(body) && NR.PlusFragmentRE(body)
          && PIV.QuantUnique(body)
          && (forall q: nat :: q in PIV.QuantIds(body) ==> q in PIV.QuantIdsInLooks(ast))
      {
        // outside `S` the bank still reads as freshly initialized, so a set
        // slot must name one of `re`'s own ids
        assert l in S;
        assert (l as nat) in LTB.LookIds(ast);
        assert l in OE.LmOf(ast);
        var la, body := OE.LmOfInv(ast, crv, l);
      }
    }
  }




  // FBuildCapture, unfolded once in a MINIMAL context (inlined in the main
  // lemma, the solver drowns in the surrounding facts): with no lookarounds
  // the look pass is the identity and the answer is the filtered result
  // thread (or None).
  /** Unfolds `AI.FBuildCapture` once for lookaround-free fragment code: with
      no lookarounds the look-resolution pass is the identity, so the final
      answer is just the filtered capture array of the winning thread (or
      `None`). */
  lemma FBuildCaptureUnfold(crv: CP.FCompiled, str: string, ov: LOr.OracleView,
                            ncap: int, nlook: int, nquant: int,
                            capture: AReg.Regs, look: AReg.Regs, quant: AReg.Regs,
                            fmp: (Option<AI.Thread>, LOr.OracleView))
    requires NR.LookBehindFragmentRE(crv.f_main_ast) && PIV.QuantUnique(crv.f_main_ast)
    requires ncap == 2 * R.max_group(crv.f_main_ast) + 2
    requires nlook == R.max_lookaround(crv.f_main_ast) + 1
    requires nquant == R.max_quant(crv.f_main_ast) + 1
    requires capture == AReg.init_regs(ncap)
    requires look == AReg.init_regs(nlook)
    requires quant == AReg.init_regs(nquant)
    requires fmp == AI.FFindMatchPlus(crv.f_main_bc, crv.f_main_ast, crv.f_plus_bc, str, ov,
                                      LAnc.Forward, 0, capture, look, quant, 0, crv.f_main_cdns)
    // the capture pass's per-row facts, from the tables and the fragment
    requires fmp.0.Some? ==>
      (forall l: int :: 1 <= l <= R.max_lookaround(crv.f_main_ast)
                        && AReg.get_cp(fmp.0.value.look_regs, l).Some? ==>
        exists la: R.lookaround, body: R.regex ::
          LTB.LookEntryOk(crv, l, la, body)
          && NR.CaptureFreeRE(body) && NR.LookFreeRE(body) && NR.PlusFragmentRE(body)
          && PIV.QuantUnique(body)
          && (forall q: nat :: q in PIV.QuantIds(body) ==> q in PIV.QuantIdsInLooks(crv.f_main_ast)))
    requires fmp.0.Some? ==> QuantRegsFinal(fmp.0.value)
    ensures fmp.0.None? ==> AI.FBuildCapture(crv, str, ov).0 == None
    ensures fmp.0.Some? ==> (AI.FBuildCapture(crv, str, ov).0
      == Some(AI.filter_reset(crv.f_main_ast, fmp.0.value.capture_regs,
                              fmp.0.value.look_regs, fmp.0.value.quant_regs, -1)))
  {
    if fmp.0.Some? {
      var thread := fmp.0.value;
      // the look pass may now really run; it just cannot move the answer
      FLookLoopFilterFrame(crv, str, 1, R.max_lookaround(crv.f_main_ast),
                           thread.capture_regs, thread.look_regs, thread.quant_regs, fmp.1,
                           crv.f_main_ast);
    }
  }

  // The Some-branch extraction, as its own verification unit (the parent
  // times out with it inlined).
  /** The `Some`-result half of `MainTheorem`, isolated as its own lemma
      because the combined proof times out. Shows the engine's filtered
      capture array and the spec's first-leaf `GroupMap` denote the same
      `MatcherSpec` answer, via leaf-closedness (`FirstLeafClosed`), the
      live/plain equivalence (`PIV.GmOfLiveEqGmOf`), and the capture-array
      bridge (`PIV.GmOfCapArrayBridge`). */
  lemma MainExtraction(raw: R.raw_regex, str: string,
                                                    t: LT.Tree, thread: AI.Thread, leaf: LT.Leaf)
    requires NR.LookBehindFragmentRaw(raw)
    requires T.Latin1Wf(raw)
    requires EL.BoolTreeLk(LES.TheRer(raw), [LS.Areg(LES.SpecRegex(raw))], LC.InitInput(str), BS.CannotExit, t)
    requires LS.IsTree(LES.TheRer(raw), [LS.Areg(LES.SpecRegex(raw))], LC.InitInput(str), LG.Empty, WP.Forward, t)
    requires CM.ThreadRegsWf(thread, 2 * R.max_group(R.annotate(raw)) + 2,
                             R.max_lookaround(R.annotate(raw)) + 1,
                             R.max_quant(R.annotate(raw)) + 1)
    requires QuantRegsFinal(thread)
    requires var re := R.lazy_prefix(R.annotate(raw));
      leaf.1 == PIV.GmOfLive(re, thread.capture_regs, thread.look_regs, thread.quant_regs)
    requires LT.FirstLeaf(t, LC.InitInput(str)) == Some(leaf)
    requires AI.FFullMatch(raw, str)
          == Some(AI.filter_reset(R.annotate(raw), thread.capture_regs, thread.look_regs,
                                  thread.quant_regs, -1))
    ensures LES.MatcherSpec(raw, str, LES.Normalize(AI.FFullMatch(raw, str)))
  {
    hide T.TransWf, NR.PlusFragmentRE, NR.LookBehindFragmentRE, NR.CaptureFreeRE, NR.LookFreeRE, NR.LookBehindFragmentRaw, NR.CaptureFreeRaw, NR.LookFreeRaw, EL.PikeLkRegex, EL.LkGateOk, SD.GroupFreeL;
    var ast := R.annotate(raw);
    var re := R.lazy_prefix(ast);
    var rer := LES.TheRer(raw);
    var inp := LC.InitInput(str);
    var ngroups := LES.NGroups(raw);
    var ncap := 2 * R.max_group(ast) + 2;
    T.AnnotateWf(raw);
    NR.SpecRegexLookBehindFragment(raw);
    var caps := thread.capture_regs;
    var lk := thread.look_regs;
    var qt := thread.quant_regs;
    assert LES.SpecRegex(raw) == T.Translate(re);

    // closedness of the leaf gm
    assert LT.TreeRes(t, LG.Empty, inp, WP.Forward) == Some(leaf);
    assert OpenOf(LG.Empty) <= PendingCloses([LS.Areg(T.Translate(re))]);
    EL.TranslateFragmentPikeLk(re);
    assert EL.PikeLkActions([LS.Areg(T.Translate(re))]) by {
      assert [LS.Areg(T.Translate(re))] == [LS.Areg(T.Translate(re))] + [];
      assert EL.PikeLkActions([]);
      EL.PikeLkActionsConsIff(LS.Areg(T.Translate(re)), []);
    }
    FirstLeafClosed(rer, [LS.Areg(T.Translate(re))], inp, BS.CannotExit, t, LG.Empty, leaf);
    assert ClosedGm(leaf.1);

    // live == plain denotation on the closed leaf
    var f := AI.filter_reset(re, caps, lk, qt, -1);
    var cc := caps.a_clk;
    PIV.FilterCaptureLen(re, caps.a_cp, cc, lk.a_clk, qt.a_clk, -1);
    assert |f| == |caps.a_cp| == ncap == 2 * ngroups;
    forall g: nat | 0 <= g < |f| && AI.get_idx(f, CP.start_reg(g)) >= 0 && AI.get_idx(f, CP.end_reg(g)) >= 0
      ensures AI.get_idx(cc, CP.end_reg(g)) >= AI.get_idx(cc, CP.start_reg(g))
    {
      assert g in PIV.GmOfLive(re, caps, lk, qt);
      assert PIV.GmOfLive(re, caps, lk, qt)[g].endIdx.Some?;
    }
    PIV.GmOfLiveEqGmOf(re, caps, lk, qt);
    assert PIV.GmOf(re, caps, lk, qt) == leaf.1;

    // the capture-array bridge
    forall i | 0 <= i < |f| ensures f[i] >= -1 {
      assert AI.get_idx(caps.a_cp, i) >= -1;      // CapRegWf
      PIV.FilterCaptureGeqNeg1(re, caps.a_cp, cc, lk.a_clk, qt.a_clk, -1, i);
      assert AI.get_idx(f, i) == f[i];
    }
    forall g: nat | 0 <= g < ngroups && f[2 * g] >= 0 ensures f[2 * g + 1] >= 0 {
      assert AI.get_idx(f, CP.start_reg(g)) == f[2 * g];
      assert g in PIV.GmOfLive(re, caps, lk, qt);
      assert PIV.GmOfLive(re, caps, lk, qt)[g].endIdx.Some?;
      assert AI.get_idx(f, CP.end_reg(g)) == f[2 * g + 1];
    }
    PIV.GmOfCapArrayBridge(re, caps, lk, qt, inp, ngroups);
    assert LES.NormalizeArr(f) == LES.CapArrayOfLeaf((inp, PIV.GmOf(re, caps, lk, qt)), ngroups);
    assert LES.CapArrayOfLeaf((inp, PIV.GmOf(re, caps, lk, qt)), ngroups)
        == LES.CapArrayOfLeaf(leaf, ngroups);

    // the lazy prefix is filter-transparent
    assert AI.get_idx(qt.a_clk, 0) >= -1;         // QuantRegsFinal
    FilterResetLazyPrefix(ast, caps, lk, qt);
    assert AI.filter_reset(ast, caps, lk, qt, -1) == f;

    assert LES.Normalize(AI.FFullMatch(raw, str)) == Some(LES.NormalizeArr(f));
    assert LES.MatcherSpec(raw, str, Some(LES.CapArrayOfLeaf(leaf, ngroups)));
  }

  /** `FConsume` (moving matched blocked threads to active for the next
      position) preserves `VmQuantFinal`. */
  lemma FConsumeQuantFinal(s: AI.VmState)
    requires VmQuantFinal(s)
    ensures VmQuantFinal(AI.FConsume(s))
    decreases |s.blocked|
  {
    if |s.blocked| == 0 { return; }
    var t := s.blocked[0].0;
    var ce := s.blocked[0].1;
    var s1 := s.(blocked := s.blocked[1..]);
    assert s.blocked[0] in s.blocked;
    assert forall x | x in s1.blocked :: x in s.blocked;
    var s2 := if RC.is_accepted(s1.context.nextchar, ce)
              then s1.(active := [t.(exit_allowed := true, pc := t.pc + 1)] + s1.active)
              else s1;
    assert VmQuantFinal(s2) by {
      forall t2 | t2 in s2.active ensures QuantRegsFinal(t2) {
        if t2 != t.(exit_allowed := true, pc := t.pc + 1) { assert t2 in s.active; }
        else { assert QuantRegsFinal(t); }
      }
      forall tb | tb in s2.blocked ensures QuantRegsFinal(tb.0) {
        assert tb in s.blocked;
      }
    }
    FConsumeQuantFinal(s2);
  }
}
