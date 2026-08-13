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
  import TM = LindenTreeMirror        // L3b: spec-tree backward<->forward mirror
  import TRM = LindenTreeResMirror    // L3b: leaf-groupmap mirror (TreeResMirror)
  import CDE = LindenCloseDisc        // L3b: CloseDisc + NoDupG + CloseDiscBody
  import LL = LindenElkLookLeaves
  import OE = LindenElkOracleEntry
  import OS = LindenElkOracleSpec
  import T = LindenElkTranslate
  import RD = LindenElkReduce
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
  import FU = FunctionalUtils
  import TR = LindenElkTreeRep
  import TT = LindenElkTreeThread
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

  // ==========================================================================
  // Item 0 support: every CLOSED range in a spec leaf is ORDERED (start <= end).
  // `GMClose` always normalizes min/max, `GMOpen` records an OPEN range, `GMReset`
  // removes — so ordering is a LOCAL per-range property preserved compositionally
  // by every `TreeRes` step (including the LK-node merge, which just continues at
  // the sub-run's ordered result). Used at `MainExtraction` to discharge the
  // widened `NormalizeArr`'s "no reversed pairs" side condition for the FORWARD
  // fragment (a lookbehind-owned group's engine spans are reversed; the spec leaf
  // stays ordered because `GMClose` orders regardless of scan direction).
  // ==========================================================================

  /** Every closed range in `gm` is ordered (`startIdx <= endIdx.value`). */
  ghost predicate OrderedGm(gm: LG.GroupMap) {
    forall g :: g in gm && gm[g].endIdx.Some? ==> gm[g].startIdx <= gm[g].endIdx.value
  }

  /** `GMUpdate` preserves `OrderedGm`: `GMOpen` records an open range, `GMClose`
      normalizes to `min <= max`, `GMReset` removes. */
  lemma GMUpdateOrdered(a: LG.GroupAction, idx: nat, gm: LG.GroupMap)
    requires OrderedGm(gm)
    ensures OrderedGm(LG.GMUpdate(a, idx, gm))
  {
    match a
    case Open(g) =>
    case Close(g) =>
      forall g' | g' in LG.GMClose(idx, g, gm) && LG.GMClose(idx, g, gm)[g'].endIdx.Some?
        ensures LG.GMClose(idx, g, gm)[g'].startIdx <= LG.GMClose(idx, g, gm)[g'].endIdx.value
      {
        if g' == g {
          match LG.Find(g, gm) case Some(rg) => case None => {}
        }
      }
    case Reset(gs) =>
  }

  /** A spec `TreeRes` from an ordered gm lands (on a match) at an ordered leaf gm.
      Structural induction; the LK node just continues at the (recursively ordered)
      sub-run result. */
  lemma TreeResOrdered(t: LT.Tree, gm: LG.GroupMap, inp: LC.Input, dir: WP.Direction)
    requires OrderedGm(gm)
    ensures LT.TreeRes(t, gm, inp, dir).Some? ==> OrderedGm(LT.TreeRes(t, gm, inp, dir).value.1)
    decreases t
  {
    match t
    case Mismatch =>
    case Match =>
    case Choice(t1, t2) =>
      TreeResOrdered(t1, gm, inp, dir);
      TreeResOrdered(t2, gm, inp, dir);
    case Read(c, t1) =>
      TreeResOrdered(t1, gm, LC.AdvanceInputP(inp, dir), dir);
    case ReadBackRef(brStr, t1) =>
      TreeResOrdered(t1, gm, LC.AdvanceInputN(inp, |brStr|, dir), dir);
    case Progress(t1) =>
      TreeResOrdered(t1, gm, inp, dir);
    case AnchorPass(a, t1) =>
      TreeResOrdered(t1, gm, inp, dir);
    case GroupActionT(a, t1) =>
      GMUpdateOrdered(a, LC.Idx(inp), gm);
      TreeResOrdered(t1, LG.GMUpdate(a, LC.Idx(inp), gm), inp, dir);
    case LK(lk, tlk, t1) =>
      if L.Positivity(lk) {
        TreeResOrdered(tlk, gm, inp, L.LkDir(lk));
        match LT.TreeRes(tlk, gm, inp, L.LkDir(lk))
        case None =>
        case Some(pair) => TreeResOrdered(t1, pair.1, inp, dir);
      } else {
        match LT.TreeRes(tlk, gm, inp, L.LkDir(lk))
        case None => TreeResOrdered(t1, gm, inp, dir);
        case Some(_) =>
      }
    case LKFail(_, _) =>
  }

  /** The spec first leaf has all ordered ranges (folded from `LG.Empty`). */
  lemma FirstLeafOrdered(t: LT.Tree, inp: LC.Input, leaf: LT.Leaf)
    requires LT.FirstLeaf(t, inp) == Some(leaf)
    ensures OrderedGm(leaf.1)
  {
    assert OrderedGm(LG.Empty);
    TreeResOrdered(t, LG.Empty, inp, WP.Forward);
  }

  // ==========================================================================
  // L3a: inside-look-group bookkeeping for FirstLeafClosed. A capturing lookahead
  // body records CLOSED captures into the continuation's map; the disjointness
  // invariant `DomLkDisjoint` (dom(gm) misses the still-pending inside-look
  // groups) lets the LK case relate the body-from-gm computation to a
  // body-from-Empty computation on the body's own groups.
  // ==========================================================================

  /** The inside-look groups of every regex still pending in `acts`. */
  ghost function LkBodyGroupsActs(acts: LS.Actions): set<LG.GroupId>
    decreases |acts|
  {
    if |acts| == 0 then {}
    else (if acts[0].Areg? then LL.LkBodyGroups(acts[0].r) else {}) + LkBodyGroupsActs(acts[1..])
  }

  /** All group ids DEFINED across `acts`, in order — for the uniqueness invariant. */
  ghost function AllDefsActs(acts: LS.Actions): seq<LG.GroupId>
    decreases |acts|
  {
    if |acts| == 0 then []
    else (if acts[0].Areg? then L.DefGroups(acts[0].r) else []) + AllDefsActs(acts[1..])
  }

  ghost predicate NoDupSeq(s: seq<LG.GroupId>) { forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j] }

  /** dom(gm) is disjoint from the inside-look groups still pending in `acts`. */
  ghost predicate DomLkDisjoint(gm: LG.GroupMap, acts: LS.Actions) {
    forall g :: g in gm ==> g !in LkBodyGroupsActs(acts)
  }

  /** L3a (quantifier-stable): every pending inside-look group already present in
      `gm` is CLOSED. (A quantified capturing look re-enters its own body groups;
      each iteration records them CLOSED, so this holds where plain disjointness
      would fail.) */
  ghost predicate LkClosedInGm(gm: LG.GroupMap, acts: LS.Actions) {
    forall g :: g in gm && g in LkBodyGroupsActs(acts) ==> gm[g].endIdx.Some?
  }

  /** Groups defined OUTSIDE lookaround bodies of `r` (a `Group` at this level, not
      the body of a look). Disjoint from `LkBodyGroups` for a unique-id regex. */
  ghost function DefGroupsOutsideLooksL(r: L.Regex): set<LG.GroupId>
    decreases r
  {
    match r
    case Disjunction(r1, r2) => DefGroupsOutsideLooksL(r1) + DefGroupsOutsideLooksL(r2)
    case Sequence(r1, r2) => DefGroupsOutsideLooksL(r1) + DefGroupsOutsideLooksL(r2)
    case Quantified(_, _, _, r1) => DefGroupsOutsideLooksL(r1)
    case Group(id, r1) => {id} + DefGroupsOutsideLooksL(r1)
    case LookaroundR(_, _) => {}
    case _ => {}
  }

  ghost function OuterDefsActs(acts: LS.Actions): set<LG.GroupId>
    decreases |acts|
  {
    if |acts| == 0 then {}
    else (if acts[0].Areg? then DefGroupsOutsideLooksL(acts[0].r) else (if acts[0].Aclose? then {acts[0].gid} else {}))
         + OuterDefsActs(acts[1..])
  }

  /** The openable (outer) groups are disjoint from the inside-look groups — the
      quantifier-stable replacement for `NoDupSeq(AllDefsActs)`. */
  ghost predicate OuterLkDisjoint(acts: LS.Actions) {
    OuterDefsActs(acts) * LkBodyGroupsActs(acts) == {}
  }

  lemma OuterDefsActsCons(x: LS.Action, cont: LS.Actions)
    ensures OuterDefsActs([x] + cont) == (if x.Areg? then DefGroupsOutsideLooksL(x.r) else (if x.Aclose? then {x.gid} else {})) + OuterDefsActs(cont)
  { assert ([x] + cont)[0] == x && ([x] + cont)[1..] == cont; }

  /** `DefGroups` no-dup ⇒ a group is not both outside a look and inside one. */
  lemma OuterLkFromNoDup(r: L.Regex)
    requires NoDupSeq(L.DefGroups(r))
    ensures DefGroupsOutsideLooksL(r) * LL.LkBodyGroups(r) == {}
    decreases r
  {
    match r
    case Disjunction(r1, r2) =>
      NoDupConcat(L.DefGroups(r1), L.DefGroups(r2)); OuterLkFromNoDup(r1); OuterLkFromNoDup(r2);
      LkBodyGroupsSubDefs(r1); LkBodyGroupsSubDefs(r2); DefGroupsOutsideSubDefs(r1); DefGroupsOutsideSubDefs(r2);
    case Sequence(r1, r2) =>
      NoDupConcat(L.DefGroups(r1), L.DefGroups(r2)); OuterLkFromNoDup(r1); OuterLkFromNoDup(r2);
      LkBodyGroupsSubDefs(r1); LkBodyGroupsSubDefs(r2); DefGroupsOutsideSubDefs(r1); DefGroupsOutsideSubDefs(r2);
    case Quantified(_, _, _, r1) => OuterLkFromNoDup(r1);
    case Group(id, r1) =>
      assert L.DefGroups(r) == [id] + L.DefGroups(r1);
      NoDupConcat([id], L.DefGroups(r1)); OuterLkFromNoDup(r1); LkBodyGroupsSubDefs(r1);
    case LookaroundR(_, r1) =>
    case _ =>
  }

  /** Reverse of `NoDupConcat`: two individually dup-free, elementwise-disjoint
      sequences concatenate to a dup-free sequence. Disjointness is phrased on
      indices (`a[i] != b[j]`) so the quantifier has a syntactic trigger. */
  lemma NoDupFromDisjoint(a: seq<LG.GroupId>, b: seq<LG.GroupId>)
    requires NoDupSeq(a) && NoDupSeq(b)
    requires forall i, j :: 0 <= i < |a| && 0 <= j < |b| ==> a[i] != b[j]
    ensures NoDupSeq(a + b)
  {
    forall i, j | 0 <= i < j < |a + b| ensures (a + b)[i] != (a + b)[j] {
      if j < |a| {
        assert (a + b)[i] == a[i] && (a + b)[j] == a[j];
      } else if i >= |a| {
        assert (a + b)[i] == b[i - |a|] && (a + b)[j] == b[j - |a|];
      } else {
        assert (a + b)[i] == a[i] && (a + b)[j] == b[j - |a|];
      }
    }
  }

  /** Prepending a fresh id `x` (not in `b`) to a dup-free `b` stays dup-free. */
  lemma NoDupPrepend(x: LG.GroupId, b: seq<LG.GroupId>)
    requires NoDupSeq(b)
    requires forall j :: 0 <= j < |b| ==> b[j] != x
    ensures NoDupSeq([x] + b)
  {
    forall i, j | 0 <= i < j < |[x] + b| ensures ([x] + b)[i] != ([x] + b)[j] {
      if i == 0 {
        assert ([x] + b)[i] == x && ([x] + b)[j] == b[j - 1];
      } else {
        assert ([x] + b)[i] == b[i - 1] && ([x] + b)[j] == b[j - 1];
      }
    }
  }

  /** The annotate/translate output has NO DUPLICATE group ids: each syntactic
      capture gets a fresh id from the monotone counter `c`. Proven by mirroring
      `RD.TA`'s structure; disjointness of sibling group ranges comes from
      `TA_DefGroups` (range) + `TA_Counters` (counter advance). */
  lemma TA_NoDup(ra: R.raw_regex, c: int, l: int, q: int)
    requires T.Latin1Wf(ra) && c >= 0
    ensures NoDupSeq(L.DefGroups(RD.TA(ra, c, l, q).0))
    decreases ra
  {
    match ra
    case Raw_empty => RD.TA_Empty(c, l, q);
    case Raw_character(ch) => RD.TA_Char(ch, c, l, q);
    case Raw_anchor(a) => RD.TA_Anchor(a, c, l, q);
    case Raw_alt(r1, r2) =>
      RD.TA_Alt(r1, r2, c, l, q);
      var (e1, c1, l1, q1) := RD.TA(r1, c, l, q);
      var (e2, c2, l2, q2) := RD.TA(r2, c1, l1, q1);
      assert L.DefGroups(RD.TA(ra, c, l, q).0) == L.DefGroups(e1) + L.DefGroups(e2);
      TA_NoDup(r1, c, l, q); TA_NoDup(r2, c1, l1, q1);
      RD.TA_Counters(r1, c, l, q);
      forall i, j | 0 <= i < |L.DefGroups(e1)| && 0 <= j < |L.DefGroups(e2)|
        ensures L.DefGroups(e1)[i] != L.DefGroups(e2)[j] {
        RD.TA_DefGroups(r1, c, l, q, L.DefGroups(e1)[i]);
        RD.TA_DefGroups(r2, c1, l1, q1, L.DefGroups(e2)[j]);
      }
      NoDupFromDisjoint(L.DefGroups(e1), L.DefGroups(e2));
    case Raw_con(r1, r2) =>
      RD.TA_Con(r1, r2, c, l, q);
      var (e1, c1, l1, q1) := RD.TA(r1, c, l, q);
      var (e2, c2, l2, q2) := RD.TA(r2, c1, l1, q1);
      assert L.DefGroups(RD.TA(ra, c, l, q).0) == L.DefGroups(e1) + L.DefGroups(e2);
      TA_NoDup(r1, c, l, q); TA_NoDup(r2, c1, l1, q1);
      RD.TA_Counters(r1, c, l, q);
      forall i, j | 0 <= i < |L.DefGroups(e1)| && 0 <= j < |L.DefGroups(e2)|
        ensures L.DefGroups(e1)[i] != L.DefGroups(e2)[j] {
        RD.TA_DefGroups(r1, c, l, q, L.DefGroups(e1)[i]);
        RD.TA_DefGroups(r2, c1, l1, q1, L.DefGroups(e2)[j]);
      }
      NoDupFromDisjoint(L.DefGroups(e1), L.DefGroups(e2));
    case Raw_quant(qk, r1) =>
      RD.TA_Quant(qk, r1, c, l, q);
      var (e1, c1, l1, q1) := RD.TA(r1, c, l, q + 1);
      assert L.DefGroups(RD.TA(ra, c, l, q).0) == L.DefGroups(e1);
      TA_NoDup(r1, c, l, q + 1);
    case Raw_count(cq, r1) =>
      RD.TA_Count(cq, r1, c, l, q);
      var (e1, c1, l1, q1) := RD.TA(r1, c, l, q + 1);
      assert L.DefGroups(RD.TA(ra, c, l, q).0) == L.DefGroups(e1);
      TA_NoDup(r1, c, l, q + 1);
    case Raw_capture(r1) =>
      RD.TA_Cap(r1, c, l, q);
      var (e1, c1, l1, q1) := RD.TA(r1, c + 1, l, q);
      assert L.DefGroups(RD.TA(ra, c, l, q).0) == [c as nat] + L.DefGroups(e1);
      TA_NoDup(r1, c + 1, l, q);
      forall j | 0 <= j < |L.DefGroups(e1)| ensures L.DefGroups(e1)[j] != c as nat {
        RD.TA_DefGroups(r1, c + 1, l, q, L.DefGroups(e1)[j]);   // e1[j] >= c+1 > c
      }
      NoDupPrepend(c as nat, L.DefGroups(e1));
    case Raw_lookaround(lk, r1) =>
      RD.TA_Look(lk, r1, c, l, q);
      var (e1, c1, l1, q1) := RD.TA(r1, c, l + 1, q);
      assert L.DefGroups(RD.TA(ra, c, l, q).0) == L.DefGroups(e1);
      TA_NoDup(r1, c, l + 1, q);
  }

  /** The top-level discharge: the whole translated regex satisfies the
      `OuterLkDisjoint` action invariant, because its group ids are unique. */
  lemma SpecRegexOuterLkDisjoint(raw: R.raw_regex)
    requires T.Latin1Wf(raw)
    ensures OuterLkDisjoint([LS.Areg(LES.SpecRegex(raw))])
    ensures NoDupSeq(L.DefGroups(LES.SpecRegex(raw)))
  {
    var body := RD.TA(raw, 1, 1, 1).0;
    RD.SpecRegexE(raw, body);
    var spec := LES.SpecRegex(raw);
    // spec == .*? ++ Group(0, body); the prefix defines no groups.
    assert L.DefGroups(spec) == [0] + L.DefGroups(body);
    TA_NoDup(raw, 1, 1, 1);
    forall j | 0 <= j < |L.DefGroups(body)| ensures L.DefGroups(body)[j] != 0 {
      RD.TA_DefGroups(raw, 1, 1, 1, L.DefGroups(body)[j]);   // body groups >= 1 > 0
    }
    NoDupPrepend(0, L.DefGroups(body));
    OuterLkFromNoDup(spec);
    LkBodyGroupsActsCons(LS.Areg(spec), []);
    OuterDefsActsCons(LS.Areg(spec), []);
    assert LkBodyGroupsActs([LS.Areg(spec)]) == LL.LkBodyGroups(spec);
    assert OuterDefsActs([LS.Areg(spec)]) == DefGroupsOutsideLooksL(spec);
  }

  /** `NoLkBrL` (look-/backref-free) ⇒ `PikeLkRegex` (the fragment is trivially met). */
  lemma NoLkBrImpliesPikeLk(r: L.Regex)
    requires EL.NoLkBrL(r)
    ensures EL.PikeLkRegex(r)
    decreases r
  {
    match r
    case Disjunction(r1, r2) => NoLkBrImpliesPikeLk(r1); NoLkBrImpliesPikeLk(r2);
    case Sequence(r1, r2) => NoLkBrImpliesPikeLk(r1); NoLkBrImpliesPikeLk(r2);
    case Quantified(_, _, _, r1) => NoLkBrImpliesPikeLk(r1);
    case Group(_, r1) => NoLkBrImpliesPikeLk(r1);
    case _ =>
  }

  /** `GroupFreeL` (no groups/looks/backrefs) ⇒ `NoLkBrL`. */
  lemma GroupFreeImpliesNoLkBr(r: L.Regex)
    requires SD.GroupFreeL(r)
    ensures EL.NoLkBrL(r)
    decreases r
  {
    match r
    case Disjunction(r1, r2) => GroupFreeImpliesNoLkBr(r1); GroupFreeImpliesNoLkBr(r2);
    case Sequence(r1, r2) => GroupFreeImpliesNoLkBr(r1); GroupFreeImpliesNoLkBr(r2);
    case Quantified(_, _, _, r1) => GroupFreeImpliesNoLkBr(r1);
    case _ =>
  }

  /** `DefGroupsOutsideLooksL ⊆ DefGroups`. */
  lemma DefGroupsOutsideSubDefs(r: L.Regex)
    ensures DefGroupsOutsideLooksL(r) <= (set g | g in L.DefGroups(r))
    decreases r
  {
    match r
    case Disjunction(r1, r2) => DefGroupsOutsideSubDefs(r1); DefGroupsOutsideSubDefs(r2);
    case Sequence(r1, r2) => DefGroupsOutsideSubDefs(r1); DefGroupsOutsideSubDefs(r2);
    case Quantified(_, _, _, r1) => DefGroupsOutsideSubDefs(r1);
    case Group(_, r1) => DefGroupsOutsideSubDefs(r1);
    case _ =>
  }

  /** Every defined group is EITHER outside every look OR inside some look body —
      the `DefGroups` split (`OuterLkFromNoDup` gives disjointness; this gives
      cover). Needed by the S-ii quant reset case. */
  lemma DefGroupsInLkOrOutside(r: L.Regex)
    ensures forall g :: g in L.DefGroups(r) ==> g in DefGroupsOutsideLooksL(r) || g in LL.LkBodyGroups(r)
    decreases r
  {
    match r
    case Disjunction(r1, r2) => DefGroupsInLkOrOutside(r1); DefGroupsInLkOrOutside(r2);
    case Sequence(r1, r2) => DefGroupsInLkOrOutside(r1); DefGroupsInLkOrOutside(r2);
    case Quantified(_, _, _, r1) => DefGroupsInLkOrOutside(r1);
    case Group(id, r1) => DefGroupsInLkOrOutside(r1);
    case LookaroundR(lk, r1) =>
      // DefGroups(LookaroundR) == DefGroups(r1) <= set(DefGroups(r1)) <= LkBodyGroups(LookaroundR)
    case _ =>
  }

  /** S-ii: a SETTLED inside-look `S`-group (present-worthy, look no longer pending)
      is NOT in a pending quantifier body's `DefGroups` — else it would be an inside-
      look group of that body, hence still pending. So the `GMReset` never touches it. */
  lemma QuantSettledNotReset(r: L.Regex, r1: L.Regex, cont: LS.Actions, acts: LS.Actions,
                             S: set<LG.GroupId>, g: LG.GroupId)
    requires r.Quantified? && r.r1 == r1 && acts == [LS.Areg(r)] + cont
    requires forall g': LG.GroupId :: g' in S ==> g' !in OuterDefsActs(acts)
    requires g in S && g !in LkBodyGroupsActs(acts)
    ensures g !in L.DefGroups(r1)
  {
    if g in L.DefGroups(r1) {
      DefGroupsInLkOrOutside(r1);
      LkBodyGroupsActsCons(LS.Areg(r), cont);
      OuterDefsActsCons(LS.Areg(r), cont);
      assert DefGroupsOutsideLooksL(r) == DefGroupsOutsideLooksL(r1);   // r == Quantified(..,r1)
      assert LL.LkBodyGroups(r) == LL.LkBodyGroups(r1);
      // g in DefGroupsOutsideLooksL(r1) <= OuterDefsActs(acts): contradicts g in S;
      // g in LkBodyGroups(r1) <= LkBodyGroupsActs(acts): contradicts g !in LkBodyGroupsActs(acts).
    }
  }

  lemma LkBodyGroupsActsCons(x: LS.Action, cont: LS.Actions)
    ensures LkBodyGroupsActs([x] + cont) == (if x.Areg? then LL.LkBodyGroups(x.r) else {}) + LkBodyGroupsActs(cont)
  { assert ([x] + cont)[0] == x && ([x] + cont)[1..] == cont; }

  /** `NoDupSeq` is preserved on any suffix / removing a prefix. */
  lemma NoDupTailSeq(a: seq<LG.GroupId>, b: seq<LG.GroupId>)
    requires NoDupSeq(a + b)
    ensures NoDupSeq(b)
  { forall i, j | 0 <= i < j < |b| ensures b[i] != b[j] { assert (a + b)[|a| + i] == b[i] && (a + b)[|a| + j] == b[j]; } }

  /** Dropping a middle chunk `b` preserves `NoDupSeq` (a+c ⊆ a+b+c, order kept). */
  lemma NoDupMid(a: seq<LG.GroupId>, b: seq<LG.GroupId>, c: seq<LG.GroupId>)
    requires NoDupSeq(a + b + c)
    ensures NoDupSeq(a + c)
  {
    forall i, j | 0 <= i < j < |a + c| ensures (a + c)[i] != (a + c)[j] {
      var s := a + b + c;
      var i' := if i < |a| then i else i + |b|;
      var j' := if j < |a| then j else j + |b|;
      assert (a + c)[i] == s[i'] && (a + c)[j] == s[j'] && i' < j';
    }
  }

  /** The invariant threads to the tail `cont` (with `gm` unchanged or domain-
      shrunk): the head action contributes ⊇{} to `LkBodyGroupsActs` and a prefix
      to `AllDefsActs`, both of which only shrink the constraint. */
  lemma TailInv(gm: LG.GroupMap, gm2: LG.GroupMap, acts: LS.Actions)
    requires |acts| > 0
    requires LkClosedInGm(gm, acts) && OuterLkDisjoint(acts)
    requires forall g :: g in gm2 ==> g in gm && (gm2[g].endIdx.Some? || gm2[g] == gm[g])
    ensures LkClosedInGm(gm2, acts[1..]) && OuterLkDisjoint(acts[1..])
  {
    var cont := acts[1..];
    assert acts == [acts[0]] + cont;
    LkBodyGroupsActsCons(acts[0], cont);
    OuterDefsActsCons(acts[0], cont);
  }

  /** The invariant threads to a rewritten action list `sub` whose look groups and
      outer defs are contained in `acts`' (the Disjunction/Sequence/Quantified
      rewrites). `gm2` groups are in `gm`, closed or unchanged. */
  lemma SubInv(gm: LG.GroupMap, gm2: LG.GroupMap, sub: LS.Actions, acts: LS.Actions)
    requires LkClosedInGm(gm, acts) && OuterLkDisjoint(acts)
    requires LkBodyGroupsActs(sub) <= LkBodyGroupsActs(acts)
    requires OuterDefsActs(sub) <= OuterDefsActs(acts)
    requires forall g :: g in gm2 ==> g in gm && (gm2[g].endIdx.Some? || gm2[g] == gm[g])
    ensures LkClosedInGm(gm2, sub) && OuterLkDisjoint(sub)
  {}

  /** Threading for the quantifier rewrite `[Areg(q)]+cont ⤳ [Areg(r1),Areg(q')]+
      cont`, where `q`,`q'` are quantifiers over `r1` (same look/outer groups). */
  lemma QuantSubInv(gm: LG.GroupMap, gm2: LG.GroupMap, r: L.Regex, r1: L.Regex, q': L.Regex,
                    cont: LS.Actions, acts: LS.Actions, acts1: LS.Actions)
    requires acts == [LS.Areg(r)] + cont && acts1 == [LS.Areg(r1), LS.Areg(q')] + cont
    requires LL.LkBodyGroups(r) == LL.LkBodyGroups(r1) && LL.LkBodyGroups(q') == LL.LkBodyGroups(r1)
    requires DefGroupsOutsideLooksL(r) == DefGroupsOutsideLooksL(r1) && DefGroupsOutsideLooksL(q') == DefGroupsOutsideLooksL(r1)
    requires LkClosedInGm(gm, acts) && OuterLkDisjoint(acts)
    requires forall g :: g in gm2 ==> g in gm && (gm2[g].endIdx.Some? || gm2[g] == gm[g])
    ensures LkClosedInGm(gm2, acts1) && OuterLkDisjoint(acts1)
  {
    assert acts1 == [LS.Areg(r1)] + ([LS.Areg(q')] + cont);
    LkBodyGroupsActsCons(LS.Areg(r), cont); LkBodyGroupsActsCons(LS.Areg(r1), [LS.Areg(q')] + cont); LkBodyGroupsActsCons(LS.Areg(q'), cont);
    OuterDefsActsCons(LS.Areg(r), cont); OuterDefsActsCons(LS.Areg(r1), [LS.Areg(q')] + cont); OuterDefsActsCons(LS.Areg(q'), cont);
    SubInv(gm, gm2, acts1, acts);
  }

  /** Threading for the delta-else quantifier rewrite `[Areg(q)]+cont ⤳
      [Areg(r1),Acheck,Areg(q'')]+cont`. `Acheck` carries no groups. */
  lemma QuantSubInvCheck(gm: LG.GroupMap, gm2: LG.GroupMap, r: L.Regex, r1: L.Regex, q'': L.Regex,
                         inp: LC.Input, cont: LS.Actions, acts: LS.Actions, acts1: LS.Actions)
    requires acts == [LS.Areg(r)] + cont && acts1 == [LS.Areg(r1), LS.Acheck(inp), LS.Areg(q'')] + cont
    requires LL.LkBodyGroups(r) == LL.LkBodyGroups(r1) && LL.LkBodyGroups(q'') == LL.LkBodyGroups(r1)
    requires DefGroupsOutsideLooksL(r) == DefGroupsOutsideLooksL(r1) && DefGroupsOutsideLooksL(q'') == DefGroupsOutsideLooksL(r1)
    requires LkClosedInGm(gm, acts) && OuterLkDisjoint(acts)
    requires forall g :: g in gm2 ==> g in gm && (gm2[g].endIdx.Some? || gm2[g] == gm[g])
    ensures LkClosedInGm(gm2, acts1) && OuterLkDisjoint(acts1)
  {
    assert acts1 == [LS.Areg(r1)] + ([LS.Acheck(inp)] + ([LS.Areg(q'')] + cont));
    LkBodyGroupsActsCons(LS.Areg(r), cont);
    LkBodyGroupsActsCons(LS.Areg(r1), [LS.Acheck(inp)] + ([LS.Areg(q'')] + cont));
    LkBodyGroupsActsCons(LS.Acheck(inp), [LS.Areg(q'')] + cont);
    LkBodyGroupsActsCons(LS.Areg(q''), cont);
    OuterDefsActsCons(LS.Areg(r), cont);
    OuterDefsActsCons(LS.Areg(r1), [LS.Acheck(inp)] + ([LS.Areg(q'')] + cont));
    OuterDefsActsCons(LS.Acheck(inp), [LS.Areg(q'')] + cont);
    OuterDefsActsCons(LS.Areg(q''), cont);
    SubInv(gm, gm2, acts1, acts);
  }

  lemma AllDefsActsCons(x: LS.Action, cont: LS.Actions)
    ensures AllDefsActs([x] + cont) == (if x.Areg? then L.DefGroups(x.r) else []) + AllDefsActs(cont)
  { assert ([x] + cont)[0] == x && ([x] + cont)[1..] == cont; }

  /** Inside-look groups of `r` are a subset of ALL its defined groups. */
  lemma LkBodyGroupsSubDefs(r: L.Regex)
    ensures LL.LkBodyGroups(r) <= (set g | g in L.DefGroups(r))
    decreases r
  {
    match r
    case Disjunction(r1, r2) => LkBodyGroupsSubDefs(r1); LkBodyGroupsSubDefs(r2);
    case Sequence(r1, r2) => LkBodyGroupsSubDefs(r1); LkBodyGroupsSubDefs(r2);
    case Quantified(_, _, _, r1) => LkBodyGroupsSubDefs(r1);
    case Group(_, r1) => LkBodyGroupsSubDefs(r1);
    case LookaroundR(_, r1) => LkBodyGroupsSubDefs(r1);
    case _ =>
  }

  /** The action-level lift: pending inside-look groups ⊆ all defined groups. */
  lemma LkBodyGroupsActsSubAllDefs(acts: LS.Actions)
    ensures LkBodyGroupsActs(acts) <= (set g | g in AllDefsActs(acts))
    decreases |acts|
  {
    if |acts| == 0 { return; }
    LkBodyGroupsActsSubAllDefs(acts[1..]);
    if acts[0].Areg? { LkBodyGroupsSubDefs(acts[0].r); }
  }

  /** `NoDupSeq` splits over concatenation: the two halves are individually
      duplicate-free AND element-disjoint. */
  lemma NoDupConcat(a: seq<LG.GroupId>, b: seq<LG.GroupId>)
    requires NoDupSeq(a + b)
    ensures NoDupSeq(a) && NoDupSeq(b) && (set g | g in a) * (set g | g in b) == {}
  {
    forall i, j | 0 <= i < j < |a| ensures a[i] != a[j] { assert (a + b)[i] == a[i] && (a + b)[j] == a[j]; }
    forall i, j | 0 <= i < j < |b| ensures b[i] != b[j] { assert (a + b)[|a| + i] == b[i] && (a + b)[|a| + j] == b[j]; }
    if (set g | g in a) * (set g | g in b) != {} {
      var g :| g in (set g | g in a) && g in (set g | g in b);
      var i :| 0 <= i < |a| && a[i] == g;
      var j :| 0 <= j < |b| && b[j] == g;
      assert (a + b)[i] == g && (a + b)[|a| + j] == g && i < |a| + j;   // contradicts NoDupSeq(a + b)
    }
  }

  /** The `GroupMap` of a `Match` leaf is always fully closed: whenever a
      tree's open groups are all covered by pending `Aclose` actions, its
      highest-priority leaf (`TreeRes`) leaves no group open. Grounds both
      `GmOfLiveEqGmOf`'s and `GmOfCapArrayBridge`'s hypotheses at the winning
      thread. */
  /** All `Areg` regexes in `acts` are look-free (and backref-free). */
  ghost predicate NoLkActs(acts: LS.Actions) {
    forall i :: 0 <= i < |acts| ==> (acts[i].Areg? ==> EL.NoLkBrL(acts[i].r))
  }

  /** Every `Areg` regex in `acts` has DUPLICATE-FREE defined groups. This is the
      per-regex (quantifier-STABLE) form of no-dup: a quantifier unfold
      `[Areg(r1),Areg(q')]` repeats `DefGroups(r1)`, so `NoDupSeq(AllDefsActs)`
      would be FALSE, but the per-regex property survives (both copies have the
      same, dup-free, `DefGroups(r1)`). Feeds `NoDupG(DefGroups(r1))` at each
      look body via `NoDupSeqIsNoDupG`. Same shape/threading as `NoLkActs`. */
  ghost predicate NoDupRegsActs(acts: LS.Actions) {
    forall i :: 0 <= i < |acts| ==> (acts[i].Areg? ==> NoDupSeq(L.DefGroups(acts[i].r)))
  }

  /** `FirstLeafClosed` restricted to LOOK-FREE actions: the LK case is
      unreachable, so this is a self-contained least lemma with no inside-look
      bookkeeping. `LookBodyLeafOpenSub` uses it on the (look-free) look body,
      which is why the main `FirstLeafClosed` LK case can reuse the balance
      without a least-lemma cycle. */
  least lemma FirstLeafClosedNoLk(rer: LW.RegExpRecord, acts: LS.Actions, inp: LC.Input,
                                  b: BS.LoopBool, t: LT.Tree, gm: LG.GroupMap, leaf: LT.Leaf)
    requires EL.BoolTreeLk(rer, acts, inp, b, t)
    requires EL.PikeLkActions(acts)
    requires NoLkActs(acts)
    requires OpenOf(gm) <= PendingCloses(acts)
    requires LT.TreeRes(t, gm, inp, WP.Forward) == Some(leaf)
    ensures ClosedGm(leaf.1)
  {
    if |acts| == 0 {
      assert t == LT.Match;
      assert leaf.1 == gm;
      forall g | g in gm ensures gm[g].endIdx.Some? { if gm[g].endIdx.None? { assert g in OpenOf(gm); } }
    } else {
      var cont := acts[1..];
      assert NoLkActs(cont) by { forall i | 0 <= i < |cont| ensures cont[i].Areg? ==> EL.NoLkBrL(cont[i].r) { assert cont[i] == acts[i + 1]; } }
      assert PendingCloses(cont) <= PendingCloses(acts);
      match acts[0]
      case Acheck(strcheck) =>
        if b == BS.CanExit { assert PendingCloses(acts) == PendingCloses(cont); FirstLeafClosedNoLk(rer, cont, inp, BS.CanExit, t.t, gm, leaf); }
        else { assert t == LT.Mismatch; assert false; }
      case Aclose(gid) =>
        var gm2 := LG.GMUpdate(t.g, LC.Idx(inp), gm);
        assert gm2 == LG.GMClose(LC.Idx(inp), gid, gm);
        assert OpenOf(gm2) <= PendingCloses(cont) by {
          forall g | g in OpenOf(gm2) ensures g in PendingCloses(cont) {
            assert g != gid; assert g in OpenOf(gm); assert g in PendingCloses(acts);
            var i :| 0 <= i < |acts| && acts[i].Aclose? && acts[i].gid == g;
            assert i != 0; assert cont[i - 1] == acts[i];
          }
        }
        FirstLeafClosedNoLk(rer, cont, inp, b, t.t, gm2, leaf);
      case Areg(r) =>
        assert EL.NoLkBrL(r);
        match r
        case Epsilon => assert PendingCloses(acts) == PendingCloses(cont); FirstLeafClosedNoLk(rer, cont, inp, b, t, gm, leaf);
        case Character(cd) =>
          if LC.ReadChar(rer, cd, inp, WP.Forward).None? { assert t == LT.Mismatch; assert false; }
          else {
            var pair := LC.ReadChar(rer, cd, inp, WP.Forward).value;
            assert PendingCloses(acts) == PendingCloses(cont);
            FirstLeafClosedNoLk(rer, cont, pair.1, BS.CanExit, t.t, gm, leaf);
          }
        case Disjunction(r1, r2) =>
          var acts1 := [LS.Areg(r1)] + cont; var acts2 := [LS.Areg(r2)] + cont;
          assert PendingCloses(acts1) == PendingCloses(cont) == PendingCloses(acts2) by { assert forall i :: 0 <= i < |cont| ==> acts1[i + 1] == cont[i] && acts2[i + 1] == cont[i]; }
          assert NoLkActs(acts1) && NoLkActs(acts2) by {
            forall i | 0 <= i < |acts1| ensures acts1[i].Areg? ==> EL.NoLkBrL(acts1[i].r) { if i == 0 {} else { assert acts1[i] == cont[i - 1]; } }
            forall i | 0 <= i < |acts2| ensures acts2[i].Areg? ==> EL.NoLkBrL(acts2[i].r) { if i == 0 {} else { assert acts2[i] == cont[i - 1]; } }
          }
          if LT.TreeRes(t.t1, gm, inp, WP.Forward).Some? { FirstLeafClosedNoLk(rer, acts1, inp, b, t.t1, gm, leaf); }
          else { FirstLeafClosedNoLk(rer, acts2, inp, b, t.t2, gm, leaf); }
        case Sequence(r1, r2) =>
          var acts1 := [LS.Areg(r1), LS.Areg(r2)] + cont;
          assert PendingCloses(acts1) == PendingCloses(cont) by { assert forall i :: 0 <= i < |cont| ==> acts1[i + 2] == cont[i]; }
          assert NoLkActs(acts1) by { forall i | 0 <= i < |acts1| ensures acts1[i].Areg? ==> EL.NoLkBrL(acts1[i].r) { if i < 2 {} else { assert acts1[i] == cont[i - 2]; } } }
          FirstLeafClosedNoLk(rer, acts1, inp, b, t, gm, leaf);
        case Quantified(greedy, min, delta, r1) =>
          var gidl := L.DefGroups(r1);
          if min > 0 {
            var gm2 := LG.GMUpdate(t.g, LC.Idx(inp), gm);
            assert gm2 == LG.GMReset(gidl, gm); assert OpenOf(gm2) <= OpenOf(gm);
            var acts1 := [LS.Areg(r1), LS.Areg(L.Quantified(greedy, min - 1, delta, r1))] + cont;
            assert PendingCloses(acts1) == PendingCloses(cont) by { assert forall i :: 0 <= i < |cont| ==> acts1[i + 2] == cont[i]; }
            assert NoLkActs(acts1) by { forall i | 0 <= i < |acts1| ensures acts1[i].Areg? ==> EL.NoLkBrL(acts1[i].r) { if i < 2 {} else { assert acts1[i] == cont[i - 2]; } } }
            FirstLeafClosedNoLk(rer, acts1, inp, b, t.t, gm2, leaf);
          } else if delta == LN.NN(0) { assert PendingCloses(acts) == PendingCloses(cont); FirstLeafClosedNoLk(rer, cont, inp, b, t, gm, leaf); }
          else {
            var itert := if greedy then t.t1 else t.t2; var skipt := if greedy then t.t2 else t.t1;
            var acts1 := [LS.Areg(r1), LS.Acheck(inp), LS.Areg(L.Quantified(greedy, 0, LFS.NoiPred(delta), r1))] + cont;
            assert PendingCloses(acts1) == PendingCloses(cont) by { assert forall i :: 0 <= i < |cont| ==> acts1[i + 3] == cont[i]; }
            assert NoLkActs(acts1) by { forall i | 0 <= i < |acts1| ensures acts1[i].Areg? ==> EL.NoLkBrL(acts1[i].r) { if i < 3 {} else { assert acts1[i] == cont[i - 3]; } } }
            assert PendingCloses(acts) == PendingCloses(cont);
            if LT.TreeRes(t.t1, gm, inp, WP.Forward).Some? {
              if greedy { var gm2 := LG.GMUpdate(itert.g, LC.Idx(inp), gm); assert gm2 == LG.GMReset(gidl, gm); assert OpenOf(gm2) <= OpenOf(gm); FirstLeafClosedNoLk(rer, acts1, inp, BS.CannotExit, itert.t, gm2, leaf); }
              else { FirstLeafClosedNoLk(rer, cont, inp, b, skipt, gm, leaf); }
            } else {
              if greedy { FirstLeafClosedNoLk(rer, cont, inp, b, skipt, gm, leaf); }
              else { var gm2 := LG.GMUpdate(itert.g, LC.Idx(inp), gm); assert gm2 == LG.GMReset(gidl, gm); assert OpenOf(gm2) <= OpenOf(gm); FirstLeafClosedNoLk(rer, acts1, inp, BS.CannotExit, itert.t, gm2, leaf); }
            }
          }
        case Group(gid, r1) =>
          var gm2 := LG.GMUpdate(t.g, LC.Idx(inp), gm);
          assert gm2 == LG.GMOpen(LC.Idx(inp), gid, gm);
          var acts1 := [LS.Areg(r1), LS.Aclose(gid)] + cont;
          assert gid in PendingCloses(acts1) by { assert acts1[1].Aclose? && acts1[1].gid == gid; }
          assert NoLkActs(acts1) by { forall i | 0 <= i < |acts1| ensures acts1[i].Areg? ==> EL.NoLkBrL(acts1[i].r) { if i == 0 {} else if i == 1 {} else { assert acts1[i] == cont[i - 2]; } } }
          assert OpenOf(gm2) <= PendingCloses(acts1) by {
            forall g | g in OpenOf(gm2) ensures g in PendingCloses(acts1) {
              if g != gid { assert g in OpenOf(gm); assert g in PendingCloses(acts); var i :| 0 <= i < |acts| && acts[i].Aclose? && acts[i].gid == g; assert i != 0; assert acts1[i + 1] == cont[i - 1] == acts[i]; }
            }
          }
          FirstLeafClosedNoLk(rer, acts1, inp, b, t.t, gm2, leaf);
        case AnchorR(a) =>
          if LS.AnchorSatisfied(rer, a, inp) { assert PendingCloses(acts) == PendingCloses(cont); FirstLeafClosedNoLk(rer, cont, inp, b, t.t, gm, leaf); }
          else { assert t == LT.Mismatch; assert false; }
        case LookaroundR(lk, r1) => assert false;   // NoLkBrL(r) excludes lookarounds
        case Backreference(_) => assert false;
    }
  }

  /** THE L3a payoff for the LK case: a positive look body's first leaf (evaluated
      from the OUTER map `gm`) leaves NO group open beyond those already open in
      `gm`, and adds only the body's own groups `S`. The body groups are fresh
      (`dom(gm) ∩ S == {}`), so the from-`gm` leaf agrees with a from-`Empty` leaf
      on `S` (`TreeLeavesFrameInside`); the from-`Empty` leaf is fully closed
      (`FirstLeafClosedNoLk` — valid since the body is look-free); and outside `S`
      the leaf equals `gm` (`GmConfinedLeaves`). */
  /** L3b: `EL.NoLkBrL` and `SD.GroupOkL` have IDENTICAL definitions (both forbid
      `LookaroundR` + `Backreference`, allow `Group`), so one implies the other.
      Bridges the linden-equiv fragment predicate to the linden-reasoning one the
      mirror machinery (`CloseDiscBody`, `RevLGroupOk`) is stated over. */
  lemma NoLkBrGroupOkL(r: L.Regex)
    requires EL.NoLkBrL(r)
    ensures SD.GroupOkL(r)
    decreases r
  {
    match r
    case Disjunction(r1, r2) => NoLkBrGroupOkL(r1); NoLkBrGroupOkL(r2);
    case Sequence(r1, r2) => NoLkBrGroupOkL(r1); NoLkBrGroupOkL(r2);
    case Quantified(_, _, _, r1) => NoLkBrGroupOkL(r1);
    case Group(_, r1) => NoLkBrGroupOkL(r1);
    case _ =>
  }

  // ---- L3b backward-closedness helpers (identical-def bridge + mirror closedness) ----
  /** Reverse of `NoLkBrGroupOkL`: `SD.GroupOkL` and `EL.NoLkBrL` have IDENTICAL
      definitions (both recurse through Disjunction/Sequence/Quantified/Group and
      reject LookaroundR/Backreference), so group-OK implies look-/backref-free. */
  lemma GroupOkLNoLkBr(r: L.Regex)
    requires SD.GroupOkL(r)
    ensures EL.NoLkBrL(r)
    decreases r
  {
    match r
    case Disjunction(r1, r2) => GroupOkLNoLkBr(r1); GroupOkLNoLkBr(r2);
    case Sequence(r1, r2) => GroupOkLNoLkBr(r1); GroupOkLNoLkBr(r2);
    case Quantified(_, _, _, r1) => GroupOkLNoLkBr(r1);
    case Group(_, r1) => GroupOkLNoLkBr(r1);
    case _ =>
  }

  /** The mirror preserves closedness both ways: `MirrorRange` maps a closed range
      (endIdx.Some) to a closed range and an open range (None) to open, and
      `MirrorGm` keeps the domain, so `ClosedGm` transfers across the mirror. */
  lemma MirrorGmClosedGm(gm: LG.GroupMap, n: nat)
    requires TRM.GmInBounds(gm, n)
    ensures ClosedGm(gm) <==> ClosedGm(TRM.MirrorGm(gm, n))
  {
    forall g
      ensures g in TRM.MirrorGm(gm, n) <==> g in gm
      ensures g in gm ==> (TRM.MirrorGm(gm, n)[g].endIdx.None? <==> gm[g].endIdx.None?)
    {
      TRM.MirrorGmOpen(gm, n, g);
    }
  }

  /** Having no open groups transfers across the mirror (open<->open, domain kept):
      `OpenOf(gm) == {}` is `ClosedGm(gm)`, which `MirrorGmClosedGm` carries over. */
  lemma MirrorGmOpenEmpty(gm: LG.GroupMap, n: nat)
    requires TRM.GmInBounds(gm, n) && OpenOf(gm) == {}
    ensures OpenOf(TRM.MirrorGm(gm, n)) == {}
  {
    assert ClosedGm(gm) by {
      forall g | g in gm ensures gm[g].endIdx.Some? {
        if gm[g].endIdx.None? { assert g in OpenOf(gm); }
      }
    }
    MirrorGmClosedGm(gm, n);
    forall g | g in OpenOf(TRM.MirrorGm(gm, n)) ensures false {
      assert g in TRM.MirrorGm(gm, n) && TRM.MirrorGm(gm, n)[g].endIdx.None?;
    }
  }

  /** `NoDupSeq` (local) and `CDE.NoDupG` are the SAME predicate (identical
      `forall i,j` definitions) — bridge for `CloseDiscBody`'s `NoDupG` requirement. */
  lemma NoDupSeqIsNoDupG(s: seq<LG.GroupId>)
    requires NoDupSeq(s)
    ensures CDE.NoDupG(s)
  {}

  /** L3b CRUX: a capturing lookBEHIND body's first leaf CLOSES its groups. The
      spec-side closedness machinery (`FirstLeafClosedNoLk`) is forward-only, so we
      go via the spec-tree MIRROR: the backward body tree `tlk` mirrors the FORWARD
      tree `tm` of `RevL(body)` over the swapped input (`TM.ComputeTrReverse`); `tm`'s
      first leaf is closed by the EXISTING forward `FirstLeafClosedNoLk`; and
      `TRM.TreeResMirror` + `MirrorGm` (which maps closed<->closed) transfer the
      closedness back to the backward leaf. The backward leaf's bound comes free from
      `TreeResMirror`'s `GmInBounds(rb.value.1, n)` ensures. */
  lemma BackBodyLeafClosed(rer: LW.RegExpRecord, r1: L.Regex, inp: LC.Input,
                           gm: LG.GroupMap, leaf: LT.Leaf)
    requires EL.NoLkBrL(r1)
    requires CDE.NoDupG(L.DefGroups(r1))
    requires TRM.GmInBounds(gm, |inp.pref| + |inp.next|)
    requires ClosedGm(gm)
    requires LT.TreeRes(FU.ComputeTr(rer, [LS.Areg(r1)], inp, LG.Empty, WP.Backward),
                        gm, inp, WP.Backward) == Some(leaf)
    ensures ClosedGm(leaf.1)
  {
    var n := |inp.pref| + |inp.next|;
    var tlk := FU.ComputeTr(rer, [LS.Areg(r1)], inp, LG.Empty, WP.Backward);
    var rr := SD.RevL(r1);
    var sinp := SD.SwapInput(inp);
    var gm2 := TRM.MirrorGm(gm, n);
    // fragment facts for the reversed body
    NoLkBrGroupOkL(r1);                                  // SD.GroupOkL(r1)
    assert SD.GroupOkActs([LS.Areg(r1)]);                // == GroupOkL(r1)
    SD.RevLGroupOk(r1);                                  // SD.GroupOkL(rr)
    GroupOkLNoLkBr(rr);                                  // EL.NoLkBrL(rr)
    NoLkBrImpliesPikeLk(rr);                             // EL.PikeLkRegex(rr)
    assert SD.RevActs([LS.Areg(r1)]) == [LS.Areg(rr)];
    var tm := FU.ComputeTr(rer, [LS.Areg(rr)], sinp, gm2, WP.Forward);
    // the backward body tree mirrors the forward tree of the reversed body
    TM.ComputeTrReverse(rer, [LS.Areg(r1)], inp, LG.Empty, gm2);
    assert TM.TreeMirrorRel(tlk, tm);
    CDE.CloseDiscBody(rer, r1, inp, LG.Empty, WP.Backward);   // CDE.CloseDisc(tlk, {})
    // the leaf-groupmap mirror: rf's leaf == MirrorGm(rb's leaf)
    TRM.TreeResMirror(tlk, tm, gm, inp, n, {});
    var rb := LT.TreeRes(tlk, gm, inp, WP.Backward);
    var rf := LT.TreeRes(tm, gm2, sinp, WP.Forward);
    assert rb == Some(leaf);
    assert rf.Some? && rf.value.1 == TRM.MirrorGm(rb.value.1, n)
        && TRM.GmInBounds(rb.value.1, n);
    // forward closedness on the mirror tree tm (existing forward machinery)
    MirrorGmOpenEmpty(gm, n);                            // OpenOf(gm2) == {}
    var fuel := LFS.ActionsFuel([LS.Areg(rr)], sinp, WP.Forward) + 1;
    LFS.FunctionalTerminates(rer, [LS.Areg(rr)], sinp, gm2, WP.Forward, fuel);
    assert LFS.ComputeTree(rer, [LS.Areg(rr)], sinp, gm2, WP.Forward, fuel) == Some(tm);
    var b0 := BS.CannotExit;
    assert BS.BoolEncoding(b0, sinp, [LS.Areg(rr)]);
    assert EL.PikeLkActions([LS.Areg(rr)]);
    assert NoLkActs([LS.Areg(rr)]);
    EL.ComputeBoolTreeLk(rer, [LS.Areg(rr)], sinp, gm2, b0, fuel, tm);
    assert OpenOf(gm2) <= PendingCloses([LS.Areg(rr)]);
    FirstLeafClosedNoLk(rer, [LS.Areg(rr)], sinp, b0, tm, gm2, rf.value);
    assert ClosedGm(rf.value.1);
    // transfer closedness back through the mirror
    MirrorGmClosedGm(rb.value.1, n);                     // ClosedGm(rb.leaf) <==> ClosedGm(rf.leaf)
    assert ClosedGm(rb.value.1);
    assert leaf == rb.value;
  }

  // ===================== L3b: GmInBounds threading helpers =====================
  /** `AdvanceInputP` preserves the input length `|pref|+|next|` (both directions),
      and `Idx(inp) = |inp.pref|` is within that length. */
  lemma AdvancePreservesSum(inp: LC.Input, dir: WP.Direction)
    ensures |LC.AdvanceInputP(inp, dir).pref| + |LC.AdvanceInputP(inp, dir).next|
         == |inp.pref| + |inp.next|
    ensures LC.Idx(inp) <= |inp.pref| + |inp.next|
  {}

  /** `AdvanceInputN` preserves the input length `|pref|+|next|` (both directions).
      Reused for the (fragment-absent) backreference tree case. */
  lemma AdvanceNPreservesSum(inp: LC.Input, k: nat, dir: WP.Direction)
    ensures |LC.AdvanceInputN(inp, k, dir).pref| + |LC.AdvanceInputN(inp, k, dir).next|
         == |inp.pref| + |inp.next|
  {
    match dir
    case Forward => LS.ReverseLength(LC.Take(inp.next, k));
    case Backward => LS.ReverseLength(LC.Take(inp.pref, k));
  }

  /** GM-op bound preservation: `GMOpen`/`GMClose` at an index `<= n` keep every
      group's endpoints `<= n`; `GMReset` only removes keys; `GMUpdate` dispatches. */
  lemma GMOpenBounds(currIdx: nat, gid: LG.GroupId, gm: LG.GroupMap, n: nat)
    requires TRM.GmInBounds(gm, n)
    requires currIdx <= n
    ensures TRM.GmInBounds(LG.GMOpen(currIdx, gid, gm), n)
  {}

  lemma GMCloseBounds(currIdx: nat, gid: LG.GroupId, gm: LG.GroupMap, n: nat)
    requires TRM.GmInBounds(gm, n)
    requires currIdx <= n
    ensures TRM.GmInBounds(LG.GMClose(currIdx, gid, gm), n)
  {}

  lemma GMResetBounds(gl: LG.GroupSet, gm: LG.GroupMap, n: nat)
    requires TRM.GmInBounds(gm, n)
    ensures TRM.GmInBounds(LG.GMReset(gl, gm), n)
  {}

  lemma GMUpdateBounds(op: LG.GroupAction, currIdx: nat, gm: LG.GroupMap, n: nat)
    requires TRM.GmInBounds(gm, n)
    requires currIdx <= n
    ensures TRM.GmInBounds(LG.GMUpdate(op, currIdx, gm), n)
  {}

  /** GENERAL leaf bound: every leaf of `TreeLeaves(t, gm, inp, dir)` has all group
      endpoints `<= n == |inp.pref|+|inp.next|`, provided the starting `gm` does.
      Structural on `t`: `Read`/`ReadBackRef` advance the input (length preserved),
      `GroupActionT` updates at `Idx(inp) <= n`, and a nested `LK` recurses on the
      body (in `LkDir(lk)`, same `n`) then the continuation. `dir`-parametric, so it
      also covers backward (lookbehind) bodies. */
  lemma TreeLeavesInBounds(t: LT.Tree, gm: LG.GroupMap, inp: LC.Input, dir: WP.Direction, n: nat)
    requires |inp.pref| + |inp.next| == n
    requires TRM.GmInBounds(gm, n)
    ensures forall i :: 0 <= i < |LT.TreeLeaves(t, gm, inp, dir)| ==>
              TRM.GmInBounds(LT.TreeLeaves(t, gm, inp, dir)[i].1, n)
    decreases t
  {
    match t
    case Mismatch =>
    case Match =>
    case Choice(t1, t2) =>
      TreeLeavesInBounds(t1, gm, inp, dir, n);
      TreeLeavesInBounds(t2, gm, inp, dir, n);
    case Read(c, t1) =>
      AdvancePreservesSum(inp, dir);
      TreeLeavesInBounds(t1, gm, LC.AdvanceInputP(inp, dir), dir, n);
    case Progress(t1) =>
      TreeLeavesInBounds(t1, gm, inp, dir, n);
    case GroupActionT(a, t1) =>
      GMUpdateBounds(a, LC.Idx(inp), gm, n);
      TreeLeavesInBounds(t1, LG.GMUpdate(a, LC.Idx(inp), gm), inp, dir, n);
    case LK(lk, tlk, t1) =>
      TreeLeavesInBounds(tlk, gm, inp, L.LkDir(lk), n);
      var sub := LT.TreeLeaves(tlk, gm, inp, L.LkDir(lk));
      if L.Positivity(lk) {
        if |sub| == 0 {} else {
          TreeLeavesInBounds(t1, sub[0].1, inp, dir, n);
        }
      } else {
        if |sub| == 0 { TreeLeavesInBounds(t1, gm, inp, dir, n); } else {}
      }
    case LKFail(_, _) =>
    case AnchorPass(_, t0) =>
      TreeLeavesInBounds(t0, gm, inp, dir, n);
    case ReadBackRef(brStr, t0) =>
      AdvanceNPreservesSum(inp, |brStr|, dir);
      TreeLeavesInBounds(t0, gm, LC.AdvanceInputN(inp, |brStr|, dir), dir, n);
  }
  // =============================================================================

  lemma LookBodyLeafOpenSub(rer: LW.RegExpRecord, lk: L.Lookaround, r1: L.Regex, tlk: LT.Tree,
                            gm: LG.GroupMap, inp: LC.Input, sub: seq<LT.Leaf>, S: set<LG.GroupId>)
    requires tlk == FU.ComputeTr(rer, [LS.Areg(r1)], inp, LG.Empty, L.LkDir(lk))
    requires EL.NoLkBrL(r1) && EL.PikeLkRegex(r1)
    requires S == (set g | g in L.DefGroups(r1))
    requires forall g :: g in gm && g in S ==> gm[g].endIdx.Some?   // reused body groups are CLOSED
    requires sub == LT.TreeLeaves(tlk, gm, inp, L.LkDir(lk))
    requires |sub| > 0
    requires L.Positivity(lk)
    // L3b: the body's captures close in EITHER direction (backward via the spec-tree
    // mirror, `BackBodyLeafClosed`). NoDupG + GmInBounds feed that mirror.
    requires CDE.NoDupG(L.DefGroups(r1))
    requires TRM.GmInBounds(gm, |inp.pref| + |inp.next|)
    ensures OpenOf(sub[0].1) <= OpenOf(gm)
    ensures forall g :: g in sub[0].1 ==> g in gm || g in S
    ensures forall g :: g in sub[0].1 && g in S ==> sub[0].1[g].endIdx.Some?   // look closed its captures
    ensures TRM.GmInBounds(sub[0].1, |inp.pref| + |inp.next|)   // L3b: leaf bound (for the caller's threading)
  {
    var dir := L.LkDir(lk);
    TreeLeavesInBounds(tlk, gm, inp, dir, |inp.pref| + |inp.next|);   // GmInBounds(sub[i].1)
    assert LL.DefGroupsIn(r1, S);
    LL.ComputeTrConfined(rer, r1, inp, LG.Empty, dir, S);       // GmConfinedTree(tlk, S)
    LL.GmConfinedLeaves(tlk, gm, inp, dir, S);                  // sub[i].1 ~outside-S~ gm
    // gmR = gm restricted to its own S-groups (all CLOSED), so OpenOf(gmR) == {}.
    var gmR := map g | g in gm && g in S :: gm[g];
    var subR := LT.TreeLeaves(tlk, gmR, inp, dir);
    assert OpenOf(gmR) == {} by { forall g | g in gmR ensures gmR[g].endIdx.Some? { assert g in gm && g in S; } }
    assert LL.GmAgreeInside(gm, gmR, S) by {
      forall g | g in S ensures (g in gm <==> g in gmR) && (g in gm ==> gm[g] == gmR[g]) {}
    }
    LL.TreeLeavesFrameInside(tlk, gm, gmR, inp, dir, S);        // sub[i].1 ~inside-S~ subR[i].1
    assert |sub| == |subR|;
    if dir == WP.Forward {
      // The from-gmR body leaf is fully closed (look-free body ⇒ FirstLeafClosedNoLk).
      LT.FirstTreeLeaf(tlk, gmR, inp, dir);
      assert LT.TreeRes(tlk, gmR, inp, WP.Forward) == Some(subR[0]);
      var fuel := LFS.ActionsFuel([LS.Areg(r1)], inp, WP.Forward) + 1;
      LFS.FunctionalTerminates(rer, [LS.Areg(r1)], inp, LG.Empty, WP.Forward, fuel);
      assert LFS.ComputeTree(rer, [LS.Areg(r1)], inp, LG.Empty, WP.Forward, fuel) == Some(tlk);
      var b0 := BS.CannotExit;
      assert BS.BoolEncoding(b0, inp, [LS.Areg(r1)]);   // single Areg ⇒ reduces to true
      EL.ComputeBoolTreeLk(rer, [LS.Areg(r1)], inp, LG.Empty, b0, fuel, tlk);   // BoolTreeLk is eval-map independent
      assert EL.PikeLkActions([LS.Areg(r1)]);
      assert NoLkActs([LS.Areg(r1)]);
      assert OpenOf(gmR) <= PendingCloses([LS.Areg(r1)]);
      FirstLeafClosedNoLk(rer, [LS.Areg(r1)], inp, b0, tlk, gmR, subR[0]);
      assert ClosedGm(subR[0].1);
      forall g | g in OpenOf(sub[0].1) ensures g in OpenOf(gm) {
        if g in S {
          assert sub[0].1[g] == subR[0].1[g];    // FrameInside on S
          assert g in subR[0].1 && subR[0].1[g].endIdx.Some?;   // ClosedGm
          assert false;
        }
      }
    } else {
      // L3b: dir == Backward, capturing lookbehind. Prove ClosedGm(subR[0].1) via
      // the spec-tree mirror (BackBodyLeafClosed), then the SAME OpenOf reasoning.
      assert dir == WP.Backward;
      var nn := |inp.pref| + |inp.next|;
      LT.FirstTreeLeaf(tlk, gmR, inp, dir);
      assert LT.TreeRes(tlk, gmR, inp, WP.Backward) == Some(subR[0]);
      assert TRM.GmInBounds(gmR, nn) by {
        assert forall g :: g in gmR ==> g in gm && gmR[g] == gm[g];
      }
      assert ClosedGm(gmR) by {
        forall g | g in gmR ensures gmR[g].endIdx.Some? { assert g !in OpenOf(gmR); }
      }
      BackBodyLeafClosed(rer, r1, inp, gmR, subR[0]);   // ClosedGm(subR[0].1)
      forall g | g in OpenOf(sub[0].1) ensures g in OpenOf(gm) {
        if g in S {
          assert sub[0].1[g] == subR[0].1[g];    // FrameInside on S
          assert g in subR[0].1 && subR[0].1[g].endIdx.Some?;   // ClosedGm
          assert false;
        }
      }
    }
    forall g | g in sub[0].1 ensures g in gm || g in S {}
    // S groups are never open in sub[0].1 (OpenOf(sub[0].1) <= OpenOf(gm), and gm's S
    // groups are closed), so a present S group is closed.
    forall g | g in sub[0].1 && g in S ensures sub[0].1[g].endIdx.Some? {
      assert g !in OpenOf(gm);
      assert g !in OpenOf(sub[0].1);
    }
  }

  /** The translated regex's DEFINED group ids are exactly the engine's capture
      ids: `Translate` maps `Re_capture(cid,_)` to `Group(cid,_)` and copies every
      other constructor, so both collect the same cids. */
  lemma TranslateDefGroupsEqCapIds(r: R.regex)
    requires T.TransWf(r)
    ensures (set g | g in L.DefGroups(T.Translate(r))) == PIV.CapIds(r)
    decreases r
  {
    match r
    case Re_empty =>
    case Re_character(_) =>
    case Re_anchor(_) =>
    case Re_alt(r1, r2) =>
      TranslateDefGroupsEqCapIds(r1); TranslateDefGroupsEqCapIds(r2);
      assert L.DefGroups(T.Translate(r)) == L.DefGroups(T.Translate(r1)) + L.DefGroups(T.Translate(r2));
      assert forall g :: g in L.DefGroups(T.Translate(r)) <==>
             g in L.DefGroups(T.Translate(r1)) || g in L.DefGroups(T.Translate(r2));
    case Re_con(r1, r2) =>
      TranslateDefGroupsEqCapIds(r1); TranslateDefGroupsEqCapIds(r2);
      assert L.DefGroups(T.Translate(r)) == L.DefGroups(T.Translate(r1)) + L.DefGroups(T.Translate(r2));
      assert forall g :: g in L.DefGroups(T.Translate(r)) <==>
             g in L.DefGroups(T.Translate(r1)) || g in L.DefGroups(T.Translate(r2));
    case Re_quant(_, _, q, r1) => TranslateDefGroupsEqCapIds(r1);
    case Re_capture(cid, r1) =>
      TranslateDefGroupsEqCapIds(r1);
      assert L.DefGroups(T.Translate(r)) == [cid as nat] + L.DefGroups(T.Translate(r1));
      assert forall g :: g in L.DefGroups(T.Translate(r)) <==> g == cid as nat || g in L.DefGroups(T.Translate(r1));
    case Re_lookaround(_, lk, r1) => TranslateDefGroupsEqCapIds(r1);
  }

  /** The translated regex's inside-lookaround group ids equal the engine's
      `CapIdsInLooks`. A `LookaroundR` contributes its whole body's `DefGroups`
      (which subsumes the body's own nested look groups, `LkBodyGroupsSubDefs`),
      matching `CapIdsInLooks(Re_lookaround) == CapIds(body)`. */
  lemma LkBodyGroupsEqCapIdsInLooks(r: R.regex)
    requires T.TransWf(r)
    ensures LL.LkBodyGroups(T.Translate(r)) == PIV.CapIdsInLooks(r)
    decreases r
  {
    match r
    case Re_empty =>
    case Re_character(_) =>
    case Re_anchor(_) =>
    case Re_alt(r1, r2) => LkBodyGroupsEqCapIdsInLooks(r1); LkBodyGroupsEqCapIdsInLooks(r2);
    case Re_con(r1, r2) => LkBodyGroupsEqCapIdsInLooks(r1); LkBodyGroupsEqCapIdsInLooks(r2);
    case Re_quant(_, _, q, r1) => LkBodyGroupsEqCapIdsInLooks(r1);
    case Re_capture(cid, r1) => LkBodyGroupsEqCapIdsInLooks(r1);
    case Re_lookaround(_, lk, r1) =>
      // LkBodyGroups(LookaroundR(_,T(r1))) == set(DefGroups(T(r1))) + LkBodyGroups(T(r1))
      //                                    == set(DefGroups(T(r1)))         (subsumed)
      //                                    == CapIds(r1) == CapIdsInLooks(r)
      TranslateDefGroupsEqCapIds(r1);
      LkBodyGroupsSubDefs(T.Translate(r1));
      assert LL.LkBodyGroups(T.Translate(r)) == (set g | g in L.DefGroups(T.Translate(r1))) + LL.LkBodyGroups(T.Translate(r1));
  }

  /** L3a OUTSIDE-look value bridge: the spec first leaf `ft` (which agrees with
      the main thread's denotation `gmBest` OUTSIDE the tree inside-look set) agrees
      with `GmOfLive(re, capR, look, quantR)` (the FLookLoop-reconstructed answer) on
      every OUTSIDE-look group. Composes `GmOfLiveFrameOutside` (capR/quantR agree
      capT/quantT outside the inside-look registers/quants) with the tree/engine
      inside-look set identity (`LkBodyGroupsEqCapIdsInLooks`). */
  lemma OutsideLookValueBridge(re: R.regex, capT: AReg.Regs, capR: AReg.Regs, look: AReg.Regs,
                               quantT: AReg.Regs, quantR: AReg.Regs, gmBest: LG.GroupMap, ft: LG.GroupMap)
    requires T.TransWf(re) && NR.LookBehindFragmentRE(re) && PIV.CapUnique(re)
    requires gmBest == PIV.GmOfLive(re, capT, look, quantT)
    requires forall g: nat :: g !in LL.LkBodyGroups(T.Translate(re)) ==>
      (g in ft <==> g in gmBest) && (g in ft ==> ft[g] == gmBest[g])
    requires forall k: int :: k !in PIV.CaptureRegsSet(PIV.CapIdsInLooks(re)) ==>
      AI.get_idx(AReg.as_arrays(capR).0, k) == AI.get_idx(AReg.as_arrays(capT).0, k)
      && AI.get_idx(AReg.as_arrays(capR).1, k) == AI.get_idx(AReg.as_arrays(capT).1, k)
    requires forall q: nat :: q in PIV.QuantIdsOutsideLooks(re) ==>
      AI.get_idx(AReg.as_arrays(quantR).1, q) == AI.get_idx(AReg.as_arrays(quantT).1, q)
    ensures forall g: nat :: g !in PIV.CapIdsInLooks(re) ==>
      (g in ft <==> g in PIV.GmOfLive(re, capR, look, quantR))
      && (g in ft ==> ft[g] == PIV.GmOfLive(re, capR, look, quantR)[g])
  {
    LkBodyGroupsEqCapIdsInLooks(re);                 // LkBodyGroups(Translate(re)) == CapIdsInLooks(re)
    PIV.GmOfLiveFrameOutside(re, capR, capT, look, quantR, quantT);   // GmOfLive(capR) ~ GmOfLive(capT) outside CapIdsInLooks
    forall g: nat | g !in PIV.CapIdsInLooks(re)
      ensures (g in ft <==> g in PIV.GmOfLive(re, capR, look, quantR))
           && (g in ft ==> ft[g] == PIV.GmOfLive(re, capR, look, quantR)[g])
    {
      assert g !in LL.LkBodyGroups(T.Translate(re));       // set identity
      // ft ~ gmBest (spec/main outside S), gmBest = GmOfLive(capT) ~ GmOfLive(capR) (frame)
    }
  }

  // ==========================================================================
  // (E) The INSIDE-look ENGINE value bridge. For a group `g` owned by a matched
  // lookahead body, the whole-regex live denotation of the RECONSTRUCTED bank
  // `cap0` (= `FLookLoop`'s `res.0`) at `g` equals the body's own live
  // denotation of the FRESH body match `cap1`. Both reduce to the same raw
  // `LiveRange` (they agree on `g`'s registers, `RegsAgreeInside` on
  // `CaptureRegs(body)`); the only work is that `filter_capture` KEEPS the value
  // on both sides. Absent case: `filter_capture` can only make a group MORE
  // absent, so an unset `g` is absent both sides (no path facts). Present case:
  // `GmOfLiveKeepsPresentLk` on each side, taking the path-presence conditions as
  // hypotheses (these are discharged at final wiring, alongside the position
  // correspondence — the outer path to the matched look is a winning-thread fact).
  // ==========================================================================

  /** (E) ABSENT half: if `g`'s start value is unset in `cap0` (hence in `cap1`,
      by agreement), then `g` is absent from BOTH live denotations. Fully
      self-contained — `filter_capture` never resurrects an unset group. */
  lemma GmOfLiveInsideLookAbsentEq(re: R.regex, body: R.regex,
                                   cap0: AReg.Regs, look: AReg.Regs, quant: AReg.Regs,
                                   cap1: AReg.Regs, look1: AReg.Regs, quant1: AReg.Regs, g: nat)
    requires g in PIV.CapIds(body)
    requires CM.RegsAgreeInside(cap0, cap1, PIV.CaptureRegs(body))
    requires AI.get_idx(AReg.as_arrays(cap0).0, CP.start_reg(g)) < 0
    ensures g !in PIV.GmOfLive(re, cap0, look, quant)
    ensures g !in PIV.GmOfLive(body, cap1, look1, quant1)
  {
    assert CP.start_reg(g) in PIV.CaptureRegs(body);
    var cr0 := AReg.as_arrays(cap0).0; var cc0 := AReg.as_arrays(cap0).1;
    var lc := AReg.as_arrays(look).1;  var qc := AReg.as_arrays(quant).1;
    var f0 := AI.filter_reset(re, cap0, look, quant, -1);
    assert f0 == AI.filter_capture(re, cr0, cc0, lc, qc, -1);
    PIV.FilterCaptureNeg(re, cr0, cc0, lc, qc, -1, CP.start_reg(g));
    assert AI.get_idx(f0, CP.start_reg(g)) < 0;

    var cr1 := AReg.as_arrays(cap1).0; var cc1 := AReg.as_arrays(cap1).1;
    var lc1 := AReg.as_arrays(look1).1; var qc1 := AReg.as_arrays(quant1).1;
    assert AI.get_idx(cr1, CP.start_reg(g)) == AI.get_idx(cr0, CP.start_reg(g));   // RegsAgreeInside
    var f1 := AI.filter_reset(body, cap1, look1, quant1, -1);
    assert f1 == AI.filter_capture(body, cr1, cc1, lc1, qc1, -1);
    PIV.FilterCaptureNeg(body, cr1, cc1, lc1, qc1, -1, CP.start_reg(g));
    assert AI.get_idx(f1, CP.start_reg(g)) < 0;
  }

  /** (E) PRESENT half: when `g`'s start is set in the fresh body match `cap1`
      and BOTH descents are path-present (the outer look matched + the inner body
      captured `g`), each side's live denotation is the raw `LiveRange` of its own
      bank, and the banks agree on `g`'s registers — so the two denotations are
      equal and `g` is present both sides. The path-presence hypotheses are the
      wiring's job (the outer `PathPresentLk(re, cap0)` is a winning-thread fact,
      coupled to the position correspondence). */
  lemma GmOfLiveInsideLookPresentEq(re: R.regex, body: R.regex,
                                    cap0: AReg.Regs, look: AReg.Regs, quant: AReg.Regs,
                                    cap1: AReg.Regs, look1: AReg.Regs, quant1: AReg.Regs, g: nat)
    requires NR.LookBehindFragmentRE(re) && PIV.CapUnique(re)
    requires NR.LookBehindFragmentRE(body) && PIV.CapUnique(body)
    requires g in PIV.CapIds(re) && g in PIV.CapIds(body)
    requires CM.RegsAgreeInside(cap0, cap1, PIV.CaptureRegs(body))
    requires AI.get_idx(AReg.as_arrays(cap1).1, CP.start_reg(g)) >= 0        // fresh clock set
    requires AI.get_idx(AReg.as_arrays(cap1).0, CP.start_reg(g)) >= 0        // fresh value set
    requires PIV.PathPresentLk(re, AReg.as_arrays(cap0).1, AReg.as_arrays(look).1, AReg.as_arrays(quant).1, -1, g)
    requires AI.get_idx(AReg.as_arrays(cap0).1, CP.start_reg(g))
               >= PIV.MxAtGidLk(re, AReg.as_arrays(cap0).1, AReg.as_arrays(look).1, AReg.as_arrays(quant).1, -1, g)
    requires PIV.PathPresentLk(body, AReg.as_arrays(cap1).1, AReg.as_arrays(look1).1, AReg.as_arrays(quant1).1, -1, g)
    requires AI.get_idx(AReg.as_arrays(cap1).1, CP.start_reg(g))
               >= PIV.MxAtGidLk(body, AReg.as_arrays(cap1).1, AReg.as_arrays(look1).1, AReg.as_arrays(quant1).1, -1, g)
    ensures g in PIV.GmOfLive(re, cap0, look, quant) && g in PIV.GmOfLive(body, cap1, look1, quant1)
    ensures PIV.GmOfLive(re, cap0, look, quant)[g] == PIV.GmOfLive(body, cap1, look1, quant1)[g]
  {
    assert CP.start_reg(g) in PIV.CaptureRegs(body) && CP.end_reg(g) in PIV.CaptureRegs(body);
    // cap0's start is set too (agreement with cap1 on CaptureRegs(body))
    assert AI.get_idx(AReg.as_arrays(cap0).1, CP.start_reg(g)) == AI.get_idx(AReg.as_arrays(cap1).1, CP.start_reg(g));
    assert AI.get_idx(AReg.as_arrays(cap0).0, CP.start_reg(g)) == AI.get_idx(AReg.as_arrays(cap1).0, CP.start_reg(g));
    PIV.GmOfLiveKeepsPresentLk(re, cap0, look, quant, g);
    PIV.GmOfLiveKeepsPresentLk(body, cap1, look1, quant1, g);
    // both values are the raw LiveRange; cap0 == cap1 on {start_reg(g), end_reg(g)}
    assert AI.get_idx(AReg.as_arrays(cap0).0, CP.end_reg(g)) == AI.get_idx(AReg.as_arrays(cap1).0, CP.end_reg(g));
    assert AI.get_idx(AReg.as_arrays(cap0).1, CP.end_reg(g)) == AI.get_idx(AReg.as_arrays(cap1).1, CP.end_reg(g));
    assert PIV.LiveRange(AReg.as_arrays(cap0).0, AReg.as_arrays(cap0).1, g)
        == PIV.LiveRange(AReg.as_arrays(cap1).0, AReg.as_arrays(cap1).1, g);
  }

  /** L3a value companion of `LookBodyLeafOpenSub`: when the look's body groups
      are UNSET in the incoming `gm` (the reset condition — a fresh or just-reset
      entry), the body's first leaf from `gm` agrees, on `S == DefGroups(r1)`, with
      the body's first leaf from `LG.Empty`. Direct `TreeLeavesFrameInside`: `gm`
      and `Empty` agree on `S` (both lack those groups), so all leaves agree on `S`. */
  lemma LookBodyLeafValue(rer: LW.RegExpRecord, lk: L.Lookaround, r1: L.Regex, tlk: LT.Tree,
                          gm: LG.GroupMap, inp: LC.Input, S: set<LG.GroupId>)
    requires tlk == FU.ComputeTr(rer, [LS.Areg(r1)], inp, LG.Empty, L.LkDir(lk))
    requires S == (set g | g in L.DefGroups(r1))
    requires GmAgreeOn(gm, LG.Empty, S)      // body groups unset in gm (reset / fresh)
    ensures var dir := L.LkDir(lk);
            var sub := LT.TreeLeaves(tlk, gm, inp, dir);
            var subE := LT.TreeLeaves(tlk, LG.Empty, inp, dir);
            |sub| == |subE|
            && forall i :: 0 <= i < |sub| ==> sub[i].0 == subE[i].0 && GmAgreeOn(sub[i].1, subE[i].1, S)
  {
    var dir := L.LkDir(lk);
    assert LL.GmAgreeInside(gm, LG.Empty, S);      // GmAgreeOn ≡ GmAgreeInside
    LL.TreeLeavesFrameInside(tlk, gm, LG.Empty, inp, dir, S);
    forall i | 0 <= i < |LT.TreeLeaves(tlk, gm, inp, dir)|
      ensures LT.TreeLeaves(tlk, gm, inp, dir)[i].0 == LT.TreeLeaves(tlk, LG.Empty, inp, dir)[i].0
           && GmAgreeOn(LT.TreeLeaves(tlk, gm, inp, dir)[i].1, LT.TreeLeaves(tlk, LG.Empty, inp, dir)[i].1, S)
    {
      assert LL.GmAgreeInside(LT.TreeLeaves(tlk, gm, inp, dir)[i].1, LT.TreeLeaves(tlk, LG.Empty, inp, dir)[i].1, S);
    }
  }

  least lemma FirstLeafClosed(rer: LW.RegExpRecord, acts: LS.Actions, inp: LC.Input,
                              b: BS.LoopBool, t: LT.Tree, gm: LG.GroupMap, leaf: LT.Leaf)
    requires EL.BoolTreeLk(rer, acts, inp, b, t)
    requires EL.PikeLkActions(acts)
    requires OpenOf(gm) <= PendingCloses(acts)
    requires LT.TreeRes(t, gm, inp, WP.Forward) == Some(leaf)
    requires LkClosedInGm(gm, acts)             // L3a: reused pending inside-look groups are closed
    requires OuterLkDisjoint(acts)              // L3a: outer defs disjoint from inside-look groups
    requires NoDupRegsActs(acts)                // L3b: each pending regex has dup-free groups (for NoDupG)
    requires TRM.GmInBounds(gm, |inp.pref| + |inp.next|)   // L3b: gm ranges within input (for the mirror)
    ensures ClosedGm(leaf.1)
  {
    var n := |inp.pref| + |inp.next|;
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
      assert NoDupRegsActs(cont) by { forall i | 0 <= i < |cont| ensures cont[i].Areg? ==> NoDupSeq(L.DefGroups(cont[i].r)) { assert cont[i] == acts[i + 1]; } }
      match acts[0]
      case Acheck(strcheck) =>
        if b == BS.CanExit {
          assert t.Progress?;
          assert PendingCloses(acts) == PendingCloses(cont);
          TailInv(gm, gm, acts);
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
        // GMClose keeps the domain, closes gid, and leaves every other group as-is.
        assert forall g :: g in gm2 ==> g in gm && (gm2[g].endIdx.Some? || gm2[g] == gm[g]);
        assert TRM.GmInBounds(gm2, n) by { assert LC.Idx(inp) <= n; }
        TailInv(gm, gm2, acts);
        FirstLeafClosed(rer, cont, inp, b, t.t, gm2, leaf);
      case Areg(r) =>
        match r
        case Epsilon =>
          assert PendingCloses(acts) == PendingCloses(cont);
          TailInv(gm, gm, acts);
          FirstLeafClosed(rer, cont, inp, b, t, gm, leaf);
        case Character(cd) =>
          if LC.ReadChar(rer, cd, inp, WP.Forward).None? {
            assert t == LT.Mismatch;
            assert false;
          } else {
            var pair := LC.ReadChar(rer, cd, inp, WP.Forward).value;
            assert t.Read?;
            assert pair.1 == LC.AdvanceInputP(inp, WP.Forward);
            assert |pair.1.pref| + |pair.1.next| == n;   // advance preserves total length
            assert PendingCloses(acts) == PendingCloses(cont);
            TailInv(gm, gm, acts);
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
          LkBodyGroupsActsCons(LS.Areg(r), cont); LkBodyGroupsActsCons(LS.Areg(r1), cont); LkBodyGroupsActsCons(LS.Areg(r2), cont);
          OuterDefsActsCons(LS.Areg(r), cont); OuterDefsActsCons(LS.Areg(r1), cont); OuterDefsActsCons(LS.Areg(r2), cont);
          assert LL.LkBodyGroups(r) == LL.LkBodyGroups(r1) + LL.LkBodyGroups(r2);
          assert DefGroupsOutsideLooksL(r) == DefGroupsOutsideLooksL(r1) + DefGroupsOutsideLooksL(r2);
          assert NoDupSeq(L.DefGroups(r)) && L.DefGroups(r) == L.DefGroups(r1) + L.DefGroups(r2);
          NoDupConcat(L.DefGroups(r1), L.DefGroups(r2));
          assert NoDupRegsActs(acts1) by { forall i | 0 <= i < |acts1| ensures acts1[i].Areg? ==> NoDupSeq(L.DefGroups(acts1[i].r)) { if i == 0 {} else { assert acts1[i] == cont[i - 1]; } } }
          assert NoDupRegsActs(acts2) by { forall i | 0 <= i < |acts2| ensures acts2[i].Areg? ==> NoDupSeq(L.DefGroups(acts2[i].r)) { if i == 0 {} else { assert acts2[i] == cont[i - 1]; } } }
          if LT.TreeRes(t.t1, gm, inp, WP.Forward).Some? {
            SubInv(gm, gm, acts1, acts);
            FirstLeafClosed(rer, acts1, inp, b, t.t1, gm, leaf);
          } else {
            SubInv(gm, gm, acts2, acts);
            FirstLeafClosed(rer, acts2, inp, b, t.t2, gm, leaf);
          }
        case Sequence(r1, r2) =>
          var acts1 := [LS.Areg(r1), LS.Areg(r2)] + cont;
          assert PendingCloses(acts1) == PendingCloses(cont) by {
            assert forall i :: 0 <= i < |cont| ==> acts1[i + 2] == cont[i];
          }
          assert PendingCloses(acts) == PendingCloses(cont);
          assert acts1 == [LS.Areg(r1)] + ([LS.Areg(r2)] + cont);
          LkBodyGroupsActsCons(LS.Areg(r), cont); LkBodyGroupsActsCons(LS.Areg(r1), [LS.Areg(r2)] + cont); LkBodyGroupsActsCons(LS.Areg(r2), cont);
          OuterDefsActsCons(LS.Areg(r), cont); OuterDefsActsCons(LS.Areg(r1), [LS.Areg(r2)] + cont); OuterDefsActsCons(LS.Areg(r2), cont);
          assert LL.LkBodyGroups(r) == LL.LkBodyGroups(r1) + LL.LkBodyGroups(r2);
          assert DefGroupsOutsideLooksL(r) == DefGroupsOutsideLooksL(r1) + DefGroupsOutsideLooksL(r2);
          assert NoDupSeq(L.DefGroups(r)) && L.DefGroups(r) == L.DefGroups(r1) + L.DefGroups(r2);
          NoDupConcat(L.DefGroups(r1), L.DefGroups(r2));
          assert NoDupRegsActs(acts1) by { forall i | 0 <= i < |acts1| ensures acts1[i].Areg? ==> NoDupSeq(L.DefGroups(acts1[i].r)) { if i < 2 {} else { assert acts1[i] == cont[i - 2]; } } }
          SubInv(gm, gm, acts1, acts);
          FirstLeafClosed(rer, acts1, inp, b, t, gm, leaf);
        case Quantified(greedy, min, delta, r1) =>
          var gidl := L.DefGroups(r1);
          if min > 0 {
            assert t.GroupActionT? && t.g == LG.Reset(gidl);
            var gm2 := LG.GMUpdate(t.g, LC.Idx(inp), gm);
            assert gm2 == LG.GMReset(gidl, gm);
            assert OpenOf(gm2) <= OpenOf(gm);
            assert forall g :: g in gm2 ==> g in gm && gm2[g] == gm[g];
            var q' := L.Quantified(greedy, min - 1, delta, r1);
            var acts1 := [LS.Areg(r1), LS.Areg(q')] + cont;
            assert PendingCloses(acts1) == PendingCloses(cont) by {
              assert forall i :: 0 <= i < |cont| ==> acts1[i + 2] == cont[i];
            }
            assert PendingCloses(acts) == PendingCloses(cont);
            assert NoDupSeq(L.DefGroups(r)) && L.DefGroups(r) == L.DefGroups(r1) && L.DefGroups(q') == L.DefGroups(r1);
            assert NoDupRegsActs(acts1) by { forall i | 0 <= i < |acts1| ensures acts1[i].Areg? ==> NoDupSeq(L.DefGroups(acts1[i].r)) { if i < 2 {} else { assert acts1[i] == cont[i - 2]; } } }
            assert TRM.GmInBounds(gm2, n);   // GMReset only shrinks the domain
            QuantSubInv(gm, gm2, r, r1, q', cont, acts, acts1);
            FirstLeafClosed(rer, acts1, inp, b, t.t, gm2, leaf);
          } else if delta == LN.NN(0) {
            assert PendingCloses(acts) == PendingCloses(cont);
            TailInv(gm, gm, acts);
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
                assert forall g :: g in gm2 ==> g in gm && gm2[g] == gm[g];
                var q'' := L.Quantified(greedy, 0, LFS.NoiPred(delta), r1);
                var acts1 := [LS.Areg(r1), LS.Acheck(inp), LS.Areg(q'')] + cont;
                assert PendingCloses(acts1) == PendingCloses(cont) by {
                  assert forall i :: 0 <= i < |cont| ==> acts1[i + 3] == cont[i];
                }
                assert NoDupSeq(L.DefGroups(r)) && L.DefGroups(r) == L.DefGroups(r1) && L.DefGroups(q'') == L.DefGroups(r1);
                assert NoDupRegsActs(acts1) by { forall i | 0 <= i < |acts1| ensures acts1[i].Areg? ==> NoDupSeq(L.DefGroups(acts1[i].r)) { if i < 3 {} else { assert acts1[i] == cont[i - 3]; } } }
                assert TRM.GmInBounds(gm2, n);
                QuantSubInvCheck(gm, gm2, r, r1, q'', inp, cont, acts, acts1);
                FirstLeafClosed(rer, acts1, inp, BS.CannotExit, itert.t, gm2, leaf);
              } else {
                TailInv(gm, gm, acts);
                FirstLeafClosed(rer, cont, inp, b, skipt, gm, leaf);
              }
            } else {
              if greedy {
                TailInv(gm, gm, acts);
                FirstLeafClosed(rer, cont, inp, b, skipt, gm, leaf);
              } else {
                var gm2 := LG.GMUpdate(itert.g, LC.Idx(inp), gm);
                assert gm2 == LG.GMReset(gidl, gm);
                assert OpenOf(gm2) <= OpenOf(gm);
                assert forall g :: g in gm2 ==> g in gm && gm2[g] == gm[g];
                var q'' := L.Quantified(greedy, 0, LFS.NoiPred(delta), r1);
                var acts1 := [LS.Areg(r1), LS.Acheck(inp), LS.Areg(q'')] + cont;
                assert PendingCloses(acts1) == PendingCloses(cont) by {
                  assert forall i :: 0 <= i < |cont| ==> acts1[i + 3] == cont[i];
                }
                assert NoDupSeq(L.DefGroups(r)) && L.DefGroups(r) == L.DefGroups(r1) && L.DefGroups(q'') == L.DefGroups(r1);
                assert NoDupRegsActs(acts1) by { forall i | 0 <= i < |acts1| ensures acts1[i].Areg? ==> NoDupSeq(L.DefGroups(acts1[i].r)) { if i < 3 {} else { assert acts1[i] == cont[i - 3]; } } }
                assert TRM.GmInBounds(gm2, n);
                QuantSubInvCheck(gm, gm2, r, r1, q'', inp, cont, acts, acts1);
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
          // gid is an OUTER group ⇒ gid ∉ LkBodyGroupsActs; the Group rewrite keeps
          // the same look groups and shrinks outer defs, so both invariants thread.
          assert acts1 == [LS.Areg(r1)] + ([LS.Aclose(gid)] + cont);
          LkBodyGroupsActsCons(LS.Areg(r), cont); LkBodyGroupsActsCons(LS.Areg(r1), [LS.Aclose(gid)] + cont); LkBodyGroupsActsCons(LS.Aclose(gid), cont);
          OuterDefsActsCons(LS.Areg(r), cont); OuterDefsActsCons(LS.Areg(r1), [LS.Aclose(gid)] + cont); OuterDefsActsCons(LS.Aclose(gid), cont);
          assert L.DefGroups(r) == [gid] + L.DefGroups(r1);
          assert gid in OuterDefsActs(acts) && gid !in LkBodyGroupsActs(acts);   // OuterLkDisjoint
          assert LkBodyGroupsActs(acts1) == LkBodyGroupsActs(acts);
          assert LkClosedInGm(gm2, acts1) by {
            forall g | g in gm2 && g in LkBodyGroupsActs(acts1) ensures gm2[g].endIdx.Some? {
              assert g != gid; assert g in gm && g in LkBodyGroupsActs(acts);
            }
          }
          assert OuterLkDisjoint(acts1);
          assert NoDupSeq(L.DefGroups(r)) && L.DefGroups(r) == [gid] + L.DefGroups(r1);
          NoDupTailSeq([gid], L.DefGroups(r1));   // drop the leading [gid] ⇒ NoDupSeq(DefGroups(r1))
          assert NoDupRegsActs(acts1) by { forall i | 0 <= i < |acts1| ensures acts1[i].Areg? ==> NoDupSeq(L.DefGroups(acts1[i].r)) { if i < 2 {} else { assert acts1[i] == cont[i - 2]; } } }
          assert TRM.GmInBounds(gm2, n) by { assert LC.Idx(inp) <= n; }
          FirstLeafClosed(rer, acts1, inp, b, t.t, gm2, leaf);
        case AnchorR(a) =>
          if LS.AnchorSatisfied(rer, a, inp) {
            assert t.AnchorPass?;
            assert PendingCloses(acts) == PendingCloses(cont);
            TailInv(gm, gm, acts);
            FirstLeafClosed(rer, cont, inp, b, t.t, gm, leaf);
          } else {
            assert t == LT.Mismatch;
            assert false;
          }
        case LookaroundR(lk, r1) =>
          // L3a: a positive-forward lookahead body may CAPTURE. A positive look
          // hands the continuation the body's first-leaf map (captures merged, all
          // CLOSED); a negative look the entry map. OpenOf carries through via
          // LookBodyLeafOpenSub; the invariants thread because the look closes its
          // own groups and outer groups stay disjoint from look groups.
          var S := (set g | g in L.DefGroups(r1));
          match t {
            case LK(lk2, tlk, tc) =>
              assert PendingCloses(acts) == PendingCloses(cont);
              assert EL.LkGateOk(rer, lk, r1, inp, tlk, true) && EL.BoolTreeLk(rer, cont, inp, b, tc);
              assert tlk == FU.ComputeTr(rer, [LS.Areg(r1)], inp, LG.Empty, L.LkDir(lk));
              assert EL.PikeLkRegex(r);
              var dir := L.LkDir(lk);
              LkBodyGroupsActsCons(LS.Areg(r), cont); OuterDefsActsCons(LS.Areg(r), cont);
              assert L.DefGroups(r) == L.DefGroups(r1);
              assert LL.LkBodyGroups(r) == S + LL.LkBodyGroups(r1);
              assert S <= LkBodyGroupsActs(acts);
              assert LkBodyGroupsActs(cont) <= LkBodyGroupsActs(acts);
              assert OuterDefsActs(cont) <= OuterDefsActs(acts);
              // L3a/L3b: a POSITIVE look (fwd/bwd) may capture -> NoLkBrL body from
              // the widened PikeLkRegex; a NEGATIVE look is group-free. (The old
              // `DefGroups(r1) != [] ==> dir == Forward` "only lookaheads capture"
              // conjunct is retired for L3b -- lookbehinds capture too.)
              assert EL.NoLkBrL(r1) && EL.PikeLkRegex(r1) by {
                if L.Positivity(lk) { NoLkBrImpliesPikeLk(r1); }
                else { assert SD.GroupFreeL(r1); LL.GroupFreeLkBodyEmpty(r1); GroupFreeImpliesNoLkBr(r1); NoLkBrImpliesPikeLk(r1); }
              }
              assert OuterLkDisjoint(cont);
              if L.Positivity(lk) {
                assert forall g :: g in gm && g in S ==> gm[g].endIdx.Some? by {
                  forall g | g in gm && g in S ensures gm[g].endIdx.Some? { assert g in LkBodyGroupsActs(acts); }
                }
                var sub := LT.TreeLeaves(tlk, gm, inp, dir);
                LT.FirstTreeLeaf(tlk, gm, inp, dir);
                assert |sub| > 0;                            // else TreeRes(t, ..) would be None
                // L3b NoDupG: acts[0]=Areg(r), r=LookaroundR(lk,r1), DefGroups(r)==DefGroups(r1);
                // NoDupRegsActs(acts) ⇒ NoDupSeq(DefGroups(r1)) ⇒ CDE.NoDupG(DefGroups(r1)).
                assert NoDupSeq(L.DefGroups(r1)) by { assert NoDupSeq(L.DefGroups(r)); assert L.DefGroups(r) == L.DefGroups(r1); }
                NoDupSeqIsNoDupG(L.DefGroups(r1));
                LookBodyLeafOpenSub(rer, lk, r1, tlk, gm, inp, sub, S);
                assert LT.TreeRes(tc, sub[0].1, inp, WP.Forward) == Some(leaf);  // LK positive unfold
                assert LkClosedInGm(sub[0].1, cont) by {
                  forall g | g in sub[0].1 && g in LkBodyGroupsActs(cont) ensures sub[0].1[g].endIdx.Some? {
                    if g in S {} else { assert g in gm; assert g in LkBodyGroupsActs(acts); assert g !in OpenOf(gm); assert g !in OpenOf(sub[0].1); }
                  }
                }
                FirstLeafClosed(rer, cont, inp, b, tc, sub[0].1, leaf);
              } else {
                assert LT.TreeRes(tc, gm, inp, WP.Forward) == Some(leaf);        // LK negative unfold
                assert LkClosedInGm(gm, cont) by {
                  forall g | g in gm && g in LkBodyGroupsActs(cont) ensures gm[g].endIdx.Some? { assert g in LkBodyGroupsActs(acts); }
                }
                FirstLeafClosed(rer, cont, inp, b, tc, gm, leaf);
              }
            case LKFail(lk2, tlk) =>
              assert false;                    // LKFail has no leaves
            case _ =>
          }
        case Backreference(_) =>
          assert false;
    }
  }

  /** The value-confinement predicate (S-ii core): every SETTLED inside-look
      group (`g in S`, `g` present in `gm`, `g`'s look no longer pending in
      `acts`) has its `gm` value preserved into the final leaf. */
  ghost predicate ValConf(gm: LG.GroupMap, acts: LS.Actions, leaf: LT.Leaf, S: set<LG.GroupId>) {
    forall g :: g in gm && g in S && g !in LkBodyGroupsActs(acts) ==>
      g in leaf.1 && leaf.1[g] == gm[g]
  }

  /** One induction step of `ValConf`: given the child holds `ValConf` and each
      settled `S`-group agrees (`gm2[g]==gm[g]`, still settled in `sub`), the
      parent holds `ValConf`. Pure bookkeeping — isolates the per-case bridge. */
  lemma ConfineStep(gm: LG.GroupMap, gm2: LG.GroupMap, acts: LS.Actions, sub: LS.Actions,
                    leaf: LT.Leaf, S: set<LG.GroupId>)
    requires ValConf(gm2, sub, leaf, S)
    requires forall g :: g in gm && g in S && g !in LkBodyGroupsActs(acts) ==>
               g in gm2 && gm2[g] == gm[g] && g !in LkBodyGroupsActs(sub)
    ensures ValConf(gm, acts, leaf, S)
  {}

  /** S-ii value-confinement least-lemma: the value analogue of
      `FirstLeafClosed`. Same recursion / same invariants (so `TailInv`/`SubInv`/
      `QuantSubInv`/`QuantSubInvCheck` are reused), but ALSO concludes `ValConf`:
      a settled inside-look group's value survives to the leaf. The LK case leans
      on `LL.GmConfinedLeaves` (the look writes only its OWN groups `S_look`, so a
      settled `g !in S_look` passes through); the Quant `GMReset` case uses the
      `DefGroups = DefGroupsOutside (+) LkBodyGroups` split (a settled `S`-group in
      `DefGroups(r1)` would be pending, contradiction). Vacuous at `gm==Empty`; an
      existential-extraction layer turns it into the per-look leaf-value equality
      the else-branch consumes. */
  least lemma FirstLeafValueConfined(rer: LW.RegExpRecord, acts: LS.Actions, inp: LC.Input,
                                     b: BS.LoopBool, t: LT.Tree, gm: LG.GroupMap, leaf: LT.Leaf,
                                     S: set<LG.GroupId>)
    requires EL.BoolTreeLk(rer, acts, inp, b, t)
    requires EL.PikeLkActions(acts)
    requires OpenOf(gm) <= PendingCloses(acts)
    requires LT.TreeRes(t, gm, inp, WP.Forward) == Some(leaf)
    requires LkClosedInGm(gm, acts)
    requires OuterLkDisjoint(acts)
    requires forall g :: g in S ==> g !in OuterDefsActs(acts)   // S = inside-look groups
    requires NoDupRegsActs(acts)                // L3b: each pending regex has dup-free groups (for NoDupG)
    requires TRM.GmInBounds(gm, |inp.pref| + |inp.next|)   // L3b: gm ranges within input (for the mirror)
    ensures ClosedGm(leaf.1)
    ensures ValConf(gm, acts, leaf, S)
  {
    var n := |inp.pref| + |inp.next|;
    if |acts| == 0 {
      assert t == LT.Match;
      assert leaf.1 == gm;
      assert PendingCloses(acts) == {};
      forall g | g in gm ensures gm[g].endIdx.Some? {
        if gm[g].endIdx.None? { assert g in OpenOf(gm); }
      }
      assert LkBodyGroupsActs(acts) == {};
    } else {
      var cont := acts[1..];
      assert forall i :: 0 <= i < |cont| ==> cont[i] == acts[i + 1];
      assert PendingCloses(cont) <= PendingCloses(acts);
      assert NoDupRegsActs(cont) by { forall i | 0 <= i < |cont| ensures cont[i].Areg? ==> NoDupSeq(L.DefGroups(cont[i].r)) { assert cont[i] == acts[i + 1]; } }
      match acts[0]
      case Acheck(strcheck) =>
        if b == BS.CanExit {
          assert t.Progress?;
          assert PendingCloses(acts) == PendingCloses(cont);
          TailInv(gm, gm, acts);
          assert LkBodyGroupsActs(acts) == LkBodyGroupsActs(cont);   // Acheck contributes {}
          FirstLeafValueConfined(rer, cont, inp, BS.CanExit, t.t, gm, leaf, S);
          ConfineStep(gm, gm, acts, cont, leaf, S);
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
        assert forall g :: g in gm2 ==> g in gm && (gm2[g].endIdx.Some? || gm2[g] == gm[g]);
        TailInv(gm, gm2, acts);
        assert gid in OuterDefsActs(acts);
        assert LkBodyGroupsActs(acts) == LkBodyGroupsActs(cont);   // Aclose contributes {}
        assert TRM.GmInBounds(gm2, n) by { assert LC.Idx(inp) <= n; }
        FirstLeafValueConfined(rer, cont, inp, b, t.t, gm2, leaf, S);
        assert forall g :: g in gm && g in S && g !in LkBodyGroupsActs(acts) ==>
                 g in gm2 && gm2[g] == gm[g] && g !in LkBodyGroupsActs(cont)
        by { forall g | g in gm && g in S && g !in LkBodyGroupsActs(acts) ensures g != gid { } }
        ConfineStep(gm, gm2, acts, cont, leaf, S);
      case Areg(r) =>
        match r
        case Epsilon =>
          assert PendingCloses(acts) == PendingCloses(cont);
          TailInv(gm, gm, acts);
          assert LkBodyGroupsActs(acts) == LkBodyGroupsActs(cont);
          FirstLeafValueConfined(rer, cont, inp, b, t, gm, leaf, S);
          ConfineStep(gm, gm, acts, cont, leaf, S);
        case Character(cd) =>
          if LC.ReadChar(rer, cd, inp, WP.Forward).None? {
            assert t == LT.Mismatch;
            assert false;
          } else {
            var pair := LC.ReadChar(rer, cd, inp, WP.Forward).value;
            assert t.Read?;
            assert pair.1 == LC.AdvanceInputP(inp, WP.Forward);
            assert |pair.1.pref| + |pair.1.next| == n;   // advance preserves total length
            assert PendingCloses(acts) == PendingCloses(cont);
            TailInv(gm, gm, acts);
            assert LkBodyGroupsActs(acts) == LkBodyGroupsActs(cont);
            FirstLeafValueConfined(rer, cont, pair.1, BS.CanExit, t.t, gm, leaf, S);
            ConfineStep(gm, gm, acts, cont, leaf, S);
          }
        case Disjunction(r1, r2) =>
          assert t.Choice?;
          var acts1 := [LS.Areg(r1)] + cont;
          var acts2 := [LS.Areg(r2)] + cont;
          assert PendingCloses(acts1) == PendingCloses(cont) == PendingCloses(acts2) by {
            assert forall i :: 0 <= i < |cont| ==> acts1[i + 1] == cont[i] && acts2[i + 1] == cont[i];
          }
          assert PendingCloses(acts) == PendingCloses(cont);
          LkBodyGroupsActsCons(LS.Areg(r), cont); LkBodyGroupsActsCons(LS.Areg(r1), cont); LkBodyGroupsActsCons(LS.Areg(r2), cont);
          OuterDefsActsCons(LS.Areg(r), cont); OuterDefsActsCons(LS.Areg(r1), cont); OuterDefsActsCons(LS.Areg(r2), cont);
          assert LL.LkBodyGroups(r) == LL.LkBodyGroups(r1) + LL.LkBodyGroups(r2);
          assert DefGroupsOutsideLooksL(r) == DefGroupsOutsideLooksL(r1) + DefGroupsOutsideLooksL(r2);
          assert NoDupSeq(L.DefGroups(r)) && L.DefGroups(r) == L.DefGroups(r1) + L.DefGroups(r2);
          NoDupConcat(L.DefGroups(r1), L.DefGroups(r2));
          assert NoDupRegsActs(acts1) by { forall i | 0 <= i < |acts1| ensures acts1[i].Areg? ==> NoDupSeq(L.DefGroups(acts1[i].r)) { if i == 0 {} else { assert acts1[i] == cont[i - 1]; } } }
          assert NoDupRegsActs(acts2) by { forall i | 0 <= i < |acts2| ensures acts2[i].Areg? ==> NoDupSeq(L.DefGroups(acts2[i].r)) { if i == 0 {} else { assert acts2[i] == cont[i - 1]; } } }
          if LT.TreeRes(t.t1, gm, inp, WP.Forward).Some? {
            SubInv(gm, gm, acts1, acts);
            FirstLeafValueConfined(rer, acts1, inp, b, t.t1, gm, leaf, S);
            ConfineStep(gm, gm, acts, acts1, leaf, S);
          } else {
            SubInv(gm, gm, acts2, acts);
            FirstLeafValueConfined(rer, acts2, inp, b, t.t2, gm, leaf, S);
            ConfineStep(gm, gm, acts, acts2, leaf, S);
          }
        case Sequence(r1, r2) =>
          var acts1 := [LS.Areg(r1), LS.Areg(r2)] + cont;
          assert PendingCloses(acts1) == PendingCloses(cont) by {
            assert forall i :: 0 <= i < |cont| ==> acts1[i + 2] == cont[i];
          }
          assert PendingCloses(acts) == PendingCloses(cont);
          assert acts1 == [LS.Areg(r1)] + ([LS.Areg(r2)] + cont);
          LkBodyGroupsActsCons(LS.Areg(r), cont); LkBodyGroupsActsCons(LS.Areg(r1), [LS.Areg(r2)] + cont); LkBodyGroupsActsCons(LS.Areg(r2), cont);
          OuterDefsActsCons(LS.Areg(r), cont); OuterDefsActsCons(LS.Areg(r1), [LS.Areg(r2)] + cont); OuterDefsActsCons(LS.Areg(r2), cont);
          assert LL.LkBodyGroups(r) == LL.LkBodyGroups(r1) + LL.LkBodyGroups(r2);
          assert DefGroupsOutsideLooksL(r) == DefGroupsOutsideLooksL(r1) + DefGroupsOutsideLooksL(r2);
          assert NoDupSeq(L.DefGroups(r)) && L.DefGroups(r) == L.DefGroups(r1) + L.DefGroups(r2);
          NoDupConcat(L.DefGroups(r1), L.DefGroups(r2));
          assert NoDupRegsActs(acts1) by { forall i | 0 <= i < |acts1| ensures acts1[i].Areg? ==> NoDupSeq(L.DefGroups(acts1[i].r)) { if i < 2 {} else { assert acts1[i] == cont[i - 2]; } } }
          SubInv(gm, gm, acts1, acts);
          FirstLeafValueConfined(rer, acts1, inp, b, t, gm, leaf, S);
          ConfineStep(gm, gm, acts, acts1, leaf, S);
        case Quantified(greedy, min, delta, r1) =>
          var gidl := L.DefGroups(r1);
          if min > 0 {
            assert t.GroupActionT? && t.g == LG.Reset(gidl);
            var gm2 := LG.GMUpdate(t.g, LC.Idx(inp), gm);
            assert gm2 == LG.GMReset(gidl, gm);
            assert OpenOf(gm2) <= OpenOf(gm);
            assert forall g :: g in gm2 ==> g in gm && gm2[g] == gm[g];
            var q' := L.Quantified(greedy, min - 1, delta, r1);
            var acts1 := [LS.Areg(r1), LS.Areg(q')] + cont;
            assert PendingCloses(acts1) == PendingCloses(cont) by {
              assert forall i :: 0 <= i < |cont| ==> acts1[i + 2] == cont[i];
            }
            assert PendingCloses(acts) == PendingCloses(cont);
            assert NoDupSeq(L.DefGroups(r)) && L.DefGroups(r) == L.DefGroups(r1) && L.DefGroups(q') == L.DefGroups(r1);
            assert NoDupRegsActs(acts1) by { forall i | 0 <= i < |acts1| ensures acts1[i].Areg? ==> NoDupSeq(L.DefGroups(acts1[i].r)) { if i < 2 {} else { assert acts1[i] == cont[i - 2]; } } }
            assert TRM.GmInBounds(gm2, n);   // GMReset only shrinks the domain
            QuantSubInv(gm, gm2, r, r1, q', cont, acts, acts1);
            QuantConfBridge(r, r1, q', gm, cont, acts, acts1, S);
            FirstLeafValueConfined(rer, acts1, inp, b, t.t, gm2, leaf, S);
            assert forall g :: g in gm && g in S && g !in LkBodyGroupsActs(acts) ==>
                     g in gm2 && gm2[g] == gm[g] && g !in LkBodyGroupsActs(acts1)
            by {
              forall g | g in gm && g in S && g !in LkBodyGroupsActs(acts) ensures g !in gidl {
                QuantSettledNotReset(r, r1, cont, acts, S, g);
              }
            }
            ConfineStep(gm, gm2, acts, acts1, leaf, S);
          } else if delta == LN.NN(0) {
            assert PendingCloses(acts) == PendingCloses(cont);
            TailInv(gm, gm, acts);
            LkBodyGroupsActsCons(LS.Areg(r), cont);
            FirstLeafValueConfined(rer, cont, inp, b, t, gm, leaf, S);
            ConfineStep(gm, gm, acts, cont, leaf, S);
          } else {
            assert t.Choice?;
            var itert := if greedy then t.t1 else t.t2;
            var skipt := if greedy then t.t2 else t.t1;
            assert itert.GroupActionT? && itert.g == LG.Reset(gidl);
            assert PendingCloses(acts) == PendingCloses(cont);
            if LT.TreeRes(t.t1, gm, inp, WP.Forward).Some? {
              if greedy {
                var gm2 := LG.GMUpdate(itert.g, LC.Idx(inp), gm);
                assert gm2 == LG.GMReset(gidl, gm);
                assert OpenOf(gm2) <= OpenOf(gm);
                assert forall g :: g in gm2 ==> g in gm && gm2[g] == gm[g];
                var q'' := L.Quantified(greedy, 0, LFS.NoiPred(delta), r1);
                var acts1 := [LS.Areg(r1), LS.Acheck(inp), LS.Areg(q'')] + cont;
                assert PendingCloses(acts1) == PendingCloses(cont) by {
                  assert forall i :: 0 <= i < |cont| ==> acts1[i + 3] == cont[i];
                }
                assert NoDupSeq(L.DefGroups(r)) && L.DefGroups(r) == L.DefGroups(r1) && L.DefGroups(q'') == L.DefGroups(r1);
                assert NoDupRegsActs(acts1) by { forall i | 0 <= i < |acts1| ensures acts1[i].Areg? ==> NoDupSeq(L.DefGroups(acts1[i].r)) { if i < 3 {} else { assert acts1[i] == cont[i - 3]; } } }
                assert TRM.GmInBounds(gm2, n);
                QuantSubInvCheck(gm, gm2, r, r1, q'', inp, cont, acts, acts1);
                QuantCheckConfBridge(r, r1, q'', inp, gm, cont, acts, acts1, S);
                FirstLeafValueConfined(rer, acts1, inp, BS.CannotExit, itert.t, gm2, leaf, S);
                assert forall g :: g in gm && g in S && g !in LkBodyGroupsActs(acts) ==>
                         g in gm2 && gm2[g] == gm[g] && g !in LkBodyGroupsActs(acts1)
                by {
                  forall g | g in gm && g in S && g !in LkBodyGroupsActs(acts) ensures g !in gidl {
                    QuantSettledNotReset(r, r1, cont, acts, S, g);
                  }
                }
                ConfineStep(gm, gm2, acts, acts1, leaf, S);
              } else {
                TailInv(gm, gm, acts);
                LkBodyGroupsActsCons(LS.Areg(r), cont);
                FirstLeafValueConfined(rer, cont, inp, b, skipt, gm, leaf, S);
                ConfineStep(gm, gm, acts, cont, leaf, S);
              }
            } else {
              if greedy {
                TailInv(gm, gm, acts);
                LkBodyGroupsActsCons(LS.Areg(r), cont);
                FirstLeafValueConfined(rer, cont, inp, b, skipt, gm, leaf, S);
                ConfineStep(gm, gm, acts, cont, leaf, S);
              } else {
                var gm2 := LG.GMUpdate(itert.g, LC.Idx(inp), gm);
                assert gm2 == LG.GMReset(gidl, gm);
                assert OpenOf(gm2) <= OpenOf(gm);
                assert forall g :: g in gm2 ==> g in gm && gm2[g] == gm[g];
                var q'' := L.Quantified(greedy, 0, LFS.NoiPred(delta), r1);
                var acts1 := [LS.Areg(r1), LS.Acheck(inp), LS.Areg(q'')] + cont;
                assert PendingCloses(acts1) == PendingCloses(cont) by {
                  assert forall i :: 0 <= i < |cont| ==> acts1[i + 3] == cont[i];
                }
                assert NoDupSeq(L.DefGroups(r)) && L.DefGroups(r) == L.DefGroups(r1) && L.DefGroups(q'') == L.DefGroups(r1);
                assert NoDupRegsActs(acts1) by { forall i | 0 <= i < |acts1| ensures acts1[i].Areg? ==> NoDupSeq(L.DefGroups(acts1[i].r)) { if i < 3 {} else { assert acts1[i] == cont[i - 3]; } } }
                assert TRM.GmInBounds(gm2, n);
                QuantSubInvCheck(gm, gm2, r, r1, q'', inp, cont, acts, acts1);
                QuantCheckConfBridge(r, r1, q'', inp, gm, cont, acts, acts1, S);
                FirstLeafValueConfined(rer, acts1, inp, BS.CannotExit, itert.t, gm2, leaf, S);
                assert forall g :: g in gm && g in S && g !in LkBodyGroupsActs(acts) ==>
                         g in gm2 && gm2[g] == gm[g] && g !in LkBodyGroupsActs(acts1)
                by {
                  forall g | g in gm && g in S && g !in LkBodyGroupsActs(acts) ensures g !in gidl {
                    QuantSettledNotReset(r, r1, cont, acts, S, g);
                  }
                }
                ConfineStep(gm, gm2, acts, acts1, leaf, S);
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
          assert acts1 == [LS.Areg(r1)] + ([LS.Aclose(gid)] + cont);
          LkBodyGroupsActsCons(LS.Areg(r), cont); LkBodyGroupsActsCons(LS.Areg(r1), [LS.Aclose(gid)] + cont); LkBodyGroupsActsCons(LS.Aclose(gid), cont);
          OuterDefsActsCons(LS.Areg(r), cont); OuterDefsActsCons(LS.Areg(r1), [LS.Aclose(gid)] + cont); OuterDefsActsCons(LS.Aclose(gid), cont);
          assert L.DefGroups(r) == [gid] + L.DefGroups(r1);
          assert gid in OuterDefsActs(acts) && gid !in LkBodyGroupsActs(acts);
          assert LkBodyGroupsActs(acts1) == LkBodyGroupsActs(acts);
          assert LkClosedInGm(gm2, acts1) by {
            forall g | g in gm2 && g in LkBodyGroupsActs(acts1) ensures gm2[g].endIdx.Some? {
              assert g != gid; assert g in gm && g in LkBodyGroupsActs(acts);
            }
          }
          assert OuterLkDisjoint(acts1);
          assert forall g :: g in S ==> g !in OuterDefsActs(acts1);
          assert NoDupSeq(L.DefGroups(r)) && L.DefGroups(r) == [gid] + L.DefGroups(r1);
          NoDupTailSeq([gid], L.DefGroups(r1));   // drop the leading [gid] ⇒ NoDupSeq(DefGroups(r1))
          assert NoDupRegsActs(acts1) by { forall i | 0 <= i < |acts1| ensures acts1[i].Areg? ==> NoDupSeq(L.DefGroups(acts1[i].r)) { if i < 2 {} else { assert acts1[i] == cont[i - 2]; } } }
          assert TRM.GmInBounds(gm2, n) by { assert LC.Idx(inp) <= n; }
          FirstLeafValueConfined(rer, acts1, inp, b, t.t, gm2, leaf, S);
          assert forall g :: g in gm && g in S && g !in LkBodyGroupsActs(acts) ==>
                   g in gm2 && gm2[g] == gm[g] && g !in LkBodyGroupsActs(acts1)
          by { forall g | g in gm && g in S && g !in LkBodyGroupsActs(acts) ensures g != gid { } }
          ConfineStep(gm, gm2, acts, acts1, leaf, S);
        case AnchorR(a) =>
          if LS.AnchorSatisfied(rer, a, inp) {
            assert t.AnchorPass?;
            assert PendingCloses(acts) == PendingCloses(cont);
            TailInv(gm, gm, acts);
            LkBodyGroupsActsCons(LS.Areg(r), cont);
            FirstLeafValueConfined(rer, cont, inp, b, t.t, gm, leaf, S);
            ConfineStep(gm, gm, acts, cont, leaf, S);
          } else {
            assert t == LT.Mismatch;
            assert false;
          }
        case LookaroundR(lk, r1) =>
          var Slook := (set g | g in L.DefGroups(r1));
          match t {
            case LK(lk2, tlk, tc) =>
              assert PendingCloses(acts) == PendingCloses(cont);
              assert EL.LkGateOk(rer, lk, r1, inp, tlk, true) && EL.BoolTreeLk(rer, cont, inp, b, tc);
              assert tlk == FU.ComputeTr(rer, [LS.Areg(r1)], inp, LG.Empty, L.LkDir(lk));
              assert EL.PikeLkRegex(r);
              var dir := L.LkDir(lk);
              LkBodyGroupsActsCons(LS.Areg(r), cont); OuterDefsActsCons(LS.Areg(r), cont);
              assert L.DefGroups(r) == L.DefGroups(r1);
              assert LL.LkBodyGroups(r) == Slook + LL.LkBodyGroups(r1);
              assert Slook <= LkBodyGroupsActs(acts);
              assert LkBodyGroupsActs(cont) <= LkBodyGroupsActs(acts);
              assert OuterDefsActs(cont) <= OuterDefsActs(acts);
              // L3a/L3b: a POSITIVE look (fwd/bwd) may capture -> NoLkBrL body from
              // the widened PikeLkRegex; a NEGATIVE look is group-free. (The old
              // `DefGroups(r1) != [] ==> dir == Forward` "only lookaheads capture"
              // conjunct is retired for L3b -- lookbehinds capture too.)
              assert EL.NoLkBrL(r1) && EL.PikeLkRegex(r1) by {
                if L.Positivity(lk) { NoLkBrImpliesPikeLk(r1); }
                else { assert SD.GroupFreeL(r1); LL.GroupFreeLkBodyEmpty(r1); GroupFreeImpliesNoLkBr(r1); NoLkBrImpliesPikeLk(r1); }
              }
              assert OuterLkDisjoint(cont);
              assert forall g :: g in S ==> g !in OuterDefsActs(cont);
              if L.Positivity(lk) {
                assert forall g :: g in gm && g in Slook ==> gm[g].endIdx.Some? by {
                  forall g | g in gm && g in Slook ensures gm[g].endIdx.Some? { assert g in LkBodyGroupsActs(acts); }
                }
                var sub := LT.TreeLeaves(tlk, gm, inp, dir);
                LT.FirstTreeLeaf(tlk, gm, inp, dir);
                assert |sub| > 0;
                // L3b NoDupG: DefGroups(r)==DefGroups(r1); NoDupRegsActs(acts) ⇒ NoDupSeq(DefGroups(r1)).
                assert NoDupSeq(L.DefGroups(r1)) by { assert NoDupSeq(L.DefGroups(r)); assert L.DefGroups(r) == L.DefGroups(r1); }
                NoDupSeqIsNoDupG(L.DefGroups(r1));
                LookBodyLeafOpenSub(rer, lk, r1, tlk, gm, inp, sub, Slook);
                assert LT.TreeRes(tc, sub[0].1, inp, WP.Forward) == Some(leaf);
                assert LkClosedInGm(sub[0].1, cont) by {
                  forall g | g in sub[0].1 && g in LkBodyGroupsActs(cont) ensures sub[0].1[g].endIdx.Some? {
                    if g in Slook {} else { assert g in gm; assert g in LkBodyGroupsActs(acts); assert g !in OpenOf(gm); assert g !in OpenOf(sub[0].1); }
                  }
                }
                // gm2 = sub[0].1 agrees with gm OUTSIDE Slook (the look writes only its own groups)
                assert LL.DefGroupsIn(r1, Slook);
                LL.ComputeTrConfined(rer, r1, inp, LG.Empty, dir, Slook);
                LL.GmConfinedLeaves(tlk, gm, inp, dir, Slook);
                FirstLeafValueConfined(rer, cont, inp, b, tc, sub[0].1, leaf, S);
                assert forall g :: g in gm && g in S && g !in LkBodyGroupsActs(acts) ==>
                         g in sub[0].1 && sub[0].1[g] == gm[g] && g !in LkBodyGroupsActs(cont)
                by {
                  forall g | g in gm && g in S && g !in LkBodyGroupsActs(acts)
                    ensures g in sub[0].1 && sub[0].1[g] == gm[g]
                  { assert g !in Slook; assert LL.GmAgreeOutside(sub[0].1, gm, Slook); }
                }
                ConfineStep(gm, sub[0].1, acts, cont, leaf, S);
              } else {
                assert LT.TreeRes(tc, gm, inp, WP.Forward) == Some(leaf);
                assert LkClosedInGm(gm, cont) by {
                  forall g | g in gm && g in LkBodyGroupsActs(cont) ensures gm[g].endIdx.Some? { assert g in LkBodyGroupsActs(acts); }
                }
                FirstLeafValueConfined(rer, cont, inp, b, tc, gm, leaf, S);
                ConfineStep(gm, gm, acts, cont, leaf, S);
              }
            case LKFail(lk2, tlk) =>
              assert false;
            case _ =>
          }
        case Backreference(_) =>
          assert false;
    }
  }

  /** Quant `min>0` reset bridge: `LkBodyGroupsActs(acts1) == LkBodyGroupsActs(acts)`
      when `acts = [Areg(Quant r1)] + cont` and `acts1 = [Areg(r1), Areg(q')] + cont`
      with `q' = Quant(...,r1)` (both contribute `LkBodyGroups(r1)`). */
  lemma QuantConfBridge(r: L.Regex, r1: L.Regex, q': L.Regex, gm: LG.GroupMap,
                        cont: LS.Actions, acts: LS.Actions, acts1: LS.Actions, S: set<LG.GroupId>)
    requires r.Quantified? && r.r1 == r1 && q'.Quantified? && q'.r1 == r1
    requires acts == [LS.Areg(r)] + cont && acts1 == [LS.Areg(r1), LS.Areg(q')] + cont
    requires forall g :: g in S ==> g !in OuterDefsActs(acts)
    ensures LkBodyGroupsActs(acts1) == LkBodyGroupsActs(acts)
    ensures forall g :: g in S ==> g !in OuterDefsActs(acts1)
  {
    assert acts1 == [LS.Areg(r1)] + ([LS.Areg(q')] + cont);
    LkBodyGroupsActsCons(LS.Areg(r), cont);
    LkBodyGroupsActsCons(LS.Areg(r1), [LS.Areg(q')] + cont);
    LkBodyGroupsActsCons(LS.Areg(q'), cont);
    OuterDefsActsCons(LS.Areg(r), cont);
    OuterDefsActsCons(LS.Areg(r1), [LS.Areg(q')] + cont);
    OuterDefsActsCons(LS.Areg(q'), cont);
    assert LL.LkBodyGroups(r) == LL.LkBodyGroups(r1) && LL.LkBodyGroups(q') == LL.LkBodyGroups(r1);
    assert DefGroupsOutsideLooksL(r) == DefGroupsOutsideLooksL(r1) && DefGroupsOutsideLooksL(q') == DefGroupsOutsideLooksL(r1);
    assert LkBodyGroupsActs(acts1) == LkBodyGroupsActs(acts);
    assert OuterDefsActs(acts1) == OuterDefsActs(acts);
  }

  /** Quant `min==0` Choice reset bridge (with the `Acheck`): same as
      `QuantConfBridge` but `acts1 = [Areg(r1), Acheck, Areg(q'')] + cont`. */
  lemma QuantCheckConfBridge(r: L.Regex, r1: L.Regex, q'': L.Regex, inp: LC.Input, gm: LG.GroupMap,
                             cont: LS.Actions, acts: LS.Actions, acts1: LS.Actions, S: set<LG.GroupId>)
    requires r.Quantified? && r.r1 == r1 && q''.Quantified? && q''.r1 == r1
    requires acts == [LS.Areg(r)] + cont && acts1 == [LS.Areg(r1), LS.Acheck(inp), LS.Areg(q'')] + cont
    requires forall g :: g in S ==> g !in OuterDefsActs(acts)
    ensures LkBodyGroupsActs(acts1) == LkBodyGroupsActs(acts)
    ensures forall g :: g in S ==> g !in OuterDefsActs(acts1)
  {
    assert acts1 == [LS.Areg(r1)] + ([LS.Acheck(inp), LS.Areg(q'')] + cont);
    assert [LS.Acheck(inp), LS.Areg(q'')] + cont == [LS.Acheck(inp)] + ([LS.Areg(q'')] + cont);
    LkBodyGroupsActsCons(LS.Areg(r), cont);
    LkBodyGroupsActsCons(LS.Areg(r1), [LS.Acheck(inp), LS.Areg(q'')] + cont);
    LkBodyGroupsActsCons(LS.Acheck(inp), [LS.Areg(q'')] + cont);
    LkBodyGroupsActsCons(LS.Areg(q''), cont);
    OuterDefsActsCons(LS.Areg(r), cont);
    OuterDefsActsCons(LS.Areg(r1), [LS.Acheck(inp), LS.Areg(q'')] + cont);
    OuterDefsActsCons(LS.Acheck(inp), [LS.Areg(q'')] + cont);
    OuterDefsActsCons(LS.Areg(q''), cont);
    assert LL.LkBodyGroups(r) == LL.LkBodyGroups(r1) && LL.LkBodyGroups(q'') == LL.LkBodyGroups(r1);
    assert DefGroupsOutsideLooksL(r) == DefGroupsOutsideLooksL(r1) && DefGroupsOutsideLooksL(q'') == DefGroupsOutsideLooksL(r1);
    assert LkBodyGroupsActs(acts1) == LkBodyGroupsActs(acts);
    assert OuterDefsActs(acts1) == OuterDefsActs(acts);
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

  /** A whole search preserves register WELL-FORMEDNESS (`ThreadRegsWf` -- array
      lengths `ncap`/`nlook`/`nquant` and `CapRegWf`). Unlike `FFindMatchThreadFacts`
      this needs NO clock bound (`FAdvanceEpsilon/FConsumeRegsWf` want only
      `clock >= 0`), so it applies to the ACTUAL FLookLoop replay from a threaded
      `cap` whose clocks may exceed 0 -- pinning the fold's register lengths. */
  lemma FFindMatchRegsWf(c: RB.code, str: string, s: AI.VmState, ov: LOr.OracleView,
                         dir: LAnc.direction, cdn: LCdn.cdns, ncap: int, nlook: int, nquant: int)
    requires |s.processed.true_set| == RB.size(c) && |s.processed.false_set| == RB.size(c)
    requires dir.Forward? ==> s.context.nextchar == AI.get_char(str, s.cp)
    requires dir.Backward? ==> s.context.nextchar == AI.get_char(str, s.cp - 1)
    requires s.clock >= 0 && s.cp >= 0
    requires CM.VmRegsWf(s, ncap, nlook, nquant)
    ensures var r := AI.FFindMatch(c, str, s, ov, dir, cdn).0;
      r.Some? ==> CM.ThreadRegsWf(r.value, ncap, nlook, nquant)
    decreases if dir.Forward? then |str| - s.cp else s.cp
  {
    var s0 := s.(cdn := LCdn.build_cdn_v(cdn, s.cp, ov, s.context, dir));
    assert CM.VmRegsWf(s0, ncap, nlook, nquant);
    CM.FAdvanceEpsilonClockGrows(c, s0, ov, dir);
    CM.FAdvanceEpsilonRegsWf(c, s0, ov, dir, ncap, nlook, nquant);
    var (s1, ov1) := AI.FAdvanceEpsilon(c, s0, ov, dir);
    assert s1.cp == s.cp && s1.context == s.context;
    assert s1.clock >= s0.clock >= 0;
    if |s1.blocked| == 0 {
      assert AI.FFindMatch(c, str, s, ov, dir, cdn).0 == s1.bestmatch;
    } else if s1.context.nextchar.None? {
      assert AI.FFindMatch(c, str, s, ov, dir, cdn).0 == s1.bestmatch;
    } else {
      CM.FConsumeRegsWf(s1, ncap, nlook, nquant);
      var s2 := AI.FConsume(s1);
      var s3 := s2.(processed := AI.init_bpcset(RB.size(c)), isblocked := AI.init_pcset(RB.size(c)),
                    cdn := LCdn.init_cdn(), cp := AI.incr_cp(s2.cp, dir));
      var newchar := AI.get_char(str, s3.cp - AI.cp_offset(dir));
      var s4 := s3.(context := LAnc.update_context(s3.context, newchar));
      assert CM.VmRegsWf(s4, ncap, nlook, nquant) by {
        assert s4.active == s2.active && s4.blocked == s2.blocked && s4.bestmatch == s2.bestmatch;
      }
      assert s4.clock == s2.clock == s1.clock >= 0;
      FFindMatchRegsWf(c, str, s4, ov1, dir, cdn, ncap, nlook, nquant);
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

  // ===========================================================================
  // §4b: run the simulation on a body from an ARBITRARY start position `cp`.
  // ===========================================================================
  //
  // `MainTheorem` runs `InitialPikeInvFullRE` + `FindMatchSimRE` from cp==0 to
  // pin the whole-regex answer to the spec first leaf. For a captured lookahead
  // (§4b) the *body* is matched from the lookaround's recorded position `cp`,
  // with FRESH registers, so we need the same pin at an arbitrary `cp`. This is
  // now bounded: `FindMatchSimRE` was always written cp-generically (it decreases
  // `|str| - vms.cp` and uses `vms.cp` abstractly), and the only piece hard-coded
  // to cp==0 was the entry invariant — now generalized as
  // `InitialPikeInvFullREAtCp`. The bridge from the search trace to the checked
  // tree's first leaf (`TrcREToLinden` -> `TreeRepPikeSubtree` -> `InitPiketreeInv`
  // -> `PikeTreeTrcCorrect`) needs only `PikeSubtree(tstar)`, so the checked tree
  // enters only through `TreeThreadRE`/`TreeRepRE` hypotheses.
  /** The cp-generalized simulation pin: from the entry state at `cp` (fresh
      registers), the best-match thread of `FFindMatch` corresponds to the
      body's checked-tree first leaf at `InpOfCp(str, cp)`. The `cp==0` special
      case is the core of `MainTheorem`'s extraction; this is the reusable form
      the captured-lookahead body match needs. */
  lemma FindMatchBodyAtCp(
      rer: LW.RegExpRecord, qm: AR.QMap, body: R.regex, bodycode: RB.code, endl: nat,
      ngroups: nat, str: string, cp: nat, tstar: LT.Tree, ov: LOr.OracleView,
      cdns: LCdn.cdns, ncap: int, nlook: int, nquant: int)
    returns (bestT: Option<LT.Leaf>)
    requires PSM.StaticOkRE(qm, body, bodycode, endl)
    requires PSM.SizesOkRE(body, ncap, nlook, nquant)
    requires qm.ov == ov
    requires !rer.ignoreCase && !rer.multiline
    requires cp <= |str|
    requires bodycode == CP.compile_to_bytecode(body)
    requires TT.TreeThreadRE(rer, qm, bodycode, PIV.InpOfCp(str, cp), tstar, 0, false)
    requires TR.TreeRepRE(qm, tstar, bodycode, 0, PIV.InpOfCp(str, cp), false)
    ensures var inp := PIV.InpOfCp(str, cp);
            var inits := AI.FInitState(bodycode, cp, AReg.init_regs(ncap), AReg.init_regs(nlook),
                                       AReg.init_regs(nquant), 0, AI.cp_context(cp, str, LAnc.Forward));
            PIV.BestMatchRE(body, bestT, AI.FFindMatch(bodycode, str, inits, ov, LAnc.Forward, cdns).0)
            && bestT == LT.FirstLeaf(tstar, inp)
  {
    var inp := PIV.InpOfCp(str, cp);
    var ctx := AI.cp_context(cp, str, LAnc.Forward);
    var capture := AReg.init_regs(ncap);
    var look := AReg.init_regs(nlook);
    var quant := AReg.init_regs(nquant);
    var inits := AI.FInitState(bodycode, cp, capture, look, quant, 0, ctx);

    // Entry invariant at cp (fresh registers) -> the full simulation invariant.
    PSM.InitialPikeInvFullREAtCp(rer, qm, body, bodycode, endl, ngroups, str, cp, tstar,
                                 inits, ncap, nlook, nquant);
    var pts0 := PT.PikeTreeInitialState(tstar, inp);
    assert ctx.nextchar == AI.get_char(str, cp);        // cp_context definitional
    bestT := PSM.FindMatchSimRE(rer, qm, body, bodycode, endl, ngroups, str, pts0, inits,
                                ov, LAnc.Forward, cdns, ncap, nlook, nquant);
    assert PSM.TrcRE(pts0, PT.PTS_final(bestT));
    assert PIV.BestMatchRE(body, bestT, AI.FFindMatch(bodycode, str, inits, ov, LAnc.Forward, cdns).0);

    // Pin bestT to the checked tree's first leaf.
    TrcREToLinden(pts0, PT.PTS_final(bestT));
    TR.TreeRepPikeSubtree(qm, tstar, bodycode, 0, inp, false);
    PT.InitPiketreeInv(tstar, inp);
    CR.PikeTreeTrcCorrect(pts0, PT.PTS_final(bestT), LT.FirstLeaf(tstar, inp));
    assert bestT == LT.FirstLeaf(tstar, inp);
  }

  /** §4b, the tree-construction port: for a fragment `body` (a look-free
      capturing plus-fragment is in `LookBehindFragmentRE`, since its
      `Re_lookaround` case — which still bans captures — never fires), the body
      match from position `cp` corresponds to the body's SPEC first leaf at
      `InpOfCp(str, cp)`. This discharges `FindMatchBodyAtCp`'s `tstar`
      hypotheses by BUILDING the checked tree (mirroring `MainTheorem`'s
      1140-1166 entry construction at `body`/`cp` instead of the whole regex at
      0), so the caller need only supply the static package + the oracle
      correctness at `cp`. `TreeThreadRE` is definitionally `TreeRepRE`
      (TreeThreadRE.dfy:56), so the one tree built serves both hypotheses. */
  lemma BodyTreeAtCp(
      rer: LW.RegExpRecord, qm: AR.QMap, body: R.regex, bodycode: RB.code, endl: nat,
      ngroups: nat, str: string, cp: nat, ov: LOr.OracleView,
      cdns: LCdn.cdns, ncap: int, nlook: int, nquant: int)
    returns (bestT: Option<LT.Leaf>)
    requires PSM.StaticOkRE(qm, body, bodycode, endl)
    requires PSM.SizesOkRE(body, ncap, nlook, nquant)
    requires qm.ov == ov
    requires !rer.ignoreCase && !rer.multiline
    requires cp <= |str|
    requires bodycode == CP.compile_to_bytecode(body)
    requires NR.LookFreeRE(body)
    requires LL.OracleOkSuffix(rer, qm, PIV.InpOfCp(str, cp))
    ensures var inp := PIV.InpOfCp(str, cp);
            var t := LFU.ComputeTr(rer, [LS.Areg(T.Translate(body))], inp, LG.Empty, WP.Forward);
            var inits := AI.FInitState(bodycode, cp, AReg.init_regs(ncap), AReg.init_regs(nlook),
                                       AReg.init_regs(nquant), 0, AI.cp_context(cp, str, LAnc.Forward));
            PIV.BestMatchRE(body, bestT, AI.FFindMatch(bodycode, str, inits, ov, LAnc.Forward, cdns).0)
            && bestT == LT.FirstLeaf(t, inp)
  {
    var inp := PIV.InpOfCp(str, cp);
    var acts := [LS.Areg(T.Translate(body))];

    // ---- the spec tree ---------------------------------------------------
    LFU.ComputeTrIsTree(rer, acts, inp, LG.Empty, WP.Forward);
    var t := LFU.ComputeTr(rer, acts, inp, LG.Empty, WP.Forward);
    assert LS.IsTree(rer, acts, inp, LG.Empty, WP.Forward, t);
    EL.TranslateFragmentPikeLk(body);          // PikeLkRegex(Translate(body))
    EL.BooleanCorrectLk(rer, T.Translate(body), inp, t);
    assert forall i :: 0 <= i < |acts| ==> !acts[i].Acheck?;
    BoolTreeLbIrrel(rer, acts, inp, BS.CanExit, BS.CannotExit, t);

    // ---- the CHECKED tree the simulation runs on -------------------------
    WOE.WalkOkEntry(body);
    assert EL.PikeLkActions(acts) by {
      assert acts == acts + [];
      assert EL.PikeLkActions([]);
      EL.PikeLkActionsConsIff(LS.Areg(T.Translate(body)), []);
    }
    assert WO.WalkOk(acts, bodycode, 0, ATR.EaOf(BS.CannotExit));
    AR.CompileToBytecodeActionsRepLookBehind(rer, qm, body);   // ActionsRepL
    // The body is look-free, so its walk has no lookaround at all: the tree is
    // `LkConfinedTree(_, {})` for the trivial (empty) inside-look set.
    EL.TranslateNoLkBr(body);                                   // NoLkBrL(Translate(body))
    assert LL.LkActsInS(acts, {}) by { LL.NoLkBrLkBodiesInS(T.Translate(body), {}); }
    LL.ComputeTrLkConfined(rer, acts, inp, LG.Empty, WP.Forward, {});   // LkConfinedTree(t, {})
    var tstar := ATR.ActionsTreeRepRE(rer, qm, acts, bodycode, 0, inp, BS.CannotExit, t, {});
    assert TR.TreeRepRE(qm, tstar, bodycode, 0, inp, false);
    LL.LeavesAgreeAtOutsideEmpty(tstar, t, inp);               // Outside({}) -> full LeavesAgreeAt
    LL.LAAtFirstLeaf(tstar, t, inp);
    assert LT.FirstLeaf(tstar, inp) == LT.FirstLeaf(t, inp);

    // TreeThreadRE is definitionally TreeRepRE, so the checked tree discharges
    // both of FindMatchBodyAtCp's tree hypotheses.
    assert TT.TreeThreadRE(rer, qm, bodycode, inp, tstar, 0, false);

    // ---- run the simulation at cp ----------------------------------------
    bestT := FindMatchBodyAtCp(rer, qm, body, bodycode, endl, ngroups, str, cp, tstar,
                               ov, cdns, ncap, nlook, nquant);
    assert bestT == LT.FirstLeaf(tstar, inp) == LT.FirstLeaf(t, inp);
  }

  /** §4b, the tree-construction port GENERALIZED off `LookFreeRE(body)` to the
      CAPTURING-lookaround (depth-1) case — the confinement swap the L4 spec-half
      needs. `BodyTreeAtCp` bakes in `LookFreeRE(body)` and builds the checked
      tree at the EMPTY inside-look set `{}` (so its leaves agree with the spec
      tree EVERYWHERE, giving raw `FirstLeaf` equality). Here `body` may contain
      capturing lookarounds, so the checked tree's leaves agree with the spec tree
      only OUTSIDE `S := LkBodyGroups(Translate(body))` (the groups captured inside
      lookaround bodies): the `{}`-confinement chain (`TranslateNoLkBr` →
      `LkActsInS(_,{})` → `ComputeTrLkConfined(_,{})`) becomes the `S`-chain
      (`LkBodyGroupsConfines` → `LkActsInS(_,S)` → `ComputeTrLkConfined(_,S)`), and
      `LeavesAgreeAtOutsideEmpty` + raw `FirstLeaf` equality becomes
      `FirstLeafAgreeOutside` (`GmAgreeOutside(bestT.1, FirstLeaf(t).1, S)`).

      SCOPE (honest): the retained `PSM.StaticOkRE(qm, body, ...)` requirement
      DEFINITIONALLY contains `LookBehindFragmentRE(body)` (PikeSimRE.dfy:99),
      which caps `NestDepth(body) <= 1` (see `LookBehindFragmentDepth1`). So this
      lifts `BodyTreeAtCp` from look-free to depth-1 CAPTURING looks — exactly what
      the current confinement predicates support (`GmConfinedTree` bans nested LK
      nodes: `LK(_,_,_) => false`, CheckErase.dfy). Genuine (depth >= 2) nesting
      additionally needs the engine confinement/compilation stack — `StaticOkRE`,
      `NfaRepRE`, `PikeLkRegex`, `GmConfinedTree`/`LkConfinedTree`,
      `ComputeTrLkConfined`, `ActionsTreeRepRE` — generalized off the depth-1
      fragment, which is the ENGINE half, disjoint from this SPEC brick. */
  lemma BodyTreeAtCpLk(
      rer: LW.RegExpRecord, qm: AR.QMap, body: R.regex, bodycode: RB.code, endl: nat,
      ngroups: nat, str: string, cp: nat, ov: LOr.OracleView,
      cdns: LCdn.cdns, ncap: int, nlook: int, nquant: int)
    returns (bestT: Option<LT.Leaf>)
    requires PSM.StaticOkRE(qm, body, bodycode, endl)
    requires PSM.SizesOkRE(body, ncap, nlook, nquant)
    requires qm.ov == ov
    requires !rer.ignoreCase && !rer.multiline
    requires cp <= |str|
    requires bodycode == CP.compile_to_bytecode(body)
    requires LL.OracleOkSuffix(rer, qm, PIV.InpOfCp(str, cp))
    ensures var inp := PIV.InpOfCp(str, cp);
            var t := LFU.ComputeTr(rer, [LS.Areg(T.Translate(body))], inp, LG.Empty, WP.Forward);
            var S := LL.LkBodyGroups(T.Translate(body));
            var inits := AI.FInitState(bodycode, cp, AReg.init_regs(ncap), AReg.init_regs(nlook),
                                       AReg.init_regs(nquant), 0, AI.cp_context(cp, str, LAnc.Forward));
            PIV.BestMatchRE(body, bestT, AI.FFindMatch(bodycode, str, inits, ov, LAnc.Forward, cdns).0)
            && (bestT.None? <==> LT.FirstLeaf(t, inp).None?)
            && (bestT.Some? ==>
                  LT.FirstLeaf(t, inp).Some?
                  && bestT.value.0 == LT.FirstLeaf(t, inp).value.0
                  && LL.GmAgreeOutside(bestT.value.1, LT.FirstLeaf(t, inp).value.1, S))
  {
    var inp := PIV.InpOfCp(str, cp);
    var acts := [LS.Areg(T.Translate(body))];
    var S := LL.LkBodyGroups(T.Translate(body));

    // ---- the spec tree ---------------------------------------------------
    LFU.ComputeTrIsTree(rer, acts, inp, LG.Empty, WP.Forward);
    var t := LFU.ComputeTr(rer, acts, inp, LG.Empty, WP.Forward);
    assert LS.IsTree(rer, acts, inp, LG.Empty, WP.Forward, t);
    EL.TranslateFragmentPikeLk(body);          // PikeLkRegex(Translate(body))
    EL.BooleanCorrectLk(rer, T.Translate(body), inp, t);
    assert forall i :: 0 <= i < |acts| ==> !acts[i].Acheck?;
    BoolTreeLbIrrel(rer, acts, inp, BS.CanExit, BS.CannotExit, t);

    // ---- the CHECKED tree the simulation runs on -------------------------
    WOE.WalkOkEntry(body);
    assert EL.PikeLkActions(acts) by {
      assert acts == acts + [];
      assert EL.PikeLkActions([]);
      EL.PikeLkActionsConsIff(LS.Areg(T.Translate(body)), []);
    }
    assert WO.WalkOk(acts, bodycode, 0, ATR.EaOf(BS.CannotExit));
    AR.CompileToBytecodeActionsRepLookBehind(rer, qm, body);   // ActionsRepL
    // `body` may now hold CAPTURING lookarounds: the spec tree's LK bodies confine
    // to `S = LkBodyGroups(Translate(body))`, so the tree is `LkConfinedTree(_, S)`.
    LL.LkBodyGroupsConfines(T.Translate(body), S);             // LkBodiesInS(Translate(body), S)
    assert LL.LkActsInS(acts, S) by { LL.LkActsInSCons(LS.Areg(T.Translate(body)), [], S); }
    LL.ComputeTrLkConfined(rer, acts, inp, LG.Empty, WP.Forward, S);   // LkConfinedTree(t, S)
    var tstar := ATR.ActionsTreeRepRE(rer, qm, acts, bodycode, 0, inp, BS.CannotExit, t, S);
    assert TR.TreeRepRE(qm, tstar, bodycode, 0, inp, false);
    // ActionsTreeRepRE ensures LeavesAgreeAtOutside(tstar, t, inp, S); lift to FirstLeaf.
    LL.FirstLeafAgreeOutside(tstar, t, inp, S);

    // TreeThreadRE is definitionally TreeRepRE, so the checked tree discharges
    // both of FindMatchBodyAtCp's tree hypotheses.
    assert TT.TreeThreadRE(rer, qm, bodycode, inp, tstar, 0, false);

    // ---- run the simulation at cp ----------------------------------------
    bestT := FindMatchBodyAtCp(rer, qm, body, bodycode, endl, ngroups, str, cp, tstar,
                               ov, cdns, ncap, nlook, nquant);
    assert bestT == LT.FirstLeaf(tstar, inp);
    // FirstLeafAgreeOutside(tstar, t, S): same success/position, gms agree outside S.
  }

  // {:isolate_assertions} is REQUIRED here, not a tuning knob. Admitting
  // lookaheads adds a second column-spec path and a second capture-regex
  // shape, and the combined VC runs past 900s. Isolated, every one of its
  // 1566 obligations passes and the lemma completes in ~10m. (Checked first
  // that no obligation FAILS -- twice in this campaign a widening turned a
  // true assertion false and presented as a timeout.)
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

  /** The L3a capture frame: `FLookLoop` writes only inside the matched
      bodies' capture registers (all within `S`); everything else passes
      through untouched. */
  lemma FLookLoopCaptureFrame(crv: CP.FCompiled, str: string, lid: int, maxlook: int,
                              cap: AReg.Regs, lk: AReg.Regs, qt: AReg.Regs, ov: LOr.OracleView,
                              mainast: R.regex, S: set<int>)
    requires NR.LookBehindFragmentRE(mainast) && PIV.QuantUnique(mainast)
    requires (forall k :: AI.get_idx(qt.a_cp, k) < 0)
          && (forall k :: AI.get_idx(qt.a_clk, k) >= -1)
    requires forall l: int :: lid <= l <= maxlook && AReg.get_cp(lk, l).Some? ==>
      exists la: R.lookaround, body: R.regex ::
        LTB.LookEntryOk(crv, l, la, body)
        && NR.LookFreeRE(body) && NR.PlusFragmentRE(body)
        && PIV.CapUnique(body) && PIV.QuantUnique(body)
        && PIV.CaptureRegs(body) <= S
        && (forall q: nat :: q in PIV.QuantIds(body) ==> q in PIV.QuantIdsInLooks(mainast))
        && ((la.NegLookbehind? || la.NegLookahead?) ==> NR.CaptureFreeRE(body))
    ensures var res := AI.FLookLoop(crv, str, lid, maxlook, cap, lk, qt, ov);
      CM.RegsAgreeOutside(res.0, cap, S) && res.1 == lk
    decreases maxlook - lid
  {
    if lid > maxlook { return; }
    var next := lid + 1;
    match AReg.get_cp(lk, lid)
    case None =>
      FLookLoopCaptureFrame(crv, str, next, maxlook, cap, lk, qt, ov, mainast, S);
    case Some(cp) =>
      var looktype := if 0 <= lid < |crv.f_look_types| then crv.f_look_types[lid] else R.Lookahead;
      if !AI.capture_type(looktype) {
        FLookLoopCaptureFrame(crv, str, next, maxlook, cap, lk, qt, ov, mainast, S);
      } else {
        var la: R.lookaround, body: R.regex :|
          LTB.LookEntryOk(crv, lid, la, body)
          && NR.LookFreeRE(body) && NR.PlusFragmentRE(body)
          && PIV.CapUnique(body) && PIV.QuantUnique(body)
          && PIV.CaptureRegs(body) <= S
          && (forall q: nat :: q in PIV.QuantIds(body) ==> q in PIV.QuantIdsInLooks(mainast))
          && ((la.NegLookbehind? || la.NegLookahead?) ==> NR.CaptureFreeRE(body));
        assert looktype == la && (la.Lookbehind? || la.Lookahead?);
        var bytecode := AI.get_code_v(crv.f_look_capture_bc, lid);
        var dir := AI.capture_direction(looktype);
        var lookcdn := if 0 <= lid < |crv.f_look_cdns| then crv.f_look_cdns[lid] else [];
        var lookast := if 0 <= lid < |crv.f_look_ast| then crv.f_look_ast[lid] else R.Re_empty;
        assert bytecode == CP.compile_to_bytecode(CP.capture_regex(la, body));
        assert lookast == body;
        var (result, ov1) := AI.FFindMatchPlus(bytecode, lookast, crv.f_plus_bc, str, ov, dir,
                                               cp, cap, lk, qt, 0, lookcdn);
        var ncap, nlk, nqt := if result.None? then cap else result.value.capture_regs,
                              if result.None? then lk else result.value.look_regs,
                              if result.None? then qt else result.value.quant_regs;
        if la.Lookahead? {
          assert dir == LAnc.Forward && CP.capture_regex(la, body) == body;
          NR.PlusIsLookBehindFragmentRE(body);
          ReplayPlusFrame(bytecode, str, ov, dir, lookcdn, crv.f_plus_bc, cp, cap, lk, qt, la, body);
          if result.Some? {
            CM.RegsAgreeOutsideWeaken(ncap, cap, PIV.CaptureRegs(body), S);
            assert QuantRegsFinal(result.value);
          }
        } else {
          // CAPTURING positive LOOKBEHIND (L3b): the backward replay writes captures
          // only inside CaptureRegs(body); weaken to S (CaptureRegs(body) <= S).
          assert la.Lookbehind?;
          assert dir == LAnc.Backward && CP.capture_regex(la, body) == R.reverse_regex(body);
          assert bytecode == CP.compile_to_bytecode(R.reverse_regex(body));
          assert AI.cp_context(cp, str, LAnc.Backward).nextchar == AI.get_char(str, cp - 1);
          ReplayPlusFrameLB(bytecode, str, ov, lookcdn, crv.f_plus_bc, cp, cap, lk, qt, body);
          if result.Some? {
            CM.RegsAgreeOutsideWeaken(ncap, cap, PIV.CaptureRegs(body), S);
          }
        }
        assert CM.RegsAgreeOutside(ncap, cap, S) && nlk == lk
            && (forall k :: AI.get_idx(nqt.a_cp, k) < 0)
            && (forall k :: AI.get_idx(nqt.a_clk, k) >= -1);
        FLookLoopCaptureFrame(crv, str, next, maxlook, ncap, nlk, nqt, ov1, mainast, S);
        CM.RegsAgreeOutsideTrans(AI.FLookLoop(crv, str, next, maxlook, ncap, nlk, nqt, ov1).0, ncap, cap, S);
      }
  }

  /** L3a — the QUANT frame for the whole FLookLoop pass: the final quant bank
      agrees with the initial one OUTSIDE `Sq`, where `Sq` covers every matched
      body's own quant ids (`QIdsInt(body) <= Sq`, from `QuantIds(body) <=
      QuantIdsInLooks(mainast)`). Each replay writes quant only inside its body
      (`QuantWritesInsideBody` -> `FFindMatchQuantFrame` for lookaheads,
      `ReplayFrames` for capture-free lookbehinds). Instantiate `Sq` with the int
      image of `QuantIdsInLooks(mainast)`, disjoint from the outer quants the main
      filter reads. Feeds P1 (`GmOfLiveFrameOutside`'s quant hypothesis). */
  lemma FLookLoopQuantFrame(crv: CP.FCompiled, str: string, lid: int, maxlook: int,
                            cap: AReg.Regs, lk: AReg.Regs, qt: AReg.Regs, ov: LOr.OracleView,
                            mainast: R.regex, Sq: set<int>)
    requires NR.LookBehindFragmentRE(mainast) && PIV.QuantUnique(mainast)
    requires (forall k :: AI.get_idx(qt.a_cp, k) < 0)
          && (forall k :: AI.get_idx(qt.a_clk, k) >= -1)
    requires forall l: int :: lid <= l <= maxlook && AReg.get_cp(lk, l).Some? ==>
      exists la: R.lookaround, body: R.regex ::
        LTB.LookEntryOk(crv, l, la, body)
        && NR.LookFreeRE(body) && NR.PlusFragmentRE(body)
        && PIV.CapUnique(body) && PIV.QuantUnique(body)
        && LKC.QIdsInt(body) <= Sq
        && ((la.NegLookbehind? || la.NegLookahead?) ==> NR.CaptureFreeRE(body))
    ensures var res := AI.FLookLoop(crv, str, lid, maxlook, cap, lk, qt, ov);
      CM.RegsAgreeOutside(res.2, qt, Sq) && res.1 == lk
    decreases maxlook - lid
  {
    if lid > maxlook { return; }
    var next := lid + 1;
    match AReg.get_cp(lk, lid)
    case None =>
      FLookLoopQuantFrame(crv, str, next, maxlook, cap, lk, qt, ov, mainast, Sq);
    case Some(cp) =>
      var looktype := if 0 <= lid < |crv.f_look_types| then crv.f_look_types[lid] else R.Lookahead;
      if !AI.capture_type(looktype) {
        FLookLoopQuantFrame(crv, str, next, maxlook, cap, lk, qt, ov, mainast, Sq);
      } else {
        var la: R.lookaround, body: R.regex :|
          LTB.LookEntryOk(crv, lid, la, body)
          && NR.LookFreeRE(body) && NR.PlusFragmentRE(body)
          && PIV.CapUnique(body) && PIV.QuantUnique(body)
          && LKC.QIdsInt(body) <= Sq
          && ((la.NegLookbehind? || la.NegLookahead?) ==> NR.CaptureFreeRE(body));
        assert looktype == la && (la.Lookbehind? || la.Lookahead?);
        var bytecode := AI.get_code_v(crv.f_look_capture_bc, lid);
        var dir := AI.capture_direction(looktype);
        var lookcdn := if 0 <= lid < |crv.f_look_cdns| then crv.f_look_cdns[lid] else [];
        var lookast := if 0 <= lid < |crv.f_look_ast| then crv.f_look_ast[lid] else R.Re_empty;
        assert bytecode == CP.compile_to_bytecode(CP.capture_regex(la, body));
        assert lookast == body;
        var (result, ov1) := AI.FFindMatchPlus(bytecode, lookast, crv.f_plus_bc, str, ov, dir,
                                               cp, cap, lk, qt, 0, lookcdn);
        var ncap, nlk, nqt := if result.None? then cap else result.value.capture_regs,
                              if result.None? then lk else result.value.look_regs,
                              if result.None? then qt else result.value.quant_regs;
        var inits := AI.FInitState(bytecode, cp, cap, lk, qt, 0, AI.cp_context(cp, str, dir));
        assert CM.VmQuantsAgree(inits, qt, LKC.QIdsInt(body)) by {
          assert inits.active == [AI.init_thread(cap, lk, qt)];
          assert AI.init_thread(cap, lk, qt).quant_regs == qt;
          assert CM.RegsAgreeOutside(qt, qt, LKC.QIdsInt(body));
        }
        if la.Lookahead? {
          assert dir == LAnc.Forward && CP.capture_regex(la, body) == body;
          NR.PlusIsLookBehindFragmentRE(body);
          ReplayPlusFrame(bytecode, str, ov, dir, lookcdn, crv.f_plus_bc, cp, cap, lk, qt, la, body);
          QuantWritesInsideBody(body);   // QuantWritesInside(bytecode, QIdsInt(body))
          CM.FFindMatchQuantFrame(bytecode, str, inits, ov, dir, lookcdn, qt, LKC.QIdsInt(body));
          NoTrueQuantStamp(body);
          assert VmQuantFinal(inits) by { assert QuantRegsFinal(AI.init_thread(cap, lk, qt)); }
          FFindMatchQuantFinalAny(bytecode, str, inits, ov, dir, lookcdn);   // res0 quant-final
          var (res0, ovx) := AI.FFindMatch(bytecode, str, inits, ov, dir, lookcdn);
          if result.Some? {
            assert res0.Some? && QuantRegsFinal(res0.value);
            FNulledPlusIdentity(body, res0.value.capture_regs, res0.value.look_regs, res0.value.quant_regs,
                                crv.f_plus_bc, str, ovx, dir);
            assert nqt == res0.value.quant_regs;
            CM.RegsAgreeOutsideWeaken(nqt, qt, LKC.QIdsInt(body), Sq);
          }
        } else {
          // CAPTURING positive LOOKBEHIND (L3b): the backward replay writes quants
          // only inside QIdsInt(body); weaken to Sq.
          assert la.Lookbehind?;
          assert dir == LAnc.Backward && CP.capture_regex(la, body) == R.reverse_regex(body);
          assert bytecode == CP.compile_to_bytecode(R.reverse_regex(body));
          assert AI.cp_context(cp, str, LAnc.Backward).nextchar == AI.get_char(str, cp - 1);
          ReplayPlusFrameLB(bytecode, str, ov, lookcdn, crv.f_plus_bc, cp, cap, lk, qt, body);   // QuantRegsFinal -> nqt unset
          ReplayQuantFrameLB(bytecode, str, cp, cap, lk, qt, ov, lookcdn, crv.f_plus_bc, body);   // quant write frame
          if result.Some? {
            assert nqt == result.value.quant_regs;
            assert CM.RegsAgreeOutside(nqt, qt, LKC.QIdsInt(body));   // ReplayQuantFrameLB
            CM.RegsAgreeOutsideWeaken(nqt, qt, LKC.QIdsInt(body), Sq);
          }
          assert (forall k :: AI.get_idx(nqt.a_cp, k) < 0) && (forall k :: AI.get_idx(nqt.a_clk, k) >= -1);
        }
        assert CM.RegsAgreeOutside(nqt, qt, Sq) && nlk == lk
            && (forall k :: AI.get_idx(nqt.a_cp, k) < 0)
            && (forall k :: AI.get_idx(nqt.a_clk, k) >= -1);
        FLookLoopQuantFrame(crv, str, next, maxlook, ncap, nlk, nqt, ov1, mainast, Sq);
        CM.RegsAgreeOutsideTrans(AI.FLookLoop(crv, str, next, maxlook, ncap, nlk, nqt, ov1).2, nqt, qt, Sq);
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

  /** L3b: the BACKWARD capture-write frame — the lookbehind twin of
      `ReplayCaptureFrame`. The engine compiles a capturing lookbehind's replay
      over `compile_to_bytecode(reverse_regex(body))` and runs it BACKWARD, so the
      capture bank agrees with the incoming `cap` OUTSIDE the body's own registers
      (`CaptureRegs(reverse_regex(body)) == CaptureRegs(body)`, via `ReverseCapIds`).
      Both engine cores (`CaptureBytecodeClassified`, `FFindMatchCapWriteFrame`) are
      direction-generic; the reversed-body statics come from `ReversePlusFragment` +
      `ReverseCapUnique`. */
  lemma ReplayCaptureFrameLB(bytecode: RB.code, str: string, inits: AI.VmState, ov: LOr.OracleView,
                             lookcdn: LCdn.cdns, cap: AReg.Regs, lk: AReg.Regs, qt: AReg.Regs, body: R.regex)
    requires NR.PlusFragmentRE(body) && PIV.CapUnique(body)
    requires bytecode == CP.compile_to_bytecode(R.reverse_regex(body))
    requires inits.active == [AI.init_thread(cap, lk, qt)]
    requires inits.blocked == [] && inits.bestmatch.None?
    requires |inits.processed.true_set| == RB.size(bytecode)
          && |inits.processed.false_set| == RB.size(bytecode)
    requires inits.context.nextchar == AI.get_char(str, inits.cp - 1)      // BACKWARD
    ensures var r := AI.FFindMatch(bytecode, str, inits, ov, LAnc.Backward, lookcdn).0;
      r.Some? ==> CM.RegsAgreeOutside(r.value.capture_regs, cap, PIV.CaptureRegs(body))
  {
    var rev := R.reverse_regex(body);
    PIV.ReversePlusFragment(body);                 // PlusFragmentRE(rev)
    NR.PlusIsLookBehindFragmentRE(rev);            // LookBehindFragmentRE(rev)
    PIV.ReverseCapUnique(body);                    // CapUnique(rev)
    PIV.ReverseCapIds(body);                       // CapIds(rev) == CapIds(body)
    assert PIV.CaptureRegs(rev) == PIV.CaptureRegs(body);
    CM.CaptureBytecodeClassified(rev);
    assert CM.VmCapturesAgree(inits, cap, PIV.CaptureRegs(rev)) by {
      assert CM.RegsAgreeOutside(cap, cap, PIV.CaptureRegs(rev));
    }
    CM.FFindMatchCapWriteFrame(bytecode, str, inits, ov, LAnc.Backward, lookcdn, cap, PIV.CaptureRegs(rev));
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

  /** A body's compiled bytecode writes quant clocks only inside its own quant ids
      -- capture-INDEPENDENT (the quant structure is the same whether or not the
      body captures), so unlike `LKC.CaptureCodeClassified` this needs no
      `CaptureFreeRE`. Via `NI.CodeShapeAt` (`sq >= 0 && sq in QuantIds(body)`).
      Feeds the per-replay `CM.FFindMatchQuantFrame`. */
  lemma QuantWritesInsideBody(body: R.regex)
    requires NR.LookBehindFragmentRE(body) && PIV.CapUnique(body) && PIV.QuantUnique(body)
    ensures CM.QuantWritesInside(CP.compile_to_bytecode(body), LKC.QIdsInt(body))
  {
    var code := CP.compile_to_bytecode(body);
    var next := CP.compile(body, 0, CP.Progress).1;
    NR.CompileToBytecodeRepLookBehind(body);
    var endl := next as nat;
    forall pc: nat | pc < |code|
      ensures code[pc].SetQuantToClock? ==> code[pc].sq in LKC.QIdsInt(body)
    {
      assert NR.GetPcRE(code, pc) == Some(code[pc]);
      if pc < endl {
        NI.CodeShapeAt(body, code, 0, endl, pc);
      } else {
        assert pc == endl;
        assert NR.GetPcRE(code, endl) == Some(RB.Accept);
      }
    }
  }

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

  /** The FULL per-replay frame the FLookLoop induction consumes: for a
      capturing lookAHEAD replay, the result's capture bank agrees with `cap`
      outside `CaptureRegs(body)`, the LOOK bank is unchanged (look-free body),
      and the QUANT bank is final (so it can seed the next replay). Extends
      `ReplayPlusCaptureFrame` with the look/quant facts, via the un-bundled
      look-write-free (`NoLookWriteBody`) and no-true-stamp classifications. */
  lemma ReplayPlusFrame(bytecode: RB.code, str: string, ov: LOr.OracleView, dir: LAnc.direction,
                        lookcdn: LCdn.cdns, plus_bcv: seq<RB.code>, cp: int,
                        cap: AReg.Regs, lk: AReg.Regs, qt: AReg.Regs, la: R.lookaround, body: R.regex)
    requires NR.LookBehindFragmentRE(body) && NR.LookFreeRE(body) && NR.PlusFragmentRE(body)
    requires PIV.CapUnique(body) && PIV.QuantUnique(body)
    requires la.Lookahead? && dir == LAnc.Forward
    requires bytecode == CP.compile_to_bytecode(body)
    requires AI.cp_context(cp, str, dir).nextchar == AI.get_char(str, cp)
    requires (forall k :: AI.get_idx(qt.a_cp, k) < 0)
          && (forall k :: AI.get_idx(qt.a_clk, k) >= -1)
    ensures var r := AI.FFindMatchPlus(bytecode, body, plus_bcv, str, ov, dir, cp, cap, lk, qt, 0, lookcdn).0;
      r.Some? ==>
        CM.RegsAgreeOutside(r.value.capture_regs, cap, PIV.CaptureRegs(body))
        && r.value.look_regs == lk
        && QuantRegsFinal(r.value)
  {
    var inits := AI.FInitState(bytecode, cp, cap, lk, qt, 0, AI.cp_context(cp, str, dir));
    ReplayCaptureFrame(bytecode, str, inits, ov, dir, lookcdn, cap, lk, qt, la, body);
    LKC.NoLookWriteBody(body);
    assert CM.VmLooksAre(inits, lk);
    CM.FFindMatchLookEq(bytecode, str, inits, ov, dir, lookcdn, lk);
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

  /** L3b: the BACKWARD plus-fragment replay frame — the lookbehind twin of
      `ReplayPlusFrame`. The engine runs a capturing lookbehind's replay over
      `compile_to_bytecode(reverse_regex(body))` BACKWARD; the capture bank agrees
      with `cap` outside `CaptureRegs(body)` (`ReplayCaptureFrameLB`), looks are
      unchanged (`NoLookWriteBody(rev)` + `FFindMatchLookEq`), quants stay final
      (`NoTrueQuantStamp(rev)` + `FFindMatchQuantFinalAny`), and the plus
      reconstruction is the identity (`FNulledPlusIdentity`). The `FFindMatchPlus`
      reconstruction regex is `body` (matching the FLookLoop call `bytecode ==
      compile_to_bytecode(capture_regex(la, body)) == compile(reverse_regex(body))`,
      2nd arg `lookast == body`). */
  lemma ReplayPlusFrameLB(bytecode: RB.code, str: string, ov: LOr.OracleView,
                          lookcdn: LCdn.cdns, plus_bcv: seq<RB.code>, cp: int,
                          cap: AReg.Regs, lk: AReg.Regs, qt: AReg.Regs, body: R.regex)
    requires NR.LookFreeRE(body) && NR.PlusFragmentRE(body)
    requires PIV.CapUnique(body) && PIV.QuantUnique(body)
    requires bytecode == CP.compile_to_bytecode(R.reverse_regex(body))
    requires AI.cp_context(cp, str, LAnc.Backward).nextchar == AI.get_char(str, cp - 1)
    requires (forall k :: AI.get_idx(qt.a_cp, k) < 0)
          && (forall k :: AI.get_idx(qt.a_clk, k) >= -1)
    ensures var r := AI.FFindMatchPlus(bytecode, body, plus_bcv, str, ov, LAnc.Backward, cp, cap, lk, qt, 0, lookcdn).0;
      r.Some? ==>
        CM.RegsAgreeOutside(r.value.capture_regs, cap, PIV.CaptureRegs(body))
        && r.value.look_regs == lk
        && QuantRegsFinal(r.value)
  {
    var rev := R.reverse_regex(body);
    PIV.ReversePlusFragment(body);                 // PlusFragmentRE(rev)
    NR.PlusIsLookBehindFragmentRE(rev);            // LookBehindFragmentRE(rev)
    PIV.ReverseLookFree(body);                     // LookFreeRE(rev)
    PIV.ReverseCapUnique(body);                    // CapUnique(rev)
    PIV.ReverseQuantUnique(body);                  // QuantUnique(rev)
    var inits := AI.FInitState(bytecode, cp, cap, lk, qt, 0, AI.cp_context(cp, str, LAnc.Backward));
    ReplayCaptureFrameLB(bytecode, str, inits, ov, lookcdn, cap, lk, qt, body);
    LKC.NoLookWriteBody(rev);
    assert CM.VmLooksAre(inits, lk);
    CM.FFindMatchLookEq(bytecode, str, inits, ov, LAnc.Backward, lookcdn, lk);
    NoTrueQuantStamp(rev);
    assert VmQuantFinal(inits) by {
      assert QuantRegsFinal(AI.init_thread(cap, lk, qt));
    }
    FFindMatchQuantFinalAny(bytecode, str, inits, ov, LAnc.Backward, lookcdn);
    var (res0, ovx) := AI.FFindMatch(bytecode, str, inits, ov, LAnc.Backward, lookcdn);
    if res0.Some? {
      var th := res0.value;
      assert QuantRegsFinal(th);
      FNulledPlusIdentity(body, th.capture_regs, th.look_regs, th.quant_regs, plus_bcv, str, ovx, LAnc.Backward);
    }
  }

  /** A compiled body's bytecode holds no `WriteOracle` -- `compile_to_bytecode`
      never emits one (only the oracle BUILD pass does). Lifts `NR.NoWriteInstrRE`
      over the whole block; the `Accept` at `endl` is not a `WriteOracle`. */
  lemma NoWriteOracleBodyCode(body: R.regex)
    requires NR.LookBehindFragmentRE(body)
    ensures CM.NoWriteOracleCode(CP.compile_to_bytecode(body))
  {
    var code := CP.compile_to_bytecode(body);
    var next := CP.compile(body, 0, CP.Progress).1;
    NR.CompileToBytecodeRepLookBehind(body);
    var endl := next as nat;
    forall pc: nat | pc < |code| ensures !code[pc].WriteOracle? {
      assert NR.GetPcRE(code, pc) == Some(code[pc]);
      if pc < endl {
        NR.NoWriteInstrRE(body, code, 0, endl, pc);
      } else {
        assert pc == endl;
        assert NR.GetPcRE(code, endl) == Some(RB.Accept);
      }
    }
  }

  /** §4b — ORACLE STABILITY of a look-free body's whole `FFindMatchPlus`. The
      `FFindMatch` half reads the oracle (`NoWriteOracleBodyCode` -> `FFindMatchOvStable`);
      the `FReconstructPlus` half is the identity on a `QuantRegsFinal` thread
      (`FNulledPlusIdentity`), so it returns the view untouched. Lets the FLookLoop
      value-lift keep the SAME `ov` across the whole fold (so `qm.ov == ov` survives
      into every per-lid `ReplayCapIsBodyLeaf`). */
  lemma FFindMatchPlusOvStable(bytecode: RB.code, str: string, ov: LOr.OracleView, dir: LAnc.direction,
                               lookcdn: LCdn.cdns, plus_bcv: seq<RB.code>, cp: int,
                               cap: AReg.Regs, lk: AReg.Regs, qt: AReg.Regs, la: R.lookaround, body: R.regex)
    requires NR.LookBehindFragmentRE(body) && PIV.CapUnique(body) && PIV.QuantUnique(body)
    requires la.Lookahead? && dir == LAnc.Forward
    requires bytecode == CP.compile_to_bytecode(body)
    requires AI.cp_context(cp, str, dir).nextchar == AI.get_char(str, cp)
    requires (forall k :: AI.get_idx(qt.a_cp, k) < 0)
          && (forall k :: AI.get_idx(qt.a_clk, k) >= -1)
    ensures AI.FFindMatchPlus(bytecode, body, plus_bcv, str, ov, dir, cp, cap, lk, qt, 0, lookcdn).1 == ov
  {
    var inits := AI.FInitState(bytecode, cp, cap, lk, qt, 0, AI.cp_context(cp, str, dir));
    NoWriteOracleBodyCode(body);
    CM.FFindMatchOvStable(bytecode, str, inits, ov, dir, lookcdn);   // FFindMatch(...).1 == ov
    NoTrueQuantStamp(body);
    assert VmQuantFinal(inits) by { assert QuantRegsFinal(AI.init_thread(cap, lk, qt)); }
    FFindMatchQuantFinalAny(bytecode, str, inits, ov, dir, lookcdn);
    var (res0, ovx) := AI.FFindMatch(bytecode, str, inits, ov, dir, lookcdn);
    assert ovx == ov;
    if res0.Some? {
      var th := res0.value;
      assert QuantRegsFinal(th);
      FNulledPlusIdentity(body, th.capture_regs, th.look_regs, th.quant_regs, plus_bcv, str, ovx, dir);
    }
  }

  /** Lookbehind companion of `FFindMatchPlusOvStable`: a capture-free lookbehind
      replay reads the oracle but never writes it, so it leaves `ov` unchanged.
      The bytecode is `compile_to_bytecode(reverse_regex(body))` (the backward
      capture regex); reversal preserves look-freedom / plus-fragment / quant
      uniqueness, so the same no-oracle-write + quant-final argument applies. The
      backward context fact (`nextchar == get_char(str, cp-1)`) is definitional. */
  lemma FFindMatchPlusOvStableLB(bytecode: RB.code, str: string, ov: LOr.OracleView, dir: LAnc.direction,
                                 lookcdn: LCdn.cdns, plus_bcv: seq<RB.code>, cp: int,
                                 cap: AReg.Regs, lk: AReg.Regs, qt: AReg.Regs, la: R.lookaround, body: R.regex)
    // L3b: capturing lookbehind bodies allowed -- `CaptureFreeRE` was only used to
    // reach `CapUnique(reverse_regex(body))`, now supplied directly by
    // `ReverseCapUnique`. Oracle stability is capture-INDEPENDENT.
    requires NR.LookFreeRE(body) && NR.PlusFragmentRE(body) && PIV.CapUnique(body) && PIV.QuantUnique(body)
    requires la.Lookbehind? && dir == LAnc.Backward
    requires bytecode == CP.compile_to_bytecode(R.reverse_regex(body))
    requires (forall k :: AI.get_idx(qt.a_cp, k) < 0)
          && (forall k :: AI.get_idx(qt.a_clk, k) >= -1)
    ensures AI.FFindMatchPlus(bytecode, body, plus_bcv, str, ov, dir, cp, cap, lk, qt, 0, lookcdn).1 == ov
  {
    var rbody := R.reverse_regex(body);
    NR.ReversePlusFragmentRE(body);          // PlusFragmentRE(rbody)
    NR.PlusIsLookBehindFragmentRE(rbody);    // LookBehindFragmentRE(rbody)
    PIV.ReverseQuantUnique(body);            // QuantUnique(rbody)
    PIV.ReverseCapUnique(body);              // CapUnique(rbody)
    var inits := AI.FInitState(bytecode, cp, cap, lk, qt, 0, AI.cp_context(cp, str, dir));
    assert inits.context.nextchar == AI.get_char(str, cp - 1);   // cp_context Backward definitional
    NoWriteOracleBodyCode(rbody);
    CM.FFindMatchOvStable(bytecode, str, inits, ov, dir, lookcdn);   // FFindMatch(...).1 == ov
    NoTrueQuantStamp(rbody);
    assert VmQuantFinal(inits) by { assert QuantRegsFinal(AI.init_thread(cap, lk, qt)); }
    FFindMatchQuantFinalAny(bytecode, str, inits, ov, dir, lookcdn);
    var (res0, ovx) := AI.FFindMatch(bytecode, str, inits, ov, dir, lookcdn);
    assert ovx == ov;
    if res0.Some? {
      var th := res0.value;
      assert QuantRegsFinal(th);
      FNulledPlusIdentity(body, th.capture_regs, th.look_regs, th.quant_regs, plus_bcv, str, ovx, dir);
    }
  }

  // ==========================================================================
  // L3a §4 — the FLookLoop VALUE lift vocabulary. The §4a frame says what
  // FLookLoop leaves UNCHANGED (outside S); the value lift says what it WRITES:
  // each matched positive lookahead's body registers carry that body's FRESH
  // match.
  // ==========================================================================

  /** `l` names a matched, capturing, positive (forward) lookahead. */
  ghost predicate MatchedPosLA(crv: CP.FCompiled, lk: AReg.Regs, l: int) {
    AReg.get_cp(lk, l).Some?
    && AI.capture_type(if 0 <= l < |crv.f_look_types| then crv.f_look_types[l] else R.Lookahead)
    // L3b: a matched POSITIVE look -- lookAHEAD or lookBEHIND -- reconstructs its
    // body's captures (the negatives record nothing; `capture_type` already excludes them).
    && ((if 0 <= l < |crv.f_look_types| then crv.f_look_types[l] else R.Lookahead).Lookahead?
        || (if 0 <= l < |crv.f_look_types| then crv.f_look_types[l] else R.Lookahead).Lookbehind?)
  }

  /** The `l`-th lookaround body (default `Re_empty` off the table). */
  ghost function VBody(crv: CP.FCompiled, l: int): R.regex {
    if 0 <= l < |crv.f_look_ast| then crv.f_look_ast[l] else R.Re_empty
  }

  /** The body-`l` match from FRESH registers at the recorded cp, under `ov`. */
  ghost function FreshBodyMatch(crv: CP.FCompiled, str: string, l: int, lk: AReg.Regs,
                                ov: LOr.OracleView, ncap: int, nlook: int, nquant: int): Option<AI.Thread> {
    var body := VBody(crv, l);
    var cp := if AReg.get_cp(lk, l).Some? then AReg.get_cp(lk, l).value else 0;
    // L3b: the fresh body match runs in the look's CAPTURE direction over its
    // compiled capture regex -- for a lookAHEAD that is `body` FORWARD (unchanged);
    // for a lookBEHIND, `reverse_regex(body)` BACKWARD (the keystone's fresh ref).
    var looktype := if 0 <= l < |crv.f_look_types| then crv.f_look_types[l] else R.Lookahead;
    var dir := AI.capture_direction(looktype);
    var bc := CP.compile_to_bytecode(CP.capture_regex(looktype, body));
    var cdn := if 0 <= l < |crv.f_look_cdns| then crv.f_look_cdns[l] else [];
    AI.FFindMatch(bc, str, AI.FInitState(bc, cp, AReg.init_regs(ncap), AReg.init_regs(nlook),
                  AReg.init_regs(nquant), 0, AI.cp_context(cp, str, dir)), ov, dir, cdn).0
  }

  /** The value-lift conclusion: on each matched positive lookahead's own capture
      registers, `res0` carries the fresh body match (or stays unset if the fresh
      body did not match). */
  ghost predicate FLookLoopValueOk(crv: CP.FCompiled, str: string, res0: AReg.Regs, lid: int, maxlook: int,
                                   lk: AReg.Regs, ov: LOr.OracleView, ncap: int, nlook: int, nquant: int) {
    forall l: int :: lid <= l <= maxlook && MatchedPosLA(crv, lk, l) ==>
      var rf := FreshBodyMatch(crv, str, l, lk, ov, ncap, nlook, nquant);
      (rf.Some? ==> CM.RegsAgreeInside(res0, rf.value.capture_regs, PIV.CaptureRegs(VBody(crv, l))))
      && (rf.None? ==> CM.RegsAgreeInside(res0, AReg.init_regs(ncap), PIV.CaptureRegs(VBody(crv, l))))
  }

  /** `l == lid` is not a matched positive lookahead, so the value map for
      `[lid, maxlook]` is exactly the one for `[lid+1, maxlook]`. */
  lemma ValueOkSkipLid(crv: CP.FCompiled, str: string, res0: AReg.Regs, lid: int, maxlook: int,
                       lk: AReg.Regs, ov: LOr.OracleView, ncap: int, nlook: int, nquant: int)
    requires FLookLoopValueOk(crv, str, res0, lid + 1, maxlook, lk, ov, ncap, nlook, nquant)
    requires !MatchedPosLA(crv, lk, lid)
    ensures FLookLoopValueOk(crv, str, res0, lid, maxlook, lk, ov, ncap, nlook, nquant)
  {
    forall l: int | lid <= l <= maxlook && MatchedPosLA(crv, lk, l)
      ensures var rf := FreshBodyMatch(crv, str, l, lk, ov, ncap, nlook, nquant);
              (rf.Some? ==> CM.RegsAgreeInside(res0, rf.value.capture_regs, PIV.CaptureRegs(VBody(crv, l))))
              && (rf.None? ==> CM.RegsAgreeInside(res0, AReg.init_regs(ncap), PIV.CaptureRegs(VBody(crv, l))))
    { assert l != lid; }
  }

  /** §4 VALUE-LIFT ENGINE BRIDGE (per matched lid): the ACTUAL FFindMatchPlus
      replay from the fold's `cap` agrees, on `CaptureRegs(body)`, with a replay
      from FRESH registers, and matches iff-together. `FReconstructPlus` is the
      identity on the `QuantRegsFinal` result (`FNulledPlusIdentity`), so the
      FFindMatchPlus capture bank IS the FFindMatch one; then the register-value-
      blind bisimulation `ReplayCapAgreeFresh` ties it to the fresh replay. This
      is the one non-trivial engine step the FLookLoop value induction consumes. */
  lemma ReplayLidCapAgreeFresh(bytecode: RB.code, str: string, cp: int, cap: AReg.Regs, lk: AReg.Regs,
                               qt: AReg.Regs, ov: LOr.OracleView, lookcdn: LCdn.cdns, plus_bcv: seq<RB.code>,
                               body: R.regex, la: R.lookaround, ncap: int, nlook: int, nquant: int)
    requires NR.LookBehindFragmentRE(body) && NR.LookFreeRE(body) && NR.PlusFragmentRE(body)
    requires PIV.CapUnique(body) && PIV.QuantUnique(body)
    requires la.Lookahead?
    requires bytecode == CP.compile_to_bytecode(body)
    requires 0 <= cp <= |str|
    requires AI.cp_context(cp, str, LAnc.Forward).nextchar == AI.get_char(str, cp)
    requires (forall k :: AI.get_idx(qt.a_cp, k) < 0)
          && (forall k :: AI.get_idx(qt.a_clk, k) >= -1)
    requires |qt.a_cp| == nquant && |qt.a_clk| == nquant
    requires CM.RegsAgreeInside(cap, AReg.init_regs(ncap), PIV.CaptureRegs(body))
    ensures
      var result := AI.FFindMatchPlus(bytecode, body, plus_bcv, str, ov, LAnc.Forward, cp, cap, lk, qt, 0, lookcdn).0;
      var rf := AI.FFindMatch(bytecode, str,
                  AI.FInitState(bytecode, cp, AReg.init_regs(ncap), AReg.init_regs(nlook),
                                AReg.init_regs(nquant), 0, AI.cp_context(cp, str, LAnc.Forward)),
                  ov, LAnc.Forward, lookcdn).0;
      (result.None? <==> rf.None?)
      && (result.Some? ==> CM.RegsAgreeInside(result.value.capture_regs, rf.value.capture_regs, PIV.CaptureRegs(body)))
  {
    var dir := LAnc.Forward;
    var inits := AI.FInitState(bytecode, cp, cap, lk, qt, 0, AI.cp_context(cp, str, dir));
    // the FFindMatchPlus capture bank == the FFindMatch capture bank (reconstruct
    // is the identity for a QuantRegsFinal result).
    NoTrueQuantStamp(body);
    assert VmQuantFinal(inits) by { assert QuantRegsFinal(AI.init_thread(cap, lk, qt)); }
    FFindMatchQuantFinalAny(bytecode, str, inits, ov, dir, lookcdn);
    var (fmres, ovx) := AI.FFindMatch(bytecode, str, inits, ov, dir, lookcdn);
    if fmres.Some? {
      FNulledPlusIdentity(body, fmres.value.capture_regs, fmres.value.look_regs, fmres.value.quant_regs,
                          plus_bcv, str, ovx, dir);
    }
    // the register-value-blind bisimulation: FFindMatch(from cap) ~ FFindMatch(from fresh).
    ReplayCapAgreeFresh(bytecode, str, cp, cap, lk, qt, ov, lookcdn, body, ncap, nlook, nquant);
  }

  /** L3b: the per-lid BACKWARD replay↔fresh capture agreement — lookbehind twin of
      `ReplayLidCapAgreeFresh`. The `FFindMatchPlus` backward replay from the main
      thread's `cap` (fresh on `CaptureRegs(body)`) agrees, on `CaptureRegs(body)`,
      with the fresh backward `FFindMatch`. `FFindMatchPlus` caps == `FFindMatch`
      caps (reconstruct is identity), then the dir-generic bisimulation
      `ReplayCapAgreeFreshLB`. The bytecode is `compile_to_bytecode(reverse_regex
      (body))`, the reconstruction reg is `body` (the FLookLoop call convention). */
  lemma ReplayLidCapAgreeFreshLB(bytecode: RB.code, str: string, cp: int, cap: AReg.Regs, lk: AReg.Regs,
                                 qt: AReg.Regs, ov: LOr.OracleView, lookcdn: LCdn.cdns, plus_bcv: seq<RB.code>,
                                 body: R.regex, ncap: int, nlook: int, nquant: int)
    requires NR.LookFreeRE(body) && NR.PlusFragmentRE(body)
    requires PIV.CapUnique(body) && PIV.QuantUnique(body)
    requires bytecode == CP.compile_to_bytecode(R.reverse_regex(body))
    requires 0 <= cp <= |str|
    requires AI.cp_context(cp, str, LAnc.Backward).nextchar == AI.get_char(str, cp - 1)
    requires (forall k :: AI.get_idx(qt.a_cp, k) < 0)
          && (forall k :: AI.get_idx(qt.a_clk, k) >= -1)
    requires |qt.a_cp| == nquant && |qt.a_clk| == nquant
    requires CM.RegsAgreeInside(cap, AReg.init_regs(ncap), PIV.CaptureRegs(body))
    ensures
      var result := AI.FFindMatchPlus(bytecode, body, plus_bcv, str, ov, LAnc.Backward, cp, cap, lk, qt, 0, lookcdn).0;
      var rf := AI.FFindMatch(bytecode, str,
                  AI.FInitState(bytecode, cp, AReg.init_regs(ncap), AReg.init_regs(nlook),
                                AReg.init_regs(nquant), 0, AI.cp_context(cp, str, LAnc.Backward)),
                  ov, LAnc.Backward, lookcdn).0;
      (result.None? <==> rf.None?)
      && (result.Some? ==> CM.RegsAgreeInside(result.value.capture_regs, rf.value.capture_regs, PIV.CaptureRegs(body)))
  {
    var rev := R.reverse_regex(body);
    PIV.ReversePlusFragment(body);
    NR.PlusIsLookBehindFragmentRE(rev);
    PIV.ReverseCapUnique(body);
    PIV.ReverseQuantUnique(body);
    var dir := LAnc.Backward;
    var inits := AI.FInitState(bytecode, cp, cap, lk, qt, 0, AI.cp_context(cp, str, dir));
    NoTrueQuantStamp(rev);
    assert VmQuantFinal(inits) by { assert QuantRegsFinal(AI.init_thread(cap, lk, qt)); }
    FFindMatchQuantFinalAny(bytecode, str, inits, ov, dir, lookcdn);
    var (fmres, ovx) := AI.FFindMatch(bytecode, str, inits, ov, dir, lookcdn);
    if fmres.Some? {
      FNulledPlusIdentity(body, fmres.value.capture_regs, fmres.value.look_regs, fmres.value.quant_regs,
                          plus_bcv, str, ovx, dir);
    }
    ReplayCapAgreeFreshLB(bytecode, str, cp, cap, lk, qt, ov, lookcdn, body, ncap, nlook, nquant);
  }

  /** A FRESH body match is well-formed (register arrays keep length `ncap`/etc.).
      The fresh run's clocks start at -1 <= 0, so the clock/reg backbone applies
      (`FInitState{ClocksLE,RegsWf}` + `FFindMatchThreadFacts`). This pins the
      length of the value-lift's fresh reference, which `RegsAgreeInside` needs. */
  lemma FreshMatchWf(bytecode: RB.code, str: string, cp: int, ov: LOr.OracleView, cdn: LCdn.cdns,
                     body: R.regex, ncap: int, nlook: int, nquant: int)
    requires NR.LookBehindFragmentRE(body) && PIV.CapUnique(body) && PIV.QuantUnique(body)
    requires bytecode == CP.compile_to_bytecode(body)
    requires ncap >= 0 && nlook >= 0 && nquant >= 0
    requires 0 <= cp <= |str|
    requires AI.cp_context(cp, str, LAnc.Forward).nextchar == AI.get_char(str, cp)
    ensures var rf := AI.FFindMatch(bytecode, str,
                        AI.FInitState(bytecode, cp, AReg.init_regs(ncap), AReg.init_regs(nlook),
                                      AReg.init_regs(nquant), 0, AI.cp_context(cp, str, LAnc.Forward)),
                        ov, LAnc.Forward, cdn).0;
      rf.Some? ==> CM.ThreadRegsWf(rf.value, ncap, nlook, nquant)
  {
    var dir := LAnc.Forward;
    var ctx := AI.cp_context(cp, str, dir);
    var inits := AI.FInitState(bytecode, cp, AReg.init_regs(ncap), AReg.init_regs(nlook),
                               AReg.init_regs(nquant), 0, ctx);
    CM.RegsClocksLEInit(ncap, 0);
    CM.RegsClocksLEInit(nlook, 0);
    CM.RegsClocksLEInit(nquant, 0);
    CM.FInitStateClocksLE(bytecode, cp, AReg.init_regs(ncap), AReg.init_regs(nlook),
                          AReg.init_regs(nquant), 0, ctx);
    CM.FInitStateRegsWf(bytecode, cp, ncap, nlook, nquant, 0, ctx);
    NoTrueQuantStamp(body);
    assert VmQuantFinal(inits) by {
      assert QuantRegsFinal(AI.init_thread(AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant)));
    }
    FFindMatchThreadFacts(bytecode, str, inits, ov, dir, cdn, ncap, nlook, nquant);
  }

  /** L3b: register well-formedness of the FRESH BACKWARD lookbehind match -- the
      lookbehind twin of `FreshMatchWf`. `FFindMatchThreadFacts` is forward-only, but
      the dir-generic `FFindMatchRegsWf` gives `ThreadRegsWf` (which is all the quant
      value lift's assemble needs) from the fresh-init `VmRegsWf`. */
  lemma FreshMatchWfLB(bytecode: RB.code, str: string, cp: int, ov: LOr.OracleView, cdn: LCdn.cdns,
                       body: R.regex, ncap: int, nlook: int, nquant: int)
    requires NR.PlusFragmentRE(body) && PIV.CapUnique(body) && PIV.QuantUnique(body)
    requires bytecode == CP.compile_to_bytecode(R.reverse_regex(body))
    requires ncap >= 0 && nlook >= 0 && nquant >= 0
    requires 0 <= cp <= |str|
    requires AI.cp_context(cp, str, LAnc.Backward).nextchar == AI.get_char(str, cp - 1)
    ensures var rf := AI.FFindMatch(bytecode, str,
                        AI.FInitState(bytecode, cp, AReg.init_regs(ncap), AReg.init_regs(nlook),
                                      AReg.init_regs(nquant), 0, AI.cp_context(cp, str, LAnc.Backward)),
                        ov, LAnc.Backward, cdn).0;
      rf.Some? ==> CM.ThreadRegsWf(rf.value, ncap, nlook, nquant)
  {
    var dir := LAnc.Backward;
    var ctx := AI.cp_context(cp, str, dir);
    var inits := AI.FInitState(bytecode, cp, AReg.init_regs(ncap), AReg.init_regs(nlook),
                               AReg.init_regs(nquant), 0, ctx);
    CM.FInitStateRegsWf(bytecode, cp, ncap, nlook, nquant, 0, ctx);
    FFindMatchRegsWf(bytecode, str, inits, ov, dir, cdn, ncap, nlook, nquant);
  }

  /** The lookahead replay preserves register well-formedness: from a `VmRegsWf`
      seed the FFindMatch result is `ThreadRegsWf` (`FFindMatchRegsWf`, no clock
      bound), and `FReconstructPlus` is the identity (`FNulledPlusIdentity`), so
      the FFindMatchPlus result is `ThreadRegsWf` too. Threads the fold's register
      lengths + `CapRegWf` past each replay. */
  lemma ReplayThreadWfLA(bytecode: RB.code, str: string, cp: int, cap: AReg.Regs, lk: AReg.Regs,
                         qt: AReg.Regs, ov: LOr.OracleView, lookcdn: LCdn.cdns, plus_bcv: seq<RB.code>,
                         body: R.regex, la: R.lookaround, ncap: int, nlook: int, nquant: int)
    requires NR.LookBehindFragmentRE(body) && PIV.CapUnique(body) && PIV.QuantUnique(body)
    requires la.Lookahead?
    requires bytecode == CP.compile_to_bytecode(body)
    requires 0 <= cp <= |str|
    requires AI.cp_context(cp, str, LAnc.Forward).nextchar == AI.get_char(str, cp)
    requires PIV.CapRegWf(cap)
    requires |cap.a_cp| == ncap && |cap.a_clk| == ncap
    requires |lk.a_cp| == nlook && |lk.a_clk| == nlook
    requires |qt.a_cp| == nquant && |qt.a_clk| == nquant
    requires (forall k :: AI.get_idx(qt.a_cp, k) < 0)
          && (forall k :: AI.get_idx(qt.a_clk, k) >= -1)
    ensures
      var result := AI.FFindMatchPlus(bytecode, body, plus_bcv, str, ov, LAnc.Forward, cp, cap, lk, qt, 0, lookcdn).0;
      result.Some? ==> CM.ThreadRegsWf(result.value, ncap, nlook, nquant)
  {
    var dir := LAnc.Forward;
    var ctx := AI.cp_context(cp, str, dir);
    var inits := AI.FInitState(bytecode, cp, cap, lk, qt, 0, ctx);
    assert CM.VmRegsWf(inits, ncap, nlook, nquant) by {
      assert CM.ThreadRegsWf(AI.init_thread(cap, lk, qt), ncap, nlook, nquant);
      assert inits.active == [AI.init_thread(cap, lk, qt)];
      forall t | t in inits.active ensures CM.ThreadRegsWf(t, ncap, nlook, nquant) {}
    }
    FFindMatchRegsWf(bytecode, str, inits, ov, dir, lookcdn, ncap, nlook, nquant);   // ThreadRegsWf(fmres)
    NoTrueQuantStamp(body);
    assert VmQuantFinal(inits) by { assert QuantRegsFinal(AI.init_thread(cap, lk, qt)); }
    FFindMatchQuantFinalAny(bytecode, str, inits, ov, dir, lookcdn);
    var (fmres, ovx) := AI.FFindMatch(bytecode, str, inits, ov, dir, lookcdn);
    if fmres.Some? {
      FNulledPlusIdentity(body, fmres.value.capture_regs, fmres.value.look_regs, fmres.value.quant_regs,
                          plus_bcv, str, ovx, dir);
    }
  }

  /** L3b: register well-formedness of the BACKWARD capturing-lookbehind replay --
      the lookbehind twin of `ReplayThreadWfLA`. `FFindMatchRegsWf` is dir-generic;
      the reversed-body statics come from the `Reverse*` helpers. */
  lemma ReplayThreadWfLB(bytecode: RB.code, str: string, cp: int, cap: AReg.Regs, lk: AReg.Regs,
                         qt: AReg.Regs, ov: LOr.OracleView, lookcdn: LCdn.cdns, plus_bcv: seq<RB.code>,
                         body: R.regex, ncap: int, nlook: int, nquant: int)
    requires NR.LookFreeRE(body) && NR.PlusFragmentRE(body)
    requires PIV.CapUnique(body) && PIV.QuantUnique(body)
    requires bytecode == CP.compile_to_bytecode(R.reverse_regex(body))
    requires 0 <= cp <= |str|
    requires AI.cp_context(cp, str, LAnc.Backward).nextchar == AI.get_char(str, cp - 1)
    requires PIV.CapRegWf(cap)
    requires |cap.a_cp| == ncap && |cap.a_clk| == ncap
    requires |lk.a_cp| == nlook && |lk.a_clk| == nlook
    requires |qt.a_cp| == nquant && |qt.a_clk| == nquant
    requires (forall k :: AI.get_idx(qt.a_cp, k) < 0)
          && (forall k :: AI.get_idx(qt.a_clk, k) >= -1)
    ensures
      var result := AI.FFindMatchPlus(bytecode, body, plus_bcv, str, ov, LAnc.Backward, cp, cap, lk, qt, 0, lookcdn).0;
      result.Some? ==> CM.ThreadRegsWf(result.value, ncap, nlook, nquant)
  {
    var rev := R.reverse_regex(body);
    PIV.ReversePlusFragment(body);
    NR.PlusIsLookBehindFragmentRE(rev);
    PIV.ReverseCapUnique(body);
    PIV.ReverseQuantUnique(body);
    var dir := LAnc.Backward;
    var inits := AI.FInitState(bytecode, cp, cap, lk, qt, 0, AI.cp_context(cp, str, dir));
    assert CM.VmRegsWf(inits, ncap, nlook, nquant) by {
      assert CM.ThreadRegsWf(AI.init_thread(cap, lk, qt), ncap, nlook, nquant);
      assert inits.active == [AI.init_thread(cap, lk, qt)];
      forall t | t in inits.active ensures CM.ThreadRegsWf(t, ncap, nlook, nquant) {}
    }
    FFindMatchRegsWf(bytecode, str, inits, ov, dir, lookcdn, ncap, nlook, nquant);
    NoTrueQuantStamp(rev);
    assert VmQuantFinal(inits) by { assert QuantRegsFinal(AI.init_thread(cap, lk, qt)); }
    FFindMatchQuantFinalAny(bytecode, str, inits, ov, dir, lookcdn);
    var (fmres, ovx) := AI.FFindMatch(bytecode, str, inits, ov, dir, lookcdn);
    if fmres.Some? {
      FNulledPlusIdentity(body, fmres.value.capture_regs, fmres.value.look_regs, fmres.value.quant_regs,
                          plus_bcv, str, ovx, dir);
    }
  }

  /** The per-lid input-context health `ReplayCapAgreeFresh`/`FreshMatchWf` need. */
  ghost predicate cp_ctx_ok(crv: CP.FCompiled, str: string, lk: AReg.Regs, l: int)
    requires AReg.get_cp(lk, l).Some?
  {
    var cp := AReg.get_cp(lk, l).value;
    0 <= cp <= |str| && AI.cp_context(cp, str, LAnc.Forward).nextchar == AI.get_char(str, cp)
  }

  /** (S-i) cp_ctx_ok on the WINNING thread, from the cp-bound. A forward main
      match starting FRESH records only look cps in `[0, |str|]` (`CM.FFindMatch
      LookCpOk`), and `cp_context`'s forward `nextchar` is definitional -- so every
      recorded look cp satisfies `cp_ctx_ok`. This is the (S-i) piece the value
      lift's `cp_ctx_ok` hypothesis needs; it does NOT require the exact
      look-position <-> tree correspondence. */
  lemma MainMatchCpCtxOk(crv: CP.FCompiled, code: RB.code, str: string, inits: AI.VmState,
                         cap: AReg.Regs, look: AReg.Regs, quant: AReg.Regs, nlook: int,
                         ov: LOr.OracleView, cdn: LCdn.cdns, result: Option<AI.Thread>)
    requires |inits.processed.true_set| == RB.size(code) && |inits.processed.false_set| == RB.size(code)
    requires inits.context.nextchar == AI.get_char(str, inits.cp)
    requires 0 <= inits.cp <= |str|
    requires look == AReg.init_regs(nlook)
    requires inits.active == [AI.init_thread(cap, look, quant)]
    requires inits.blocked == [] && inits.bestmatch.None?
    requires result == AI.FFindMatch(code, str, inits, ov, LAnc.Forward, cdn).0
    ensures result.Some? ==>
      forall l: int :: AReg.get_cp(result.value.look_regs, l).Some? ==>
        cp_ctx_ok(crv, str, result.value.look_regs, l)
  {
    // fresh init threads have all look cps == -1 <= |str|
    assert CM.VmLookCpOk(inits, |str|) by {
      assert CM.LookCpsLE(look, |str|) by {
        forall l: int ensures AI.get_idx(look.a_cp, l) <= |str| {
          if 0 <= l < |look.a_cp| { assert look.a_cp[l] == -1; }
        }
      }
      assert AI.init_thread(cap, look, quant).look_regs == look;
    }
    CM.FFindMatchLookCpOk(code, str, inits, ov, LAnc.Forward, cdn);
    if result.Some? {
      var lk := result.value.look_regs;
      assert CM.LookCpsLE(lk, |str|);
      forall l: int | AReg.get_cp(lk, l).Some? ensures cp_ctx_ok(crv, str, lk, l) {
        var cp := AReg.get_cp(lk, l).value;
        assert 0 <= l < |lk.a_cp| && cp == AI.get_idx(lk.a_cp, l) && cp >= 0;   // get_cp Some => a_cp[l] >= 0
        assert cp <= |str|;                                                      // LookCpsLE
      }
    }
  }

  /** L3a (E): the `get_idx(lc, lid) >= 0` half of `PIV.PathPresentLk`'s
      matched-lookaround condition, on the WINNING thread. A look whose cp was
      recorded (its `CheckOracle` fired on this thread's path) also carries a
      non-negative clock stamp, because both slots land in one `set_reg`. The
      `>= mx` half is coupled to the enclosing quant clocks and is NOT proved
      here — it is part of the outstanding position/structure gate. Companion to
      `MainMatchCpCtxOk`, same fresh-entry shape. */
  lemma MainMatchLookClkSet(code: RB.code, str: string, inits: AI.VmState,
                            cap: AReg.Regs, look: AReg.Regs, quant: AReg.Regs, nlook: int,
                            ov: LOr.OracleView, cdn: LCdn.cdns, result: Option<AI.Thread>)
    requires |inits.processed.true_set| == RB.size(code) && |inits.processed.false_set| == RB.size(code)
    requires inits.context.nextchar == AI.get_char(str, inits.cp)
    requires 0 <= inits.cp <= |str|
    requires inits.clock >= 0
    requires look == AReg.init_regs(nlook)
    requires inits.active == [AI.init_thread(cap, look, quant)]
    requires inits.blocked == [] && inits.bestmatch.None?
    requires result == AI.FFindMatch(code, str, inits, ov, LAnc.Forward, cdn).0
    ensures result.Some? ==>
      forall l: int :: AReg.get_cp(result.value.look_regs, l).Some? ==>
        AI.get_idx(result.value.look_regs.a_clk, l) >= 0
  {
    // fresh init threads have every look cp == -1, so the implication is vacuous
    assert CM.VmLookClkSet(inits) by {
      assert CM.LookClkSetWithCp(look) by {
        forall l: int | AI.get_idx(look.a_cp, l) >= 0 ensures AI.get_idx(look.a_clk, l) >= 0 {
          if 0 <= l < |look.a_cp| { assert look.a_cp[l] == -1; }
        }
      }
      assert AI.init_thread(cap, look, quant).look_regs == look;
    }
    CM.FFindMatchLookClkSet(code, str, inits, ov, LAnc.Forward, cdn);
    if result.Some? {
      var lk := result.value.look_regs;
      assert CM.LookClkSetWithCp(lk);
      forall l: int | AReg.get_cp(lk, l).Some? ensures AI.get_idx(lk.a_clk, l) >= 0 {
        assert 0 <= l < |lk.a_cp| && AI.get_idx(lk.a_cp, l) >= 0;   // get_cp Some => a_cp[l] >= 0
      }
    }
  }

  /** L3a (E2): the MAIN pass never stamps an inside-look quant — every
      `SetQuantToClock` in the fragment code targets `QuantIdsOutsideLooks(re)`
      (`PIV.QuantWriteIdsRE`, L3a-sharpened) — so a genuine-start search
      returns a winning thread whose quant bank still agrees with the INITIAL
      bank outside that set. In particular every look body's quant slots are
      EXACTLY initial: the entry fact of the FLookLoop quant value lift
      (`ReplayLidCapQuantAgreeFresh`'s body-quants-INIT hypothesis). */
  lemma MainMatchBodyQuantsInit(re: R.regex, code: RB.code, endl: nat, str: string,
                                inits: AI.VmState, cap: AReg.Regs, look: AReg.Regs, quant: AReg.Regs,
                                ov: LOr.OracleView, cdn: LCdn.cdns, result: Option<AI.Thread>)
    requires NR.LookBehindFragmentRE(re) && PIV.QuantUnique(re)
    requires NR.NfaRepRE(re, code, 0, endl) && |code| == endl + 1
    requires NR.GetPcRE(code, endl) == Some(RB.Accept)
    requires |inits.processed.true_set| == RB.size(code) && |inits.processed.false_set| == RB.size(code)
    requires inits.context.nextchar == AI.get_char(str, inits.cp)
    requires inits.active == [AI.init_thread(cap, look, quant)]
    requires inits.blocked == [] && inits.bestmatch.None?
    requires result == AI.FFindMatch(code, str, inits, ov, LAnc.Forward, cdn).0
    ensures var S := set q: nat | q in PIV.QuantIdsOutsideLooks(re) :: q as int;
      result.Some? ==> CM.RegsAgreeOutside(result.value.quant_regs, quant, S)
  {
    var S := set q: nat | q in PIV.QuantIdsOutsideLooks(re) :: q as int;
    assert CM.QuantWritesInside(code, S) by {
      forall pc: nat | pc < |code| ensures code[pc].SetQuantToClock? ==> code[pc].sq in S {
        assert NR.GetPcRE(code, pc) == Some(code[pc]);
        if pc < endl {
          PIV.QuantWriteIdsRE(re, code, 0, endl, pc);
          if code[pc].SetQuantToClock? {
            var qn: nat := code[pc].sq as nat;
            assert qn in PIV.QuantIdsOutsideLooks(re);
            assert (qn as int) in S;
          }
        } else {
          assert pc == endl;                          // the Accept terminator
        }
      }
    }
    assert CM.VmQuantsAgree(inits, quant, S) by {
      assert AI.init_thread(cap, look, quant).quant_regs == quant;
      assert CM.RegsAgreeOutside(quant, quant, S);
    }
    CM.FFindMatchQuantFrame(code, str, inits, ov, LAnc.Forward, cdn, quant, S);
  }

  /** L3a (E4): the MAIN pass writes only OUTSIDE-look capture registers
      (`PIV.CaptureWriteIdsOutsideRE` per pc), so a genuine-start search
      returns a winning thread whose INSIDE-look capture slots are EXACTLY
      initial — value and clock both `-1`. The reverse tie's unmatched-owner
      case reads this: an untouched owner leaves `res0`'s slot unset. */
  lemma MainMatchInsideCapsInit(re: R.regex, code: RB.code, endl: nat, str: string,
                                inits: AI.VmState, cap: AReg.Regs, look: AReg.Regs, quant: AReg.Regs,
                                ov: LOr.OracleView, cdn: LCdn.cdns, result: Option<AI.Thread>)
    requires NR.LookBehindFragmentRE(re) && PIV.CapUnique(re)
    requires NR.NfaRepRE(re, code, 0, endl) && |code| == endl + 1
    requires NR.GetPcRE(code, endl) == Some(RB.Accept)
    requires |inits.processed.true_set| == RB.size(code) && |inits.processed.false_set| == RB.size(code)
    requires inits.context.nextchar == AI.get_char(str, inits.cp)
    requires inits.active == [AI.init_thread(cap, look, quant)]
    requires inits.blocked == [] && inits.bestmatch.None?
    requires result == AI.FFindMatch(code, str, inits, ov, LAnc.Forward, cdn).0
    ensures var Sc := PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(re));
      result.Some? ==> CM.RegsAgreeOutside(result.value.capture_regs, cap, Sc)
  {
    var Sc := PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(re));
    assert CM.CaptureWritesInside(code, Sc) by {
      forall pc: nat | pc < |code| ensures code[pc].SetRegisterToCP? ==> code[pc].reg in Sc {
        assert NR.GetPcRE(code, pc) == Some(code[pc]);
        if pc < endl {
          PIV.CaptureWriteIdsOutsideRE(re, code, 0, endl, pc);
        } else {
          assert pc == endl;                          // the Accept terminator
        }
      }
    }
    assert CM.VmCapturesAgree(inits, cap, Sc) by {
      assert AI.init_thread(cap, look, quant).capture_regs == cap;
      assert CM.RegsAgreeOutside(cap, cap, Sc);
    }
    CM.FFindMatchCapWriteFrame(code, str, inits, ov, LAnc.Forward, cdn, cap, Sc);
  }

  /** L3a (S-i): on the WINNING thread, every recorded look cp is a position
      where that look's ORACLE BIT IS SET — `CheckOracle` writes `a_cp[l]` only
      on the branch that just read the bit, and the main pass never writes the
      view. Same fresh-entry shape as `MainMatchCpCtxOk`. */
  lemma MainMatchLookOracleTrue(code: RB.code, str: string, inits: AI.VmState,
                                cap: AReg.Regs, look: AReg.Regs, quant: AReg.Regs, nlook: int,
                                ov: LOr.OracleView, cdn: LCdn.cdns, result: Option<AI.Thread>)
    requires |inits.processed.true_set| == RB.size(code) && |inits.processed.false_set| == RB.size(code)
    requires CM.NoWriteOracleCode(code)
    requires inits.context.nextchar == AI.get_char(str, inits.cp)
    requires 0 <= inits.cp <= |str|
    requires look == AReg.init_regs(nlook)
    requires inits.active == [AI.init_thread(cap, look, quant)]
    requires inits.blocked == [] && inits.bestmatch.None?
    requires result == AI.FFindMatch(code, str, inits, ov, LAnc.Forward, cdn).0
    ensures result.Some? ==> CM.LookCpsOracleTrue(result.value.look_regs, ov)
  {
    // fresh init threads have every look cp == -1, so the guard is vacuous
    assert CM.VmLookOracleTrue(inits, ov) by {
      assert CM.LookCpsOracleTrue(look, ov) by {
        forall l: int | AI.get_idx(look.a_cp, l) >= 0
          ensures LOr.view_get_oracle(ov, AI.get_idx(look.a_cp, l), l)
        {
          if 0 <= l < |look.a_cp| { assert look.a_cp[l] == -1; }
        }
      }
      assert AI.init_thread(cap, look, quant).look_regs == look;
    }
    CM.FFindMatchLookOracleTrue(code, str, inits, ov, LAnc.Forward, cdn);
  }

  /** L3a (S-i) PAYOFF: the SPEC look `l` MATCHES at the engine's recorded
      `a_cp[l]`. The engine says the bit is set there (`LookCpsOracleTrue`);
      `OracleOkAt` says the bit at a position is exactly the spec body's verdict
      there. So the two candidate positions of the §2 gate — the engine's
      `a_cp[l]` and the spec LK node's `inp_l` — are BOTH positions at which look
      `l` matches. That is the engine-side half of the oracle-uniqueness
      argument; identifying them still needs the path-uniqueness half (that on
      the priority-first winning path the look is crossed at a UNIQUE position),
      which is NOT proved here. */
  lemma LookCpSpecMatch(rer: LW.RegExpRecord, qm: AR.QMap, str: string, lk: AReg.Regs,
                        l: int, lkr: L.Lookaround, r1: L.Regex)
    requires CM.LookCpsOracleTrue(lk, qm.ov)
    requires CM.LookCpsLE(lk, |str|)
    requires AI.get_idx(lk.a_cp, l) >= 0
    requires l in qm.looks && qm.looks[l] == (lkr, r1)
    requires LL.OracleOkAt(rer, qm, PIV.InpOfCp(str, AI.get_idx(lk.a_cp, l) as nat))
    ensures var inpl := PIV.InpOfCp(str, AI.get_idx(lk.a_cp, l) as nat);
      LT.TreeRes(FU.ComputeTr(rer, [LS.Areg(r1)], inpl, LG.Empty, L.LkDir(lkr)),
                 LG.Empty, inpl, L.LkDir(lkr)).Some?
  {
    var cp := AI.get_idx(lk.a_cp, l) as nat;          // 0 <= cp <= |str| (LookCpsLE)
    var inpl := PIV.InpOfCp(str, cp);
    assert TR.CpOf(inpl) == cp by { LS.ReverseLength(str[..cp]); }
    assert LOr.view_get_oracle(qm.ov, cp, l);         // LookCpsOracleTrue at l
  }

  /** L3a §2 SPEC-SIDE GATE POSITION. When the action walk's head is a
      lookaround, `BoolTreeLk` FORCES the spec tree at that point to be the
      lookaround's own node — `LK` on a pass, `LKFail` on a kill — and
      `LkGateOk` pins its body tree to `ComputeTr(.., inp, ..)` at THAT SAME
      `inp`. So the LK node's position is definitionally the walk's current
      input; there is no separate position theorem to prove on this side.
      Pure inversion of the `least predicate`, so it costs nothing.

      This is the half of §2's `GatePos(tstar,l) == inp_l` that lives on the
      spec: `ActionsTreeRepFRE`'s gate case pins `lid` from the `CheckOracle`
      instruction at `pc` while holding `t` at `inp`, and this says that `t`
      is then lid's LK node AT `inp`. It is stated here rather than in
      `EntryLk` to keep the change inside a file with a fresh baseline.

      What it does NOT give: the tie to the ENGINE's `a_cp[l]`. That needs the
      winning thread's PATH to be matched to the first-leaf path of `tstar`,
      and the simulation state carries no history to express it (see the
      session notes). */
  lemma GateNodeAtInp(rer: LW.RegExpRecord, acts: LS.Actions, inp: LC.Input,
                      b: BS.LoopBool, t: LT.Tree, lk: L.Lookaround, r1: L.Regex)
    requires |acts| > 0 && acts[0] == LS.Areg(L.LookaroundR(lk, r1))
    requires EL.BoolTreeLk(rer, acts, inp, b, t)
    ensures (t.LK? && t.lk == lk
             && EL.LkGateOk(rer, lk, r1, inp, t.tlk, true)
             && EL.BoolTreeLk(rer, acts[1..], inp, b, t.t))
         || (t.LKFail? && t.lk == lk && EL.LkGateOk(rer, lk, r1, inp, t.tlk, false))
  {
    // unfold the gate case: the match on `t` admits only LK / LKFail
  }

  /** Corollary in the form §2 wants it: the body tree hanging at the gate is
      the one computed AT `inp`, i.e. the gate's position is `TR.CpOf(inp)`. */
  lemma GatePosIsWalkInp(rer: LW.RegExpRecord, acts: LS.Actions, inp: LC.Input,
                         b: BS.LoopBool, t: LT.Tree, lk: L.Lookaround, r1: L.Regex)
    requires |acts| > 0 && acts[0] == LS.Areg(L.LookaroundR(lk, r1))
    requires EL.BoolTreeLk(rer, acts, inp, b, t)
    ensures t.LK? || t.LKFail?
    ensures t.tlk == FU.ComputeTr(rer, [LS.Areg(r1)], inp, LG.Empty, L.LkDir(lk))
  {
    GateNodeAtInp(rer, acts, inp, b, t, lk, r1);
  }

  /** L3a §2 CHECKED-SIDE GATE POSITION — the mirror of `GateNodeAtInp`. At a
      `CheckOracle(lid)` pc every other `TreeRepRE` disjunct pins a different
      instruction, so only the gate rule can apply: on a set bit the derivation
      carries the SAME tree on to `pc+1` at the SAME `inp` (the transparency
      `TT.StuttersRE` records), and on a clear bit the tree is `Mismatch`.
      Pure inversion, in the style of `TT.TtAtJmp`. */
  lemma GateFiresAtWalkInp(qm: AR.QMap, tstar: LT.Tree, code: RB.code, pc: nat,
                           inp: LC.Input, b: bool, lid: int)
    requires TR.TreeRepRE(qm, tstar, code, pc, inp, b)
    requires NR.GetPcRE(code, pc) == Some(RB.CheckOracle(lid))
    ensures LOr.view_get_oracle(qm.ov, TR.CpOf(inp), lid) ==>
              TR.TreeRepRE(qm, tstar, code, pc + 1, inp, b)
    ensures !LOr.view_get_oracle(qm.ov, TR.CpOf(inp), lid) ==> tstar == LT.Mismatch
  {
  }

  /** The cp-level reading of the mirror, in the form the simulation supplies
      its inputs: a derivation standing at lid's gate with the VM at `cp` fires
      that gate AT `cp` — because `PIV.PikeInvRE`'s `PTS` case carries
      `inp == InpOfCp(str, vms.cp)`, so the derivation's input at every step IS
      the VM's cp.

      Together with `GateNodeAtInp` (spec side) both halves of §2's position
      question are now local inversions: the gate fires at the walk's `inp` on
      BOTH sides. What is still missing to close the gate is neither of these —
      it is that the crossing which wrote the winning thread's FINAL `a_cp[l]`
      is the one on the first-leaf path (the sim relates threads to `tstar`
      subtrees, and a subtree does not know the path taken to reach it). */
  lemma GateFiresAtCp(qm: AR.QMap, tstar: LT.Tree, code: RB.code, pc: nat,
                      str: string, cp: nat, b: bool, lid: int)
    requires cp <= |str|
    requires TR.TreeRepRE(qm, tstar, code, pc, PIV.InpOfCp(str, cp), b)
    requires NR.GetPcRE(code, pc) == Some(RB.CheckOracle(lid))
    requires LOr.view_get_oracle(qm.ov, cp, lid)
    ensures TR.TreeRepRE(qm, tstar, code, pc + 1, PIV.InpOfCp(str, cp), b)
  {
    var inp := PIV.InpOfCp(str, cp);
    assert TR.CpOf(inp) == cp by { LS.ReverseLength(str[..cp]); }
    GateFiresAtWalkInp(qm, tstar, code, pc, inp, b, lid);
  }

  /** Agreeing OUTSIDE `Sp` and equal lengths give agreement INSIDE any `T`
      disjoint from `Sp`. Isolated so the set step doesn't drag heavy context. */
  lemma RegsAgreeOutsideToInside(a: AReg.Regs, b: AReg.Regs, T: set<int>, Sp: set<int>)
    requires CM.RegsAgreeOutside(a, b, Sp)
    requires |a.a_cp| == |b.a_cp| && |a.a_clk| == |b.a_clk|
    requires forall k: int :: k in T ==> k !in Sp
    ensures CM.RegsAgreeInside(a, b, T)
  {}

  /** THE FLookLoop VALUE LIFT (lookahead-only fold). On each matched positive
      lookahead's own capture registers, the fold result carries that body's
      FRESH match; and the fold preserves register lengths. Every capturing lid is
      a lookahead (`requires`, discharged by the caller for lookahead-capturing
      regexes; capture-free lookbehinds are L1 and can be admitted later). */
  lemma {:isolate_assertions} FLookLoopValueLift(crv: CP.FCompiled, str: string, lid: int, maxlook: int,
                           cap: AReg.Regs, lk: AReg.Regs, qt: AReg.Regs, ov: LOr.OracleView,
                           mainast: R.regex, S: set<int>, ncap: int, nlook: int, nquant: int)
    requires ncap >= 0 && nlook >= 0 && nquant >= 0
    requires NR.LookBehindFragmentRE(mainast) && PIV.QuantUnique(mainast)
    requires (forall k :: AI.get_idx(qt.a_cp, k) < 0)
          && (forall k :: AI.get_idx(qt.a_clk, k) >= -1)
    requires |qt.a_cp| == nquant && |qt.a_clk| == nquant
    requires |cap.a_cp| == ncap && |cap.a_clk| == ncap && PIV.CapRegWf(cap)
    requires |lk.a_cp| == nlook && |lk.a_clk| == nlook
    requires forall l: int :: lid <= l <= maxlook && AReg.get_cp(lk, l).Some? ==>
      exists la: R.lookaround, body: R.regex ::
        LTB.LookEntryOk(crv, l, la, body)
        && NR.LookFreeRE(body) && NR.PlusFragmentRE(body)
        && PIV.CapUnique(body) && PIV.QuantUnique(body)
        && PIV.CaptureRegs(body) <= S
        && (forall q: nat :: q in PIV.QuantIds(body) ==> q in PIV.QuantIdsInLooks(mainast))
        && ((la.NegLookbehind? || la.NegLookahead?) ==> NR.CaptureFreeRE(body))
    // NOTE (L3a full fragment): NO lookahead-only requires. A capturing body is
    // necessarily a positive forward lookahead (fragment), and capture-free
    // positive lookbehinds are stepped through as the identity below -- so the
    // value lift holds for the whole fragment (lookbehinds included).
    // each matched body's own registers are UNSET in the incoming `cap`
    requires forall l: int :: lid <= l <= maxlook && AReg.get_cp(lk, l).Some? ==>
      CM.RegsAgreeInside(cap, AReg.init_regs(ncap), PIV.CaptureRegs(VBody(crv, l)))
    // distinct matched lids write DISJOINT capture registers
    requires forall l1: int, l2: int ::
      lid <= l1 <= maxlook && lid <= l2 <= maxlook && l1 != l2
      && AReg.get_cp(lk, l1).Some? && AReg.get_cp(lk, l2).Some? ==>
      PIV.CaptureRegs(VBody(crv, l1)) * PIV.CaptureRegs(VBody(crv, l2)) == {}
    requires forall l: int :: lid <= l <= maxlook && AReg.get_cp(lk, l).Some? ==> cp_ctx_ok(crv, str, lk, l)
    ensures var res := AI.FLookLoop(crv, str, lid, maxlook, cap, lk, qt, ov);
      |res.0.a_cp| == ncap && |res.0.a_clk| == ncap && PIV.CapRegWf(res.0)
      && FLookLoopValueOk(crv, str, res.0, lid, maxlook, lk, ov, ncap, nlook, nquant)
    decreases maxlook - lid
  {
    var res := AI.FLookLoop(crv, str, lid, maxlook, cap, lk, qt, ov);
    if lid > maxlook {
      assert res.0 == cap;
      return;
    }
    var next := lid + 1;
    match AReg.get_cp(lk, lid)
    case None =>
      assert res == AI.FLookLoop(crv, str, next, maxlook, cap, lk, qt, ov);
      FLookLoopValueLift(crv, str, next, maxlook, cap, lk, qt, ov, mainast, S, ncap, nlook, nquant);
      ValueOkSkipLid(crv, str, res.0, lid, maxlook, lk, ov, ncap, nlook, nquant);
    case Some(cp) =>
      var looktype := if 0 <= lid < |crv.f_look_types| then crv.f_look_types[lid] else R.Lookahead;
      if !AI.capture_type(looktype) {
        assert res == AI.FLookLoop(crv, str, next, maxlook, cap, lk, qt, ov);
        FLookLoopValueLift(crv, str, next, maxlook, cap, lk, qt, ov, mainast, S, ncap, nlook, nquant);
        ValueOkSkipLid(crv, str, res.0, lid, maxlook, lk, ov, ncap, nlook, nquant);
      } else {
        var la: R.lookaround, body: R.regex :|
          LTB.LookEntryOk(crv, lid, la, body)
          && NR.LookFreeRE(body) && NR.PlusFragmentRE(body)
          && PIV.CapUnique(body) && PIV.QuantUnique(body)
          && PIV.CaptureRegs(body) <= S
          && (forall q: nat :: q in PIV.QuantIds(body) ==> q in PIV.QuantIdsInLooks(mainast))
          && ((la.NegLookbehind? || la.NegLookahead?) ==> NR.CaptureFreeRE(body));
        assert looktype == la;
        assert body == VBody(crv, lid);
        var bytecode := AI.get_code_v(crv.f_look_capture_bc, lid);
        var dir := AI.capture_direction(looktype);
        var lookcdn := if 0 <= lid < |crv.f_look_cdns| then crv.f_look_cdns[lid] else [];
        var lookast := if 0 <= lid < |crv.f_look_ast| then crv.f_look_ast[lid] else R.Re_empty;
        assert lookast == body;
        assert bytecode == CP.compile_to_bytecode(CP.capture_regex(la, body));
        var (result, ov1) := AI.FFindMatchPlus(bytecode, lookast, crv.f_plus_bc, str, ov, dir,
                                               cp, cap, lk, qt, 0, lookcdn);
        var capN := if result.None? then cap else result.value.capture_regs;
        var lkN := if result.None? then lk else result.value.look_regs;
        var qtN := if result.None? then qt else result.value.quant_regs;
        assert res == AI.FLookLoop(crv, str, next, maxlook, capN, lkN, qtN, ov1);
        NR.PlusIsLookBehindFragmentRE(body);
        // capture_type(la) holds => la is Lookahead (positive forward, may
        // capture) or Lookbehind (capture-free -> the identity on captures).
        if la.Lookahead? {
        assert dir == LAnc.Forward && CP.capture_regex(la, body) == body;
        assert bytecode == CP.compile_to_bytecode(body);
        FFindMatchPlusOvStable(bytecode, str, ov, dir, lookcdn, crv.f_plus_bc, cp, cap, lk, qt, la, body);
        assert ov1 == ov;
        ReplayPlusFrame(bytecode, str, ov, dir, lookcdn, crv.f_plus_bc, cp, cap, lk, qt, la, body);
        assert CM.RegsAgreeOutside(capN, cap, PIV.CaptureRegs(body)) && lkN == lk;
        assert (forall k :: AI.get_idx(qtN.a_cp, k) < 0) && (forall k :: AI.get_idx(qtN.a_clk, k) >= -1);
        ReplayThreadWfLA(bytecode, str, cp, cap, lk, qt, ov, lookcdn, crv.f_plus_bc, body, la, ncap, nlook, nquant);
        assert |capN.a_cp| == ncap && |capN.a_clk| == ncap && PIV.CapRegWf(capN)
            && |qtN.a_cp| == nquant && |qtN.a_clk| == nquant by {
          if result.Some? { assert CM.ThreadRegsWf(result.value, ncap, nlook, nquant); }
        }

        // ---- value at lid: result ~ rfLid on CaptureRegs(body) ----
        assert cp_ctx_ok(crv, str, lk, lid);
        assert 0 <= cp <= |str| && AI.cp_context(cp, str, LAnc.Forward).nextchar == AI.get_char(str, cp);
        ReplayLidCapAgreeFresh(bytecode, str, cp, cap, lk, qt, ov, lookcdn, crv.f_plus_bc, body, la, ncap, nlook, nquant);
        FreshMatchWf(bytecode, str, cp, ov, lookcdn, body, ncap, nlook, nquant);
        var rfLid := FreshBodyMatch(crv, str, lid, lk, ov, ncap, nlook, nquant);
        var rf := AI.FFindMatch(bytecode, str,
                    AI.FInitState(bytecode, cp, AReg.init_regs(ncap), AReg.init_regs(nlook),
                                  AReg.init_regs(nquant), 0, AI.cp_context(cp, str, LAnc.Forward)),
                    ov, LAnc.Forward, lookcdn).0;
        assert rfLid == rf;                      // VBody(lid)==body, cdn==lookcdn, cp matches

        // ---- suffix bundle at S' = S - CaptureRegs(body); frame ----
        var Sp := S - PIV.CaptureRegs(body);
        assert forall l: int :: next <= l <= maxlook && AReg.get_cp(lkN, l).Some? ==>
          exists la2: R.lookaround, body2: R.regex ::
            LTB.LookEntryOk(crv, l, la2, body2)
            && NR.LookFreeRE(body2) && NR.PlusFragmentRE(body2)
            && PIV.CapUnique(body2) && PIV.QuantUnique(body2)
            && PIV.CaptureRegs(body2) <= Sp
            && (forall q: nat :: q in PIV.QuantIds(body2) ==> q in PIV.QuantIdsInLooks(mainast))
            && ((la2.NegLookbehind? || la2.NegLookahead?) ==> NR.CaptureFreeRE(body2))
        by {
          forall l: int | next <= l <= maxlook && AReg.get_cp(lkN, l).Some?
            ensures exists la2: R.lookaround, body2: R.regex ::
              LTB.LookEntryOk(crv, l, la2, body2)
              && NR.LookFreeRE(body2) && NR.PlusFragmentRE(body2)
              && PIV.CapUnique(body2) && PIV.QuantUnique(body2)
              && PIV.CaptureRegs(body2) <= Sp
              && (forall q: nat :: q in PIV.QuantIds(body2) ==> q in PIV.QuantIdsInLooks(mainast))
              && ((la2.NegLookbehind? || la2.NegLookahead?) ==> NR.CaptureFreeRE(body2))
          {
            assert AReg.get_cp(lk, l).Some?;
            var la2: R.lookaround, body2: R.regex :|
              LTB.LookEntryOk(crv, l, la2, body2)
              && NR.LookFreeRE(body2) && NR.PlusFragmentRE(body2)
              && PIV.CapUnique(body2) && PIV.QuantUnique(body2)
              && PIV.CaptureRegs(body2) <= S
              && (forall q: nat :: q in PIV.QuantIds(body2) ==> q in PIV.QuantIdsInLooks(mainast))
              && ((la2.NegLookbehind? || la2.NegLookahead?) ==> NR.CaptureFreeRE(body2));
            assert body2 == VBody(crv, l) && body == VBody(crv, lid);
            assert PIV.CaptureRegs(VBody(crv, l)) * PIV.CaptureRegs(VBody(crv, lid)) == {};   // pairwise
            assert PIV.CaptureRegs(body2) * PIV.CaptureRegs(body) == {};
            assert PIV.CaptureRegs(body2) <= Sp by {
              forall k: int | k in PIV.CaptureRegs(body2) ensures k in Sp {
                assert k in S;
                assert k !in PIV.CaptureRegs(body) by {
                  if k in PIV.CaptureRegs(body) { assert k in PIV.CaptureRegs(body2) * PIV.CaptureRegs(body); }
                }
              }
            }
          }
        }
        // ---- IH at [next] with capN (per-body-unset preserved by disjointness) ----
        assert forall l: int :: next <= l <= maxlook && AReg.get_cp(lk, l).Some? ==>
          CM.RegsAgreeInside(capN, AReg.init_regs(ncap), PIV.CaptureRegs(VBody(crv, l)))
        by {
          forall l: int | next <= l <= maxlook && AReg.get_cp(lk, l).Some?
            ensures CM.RegsAgreeInside(capN, AReg.init_regs(ncap), PIV.CaptureRegs(VBody(crv, l)))
          {
            assert body == VBody(crv, lid);
            assert PIV.CaptureRegs(VBody(crv, l)) * PIV.CaptureRegs(VBody(crv, lid)) == {};   // pairwise
            assert PIV.CaptureRegs(VBody(crv, l)) * PIV.CaptureRegs(body) == {};
            assert CM.RegsAgreeInside(cap, AReg.init_regs(ncap), PIV.CaptureRegs(VBody(crv, l)));   // per-body-unset
            forall k: int | k in PIV.CaptureRegs(VBody(crv, l))
              ensures AI.get_idx(capN.a_cp, k) == AI.get_idx(AReg.init_regs(ncap).a_cp, k)
                   && AI.get_idx(capN.a_clk, k) == AI.get_idx(AReg.init_regs(ncap).a_clk, k)
            {
              assert k !in PIV.CaptureRegs(body) by {
                if k in PIV.CaptureRegs(body) { assert k in PIV.CaptureRegs(VBody(crv, l)) * PIV.CaptureRegs(body); }
              }
              assert AI.get_idx(capN.a_cp, k) == AI.get_idx(cap.a_cp, k);   // capN ~ cap off body
            }
          }
        }
        FLookLoopValueLift(crv, str, next, maxlook, capN, lkN, qtN, ov1, mainast, S, ncap, nlook, nquant);
        assert FLookLoopValueOk(crv, str, res.0, next, maxlook, lk, ov, ncap, nlook, nquant);
        assert |res.0.a_cp| == ncap && |res.0.a_clk| == ncap;   // from the IH ensures

        // ---- frame: res.0 == capN on CaptureRegs(body) (suffix writes disjoint regs) ----
        FLookLoopCaptureFrame(crv, str, next, maxlook, capN, lkN, qtN, ov1, mainast, Sp);
        assert CM.RegsAgreeOutside(res.0, capN, Sp);
        assert forall k: int :: k in PIV.CaptureRegs(body) ==> k !in Sp;
        RegsAgreeOutsideToInside(res.0, capN, PIV.CaptureRegs(body), Sp);
        assert CM.RegsAgreeInside(res.0, capN, PIV.CaptureRegs(body));

        // ---- assemble FLookLoopValueOk for [lid] ----
        forall l: int | lid <= l <= maxlook && MatchedPosLA(crv, lk, l)
          ensures var rf2 := FreshBodyMatch(crv, str, l, lk, ov, ncap, nlook, nquant);
                  (rf2.Some? ==> CM.RegsAgreeInside(res.0, rf2.value.capture_regs, PIV.CaptureRegs(VBody(crv, l))))
                  && (rf2.None? ==> CM.RegsAgreeInside(res.0, AReg.init_regs(ncap), PIV.CaptureRegs(VBody(crv, l))))
        {
          if l == lid {
            if rfLid.Some? {
              assert result.Some? && CM.RegsAgreeInside(result.value.capture_regs, rf.value.capture_regs, PIV.CaptureRegs(body));
              assert CM.RegsAgreeInside(res.0, rfLid.value.capture_regs, PIV.CaptureRegs(body));
            } else {
              assert result.None? && capN == cap;
              assert CM.RegsAgreeInside(cap, AReg.init_regs(ncap), PIV.CaptureRegs(body));   // per-body-unset(lid)
              assert CM.RegsAgreeInside(res.0, AReg.init_regs(ncap), PIV.CaptureRegs(body));
            }
          }
        }
        } else {
          // ---- CAPTURING positive LOOKBEHIND (L3b): the backward capture replay,
          //      value-lifted exactly like the lookahead branch but with the
          //      lookbehind frames/bisimulation over compile_to_bytecode(reverse_regex(body)). ----
          assert la.Lookbehind?;
          assert dir == LAnc.Backward && CP.capture_regex(la, body) == R.reverse_regex(body);
          assert bytecode == CP.compile_to_bytecode(R.reverse_regex(body));
          assert cp_ctx_ok(crv, str, lk, lid);
          assert 0 <= cp <= |str|;
          assert AI.cp_context(cp, str, LAnc.Backward).nextchar == AI.get_char(str, cp - 1);
          FFindMatchPlusOvStableLB(bytecode, str, ov, dir, lookcdn, crv.f_plus_bc, cp, cap, lk, qt, la, body);
          assert ov1 == ov;
          ReplayPlusFrameLB(bytecode, str, ov, lookcdn, crv.f_plus_bc, cp, cap, lk, qt, body);
          assert CM.RegsAgreeOutside(capN, cap, PIV.CaptureRegs(body)) && lkN == lk;
          assert (forall k :: AI.get_idx(qtN.a_cp, k) < 0) && (forall k :: AI.get_idx(qtN.a_clk, k) >= -1);
          ReplayThreadWfLB(bytecode, str, cp, cap, lk, qt, ov, lookcdn, crv.f_plus_bc, body, ncap, nlook, nquant);
          assert |capN.a_cp| == ncap && |capN.a_clk| == ncap && PIV.CapRegWf(capN)
              && |qtN.a_cp| == nquant && |qtN.a_clk| == nquant by {
            if result.Some? { assert CM.ThreadRegsWf(result.value, ncap, nlook, nquant); }
          }

          // ---- value at lid: result ~ rf on CaptureRegs(body) (backward bisimulation) ----
          ReplayLidCapAgreeFreshLB(bytecode, str, cp, cap, lk, qt, ov, lookcdn, crv.f_plus_bc, body, ncap, nlook, nquant);
          var rfLid := FreshBodyMatch(crv, str, lid, lk, ov, ncap, nlook, nquant);
          var rf := AI.FFindMatch(bytecode, str,
                      AI.FInitState(bytecode, cp, AReg.init_regs(ncap), AReg.init_regs(nlook),
                                    AReg.init_regs(nquant), 0, AI.cp_context(cp, str, LAnc.Backward)),
                      ov, LAnc.Backward, lookcdn).0;
          assert rfLid == rf;                      // FreshBodyMatch(lid) dispatches to this backward run

          // ---- suffix bundle at S' = S - CaptureRegs(body); frame (direction-independent) ----
          var Sp := S - PIV.CaptureRegs(body);
          assert forall l: int :: next <= l <= maxlook && AReg.get_cp(lkN, l).Some? ==>
            exists la2: R.lookaround, body2: R.regex ::
              LTB.LookEntryOk(crv, l, la2, body2)
              && NR.LookFreeRE(body2) && NR.PlusFragmentRE(body2)
              && PIV.CapUnique(body2) && PIV.QuantUnique(body2)
              && PIV.CaptureRegs(body2) <= Sp
              && (forall q: nat :: q in PIV.QuantIds(body2) ==> q in PIV.QuantIdsInLooks(mainast))
              && ((la2.NegLookbehind? || la2.NegLookahead?) ==> NR.CaptureFreeRE(body2))
          by {
            forall l: int | next <= l <= maxlook && AReg.get_cp(lkN, l).Some?
              ensures exists la2: R.lookaround, body2: R.regex ::
                LTB.LookEntryOk(crv, l, la2, body2)
                && NR.LookFreeRE(body2) && NR.PlusFragmentRE(body2)
                && PIV.CapUnique(body2) && PIV.QuantUnique(body2)
                && PIV.CaptureRegs(body2) <= Sp
                && (forall q: nat :: q in PIV.QuantIds(body2) ==> q in PIV.QuantIdsInLooks(mainast))
                && ((la2.NegLookbehind? || la2.NegLookahead?) ==> NR.CaptureFreeRE(body2))
            {
              assert AReg.get_cp(lk, l).Some?;
              var la2: R.lookaround, body2: R.regex :|
                LTB.LookEntryOk(crv, l, la2, body2)
                && NR.LookFreeRE(body2) && NR.PlusFragmentRE(body2)
                && PIV.CapUnique(body2) && PIV.QuantUnique(body2)
                && PIV.CaptureRegs(body2) <= S
                && (forall q: nat :: q in PIV.QuantIds(body2) ==> q in PIV.QuantIdsInLooks(mainast))
                && ((la2.NegLookbehind? || la2.NegLookahead?) ==> NR.CaptureFreeRE(body2));
              assert body2 == VBody(crv, l) && body == VBody(crv, lid);
              assert PIV.CaptureRegs(VBody(crv, l)) * PIV.CaptureRegs(VBody(crv, lid)) == {};   // pairwise
              assert PIV.CaptureRegs(body2) * PIV.CaptureRegs(body) == {};
              assert PIV.CaptureRegs(body2) <= Sp by {
                forall k: int | k in PIV.CaptureRegs(body2) ensures k in Sp {
                  assert k in S;
                  assert k !in PIV.CaptureRegs(body) by {
                    if k in PIV.CaptureRegs(body) { assert k in PIV.CaptureRegs(body2) * PIV.CaptureRegs(body); }
                  }
                }
              }
            }
          }
          // ---- IH at [next] with capN (per-body-unset preserved by disjointness) ----
          assert forall l: int :: next <= l <= maxlook && AReg.get_cp(lk, l).Some? ==>
            CM.RegsAgreeInside(capN, AReg.init_regs(ncap), PIV.CaptureRegs(VBody(crv, l)))
          by {
            forall l: int | next <= l <= maxlook && AReg.get_cp(lk, l).Some?
              ensures CM.RegsAgreeInside(capN, AReg.init_regs(ncap), PIV.CaptureRegs(VBody(crv, l)))
            {
              assert body == VBody(crv, lid);
              assert PIV.CaptureRegs(VBody(crv, l)) * PIV.CaptureRegs(VBody(crv, lid)) == {};   // pairwise
              assert PIV.CaptureRegs(VBody(crv, l)) * PIV.CaptureRegs(body) == {};
              assert CM.RegsAgreeInside(cap, AReg.init_regs(ncap), PIV.CaptureRegs(VBody(crv, l)));   // per-body-unset
              forall k: int | k in PIV.CaptureRegs(VBody(crv, l))
                ensures AI.get_idx(capN.a_cp, k) == AI.get_idx(AReg.init_regs(ncap).a_cp, k)
                     && AI.get_idx(capN.a_clk, k) == AI.get_idx(AReg.init_regs(ncap).a_clk, k)
              {
                assert k !in PIV.CaptureRegs(body) by {
                  if k in PIV.CaptureRegs(body) { assert k in PIV.CaptureRegs(VBody(crv, l)) * PIV.CaptureRegs(body); }
                }
                assert AI.get_idx(capN.a_cp, k) == AI.get_idx(cap.a_cp, k);   // capN ~ cap off body
              }
            }
          }
          FLookLoopValueLift(crv, str, next, maxlook, capN, lkN, qtN, ov1, mainast, S, ncap, nlook, nquant);
          assert FLookLoopValueOk(crv, str, res.0, next, maxlook, lk, ov, ncap, nlook, nquant);
          assert |res.0.a_cp| == ncap && |res.0.a_clk| == ncap;   // from the IH ensures

          // ---- frame: res.0 == capN on CaptureRegs(body) (suffix writes disjoint regs) ----
          FLookLoopCaptureFrame(crv, str, next, maxlook, capN, lkN, qtN, ov1, mainast, Sp);
          assert CM.RegsAgreeOutside(res.0, capN, Sp);
          assert forall k: int :: k in PIV.CaptureRegs(body) ==> k !in Sp;
          RegsAgreeOutsideToInside(res.0, capN, PIV.CaptureRegs(body), Sp);
          assert CM.RegsAgreeInside(res.0, capN, PIV.CaptureRegs(body));

          // ---- assemble FLookLoopValueOk for [lid] (now a MATCHED positive lookbehind) ----
          forall l: int | lid <= l <= maxlook && MatchedPosLA(crv, lk, l)
            ensures var rf2 := FreshBodyMatch(crv, str, l, lk, ov, ncap, nlook, nquant);
                    (rf2.Some? ==> CM.RegsAgreeInside(res.0, rf2.value.capture_regs, PIV.CaptureRegs(VBody(crv, l))))
                    && (rf2.None? ==> CM.RegsAgreeInside(res.0, AReg.init_regs(ncap), PIV.CaptureRegs(VBody(crv, l))))
          {
            if l == lid {
              if rfLid.Some? {
                assert result.Some? && CM.RegsAgreeInside(result.value.capture_regs, rf.value.capture_regs, PIV.CaptureRegs(body));
                assert CM.RegsAgreeInside(res.0, rfLid.value.capture_regs, PIV.CaptureRegs(body));
              } else {
                assert result.None? && capN == cap;
                assert CM.RegsAgreeInside(cap, AReg.init_regs(ncap), PIV.CaptureRegs(body));   // per-body-unset(lid)
                assert CM.RegsAgreeInside(res.0, AReg.init_regs(ncap), PIV.CaptureRegs(body));
              }
            }
          }
        }
      }
  }

  /** L3a (E2): the value-lift conclusion for the QUANT bank — on each matched
      positive lookahead's own quant slots, `res.2` carries the fresh body
      match's clocks (the body-side quant clauses of `PIV.PathPresentLk` then
      transfer from `PIV.BodyPathPresentLk` by congruence). */
  ghost predicate FLookLoopQuantValueOk(crv: CP.FCompiled, str: string, res2: AReg.Regs, lid: int, maxlook: int,
                                        lk: AReg.Regs, ov: LOr.OracleView, ncap: int, nlook: int, nquant: int) {
    forall l: int :: lid <= l <= maxlook && MatchedPosLA(crv, lk, l) ==>
      var rf := FreshBodyMatch(crv, str, l, lk, ov, ncap, nlook, nquant);
      rf.Some? ==> CM.RegsAgreeInside(res2, rf.value.quant_regs, LKC.QIdsInt(VBody(crv, l)))
  }

  /** `l == lid` is not a matched positive lookahead, so the quant value map
      for `[lid, maxlook]` is exactly the one for `[lid+1, maxlook]`. */
  lemma QuantValueOkSkipLid(crv: CP.FCompiled, str: string, res2: AReg.Regs, lid: int, maxlook: int,
                            lk: AReg.Regs, ov: LOr.OracleView, ncap: int, nlook: int, nquant: int)
    requires FLookLoopQuantValueOk(crv, str, res2, lid + 1, maxlook, lk, ov, ncap, nlook, nquant)
    requires !MatchedPosLA(crv, lk, lid)
    ensures FLookLoopQuantValueOk(crv, str, res2, lid, maxlook, lk, ov, ncap, nlook, nquant)
  {
    forall l: int | lid <= l <= maxlook && MatchedPosLA(crv, lk, l)
      ensures var rf := FreshBodyMatch(crv, str, l, lk, ov, ncap, nlook, nquant);
              rf.Some? ==> CM.RegsAgreeInside(res2, rf.value.quant_regs, LKC.QIdsInt(VBody(crv, l)))
    { assert l != lid; }
  }

  /** L3a (E2): the QUANT-only replay bridge — the `FFindMatchPlus` replay's
      quant bank agrees with the FRESH body match's on `QIdsInt(body)`, with NO
      capture hypotheses (the bisimulation runs at `Sc == {}`: control never
      reads register values, so capture agreement is not needed to stay in
      lockstep). Entry: the body's quant slots are still INITIAL in the
      incoming bank. */
  lemma ReplayLidQuantAgreeFresh(bytecode: RB.code, str: string, cp: int, cap: AReg.Regs, lk: AReg.Regs,
                                 qt: AReg.Regs, ov: LOr.OracleView, lookcdn: LCdn.cdns, plus_bcv: seq<RB.code>,
                                 body: R.regex, la: R.lookaround, ncap: int, nlook: int, nquant: int)
    requires NR.LookBehindFragmentRE(body) && NR.LookFreeRE(body) && NR.PlusFragmentRE(body)
    requires PIV.CapUnique(body) && PIV.QuantUnique(body)
    requires la.Lookahead?
    requires bytecode == CP.compile_to_bytecode(body)
    requires 0 <= cp <= |str|
    requires AI.cp_context(cp, str, LAnc.Forward).nextchar == AI.get_char(str, cp)
    requires (forall k :: AI.get_idx(qt.a_cp, k) < 0)
          && (forall k :: AI.get_idx(qt.a_clk, k) >= -1)
    requires |qt.a_cp| == nquant && |qt.a_clk| == nquant
    requires |cap.a_cp| == ncap && |cap.a_clk| == ncap
    requires CM.RegsAgreeInside(qt, AReg.init_regs(nquant), LKC.QIdsInt(body))
    ensures
      var result := AI.FFindMatchPlus(bytecode, body, plus_bcv, str, ov, LAnc.Forward, cp, cap, lk, qt, 0, lookcdn).0;
      var rf := AI.FFindMatch(bytecode, str,
                  AI.FInitState(bytecode, cp, AReg.init_regs(ncap), AReg.init_regs(nlook),
                                AReg.init_regs(nquant), 0, AI.cp_context(cp, str, LAnc.Forward)),
                  ov, LAnc.Forward, lookcdn).0;
      (result.None? <==> rf.None?)
      && (result.Some? ==>
            CM.RegsAgreeInside(result.value.quant_regs, rf.value.quant_regs, LKC.QIdsInt(body)))
  {
    var dir := LAnc.Forward;
    var ctxc := AI.cp_context(cp, str, dir);
    var inits := AI.FInitState(bytecode, cp, cap, lk, qt, 0, ctxc);
    NoTrueQuantStamp(body);
    assert VmQuantFinal(inits) by { assert QuantRegsFinal(AI.init_thread(cap, lk, qt)); }
    FFindMatchQuantFinalAny(bytecode, str, inits, ov, dir, lookcdn);
    var (fmres, ovx) := AI.FFindMatch(bytecode, str, inits, ov, dir, lookcdn);
    if fmres.Some? {
      FNulledPlusIdentity(body, fmres.value.capture_regs, fmres.value.look_regs, fmres.value.quant_regs,
                          plus_bcv, str, ovx, dir);
    }
    var sf := AI.FInitState(bytecode, cp, AReg.init_regs(ncap), AReg.init_regs(nlook),
                            AReg.init_regs(nquant), 0, ctxc);
    assert CM.VmRel(inits, sf, {}, LKC.QIdsInt(body)) by {
      assert CM.ThreadRel(AI.init_thread(cap, lk, qt),
                          AI.init_thread(AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant)),
                          {}, LKC.QIdsInt(body)) by {
        assert CM.RegsAgreeInside(cap, AReg.init_regs(ncap), {});
        assert CM.RegsAgreeInside(qt, AReg.init_regs(nquant), LKC.QIdsInt(body));
      }
    }
    CM.FFindMatchCapRel(bytecode, str, inits, sf, ov, dir, lookcdn, {}, LKC.QIdsInt(body));
  }

  /** L3b: the per-lid BACKWARD replay↔fresh QUANT agreement — lookbehind twin of
      `ReplayLidQuantAgreeFresh`. Register-value-blind bisimulation at `Sc == {}`,
      `Sq == QIdsInt(body)`; `FFindMatchCapRel` is dir-generic, so it relates the two
      backward runs of `compile_to_bytecode(reverse_regex(body))` directly on the
      body's own quant slots (no reversed-set rewrite needed for the bisimulation). */
  lemma ReplayLidQuantAgreeFreshLB(bytecode: RB.code, str: string, cp: int, cap: AReg.Regs, lk: AReg.Regs,
                                   qt: AReg.Regs, ov: LOr.OracleView, lookcdn: LCdn.cdns, plus_bcv: seq<RB.code>,
                                   body: R.regex, ncap: int, nlook: int, nquant: int)
    requires NR.LookFreeRE(body) && NR.PlusFragmentRE(body)
    requires PIV.CapUnique(body) && PIV.QuantUnique(body)
    requires bytecode == CP.compile_to_bytecode(R.reverse_regex(body))
    requires 0 <= cp <= |str|
    requires AI.cp_context(cp, str, LAnc.Backward).nextchar == AI.get_char(str, cp - 1)
    requires (forall k :: AI.get_idx(qt.a_cp, k) < 0)
          && (forall k :: AI.get_idx(qt.a_clk, k) >= -1)
    requires |qt.a_cp| == nquant && |qt.a_clk| == nquant
    requires |cap.a_cp| == ncap && |cap.a_clk| == ncap
    requires CM.RegsAgreeInside(qt, AReg.init_regs(nquant), LKC.QIdsInt(body))
    ensures
      var result := AI.FFindMatchPlus(bytecode, body, plus_bcv, str, ov, LAnc.Backward, cp, cap, lk, qt, 0, lookcdn).0;
      var rf := AI.FFindMatch(bytecode, str,
                  AI.FInitState(bytecode, cp, AReg.init_regs(ncap), AReg.init_regs(nlook),
                                AReg.init_regs(nquant), 0, AI.cp_context(cp, str, LAnc.Backward)),
                  ov, LAnc.Backward, lookcdn).0;
      (result.None? <==> rf.None?)
      && (result.Some? ==>
            CM.RegsAgreeInside(result.value.quant_regs, rf.value.quant_regs, LKC.QIdsInt(body)))
  {
    var rev := R.reverse_regex(body);
    PIV.ReversePlusFragment(body);
    NR.PlusIsLookBehindFragmentRE(rev);
    PIV.ReverseCapUnique(body);
    PIV.ReverseQuantUnique(body);
    var dir := LAnc.Backward;
    var ctxc := AI.cp_context(cp, str, dir);
    var inits := AI.FInitState(bytecode, cp, cap, lk, qt, 0, ctxc);
    NoTrueQuantStamp(rev);
    assert VmQuantFinal(inits) by { assert QuantRegsFinal(AI.init_thread(cap, lk, qt)); }
    FFindMatchQuantFinalAny(bytecode, str, inits, ov, dir, lookcdn);
    var (fmres, ovx) := AI.FFindMatch(bytecode, str, inits, ov, dir, lookcdn);
    if fmres.Some? {
      FNulledPlusIdentity(body, fmres.value.capture_regs, fmres.value.look_regs, fmres.value.quant_regs,
                          plus_bcv, str, ovx, dir);
    }
    var sf := AI.FInitState(bytecode, cp, AReg.init_regs(ncap), AReg.init_regs(nlook),
                            AReg.init_regs(nquant), 0, ctxc);
    assert CM.VmRel(inits, sf, {}, LKC.QIdsInt(body)) by {
      assert CM.ThreadRel(AI.init_thread(cap, lk, qt),
                          AI.init_thread(AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant)),
                          {}, LKC.QIdsInt(body)) by {
        assert CM.RegsAgreeInside(cap, AReg.init_regs(ncap), {});
        assert CM.RegsAgreeInside(qt, AReg.init_regs(nquant), LKC.QIdsInt(body));
      }
    }
    CM.FFindMatchCapRel(bytecode, str, inits, sf, ov, dir, lookcdn, {}, LKC.QIdsInt(body));
  }

  /** L3b: the BACKWARD quant WRITE frame — the replay writes quant clocks only
      inside the body's own quant slots (`QIdsInt(reverse_regex(body)) == QIdsInt(body)`
      via `ReverseQuantIds`). Lookbehind analogue of the lookahead branch's inline
      `QuantWritesInsideBody` + `FFindMatchQuantFrame`. Capture-independent. */
  lemma ReplayQuantFrameLB(bytecode: RB.code, str: string, cp: int, cap: AReg.Regs, lk: AReg.Regs,
                           qt: AReg.Regs, ov: LOr.OracleView, lookcdn: LCdn.cdns, plus_bcv: seq<RB.code>,
                           body: R.regex)
    requires NR.LookFreeRE(body) && NR.PlusFragmentRE(body)
    requires PIV.CapUnique(body) && PIV.QuantUnique(body)
    requires bytecode == CP.compile_to_bytecode(R.reverse_regex(body))
    requires AI.cp_context(cp, str, LAnc.Backward).nextchar == AI.get_char(str, cp - 1)
    requires (forall k :: AI.get_idx(qt.a_cp, k) < 0)
          && (forall k :: AI.get_idx(qt.a_clk, k) >= -1)
    ensures var r := AI.FFindMatchPlus(bytecode, body, plus_bcv, str, ov, LAnc.Backward, cp, cap, lk, qt, 0, lookcdn).0;
      r.Some? ==> CM.RegsAgreeOutside(r.value.quant_regs, qt, LKC.QIdsInt(body))
  {
    var rev := R.reverse_regex(body);
    PIV.ReversePlusFragment(body);
    NR.PlusIsLookBehindFragmentRE(rev);
    PIV.ReverseCapUnique(body);
    PIV.ReverseQuantUnique(body);
    PIV.ReverseQuantIds(body);                     // QuantIds(rev) == QuantIds(body)
    assert LKC.QIdsInt(rev) == LKC.QIdsInt(body);
    var dir := LAnc.Backward;
    var inits := AI.FInitState(bytecode, cp, cap, lk, qt, 0, AI.cp_context(cp, str, dir));
    assert CM.VmQuantsAgree(inits, qt, LKC.QIdsInt(body)) by {
      assert inits.active == [AI.init_thread(cap, lk, qt)];
      assert AI.init_thread(cap, lk, qt).quant_regs == qt;
      assert CM.RegsAgreeOutside(qt, qt, LKC.QIdsInt(body));
    }
    QuantWritesInsideBody(rev);                    // QuantWritesInside(compile(rev), QIdsInt(rev)==QIdsInt(body))
    CM.FFindMatchQuantFrame(bytecode, str, inits, ov, dir, lookcdn, qt, LKC.QIdsInt(body));
    NoTrueQuantStamp(rev);
    assert VmQuantFinal(inits) by { assert QuantRegsFinal(AI.init_thread(cap, lk, qt)); }
    FFindMatchQuantFinalAny(bytecode, str, inits, ov, dir, lookcdn);
    var (res0, ovx) := AI.FFindMatch(bytecode, str, inits, ov, dir, lookcdn);
    if res0.Some? {
      FNulledPlusIdentity(body, res0.value.capture_regs, res0.value.look_regs, res0.value.quant_regs,
                          plus_bcv, str, ovx, dir);
    }
  }

  /** L3a (E2) THE QUANT VALUE LIFT: `FLookLoop`'s final quant bank carries, on
      each matched positive lookahead's own quant slots, that body's FRESH
      match clocks. Quant-only mirror of `FLookLoopValueLift` — the capture
      bank enters through its LENGTH alone (the `Sc == {}` bridge), so none of
      the capture-side bookkeeping is re-threaded. */
  lemma {:isolate_assertions} FLookLoopQuantValueLift(
                           crv: CP.FCompiled, str: string, lid: int, maxlook: int,
                           cap: AReg.Regs, lk: AReg.Regs, qt: AReg.Regs, ov: LOr.OracleView,
                           mainast: R.regex, Sq: set<int>, ncap: int, nlook: int, nquant: int)
    requires ncap >= 0 && nlook >= 0 && nquant >= 0
    requires NR.LookBehindFragmentRE(mainast) && PIV.QuantUnique(mainast)
    requires (forall k :: AI.get_idx(qt.a_cp, k) < 0)
          && (forall k :: AI.get_idx(qt.a_clk, k) >= -1)
    requires |qt.a_cp| == nquant && |qt.a_clk| == nquant
    requires |cap.a_cp| == ncap && |cap.a_clk| == ncap && PIV.CapRegWf(cap)
    requires |lk.a_cp| == nlook && |lk.a_clk| == nlook
    requires forall l: int :: lid <= l <= maxlook && AReg.get_cp(lk, l).Some? ==>
      exists la: R.lookaround, body: R.regex ::
        LTB.LookEntryOk(crv, l, la, body)
        && NR.LookFreeRE(body) && NR.PlusFragmentRE(body)
        && PIV.CapUnique(body) && PIV.QuantUnique(body)
        && LKC.QIdsInt(body) <= Sq
        && ((la.NegLookbehind? || la.NegLookahead?) ==> NR.CaptureFreeRE(body))
    // each matched body's own quant slots are INITIAL in the incoming bank
    requires forall l: int :: lid <= l <= maxlook && AReg.get_cp(lk, l).Some? ==>
      CM.RegsAgreeInside(qt, AReg.init_regs(nquant), LKC.QIdsInt(VBody(crv, l)))
    // distinct matched lids own DISJOINT quant ids
    requires forall l1: int, l2: int ::
      lid <= l1 <= maxlook && lid <= l2 <= maxlook && l1 != l2
      && AReg.get_cp(lk, l1).Some? && AReg.get_cp(lk, l2).Some? ==>
      LKC.QIdsInt(VBody(crv, l1)) * LKC.QIdsInt(VBody(crv, l2)) == {}
    requires forall l: int :: lid <= l <= maxlook && AReg.get_cp(lk, l).Some? ==> cp_ctx_ok(crv, str, lk, l)
    ensures var res := AI.FLookLoop(crv, str, lid, maxlook, cap, lk, qt, ov);
      |res.2.a_cp| == nquant && |res.2.a_clk| == nquant
      && (forall k :: AI.get_idx(res.2.a_cp, k) < 0)
      && (forall k :: AI.get_idx(res.2.a_clk, k) >= -1)
      && FLookLoopQuantValueOk(crv, str, res.2, lid, maxlook, lk, ov, ncap, nlook, nquant)
    decreases maxlook - lid
  {
    var res := AI.FLookLoop(crv, str, lid, maxlook, cap, lk, qt, ov);
    if lid > maxlook {
      assert res.2 == qt;
      return;
    }
    var next := lid + 1;
    match AReg.get_cp(lk, lid)
    case None =>
      assert res == AI.FLookLoop(crv, str, next, maxlook, cap, lk, qt, ov);
      FLookLoopQuantValueLift(crv, str, next, maxlook, cap, lk, qt, ov, mainast, Sq, ncap, nlook, nquant);
      assert !MatchedPosLA(crv, lk, lid);
      QuantValueOkSkipLid(crv, str, res.2, lid, maxlook, lk, ov, ncap, nlook, nquant);
    case Some(cp) =>
      var looktype := if 0 <= lid < |crv.f_look_types| then crv.f_look_types[lid] else R.Lookahead;
      if !AI.capture_type(looktype) {
        assert res == AI.FLookLoop(crv, str, next, maxlook, cap, lk, qt, ov);
        FLookLoopQuantValueLift(crv, str, next, maxlook, cap, lk, qt, ov, mainast, Sq, ncap, nlook, nquant);
        assert !MatchedPosLA(crv, lk, lid);
        QuantValueOkSkipLid(crv, str, res.2, lid, maxlook, lk, ov, ncap, nlook, nquant);
      } else {
        var la: R.lookaround, body: R.regex :|
          LTB.LookEntryOk(crv, lid, la, body)
          && NR.LookFreeRE(body) && NR.PlusFragmentRE(body)
          && PIV.CapUnique(body) && PIV.QuantUnique(body)
          && LKC.QIdsInt(body) <= Sq
          && ((la.NegLookbehind? || la.NegLookahead?) ==> NR.CaptureFreeRE(body));
        assert looktype == la;
        assert body == VBody(crv, lid);
        var bytecode := AI.get_code_v(crv.f_look_capture_bc, lid);
        var dir := AI.capture_direction(looktype);
        var lookcdn := if 0 <= lid < |crv.f_look_cdns| then crv.f_look_cdns[lid] else [];
        var lookast := if 0 <= lid < |crv.f_look_ast| then crv.f_look_ast[lid] else R.Re_empty;
        assert lookast == body;
        assert bytecode == CP.compile_to_bytecode(CP.capture_regex(la, body));
        var (result, ov1) := AI.FFindMatchPlus(bytecode, lookast, crv.f_plus_bc, str, ov, dir,
                                               cp, cap, lk, qt, 0, lookcdn);
        var capN := if result.None? then cap else result.value.capture_regs;
        var lkN := if result.None? then lk else result.value.look_regs;
        var qtN := if result.None? then qt else result.value.quant_regs;
        assert res == AI.FLookLoop(crv, str, next, maxlook, capN, lkN, qtN, ov1);
        NR.PlusIsLookBehindFragmentRE(body);
        assert cp_ctx_ok(crv, str, lk, lid);
        assert 0 <= cp <= |str| && AI.cp_context(cp, str, LAnc.Forward).nextchar == AI.get_char(str, cp);

        if la.Lookahead? {
          assert dir == LAnc.Forward && CP.capture_regex(la, body) == body;
          assert bytecode == CP.compile_to_bytecode(body);
          FFindMatchPlusOvStable(bytecode, str, ov, dir, lookcdn, crv.f_plus_bc, cp, cap, lk, qt, la, body);
          assert ov1 == ov;
          ReplayPlusFrame(bytecode, str, ov, dir, lookcdn, crv.f_plus_bc, cp, cap, lk, qt, la, body);
          assert lkN == lk;
          assert (forall k :: AI.get_idx(qtN.a_cp, k) < 0) && (forall k :: AI.get_idx(qtN.a_clk, k) >= -1);
          ReplayThreadWfLA(bytecode, str, cp, cap, lk, qt, ov, lookcdn, crv.f_plus_bc, body, la, ncap, nlook, nquant);
          assert |capN.a_cp| == ncap && |capN.a_clk| == ncap && PIV.CapRegWf(capN)
              && |qtN.a_cp| == nquant && |qtN.a_clk| == nquant by {
            if result.Some? { assert CM.ThreadRegsWf(result.value, ncap, nlook, nquant); }
          }

          // ---- the replay writes quants only inside the body's slots ----
          var inits := AI.FInitState(bytecode, cp, cap, lk, qt, 0, AI.cp_context(cp, str, dir));
          assert CM.VmQuantsAgree(inits, qt, LKC.QIdsInt(body)) by {
            assert inits.active == [AI.init_thread(cap, lk, qt)];
            assert AI.init_thread(cap, lk, qt).quant_regs == qt;
            assert CM.RegsAgreeOutside(qt, qt, LKC.QIdsInt(body));
          }
          QuantWritesInsideBody(body);
          CM.FFindMatchQuantFrame(bytecode, str, inits, ov, dir, lookcdn, qt, LKC.QIdsInt(body));
          NoTrueQuantStamp(body);
          assert VmQuantFinal(inits) by { assert QuantRegsFinal(AI.init_thread(cap, lk, qt)); }
          FFindMatchQuantFinalAny(bytecode, str, inits, ov, dir, lookcdn);
          var (res0, ovx) := AI.FFindMatch(bytecode, str, inits, ov, dir, lookcdn);
          if result.Some? {
            assert res0.Some? && QuantRegsFinal(res0.value);
            FNulledPlusIdentity(body, res0.value.capture_regs, res0.value.look_regs, res0.value.quant_regs,
                                crv.f_plus_bc, str, ovx, dir);
            assert qtN == res0.value.quant_regs;
          }
          assert CM.RegsAgreeOutside(qtN, qt, LKC.QIdsInt(body)) by {
            if result.None? { assert qtN == qt; }
          }

          // ---- value at lid: result ~ rfLid on QIdsInt(body) ----
          ReplayLidQuantAgreeFresh(bytecode, str, cp, cap, lk, qt, ov, lookcdn, crv.f_plus_bc, body, la, ncap, nlook, nquant);
          FreshMatchWf(bytecode, str, cp, ov, lookcdn, body, ncap, nlook, nquant);
          var rfLid := FreshBodyMatch(crv, str, lid, lk, ov, ncap, nlook, nquant);
          var rf := AI.FFindMatch(bytecode, str,
                      AI.FInitState(bytecode, cp, AReg.init_regs(ncap), AReg.init_regs(nlook),
                                    AReg.init_regs(nquant), 0, AI.cp_context(cp, str, LAnc.Forward)),
                      ov, LAnc.Forward, lookcdn).0;
          assert rfLid == rf;                    // VBody(lid)==body, cdn==lookcdn, cp matches

          // ---- suffix bundle at Sq' = Sq - QIdsInt(body) ----
          var Sqp := Sq - LKC.QIdsInt(body);
          assert forall l: int :: next <= l <= maxlook && AReg.get_cp(lkN, l).Some? ==>
            exists la2: R.lookaround, body2: R.regex ::
              LTB.LookEntryOk(crv, l, la2, body2)
              && NR.LookFreeRE(body2) && NR.PlusFragmentRE(body2)
              && PIV.CapUnique(body2) && PIV.QuantUnique(body2)
              && LKC.QIdsInt(body2) <= Sqp
              && ((la2.NegLookbehind? || la2.NegLookahead?) ==> NR.CaptureFreeRE(body2))
          by {
            forall l: int | next <= l <= maxlook && AReg.get_cp(lkN, l).Some?
              ensures exists la2: R.lookaround, body2: R.regex ::
                LTB.LookEntryOk(crv, l, la2, body2)
                && NR.LookFreeRE(body2) && NR.PlusFragmentRE(body2)
                && PIV.CapUnique(body2) && PIV.QuantUnique(body2)
                && LKC.QIdsInt(body2) <= Sqp
                && ((la2.NegLookbehind? || la2.NegLookahead?) ==> NR.CaptureFreeRE(body2))
            {
              assert AReg.get_cp(lk, l).Some?;
              var la2: R.lookaround, body2: R.regex :|
                LTB.LookEntryOk(crv, l, la2, body2)
                && NR.LookFreeRE(body2) && NR.PlusFragmentRE(body2)
                && PIV.CapUnique(body2) && PIV.QuantUnique(body2)
                && LKC.QIdsInt(body2) <= Sq
                && ((la2.NegLookbehind? || la2.NegLookahead?) ==> NR.CaptureFreeRE(body2));
              assert body2 == VBody(crv, l) && body == VBody(crv, lid);
              assert LKC.QIdsInt(VBody(crv, l)) * LKC.QIdsInt(VBody(crv, lid)) == {};   // pairwise
              assert LKC.QIdsInt(body2) * LKC.QIdsInt(body) == {};
              assert LKC.QIdsInt(body2) <= Sqp by {
                forall k: int | k in LKC.QIdsInt(body2) ensures k in Sqp {
                  assert k in Sq;
                  assert k !in LKC.QIdsInt(body) by {
                    if k in LKC.QIdsInt(body) { assert k in LKC.QIdsInt(body2) * LKC.QIdsInt(body); }
                  }
                }
              }
            }
          }
          // ---- IH entry: per-body quant slots still INITIAL in qtN ----
          assert forall l: int :: next <= l <= maxlook && AReg.get_cp(lk, l).Some? ==>
            CM.RegsAgreeInside(qtN, AReg.init_regs(nquant), LKC.QIdsInt(VBody(crv, l)))
          by {
            forall l: int | next <= l <= maxlook && AReg.get_cp(lk, l).Some?
              ensures CM.RegsAgreeInside(qtN, AReg.init_regs(nquant), LKC.QIdsInt(VBody(crv, l)))
            {
              assert LKC.QIdsInt(VBody(crv, l)) * LKC.QIdsInt(VBody(crv, lid)) == {};   // pairwise
              assert CM.RegsAgreeInside(qt, AReg.init_regs(nquant), LKC.QIdsInt(VBody(crv, l)));
              forall k: int | k in LKC.QIdsInt(VBody(crv, l))
                ensures AI.get_idx(qtN.a_cp, k) == AI.get_idx(AReg.init_regs(nquant).a_cp, k)
                     && AI.get_idx(qtN.a_clk, k) == AI.get_idx(AReg.init_regs(nquant).a_clk, k)
              {
                assert k !in LKC.QIdsInt(body) by {
                  if k in LKC.QIdsInt(body) { assert k in LKC.QIdsInt(VBody(crv, l)) * LKC.QIdsInt(body); }
                }
                assert AI.get_idx(qtN.a_cp, k) == AI.get_idx(qt.a_cp, k)
                    && AI.get_idx(qtN.a_clk, k) == AI.get_idx(qt.a_clk, k);   // qtN ~ qt off body
              }
            }
          }
          FLookLoopQuantValueLift(crv, str, next, maxlook, capN, lkN, qtN, ov1, mainast, Sqp, ncap, nlook, nquant);
          assert FLookLoopQuantValueOk(crv, str, res.2, next, maxlook, lk, ov, ncap, nlook, nquant);   // lkN==lk, ov1==ov

          // ---- frame: res.2 == qtN on QIdsInt(body) (suffix writes disjoint slots) ----
          FLookLoopQuantFrame(crv, str, next, maxlook, capN, lkN, qtN, ov1, mainast, Sqp);
          assert CM.RegsAgreeOutside(res.2, qtN, Sqp);
          assert forall k: int :: k in LKC.QIdsInt(body) ==> k !in Sqp;
          RegsAgreeOutsideToInside(res.2, qtN, LKC.QIdsInt(body), Sqp);
          assert CM.RegsAgreeInside(res.2, qtN, LKC.QIdsInt(body));

          // ---- assemble FLookLoopQuantValueOk for [lid] ----
          forall l: int | lid <= l <= maxlook && MatchedPosLA(crv, lk, l)
            ensures var rf2 := FreshBodyMatch(crv, str, l, lk, ov, ncap, nlook, nquant);
                    rf2.Some? ==> CM.RegsAgreeInside(res.2, rf2.value.quant_regs, LKC.QIdsInt(VBody(crv, l)))
          {
            if l == lid {
              if rfLid.Some? {
                assert result.Some?;
                assert CM.RegsAgreeInside(result.value.quant_regs, rf.value.quant_regs, LKC.QIdsInt(body));
                assert qtN == result.value.quant_regs;
                assert CM.ThreadRegsWf(rfLid.value, ncap, nlook, nquant);   // FreshMatchWf
                assert CM.RegsAgreeInside(res.2, rfLid.value.quant_regs, LKC.QIdsInt(VBody(crv, l))) by {
                  forall k: int | k in LKC.QIdsInt(body)
                    ensures AI.get_idx(res.2.a_cp, k) == AI.get_idx(rfLid.value.quant_regs.a_cp, k)
                         && AI.get_idx(res.2.a_clk, k) == AI.get_idx(rfLid.value.quant_regs.a_clk, k)
                  {
                    assert AI.get_idx(res.2.a_cp, k) == AI.get_idx(qtN.a_cp, k)
                        && AI.get_idx(res.2.a_clk, k) == AI.get_idx(qtN.a_clk, k);
                  }
                }
              }
            }
          }
        } else {
          // ---- capture-free positive LOOKBEHIND: quants still rewritten, but
          // MatchedPosLA(lid) is false (not a lookahead) — skip-lid after the
          // IH, whose entry facts survive by quant-set disjointness. ----
          assert la.Lookbehind?;
          assert dir == LAnc.Backward && CP.capture_regex(la, body) == R.reverse_regex(body);
          assert bytecode == CP.compile_to_bytecode(R.reverse_regex(body));
          assert AI.cp_context(cp, str, LAnc.Backward).nextchar == AI.get_char(str, cp - 1);
          FFindMatchPlusOvStableLB(bytecode, str, ov, dir, lookcdn, crv.f_plus_bc, cp, cap, lk, qt, la, body);
          assert ov1 == ov;
          ReplayPlusFrameLB(bytecode, str, ov, lookcdn, crv.f_plus_bc, cp, cap, lk, qt, body);
          assert lkN == lk;
          assert (forall k :: AI.get_idx(qtN.a_cp, k) < 0) && (forall k :: AI.get_idx(qtN.a_clk, k) >= -1);
          ReplayThreadWfLB(bytecode, str, cp, cap, lk, qt, ov, lookcdn, crv.f_plus_bc, body, ncap, nlook, nquant);
          assert |capN.a_cp| == ncap && |capN.a_clk| == ncap && PIV.CapRegWf(capN)
              && |qtN.a_cp| == nquant && |qtN.a_clk| == nquant by {
            if result.Some? { assert CM.ThreadRegsWf(result.value, ncap, nlook, nquant); }
          }

          // ---- the replay writes quants only inside the body's slots ----
          ReplayQuantFrameLB(bytecode, str, cp, cap, lk, qt, ov, lookcdn, crv.f_plus_bc, body);
          assert CM.RegsAgreeOutside(qtN, qt, LKC.QIdsInt(body)) by {
            if result.None? { assert qtN == qt; }
          }

          // ---- value at lid: result ~ rf on QIdsInt(body) (backward quant bisimulation) ----
          ReplayLidQuantAgreeFreshLB(bytecode, str, cp, cap, lk, qt, ov, lookcdn, crv.f_plus_bc, body, ncap, nlook, nquant);
          FreshMatchWfLB(bytecode, str, cp, ov, lookcdn, body, ncap, nlook, nquant);
          var rfLid := FreshBodyMatch(crv, str, lid, lk, ov, ncap, nlook, nquant);
          var rf := AI.FFindMatch(bytecode, str,
                      AI.FInitState(bytecode, cp, AReg.init_regs(ncap), AReg.init_regs(nlook),
                                    AReg.init_regs(nquant), 0, AI.cp_context(cp, str, LAnc.Backward)),
                      ov, LAnc.Backward, lookcdn).0;
          assert rfLid == rf;

          // ---- suffix bundle at Sq' + IH entry, as in the lookahead branch ----
          var Sqp := Sq - LKC.QIdsInt(body);
          assert forall l: int :: next <= l <= maxlook && AReg.get_cp(lkN, l).Some? ==>
            exists la2: R.lookaround, body2: R.regex ::
              LTB.LookEntryOk(crv, l, la2, body2)
              && NR.LookFreeRE(body2) && NR.PlusFragmentRE(body2)
              && PIV.CapUnique(body2) && PIV.QuantUnique(body2)
              && LKC.QIdsInt(body2) <= Sqp
              && ((la2.NegLookbehind? || la2.NegLookahead?) ==> NR.CaptureFreeRE(body2))
          by {
            forall l: int | next <= l <= maxlook && AReg.get_cp(lkN, l).Some?
              ensures exists la2: R.lookaround, body2: R.regex ::
                LTB.LookEntryOk(crv, l, la2, body2)
                && NR.LookFreeRE(body2) && NR.PlusFragmentRE(body2)
                && PIV.CapUnique(body2) && PIV.QuantUnique(body2)
                && LKC.QIdsInt(body2) <= Sqp
                && ((la2.NegLookbehind? || la2.NegLookahead?) ==> NR.CaptureFreeRE(body2))
            {
              assert AReg.get_cp(lk, l).Some?;
              var la2: R.lookaround, body2: R.regex :|
                LTB.LookEntryOk(crv, l, la2, body2)
                && NR.LookFreeRE(body2) && NR.PlusFragmentRE(body2)
                && PIV.CapUnique(body2) && PIV.QuantUnique(body2)
                && LKC.QIdsInt(body2) <= Sq
                && ((la2.NegLookbehind? || la2.NegLookahead?) ==> NR.CaptureFreeRE(body2));
              assert body2 == VBody(crv, l) && body == VBody(crv, lid);
              assert LKC.QIdsInt(VBody(crv, l)) * LKC.QIdsInt(VBody(crv, lid)) == {};   // pairwise
              assert LKC.QIdsInt(body2) * LKC.QIdsInt(body) == {};
              assert LKC.QIdsInt(body2) <= Sqp by {
                forall k: int | k in LKC.QIdsInt(body2) ensures k in Sqp {
                  assert k in Sq;
                  assert k !in LKC.QIdsInt(body) by {
                    if k in LKC.QIdsInt(body) { assert k in LKC.QIdsInt(body2) * LKC.QIdsInt(body); }
                  }
                }
              }
            }
          }
          assert forall l: int :: next <= l <= maxlook && AReg.get_cp(lk, l).Some? ==>
            CM.RegsAgreeInside(qtN, AReg.init_regs(nquant), LKC.QIdsInt(VBody(crv, l)))
          by {
            forall l: int | next <= l <= maxlook && AReg.get_cp(lk, l).Some?
              ensures CM.RegsAgreeInside(qtN, AReg.init_regs(nquant), LKC.QIdsInt(VBody(crv, l)))
            {
              assert LKC.QIdsInt(VBody(crv, l)) * LKC.QIdsInt(VBody(crv, lid)) == {};   // pairwise
              assert CM.RegsAgreeInside(qt, AReg.init_regs(nquant), LKC.QIdsInt(VBody(crv, l)));
              forall k: int | k in LKC.QIdsInt(VBody(crv, l))
                ensures AI.get_idx(qtN.a_cp, k) == AI.get_idx(AReg.init_regs(nquant).a_cp, k)
                     && AI.get_idx(qtN.a_clk, k) == AI.get_idx(AReg.init_regs(nquant).a_clk, k)
              {
                assert k !in LKC.QIdsInt(body) by {
                  if k in LKC.QIdsInt(body) { assert k in LKC.QIdsInt(VBody(crv, l)) * LKC.QIdsInt(body); }
                }
                assert AI.get_idx(qtN.a_cp, k) == AI.get_idx(qt.a_cp, k)
                    && AI.get_idx(qtN.a_clk, k) == AI.get_idx(qt.a_clk, k);   // qtN ~ qt off body
              }
            }
          }
          FLookLoopQuantValueLift(crv, str, next, maxlook, capN, lkN, qtN, ov1, mainast, Sqp, ncap, nlook, nquant);
          assert FLookLoopQuantValueOk(crv, str, res.2, next, maxlook, lk, ov, ncap, nlook, nquant);

          // ---- frame: res.2 == qtN on QIdsInt(body) (suffix writes disjoint slots) ----
          FLookLoopQuantFrame(crv, str, next, maxlook, capN, lkN, qtN, ov1, mainast, Sqp);
          assert CM.RegsAgreeOutside(res.2, qtN, Sqp);
          assert forall k: int :: k in LKC.QIdsInt(body) ==> k !in Sqp;
          RegsAgreeOutsideToInside(res.2, qtN, LKC.QIdsInt(body), Sqp);
          assert CM.RegsAgreeInside(res.2, qtN, LKC.QIdsInt(body));

          // ---- assemble FLookLoopQuantValueOk for [lid] (a MATCHED positive lookbehind) ----
          forall l: int | lid <= l <= maxlook && MatchedPosLA(crv, lk, l)
            ensures var rf2 := FreshBodyMatch(crv, str, l, lk, ov, ncap, nlook, nquant);
                    rf2.Some? ==> CM.RegsAgreeInside(res.2, rf2.value.quant_regs, LKC.QIdsInt(VBody(crv, l)))
          {
            if l == lid {
              if rfLid.Some? {
                assert result.Some?;
                assert CM.RegsAgreeInside(result.value.quant_regs, rf.value.quant_regs, LKC.QIdsInt(body));
                assert qtN == result.value.quant_regs;
                assert CM.ThreadRegsWf(rfLid.value, ncap, nlook, nquant);   // FreshMatchWfLB
                assert CM.RegsAgreeInside(res.2, rfLid.value.quant_regs, LKC.QIdsInt(VBody(crv, l))) by {
                  forall k: int | k in LKC.QIdsInt(body)
                    ensures AI.get_idx(res.2.a_cp, k) == AI.get_idx(rfLid.value.quant_regs.a_cp, k)
                         && AI.get_idx(res.2.a_clk, k) == AI.get_idx(rfLid.value.quant_regs.a_clk, k)
                  {
                    assert AI.get_idx(res.2.a_cp, k) == AI.get_idx(qtN.a_cp, k)
                        && AI.get_idx(res.2.a_clk, k) == AI.get_idx(qtN.a_clk, k);
                  }
                }
              }
            }
          }
        }
      }
  }

  /** L3a (E2): the quant-bank companion of `ReplayCapAgreeFresh` — the same
      lockstep bisimulation (`CM.FFindMatchCapRel` threads BOTH agreement sets),
      with `Sq := QIdsInt(body)`: when the body's quant slots are still INITIAL
      in the incoming bank (the main pass stamps only outside-look quants, and
      earlier lids' replays write only their own disjoint slots), the replay's
      final quant bank agrees with the FRESH replay's on the body's slots. This
      is what lets the reconstructed `res.2` discharge the body-side quant
      clauses of `PIV.PathPresentLk` via `PIV.BodyPathPresentLk` + congruence. */
  lemma ReplayCapQuantAgreeFresh(bodycode: RB.code, str: string, cp: int, cap: AReg.Regs, lk: AReg.Regs,
                                 qt: AReg.Regs, ov: LOr.OracleView, cdns: LCdn.cdns, body: R.regex,
                                 ncap: int, nlook: int, nquant: int)
    requires 0 <= cp <= |str|
    requires AI.cp_context(cp, str, LAnc.Forward).nextchar == AI.get_char(str, cp)
    requires CM.RegsAgreeInside(cap, AReg.init_regs(ncap), PIV.CaptureRegs(body))
    requires CM.RegsAgreeInside(qt, AReg.init_regs(nquant), LKC.QIdsInt(body))
    requires |qt.a_cp| == nquant && |qt.a_clk| == nquant
    ensures var ctxc := AI.cp_context(cp, str, LAnc.Forward);
            var ra := AI.FFindMatch(bodycode, str,
                        AI.FInitState(bodycode, cp, cap, lk, qt, 0, ctxc), ov, LAnc.Forward, cdns).0;
            var rf := AI.FFindMatch(bodycode, str,
                        AI.FInitState(bodycode, cp, AReg.init_regs(ncap), AReg.init_regs(nlook),
                                      AReg.init_regs(nquant), 0, ctxc), ov, LAnc.Forward, cdns).0;
            (ra.None? <==> rf.None?)
            && (ra.Some? ==>
                  CM.RegsAgreeInside(ra.value.capture_regs, rf.value.capture_regs, PIV.CaptureRegs(body))
                  && CM.RegsAgreeInside(ra.value.quant_regs, rf.value.quant_regs, LKC.QIdsInt(body)))
  {
    var ctxc := AI.cp_context(cp, str, LAnc.Forward);
    var sa := AI.FInitState(bodycode, cp, cap, lk, qt, 0, ctxc);
    var sf := AI.FInitState(bodycode, cp, AReg.init_regs(ncap), AReg.init_regs(nlook),
                            AReg.init_regs(nquant), 0, ctxc);
    var Sc := PIV.CaptureRegs(body);
    var Sq := LKC.QIdsInt(body);
    assert CM.VmRel(sa, sf, Sc, Sq) by {
      assert CM.ThreadRel(AI.init_thread(cap, lk, qt),
                          AI.init_thread(AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant)),
                          Sc, Sq);
    }
    CM.FFindMatchCapRel(bodycode, str, sa, sf, ov, LAnc.Forward, cdns, Sc, Sq);
  }

  /** L3a (E2): `ReplayLidCapAgreeFresh` with the quant conclusion — the ACTUAL
      `FFindMatchPlus` replay's quant bank agrees with the FRESH body match's on
      `QIdsInt(body)` (alongside the capture agreement). Same route: reconstruct
      is the identity on a `QuantRegsFinal` result, then the `Sq`-threaded
      bisimulation (`ReplayCapQuantAgreeFresh`). The extra entry fact — body
      quant slots still INITIAL in the incoming bank — is the caller's (main
      pass stamps only outside-look quants; earlier lids' replays write only
      their own disjoint slots). */
  lemma ReplayLidCapQuantAgreeFresh(bytecode: RB.code, str: string, cp: int, cap: AReg.Regs, lk: AReg.Regs,
                                    qt: AReg.Regs, ov: LOr.OracleView, lookcdn: LCdn.cdns, plus_bcv: seq<RB.code>,
                                    body: R.regex, la: R.lookaround, ncap: int, nlook: int, nquant: int)
    requires NR.LookBehindFragmentRE(body) && NR.LookFreeRE(body) && NR.PlusFragmentRE(body)
    requires PIV.CapUnique(body) && PIV.QuantUnique(body)
    requires la.Lookahead?
    requires bytecode == CP.compile_to_bytecode(body)
    requires 0 <= cp <= |str|
    requires AI.cp_context(cp, str, LAnc.Forward).nextchar == AI.get_char(str, cp)
    requires (forall k :: AI.get_idx(qt.a_cp, k) < 0)
          && (forall k :: AI.get_idx(qt.a_clk, k) >= -1)
    requires |qt.a_cp| == nquant && |qt.a_clk| == nquant
    requires CM.RegsAgreeInside(cap, AReg.init_regs(ncap), PIV.CaptureRegs(body))
    requires CM.RegsAgreeInside(qt, AReg.init_regs(nquant), LKC.QIdsInt(body))
    ensures
      var result := AI.FFindMatchPlus(bytecode, body, plus_bcv, str, ov, LAnc.Forward, cp, cap, lk, qt, 0, lookcdn).0;
      var rf := AI.FFindMatch(bytecode, str,
                  AI.FInitState(bytecode, cp, AReg.init_regs(ncap), AReg.init_regs(nlook),
                                AReg.init_regs(nquant), 0, AI.cp_context(cp, str, LAnc.Forward)),
                  ov, LAnc.Forward, lookcdn).0;
      (result.None? <==> rf.None?)
      && (result.Some? ==>
            CM.RegsAgreeInside(result.value.capture_regs, rf.value.capture_regs, PIV.CaptureRegs(body))
            && CM.RegsAgreeInside(result.value.quant_regs, rf.value.quant_regs, LKC.QIdsInt(body)))
  {
    var dir := LAnc.Forward;
    var inits := AI.FInitState(bytecode, cp, cap, lk, qt, 0, AI.cp_context(cp, str, dir));
    NoTrueQuantStamp(body);
    assert VmQuantFinal(inits) by { assert QuantRegsFinal(AI.init_thread(cap, lk, qt)); }
    FFindMatchQuantFinalAny(bytecode, str, inits, ov, dir, lookcdn);
    var (fmres, ovx) := AI.FFindMatch(bytecode, str, inits, ov, dir, lookcdn);
    if fmres.Some? {
      FNulledPlusIdentity(body, fmres.value.capture_regs, fmres.value.look_regs, fmres.value.quant_regs,
                          plus_bcv, str, ovx, dir);
    }
    ReplayCapQuantAgreeFresh(bytecode, str, cp, cap, lk, qt, ov, lookcdn, body, ncap, nlook, nquant);
  }

  /** §4b ENGINE BRIDGE: the body replay from the MAIN thread's `cap/lk/qt`
      agrees, on `CaptureRegs(body)`, with the replay from FRESH registers. `cap`
      has the body's ids UNSET (the main pass writes only outside-look captures,
      §4b groundwork), so `cap` agrees with fresh there; and the engine never
      branches on register values, so the two runs stay in lockstep
      (`CM.FFindMatchCapRel`). `Sq = {}`: control is quant-value-independent too,
      so no quant hypothesis is needed. Composed with `BodyTreeAtCp` on the fresh
      run, this pins the replay's body captures to the body's spec first leaf. */
  lemma ReplayCapAgreeFresh(bodycode: RB.code, str: string, cp: int, cap: AReg.Regs, lk: AReg.Regs,
                            qt: AReg.Regs, ov: LOr.OracleView, cdns: LCdn.cdns, body: R.regex,
                            ncap: int, nlook: int, nquant: int)
    requires 0 <= cp <= |str|
    requires AI.cp_context(cp, str, LAnc.Forward).nextchar == AI.get_char(str, cp)
    requires CM.RegsAgreeInside(cap, AReg.init_regs(ncap), PIV.CaptureRegs(body))
    requires |qt.a_cp| == nquant && |qt.a_clk| == nquant
    ensures var ctxc := AI.cp_context(cp, str, LAnc.Forward);
            var ra := AI.FFindMatch(bodycode, str,
                        AI.FInitState(bodycode, cp, cap, lk, qt, 0, ctxc), ov, LAnc.Forward, cdns).0;
            var rf := AI.FFindMatch(bodycode, str,
                        AI.FInitState(bodycode, cp, AReg.init_regs(ncap), AReg.init_regs(nlook),
                                      AReg.init_regs(nquant), 0, ctxc), ov, LAnc.Forward, cdns).0;
            (ra.None? <==> rf.None?)
            && (ra.Some? ==> CM.RegsAgreeInside(ra.value.capture_regs, rf.value.capture_regs, PIV.CaptureRegs(body)))
  {
    var ctxc := AI.cp_context(cp, str, LAnc.Forward);
    var sa := AI.FInitState(bodycode, cp, cap, lk, qt, 0, ctxc);
    var sf := AI.FInitState(bodycode, cp, AReg.init_regs(ncap), AReg.init_regs(nlook),
                            AReg.init_regs(nquant), 0, ctxc);
    var Sc := PIV.CaptureRegs(body);
    assert CM.VmRel(sa, sf, Sc, {}) by {
      assert CM.ThreadRel(AI.init_thread(cap, lk, qt),
                          AI.init_thread(AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant)),
                          Sc, {}) by {
        assert CM.RegsAgreeInside(qt, AReg.init_regs(nquant), {});  // just equal lengths (nquant)
      }
    }
    CM.FFindMatchCapRel(bodycode, str, sa, sf, ov, LAnc.Forward, cdns, Sc, {});
  }

  /** L3b: the BACKWARD register-value-blind bisimulation — the lookbehind twin of
      `ReplayCapAgreeFresh`. A backward `FFindMatch` from the main thread's `cap`
      (fresh on `CaptureRegs(body)`) and one from a fully-fresh state agree on
      `CaptureRegs(body)`. Direction is the ONLY difference: `CM.FFindMatchCapRel`
      is dir-generic and control never reads register values, so no fragment /
      uniqueness / capture-freeness hypotheses are needed. */
  lemma ReplayCapAgreeFreshLB(bodycode: RB.code, str: string, cp: int, cap: AReg.Regs, lk: AReg.Regs,
                              qt: AReg.Regs, ov: LOr.OracleView, cdns: LCdn.cdns, body: R.regex,
                              ncap: int, nlook: int, nquant: int)
    requires 0 <= cp <= |str|
    requires AI.cp_context(cp, str, LAnc.Backward).nextchar == AI.get_char(str, cp - 1)
    requires CM.RegsAgreeInside(cap, AReg.init_regs(ncap), PIV.CaptureRegs(body))
    requires |qt.a_cp| == nquant && |qt.a_clk| == nquant
    ensures var ctxc := AI.cp_context(cp, str, LAnc.Backward);
            var ra := AI.FFindMatch(bodycode, str,
                        AI.FInitState(bodycode, cp, cap, lk, qt, 0, ctxc), ov, LAnc.Backward, cdns).0;
            var rf := AI.FFindMatch(bodycode, str,
                        AI.FInitState(bodycode, cp, AReg.init_regs(ncap), AReg.init_regs(nlook),
                                      AReg.init_regs(nquant), 0, ctxc), ov, LAnc.Backward, cdns).0;
            (ra.None? <==> rf.None?)
            && (ra.Some? ==> CM.RegsAgreeInside(ra.value.capture_regs, rf.value.capture_regs, PIV.CaptureRegs(body)))
  {
    var ctxc := AI.cp_context(cp, str, LAnc.Backward);
    var sa := AI.FInitState(bodycode, cp, cap, lk, qt, 0, ctxc);
    var sf := AI.FInitState(bodycode, cp, AReg.init_regs(ncap), AReg.init_regs(nlook),
                            AReg.init_regs(nquant), 0, ctxc);
    var Sc := PIV.CaptureRegs(body);
    assert CM.VmRel(sa, sf, Sc, {}) by {
      assert CM.ThreadRel(AI.init_thread(cap, lk, qt),
                          AI.init_thread(AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant)),
                          Sc, {}) by {
        assert CM.RegsAgreeInside(qt, AReg.init_regs(nquant), {});
      }
    }
    CM.FFindMatchCapRel(bodycode, str, sa, sf, ov, LAnc.Backward, cdns, Sc, {});
  }

  /** §4b ENGINE VALUE BRIDGE (capstone): the body replay from the MAIN thread's
      `cap/lk/qt` produces, on `CaptureRegs(body)`, exactly the capture registers
      of the FRESH body match, whose group-map denotation `GmOfLive(body, .)` is
      the body's SPEC first leaf `FirstLeaf(ComputeTr(body, InpOfCp(str,cp)))`.
      Composes `BodyTreeAtCp` (fresh match <-> spec leaf) with `ReplayCapAgreeFresh`
      (replay-cap ~ fresh on body ids). This closes the ENGINE half of §4b; what
      remains is the SPEC-side bridge from this standalone body leaf to the main
      tree's lookaround subtree (gm-independence of own-group captures). */
  lemma ReplayCapIsBodyLeaf(rer: LW.RegExpRecord, qm: AR.QMap, body: R.regex, bodycode: RB.code,
                            endl: nat, ngroups: nat, str: string, cp: nat, cap: AReg.Regs, lk: AReg.Regs,
                            qt: AReg.Regs, ov: LOr.OracleView, cdns: LCdn.cdns, ncap: int, nlook: int, nquant: int)
    returns (bestT: Option<LT.Leaf>)
    requires PSM.StaticOkRE(qm, body, bodycode, endl)
    requires PSM.SizesOkRE(body, ncap, nlook, nquant)
    requires qm.ov == ov
    requires !rer.ignoreCase && !rer.multiline
    requires cp <= |str|
    requires bodycode == CP.compile_to_bytecode(body)
    requires NR.LookFreeRE(body)
    requires LL.OracleOkSuffix(rer, qm, PIV.InpOfCp(str, cp))
    requires CM.RegsAgreeInside(cap, AReg.init_regs(ncap), PIV.CaptureRegs(body))
    requires |qt.a_cp| == nquant && |qt.a_clk| == nquant
    ensures var inp := PIV.InpOfCp(str, cp);
            var t := LFU.ComputeTr(rer, [LS.Areg(T.Translate(body))], inp, LG.Empty, WP.Forward);
            var ctxc := AI.cp_context(cp, str, LAnc.Forward);
            var ra := AI.FFindMatch(bodycode, str,
                        AI.FInitState(bodycode, cp, cap, lk, qt, 0, ctxc), ov, LAnc.Forward, cdns).0;
            var rf := AI.FFindMatch(bodycode, str,
                        AI.FInitState(bodycode, cp, AReg.init_regs(ncap), AReg.init_regs(nlook),
                                      AReg.init_regs(nquant), 0, ctxc), ov, LAnc.Forward, cdns).0;
            bestT == LT.FirstLeaf(t, inp)
            && (ra.None? <==> bestT.None?)
            && (ra.Some? ==>
                  bestT.Some? && rf.Some?
                  && CM.RegsAgreeInside(ra.value.capture_regs, rf.value.capture_regs, PIV.CaptureRegs(body))
                  && bestT.value.1 == PIV.GmOfLive(body, rf.value.capture_regs, rf.value.look_regs, rf.value.quant_regs))
  {
    bestT := BodyTreeAtCp(rer, qm, body, bodycode, endl, ngroups, str, cp, ov, cdns, ncap, nlook, nquant);
    ReplayCapAgreeFresh(bodycode, str, cp, cap, lk, qt, ov, cdns, body, ncap, nlook, nquant);
    // BodyTreeAtCp:  BestMatchRE(body, bestT, rf) && bestT == FirstLeaf(t, inp)
    //   -> bestT.value.1 == GmOfLive(body, rf.regs), bestT.None? <==> rf.None?
    // ReplayCapAgreeFresh:  ra.None? <==> rf.None? && captures agree on CaptureRegs(body)
  }

  /** §4b ENGINE VALUE BRIDGE generalized off `LookFreeRE(body)` to the CAPTURING
      (depth-1) lookaround case — the `ReplayCapIsBodyLeaf` twin built on
      `BodyTreeAtCpLk`. The FRESH-match facts are UNCHANGED (`ReplayCapAgreeFresh`
      is register-value-blind — no fragment / look-free hypothesis — and
      `BestMatchRE` ties `bestT.1` to `GmOfLive(body, rf)` regardless of looks); the
      only weakening is the CHECKED-tree relation to the spec first leaf, which
      holds OUTSIDE `S := LkBodyGroups(Translate(body))` (the erased look captures)
      rather than everywhere. A clean composition — no new proof obligations beyond
      the two called lemmas. Downstream, closing the keystone `LkResult ~ GmOfLive`
      on the body's FULL `DefGroups` (not merely outside `S`) additionally needs
      the L3a look-capture RECONSTRUCTION (`FLookLoop`), which lies on the engine
      side, not in this composition. */
  lemma ReplayCapIsBodyLeafLk(rer: LW.RegExpRecord, qm: AR.QMap, body: R.regex, bodycode: RB.code,
                              endl: nat, ngroups: nat, str: string, cp: nat, cap: AReg.Regs, lk: AReg.Regs,
                              qt: AReg.Regs, ov: LOr.OracleView, cdns: LCdn.cdns, ncap: int, nlook: int, nquant: int)
    returns (bestT: Option<LT.Leaf>)
    requires PSM.StaticOkRE(qm, body, bodycode, endl)
    requires PSM.SizesOkRE(body, ncap, nlook, nquant)
    requires qm.ov == ov
    requires !rer.ignoreCase && !rer.multiline
    requires cp <= |str|
    requires bodycode == CP.compile_to_bytecode(body)
    requires LL.OracleOkSuffix(rer, qm, PIV.InpOfCp(str, cp))
    requires CM.RegsAgreeInside(cap, AReg.init_regs(ncap), PIV.CaptureRegs(body))
    requires |qt.a_cp| == nquant && |qt.a_clk| == nquant
    ensures var inp := PIV.InpOfCp(str, cp);
            var t := LFU.ComputeTr(rer, [LS.Areg(T.Translate(body))], inp, LG.Empty, WP.Forward);
            var S := LL.LkBodyGroups(T.Translate(body));
            var ctxc := AI.cp_context(cp, str, LAnc.Forward);
            var ra := AI.FFindMatch(bodycode, str,
                        AI.FInitState(bodycode, cp, cap, lk, qt, 0, ctxc), ov, LAnc.Forward, cdns).0;
            var rf := AI.FFindMatch(bodycode, str,
                        AI.FInitState(bodycode, cp, AReg.init_regs(ncap), AReg.init_regs(nlook),
                                      AReg.init_regs(nquant), 0, ctxc), ov, LAnc.Forward, cdns).0;
            // checked-tree first leaf, confined (replaces raw `bestT == FirstLeaf(t)`):
            (bestT.None? <==> LT.FirstLeaf(t, inp).None?)
            && (bestT.Some? ==>
                  LT.FirstLeaf(t, inp).Some?
                  && bestT.value.0 == LT.FirstLeaf(t, inp).value.0
                  && LL.GmAgreeOutside(bestT.value.1, LT.FirstLeaf(t, inp).value.1, S))
            // fresh-match facts (UNCHANGED from ReplayCapIsBodyLeaf):
            && (ra.None? <==> bestT.None?)
            && (ra.Some? ==>
                  bestT.Some? && rf.Some?
                  && CM.RegsAgreeInside(ra.value.capture_regs, rf.value.capture_regs, PIV.CaptureRegs(body))
                  && bestT.value.1 == PIV.GmOfLive(body, rf.value.capture_regs, rf.value.look_regs, rf.value.quant_regs))
  {
    bestT := BodyTreeAtCpLk(rer, qm, body, bodycode, endl, ngroups, str, cp, ov, cdns, ncap, nlook, nquant);
    ReplayCapAgreeFresh(bodycode, str, cp, cap, lk, qt, ov, cdns, body, ncap, nlook, nquant);
    // BodyTreeAtCpLk:  BestMatchRE(body, bestT, rf) (fresh) && confined FirstLeaf facts
    //   -> bestT.1 == GmOfLive(body, rf.regs), bestT.None? <==> rf.None?
    // ReplayCapAgreeFresh:  ra.None? <==> rf.None? && captures agree on CaptureRegs(body)
  }

  // ===========================================================================
  // §4b -- SPEC-side gm-frame. `TreeRes` threads `gm` through the tree; a
  // look-free tree (`NoLKTree`) never branches on `gm` (only `LK` nodes read it),
  // so two runs from gms agreeing on a group set `S` end at the same position and
  // agree on `S`. Since `FirstLeaf(t, inp) == TreeRes(t, Empty, inp, Forward)` and
  // `LkResult` of a positive lookAHEAD is `TreeRes(tlk, gm, inp, Forward).1`, this
  // bridges the standalone body leaf (at `Empty`) to the main tree's lookaround
  // subtree (at the main `gm`) on the body's own groups -- the SPEC analogue of
  // the engine bisimulation.
  // ===========================================================================

  /** Two group maps agree on membership and value at every group in `S`. */
  ghost predicate GmAgreeOn(gm1: LG.GroupMap, gm2: LG.GroupMap, S: set<LG.GroupId>) {
    forall g :: g in S ==> (g in gm1 <==> g in gm2) && (g in gm1 ==> gm1[g] == gm2[g])
  }

  /** Applying the SAME group action to two `S`-agreeing maps preserves
      `S`-agreement (the action reads/writes one group -- or a reset set --
      identically on both). */
  lemma GMUpdateAgree(op: LG.GroupAction, idx: nat, gm1: LG.GroupMap, gm2: LG.GroupMap, S: set<LG.GroupId>)
    requires GmAgreeOn(gm1, gm2, S)
    ensures GmAgreeOn(LG.GMUpdate(op, idx, gm1), LG.GMUpdate(op, idx, gm2), S)
  {
    match op
    case Open(g) =>
    case Close(g) =>
      // GMClose modifies only group `g`; for `g' in S`, either g' != g (entry
      // unchanged in both) or g' == g in S (so Find(g, .) agrees -> same close).
      forall g' | g' in S
        ensures (g' in LG.GMClose(idx, g, gm1) <==> g' in LG.GMClose(idx, g, gm2))
             && (g' in LG.GMClose(idx, g, gm1) ==> LG.GMClose(idx, g, gm1)[g'] == LG.GMClose(idx, g, gm2)[g'])
      {
        if g' == g {
          assert LG.Find(g, gm1) == LG.Find(g, gm2);   // g in S: maps agree at g
        }
      }
    case Reset(gs) =>
  }

  /** SPEC-side gm-frame: for a look-free tree, `TreeRes` from `S`-agreeing gms
      lands at the same position and its leaf gms still agree on `S`. */
  lemma TreeResGmFrame(t: LT.Tree, gm1: LG.GroupMap, gm2: LG.GroupMap, inp: LC.Input,
                       dir: WP.Direction, S: set<LG.GroupId>)
    requires EL.NoLKTree(t)
    requires GmAgreeOn(gm1, gm2, S)
    ensures (LT.TreeRes(t, gm1, inp, dir).None? <==> LT.TreeRes(t, gm2, inp, dir).None?)
    ensures LT.TreeRes(t, gm1, inp, dir).Some? ==>
              LT.TreeRes(t, gm1, inp, dir).value.0 == LT.TreeRes(t, gm2, inp, dir).value.0
              && GmAgreeOn(LT.TreeRes(t, gm1, inp, dir).value.1, LT.TreeRes(t, gm2, inp, dir).value.1, S)
    decreases t
  {
    match t
    case Mismatch =>
    case Match =>
    case Choice(t1, t2) =>
      TreeResGmFrame(t1, gm1, gm2, inp, dir, S);
      TreeResGmFrame(t2, gm1, gm2, inp, dir, S);
    case Read(c, t1) =>
      TreeResGmFrame(t1, gm1, gm2, LC.AdvanceInputP(inp, dir), dir, S);
    case ReadBackRef(brStr, t1) =>
      TreeResGmFrame(t1, gm1, gm2, LC.AdvanceInputN(inp, |brStr|, dir), dir, S);
    case Progress(t1) =>
      TreeResGmFrame(t1, gm1, gm2, inp, dir, S);
    case AnchorPass(a, t1) =>
      TreeResGmFrame(t1, gm1, gm2, inp, dir, S);
    case GroupActionT(a, t1) =>
      GMUpdateAgree(a, LC.Idx(inp), gm1, gm2, S);
      TreeResGmFrame(t1, LG.GMUpdate(a, LC.Idx(inp), gm1), LG.GMUpdate(a, LC.Idx(inp), gm2), inp, dir, S);
  }

  /** A `GmConfinedTree` has no `LK`/`LKFail` node (those cases are `false`), so
      it is a `NoLKTree` — the bridge that lets the ORIGINAL `TreeResGmFrame`
      apply to a confined look body inside the L4 gm-frame below. */
  lemma GmConfinedNoLK(t: LT.Tree, S: set<LG.GroupId>)
    requires CE.GmConfinedTree(t, S)
    ensures EL.NoLKTree(t)
    decreases t
  {
    match t
    case Choice(t1, t2) => GmConfinedNoLK(t1, S); GmConfinedNoLK(t2, S);
    case Read(_, t1) => GmConfinedNoLK(t1, S);
    case Progress(t1) => GmConfinedNoLK(t1, S);
    case GroupActionT(_, t1) => GmConfinedNoLK(t1, S);
    case AnchorPass(_, t1) => GmConfinedNoLK(t1, S);
    case ReadBackRef(_, t1) => GmConfinedNoLK(t1, S);
    case _ =>
  }

  /** L4 SPEC-side gm-frame, GENERALIZED to LK-node trees — the lemma the W4
      keystone needs where `TreeResGmFrame` currently forces `NoLKTree(t)`. Under
      `LkConfinedTree(t, S)` (every look body is confined to `S`, hence LK-free),
      `TreeRes` from `S`-agreeing gms lands at the same position with `S`-agreeing
      leaf gms. Each look body is discharged by the ORIGINAL `TreeResGmFrame`
      (it is `NoLKTree` by `GmConfinedNoLK`); only the CONTINUATIONS recurse — so
      the depth-1 gm-frame lifts through one layer of gates, exactly what one step
      of the keystone's depth induction consumes. */
  lemma TreeResGmFrameLk(t: LT.Tree, gm1: LG.GroupMap, gm2: LG.GroupMap, inp: LC.Input,
                         dir: WP.Direction, S: set<LG.GroupId>)
    requires CE.LkConfinedTree(t, S)
    requires GmAgreeOn(gm1, gm2, S)
    ensures (LT.TreeRes(t, gm1, inp, dir).None? <==> LT.TreeRes(t, gm2, inp, dir).None?)
    ensures LT.TreeRes(t, gm1, inp, dir).Some? ==>
              LT.TreeRes(t, gm1, inp, dir).value.0 == LT.TreeRes(t, gm2, inp, dir).value.0
              && GmAgreeOn(LT.TreeRes(t, gm1, inp, dir).value.1, LT.TreeRes(t, gm2, inp, dir).value.1, S)
    decreases t
  {
    match t
    case Mismatch =>
    case Match =>
    case Choice(t1, t2) =>
      TreeResGmFrameLk(t1, gm1, gm2, inp, dir, S);
      TreeResGmFrameLk(t2, gm1, gm2, inp, dir, S);
    case Read(c, t1) =>
      TreeResGmFrameLk(t1, gm1, gm2, LC.AdvanceInputP(inp, dir), dir, S);
    case ReadBackRef(brStr, t1) =>
      TreeResGmFrameLk(t1, gm1, gm2, LC.AdvanceInputN(inp, |brStr|, dir), dir, S);
    case Progress(t1) =>
      TreeResGmFrameLk(t1, gm1, gm2, inp, dir, S);
    case AnchorPass(a, t1) =>
      TreeResGmFrameLk(t1, gm1, gm2, inp, dir, S);
    case GroupActionT(a, t1) =>
      GMUpdateAgree(a, LC.Idx(inp), gm1, gm2, S);
      TreeResGmFrameLk(t1, LG.GMUpdate(a, LC.Idx(inp), gm1), LG.GMUpdate(a, LC.Idx(inp), gm2), inp, dir, S);
    case LK(lk, tlk, t1) =>
      // the confined body is LK-free -> the ORIGINAL frame discharges it
      GmConfinedNoLK(tlk, S);
      TreeResGmFrame(tlk, gm1, gm2, inp, L.LkDir(lk), S);
      if L.Positivity(lk) {
        match LT.TreeRes(tlk, gm1, inp, L.LkDir(lk))
        case None =>
        case Some(pair1) =>
          var pair2 := LT.TreeRes(tlk, gm2, inp, L.LkDir(lk)).value;
          TreeResGmFrameLk(t1, pair1.1, pair2.1, inp, dir, S);
      } else {
        match LT.TreeRes(tlk, gm1, inp, L.LkDir(lk))
        case None => TreeResGmFrameLk(t1, gm1, gm2, inp, dir, S);
        case Some(_) =>
      }
    case LKFail(lk, tlk) =>
  }

  /** L4 SPEC-side gm-frame, generalized to ARBITRARY lookaround NESTING depth —
      the depth-parametric strengthening of the W4 brick `TreeResGmFrameLk`.
      Unlike `TreeResGmFrameLk`, this needs NO confinement hypothesis at all
      (`LkConfinedTree` is dropped): `TreeRes`'s CONTROL FLOW — its `None?` verdict
      and end position — never branches on the group map. Backreference strings are
      baked into the `ReadBackRef` node (not recomputed from `gm`), and a look
      node's success is decided by running its body, whose own control flow is
      likewise gm-blind. So every LK/LKFail body is discharged by a RECURSIVE call
      (a strict subterm, hence any nesting depth) instead of the depth-1
      `TreeResGmFrame` + `GmConfinedNoLK`, and `S`-agreement threads through
      unconditionally. Strictly generalizes both `TreeResGmFrame` (drops
      `NoLKTree`) and `TreeResGmFrameLk` (drops `LkConfinedTree`). */
  lemma TreeResGmFrameRec(t: LT.Tree, gm1: LG.GroupMap, gm2: LG.GroupMap, inp: LC.Input,
                          dir: WP.Direction, S: set<LG.GroupId>)
    requires GmAgreeOn(gm1, gm2, S)
    ensures (LT.TreeRes(t, gm1, inp, dir).None? <==> LT.TreeRes(t, gm2, inp, dir).None?)
    ensures LT.TreeRes(t, gm1, inp, dir).Some? ==>
              LT.TreeRes(t, gm1, inp, dir).value.0 == LT.TreeRes(t, gm2, inp, dir).value.0
              && GmAgreeOn(LT.TreeRes(t, gm1, inp, dir).value.1, LT.TreeRes(t, gm2, inp, dir).value.1, S)
    decreases t
  {
    match t
    case Mismatch =>
    case Match =>
    case Choice(t1, t2) =>
      TreeResGmFrameRec(t1, gm1, gm2, inp, dir, S);
      TreeResGmFrameRec(t2, gm1, gm2, inp, dir, S);
    case Read(c, t1) =>
      TreeResGmFrameRec(t1, gm1, gm2, LC.AdvanceInputP(inp, dir), dir, S);
    case ReadBackRef(brStr, t1) =>
      TreeResGmFrameRec(t1, gm1, gm2, LC.AdvanceInputN(inp, |brStr|, dir), dir, S);
    case Progress(t1) =>
      TreeResGmFrameRec(t1, gm1, gm2, inp, dir, S);
    case AnchorPass(a, t1) =>
      TreeResGmFrameRec(t1, gm1, gm2, inp, dir, S);
    case GroupActionT(a, t1) =>
      GMUpdateAgree(a, LC.Idx(inp), gm1, gm2, S);
      TreeResGmFrameRec(t1, LG.GMUpdate(a, LC.Idx(inp), gm1), LG.GMUpdate(a, LC.Idx(inp), gm2), inp, dir, S);
    case LK(lk, tlk, t1) =>
      // the look body is discharged by RECURSION (any depth), not the depth-1 frame
      TreeResGmFrameRec(tlk, gm1, gm2, inp, L.LkDir(lk), S);
      if L.Positivity(lk) {
        match LT.TreeRes(tlk, gm1, inp, L.LkDir(lk))
        case None =>
        case Some(pair1) =>
          var pair2 := LT.TreeRes(tlk, gm2, inp, L.LkDir(lk)).value;
          TreeResGmFrameRec(t1, pair1.1, pair2.1, inp, dir, S);
      } else {
        match LT.TreeRes(tlk, gm1, inp, L.LkDir(lk))
        case None => TreeResGmFrameRec(t1, gm1, gm2, inp, dir, S);
        case Some(_) =>
      }
    case LKFail(lk, tlk) =>
  }

  /** L4 BOUNDARY (machine-checked): the depth-1 lookbehind fragment caps nesting
      depth at 1 — every lookaround leaf's body is look-free (`NestDepth == 0` by
      `LookFreePlusIsNestedRE`), so `1 + 0` is the deepest a node reaches. This
      pins down WHY the `NestedFragmentRE` swap alone cannot lift `BodyTreeAtCp` /
      `LkReplayMatchesSpec` to genuine nesting: those lemmas KEEP the required
      `PSM.StaticOkRE`, which DEFINITIONALLY contains `LookBehindFragmentRE(body)`
      (PikeSimRE.dfy), so any admissible `body` already satisfies `NestDepth <= 1`.
      Lifting to depth >= 2 needs `StaticOkRE` (and the compilation-rep stack it
      wraps: `NfaRepRE`, `PikeLkRegex`, the confinement predicates) generalized to
      the nested fragment first — the ENGINE half, disjoint from this SPEC brick. */
  lemma LookBehindFragmentDepth1(re: R.regex)
    requires NR.LookBehindFragmentRE(re)
    ensures NR.NestDepth(re) <= 1
    decreases re
  {
    match re
    case Re_alt(r1, r2) => LookBehindFragmentDepth1(r1); LookBehindFragmentDepth1(r2);
    case Re_con(r1, r2) => LookBehindFragmentDepth1(r1); LookBehindFragmentDepth1(r2);
    case Re_quant(_, _, _, r1) => LookBehindFragmentDepth1(r1);
    case Re_capture(_, r1) => LookBehindFragmentDepth1(r1);
    case Re_lookaround(lid, la, r1) => NR.LookFreePlusIsNestedRE(r1);   // NestDepth(r1) == 0
    case _ =>
  }

  /** §4b KEYSTONE: the per-lookaround value theorem. For a positive lookAHEAD
      with a look-free body, the engine replay from the main thread's `cap/lk/qt`
      MATCHES the spec `LkResult` on the body's own groups. Composes every §4b
      piece: `ReplayCapIsBodyLeaf` (engine: replay caps agree with the fresh body
      match on `CaptureRegs(body)`, whose `GmOfLive(body,.)` is the body's spec
      first leaf `FirstLeaf(ComputeTr(body,Empty))`), `TranslateNoLkBr` +
      `ComputeTrGmIndepLk` (the main-tree subtree `tlk` at the running gm equals
      the body tree at `Empty`), `ComputeTrNoLK` (`NoLKTree(tlk)`), and
      `TreeResGmFrame` (spec: `LkResult` at the running gm agrees with the leaf
      at `Empty` on the body's `DefGroups`). */
  lemma LkReplayMatchesSpec(
      rer: LW.RegExpRecord, qm: AR.QMap, body: R.regex, bodycode: RB.code, endl: nat, ngroups: nat,
      str: string, cp: nat, cap: AReg.Regs, lk: AReg.Regs, qt: AReg.Regs, ov: LOr.OracleView,
      cdns: LCdn.cdns, la: R.lookaround, tlk: LT.Tree, gmMain: LG.GroupMap,
      ncap: int, nlook: int, nquant: int)
    requires PSM.StaticOkRE(qm, body, bodycode, endl)
    requires PSM.SizesOkRE(body, ncap, nlook, nquant)
    requires qm.ov == ov
    requires !rer.ignoreCase && !rer.multiline
    requires cp <= |str|
    requires bodycode == CP.compile_to_bytecode(body)
    requires NR.LookFreeRE(body)
    requires LL.OracleOkSuffix(rer, qm, PIV.InpOfCp(str, cp))
    requires CM.RegsAgreeInside(cap, AReg.init_regs(ncap), PIV.CaptureRegs(body))
    requires |qt.a_cp| == nquant && |qt.a_clk| == nquant
    requires la.Lookahead?
    requires tlk == LFU.ComputeTr(rer, [LS.Areg(T.Translate(body))], PIV.InpOfCp(str, cp), gmMain, WP.Forward)
    requires GmAgreeOn(gmMain, LG.Empty, set g | g in L.DefGroups(T.Translate(body)))
    ensures var inp := PIV.InpOfCp(str, cp);
            var ctxc := AI.cp_context(cp, str, LAnc.Forward);
            var ra := AI.FFindMatch(bodycode, str,
                        AI.FInitState(bodycode, cp, cap, lk, qt, 0, ctxc), ov, LAnc.Forward, cdns).0;
            var rf := AI.FFindMatch(bodycode, str,
                        AI.FInitState(bodycode, cp, AReg.init_regs(ncap), AReg.init_regs(nlook),
                                      AReg.init_regs(nquant), 0, ctxc), ov, LAnc.Forward, cdns).0;
            var S := set g | g in L.DefGroups(T.Translate(body));
            (ra.None? <==> LS.LkResult(T.TrLookaround(la), tlk, gmMain, inp).None?)
            && (ra.Some? ==>
                  LS.LkResult(T.TrLookaround(la), tlk, gmMain, inp).Some?
                  && rf.Some?
                  && CM.RegsAgreeInside(ra.value.capture_regs, rf.value.capture_regs, PIV.CaptureRegs(body))
                  && GmAgreeOn(LS.LkResult(T.TrLookaround(la), tlk, gmMain, inp).value,
                               PIV.GmOfLive(body, rf.value.capture_regs, rf.value.look_regs, rf.value.quant_regs), S))
  {
    var inp := PIV.InpOfCp(str, cp);
    var S := set g | g in L.DefGroups(T.Translate(body));
    var tr := T.Translate(body);

    // engine: the replay from cap ~ fresh, both == the body's spec first leaf.
    var bestT := ReplayCapIsBodyLeaf(rer, qm, body, bodycode, endl, ngroups, str, cp, cap, lk, qt,
                                     ov, cdns, ncap, nlook, nquant);
    var tEmpty := LFU.ComputeTr(rer, [LS.Areg(tr)], inp, LG.Empty, WP.Forward);
    assert bestT == LT.FirstLeaf(tEmpty, inp);            // from ReplayCapIsBodyLeaf

    // tlk (at gmMain) == tEmpty (at Empty): group-map independence for look-free.
    EL.TranslateNoLkBr(body);                             // NoLkBrL(tr)
    EL.ComputeTrGmIndepLk(rer, tr, inp, gmMain, WP.Forward);
    assert tlk == tEmpty;
    EL.ComputeTrNoLK(rer, tr, inp, LG.Empty, WP.Forward);
    assert EL.NoLKTree(tlk);

    // spec: TreeRes at gmMain agrees with TreeRes at Empty on the body's groups.
    TreeResGmFrame(tlk, gmMain, LG.Empty, inp, WP.Forward, S);
    assert LT.FirstLeaf(tlk, inp) == LT.TreeRes(tlk, LG.Empty, inp, WP.Forward);   // definitional
    assert LT.FirstLeaf(tlk, inp) == bestT;

    // LkResult of a positive lookAHEAD == TreeRes(tlk, gmMain, inp, Forward) folded.
    assert L.Positivity(T.TrLookaround(la)) && L.LkDir(T.TrLookaround(la)) == WP.Forward;
  }

  /** L3a extension of `OE.LmOfInv`: threads `CapUnique(re)` to derive the two
      capture-side facts the L3a `FLookLoop` frame/value lift ask of each
      matched lookaround (`LookEntryOk` pins the shared body). */
  lemma LmOfInvL3a(re: R.regex, fc: CP.FCompiled, lid: int)
    returns (la: R.lookaround, body: R.regex)
    requires T.TransWf(re) && NR.LookBehindFragmentRE(re)
    requires LTB.LookUnique(re) && LTB.LookTablesOk(re, fc)
    requires PIV.QuantUnique(re) && PIV.CapUnique(re)
    requires lid in OE.LmOf(re)
    ensures T.TransWf(body)
    ensures OE.LmOf(re)[lid] == (T.TrLookaround(la), T.Translate(body))
    ensures LTB.LookEntryOk(fc, lid, la, body)
    ensures (la.Lookahead? || la.Lookbehind? || NR.CaptureFreeRE(body)) && NR.LookFreeRE(body) && NR.PlusFragmentRE(body)
    ensures lid >= 0 && (lid as nat) in LTB.LookIds(re)
    ensures PIV.QuantUnique(body)
    ensures forall q: nat :: q in PIV.QuantIds(body) ==> q in PIV.QuantIdsInLooks(re)
    ensures PIV.CapUnique(body)
    ensures PIV.CapIds(body) <= PIV.CapIdsInLooks(re)
    decreases re
  {
    OE.LmOfDom(re);
    // the L1 half of the body facts, from the shared inversion
    la, body := OE.LmOfInv(re, fc, lid);
    // the two capture facts, by a parallel recursion threading CapUnique(re)
    match re
    case Re_alt(r1, r2) =>
      OE.LmOfDom(r1); OE.LmOfDom(r2);
      if lid in OE.LmOf(r2) {
        var la2, body2 := LmOfInvL3a(r2, fc, lid);
        LookEntryBody(fc, lid, la, body, la2, body2);
      } else {
        assert lid in OE.LmOf(r1);
        var la2, body2 := LmOfInvL3a(r1, fc, lid);
        LookEntryBody(fc, lid, la, body, la2, body2);
      }
    case Re_con(r1, r2) =>
      OE.LmOfDom(r1); OE.LmOfDom(r2);
      if lid in OE.LmOf(r2) {
        var la2, body2 := LmOfInvL3a(r2, fc, lid);
        LookEntryBody(fc, lid, la, body, la2, body2);
      } else {
        assert lid in OE.LmOf(r1);
        var la2, body2 := LmOfInvL3a(r1, fc, lid);
        LookEntryBody(fc, lid, la, body, la2, body2);
      }
    case Re_quant(_, _, _, r1) =>
      var la2, body2 := LmOfInvL3a(r1, fc, lid);
      LookEntryBody(fc, lid, la, body, la2, body2);
    case Re_capture(_, r1) =>
      var la2, body2 := LmOfInvL3a(r1, fc, lid);
      LookEntryBody(fc, lid, la, body, la2, body2);
    case Re_lookaround(lid0, la0, r1) =>
      OE.LmOfDom(r1);
      OE.LookFreeLmOfEmpty(r1);
      assert lid == lid0;
      assert body == r1;                      // LookEntryOk pins body == r1
      // CapIdsInLooks(Re_lookaround(_,_,r1)) == CapIds(r1); CapUnique(re) == CapUnique(r1)
      assert PIV.CapIdsInLooks(re) == PIV.CapIds(r1);
      assert PIV.CapUnique(r1);
  }

  /** Two inversions of the SAME lid share a body: `LookEntryOk` forces both to
      equal `fc.f_look_ast[lid]`, so the sub-recursion's capture facts transfer
      to the shared body. */
  lemma LookEntryBody(fc: CP.FCompiled, lid: int, la: R.lookaround, body: R.regex,
                      la2: R.lookaround, body2: R.regex)
    requires LTB.LookEntryOk(fc, lid, la, body) && LTB.LookEntryOk(fc, lid, la2, body2)
    ensures body == body2
  {}

  /** DISTINCT lookaround ids own bodies with DISJOINT capture ids. A body's
      captures sit under exactly one alt/con branch (lookaround bodies are
      look-free, so looks never nest), and `CapUnique` makes sibling branches
      share no ids. The cross-lid half of the value lift's per-body-disjoint
      hypothesis (lifted to registers by `PIV.CaptureRegsDisjoint`). */
  lemma LmOfBodiesDisjoint(re: R.regex, fc: CP.FCompiled, l1: int, l2: int)
    returns (la1: R.lookaround, b1: R.regex, la2: R.lookaround, b2: R.regex)
    requires T.TransWf(re) && NR.LookBehindFragmentRE(re)
    requires LTB.LookUnique(re) && LTB.LookTablesOk(re, fc)
    requires PIV.QuantUnique(re) && PIV.CapUnique(re)
    requires l1 in OE.LmOf(re) && l2 in OE.LmOf(re) && l1 != l2
    ensures LTB.LookEntryOk(fc, l1, la1, b1) && LTB.LookEntryOk(fc, l2, la2, b2)
    ensures PIV.CapIds(b1) * PIV.CapIds(b2) == {}
    // L3a (E2): the quant twin — distinct lids own disjoint QUANT ids too
    // (same split: a body's quants sit under exactly one alt/con branch, and
    // `QuantUnique` makes sibling branches share none).
    ensures PIV.QuantIds(b1) * PIV.QuantIds(b2) == {}
    decreases re
  {
    OE.LmOfDom(re);
    match re
    case Re_alt(r1, r2) =>
      OE.LmOfDom(r1); OE.LmOfDom(r2);
      if l1 in OE.LmOf(r2) && l2 in OE.LmOf(r2) {
        la1, b1, la2, b2 := LmOfBodiesDisjoint(r2, fc, l1, l2);
      } else if l1 in OE.LmOf(r1) && l2 in OE.LmOf(r1) {
        la1, b1, la2, b2 := LmOfBodiesDisjoint(r1, fc, l1, l2);
      } else {
        AltConBodiesSplit(re, r1, r2, fc, l1, l2);
        if l1 in OE.LmOf(r1) {
          assert l2 in OE.LmOf(r2);
          la1, b1 := LmOfInvL3a(r1, fc, l1);
          la2, b2 := LmOfInvL3a(r2, fc, l2);
        } else {
          assert l1 in OE.LmOf(r2) && l2 in OE.LmOf(r1);
          la1, b1 := LmOfInvL3a(r2, fc, l1);
          la2, b2 := LmOfInvL3a(r1, fc, l2);
        }
        PIV.CapIdsSplit(r1); PIV.CapIdsSplit(r2);   // CapIdsInLooks(ri) <= CapIds(ri)
        PIV.QuantIdsSplit(r1); PIV.QuantIdsSplit(r2);   // QuantIdsInLooks(ri) <= QuantIds(ri)
      }
    case Re_con(r1, r2) =>
      OE.LmOfDom(r1); OE.LmOfDom(r2);
      if l1 in OE.LmOf(r2) && l2 in OE.LmOf(r2) {
        la1, b1, la2, b2 := LmOfBodiesDisjoint(r2, fc, l1, l2);
      } else if l1 in OE.LmOf(r1) && l2 in OE.LmOf(r1) {
        la1, b1, la2, b2 := LmOfBodiesDisjoint(r1, fc, l1, l2);
      } else {
        AltConBodiesSplit(re, r1, r2, fc, l1, l2);
        if l1 in OE.LmOf(r1) {
          assert l2 in OE.LmOf(r2);
          la1, b1 := LmOfInvL3a(r1, fc, l1);
          la2, b2 := LmOfInvL3a(r2, fc, l2);
        } else {
          assert l1 in OE.LmOf(r2) && l2 in OE.LmOf(r1);
          la1, b1 := LmOfInvL3a(r2, fc, l1);
          la2, b2 := LmOfInvL3a(r1, fc, l2);
        }
        PIV.CapIdsSplit(r1); PIV.CapIdsSplit(r2);
        PIV.QuantIdsSplit(r1); PIV.QuantIdsSplit(r2);
      }
    case Re_quant(_, _, _, r1) => la1, b1, la2, b2 := LmOfBodiesDisjoint(r1, fc, l1, l2);
    case Re_capture(_, r1) => la1, b1, la2, b2 := LmOfBodiesDisjoint(r1, fc, l1, l2);
    case Re_lookaround(lid0, la0, r1) =>
      OE.LmOfDom(r1);
      OE.LookFreeLmOfEmpty(r1);          // r1 look-free => LmOf(r1) == map[], so LmOf(re) == {lid0}
      assert l1 == lid0 && l2 == lid0;   // both in the singleton dom, contradicting l1 != l2
  }

  /** In an alt/con `re == C(r1, r2)`, `LmOf(re) == LmOf(r1) + LmOf(r2)` with
      DISJOINT domains (LookUnique), so each lid lands in exactly one branch. */
  lemma AltConBodiesSplit(re: R.regex, r1: R.regex, r2: R.regex, fc: CP.FCompiled, l1: int, l2: int)
    requires T.TransWf(re) && LTB.LookUnique(re)
    requires re.Re_alt? || re.Re_con?
    requires re.Re_alt? ==> re == R.Re_alt(r1, r2)
    requires re.Re_con? ==> re == R.Re_con(r1, r2)
    requires l1 in OE.LmOf(re) && l2 in OE.LmOf(re)
    ensures (l1 in OE.LmOf(r1)) <==> (l1 !in OE.LmOf(r2))
    ensures (l2 in OE.LmOf(r1)) <==> (l2 !in OE.LmOf(r2))
    ensures l1 in OE.LmOf(r1) || l1 in OE.LmOf(r2)
    ensures l2 in OE.LmOf(r1) || l2 in OE.LmOf(r2)
  {
    OE.LmOfDom(re); OE.LmOfDom(r1); OE.LmOfDom(r2);
    // LookUnique(C(r1,r2)) => LookIds(r1) * LookIds(r2) == {}
  }

  lemma LookRowsFromTablesL3a(ast: R.regex, re: R.regex, crv: CP.FCompiled, code: RB.code,
                              str: string, ov: LOr.OracleView, cdn: LCdn.cdns,
                              inits: AI.VmState, cap: AReg.Regs, look: AReg.Regs,
                              quant: AReg.Regs, nlook: int, endl: nat,
                              result: Option<AI.Thread>)
    requires T.TransWf(ast) && T.TransWf(re) && re == R.lazy_prefix(ast)
    requires NR.LookBehindFragmentRE(re) && LTB.LookUnique(re) && PIV.QuantUnique(re)
    requires PIV.CapUnique(re)
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
        (l as nat) in LTB.LookIds(re)
        && exists la: R.lookaround, body: R.regex ::
          LTB.LookEntryOk(crv, l, la, body)
          && NR.LookFreeRE(body) && NR.PlusFragmentRE(body)
          && PIV.CapUnique(body) && PIV.QuantUnique(body)
          && PIV.CaptureRegs(body) <= PIV.CaptureRegsSet(PIV.CapIdsInLooks(ast))
          && (forall q: nat :: q in PIV.QuantIds(body) ==> q in PIV.QuantIdsInLooks(ast))
          && ((la.NegLookbehind? || la.NegLookahead?) ==> NR.CaptureFreeRE(body))
    // (E4): every RECORDED look cp names one of re's lids (write confinement)
    ensures result.Some? ==>
      forall l: int :: AReg.get_cp(result.value.look_regs, l).Some? ==>
        l >= 0 && (l as nat) in LTB.LookIds(re)
    // distinct matched lids own DISJOINT capture registers
    ensures result.Some? ==>
      forall l1: int, l2: int ::
        1 <= l1 <= R.max_lookaround(ast) && 1 <= l2 <= R.max_lookaround(ast) && l1 != l2
        && AReg.get_cp(result.value.look_regs, l1).Some?
        && AReg.get_cp(result.value.look_regs, l2).Some? ==>
        PIV.CaptureRegs(VBody(crv, l1)) * PIV.CaptureRegs(VBody(crv, l2)) == {}
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
    assert PIV.CapUnique(ast);              // CapUnique(Re_con(pre, ast)) => CapUnique(ast)
    LTB.FFullCompilationLookOk(ast);
    OE.LmOfDom(ast);
    RL.AInitLaws(nlook);

    if result.Some? {
      forall l: int | 1 <= l <= R.max_lookaround(ast)
                      && AReg.get_cp(result.value.look_regs, l).Some?
        ensures (l as nat) in LTB.LookIds(re)
        ensures exists la: R.lookaround, body: R.regex ::
          LTB.LookEntryOk(crv, l, la, body)
          && NR.LookFreeRE(body) && NR.PlusFragmentRE(body)
          && PIV.CapUnique(body) && PIV.QuantUnique(body)
          && PIV.CaptureRegs(body) <= PIV.CaptureRegsSet(PIV.CapIdsInLooks(ast))
          && (forall q: nat :: q in PIV.QuantIds(body) ==> q in PIV.QuantIdsInLooks(ast))
          && ((la.NegLookbehind? || la.NegLookahead?) ==> NR.CaptureFreeRE(body))
      {
        assert l in S;
        assert (l as nat) in LTB.LookIds(ast);
        assert (l as nat) in LTB.LookIds(re);
        assert l in OE.LmOf(ast);
        var la, body := LmOfInvL3a(ast, crv, l);
        // CaptureRegs(body) <= CaptureRegsSet(CapIdsInLooks(ast))
        PIV.CaptureRegsIsSet(body);          // CaptureRegs(body) == CaptureRegsSet(CapIds(body))
        PIV.CaptureRegsSetMono(PIV.CapIds(body), PIV.CapIdsInLooks(ast));
      }
      forall l: int | AReg.get_cp(result.value.look_regs, l).Some?
        ensures l >= 0 && (l as nat) in LTB.LookIds(re)
      {
        assert l in S;
        assert (l as nat) in LTB.LookIds(re);
      }
      forall l1: int, l2: int |
        1 <= l1 <= R.max_lookaround(ast) && 1 <= l2 <= R.max_lookaround(ast) && l1 != l2
        && AReg.get_cp(result.value.look_regs, l1).Some?
        && AReg.get_cp(result.value.look_regs, l2).Some?
        ensures PIV.CaptureRegs(VBody(crv, l1)) * PIV.CaptureRegs(VBody(crv, l2)) == {}
      {
        assert l1 in S && l2 in S;
        assert (l1 as nat) in LTB.LookIds(ast) && (l2 as nat) in LTB.LookIds(ast);
        assert l1 in OE.LmOf(ast) && l2 in OE.LmOf(ast);
        var la1, b1, la2, b2 := LmOfBodiesDisjoint(ast, crv, l1, l2);
        assert b1 == VBody(crv, l1) && b2 == VBody(crv, l2);   // LookEntryOk pins bodies
        PIV.CaptureRegsDisjoint(b1, b2);
      }
    }
  }




  /** L3a `FBuildCapture` unfold: purely definitional — the answer IS
      `filter_reset` of the `FLookLoop` result triple. */
  lemma FBuildCaptureUnfoldL3a(crv: CP.FCompiled, str: string, ov: LOr.OracleView,
                               ncap: int, nlook: int, nquant: int,
                               capture: AReg.Regs, look: AReg.Regs, quant: AReg.Regs,
                               fmp: (Option<AI.Thread>, LOr.OracleView))
    requires ncap == 2 * R.max_group(crv.f_main_ast) + 2
    requires nlook == R.max_lookaround(crv.f_main_ast) + 1
    requires nquant == R.max_quant(crv.f_main_ast) + 1
    requires capture == AReg.init_regs(ncap)
    requires look == AReg.init_regs(nlook)
    requires quant == AReg.init_regs(nquant)
    requires fmp == AI.FFindMatchPlus(crv.f_main_bc, crv.f_main_ast, crv.f_plus_bc, str, ov,
                                      LAnc.Forward, 0, capture, look, quant, 0, crv.f_main_cdns)
    ensures fmp.0.None? ==> AI.FBuildCapture(crv, str, ov).0 == None
    ensures fmp.0.Some? ==>
      var thread := fmp.0.value;
      var res := AI.FLookLoop(crv, str, 1, R.max_lookaround(crv.f_main_ast),
                              thread.capture_regs, thread.look_regs, thread.quant_regs, fmp.1);
      AI.FBuildCapture(crv, str, ov).0
        == Some(AI.filter_reset(crv.f_main_ast, res.0, res.1, res.2, -1))
  {
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
    // L3b: for a CAPTURING lookbehind the engine registers hold the REVERSED span,
    // so the ordered spec leaf is the POSITIONAL normalization (`NormGm`) of the
    // reconstructed `GmOfLive`. NO-OP for forward matches (`NormGm` is identity on
    // ordered ranges), so this subsumes the old `leaf.1 == GmOfLive`.
    requires var re := R.lazy_prefix(R.annotate(raw));
      leaf.1 == PIV.NormGm(PIV.GmOfLive(re, thread.capture_regs, thread.look_regs, thread.quant_regs))
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
    assert LkClosedInGm(LG.Empty, [LS.Areg(T.Translate(re))]);   // Empty has no groups
    SpecRegexOuterLkDisjoint(raw);   // also ensures NoDupSeq(L.DefGroups(SpecRegex(raw)))
    assert T.Translate(re) == LES.SpecRegex(raw);
    assert OuterLkDisjoint([LS.Areg(T.Translate(re))]);
    assert NoDupRegsActs([LS.Areg(T.Translate(re))]) by { assert NoDupSeq(L.DefGroups(T.Translate(re))); }
    assert TRM.GmInBounds(LG.Empty, |inp.pref| + |inp.next|);   // Empty has no ranges
    FirstLeafClosed(rer, [LS.Areg(T.Translate(re))], inp, BS.CannotExit, t, LG.Empty, leaf);
    assert ClosedGm(leaf.1);

    // live == plain denotation on the closed leaf
    var f := AI.filter_reset(re, caps, lk, qt, -1);
    var cc := caps.a_clk;
    PIV.FilterCaptureLen(re, caps.a_cp, cc, lk.a_clk, qt.a_clk, -1);
    assert |f| == |caps.a_cp| == ncap == 2 * ngroups;
    // closedness (item 0): `leaf.1 == NormGm(GmOfLive)` and `NormRange` preserves
    // endIdx.Some?, so every present group of GmOfLive is closed. Needed by BOTH
    // the clock-order forall below AND the closed-match forall. (NO `GmOfLiveEqGmOf`
    // here — that needs the clock order the forall below produces.)
    assert leaf.1 == PIV.NormGm(PIV.GmOfLive(re, caps, lk, qt));            // requires
    assert forall g: LG.GroupId :: g in PIV.GmOfLive(re, caps, lk, qt)
        ==> PIV.GmOfLive(re, caps, lk, qt)[g].endIdx.Some? by {
      forall g: LG.GroupId | g in PIV.GmOfLive(re, caps, lk, qt)
        ensures PIV.GmOfLive(re, caps, lk, qt)[g].endIdx.Some?
      {
        assert g in leaf.1;                               // NormGm preserves keys
        assert leaf.1[g] == PIV.NormRange(PIV.GmOfLive(re, caps, lk, qt)[g]);  // NormGm def at g
        assert leaf.1[g].endIdx.Some?;                    // ClosedGm(leaf.1)
        PIV.NormRangeClosed(PIV.GmOfLive(re, caps, lk, qt)[g]);   // closedness transfers
      }
    }
    forall g: nat | 0 <= g < |f| && AI.get_idx(f, CP.start_reg(g)) >= 0 && AI.get_idx(f, CP.end_reg(g)) >= 0
      ensures AI.get_idx(cc, CP.end_reg(g)) >= AI.get_idx(cc, CP.start_reg(g))
    {
      assert g in PIV.GmOfLive(re, caps, lk, qt);
      assert PIV.GmOfLive(re, caps, lk, qt)[g].endIdx.Some?;
    }
    PIV.GmOfLiveEqGmOf(re, caps, lk, qt);                 // GmOfLive == GmOf (needs the clock order above)
    assert PIV.NormGm(PIV.GmOf(re, caps, lk, qt)) == leaf.1;   // leaf.1 == NormGm(GmOfLive) == NormGm(GmOf)

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
    // item 0 (capturing lookbehind): `f` MAY contain reversed pairs (backward
    // spans). `NormalizeArr` swaps them POSITIONALLY, which is exactly `NormGm` on
    // the `GmOf` read (`GmOfCapArrayBridgeNorm` — no no-reversed-pairs hypothesis),
    // and `leaf.1 == NormGm(GmOfLive) == NormGm(GmOf)`.
    PIV.GmOfCapArrayBridgeNorm(re, caps, lk, qt, inp, ngroups);
    assert LES.NormalizeArr(f)
        == LES.CapArrayOfLeaf((inp, PIV.NormGm(PIV.GmOf(re, caps, lk, qt))), ngroups);
    assert LES.CapArrayOfLeaf((inp, PIV.NormGm(PIV.GmOf(re, caps, lk, qt))), ngroups)
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
