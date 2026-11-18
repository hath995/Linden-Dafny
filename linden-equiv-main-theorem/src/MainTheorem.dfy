// The PINNACLE assembly: MatcherSpec(raw, str, Normalize(FFullMatch(raw, str)))
// for StarFragmentRaw && Latin1Wf. Builds on FindMatchSimRE (the complete
// simulation) plus Linden's own PikeTree correctness tail; the remaining
// bricks are pipeline plumbing and the leaf-closedness extraction.

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
  import NUL = LindenElkNullable
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
  import LB = LindenElkLookBank       // (gate C, G2) the look-bank invariant: set records sit at positive rows
  import NI = LindenElkNestInv
  import LES = LindenElkSpec
  import LFU = FunctionalUtils
  import PS = PikeSubset
  import ATR = LindenElkActionsTreeRep
  import NP = LindenElkNulledPlus
  import NB = LindenElkNulledPlusBool
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
  import SS = StrictSuffix
  // (G3a) the reconstruction at a lookahead row
  import FV = LindenElkFinalVm
  import FRD = LindenElkFinalReadout
  import RF = LindenElkReconFrame
  import NRC = LindenElkNulledRecon
  import NRR = LindenElkNulledReconRegs
  import RRA = LindenElkRowReconAt
  import ELk = LindenElkEmptyLooks   // (G4b-1b) the empty-path look set
  import RA = LindenElkReconAgree
  import QCI = LindenElkQuantCpIrrel
  import LLAF = LindenElkLookLoopAgreeFrom
  import FRA = LindenElkFinalReadoutAt
  import BR = LindenElkBackRowAt          // (G3b) backward row register lemmas
  import OBu = LindenElkOracleBuild       // (G5b-2) ReverseCdnFragmentRE
  import SBk = LindenElkStampBank         // (G5b-3) the bank through a row's reconstruction
  import DB = LindenElkDirBlind           // (G3b) FReconstructPlus is direction-blind

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
  /** (G3a) The clock half of `QuantRegsFinal`: what the final extraction reads off the winner
      (`MainExtractionFromClosed` uses only `get_idx(qt.a_clk, 0) >= -1`). A reconstructing look row
      stamps quant POSITIONS, so the post-loop thread is clock-final only. */
  ghost predicate QuantClkFinal(t: AI.Thread) {
    forall k :: AI.get_idx(t.quant_regs.a_clk, k) >= -1
  }

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
  lemma LkBodyGroupsActsCons(x: LS.Action, cont: LS.Actions)
    ensures LkBodyGroupsActs([x] + cont) == (if x.Areg? then LL.LkBodyGroups(x.r) else {}) + LkBodyGroupsActs(cont)
  { assert ([x] + cont)[0] == x && ([x] + cont)[1..] == cont; }

  /** `NoDupSeq` is preserved on any suffix / removing a prefix. */
  lemma NoDupTailSeq(a: seq<LG.GroupId>, b: seq<LG.GroupId>)
    requires NoDupSeq(a + b)
    ensures NoDupSeq(b)
  { forall i, j | 0 <= i < j < |b| ensures b[i] != b[j] { assert (a + b)[|a| + i] == b[i] && (a + b)[|a| + j] == b[j]; } }

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
  ghost predicate NoDupRegsActs(acts: LS.Actions) {
    forall i :: 0 <= i < |acts| ==> (acts[i].Areg? ==> NoDupSeq(L.DefGroups(acts[i].r)))
  }

  /** `FirstLeafClosed` restricted to LOOK-FREE actions: the LK case is
      unreachable, so this is a self-contained least lemma with no inside-look
      bookkeeping. `LookBodyLeafOpenSub` uses it on the (look-free) look body,
      which is why the main `FirstLeafClosed` LK case can reuse the balance
      without a least-lemma cycle. */
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

  // ==========================================================================
  // B'' deliverable #1: the R<->L "innermost owner body" correspondence. The
  // B'' descent (`ComputeTrOwnerNamed`) records `rr` as the L-look-body of
  // `Translate(body)` that DIRECTLY captures `g`. This block identifies that
  // `rr` with `Translate(LookBodyOfRE(body, InnermostOwnerDirect(body, g)))`.
  // ==========================================================================

  /** `w` is the body of SOME `LookaroundR` node inside `r` — the L-side "is a
      look body of" relation. The B'' descent records its `rr` as such a body of
      `Translate(body)`; this pins it structurally so it can be identified with
      a `Translate(LookBodyOfRE(...))`. */
  lemma TransWfLookBodyOfRE(r: R.regex, lid: nat)
    requires T.TransWf(r) && lid in LTB.LookIds(r)
    ensures T.TransWf(NI.LookBodyOfRE(r, lid))
    decreases r
  {
    match r
    case Re_alt(r1, r2) => if lid in LTB.LookIds(r1) { TransWfLookBodyOfRE(r1, lid); } else { TransWfLookBodyOfRE(r2, lid); }
    case Re_con(r1, r2) => if lid in LTB.LookIds(r1) { TransWfLookBodyOfRE(r1, lid); } else { TransWfLookBodyOfRE(r2, lid); }
    case Re_quant(_, _, _, r1) => TransWfLookBodyOfRE(r1, lid);
    case Re_capture(_, r1) => TransWfLookBodyOfRE(r1, lid);
    case Re_lookaround(lid0, _, r1) => if lid0 >= 0 && (lid0 as nat) == lid { } else { TransWfLookBodyOfRE(r1, lid); }
    case _ =>
  }

  /** `LookBodyOfRE` preserves `CapUnique` (its result is a subterm of `r`). */
  lemma CapUniqueLookBodyOfRE(r: R.regex, lid: nat)
    requires PIV.CapUnique(r) && lid in LTB.LookIds(r)
    ensures PIV.CapUnique(NI.LookBodyOfRE(r, lid))
    decreases r
  {
    match r
    case Re_alt(r1, r2) => if lid in LTB.LookIds(r1) { CapUniqueLookBodyOfRE(r1, lid); } else { CapUniqueLookBodyOfRE(r2, lid); }
    case Re_con(r1, r2) => if lid in LTB.LookIds(r1) { CapUniqueLookBodyOfRE(r1, lid); } else { CapUniqueLookBodyOfRE(r2, lid); }
    case Re_quant(_, _, _, r1) => CapUniqueLookBodyOfRE(r1, lid);
    case Re_capture(_, r1) => CapUniqueLookBodyOfRE(r1, lid);
    case Re_lookaround(lid0, _, r1) => if lid0 >= 0 && (lid0 as nat) == lid { } else { CapUniqueLookBodyOfRE(r1, lid); }
    case _ =>
  }

  /** Translate structural bridge: every L-look-body of `Translate(body)` is the
      translation of an R-look-body of `body`. `Translate` maps `Re_lookaround`
      to `LookaroundR` and nothing else creates a `LookaroundR`, so the L-look
      nodes of `Translate(body)` correspond exactly to the lookaround nodes of
      `body`. The `TransWf` conjunct keeps the `Translate` in the witness
      well-formed. */
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

  // ==========================================================================
  // (L4 FINAL EXTRACTION) FIRST-LEAF CLOSEDNESS for the RECURSIVE (depth-k)
  // fragment. The depth-1 `FirstLeafClosed` is `PikeLkActions`-gated: its
  // positive-look case needs a LOOK-FREE body (`LookBodyLeafOpenSub` bottoms out
  // on `FirstLeafClosedNoLk`). The nested twin stratifies on LOOK-NESTING DEPTH:
  // the ∀-hypothesis `ClosedBelow(rer, D)` (closedness for every instance whose
  // pending regexes nest strictly below `D`) discharges the look-BODY leaf at a
  // gate (its depth drops by one), and the walk recursion stays a `least lemma`
  // over `BoolTreeLk` exactly as at depth 1. `ClosedBelowAll` closes the ladder.
  // Positive looks are FORWARD-only (`FwdPosLooksL` — the L4 `NoPosLookbehind`
  // scope); negative bodies are group-free as before.
  // ==========================================================================

  /** L-side look-nesting depth. */
  ghost function NestDepthL(r: L.Regex): nat
    decreases r
  {
    match r
    case Disjunction(r1, r2) => if NestDepthL(r1) >= NestDepthL(r2) then NestDepthL(r1) else NestDepthL(r2)
    case Sequence(r1, r2) => if NestDepthL(r1) >= NestDepthL(r2) then NestDepthL(r1) else NestDepthL(r2)
    case Quantified(_, _, _, r1) => NestDepthL(r1)
    case Group(_, r1) => NestDepthL(r1)
    case LookaroundR(_, r1) => NestDepthL(r1) + 1
    case _ => 0
  }

  /** Every pending regex nests at most `D` deep. */
  ghost predicate NestDepthActsLe(acts: LS.Actions, D: nat) {
    forall i :: 0 <= i < |acts| ==> (acts[i].Areg? ==> NestDepthL(acts[i].r) <= D)
  }

  /** Positive looks are FORWARD (the L4 `NoPosLookbehind` scope, L-side). */
  ghost predicate FwdPosLooksL(r: L.Regex)
    decreases r
  {
    match r
    case Disjunction(r1, r2) => FwdPosLooksL(r1) && FwdPosLooksL(r2)
    case Sequence(r1, r2) => FwdPosLooksL(r1) && FwdPosLooksL(r2)
    case Quantified(_, _, _, r1) => FwdPosLooksL(r1)
    case Group(_, r1) => FwdPosLooksL(r1)
    case LookaroundR(lk, r1) => (L.Positivity(lk) ==> L.LkDir(lk) == WP.Forward) && FwdPosLooksL(r1)
    case _ => true
  }

  ghost predicate FwdPosActsL(acts: LS.Actions) {
    forall i :: 0 <= i < |acts| ==> (acts[i].Areg? ==> FwdPosLooksL(acts[i].r))
  }

  /** The depth-stratification hypothesis: every closedness instance whose
      pending regexes nest STRICTLY below `D` lands at a closed leaf. */
  ghost predicate ClosedBelow(rer: LW.RegExpRecord, D: nat) {
    forall acts: LS.Actions, inp: LC.Input, b: BS.LoopBool, t: LT.Tree, gm: LG.GroupMap, leaf: LT.Leaf ::
      (D > 0 && NestDepthActsLe(acts, D - 1)
       && EL.BoolTreeLk(rer, acts, inp, b, t)
       && EL.PikeLkActionsRec(acts) && FwdPosActsL(acts)
       && OpenOf(gm) <= PendingCloses(acts)
       && LT.TreeRes(t, gm, inp, WP.Forward) == Some(leaf)
       && LkClosedInGm(gm, acts)
       && OuterLkDisjoint(acts)
       && NoDupRegsActs(acts)
       && TRM.GmInBounds(gm, |inp.pref| + |inp.next|))
      ==> ClosedGm(leaf.1)
  }


  /** (helper, REGULAR lemma — outside the least context) The from-`gmR` body
      leaf of a positive FORWARD gate is CLOSED, by the depth-stratification
      hypothesis `ClosedBelow` (the body instance nests strictly below `D`). The
      full `BoolTreeLk` for the body tree is derived here via the fuel route, so
      the least lemma's prefix semantics never see it. */
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

  /** §2.5b: the BODY table of the `AR.QMap` for `re`: maps each quant id to
      that quantifier's (annotated) body — what `TreeRepRE`'s nulled-exit stamp
      rule reads the virtual empty-path chain off. Same walk as `QmOfRE`. */
  ghost function BodiesOfRE(re: R.regex): map<int, R.regex>
    requires T.TransWf(re)
    decreases re
  {
    match re
    case Re_empty => map[]
    case Re_character(_) => map[]
    case Re_anchor(_) => map[]
    case Re_alt(r1, r2) => BodiesOfRE(r1) + BodiesOfRE(r2)
    case Re_con(r1, r2) => BodiesOfRE(r1) + BodiesOfRE(r2)
    case Re_quant(nul, qid, q, r1) => BodiesOfRE(r1)[qid := r1]
    case Re_capture(_, r1) => BodiesOfRE(r1)
    case Re_lookaround(_, _, r1) => BodiesOfRE(r1)
  }

  /** `BodiesOfRE(re)`'s domain is exactly `re`'s quant ids (`PIV.QuantIds`). */
  lemma BodiesOfREDom(re: R.regex)
    requires T.TransWf(re) && PIV.QuantUnique(re)
    ensures forall k: int :: k in BodiesOfRE(re) <==> (k >= 0 && (k as nat) in PIV.QuantIds(re))
    decreases re
  {
    match re
    case Re_empty => case Re_character(_) => case Re_anchor(_) =>
    case Re_alt(r1, r2) => BodiesOfREDom(r1); BodiesOfREDom(r2);
    case Re_con(r1, r2) => BodiesOfREDom(r1); BodiesOfREDom(r2);
    case Re_quant(nul, qid, q, r1) => BodiesOfREDom(r1);
    case Re_capture(_, r1) => BodiesOfREDom(r1);
    case Re_lookaround(_, _, r1) => BodiesOfREDom(r1);
  }

  /** Each entry of `BodiesOfRE(re)` really is that quant id's body, provided
      quant ids are unique (`PIV.QuantUnique`) — the `QmOfREEntries` twin. */
  lemma BodiesOfREEntries(re: R.regex)
    requires T.TransWf(re) && PIV.QuantUnique(re)
    ensures forall qid: nat :: qid in PIV.QuantIds(re) ==>
                                 (qid as int) in BodiesOfRE(re)
                                 && BodiesOfRE(re)[qid as int] == PIV.QidBody(re, qid)
    decreases re
  {
    match re
    case Re_empty => case Re_character(_) => case Re_anchor(_) =>
    case Re_alt(r1, r2) =>
      BodiesOfREEntries(r1); BodiesOfREEntries(r2);
      BodiesOfREDom(r1); BodiesOfREDom(r2);
      forall qid: nat | qid in PIV.QuantIds(re)
        ensures (qid as int) in BodiesOfRE(re) && BodiesOfRE(re)[qid as int] == PIV.QidBody(re, qid)
      {
        if qid in PIV.QuantIds(r1) {
          assert qid !in PIV.QuantIds(r2) by {
            if qid in PIV.QuantIds(r2) { assert qid in PIV.QuantIds(r1) * PIV.QuantIds(r2); }
          }
          assert (qid as int) !in BodiesOfRE(r2);
        } else {
          assert qid in PIV.QuantIds(r2);
        }
      }
    case Re_con(r1, r2) =>
      BodiesOfREEntries(r1); BodiesOfREEntries(r2);
      BodiesOfREDom(r1); BodiesOfREDom(r2);
      forall qid: nat | qid in PIV.QuantIds(re)
        ensures (qid as int) in BodiesOfRE(re) && BodiesOfRE(re)[qid as int] == PIV.QidBody(re, qid)
      {
        if qid in PIV.QuantIds(r1) {
          assert qid !in PIV.QuantIds(r2) by {
            if qid in PIV.QuantIds(r2) { assert qid in PIV.QuantIds(r1) * PIV.QuantIds(r2); }
          }
          assert (qid as int) !in BodiesOfRE(r2);
        } else {
          assert qid in PIV.QuantIds(r2);
        }
      }
    case Re_quant(nul, qid0, q, r1) =>
      BodiesOfREEntries(r1);
      BodiesOfREDom(r1);
      assert qid0 >= 0;                                 // QuantUnique
      forall qid: nat | qid in PIV.QuantIds(re)
        ensures (qid as int) in BodiesOfRE(re) && BodiesOfRE(re)[qid as int] == PIV.QidBody(re, qid)
      {
        if (qid0 as nat) == qid {
          assert PIV.QidBody(re, qid) == r1;
        } else {
          assert qid in PIV.QuantIds(r1);
          assert (qid as int) != qid0;
        }
      }
    case Re_capture(_, r1) => BodiesOfREEntries(r1);
    case Re_lookaround(_, _, r1) => BodiesOfREEntries(r1);
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
    requires forall qid: nat :: qid in PIV.QuantIds(re) && T.TransWf(PIV.QidBody(re, qid)) ==>
                                  (qid as int) in qm.bodies && qm.bodies[qid as int] == PIV.QidBody(re, qid)   // §2.5b
    ensures AR.QmapOk(re, qm)
    decreases re
  {
    match re
    case Re_empty => case Re_character(_) => case Re_anchor(_) =>
    case Re_alt(r1, r2) =>
      forall qid: nat | qid in PIV.QuantIds(r1) && T.TransWf(PIV.QidBody(r1, qid))
        ensures (qid as int) in qm.quants && qm.quants[qid as int] == L.DefGroups(T.Translate(PIV.QidBody(r1, qid)))
                && (qid as int) in qm.bodies && qm.bodies[qid as int] == PIV.QidBody(r1, qid)
      {
        assert qid in PIV.QuantIds(re);
        TransWfQidBody(re, qid);
        assert PIV.QidBody(re, qid) == PIV.QidBody(r1, qid);
      }
      QmapOkFromEntries(r1, qm);
      forall qid: nat | qid in PIV.QuantIds(r2) && T.TransWf(PIV.QidBody(r2, qid))
        ensures (qid as int) in qm.quants && qm.quants[qid as int] == L.DefGroups(T.Translate(PIV.QidBody(r2, qid)))
                && (qid as int) in qm.bodies && qm.bodies[qid as int] == PIV.QidBody(r2, qid)
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
                && (qid as int) in qm.bodies && qm.bodies[qid as int] == PIV.QidBody(r1, qid)
      {
        assert qid in PIV.QuantIds(re);
        TransWfQidBody(re, qid);
        assert PIV.QidBody(re, qid) == PIV.QidBody(r1, qid);
      }
      QmapOkFromEntries(r1, qm);
      forall qid: nat | qid in PIV.QuantIds(r2) && T.TransWf(PIV.QidBody(r2, qid))
        ensures (qid as int) in qm.quants && qm.quants[qid as int] == L.DefGroups(T.Translate(PIV.QidBody(r2, qid)))
                && (qid as int) in qm.bodies && qm.bodies[qid as int] == PIV.QidBody(r2, qid)
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
      assert qid0 in qm.bodies && qm.bodies[qid0] == r1;
      forall qid: nat | qid in PIV.QuantIds(r1) && T.TransWf(PIV.QidBody(r1, qid))
        ensures (qid as int) in qm.quants && qm.quants[qid as int] == L.DefGroups(T.Translate(PIV.QidBody(r1, qid)))
                && (qid as int) in qm.bodies && qm.bodies[qid as int] == PIV.QidBody(r1, qid)
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
                && (qid as int) in qm.bodies && qm.bodies[qid as int] == PIV.QidBody(r1, qid)
      {
        assert qid in PIV.QuantIds(re);
        TransWfQidBody(re, qid);
        assert PIV.QidBody(re, qid) == PIV.QidBody(r1, qid);
      }
      QmapOkFromEntries(r1, qm);
    case Re_lookaround(_, _, r1) =>
      forall qid: nat | qid in PIV.QuantIds(r1) && T.TransWf(PIV.QidBody(r1, qid))
        ensures (qid as int) in qm.quants && qm.quants[qid as int] == L.DefGroups(T.Translate(PIV.QidBody(r1, qid)))
                && (qid as int) in qm.bodies && qm.bodies[qid as int] == PIV.QidBody(r1, qid)
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
            PIV.BestMatchRE(body, qm, str, bestT, AI.FFindMatch(bodycode, str, inits, ov, LAnc.Forward, cdns).0)
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
    PSM.GuardsOkRunStatic(qm, body, bodycode, endl, cdns, ov, str);   // (G5a step 2) no guard in this code
    bestT := PSM.FindMatchSimRE(rer, qm, body, bodycode, endl, ngroups, str, pts0, inits,
                                ov, LAnc.Forward, cdns, ncap, nlook, nquant);
    assert PSM.TrcRE(pts0, PT.PTS_final(bestT));
    assert PIV.BestMatchRE(body, qm, str, bestT, AI.FFindMatch(bodycode, str, inits, ov, LAnc.Forward, cdns).0);

    // Pin bestT to the checked tree's first leaf.
    TrcREToLinden(pts0, PT.PTS_final(bestT));
    TR.TreeRepPikeSubtree(qm, tstar, bodycode, 0, inp, false);
    PT.InitPiketreeInv(tstar, inp);
    CR.PikeTreeTrcCorrect(pts0, PT.PTS_final(bestT), LT.FirstLeaf(tstar, inp));
    assert bestT == LT.FirstLeaf(tstar, inp);
  }

  /** L4 depth-k (ADDITIVE): `FindMatchBodyAtCp` under the nested fragment.
      Verbatim `FindMatchBodyAtCp` with `StaticOkRE -> StaticOkNestedRE`, the
      entry establisher `InitialPikeInvFullREAtCp -> ...Nested`, and the
      simulation `FindMatchSimRE -> FindMatchSimRENested` (Phase 1). This runs a
      NESTED-fragment body's forward match from `cp` through the depth-k sim and
      pins the answer to the checked tree's first leaf — the engine half of the
      depth-k keystone STEP, now unblocked by Phase 1. The tree-correctness
      callees (`TrcREToLinden`/`TreeRepPikeSubtree`/`InitPiketreeInv`/
      `PikeTreeTrcCorrect`) are depth-blind. */
  lemma FindMatchBodyAtCpNested(
    rer: LW.RegExpRecord, qm: AR.QMap, body: R.regex, bodycode: RB.code, endl: nat,
    ngroups: nat, str: string, cp: nat, tstar: LT.Tree, ov: LOr.OracleView,
    cdns: LCdn.cdns, ncap: int, nlook: int, nquant: int)
    returns (bestT: Option<LT.Leaf>)
    requires PSM.StaticCoreNestedRE(qm, body, bodycode, endl)   // (G3a) no stamp-free premise: a boolean
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
            PIV.BestMatchRE(body, qm, str, bestT, AI.FFindMatch(bodycode, str, inits, ov, LAnc.Forward, cdns).0)
            && bestT == LT.FirstLeaf(tstar, inp)
  {
    var inp := PIV.InpOfCp(str, cp);
    var ctx := AI.cp_context(cp, str, LAnc.Forward);
    var capture := AReg.init_regs(ncap);
    var look := AReg.init_regs(nlook);
    var quant := AReg.init_regs(nquant);
    var inits := AI.FInitState(bodycode, cp, capture, look, quant, 0, ctx);

    // Entry invariant at cp (fresh registers) -> the full simulation invariant.
    PSM.InitialPikeInvFullREAtCpNested(rer, qm, body, bodycode, endl, ngroups, str, cp, tstar,
                                       inits, ncap, nlook, nquant);
    var pts0 := PT.PikeTreeInitialState(tstar, inp);
    assert ctx.nextchar == AI.get_char(str, cp);
    PSM.GuardsOkRunStaticNested(qm, body, bodycode, endl, cdns, ov, str);   // (G5a step 2) no guard in this code
    bestT := PSM.FindMatchSimRENested(rer, qm, body, bodycode, endl, ngroups, str, pts0, inits,
                                      ov, LAnc.Forward, cdns, ncap, nlook, nquant);
    assert PSM.TrcRE(pts0, PT.PTS_final(bestT));
    assert PIV.BestMatchRE(body, qm, str, bestT, AI.FFindMatch(bodycode, str, inits, ov, LAnc.Forward, cdns).0);

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
            PIV.BestMatchRE(body, qm, str, bestT, AI.FFindMatch(bodycode, str, inits, ov, LAnc.Forward, cdns).0)
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
    assert NB.EncOk(acts, inp, BS.CannotExit) by { NB.EncOkNoChecks(acts, inp, BS.CannotExit); }
    // (G5a-1 row F) the Rec family serves the look-free body too: both premises embed
    EL.PikeLkActionsEmbedsRec(acts);
    CE.LkConfinedTreeEmbedsK(t, {});
    var tstar := ATR.ActionsTreeRepRENested(rer, qm, acts, bodycode, 0, inp, BS.CannotExit, t, {});
    assert TR.TreeRepRE(qm, tstar, bodycode, 0, inp, false);
    NB.RAFirstLeafEmpty(tstar, t, inp);                       // Outside({}) -> equal first leaves
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
  lemma BodyTreeAtCpNested(
    rer: LW.RegExpRecord, qm: AR.QMap, body: R.regex, bodycode: RB.code, endl: nat,
    ngroups: nat, str: string, cp: nat, ov: LOr.OracleView,
    cdns: LCdn.cdns, ncap: int, nlook: int, nquant: int)
    returns (bestT: Option<LT.Leaf>)
    requires PSM.StaticCoreNestedRE(qm, body, bodycode, endl)   // (G3a) no stamp-free premise: a boolean
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
            PIV.BestMatchRE(body, qm, str, bestT, AI.FFindMatch(bodycode, str, inits, ov, LAnc.Forward, cdns).0)
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
    EL.TranslateFragmentPikeLkRec(body);          // PikeLkRegex(Translate(body))
    EL.BooleanCorrectLkRec(rer, T.Translate(body), inp, t);
    assert forall i :: 0 <= i < |acts| ==> !acts[i].Acheck?;
    BoolTreeLbIrrel(rer, acts, inp, BS.CanExit, BS.CannotExit, t);

    // ---- the CHECKED tree the simulation runs on -------------------------
    WOE.WalkOkEntryNested(body);
    assert EL.PikeLkActionsRec(acts) by {
      assert acts == acts + [];
      assert EL.PikeLkActionsRec([]);
      EL.PikeLkActionsRecConsIff(LS.Areg(T.Translate(body)), []);
    }
    assert WO.WalkOk(acts, bodycode, 0, ATR.EaOf(BS.CannotExit));
    AR.CompileToBytecodeActionsRepNested(rer, qm, body);   // ActionsRepL
    // `body` may now hold CAPTURING lookarounds: the spec tree's LK bodies confine
    // to `S = LkBodyGroups(Translate(body))`, so the tree is `LkConfinedTree(_, S)`.
    LL.LkBodyGroupsConfines(T.Translate(body), S);             // LkBodiesInS(Translate(body), S)
    assert LL.LkActsInS(acts, S) by { LL.LkActsInSCons(LS.Areg(T.Translate(body)), [], S); }
    LL.ComputeTrLkConfinedK(rer, acts, inp, LG.Empty, WP.Forward, S);   // LkConfinedTree(t, S)
    assert NB.EncOk(acts, inp, BS.CannotExit) by { NB.EncOkNoChecks(acts, inp, BS.CannotExit); }
    var tstar := ATR.ActionsTreeRepRENested(rer, qm, acts, bodycode, 0, inp, BS.CannotExit, t, S);
    assert TR.TreeRepRE(qm, tstar, bodycode, 0, inp, false);
    // ActionsTreeRepRE ensures LeavesAgreeAtOutside(tstar, t, inp, S); lift to FirstLeaf.
    NB.RAFirstLeafOutside(tstar, t, inp, S);

    // TreeThreadRE is definitionally TreeRepRE, so the checked tree discharges
    // both of FindMatchBodyAtCpNested's tree hypotheses.
    assert TT.TreeThreadRE(rer, qm, bodycode, inp, tstar, 0, false);

    // ---- run the simulation at cp ----------------------------------------
    bestT := FindMatchBodyAtCpNested(rer, qm, body, bodycode, endl, ngroups, str, cp, tstar,
                                     ov, cdns, ncap, nlook, nquant);
    assert bestT == LT.FirstLeaf(tstar, inp);
    // FirstLeafAgreeOutside(tstar, t, S): same success/position, gms agree outside S.
  }
  /** (G5b) `FindMatchBodyAtCpNested` / `BodyTreeAtCpNested` on the Cdn fragment: the body may hold a
      greedy CDN plus, whose guard reads the run's table (`PSM.GuardsOkRun`, the caller's premise). The
      oracle column's own forward run of a look body. */
  lemma FindMatchBodyAtCpCdn(
    rer: LW.RegExpRecord, qm: AR.QMap, body: R.regex, bodycode: RB.code, endl: nat,
    ngroups: nat, str: string, cp: nat, tstar: LT.Tree, ov: LOr.OracleView,
    cdns: LCdn.cdns, ncap: int, nlook: int, nquant: int)
    returns (bestT: Option<LT.Leaf>)
    requires PSM.StaticCoreCdnRE(qm, body, bodycode, endl)
    requires PSM.GuardsOkRun(qm, bodycode, cdns, ov, str)   // (G5b) every guard of the body code reads a right bit
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
            PIV.BestMatchRE(body, qm, str, bestT, AI.FFindMatch(bodycode, str, inits, ov, LAnc.Forward, cdns).0)
            && bestT == LT.FirstLeaf(tstar, inp)
  {
    var inp := PIV.InpOfCp(str, cp);
    var ctx := AI.cp_context(cp, str, LAnc.Forward);
    var capture := AReg.init_regs(ncap);
    var look := AReg.init_regs(nlook);
    var quant := AReg.init_regs(nquant);
    var inits := AI.FInitState(bodycode, cp, capture, look, quant, 0, ctx);

    // Entry invariant at cp (fresh registers) -> the full simulation invariant.
    PSM.InitialPikeInvFullREAtCpCdn(rer, qm, body, bodycode, endl, ngroups, str, cp, tstar,
                                       inits, ncap, nlook, nquant);
    var pts0 := PT.PikeTreeInitialState(tstar, inp);
    assert ctx.nextchar == AI.get_char(str, cp);
    bestT := PSM.FindMatchSimRECdn(rer, qm, body, bodycode, endl, ngroups, str, pts0, inits,
                                      ov, LAnc.Forward, cdns, ncap, nlook, nquant);
    assert PSM.TrcRE(pts0, PT.PTS_final(bestT));
    assert PIV.BestMatchRE(body, qm, str, bestT, AI.FFindMatch(bodycode, str, inits, ov, LAnc.Forward, cdns).0);

    // Pin bestT to the checked tree's first leaf.
    TrcREToLinden(pts0, PT.PTS_final(bestT));
    TR.TreeRepPikeSubtree(qm, tstar, bodycode, 0, inp, false);
    PT.InitPiketreeInv(tstar, inp);
    CR.PikeTreeTrcCorrect(pts0, PT.PTS_final(bestT), LT.FirstLeaf(tstar, inp));
    assert bestT == LT.FirstLeaf(tstar, inp);
  }
  lemma BodyTreeAtCpCdn(
    rer: LW.RegExpRecord, qm: AR.QMap, body: R.regex, bodycode: RB.code, endl: nat,
    ngroups: nat, str: string, cp: nat, ov: LOr.OracleView,
    cdns: LCdn.cdns, ncap: int, nlook: int, nquant: int)
    returns (bestT: Option<LT.Leaf>)
    requires PSM.StaticCoreCdnRE(qm, body, bodycode, endl)
    requires PSM.GuardsOkRun(qm, bodycode, cdns, ov, str)   // (G5b) every guard of the body code reads a right bit
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
            PIV.BestMatchRE(body, qm, str, bestT, AI.FFindMatch(bodycode, str, inits, ov, LAnc.Forward, cdns).0)
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
    EL.TranslateFragmentPikeLkRecCdn(body);          // PikeLkRegex(Translate(body))
    EL.BooleanCorrectLkRec(rer, T.Translate(body), inp, t);
    assert forall i :: 0 <= i < |acts| ==> !acts[i].Acheck?;
    BoolTreeLbIrrel(rer, acts, inp, BS.CanExit, BS.CannotExit, t);

    // ---- the CHECKED tree the simulation runs on -------------------------
    WOE.WalkOkEntryCdn(body);
    assert EL.PikeLkActionsRec(acts) by {
      assert acts == acts + [];
      assert EL.PikeLkActionsRec([]);
      EL.PikeLkActionsRecConsIff(LS.Areg(T.Translate(body)), []);
    }
    assert WO.WalkOk(acts, bodycode, 0, ATR.EaOf(BS.CannotExit));
    AR.CompileToBytecodeActionsRepCdn(rer, qm, body);   // ActionsRepL
    // `body` may now hold CAPTURING lookarounds: the spec tree's LK bodies confine
    // to `S = LkBodyGroups(Translate(body))`, so the tree is `LkConfinedTree(_, S)`.
    LL.LkBodyGroupsConfines(T.Translate(body), S);             // LkBodiesInS(Translate(body), S)
    assert LL.LkActsInS(acts, S) by { LL.LkActsInSCons(LS.Areg(T.Translate(body)), [], S); }
    LL.ComputeTrLkConfinedK(rer, acts, inp, LG.Empty, WP.Forward, S);   // LkConfinedTree(t, S)
    assert NB.EncOk(acts, inp, BS.CannotExit) by { NB.EncOkNoChecks(acts, inp, BS.CannotExit); }
    var tstar := ATR.ActionsTreeRepRENested(rer, qm, acts, bodycode, 0, inp, BS.CannotExit, t, S);
    assert TR.TreeRepRE(qm, tstar, bodycode, 0, inp, false);
    // ActionsTreeRepRE ensures LeavesAgreeAtOutside(tstar, t, inp, S); lift to FirstLeaf.
    NB.RAFirstLeafOutside(tstar, t, inp, S);

    // TreeThreadRE is definitionally TreeRepRE, so the checked tree discharges
    // both of FindMatchBodyAtCpNested's tree hypotheses.
    assert TT.TreeThreadRE(rer, qm, bodycode, inp, tstar, 0, false);

    // ---- run the simulation at cp ----------------------------------------
    bestT := FindMatchBodyAtCpCdn(rer, qm, body, bodycode, endl, ngroups, str, cp, tstar,
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
  lemma FCompileExtraFrameAny(r: R.regex, c: CP.FCompiled)
    ensures CP.FCompileExtra(r, c).f_main_ast == c.f_main_ast
    ensures CP.FCompileExtra(r, c).f_main_bc == c.f_main_bc
    ensures CP.FCompileExtra(r, c).f_main_cdns == c.f_main_cdns
    decreases r
  {
    match r
    case Re_empty => case Re_character(_) => case Re_anchor(_) =>
    case Re_capture(_, r1) => FCompileExtraFrameAny(r1, c);
    case Re_alt(r1, r2) => FCompileExtraFrameAny(r1, c); FCompileExtraFrameAny(r2, CP.FCompileExtra(r1, c));
    case Re_con(r1, r2) => FCompileExtraFrameAny(r1, c); FCompileExtraFrameAny(r2, CP.FCompileExtra(r1, c));
    case Re_quant(nul, qid, quant, r1) =>
      var c1 := if quant.min > 0 && quant.max == None && nul != R.NonNullable && quant.greedy
      then c.(f_plus_bc := CP.upd(c.f_plus_bc, qid, CP.compile_reconstruct_nulled(r1)))
      else c;
      FCompileExtraFrameAny(r1, c1);
    case Re_lookaround(lid, la, body) =>
      var c1 := c.(f_look_types := CP.upd(c.f_look_types, lid, la));
      var c2 := c1.(f_look_cdns := CP.upd(c1.f_look_cdns, lid, LCdn.compile_cdns(body)));
      var c3 := c2.(f_look_ast := CP.upd(c2.f_look_ast, lid, body));
      var c4 := c3.(f_look_build_bc :=
      CP.upd(c3.f_look_build_bc, lid,
             CP.compile_to_write(CP.oracle_regex(la, body), lid)));
      var c5 := c4.(f_look_capture_bc :=
      CP.upd(c4.f_look_capture_bc, lid,
             CP.compile_to_bytecode(CP.capture_regex(la, body))));
      FCompileExtraFrameAny(body, c5);
  }

  /** (L4 NESTED) `FFullCompilationFacts` for the NESTED fragment: the three
      main fields of `FFullCompilation(ast)` are the obvious compile outputs,
      for a nested-fragment `ast`. Same base literal as the depth-1 version,
      the frame discharged by `FCompileExtraFrameAny` (no fragment premise). */
  lemma FFullCompilationFactsNested(ast: R.regex)
    ensures CP.FFullCompilation(ast).f_main_ast == ast
    ensures CP.FFullCompilation(ast).f_main_bc == CP.compile_to_bytecode(R.lazy_prefix(ast))
    ensures CP.FFullCompilation(ast).f_main_cdns == LCdn.compile_cdns(ast)
  {
    hide R.max_lookaround, R.max_quant, R.lazy_prefix;   // (2026-09-06) recursive + in every term here: their unfolding is the matching loop
    var nlook0 := R.max_lookaround(ast) + 1;
    var nquant0 := R.max_quant(ast) + 1;
    var base := CP.FCompiled(ast, CP.compile_to_bytecode(R.lazy_prefix(ast)), LCdn.compile_cdns(ast),
                             seq(nlook0, i => R.Lookahead), seq(nlook0, i => R.Re_empty),
                             seq(nlook0, i => []), seq(nlook0, i => []),
                             seq(nlook0, i => []), seq(nquant0, i => []));
    assert CP.FFullCompilation(ast) == CP.FCompileExtra(ast, base);
    FCompileExtraFrameAny(ast, base);
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
  lemma NoTrueQuantStamp(body: R.regex)
    requires NR.LookBehindFragmentRE(body) && PIV.CapUnique(body) && PIV.QuantUnique(body)
    // §2.5b: the widened fragment admits the CIN-GREEDY scheme, whose exit
    // stamps TRUE — the all-stamps-false fact now needs the interim
    // no-nulled-plus gate conjunct.
    requires NR.NoNulledPlusRE(body)
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
        NI.StampFalseAt(body, code, 0, endl, pc);
      } else {
        assert pc == endl;
        assert NR.GetPcRE(code, endl) == Some(RB.Accept);
      }
    }
  }

  /** L4 depth-k (ADDITIVE): nested-fragment twin of `NoTrueQuantStamp`. A
      NESTED-fragment body's compiled bytecode never emits a TRUE quant stamp.
      `NR.CompileToBytecodeRepNested` supplies the `NfaRepRE`, and `NI.CodeShapeAt`
      (whose `Re_lookaround` case is trivial — a look compiles to a single
      `CheckOracle` leaf, which is neither `SetQuantToClock` nor `SetRegisterToCP`)
      discharges every pc, exactly as in the depth-1 proof. This is the ONE
      depth-1-capped ingredient the per-lid replay bridge needs generalized off
      `LookBehindFragmentRE`. */
  lemma NoTrueQuantStampNested(body: R.regex)
    requires NR.NestedFragmentRE(body) && PIV.CapUnique(body) && PIV.QuantUnique(body)
    requires NR.NoNulledPlusRE(body)   // §2.5b interim (see NoTrueQuantStamp)
    ensures var code := CP.compile_to_bytecode(body);
            forall pc: nat, q: int, b: bool ::
              NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(q, b)) ==> !b
  {
    var code := CP.compile_to_bytecode(body);
    var next := CP.compile(body, 0, CP.Progress).1;
    NR.CompileToBytecodeRepNested(body);
    var endl := next as nat;
    forall pc: nat, q: int, b: bool | NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(q, b))
      ensures !b
    {
      assert pc < |code|;
      if pc < endl {
        NI.StampFalseAt(body, code, 0, endl, pc);
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

  /** (G3a) The body-`l` match from FRESH registers FOLLOWED BY the nulled-plus reconstruction of
      `VBody(crv, l)`: exactly the engine's look replay `AI.FFindMatchPlus` from init banks (`AI.FLookLoop`
      reconstructs with `f_look_ast[l]` in both directions). The value predicates name it. OPAQUE: those
      predicates are unfolded inside the largest proofs; `FreshBodyMatchPlusPlain` is the bridge to
      `FreshBodyMatch` when the row's code stamps nothing. */
  opaque ghost function FreshBodyMatchPlus(crv: CP.FCompiled, str: string, l: int, lk: AReg.Regs,
                                           ov: LOr.OracleView, ncap: int, nlook: int, nquant: int): Option<AI.Thread> {
    var cp := if AReg.get_cp(lk, l).Some? then AReg.get_cp(lk, l).value else 0;
    var looktype := if 0 <= l < |crv.f_look_types| then crv.f_look_types[l] else R.Lookahead;
    var dir := AI.capture_direction(looktype);
    var bc := CP.compile_to_bytecode(CP.capture_regex(looktype, VBody(crv, l)));
    var cdn := if 0 <= l < |crv.f_look_cdns| then crv.f_look_cdns[l] else [];
    AI.FFindMatchPlus(bc, VBody(crv, l), crv.f_plus_bc, str, ov, dir, cp,
                      AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant), 0, cdn).0
  }

  /** (G3a) When row `l`'s code never stamps a quantifier `true` (every body that is nulled-plus-free,
      `NoTrueQuantStampNested`), the reconstruction is the identity: the plus match IS the plain one. */
  lemma FreshBodyMatchPlusPlain(crv: CP.FCompiled, str: string, l: int, lk: AReg.Regs,
                                ov: LOr.OracleView, ncap: int, nlook: int, nquant: int)
    requires ncap >= 0 && nlook >= 0 && nquant >= 0
    requires var looktype := if 0 <= l < |crv.f_look_types| then crv.f_look_types[l] else R.Lookahead;
             var bc := CP.compile_to_bytecode(CP.capture_regex(looktype, VBody(crv, l)));
             forall pc: nat, q: int, b: bool :: NR.GetPcRE(bc, pc) == Some(RB.SetQuantToClock(q, b)) ==> !b
    ensures FreshBodyMatchPlus(crv, str, l, lk, ov, ncap, nlook, nquant)
         == FreshBodyMatch(crv, str, l, lk, ov, ncap, nlook, nquant)
  {
    reveal FreshBodyMatchPlus();
    var cp := if AReg.get_cp(lk, l).Some? then AReg.get_cp(lk, l).value else 0;
    var looktype := if 0 <= l < |crv.f_look_types| then crv.f_look_types[l] else R.Lookahead;
    var dir := AI.capture_direction(looktype);
    var bc := CP.compile_to_bytecode(CP.capture_regex(looktype, VBody(crv, l)));
    var cdn := if 0 <= l < |crv.f_look_cdns| then crv.f_look_cdns[l] else [];
    var ctx := AI.cp_context(cp, str, dir);
    var inits := AI.FInitState(bc, cp, AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant), 0, ctx);
    assert VmQuantFinal(inits) by {
      var th0 := AI.init_thread(AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant));
      assert QuantRegsFinal(th0) by {
        hide *;
        reveal QuantRegsFinal, AI.init_thread, AI.get_idx, AReg.init_regs;
        RL.AInitLaws(nquant);
        forall k ensures AI.get_idx(AReg.init_regs(nquant).a_cp, k) < 0
                         && AI.get_idx(AReg.init_regs(nquant).a_clk, k) >= -1 {
          if 0 <= k < nquant { }
        }
      }
      forall t2 | t2 in inits.active ensures QuantRegsFinal(t2) { assert t2 == th0; }
    }
    FFindMatchQuantFinalAny(bc, str, inits, ov, dir, cdn);
    var (fm, ov1) := AI.FFindMatch(bc, str, inits, ov, dir, cdn);
    if fm.Some? {
      assert QuantRegsFinal(fm.value);
      FNulledPlusIdentity(VBody(crv, l), fm.value.capture_regs, fm.value.look_regs, fm.value.quant_regs,
                          crv.f_plus_bc, str, ov1, dir);
      assert AI.FReconstructPlus(fm.value, VBody(crv, l), crv.f_plus_bc, str, ov1, dir).0 == fm.value;
    }
  }

  /** (G3a) `FreshBodyMatchPlusPlain` at a positive row whose body carries the frame facts
      (`FrameEntryOk`'s first conjuncts): a lookahead replays `body`, a lookbehind `reverse_regex(body)`. */
  lemma FreshBodyMatchPlusPlainRow(crv: CP.FCompiled, str: string, l: int, lk: AReg.Regs,
                                   ov: LOr.OracleView, ncap: int, nlook: int, nquant: int,
                                   la: R.lookaround, body: R.regex)
    requires 0 <= l < |crv.f_look_types| && crv.f_look_types[l] == la && body == VBody(crv, l)
    requires la.Lookahead? || la.Lookbehind?
    requires NR.NestedFragmentRE(body) && PIV.CapUnique(body) && PIV.QuantUnique(body) && NR.NoNulledPlusRE(body)
    requires ncap >= 0 && nlook >= 0 && nquant >= 0
    ensures FreshBodyMatchPlus(crv, str, l, lk, ov, ncap, nlook, nquant)
         == FreshBodyMatch(crv, str, l, lk, ov, ncap, nlook, nquant)
  {
    if la.Lookahead? {
      assert CP.capture_regex(la, body) == body;
      NoTrueQuantStampNested(body);
    } else {
      assert CP.capture_regex(la, body) == R.reverse_regex(body);
      ReverseNestedPackage(body);
      NR.NoNulledPlusReverse(body);
      NoTrueQuantStampNested(R.reverse_regex(body));
    }
    FreshBodyMatchPlusPlain(crv, str, l, lk, ov, ncap, nlook, nquant);
  }

  /** The value-lift conclusion: on each matched positive lookahead's own capture
      registers, `res0` carries the fresh body match (or stays unset if the fresh
      body did not match). */
  lemma ReplayLidCapAgreeFreshNested(bytecode: RB.code, str: string, cp: int, cap: AReg.Regs, lk: AReg.Regs,
                                     qt: AReg.Regs, ov: LOr.OracleView, lookcdn: LCdn.cdns, plus_bcv: seq<RB.code>,
                                     body: R.regex, la: R.lookaround, ncap: int, nlook: int, nquant: int)
    requires NR.NestedFragmentRE(body)
    requires NR.NoNulledPlusRE(body)   // §2.5b interim: all stamps false
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
    NoTrueQuantStampNested(body);
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

  /** C4e: the per-lid FORWARD replay↔fresh QUANT agreement for a NESTED body —
      nested twin of `ReplayLidQuantAgreeFresh` (:5076) and quant analogue of
      `ReplayLidCapAgreeFreshNested`. The `FFindMatchPlus` lookahead replay's quant
      bank agrees, on `QIdsInt(body)`, with the fresh `FFindMatch`, with NO capture
      hypotheses (the register-value-blind bisimulation `CM.FFindMatchCapRel` runs
      at `Sc == {}`: control never reads register values, so it stays in lockstep
      regardless of the incoming capture bank). Entry: the body's quant slots are
      still INITIAL in the incoming bank. The ONE depth-1-capped ingredient is
      `NoTrueQuantStampNested` (nested twin of `NoTrueQuantStamp`); `FNulledPlus
      Identity` and `FFindMatchCapRel` are already fragment-generic. */
  lemma ReplayLidQuantAgreeFreshNested(bytecode: RB.code, str: string, cp: int, cap: AReg.Regs, lk: AReg.Regs,
                                       qt: AReg.Regs, ov: LOr.OracleView, lookcdn: LCdn.cdns, plus_bcv: seq<RB.code>,
                                       body: R.regex, la: R.lookaround, ncap: int, nlook: int, nquant: int)
    requires NR.NestedFragmentRE(body)
    requires NR.NoNulledPlusRE(body)   // §2.5b interim: all stamps false
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
    NoTrueQuantStampNested(body);
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
  // ===========================================================================
  // (L5 F7c-2) LOOKBEHIND twins of the nested replay helpers. `FLookLoop`
  // replays a positive LOOKBEHIND lid with `capture_regex(Lookbehind, body) ==
  // reverse_regex(body)` run BACKWARD (`capture_direction`), ast = `body`.
  // `rev := reverse_regex(body)` is itself a nested fragment with the SAME
  // capture / quant / look ids, so every code-shape fact of the forward helpers
  // applies to `compile(rev)`, and every engine lemma underneath already takes
  // `dir`. Conclusions are stated on `body`'s id sets (transferred by
  // `ReverseIdSets`).
  // ===========================================================================

  lemma ReverseCapIdsOutsideLooks(r: R.regex)
    ensures PIV.CapIdsOutsideLooks(R.reverse_regex(r)) == PIV.CapIdsOutsideLooks(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => ReverseCapIdsOutsideLooks(r1); ReverseCapIdsOutsideLooks(r2);
    case Re_con(r1, r2) => ReverseCapIdsOutsideLooks(r1); ReverseCapIdsOutsideLooks(r2);
    case Re_quant(_, _, _, r1) => ReverseCapIdsOutsideLooks(r1);
    case Re_capture(_, r1) => ReverseCapIdsOutsideLooks(r1);
    case _ =>
  }

  lemma ReverseDirectLookIds(r: R.regex)
    ensures DirectLookIds(R.reverse_regex(r)) == DirectLookIds(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => ReverseDirectLookIds(r1); ReverseDirectLookIds(r2);
    case Re_con(r1, r2) => ReverseDirectLookIds(r1); ReverseDirectLookIds(r2);
    case Re_quant(_, _, _, r1) => ReverseDirectLookIds(r1);
    case Re_capture(_, r1) => ReverseDirectLookIds(r1);
    case _ =>
  }

  /** All the id sets the replay frames speak about are `reverse_regex`-invariant. */
  lemma ReverseIdSets(body: R.regex)
    ensures PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(R.reverse_regex(body)))
         == PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(body))
    ensures LookIdSet(R.reverse_regex(body)) == LookIdSet(body)
    ensures DirectLidSet(R.reverse_regex(body)) == DirectLidSet(body)
    ensures LKC.QIdsInt(R.reverse_regex(body)) == LKC.QIdsInt(body)
    ensures PIV.CaptureRegs(R.reverse_regex(body)) == PIV.CaptureRegs(body)
  {
    ReverseCapIdsOutsideLooks(body);
    NR.LookIdsReverseRE(body);
    ReverseDirectLookIds(body);
    PIV.ReverseQuantIds(body);
    PIV.ReverseCapIds(body);
  }

  /** The reversed body's structural package. */
  lemma ReverseNestedPackage(body: R.regex)
    requires NR.NestedFragmentRE(body) && PIV.CapUnique(body) && PIV.QuantUnique(body)
    ensures NR.NestedFragmentRE(R.reverse_regex(body))
    ensures PIV.CapUnique(R.reverse_regex(body)) && PIV.QuantUnique(R.reverse_regex(body))
    ensures LTB.LookUnique(body) ==> LTB.LookUnique(R.reverse_regex(body))
  {
    NR.ReverseNestedFragmentRE(body);
    PIV.ReverseCapUnique(body);
    PIV.ReverseQuantUnique(body);
    if LTB.LookUnique(body) { NR.LookUniqueReverseRE(body); }
  }

  /** (G5b-2) `ReverseNestedPackage` on the Cdn fragment. */
  lemma ReverseCdnPackage(body: R.regex)
    requires NR.NestedFragmentCdnRE(body) && PIV.CapUnique(body) && PIV.QuantUnique(body)
    ensures NR.NestedFragmentCdnRE(R.reverse_regex(body))
    ensures PIV.CapUnique(R.reverse_regex(body)) && PIV.QuantUnique(R.reverse_regex(body))
    ensures LTB.LookUnique(body) ==> LTB.LookUnique(R.reverse_regex(body))
  {
    OBu.ReverseCdnFragmentRE(body);
    PIV.ReverseCapUnique(body);
    PIV.ReverseQuantUnique(body);
    if LTB.LookUnique(body) { NR.LookUniqueReverseRE(body); }
  }

  /** LB twin of `ReplayCaptureFrameNestedOuter`. */
  lemma ReplayCaptureFrameNestedOuterLB(bytecode: RB.code, str: string, inits: AI.VmState, ov: LOr.OracleView,
                                        lookcdn: LCdn.cdns, cap: AReg.Regs, lk: AReg.Regs, qt: AReg.Regs, body: R.regex)
    requires NR.NestedFragmentRE(body) && PIV.CapUnique(body)
    requires bytecode == CP.compile_to_bytecode(R.reverse_regex(body))
    requires inits.active == [AI.init_thread(cap, lk, qt)]
    requires inits.blocked == [] && inits.bestmatch.None?
    requires |inits.processed.true_set| == RB.size(bytecode)
             && |inits.processed.false_set| == RB.size(bytecode)
    requires inits.context.nextchar == AI.get_char(str, inits.cp - 1)
    ensures var r := AI.FFindMatch(bytecode, str, inits, ov, LAnc.Backward, lookcdn).0;
            r.Some? ==> CM.RegsAgreeOutside(r.value.capture_regs, cap,
                                            PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(body)))
  {
    var rev := R.reverse_regex(body);
    NR.ReverseNestedFragmentRE(body);
    PIV.ReverseCapUnique(body);
    var Sc := PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(body));
    ReverseCapIdsOutsideLooks(body);
    CaptureBytecodeClassifiedNestedOuter(rev);
    assert CM.CaptureWritesInside(bytecode, Sc);
    assert CM.VmCapturesAgree(inits, cap, Sc) by {
      assert CM.RegsAgreeOutside(cap, cap, Sc);
    }
    CM.FFindMatchCapWriteFrame(bytecode, str, inits, ov, LAnc.Backward, lookcdn, cap, Sc);
  }

  /** LB twin of `ReplayPlusCaptureFrameNestedOuter`. */
  lemma ReplayPlusCaptureFrameNestedOuterLB(bytecode: RB.code, str: string, ov: LOr.OracleView,
                                            lookcdn: LCdn.cdns, plus_bcv: seq<RB.code>, cp: int,
                                            cap: AReg.Regs, lk: AReg.Regs, qt: AReg.Regs, body: R.regex)
    requires NR.NestedFragmentRE(body) && PIV.CapUnique(body) && PIV.QuantUnique(body)
    requires NR.NoNulledPlusRE(body)   // §2.5b interim: all stamps false
    requires bytecode == CP.compile_to_bytecode(R.reverse_regex(body))
    requires AI.cp_context(cp, str, LAnc.Backward).nextchar == AI.get_char(str, cp - 1)
    requires (forall k :: AI.get_idx(qt.a_cp, k) < 0)
             && (forall k :: AI.get_idx(qt.a_clk, k) >= -1)
    ensures var r := AI.FFindMatchPlus(bytecode, body, plus_bcv, str, ov, LAnc.Backward, cp, cap, lk, qt, 0, lookcdn).0;
            r.Some? ==> CM.RegsAgreeOutside(r.value.capture_regs, cap,
                                            PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(body)))
  {
    var dir := LAnc.Backward;
    var rev := R.reverse_regex(body);
    ReverseNestedPackage(body);
    var inits := AI.FInitState(bytecode, cp, cap, lk, qt, 0, AI.cp_context(cp, str, dir));
    ReplayCaptureFrameNestedOuterLB(bytecode, str, inits, ov, lookcdn, cap, lk, qt, body);
    NR.NoNulledPlusReverse(body);
    NoTrueQuantStampNested(rev);
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

  /** LB twin of `ReplayPlusLookFrameNested`. */
  lemma ReplayPlusLookFrameNestedLB(bytecode: RB.code, str: string, ov: LOr.OracleView,
                                    lookcdn: LCdn.cdns, plus_bcv: seq<RB.code>, cp: int,
                                    cap: AReg.Regs, lk: AReg.Regs, qt: AReg.Regs, body: R.regex)
    requires NR.NestedFragmentRE(body) && PIV.CapUnique(body) && PIV.QuantUnique(body) && LTB.LookUnique(body)
    requires NR.NoNulledPlusRE(body)   // §2.5b interim: all stamps false
    requires bytecode == CP.compile_to_bytecode(R.reverse_regex(body))
    requires AI.cp_context(cp, str, LAnc.Backward).nextchar == AI.get_char(str, cp - 1)
    requires (forall k :: AI.get_idx(qt.a_cp, k) < 0)
             && (forall k :: AI.get_idx(qt.a_clk, k) >= -1)
    ensures var r := AI.FFindMatchPlus(bytecode, body, plus_bcv, str, ov, LAnc.Backward, cp, cap, lk, qt, 0, lookcdn).0;
            r.Some? ==> CM.RegsAgreeOutside(r.value.look_regs, lk, LookIdSet(body))
  {
    var dir := LAnc.Backward;
    var rev := R.reverse_regex(body);
    ReverseNestedPackage(body);
    ReverseIdSets(body);
    var inits := AI.FInitState(bytecode, cp, cap, lk, qt, 0, AI.cp_context(cp, str, dir));
    LookBytecodeClassifiedNested(rev);
    assert CM.LookChecksInside(bytecode, LookIdSet(body));
    assert CM.VmLooksAgree(inits, lk, LookIdSet(body)) by {
      assert CM.RegsAgreeOutside(lk, lk, LookIdSet(body));
    }
    CM.FFindMatchLookFrame(bytecode, str, inits, ov, dir, lookcdn, lk, LookIdSet(body));
    NR.NoNulledPlusReverse(body);
    NoTrueQuantStampNested(rev);
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

  /** LB twin of `ReplayPlusLookFrameDirectNested`. */
  lemma ReplayPlusLookFrameDirectNestedLB(bytecode: RB.code, str: string, ov: LOr.OracleView,
                                          lookcdn: LCdn.cdns, plus_bcv: seq<RB.code>, cp: int,
                                          cap: AReg.Regs, lk: AReg.Regs, qt: AReg.Regs, body: R.regex)
    requires NR.NestedFragmentRE(body) && PIV.CapUnique(body) && PIV.QuantUnique(body) && LTB.LookUnique(body)
    requires NR.NoNulledPlusRE(body)   // §2.5b interim: all stamps false
    requires bytecode == CP.compile_to_bytecode(R.reverse_regex(body))
    requires AI.cp_context(cp, str, LAnc.Backward).nextchar == AI.get_char(str, cp - 1)
    requires (forall k :: AI.get_idx(qt.a_cp, k) < 0)
             && (forall k :: AI.get_idx(qt.a_clk, k) >= -1)
    ensures var r := AI.FFindMatchPlus(bytecode, body, plus_bcv, str, ov, LAnc.Backward, cp, cap, lk, qt, 0, lookcdn).0;
            r.Some? ==> CM.RegsAgreeOutside(r.value.look_regs, lk, DirectLidSet(body))
  {
    var dir := LAnc.Backward;
    var rev := R.reverse_regex(body);
    ReverseNestedPackage(body);
    ReverseIdSets(body);
    var inits := AI.FInitState(bytecode, cp, cap, lk, qt, 0, AI.cp_context(cp, str, dir));
    DirectLidClassified(rev);
    assert CM.LookChecksInside(bytecode, DirectLidSet(body));
    assert CM.VmLooksAgree(inits, lk, DirectLidSet(body)) by {
      assert CM.RegsAgreeOutside(lk, lk, DirectLidSet(body));
    }
    CM.FFindMatchLookFrame(bytecode, str, inits, ov, dir, lookcdn, lk, DirectLidSet(body));
    NR.NoNulledPlusReverse(body);
    NoTrueQuantStampNested(rev);
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

  /** LB twin of `ReplayPlusFrameNested`. */
  lemma ReplayPlusFrameNestedLB(bytecode: RB.code, str: string, ov: LOr.OracleView,
                                lookcdn: LCdn.cdns, plus_bcv: seq<RB.code>, cp: int,
                                cap: AReg.Regs, lk: AReg.Regs, qt: AReg.Regs, body: R.regex)
    requires NR.NestedFragmentRE(body) && PIV.CapUnique(body) && PIV.QuantUnique(body) && LTB.LookUnique(body)
    requires NR.NoNulledPlusRE(body)   // §2.5b interim: all stamps false
    requires bytecode == CP.compile_to_bytecode(R.reverse_regex(body))
    requires AI.cp_context(cp, str, LAnc.Backward).nextchar == AI.get_char(str, cp - 1)
    requires (forall k :: AI.get_idx(qt.a_cp, k) < 0)
             && (forall k :: AI.get_idx(qt.a_clk, k) >= -1)
    ensures var r := AI.FFindMatchPlus(bytecode, body, plus_bcv, str, ov, LAnc.Backward, cp, cap, lk, qt, 0, lookcdn).0;
            r.Some? ==>
              CM.RegsAgreeOutside(r.value.capture_regs, cap, PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(body)))
              && CM.RegsAgreeOutside(r.value.look_regs, lk, LookIdSet(body))
              && QuantRegsFinal(r.value)
  {
    var dir := LAnc.Backward;
    var rev := R.reverse_regex(body);
    ReverseNestedPackage(body);
    ReplayPlusCaptureFrameNestedOuterLB(bytecode, str, ov, lookcdn, plus_bcv, cp, cap, lk, qt, body);
    ReplayPlusLookFrameNestedLB(bytecode, str, ov, lookcdn, plus_bcv, cp, cap, lk, qt, body);
    var inits := AI.FInitState(bytecode, cp, cap, lk, qt, 0, AI.cp_context(cp, str, dir));
    NR.NoNulledPlusReverse(body);
    NoTrueQuantStampNested(rev);
    assert VmQuantFinal(inits) by {
      assert QuantRegsFinal(AI.init_thread(cap, lk, qt));
    }
    FFindMatchQuantFinalAny(bytecode, str, inits, ov, dir, lookcdn);
    var (res0, ovx) := AI.FFindMatch(bytecode, str, inits, ov, dir, lookcdn);
    if res0.Some? {
      var th := res0.value;
      FNulledPlusIdentity(body, th.capture_regs, th.look_regs, th.quant_regs, plus_bcv, str, ovx, dir);
    }
  }

  /** LB twin of `FFindMatchPlusOvStableNested`. */
  lemma FFindMatchPlusOvStableNestedLB(bytecode: RB.code, str: string, ov: LOr.OracleView,
                                       lookcdn: LCdn.cdns, plus_bcv: seq<RB.code>, cp: int,
                                       cap: AReg.Regs, lk: AReg.Regs, qt: AReg.Regs, body: R.regex)
    requires NR.NestedFragmentRE(body) && PIV.CapUnique(body) && PIV.QuantUnique(body)
    requires NR.NoNulledPlusRE(body)   // §2.5b interim: all stamps false
    requires bytecode == CP.compile_to_bytecode(R.reverse_regex(body))
    requires AI.cp_context(cp, str, LAnc.Backward).nextchar == AI.get_char(str, cp - 1)
    requires (forall k :: AI.get_idx(qt.a_cp, k) < 0)
             && (forall k :: AI.get_idx(qt.a_clk, k) >= -1)
    ensures AI.FFindMatchPlus(bytecode, body, plus_bcv, str, ov, LAnc.Backward, cp, cap, lk, qt, 0, lookcdn).1 == ov
  {
    var dir := LAnc.Backward;
    var rev := R.reverse_regex(body);
    ReverseNestedPackage(body);
    var inits := AI.FInitState(bytecode, cp, cap, lk, qt, 0, AI.cp_context(cp, str, dir));
    NoWriteOracleBodyCodeNested(rev);
    CM.FFindMatchOvStable(bytecode, str, inits, ov, dir, lookcdn);
    NR.NoNulledPlusReverse(body);
    NoTrueQuantStampNested(rev);
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

  /** LB twin of `ReplayThreadWfLANested`. */
  lemma ReplayThreadWfLBNested(bytecode: RB.code, str: string, cp: int, cap: AReg.Regs, lk: AReg.Regs,
                               qt: AReg.Regs, ov: LOr.OracleView, lookcdn: LCdn.cdns, plus_bcv: seq<RB.code>,
                               body: R.regex, ncap: int, nlook: int, nquant: int)
    requires NR.NestedFragmentRE(body) && PIV.CapUnique(body) && PIV.QuantUnique(body)
    requires NR.NoNulledPlusRE(body)   // §2.5b interim: all stamps false
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
    var dir := LAnc.Backward;
    var rev := R.reverse_regex(body);
    ReverseNestedPackage(body);
    var ctx := AI.cp_context(cp, str, dir);
    var inits := AI.FInitState(bytecode, cp, cap, lk, qt, 0, ctx);
    assert CM.VmRegsWf(inits, ncap, nlook, nquant) by {
      assert CM.ThreadRegsWf(AI.init_thread(cap, lk, qt), ncap, nlook, nquant);
      assert inits.active == [AI.init_thread(cap, lk, qt)];
      forall t | t in inits.active ensures CM.ThreadRegsWf(t, ncap, nlook, nquant) {}
    }
    FFindMatchRegsWf(bytecode, str, inits, ov, dir, lookcdn, ncap, nlook, nquant);
    NR.NoNulledPlusReverse(body);
    NoTrueQuantStampNested(rev);
    assert VmQuantFinal(inits) by { assert QuantRegsFinal(AI.init_thread(cap, lk, qt)); }
    FFindMatchQuantFinalAny(bytecode, str, inits, ov, dir, lookcdn);
    var (fmres, ovx) := AI.FFindMatch(bytecode, str, inits, ov, dir, lookcdn);
    if fmres.Some? {
      FNulledPlusIdentity(body, fmres.value.capture_regs, fmres.value.look_regs, fmres.value.quant_regs,
                          plus_bcv, str, ovx, dir);
    }
  }

  /** LB twin of `ReplayLookCpOkNested`. */
  lemma ReplayLookCpOkNestedLB(bytecode: RB.code, str: string, ov: LOr.OracleView,
                               lookcdn: LCdn.cdns, plus_bcv: seq<RB.code>, cp: int,
                               cap: AReg.Regs, lk: AReg.Regs, qt: AReg.Regs, body: R.regex)
    requires NR.NestedFragmentRE(body) && PIV.CapUnique(body) && PIV.QuantUnique(body)
    requires NR.NoNulledPlusRE(body)   // §2.5b interim: all stamps false
    requires bytecode == CP.compile_to_bytecode(R.reverse_regex(body))
    requires 0 <= cp <= |str|
    requires (forall k :: AI.get_idx(qt.a_cp, k) < 0)
             && (forall k :: AI.get_idx(qt.a_clk, k) >= -1)
    requires CM.LookCpsLE(lk, |str|)
    ensures var r := AI.FFindMatchPlus(bytecode, body, plus_bcv, str, ov, LAnc.Backward, cp, cap, lk, qt, 0, lookcdn).0;
            r.Some? ==> CM.LookCpsLE(r.value.look_regs, |str|)
  {
    var dir := LAnc.Backward;
    var rev := R.reverse_regex(body);
    ReverseNestedPackage(body);
    var ctx := AI.cp_context(cp, str, dir);
    var inits := AI.FInitState(bytecode, cp, cap, lk, qt, 0, ctx);
    assert CM.VmLookCpOk(inits, |str|) by {
      assert AI.init_thread(cap, lk, qt).look_regs == lk;
      assert inits.active == [AI.init_thread(cap, lk, qt)];
    }
    assert ctx.nextchar == AI.get_char(str, cp - 1);
    CM.FFindMatchLookCpOkB(bytecode, str, inits, ov, dir, lookcdn);
    NR.NoNulledPlusReverse(body);
    NoTrueQuantStampNested(rev);
    assert VmQuantFinal(inits) by { assert QuantRegsFinal(AI.init_thread(cap, lk, qt)); }
    FFindMatchQuantFinalAny(bytecode, str, inits, ov, dir, lookcdn);
    var (res0, ovx) := AI.FFindMatch(bytecode, str, inits, ov, dir, lookcdn);
    if res0.Some? {
      var th := res0.value;
      FNulledPlusIdentity(body, th.capture_regs, th.look_regs, th.quant_regs, plus_bcv, str, ovx, dir);
    }
  }

  /** LB twin of `ReplayCapAgreeFresh` (the register-value-blind bisimulation, Backward). */
  lemma ReplayCapAgreeFreshLBNested(bodycode: RB.code, str: string, cp: int, cap: AReg.Regs, lk: AReg.Regs,
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

  /** LB twin of `ReplayLidCapAgreeFreshNested`. */
  lemma ReplayLidCapAgreeFreshNestedLB(bytecode: RB.code, str: string, cp: int, cap: AReg.Regs, lk: AReg.Regs,
                                       qt: AReg.Regs, ov: LOr.OracleView, lookcdn: LCdn.cdns, plus_bcv: seq<RB.code>,
                                       body: R.regex, ncap: int, nlook: int, nquant: int)
    requires NR.NestedFragmentRE(body)
    requires NR.NoNulledPlusRE(body)   // §2.5b interim: all stamps false
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
    var dir := LAnc.Backward;
    var rev := R.reverse_regex(body);
    ReverseNestedPackage(body);
    var inits := AI.FInitState(bytecode, cp, cap, lk, qt, 0, AI.cp_context(cp, str, dir));
    NR.NoNulledPlusReverse(body);
    NoTrueQuantStampNested(rev);
    assert VmQuantFinal(inits) by { assert QuantRegsFinal(AI.init_thread(cap, lk, qt)); }
    FFindMatchQuantFinalAny(bytecode, str, inits, ov, dir, lookcdn);
    var (fmres, ovx) := AI.FFindMatch(bytecode, str, inits, ov, dir, lookcdn);
    if fmres.Some? {
      FNulledPlusIdentity(body, fmres.value.capture_regs, fmres.value.look_regs, fmres.value.quant_regs,
                          plus_bcv, str, ovx, dir);
    }
    ReplayCapAgreeFreshLBNested(bytecode, str, cp, cap, lk, qt, ov, lookcdn, body, ncap, nlook, nquant);
  }

  /** LB twin of `ReplayLidLookAgreeFreshNested`. */
  lemma ReplayLidLookAgreeFreshNestedLB(bytecode: RB.code, str: string, cp: int, cap: AReg.Regs, lk: AReg.Regs,
                                        qt: AReg.Regs, ov: LOr.OracleView, lookcdn: LCdn.cdns, plus_bcv: seq<RB.code>,
                                        body: R.regex, SL: set<int>, ncap: int, nlook: int, nquant: int)
    requires NR.NestedFragmentRE(body)
    requires NR.NoNulledPlusRE(body)   // §2.5b interim: all stamps false
    requires PIV.CapUnique(body) && PIV.QuantUnique(body)
    requires bytecode == CP.compile_to_bytecode(R.reverse_regex(body))
    requires 0 <= cp <= |str|
    requires AI.cp_context(cp, str, LAnc.Backward).nextchar == AI.get_char(str, cp - 1)
    requires (forall k :: AI.get_idx(qt.a_cp, k) < 0)
             && (forall k :: AI.get_idx(qt.a_clk, k) >= -1)
    requires |qt.a_cp| == nquant && |qt.a_clk| == nquant
    requires |cap.a_cp| == ncap && |cap.a_clk| == ncap
    requires CM.RegsAgreeInside(lk, AReg.init_regs(nlook), SL)
    ensures
      var result := AI.FFindMatchPlus(bytecode, body, plus_bcv, str, ov, LAnc.Backward, cp, cap, lk, qt, 0, lookcdn).0;
      var rf := AI.FFindMatch(bytecode, str,
                              AI.FInitState(bytecode, cp, AReg.init_regs(ncap), AReg.init_regs(nlook),
                                            AReg.init_regs(nquant), 0, AI.cp_context(cp, str, LAnc.Backward)),
                              ov, LAnc.Backward, lookcdn).0;
      (result.None? <==> rf.None?)
      && (result.Some? ==>
            CM.RegsAgreeInside(result.value.look_regs, rf.value.look_regs, SL))
  {
    var dir := LAnc.Backward;
    var rev := R.reverse_regex(body);
    ReverseNestedPackage(body);
    var ctxc := AI.cp_context(cp, str, dir);
    var inits := AI.FInitState(bytecode, cp, cap, lk, qt, 0, ctxc);
    NR.NoNulledPlusReverse(body);
    NoTrueQuantStampNested(rev);
    assert VmQuantFinal(inits) by { assert QuantRegsFinal(AI.init_thread(cap, lk, qt)); }
    FFindMatchQuantFinalAny(bytecode, str, inits, ov, dir, lookcdn);
    var (fmres, ovx) := AI.FFindMatch(bytecode, str, inits, ov, dir, lookcdn);
    if fmres.Some? {
      FNulledPlusIdentity(body, fmres.value.capture_regs, fmres.value.look_regs, fmres.value.quant_regs,
                          plus_bcv, str, ovx, dir);
    }
    var sf := AI.FInitState(bytecode, cp, AReg.init_regs(ncap), AReg.init_regs(nlook),
                            AReg.init_regs(nquant), 0, ctxc);
    assert CM.VmRelLk(inits, sf, {}, {}, SL) by {
      assert CM.ThreadRelLk(AI.init_thread(cap, lk, qt),
                            AI.init_thread(AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant)),
    {}, {}, SL) by {
        assert CM.RegsAgreeInside(cap, AReg.init_regs(ncap), {});
        assert CM.RegsAgreeInside(qt, AReg.init_regs(nquant), {});
        assert CM.RegsAgreeInside(lk, AReg.init_regs(nlook), SL);
      }
    }
    CM.FFindMatchLookRel(bytecode, str, inits, sf, ov, dir, lookcdn, {}, {}, SL);
  }

  /** LB twin of `ReplayLidQuantAgreeFreshNested`. */
  lemma ReplayLidQuantAgreeFreshNestedLB(bytecode: RB.code, str: string, cp: int, cap: AReg.Regs, lk: AReg.Regs,
                                         qt: AReg.Regs, ov: LOr.OracleView, lookcdn: LCdn.cdns, plus_bcv: seq<RB.code>,
                                         body: R.regex, ncap: int, nlook: int, nquant: int)
    requires NR.NestedFragmentRE(body)
    requires NR.NoNulledPlusRE(body)   // §2.5b interim: all stamps false
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
    var dir := LAnc.Backward;
    var rev := R.reverse_regex(body);
    ReverseNestedPackage(body);
    var ctxc := AI.cp_context(cp, str, dir);
    var inits := AI.FInitState(bytecode, cp, cap, lk, qt, 0, ctxc);
    NR.NoNulledPlusReverse(body);
    NoTrueQuantStampNested(rev);
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
  lemma ReverseQuantIdsOutsideLooks(r: R.regex)
    ensures PIV.QuantIdsOutsideLooks(R.reverse_regex(r)) == PIV.QuantIdsOutsideLooks(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => ReverseQuantIdsOutsideLooks(r1); ReverseQuantIdsOutsideLooks(r2);
    case Re_con(r1, r2) => ReverseQuantIdsOutsideLooks(r1); ReverseQuantIdsOutsideLooks(r2);
    case Re_quant(_, _, _, r1) => ReverseQuantIdsOutsideLooks(r1);
    case Re_capture(_, r1) => ReverseQuantIdsOutsideLooks(r1);
    case _ =>
  }

  /** LB twin of `ReplayPlusQuantFrameNestedOuter`. */
  lemma ReplayPlusQuantFrameNestedOuterLB(bytecode: RB.code, str: string, ov: LOr.OracleView,
                                          lookcdn: LCdn.cdns, plus_bcv: seq<RB.code>, cp: int,
                                          cap: AReg.Regs, lk: AReg.Regs, qt: AReg.Regs, body: R.regex)
    requires NR.NestedFragmentRE(body) && PIV.CapUnique(body) && PIV.QuantUnique(body)
    requires NR.NoNulledPlusRE(body)   // §2.5b interim: all stamps false
    requires bytecode == CP.compile_to_bytecode(R.reverse_regex(body))
    requires AI.cp_context(cp, str, LAnc.Backward).nextchar == AI.get_char(str, cp - 1)
    requires (forall k :: AI.get_idx(qt.a_cp, k) < 0)
             && (forall k :: AI.get_idx(qt.a_clk, k) >= -1)
    ensures var r := AI.FFindMatchPlus(bytecode, body, plus_bcv, str, ov, LAnc.Backward, cp, cap, lk, qt, 0, lookcdn).0;
            r.Some? ==> CM.RegsAgreeOutside(r.value.quant_regs, qt, QIdsOuter(body))
  {
    var dir := LAnc.Backward;
    var rev := R.reverse_regex(body);
    ReverseNestedPackage(body);
    ReverseQuantIdsOutsideLooks(body);
    var Sq := QIdsOuter(body);
    assert QIdsOuter(rev) == Sq;
    var inits := AI.FInitState(bytecode, cp, cap, lk, qt, 0, AI.cp_context(cp, str, dir));
    QuantBytecodeClassifiedNestedOuter(rev);
    assert CM.QuantWritesInside(bytecode, Sq);
    assert CM.VmQuantsAgree(inits, qt, Sq) by {
      assert inits.active == [AI.init_thread(cap, lk, qt)];
      assert AI.init_thread(cap, lk, qt).quant_regs == qt;
      assert CM.RegsAgreeOutside(qt, qt, Sq);
    }
    CM.FFindMatchQuantFrame(bytecode, str, inits, ov, dir, lookcdn, qt, Sq);
    NR.NoNulledPlusReverse(body);
    NoTrueQuantStampNested(rev);
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



  /** (DEEP reverse-recon LEVEL-LINK, engine half) the per-lid replay↔fresh LOOK
      agreement for a NESTED body — look twin of `ReplayLidQuantAgreeFreshNested`.
      The `FFindMatchPlus` lookahead replay's LOOK bank agrees, on any index set
      `SL` where the incoming bank is still INITIAL, with the fresh `FFindMatch`'s
      look bank, matching iff-together. Both runs are in register-blind lockstep
      (`CM.FFindMatchLookRel` at `Sc == Sq == {}`), and CheckOracle writes the same
      (l, cp, clock) at every crossing, so initial agreement inside `SL` persists.
      Instantiated at `SL := DirectLidSet(body)` (the only look ids the replay
      writes), this ties the FLookLoop iteration's recorded DIRECT-child positions
      to the FRESH body match's — the level-link of the deep landing recursion. */
  lemma ReplayLidLookAgreeFreshNested(bytecode: RB.code, str: string, cp: int, cap: AReg.Regs, lk: AReg.Regs,
                                      qt: AReg.Regs, ov: LOr.OracleView, lookcdn: LCdn.cdns, plus_bcv: seq<RB.code>,
                                      body: R.regex, la: R.lookaround, SL: set<int>, ncap: int, nlook: int, nquant: int)
    requires NR.NestedFragmentRE(body)
    requires NR.NoNulledPlusRE(body)   // §2.5b interim: all stamps false
    requires PIV.CapUnique(body) && PIV.QuantUnique(body)
    requires la.Lookahead?
    requires bytecode == CP.compile_to_bytecode(body)
    requires 0 <= cp <= |str|
    requires AI.cp_context(cp, str, LAnc.Forward).nextchar == AI.get_char(str, cp)
    requires (forall k :: AI.get_idx(qt.a_cp, k) < 0)
             && (forall k :: AI.get_idx(qt.a_clk, k) >= -1)
    requires |qt.a_cp| == nquant && |qt.a_clk| == nquant
    requires |cap.a_cp| == ncap && |cap.a_clk| == ncap
    requires CM.RegsAgreeInside(lk, AReg.init_regs(nlook), SL)
    ensures
      var result := AI.FFindMatchPlus(bytecode, body, plus_bcv, str, ov, LAnc.Forward, cp, cap, lk, qt, 0, lookcdn).0;
      var rf := AI.FFindMatch(bytecode, str,
                              AI.FInitState(bytecode, cp, AReg.init_regs(ncap), AReg.init_regs(nlook),
                                            AReg.init_regs(nquant), 0, AI.cp_context(cp, str, LAnc.Forward)),
                              ov, LAnc.Forward, lookcdn).0;
      (result.None? <==> rf.None?)
      && (result.Some? ==>
            CM.RegsAgreeInside(result.value.look_regs, rf.value.look_regs, SL))
  {
    var dir := LAnc.Forward;
    var ctxc := AI.cp_context(cp, str, dir);
    var inits := AI.FInitState(bytecode, cp, cap, lk, qt, 0, ctxc);
    NoTrueQuantStampNested(body);
    assert VmQuantFinal(inits) by { assert QuantRegsFinal(AI.init_thread(cap, lk, qt)); }
    FFindMatchQuantFinalAny(bytecode, str, inits, ov, dir, lookcdn);
    var (fmres, ovx) := AI.FFindMatch(bytecode, str, inits, ov, dir, lookcdn);
    if fmres.Some? {
      FNulledPlusIdentity(body, fmres.value.capture_regs, fmres.value.look_regs, fmres.value.quant_regs,
                          plus_bcv, str, ovx, dir);
    }
    var sf := AI.FInitState(bytecode, cp, AReg.init_regs(ncap), AReg.init_regs(nlook),
                            AReg.init_regs(nquant), 0, ctxc);
    assert CM.VmRelLk(inits, sf, {}, {}, SL) by {
      assert CM.ThreadRelLk(AI.init_thread(cap, lk, qt),
                            AI.init_thread(AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant)),
    {}, {}, SL) by {
        assert CM.RegsAgreeInside(cap, AReg.init_regs(ncap), {});
        assert CM.RegsAgreeInside(qt, AReg.init_regs(nquant), {});
        assert CM.RegsAgreeInside(lk, AReg.init_regs(nlook), SL);
      }
    }
    CM.FFindMatchLookRel(bytecode, str, inits, sf, ov, dir, lookcdn, {}, {}, SL);
  }

  /** L3b: the per-lid BACKWARD replay↔fresh capture agreement — lookbehind twin of
      `ReplayLidCapAgreeFresh`. The `FFindMatchPlus` backward replay from the main
      thread's `cap` (fresh on `CaptureRegs(body)`) agrees, on `CaptureRegs(body)`,
      with the fresh backward `FFindMatch`. `FFindMatchPlus` caps == `FFindMatch`
      caps (reconstruct is identity), then the dir-generic bisimulation
      `ReplayCapAgreeFreshLB`. The bytecode is `compile_to_bytecode(reverse_regex
      (body))`, the reconstruction reg is `body` (the FLookLoop call convention). */
  lemma FreshMatchWf(bytecode: RB.code, str: string, cp: int, ov: LOr.OracleView, cdn: LCdn.cdns,
                     body: R.regex, ncap: int, nlook: int, nquant: int)
    requires NR.LookBehindFragmentRE(body) && PIV.CapUnique(body) && PIV.QuantUnique(body)
    requires NR.NoNulledPlusRE(body)   // §2.5b interim: all stamps false
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
  lemma MainMatchInsideCapsInitNested(re: R.regex, code: RB.code, endl: nat, str: string,
                                      inits: AI.VmState, cap: AReg.Regs, look: AReg.Regs, quant: AReg.Regs,
                                      ov: LOr.OracleView, cdn: LCdn.cdns, result: Option<AI.Thread>)
    requires NR.NestedFragmentRE(re) && PIV.CapUnique(re)
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
          PIV.CaptureWriteIdsOutsideRENested(re, code, 0, endl, pc);
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
    // §2.5b rung D: the fresh best thread carries no stamp (interim gate), so
    // BestMatchRE's reconstruction-aware readout is the plain GmOfLive.
    NoTrueQuantStamp(body);
    FreshBestNoStamps(bodycode, str, cp, ov, cdns, ncap, nlook, nquant);
    var rfB := AI.FFindMatch(bodycode, str,
                             AI.FInitState(bodycode, cp, AReg.init_regs(ncap), AReg.init_regs(nlook),
                                           AReg.init_regs(nquant), 0, AI.cp_context(cp, str, LAnc.Forward)),
                             ov, LAnc.Forward, cdns).0;
    PIV.BestMatchRENoStamps(body, qm, str, bestT, rfB);
    // BodyTreeAtCp:  BestMatchRE(body, bestT, rf) && bestT == FirstLeaf(t, inp)
    //   -> bestT.value.1 == GmOfLive(body, rf.regs), bestT.None? <==> rf.None?
    // ReplayCapAgreeFresh:  ra.None? <==> rf.None? && captures agree on CaptureRegs(body)
  }

  /** §2.5b rung D (2026-11-04): `BestMatchRE` now reads the best thread through
      the reconstruction-aware `PIV.GmOfLiveR`. Under the interim gate the code
      never stamps TRUE, so the fresh run's best thread carries no stamp and the
      readout is the plain `GmOfLive` these consumers were written against. */
  lemma FreshBestNoStamps(bodycode: RB.code, str: string, cp: nat,
                          ov: LOr.OracleView, cdns: LCdn.cdns, ncap: int, nlook: int, nquant: int)
    requires cp <= |str|
    requires forall pc: nat, q: int, b: bool ::
               NR.GetPcRE(bodycode, pc) == Some(RB.SetQuantToClock(q, b)) ==> !b
    ensures var ctxc := AI.cp_context(cp, str, LAnc.Forward);
            var rf := AI.FFindMatch(bodycode, str,
                                    AI.FInitState(bodycode, cp, AReg.init_regs(ncap), AReg.init_regs(nlook),
                                                  AReg.init_regs(nquant), 0, ctxc), ov, LAnc.Forward, cdns).0;
            rf.Some? ==> forall q: int :: AI.get_idx(rf.value.quant_regs.a_cp, q) < 0
  {
    var ctxc := AI.cp_context(cp, str, LAnc.Forward);
    var inits := AI.FInitState(bodycode, cp, AReg.init_regs(ncap), AReg.init_regs(nlook),
                               AReg.init_regs(nquant), 0, ctxc);
    assert ctxc.nextchar == AI.get_char(str, cp);        // cp_context definitional
    var qt := AReg.init_regs(nquant);
    assert forall k :: AI.get_idx(qt.a_cp, k) < 0 by {
      forall k ensures AI.get_idx(qt.a_cp, k) < 0 { if 0 <= k < |qt.a_cp| { assert qt.a_cp[k] == -1; } }
    }
    assert forall k :: AI.get_idx(qt.a_clk, k) >= -1 by {
      forall k ensures AI.get_idx(qt.a_clk, k) >= -1 { if 0 <= k < |qt.a_clk| { assert qt.a_clk[k] == -1; } }
    }
    assert QuantRegsFinal(inits.active[0]);
    assert VmQuantFinal(inits);
    FFindMatchQuantFinalAny(bodycode, str, inits, ov, LAnc.Forward, cdns);
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
  lemma ReplayCapIsBodyLeafNested(rer: LW.RegExpRecord, qm: AR.QMap, body: R.regex, bodycode: RB.code,
                                  endl: nat, ngroups: nat, str: string, cp: nat, cap: AReg.Regs, lk: AReg.Regs,
                                  qt: AReg.Regs, ov: LOr.OracleView, cdns: LCdn.cdns, ncap: int, nlook: int, nquant: int)
    returns (bestT: Option<LT.Leaf>)
    requires PSM.StaticOkNestedRE(qm, body, bodycode, endl)
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
    bestT := BodyTreeAtCpNested(rer, qm, body, bodycode, endl, ngroups, str, cp, ov, cdns, ncap, nlook, nquant);
    ReplayCapAgreeFresh(bodycode, str, cp, cap, lk, qt, ov, cdns, body, ncap, nlook, nquant);
    // §2.5b rung D: the fresh best thread carries no stamp (interim gate), so
    // BestMatchRE's reconstruction-aware readout is the plain GmOfLive.
    NoTrueQuantStampNested(body);
    FreshBestNoStamps(bodycode, str, cp, ov, cdns, ncap, nlook, nquant);
    var rfB := AI.FFindMatch(bodycode, str,
                             AI.FInitState(bodycode, cp, AReg.init_regs(ncap), AReg.init_regs(nlook),
                                           AReg.init_regs(nquant), 0, AI.cp_context(cp, str, LAnc.Forward)),
                             ov, LAnc.Forward, cdns).0;
    PIV.BestMatchRENoStamps(body, qm, str, bestT, rfB);
    // BodyTreeAtCpNested:  BestMatchRE(body, bestT, rf) (fresh) && confined FirstLeaf facts
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

  // ===========================================================================
  // R3b (ADDITIVE): pure-spec VALUE composition for captures defined inside looks.
  //
  // These are the SPEC-tree half of the nested value-reconstruction seam. They
  // isolate how a SINGLE capture group `g` gets its value at the highest-priority
  // leaf of a `TreeRes`, independent of the surrounding group map (`gmMain`) and
  // of the continuation. Two orthogonal facts:
  //   * `TreeResGValueFramed`  -- `g`'s leaf value depends on the incoming map
  //     ONLY through its value AT `g` (changing OTHER groups is irrelevant).
  //   * `TreeResGNotWritten` / `TreeResLkNodeGValue` -- if `g` is written only
  //     inside a look, the value the look CONTRIBUTES flows out to the leaf
  //     unchanged (the continuation, defining `g` nowhere, only threads it).
  // Together: the value of an inner-look `g` at the OUTER leaf equals the owning
  // look's own sub-result at `g` (`LkResult` of that look), which is the last hop
  // of the `recon_inner` chain.
  // ===========================================================================


  // ==========================================================================
  // B' SINGLE-WRITER (ADDITIVE): `GBodyOK`/`GOwnerWF2` for a compiled body tree.
  //
  // The single-writer condition of the corrected descent — along each spine path
  // `g`'s write lives in a UNIQUE look body — is exactly `CapUnique` lifted to the
  // `ComputeTree` walk. The invariant is `GOnceInv`: across the pending action
  // list, `g` is "accounted for" AT MOST ONCE, counting BOTH the defs it still
  // appears in (`multiset(AllDefsActs)[g]`) AND a pending `Aclose(g)` (`g in
  // PendingCloses`) — a `Group(g,·)` moves `g` from the first to the second,
  // preserving the sum. Under `GNotUnderQuantL` (no `g` under a quantifier, so the
  // min>0 unfold does NOT duplicate `g`) the invariant is preserved, and at each
  // `LK` it yields the disjunct: `g in DefGroups(r1)` ⇒ `g` misses the whole
  // continuation (`GNotWrittenComputeTreeActs`), else `g` misses the body.
  // ==========================================================================

  lemma LkReplayMatchesSpecNested(
    rer: LW.RegExpRecord, qm: AR.QMap, body: R.regex, bodycode: RB.code, endl: nat, ngroups: nat,
    str: string, cp: nat, cap: AReg.Regs, lk: AReg.Regs, qt: AReg.Regs, ov: LOr.OracleView,
    cdns: LCdn.cdns, la: R.lookaround, tlk: LT.Tree, gmMain: LG.GroupMap,
    ncap: int, nlook: int, nquant: int)
    requires PSM.StaticOkNestedRE(qm, body, bodycode, endl)
    requires PSM.SizesOkRE(body, ncap, nlook, nquant)
    requires qm.ov == ov
    requires !rer.ignoreCase && !rer.multiline
    requires cp <= |str|
    requires bodycode == CP.compile_to_bytecode(body)
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
            var S := set g | g in L.DefGroups(T.Translate(body)) && g !in LL.LkBodyGroups(T.Translate(body));
            (ra.None? <==> LS.LkResult(T.TrLookaround(la), tlk, gmMain, inp).None?)
            && (ra.Some? ==>
                  LS.LkResult(T.TrLookaround(la), tlk, gmMain, inp).Some?
                  && rf.Some?
                  && CM.RegsAgreeInside(ra.value.capture_regs, rf.value.capture_regs, PIV.CaptureRegs(body))
                  && GmAgreeOn(LS.LkResult(T.TrLookaround(la), tlk, gmMain, inp).value,
                               PIV.GmOfLive(body, rf.value.capture_regs, rf.value.look_regs, rf.value.quant_regs), S))
  {
    var inp := PIV.InpOfCp(str, cp);
    var Sd := set g | g in L.DefGroups(T.Translate(body));
    var Slk := LL.LkBodyGroups(T.Translate(body));
    var S := set g | g in L.DefGroups(T.Translate(body)) && g !in LL.LkBodyGroups(T.Translate(body));
    var tr := T.Translate(body);

    // engine: replay from cap ~ fresh; both == body spec first leaf OUTSIDE Slk.
    var bestT := ReplayCapIsBodyLeafNested(rer, qm, body, bodycode, endl, ngroups, str, cp, cap, lk, qt,
                                           ov, cdns, ncap, nlook, nquant);
    var tEmpty := LFU.ComputeTr(rer, [LS.Areg(tr)], inp, LG.Empty, WP.Forward);
    // ReplayCapIsBodyLeafNested: bestT.None <==> FirstLeaf(tEmpty).None; when Some,
    // bestT.0 == FirstLeaf(tEmpty).0 and GmAgreeOutside(bestT.1, FirstLeaf(tEmpty).1, Slk).

    // tlk (at gmMain) == tEmpty (at Empty): depth-k group-map independence.
    EL.TranslateFragmentPikeLkRec(body);                 // PikeLkRegexRec(tr)
    EL.ComputeTrGmIndepLkRec(rer, tr, inp, gmMain, WP.Forward);
    assert tlk == tEmpty;
    assert LT.FirstLeaf(tlk, inp) == LT.TreeRes(tlk, LG.Empty, inp, WP.Forward);   // definitional

    // spec: TreeRes at gmMain agrees with TreeRes at Empty on Sd (no confinement).
    TreeResGmFrameRec(tlk, gmMain, LG.Empty, inp, WP.Forward, Sd);

    // LkResult of a positive lookAHEAD == TreeRes(tlk, gmMain, inp, Forward) folded.
    assert L.Positivity(T.TrLookaround(la)) && L.LkDir(T.TrLookaround(la)) == WP.Forward;
  }

  /** L4 depth-k (ADDITIVE): the FULL-`DefGroups` value keystone for a nested
      positive lookAHEAD — the recursion target that EXTENDS `LkReplayMatchesSpecNested`
      (agreement OUTSIDE the inner looks) to agreement on the WHOLE `DefGroups(tr)`,
      i.e. ALSO on the captures recorded INSIDE nested look bodies.

      Stated as the honest COMPOSITION over the partition
      `DefGroups(tr) = (DefGroups(tr) \ LkBodyGroups(tr)) ∪ LkBodyGroups(tr)`: the
      OUTER half is discharged INTERNALLY by `LkReplayMatchesSpecNested`; the INNER
      half (`LkBodyGroups(tr)` — the groups sunk inside nested looks) is the explicit
      reconstruction premise `recon_inner`, whose engine reference is a RECONSTRUCTED
      register bank `(reccap, reclk, recqt)` — the depth-k `FLookLoop` output that
      fills in the inner-look captures the fresh body match `rf` leaves UNSET (a
      lookaround compiles to a single `CheckOracle` leaf, so `rf` never records its
      body's inner-look captures). The companion premise `recon_outer` pins that the
      reconstruction leaves the OUTER groups exactly as `rf` (FLookLoop writes only
      inside looks).

      WHY THE ENGINE REFERENCE IS NOT `rf`: for a body that is itself a single
      capturing look (e.g. `(?=(a))`), `LkBodyGroups(tr) == DefGroups(tr)` and the
      fresh body match `rf` sets NONE of those registers — so `GmOfLive(body, rf, …)`
      disagrees with the spec `LkResult` on exactly the inner groups. The values live
      in the reconstructed bank, which the top-level `FLookLoop` fills via the SEPARATE
      iterations for the inner (higher-id) lids. This is why the full keystone is a
      `FLookLoop`-reconstruction statement, not a fresh-match one.

      The two premises are EXACTLY what the recursive depth-k value lift discharges:
      `recon_outer` from the `FLookLoop` capture frame (`FLookLoopCaptureFrame`
      generalized off look-free bodies), and `recon_inner` by applying THIS keystone
      recursively to each of body's inner looks (`NestDepth(inner body) <
      NestDepth(body)`), bridged spec-side by how an outer body leaf records an inner
      look's own leaf and engine-side by the `FLookLoop` reconstruction merge.
      `ReplayLidCapAgreeFreshNested` + `ReplayCapIsBodyLeafNested` supply the
      per-inner-look replay↔fresh↔leaf tie. At `NestDepth(body) == 0` both premises
      are vacuous (`LkBodyGroups(tr) == {}`), so the full keystone holds
      unconditionally — see `LkReplayMatchesSpecNestedFullBase`. */
  lemma LookFreeCapIdsInLooksEmpty(re: R.regex)
    requires NR.LookFreeRE(re)
    ensures PIV.CapIdsInLooks(re) == {}
    decreases re
  {
    match re
    case Re_alt(r1, r2) => LookFreeCapIdsInLooksEmpty(r1); LookFreeCapIdsInLooksEmpty(r2);
    case Re_con(r1, r2) => LookFreeCapIdsInLooksEmpty(r1); LookFreeCapIdsInLooksEmpty(r2);
    case Re_quant(_, _, _, r1) => LookFreeCapIdsInLooksEmpty(r1);
    case Re_capture(_, r1) => LookFreeCapIdsInLooksEmpty(r1);
    case _ =>
  }

  /** L3a extension of `OE.LmOfInv`: threads `CapUnique(re)` to derive the two
      capture-side facts the L3a `FLookLoop` frame/value lift ask of each
      matched lookaround (`LookEntryOk` pins the shared body). */
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

  /** `NoPosLookbehindRE` translates to FORWARD-only positive looks on the L side
      (`TrLookaround` maps Lookahead to a forward positive look; the negatives are
      not positive). Feeds `FirstLeafClosedRec`'s scope. */
/** (G5a-1 P5b) `CapArrayFromRegs` on the top-level fragment: the same proof, the premise widened and its callees
      on their `…Cdn` forms where the argument is the top regex or a non-look subterm of it. */
  lemma CapArrayFromRegsCdn(re: R.regex, thread: AI.Thread, leaf: LT.Leaf, inp: LC.Input,
                         ngroups: nat, ncap: nat, nlook: nat, nquant: nat)
    requires NR.NestedFragmentCdnRE(re)
    requires ClosedGm(leaf.1)
    requires leaf.1 == PIV.NormGm(PIV.GmOfLive(re, thread.capture_regs, thread.look_regs, thread.quant_regs))
    requires CM.ThreadRegsWf(thread, ncap, nlook, nquant)
    requires ncap == 2 * ngroups
    ensures LES.NormalizeArr(AI.filter_reset(re, thread.capture_regs, thread.look_regs, thread.quant_regs, -1))
         == LES.CapArrayOfLeaf(leaf, ngroups)
  {
    var caps := thread.capture_regs;
    var lk := thread.look_regs;
    var qt := thread.quant_regs;
    var f := AI.filter_reset(re, caps, lk, qt, -1);
    var cc := caps.a_clk;
    assert {:split_here} true;
    PIV.FilterCaptureLen(re, caps.a_cp, cc, lk.a_clk, qt.a_clk, -1);
    assert {:split_here} true;
    // (2026-09-05) the size chain, one link per batch with the length lemma
    // supplied explicitly: as a single four-way chain this assert was the
    // 900 s batch of BOTH extraction lemmas.
    PIV.FilterCaptureLen(re, caps.a_cp, caps.a_clk, lk.a_clk, qt.a_clk, -1);
    assert {:split_here} true;
    assert |f| == |caps.a_cp|;
    assert {:split_here} true;
    assert |caps.a_cp| == ncap by { hide *; }        // ThreadRegsWf
    assert {:split_here} true;
    assert ncap == 2 * ngroups;
    // closedness (item 0): `leaf.1 == NormGm(GmOfLive)` and `NormRange` preserves
    // endIdx.Some?, so every present group of GmOfLive is closed. Needed by BOTH
    // the clock-order forall below AND the closed-match forall. (NO `GmOfLiveEqGmOf`
    // here — that needs the clock order the forall below produces.)
    assert {:split_here} true;
    // (2026-09-05) a verbatim restatement of the `requires`; with the whole
    // context unfolded this single assert was a 900 s batch.
    assert leaf.1 == PIV.NormGm(PIV.GmOfLive(re, caps, lk, qt)) by { hide *; }   // requires
    assert {:split_here} true;
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
    assert {:split_here} true;   // (2026-09-05) per-step batch: linear 100-line body, one VC, 900 s+
    forall g: nat | 0 <= g < |f| && AI.get_idx(f, CP.start_reg(g)) >= 0 && AI.get_idx(f, CP.end_reg(g)) >= 0
      ensures AI.get_idx(cc, CP.end_reg(g)) >= AI.get_idx(cc, CP.start_reg(g))
    {
      assert g in PIV.GmOfLive(re, caps, lk, qt);
      assert PIV.GmOfLive(re, caps, lk, qt)[g].endIdx.Some?;
    }
    assert {:split_here} true;
    PIV.GmOfLiveEqGmOf(re, caps, lk, qt);                 // GmOfLive == GmOf (needs the clock order above)
    assert {:split_here} true;
    assert PIV.NormGm(PIV.GmOf(re, caps, lk, qt)) == leaf.1;   // leaf.1 == NormGm(GmOfLive) == NormGm(GmOf)

    // the capture-array bridge
    assert {:split_here} true;   // (2026-09-05) per-step batch: linear 100-line body, one VC, 900 s+
    // (2026-09-05) 900 s batch: the element-wise bound needs only the filter
    // lemma, not the surrounding context.
    forall i | 0 <= i < |f| ensures f[i] >= -1 {
      hide *;                                        // the whole ambient context is dead weight here
      PIV.FilterCaptureGeqNeg1Cdn(re, caps.a_cp, cc, lk.a_clk, qt.a_clk, -1, i);
      assert AI.get_idx(caps.a_cp, i) >= -1;         // CapRegWf
      assert AI.get_idx(f, i) == f[i];
    }
    assert {:split_here} true;   // (2026-09-05) per-step batch: linear 100-line body, one VC, 900 s+
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
    assert {:split_here} true;
    PIV.GmOfCapArrayBridgeNorm(re, caps, lk, qt, inp, ngroups);
    assert {:split_here} true;
    assert LES.NormalizeArr(f)
        == LES.CapArrayOfLeaf((inp, PIV.NormGm(PIV.GmOf(re, caps, lk, qt))), ngroups);
    assert {:split_here} true;
    assert LES.CapArrayOfLeaf((inp, PIV.NormGm(PIV.GmOf(re, caps, lk, qt))), ngroups)
        == LES.CapArrayOfLeaf(leaf, ngroups);
  }

  /** (G5a-1 P5b) The narrow form, as a corollary of `CapArrayFromRegsCdn`. */
  lemma CapArrayFromRegs(re: R.regex, thread: AI.Thread, leaf: LT.Leaf, inp: LC.Input,
                         ngroups: nat, ncap: nat, nlook: nat, nquant: nat)
    requires NR.NestedFragmentRE(re)
    requires ClosedGm(leaf.1)
    requires leaf.1 == PIV.NormGm(PIV.GmOfLive(re, thread.capture_regs, thread.look_regs, thread.quant_regs))
    requires CM.ThreadRegsWf(thread, ncap, nlook, nquant)
    requires ncap == 2 * ngroups
    ensures LES.NormalizeArr(AI.filter_reset(re, thread.capture_regs, thread.look_regs, thread.quant_regs, -1))
         == LES.CapArrayOfLeaf(leaf, ngroups)
  {
    NR.NarrowIsCdn(re);
    hide *;   // the wide premises are this lemma's own: match by name
    CapArrayFromRegsCdn(re, thread, leaf, inp, ngroups, ncap, nlook, nquant);
  }

/** (G5a-1 P5b) `MainExtractionFromClosed` on the top-level fragment: the same proof, the premise widened and its callees
      on their `…Cdn` forms where the argument is the top regex or a non-look subterm of it. */
  lemma MainExtractionFromClosedCdn(raw: R.raw_regex, str: string,
                                 t: LT.Tree, thread: AI.Thread, leaf: LT.Leaf)
    requires NR.NestedFragmentCdnRaw(raw)
    requires ClosedGm(leaf.1)                                   // (L5 F7e-2) closedness IS the scope's only use
    // (2026-09-05) `NegLooksLookFreeRE` dropped: the register half moved to
    // `CapArrayFromRegs` and the remaining body does not use it — which lets
    // `MainExtraction` (LookBehind fragment) delegate here.
    requires T.Latin1Wf(raw)
    requires EL.BoolTreeLk(LES.TheRer(raw), [LS.Areg(LES.SpecRegex(raw))], LC.InitInput(str), BS.CannotExit, t)
    requires LS.IsTree(LES.TheRer(raw), [LS.Areg(LES.SpecRegex(raw))], LC.InitInput(str), LG.Empty, WP.Forward, t)
    requires CM.ThreadRegsWf(thread, 2 * R.max_group(R.annotate(raw)) + 2,
                             R.max_lookaround(R.annotate(raw)) + 1,
                             R.max_quant(R.annotate(raw)) + 1)
    requires QuantClkFinal(thread)   // (G3a) clocks only
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
    hide T.TransWf, NR.PlusFragmentRE, NR.LookBehindFragmentRE, NR.CaptureFreeRE, NR.LookFreeRE, NR.LookBehindFragmentRaw, NR.CaptureFreeRaw, NR.LookFreeRaw, EL.PikeLkRegex, EL.LkGateOk, SD.GroupFreeL, R.annotate, R.max_group, R.max_lookaround, R.max_quant;   // (2026-09-05) recursive + mentioned everywhere: their unfolding is the matching loop
    var ast := R.annotate(raw);
    var re := R.lazy_prefix(ast);
    var rer := LES.TheRer(raw);
    var inp := LC.InitInput(str);
    var ngroups := LES.NGroups(raw);
    var ncap := 2 * R.max_group(ast) + 2;
    assert {:split_here} true;
    T.AnnotateWf(raw);
    assert {:split_here} true;
    NR.SpecRegexNestedFragmentCdn(raw);
    var caps := thread.capture_regs;
    var lk := thread.look_regs;
    var qt := thread.quant_regs;
    assert {:split_here} true;
    assert LES.SpecRegex(raw) == T.Translate(re);


    // live == plain denotation on the closed leaf
    assert {:split_here} true;
    var f := AI.filter_reset(re, caps, lk, qt, -1);
    var cc := caps.a_clk;
    // the core's size precondition gets its OWN batch (inline it was 900 s)
    assert ncap == 2 * ngroups;
    assert {:split_here} true;
    // (2026-09-05) the register/filter half is its own lemma — see CapArrayFromRegs.
    // Its preconditions are asserted ONE PER BATCH first: matched against the
    // ambient context all at once, the call site alone was a 900 s batch.
    assert NR.NestedFragmentCdnRE(re);   // (G5a-1 P5b) the top-level fragment
    assert {:split_here} true;
    assert ClosedGm(leaf.1);
    assert {:split_here} true;
    assert leaf.1 == PIV.NormGm(PIV.GmOfLive(re, thread.capture_regs, thread.look_regs, thread.quant_regs));
    assert {:split_here} true;
    assert CM.ThreadRegsWf(thread, ncap, R.max_lookaround(ast) + 1, R.max_quant(ast) + 1);
    assert {:split_here} true;
    CapArrayFromRegsCdn(re, thread, leaf, inp, ngroups, ncap,
                     R.max_lookaround(ast) + 1, R.max_quant(ast) + 1);
    assert {:split_here} true;
    assert LES.NormalizeArr(f) == LES.CapArrayOfLeaf(leaf, ngroups);

    // the lazy prefix is filter-transparent
    assert {:split_here} true;
    assert AI.get_idx(qt.a_clk, 0) >= -1;         // QuantRegsFinal
    assert {:split_here} true;
    FilterResetLazyPrefix(ast, caps, lk, qt);
    assert {:split_here} true;
    assert AI.filter_reset(ast, caps, lk, qt, -1) == f;

    assert {:split_here} true;
    assert LES.Normalize(AI.FFullMatch(raw, str)) == Some(LES.NormalizeArr(f));
    assert {:split_here} true;
    assert LES.MatcherSpec(raw, str, Some(LES.CapArrayOfLeaf(leaf, ngroups)));
  }

  /** (G5a-1 P5b) The narrow form, as a corollary of `MainExtractionFromClosedCdn`. */
  lemma MainExtractionFromClosed(raw: R.raw_regex, str: string,
                                 t: LT.Tree, thread: AI.Thread, leaf: LT.Leaf)
    requires NR.NestedFragmentRaw(raw)
    requires ClosedGm(leaf.1)                                   // (L5 F7e-2) closedness IS the scope's only use
    // (2026-09-05) `NegLooksLookFreeRE` dropped: the register half moved to
    // `CapArrayFromRegs` and the remaining body does not use it — which lets
    // `MainExtraction` (LookBehind fragment) delegate here.
    requires T.Latin1Wf(raw)
    requires EL.BoolTreeLk(LES.TheRer(raw), [LS.Areg(LES.SpecRegex(raw))], LC.InitInput(str), BS.CannotExit, t)
    requires LS.IsTree(LES.TheRer(raw), [LS.Areg(LES.SpecRegex(raw))], LC.InitInput(str), LG.Empty, WP.Forward, t)
    requires CM.ThreadRegsWf(thread, 2 * R.max_group(R.annotate(raw)) + 2,
                             R.max_lookaround(R.annotate(raw)) + 1,
                             R.max_quant(R.annotate(raw)) + 1)
    requires QuantClkFinal(thread)   // (G3a) clocks only
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
    NR.NarrowIsCdnRaw(raw);
    hide *;   // the callee's premises are this lemma's own, verbatim: match them by name, unfold nothing
    MainExtractionFromClosedCdn(raw, str, t, thread, leaf);
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

  /** R1 #4 (VBody bridge): the table-view body `VBody(crv, l)` is exactly the
      structural body `LookBodyOfRE(r, l)`. `LookTablesOk` records a
      `LookEntryOk` row at every look node (via `NI.LookBodyOfTablesTie`); that
      row pins `crv.f_look_ast[l] == LookBodyOfRE(r, l)` and `0 <= l < |f_look_ast|`,
      so the `VBody` lookup returns exactly that body. */
  lemma CaptureWriteIdsOutsideREGen(re: R.regex, code: RB.code, start: nat, endl: nat, pc: nat)
    requires PIV.CapUnique(re)
    requires NR.NfaRepRE(re, code, start, endl)
    requires start <= pc < endl
    ensures NR.GetPcRE(code, pc).Some? && NR.GetPcRE(code, pc).value.SetRegisterToCP? ==>
              NR.GetPcRE(code, pc).value.reg in PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(re))
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
        CaptureWriteIdsOutsideREGen(r1, code, start + 1, e1, pc);
        PIV.CaptureRegsSetMono(PIV.CapIdsOutsideLooks(r1), PIV.CapIdsOutsideLooks(re));
      } else if pc == e1 {
      } else {
        CaptureWriteIdsOutsideREGen(r2, code, e1 + 1, endl, pc);
        PIV.CaptureRegsSetMono(PIV.CapIdsOutsideLooks(r2), PIV.CapIdsOutsideLooks(re));
      }
    case Re_con(r1, r2) =>
      var e1: nat :| NR.NfaRepRE(r1, code, start, e1) && NR.NfaRepRE(r2, code, e1, endl);
      NR.NfaRepIncrRE(r1, code, start, e1);
      NR.NfaRepIncrRE(r2, code, e1, endl);
      if pc < e1 {
        CaptureWriteIdsOutsideREGen(r1, code, start, e1, pc);
        PIV.CaptureRegsSetMono(PIV.CapIdsOutsideLooks(r1), PIV.CapIdsOutsideLooks(re));
      } else {
        CaptureWriteIdsOutsideREGen(r2, code, e1, endl, pc);
        PIV.CaptureRegsSetMono(PIV.CapIdsOutsideLooks(r2), PIV.CapIdsOutsideLooks(re));
      }
    case Re_capture(cid, r1) =>
      var e1: nat :| NR.GetPcRE(code, start) == Some(RB.SetRegisterToCP(CP.start_reg(cid)))
                     && NR.NfaRepRE(r1, code, start + 1, e1)
                     && NR.GetPcRE(code, e1) == Some(RB.SetRegisterToCP(CP.end_reg(cid)))
                     && endl == e1 + 1;
      NR.NfaRepIncrRE(r1, code, start + 1, e1);
      assert cid >= 0 && (cid as nat) in PIV.CapIdsOutsideLooks(re);   // CapUnique; Re_capture adds it outside
      if pc == start {
        assert CP.start_reg(cid) in PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(re));
      } else if pc < e1 {
        CaptureWriteIdsOutsideREGen(r1, code, start + 1, e1, pc);
        PIV.CaptureRegsSetMono(PIV.CapIdsOutsideLooks(r1), PIV.CapIdsOutsideLooks(re));
      } else {
        assert CP.end_reg(cid) in PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(re));
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
          CaptureWriteIdsOutsideREGen(r1, code, start + 3, e1, pc);
        } else {
        }
      } else if q.max.Some? {
        var em := NR.NfaRepREQuantInv(nul, qid, q, r1, code, start, endl);
        NR.NfaRepIncrMinRE(q.min as nat, qid, r1, code, start, em);
        NR.NfaRepIncrOptRE((q.max.value - q.min) as nat, q.greedy, qid, r1, code, em, endl);
        if pc < em {
          CaptureWriteIdsOutsideMinREGen(q.min as nat, qid, r1, code, start, em, pc);
        } else {
          CaptureWriteIdsOutsideOptREGen((q.max.value - q.min) as nat, q.greedy, qid, r1, code, em, endl, pc);
        }
      } else if nul != R.NonNullable && !q.greedy {
        // §2.5a GENERIC: min forced copies then the star loop; the loop's own
        // five instructions (Fork/SetQuantToClock/BeginLoop at em..em+2,
        // EndLoop/Jmp at e1..e1+1) are all of the harmless kind
        var em, e1 := NR.NfaRepREGenInv(nul, qid, q, r1, code, start, endl);
        NR.NfaRepIncrMinRE(q.min as nat, qid, r1, code, start, em);
        NR.NfaRepIncrRE(r1, code, em + 3, e1);
        if pc < em {
          CaptureWriteIdsOutsideMinREGen(q.min as nat, qid, r1, code, start, em, pc);
        } else if pc <= em + 2 {
        } else if pc < e1 {
          CaptureWriteIdsOutsideREGen(r1, code, em + 3, e1, pc);
        } else {
        }
      } else if nul == R.CINullable {
        // §2.5b CIN-GREEDY: min-1 forced copies, then the stamped end-fork
        // loop; its six own instructions are all of the harmless kind
        var em, e1 := NR.NfaRepRECinInv(nul, qid, q, r1, code, start, endl);
        NR.NfaRepIncrMinRE((q.min - 1) as nat, qid, r1, code, start, em);
        NR.NfaRepIncrRE(r1, code, em + 3, e1);
        if pc < em {
          CaptureWriteIdsOutsideMinREGen((q.min - 1) as nat, qid, r1, code, start, em, pc);
        } else if pc <= em + 2 {
        } else if pc < e1 {
          CaptureWriteIdsOutsideREGen(r1, code, em + 3, e1, pc);
        } else {
        }
      } else if nul == R.CDNullable {
        // §2.5b CDN-GREEDY (G5a): min-1 forced copies, then the stamped end-fork
        // loop; its six own instructions are all of the harmless kind
        var em, e1 := NR.NfaRepRECdnInv(nul, qid, q, r1, code, start, endl);
        NR.NfaRepIncrMinRE((q.min - 1) as nat, qid, r1, code, start, em);
        NR.NfaRepIncrRE(r1, code, em + 3, e1);
        if pc < em {
          CaptureWriteIdsOutsideMinREGen((q.min - 1) as nat, qid, r1, code, start, em, pc);
        } else if pc <= em + 2 {
        } else if pc < e1 {
          CaptureWriteIdsOutsideREGen(r1, code, em + 3, e1, pc);
        } else {
        }
      } else {
        var em, e1 := NR.NfaRepREPlusInv(nul, qid, q, r1, code, start, endl);
        NR.NfaRepIncrMinRE((q.min - 1) as nat, qid, r1, code, start, em);
        NR.NfaRepIncrRE(r1, code, em + 1, e1);
        if pc < em {
          CaptureWriteIdsOutsideMinREGen((q.min - 1) as nat, qid, r1, code, start, em, pc);
        } else if pc == em {
        } else if pc < e1 {
          CaptureWriteIdsOutsideREGen(r1, code, em + 1, e1, pc);
        } else {
        }
      }
  }

  lemma CaptureWriteIdsOutsideMinREGen(k: nat, qid: R.quantid, r1: R.regex, code: RB.code, start: nat, endl: nat, pc: nat)
    requires PIV.CapUnique(r1)
    requires NR.NfaRepMinRE(k, qid, r1, code, start, endl)
    requires start <= pc < endl
    ensures NR.GetPcRE(code, pc).Some? && NR.GetPcRE(code, pc).value.SetRegisterToCP? ==>
              NR.GetPcRE(code, pc).value.reg in PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(r1))
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
      CaptureWriteIdsOutsideREGen(r1, code, start + 1, e1, pc);
    } else {
      CaptureWriteIdsOutsideMinREGen(k - 1, qid, r1, code, e1, endl, pc);
    }
  }

  lemma CaptureWriteIdsOutsideOptREGen(k: nat, greedy: bool, qid: R.quantid, r1: R.regex, code: RB.code, start: nat, endl: nat, pc: nat)
    requires PIV.CapUnique(r1)
    requires NR.NfaRepOptRE(k, greedy, qid, r1, code, start, endl)
    requires start <= pc < endl
    ensures NR.GetPcRE(code, pc).Some? && NR.GetPcRE(code, pc).value.SetRegisterToCP? ==>
              NR.GetPcRE(code, pc).value.reg in PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(r1))
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
      CaptureWriteIdsOutsideREGen(r1, code, start + 3, e1, pc);
    } else if pc == e1 {
    } else {
      CaptureWriteIdsOutsideOptREGen(k - 1, greedy, qid, r1, code, e1 + 1, endl, pc);
    }
  }

  /** R2: nested twin of `CM.CaptureBytecodeClassifiedOutside` — a NESTED body's
      compiled bytecode writes captures only to its OUTSIDE-look registers.
      `NR.CompileToBytecodeRepNested` supplies the `NfaRepRE` (and the `Accept`
      terminator), and `CaptureWriteIdsOutsideREGen` discharges every body pc. */
/** (G5a-1 P5b) `CaptureBytecodeClassifiedNestedOuter` on the top-level fragment: the same proof, the premise widened and its callees
      on their `…Cdn` forms where the argument is the top regex or a non-look subterm of it. */
  lemma CaptureBytecodeClassifiedCdnOuter(body: R.regex)
    requires NR.NestedFragmentCdnRE(body) && PIV.CapUnique(body)
    ensures CM.CaptureWritesInside(CP.compile_to_bytecode(body),
                                   PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(body)))
  {
    var code := CP.compile_to_bytecode(body);
    var next := CP.compile(body, 0, CP.Progress).1;
    NR.CompileToBytecodeRepCdn(body);
    var endl := next as nat;
    var Sc := PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(body));
    forall pc: nat | pc < |code|
      ensures code[pc].SetRegisterToCP? ==> code[pc].reg in Sc
    {
      assert NR.GetPcRE(code, pc) == Some(code[pc]);
      if pc < endl {
        CaptureWriteIdsOutsideREGen(body, code, 0, endl, pc);
      } else {
        assert pc == endl;
        assert NR.GetPcRE(code, endl) == Some(RB.Accept);
      }
    }
  }

  /** (G5a-1 P5b) The narrow form, as a corollary of `CaptureBytecodeClassifiedCdnOuter`. */
  lemma CaptureBytecodeClassifiedNestedOuter(body: R.regex)
    requires NR.NestedFragmentRE(body) && PIV.CapUnique(body)
    ensures CM.CaptureWritesInside(CP.compile_to_bytecode(body),
                                   PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(body)))
  {
    NR.NarrowIsCdn(body);
    hide *;   // the wide premises are this lemma's own: match by name
    CaptureBytecodeClassifiedCdnOuter(body);
  }

  /** R2: nested twin of `ReplayCaptureFrame`, restricted to OUTER caps. For a
      capturing positive lookAHEAD replay over a NESTED body's compiled block
      (run FORWARD), the `FFindMatch` result's capture bank agrees with `cap`
      OUTSIDE the body's OUTSIDE-look registers `CaptureRegsSet(CapIdsOutside
      Looks(body))`. The inner looks are single CheckOracle leaves (no capture
      writes), so no inner-look register is touched here. Built from the
      outer-caps capture-write classification + `CM.FFindMatchCapWriteFrame`. */
  lemma ReplayCaptureFrameNestedOuter(bytecode: RB.code, str: string, inits: AI.VmState, ov: LOr.OracleView,
                                      dir: LAnc.direction, lookcdn: LCdn.cdns,
                                      cap: AReg.Regs, lk: AReg.Regs, qt: AReg.Regs,
                                      la: R.lookaround, body: R.regex)
    requires NR.NestedFragmentRE(body) && PIV.CapUnique(body)
    requires la.Lookahead? && dir == LAnc.Forward
    requires bytecode == CP.compile_to_bytecode(body)
    requires inits.active == [AI.init_thread(cap, lk, qt)]
    requires inits.blocked == [] && inits.bestmatch.None?
    requires |inits.processed.true_set| == RB.size(bytecode)
             && |inits.processed.false_set| == RB.size(bytecode)
    requires inits.context.nextchar == AI.get_char(str, inits.cp)
    ensures var r := AI.FFindMatch(bytecode, str, inits, ov, dir, lookcdn).0;
            r.Some? ==> CM.RegsAgreeOutside(r.value.capture_regs, cap,
                                            PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(body)))
  {
    var Sc := PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(body));
    CaptureBytecodeClassifiedNestedOuter(body);
    assert CM.VmCapturesAgree(inits, cap, Sc) by {
      assert CM.RegsAgreeOutside(cap, cap, Sc);
    }
    CM.FFindMatchCapWriteFrame(bytecode, str, inits, ov, dir, lookcdn, cap, Sc);
  }

  /** R2: nested twin of `ReplayPlusCaptureFrame`, restricted to OUTER caps. The
      `FFindMatchPlus` capturing lookAHEAD replay over a NESTED body writes its
      capture bank only inside the body's OUTSIDE-look registers. The plus
      reconstruction is the identity on the `QuantRegsFinal` result
      (`FNulledPlusIdentity`, since `NoTrueQuantStampNested` + `FFindMatchQuant
      FinalAny` give a quant-final result), so the `FFindMatchPlus` capture bank
      IS the `FFindMatch` one, which `ReplayCaptureFrameNestedOuter` frames. */
  lemma ReplayPlusCaptureFrameNestedOuter(bytecode: RB.code, str: string, ov: LOr.OracleView, dir: LAnc.direction,
                                          lookcdn: LCdn.cdns, plus_bcv: seq<RB.code>, cp: int,
                                          cap: AReg.Regs, lk: AReg.Regs, qt: AReg.Regs, la: R.lookaround, body: R.regex)
    requires NR.NestedFragmentRE(body) && PIV.CapUnique(body) && PIV.QuantUnique(body)
    requires NR.NoNulledPlusRE(body)   // §2.5b interim: all stamps false
    requires la.Lookahead? && dir == LAnc.Forward
    requires bytecode == CP.compile_to_bytecode(body)
    requires AI.cp_context(cp, str, dir).nextchar == AI.get_char(str, cp)
    requires (forall k :: AI.get_idx(qt.a_cp, k) < 0)
             && (forall k :: AI.get_idx(qt.a_clk, k) >= -1)
    ensures var r := AI.FFindMatchPlus(bytecode, body, plus_bcv, str, ov, dir, cp, cap, lk, qt, 0, lookcdn).0;
            r.Some? ==> CM.RegsAgreeOutside(r.value.capture_regs, cap,
                                            PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(body)))
  {
    var inits := AI.FInitState(bytecode, cp, cap, lk, qt, 0, AI.cp_context(cp, str, dir));
    ReplayCaptureFrameNestedOuter(bytecode, str, inits, ov, dir, lookcdn, cap, lk, qt, la, body);
    NoTrueQuantStampNested(body);
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

  // ==========================================================================
  // R2 (look-bank side): a NESTED body's replay CROSSES its inner CheckOracle
  // gates and WRITES their look_regs a_cp entries -- so, unlike a look-free
  // body, the look bank does NOT pass through. The tightest true frame is that
  // the replay writes look entries only for the body's OWN look ids
  // (`LTB.LookIds(body)`), leaving every other look (in particular the outer
  // gates set by the main pass) untouched. Built exactly like the capture side:
  // a fragment-agnostic `LookChecksInside` classification + `CM.FFindMatch
  // LookFrame`. `LookCheckIdsREGen` mirrors `PIV.LookCheckIdsRE` with the
  // fragment hypothesis dropped for `NfaRepRE` + `LookUnique`.
  // ==========================================================================

  /** The int-lid image of `body`'s look ids -- the register indices a replay of
      `body` may touch in the look bank. */
  ghost function LookIdSet(body: R.regex): set<int> {
    set l: nat | l in LTB.LookIds(body) :: l as int
  }

  /** Fragment-agnostic twin of `PIV.LookCheckIdsRE`: every `CheckOracle`/
      `NegCheckOracle` in a block representing `re` (`NfaRepRE`) targets one of
      `re`'s own look ids. Verbatim structural recursion; the fragment hypothesis
      is unused (the `Re_lookaround` leaf carries only its own lid). */
  lemma LookCheckIdsREGen(re: R.regex, code: RB.code, start: nat, endl: nat, pc: nat)
    requires LTB.LookUnique(re)
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
      assert pc == start;
      assert lid >= 0;
    case Re_alt(r1, r2) =>
      var e1: nat :| NR.GetPcRE(code, start) == Some(RB.Fork(start + 1, e1 + 1))
                     && NR.NfaRepRE(r1, code, start + 1, e1)
                     && NR.GetPcRE(code, e1) == Some(RB.Jmp(endl))
                     && NR.NfaRepRE(r2, code, e1 + 1, endl);
      NR.NfaRepIncrRE(r1, code, start + 1, e1);
      NR.NfaRepIncrRE(r2, code, e1 + 1, endl);
      if pc == start {
      } else if pc < e1 {
        LookCheckIdsREGen(r1, code, start + 1, e1, pc);
      } else if pc == e1 {
      } else {
        LookCheckIdsREGen(r2, code, e1 + 1, endl, pc);
      }
    case Re_con(r1, r2) =>
      var e1: nat :| NR.NfaRepRE(r1, code, start, e1) && NR.NfaRepRE(r2, code, e1, endl);
      NR.NfaRepIncrRE(r1, code, start, e1);
      NR.NfaRepIncrRE(r2, code, e1, endl);
      if pc < e1 {
        LookCheckIdsREGen(r1, code, start, e1, pc);
      } else {
        LookCheckIdsREGen(r2, code, e1, endl, pc);
      }
    case Re_capture(cid, r1) =>
      var e1: nat :| NR.GetPcRE(code, start) == Some(RB.SetRegisterToCP(CP.start_reg(cid)))
                     && NR.NfaRepRE(r1, code, start + 1, e1)
                     && NR.GetPcRE(code, e1) == Some(RB.SetRegisterToCP(CP.end_reg(cid)))
                     && endl == e1 + 1;
      NR.NfaRepIncrRE(r1, code, start + 1, e1);
      if pc == start {
      } else if pc < e1 {
        LookCheckIdsREGen(r1, code, start + 1, e1, pc);
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
          LookCheckIdsREGen(r1, code, start + 3, e1, pc);
        } else {
        }
      } else if q.max.Some? {
        var em := NR.NfaRepREQuantInv(nul, qid, q, r1, code, start, endl);
        NR.NfaRepIncrMinRE(q.min as nat, qid, r1, code, start, em);
        NR.NfaRepIncrOptRE((q.max.value - q.min) as nat, q.greedy, qid, r1, code, em, endl);
        if pc < em {
          LookCheckIdsMinREGen(q.min as nat, qid, r1, code, start, em, pc);
        } else {
          LookCheckIdsOptREGen((q.max.value - q.min) as nat, q.greedy, qid, r1, code, em, endl, pc);
        }
      } else if nul != R.NonNullable && !q.greedy {
        // §2.5a GENERIC: min forced copies then the star loop; the loop's own
        // five instructions (Fork/SetQuantToClock/BeginLoop at em..em+2,
        // EndLoop/Jmp at e1..e1+1) are all of the harmless kind
        var em, e1 := NR.NfaRepREGenInv(nul, qid, q, r1, code, start, endl);
        NR.NfaRepIncrMinRE(q.min as nat, qid, r1, code, start, em);
        NR.NfaRepIncrRE(r1, code, em + 3, e1);
        if pc < em {
          LookCheckIdsMinREGen(q.min as nat, qid, r1, code, start, em, pc);
        } else if pc <= em + 2 {
        } else if pc < e1 {
          LookCheckIdsREGen(r1, code, em + 3, e1, pc);
        } else {
        }
      } else if nul == R.CINullable {
        // §2.5b CIN-GREEDY: min-1 forced copies, then the stamped end-fork
        // loop; its six own instructions are all of the harmless kind
        var em, e1 := NR.NfaRepRECinInv(nul, qid, q, r1, code, start, endl);
        NR.NfaRepIncrMinRE((q.min - 1) as nat, qid, r1, code, start, em);
        NR.NfaRepIncrRE(r1, code, em + 3, e1);
        if pc < em {
          LookCheckIdsMinREGen((q.min - 1) as nat, qid, r1, code, start, em, pc);
        } else if pc <= em + 2 {
        } else if pc < e1 {
          LookCheckIdsREGen(r1, code, em + 3, e1, pc);
        } else {
        }
      } else if nul == R.CDNullable {
        // §2.5b CDN-GREEDY (G5a): min-1 forced copies, then the stamped end-fork
        // loop; its six own instructions are all of the harmless kind
        var em, e1 := NR.NfaRepRECdnInv(nul, qid, q, r1, code, start, endl);
        NR.NfaRepIncrMinRE((q.min - 1) as nat, qid, r1, code, start, em);
        NR.NfaRepIncrRE(r1, code, em + 3, e1);
        if pc < em {
          LookCheckIdsMinREGen((q.min - 1) as nat, qid, r1, code, start, em, pc);
        } else if pc <= em + 2 {
        } else if pc < e1 {
          LookCheckIdsREGen(r1, code, em + 3, e1, pc);
        } else {
        }
      } else {
        var em, e1 := NR.NfaRepREPlusInv(nul, qid, q, r1, code, start, endl);
        NR.NfaRepIncrMinRE((q.min - 1) as nat, qid, r1, code, start, em);
        NR.NfaRepIncrRE(r1, code, em + 1, e1);
        if pc < em {
          LookCheckIdsMinREGen((q.min - 1) as nat, qid, r1, code, start, em, pc);
        } else if pc == em {
        } else if pc < e1 {
          LookCheckIdsREGen(r1, code, em + 1, e1, pc);
        } else {
        }
      }
  }

  lemma LookCheckIdsMinREGen(k: nat, qid: R.quantid, r1: R.regex, code: RB.code, start: nat, endl: nat, pc: nat)
    requires LTB.LookUnique(r1)
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
      LookCheckIdsREGen(r1, code, start + 1, e1, pc);
    } else {
      LookCheckIdsMinREGen(k - 1, qid, r1, code, e1, endl, pc);
    }
  }

  lemma LookCheckIdsOptREGen(k: nat, greedy: bool, qid: R.quantid, r1: R.regex, code: RB.code, start: nat, endl: nat, pc: nat)
    requires LTB.LookUnique(r1)
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
      LookCheckIdsREGen(r1, code, start + 3, e1, pc);
    } else if pc == e1 {
    } else {
      LookCheckIdsOptREGen(k - 1, greedy, qid, r1, code, e1 + 1, endl, pc);
    }
  }

  /** R2: `LookChecksInside(compile_to_bytecode(body), LookIdSet(body))` for a
      NESTED body -- every gate the replay executes targets one of `body`'s own
      look ids. Nested twin of the capture-side `CaptureBytecodeClassifiedNested
      Outer`, via `LookCheckIdsREGen`. */
/** (G5a-1 P5b) `LookBytecodeClassifiedNested` on the top-level fragment: the same proof, the premise widened and its callees
      on their `…Cdn` forms where the argument is the top regex or a non-look subterm of it. */
  lemma LookBytecodeClassifiedCdn(body: R.regex)
    requires NR.NestedFragmentCdnRE(body) && LTB.LookUnique(body)
    ensures CM.LookChecksInside(CP.compile_to_bytecode(body), LookIdSet(body))
  {
    var code := CP.compile_to_bytecode(body);
    var next := CP.compile(body, 0, CP.Progress).1;
    NR.CompileToBytecodeRepCdn(body);
    var endl := next as nat;
    var S := LookIdSet(body);
    forall pc: nat | pc < |code|
      ensures (code[pc].CheckOracle? ==> code[pc].col in S)
              && (code[pc].NegCheckOracle? ==> code[pc].ncl in S)
    {
      assert NR.GetPcRE(code, pc) == Some(code[pc]);
      if pc < endl {
        LookCheckIdsREGen(body, code, 0, endl, pc);
      } else {
        assert pc == endl;
        assert NR.GetPcRE(code, endl) == Some(RB.Accept);
      }
    }
  }

  /** (G5a-1 P5b) The narrow form, as a corollary of `LookBytecodeClassifiedCdn`. */
  lemma LookBytecodeClassifiedNested(body: R.regex)
    requires NR.NestedFragmentRE(body) && LTB.LookUnique(body)
    ensures CM.LookChecksInside(CP.compile_to_bytecode(body), LookIdSet(body))
  {
    NR.NarrowIsCdn(body);
    hide *;   // the wide premises are this lemma's own: match by name
    LookBytecodeClassifiedCdn(body);
  }

  /** R2: the FFindMatchPlus-level look frame for a NESTED positive lookAHEAD
      replay: the result's look bank agrees with the incoming `lk` OUTSIDE the
      body's own look ids `LookIdSet(body)`. So the replay only ADDS inner-look
      a_cp entries (its own gates) and never disturbs any look outside the body
      -- in particular the outer gates the main pass recorded. Structure mirrors
      `ReplayPlusCaptureFrameNestedOuter`: the FFindMatch look frame
      (`LookBytecodeClassifiedNested` + `CM.FFindMatchLookFrame`) plus the plus
      reconstruction identity (`FNulledPlusIdentity` leaves the look bank fixed). */
  lemma ReplayPlusLookFrameNested(bytecode: RB.code, str: string, ov: LOr.OracleView, dir: LAnc.direction,
                                  lookcdn: LCdn.cdns, plus_bcv: seq<RB.code>, cp: int,
                                  cap: AReg.Regs, lk: AReg.Regs, qt: AReg.Regs, la: R.lookaround, body: R.regex)
    requires NR.NestedFragmentRE(body) && PIV.CapUnique(body) && PIV.QuantUnique(body) && LTB.LookUnique(body)
    requires NR.NoNulledPlusRE(body)   // §2.5b interim: all stamps false
    requires la.Lookahead? && dir == LAnc.Forward
    requires bytecode == CP.compile_to_bytecode(body)
    requires AI.cp_context(cp, str, dir).nextchar == AI.get_char(str, cp)
    requires (forall k :: AI.get_idx(qt.a_cp, k) < 0)
             && (forall k :: AI.get_idx(qt.a_clk, k) >= -1)
    ensures var r := AI.FFindMatchPlus(bytecode, body, plus_bcv, str, ov, dir, cp, cap, lk, qt, 0, lookcdn).0;
            r.Some? ==> CM.RegsAgreeOutside(r.value.look_regs, lk, LookIdSet(body))
  {
    var inits := AI.FInitState(bytecode, cp, cap, lk, qt, 0, AI.cp_context(cp, str, dir));
    LookBytecodeClassifiedNested(body);
    assert CM.VmLooksAgree(inits, lk, LookIdSet(body)) by {
      assert CM.RegsAgreeOutside(lk, lk, LookIdSet(body));
    }
    CM.FFindMatchLookFrame(bytecode, str, inits, ov, dir, lookcdn, lk, LookIdSet(body));
    NoTrueQuantStampNested(body);
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

  /** recon A: the TIGHT twin of `ReplayPlusLookFrameNested`. The replay's main
      pass `compile_to_bytecode(body)` gates ONLY on `body`'s DIRECT (top-level)
      look ids (`DirectLidClassified`), so the result look bank agrees with the
      incoming `lk` OUTSIDE `DirectLidSet(body)` -- strictly tighter than
      `LookIdSet(body)`. This is the frame that makes the (f) look-stability
      invariant re-establishable at ALL nesting depths: a newly-set look id is a
      DIRECT child of `body`, never a grandchild. Verbatim clone of
      `ReplayPlusLookFrameNested` with `LookBytecodeClassifiedNested`/`LookIdSet`
      replaced by `DirectLidClassified`/`DirectLidSet`. */
  lemma ReplayPlusLookFrameDirectNested(bytecode: RB.code, str: string, ov: LOr.OracleView, dir: LAnc.direction,
                                        lookcdn: LCdn.cdns, plus_bcv: seq<RB.code>, cp: int,
                                        cap: AReg.Regs, lk: AReg.Regs, qt: AReg.Regs, la: R.lookaround, body: R.regex)
    requires NR.NestedFragmentRE(body) && PIV.CapUnique(body) && PIV.QuantUnique(body) && LTB.LookUnique(body)
    requires NR.NoNulledPlusRE(body)   // §2.5b interim: all stamps false
    requires la.Lookahead? && dir == LAnc.Forward
    requires bytecode == CP.compile_to_bytecode(body)
    requires AI.cp_context(cp, str, dir).nextchar == AI.get_char(str, cp)
    requires (forall k :: AI.get_idx(qt.a_cp, k) < 0)
             && (forall k :: AI.get_idx(qt.a_clk, k) >= -1)
    ensures var r := AI.FFindMatchPlus(bytecode, body, plus_bcv, str, ov, dir, cp, cap, lk, qt, 0, lookcdn).0;
            r.Some? ==> CM.RegsAgreeOutside(r.value.look_regs, lk, DirectLidSet(body))
  {
    var inits := AI.FInitState(bytecode, cp, cap, lk, qt, 0, AI.cp_context(cp, str, dir));
    DirectLidClassified(body);
    assert CM.VmLooksAgree(inits, lk, DirectLidSet(body)) by {
      assert CM.RegsAgreeOutside(lk, lk, DirectLidSet(body));
    }
    CM.FFindMatchLookFrame(bytecode, str, inits, ov, dir, lookcdn, lk, DirectLidSet(body));
    NoTrueQuantStampNested(body);
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

  /** R2: every look id of `re` has a correct table row, given `re`'s rows are
      all correct (`LookTablesOk`). Lets a body's replay-set inner-look id be
      resolved to a real look entry (with a body in the fragment) so the
      FLookLoop induction can process it downstream. Small structural recursion. */
  lemma LookIdEntryExists(re: R.regex, fc: CP.FCompiled, l: nat)
    requires LTB.LookTablesOk(re, fc)
    requires l in LTB.LookIds(re)
    ensures var li: int := l as int;   // (2026-08-28) cast-free trigger term for the exists
            exists la: R.lookaround, body: R.regex :: LTB.LookEntryOk(fc, li, la, body)
    decreases re
  {
    match re
    case Re_alt(r1, r2) =>
      if l in LTB.LookIds(r1) { LookIdEntryExists(r1, fc, l); } else { LookIdEntryExists(r2, fc, l); }
    case Re_con(r1, r2) =>
      if l in LTB.LookIds(r1) { LookIdEntryExists(r1, fc, l); } else { LookIdEntryExists(r2, fc, l); }
    case Re_quant(_, _, _, r1) => LookIdEntryExists(r1, fc, l);
    case Re_capture(_, r1) => LookIdEntryExists(r1, fc, l);
    case Re_lookaround(lid, la, r1) =>
      if l == lid as nat {
        assert LTB.LookEntryOk(fc, lid, la, r1);   // LookTablesOk's lookaround case
      } else {
        assert l in LTB.LookIds(r1);
        LookIdEntryExists(r1, fc, l);
      }
    case Re_empty => case Re_character(_) => case Re_anchor(_) =>
  }

  /** R2: the FULL per-replay frame the NESTED FLookLoop induction consumes, for
      a positive lookAHEAD replay over a NESTED body. Bundles the outer-caps
      capture frame, the own-look-ids look frame, and quant-finality. Nested twin
      of `ReplayPlusFrame` (which for a look-free body got `look_regs == lk`; a
      nested body instead only ADDS its own inner-look entries). */
  lemma ReplayPlusFrameNested(bytecode: RB.code, str: string, ov: LOr.OracleView, dir: LAnc.direction,
                              lookcdn: LCdn.cdns, plus_bcv: seq<RB.code>, cp: int,
                              cap: AReg.Regs, lk: AReg.Regs, qt: AReg.Regs, la: R.lookaround, body: R.regex)
    requires NR.NestedFragmentRE(body) && PIV.CapUnique(body) && PIV.QuantUnique(body) && LTB.LookUnique(body)
    requires NR.NoNulledPlusRE(body)   // §2.5b interim: all stamps false
    requires la.Lookahead? && dir == LAnc.Forward
    requires bytecode == CP.compile_to_bytecode(body)
    requires AI.cp_context(cp, str, dir).nextchar == AI.get_char(str, cp)
    requires (forall k :: AI.get_idx(qt.a_cp, k) < 0)
             && (forall k :: AI.get_idx(qt.a_clk, k) >= -1)
    ensures var r := AI.FFindMatchPlus(bytecode, body, plus_bcv, str, ov, dir, cp, cap, lk, qt, 0, lookcdn).0;
            r.Some? ==>
              CM.RegsAgreeOutside(r.value.capture_regs, cap, PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(body)))
              && CM.RegsAgreeOutside(r.value.look_regs, lk, LookIdSet(body))
              && QuantRegsFinal(r.value)
  {
    ReplayPlusCaptureFrameNestedOuter(bytecode, str, ov, dir, lookcdn, plus_bcv, cp, cap, lk, qt, la, body);
    ReplayPlusLookFrameNested(bytecode, str, ov, dir, lookcdn, plus_bcv, cp, cap, lk, qt, la, body);
    var inits := AI.FInitState(bytecode, cp, cap, lk, qt, 0, AI.cp_context(cp, str, dir));
    NoTrueQuantStampNested(body);
    assert VmQuantFinal(inits) by {
      assert QuantRegsFinal(AI.init_thread(cap, lk, qt));
    }
    FFindMatchQuantFinalAny(bytecode, str, inits, ov, dir, lookcdn);
    var (res0, ovx) := AI.FFindMatch(bytecode, str, inits, ov, dir, lookcdn);
    if res0.Some? {
      var th := res0.value;
      FNulledPlusIdentity(body, th.capture_regs, th.look_regs, th.quant_regs, plus_bcv, str, ovx, dir);
    }
  }

  /** (G3a) What a lookahead row needs of its body. Opaque: a ground fact in the loops. */
  opaque ghost predicate RowLAStatics(body: R.regex, plus_bcv: seq<RB.code>) {
    NR.NestedFragmentRE(body) && PIV.CapUnique(body) && PIV.QuantUnique(body) && LTB.LookUnique(body)
    && NRC.NoCdnPlusRE(body) && RF.CinBodiesLookFreeRE(body) && NRR.PlusTableOk(body, plus_bcv)
  }

  /** (G3a) Everything the look loops read at a matched LOOKAHEAD row whose body may hold a CIN-greedy
      nulled plus. The incoming quant bank is final, so the replay's `FFindMatch` winner is
      `RegsFinalOk` on the body's CIN quantifiers (`FV.FFindMatchRegsFinal`, as at the top level), and
      `RRA.RowReconAt` says what `FReconstructPlus` does to it. Only the quant conclusion is weaker than
      the stamp-free twins': positions may be set inside `QIdsOuter(body)`. */
  lemma ReplayPlusRowLA(bytecode: RB.code, str: string, ov: LOr.OracleView, lookcdn: LCdn.cdns,
                        plus_bcv: seq<RB.code>, cp: int, cap: AReg.Regs, lk: AReg.Regs, qt: AReg.Regs,
                        body: R.regex, ncap: int, nlook: int, nquant: int)
    requires RowLAStatics(body, plus_bcv)
    requires bytecode == CP.compile_to_bytecode(body)
    requires 0 <= cp <= |str|
    requires ncap >= 0 && nlook >= 0 && nquant >= 0
    requires |cap.a_cp| == ncap && |cap.a_clk| == ncap && PIV.CapRegWf(cap)
    requires |lk.a_cp| == nlook && |lk.a_clk| == nlook && CM.LookCpsLE(lk, |str|)
    requires |qt.a_cp| == nquant && |qt.a_clk| == nquant
    requires (forall k :: AI.get_idx(qt.a_cp, k) < 0) && (forall k :: AI.get_idx(qt.a_clk, k) >= -1)
    ensures var rr := AI.FFindMatchPlus(bytecode, body, plus_bcv, str, ov, LAnc.Forward,
                                        cp, cap, lk, qt, 0, lookcdn);
            var r := rr.0;
            rr.1 == ov
            && (r.Some? ==>
                  CM.ThreadRegsWf(r.value, ncap, nlook, nquant)
                  && CM.RegsAgreeOutside(r.value.capture_regs, cap,
                                         PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(body)))
                  && CM.RegsAgreeOutside(r.value.look_regs, lk, LookIdSet(body))
                  && CM.RegsAgreeOutside(r.value.look_regs, lk, DirectLidSet(body))   // the tight frame
                  && CM.LookCpsLE(r.value.look_regs, |str|)
                  && CM.RegsAgreeOutside(r.value.quant_regs, qt, QIdsOuter(body))
                  && (forall k :: AI.get_idx(r.value.quant_regs.a_clk, k) >= -1)
                  && (forall k :: k !in QIdsOuter(body) ==> AI.get_idx(r.value.quant_regs.a_cp, k) < 0))
    // the reconstruction leaves the look bank of the VM winner untouched
    ensures var r := AI.FFindMatchPlus(bytecode, body, plus_bcv, str, ov, LAnc.Forward, cp, cap, lk, qt, 0, lookcdn).0;
            var fm := AI.FFindMatch(bytecode, str, AI.FInitState(bytecode, cp, cap, lk, qt, 0, AI.cp_context(cp, str, LAnc.Forward)), ov, LAnc.Forward, lookcdn).0;
            r.Some? ==> fm.Some? && r.value.look_regs == fm.value.look_regs
  {
    reveal RowLAStatics();
    var dir := LAnc.Forward;
    var ctx := AI.cp_context(cp, str, dir);
    var inits := AI.FInitState(bytecode, cp, cap, lk, qt, 0, ctx);
    var th0 := AI.init_thread(cap, lk, qt);
    assert inits.active == [th0] && inits.blocked == [] && inits.bestmatch.None?;
    assert {:split_here} true;
    // well-formedness of the VM winner
    assert CM.VmRegsWf(inits, ncap, nlook, nquant) by {
      assert CM.ThreadRegsWf(th0, ncap, nlook, nquant);
      forall t | t in inits.active ensures CM.ThreadRegsWf(t, ncap, nlook, nquant) {}
    }
    FFindMatchRegsWf(bytecode, str, inits, ov, dir, lookcdn, ncap, nlook, nquant);
    assert {:split_here} true;
    // the winner is RegsFinalOk on the body's CIN quantifiers (the incoming quant bank is final)
    NR.CompileToBytecodeRepNested(body);
    var endl := CP.compile(body, 0, CP.Progress).1;
    FRD.TrueStampsInCin(body, bytecode, endl as nat);
    var Q := FRD.CinQids(body);
    assert FV.VmRegsFinalOk(inits, |str|, Q) by {
      assert FV.RegsFinalOk(th0, |str|, Q);
      forall t | t in inits.active ensures FV.RegsFinalOk(t, |str|, Q) { assert t == th0; }
    }
    FV.FFindMatchRegsFinal(bytecode, str, inits, ov, dir, lookcdn, Q);
    assert {:split_here} true;
    // the VM's write frames, its look-cp bound, and the untouched view
    ReplayCaptureFrameNestedOuter(bytecode, str, inits, ov, dir, lookcdn, cap, lk, qt, R.Lookahead, body);
    LookBytecodeClassifiedNested(body);
    assert CM.VmLooksAgree(inits, lk, LookIdSet(body)) by {
      assert CM.RegsAgreeOutside(lk, lk, LookIdSet(body));
    }
    CM.FFindMatchLookFrame(bytecode, str, inits, ov, dir, lookcdn, lk, LookIdSet(body));
    DirectLidClassified(body);
    assert CM.VmLooksAgree(inits, lk, DirectLidSet(body)) by {
      assert CM.RegsAgreeOutside(lk, lk, DirectLidSet(body));
    }
    CM.FFindMatchLookFrame(bytecode, str, inits, ov, dir, lookcdn, lk, DirectLidSet(body));
    QuantBytecodeClassifiedNestedOuter(body);
    assert CM.VmQuantsAgree(inits, qt, QIdsOuter(body)) by {
      assert th0.quant_regs == qt;
      assert CM.RegsAgreeOutside(qt, qt, QIdsOuter(body));
    }
    CM.FFindMatchQuantFrame(bytecode, str, inits, ov, dir, lookcdn, qt, QIdsOuter(body));
    assert CM.VmLookCpOk(inits, |str|) by { assert th0.look_regs == lk; }
    CM.FFindMatchLookCpOk(bytecode, str, inits, ov, dir, lookcdn);
    NoWriteOracleBodyCodeNested(body);
    CM.FFindMatchOvStable(bytecode, str, inits, ov, dir, lookcdn);
    var (res0, ovx) := AI.FFindMatch(bytecode, str, inits, ov, dir, lookcdn);
    assert ovx == ov;
    assert {:split_here} true;
    // the reconstruction (`RowReconAt` reads the view through `qm.ov` only)
    if res0.Some? {
      var th := res0.value;
      var qm := AR.QMap(map[], map[], ov, map[]);
      RRA.RowReconAt(qm, body, plus_bcv, str, th, ncap, nlook, nquant);
      var rp := AI.FReconstructPlus(th, body, plus_bcv, str, ov, dir);
      assert RRA.QOuter(body) == QIdsOuter(body);
      CM.RegsAgreeOutsideTrans(rp.0.capture_regs, th.capture_regs, cap,
                               PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(body)));
      RRA.RowQuantFinalOutside(th, rp.0.quant_regs, qt, QIdsOuter(body));
      assert AI.FFindMatchPlus(bytecode, body, plus_bcv, str, ov, dir, cp, cap, lk, qt, 0, lookcdn)
          == (Some(rp.0), rp.1);
    } else {
      assert AI.FFindMatchPlus(bytecode, body, plus_bcv, str, ov, dir, cp, cap, lk, qt, 0, lookcdn) == (None, ovx);
    }
  }
  /** (G5b-1) `RowLAStatics` on the S forms: the row body may hold a greedy CDN plus (its stamps are the
      `QidStampPlus` pluses; every stamp body is look-free). */
  opaque ghost predicate RowLAStaticsS(body: R.regex, plus_bcv: seq<RB.code>) {
    T.TransWf(body) && NR.NestedFragmentCdnRE(body) && PIV.CapUnique(body) && PIV.QuantUnique(body)
    && LTB.LookUnique(body) && NRC.CdnTopRE(body)
    && NRR.PlusTableOkS(body, plus_bcv)
  }

  /** (G5b-1) The narrow row statics are an instance of the S ones. */
  lemma RowLAStaticsToS(body: R.regex, plus_bcv: seq<RB.code>)
    requires RowLAStatics(body, plus_bcv) && T.TransWf(body)
    ensures RowLAStaticsS(body, plus_bcv)
  {
    reveal RowLAStatics(); reveal RowLAStaticsS();
    NR.NarrowIsCdn(body);
    NRC.NoCdnIsCdnTop(body);
    RF.CinStampBodiesNoCdn(body);
    NRR.PlusTableOkSNarrow(body, plus_bcv);
  }

  /** (G5b-1) `ReplayPlusRowLA` on the S forms. The run's frames are kind-blind; the reconstruction is
      `RRA.RowReconAtS` (no empty-path fact needed: the frame reads only the stamps' range). */
  lemma ReplayPlusRowLAS(bytecode: RB.code, str: string, ov: LOr.OracleView, lookcdn: LCdn.cdns,
                         plus_bcv: seq<RB.code>, cp: int, cap: AReg.Regs, lk: AReg.Regs, qt: AReg.Regs,
                         body: R.regex, ncap: int, nlook: int, nquant: int)
    requires RowLAStaticsS(body, plus_bcv)
    requires bytecode == CP.compile_to_bytecode(body)
    requires 0 <= cp <= |str|
    requires ncap >= 0 && nlook >= 0 && nquant >= 0
    requires |cap.a_cp| == ncap && |cap.a_clk| == ncap && PIV.CapRegWf(cap)
    requires |lk.a_cp| == nlook && |lk.a_clk| == nlook && CM.LookCpsLE(lk, |str|)
    requires |qt.a_cp| == nquant && |qt.a_clk| == nquant
    requires (forall k :: AI.get_idx(qt.a_cp, k) < 0) && (forall k :: AI.get_idx(qt.a_clk, k) >= -1)
    ensures var rr := AI.FFindMatchPlus(bytecode, body, plus_bcv, str, ov, LAnc.Forward,
                                        cp, cap, lk, qt, 0, lookcdn);
            var r := rr.0;
            rr.1 == ov
            && (r.Some? ==>
                  CM.ThreadRegsWf(r.value, ncap, nlook, nquant)
                  && CM.RegsAgreeOutside(r.value.capture_regs, cap,
                                         PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(body)))
                  && CM.RegsAgreeOutside(r.value.look_regs, lk, LookIdSet(body))
                  && CM.RegsAgreeOutside(r.value.look_regs, lk, DirectLidSet(body))   // the tight frame
                  && CM.LookCpsLE(r.value.look_regs, |str|)
                  && CM.RegsAgreeOutside(r.value.quant_regs, qt, QIdsOuter(body))
                  && (forall k :: AI.get_idx(r.value.quant_regs.a_clk, k) >= -1)
                  && (forall k :: k !in QIdsOuter(body) ==> AI.get_idx(r.value.quant_regs.a_cp, k) < 0))
    // (G5b-3) the reconstruction may re-set lids inside a stamp body (capture-free looks): the plus winner's
    // look bank agrees with the VM winner's outside them, and keeps each bank invariant the VM winner has
    ensures var r := AI.FFindMatchPlus(bytecode, body, plus_bcv, str, ov, LAnc.Forward, cp, cap, lk, qt, 0, lookcdn).0;
            var fm := AI.FFindMatch(bytecode, str, AI.FInitState(bytecode, cp, cap, lk, qt, 0, AI.cp_context(cp, str, LAnc.Forward)), ov, LAnc.Forward, lookcdn).0;
            r.Some? ==> (fm.Some?
              && CM.RegsAgreeOutside(r.value.look_regs, fm.value.look_regs, DirectLidSet(body))
              && CM.RegsAgreeOutside(r.value.look_regs, fm.value.look_regs, RF.LooksQ(body, FRD.StampQids(body)))
              && CM.RegsAgreeOutside(r.value.look_regs, fm.value.look_regs, ELk.LooksQE(body, FRD.StampQids(body)))   // (G4b-1b)
              && (CM.LookCpsOracleTrue(fm.value.look_regs, ov) ==> CM.LookCpsOracleTrue(r.value.look_regs, ov))
              && (CM.LookClkSetWithCp(fm.value.look_regs) ==> CM.LookClkSetWithCp(r.value.look_regs))
              && (CM.LookCpSetWithClk(fm.value.look_regs) ==> CM.LookCpSetWithClk(r.value.look_regs)))
  {
    reveal RowLAStaticsS();
    var dir := LAnc.Forward;
    var ctx := AI.cp_context(cp, str, dir);
    var inits := AI.FInitState(bytecode, cp, cap, lk, qt, 0, ctx);
    var th0 := AI.init_thread(cap, lk, qt);
    assert inits.active == [th0] && inits.blocked == [] && inits.bestmatch.None?;
    assert {:split_here} true;
    // well-formedness of the VM winner
    assert CM.VmRegsWf(inits, ncap, nlook, nquant) by {
      assert CM.ThreadRegsWf(th0, ncap, nlook, nquant);
      forall t | t in inits.active ensures CM.ThreadRegsWf(t, ncap, nlook, nquant) {}
    }
    FFindMatchRegsWf(bytecode, str, inits, ov, dir, lookcdn, ncap, nlook, nquant);
    assert {:split_here} true;
    // the winner is RegsFinalOk on the body's stamp quantifiers (the incoming quant bank is final)
    NR.CompileToBytecodeRepCdn(body);
    var endl := CP.compile(body, 0, CP.Progress).1;
    FRD.TrueStampsInStamp(body, bytecode, endl as nat);
    var Q := FRD.StampQids(body);
    assert FV.VmRegsFinalOk(inits, |str|, Q) by {
      assert FV.RegsFinalOk(th0, |str|, Q);
      forall t | t in inits.active ensures FV.RegsFinalOk(t, |str|, Q) { assert t == th0; }
    }
    FV.FFindMatchRegsFinal(bytecode, str, inits, ov, dir, lookcdn, Q);
    assert {:split_here} true;
    // the VM's write frames, its look-cp bound, and the untouched view
    var Sc := PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(body));
    CaptureBytecodeClassifiedCdnOuter(body);
    assert CM.VmCapturesAgree(inits, cap, Sc) by {
      assert CM.RegsAgreeOutside(cap, cap, Sc);
    }
    CM.FFindMatchCapWriteFrame(bytecode, str, inits, ov, dir, lookcdn, cap, Sc);
    LookBytecodeClassifiedCdn(body);
    assert CM.VmLooksAgree(inits, lk, LookIdSet(body)) by {
      assert CM.RegsAgreeOutside(lk, lk, LookIdSet(body));
    }
    CM.FFindMatchLookFrame(bytecode, str, inits, ov, dir, lookcdn, lk, LookIdSet(body));
    DirectLidClassifiedCdn(body);
    assert CM.VmLooksAgree(inits, lk, DirectLidSet(body)) by {
      assert CM.RegsAgreeOutside(lk, lk, DirectLidSet(body));
    }
    CM.FFindMatchLookFrame(bytecode, str, inits, ov, dir, lookcdn, lk, DirectLidSet(body));
    QuantBytecodeClassifiedCdnOuter(body);
    assert CM.VmQuantsAgree(inits, qt, QIdsOuter(body)) by {
      assert th0.quant_regs == qt;
      assert CM.RegsAgreeOutside(qt, qt, QIdsOuter(body));
    }
    CM.FFindMatchQuantFrame(bytecode, str, inits, ov, dir, lookcdn, qt, QIdsOuter(body));
    assert CM.VmLookCpOk(inits, |str|) by { assert th0.look_regs == lk; }
    CM.FFindMatchLookCpOk(bytecode, str, inits, ov, dir, lookcdn);
    NoWriteOracleBodyCodeCdn(body);
    CM.FFindMatchOvStable(bytecode, str, inits, ov, dir, lookcdn);
    var (res0, ovx) := AI.FFindMatch(bytecode, str, inits, ov, dir, lookcdn);
    assert ovx == ov;
    assert {:split_here} true;
    // the reconstruction (`RowReconAtS` reads the view through `qm.ov` only)
    if res0.Some? {
      var th := res0.value;
      var qm := AR.QMap(map[], map[], ov, map[]);
      // (G5b-3) the reconstruction re-sets only lids inside stamp bodies (direct lids of `body`); the bank
      // invariants the VM winner has pass through
      var F := SBk.Flags(CM.LookCpsOracleTrue(th.look_regs, ov), CM.LookClkSetWithCp(th.look_regs),
                         CM.LookCpSetWithClk(th.look_regs), true, |str|);
      RRA.RowReconAtG4(F, qm, body, plus_bcv, str, th, ncap, nlook, nquant);
      DirectLidSetBridge(body);
      DirectLidsSubLookIds(body);
      assert CM.RegsAgreeOutside(AI.FReconstructPlus(th, body, plus_bcv, str, ov, LAnc.Forward).0.look_regs,
                                 lk, DirectLidSet(body)) by {
        CM.RegsAgreeOutsideTrans(AI.FReconstructPlus(th, body, plus_bcv, str, ov, LAnc.Forward).0.look_regs,
                                 th.look_regs, lk, DirectLidSet(body));
      }
      assert CM.RegsAgreeOutside(AI.FReconstructPlus(th, body, plus_bcv, str, ov, LAnc.Forward).0.look_regs,
                                 lk, LookIdSet(body)) by {
        var a := AI.FReconstructPlus(th, body, plus_bcv, str, ov, LAnc.Forward).0.look_regs;
        forall k: int | k !in LookIdSet(body)
          ensures AI.get_idx(a.a_cp, k) == AI.get_idx(lk.a_cp, k) && AI.get_idx(a.a_clk, k) == AI.get_idx(lk.a_clk, k)
        {
          assert k !in DirectLidSet(body);
        }
      }
      var rp := AI.FReconstructPlus(th, body, plus_bcv, str, ov, dir);
      assert RRA.QOuter(body) == QIdsOuter(body);
      CM.RegsAgreeOutsideTrans(rp.0.capture_regs, th.capture_regs, cap,
                               PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(body)));
      RRA.RowQuantFinalOutside(th, rp.0.quant_regs, qt, QIdsOuter(body));
      assert AI.FFindMatchPlus(bytecode, body, plus_bcv, str, ov, dir, cp, cap, lk, qt, 0, lookcdn)
          == (Some(rp.0), rp.1);
    } else {
      assert AI.FFindMatchPlus(bytecode, body, plus_bcv, str, ov, dir, cp, cap, lk, qt, 0, lookcdn) == (None, ovx);
    }
  }

  /** (G3b) `ReplayPlusRowLA`'s lookbehind twin: the row replays `compile(reverse_regex(body))` BACKWARD and
      reconstructs with `body` (`FReconstructPlus` is direction-blind). Same conclusions. */
  lemma ReplayPlusRowLB(bytecode: RB.code, str: string, ov: LOr.OracleView, lookcdn: LCdn.cdns,
                        plus_bcv: seq<RB.code>, cp: int, cap: AReg.Regs, lk: AReg.Regs, qt: AReg.Regs,
                        body: R.regex, ncap: int, nlook: int, nquant: int)
    requires RowLAStatics(body, plus_bcv)
    requires bytecode == CP.compile_to_bytecode(R.reverse_regex(body))
    requires 0 <= cp <= |str|
    requires ncap >= 0 && nlook >= 0 && nquant >= 0
    requires |cap.a_cp| == ncap && |cap.a_clk| == ncap && PIV.CapRegWf(cap)
    requires |lk.a_cp| == nlook && |lk.a_clk| == nlook && CM.LookCpsLE(lk, |str|)
    requires |qt.a_cp| == nquant && |qt.a_clk| == nquant
    requires (forall k :: AI.get_idx(qt.a_cp, k) < 0) && (forall k :: AI.get_idx(qt.a_clk, k) >= -1)
    ensures var rr := AI.FFindMatchPlus(bytecode, body, plus_bcv, str, ov, LAnc.Backward,
                                        cp, cap, lk, qt, 0, lookcdn);
            var r := rr.0;
            rr.1 == ov
            && (r.Some? ==>
                  CM.ThreadRegsWf(r.value, ncap, nlook, nquant)
                  && CM.RegsAgreeOutside(r.value.capture_regs, cap,
                                         PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(body)))
                  && CM.RegsAgreeOutside(r.value.look_regs, lk, LookIdSet(body))
                  && CM.RegsAgreeOutside(r.value.look_regs, lk, DirectLidSet(body))
                  && CM.LookCpsLE(r.value.look_regs, |str|)
                  && CM.RegsAgreeOutside(r.value.quant_regs, qt, QIdsOuter(body))
                  && (forall k :: AI.get_idx(r.value.quant_regs.a_clk, k) >= -1)
                  && (forall k :: k !in QIdsOuter(body) ==> AI.get_idx(r.value.quant_regs.a_cp, k) < 0))
    ensures var r := AI.FFindMatchPlus(bytecode, body, plus_bcv, str, ov, LAnc.Backward, cp, cap, lk, qt, 0, lookcdn).0;
            var fm := AI.FFindMatch(bytecode, str, AI.FInitState(bytecode, cp, cap, lk, qt, 0, AI.cp_context(cp, str, LAnc.Backward)), ov, LAnc.Backward, lookcdn).0;
            r.Some? ==> fm.Some? && r.value.look_regs == fm.value.look_regs
  {
    reveal RowLAStatics();
    var dir := LAnc.Backward;
    var ctx := AI.cp_context(cp, str, dir);
    assert ctx.nextchar == AI.get_char(str, cp - 1) by { hide *; reveal AI.cp_context; }
    var inits := AI.FInitState(bytecode, cp, cap, lk, qt, 0, ctx);
    var th0 := AI.init_thread(cap, lk, qt);
    assert inits.active == [th0] && inits.blocked == [] && inits.bestmatch.None?;
    var rev := R.reverse_regex(body);
    ReverseNestedPackage(body);
    ReverseIdSets(body);
    assert {:split_here} true;
    // well-formedness of the VM winner
    assert CM.VmRegsWf(inits, ncap, nlook, nquant) by {
      assert CM.ThreadRegsWf(th0, ncap, nlook, nquant);
      forall t | t in inits.active ensures CM.ThreadRegsWf(t, ncap, nlook, nquant) {}
    }
    FFindMatchRegsWf(bytecode, str, inits, ov, dir, lookcdn, ncap, nlook, nquant);
    assert {:split_here} true;
    // the winner is RegsFinalOk on the body's CIN quantifiers (the reverse code stamps the same ids)
    BR.RevTrueStampsCin(body);
    var Q := FRD.CinQids(body);
    assert FV.VmRegsFinalOk(inits, |str|, Q) by {
      assert FV.RegsFinalOk(th0, |str|, Q);
      forall t | t in inits.active ensures FV.RegsFinalOk(t, |str|, Q) { assert t == th0; }
    }
    BR.FFindMatchRegsFinalAny(bytecode, str, inits, ov, dir, lookcdn, Q);
    assert {:split_here} true;
    // the VM's write frames (reverse code: the same id sets), its look-cp bound, and the untouched view
    ReplayCaptureFrameNestedOuterLB(bytecode, str, inits, ov, lookcdn, cap, lk, qt, body);
    LookBytecodeClassifiedNested(rev);
    assert CM.VmLooksAgree(inits, lk, LookIdSet(body)) by {
      assert CM.RegsAgreeOutside(lk, lk, LookIdSet(body));
    }
    CM.FFindMatchLookFrame(bytecode, str, inits, ov, dir, lookcdn, lk, LookIdSet(body));
    DirectLidClassified(rev);
    assert CM.VmLooksAgree(inits, lk, DirectLidSet(body)) by {
      assert CM.RegsAgreeOutside(lk, lk, DirectLidSet(body));
    }
    CM.FFindMatchLookFrame(bytecode, str, inits, ov, dir, lookcdn, lk, DirectLidSet(body));
    ReverseQuantIdsOutsideLooks(body);
    assert QIdsOuter(rev) == QIdsOuter(body);
    QuantBytecodeClassifiedNestedOuter(rev);
    assert CM.VmQuantsAgree(inits, qt, QIdsOuter(body)) by {
      assert th0.quant_regs == qt;
      assert CM.RegsAgreeOutside(qt, qt, QIdsOuter(body));
    }
    CM.FFindMatchQuantFrame(bytecode, str, inits, ov, dir, lookcdn, qt, QIdsOuter(body));
    assert CM.VmLookCpOk(inits, |str|) by { assert th0.look_regs == lk; }
    CM.FFindMatchLookCpOkB(bytecode, str, inits, ov, dir, lookcdn);
    NoWriteOracleBodyCodeNested(rev);
    CM.FFindMatchOvStable(bytecode, str, inits, ov, dir, lookcdn);
    var (res0, ovx) := AI.FFindMatch(bytecode, str, inits, ov, dir, lookcdn);
    assert ovx == ov;
    assert {:split_here} true;
    // the reconstruction: `RowReconAt` states Forward; `FReconstructPlus` is direction-blind
    if res0.Some? {
      var th := res0.value;
      var qm := AR.QMap(map[], map[], ov, map[]);
      RRA.RowReconAt(qm, body, plus_bcv, str, th, ncap, nlook, nquant);
      DB.ReconstructPlusDirBlind(th, body, plus_bcv, str, ov);
      var rp := AI.FReconstructPlus(th, body, plus_bcv, str, ov, dir);
      assert rp == AI.FReconstructPlus(th, body, plus_bcv, str, ov, LAnc.Forward);
      assert RRA.QOuter(body) == QIdsOuter(body);
      CM.RegsAgreeOutsideTrans(rp.0.capture_regs, th.capture_regs, cap,
                               PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(body)));
      RRA.RowQuantFinalOutside(th, rp.0.quant_regs, qt, QIdsOuter(body));
      assert AI.FFindMatchPlus(bytecode, body, plus_bcv, str, ov, dir, cp, cap, lk, qt, 0, lookcdn)
          == (Some(rp.0), rp.1);
    } else {
      assert AI.FFindMatchPlus(bytecode, body, plus_bcv, str, ov, dir, cp, cap, lk, qt, 0, lookcdn) == (None, ovx);
    }
  }



  /** (G5b-2) `ReplayPlusRowLB` on the S forms: the lookbehind row body may hold a greedy CDN plus (its
      stamps are the `QidStampPlus` pluses). Same conclusions. */
  lemma ReplayPlusRowLBS(bytecode: RB.code, str: string, ov: LOr.OracleView, lookcdn: LCdn.cdns,
                         plus_bcv: seq<RB.code>, cp: int, cap: AReg.Regs, lk: AReg.Regs, qt: AReg.Regs,
                         body: R.regex, ncap: int, nlook: int, nquant: int)
    requires RowLAStaticsS(body, plus_bcv)
    requires bytecode == CP.compile_to_bytecode(R.reverse_regex(body))
    requires 0 <= cp <= |str|
    requires ncap >= 0 && nlook >= 0 && nquant >= 0
    requires |cap.a_cp| == ncap && |cap.a_clk| == ncap && PIV.CapRegWf(cap)
    requires |lk.a_cp| == nlook && |lk.a_clk| == nlook && CM.LookCpsLE(lk, |str|)
    requires |qt.a_cp| == nquant && |qt.a_clk| == nquant
    requires (forall k :: AI.get_idx(qt.a_cp, k) < 0) && (forall k :: AI.get_idx(qt.a_clk, k) >= -1)
    ensures var rr := AI.FFindMatchPlus(bytecode, body, plus_bcv, str, ov, LAnc.Backward,
                                        cp, cap, lk, qt, 0, lookcdn);
            var r := rr.0;
            rr.1 == ov
            && (r.Some? ==>
                  CM.ThreadRegsWf(r.value, ncap, nlook, nquant)
                  && CM.RegsAgreeOutside(r.value.capture_regs, cap,
                                         PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(body)))
                  && CM.RegsAgreeOutside(r.value.look_regs, lk, LookIdSet(body))
                  && CM.RegsAgreeOutside(r.value.look_regs, lk, DirectLidSet(body))
                  && CM.LookCpsLE(r.value.look_regs, |str|)
                  && CM.RegsAgreeOutside(r.value.quant_regs, qt, QIdsOuter(body))
                  && (forall k :: AI.get_idx(r.value.quant_regs.a_clk, k) >= -1)
                  && (forall k :: k !in QIdsOuter(body) ==> AI.get_idx(r.value.quant_regs.a_cp, k) < 0))
    // (G5b-3) the reconstruction may re-set lids inside a stamp body (capture-free looks): the plus winner's
    // look bank agrees with the VM winner's outside them, and keeps each bank invariant the VM winner has
    ensures var r := AI.FFindMatchPlus(bytecode, body, plus_bcv, str, ov, LAnc.Backward, cp, cap, lk, qt, 0, lookcdn).0;
            var fm := AI.FFindMatch(bytecode, str, AI.FInitState(bytecode, cp, cap, lk, qt, 0, AI.cp_context(cp, str, LAnc.Backward)), ov, LAnc.Backward, lookcdn).0;
            r.Some? ==> (fm.Some?
              && CM.RegsAgreeOutside(r.value.look_regs, fm.value.look_regs, DirectLidSet(body))
              && CM.RegsAgreeOutside(r.value.look_regs, fm.value.look_regs, RF.LooksQ(body, FRD.StampQids(body)))
              && CM.RegsAgreeOutside(r.value.look_regs, fm.value.look_regs, ELk.LooksQE(body, FRD.StampQids(body)))   // (G4b-1b)
              && (CM.LookCpsOracleTrue(fm.value.look_regs, ov) ==> CM.LookCpsOracleTrue(r.value.look_regs, ov))
              && (CM.LookClkSetWithCp(fm.value.look_regs) ==> CM.LookClkSetWithCp(r.value.look_regs))
              && (CM.LookCpSetWithClk(fm.value.look_regs) ==> CM.LookCpSetWithClk(r.value.look_regs)))
  {
    reveal RowLAStaticsS();
    var dir := LAnc.Backward;
    var ctx := AI.cp_context(cp, str, dir);
    assert ctx.nextchar == AI.get_char(str, cp - 1) by { hide *; reveal AI.cp_context; }
    var inits := AI.FInitState(bytecode, cp, cap, lk, qt, 0, ctx);
    var th0 := AI.init_thread(cap, lk, qt);
    assert inits.active == [th0] && inits.blocked == [] && inits.bestmatch.None?;
    var rev := R.reverse_regex(body);
    ReverseCdnPackage(body);
    ReverseIdSets(body);
    assert {:split_here} true;
    // well-formedness of the VM winner
    assert CM.VmRegsWf(inits, ncap, nlook, nquant) by {
      assert CM.ThreadRegsWf(th0, ncap, nlook, nquant);
      forall t | t in inits.active ensures CM.ThreadRegsWf(t, ncap, nlook, nquant) {}
    }
    FFindMatchRegsWf(bytecode, str, inits, ov, dir, lookcdn, ncap, nlook, nquant);
    assert {:split_here} true;
    // the winner is RegsFinalOk on the body's stamp quantifiers (the reverse code stamps the same ids)
    BR.RevTrueStampsS(body);
    var Q := FRD.StampQids(body);
    assert FV.VmRegsFinalOk(inits, |str|, Q) by {
      assert FV.RegsFinalOk(th0, |str|, Q);
      forall t | t in inits.active ensures FV.RegsFinalOk(t, |str|, Q) { assert t == th0; }
    }
    BR.FFindMatchRegsFinalAny(bytecode, str, inits, ov, dir, lookcdn, Q);
    assert {:split_here} true;
    // the VM's write frames (reverse code: the same id sets), its look-cp bound, and the untouched view
    var Sc := PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(body));
    ReverseCapIdsOutsideLooks(body);
    CaptureBytecodeClassifiedCdnOuter(rev);
    assert CM.CaptureWritesInside(bytecode, Sc);
    assert CM.VmCapturesAgree(inits, cap, Sc) by {
      assert CM.RegsAgreeOutside(cap, cap, Sc);
    }
    CM.FFindMatchCapWriteFrame(bytecode, str, inits, ov, dir, lookcdn, cap, Sc);
    LookBytecodeClassifiedCdn(rev);
    assert CM.VmLooksAgree(inits, lk, LookIdSet(body)) by {
      assert CM.RegsAgreeOutside(lk, lk, LookIdSet(body));
    }
    CM.FFindMatchLookFrame(bytecode, str, inits, ov, dir, lookcdn, lk, LookIdSet(body));
    DirectLidClassifiedCdn(rev);
    assert CM.VmLooksAgree(inits, lk, DirectLidSet(body)) by {
      assert CM.RegsAgreeOutside(lk, lk, DirectLidSet(body));
    }
    CM.FFindMatchLookFrame(bytecode, str, inits, ov, dir, lookcdn, lk, DirectLidSet(body));
    ReverseQuantIdsOutsideLooks(body);
    assert QIdsOuter(rev) == QIdsOuter(body);
    QuantBytecodeClassifiedCdnOuter(rev);
    assert CM.VmQuantsAgree(inits, qt, QIdsOuter(body)) by {
      assert th0.quant_regs == qt;
      assert CM.RegsAgreeOutside(qt, qt, QIdsOuter(body));
    }
    CM.FFindMatchQuantFrame(bytecode, str, inits, ov, dir, lookcdn, qt, QIdsOuter(body));
    assert CM.VmLookCpOk(inits, |str|) by { assert th0.look_regs == lk; }
    CM.FFindMatchLookCpOkB(bytecode, str, inits, ov, dir, lookcdn);
    NoWriteOracleBodyCodeCdn(rev);
    CM.FFindMatchOvStable(bytecode, str, inits, ov, dir, lookcdn);
    var (res0, ovx) := AI.FFindMatch(bytecode, str, inits, ov, dir, lookcdn);
    assert ovx == ov;
    assert {:split_here} true;
    // the reconstruction: `RowReconAt` states Forward; `FReconstructPlus` is direction-blind
    if res0.Some? {
      var th := res0.value;
      var qm := AR.QMap(map[], map[], ov, map[]);
      // (G5b-3) the reconstruction re-sets only lids inside stamp bodies (direct lids of `body`); the bank
      // invariants the VM winner has pass through
      var F := SBk.Flags(CM.LookCpsOracleTrue(th.look_regs, ov), CM.LookClkSetWithCp(th.look_regs),
                         CM.LookCpSetWithClk(th.look_regs), true, |str|);
      RRA.RowReconAtG4(F, qm, body, plus_bcv, str, th, ncap, nlook, nquant);
      DirectLidSetBridge(body);
      DirectLidsSubLookIds(body);
      assert CM.RegsAgreeOutside(AI.FReconstructPlus(th, body, plus_bcv, str, ov, LAnc.Forward).0.look_regs,
                                 lk, DirectLidSet(body)) by {
        CM.RegsAgreeOutsideTrans(AI.FReconstructPlus(th, body, plus_bcv, str, ov, LAnc.Forward).0.look_regs,
                                 th.look_regs, lk, DirectLidSet(body));
      }
      assert CM.RegsAgreeOutside(AI.FReconstructPlus(th, body, plus_bcv, str, ov, LAnc.Forward).0.look_regs,
                                 lk, LookIdSet(body)) by {
        var a := AI.FReconstructPlus(th, body, plus_bcv, str, ov, LAnc.Forward).0.look_regs;
        forall k: int | k !in LookIdSet(body)
          ensures AI.get_idx(a.a_cp, k) == AI.get_idx(lk.a_cp, k) && AI.get_idx(a.a_clk, k) == AI.get_idx(lk.a_clk, k)
        {
          assert k !in DirectLidSet(body);
        }
      }
      DB.ReconstructPlusDirBlind(th, body, plus_bcv, str, ov);
      var rp := AI.FReconstructPlus(th, body, plus_bcv, str, ov, dir);
      assert rp == AI.FReconstructPlus(th, body, plus_bcv, str, ov, LAnc.Forward);
      assert RRA.QOuter(body) == QIdsOuter(body);
      CM.RegsAgreeOutsideTrans(rp.0.capture_regs, th.capture_regs, cap,
                               PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(body)));
      RRA.RowQuantFinalOutside(th, rp.0.quant_regs, qt, QIdsOuter(body));
      assert AI.FFindMatchPlus(bytecode, body, plus_bcv, str, ov, dir, cp, cap, lk, qt, 0, lookcdn)
          == (Some(rp.0), rp.1);
    } else {
      assert AI.FFindMatchPlus(bytecode, body, plus_bcv, str, ov, dir, cp, cap, lk, qt, 0, lookcdn) == (None, ovx);
    }
  }


  /** (G3a) A4's quant set: `RAgree` ranges over valid indices only, so the negative members of
      `QidsOf(body)` are vacuous and the nonnegative ones lie in `QIdsInt(body)`. */
  lemma RAgreeAddQidsOf(a: AReg.Regs, b: AReg.Regs, body: R.regex)
    requires CM.RegsAgreeInside(a, b, LKC.QIdsInt(body))
    ensures RA.RAgree(a, b, LKC.QIdsInt(body) + QCI.QidsOf(body))
  {
    RRA.QidsOfNonneg(body);
    RRA.QOuterSubAll(body);
    assert RRA.QAll(body) == LKC.QIdsInt(body);
    RRA.RAgreeFromInside(a, b, LKC.QIdsInt(body));
  }

  /** (G3a) The replay of a lookahead row on the running banks against the fresh plus replay from init
      banks: they agree on whatever the running banks agree with init on (A4). No statics, no finality. */
  lemma ReplayAgreePlusFresh(bytecode: RB.code, str: string, cp: int, cap: AReg.Regs, lk: AReg.Regs,
                             qt: AReg.Regs, ov: LOr.OracleView, lookcdn: LCdn.cdns, plus_bcv: seq<RB.code>,
                             body: R.regex, C: set<int>, SL: set<int>, ncap: int, nlook: int, nquant: int)
    requires |cap.a_cp| == ncap && |cap.a_clk| == ncap && ncap >= 0
    requires |lk.a_cp| == nlook && |lk.a_clk| == nlook && nlook >= 0
    requires |qt.a_cp| == nquant && |qt.a_clk| == nquant && nquant >= 0
    requires CM.RegsAgreeInside(cap, AReg.init_regs(ncap), C)
    requires CM.RegsAgreeInside(lk, AReg.init_regs(nlook), SL)
    requires CM.RegsAgreeInside(qt, AReg.init_regs(nquant), LKC.QIdsInt(body))
    ensures var a := AI.FFindMatchPlus(bytecode, body, plus_bcv, str, ov, LAnc.Forward, cp, cap, lk, qt, 0, lookcdn);
            var f := AI.FFindMatchPlus(bytecode, body, plus_bcv, str, ov, LAnc.Forward, cp,
                                       AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant), 0, lookcdn);
            a.1 == f.1 && (a.0.None? <==> f.0.None?)
            && (a.0.Some? ==>
                  CM.RegsAgreeInside(a.0.value.capture_regs, f.0.value.capture_regs, C)
                  && CM.RegsAgreeInside(a.0.value.look_regs, f.0.value.look_regs, SL)
                  && CM.RegsAgreeInside(a.0.value.quant_regs, f.0.value.quant_regs, LKC.QIdsInt(body)))
  {
    var D := RA.Ks(C, SL, LKC.QIdsInt(body) + QCI.QidsOf(body));
    RRA.RAgreeFromInside(cap, AReg.init_regs(ncap), C);
    RRA.RAgreeFromInside(lk, AReg.init_regs(nlook), SL);
    RAgreeAddQidsOf(qt, AReg.init_regs(nquant), body);
    RA.FFindMatchPlusAgree(bytecode, body, plus_bcv, str, ov, LAnc.Forward, cp,
                           cap, AReg.init_regs(ncap), lk, AReg.init_regs(nlook), qt, AReg.init_regs(nquant),
                           0, lookcdn, D);
    var a := AI.FFindMatchPlus(bytecode, body, plus_bcv, str, ov, LAnc.Forward, cp, cap, lk, qt, 0, lookcdn);
    var f := AI.FFindMatchPlus(bytecode, body, plus_bcv, str, ov, LAnc.Forward, cp,
                               AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant), 0, lookcdn);
    if a.0.Some? {
      RRA.InsideFromRAgree(a.0.value.capture_regs, f.0.value.capture_regs, C);
      RRA.InsideFromRAgree(a.0.value.look_regs, f.0.value.look_regs, SL);
      RRA.InsideFromRAgree(a.0.value.quant_regs, f.0.value.quant_regs, D.q);
      RegsAgreeInsideWeakenSub(a.0.value.quant_regs, f.0.value.quant_regs, LKC.QIdsInt(body), D.q);
    }
  }
  /** (G3b) `ReplayAgreePlusFresh` in either direction (A4 is direction-generic). */
  lemma ReplayAgreePlusFreshDir(bytecode: RB.code, str: string, cp: int, cap: AReg.Regs, lk: AReg.Regs,
                             qt: AReg.Regs, ov: LOr.OracleView, lookcdn: LCdn.cdns, plus_bcv: seq<RB.code>,
                             body: R.regex, C: set<int>, SL: set<int>, ncap: int, nlook: int, nquant: int,
                                dir: LAnc.direction)
    requires |cap.a_cp| == ncap && |cap.a_clk| == ncap && ncap >= 0
    requires |lk.a_cp| == nlook && |lk.a_clk| == nlook && nlook >= 0
    requires |qt.a_cp| == nquant && |qt.a_clk| == nquant && nquant >= 0
    requires CM.RegsAgreeInside(cap, AReg.init_regs(ncap), C)
    requires CM.RegsAgreeInside(lk, AReg.init_regs(nlook), SL)
    requires CM.RegsAgreeInside(qt, AReg.init_regs(nquant), LKC.QIdsInt(body))
    ensures var a := AI.FFindMatchPlus(bytecode, body, plus_bcv, str, ov, dir, cp, cap, lk, qt, 0, lookcdn);
            var f := AI.FFindMatchPlus(bytecode, body, plus_bcv, str, ov, dir, cp,
                                       AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant), 0, lookcdn);
            a.1 == f.1 && (a.0.None? <==> f.0.None?)
            && (a.0.Some? ==>
                  CM.RegsAgreeInside(a.0.value.capture_regs, f.0.value.capture_regs, C)
                  && CM.RegsAgreeInside(a.0.value.look_regs, f.0.value.look_regs, SL)
                  && CM.RegsAgreeInside(a.0.value.quant_regs, f.0.value.quant_regs, LKC.QIdsInt(body)))
  {
    var D := RA.Ks(C, SL, LKC.QIdsInt(body) + QCI.QidsOf(body));
    RRA.RAgreeFromInside(cap, AReg.init_regs(ncap), C);
    RRA.RAgreeFromInside(lk, AReg.init_regs(nlook), SL);
    RAgreeAddQidsOf(qt, AReg.init_regs(nquant), body);
    RA.FFindMatchPlusAgree(bytecode, body, plus_bcv, str, ov, dir, cp,
                           cap, AReg.init_regs(ncap), lk, AReg.init_regs(nlook), qt, AReg.init_regs(nquant),
                           0, lookcdn, D);
    var a := AI.FFindMatchPlus(bytecode, body, plus_bcv, str, ov, dir, cp, cap, lk, qt, 0, lookcdn);
    var f := AI.FFindMatchPlus(bytecode, body, plus_bcv, str, ov, dir, cp,
                               AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant), 0, lookcdn);
    if a.0.Some? {
      RRA.InsideFromRAgree(a.0.value.capture_regs, f.0.value.capture_regs, C);
      RRA.InsideFromRAgree(a.0.value.look_regs, f.0.value.look_regs, SL);
      RRA.InsideFromRAgree(a.0.value.quant_regs, f.0.value.quant_regs, D.q);
      RegsAgreeInsideWeakenSub(a.0.value.quant_regs, f.0.value.quant_regs, LKC.QIdsInt(body), D.q);
    }
  }

  // ==========================================================================
  // (G3a slice 3) The look-body plus gate and the rows-avoid premise. From the peer session's probe
  // `endgame/probes/GateRows.dfy.txt` (18/0).
  // ==========================================================================

  // ===========================================================================
  // 1. The gate
  // ===========================================================================

  ghost predicate BehindKind(la: R.lookaround) { la.Lookbehind? || la.NegLookbehind? }

  /** The look-bodies gate. History: G3a asked lookbehind bodies to be nulled-plus-free and lookahead bodies CIN;
      G5b let any look body hold a CDN plus; G5b-3/G4b-1 kept only "inside a positive body, every look an empty path
      of a stamp body crosses is capture-free"; (G4b-2) that scope is gone too, so the gate holds of every regex
      (`LookBodiesPlusGateAll`). It stays a premise name of the band's lemmas. */
  ghost predicate LookBodiesPlusGateRE(re: R.regex)
    decreases re
  {
    match re
    case Re_alt(r1, r2) => LookBodiesPlusGateRE(r1) && LookBodiesPlusGateRE(r2)
    case Re_con(r1, r2) => LookBodiesPlusGateRE(r1) && LookBodiesPlusGateRE(r2)
    case Re_quant(_, _, _, r1) => LookBodiesPlusGateRE(r1)
    case Re_capture(_, r1) => LookBodiesPlusGateRE(r1)
    case Re_lookaround(_, _, r1) => LookBodiesPlusGateRE(r1)
    case _ => true
  }

  /** (G4b-2) The gate holds of every regex. */
  lemma LookBodiesPlusGateAll(re: R.regex)
    ensures LookBodiesPlusGateRE(re)
    decreases re
  {
    match re
    case Re_alt(r1, r2) => LookBodiesPlusGateAll(r1); LookBodiesPlusGateAll(r2);
    case Re_con(r1, r2) => LookBodiesPlusGateAll(r1); LookBodiesPlusGateAll(r2);
    case Re_quant(_, _, _, r1) => LookBodiesPlusGateAll(r1);
    case Re_capture(_, r1) => LookBodiesPlusGateAll(r1);
    case Re_lookaround(_, _, r1) => LookBodiesPlusGateAll(r1);
    case _ =>
  }

  /** The nested fragment passes to a look body. */
  lemma NestedFragmentLookBody(r: R.regex, l: nat)
    requires NR.NestedFragmentRE(r) && l in LTB.LookIds(r)
    ensures NR.NestedFragmentRE(NI.LookBodyOfRE(r, l))
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      if l in LTB.LookIds(r1) { NestedFragmentLookBody(r1, l); } else { NestedFragmentLookBody(r2, l); }
    case Re_con(r1, r2) =>
      if l in LTB.LookIds(r1) { NestedFragmentLookBody(r1, l); } else { NestedFragmentLookBody(r2, l); }
    case Re_quant(_, _, _, r1) => NestedFragmentLookBody(r1, l);
    case Re_capture(_, r1) => NestedFragmentLookBody(r1, l);
    case Re_lookaround(lid0, _, r1) =>
      if lid0 >= 0 && (lid0 as nat) == l { } else { NestedFragmentLookBody(r1, l); }
  }

  /** A nulled-plus-free regex has no CDN plus and no CIN plus at all. (`NestedFragmentRE` is here
      for `q.min >= 0`: `NoNulledPlusRE` says `min > 0`, the other two say `min != 0`.) */
  lemma NoNulledPlusCinFragment(re: R.regex)
    requires NR.NestedFragmentRE(re)
    requires NR.NoNulledPlusRE(re)
    ensures NRC.NoCdnPlusRE(re) && RF.CinBodiesLookFreeRE(re)
    decreases re
  {
    match re
    case Re_alt(r1, r2) => NoNulledPlusCinFragment(r1); NoNulledPlusCinFragment(r2);
    case Re_con(r1, r2) => NoNulledPlusCinFragment(r1); NoNulledPlusCinFragment(r2);
    case Re_quant(_, _, _, r1) => NoNulledPlusCinFragment(r1);
    case Re_capture(_, r1) => NoNulledPlusCinFragment(r1);
    case Re_lookaround(_, _, r1) => NoNulledPlusCinFragment(r1);
    case _ =>
  }

  lemma PlusGateFromFull(re: R.regex)
    requires NR.NestedFragmentRE(re)
    requires NR.NoNulledPlusRE(re)
    ensures LookBodiesPlusGateRE(re)
    decreases re
  {
    match re
    case Re_alt(r1, r2) => PlusGateFromFull(r1); PlusGateFromFull(r2);
    case Re_con(r1, r2) => PlusGateFromFull(r1); PlusGateFromFull(r2);
    case Re_quant(_, _, _, r1) => PlusGateFromFull(r1);
    case Re_capture(_, r1) => PlusGateFromFull(r1);
    case Re_lookaround(_, _, r1) =>
      NoNulledPlusCinFragment(r1); RF.CinStampBodiesNoCdn(r1); PlusGateFromFull(r1);
    case _ =>
  }

  lemma PlusGateFromStrong(re: R.regex)
    requires NR.NestedFragmentRE(re)
    requires LooksNoNulledPlusRE(re)
    ensures LookBodiesPlusGateRE(re)
    decreases re
  {
    match re
    case Re_alt(r1, r2) => PlusGateFromStrong(r1); PlusGateFromStrong(r2);
    case Re_con(r1, r2) => PlusGateFromStrong(r1); PlusGateFromStrong(r2);
    case Re_quant(_, _, _, r1) => PlusGateFromStrong(r1);
    case Re_capture(_, r1) => PlusGateFromStrong(r1);
    case Re_lookaround(_, _, r1) =>
      NoNulledPlusCinFragment(r1); RF.CinStampBodiesNoCdn(r1); PlusGateFromFull(r1);
    case _ =>
  }

  /** The kind of the `lid`-labelled lookaround node in `r` (twin of `NI.LookBodyOfRE`). */
  ghost function LookKindOfRE(r: R.regex, lid: nat): R.lookaround
    requires lid in LTB.LookIds(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      if lid in LTB.LookIds(r1) then LookKindOfRE(r1, lid) else LookKindOfRE(r2, lid)
    case Re_con(r1, r2) =>
      if lid in LTB.LookIds(r1) then LookKindOfRE(r1, lid) else LookKindOfRE(r2, lid)
    case Re_quant(_, _, _, r1) => LookKindOfRE(r1, lid)
    case Re_capture(_, r1) => LookKindOfRE(r1, lid)
    case Re_lookaround(lid0, la, r1) =>
      if lid0 >= 0 && (lid0 as nat) == lid then la else LookKindOfRE(r1, lid)
  }

  /** The table row at `lid` holds the node's kind and body. */
  lemma LookKindOfTablesTie(re: R.regex, fc: CP.FCompiled, lid: nat)
    requires LTB.LookTablesOk(re, fc)
    requires lid in LTB.LookIds(re)
    ensures LTB.LookEntryOk(fc, lid as int, LookKindOfRE(re, lid), NI.LookBodyOfRE(re, lid))
    decreases re
  {
    match re
    case Re_alt(r1, r2) =>
      if lid in LTB.LookIds(r1) { LookKindOfTablesTie(r1, fc, lid); } else { LookKindOfTablesTie(r2, fc, lid); }
    case Re_con(r1, r2) =>
      if lid in LTB.LookIds(r1) { LookKindOfTablesTie(r1, fc, lid); } else { LookKindOfTablesTie(r2, fc, lid); }
    case Re_quant(_, _, _, r1) => LookKindOfTablesTie(r1, fc, lid);
    case Re_capture(_, r1) => LookKindOfTablesTie(r1, fc, lid);
    case Re_lookaround(lid0, la, r1) =>
      if lid0 >= 0 && (lid0 as nat) == lid { } else { LookKindOfTablesTie(r1, fc, lid); }
  }

  /** The gate at a look node (G3b: the same for every kind). Structural; replaces `LooksNoNulledPlusBody`. */
  lemma PlusGateBodyRECdn(re: R.regex, l: nat)
    requires NR.NestedFragmentCdnRE(re)
    requires LookBodiesPlusGateRE(re) && l in LTB.LookIds(re)
    ensures var b := NI.LookBodyOfRE(re, l);
            LookBodiesPlusGateRE(b)
    decreases re
  {
    match re
    case Re_alt(r1, r2) =>
      if l in LTB.LookIds(r1) { PlusGateBodyRECdn(r1, l); } else { PlusGateBodyRECdn(r2, l); }
    case Re_con(r1, r2) =>
      if l in LTB.LookIds(r1) { PlusGateBodyRECdn(r1, l); } else { PlusGateBodyRECdn(r2, l); }
    case Re_quant(_, _, _, r1) => PlusGateBodyRECdn(r1, l);
    case Re_capture(_, r1) => PlusGateBodyRECdn(r1, l);
    case Re_lookaround(lid0, la0, r1) =>
      if lid0 >= 0 && (lid0 as nat) == l { } else { PlusGateBodyRECdn(r1, l); }   // (G5b) the look arm is Cdn
  }

  /** (G5a-1 row J) The narrow name, as a corollary of `PlusGateBodyRECdn`. */
  lemma PlusGateBodyRE(re: R.regex, l: nat)
    requires NR.NestedFragmentRE(re)
    requires LookBodiesPlusGateRE(re) && l in LTB.LookIds(re)
    ensures var b := NI.LookBodyOfRE(re, l);
            LookBodiesPlusGateRE(b) && NRC.NoCdnPlusRE(b)
  {
    NR.NarrowIsCdn(re);
    PlusGateBodyRECdn(re, l);
    NestedFragmentLookBody(re, l);
    NestedNoCdn(NI.LookBodyOfRE(re, l));   // (G5b) a narrow regex's look body is CDN-free
  }

  /** The row form: any table row `(la, body)` at a look id of `re`. */
  lemma PlusGateBodyCdn(re: R.regex, crv: CP.FCompiled, l: nat, la: R.lookaround, body: R.regex)
    requires NR.NestedFragmentCdnRE(re)
    requires LookBodiesPlusGateRE(re) && l in LTB.LookIds(re)
    requires LTB.LookTablesOk(re, crv)
    requires LTB.LookEntryOk(crv, l as int, la, body)
    ensures body == NI.LookBodyOfRE(re, l) && la == LookKindOfRE(re, l)
    ensures LookBodiesPlusGateRE(body)
  {
    LookKindOfTablesTie(re, crv, l);
    PlusGateBodyRECdn(re, l);
  }

  /** (G5b-1) The gate is in the scope `NRC.CdnTopRE` ((G5b-2) every regex is). */
  lemma GateCdnTop(re: R.regex)
    requires LookBodiesPlusGateRE(re)
    ensures NRC.CdnTopRE(re)
    decreases re
  {
    match re
    case Re_alt(r1, r2) => GateCdnTop(r1); GateCdnTop(r2);
    case Re_con(r1, r2) => GateCdnTop(r1); GateCdnTop(r2);
    case Re_quant(_, _, _, r1) => GateCdnTop(r1);
    case Re_capture(_, r1) => GateCdnTop(r1);
    case Re_lookaround(_, _, r1) => GateCdnTop(r1);
    case _ =>
  }

  /** (G5a-1 row J) The narrow name, as a corollary of `PlusGateBodyCdn`. */
  lemma PlusGateBody(re: R.regex, crv: CP.FCompiled, l: nat, la: R.lookaround, body: R.regex)
    requires NR.NestedFragmentRE(re)
    requires LookBodiesPlusGateRE(re) && l in LTB.LookIds(re)
    requires LTB.LookTablesOk(re, crv)
    requires LTB.LookEntryOk(crv, l as int, la, body)
    ensures body == NI.LookBodyOfRE(re, l) && la == LookKindOfRE(re, l)
    ensures LookBodiesPlusGateRE(body)
    ensures NRC.NoCdnPlusRE(body)
  {
    NR.NarrowIsCdn(re);
    PlusGateBodyCdn(re, crv, l, la, body);
    NestedFragmentLookBody(re, l);
    NestedNoCdn(body);   // (G5b) a narrow regex's look body is CDN-free
  }

  // ===========================================================================
  // 2. Rows after a row never name its outside-look quantifiers
  // ===========================================================================

  /** Slot form: this is what `LLAF.FLookLoopAgreeFrom` consumes at row `l1`. */
  opaque ghost predicate RowsAvoidO(crv: CP.FCompiled, lid: int, maxlook: int) {
    forall l1: int, la1: R.lookaround, b1: R.regex ::
      lid <= l1 <= maxlook && LTB.LookEntryOk(crv, l1, la1, b1) ==>
        LLAF.LookAstsAvoidFrom(crv, l1 + 1, maxlook, QIdsOuter(b1))
  }

  lemma RowsAvoidSuffix(crv: CP.FCompiled, lid: int, maxlook: int)
    requires RowsAvoidO(crv, lid, maxlook)
    ensures RowsAvoidO(crv, lid + 1, maxlook)
  {
    reveal RowsAvoidO();
  }

  /** The use at a row. */
  lemma RowsAvoidAt(crv: CP.FCompiled, lid: int, maxlook: int, la: R.lookaround, body: R.regex)
    requires RowsAvoidO(crv, lid, maxlook)
    requires lid <= maxlook && LTB.LookEntryOk(crv, lid, la, body)
    ensures LLAF.LookAstsAvoidFrom(crv, lid + 1, maxlook, QIdsOuter(body))
  {
    reveal RowsAvoidO();
  }

  /** Two rows `l1 < l2` of `re`: the earlier body's outside-look quantifiers are not quantifiers of the
      later body. `DOrdQuantFromTables` on the syntax, without the gate. */
/** (G5a-1 P5b) `DOrdQuantRE` on the top-level fragment: the same proof, the premise widened and its callees
      on their `…Cdn` forms where the argument is the top regex or a non-look subterm of it. */
  lemma DOrdQuantRECdn(re: R.regex, crv: CP.FCompiled, l1: nat, l2: nat)
    requires NR.NestedFragmentCdnRE(re)
    requires PIV.CapUnique(re) && PIV.QuantUnique(re) && LTB.LookUnique(re)
    requires LTB.LookTablesOk(re, crv) && LTB.LidsWellNested(re)
    requires l1 in LTB.LookIds(re) && l2 in LTB.LookIds(re) && l1 < l2
    ensures PIV.QuantIdsOutsideLooks(NI.LookBodyOfRE(re, l1)) * PIV.QuantIds(NI.LookBodyOfRE(re, l2)) == {}
  {
    var b1 := NI.LookBodyOfRE(re, l1);
    var b2 := NI.LookBodyOfRE(re, l2);
    PIV.QuantIdsSplit(b1);
    LookBodyFactsL5Cdn(re, crv, l1);
    LookBodiesQuantsDisjointOrNested(re, l1, l2);
    if PIV.QuantIds(b1) * PIV.QuantIds(b2) == {} {
    } else if l2 in LTB.LookIds(b1) && PIV.QuantIds(b2) <= PIV.QuantIds(b1) {
      NI.LookBodyCompose(re, l1, l2);
      LookBodyQuantsIn(b1, l2);
      PIV.QuantIdsLooksDisjoint(b1);
    } else {
      assert l1 in LTB.LookIds(b2);
      LookBodyLidsGt(re, l2);
      assert false;
    }
  }

  /** (G5a-1 P5b) The narrow form, as a corollary of `DOrdQuantRECdn`. */
  lemma DOrdQuantRE(re: R.regex, crv: CP.FCompiled, l1: nat, l2: nat)
    requires NR.NestedFragmentRE(re)
    requires PIV.CapUnique(re) && PIV.QuantUnique(re) && LTB.LookUnique(re)
    requires LTB.LookTablesOk(re, crv) && LTB.LidsWellNested(re)
    requires l1 in LTB.LookIds(re) && l2 in LTB.LookIds(re) && l1 < l2
    ensures PIV.QuantIdsOutsideLooks(NI.LookBodyOfRE(re, l1)) * PIV.QuantIds(NI.LookBodyOfRE(re, l2)) == {}
  {
    NR.NarrowIsCdn(re);
    hide *;   // the wide premises are this lemma's own: match by name
    DOrdQuantRECdn(re, crv, l1, l2);
  }

  /** The producer, from the whole-regex tables. */
/** (G5a-1 P5b) `RowsAvoidFromTables` on the top-level fragment: the same proof, the premise widened and its callees
      on their `…Cdn` forms where the argument is the top regex or a non-look subterm of it. */
  lemma RowsAvoidFromTablesCdn(ast: R.regex, re: R.regex, crv: CP.FCompiled)
    requires crv == CP.FFullCompilation(ast) && re == R.lazy_prefix(ast)
    requires NR.NestedFragmentCdnRE(re)
    requires PIV.CapUnique(re) && PIV.QuantUnique(re) && LTB.LookUnique(re)
    requires LTB.LookTablesOk(re, crv) && LTB.LidsWellNested(re)
    ensures RowsAvoidO(crv, 1, R.max_lookaround(ast))
  {
    var maxlook := R.max_lookaround(ast);
    var pre := R.Re_quant(R.NonNullable, 0, R.CountedQuant(0, None, false), R.Re_character(R.Dot));
    assert re == R.Re_con(pre, ast);
    assert LTB.LookIds(pre) == {};
    assert LTB.LookIds(re) == LTB.LookIds(ast);
    var nlook0 := R.max_lookaround(ast) + 1;
    var nquant0 := R.max_quant(ast) + 1;
    var seed := CP.FCompiled(ast, CP.compile_to_bytecode(R.lazy_prefix(ast)), LCdn.compile_cdns(ast),
                             seq(nlook0, i => R.Lookahead), seq(nlook0, i => R.Re_empty),
                             seq(nlook0, i => []), seq(nlook0, i => []),
                             seq(nlook0, i => []), seq(nquant0, i => []));
    assert CP.FFullCompilation(ast) == CP.FCompileExtra(ast, seed);
    LTB.FCompileExtraLookFrame(ast, seed);
    forall l1: int, la1: R.lookaround, b1: R.regex | 1 <= l1 <= maxlook && LTB.LookEntryOk(crv, l1, la1, b1)
      ensures LLAF.LookAstsAvoidFrom(crv, l1 + 1, maxlook, QIdsOuter(b1))
    {
      LookEntryOnlyReal(ast, crv, l1, la1, b1);
      var lid1 := l1 as nat;
      LookKindOfTablesTie(re, crv, lid1);
      assert b1 == NI.LookBodyOfRE(re, lid1);
      forall l | l1 + 1 <= l <= maxlook && 0 <= l < |crv.f_look_ast|
        ensures QCI.QidsOf(crv.f_look_ast[l]) * QIdsOuter(b1) == {}
      {
        var lid2 := l as nat;
        if lid2 in LTB.LookIds(re) {
          LookKindOfTablesTie(re, crv, lid2);
          var b2 := NI.LookBodyOfRE(re, lid2);
          assert crv.f_look_ast[l] == b2;
          DOrdQuantRECdn(re, crv, lid1, lid2);
          RRA.QidsOfNonneg(b2);
          PIV.QuantIdsSplit(b2);
          forall k | k in QCI.QidsOf(b2) && k in QIdsOuter(b1) ensures false {
            var q1: nat :| q1 in PIV.QuantIdsOutsideLooks(b1) && (q1 as int) == k;
            assert k in RRA.QOuter(b2);
            var q2: nat :| q2 in PIV.QuantIdsOutsideLooks(b2) && (q2 as int) == k;
            assert q1 == q2;
            assert q1 in PIV.QuantIdsOutsideLooks(b1) * PIV.QuantIds(b2);
          }
        } else {
          assert LTB.AgreeAt(seed, crv, lid2);
          assert crv.f_look_ast[l] == R.Re_empty;
        }
      }
    }
    reveal RowsAvoidO();
  }

  /** (G5a-1 P5b) The narrow form, as a corollary of `RowsAvoidFromTablesCdn`. */
  lemma RowsAvoidFromTables(ast: R.regex, re: R.regex, crv: CP.FCompiled)
    requires crv == CP.FFullCompilation(ast) && re == R.lazy_prefix(ast)
    requires NR.NestedFragmentRE(re)
    requires PIV.CapUnique(re) && PIV.QuantUnique(re) && LTB.LookUnique(re)
    requires LTB.LookTablesOk(re, crv) && LTB.LidsWellNested(re)
    ensures RowsAvoidO(crv, 1, R.max_lookaround(ast))
  {
    NR.NarrowIsCdn(re);
    hide *;   // the wide premises are this lemma's own: match by name
    RowsAvoidFromTablesCdn(ast, re, crv);
  }

  /** C4e: the int-lid image of `body`'s OUTSIDE-look quant ids — the quant-bank
      indices a replay of `body` may touch (its inner looks are CheckOracle
      leaves, so their quants never appear in `body`'s code). Quant analogue of
      `PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(body))`. */
  ghost function QIdsOuter(body: R.regex): set<int> {
    set q: nat | q in PIV.QuantIdsOutsideLooks(body) :: q as int
  }

  /** C4e: nested twin of `CaptureBytecodeClassifiedNestedOuter` for QUANTS — a
      NESTED body's compiled bytecode writes quant clocks only inside its
      OUTSIDE-look quant ids (`QuantWriteIdsRENested`, the L3a-sharpened classifier
      that already excludes inside-look quants). `NR.CompileToBytecodeRepNested`
      supplies the `NfaRepRE` + `Accept` terminator. */
/** (G5a-1 P5b) `QuantBytecodeClassifiedNestedOuter` on the top-level fragment: the same proof, the premise widened and its callees
      on their `…Cdn` forms where the argument is the top regex or a non-look subterm of it. */
  lemma QuantBytecodeClassifiedCdnOuter(body: R.regex)
    requires NR.NestedFragmentCdnRE(body) && PIV.QuantUnique(body)
    ensures CM.QuantWritesInside(CP.compile_to_bytecode(body), QIdsOuter(body))
  {
    var code := CP.compile_to_bytecode(body);
    var next := CP.compile(body, 0, CP.Progress).1;
    NR.CompileToBytecodeRepCdn(body);
    var endl := next as nat;
    var Sq := QIdsOuter(body);
    forall pc: nat | pc < |code|
      ensures code[pc].SetQuantToClock? ==> code[pc].sq in Sq
    {
      assert NR.GetPcRE(code, pc) == Some(code[pc]);
      if pc < endl {
        PIV.QuantWriteIdsRECdn(body, code, 0, endl, pc);
        if code[pc].SetQuantToClock? {
          var qn: nat := code[pc].sq as nat;
          assert qn in PIV.QuantIdsOutsideLooks(body);
          assert (qn as int) in Sq;
        }
      } else {
        assert pc == endl;
        assert NR.GetPcRE(code, endl) == Some(RB.Accept);
      }
    }
  }

  /** (G5a-1 P5b) The narrow form, as a corollary of `QuantBytecodeClassifiedCdnOuter`. */
  lemma QuantBytecodeClassifiedNestedOuter(body: R.regex)
    requires NR.NestedFragmentRE(body) && PIV.QuantUnique(body)
    ensures CM.QuantWritesInside(CP.compile_to_bytecode(body), QIdsOuter(body))
  {
    NR.NarrowIsCdn(body);
    hide *;   // the wide premises are this lemma's own: match by name
    QuantBytecodeClassifiedCdnOuter(body);
  }

  /** C4e: nested twin of `ReplayPlusCaptureFrameNestedOuter` for QUANTS. The
      `FFindMatchPlus` capturing lookAHEAD replay over a NESTED body writes its
      quant bank only inside the body's OUTSIDE-look quant ids `QIdsOuter(body)`
      (its inner looks are CheckOracle leaves). The plus reconstruction is the
      identity on the `QuantRegsFinal` result (`FNulledPlusIdentity`), so the
      `FFindMatchPlus` quant bank IS the `FFindMatch` one, which the outer-quant
      write classification + `CM.FFindMatchQuantFrame` frames. */
  lemma ReplayPlusQuantFrameNestedOuter(bytecode: RB.code, str: string, ov: LOr.OracleView, dir: LAnc.direction,
                                        lookcdn: LCdn.cdns, plus_bcv: seq<RB.code>, cp: int,
                                        cap: AReg.Regs, lk: AReg.Regs, qt: AReg.Regs, la: R.lookaround, body: R.regex)
    requires NR.NestedFragmentRE(body) && PIV.CapUnique(body) && PIV.QuantUnique(body)
    requires NR.NoNulledPlusRE(body)   // §2.5b interim: all stamps false
    requires la.Lookahead? && dir == LAnc.Forward
    requires bytecode == CP.compile_to_bytecode(body)
    requires AI.cp_context(cp, str, dir).nextchar == AI.get_char(str, cp)
    requires (forall k :: AI.get_idx(qt.a_cp, k) < 0)
             && (forall k :: AI.get_idx(qt.a_clk, k) >= -1)
    ensures var r := AI.FFindMatchPlus(bytecode, body, plus_bcv, str, ov, dir, cp, cap, lk, qt, 0, lookcdn).0;
            r.Some? ==> CM.RegsAgreeOutside(r.value.quant_regs, qt, QIdsOuter(body))
  {
    var Sq := QIdsOuter(body);
    var inits := AI.FInitState(bytecode, cp, cap, lk, qt, 0, AI.cp_context(cp, str, dir));
    QuantBytecodeClassifiedNestedOuter(body);
    assert CM.VmQuantsAgree(inits, qt, Sq) by {
      assert inits.active == [AI.init_thread(cap, lk, qt)];
      assert AI.init_thread(cap, lk, qt).quant_regs == qt;
      assert CM.RegsAgreeOutside(qt, qt, Sq);
    }
    CM.FFindMatchQuantFrame(bytecode, str, inits, ov, dir, lookcdn, qt, Sq);
    NoTrueQuantStampNested(body);
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

  /** R2: per-look-entry side condition for the nested FLookLoop frame. Each
      lookaround body in range is a nested-fragment regex with unique cap/quant/
      look ids and correct sub-rows; its OUTER capture regs land in `S`, its own
      look ids in `Slook`, and (this brick is lookahead-only) any CAPTURING look
      is a positive lookahead. STATIC (look-bank independent), so it transfers
      unchanged through the induction as the look bank grows. */
  ghost predicate FrameEntryOk(crv: CP.FCompiled, la: R.lookaround, body: R.regex, S: set<int>, Slook: set<int>) {
    NR.NestedFragmentCdnRE(body) && PIV.CapUnique(body) && PIV.QuantUnique(body) && LTB.LookUnique(body)
    // (G3b) every positive row replays the plus machine; (G5b) a negative row is never replayed and its
    // body may hold a CDN plus
    // (G5b-1, G5b-2) a positive row's body (either direction) may hold a CDN plus: the S statics
    && (NRC.PositiveLk(la) ==> RowLAStaticsS(body, crv.f_plus_bc))
    && LTB.LookTablesOk(body, crv)
    && PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(body)) <= S
    && LookIdSet(body) <= Slook
    // (L5 F7c-2) the former `capture_type(la) ==> la.Lookahead?` clause is GONE:
    // the nested `FLookLoop*` frames now dispatch per kind (a positive LOOKBEHIND
    // lid replays `reverse_regex(body)` BACKWARD — the `...LB` helper twins).
  }

  /** R2 DELIVERABLE 1: the L4 nested capture+look frame for `FLookLoop`. Every
      matched positive-lookahead body may itself NEST looks to any depth. The
      capture bank is written only inside `S` (each body's OUTER capture regs
      land in `S`), and the look bank is written only inside `Slook` (each replay
      only ADDS its body's own inner-look ids). This is the honest nested
      weakening of `FLookLoopCaptureFrame`: NOT `res.1 == lk` (a nested body's
      replay crosses inner CheckOracle gates and writes their a_cp), but the
      OUTER looks/groups are untouched (`Slook`/`S` are the inner regions). The
      body-shape hypothesis is stated STATICALLY over the look tables so it
      survives the look-bank growth; the "matched look has a table row"
      invariant is preserved across each replay via the own-look-ids look frame
      + `LookIdEntryExists`. `decreases maxlook - lid`; mirrors
      `FLookLoopCaptureFrame`'s structure. */
  lemma FLookLoopCaptureFrameNested(crv: CP.FCompiled, str: string, lid: int, maxlook: int,
                                    cap: AReg.Regs, lk: AReg.Regs, qt: AReg.Regs, ov: LOr.OracleView,
                                    S: set<int>, Slook: set<int>, ncap: int, nlook: int, nquant: int)
    requires (forall k :: AI.get_idx(qt.a_cp, k) < 0)
             && (forall k :: AI.get_idx(qt.a_clk, k) >= -1)
    // (G3a) the wf block: a lookahead row's replay reconstructs, and `ReplayPlusRowLA` reads these
    requires ncap >= 0 && nlook >= 0 && nquant >= 0
    requires |qt.a_cp| == nquant && |qt.a_clk| == nquant
    requires |cap.a_cp| == ncap && |cap.a_clk| == ncap && PIV.CapRegWf(cap)
    requires |lk.a_cp| == nlook && |lk.a_clk| == nlook
    requires CM.LookCpsLE(lk, |str|)
    requires RowsAvoidO(crv, lid, maxlook)   // (G3a) later rows never name a row's outside-look quantifiers
    requires forall l: int, la: R.lookaround, body: R.regex ::
               lid <= l <= maxlook && LTB.LookEntryOk(crv, l, la, body) ==> FrameEntryOk(crv, la, body, S, Slook)
    requires forall l: int :: lid <= l <= maxlook && AReg.get_cp(lk, l).Some? ==>
                                exists la: R.lookaround, body: R.regex :: LTB.LookEntryOk(crv, l, la, body)
    ensures var res := AI.FLookLoop(crv, str, lid, maxlook, cap, lk, qt, ov);
            CM.RegsAgreeOutside(res.0, cap, S) && CM.RegsAgreeOutside(res.1, lk, Slook)
    decreases maxlook - lid
  {
    if lid > maxlook { return; }
    var next := lid + 1;
    RowsAvoidSuffix(crv, lid, maxlook);
    match AReg.get_cp(lk, lid)
    case None =>
      FLookLoopCaptureFrameNested(crv, str, next, maxlook, cap, lk, qt, ov, S, Slook, ncap, nlook, nquant);
    case Some(cp) =>
      var looktype := if 0 <= lid < |crv.f_look_types| then crv.f_look_types[lid] else R.Lookahead;
      if !AI.capture_type(looktype) {
        FLookLoopCaptureFrameNested(crv, str, next, maxlook, cap, lk, qt, ov, S, Slook, ncap, nlook, nquant);
      } else {
        var la: R.lookaround, body: R.regex :| LTB.LookEntryOk(crv, lid, la, body);
        assert 0 <= lid < |crv.f_look_types| && crv.f_look_types[lid] == la;
        assert looktype == la;
        assert FrameEntryOk(crv, la, body, S, Slook);
        assert la.Lookahead? || la.Lookbehind?;            // (L5 F7c-2) capture_type; per-kind dispatch below
        var bytecode := AI.get_code_v(crv.f_look_capture_bc, lid);
        var dir := AI.capture_direction(looktype);
        var lookcdn := if 0 <= lid < |crv.f_look_cdns| then crv.f_look_cdns[lid] else [];
        var lookast := if 0 <= lid < |crv.f_look_ast| then crv.f_look_ast[lid] else R.Re_empty;
        assert lookast == body;
        assert bytecode == CP.compile_to_bytecode(CP.capture_regex(la, body));
        var (result, ov1) := AI.FFindMatchPlus(bytecode, lookast, crv.f_plus_bc, str, ov, dir,
                                               cp, cap, lk, qt, 0, lookcdn);
        var capN := if result.None? then cap else result.value.capture_regs;
        var nlk := if result.None? then lk else result.value.look_regs;
        var nqt := if result.None? then qt else result.value.quant_regs;
        var D := QIdsOuter(body);
        assert 0 <= cp <= |str| by { assert AI.get_idx(lk.a_cp, lid) == cp; }   // LookCpsLE + get_cp.Some?
        // (L5 F7c-2) per-kind replay frames. Both kinds give the same wf block for the new banks; only the
        // lookahead row may leave quant POSITIONS set, and only inside `D`.
        if la.Lookahead? {
          assert CP.capture_regex(la, body) == body;
          assert bytecode == CP.compile_to_bytecode(body);
          assert dir == LAnc.Forward;
          ReplayPlusRowLAS(bytecode, str, ov, lookcdn, crv.f_plus_bc, cp, cap, lk, qt, body, ncap, nlook, nquant);
        } else {
          assert CP.capture_regex(la, body) == R.reverse_regex(body);
          assert bytecode == CP.compile_to_bytecode(R.reverse_regex(body));
          assert dir == LAnc.Backward;
          ReplayPlusRowLBS(bytecode, str, ov, lookcdn, crv.f_plus_bc, cp, cap, lk, qt, body, ncap, nlook, nquant);   // (G3b)
        }
        assert {:split_here} true;
        // ---- what both kinds deliver ----
        assert result.Some? ==> CM.ThreadRegsWf(result.value, ncap, nlook, nquant);
        assert |capN.a_cp| == ncap && |capN.a_clk| == ncap && PIV.CapRegWf(capN);
        assert |nlk.a_cp| == nlook && |nlk.a_clk| == nlook && CM.LookCpsLE(nlk, |str|);
        assert |nqt.a_cp| == nquant && |nqt.a_clk| == nquant;
        assert (forall k :: AI.get_idx(nqt.a_clk, k) >= -1)
            && (forall k :: k !in D ==> AI.get_idx(nqt.a_cp, k) < 0);

        // ---- this replay's frames, weakened to S / Slook ----
        assert CM.RegsAgreeOutside(capN, cap, S) by {
          if result.Some? {
            assert CM.RegsAgreeOutside(capN, cap, PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(body)));
            CM.RegsAgreeOutsideWeaken(capN, cap, PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(body)), S);
          } else {
            assert CM.RegsAgreeOutside(cap, cap, S);
          }
        }
        assert CM.RegsAgreeOutside(nlk, lk, Slook) by {
          if result.Some? {
            assert CM.RegsAgreeOutside(nlk, lk, LookIdSet(body));
            CM.RegsAgreeOutsideWeaken(nlk, lk, LookIdSet(body), Slook);
          } else {
            assert CM.RegsAgreeOutside(lk, lk, Slook);
          }
        }

        // ---- preserve the "matched look has a table row" invariant for nlk ----
        assert forall l: int :: next <= l <= maxlook && AReg.get_cp(nlk, l).Some? ==>
                                  exists la2: R.lookaround, body2: R.regex :: LTB.LookEntryOk(crv, l, la2, body2)
        by {
          forall l: int | next <= l <= maxlook && AReg.get_cp(nlk, l).Some?
            ensures exists la2: R.lookaround, body2: R.regex :: LTB.LookEntryOk(crv, l, la2, body2)
          {
            if AReg.get_cp(lk, l).Some? {
              // old matched look: from the incoming invariant
            } else {
              // NEWLY set by this replay: nlk differs from lk at l, so l is one of body's own look ids
              assert result.Some?;
              assert CM.RegsAgreeOutside(nlk, lk, LookIdSet(body));
              assert AI.get_idx(nlk.a_cp, l) >= 0;   // get_cp(nlk,l).Some?
              assert AI.get_idx(lk.a_cp, l) < 0;      // get_cp(lk,l).None
              assert l in LookIdSet(body);
              assert (l as nat) in LTB.LookIds(body);
              assert LTB.LookTablesOk(body, crv);     // FrameEntryOk
              LookIdEntryExists(body, crv, l as nat);
            }
          }
        }

        assert {:split_here} true;
        // ---- (G3a) clear-and-transfer: the tail on the CLEARED bank is the tail on the real one ----
        // `nqtC` is final (positions were set only inside D), so the IH applies to it; later rows never
        // read a quant position in D (`RowsAvoidO`), so `FLookLoopAgreeFrom` equates the two tails'
        // capture bank, look bank and view. A lookbehind row and a failed replay have `nqtC == nqt` in
        // content; the same three calls cover them.
        var nqtC := RRA.ClearCps(nqt, D);
        RRA.ClearCpsFinal(nqt, D);
        RRA.ClearCpsFacts(nqt, D);
        assert |nqtC.a_cp| == nquant && |nqtC.a_clk| == nquant;
        FLookLoopCaptureFrameNested(crv, str, next, maxlook, capN, nlk, nqtC, ov1, S, Slook, ncap, nlook, nquant);
        RowsAvoidAt(crv, lid, maxlook, la, body);
        LLAF.FLookLoopAgreeFrom(crv, str, next, maxlook, capN, nlk, nqt, nqtC, ov1, D);
        var resTail := AI.FLookLoop(crv, str, next, maxlook, capN, nlk, nqt, ov1);
        var resTailC := AI.FLookLoop(crv, str, next, maxlook, capN, nlk, nqtC, ov1);
        assert resTail.0 == resTailC.0 && resTail.1 == resTailC.1;
        CM.RegsAgreeOutsideTrans(resTail.0, capN, cap, S);
        CM.RegsAgreeOutsideTrans(resTail.1, nlk, lk, Slook);
      }
  }

  /** C4e: the L4 nested QUANT frame for `FLookLoop` — quant twin of
      `FLookLoopCaptureFrameNested`. Every matched positive-lookahead body may
      NEST looks; the quant bank is written only inside `Sq` (each body's
      OUTSIDE-look quant ids land in `Sq`; its inner-look quants come from the
      body's OWN inner lids, which are OTHER rows also covered by `Sq`). This is
      the nested weakening of `FLookLoopQuantFrame`: NOT the depth-1 LookFree
      per-body hypothesis, but the STATIC `FrameEntryOk` rows (surviving look-bank
      growth) plus the per-row `QIdsOuter(body) <= Sq`. The "matched look has a
      table row" invariant is preserved across each replay via the own-look-ids
      look frame (`ReplayPlusLookFrameNested`) + `LookIdEntryExists`, exactly as
      on the capture side. `decreases maxlook - lid`. */
  lemma FLookLoopQuantFrameNested(crv: CP.FCompiled, str: string, lid: int, maxlook: int,
                                  cap: AReg.Regs, lk: AReg.Regs, qt: AReg.Regs, ov: LOr.OracleView,
                                  S: set<int>, Slook: set<int>, Sq: set<int>, ncap: int, nlook: int, nquant: int)
    requires (forall k :: AI.get_idx(qt.a_cp, k) < 0)
             && (forall k :: AI.get_idx(qt.a_clk, k) >= -1)
    // (G3a) the wf block: a lookahead row's replay reconstructs, and `ReplayPlusRowLA` reads these
    requires ncap >= 0 && nlook >= 0 && nquant >= 0
    requires |qt.a_cp| == nquant && |qt.a_clk| == nquant
    requires |cap.a_cp| == ncap && |cap.a_clk| == ncap && PIV.CapRegWf(cap)
    requires |lk.a_cp| == nlook && |lk.a_clk| == nlook
    requires CM.LookCpsLE(lk, |str|)
    requires RowsAvoidO(crv, lid, maxlook)   // (G3a) later rows never name a row's outside-look quantifiers
    requires forall l: int, la: R.lookaround, body: R.regex ::
               lid <= l <= maxlook && LTB.LookEntryOk(crv, l, la, body) ==>
                 FrameEntryOk(crv, la, body, S, Slook) && QIdsOuter(body) <= Sq
    requires forall l: int :: lid <= l <= maxlook && AReg.get_cp(lk, l).Some? ==>
                                exists la: R.lookaround, body: R.regex :: LTB.LookEntryOk(crv, l, la, body)
    ensures var res := AI.FLookLoop(crv, str, lid, maxlook, cap, lk, qt, ov);
            CM.RegsAgreeOutside(res.2, qt, Sq)
    decreases maxlook - lid
  {
    if lid > maxlook { return; }
    var next := lid + 1;
    RowsAvoidSuffix(crv, lid, maxlook);
    match AReg.get_cp(lk, lid)
    case None =>
      FLookLoopQuantFrameNested(crv, str, next, maxlook, cap, lk, qt, ov, S, Slook, Sq, ncap, nlook, nquant);
    case Some(cp) =>
      var looktype := if 0 <= lid < |crv.f_look_types| then crv.f_look_types[lid] else R.Lookahead;
      if !AI.capture_type(looktype) {
        FLookLoopQuantFrameNested(crv, str, next, maxlook, cap, lk, qt, ov, S, Slook, Sq, ncap, nlook, nquant);
      } else {
        var la: R.lookaround, body: R.regex :| LTB.LookEntryOk(crv, lid, la, body);
        assert 0 <= lid < |crv.f_look_types| && crv.f_look_types[lid] == la;
        assert looktype == la;
        assert FrameEntryOk(crv, la, body, S, Slook) && QIdsOuter(body) <= Sq;
        assert la.Lookahead? || la.Lookbehind?;            // (L5 F7c-2) capture_type; per-kind dispatch below
        assert {:split_here} true;
        var bytecode := AI.get_code_v(crv.f_look_capture_bc, lid);
        var dir := AI.capture_direction(looktype);
        var lookcdn := if 0 <= lid < |crv.f_look_cdns| then crv.f_look_cdns[lid] else [];
        var lookast := if 0 <= lid < |crv.f_look_ast| then crv.f_look_ast[lid] else R.Re_empty;
        assert lookast == body;
        assert bytecode == CP.compile_to_bytecode(CP.capture_regex(la, body));
        var (result, ov1) := AI.FFindMatchPlus(bytecode, lookast, crv.f_plus_bc, str, ov, dir,
                                               cp, cap, lk, qt, 0, lookcdn);
        var capN := if result.None? then cap else result.value.capture_regs;
        var nlk := if result.None? then lk else result.value.look_regs;
        var nqt := if result.None? then qt else result.value.quant_regs;
        var D := QIdsOuter(body);
        assert 0 <= cp <= |str| by { assert AI.get_idx(lk.a_cp, lid) == cp; }   // LookCpsLE + get_cp.Some?
        var ctxc := AI.cp_context(cp, str, dir);
        var inits := AI.FInitState(bytecode, cp, cap, lk, qt, 0, ctxc);
        assert {:split_here} true;
        // (L5 F7c-2) per-kind replay frames. Both kinds give the same wf block for the new banks; only the
        // lookahead row may leave quant POSITIONS set, and only inside `D`.
        if la.Lookahead? {
          assert CP.capture_regex(la, body) == body;
          assert bytecode == CP.compile_to_bytecode(body);
          assert dir == LAnc.Forward;
          assert ctxc.nextchar == AI.get_char(str, cp);
          ReplayPlusRowLAS(bytecode, str, ov, lookcdn, crv.f_plus_bc, cp, cap, lk, qt, body, ncap, nlook, nquant);
        } else {
          assert CP.capture_regex(la, body) == R.reverse_regex(body);
          assert bytecode == CP.compile_to_bytecode(R.reverse_regex(body));
          assert dir == LAnc.Backward;
          assert ctxc.nextchar == AI.get_char(str, cp - 1);
          ReplayPlusRowLBS(bytecode, str, ov, lookcdn, crv.f_plus_bc, cp, cap, lk, qt, body, ncap, nlook, nquant);   // (G3b)
        }
        assert {:split_here} true;
        // ---- what both kinds deliver ----
        assert result.Some? ==> CM.ThreadRegsWf(result.value, ncap, nlook, nquant);
        assert |capN.a_cp| == ncap && |capN.a_clk| == ncap && PIV.CapRegWf(capN);
        assert |nlk.a_cp| == nlook && |nlk.a_clk| == nlook && CM.LookCpsLE(nlk, |str|);
        assert |nqt.a_cp| == nquant && |nqt.a_clk| == nquant;
        assert (forall k :: AI.get_idx(nqt.a_clk, k) >= -1)
            && (forall k :: k !in D ==> AI.get_idx(nqt.a_cp, k) < 0);
        assert CM.RegsAgreeOutside(nlk, lk, LookIdSet(body)) by {
          if result.Some? {} else { assert nlk == lk; }
        }

        // ---- preserve the "matched look has a table row" invariant for nlk ----
        assert forall l: int :: next <= l <= maxlook && AReg.get_cp(nlk, l).Some? ==>
                                  exists la2: R.lookaround, body2: R.regex :: LTB.LookEntryOk(crv, l, la2, body2)
        by {
          forall l: int | next <= l <= maxlook && AReg.get_cp(nlk, l).Some?
            ensures exists la2: R.lookaround, body2: R.regex :: LTB.LookEntryOk(crv, l, la2, body2)
          {
            if AReg.get_cp(lk, l).Some? {
            } else {
              assert result.Some?;
              NewLookInBody(nlk, lk, body, l);
              assert LTB.LookTablesOk(body, crv);
              LookIdEntryExists(body, crv, l as nat);
            }
          }
        }

        // ---- this replay's quant frame, weakened to Sq ----
        assert CM.RegsAgreeOutside(nqt, qt, Sq) by {
          if result.Some? {
            assert CM.RegsAgreeOutside(nqt, qt, D);
            CM.RegsAgreeOutsideWeaken(nqt, qt, D, Sq);
          } else {
            assert CM.RegsAgreeOutside(qt, qt, Sq);
          }
        }
        assert {:split_here} true;
        // ---- (G3a) clear-and-transfer: the tail on the CLEARED bank is the tail on the real one ----
        var nqtC := RRA.ClearCps(nqt, D);
        RRA.ClearCpsFinal(nqt, D);
        RRA.ClearCpsFacts(nqt, D);
        assert |nqtC.a_cp| == nquant && |nqtC.a_clk| == nquant;
        FLookLoopQuantFrameNested(crv, str, next, maxlook, capN, nlk, nqtC, ov1, S, Slook, Sq, ncap, nlook, nquant);
        RowsAvoidAt(crv, lid, maxlook, la, body);
        LLAF.FLookLoopAgreeFrom(crv, str, next, maxlook, capN, nlk, nqt, nqtC, ov1, D);
        var resTail := AI.FLookLoop(crv, str, next, maxlook, capN, nlk, nqt, ov1);
        var resTailC := AI.FLookLoop(crv, str, next, maxlook, capN, nlk, nqtC, ov1);
        assert resTail.0 == resTailC.0 && resTail.1 == resTailC.1;
        // the real tail's quant bank differs from the cleared tail's only inside D <= Sq, as do nqt and nqtC
        RRA.QAgreeIdx(resTail.2, resTailC.2, D);
        CM.RegsAgreeOutsideWeaken(resTail.2, resTailC.2, D, Sq);
        RRA.QAgreeIdx(nqt, nqtC, D);
        assert CM.RegsAgreeOutside(nqtC, nqt, Sq);
        CM.RegsAgreeOutsideTrans(resTail.2, resTailC.2, nqtC, Sq);
        CM.RegsAgreeOutsideTrans(resTail.2, nqtC, nqt, Sq);
        CM.RegsAgreeOutsideTrans(resTail.2, nqt, qt, Sq);
      }
  }

  /** R2: nested twin of `FreshMatchWf` — register well-formedness of a nested
      body's FRESH forward match. Only the no-true-quant-stamp step is fragment
      specific (`NoTrueQuantStampNested`); the rest is structural. */
  lemma FreshMatchWfNested(bytecode: RB.code, str: string, cp: int, ov: LOr.OracleView, cdn: LCdn.cdns,
                           body: R.regex, ncap: int, nlook: int, nquant: int)
    requires NR.NestedFragmentRE(body) && PIV.CapUnique(body) && PIV.QuantUnique(body)
    requires NR.NoNulledPlusRE(body)   // §2.5b interim: all stamps false
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
    NoTrueQuantStampNested(body);
    assert VmQuantFinal(inits) by {
      assert QuantRegsFinal(AI.init_thread(AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant)));
    }
    FFindMatchThreadFacts(bytecode, str, inits, ov, dir, cdn, ncap, nlook, nquant);
  }

  /** R2: nested twin of `ReplayThreadWfLA` — the nested lookahead replay
      preserves register well-formedness (lengths + `CapRegWf`). Only
      `NoTrueQuantStampNested` is fragment specific. */
  lemma ReplayThreadWfLANested(bytecode: RB.code, str: string, cp: int, cap: AReg.Regs, lk: AReg.Regs,
                               qt: AReg.Regs, ov: LOr.OracleView, lookcdn: LCdn.cdns, plus_bcv: seq<RB.code>,
                               body: R.regex, la: R.lookaround, ncap: int, nlook: int, nquant: int)
    requires NR.NestedFragmentRE(body) && PIV.CapUnique(body) && PIV.QuantUnique(body)
    requires NR.NoNulledPlusRE(body)   // §2.5b interim: all stamps false
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
    FFindMatchRegsWf(bytecode, str, inits, ov, dir, lookcdn, ncap, nlook, nquant);
    NoTrueQuantStampNested(body);
    assert VmQuantFinal(inits) by { assert QuantRegsFinal(AI.init_thread(cap, lk, qt)); }
    FFindMatchQuantFinalAny(bytecode, str, inits, ov, dir, lookcdn);
    var (fmres, ovx) := AI.FFindMatch(bytecode, str, inits, ov, dir, lookcdn);
    if fmres.Some? {
      FNulledPlusIdentity(body, fmres.value.capture_regs, fmres.value.look_regs, fmres.value.quant_regs,
                          plus_bcv, str, ovx, dir);
    }
  }

  /** R2: the nested lookahead replay only records look cps in `[.., |str|]`, so
      the `LookCpsLE(_, |str|)` invariant (which underwrites `cp_ctx_ok` on the
      recorded look positions) is PRESERVED across the replay. `CM.FFindMatch
      LookCpOk` bounds the FFindMatch result; `FNulledPlusIdentity` ties the
      FFindMatchPlus look bank to it. */
  lemma ReplayLookCpOkNested(bytecode: RB.code, str: string, ov: LOr.OracleView, dir: LAnc.direction,
                             lookcdn: LCdn.cdns, plus_bcv: seq<RB.code>, cp: int,
                             cap: AReg.Regs, lk: AReg.Regs, qt: AReg.Regs, body: R.regex)
    requires NR.NestedFragmentRE(body) && PIV.CapUnique(body) && PIV.QuantUnique(body)
    requires NR.NoNulledPlusRE(body)   // §2.5b interim: all stamps false
    requires dir == LAnc.Forward
    requires bytecode == CP.compile_to_bytecode(body)
    requires 0 <= cp <= |str|
    requires (forall k :: AI.get_idx(qt.a_cp, k) < 0)
             && (forall k :: AI.get_idx(qt.a_clk, k) >= -1)
    requires CM.LookCpsLE(lk, |str|)
    ensures var r := AI.FFindMatchPlus(bytecode, body, plus_bcv, str, ov, dir, cp, cap, lk, qt, 0, lookcdn).0;
            r.Some? ==> CM.LookCpsLE(r.value.look_regs, |str|)
  {
    var ctx := AI.cp_context(cp, str, dir);
    var inits := AI.FInitState(bytecode, cp, cap, lk, qt, 0, ctx);
    assert CM.VmLookCpOk(inits, |str|) by {
      assert AI.init_thread(cap, lk, qt).look_regs == lk;
      assert inits.active == [AI.init_thread(cap, lk, qt)];
    }
    CM.FFindMatchLookCpOk(bytecode, str, inits, ov, dir, lookcdn);
    NoTrueQuantStampNested(body);
    assert VmQuantFinal(inits) by { assert QuantRegsFinal(AI.init_thread(cap, lk, qt)); }
    FFindMatchQuantFinalAny(bytecode, str, inits, ov, dir, lookcdn);
    var (res0, ovx) := AI.FFindMatch(bytecode, str, inits, ov, dir, lookcdn);
    if res0.Some? {
      var th := res0.value;
      FNulledPlusIdentity(body, th.capture_regs, th.look_regs, th.quant_regs, plus_bcv, str, ovx, dir);
    }
  }

  /** R2 DELIVERABLE 2 (value predicate): the OUTER-caps value-lift conclusion.
      On each matched positive lookahead's own OUTSIDE-look capture registers
      `CaptureRegsSet(CapIdsOutsideLooks(VBody(crv,l)))`, `res0` carries that
      body's FRESH match (or stays unset if the fresh body did not match). The
      restriction to OUTER caps is deliberate: a fresh single body match of a
      NESTED body compiles inner looks to CheckOracle leaves recording NONE of
      their captures, and the DEEPER lids' own iterations overwrite `res0`'s
      inner-look slots -- so `res0` agrees with the (inner-blind) fresh match
      only on the body's directly-captured groups. */
  lemma GetCpAgreeIdx(a: AReg.Regs, b: AReg.Regs, k: int)
    requires AI.get_idx(a.a_cp, k) == AI.get_idx(b.a_cp, k)
    ensures AReg.get_cp(a, k) == AReg.get_cp(b, k)
  {
    if 0 <= k < |a.a_cp| && 0 <= k < |b.a_cp| {
      assert a.a_cp[k] == AI.get_idx(a.a_cp, k) == AI.get_idx(b.a_cp, k) == b.a_cp[k];
    } else if 0 <= k < |a.a_cp| {
      assert a.a_cp[k] == AI.get_idx(a.a_cp, k) == AI.get_idx(b.a_cp, k) == -1;
    } else if 0 <= k < |b.a_cp| {
      assert b.a_cp[k] == AI.get_idx(b.a_cp, k) == AI.get_idx(a.a_cp, k) == -1;
    }
  }

  /** R3 STABILITY: the FINAL look bank agrees with the input `lk` at index `lid`.
      The whole fold over `[lid,maxlook]` only writes look ids in each matched
      body's `LookIdSet` (`FLookLoopCaptureFrameNested`), and by well-nestedness
      (hyp (h)) `lid` is in NONE of them. So framing against `Slook - {lid}` (the
      shape/`LookIdSet` requirement survives because `lid !in LookIdSet(body)`)
      pins `get_cp(res.1, lid) == get_cp(lk, lid)`. This is the fact that lets R3
      re-key `lid`'s coverage from `lk` onto `res.1`, and shows `lid` unmatched in
      `lk` stays unmatched in `res.1`. */
  lemma FLookLoopLidCpStable(crv: CP.FCompiled, str: string, lid: int, maxlook: int,
      cap: AReg.Regs, lk: AReg.Regs, qt: AReg.Regs, ov: LOr.OracleView,
      S: set<int>, Slook: set<int>, ncap: int, nlook: int, nquant: int)
    requires (forall k :: AI.get_idx(qt.a_cp, k) < 0)
             && (forall k :: AI.get_idx(qt.a_clk, k) >= -1)
    // (G3a) the wf block: a lookahead row's replay reconstructs, and `ReplayPlusRowLA` reads these
    requires ncap >= 0 && nlook >= 0 && nquant >= 0
    requires |qt.a_cp| == nquant && |qt.a_clk| == nquant
    requires |cap.a_cp| == ncap && |cap.a_clk| == ncap && PIV.CapRegWf(cap)
    requires |lk.a_cp| == nlook && |lk.a_clk| == nlook
    requires CM.LookCpsLE(lk, |str|)
    requires RowsAvoidO(crv, lid, maxlook)   // (G3a) later rows never name a row's outside-look quantifiers
    requires forall l: int, la: R.lookaround, body: R.regex ::
               lid <= l <= maxlook && LTB.LookEntryOk(crv, l, la, body) ==> FrameEntryOk(crv, la, body, S, Slook)
    requires forall l: int :: lid <= l <= maxlook && AReg.get_cp(lk, l).Some? ==>
                                 exists la: R.lookaround, body: R.regex :: LTB.LookEntryOk(crv, l, la, body)
    requires forall l1: int, la1: R.lookaround, b1: R.regex ::                                  // (h)@lid
               lid <= l1 <= maxlook && LTB.LookEntryOk(crv, l1, la1, b1) ==> lid !in LookIdSet(b1)
    ensures AReg.get_cp(AI.FLookLoop(crv, str, lid, maxlook, cap, lk, qt, ov).1, lid)
         == AReg.get_cp(lk, lid)
  {
    var Slookp := Slook - {lid};
    forall l: int, la: R.lookaround, body: R.regex | lid <= l <= maxlook && LTB.LookEntryOk(crv, l, la, body)
      ensures FrameEntryOk(crv, la, body, S, Slookp)
    {
      assert FrameEntryOk(crv, la, body, S, Slook);   // LookIdSet(body) <= Slook
      assert lid !in LookIdSet(body);
      assert LookIdSet(body) <= Slookp;
    }
    FLookLoopCaptureFrameNested(crv, str, lid, maxlook, cap, lk, qt, ov, S, Slookp, ncap, nlook, nquant);
    var res := AI.FLookLoop(crv, str, lid, maxlook, cap, lk, qt, ov);
    assert CM.RegsAgreeOutside(res.1, lk, Slookp);
    assert lid !in Slookp;
    assert AI.get_idx(res.1.a_cp, lid) == AI.get_idx(lk.a_cp, lid);
    GetCpAgreeIdx(res.1, lk, lid);
  }

  /** C4c STABILITY (clock twin of `FLookLoopLidCpStable`): the FINAL look bank's
      CLOCK at index `lid` is unchanged by the fold. Same argument — the fold only
      writes look ids in matched bodies' `LookIdSet`, none of which is `lid` by
      well-nestedness (h), so `RegsAgreeOutside(res.1, lk, Slook - {lid})` (which
      constrains BOTH `a_cp` and `a_clk`) pins the `a_clk` slot too. This is the
      look-clock stability the ancestor-chain assembly needs: an ancestor look
      `l`'s clock, set by an EARLIER stage (its parent's replay, or the main match
      for a top-level `l`), survives every LATER fold iteration untouched — so the
      chain read on the FINAL `res.1` equals the chain as each stage left it. */
  lemma FLookLoopTopLookClkStableFull(crv: CP.FCompiled, str: string, lid: int, maxlook: int, l: int,
      cap: AReg.Regs, lk: AReg.Regs, qt: AReg.Regs, ov: LOr.OracleView,
      S: set<int>, Slook: set<int>, ncap: int, nlook: int, nquant: int)
    requires (forall k :: AI.get_idx(qt.a_cp, k) < 0)
             && (forall k :: AI.get_idx(qt.a_clk, k) >= -1)
    // (G3a) the wf block: a lookahead row's replay reconstructs, and `ReplayPlusRowLA` reads these
    requires ncap >= 0 && nlook >= 0 && nquant >= 0
    requires |qt.a_cp| == nquant && |qt.a_clk| == nquant
    requires |cap.a_cp| == ncap && |cap.a_clk| == ncap && PIV.CapRegWf(cap)
    requires |lk.a_cp| == nlook && |lk.a_clk| == nlook
    requires CM.LookCpsLE(lk, |str|)
    requires RowsAvoidO(crv, lid, maxlook)   // (G3a) later rows never name a row's outside-look quantifiers
    requires forall l0: int, la: R.lookaround, body: R.regex ::
               lid <= l0 <= maxlook && LTB.LookEntryOk(crv, l0, la, body) ==> FrameEntryOk(crv, la, body, S, Slook)
    requires forall l0: int :: lid <= l0 <= maxlook && AReg.get_cp(lk, l0).Some? ==>
                                 exists la: R.lookaround, body: R.regex :: LTB.LookEntryOk(crv, l0, la, body)
    requires forall l1: int, la1: R.lookaround, b1: R.regex ::                                  // (h')@l
               lid <= l1 <= maxlook && LTB.LookEntryOk(crv, l1, la1, b1) ==> l !in LookIdSet(b1)
    ensures AI.get_idx(AI.FLookLoop(crv, str, lid, maxlook, cap, lk, qt, ov).1.a_clk, l)
         == AI.get_idx(lk.a_clk, l)
  {
    var Slookp := Slook - {l};
    forall l0: int, la: R.lookaround, body: R.regex | lid <= l0 <= maxlook && LTB.LookEntryOk(crv, l0, la, body)
      ensures FrameEntryOk(crv, la, body, S, Slookp)
    {
      assert FrameEntryOk(crv, la, body, S, Slook);   // LookIdSet(body) <= Slook
      assert l !in LookIdSet(body);
      assert LookIdSet(body) <= Slookp;
    }
    FLookLoopCaptureFrameNested(crv, str, lid, maxlook, cap, lk, qt, ov, S, Slookp, ncap, nlook, nquant);
    var res := AI.FLookLoop(crv, str, lid, maxlook, cap, lk, qt, ov);
    assert CM.RegsAgreeOutside(res.1, lk, Slookp);
    assert l !in Slookp;
  }

  /** (cp twin of `FLookLoopTopLookClkStableFull`) WHOLE-LOOP top-look POSITION
      stability: for ANY stable index `l` in NO replayed body's `LookIdSet` (in
      particular any TOP-LEVEL look of `re`, `TopLookNotNested`), the FINAL look
      bank's recorded position at `l` is unchanged by the ENTIRE fold from `lid` to
      `maxlook`. Same argument as `FLookLoopTopLookClkStableFull` read off the
      `a_cp` slot and finished by `GetCpAgreeIdx`. This is the whole-loop POSITION
      stability the reverse-recon descent needs to transport `MatchedPosLA` /
      `FreshBodyMatch` (which read only `get_cp(lk, l)` at index `l`) from the
      reconstructed bank `res.1 = FLookLoop(...).1` back onto the winning thread's
      `look_regs` at a top look `l`. */
  lemma FLookLoopTopLookCpStableFull(crv: CP.FCompiled, str: string, lid: int, maxlook: int, l: int,
      cap: AReg.Regs, lk: AReg.Regs, qt: AReg.Regs, ov: LOr.OracleView,
      S: set<int>, Slook: set<int>, ncap: int, nlook: int, nquant: int)
    requires (forall k :: AI.get_idx(qt.a_cp, k) < 0)
             && (forall k :: AI.get_idx(qt.a_clk, k) >= -1)
    // (G3a) the wf block: a lookahead row's replay reconstructs, and `ReplayPlusRowLA` reads these
    requires ncap >= 0 && nlook >= 0 && nquant >= 0
    requires |qt.a_cp| == nquant && |qt.a_clk| == nquant
    requires |cap.a_cp| == ncap && |cap.a_clk| == ncap && PIV.CapRegWf(cap)
    requires |lk.a_cp| == nlook && |lk.a_clk| == nlook
    requires CM.LookCpsLE(lk, |str|)
    requires RowsAvoidO(crv, lid, maxlook)   // (G3a) later rows never name a row's outside-look quantifiers
    requires forall l0: int, la: R.lookaround, body: R.regex ::
               lid <= l0 <= maxlook && LTB.LookEntryOk(crv, l0, la, body) ==> FrameEntryOk(crv, la, body, S, Slook)
    requires forall l0: int :: lid <= l0 <= maxlook && AReg.get_cp(lk, l0).Some? ==>
                                 exists la: R.lookaround, body: R.regex :: LTB.LookEntryOk(crv, l0, la, body)
    requires forall l1: int, la1: R.lookaround, b1: R.regex ::                                  // (h')@l
               lid <= l1 <= maxlook && LTB.LookEntryOk(crv, l1, la1, b1) ==> l !in LookIdSet(b1)
    ensures AReg.get_cp(AI.FLookLoop(crv, str, lid, maxlook, cap, lk, qt, ov).1, l)
         == AReg.get_cp(lk, l)
  {
    var Slookp := Slook - {l};
    forall l0: int, la: R.lookaround, body: R.regex | lid <= l0 <= maxlook && LTB.LookEntryOk(crv, l0, la, body)
      ensures FrameEntryOk(crv, la, body, S, Slookp)
    {
      assert FrameEntryOk(crv, la, body, S, Slook);   // LookIdSet(body) <= Slook
      assert l !in LookIdSet(body);
      assert LookIdSet(body) <= Slookp;
    }
    FLookLoopCaptureFrameNested(crv, str, lid, maxlook, cap, lk, qt, ov, S, Slookp, ncap, nlook, nquant);
    var res := AI.FLookLoop(crv, str, lid, maxlook, cap, lk, qt, ov);
    assert CM.RegsAgreeOutside(res.1, lk, Slookp);
    assert l !in Slookp;
    assert AI.get_idx(res.1.a_cp, l) == AI.get_idx(lk.a_cp, l);
    GetCpAgreeIdx(res.1, lk, l);
  }

  /** (reconciliation) `MatchedPosLA` and `FreshBodyMatch` at index `l` read the
      look bank ONLY through `AReg.get_cp(lk, l)` (the recorded position of look
      `l`). So two look banks that agree at that one slot yield the SAME
      `MatchedPosLA` verdict and the SAME fresh body match. Combined with
      `FLookLoopTopLookCpStableFull` (`get_cp` stable at a top look under the
      whole fold), this transports both `MatchedPosLA` and `FreshBodyMatch` from
      the reconstructed bank `res.1 = FLookLoop(...).1` onto the winning thread's
      `look_regs` at a top look — the reconciliation the reverse-recon descent
      needs to key A1/A2's outputs (stated on `res.1`) onto the SIM carrier's
      thread banks. */
  ghost predicate FLookLoopValueOkFull(crv: CP.FCompiled, str: string, res0: AReg.Regs, res1: AReg.Regs,
                                       lid: int, maxlook: int, ov: LOr.OracleView, ncap: int, nlook: int, nquant: int) {
    forall owner: int :: lid <= owner <= maxlook && MatchedPosLA(crv, res1, owner) ==>
                           var rf := FreshBodyMatchPlus(crv, str, owner, res1, ov, ncap, nlook, nquant);
                           (rf.Some? ==> CM.RegsAgreeInside(res0, rf.value.capture_regs,
                                                            PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(VBody(crv, owner)))))
                           && (rf.None? ==> CM.RegsAgreeInside(res0, AReg.init_regs(ncap),
                                                               PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(VBody(crv, owner)))))
  }

  /** R3: `owner == lid` is not a matched positive lookahead in `res1`, so the
      full value map for `[lid, maxlook]` (keyed on `res1`) is exactly the one for
      `[lid+1, maxlook]`. Full twin of `ValueOkOuterSkipLid`. */
  lemma ValueOkFullSkipLid(crv: CP.FCompiled, str: string, res0: AReg.Regs, res1: AReg.Regs,
                           lid: int, maxlook: int, ov: LOr.OracleView, ncap: int, nlook: int, nquant: int)
    requires FLookLoopValueOkFull(crv, str, res0, res1, lid + 1, maxlook, ov, ncap, nlook, nquant)
    requires !MatchedPosLA(crv, res1, lid)
    ensures FLookLoopValueOkFull(crv, str, res0, res1, lid, maxlook, ov, ncap, nlook, nquant)
  {
    forall owner: int | lid <= owner <= maxlook && MatchedPosLA(crv, res1, owner)
      ensures var rf := FreshBodyMatchPlus(crv, str, owner, res1, ov, ncap, nlook, nquant);
              (rf.Some? ==> CM.RegsAgreeInside(res0, rf.value.capture_regs,
                                               PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(VBody(crv, owner)))))
              && (rf.None? ==> CM.RegsAgreeInside(res0, AReg.init_regs(ncap),
                                                  PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(VBody(crv, owner)))))
    { assert owner != lid; }
  }

  /** R3 DELIVERABLE 1 (value lift): THE nested FLookLoop VALUE LIFT keyed on the
      FINAL look bank `res.1`. Generalizes `FLookLoopValueLiftOuter` (keyed on the
      loop's INPUT `lk`) so that INNER looks — matched only PART-WAY through the
      loop, when an OUTER look's replay crosses their CheckOracle gates and writes
      their `a_cp` into the threaded look bank — are RETAINED. Same hypotheses as
      `FLookLoopValueLiftOuter` PLUS (h) well-nested lids: this ordering fact
      (`LookIdSet(body)` sits strictly ABOVE the enclosing lid; caller-
      dischargeable from `LidsWellNested`) is what R3 needs and (f)/(g) do NOT
      give — (f) requires its target already matched in `lk`, so it cannot pin
      `lid !in LookIdSet(body_lid)` (self) nor cover an unmatched-in-`lk` `lid`.
      The recursion mirrors `FLookLoopValueLiftOuter`; the extra re-keying step is
      the R3 stability fact `FLookLoopLidCpStable` (`get_cp(res.1, lid) ==
      get_cp(lk, lid)`), which converts `lid`'s `lk`-keyed coverage onto `res.1`
      and settles the unmatched cases; owners `> lid` come DIRECTLY from the IH
      (already keyed on `res.1`), simpler than R2's `nlk`↔`lk` reconciliation.
      `decreases maxlook - lid`. */
  lemma FLookLoopValueLiftFull(crv: CP.FCompiled, str: string, lid: int, maxlook: int,
                                                     cap: AReg.Regs, lk: AReg.Regs, qt: AReg.Regs, ov: LOr.OracleView,
                                                     S: set<int>, Slook: set<int>, ncap: int, nlook: int, nquant: int)
    requires ncap >= 0 && nlook >= 0 && nquant >= 0
    requires (forall k :: AI.get_idx(qt.a_cp, k) < 0)
             && (forall k :: AI.get_idx(qt.a_clk, k) >= -1)
    requires |qt.a_cp| == nquant && |qt.a_clk| == nquant
    requires |cap.a_cp| == ncap && |cap.a_clk| == ncap && PIV.CapRegWf(cap)
    requires |lk.a_cp| == nlook && |lk.a_clk| == nlook
    requires CM.LookCpsLE(lk, |str|)                                                            // (e)
    requires forall l: int, la: R.lookaround, body: R.regex ::                                   // (a)
               lid <= l <= maxlook && LTB.LookEntryOk(crv, l, la, body) ==> FrameEntryOk(crv, la, body, S, Slook)
    requires forall l: int :: lid <= l <= maxlook && AReg.get_cp(lk, l).Some? ==>                // (b)
                                exists la: R.lookaround, body: R.regex :: LTB.LookEntryOk(crv, l, la, body)
    requires forall l: int, la: R.lookaround, body: R.regex ::                                   // (c') full per-body-unset
               lid <= l <= maxlook && LTB.LookEntryOk(crv, l, la, body) ==>
                 CM.RegsAgreeInside(cap, AReg.init_regs(ncap), PIV.CaptureRegs(body))
    requires forall l1: int, la1: R.lookaround, b1: R.regex, l2: int, la2: R.lookaround, b2: R.regex ::  // (D-ord)
               lid <= l1 <= maxlook && lid <= l2 <= maxlook && l1 < l2
               && LTB.LookEntryOk(crv, l1, la1, b1) && LTB.LookEntryOk(crv, l2, la2, b2) ==>
                 PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(b1)) * PIV.CaptureRegs(b2) == {}
    requires forall l1: int, la1: R.lookaround, b1: R.regex, l2: int ::                          // (f) look-stability
               (lid <= l1 <= maxlook && LTB.LookEntryOk(crv, l1, la1, b1)
               && lid <= l2 <= maxlook && l2 != l1 && AReg.get_cp(lk, l2).Some?) ==> l2 !in LookIdSet(b1)
    requires forall l1: int, la1: R.lookaround, b1: R.regex, l2: int, la2: R.lookaround, b2: R.regex ::  // (g_new)
               lid <= l1 <= maxlook && lid <= l2 <= maxlook && l1 < l2
               && LTB.LookEntryOk(crv, l1, la1, b1) && LTB.LookEntryOk(crv, l2, la2, b2) ==>
                 DirectLookIds(b1) * LTB.LookIds(b2) == {}
    requires forall l1: int, la1: R.lookaround, b1: R.regex, l2: int ::                          // (h) well-nested lids
               lid <= l1 <= maxlook && LTB.LookEntryOk(crv, l1, la1, b1) && lid <= l2 <= l1 ==> l2 !in LookIdSet(b1)
    // (G3a) a lookahead row may reconstruct a nulled plus: the replay reads the quant bank at the
    // body's quantifiers (A4), and the tail runs on the cleared bank (A5)
    requires RowsAvoidO(crv, lid, maxlook)
    requires forall l: int, la: R.lookaround, body: R.regex ::                                   // (c'q) per-body quant-unset
               lid <= l <= maxlook && LTB.LookEntryOk(crv, l, la, body) ==>
                 CM.RegsAgreeInside(qt, AReg.init_regs(nquant), LKC.QIdsInt(body))
    requires forall l1: int, la1: R.lookaround, b1: R.regex, l2: int, la2: R.lookaround, b2: R.regex ::  // (D-ord-q)
               lid <= l1 <= maxlook && lid <= l2 <= maxlook && l1 < l2
               && LTB.LookEntryOk(crv, l1, la1, b1) && LTB.LookEntryOk(crv, l2, la2, b2) ==>
                 QIdsOuter(b1) * LKC.QIdsInt(b2) == {}
    ensures var res := AI.FLookLoop(crv, str, lid, maxlook, cap, lk, qt, ov);
            |res.0.a_cp| == ncap && |res.0.a_clk| == ncap && PIV.CapRegWf(res.0)
            && |res.1.a_cp| == nlook && |res.1.a_clk| == nlook          // L4 PERF: expose the look-bank length
            && |res.2.a_cp| == nquant && |res.2.a_clk| == nquant        // L4 PERF: expose the quant-bank length
            && FLookLoopValueOkFull(crv, str, res.0, res.1, lid, maxlook, ov, ncap, nlook, nquant)
    decreases maxlook - lid
  {
    var res := AI.FLookLoop(crv, str, lid, maxlook, cap, lk, qt, ov);
    assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
    if lid > maxlook {
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert res.0 == cap;
      return;
    }
    var next := lid + 1;
    RowsAvoidSuffix(crv, lid, maxlook);
    match AReg.get_cp(lk, lid)
    case None =>
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert res == AI.FLookLoop(crv, str, next, maxlook, cap, lk, qt, ov);
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      FLookLoopValueLiftFull(crv, str, next, maxlook, cap, lk, qt, ov, S, Slook, ncap, nlook, nquant);
      // stability: res.1 agrees with lk at lid; lk is None there => res.1 None => not matched
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert forall l1: int, la1: R.lookaround, b1: R.regex ::
          lid <= l1 <= maxlook && LTB.LookEntryOk(crv, l1, la1, b1) ==> lid !in LookIdSet(b1);   // (h)@lid, l2:=lid
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      FLookLoopLidCpStable(crv, str, lid, maxlook, cap, lk, qt, ov, S, Slook, ncap, nlook, nquant);
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert AReg.get_cp(res.1, lid) == AReg.get_cp(lk, lid);
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert !MatchedPosLA(crv, res.1, lid);
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      ValueOkFullSkipLid(crv, str, res.0, res.1, lid, maxlook, ov, ncap, nlook, nquant);
    case Some(cp) =>
      var looktype := if 0 <= lid < |crv.f_look_types| then crv.f_look_types[lid] else R.Lookahead;
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      if !AI.capture_type(looktype) {
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert res == AI.FLookLoop(crv, str, next, maxlook, cap, lk, qt, ov);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        FLookLoopValueLiftFull(crv, str, next, maxlook, cap, lk, qt, ov, S, Slook, ncap, nlook, nquant);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert !MatchedPosLA(crv, res.1, lid);   // !capture_type(looktype), looktype == f_look_types[lid]
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        ValueOkFullSkipLid(crv, str, res.0, res.1, lid, maxlook, ov, ncap, nlook, nquant);
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      } else {
        var la: R.lookaround, body: R.regex :| LTB.LookEntryOk(crv, lid, la, body);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert 0 <= lid < |crv.f_look_types| && crv.f_look_types[lid] == la;
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert looktype == la;
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert body == VBody(crv, lid);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert FrameEntryOk(crv, la, body, S, Slook);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert la.Lookahead? || la.Lookbehind?;            // (L5 F7c-2) capture_type
        var bytecode := AI.get_code_v(crv.f_look_capture_bc, lid);
        var dir := AI.capture_direction(looktype);
        var lookcdn := if 0 <= lid < |crv.f_look_cdns| then crv.f_look_cdns[lid] else [];
        var lookast := if 0 <= lid < |crv.f_look_ast| then crv.f_look_ast[lid] else R.Re_empty;
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert lookast == body;
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert bytecode == CP.compile_to_bytecode(CP.capture_regex(la, body));
        var (result, ov1) := AI.FFindMatchPlus(bytecode, lookast, crv.f_plus_bc, str, ov, dir,
                                               cp, cap, lk, qt, 0, lookcdn);
        var capN := if result.None? then cap else result.value.capture_regs;
        var nlk := if result.None? then lk else result.value.look_regs;
        var nqt := if result.None? then qt else result.value.quant_regs;
        // (L5 F7c-2) per-kind replay facts (the `...LB` twins take the BACKWARD ones)
        assert {:split_here} true;
        assert res == AI.FLookLoop(crv, str, next, maxlook, capN, nlk, nqt, ov1);
        assert 0 <= cp <= |str| by {
          assert cp == AI.get_idx(lk.a_cp, lid) && cp >= 0;   // get_cp(lk,lid)==Some(cp)
          assert AI.get_idx(lk.a_cp, lid) <= |str|;            // LookCpsLE
        }
        var D := QIdsOuter(body);
        // the row's value witness: the fresh PLUS replay of `body` from init banks
        var rfLid := FreshBodyMatchPlus(crv, str, lid, lk, ov, ncap, nlook, nquant);
        assert {:split_here} true;
        if la.Lookahead? {
          // (G3a) a lookahead row: the body may hold a CIN-greedy nulled plus
          assert CP.capture_regex(la, body) == body;
          assert bytecode == CP.compile_to_bytecode(body);
          assert dir == LAnc.Forward;
          ReplayPlusRowLAS(bytecode, str, ov, lookcdn, crv.f_plus_bc, cp, cap, lk, qt, body, ncap, nlook, nquant);
          ReplayAgreePlusFresh(bytecode, str, cp, cap, lk, qt, ov, lookcdn, crv.f_plus_bc, body,
                               PIV.CaptureRegs(body), {}, ncap, nlook, nquant);
          assert rfLid == AI.FFindMatchPlus(bytecode, body, crv.f_plus_bc, str, ov, LAnc.Forward, cp,
                                            AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant),
                                            0, lookcdn).0 by {
            reveal FreshBodyMatchPlus();
            assert AReg.get_cp(lk, lid).value == cp;
          }
        } else {
          // a lookbehind row: stamp-free, as before (G3b lifts it)
          assert dir == LAnc.Backward && CP.capture_regex(la, body) == R.reverse_regex(body);
          assert bytecode == CP.compile_to_bytecode(R.reverse_regex(body));
          assert AI.cp_context(cp, str, LAnc.Backward).nextchar == AI.get_char(str, cp - 1);
          // (G3b) a lookbehind row replays the plus machine too
          ReplayPlusRowLBS(bytecode, str, ov, lookcdn, crv.f_plus_bc, cp, cap, lk, qt, body, ncap, nlook, nquant);
          ReplayAgreePlusFreshDir(bytecode, str, cp, cap, lk, qt, ov, lookcdn, crv.f_plus_bc, body,
                                  PIV.CaptureRegs(body), {}, ncap, nlook, nquant, LAnc.Backward);
          assert rfLid == AI.FFindMatchPlus(bytecode, body, crv.f_plus_bc, str, ov, LAnc.Backward, cp,
                                            AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant),
                                            0, lookcdn).0 by {
            reveal FreshBodyMatchPlus();
            assert AReg.get_cp(lk, lid).value == cp;
          }
        }
        assert {:split_here} true;
        // ---- what both kinds deliver ----
        assert ov1 == ov;
        assert CM.RegsAgreeOutside(capN, cap, PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(body))) by {
          if result.Some? {} else { assert capN == cap; }
        }
        assert CM.RegsAgreeOutside(nlk, lk, LookIdSet(body)) by {
          if result.Some? {} else { assert nlk == lk; }
        }
        assert CM.RegsAgreeOutside(nlk, lk, DirectLidSet(body)) by {
          if result.Some? {} else { assert nlk == lk; }
        }
        assert |capN.a_cp| == ncap && |capN.a_clk| == ncap && PIV.CapRegWf(capN)
               && |nqt.a_cp| == nquant && |nqt.a_clk| == nquant && |nlk.a_cp| == nlook && |nlk.a_clk| == nlook by {
          if result.Some? { assert CM.ThreadRegsWf(result.value, ncap, nlook, nquant); }
        }
        assert CM.LookCpsLE(nlk, |str|) by {
          if result.Some? {} else { assert nlk == lk; }
        }
        assert (forall k :: AI.get_idx(nqt.a_clk, k) >= -1)
            && (forall k :: k !in D ==> AI.get_idx(nqt.a_cp, k) < 0) by {
          if result.Some? {} else { assert nqt == qt; }
        }
        assert CM.RegsAgreeOutside(nqt, qt, D) by {
          if result.None? { assert nqt == qt; }   // (G3b) both kinds: the plus row's quant frame
        }
        // the value at lid: the replay agrees with the fresh plus replay on CaptureRegs(body); None iff None
        assert (result.None? <==> rfLid.None?)
               && (result.Some? ==> CM.RegsAgreeInside(capN, rfLid.value.capture_regs, PIV.CaptureRegs(body)));

        var Sp := S - PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(body));

        // ---- recursion hypothesis transfer at [next] with (capN, nlk, nqt) ----
        // (b) matched-look-has-entry for nlk
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert forall l: int :: next <= l <= maxlook && AReg.get_cp(nlk, l).Some? ==>
                                  exists la2: R.lookaround, body2: R.regex :: LTB.LookEntryOk(crv, l, la2, body2)
        by {
          forall l: int | next <= l <= maxlook && AReg.get_cp(nlk, l).Some?
            ensures exists la2: R.lookaround, body2: R.regex :: LTB.LookEntryOk(crv, l, la2, body2)
          {
            if AReg.get_cp(lk, l).Some? {
            } else {
              assert result.Some?;
              assert CM.RegsAgreeOutside(nlk, lk, LookIdSet(body));
              NewLookInBody(nlk, lk, body, l);
              assert LTB.LookTablesOk(body, crv);
              LookIdEntryExists(body, crv, l as nat);
            }
          }
        }
        // (c') full per-body-unset for capN
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert forall l: int, la2: R.lookaround, body2: R.regex ::
            next <= l <= maxlook && LTB.LookEntryOk(crv, l, la2, body2) ==>
              CM.RegsAgreeInside(capN, AReg.init_regs(ncap), PIV.CaptureRegs(body2))
        by {
          forall l: int, la2: R.lookaround, body2: R.regex | next <= l <= maxlook && LTB.LookEntryOk(crv, l, la2, body2)
            ensures CM.RegsAgreeInside(capN, AReg.init_regs(ncap), PIV.CaptureRegs(body2))
          {
            assert CM.RegsAgreeInside(cap, AReg.init_regs(ncap), PIV.CaptureRegs(body2));   // (c')@cap
            assert PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(body)) * PIV.CaptureRegs(body2) == {};   // (D-ord) lid<l
            assert CM.RegsAgreeOutside(capN, cap, PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(body)));
            UnsetOffTransfer(capN, cap, ncap, PIV.CaptureRegs(body2), PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(body)));
          }
        }
        // (f) look-stability for nlk
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert forall l1: int, la1: R.lookaround, b1: R.regex, l2: int ::
            (next <= l1 <= maxlook && LTB.LookEntryOk(crv, l1, la1, b1)
            && next <= l2 <= maxlook && l2 != l1 && AReg.get_cp(nlk, l2).Some?) ==> l2 !in LookIdSet(b1)
        by {
          forall l1: int, la1: R.lookaround, b1: R.regex, l2: int |
            next <= l1 <= maxlook && LTB.LookEntryOk(crv, l1, la1, b1)
            && next <= l2 <= maxlook && l2 != l1 && AReg.get_cp(nlk, l2).Some?
            ensures l2 !in LookIdSet(b1)
          {
            if AReg.get_cp(lk, l2).Some? {
              // (f)@lk
            } else {
              // recon A: l2 newly set => l2 is a DIRECT child of body; (g_new) (lid < l1) => l2 !in LookIds(b1)
              assert result.Some?;
              assert CM.RegsAgreeOutside(nlk, lk, DirectLidSet(body));
              NewLookInBodyDirect(nlk, lk, body, l2);
              assert (l2 as nat) in DirectLookIds(body);
              assert lid < l1;                                          // l1 >= next
              assert DirectLookIds(body) * LTB.LookIds(b1) == {};       // (g_new) with (lid, l1)
              assert (l2 as nat) !in DirectLookIds(body) * LTB.LookIds(b1);
              assert (l2 as nat) !in LTB.LookIds(b1);
              if l2 in LookIdSet(b1) {
                var q: nat :| q in LTB.LookIds(b1) && (q as int) == l2;
                assert q == l2 as nat;
              }
            }
          }
        }
        // (h) well-nested lids for [next] — sub-instance of (h)@lid
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert forall l1: int, la1: R.lookaround, b1: R.regex, l2: int ::
            next <= l1 <= maxlook && LTB.LookEntryOk(crv, l1, la1, b1) && next <= l2 <= l1 ==> l2 !in LookIdSet(b1);

        // (c'q) for the tail, on the CLEARED bank: a later row's quantifiers avoid D (D-ord-q), the
        // replay wrote quants only inside D, and clearing D writes the init value
        var nqtC := RRA.ClearCps(nqt, D);
        RRA.ClearCpsFinal(nqt, D);
        RRA.ClearCpsFacts(nqt, D);
        assert {:split_here} true;
        assert forall l: int, la2: R.lookaround, body2: R.regex ::
            next <= l <= maxlook && LTB.LookEntryOk(crv, l, la2, body2) ==>
              CM.RegsAgreeInside(nqtC, AReg.init_regs(nquant), LKC.QIdsInt(body2))
        by {
          forall l: int, la2: R.lookaround, body2: R.regex | next <= l <= maxlook && LTB.LookEntryOk(crv, l, la2, body2)
            ensures CM.RegsAgreeInside(nqtC, AReg.init_regs(nquant), LKC.QIdsInt(body2))
          {
            assert CM.RegsAgreeInside(qt, AReg.init_regs(nquant), LKC.QIdsInt(body2));   // (c'q)@qt
            assert D * LKC.QIdsInt(body2) == {};                                          // (D-ord-q) lid < l
            RRA.QAgreeIdx(nqt, nqtC, D);
            forall k | k in LKC.QIdsInt(body2)
              ensures AI.get_idx(nqtC.a_cp, k) == AI.get_idx(AReg.init_regs(nquant).a_cp, k)
                      && AI.get_idx(nqtC.a_clk, k) == AI.get_idx(AReg.init_regs(nquant).a_clk, k)
            {
              assert k !in D * LKC.QIdsInt(body2);
              assert k !in D;
            }
          }
        }
        assert {:split_here} true;
        // the IH on the cleared bank; A5 equates the two tails off the quant bank
        FLookLoopValueLiftFull(crv, str, next, maxlook, capN, nlk, nqtC, ov1, S, Slook, ncap, nlook, nquant);
        RowsAvoidAt(crv, lid, maxlook, la, body);
        LLAF.FLookLoopAgreeFrom(crv, str, next, maxlook, capN, nlk, nqt, nqtC, ov1, D);
        var resC := AI.FLookLoop(crv, str, next, maxlook, capN, nlk, nqtC, ov1);
        assert {:split_here} true;
        assert res.0 == resC.0 && res.1 == resC.1 && |res.2.a_cp| == |resC.2.a_cp| && |res.2.a_clk| == |resC.2.a_clk|;
        assert FLookLoopValueOkFull(crv, str, res.0, res.1, next, maxlook, ov, ncap, nlook, nquant);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert |res.0.a_cp| == ncap && |res.0.a_clk| == ncap && PIV.CapRegWf(res.0);

        // ---- R3 stability: res.1 agrees with lk at lid ----
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert forall l1: int, la1: R.lookaround, b1: R.regex ::
            lid <= l1 <= maxlook && LTB.LookEntryOk(crv, l1, la1, b1) ==> lid !in LookIdSet(b1);   // (h)@lid, l2:=lid
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        FLookLoopLidCpStable(crv, str, lid, maxlook, cap, lk, qt, ov, S, Slook, ncap, nlook, nquant);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert AReg.get_cp(res.1, lid) == AReg.get_cp(lk, lid);

        // ---- suffix frame: res.0 == capN on OuterCaps(body) ----
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert forall l: int, la2: R.lookaround, body2: R.regex ::
            next <= l <= maxlook && LTB.LookEntryOk(crv, l, la2, body2) ==> FrameEntryOk(crv, la2, body2, Sp, Slook)
        by {
          forall l: int, la2: R.lookaround, body2: R.regex | next <= l <= maxlook && LTB.LookEntryOk(crv, l, la2, body2)
            ensures FrameEntryOk(crv, la2, body2, Sp, Slook)
          {
            assert FrameEntryOk(crv, la2, body2, S, Slook);   // (a)
            assert PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(body)) * PIV.CaptureRegs(body2) == {};   // (D-ord)
            OuterCapsLeCaptureRegs(body2);
            assert PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(body2)) <= Sp by {
              forall k: int | k in PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(body2)) ensures k in Sp {
                assert k in S;
                assert k in PIV.CaptureRegs(body2);   // OuterCaps(body2) <= CaptureRegs(body2)
                assert k !in PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(body)) by {
                  if k in PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(body)) {
                    assert k in PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(body)) * PIV.CaptureRegs(body2);
                  }
                }
              }
            }
          }
        }
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        FLookLoopCaptureFrameNested(crv, str, next, maxlook, capN, nlk, nqtC, ov1, Sp, Slook, ncap, nlook, nquant);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert CM.RegsAgreeOutside(res.0, capN, Sp) by { assert res.0 == resC.0; }
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert forall k: int :: k in PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(body)) ==> k !in Sp;
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        RegsAgreeOutsideToInside(res.0, capN, PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(body)), Sp);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert CM.RegsAgreeInside(res.0, capN, PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(body)));

        // ---- assemble FLookLoopValueOkFull for [lid] keyed on res.1 ----
        forall owner: int | lid <= owner <= maxlook && MatchedPosLA(crv, res.1, owner)
          ensures var rf2 := FreshBodyMatchPlus(crv, str, owner, res.1, ov, ncap, nlook, nquant);
                  (rf2.Some? ==> CM.RegsAgreeInside(res.0, rf2.value.capture_regs,
                                                    PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(VBody(crv, owner)))))
                  && (rf2.None? ==> CM.RegsAgreeInside(res.0, AReg.init_regs(ncap),
                                                       PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(VBody(crv, owner)))))
        {
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          if owner == lid {
            // re-key the row's witness from lk onto res.1 (stability); the plus replay reads only get_cp
            var rf2 := FreshBodyMatchPlus(crv, str, lid, res.1, ov, ncap, nlook, nquant);
            assert rf2 == rfLid by {
              assert AReg.get_cp(res.1, lid) == AReg.get_cp(lk, lid);   // stability
              reveal FreshBodyMatchPlus();
            }
            assert VBody(crv, lid) == body;
            var OC := PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(body));
            OuterCapsLeCaptureRegs(body);
            assert OC <= PIV.CaptureRegs(body);
            if rfLid.Some? {
              assert result.Some? && capN == result.value.capture_regs;
              assert CM.RegsAgreeInside(capN, rfLid.value.capture_regs, PIV.CaptureRegs(body));
              RegsAgreeInsideWeakenSub(capN, rfLid.value.capture_regs, OC, PIV.CaptureRegs(body));
              assert CM.RegsAgreeInside(res.0, capN, OC);   // suffix frame
              assert CM.RegsAgreeInside(res.0, rfLid.value.capture_regs, OC);
            } else {
              assert result.None? && capN == cap;
              assert CM.RegsAgreeInside(cap, AReg.init_regs(ncap), PIV.CaptureRegs(body));   // (c')@lid
              RegsAgreeInsideWeakenSub(cap, AReg.init_regs(ncap), OC, PIV.CaptureRegs(body));
              assert CM.RegsAgreeInside(res.0, capN, OC);
              assert CM.RegsAgreeInside(res.0, AReg.init_regs(ncap), OC);
            }
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          } else {
            // owner in [next, maxlook]: DIRECT from the IH (already keyed on res.1)
            assert next <= owner <= maxlook;
            assert MatchedPosLA(crv, res.1, owner);
            assert FLookLoopValueOkFull(crv, str, res.0, res.1, next, maxlook, ov, ncap, nlook, nquant);
          }
        }
      }
  }

  /** (DEEP reverse-recon LEVEL-LINK, predicate) Whole-loop child-record link
      keyed on the FINAL look bank `res1`: for EVERY matched positive lookahead
      `l1` (matched in `res1`), the FINAL bank's recorded positions at `l1`'s
      DIRECT-child look ids agree with `l1`'s FRESH body match's own records.
      This is the per-level position tie the deep landing recursion descends on:
      `res1`'s entry at an inner lid `l2` (child of `l1`) IS the position where
      `l1`'s fresh replay crossed `l2`'s gate. */
  ghost predicate FLookLoopChildLinkOk(crv: CP.FCompiled, str: string, res1: AReg.Regs,
                                       lid: int, maxlook: int, ov: LOr.OracleView,
                                       ncap: int, nlook: int, nquant: int) {
    forall l1: int :: lid <= l1 <= maxlook && MatchedPosLA(crv, res1, l1) ==>
                        var rf := FreshBodyMatchPlus(crv, str, l1, res1, ov, ncap, nlook, nquant);
                        rf.Some? ==>
                          forall l2: int :: l2 in DirectLidSet(VBody(crv, l1)) ==>
                                              AReg.get_cp(res1, l2) == AReg.get_cp(rf.value.look_regs, l2)
                                              && AI.get_idx(res1.a_clk, l2) == AI.get_idx(rf.value.look_regs.a_clk, l2)
  }

  /** `l1 == lid` is not matched in `res1`, so the child-link map for
      `[lid, maxlook]` is exactly the one for `[lid+1, maxlook]`. */
  lemma ChildLinkSkipLid(crv: CP.FCompiled, str: string, res1: AReg.Regs, lid: int, maxlook: int,
                         ov: LOr.OracleView, ncap: int, nlook: int, nquant: int)
    requires FLookLoopChildLinkOk(crv, str, res1, lid + 1, maxlook, ov, ncap, nlook, nquant)
    requires !MatchedPosLA(crv, res1, lid)
    ensures FLookLoopChildLinkOk(crv, str, res1, lid, maxlook, ov, ncap, nlook, nquant)
  {
    forall l1: int | lid <= l1 <= maxlook && MatchedPosLA(crv, res1, l1)
      ensures var rf := FreshBodyMatchPlus(crv, str, l1, res1, ov, ncap, nlook, nquant);
              rf.Some? ==>
                forall l2: int :: l2 in DirectLidSet(VBody(crv, l1)) ==>
                                    AReg.get_cp(res1, l2) == AReg.get_cp(rf.value.look_regs, l2)
                                    && AI.get_idx(res1.a_clk, l2) == AI.get_idx(rf.value.look_regs.a_clk, l2)
    { assert l1 != lid; }
  }

  /** (DEEP reverse-recon LEVEL-LINK, lift) THE whole-loop child-record link.
      Mirrors `FLookLoopValueLiftFull`'s induction verbatim with the SAME
      hypotheses (a)-(h) PLUS (c'-look): the incoming look bank is still INITIAL
      at every row's DIRECT-child ids (main code gates only on TOP lids, so this
      holds at the loop entry; the replay writes only the CURRENT row's direct
      children, disjoint from every later row's — (g_new) — so it transfers).
      At the matched row `lid`: the tail fold leaves `lid`'s direct children
      untouched (`FLookLoopTopLookCpStableFull` at each child, via (g_new)), the
      iteration's banks ARE the replay winner's, and the replay agrees with the
      FRESH match on the direct children (`ReplayLidLookAgreeFreshNested` at
      `SL := DirectLidSet(body)`) — so the FINAL bank's child records are the
      fresh match's. Rows above `lid` come from the IH keyed on `res.1`. */
  lemma FLookLoopChildLinkLift(crv: CP.FCompiled, str: string, lid: int, maxlook: int,
                                                     cap: AReg.Regs, lk: AReg.Regs, qt: AReg.Regs, ov: LOr.OracleView,
                                                     S: set<int>, Slook: set<int>, ncap: int, nlook: int, nquant: int)
    requires ncap >= 0 && nlook >= 0 && nquant >= 0
    requires (forall k :: AI.get_idx(qt.a_cp, k) < 0)
             && (forall k :: AI.get_idx(qt.a_clk, k) >= -1)
    requires |qt.a_cp| == nquant && |qt.a_clk| == nquant
    requires |cap.a_cp| == ncap && |cap.a_clk| == ncap && PIV.CapRegWf(cap)
    requires |lk.a_cp| == nlook && |lk.a_clk| == nlook
    requires CM.LookCpsLE(lk, |str|)                                                            // (e)
    requires forall l: int, la: R.lookaround, body: R.regex ::                                   // (a)
               lid <= l <= maxlook && LTB.LookEntryOk(crv, l, la, body) ==> FrameEntryOk(crv, la, body, S, Slook)
    requires forall l: int :: lid <= l <= maxlook && AReg.get_cp(lk, l).Some? ==>                // (b)
                                exists la: R.lookaround, body: R.regex :: LTB.LookEntryOk(crv, l, la, body)
    requires forall l: int, la: R.lookaround, body: R.regex ::                                   // (c') full per-body-unset
               lid <= l <= maxlook && LTB.LookEntryOk(crv, l, la, body) ==>
                 CM.RegsAgreeInside(cap, AReg.init_regs(ncap), PIV.CaptureRegs(body))
    requires forall l: int, la: R.lookaround, body: R.regex ::                                   // (c'-look) child-unset
               lid <= l <= maxlook && LTB.LookEntryOk(crv, l, la, body) ==>
                 CM.RegsAgreeInside(lk, AReg.init_regs(nlook), DirectLidSet(body))
    requires forall l1: int, la1: R.lookaround, b1: R.regex, l2: int, la2: R.lookaround, b2: R.regex ::  // (D-ord)
               lid <= l1 <= maxlook && lid <= l2 <= maxlook && l1 < l2
               && LTB.LookEntryOk(crv, l1, la1, b1) && LTB.LookEntryOk(crv, l2, la2, b2) ==>
                 PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(b1)) * PIV.CaptureRegs(b2) == {}
    requires forall l1: int, la1: R.lookaround, b1: R.regex, l2: int ::                          // (f) look-stability
               (lid <= l1 <= maxlook && LTB.LookEntryOk(crv, l1, la1, b1)
               && lid <= l2 <= maxlook && l2 != l1 && AReg.get_cp(lk, l2).Some?) ==> l2 !in LookIdSet(b1)
    requires forall l1: int, la1: R.lookaround, b1: R.regex, l2: int, la2: R.lookaround, b2: R.regex ::  // (g_new)
               lid <= l1 <= maxlook && lid <= l2 <= maxlook && l1 < l2
               && LTB.LookEntryOk(crv, l1, la1, b1) && LTB.LookEntryOk(crv, l2, la2, b2) ==>
                 DirectLookIds(b1) * LTB.LookIds(b2) == {}
    requires forall l1: int, la1: R.lookaround, b1: R.regex, l2: int ::                          // (h) well-nested lids
               lid <= l1 <= maxlook && LTB.LookEntryOk(crv, l1, la1, b1) && lid <= l2 <= l1 ==> l2 !in LookIdSet(b1)
    // (G3a) a lookahead row may reconstruct a nulled plus (A4 reads the quant bank at its quantifiers;
    // the tail runs on the cleared bank, A5)
    requires RowsAvoidO(crv, lid, maxlook)
    requires forall l: int, la: R.lookaround, body: R.regex ::                                   // (c'q) per-body quant-unset
               lid <= l <= maxlook && LTB.LookEntryOk(crv, l, la, body) ==>
                 CM.RegsAgreeInside(qt, AReg.init_regs(nquant), LKC.QIdsInt(body))
    requires forall l1: int, la1: R.lookaround, b1: R.regex, l2: int, la2: R.lookaround, b2: R.regex ::  // (D-ord-q)
               lid <= l1 <= maxlook && lid <= l2 <= maxlook && l1 < l2
               && LTB.LookEntryOk(crv, l1, la1, b1) && LTB.LookEntryOk(crv, l2, la2, b2) ==>
                 QIdsOuter(b1) * LKC.QIdsInt(b2) == {}
    ensures var res := AI.FLookLoop(crv, str, lid, maxlook, cap, lk, qt, ov);
            FLookLoopChildLinkOk(crv, str, res.1, lid, maxlook, ov, ncap, nlook, nquant)
    decreases maxlook - lid
  {
    var res := AI.FLookLoop(crv, str, lid, maxlook, cap, lk, qt, ov);
    assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
    if lid > maxlook {
      return;
    }
    var next := lid + 1;
    RowsAvoidSuffix(crv, lid, maxlook);
    match AReg.get_cp(lk, lid)
    case None =>
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert res == AI.FLookLoop(crv, str, next, maxlook, cap, lk, qt, ov);
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      FLookLoopChildLinkLift(crv, str, next, maxlook, cap, lk, qt, ov, S, Slook, ncap, nlook, nquant);
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert forall l1: int, la1: R.lookaround, b1: R.regex ::
          lid <= l1 <= maxlook && LTB.LookEntryOk(crv, l1, la1, b1) ==> lid !in LookIdSet(b1);   // (h)@lid, l2:=lid
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      FLookLoopLidCpStable(crv, str, lid, maxlook, cap, lk, qt, ov, S, Slook, ncap, nlook, nquant);
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert AReg.get_cp(res.1, lid) == AReg.get_cp(lk, lid);
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert !MatchedPosLA(crv, res.1, lid);
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      ChildLinkSkipLid(crv, str, res.1, lid, maxlook, ov, ncap, nlook, nquant);
    case Some(cp) =>
      var looktype := if 0 <= lid < |crv.f_look_types| then crv.f_look_types[lid] else R.Lookahead;
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      if !AI.capture_type(looktype) {
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert res == AI.FLookLoop(crv, str, next, maxlook, cap, lk, qt, ov);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        FLookLoopChildLinkLift(crv, str, next, maxlook, cap, lk, qt, ov, S, Slook, ncap, nlook, nquant);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert !MatchedPosLA(crv, res.1, lid);   // !capture_type(looktype), looktype == f_look_types[lid]
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        ChildLinkSkipLid(crv, str, res.1, lid, maxlook, ov, ncap, nlook, nquant);
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      } else {
        // (2026-08-29 E3) the preamble is an OPAQUE block: only the facts below reach the arm's VC.
        var la: R.lookaround := *;
        var body: R.regex := *;
        var bytecode := *;
        var dir := *;
        var lookcdn := *;
        var lookast := *;
        var result := *;
        var ov1 := *;
        var capN := *;
        var nlk := *;
        var nqt := *;
        var rfLid := *;
        var rf := *;
        opaque
          ensures (LTB.LookEntryOk(crv, lid, la, body))
          ensures (bytecode == AI.get_code_v(crv.f_look_capture_bc, lid))
          ensures (dir == AI.capture_direction(looktype))
          ensures (lookcdn == if 0 <= lid < |crv.f_look_cdns| then crv.f_look_cdns[lid] else [])
          ensures (lookast == if 0 <= lid < |crv.f_look_ast| then crv.f_look_ast[lid] else R.Re_empty)
          ensures (AI.FFindMatchPlus(bytecode, lookast, crv.f_plus_bc, str, ov, dir,
                                                           cp, cap, lk, qt, 0, lookcdn) == (result, ov1))
          ensures (capN == if result.None? then cap else result.value.capture_regs)
          ensures (nlk == if result.None? then lk else result.value.look_regs)
          ensures (nqt == if result.None? then qt else result.value.quant_regs)
          ensures (rfLid == FreshBodyMatchPlus(crv, str, lid, lk, ov, ncap, nlook, nquant))
          ensures (rf == AI.FFindMatchPlus(bytecode, body, crv.f_plus_bc, str, ov, dir, cp,
                                           AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant),
                                           0, lookcdn).0)   // (G3a) the fresh PLUS replay
          ensures (0 <= lid < |crv.f_look_types| && crv.f_look_types[lid] == la)
          ensures (body == VBody(crv, lid))
          ensures (FrameEntryOk(crv, la, body, S, Slook))
          ensures (lookast == body)
          ensures (bytecode == CP.compile_to_bytecode(CP.capture_regex(la, body)))
          ensures (la.Lookahead? ==> (dir == LAnc.Forward && CP.capture_regex(la, body) == body
                                              && bytecode == CP.compile_to_bytecode(body)
                                              && AI.cp_context(cp, str, LAnc.Forward).nextchar == AI.get_char(str, cp)))
          ensures (la.Lookbehind? ==> (dir == LAnc.Backward && CP.capture_regex(la, body) == R.reverse_regex(body)
                                               && bytecode == CP.compile_to_bytecode(R.reverse_regex(body))
                                               && AI.cp_context(cp, str, LAnc.Backward).nextchar == AI.get_char(str, cp - 1)))
          ensures (res == AI.FLookLoop(crv, str, next, maxlook, capN, nlk, nqt, ov1))
          ensures (0 <= cp <= |str|)
          ensures (ov1 == ov)
          ensures (CM.RegsAgreeOutside(capN, cap, PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(body))))
          ensures (CM.RegsAgreeOutside(nlk, lk, LookIdSet(body)))
          ensures (CM.RegsAgreeOutside(nlk, lk, DirectLidSet(body)))
          ensures ((forall k :: AI.get_idx(nqt.a_clk, k) >= -1)
                   && (forall k :: k !in QIdsOuter(body) ==> AI.get_idx(nqt.a_cp, k) < 0)
                   && CM.RegsAgreeOutside(nqt, qt, QIdsOuter(body)))   // (G3a) positions may be set inside D
          ensures (|capN.a_cp| == ncap && |capN.a_clk| == ncap && PIV.CapRegWf(capN)
                           && |nqt.a_cp| == nquant && |nqt.a_clk| == nquant && |nlk.a_cp| == nlook && |nlk.a_clk| == nlook)
          ensures (CM.LookCpsLE(nlk, |str|))
          ensures (rfLid == rf)
          ensures ((result.None? <==> rf.None?) && (result.Some? ==> CM.RegsAgreeInside(result.value.look_regs, rf.value.look_regs, DirectLidSet(body))))
        {
          la, body :| LTB.LookEntryOk(crv, lid, la, body);
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          assert 0 <= lid < |crv.f_look_types| && crv.f_look_types[lid] == la;
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          assert looktype == la;
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          assert body == VBody(crv, lid);
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          assert FrameEntryOk(crv, la, body, S, Slook);
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          assert la.Lookahead? || la.Lookbehind?;            // (L5 F7c-2) capture_type
          bytecode := AI.get_code_v(crv.f_look_capture_bc, lid);
          dir := AI.capture_direction(looktype);
          lookcdn := if 0 <= lid < |crv.f_look_cdns| then crv.f_look_cdns[lid] else [];
          lookast := if 0 <= lid < |crv.f_look_ast| then crv.f_look_ast[lid] else R.Re_empty;
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          assert lookast == body;
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          assert bytecode == CP.compile_to_bytecode(CP.capture_regex(la, body));
          var (result', ov1') := AI.FFindMatchPlus(bytecode, lookast, crv.f_plus_bc, str, ov, dir,
                                                 cp, cap, lk, qt, 0, lookcdn); result, ov1 := result', ov1';
          capN := if result.None? then cap else result.value.capture_regs;
          nlk := if result.None? then lk else result.value.look_regs;
          nqt := if result.None? then qt else result.value.quant_regs;
          // (L5 F7c-2) per-kind replay facts (the `...LB` twins take the BACKWARD ones)
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          assert la.Lookahead? ==> (dir == LAnc.Forward && CP.capture_regex(la, body) == body
                                    && bytecode == CP.compile_to_bytecode(body)
                                    && AI.cp_context(cp, str, LAnc.Forward).nextchar == AI.get_char(str, cp));
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          assert la.Lookbehind? ==> (dir == LAnc.Backward && CP.capture_regex(la, body) == R.reverse_regex(body)
                                     && bytecode == CP.compile_to_bytecode(R.reverse_regex(body))
                                     && AI.cp_context(cp, str, LAnc.Backward).nextchar == AI.get_char(str, cp - 1));
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          assert res == AI.FLookLoop(crv, str, next, maxlook, capN, nlk, nqt, ov1);
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          assert 0 <= cp <= |str| by {
            assert cp == AI.get_idx(lk.a_cp, lid) && cp >= 0;   // get_cp(lk,lid)==Some(cp)
            assert AI.get_idx(lk.a_cp, lid) <= |str|;            // LookCpsLE
          }
  
          // per-lid replay frames / wf / cp, and the value witness, by kind
          rfLid := FreshBodyMatchPlus(crv, str, lid, lk, ov, ncap, nlook, nquant);
          rf := AI.FFindMatchPlus(bytecode, body, crv.f_plus_bc, str, ov, dir, cp,
                                  AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant), 0, lookcdn).0;
          assert rfLid == rf by {
            reveal FreshBodyMatchPlus();
            assert AReg.get_cp(lk, lid).value == cp;
          }
          assert {:split_here} true;
          if la.Lookahead? {
            ReplayPlusRowLAS(bytecode, str, ov, lookcdn, crv.f_plus_bc, cp, cap, lk, qt, body, ncap, nlook, nquant);
            assert CM.RegsAgreeInside(cap, AReg.init_regs(ncap), {});
            ReplayAgreePlusFresh(bytecode, str, cp, cap, lk, qt, ov, lookcdn, crv.f_plus_bc, body,
                                 {}, DirectLidSet(body), ncap, nlook, nquant);
          } else {
            // (G3b) a lookbehind row replays the plus machine too
            ReplayPlusRowLBS(bytecode, str, ov, lookcdn, crv.f_plus_bc, cp, cap, lk, qt, body, ncap, nlook, nquant);
            assert CM.RegsAgreeInside(cap, AReg.init_regs(ncap), {});
            ReplayAgreePlusFreshDir(bytecode, str, cp, cap, lk, qt, ov, lookcdn, crv.f_plus_bc, body,
                                    {}, DirectLidSet(body), ncap, nlook, nquant, LAnc.Backward);
          }
          assert {:split_here} true;
          assert ov1 == ov;
          assert CM.RegsAgreeOutside(capN, cap, PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(body))) by {
            if result.Some? {} else { assert capN == cap; }
          }
          assert CM.RegsAgreeOutside(nlk, lk, LookIdSet(body)) by {
            if result.Some? {} else { assert nlk == lk; }
          }
          assert CM.RegsAgreeOutside(nlk, lk, DirectLidSet(body)) by {
            if result.Some? {} else { assert nlk == lk; }
          }
          assert |capN.a_cp| == ncap && |capN.a_clk| == ncap && PIV.CapRegWf(capN)
                 && |nqt.a_cp| == nquant && |nqt.a_clk| == nquant && |nlk.a_cp| == nlook && |nlk.a_clk| == nlook by {
            if result.Some? { assert CM.ThreadRegsWf(result.value, ncap, nlook, nquant); }
          }
          assert CM.LookCpsLE(nlk, |str|) by {
            if result.Some? {} else { assert nlk == lk; }
          }
          assert (forall k :: AI.get_idx(nqt.a_clk, k) >= -1)
                 && (forall k :: k !in QIdsOuter(body) ==> AI.get_idx(nqt.a_cp, k) < 0)
                 && CM.RegsAgreeOutside(nqt, qt, QIdsOuter(body)) by {
            if result.None? { assert nqt == qt; }
          }
          assert (result.None? <==> rf.None?) && (result.Some? ==> CM.RegsAgreeInside(result.value.look_regs, rf.value.look_regs, DirectLidSet(body)));   // (E3) exported: the look-agreement None-iff + inside-agreement
        }
        // (G3a) the cleared bank the tail runs on
        var D := QIdsOuter(body);
        var nqtC := RRA.ClearCps(nqt, D);
        RRA.ClearCpsFinal(nqt, D);
        RRA.ClearCpsFacts(nqt, D);
        assert {:split_here} true;   // (E3) section boundary: its own assertion batch

        // ---- recursion hypothesis transfer at [next] (verbatim + (c'-look)) ----
        // (b) matched-look-has-entry for nlk
        // (2026-08-29 E3) the preamble is an OPAQUE block: only the facts below reach the arm's VC.
        opaque
          ensures (forall l: int :: next <= l <= maxlook && AReg.get_cp(nlk, l).Some? ==>
                                              exists la2: R.lookaround, body2: R.regex :: LTB.LookEntryOk(crv, l, la2, body2))
          ensures (forall l1: int, la1: R.lookaround, b1: R.regex, l2: int ::
                        (next <= l1 <= maxlook && LTB.LookEntryOk(crv, l1, la1, b1)
                        && next <= l2 <= maxlook && l2 != l1 && AReg.get_cp(nlk, l2).Some?) ==> l2 !in LookIdSet(b1))
          ensures (forall l: int, la2: R.lookaround, body2: R.regex ::
                        next <= l <= maxlook && LTB.LookEntryOk(crv, l, la2, body2) ==>
                          CM.RegsAgreeInside(capN, AReg.init_regs(ncap), PIV.CaptureRegs(body2)))
          ensures (forall l: int, la2: R.lookaround, body2: R.regex ::
                        next <= l <= maxlook && LTB.LookEntryOk(crv, l, la2, body2) ==>
                          CM.RegsAgreeInside(nlk, AReg.init_regs(nlook), DirectLidSet(body2)))
          ensures (forall l1: int, la1: R.lookaround, b1: R.regex, l2: int ::
                        next <= l1 <= maxlook && LTB.LookEntryOk(crv, l1, la1, b1) && next <= l2 <= l1 ==> l2 !in LookIdSet(b1))
          ensures (res.1 == AI.FLookLoop(crv, str, next, maxlook, capN, nlk, nqt, ov1).1)
          ensures (res.1 == AI.FLookLoop(crv, str, next, maxlook, capN, nlk, nqtC, ov1).1)
          ensures (FLookLoopChildLinkOk(crv, str, res.1, next, maxlook, ov, ncap, nlook, nquant))
        {
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          assert forall l: int :: next <= l <= maxlook && AReg.get_cp(nlk, l).Some? ==>
                                    exists la2: R.lookaround, body2: R.regex :: LTB.LookEntryOk(crv, l, la2, body2)
          by {
            forall l: int | next <= l <= maxlook && AReg.get_cp(nlk, l).Some?
              ensures exists la2: R.lookaround, body2: R.regex :: LTB.LookEntryOk(crv, l, la2, body2)
            {
              if AReg.get_cp(lk, l).Some? {
              } else {
                assert result.Some?;
                assert CM.RegsAgreeOutside(nlk, lk, LookIdSet(body));
                NewLookInBody(nlk, lk, body, l);
                assert LTB.LookTablesOk(body, crv);
                LookIdEntryExists(body, crv, l as nat);
              }
            }
          }
          // (c') full per-body-unset for capN
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          assert forall l: int, la2: R.lookaround, body2: R.regex ::
              next <= l <= maxlook && LTB.LookEntryOk(crv, l, la2, body2) ==>
                CM.RegsAgreeInside(capN, AReg.init_regs(ncap), PIV.CaptureRegs(body2))
          by {
            forall l: int, la2: R.lookaround, body2: R.regex | next <= l <= maxlook && LTB.LookEntryOk(crv, l, la2, body2)
              ensures CM.RegsAgreeInside(capN, AReg.init_regs(ncap), PIV.CaptureRegs(body2))
            {
              assert CM.RegsAgreeInside(cap, AReg.init_regs(ncap), PIV.CaptureRegs(body2));   // (c')@cap
              assert PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(body)) * PIV.CaptureRegs(body2) == {};   // (D-ord) lid<l
              assert CM.RegsAgreeOutside(capN, cap, PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(body)));
              UnsetOffTransfer(capN, cap, ncap, PIV.CaptureRegs(body2), PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(body)));
            }
          }
          // (c'-look) child-unset for nlk: the replay writes only lid's direct
          // children, disjoint from every later row's ((g_new) at (lid, l)).
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          assert forall l: int, la2: R.lookaround, body2: R.regex ::
              next <= l <= maxlook && LTB.LookEntryOk(crv, l, la2, body2) ==>
                CM.RegsAgreeInside(nlk, AReg.init_regs(nlook), DirectLidSet(body2))
          by {
            forall l: int, la2: R.lookaround, body2: R.regex | next <= l <= maxlook && LTB.LookEntryOk(crv, l, la2, body2)
              ensures CM.RegsAgreeInside(nlk, AReg.init_regs(nlook), DirectLidSet(body2))
            {
              assert CM.RegsAgreeInside(lk, AReg.init_regs(nlook), DirectLidSet(body2));   // (c'-look)@lk
              assert DirectLookIds(body) * LTB.LookIds(body2) == {};                       // (g_new)@(lid, l)
              forall k: int | k in DirectLidSet(body2)
                ensures AI.get_idx(nlk.a_cp, k) == AI.get_idx(AReg.init_regs(nlook).a_cp, k)
                        && AI.get_idx(nlk.a_clk, k) == AI.get_idx(AReg.init_regs(nlook).a_clk, k)
              {
                var kn: nat :| kn in DirectLookIds(body2) && (kn as int) == k;
                DirectLidsSubLookIds(body2);
                assert kn in LTB.LookIds(body2);
                assert kn !in DirectLookIds(body) by {
                  if kn in DirectLookIds(body) { assert kn in DirectLookIds(body) * LTB.LookIds(body2); }
                }
                assert k !in DirectLidSet(body) by {
                  if k in DirectLidSet(body) {
                    var kn2: nat :| kn2 in DirectLookIds(body) && (kn2 as int) == k;
                    assert kn2 == kn;
                  }
                }
                assert AI.get_idx(nlk.a_cp, k) == AI.get_idx(lk.a_cp, k)
                       && AI.get_idx(nlk.a_clk, k) == AI.get_idx(lk.a_clk, k);   // frame off DirectLidSet(body)
              }
            }
          }
          // (f) look-stability for nlk
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          assert forall l1: int, la1: R.lookaround, b1: R.regex, l2: int ::
              (next <= l1 <= maxlook && LTB.LookEntryOk(crv, l1, la1, b1)
              && next <= l2 <= maxlook && l2 != l1 && AReg.get_cp(nlk, l2).Some?) ==> l2 !in LookIdSet(b1)
          by {
            forall l1: int, la1: R.lookaround, b1: R.regex, l2: int |
              next <= l1 <= maxlook && LTB.LookEntryOk(crv, l1, la1, b1)
              && next <= l2 <= maxlook && l2 != l1 && AReg.get_cp(nlk, l2).Some?
              ensures l2 !in LookIdSet(b1)
            {
              if AReg.get_cp(lk, l2).Some? {
                // (f)@lk
              } else {
                assert result.Some?;
                assert CM.RegsAgreeOutside(nlk, lk, DirectLidSet(body));
                NewLookInBodyDirect(nlk, lk, body, l2);
                assert (l2 as nat) in DirectLookIds(body);
                assert lid < l1;                                          // l1 >= next
                assert DirectLookIds(body) * LTB.LookIds(b1) == {};       // (g_new) with (lid, l1)
                assert (l2 as nat) !in LTB.LookIds(b1) by {
                  if (l2 as nat) in LTB.LookIds(b1) { assert (l2 as nat) in DirectLookIds(body) * LTB.LookIds(b1); }
                }
                if l2 in LookIdSet(b1) {
                  var q: nat :| q in LTB.LookIds(b1) && (q as int) == l2;
                  assert q == l2 as nat;
                }
              }
            }
          }
          // (h) well-nested lids for [next] — sub-instance of (h)@lid
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          assert forall l1: int, la1: R.lookaround, b1: R.regex, l2: int ::
              next <= l1 <= maxlook && LTB.LookEntryOk(crv, l1, la1, b1) && next <= l2 <= l1 ==> l2 !in LookIdSet(b1);
  
          // (c'q) for the tail on the cleared bank
          assert {:split_here} true;
          assert forall l: int, la2: R.lookaround, body2: R.regex ::
              next <= l <= maxlook && LTB.LookEntryOk(crv, l, la2, body2) ==>
                CM.RegsAgreeInside(nqtC, AReg.init_regs(nquant), LKC.QIdsInt(body2))
          by {
            forall l: int, la2: R.lookaround, body2: R.regex | next <= l <= maxlook && LTB.LookEntryOk(crv, l, la2, body2)
              ensures CM.RegsAgreeInside(nqtC, AReg.init_regs(nquant), LKC.QIdsInt(body2))
            {
              assert CM.RegsAgreeInside(qt, AReg.init_regs(nquant), LKC.QIdsInt(body2));   // (c'q)@qt
              assert D * LKC.QIdsInt(body2) == {};                                          // (D-ord-q) lid < l
              RRA.QAgreeIdx(nqt, nqtC, D);
              forall k | k in LKC.QIdsInt(body2)
                ensures AI.get_idx(nqtC.a_cp, k) == AI.get_idx(AReg.init_regs(nquant).a_cp, k)
                        && AI.get_idx(nqtC.a_clk, k) == AI.get_idx(AReg.init_regs(nquant).a_clk, k)
              {
                assert k !in D by { if k in D { assert k in D * LKC.QIdsInt(body2); } }
              }
            }
          }
          assert {:split_here} true;
          FLookLoopChildLinkLift(crv, str, next, maxlook, capN, nlk, nqtC, ov1, S, Slook, ncap, nlook, nquant);
          RowsAvoidAt(crv, lid, maxlook, la, body);
          LLAF.FLookLoopAgreeFrom(crv, str, next, maxlook, capN, nlk, nqt, nqtC, ov1, D);
          assert {:split_here} true;
          assert res.1 == AI.FLookLoop(crv, str, next, maxlook, capN, nlk, nqt, ov1).1;
          assert res.1 == AI.FLookLoop(crv, str, next, maxlook, capN, nlk, nqtC, ov1).1;
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          assert FLookLoopChildLinkOk(crv, str, res.1, next, maxlook, ov, ncap, nlook, nquant);
        }
        assert {:split_here} true;   // (E3) section boundary: its own assertion batch

        // ---- stability: res.1 agrees with lk at lid ----
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert forall l1: int, la1: R.lookaround, b1: R.regex ::
            lid <= l1 <= maxlook && LTB.LookEntryOk(crv, l1, la1, b1) ==> lid !in LookIdSet(b1);   // (h)@lid, l2:=lid
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        FLookLoopLidCpStable(crv, str, lid, maxlook, cap, lk, qt, ov, S, Slook, ncap, nlook, nquant);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert AReg.get_cp(res.1, lid) == AReg.get_cp(lk, lid);

        // ---- assemble the child-link for [lid] keyed on res.1 ----
        forall l1: int | lid <= l1 <= maxlook && MatchedPosLA(crv, res.1, l1)
          ensures var rf2 := FreshBodyMatchPlus(crv, str, l1, res.1, ov, ncap, nlook, nquant);
                  rf2.Some? ==>
                    forall l2: int :: l2 in DirectLidSet(VBody(crv, l1)) ==>
                                        AReg.get_cp(res.1, l2) == AReg.get_cp(rf2.value.look_regs, l2)
                                        && AI.get_idx(res.1.a_clk, l2) == AI.get_idx(rf2.value.look_regs.a_clk, l2)
        {
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          if l1 == lid {
            var rf2 := FreshBodyMatchPlus(crv, str, lid, res.1, ov, ncap, nlook, nquant);
            assert rf2 == rfLid by {
              assert AReg.get_cp(res.1, lid) == AReg.get_cp(lk, lid);   // stability
              reveal FreshBodyMatchPlus();
            }
            assert VBody(crv, lid) == body;
            if rf2.Some? {
              assert result.Some? by {
                // iff-together from the look-agreement lemma's None-iff
                assert rfLid.Some?;
              }
              assert nlk == result.value.look_regs;
              assert CM.RegsAgreeInside(result.value.look_regs, rf.value.look_regs, DirectLidSet(body));
              forall l2: int | l2 in DirectLidSet(body)
                ensures AReg.get_cp(res.1, l2) == AReg.get_cp(rf2.value.look_regs, l2)
                        && AI.get_idx(res.1.a_clk, l2) == AI.get_idx(rf2.value.look_regs.a_clk, l2)
              {
                // tail fold leaves l2 untouched: (h')@l2 on [next..] from (g_new)@(lid, ·)
                assert forall l1': int, la1': R.lookaround, b1': R.regex ::
                    next <= l1' <= maxlook && LTB.LookEntryOk(crv, l1', la1', b1') ==> l2 !in LookIdSet(b1')
                by {
                  forall l1': int, la1': R.lookaround, b1': R.regex |
                    next <= l1' <= maxlook && LTB.LookEntryOk(crv, l1', la1', b1')
                    ensures l2 !in LookIdSet(b1')
                  {
                    assert DirectLookIds(body) * LTB.LookIds(b1') == {};   // (g_new)@(lid, l1')
                    var kn: nat :| kn in DirectLookIds(body) && (kn as int) == l2;
                    assert kn !in DirectLookIds(body) * LTB.LookIds(b1');
                    assert kn !in LTB.LookIds(b1');
                    if l2 in LookIdSet(b1') {
                      var q: nat :| q in LTB.LookIds(b1') && (q as int) == l2;
                      assert q == kn;
                    }
                  }
                }
                FLookLoopTopLookCpStableFull(crv, str, next, maxlook, l2, capN, nlk, nqtC, ov1, S, Slook, ncap, nlook, nquant);
                FLookLoopTopLookClkStableFull(crv, str, next, maxlook, l2, capN, nlk, nqtC, ov1, S, Slook, ncap, nlook, nquant);
                assert AReg.get_cp(res.1, l2) == AReg.get_cp(nlk, l2);
                assert AI.get_idx(res.1.a_clk, l2) == AI.get_idx(nlk.a_clk, l2);
                // replay winner == fresh at l2 (RegsAgreeInside -> get_cp + clk)
                assert AI.get_idx(result.value.look_regs.a_cp, l2) == AI.get_idx(rf.value.look_regs.a_cp, l2);
                assert AI.get_idx(result.value.look_regs.a_clk, l2) == AI.get_idx(rf.value.look_regs.a_clk, l2);
                GetCpAgreeIdx(result.value.look_regs, rf.value.look_regs, l2);
                assert AReg.get_cp(nlk, l2) == AReg.get_cp(rf.value.look_regs, l2);
                assert rf2.value.look_regs == rf.value.look_regs;   // rf2 == rfLid == rf
              }
            }
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          } else {
            assert next <= l1 <= maxlook;
            assert FLookLoopChildLinkOk(crv, str, res.1, next, maxlook, ov, ncap, nlook, nquant);
          }
        }
      }
  }

  /** (DEEP reverse-recon) the REVERSE look-bank invariant (clk-set ==> cp-set)
      is preserved through the WHOLE `FLookLoop` fold: each iteration replaces
      the banks with an `FFindMatchPlus` winner, whose `FFindMatch` run preserves
      `CM.VmLookCpSet` (cp and clock land in the same CheckOracle `set_reg`) and
      whose `FReconstructPlus` is the identity on the `QuantRegsFinal` result.
      With `PathPresentLk`'s ancestor look-clock conjunct, this recovers
      `MatchedPosLA(crv, res.1, A)` for EVERY look-ancestor `A` of a live inside
      capture — at ANY depth (the top-level reverse invariant `CM.FFindMatch
      LookCpSet` covers only the main match / top lids). */
  lemma FLookLoopLookCpSet(crv: CP.FCompiled, str: string, lid: int, maxlook: int,
      cap: AReg.Regs, lk: AReg.Regs, qt: AReg.Regs, ov: LOr.OracleView,
      S: set<int>, Slook: set<int>, ncap: int, nlook: int, nquant: int)
    requires ncap >= 0 && nlook >= 0 && nquant >= 0
    requires (forall k :: AI.get_idx(qt.a_cp, k) < 0)
             && (forall k :: AI.get_idx(qt.a_clk, k) >= -1)
    requires |qt.a_cp| == nquant && |qt.a_clk| == nquant
    requires |cap.a_cp| == ncap && |cap.a_clk| == ncap && PIV.CapRegWf(cap)
    requires |lk.a_cp| == nlook && |lk.a_clk| == nlook
    requires CM.LookCpsLE(lk, |str|)                                                            // (e)
    requires CM.LookCpSetWithClk(lk)
    requires RowsAvoidO(crv, lid, maxlook)   // (G3a) later rows never name a row's outside-look quantifiers
    requires forall l: int, la: R.lookaround, body: R.regex ::                                   // (a)
               lid <= l <= maxlook && LTB.LookEntryOk(crv, l, la, body) ==> FrameEntryOk(crv, la, body, S, Slook)
    requires forall l: int :: lid <= l <= maxlook && AReg.get_cp(lk, l).Some? ==>                // (b)
                                exists la: R.lookaround, body: R.regex :: LTB.LookEntryOk(crv, l, la, body)
    ensures CM.LookCpSetWithClk(AI.FLookLoop(crv, str, lid, maxlook, cap, lk, qt, ov).1)
    ensures CM.LookCpsLE(AI.FLookLoop(crv, str, lid, maxlook, cap, lk, qt, ov).1, |str|)
    decreases maxlook - lid
  {
    var res := AI.FLookLoop(crv, str, lid, maxlook, cap, lk, qt, ov);
    if lid > maxlook { return; }
    var next := lid + 1;
    RowsAvoidSuffix(crv, lid, maxlook);
    match AReg.get_cp(lk, lid)
    case None =>
      FLookLoopLookCpSet(crv, str, next, maxlook, cap, lk, qt, ov, S, Slook, ncap, nlook, nquant);
    case Some(cp) =>
      var looktype := if 0 <= lid < |crv.f_look_types| then crv.f_look_types[lid] else R.Lookahead;
      if !AI.capture_type(looktype) {
        FLookLoopLookCpSet(crv, str, next, maxlook, cap, lk, qt, ov, S, Slook, ncap, nlook, nquant);
      } else {
        var la: R.lookaround, body: R.regex :| LTB.LookEntryOk(crv, lid, la, body);
        assert 0 <= lid < |crv.f_look_types| && crv.f_look_types[lid] == la;
        assert looktype == la;
        assert FrameEntryOk(crv, la, body, S, Slook);
        assert la.Lookahead? || la.Lookbehind?;            // (L5 F7c-2) capture_type; per-kind dispatch below
        assert NRC.PositiveLk(la);                         // (G5b) a replayed row is positive: its row statics
        assert RowLAStaticsS(body, crv.f_plus_bc);         // (G5b-1, G5b-2) S at every positive row
        assert {:split_here} true;
        var bytecode := AI.get_code_v(crv.f_look_capture_bc, lid);
        var dir := AI.capture_direction(looktype);
        var lookcdn := if 0 <= lid < |crv.f_look_cdns| then crv.f_look_cdns[lid] else [];
        var lookast := if 0 <= lid < |crv.f_look_ast| then crv.f_look_ast[lid] else R.Re_empty;
        assert lookast == body;
        assert bytecode == CP.compile_to_bytecode(CP.capture_regex(la, body));
        var (result, ov1) := AI.FFindMatchPlus(bytecode, lookast, crv.f_plus_bc, str, ov, dir,
                                               cp, cap, lk, qt, 0, lookcdn);
        var capN := if result.None? then cap else result.value.capture_regs;
        var nlk := if result.None? then lk else result.value.look_regs;
        var nqt := if result.None? then qt else result.value.quant_regs;
        var D := QIdsOuter(body);
        assert 0 <= cp <= |str| by { assert AI.get_idx(lk.a_cp, lid) == cp; }   // LookCpsLE + get_cp.Some?
        var ctxc := AI.cp_context(cp, str, dir);
        var inits := AI.FInitState(bytecode, cp, cap, lk, qt, 0, ctxc);
        assert {:split_here} true;
        // (L5 F7c-2) per-kind replay frames. Both kinds give the same wf block for the new banks; only the
        // lookahead row may leave quant POSITIONS set, and only inside `D`.
        if la.Lookahead? {
          assert CP.capture_regex(la, body) == body;
          assert bytecode == CP.compile_to_bytecode(body);
          assert dir == LAnc.Forward;
          assert ctxc.nextchar == AI.get_char(str, cp);
          ReplayPlusRowLAS(bytecode, str, ov, lookcdn, crv.f_plus_bc, cp, cap, lk, qt, body, ncap, nlook, nquant);
        } else {
          assert CP.capture_regex(la, body) == R.reverse_regex(body);
          assert bytecode == CP.compile_to_bytecode(R.reverse_regex(body));
          assert dir == LAnc.Backward;
          assert ctxc.nextchar == AI.get_char(str, cp - 1);
          ReplayPlusRowLBS(bytecode, str, ov, lookcdn, crv.f_plus_bc, cp, cap, lk, qt, body, ncap, nlook, nquant);   // (G3b)
        }
        assert {:split_here} true;
        // ---- what both kinds deliver ----
        assert result.Some? ==> CM.ThreadRegsWf(result.value, ncap, nlook, nquant);
        assert |capN.a_cp| == ncap && |capN.a_clk| == ncap && PIV.CapRegWf(capN);
        assert |nlk.a_cp| == nlook && |nlk.a_clk| == nlook && CM.LookCpsLE(nlk, |str|);
        assert |nqt.a_cp| == nquant && |nqt.a_clk| == nquant;
        assert (forall k :: AI.get_idx(nqt.a_clk, k) >= -1)
            && (forall k :: k !in D ==> AI.get_idx(nqt.a_cp, k) < 0);
        assert CM.RegsAgreeOutside(nlk, lk, LookIdSet(body)) by {
          if result.Some? {} else { assert nlk == lk; }
        }

        // ---- preserve the "matched look has a table row" invariant for nlk ----
        assert forall l: int :: next <= l <= maxlook && AReg.get_cp(nlk, l).Some? ==>
                                  exists la2: R.lookaround, body2: R.regex :: LTB.LookEntryOk(crv, l, la2, body2)
        by {
          forall l: int | next <= l <= maxlook && AReg.get_cp(nlk, l).Some?
            ensures exists la2: R.lookaround, body2: R.regex :: LTB.LookEntryOk(crv, l, la2, body2)
          {
            if AReg.get_cp(lk, l).Some? {
            } else {
              assert result.Some?;
              NewLookInBody(nlk, lk, body, l);
              assert LTB.LookTablesOk(body, crv);
              LookIdEntryExists(body, crv, l as nat);
            }
          }
        }

        assert {:split_here} true;
        // ---- the winner's look bank is the VM winner's (a lookahead row: `ReplayPlusRowLA`'s last
        //      conjunct; the reconstruction keeps the look bank), and the VM run keeps the invariant ----
        assert res == AI.FLookLoop(crv, str, next, maxlook, capN, nlk, nqt, ov1);
        assert CM.VmLookCpSet(inits) by {
          assert AI.init_thread(cap, lk, qt).look_regs == lk;
          assert inits.active == [AI.init_thread(cap, lk, qt)];
        }
        var (fmres, ovx) := AI.FFindMatch(bytecode, str, inits, ov, dir, lookcdn);
        assert {:split_here} true;   // (G5b-1) the section loops as one batch (each obligation alone < 60 s)
        if la.Lookahead? {
          CM.FFindMatchLookCpSet(bytecode, str, inits, ov, dir, lookcdn);
        } else {
          CM.FFindMatchLookCpSetB(bytecode, str, inits, ov, dir, lookcdn);
          // (G3b) the plus winner keeps the VM winner's look bank (`ReplayPlusRowLB`)
        }
        assert {:split_here} true;
        assert CM.LookCpSetWithClk(nlk) by {
          if result.Some? { assert fmres.Some?; } else { assert nlk == lk; }   // (G5b-3) the replay keeps CpSet
        }
        assert {:split_here} true;
        // ---- (G3a) clear-and-transfer: the tail on the CLEARED bank is the tail on the real one ----
        var nqtC := RRA.ClearCps(nqt, D);
        RRA.ClearCpsFinal(nqt, D);
        RRA.ClearCpsFacts(nqt, D);
        assert |nqtC.a_cp| == nquant && |nqtC.a_clk| == nquant;
        FLookLoopLookCpSet(crv, str, next, maxlook, capN, nlk, nqtC, ov1, S, Slook, ncap, nlook, nquant);
        RowsAvoidAt(crv, lid, maxlook, la, body);
        LLAF.FLookLoopAgreeFrom(crv, str, next, maxlook, capN, nlk, nqt, nqtC, ov1, D);
        var resTail := AI.FLookLoop(crv, str, next, maxlook, capN, nlk, nqt, ov1);
        var resTailC := AI.FLookLoop(crv, str, next, maxlook, capN, nlk, nqtC, ov1);
        assert resTail.0 == resTailC.0 && resTail.1 == resTailC.1;
      }
  }

  /** (DEEP reverse-recon) `LookCpsOracleTrue` — every recorded look cp is an
      ORACLE-TRUE position — is preserved through the WHOLE `FLookLoop` fold:
      each iteration's banks are an `FFindMatchPlus` winner over WRITE-FREE body
      code (`NoWriteOracleBodyCodeNested`), so the per-run invariant
      (`CM.FFindMatchLookOracleTrue`) carries, and `FReconstructPlus` is the
      identity. With `OracleOkAt` (bit ⟺ the spec body matches there), this
      makes EVERY `res.1`-recorded position — any depth — a position where the
      recorded look's SPEC BODY TREE has a leaf: the `rf.Some?`/`FirstLeaf.Some?`
      feed of the deep landing recursion at every level. */
  lemma FLookLoopLookOracleTrue(crv: CP.FCompiled, str: string, lid: int, maxlook: int,
      cap: AReg.Regs, lk: AReg.Regs, qt: AReg.Regs, ov: LOr.OracleView,
      S: set<int>, Slook: set<int>, ncap: int, nlook: int, nquant: int)
    requires ncap >= 0 && nlook >= 0 && nquant >= 0
    requires (forall k :: AI.get_idx(qt.a_cp, k) < 0)
             && (forall k :: AI.get_idx(qt.a_clk, k) >= -1)
    requires |qt.a_cp| == nquant && |qt.a_clk| == nquant
    requires |cap.a_cp| == ncap && |cap.a_clk| == ncap && PIV.CapRegWf(cap)
    requires |lk.a_cp| == nlook && |lk.a_clk| == nlook
    requires CM.LookCpsLE(lk, |str|)                                                            // (e)
    requires CM.LookCpsOracleTrue(lk, ov)
    requires RowsAvoidO(crv, lid, maxlook)   // (G3a) later rows never name a row's outside-look quantifiers
    requires forall l: int, la: R.lookaround, body: R.regex ::                                   // (a)
               lid <= l <= maxlook && LTB.LookEntryOk(crv, l, la, body) ==> FrameEntryOk(crv, la, body, S, Slook)
    requires forall l: int :: lid <= l <= maxlook && AReg.get_cp(lk, l).Some? ==>                // (b)
                                exists la: R.lookaround, body: R.regex :: LTB.LookEntryOk(crv, l, la, body)
    ensures CM.LookCpsOracleTrue(AI.FLookLoop(crv, str, lid, maxlook, cap, lk, qt, ov).1, ov)
    decreases maxlook - lid
  {
    var res := AI.FLookLoop(crv, str, lid, maxlook, cap, lk, qt, ov);
    if lid > maxlook { return; }
    var next := lid + 1;
    RowsAvoidSuffix(crv, lid, maxlook);
    match AReg.get_cp(lk, lid)
    case None =>
      FLookLoopLookOracleTrue(crv, str, next, maxlook, cap, lk, qt, ov, S, Slook, ncap, nlook, nquant);
    case Some(cp) =>
      var looktype := if 0 <= lid < |crv.f_look_types| then crv.f_look_types[lid] else R.Lookahead;
      if !AI.capture_type(looktype) {
        FLookLoopLookOracleTrue(crv, str, next, maxlook, cap, lk, qt, ov, S, Slook, ncap, nlook, nquant);
      } else {
        var la: R.lookaround, body: R.regex :| LTB.LookEntryOk(crv, lid, la, body);
        assert 0 <= lid < |crv.f_look_types| && crv.f_look_types[lid] == la;
        assert looktype == la;
        assert FrameEntryOk(crv, la, body, S, Slook);
        assert la.Lookahead? || la.Lookbehind?;            // (L5 F7c-2) capture_type; per-kind dispatch below
        assert {:split_here} true;
        var bytecode := AI.get_code_v(crv.f_look_capture_bc, lid);
        var dir := AI.capture_direction(looktype);
        var lookcdn := if 0 <= lid < |crv.f_look_cdns| then crv.f_look_cdns[lid] else [];
        var lookast := if 0 <= lid < |crv.f_look_ast| then crv.f_look_ast[lid] else R.Re_empty;
        assert lookast == body;
        assert bytecode == CP.compile_to_bytecode(CP.capture_regex(la, body));
        var (result, ov1) := AI.FFindMatchPlus(bytecode, lookast, crv.f_plus_bc, str, ov, dir,
                                               cp, cap, lk, qt, 0, lookcdn);
        var capN := if result.None? then cap else result.value.capture_regs;
        var nlk := if result.None? then lk else result.value.look_regs;
        var nqt := if result.None? then qt else result.value.quant_regs;
        var D := QIdsOuter(body);
        assert 0 <= cp <= |str| by { assert AI.get_idx(lk.a_cp, lid) == cp; }   // LookCpsLE + get_cp.Some?
        var ctxc := AI.cp_context(cp, str, dir);
        var inits := AI.FInitState(bytecode, cp, cap, lk, qt, 0, ctxc);
        assert {:split_here} true;
        // (L5 F7c-2) per-kind replay frames. Both kinds give the same wf block for the new banks; only the
        // lookahead row may leave quant POSITIONS set, and only inside `D`.
        if la.Lookahead? {
          assert CP.capture_regex(la, body) == body;
          assert bytecode == CP.compile_to_bytecode(body);
          assert dir == LAnc.Forward;
          assert ctxc.nextchar == AI.get_char(str, cp);
          ReplayPlusRowLAS(bytecode, str, ov, lookcdn, crv.f_plus_bc, cp, cap, lk, qt, body, ncap, nlook, nquant);
        } else {
          assert CP.capture_regex(la, body) == R.reverse_regex(body);
          assert bytecode == CP.compile_to_bytecode(R.reverse_regex(body));
          assert dir == LAnc.Backward;
          assert ctxc.nextchar == AI.get_char(str, cp - 1);
          ReplayPlusRowLBS(bytecode, str, ov, lookcdn, crv.f_plus_bc, cp, cap, lk, qt, body, ncap, nlook, nquant);   // (G3b)
        }
        assert {:split_here} true;
        // ---- what both kinds deliver ----
        assert result.Some? ==> CM.ThreadRegsWf(result.value, ncap, nlook, nquant);
        assert |capN.a_cp| == ncap && |capN.a_clk| == ncap && PIV.CapRegWf(capN);
        assert |nlk.a_cp| == nlook && |nlk.a_clk| == nlook && CM.LookCpsLE(nlk, |str|);
        assert |nqt.a_cp| == nquant && |nqt.a_clk| == nquant;
        assert (forall k :: AI.get_idx(nqt.a_clk, k) >= -1)
            && (forall k :: k !in D ==> AI.get_idx(nqt.a_cp, k) < 0);
        assert CM.RegsAgreeOutside(nlk, lk, LookIdSet(body)) by {
          if result.Some? {} else { assert nlk == lk; }
        }

        // ---- preserve the "matched look has a table row" invariant for nlk ----
        assert forall l: int :: next <= l <= maxlook && AReg.get_cp(nlk, l).Some? ==>
                                  exists la2: R.lookaround, body2: R.regex :: LTB.LookEntryOk(crv, l, la2, body2)
        by {
          forall l: int | next <= l <= maxlook && AReg.get_cp(nlk, l).Some?
            ensures exists la2: R.lookaround, body2: R.regex :: LTB.LookEntryOk(crv, l, la2, body2)
          {
            if AReg.get_cp(lk, l).Some? {
            } else {
              assert result.Some?;
              NewLookInBody(nlk, lk, body, l);
              assert LTB.LookTablesOk(body, crv);
              LookIdEntryExists(body, crv, l as nat);
            }
          }
        }

        assert {:split_here} true;
        // ---- the winner's look bank is the VM winner's (a lookahead row: `ReplayPlusRowLA`'s last
        //      conjunct; the reconstruction keeps the look bank), and the VM run keeps the invariant ----
        assert res == AI.FLookLoop(crv, str, next, maxlook, capN, nlk, nqt, ov1);
        assert ov1 == ov;
        assert CM.VmLookOracleTrue(inits, ov) by {
          assert AI.init_thread(cap, lk, qt).look_regs == lk;
          assert inits.active == [AI.init_thread(cap, lk, qt)];
        }
        var (fmres, ovx) := AI.FFindMatch(bytecode, str, inits, ov, dir, lookcdn);
        if la.Lookahead? {
          reveal RowLAStaticsS();
          NoWriteOracleBodyCodeCdn(body);
          CM.FFindMatchLookOracleTrue(bytecode, str, inits, ov, dir, lookcdn);
        } else {
          reveal RowLAStaticsS();   // (G5b-2) a lookbehind row on the S statics
          ReverseCdnPackage(body);
          NoWriteOracleBodyCodeCdn(R.reverse_regex(body));
          CM.FFindMatchLookOracleTrueB(bytecode, str, inits, ov, dir, lookcdn);
          // (G3b) the plus winner keeps the VM winner's look bank (`ReplayPlusRowLB`)
        }
        assert CM.LookCpsOracleTrue(nlk, ov1) by {
          if result.Some? { assert fmres.Some?; } else { assert nlk == lk; }   // (G5b-3) the replay keeps OracleTrue
        }
        assert {:split_here} true;
        // ---- (G3a) clear-and-transfer: the tail on the CLEARED bank is the tail on the real one ----
        var nqtC := RRA.ClearCps(nqt, D);
        RRA.ClearCpsFinal(nqt, D);
        RRA.ClearCpsFacts(nqt, D);
        assert |nqtC.a_cp| == nquant && |nqtC.a_clk| == nquant;
        FLookLoopLookOracleTrue(crv, str, next, maxlook, capN, nlk, nqtC, ov1, S, Slook, ncap, nlook, nquant);
        RowsAvoidAt(crv, lid, maxlook, la, body);
        LLAF.FLookLoopAgreeFrom(crv, str, next, maxlook, capN, nlk, nqt, nqtC, ov1, D);
        var resTail := AI.FLookLoop(crv, str, next, maxlook, capN, nlk, nqt, ov1);
        var resTailC := AI.FLookLoop(crv, str, next, maxlook, capN, nlk, nqtC, ov1);
        assert resTail.0 == resTailC.0 && resTail.1 == resTailC.1;
      }
  }

  /** R3 DELIVERABLE 2 (DefGroups coverage corollary): under the whole-regex
      setup, EVERY inside-look group `g` whose innermost-DIRECT owner is matched
      in the FINAL look bank `res.1` has `res.0` carrying `g` at that owner's
      FRESH-body-match value. The bridge the seam `LkReplayMatchesSpecNestedFull`'s
      `recon_inner`/`recon_outer` premises consume. Proof: the `owner` guard is
      exactly `NI.InnermostOwnerDirect`'s three facts (`owner in LookIds(re)`,
      `g in CapIds(body_owner)`, `g !in CapIdsInLooks(body_owner)`); `VBodyEq
      LookBody` translates the table body to the structural body, `CapIdsSplit`
      places `g` in `CapIdsOutsideLooks(VBody(crv,owner))`, so `g`'s registers sit
      in `owner`'s OUTSIDE-look capture set; then DELIVERABLE 1
      (`FLookLoopValueLiftFull`) at `owner` supplies the value, weakened onto
      `CaptureRegsSet({g})`. Takes deliverable 1's hypotheses (a)-(h) as premises
      (the seam discharges them from the compilation's uniqueness + outer-before-
      inner ordering, as in `LookRowsFromTablesL3a`). */
  lemma InnermostOwnerUnique(re: R.regex, g: nat, owner0: nat, l: nat)
    requires PIV.CapUnique(re) && LTB.LookUnique(re)
    requires g in PIV.CapIdsInLooks(re)
    requires owner0 in LTB.LookIds(re) && g in PIV.CapIds(NI.LookBodyOfRE(re, owner0))
             && g !in PIV.CapIdsInLooks(NI.LookBodyOfRE(re, owner0))
    requires l in LTB.LookIds(re) && g in PIV.CapIds(NI.LookBodyOfRE(re, l))
             && g !in PIV.CapIdsInLooks(NI.LookBodyOfRE(re, l))
    ensures l == owner0
  {
    if l != owner0 {
      NI.NestedGWriteFrame(re, g, owner0, l);              // owner0 in LookIds(LookBodyOfRE(re, l))
      NI.LookBodyCompose(re, l, owner0);                   // LookBodyOfRE(re,owner0)==LookBodyOfRE(LookBodyOfRE(re,l),owner0)
      NI.LookBodyCapsIn(NI.LookBodyOfRE(re, l), owner0);   // CapIds(that) <= CapIdsInLooks(body_l)
      assert g in PIV.CapIdsInLooks(NI.LookBodyOfRE(re, l));   // contradiction
    }
  }

  /** REVERSE-LIVENESS FRAME (contrapositive engine step): the fold LEAVES `g`'s
      start register at its incoming `cap` value — provided the unique innermost
      owner `owner0` of `g` did NOT match in the final look bank. The register is
      written at a step only when that step's replay RUNS and its body owns `g`
      OUTSIDE its looks (`g in CapIdsOutsideLooks(body)`); by uniqueness only
      `owner0`'s step qualifies, and if that step ran it would force
      `MatchedPosLA(res.1, owner0)` (via `FLookLoopLidCpStable`) — ruled out by
      the hypothesis. Mirrors `FLookLoopCaptureFrameNested`'s induction (same
      per-step frame/`(b)`-transfer machinery), tracking a single register plus
      the owner exception. `decreases maxlook - lid`. */
  lemma QIdsOuterLeQIdsInt(body: R.regex)
    ensures QIdsOuter(body) <= LKC.QIdsInt(body)
  {
    PIV.QuantIdsSplit(body);
    forall k: int | k in QIdsOuter(body) ensures k in LKC.QIdsInt(body) {
      var q: nat :| q in PIV.QuantIdsOutsideLooks(body) && (q as int) == k;
      assert q in PIV.QuantIds(body);
    }
  }

  /** (G3a) Agreement of two banks' CLOCKS on `S` (lengths equal). The quant value lift is stated
      on clocks only: a reconstructing look row stamps quant POSITIONS in the running bank, and no
      consumer reads them (`GmOfLive` reads clocks, `GmOfLiveClkCong`). */
  ghost predicate QuantClkAgreeInside(a: AReg.Regs, b: AReg.Regs, S: set<int>) {
    |a.a_cp| == |b.a_cp| && |a.a_clk| == |b.a_clk|
    && (forall k: int :: k in S ==> AI.get_idx(a.a_clk, k) == AI.get_idx(b.a_clk, k))
  }

  /** C4e DELIVERABLE 2 (predicate): whole-loop QUANT reconstruction keyed on the
      FINAL look bank `res1` — quant twin of `FLookLoopValueOkFull`. For EVERY
      (possibly inner) matched positive lookahead `owner`, the fold's quant bank
      `res2` carries that body's FRESH match clocks on its OWN OUTSIDE-look quant
      ids `QIdsOuter(VBody(crv, owner))`. (Inner-look quants of the body come from
      the body's own inner lids — other owners — so, like inner-look CAPTURES on
      the capture side, they are covered per-owner and stitched by the endpoint,
      not claimed here.) */
  ghost predicate FLookLoopQuantValueOkFull(crv: CP.FCompiled, str: string, res2: AReg.Regs, res1: AReg.Regs,
                                            lid: int, maxlook: int, ov: LOr.OracleView, ncap: int, nlook: int, nquant: int) {
    forall owner: int :: lid <= owner <= maxlook && MatchedPosLA(crv, res1, owner) ==>
                           var rf := FreshBodyMatchPlus(crv, str, owner, res1, ov, ncap, nlook, nquant);
                           (rf.Some? ==> QuantClkAgreeInside(res2, rf.value.quant_regs, QIdsOuter(VBody(crv, owner))))
                           && (rf.None? ==> QuantClkAgreeInside(res2, AReg.init_regs(nquant), QIdsOuter(VBody(crv, owner))))
  }

  lemma QuantValueOkFullClkCong(crv: CP.FCompiled, str: string, a: AReg.Regs, b: AReg.Regs, res1: AReg.Regs,
                                lid: int, maxlook: int, ov: LOr.OracleView, ncap: int, nlook: int, nquant: int)
    requires |a.a_cp| == |b.a_cp| && |a.a_clk| == |b.a_clk|
    requires forall k: int :: AI.get_idx(a.a_clk, k) == AI.get_idx(b.a_clk, k)
    requires FLookLoopQuantValueOkFull(crv, str, b, res1, lid, maxlook, ov, ncap, nlook, nquant)
    ensures FLookLoopQuantValueOkFull(crv, str, a, res1, lid, maxlook, ov, ncap, nlook, nquant)
  {
    forall owner: int | lid <= owner <= maxlook && MatchedPosLA(crv, res1, owner)
      ensures var rf := FreshBodyMatchPlus(crv, str, owner, res1, ov, ncap, nlook, nquant);
              (rf.Some? ==> QuantClkAgreeInside(a, rf.value.quant_regs, QIdsOuter(VBody(crv, owner))))
              && (rf.None? ==> QuantClkAgreeInside(a, AReg.init_regs(nquant), QIdsOuter(VBody(crv, owner))))
    {
      var rf := FreshBodyMatchPlus(crv, str, owner, res1, ov, ncap, nlook, nquant);
      if rf.Some? { assert QuantClkAgreeInside(b, rf.value.quant_regs, QIdsOuter(VBody(crv, owner))); }
      else { assert QuantClkAgreeInside(b, AReg.init_regs(nquant), QIdsOuter(VBody(crv, owner))); }
    }
  }

  /** C4e: `owner == lid` is not a matched positive lookahead in `res1`, so the
      full quant map for `[lid, maxlook]` (keyed on `res1`) is exactly the one for
      `[lid+1, maxlook]`. Quant twin of `ValueOkFullSkipLid`. */
  lemma QuantValueOkFullSkipLid(crv: CP.FCompiled, str: string, res2: AReg.Regs, res1: AReg.Regs,
                                lid: int, maxlook: int, ov: LOr.OracleView, ncap: int, nlook: int, nquant: int)
    requires FLookLoopQuantValueOkFull(crv, str, res2, res1, lid + 1, maxlook, ov, ncap, nlook, nquant)
    requires !MatchedPosLA(crv, res1, lid)
    ensures FLookLoopQuantValueOkFull(crv, str, res2, res1, lid, maxlook, ov, ncap, nlook, nquant)
  {
    forall owner: int | lid <= owner <= maxlook && MatchedPosLA(crv, res1, owner)
      ensures var rf := FreshBodyMatchPlus(crv, str, owner, res1, ov, ncap, nlook, nquant);
              (rf.Some? ==> QuantClkAgreeInside(res2, rf.value.quant_regs, QIdsOuter(VBody(crv, owner))))
              && (rf.None? ==> QuantClkAgreeInside(res2, AReg.init_regs(nquant), QIdsOuter(VBody(crv, owner))))
    { assert owner != lid; }
  }

  /** C4e DELIVERABLE 2 (value lift): THE nested FLookLoop QUANT value lift keyed
      on the FINAL look bank `res.1` — quant twin of `FLookLoopValueLiftFull`,
      generalizing depth-1 `FLookLoopQuantValueLift` from `lk`-keyed to `res.1`-
      keyed (retaining inner looks matched part-way). The capture bank enters
      through its LENGTH alone; the per-lid value comes from `ReplayLidQuant
      AgreeFreshNested`, the per-replay quant write frame from `ReplayPlusQuant
      FrameNestedOuter`, and the suffix frame from `FLookLoopQuantFrameNested`.
      Same (a),(b),(e),(f),(g_new),(h) look-bank hypotheses as the capture lift,
      plus quant twins: (c'q) each body's quant slots INITIAL, (D-ord-q) outer
      quants of earlier ⟂ all quants of later, (Sq-bound) each body's outer quant
      ids land in `Sq`. `decreases maxlook - lid`. */
  lemma FLookLoopQuantValueLiftFull(crv: CP.FCompiled, str: string, lid: int, maxlook: int,
                                    cap: AReg.Regs, lk: AReg.Regs, qt: AReg.Regs, ov: LOr.OracleView,
                                    S: set<int>, Slook: set<int>, Sq: set<int>, ncap: int, nlook: int, nquant: int)
    requires ncap >= 0 && nlook >= 0 && nquant >= 0
    requires (forall k :: AI.get_idx(qt.a_cp, k) < 0)
             && (forall k :: AI.get_idx(qt.a_clk, k) >= -1)
    requires |qt.a_cp| == nquant && |qt.a_clk| == nquant
    requires |cap.a_cp| == ncap && |cap.a_clk| == ncap && PIV.CapRegWf(cap)
    requires |lk.a_cp| == nlook && |lk.a_clk| == nlook
    requires CM.LookCpsLE(lk, |str|)                                                            // (e)
    requires RowsAvoidO(crv, lid, maxlook)   // (G3a) later rows never name a row's outside-look quantifiers
    requires forall l: int, la: R.lookaround, body: R.regex ::                                   // (a)
               lid <= l <= maxlook && LTB.LookEntryOk(crv, l, la, body) ==> FrameEntryOk(crv, la, body, S, Slook)
    requires forall l: int :: lid <= l <= maxlook && AReg.get_cp(lk, l).Some? ==>                // (b)
                                exists la: R.lookaround, body: R.regex :: LTB.LookEntryOk(crv, l, la, body)
    requires forall l: int, la: R.lookaround, body: R.regex ::                                   // (c'q) per-body quant-unset
               lid <= l <= maxlook && LTB.LookEntryOk(crv, l, la, body) ==>
                 CM.RegsAgreeInside(qt, AReg.init_regs(nquant), LKC.QIdsInt(body))
    requires forall l1: int, la1: R.lookaround, b1: R.regex, l2: int, la2: R.lookaround, b2: R.regex ::  // (D-ord-q)
               lid <= l1 <= maxlook && lid <= l2 <= maxlook && l1 < l2
               && LTB.LookEntryOk(crv, l1, la1, b1) && LTB.LookEntryOk(crv, l2, la2, b2) ==>
                 QIdsOuter(b1) * LKC.QIdsInt(b2) == {}
    requires forall l1: int, la1: R.lookaround, b1: R.regex, l2: int ::                          // (f) look-stability
               (lid <= l1 <= maxlook && LTB.LookEntryOk(crv, l1, la1, b1)
               && lid <= l2 <= maxlook && l2 != l1 && AReg.get_cp(lk, l2).Some?) ==> l2 !in LookIdSet(b1)
    requires forall l1: int, la1: R.lookaround, b1: R.regex, l2: int, la2: R.lookaround, b2: R.regex ::  // (g_new)
               lid <= l1 <= maxlook && lid <= l2 <= maxlook && l1 < l2
               && LTB.LookEntryOk(crv, l1, la1, b1) && LTB.LookEntryOk(crv, l2, la2, b2) ==>
                 DirectLookIds(b1) * LTB.LookIds(b2) == {}
    requires forall l1: int, la1: R.lookaround, b1: R.regex, l2: int ::                          // (h) well-nested lids
               lid <= l1 <= maxlook && LTB.LookEntryOk(crv, l1, la1, b1) && lid <= l2 <= l1 ==> l2 !in LookIdSet(b1)
    requires forall l: int, la: R.lookaround, body: R.regex ::                                   // (Sq-bound)
               lid <= l <= maxlook && LTB.LookEntryOk(crv, l, la, body) ==> QIdsOuter(body) <= Sq
    // (G3a) no `a_cp < 0` any more: a lookahead row's reconstruction may leave positions set
    ensures var res := AI.FLookLoop(crv, str, lid, maxlook, cap, lk, qt, ov);
            |res.2.a_cp| == nquant && |res.2.a_clk| == nquant
            && (forall k :: AI.get_idx(res.2.a_clk, k) >= -1)
            && FLookLoopQuantValueOkFull(crv, str, res.2, res.1, lid, maxlook, ov, ncap, nlook, nquant)
    decreases maxlook - lid
  {
    var res := AI.FLookLoop(crv, str, lid, maxlook, cap, lk, qt, ov);
    if lid > maxlook {
      assert res.2 == qt;
      return;
    }
    var next := lid + 1;
    RowsAvoidSuffix(crv, lid, maxlook);
    assert forall l1: int, la1: R.lookaround, b1: R.regex ::
        lid <= l1 <= maxlook && LTB.LookEntryOk(crv, l1, la1, b1) ==> lid !in LookIdSet(b1);   // (h)@lid, l2:=lid
    FLookLoopLidCpStable(crv, str, lid, maxlook, cap, lk, qt, ov, S, Slook, ncap, nlook, nquant);
    assert AReg.get_cp(res.1, lid) == AReg.get_cp(lk, lid);
    assert {:split_here} true;
    match AReg.get_cp(lk, lid)
    case None =>
      assert res == AI.FLookLoop(crv, str, next, maxlook, cap, lk, qt, ov);
      FLookLoopQuantValueLiftFull(crv, str, next, maxlook, cap, lk, qt, ov, S, Slook, Sq, ncap, nlook, nquant);
      assert !MatchedPosLA(crv, res.1, lid);
      QuantValueOkFullSkipLid(crv, str, res.2, res.1, lid, maxlook, ov, ncap, nlook, nquant);
    case Some(cp) =>
      var looktype := if 0 <= lid < |crv.f_look_types| then crv.f_look_types[lid] else R.Lookahead;
      if !AI.capture_type(looktype) {
        assert res == AI.FLookLoop(crv, str, next, maxlook, cap, lk, qt, ov);
        FLookLoopQuantValueLiftFull(crv, str, next, maxlook, cap, lk, qt, ov, S, Slook, Sq, ncap, nlook, nquant);
        assert !MatchedPosLA(crv, res.1, lid);   // !capture_type(looktype), looktype == f_look_types[lid]
        QuantValueOkFullSkipLid(crv, str, res.2, res.1, lid, maxlook, ov, ncap, nlook, nquant);
      } else {
        var la: R.lookaround, body: R.regex :| LTB.LookEntryOk(crv, lid, la, body);
        assert 0 <= lid < |crv.f_look_types| && crv.f_look_types[lid] == la;
        assert looktype == la;
        assert body == VBody(crv, lid);
        assert FrameEntryOk(crv, la, body, S, Slook);
        assert la.Lookahead? || la.Lookbehind?;            // (L5 F7c-2) capture_type
        assert {:split_here} true;
        var bytecode := AI.get_code_v(crv.f_look_capture_bc, lid);
        var dir := AI.capture_direction(looktype);
        var lookcdn := if 0 <= lid < |crv.f_look_cdns| then crv.f_look_cdns[lid] else [];
        var lookast := if 0 <= lid < |crv.f_look_ast| then crv.f_look_ast[lid] else R.Re_empty;
        assert lookast == body;
        assert bytecode == CP.compile_to_bytecode(CP.capture_regex(la, body));
        var (result, ov1) := AI.FFindMatchPlus(bytecode, lookast, crv.f_plus_bc, str, ov, dir,
                                               cp, cap, lk, qt, 0, lookcdn);
        var capN := if result.None? then cap else result.value.capture_regs;
        var nlk := if result.None? then lk else result.value.look_regs;
        var nqt := if result.None? then qt else result.value.quant_regs;
        var D := QIdsOuter(body);
        assert res == AI.FLookLoop(crv, str, next, maxlook, capN, nlk, nqt, ov1);
        assert 0 <= cp <= |str| by { assert AI.get_idx(lk.a_cp, lid) == cp; }   // LookCpsLE + get_cp.Some?
        assert CM.RegsAgreeInside(qt, AReg.init_regs(nquant), LKC.QIdsInt(body));   // (c'q)@lid
        // the fresh PLUS match at lid, keyed on lk
        var rfLid := FreshBodyMatchPlus(crv, str, lid, lk, ov, ncap, nlook, nquant);
        assert {:split_here} true;
        // ---- per-kind replay: frames, wf, and the value at lid (replay ~ fresh on QIdsInt(body)) ----
        if la.Lookahead? {
          assert CP.capture_regex(la, body) == body;
          assert bytecode == CP.compile_to_bytecode(body);
          assert dir == LAnc.Forward;
          ReplayPlusRowLAS(bytecode, str, ov, lookcdn, crv.f_plus_bc, cp, cap, lk, qt, body, ncap, nlook, nquant);
          assert {:split_here} true;
          ReplayAgreePlusFresh(bytecode, str, cp, cap, lk, qt, ov, lookcdn, crv.f_plus_bc, body, {}, {},
                               ncap, nlook, nquant);
          assert {:split_here} true;
          assert rfLid == AI.FFindMatchPlus(bytecode, body, crv.f_plus_bc, str, ov, LAnc.Forward, cp,
                                            AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant),
                                            0, lookcdn).0 by {
            reveal FreshBodyMatchPlus();
          }
        } else {
          assert CP.capture_regex(la, body) == R.reverse_regex(body);
          assert bytecode == CP.compile_to_bytecode(R.reverse_regex(body));
          assert dir == LAnc.Backward;
          assert AI.cp_context(cp, str, LAnc.Backward).nextchar == AI.get_char(str, cp - 1) by {
            hide *; reveal AI.cp_context;   // a one-step unfold the ambient context drowns (20 s isolated)
          }
          assert {:split_here} true;
          // (G3b) a lookbehind row replays the plus machine too
          ReplayPlusRowLBS(bytecode, str, ov, lookcdn, crv.f_plus_bc, cp, cap, lk, qt, body, ncap, nlook, nquant);
          assert {:split_here} true;
          ReplayAgreePlusFreshDir(bytecode, str, cp, cap, lk, qt, ov, lookcdn, crv.f_plus_bc, body, {}, {},
                                  ncap, nlook, nquant, LAnc.Backward);
          assert {:split_here} true;
          assert rfLid == AI.FFindMatchPlus(bytecode, body, crv.f_plus_bc, str, ov, LAnc.Backward, cp,
                                            AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant),
                                            0, lookcdn).0 by {
            reveal FreshBodyMatchPlus();
          }
        }
        assert {:split_here} true;
        // ---- what both kinds deliver ----
        assert ov1 == ov;
        assert result.Some? ==> CM.ThreadRegsWf(result.value, ncap, nlook, nquant);
        assert |capN.a_cp| == ncap && |capN.a_clk| == ncap && PIV.CapRegWf(capN);
        assert |nlk.a_cp| == nlook && |nlk.a_clk| == nlook && CM.LookCpsLE(nlk, |str|);
        assert |nqt.a_cp| == nquant && |nqt.a_clk| == nquant;
        assert (forall k :: AI.get_idx(nqt.a_clk, k) >= -1)
            && (forall k :: k !in D ==> AI.get_idx(nqt.a_cp, k) < 0);
        assert CM.RegsAgreeOutside(nqt, qt, D) by { if result.Some? {} else { assert nqt == qt; } }
        assert CM.RegsAgreeOutside(nlk, lk, LookIdSet(body)) by { if result.Some? {} else { assert nlk == lk; } }
        assert CM.RegsAgreeOutside(nlk, lk, DirectLidSet(body)) by { if result.Some? {} else { assert nlk == lk; } }
        assert (result.None? <==> rfLid.None?)
            && (result.Some? ==> CM.RegsAgreeInside(nqt, rfLid.value.quant_regs, LKC.QIdsInt(body)));

        // ---- (G3a) the cleared bank the induction continues on ----
        assert {:split_here} true;
        var nqtC := RRA.ClearCps(nqt, D);
        RRA.ClearCpsFinal(nqt, D);
        RRA.ClearCpsFacts(nqt, D);
        assert |nqtC.a_cp| == nquant && |nqtC.a_clk| == nquant;
        RRA.QAgreeIdx(nqt, nqtC, D);

        // ---- recursion hypothesis transfer at [next] with (capN, nlk, nqtC) ----
        // (b) matched-look-has-entry for nlk
        assert {:split_here} true;
        assert forall l: int :: next <= l <= maxlook && AReg.get_cp(nlk, l).Some? ==>
                                  exists la2: R.lookaround, body2: R.regex :: LTB.LookEntryOk(crv, l, la2, body2)
        by {
          forall l: int | next <= l <= maxlook && AReg.get_cp(nlk, l).Some?
            ensures exists la2: R.lookaround, body2: R.regex :: LTB.LookEntryOk(crv, l, la2, body2)
          {
            if AReg.get_cp(lk, l).Some? {
            } else {
              assert result.Some?;
              NewLookInBody(nlk, lk, body, l);
              assert LTB.LookTablesOk(body, crv);
              LookIdEntryExists(body, crv, l as nat);
            }
          }
        }
        // (c'q) per-body quant-unset for nqtC: the row wrote only inside D, and clearing D writes `-1`
        assert {:split_here} true;
        assert forall l: int, la2: R.lookaround, body2: R.regex ::
            next <= l <= maxlook && LTB.LookEntryOk(crv, l, la2, body2) ==>
              CM.RegsAgreeInside(nqtC, AReg.init_regs(nquant), LKC.QIdsInt(body2))
        by {
          forall l: int, la2: R.lookaround, body2: R.regex | next <= l <= maxlook && LTB.LookEntryOk(crv, l, la2, body2)
            ensures CM.RegsAgreeInside(nqtC, AReg.init_regs(nquant), LKC.QIdsInt(body2))
          {
            assert CM.RegsAgreeInside(qt, AReg.init_regs(nquant), LKC.QIdsInt(body2));   // (c'q)@qt
            assert D * LKC.QIdsInt(body2) == {};   // (D-ord-q) lid<l
            CM.RegsAgreeOutsideTrans(nqtC, nqt, qt, D);
            UnsetOffTransfer(nqtC, qt, nquant, LKC.QIdsInt(body2), D);
          }
        }
        // (f) look-stability for nlk
        assert {:split_here} true;
        assert forall l1: int, la1: R.lookaround, b1: R.regex, l2: int ::
            (next <= l1 <= maxlook && LTB.LookEntryOk(crv, l1, la1, b1)
            && next <= l2 <= maxlook && l2 != l1 && AReg.get_cp(nlk, l2).Some?) ==> l2 !in LookIdSet(b1)
        by {
          forall l1: int, la1: R.lookaround, b1: R.regex, l2: int |
            next <= l1 <= maxlook && LTB.LookEntryOk(crv, l1, la1, b1)
            && next <= l2 <= maxlook && l2 != l1 && AReg.get_cp(nlk, l2).Some?
            ensures l2 !in LookIdSet(b1)
          {
            if AReg.get_cp(lk, l2).Some? {
              // (f)@lk
            } else {
              assert result.Some?;
              NewLookInBodyDirect(nlk, lk, body, l2);
              assert (l2 as nat) in DirectLookIds(body);
              assert lid < l1;                                          // l1 >= next
              assert DirectLookIds(body) * LTB.LookIds(b1) == {};       // (g_new) with (lid, l1)
              assert (l2 as nat) !in LTB.LookIds(b1) by {
                if (l2 as nat) in LTB.LookIds(b1) { assert (l2 as nat) in DirectLookIds(body) * LTB.LookIds(b1); }
              }
              if l2 in LookIdSet(b1) {
                var q: nat :| q in LTB.LookIds(b1) && (q as int) == l2;
                assert q == l2 as nat;
              }
            }
          }
        }
        // (h) well-nested lids for [next] — sub-instance of (h)@lid
        assert {:split_here} true;
        assert forall l1: int, la1: R.lookaround, b1: R.regex, l2: int ::
            next <= l1 <= maxlook && LTB.LookEntryOk(crv, l1, la1, b1) && next <= l2 <= l1 ==> l2 !in LookIdSet(b1);

        // ---- the IH on the cleared bank, and its transfer to the real tail ----
        assert {:split_here} true;
        FLookLoopQuantValueLiftFull(crv, str, next, maxlook, capN, nlk, nqtC, ov1, S, Slook, Sq, ncap, nlook, nquant);
        RowsAvoidAt(crv, lid, maxlook, la, body);
        LLAF.FLookLoopAgreeFrom(crv, str, next, maxlook, capN, nlk, nqt, nqtC, ov1, D);
        var resC := AI.FLookLoop(crv, str, next, maxlook, capN, nlk, nqtC, ov1);
        assert res.0 == resC.0 && res.1 == resC.1;
        RRA.QAgreeIdx(res.2, resC.2, D);
        assert |res.2.a_cp| == nquant && |res.2.a_clk| == nquant
               && (forall k :: AI.get_idx(res.2.a_clk, k) >= -1);
        assert {:split_here} true;
        assert FLookLoopQuantValueOkFull(crv, str, resC.2, res.1, next, maxlook, ov, ncap, nlook, nquant);
        QuantValueOkFullClkCong(crv, str, res.2, resC.2, res.1, next, maxlook, ov, ncap, nlook, nquant);
        assert FLookLoopQuantValueOkFull(crv, str, res.2, res.1, next, maxlook, ov, ncap, nlook, nquant);

        // ---- suffix frame: the cleared tail keeps nqtC on D; so res.2's CLOCKS on D are nqt's ----
        assert {:split_here} true;
        var Sqp := Sq - D;
        assert forall l: int, la2: R.lookaround, body2: R.regex ::
            next <= l <= maxlook && LTB.LookEntryOk(crv, l, la2, body2) ==>
              FrameEntryOk(crv, la2, body2, S, Slook) && QIdsOuter(body2) <= Sqp
        by {
          forall l: int, la2: R.lookaround, body2: R.regex | next <= l <= maxlook && LTB.LookEntryOk(crv, l, la2, body2)
            ensures FrameEntryOk(crv, la2, body2, S, Slook) && QIdsOuter(body2) <= Sqp
          {
            assert FrameEntryOk(crv, la2, body2, S, Slook);   // (a)
            QIdsOuterLeQIdsInt(body2);
            assert D * LKC.QIdsInt(body2) == {};   // (D-ord-q) lid<l
            assert QIdsOuter(body2) <= Sqp by {
              forall k: int | k in QIdsOuter(body2) ensures k in Sqp {
                assert k in Sq;   // (Sq-bound)
                assert k !in D by {
                  if k in D { assert k in D * LKC.QIdsInt(body2); }
                }
              }
            }
          }
        }
        assert {:split_here} true;
        FLookLoopQuantFrameNested(crv, str, next, maxlook, capN, nlk, nqtC, ov1, S, Slook, Sqp, ncap, nlook, nquant);
        assert CM.RegsAgreeOutside(resC.2, nqtC, Sqp);
        assert forall k: int :: k in D ==>
                 AI.get_idx(res.2.a_clk, k) == AI.get_idx(nqt.a_clk, k) by {
          forall k: int | k in D ensures AI.get_idx(res.2.a_clk, k) == AI.get_idx(nqt.a_clk, k) {
            assert k !in Sqp;
            assert AI.get_idx(res.2.a_clk, k) == AI.get_idx(resC.2.a_clk, k);    // QAgreeIdx(res.2, resC.2)
            assert AI.get_idx(resC.2.a_clk, k) == AI.get_idx(nqtC.a_clk, k);     // suffix frame
            assert AI.get_idx(nqtC.a_clk, k) == AI.get_idx(nqt.a_clk, k);        // QAgreeIdx(nqt, nqtC)
          }
        }

        // ---- assemble FLookLoopQuantValueOkFull for [lid] keyed on res.1 ----
        assert {:split_here} true;
        forall owner: int | lid <= owner <= maxlook && MatchedPosLA(crv, res.1, owner)
          ensures var rf2 := FreshBodyMatchPlus(crv, str, owner, res.1, ov, ncap, nlook, nquant);
                  (rf2.Some? ==> QuantClkAgreeInside(res.2, rf2.value.quant_regs, QIdsOuter(VBody(crv, owner))))
                  && (rf2.None? ==> QuantClkAgreeInside(res.2, AReg.init_regs(nquant), QIdsOuter(VBody(crv, owner))))
        {
          if owner == lid {
            // re-key lid's coverage from lk onto res.1 via stability (the fresh match reads lk at lid only)
            var rf2 := FreshBodyMatchPlus(crv, str, lid, res.1, ov, ncap, nlook, nquant);
            assert rf2 == rfLid by {
              assert AReg.get_cp(res.1, lid) == AReg.get_cp(lk, lid);   // stability
              reveal FreshBodyMatchPlus();
            }
            assert VBody(crv, lid) == body;
            QIdsOuterLeQIdsInt(body);
            assert D <= LKC.QIdsInt(body);
            if rfLid.Some? {
              assert result.Some?;
              assert CM.RegsAgreeInside(nqt, rfLid.value.quant_regs, LKC.QIdsInt(body));
              assert QuantClkAgreeInside(res.2, rfLid.value.quant_regs, D);
            } else {
              assert result.None? && nqt == qt;
              assert CM.RegsAgreeInside(qt, AReg.init_regs(nquant), LKC.QIdsInt(body));   // (c'q)@lid
              assert QuantClkAgreeInside(res.2, AReg.init_regs(nquant), D);
            }
          } else {
            // owner in [next, maxlook]: DIRECT from the IH (already keyed on res.1)
            assert next <= owner <= maxlook;
            assert FLookLoopQuantValueOkFull(crv, str, res.2, res.1, next, maxlook, ov, ncap, nlook, nquant);
          }
        }
      }
  }

  /** C4e DELIVERABLE 2 (QuantIds coverage corollary): quant twin of
      `FLookLoopFullCoversInLooks`. Under the whole-regex setup, EVERY inside-look
      quant id `qd` whose innermost-DIRECT owner is matched in the FINAL look bank
      `res.1` has `res.2` carrying `qd`'s FRESH-body-match clock at that owner.
      The bridge the endpoint's inside-value capstone consumes for feed (iii).
      Proof mirrors the capture corollary: the `owner` guard is `NI.Innermost
      OwnerDirect`'s three facts (with `QuantIds`/`QuantIdsInLooks` for `qd`),
      `VBodyEqLookBody` translates the table body to the structural body,
      `QuantIdsSplit` places `qd` in `QuantIdsOutsideLooks(VBody(crv,owner))`, so
      `qd as int` sits in `QIdsOuter`; then DELIVERABLE 2 (`FLookLoopQuantValue
      LiftFull`) at `owner` supplies the value, weakened onto `{qd as int}`.
      Takes the lift's hypotheses (a),(b),(e),(f),(g_new),(h) plus the quant
      twins (c'q),(D-ord-q),(Sq-bound) as premises. */
  // ===========================================================================
  // (L5 F7c-2b) LOOKBEHIND twins for the ancestor-set rider of the fresh body
  // match: the BACKWARD run of `compile(reverse_regex(body))`. The invariant
  // `AncSetInvRE` is `reverse_regex`-invariant (capture NESTING is untouched).
  // ===========================================================================

/** (G5a-1 P5b) `NoWriteOracleBodyCodeNested` on the top-level fragment: the same proof, the premise widened and its callees
      on their `…Cdn` forms where the argument is the top regex or a non-look subterm of it. */
  lemma NoWriteOracleBodyCodeCdn(body: R.regex)
    requires NR.NestedFragmentCdnRE(body)
    ensures CM.NoWriteOracleCode(CP.compile_to_bytecode(body))
  {
    var code := CP.compile_to_bytecode(body);
    var next := CP.compile(body, 0, CP.Progress).1;
    NR.CompileToBytecodeRepCdn(body);
    var endl := next as nat;
    forall pc: nat | pc < |code| ensures !code[pc].WriteOracle? {
      assert NR.GetPcRE(code, pc) == Some(code[pc]);
      if pc < endl {
        PSM.NoWriteInstrCdnRE(body, code, 0, endl, pc);
      } else {
        assert pc == endl;
        assert NR.GetPcRE(code, endl) == Some(RB.Accept);
      }
    }
  }

  /** (G5a-1 P5b) The narrow form, as a corollary of `NoWriteOracleBodyCodeCdn`. */
  lemma NoWriteOracleBodyCodeNested(body: R.regex)
    requires NR.NestedFragmentRE(body)
    ensures CM.NoWriteOracleCode(CP.compile_to_bytecode(body))
  {
    NR.NarrowIsCdn(body);
    hide *;   // the wide premises are this lemma's own: match by name
    NoWriteOracleBodyCodeCdn(body);
  }

  /** R2: nested twin of `FFindMatchPlusOvStable` — a nested positive lookAHEAD
      replay reads the oracle but never writes it, so `FFindMatchPlus` returns
      `ov` unchanged. Only the fragment inputs differ (`NoWriteOracleBodyCode
      Nested`, `NoTrueQuantStampNested`). */
  lemma FFindMatchPlusOvStableNested(bytecode: RB.code, str: string, ov: LOr.OracleView, dir: LAnc.direction,
                                     lookcdn: LCdn.cdns, plus_bcv: seq<RB.code>, cp: int,
                                     cap: AReg.Regs, lk: AReg.Regs, qt: AReg.Regs, la: R.lookaround, body: R.regex)
    requires NR.NestedFragmentRE(body) && PIV.CapUnique(body) && PIV.QuantUnique(body)
    requires NR.NoNulledPlusRE(body)   // §2.5b interim: all stamps false
    requires la.Lookahead? && dir == LAnc.Forward
    requires bytecode == CP.compile_to_bytecode(body)
    requires AI.cp_context(cp, str, dir).nextchar == AI.get_char(str, cp)
    requires (forall k :: AI.get_idx(qt.a_cp, k) < 0)
             && (forall k :: AI.get_idx(qt.a_clk, k) >= -1)
    ensures AI.FFindMatchPlus(bytecode, body, plus_bcv, str, ov, dir, cp, cap, lk, qt, 0, lookcdn).1 == ov
  {
    var inits := AI.FInitState(bytecode, cp, cap, lk, qt, 0, AI.cp_context(cp, str, dir));
    NoWriteOracleBodyCodeNested(body);
    CM.FFindMatchOvStable(bytecode, str, inits, ov, dir, lookcdn);
    NoTrueQuantStampNested(body);
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

  /** Agreement on `T` from agreement on a SUPERSET `U`. */
  lemma RegsAgreeInsideWeakenSub(a: AReg.Regs, b: AReg.Regs, T: set<int>, U: set<int>)
    requires CM.RegsAgreeInside(a, b, U) && T <= U
    ensures CM.RegsAgreeInside(a, b, T)
  {}

  /** R2: a regex's OUTSIDE-look capture regs are among ALL its capture regs. */
  lemma OuterCapsLeCaptureRegs(re: R.regex)
    ensures PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(re)) <= PIV.CaptureRegs(re)
  {
    PIV.CapIdsSplit(re);
    PIV.CaptureRegsSetMono(PIV.CapIdsOutsideLooks(re), PIV.CapIds(re));
    PIV.CaptureRegsIsSet(re);
  }

  /** R2: a look id NEWLY recorded by a body's replay (Some in `nlk`, None in the
      pre-replay `lk`, and `nlk`/`lk` agree outside `body`'s own look ids) is one
      of `body`'s own look ids. The `get_cp`↔`get_idx(a_cp)` bridge + the
      agree-outside contrapositive. */
  lemma NewLookInBody(nlk: AReg.Regs, lk: AReg.Regs, body: R.regex, l: int)
    requires CM.RegsAgreeOutside(nlk, lk, LookIdSet(body))
    requires AReg.get_cp(nlk, l).Some?
    requires AReg.get_cp(lk, l).None?
    ensures l >= 0 && (l as nat) in LTB.LookIds(body)
  {
    assert AI.get_idx(nlk.a_cp, l) >= 0 by {
      assert 0 <= l < |nlk.a_cp|;
      assert nlk.a_cp[l] >= 0;
    }
    assert AI.get_idx(lk.a_cp, l) < 0 by {
      if 0 <= l < |lk.a_cp| { assert lk.a_cp[l] < 0; }
    }
    assert l in LookIdSet(body) by {
      if l !in LookIdSet(body) {
        assert AI.get_idx(nlk.a_cp, l) == AI.get_idx(lk.a_cp, l);
        assert false;
      }
    }
    var l2: nat :| l2 in LTB.LookIds(body) && (l2 as int) == l;
    assert l as nat == l2;
  }

  /** recon A: DIRECT twin of `NewLookInBody`. Under the TIGHT replay frame
      (`RegsAgreeOutside(nlk, lk, DirectLidSet(body))`), any look id `l` newly
      set by the replay is a DIRECT (top-level) look id of `body`. Mirror of
      `NewLookInBody` with `LookIdSet`/`LookIds` replaced by `DirectLidSet`/
      `DirectLookIds`. */
  lemma NewLookInBodyDirect(nlk: AReg.Regs, lk: AReg.Regs, body: R.regex, l: int)
    requires CM.RegsAgreeOutside(nlk, lk, DirectLidSet(body))
    requires AReg.get_cp(nlk, l).Some?
    requires AReg.get_cp(lk, l).None?
    ensures l >= 0 && (l as nat) in DirectLookIds(body)
  {
    assert AI.get_idx(nlk.a_cp, l) >= 0 by {
      assert 0 <= l < |nlk.a_cp|;
      assert nlk.a_cp[l] >= 0;
    }
    assert AI.get_idx(lk.a_cp, l) < 0 by {
      if 0 <= l < |lk.a_cp| { assert lk.a_cp[l] < 0; }
    }
    assert l in DirectLidSet(body) by {
      if l !in DirectLidSet(body) {
        assert AI.get_idx(nlk.a_cp, l) == AI.get_idx(lk.a_cp, l);
        assert false;
      }
    }
    var l2: nat :| l2 in DirectLookIds(body) && (l2 as int) == l;
    assert l as nat == l2;
  }

  // ==========================================================================
  // R30a (L4 depth-k, ADDITIVE): discharge the (a)-(h) hypotheses of R3's
  // `FLookLoopValueLiftFull` / `FLookLoopFullCoversInLooks` (and R2's
  // `FLookLoopCaptureFrameNested`) from the compilation tables — the nested
  // analogue of `LookRowsFromTablesL3a`. The frame data comes from
  // `LookBodyFactsNested` (each look body is a nested fragment with its own
  // uniqueness/tables), well-nesting from `LTB.LidsWellNested`, and cross-lid
  // capture disjointness from `NI.LookBodiesCapsDisjointOrNested`.
  //
  // SCOPE: capturing looks are Lookahead-only (`NoPosLookbehindRE`), matching
  // the nested keystone; `FrameEntryOk`'s `capture_type(la) ==> la.Lookahead?`
  // clause forbids POSITIVE lookbehinds. recon A: the old (g) hypothesis
  // (`LookIds(b1)*LookIds(b2)=={}` for distinct rows) was only TRUE at nesting
  // depth <= 2; it is REPLACED by the ordered depth-general (g_new)
  // (`l1 < l2 ==> DirectLookIds(b1)*LookIds(b2)=={}`, `GNewFromTablesNested` via
  // `DirectEarlyNotInLateBody`), so `LookRowsFromTablesNested` /
  // `FLookLoopFullCoversFromTables` are now depth-GENERAL — the
  // `NR.NestDepth(re) <= 2` premise is GONE. The strong-(g) cluster
  // (`GDisjointBodies`/`GDisjointFromTablesNested`/`NestDepth0NoLookIds`) is kept
  // as dead code. ALL hypotheses are depth-general.
  // ==========================================================================

  /** No POSITIVE lookbehind occurs anywhere in `re`: at every lookaround node
      `la` is not `Lookbehind` (it may be `Lookahead`, `NegLookahead`, or
      `NegLookbehind`). This is exactly the side condition that makes
      `FrameEntryOk`'s `AI.capture_type(la) ==> la.Lookahead?` clause hold
      (`capture_type` is `Lookahead? || Lookbehind?`), i.e. the Lookahead-only
      scope of the nested capture-reconstruction bricks. */
  predicate NoPosLookbehindRE(re: R.regex)
    decreases re
  {
    match re
    case Re_empty => true
    case Re_character(_) => true
    case Re_anchor(_) => true
    case Re_alt(r1, r2) => NoPosLookbehindRE(r1) && NoPosLookbehindRE(r2)
    case Re_con(r1, r2) => NoPosLookbehindRE(r1) && NoPosLookbehindRE(r2)
    case Re_quant(_, _, _, r1) => NoPosLookbehindRE(r1)
    case Re_capture(_, r1) => NoPosLookbehindRE(r1)
    case Re_lookaround(lid, la, r1) => !la.Lookbehind? && NoPosLookbehindRE(r1)
  }


  /** Annotation transfers `NR.NoPosLookbehindRaw` (annotation preserves the
      lookaround CONSTRUCTOR at every look node). */
  lemma AnnotateNoPosLookbehind(ra: R.raw_regex, c: int, l: int, q: int)
    requires NR.NoPosLookbehindRaw(ra)
    ensures NoPosLookbehindRE(R.annotate_regex(ra, c, l, q).0)
    decreases ra
  {
    match ra
    case Raw_alt(r1, r2) =>
      AnnotateNoPosLookbehind(r1, c, l, q);
      var (_, c1, l1, q1) := R.annotate_regex(r1, c, l, q);
      AnnotateNoPosLookbehind(r2, c1, l1, q1);
    case Raw_con(r1, r2) =>
      AnnotateNoPosLookbehind(r1, c, l, q);
      var (_, c1, l1, q1) := R.annotate_regex(r1, c, l, q);
      AnnotateNoPosLookbehind(r2, c1, l1, q1);
    case Raw_quant(_, r1) => AnnotateNoPosLookbehind(r1, c, l, q + 1);
    case Raw_count(_, r1) => AnnotateNoPosLookbehind(r1, c, l, q + 1);
    case Raw_capture(r1) => AnnotateNoPosLookbehind(r1, c + 1, l, q);
    case Raw_lookaround(_, r1) => AnnotateNoPosLookbehind(r1, c, l + 1, q);
    case _ =>
  }

  /** The body of a look node in a nested-fragment regex is itself a nested
      fragment with its own uniqueness/tables, its lids sit among `re`'s, and
      the enclosing look is not a positive lookbehind. The nested analogue of
      `LookBodyOfFragment` + the uniqueness/table transfers, in one recursion
      mirroring `NI.LookBodyOfRE`. Depth-general. */
/** (G5a-1 P5b) `LookBodyFactsL5` on the top-level fragment: the same proof, the premise widened and its callees
      on their `…Cdn` forms where the argument is the top regex or a non-look subterm of it. */
  lemma LookBodyFactsL5Cdn(re: R.regex, crv: CP.FCompiled, lid: nat)
    requires NR.NestedFragmentCdnRE(re)
    requires PIV.CapUnique(re) && PIV.QuantUnique(re) && LTB.LookUnique(re)
    requires LTB.LookTablesOk(re, crv)
    requires lid in LTB.LookIds(re)
    ensures var body := NI.LookBodyOfRE(re, lid);
            NR.NestedFragmentCdnRE(body)   // (G5b) the look arm is Cdn; narrow readers add the gate
            && PIV.CapUnique(body) && PIV.QuantUnique(body) && LTB.LookUnique(body)
            && LTB.LookTablesOk(body, crv)
            && LTB.LookIds(body) <= LTB.LookIds(re)
            && var li: int := lid as int;   // (gate B) cast-free trigger; the LB-only clause is gone
               exists la: R.lookaround {:trigger LTB.LookEntryOk(crv, li, la, body)} :: LTB.LookEntryOk(crv, li, la, body)
    decreases re, 0
  {
    match re
    case Re_alt(r1, r2) =>
      if lid in LTB.LookIds(r1) { LookBodyFactsL5Cdn(r1, crv, lid); }
      else { LookBodyFactsL5Cdn(r2, crv, lid); }
    case Re_con(r1, r2) =>
      if lid in LTB.LookIds(r1) { LookBodyFactsL5Cdn(r1, crv, lid); }
      else { LookBodyFactsL5Cdn(r2, crv, lid); }
    case Re_quant(_, _, _, r1) => LookBodyFactsL5Cdn(r1, crv, lid);
    case Re_capture(_, r1) => LookBodyFactsL5Cdn(r1, crv, lid);
    case Re_lookaround(lid0, la0, r1) =>
      if lid0 >= 0 && (lid0 as nat) == lid {
        assert NI.LookBodyOfRE(re, lid) == r1;
        assert LTB.LookEntryOk(crv, lid as int, la0, r1);   // LookTablesOk's lookaround case
      } else {
        assert lid in LTB.LookIds(r1);
        LookBodyFactsL5Cdn(r1, crv, lid);
        assert LTB.LookIds(r1) <= LTB.LookIds(re);
      }
  }

  /** (G5a-1 P5b) The narrow form, as a corollary of `LookBodyFactsL5Cdn`. */
  lemma LookBodyFactsL5(re: R.regex, crv: CP.FCompiled, lid: nat)
    requires NR.NestedFragmentRE(re)
    requires PIV.CapUnique(re) && PIV.QuantUnique(re) && LTB.LookUnique(re)
    requires LTB.LookTablesOk(re, crv)
    requires lid in LTB.LookIds(re)
    ensures var body := NI.LookBodyOfRE(re, lid);
            NR.NestedFragmentRE(body)
            && PIV.CapUnique(body) && PIV.QuantUnique(body) && LTB.LookUnique(body)
            && LTB.LookTablesOk(body, crv)
            && LTB.LookIds(body) <= LTB.LookIds(re)
            && var li: int := lid as int;   // (gate B) cast-free trigger; the LB-only clause is gone
               exists la: R.lookaround {:trigger LTB.LookEntryOk(crv, li, la, body)} :: LTB.LookEntryOk(crv, li, la, body)
    decreases re
  {
    NR.NarrowIsCdn(re);
    hide *;   // the wide premises are this lemma's own: match by name
    LookBodyFactsL5Cdn(re, crv, lid);
    NestedFragmentLookBody(re, lid);   // (G5b) narrow body from a narrow regex
  }


  /** R2: transfer of "unset on `Bset`" across a write confined to `Dset`
      (disjoint from `Bset`): if `cap` is init on `Bset` and `capN` agrees with
      `cap` outside `Dset`, then `capN` is init on `Bset` too. */
  lemma UnsetOffTransfer(capN: AReg.Regs, cap: AReg.Regs, ncap: int, Bset: set<int>, Dset: set<int>)
    requires CM.RegsAgreeInside(cap, AReg.init_regs(ncap), Bset)
    requires CM.RegsAgreeOutside(capN, cap, Dset)
    requires Dset * Bset == {}
    requires |capN.a_cp| == |cap.a_cp| && |capN.a_clk| == |cap.a_clk|
    ensures CM.RegsAgreeInside(capN, AReg.init_regs(ncap), Bset)
  {
    forall k: int | k in Bset
      ensures AI.get_idx(capN.a_cp, k) == AI.get_idx(AReg.init_regs(ncap).a_cp, k)
              && AI.get_idx(capN.a_clk, k) == AI.get_idx(AReg.init_regs(ncap).a_clk, k)
    {
      assert k !in Dset by { if k in Dset { assert k in Dset * Bset; } }
      assert AI.get_idx(capN.a_cp, k) == AI.get_idx(cap.a_cp, k);
    }
  }

  // ==========================================================================
  // R31a (L4 depth-k, ADDITIVE): ENGINE-glue tables-discharge. Produces the
  // (a)-(h) hypotheses that R3's `FLookLoopValueLiftFull`/`FLookLoopFullCovers
  // InLooks` and R2's `FLookLoopCaptureFrameNested` require, from the
  // whole-regex compilation setup — the nested analogue of
  // `LookRowsFromTablesL3a`. S := CaptureRegsSet(CapIdsInLooks(re)), Slook :=
  // LookIdSet(re). recon A: (g) is replaced by the ordered (g_new); ALL
  // hypotheses are now depth-general (no `NR.NestDepth(re) <= 2` premise).
  // ==========================================================================

  /** `tl_flatten` never shrinks below its `tail`: the compiled body sits in
      front of the terminal instruction(s). */
  lemma TlFlattenLenGe(t: CP.treelist, tail: seq<RB.instruction>)
    ensures |CP.tl_flatten(t, tail)| >= |tail|
    decreases t
  {
    match t
    case Leaf(l) =>
    case Concat(a, b) => TlFlattenLenGe(b, tail); TlFlattenLenGe(a, CP.tl_flatten(b, tail));
  }

  /** Every compiled block is non-empty (it ends in `Accept`). Lets us rule out
      a "garbage" look-table row, whose seed `f_look_capture_bc` is `[]`. */
  lemma CompileToBytecodeNonEmpty(x: R.regex)
    ensures |CP.compile_to_bytecode(x)| >= 1
  {
    TlFlattenLenGe(CP.compile(x, 0, CP.Progress).0, [RB.Accept]);
  }

  /** A look-table row satisfying `LookEntryOk` is a REAL look id: the
      `FFullCompilation` seed leaves every non-lookid row's `f_look_capture_bc`
      at `[]`, but `LookEntryOk` pins it to the (non-empty) compiled capture
      block. So the (a)-(h) row quantifiers never hit a spurious row. */
  lemma LookEntryOnlyReal(ast: R.regex, crv: CP.FCompiled, l: int, la: R.lookaround, body: R.regex)
    requires crv == CP.FFullCompilation(ast)
    requires 0 <= l <= R.max_lookaround(ast)
    requires LTB.LookEntryOk(crv, l, la, body)
    ensures (l as nat) in LTB.LookIds(ast)
  {
    if (l as nat) !in LTB.LookIds(ast) {
      var nlook0 := R.max_lookaround(ast) + 1;
      var nquant0 := R.max_quant(ast) + 1;
      var seed := CP.FCompiled(ast, CP.compile_to_bytecode(R.lazy_prefix(ast)), LCdn.compile_cdns(ast),
                               seq(nlook0, i => R.Lookahead), seq(nlook0, i => R.Re_empty),
                               seq(nlook0, i => []), seq(nlook0, i => []),
                               seq(nlook0, i => []), seq(nquant0, i => []));
      assert CP.FFullCompilation(ast) == CP.FCompileExtra(ast, seed);
      LTB.FCompileExtraLookFrame(ast, seed);
      assert LTB.SameLookSizes(seed, crv);
      assert LTB.AgreeAt(seed, crv, l as nat);
      assert |seed.f_look_capture_bc| == nlook0 && |crv.f_look_capture_bc| == nlook0;
      assert seed.f_look_capture_bc[l] == [];
      assert crv.f_look_capture_bc[l] == seed.f_look_capture_bc[l];   // AgreeAt
      assert crv.f_look_capture_bc[l] == CP.compile_to_bytecode(CP.capture_regex(la, body));  // LookEntryOk
      CompileToBytecodeNonEmpty(CP.capture_regex(la, body));
      assert false;
    }
  }

  /** Every lid in a look body sits STRICTLY ABOVE the enclosing lid — the
      body-scoped reading of `LidsWellNested`. Discharges (h) and kills the
      "outer nested in inner" arm of the (D-ord) trichotomy (an `l1 < l2` pair
      can never have `l1` nested in `l2`'s body). */
  lemma LookBodyLidsGt(r: R.regex, l: nat)
    requires LTB.LidsWellNested(r)
    requires l in LTB.LookIds(r)
    ensures forall x: nat :: x in LTB.LookIds(NI.LookBodyOfRE(r, l)) ==> l < x
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      if l in LTB.LookIds(r1) { LookBodyLidsGt(r1, l); } else { LookBodyLidsGt(r2, l); }
    case Re_con(r1, r2) =>
      if l in LTB.LookIds(r1) { LookBodyLidsGt(r1, l); } else { LookBodyLidsGt(r2, l); }
    case Re_quant(_, _, _, r1) => LookBodyLidsGt(r1, l);
    case Re_capture(_, r1) => LookBodyLidsGt(r1, l);
    case Re_lookaround(lid0, _, r1) =>
      if lid0 >= 0 && (lid0 as nat) == l {
        assert NI.LookBodyOfRE(r, l) == r1;
        // LidsWellNested at this node: every lid of r1 is > lid0 == l
      } else {
        assert l in LTB.LookIds(r1);
        LookBodyLidsGt(r1, l);
        assert NI.LookBodyOfRE(r, l) == NI.LookBodyOfRE(r1, l);
      }
  }

  /** (§2.5b F-c) The look bodies are nulled-plus-free — all the look-row and
      look-loop machinery needs; the main regex may carry CIN-greedy pluses
      OUTSIDE its lookarounds. Structural, so it descends with every sweep. */
  ghost predicate LooksNoNulledPlusRE(re: R.regex)
    decreases re
  {
    match re
    case Re_alt(r1, r2) => LooksNoNulledPlusRE(r1) && LooksNoNulledPlusRE(r2)
    case Re_con(r1, r2) => LooksNoNulledPlusRE(r1) && LooksNoNulledPlusRE(r2)
    case Re_quant(_, _, _, r1) => LooksNoNulledPlusRE(r1)
    case Re_capture(_, r1) => LooksNoNulledPlusRE(r1)
    case Re_lookaround(_, _, r1) => NR.NoNulledPlusRE(r1)
    case _ => true
  }

  lemma LooksNoNulledPlusFromFull(re: R.regex)
    requires NR.NoNulledPlusRE(re)
    ensures LooksNoNulledPlusRE(re)
    decreases re
  {
    match re
    case Re_alt(r1, r2) => LooksNoNulledPlusFromFull(r1); LooksNoNulledPlusFromFull(r2);
    case Re_con(r1, r2) => LooksNoNulledPlusFromFull(r1); LooksNoNulledPlusFromFull(r2);
    case Re_quant(_, _, _, r1) => LooksNoNulledPlusFromFull(r1);
    case Re_capture(_, r1) => LooksNoNulledPlusFromFull(r1);
    case _ =>
  }

  /** The look-bodies gate descends: a look body is fully nulled-plus-free, so
      its own look bodies are too. */
  lemma LooksNoNulledPlusBody(re: R.regex, l: nat)
    requires LooksNoNulledPlusRE(re) && l in LTB.LookIds(re)
    ensures NR.NoNulledPlusRE(NI.LookBodyOfRE(re, l)) && LooksNoNulledPlusRE(NI.LookBodyOfRE(re, l))
    decreases re
  {
    match re
    case Re_alt(r1, r2) =>
      if l in LTB.LookIds(r1) { LooksNoNulledPlusBody(r1, l); } else { LooksNoNulledPlusBody(r2, l); }
    case Re_con(r1, r2) =>
      if l in LTB.LookIds(r1) { LooksNoNulledPlusBody(r1, l); } else { LooksNoNulledPlusBody(r2, l); }
    case Re_quant(_, _, _, r1) => LooksNoNulledPlusBody(r1, l);
    case Re_capture(_, r1) => LooksNoNulledPlusBody(r1, l);
    case Re_lookaround(lid0, _, r1) =>
      if lid0 >= 0 && (lid0 as nat) == l {
        LooksNoNulledPlusFromFull(r1);
      } else {
        NI.NoNulledPlusLookBody(r1, l);
        LooksNoNulledPlusFromFull(NI.LookBodyOfRE(r1, l));
      }
    case _ =>
  }

  /** (a) per-row: any `LookEntryOk` row of the whole-regex tables satisfies
      `FrameEntryOk` at S := CaptureRegsSet(CapIdsInLooks(re)), Slook :=
      LookIdSet(re). Body facts from `LookBodyFactsNested`; the capture-set
      containment from `NI.LookBodyCapsIn` (body caps are inside-look caps of
      re); the lookahead-only clause from `NoPosLookbehindRE`. Depth-general. */
/** (G5a-1 P5b) `FrameEntryOkFromTables` on the top-level fragment: the same proof, the premise widened and its callees
      on their `…Cdn` forms where the argument is the top regex or a non-look subterm of it. */
  lemma FrameEntryOkFromTablesCdn(ast: R.regex, re: R.regex, crv: CP.FCompiled,
                               l: int, la: R.lookaround, body: R.regex)
    requires crv == CP.FFullCompilation(ast)
    requires re == R.lazy_prefix(ast)
    requires LookBodiesPlusGateRE(re)   // (G3a) the weak gate: lookbehind bodies stamp-free, lookahead bodies CIN
    requires T.TransWf(re)               // (G3a) for the plus table (`FRD.PlusTableOkFull`)
    requires NR.NestedFragmentCdnRE(re)
    requires PIV.CapUnique(re) && PIV.QuantUnique(re) && LTB.LookUnique(re)
    requires LTB.LookTablesOk(re, crv)
    requires 1 <= l <= R.max_lookaround(ast)
    requires LTB.LookEntryOk(crv, l, la, body)
    ensures FrameEntryOk(crv, la, body,
                         PIV.CaptureRegsSet(PIV.CapIdsInLooks(re)), LookIdSet(re))
  {
    var pre := R.Re_quant(R.NonNullable, 0, R.CountedQuant(0, None, false),
                          R.Re_character(R.Dot));
    assert re == R.Re_con(pre, ast);
    assert LTB.LookIds(pre) == {};
    assert LTB.LookIds(re) == LTB.LookIds(ast);
    LookEntryOnlyReal(ast, crv, l, la, body);           // (l as nat) in LookIds(ast) == LookIds(re)
    var lid := l as nat;
    assert lid in LTB.LookIds(re);
    LookBodyFactsL5Cdn(re, crv, lid);
    var body' := NI.LookBodyOfRE(re, lid);
    // LookEntryOk determinism at row lid pins body == body' (via the table tie).
    NI.LookBodyOfTablesTie(re, crv, lid);
    var la0: R.lookaround :| LTB.LookEntryOk(crv, lid as int, la0, body');
    assert body == crv.f_look_ast[lid] == body';
    // CaptureRegsSet(CapIdsOutsideLooks(body)) <= CaptureRegsSet(CapIdsInLooks(re))
    NI.LookBodyCapsIn(re, lid);                          // CapIds(body') <= CapIdsInLooks(re)
    PIV.CapIdsSplit(body');                              // CapIdsOutsideLooks(body') <= CapIds(body')
    PIV.CaptureRegsSetMono(PIV.CapIdsOutsideLooks(body'), PIV.CapIdsInLooks(re));
    // LookIdSet(body) <= LookIdSet(re)
    assert LTB.LookIds(body') <= LTB.LookIds(re);
    assert LookIdSet(body') <= LookIdSet(re);
    // (G3a/G3b) the row's statics, every kind
    PlusGateBodyCdn(re, crv, lid, la, body);
    NI.LookBodyOfFragmentCdn(re, lid);   // the body is in the Cdn fragment
    if NRC.PositiveLk(la) {
      // (G5a-1 P5b) the top may hold a CDN plus (`NestedNoCdn(ast)` is false then): the widened table of
      // the whole regex
      FRD.PlusTableOkFullS(ast);
      // (G5b-1, G5b-2) a positive body (either direction) may hold a CDN plus: the S statics, the widened table
      // at the body
      TransWfLookBodyOfRE(re, lid);
      FRA.PlusTableOkSLookBodyS(re, crv.f_plus_bc, lid);
      GateCdnTop(body);
      reveal RowLAStaticsS();
      assert RowLAStaticsS(body, crv.f_plus_bc);
    }
  }

  /** (G5a-1 P5b) The narrow form, as a corollary of `FrameEntryOkFromTablesCdn`. */
  lemma FrameEntryOkFromTables(ast: R.regex, re: R.regex, crv: CP.FCompiled,
                               l: int, la: R.lookaround, body: R.regex)
    requires crv == CP.FFullCompilation(ast)
    requires re == R.lazy_prefix(ast)
    requires LookBodiesPlusGateRE(re)   // (G3a) the weak gate: lookbehind bodies stamp-free, lookahead bodies CIN
    requires T.TransWf(re)               // (G3a) for the plus table (`FRD.PlusTableOkFull`)
    requires NR.NestedFragmentRE(re)
    requires PIV.CapUnique(re) && PIV.QuantUnique(re) && LTB.LookUnique(re)
    requires LTB.LookTablesOk(re, crv)
    requires 1 <= l <= R.max_lookaround(ast)
    requires LTB.LookEntryOk(crv, l, la, body)
    ensures FrameEntryOk(crv, la, body,
                         PIV.CaptureRegsSet(PIV.CapIdsInLooks(re)), LookIdSet(re))
  {
    NR.NarrowIsCdn(re);
    hide *;   // the wide premises are this lemma's own: match by name
    FrameEntryOkFromTablesCdn(ast, re, crv, l, la, body);
  }

  /** (G3a) The nested fragment admits no CDN-greedy plus (twin of `MCL.NestedNoCdnLk`, needed below
      the top level for the plus table). */
  lemma {:induction false} NestedNoCdn(re: R.regex)
    requires NR.NestedFragmentRE(re)
    ensures NRC.NoCdnPlusRE(re)
    decreases re
  {
    match re
    case Re_empty =>
    case Re_character(_) =>
    case Re_anchor(_) =>
    case Re_alt(r1, r2) => NestedNoCdn(r1); NestedNoCdn(r2);
    case Re_con(r1, r2) => NestedNoCdn(r1); NestedNoCdn(r2);
    case Re_quant(_, _, _, r1) => NestedNoCdn(r1);
    case Re_capture(_, r1) => NestedNoCdn(r1);
    case Re_lookaround(_, _, r1) => NestedNoCdn(r1);
  }

  /** (h) per-row: `l2 !in LookIdSet(b1)` for `l2 <= l1`. The row `b1` is
      `LookBodyOfRE(re, l1)`, whose lids are all `> l1` (`LookBodyLidsGt`), so
      no `l2 <= l1` lands inside. Depth-general. */
  lemma HFromTables(ast: R.regex, re: R.regex, crv: CP.FCompiled,
                    l1: int, la1: R.lookaround, b1: R.regex, l2: int)
    requires crv == CP.FFullCompilation(ast)
    requires re == R.lazy_prefix(ast)
    requires LookBodiesPlusGateRE(re)   // (G3a) the weak gate (was LooksNoNulledPlusRE)
    requires T.TransWf(re)   // (G3a) for FrameEntryOkFromTables' plus table
    requires LTB.LookUnique(re) && LTB.LookTablesOk(re, crv) && LTB.LidsWellNested(re)
    requires 1 <= l1 <= R.max_lookaround(ast)
    requires LTB.LookEntryOk(crv, l1, la1, b1)
    requires 1 <= l2 <= l1
    ensures l2 !in LookIdSet(b1)
  {
    var pre := R.Re_quant(R.NonNullable, 0, R.CountedQuant(0, None, false),
                          R.Re_character(R.Dot));
    assert re == R.Re_con(pre, ast);
    assert LTB.LookIds(re) == LTB.LookIds(ast);
    LookEntryOnlyReal(ast, crv, l1, la1, b1);
    var lid1 := l1 as nat;
    assert lid1 in LTB.LookIds(re);
    NI.LookBodyOfTablesTie(re, crv, lid1);
    var la0: R.lookaround :| LTB.LookEntryOk(crv, lid1 as int, la0, NI.LookBodyOfRE(re, lid1));
    assert b1 == crv.f_look_ast[lid1] == NI.LookBodyOfRE(re, lid1);
    LookBodyLidsGt(re, lid1);                       // every x in LookIds(b1) has l1 < x
    if l2 in LookIdSet(b1) {
      var x: nat :| x in LTB.LookIds(b1) && (x as int) == l2;
      assert lid1 < x;                              // LookBodyLidsGt
      assert false;                                 // x == l2 <= l1 == lid1 < x
    }
  }

  /** (D-ord) per-pair: for `l1 < l2`, `CaptureRegsSet(CapIdsOutsideLooks(b1))`
      is disjoint from `CaptureRegs(b2)`. The two bodies are disjoint siblings
      or `b2` is nested inside `b1` (`NI.LookBodiesCapsDisjointOrNested`); the
      third "b1 nested in b2" arm is killed by well-nesting (`l1 < l2` forbids
      `l1 in LookIds(b2)`). In the nested arm `b2`'s caps sit in `b1`'s
      INSIDE-look caps, disjoint from `b1`'s OUTSIDE-look caps. Depth-general. */
/** (G5a-1 P5b) `DOrdFromTables` on the top-level fragment: the same proof, the premise widened and its callees
      on their `…Cdn` forms where the argument is the top regex or a non-look subterm of it. */
  lemma DOrdFromTablesCdn(ast: R.regex, re: R.regex, crv: CP.FCompiled,
                       l1: int, la1: R.lookaround, b1: R.regex,
                       l2: int, la2: R.lookaround, b2: R.regex)
    requires crv == CP.FFullCompilation(ast)
    requires re == R.lazy_prefix(ast)
    requires LookBodiesPlusGateRE(re)   // (G3a) the weak gate (was LooksNoNulledPlusRE)
    requires T.TransWf(re)   // (G3a) for FrameEntryOkFromTables' plus table
    requires NR.NestedFragmentCdnRE(re)   // (L5 F7c) lifted from NoPosLookbehindRE
    requires PIV.CapUnique(re) && PIV.QuantUnique(re) && LTB.LookUnique(re)
    requires LTB.LookTablesOk(re, crv) && LTB.LidsWellNested(re)
    requires 1 <= l1 <= R.max_lookaround(ast) && 1 <= l2 <= R.max_lookaround(ast) && l1 < l2
    requires LTB.LookEntryOk(crv, l1, la1, b1) && LTB.LookEntryOk(crv, l2, la2, b2)
    ensures PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(b1)) * PIV.CaptureRegs(b2) == {}
  {
    var pre := R.Re_quant(R.NonNullable, 0, R.CountedQuant(0, None, false),
                          R.Re_character(R.Dot));
    assert re == R.Re_con(pre, ast);
    assert LTB.LookIds(re) == LTB.LookIds(ast);
    LookEntryOnlyReal(ast, crv, l1, la1, b1);
    LookEntryOnlyReal(ast, crv, l2, la2, b2);
    var lid1 := l1 as nat;
    var lid2 := l2 as nat;
    NI.LookBodyOfTablesTie(re, crv, lid1);
    NI.LookBodyOfTablesTie(re, crv, lid2);
    var la01: R.lookaround :| LTB.LookEntryOk(crv, lid1 as int, la01, NI.LookBodyOfRE(re, lid1));
    var la02: R.lookaround :| LTB.LookEntryOk(crv, lid2 as int, la02, NI.LookBodyOfRE(re, lid2));
    assert b1 == NI.LookBodyOfRE(re, lid1);
    assert b2 == NI.LookBodyOfRE(re, lid2);
    LookBodyFactsL5Cdn(re, crv, lid1);                 // CapUnique(b1)
    PIV.CaptureRegsIsSet(b2);                           // CaptureRegs(b2) == CaptureRegsSet(CapIds(b2))
    PIV.CapIdsSplit(b1);                                // CapIdsOutsideLooks(b1) <= CapIds(b1)
    NI.LookBodiesCapsDisjointOrNested(re, lid1, lid2);
    if PIV.CapIds(b1) * PIV.CapIds(b2) == {} {
      // siblings: outside(b1) <= CapIds(b1), disjoint from CapIds(b2)
      assert PIV.CapIdsOutsideLooks(b1) * PIV.CapIds(b2) == {};
      PIV.CaptureRegsSetDisjoint(PIV.CapIdsOutsideLooks(b1), PIV.CapIds(b2));
    } else if lid2 in LTB.LookIds(b1) && PIV.CapIds(b2) <= PIV.CapIds(b1) {
      // b2 nested in b1: b2's caps are INSIDE-look caps of b1
      NI.LookBodyCompose(re, lid1, lid2);              // b2 == LookBodyOfRE(b1, lid2)
      NI.LookBodyCapsIn(b1, lid2);                     // CapIds(b2) <= CapIdsInLooks(b1)
      PIV.CapIdsLooksDisjoint(b1);                     // outside(b1) * inside(b1) == {}
      assert PIV.CapIdsOutsideLooks(b1) * PIV.CapIds(b2) == {};
      PIV.CaptureRegsSetDisjoint(PIV.CapIdsOutsideLooks(b1), PIV.CapIds(b2));
    } else {
      // b1 nested in b2 (l1 in LookIds(b2)) — impossible: well-nesting forces l2 < l1
      assert lid1 in LTB.LookIds(b2);
      LookBodyLidsGt(re, lid2);                         // x in LookIds(b2) ==> l2 < x
      assert lid2 < lid1;                               // contra l1 < l2
      assert false;
    }
  }

  /** (G5a-1 P5b) The narrow form, as a corollary of `DOrdFromTablesCdn`. */
  lemma DOrdFromTables(ast: R.regex, re: R.regex, crv: CP.FCompiled,
                       l1: int, la1: R.lookaround, b1: R.regex,
                       l2: int, la2: R.lookaround, b2: R.regex)
    requires crv == CP.FFullCompilation(ast)
    requires re == R.lazy_prefix(ast)
    requires LookBodiesPlusGateRE(re)   // (G3a) the weak gate (was LooksNoNulledPlusRE)
    requires T.TransWf(re)   // (G3a) for FrameEntryOkFromTables' plus table
    requires NR.NestedFragmentRE(re)   // (L5 F7c) lifted from NoPosLookbehindRE
    requires PIV.CapUnique(re) && PIV.QuantUnique(re) && LTB.LookUnique(re)
    requires LTB.LookTablesOk(re, crv) && LTB.LidsWellNested(re)
    requires 1 <= l1 <= R.max_lookaround(ast) && 1 <= l2 <= R.max_lookaround(ast) && l1 < l2
    requires LTB.LookEntryOk(crv, l1, la1, b1) && LTB.LookEntryOk(crv, l2, la2, b2)
    ensures PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(b1)) * PIV.CaptureRegs(b2) == {}
  {
    NR.NarrowIsCdn(re);
    hide *;   // the wide premises are this lemma's own: match by name
    DOrdFromTablesCdn(ast, re, crv, l1, la1, b1, l2, la2, b2);
  }

  /** A look body's lids are among the whole regex's lids — the LookIds twin of
      `NI.LookBodyCapsIn`. */
  lemma LookBodyLidsSubset(r: R.regex, l: nat)
    requires l in LTB.LookIds(r)
    ensures LTB.LookIds(NI.LookBodyOfRE(r, l)) <= LTB.LookIds(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      if l in LTB.LookIds(r1) { LookBodyLidsSubset(r1, l); } else { LookBodyLidsSubset(r2, l); }
    case Re_con(r1, r2) =>
      if l in LTB.LookIds(r1) { LookBodyLidsSubset(r1, l); } else { LookBodyLidsSubset(r2, l); }
    case Re_quant(_, _, _, r1) => LookBodyLidsSubset(r1, l);
    case Re_capture(_, r1) => LookBodyLidsSubset(r1, l);
    case Re_lookaround(lid0, _, r1) =>
      if lid0 >= 0 && (lid0 as nat) == l {
      } else {
        LookBodyLidsSubset(r1, l);
      }
  }

  /** A regex with no lookaround nesting (`NestDepth == 0`) has no lookaround at
      all, hence no look ids. */
  lemma GNewFromTablesNested(ast: R.regex, re: R.regex, crv: CP.FCompiled,
                             l1: int, la1: R.lookaround, b1: R.regex,
                             l2: int, la2: R.lookaround, b2: R.regex)
    requires crv == CP.FFullCompilation(ast)
    requires re == R.lazy_prefix(ast)
    requires LookBodiesPlusGateRE(re)   // (G3a) the weak gate (was LooksNoNulledPlusRE)
    requires T.TransWf(re)   // (G3a) for FrameEntryOkFromTables' plus table
    requires LTB.LookUnique(re) && LTB.LookTablesOk(re, crv) && LTB.LidsWellNested(re)
    requires 1 <= l1 <= R.max_lookaround(ast) && 1 <= l2 <= R.max_lookaround(ast) && l1 < l2
    requires LTB.LookEntryOk(crv, l1, la1, b1) && LTB.LookEntryOk(crv, l2, la2, b2)
    ensures DirectLookIds(b1) * LTB.LookIds(b2) == {}
  {
    var pre := R.Re_quant(R.NonNullable, 0, R.CountedQuant(0, None, false),
                          R.Re_character(R.Dot));
    assert re == R.Re_con(pre, ast);
    assert LTB.LookIds(re) == LTB.LookIds(ast);
    LookEntryOnlyReal(ast, crv, l1, la1, b1);
    LookEntryOnlyReal(ast, crv, l2, la2, b2);
    var lid1 := l1 as nat;
    var lid2 := l2 as nat;
    NI.LookBodyOfTablesTie(re, crv, lid1);
    NI.LookBodyOfTablesTie(re, crv, lid2);
    var la01: R.lookaround :| LTB.LookEntryOk(crv, lid1 as int, la01, NI.LookBodyOfRE(re, lid1));
    var la02: R.lookaround :| LTB.LookEntryOk(crv, lid2 as int, la02, NI.LookBodyOfRE(re, lid2));
    assert b1 == NI.LookBodyOfRE(re, lid1);
    assert b2 == NI.LookBodyOfRE(re, lid2);
    DirectEarlyNotInLateBody(re, lid1, lid2);
  }

  /** The STATIC quartet (a)/(D-ord)/(g_new)/(h): the hypotheses of R3's
      `FLookLoopFullCoversInLooks` that depend only on the look tables + nesting
      (not on the running register banks), at S := CaptureRegsSet(CapIdsInLooks
      (re)), Slook := LookIdSet(re). recon A: ALL FOUR are now DEPTH-GENERAL --
      (g) was replaced by the ordered (g_new) (`GNewFromTablesNested` via
      `DirectEarlyNotInLateBody`), so the `NR.NestDepth(re) <= 2` premise is GONE.
      Each forall dispatches to its per-row helper. */
/** (G5a-1 P5b) `LookRowsStaticNested` on the top-level fragment: the same proof, the premise widened and its callees
      on their `…Cdn` forms where the argument is the top regex or a non-look subterm of it. */
  lemma LookRowsStaticCdn(ast: R.regex, re: R.regex, crv: CP.FCompiled)
    requires crv == CP.FFullCompilation(ast)
    requires re == R.lazy_prefix(ast)
    requires LookBodiesPlusGateRE(re)   // (G3a) the weak gate (was LooksNoNulledPlusRE)
    requires T.TransWf(re)   // (G3a) for FrameEntryOkFromTables' plus table
    requires NR.NestedFragmentCdnRE(re)
    requires PIV.CapUnique(re) && PIV.QuantUnique(re) && LTB.LookUnique(re)
    requires LTB.LookTablesOk(re, crv) && LTB.LidsWellNested(re)
    ensures forall l: int, la: R.lookaround, body: R.regex ::                                  // (a)
              1 <= l <= R.max_lookaround(ast) && LTB.LookEntryOk(crv, l, la, body) ==>
                FrameEntryOk(crv, la, body, PIV.CaptureRegsSet(PIV.CapIdsInLooks(re)), LookIdSet(re))
    ensures forall l1: int, la1: R.lookaround, b1: R.regex, l2: int, la2: R.lookaround, b2: R.regex ::  // (D-ord)
              1 <= l1 <= R.max_lookaround(ast) && 1 <= l2 <= R.max_lookaround(ast) && l1 < l2
              && LTB.LookEntryOk(crv, l1, la1, b1) && LTB.LookEntryOk(crv, l2, la2, b2) ==>
                PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(b1)) * PIV.CaptureRegs(b2) == {}
    ensures forall l1: int, la1: R.lookaround, b1: R.regex, l2: int, la2: R.lookaround, b2: R.regex ::  // (g_new)
              1 <= l1 <= R.max_lookaround(ast) && 1 <= l2 <= R.max_lookaround(ast) && l1 < l2
              && LTB.LookEntryOk(crv, l1, la1, b1) && LTB.LookEntryOk(crv, l2, la2, b2) ==>
                DirectLookIds(b1) * LTB.LookIds(b2) == {}
    ensures forall l1: int, la1: R.lookaround, b1: R.regex, l2: int ::                          // (h)
              1 <= l1 <= R.max_lookaround(ast) && LTB.LookEntryOk(crv, l1, la1, b1) && 1 <= l2 <= l1 ==>
                l2 !in LookIdSet(b1)
  {
    forall l: int, la: R.lookaround, body: R.regex |
      1 <= l <= R.max_lookaround(ast) && LTB.LookEntryOk(crv, l, la, body)
      ensures FrameEntryOk(crv, la, body, PIV.CaptureRegsSet(PIV.CapIdsInLooks(re)), LookIdSet(re))
    { FrameEntryOkFromTablesCdn(ast, re, crv, l, la, body); }

    forall l1: int, la1: R.lookaround, b1: R.regex, l2: int, la2: R.lookaround, b2: R.regex |
      1 <= l1 <= R.max_lookaround(ast) && 1 <= l2 <= R.max_lookaround(ast) && l1 < l2
      && LTB.LookEntryOk(crv, l1, la1, b1) && LTB.LookEntryOk(crv, l2, la2, b2)
      ensures PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(b1)) * PIV.CaptureRegs(b2) == {}
    { DOrdFromTablesCdn(ast, re, crv, l1, la1, b1, l2, la2, b2); }

    forall l1: int, la1: R.lookaround, b1: R.regex, l2: int, la2: R.lookaround, b2: R.regex |
      1 <= l1 <= R.max_lookaround(ast) && 1 <= l2 <= R.max_lookaround(ast) && l1 < l2
      && LTB.LookEntryOk(crv, l1, la1, b1) && LTB.LookEntryOk(crv, l2, la2, b2)
      ensures DirectLookIds(b1) * LTB.LookIds(b2) == {}
    { GNewFromTablesNested(ast, re, crv, l1, la1, b1, l2, la2, b2); }

    forall l1: int, la1: R.lookaround, b1: R.regex, l2: int |
      1 <= l1 <= R.max_lookaround(ast) && LTB.LookEntryOk(crv, l1, la1, b1) && 1 <= l2 <= l1
      ensures l2 !in LookIdSet(b1)
    { HFromTables(ast, re, crv, l1, la1, b1, l2); }
  }

  /** (G5a-1 P5b) The narrow form, as a corollary of `LookRowsStaticCdn`. */
  lemma LookRowsStaticNested(ast: R.regex, re: R.regex, crv: CP.FCompiled)
    requires crv == CP.FFullCompilation(ast)
    requires re == R.lazy_prefix(ast)
    requires LookBodiesPlusGateRE(re)   // (G3a) the weak gate (was LooksNoNulledPlusRE)
    requires T.TransWf(re)   // (G3a) for FrameEntryOkFromTables' plus table
    requires NR.NestedFragmentRE(re)
    requires PIV.CapUnique(re) && PIV.QuantUnique(re) && LTB.LookUnique(re)
    requires LTB.LookTablesOk(re, crv) && LTB.LidsWellNested(re)
    ensures forall l: int, la: R.lookaround, body: R.regex ::                                  // (a)
              1 <= l <= R.max_lookaround(ast) && LTB.LookEntryOk(crv, l, la, body) ==>
                FrameEntryOk(crv, la, body, PIV.CaptureRegsSet(PIV.CapIdsInLooks(re)), LookIdSet(re))
    ensures forall l1: int, la1: R.lookaround, b1: R.regex, l2: int, la2: R.lookaround, b2: R.regex ::  // (D-ord)
              1 <= l1 <= R.max_lookaround(ast) && 1 <= l2 <= R.max_lookaround(ast) && l1 < l2
              && LTB.LookEntryOk(crv, l1, la1, b1) && LTB.LookEntryOk(crv, l2, la2, b2) ==>
                PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(b1)) * PIV.CaptureRegs(b2) == {}
    ensures forall l1: int, la1: R.lookaround, b1: R.regex, l2: int, la2: R.lookaround, b2: R.regex ::  // (g_new)
              1 <= l1 <= R.max_lookaround(ast) && 1 <= l2 <= R.max_lookaround(ast) && l1 < l2
              && LTB.LookEntryOk(crv, l1, la1, b1) && LTB.LookEntryOk(crv, l2, la2, b2) ==>
                DirectLookIds(b1) * LTB.LookIds(b2) == {}
    ensures forall l1: int, la1: R.lookaround, b1: R.regex, l2: int ::                          // (h)
              1 <= l1 <= R.max_lookaround(ast) && LTB.LookEntryOk(crv, l1, la1, b1) && 1 <= l2 <= l1 ==>
                l2 !in LookIdSet(b1)
  {
    NR.NarrowIsCdn(re);
    hide *;   // the wide premises are this lemma's own: match by name
    LookRowsStaticCdn(ast, re, crv);
  }

  /** The DYNAMIC trio (b)/(c')/(e) plus register well-formedness: the
      hypotheses that read the MAIN-MATCH result register banks. `cap`/`look`/
      `quant` are the INITIAL (fresh) banks; the winning thread's banks satisfy:
      (e) look cps <= |str| (`FFindMatchLookCpOk`); (b) every recorded lid has a
      table row (nested look-check classification + `LookIdEntryExists`); (c')
      the capture bank is INIT on every look body's capture regs (the main pass
      writes only OUTSIDE-look caps, `CaptureBytecodeClassifiedNestedOuter`,
      transported to `RegsAgreeInside` off each body's caps). */
  /** (§2.5b F-c) `LookRowsDynamicNested`'s (c') per row, in its own VC: the main
      pass writes only outside-look capture registers, so a look body's capture
      registers keep their init values. (Inline, the step timed out the lemma's last
      batch once the precondition was swapped to `LooksNoNulledPlusRE`.) */
  lemma LookRowCapsUntouched(ast: R.regex, re: R.regex, crv: CP.FCompiled, cp': AReg.Regs, cap: AReg.Regs,
                             ncap: int, l: int, la: R.lookaround, body: R.regex)
    requires crv == CP.FFullCompilation(ast)
    requires LTB.LookIds(re) == LTB.LookIds(ast)
    requires PIV.CapUnique(re) && LTB.LookTablesOk(re, crv)
    requires 1 <= l <= R.max_lookaround(ast) && LTB.LookEntryOk(crv, l, la, body)
    requires ncap >= 0 && cap == AReg.init_regs(ncap)
    requires |cp'.a_cp| == ncap && |cp'.a_clk| == ncap
    requires CM.RegsAgreeOutside(cp', cap, PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(re)))
    ensures CM.RegsAgreeInside(cp', AReg.init_regs(ncap), PIV.CaptureRegs(body))
  {
    var Sc := PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(re));
    LookEntryOnlyReal(ast, crv, l, la, body);
    var lid := l as nat;
    NI.LookBodyOfTablesTie(re, crv, lid);
    var la0: R.lookaround :| LTB.LookEntryOk(crv, lid as int, la0, NI.LookBodyOfRE(re, lid));
    assert body == NI.LookBodyOfRE(re, lid);
    NI.LookBodyCapsIn(re, lid);                    // CapIds(body) <= CapIdsInLooks(re)
    PIV.CapIdsLooksDisjoint(re);                   // outside(re) * inside(re) == {}
    assert PIV.CapIds(body) * PIV.CapIdsOutsideLooks(re) == {};
    PIV.CaptureRegsSetDisjoint(PIV.CapIds(body), PIV.CapIdsOutsideLooks(re));
    PIV.CaptureRegsIsSet(body);                    // CaptureRegs(body) == CaptureRegsSet(CapIds(body))
    // pure set algebra on the ground equalities: with the comprehensions visible the
    // solver expands them and never closes (the one 60 s+ obligation in isolation)
    assert forall k: int :: k in PIV.CaptureRegs(body) ==> k !in Sc by {
      var Sb := PIV.CaptureRegsSet(PIV.CapIds(body));
      assert PIV.CaptureRegs(body) == Sb && Sb * Sc == {};
      hide *;
      forall k: int | k in PIV.CaptureRegs(body) ensures k !in Sc {
        assert k in Sb;
        if k in Sc { assert k in Sb * Sc; }
      }
    }
    RegsAgreeOutsideToInside(cp', cap, PIV.CaptureRegs(body), Sc);
  }

/** (G5a-1 P5b) `LookRowsDynamicNested` on the top-level fragment: the same proof, the premise widened and its callees
      on their `…Cdn` forms where the argument is the top regex or a non-look subterm of it. */
  lemma LookRowsDynamicCdn(
    ast: R.regex, re: R.regex, crv: CP.FCompiled, code: RB.code, str: string,
    ov: LOr.OracleView, cdn: LCdn.cdns, inits: AI.VmState,
    cap: AReg.Regs, look: AReg.Regs, quant: AReg.Regs,
    ncap: int, nlook: int, nquant: int, endl: nat, result: Option<AI.Thread>)
    requires crv == CP.FFullCompilation(ast)
    requires re == R.lazy_prefix(ast)
    requires LookBodiesPlusGateRE(re)   // (G3a) the weak gate (was LooksNoNulledPlusRE)
    requires T.TransWf(re)   // (G3a) for FrameEntryOkFromTables' plus table
    requires code == CP.compile_to_bytecode(re)
    requires NR.NestedFragmentCdnRE(re) && PIV.CapUnique(re) && PIV.QuantUnique(re) && LTB.LookUnique(re)
    requires LTB.LookTablesOk(re, crv)
    requires NR.NfaRepRE(re, code, 0, endl) && |code| == endl + 1
    requires NR.GetPcRE(code, endl) == Some(RB.Accept)
    requires ncap >= 0 && nlook >= 0 && nquant >= 0
    requires cap == AReg.init_regs(ncap) && look == AReg.init_regs(nlook) && quant == AReg.init_regs(nquant)
    requires |inits.processed.true_set| == RB.size(code) && |inits.processed.false_set| == RB.size(code)
    requires inits.context.nextchar == AI.get_char(str, inits.cp)
    requires 0 <= inits.cp <= |str| && inits.clock >= 0
    requires inits.active == [AI.init_thread(cap, look, quant)]
    requires inits.blocked == [] && inits.bestmatch.None?
    requires result == AI.FFindMatch(code, str, inits, ov, LAnc.Forward, cdn).0
    ensures result.Some? ==> CM.ThreadRegsWf(result.value, ncap, nlook, nquant)                   // reg wf
    ensures result.Some? ==> CM.LookCpsLE(result.value.look_regs, |str|)                           // (e)
    ensures result.Some? ==>
              forall l: int :: 1 <= l <= R.max_lookaround(ast) && AReg.get_cp(result.value.look_regs, l).Some? ==>  // (b)
                                 exists la: R.lookaround, body: R.regex :: LTB.LookEntryOk(crv, l, la, body)
    ensures result.Some? ==>
              forall l: int, la: R.lookaround, body: R.regex ::                                            // (c')
                1 <= l <= R.max_lookaround(ast) && LTB.LookEntryOk(crv, l, la, body) ==>
                  CM.RegsAgreeInside(result.value.capture_regs, AReg.init_regs(ncap), PIV.CaptureRegs(body))
  {
    hide LookBodiesPlusGateRE;   // (G3a) unused here, like its predecessor: in context it blew (c') to 560 M / 900 s
    var pre := R.Re_quant(R.NonNullable, 0, R.CountedQuant(0, None, false),
                          R.Re_character(R.Dot));
    assert re == R.Re_con(pre, ast);
    assert LTB.LookIds(re) == LTB.LookIds(ast);

    // reg wf of the winning thread
    assert CM.VmRegsWf(inits, ncap, nlook, nquant) by {
      assert AI.init_thread(cap, look, quant) in inits.active;
      assert PIV.CapRegWf(cap);                      // init_regs
    }
    FFindMatchRegsWf(code, str, inits, ov, LAnc.Forward, cdn, ncap, nlook, nquant);

    // (e): look cps <= |str|
    assert CM.VmLookCpOk(inits, |str|) by {
      assert CM.LookCpsLE(look, |str|) by {
        forall l: int ensures AI.get_idx(look.a_cp, l) <= |str| {
          if 0 <= l < |look.a_cp| { assert look.a_cp[l] == -1; }
        }
      }
      assert AI.init_thread(cap, look, quant).look_regs == look;
    }
    CM.FFindMatchLookCpOk(code, str, inits, ov, LAnc.Forward, cdn);

    // look-frame: recorded lids sit in LookIdSet(re)
    var Slk := LookIdSet(re);
    LookBytecodeClassifiedCdn(re);                 // LookChecksInside(code, Slk)
    assert CM.VmLooksAgree(inits, look, Slk) by {
      assert CM.RegsAgreeOutside(look, look, Slk);
    }
    CM.FFindMatchLookFrame(code, str, inits, ov, LAnc.Forward, cdn, look, Slk);

    // capture-frame: main pass writes only OUTSIDE-look caps
    var Sc := PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(re));
    CaptureBytecodeClassifiedCdnOuter(re);         // CaptureWritesInside(code, Sc)
    assert CM.VmCapturesAgree(inits, cap, Sc) by {
      assert AI.init_thread(cap, look, quant).capture_regs == cap;
      assert CM.RegsAgreeOutside(cap, cap, Sc);
    }
    CM.FFindMatchCapWriteFrame(code, str, inits, ov, LAnc.Forward, cdn, cap, Sc);

    assert {:split_here} true;   // (E3) section boundary: its own assertion batch
    if result.Some? {
      var lk := result.value.look_regs;
      var cp' := result.value.capture_regs;
      assert CM.ThreadRegsWf(result.value, ncap, nlook, nquant);
      assert CM.RegsAgreeOutside(lk, look, Slk);
      assert CM.RegsAgreeOutside(cp', cap, Sc);

      // (b)
      assert {:split_here} true;   // (E3) section boundary: its own assertion batch
      forall l: int | 1 <= l <= R.max_lookaround(ast) && AReg.get_cp(lk, l).Some?
        ensures exists la: R.lookaround, body: R.regex :: LTB.LookEntryOk(crv, l, la, body)
      {
        assert l in Slk by {
          if l !in Slk {
            assert AI.get_idx(lk.a_cp, l) == AI.get_idx(look.a_cp, l);   // RegsAgreeOutside
            assert AReg.get_cp(look, l).None?;                          // init: a_cp[l] == -1
            assert AReg.get_cp(lk, l).None?;                            // contradiction
          }
        }
        assert (l as nat) in LTB.LookIds(re);
        LookIdEntryExists(re, crv, l as nat);
      }

      // (c')
      assert {:split_here} true;   // (E3) section boundary: its own assertion batch
      forall l: int, la: R.lookaround, body: R.regex |
        1 <= l <= R.max_lookaround(ast) && LTB.LookEntryOk(crv, l, la, body)
        ensures CM.RegsAgreeInside(cp', AReg.init_regs(ncap), PIV.CaptureRegs(body))
      {
        LookRowCapsUntouched(ast, re, crv, cp', cap, ncap, l, la, body);
      }
    }
  }

  /** (G5a-1 P5b) The narrow form, as a corollary of `LookRowsDynamicCdn`. */
  lemma LookRowsDynamicNested(
    ast: R.regex, re: R.regex, crv: CP.FCompiled, code: RB.code, str: string,
    ov: LOr.OracleView, cdn: LCdn.cdns, inits: AI.VmState,
    cap: AReg.Regs, look: AReg.Regs, quant: AReg.Regs,
    ncap: int, nlook: int, nquant: int, endl: nat, result: Option<AI.Thread>)
    requires crv == CP.FFullCompilation(ast)
    requires re == R.lazy_prefix(ast)
    requires LookBodiesPlusGateRE(re)   // (G3a) the weak gate (was LooksNoNulledPlusRE)
    requires T.TransWf(re)   // (G3a) for FrameEntryOkFromTables' plus table
    requires code == CP.compile_to_bytecode(re)
    requires NR.NestedFragmentRE(re) && PIV.CapUnique(re) && PIV.QuantUnique(re) && LTB.LookUnique(re)
    requires LTB.LookTablesOk(re, crv)
    requires NR.NfaRepRE(re, code, 0, endl) && |code| == endl + 1
    requires NR.GetPcRE(code, endl) == Some(RB.Accept)
    requires ncap >= 0 && nlook >= 0 && nquant >= 0
    requires cap == AReg.init_regs(ncap) && look == AReg.init_regs(nlook) && quant == AReg.init_regs(nquant)
    requires |inits.processed.true_set| == RB.size(code) && |inits.processed.false_set| == RB.size(code)
    requires inits.context.nextchar == AI.get_char(str, inits.cp)
    requires 0 <= inits.cp <= |str| && inits.clock >= 0
    requires inits.active == [AI.init_thread(cap, look, quant)]
    requires inits.blocked == [] && inits.bestmatch.None?
    requires result == AI.FFindMatch(code, str, inits, ov, LAnc.Forward, cdn).0
    ensures result.Some? ==> CM.ThreadRegsWf(result.value, ncap, nlook, nquant)                   // reg wf
    ensures result.Some? ==> CM.LookCpsLE(result.value.look_regs, |str|)                           // (e)
    ensures result.Some? ==>
              forall l: int :: 1 <= l <= R.max_lookaround(ast) && AReg.get_cp(result.value.look_regs, l).Some? ==>  // (b)
                                 exists la: R.lookaround, body: R.regex :: LTB.LookEntryOk(crv, l, la, body)
    ensures result.Some? ==>
              forall l: int, la: R.lookaround, body: R.regex ::                                            // (c')
                1 <= l <= R.max_lookaround(ast) && LTB.LookEntryOk(crv, l, la, body) ==>
                  CM.RegsAgreeInside(result.value.capture_regs, AReg.init_regs(ncap), PIV.CaptureRegs(body))
  {
    NR.NarrowIsCdn(re);
    hide *;   // the wide premises are this lemma's own: match by name
    LookRowsDynamicCdn(ast, re, crv, code, str, ov, cdn, inits, cap, look, quant, ncap, nlook, nquant, endl, result);
  }

  /** The DIRECT (top-level) lookaround ids of `re`: a lookaround node
      contributes its own lid but NOT the lids inside its body (the body is a
      single CheckOracle leaf in the main code — its inner looks live only in
      the look tables). This is exactly the set the MAIN bytecode gates on. */
  ghost function DirectLookIds(re: R.regex): set<nat>
    decreases re
  {
    match re
    case Re_empty => {}
    case Re_character(_) => {}
    case Re_anchor(_) => {}
    case Re_alt(r1, r2) => DirectLookIds(r1) + DirectLookIds(r2)
    case Re_con(r1, r2) => DirectLookIds(r1) + DirectLookIds(r2)
    case Re_quant(_, _, _, r1) => DirectLookIds(r1)
    case Re_capture(_, r1) => DirectLookIds(r1)
    case Re_lookaround(lid, _, r1) => if lid >= 0 then {lid as nat} else {}
  }

  ghost function DirectLidSet(re: R.regex): set<int> {
    set l: nat | l in DirectLookIds(re) :: l as int
  }

  /** DIRECT-lid twin of `LookCheckIdsREGen`: every `CheckOracle`/`NegCheckOracle`
      in the main block of `re` targets a DIRECT (top-level) lid. Verbatim clone
      of `LookCheckIdsREGen` with `LookIds` replaced by `DirectLookIds` — the
      recursion never descends into a lookaround body (that leaf is a single
      gate), so the tighter set holds. */
  lemma LookCheckDirectREGen(re: R.regex, code: RB.code, start: nat, endl: nat, pc: nat)
    requires LTB.LookUnique(re)
    requires NR.NfaRepRE(re, code, start, endl)
    requires start <= pc < endl
    ensures NR.GetPcRE(code, pc).Some? && NR.GetPcRE(code, pc).value.CheckOracle? ==>
              var l := NR.GetPcRE(code, pc).value.col;
              l >= 0 && (l as nat) in DirectLookIds(re)
    ensures NR.GetPcRE(code, pc).Some? && NR.GetPcRE(code, pc).value.NegCheckOracle? ==>
              var l := NR.GetPcRE(code, pc).value.ncl;
              l >= 0 && (l as nat) in DirectLookIds(re)
    decreases CP.rsize(re), 1
  {
    match re
    case Re_empty =>
      assert {:split_here} true;   // (2026-11-05) per-arm: 9.4 GB as one batch
    case Re_character(_) =>
      assert {:split_here} true;   // (2026-11-05) per-arm: 9.4 GB as one batch
    case Re_anchor(_) =>
      assert {:split_here} true;   // (2026-11-05) per-arm: 9.4 GB as one batch
    case Re_lookaround(lid, la, r1) =>
      assert {:split_here} true;   // (2026-11-05) per-arm: 9.4 GB as one batch
      assert pc == start;
      assert lid >= 0;
      assert (lid as nat) in DirectLookIds(re);
    case Re_alt(r1, r2) =>
      assert {:split_here} true;   // (2026-11-05) per-arm: 9.4 GB as one batch
      var e1: nat :| NR.GetPcRE(code, start) == Some(RB.Fork(start + 1, e1 + 1))
                     && NR.NfaRepRE(r1, code, start + 1, e1)
                     && NR.GetPcRE(code, e1) == Some(RB.Jmp(endl))
                     && NR.NfaRepRE(r2, code, e1 + 1, endl);
      NR.NfaRepIncrRE(r1, code, start + 1, e1);
      NR.NfaRepIncrRE(r2, code, e1 + 1, endl);
      if pc == start {
      } else if pc < e1 {
        LookCheckDirectREGen(r1, code, start + 1, e1, pc);
      } else if pc == e1 {
      } else {
        LookCheckDirectREGen(r2, code, e1 + 1, endl, pc);
      }
    case Re_con(r1, r2) =>
      assert {:split_here} true;   // (2026-11-05) per-arm: 9.4 GB as one batch
      var e1: nat :| NR.NfaRepRE(r1, code, start, e1) && NR.NfaRepRE(r2, code, e1, endl);
      NR.NfaRepIncrRE(r1, code, start, e1);
      NR.NfaRepIncrRE(r2, code, e1, endl);
      if pc < e1 {
        LookCheckDirectREGen(r1, code, start, e1, pc);
      } else {
        LookCheckDirectREGen(r2, code, e1, endl, pc);
      }
    case Re_capture(cid, r1) =>
      assert {:split_here} true;   // (2026-11-05) per-arm: 9.4 GB as one batch
      var e1: nat :| NR.GetPcRE(code, start) == Some(RB.SetRegisterToCP(CP.start_reg(cid)))
                     && NR.NfaRepRE(r1, code, start + 1, e1)
                     && NR.GetPcRE(code, e1) == Some(RB.SetRegisterToCP(CP.end_reg(cid)))
                     && endl == e1 + 1;
      NR.NfaRepIncrRE(r1, code, start + 1, e1);
      if pc == start {
      } else if pc < e1 {
        LookCheckDirectREGen(r1, code, start + 1, e1, pc);
      } else {
      }
    case Re_quant(nul, qid, q, r1) =>
      assert {:split_here} true;   // (2026-11-05) per-arm: 9.4 GB as one batch
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
          LookCheckDirectREGen(r1, code, start + 3, e1, pc);
        } else {
        }
      } else if q.max.Some? {
        var em := NR.NfaRepREQuantInv(nul, qid, q, r1, code, start, endl);
        NR.NfaRepIncrMinRE(q.min as nat, qid, r1, code, start, em);
        NR.NfaRepIncrOptRE((q.max.value - q.min) as nat, q.greedy, qid, r1, code, em, endl);
        if pc < em {
          LookCheckDirectMinREGen(q.min as nat, qid, r1, code, start, em, pc);
        } else {
          LookCheckDirectOptREGen((q.max.value - q.min) as nat, q.greedy, qid, r1, code, em, endl, pc);
        }
      } else if nul != R.NonNullable && !q.greedy {
        // §2.5a GENERIC: min forced copies then the star loop; the loop's own
        // five instructions (Fork/SetQuantToClock/BeginLoop at em..em+2,
        // EndLoop/Jmp at e1..e1+1) are all of the harmless kind
        var em, e1 := NR.NfaRepREGenInv(nul, qid, q, r1, code, start, endl);
        NR.NfaRepIncrMinRE(q.min as nat, qid, r1, code, start, em);
        NR.NfaRepIncrRE(r1, code, em + 3, e1);
        if pc < em {
          LookCheckDirectMinREGen(q.min as nat, qid, r1, code, start, em, pc);
        } else if pc <= em + 2 {
        } else if pc < e1 {
          LookCheckDirectREGen(r1, code, em + 3, e1, pc);
        } else {
        }
      } else if nul == R.CINullable {
        // §2.5b CIN-GREEDY: min-1 forced copies, then the stamped end-fork
        // loop; its six own instructions are all of the harmless kind
        var em, e1 := NR.NfaRepRECinInv(nul, qid, q, r1, code, start, endl);
        NR.NfaRepIncrMinRE((q.min - 1) as nat, qid, r1, code, start, em);
        NR.NfaRepIncrRE(r1, code, em + 3, e1);
        if pc < em {
          LookCheckDirectMinREGen((q.min - 1) as nat, qid, r1, code, start, em, pc);
        } else if pc <= em + 2 {
        } else if pc < e1 {
          LookCheckDirectREGen(r1, code, em + 3, e1, pc);
        } else {
        }
      } else if nul == R.CDNullable {
        // §2.5b CDN-GREEDY (G5a): min-1 forced copies, then the stamped end-fork
        // loop; its six own instructions are all of the harmless kind
        var em, e1 := NR.NfaRepRECdnInv(nul, qid, q, r1, code, start, endl);
        NR.NfaRepIncrMinRE((q.min - 1) as nat, qid, r1, code, start, em);
        NR.NfaRepIncrRE(r1, code, em + 3, e1);
        if pc < em {
          LookCheckDirectMinREGen((q.min - 1) as nat, qid, r1, code, start, em, pc);
        } else if pc <= em + 2 {
        } else if pc < e1 {
          LookCheckDirectREGen(r1, code, em + 3, e1, pc);
        } else {
        }
      } else {
        var em, e1 := NR.NfaRepREPlusInv(nul, qid, q, r1, code, start, endl);
        NR.NfaRepIncrMinRE((q.min - 1) as nat, qid, r1, code, start, em);
        NR.NfaRepIncrRE(r1, code, em + 1, e1);
        if pc < em {
          LookCheckDirectMinREGen((q.min - 1) as nat, qid, r1, code, start, em, pc);
        } else if pc == em {
        } else if pc < e1 {
          LookCheckDirectREGen(r1, code, em + 1, e1, pc);
        } else {
        }
      }
  }

  lemma LookCheckDirectMinREGen(k: nat, qid: R.quantid, r1: R.regex, code: RB.code, start: nat, endl: nat, pc: nat)
    requires LTB.LookUnique(r1)
    requires NR.NfaRepMinRE(k, qid, r1, code, start, endl)
    requires start <= pc < endl
    ensures NR.GetPcRE(code, pc).Some? && NR.GetPcRE(code, pc).value.CheckOracle? ==>
              var l := NR.GetPcRE(code, pc).value.col;
              l >= 0 && (l as nat) in DirectLookIds(r1)
    ensures NR.GetPcRE(code, pc).Some? && NR.GetPcRE(code, pc).value.NegCheckOracle? ==>
              var l := NR.GetPcRE(code, pc).value.ncl;
              l >= 0 && (l as nat) in DirectLookIds(r1)
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
      LookCheckDirectREGen(r1, code, start + 1, e1, pc);
    } else {
      LookCheckDirectMinREGen(k - 1, qid, r1, code, e1, endl, pc);
    }
  }

  lemma LookCheckDirectOptREGen(k: nat, greedy: bool, qid: R.quantid, r1: R.regex, code: RB.code, start: nat, endl: nat, pc: nat)
    requires LTB.LookUnique(r1)
    requires NR.NfaRepOptRE(k, greedy, qid, r1, code, start, endl)
    requires start <= pc < endl
    ensures NR.GetPcRE(code, pc).Some? && NR.GetPcRE(code, pc).value.CheckOracle? ==>
              var l := NR.GetPcRE(code, pc).value.col;
              l >= 0 && (l as nat) in DirectLookIds(r1)
    ensures NR.GetPcRE(code, pc).Some? && NR.GetPcRE(code, pc).value.NegCheckOracle? ==>
              var l := NR.GetPcRE(code, pc).value.ncl;
              l >= 0 && (l as nat) in DirectLookIds(r1)
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
      LookCheckDirectREGen(r1, code, start + 3, e1, pc);
    } else if pc == e1 {
    } else {
      LookCheckDirectOptREGen(k - 1, greedy, qid, r1, code, e1 + 1, endl, pc);
    }
  }

  /** `LookChecksInside(compile_to_bytecode(re), DirectLidSet(re))`: the main
      bytecode gates only on DIRECT lids. Nested-body twin of the (b) look
      classification but with the TIGHTER direct set — the (f) backbone. */
/** (G5a-1 P5b) `DirectLidClassified` on the top-level fragment: the same proof, the premise widened and its callees
      on their `…Cdn` forms where the argument is the top regex or a non-look subterm of it. */
  lemma DirectLidClassifiedCdn(re: R.regex)
    requires NR.NestedFragmentCdnRE(re) && LTB.LookUnique(re)
    ensures CM.LookChecksInside(CP.compile_to_bytecode(re), DirectLidSet(re))
  {
    var code := CP.compile_to_bytecode(re);
    var next := CP.compile(re, 0, CP.Progress).1;
    NR.CompileToBytecodeRepCdn(re);
    var endl := next as nat;
    var S := DirectLidSet(re);
    forall pc: nat | pc < |code|
      ensures (code[pc].CheckOracle? ==> code[pc].col in S)
              && (code[pc].NegCheckOracle? ==> code[pc].ncl in S)
    {
      assert NR.GetPcRE(code, pc) == Some(code[pc]);
      if pc < endl {
        LookCheckDirectREGen(re, code, 0, endl, pc);
      } else {
        assert pc == endl;
        assert NR.GetPcRE(code, endl) == Some(RB.Accept);
      }
    }
  }

  /** (G5a-1 P5b) The narrow form, as a corollary of `DirectLidClassifiedCdn`. */
  lemma DirectLidClassified(re: R.regex)
    requires NR.NestedFragmentRE(re) && LTB.LookUnique(re)
    ensures CM.LookChecksInside(CP.compile_to_bytecode(re), DirectLidSet(re))
  {
    NR.NarrowIsCdn(re);
    hide *;   // the wide premises are this lemma's own: match by name
    DirectLidClassifiedCdn(re);
  }

  /** (G5b-3) plus-at's copy of the direct lids is this one. */
  lemma DirectLidSetBridge(re: R.regex)
    ensures DirectLookIds(re) == SBk.DirectLooksRN(re)
    ensures DirectLidSet(re) == SBk.DirectLidSetRN(re)
    decreases re
  {
    match re
    case Re_alt(r1, r2) => DirectLidSetBridge(r1); DirectLidSetBridge(r2);
    case Re_con(r1, r2) => DirectLidSetBridge(r1); DirectLidSetBridge(r2);
    case Re_quant(_, _, _, r1) => DirectLidSetBridge(r1);
    case Re_capture(_, r1) => DirectLidSetBridge(r1);
    case _ =>
  }

  /** Direct lids are among all lids. */
  lemma DirectLidsSubLookIds(re: R.regex)
    ensures DirectLookIds(re) <= LTB.LookIds(re)
    decreases re
  {
    match re
    case Re_alt(r1, r2) => DirectLidsSubLookIds(r1); DirectLidsSubLookIds(r2);
    case Re_con(r1, r2) => DirectLidsSubLookIds(r1); DirectLidsSubLookIds(r2);
    case Re_quant(_, _, _, r1) => DirectLidsSubLookIds(r1);
    case Re_capture(_, r1) => DirectLidsSubLookIds(r1);
    case Re_lookaround(lid, _, r1) =>
    case _ =>
  }

  /** No DIRECT (top-level) lid lands inside any look body: a lid inside `l1`'s
      body is nested under `l1`'s lookaround, hence not top-level. Uniqueness
      keeps a lid from being BOTH. The (f) disjointness. */
  lemma DirectLidsNotInBody(re: R.regex, l1: nat)
    requires LTB.LookUnique(re)
    requires l1 in LTB.LookIds(re)
    ensures DirectLookIds(re) * LTB.LookIds(NI.LookBodyOfRE(re, l1)) == {}
    decreases re
  {
    match re
    case Re_alt(r1, r2) =>
      if l1 in LTB.LookIds(r1) {
        DirectLidsNotInBody(r1, l1);
        LookBodyLidsSubset(r1, l1);                // LookIds(body) <= LookIds(r1)
        DirectLidsSubLookIds(r2);                  // DirectLookIds(r2) <= LookIds(r2)
      } else {
        DirectLidsNotInBody(r2, l1);
        LookBodyLidsSubset(r2, l1);
        DirectLidsSubLookIds(r1);
      }
    case Re_con(r1, r2) =>
      if l1 in LTB.LookIds(r1) {
        DirectLidsNotInBody(r1, l1);
        LookBodyLidsSubset(r1, l1);
        DirectLidsSubLookIds(r2);
      } else {
        DirectLidsNotInBody(r2, l1);
        LookBodyLidsSubset(r2, l1);
        DirectLidsSubLookIds(r1);
      }
    case Re_quant(_, _, _, r1) => DirectLidsNotInBody(r1, l1);
    case Re_capture(_, r1) => DirectLidsNotInBody(r1, l1);
    case Re_lookaround(lid0, _, r1) =>
      if lid0 >= 0 && (lid0 as nat) == l1 {
        assert NI.LookBodyOfRE(re, l1) == r1;
        // DirectLookIds(re) == {lid0}; lid0 !in LookIds(r1) by LookUnique
      } else {
        assert l1 in LTB.LookIds(r1);
        assert NI.LookBodyOfRE(re, l1) == NI.LookBodyOfRE(r1, l1);
        LookBodyLidsSubset(r1, l1);                // LookIds(body) <= LookIds(r1); lid0 !in LookIds(r1)
      }
  }

  /** recon A: the STRUCTURAL core of the replacement hypothesis (g_new). For two
      distinct rows ordered `l1 < l2`, the DIRECT (top-level) look ids of the
      EARLIER row's body never land inside the LATER row's body. Depth-general
      (no `NestDepth` cap): a direct child of `l1`'s body has `l1` as its parent;
      were it inside `l2`'s body it would be nested under `l2`, forcing `l2` to be
      an ancestor of a child of `l1`, i.e. `l2 <= l1` -- contradicting `l1 < l2`.
      The `l2 IS this node` case is impossible by well-nesting (`l1 in LookIds(r1)`
      forces `l1 > lid0 == l2`); the `l1 IS this node` case reduces to
      `DirectLidsNotInBody`; siblings are disjoint by `LookUnique`. Mirrors
      `GDisjointBodies`/`DirectLidsNotInBody` structure. */
  lemma DirectEarlyNotInLateBody(r: R.regex, l1: nat, l2: nat)
    requires LTB.LookUnique(r) && LTB.LidsWellNested(r)
    requires l1 in LTB.LookIds(r) && l2 in LTB.LookIds(r) && l1 < l2
    ensures DirectLookIds(NI.LookBodyOfRE(r, l1)) * LTB.LookIds(NI.LookBodyOfRE(r, l2)) == {}
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      if l1 in LTB.LookIds(r1) && l2 in LTB.LookIds(r1) {
        DirectEarlyNotInLateBody(r1, l1, l2);
      } else if l1 !in LTB.LookIds(r1) && l2 !in LTB.LookIds(r1) {
        DirectEarlyNotInLateBody(r2, l1, l2);
      } else {
        if l1 in LTB.LookIds(r1) {
          LookBodyLidsSubset(r1, l1); LookBodyLidsSubset(r2, l2);
          DirectLidsSubLookIds(NI.LookBodyOfRE(r1, l1));
        } else {
          LookBodyLidsSubset(r2, l1); LookBodyLidsSubset(r1, l2);
          DirectLidsSubLookIds(NI.LookBodyOfRE(r2, l1));
        }
      }
    case Re_con(r1, r2) =>
      if l1 in LTB.LookIds(r1) && l2 in LTB.LookIds(r1) {
        DirectEarlyNotInLateBody(r1, l1, l2);
      } else if l1 !in LTB.LookIds(r1) && l2 !in LTB.LookIds(r1) {
        DirectEarlyNotInLateBody(r2, l1, l2);
      } else {
        if l1 in LTB.LookIds(r1) {
          LookBodyLidsSubset(r1, l1); LookBodyLidsSubset(r2, l2);
          DirectLidsSubLookIds(NI.LookBodyOfRE(r1, l1));
        } else {
          LookBodyLidsSubset(r2, l1); LookBodyLidsSubset(r1, l2);
          DirectLidsSubLookIds(NI.LookBodyOfRE(r2, l1));
        }
      }
    case Re_quant(_, _, _, r1) => DirectEarlyNotInLateBody(r1, l1, l2);
    case Re_capture(_, r1) => DirectEarlyNotInLateBody(r1, l1, l2);
    case Re_lookaround(lid0, _, r1) =>
      if lid0 >= 0 && (lid0 as nat) == l1 {
        // l1 IS this node: body(l1) == r1; l2 (!= l1) nested in r1
        assert NI.LookBodyOfRE(r, l1) == r1;
        assert l2 in LTB.LookIds(r1);
        assert NI.LookBodyOfRE(r, l2) == NI.LookBodyOfRE(r1, l2);
        DirectLidsNotInBody(r1, l2);   // DirectLookIds(r1) * LookIds(LookBodyOfRE(r1,l2)) == {}
      } else if lid0 >= 0 && (lid0 as nat) == l2 {
        // l2 IS this node: l1 nested in r1 => l1 > lid0 == l2 (well-nesting), contradicting l1 < l2
        assert l1 in LTB.LookIds(r1);
        assert lid0 as nat < l1;       // LidsWellNested at this node
        assert false;
      } else {
        assert l1 in LTB.LookIds(r1) && l2 in LTB.LookIds(r1);
        assert NI.LookBodyOfRE(r, l1) == NI.LookBodyOfRE(r1, l1);
        assert NI.LookBodyOfRE(r, l2) == NI.LookBodyOfRE(r1, l2);
        DirectEarlyNotInLateBody(r1, l1, l2);
      }
  }

  /** (f) look-stability from the MAIN match: every recorded lid `l2` is DIRECT
      (the main bytecode gates only on direct lids, `DirectLidClassified` +
      look-frame), and no direct lid lands inside another look's body
      (`DirectLidsNotInBody`), so `l2 !in LookIdSet(b1)`. */
/** (G5a-1 P5b) `FStabilityNested` on the top-level fragment: the same proof, the premise widened and its callees
      on their `…Cdn` forms where the argument is the top regex or a non-look subterm of it. */
  lemma FStabilityCdn(
    ast: R.regex, re: R.regex, crv: CP.FCompiled, code: RB.code, str: string,
    ov: LOr.OracleView, cdn: LCdn.cdns, inits: AI.VmState,
    cap: AReg.Regs, look: AReg.Regs, quant: AReg.Regs, nlook: int, result: Option<AI.Thread>)
    requires crv == CP.FFullCompilation(ast)
    requires re == R.lazy_prefix(ast)
    requires LookBodiesPlusGateRE(re)   // (G3a) the weak gate (was LooksNoNulledPlusRE)
    requires T.TransWf(re)   // (G3a) for FrameEntryOkFromTables' plus table
    requires code == CP.compile_to_bytecode(re)
    requires NR.NestedFragmentCdnRE(re) && LTB.LookUnique(re) && LTB.LookTablesOk(re, crv)
    requires look == AReg.init_regs(nlook)
    requires |inits.processed.true_set| == RB.size(code) && |inits.processed.false_set| == RB.size(code)
    requires inits.context.nextchar == AI.get_char(str, inits.cp)
    requires inits.active == [AI.init_thread(cap, look, quant)]
    requires inits.blocked == [] && inits.bestmatch.None?
    requires result == AI.FFindMatch(code, str, inits, ov, LAnc.Forward, cdn).0
    ensures result.Some? ==>
              forall l1: int, la1: R.lookaround, b1: R.regex, l2: int ::
                (1 <= l1 <= R.max_lookaround(ast) && LTB.LookEntryOk(crv, l1, la1, b1)
                && 1 <= l2 <= R.max_lookaround(ast) && l2 != l1
                && AReg.get_cp(result.value.look_regs, l2).Some?) ==> l2 !in LookIdSet(b1)
  {
    var Sd := DirectLidSet(re);
    DirectLidClassifiedCdn(re);                            // LookChecksInside(code, Sd)
    assert CM.VmLooksAgree(inits, look, Sd) by {
      assert CM.RegsAgreeOutside(look, look, Sd);
    }
    CM.FFindMatchLookFrame(code, str, inits, ov, LAnc.Forward, cdn, look, Sd);
    if result.Some? {
      var lk := result.value.look_regs;
      assert CM.RegsAgreeOutside(lk, look, Sd);
      forall l1: int, la1: R.lookaround, b1: R.regex, l2: int |
        1 <= l1 <= R.max_lookaround(ast) && LTB.LookEntryOk(crv, l1, la1, b1)
        && 1 <= l2 <= R.max_lookaround(ast) && l2 != l1
        && AReg.get_cp(lk, l2).Some?
        ensures l2 !in LookIdSet(b1)
      {
        // l2 recorded => l2 is a direct lid
        assert l2 in Sd by {
          if l2 !in Sd {
            assert AI.get_idx(lk.a_cp, l2) == AI.get_idx(look.a_cp, l2);   // RegsAgreeOutside
            assert AReg.get_cp(look, l2).None?;                           // init: -1
            assert AReg.get_cp(lk, l2).None?;                             // contradiction
          }
        }
        assert (l2 as nat) in DirectLookIds(re);
        // b1 == LookBodyOfRE(re, l1)
        LookEntryOnlyReal(ast, crv, l1, la1, b1);
        var lid1 := l1 as nat;
        NI.LookBodyOfTablesTie(re, crv, lid1);
        var la0: R.lookaround :| LTB.LookEntryOk(crv, lid1 as int, la0, NI.LookBodyOfRE(re, lid1));
        assert b1 == NI.LookBodyOfRE(re, lid1);
        DirectLidsNotInBody(re, lid1);                  // DirectLookIds(re) * LookIds(b1) == {}
        if l2 in LookIdSet(b1) {
          var x: nat :| x in LTB.LookIds(b1) && (x as int) == l2;
          assert x == (l2 as nat);
          assert x in DirectLookIds(re) * LTB.LookIds(b1);   // false
        }
      }
    }
  }

  /** (G5a-1 P5b) The narrow form, as a corollary of `FStabilityCdn`. */
  lemma FStabilityNested(
    ast: R.regex, re: R.regex, crv: CP.FCompiled, code: RB.code, str: string,
    ov: LOr.OracleView, cdn: LCdn.cdns, inits: AI.VmState,
    cap: AReg.Regs, look: AReg.Regs, quant: AReg.Regs, nlook: int, result: Option<AI.Thread>)
    requires crv == CP.FFullCompilation(ast)
    requires re == R.lazy_prefix(ast)
    requires LookBodiesPlusGateRE(re)   // (G3a) the weak gate (was LooksNoNulledPlusRE)
    requires T.TransWf(re)   // (G3a) for FrameEntryOkFromTables' plus table
    requires code == CP.compile_to_bytecode(re)
    requires NR.NestedFragmentRE(re) && LTB.LookUnique(re) && LTB.LookTablesOk(re, crv)
    requires look == AReg.init_regs(nlook)
    requires |inits.processed.true_set| == RB.size(code) && |inits.processed.false_set| == RB.size(code)
    requires inits.context.nextchar == AI.get_char(str, inits.cp)
    requires inits.active == [AI.init_thread(cap, look, quant)]
    requires inits.blocked == [] && inits.bestmatch.None?
    requires result == AI.FFindMatch(code, str, inits, ov, LAnc.Forward, cdn).0
    ensures result.Some? ==>
              forall l1: int, la1: R.lookaround, b1: R.regex, l2: int ::
                (1 <= l1 <= R.max_lookaround(ast) && LTB.LookEntryOk(crv, l1, la1, b1)
                && 1 <= l2 <= R.max_lookaround(ast) && l2 != l1
                && AReg.get_cp(result.value.look_regs, l2).Some?) ==> l2 !in LookIdSet(b1)
  {
    NR.NarrowIsCdn(re);
    hide *;   // the wide premises are this lemma's own: match by name
    FStabilityCdn(ast, re, crv, code, str, ov, cdn, inits, cap, look, quant, nlook, result);
  }

  /** DELIVERABLE #3: the nested analogue of `LookRowsFromTablesL3a`. From the
      whole-regex main-match setup, PRODUCES every (a)-(h) hypothesis that R3's
      `FLookLoopValueLiftFull`/`FLookLoopFullCoversInLooks` and R2's
      `FLookLoopCaptureFrameNested` require, at cap/lk/qt := the winning thread's
      register banks, S := CaptureRegsSet(CapIdsInLooks(re)), Slook :=
      LookIdSet(re). recon A: (a)/(D-ord)/(g_new)/(h) are ALL unconditional
      (table+nesting only, DEPTH-GENERAL — no `NestDepth` cap); (b)/(c')/(e)/(f)
      + register wf + quant finality read the winning thread and are guarded by
      `result.Some?`. Assembles `LookRowsStaticNested` + `LookRowsDynamicNested`
      + `FStabilityNested` + `FFindMatchQuantFinalAny`. */
  lemma LookBodyQuantsIn(r: R.regex, lid: nat)
    requires lid in LTB.LookIds(r)
    ensures PIV.QuantIds(NI.LookBodyOfRE(r, lid)) <= PIV.QuantIdsInLooks(r)
    ensures PIV.QuantIds(NI.LookBodyOfRE(r, lid)) <= PIV.QuantIds(r)
    decreases r
  {
    PIV.QuantIdsSplit(r);
    match r
    case Re_alt(r1, r2) =>
      if lid in LTB.LookIds(r1) { LookBodyQuantsIn(r1, lid); } else { LookBodyQuantsIn(r2, lid); }
    case Re_con(r1, r2) =>
      if lid in LTB.LookIds(r1) { LookBodyQuantsIn(r1, lid); } else { LookBodyQuantsIn(r2, lid); }
    case Re_quant(_, _, _, r1) => LookBodyQuantsIn(r1, lid);
    case Re_capture(_, r1) => LookBodyQuantsIn(r1, lid);
    case Re_lookaround(lid0, _, r1) =>
      if lid0 >= 0 && (lid0 as nat) == lid {
      } else {
        LookBodyQuantsIn(r1, lid);
      }
  }

  /** C4e: quant twin of `NI.LookBodiesCapsDisjointOrNested`. For two distinct
      look ids, either their bodies' QUANT ids are DISJOINT (siblings) or one is
      nested in the other and the inner body's quants are a SUBSET. Pure
      structure + unique ids; mirrors the capture trichotomy with `QuantUnique` +
      `LookBodyQuantsIn`. */
  lemma LookBodiesQuantsDisjointOrNested(r: R.regex, l1: nat, l2: nat)
    requires PIV.QuantUnique(r) && LTB.LookUnique(r)
    requires l1 in LTB.LookIds(r) && l2 in LTB.LookIds(r) && l1 != l2
    ensures (PIV.QuantIds(NI.LookBodyOfRE(r, l1)) * PIV.QuantIds(NI.LookBodyOfRE(r, l2)) == {})
            || (l2 in LTB.LookIds(NI.LookBodyOfRE(r, l1))
                && PIV.QuantIds(NI.LookBodyOfRE(r, l2)) <= PIV.QuantIds(NI.LookBodyOfRE(r, l1)))
            || (l1 in LTB.LookIds(NI.LookBodyOfRE(r, l2))
                && PIV.QuantIds(NI.LookBodyOfRE(r, l1)) <= PIV.QuantIds(NI.LookBodyOfRE(r, l2)))
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      if l1 in LTB.LookIds(r1) && l2 in LTB.LookIds(r1) {
        LookBodiesQuantsDisjointOrNested(r1, l1, l2);
      } else if l1 !in LTB.LookIds(r1) && l2 !in LTB.LookIds(r1) {
        LookBodiesQuantsDisjointOrNested(r2, l1, l2);
      } else {
        if l1 in LTB.LookIds(r1) { LookBodyQuantsIn(r1, l1); LookBodyQuantsIn(r2, l2); }
        else { LookBodyQuantsIn(r2, l1); LookBodyQuantsIn(r1, l2); }
        forall q: nat | q in PIV.QuantIds(NI.LookBodyOfRE(r, l1)) * PIV.QuantIds(NI.LookBodyOfRE(r, l2))
          ensures false
        { assert q in PIV.QuantIds(r1) * PIV.QuantIds(r2); }
      }
    case Re_con(r1, r2) =>
      if l1 in LTB.LookIds(r1) && l2 in LTB.LookIds(r1) {
        LookBodiesQuantsDisjointOrNested(r1, l1, l2);
      } else if l1 !in LTB.LookIds(r1) && l2 !in LTB.LookIds(r1) {
        LookBodiesQuantsDisjointOrNested(r2, l1, l2);
      } else {
        if l1 in LTB.LookIds(r1) { LookBodyQuantsIn(r1, l1); LookBodyQuantsIn(r2, l2); }
        else { LookBodyQuantsIn(r2, l1); LookBodyQuantsIn(r1, l2); }
        forall q: nat | q in PIV.QuantIds(NI.LookBodyOfRE(r, l1)) * PIV.QuantIds(NI.LookBodyOfRE(r, l2))
          ensures false
        { assert q in PIV.QuantIds(r1) * PIV.QuantIds(r2); }
      }
    case Re_quant(_, _, _, r1) => LookBodiesQuantsDisjointOrNested(r1, l1, l2);
    case Re_capture(_, r1) => LookBodiesQuantsDisjointOrNested(r1, l1, l2);
    case Re_lookaround(lid0, _, r1) =>
      if lid0 >= 0 && (lid0 as nat) == l1 {
        assert l2 in LTB.LookIds(r1);
        assert NI.LookBodyOfRE(r, l1) == r1;
        assert NI.LookBodyOfRE(r, l2) == NI.LookBodyOfRE(r1, l2);
        LookBodyQuantsIn(r1, l2);
      } else if lid0 >= 0 && (lid0 as nat) == l2 {
        assert l1 in LTB.LookIds(r1);
        assert NI.LookBodyOfRE(r, l2) == r1;
        assert NI.LookBodyOfRE(r, l1) == NI.LookBodyOfRE(r1, l1);
        LookBodyQuantsIn(r1, l1);
      } else {
        assert l1 in LTB.LookIds(r1) && l2 in LTB.LookIds(r1);
        assert NI.LookBodyOfRE(r, l1) == NI.LookBodyOfRE(r1, l1);
        assert NI.LookBodyOfRE(r, l2) == NI.LookBodyOfRE(r1, l2);
        LookBodiesQuantsDisjointOrNested(r1, l1, l2);
      }
  }

  /** DELIVERABLE #4: the PREMISE-FREE corollary (engine side of recon_inner +
      recon_outer). From the whole-regex main-match setup alone (all (a)-(h)
      discharged by `LookRowsFromTablesNested`), the whole-regex `FLookLoop`'s
      capture bank `res.0`:
      - (recon_outer) writes ONLY inside look bodies: agrees with the main-match
        bank OUTSIDE `CaptureRegsSet(CapIdsInLooks(re))`, and the look bank
        `res.1` agrees OUTSIDE `LookIdSet(re)` (`FLookLoopCaptureFrameNested`);
      - (recon_inner) carries every `g in CapIdsInLooks(re)` whose innermost
        owner is a matched positive lookahead, at the owner's fresh-body value
        (`FLookLoopFullCoversInLooks`). */
/** (G5a-1 P5b) `DOrdQuantFromTables` on the top-level fragment: the same proof, the premise widened and its callees
      on their `…Cdn` forms where the argument is the top regex or a non-look subterm of it. */
  lemma DOrdQuantFromTablesCdn(ast: R.regex, re: R.regex, crv: CP.FCompiled,
                            l1: int, la1: R.lookaround, b1: R.regex,
                            l2: int, la2: R.lookaround, b2: R.regex)
    requires crv == CP.FFullCompilation(ast)
    requires re == R.lazy_prefix(ast)
    requires LookBodiesPlusGateRE(re)   // (G3a) the weak gate (was LooksNoNulledPlusRE)
    requires T.TransWf(re)   // (G3a) for FrameEntryOkFromTables' plus table
    requires NR.NestedFragmentCdnRE(re)   // (L5 F7c) lifted from NoPosLookbehindRE
    requires PIV.CapUnique(re) && PIV.QuantUnique(re) && LTB.LookUnique(re)
    requires LTB.LookTablesOk(re, crv) && LTB.LidsWellNested(re)
    requires 1 <= l1 <= R.max_lookaround(ast) && 1 <= l2 <= R.max_lookaround(ast) && l1 < l2
    requires LTB.LookEntryOk(crv, l1, la1, b1) && LTB.LookEntryOk(crv, l2, la2, b2)
    ensures QIdsOuter(b1) * LKC.QIdsInt(b2) == {}
  {
    var pre := R.Re_quant(R.NonNullable, 0, R.CountedQuant(0, None, false),
                          R.Re_character(R.Dot));
    assert re == R.Re_con(pre, ast);
    assert LTB.LookIds(re) == LTB.LookIds(ast);
    LookEntryOnlyReal(ast, crv, l1, la1, b1);
    LookEntryOnlyReal(ast, crv, l2, la2, b2);
    var lid1 := l1 as nat;
    var lid2 := l2 as nat;
    NI.LookBodyOfTablesTie(re, crv, lid1);
    NI.LookBodyOfTablesTie(re, crv, lid2);
    var la01: R.lookaround :| LTB.LookEntryOk(crv, lid1 as int, la01, NI.LookBodyOfRE(re, lid1));
    var la02: R.lookaround :| LTB.LookEntryOk(crv, lid2 as int, la02, NI.LookBodyOfRE(re, lid2));
    assert b1 == NI.LookBodyOfRE(re, lid1);
    assert b2 == NI.LookBodyOfRE(re, lid2);
    PIV.QuantIdsSplit(b1);                               // QuantIdsOutsideLooks(b1) <= QuantIds(b1)
    LookBodyFactsL5Cdn(re, crv, lid1);                  // QuantUnique(b1)
    LookBodiesQuantsDisjointOrNested(re, lid1, lid2);
    // nat-set disjointness: QuantIdsOutsideLooks(b1) * QuantIds(b2) == {}
    if PIV.QuantIds(b1) * PIV.QuantIds(b2) == {} {
      assert PIV.QuantIdsOutsideLooks(b1) * PIV.QuantIds(b2) == {};
    } else if lid2 in LTB.LookIds(b1) && PIV.QuantIds(b2) <= PIV.QuantIds(b1) {
      NI.LookBodyCompose(re, lid1, lid2);               // b2 == LookBodyOfRE(b1, lid2)
      LookBodyQuantsIn(b1, lid2);                        // QuantIds(b2) <= QuantIdsInLooks(b1)
      PIV.QuantIdsLooksDisjoint(b1);                     // outside(b1) * inside(b1) == {}
      assert PIV.QuantIdsOutsideLooks(b1) * PIV.QuantIds(b2) == {};
    } else {
      assert lid1 in LTB.LookIds(b2);
      LookBodyLidsGt(re, lid2);                          // x in LookIds(b2) ==> l2 < x
      assert lid2 < lid1;                                // contra l1 < l2
      assert false;
    }
    // transfer nat-disjointness to the int images
    forall k: int | k in QIdsOuter(b1) * LKC.QIdsInt(b2) ensures false {
      var q1: nat :| q1 in PIV.QuantIdsOutsideLooks(b1) && (q1 as int) == k;
      var q2: nat :| q2 in PIV.QuantIds(b2) && (q2 as int) == k;
      assert q1 == q2;
      assert q1 in PIV.QuantIdsOutsideLooks(b1) * PIV.QuantIds(b2);
    }
  }

  /** (G5a-1 P5b) The narrow form, as a corollary of `DOrdQuantFromTablesCdn`. */
  lemma DOrdQuantFromTables(ast: R.regex, re: R.regex, crv: CP.FCompiled,
                            l1: int, la1: R.lookaround, b1: R.regex,
                            l2: int, la2: R.lookaround, b2: R.regex)
    requires crv == CP.FFullCompilation(ast)
    requires re == R.lazy_prefix(ast)
    requires LookBodiesPlusGateRE(re)   // (G3a) the weak gate (was LooksNoNulledPlusRE)
    requires T.TransWf(re)   // (G3a) for FrameEntryOkFromTables' plus table
    requires NR.NestedFragmentRE(re)   // (L5 F7c) lifted from NoPosLookbehindRE
    requires PIV.CapUnique(re) && PIV.QuantUnique(re) && LTB.LookUnique(re)
    requires LTB.LookTablesOk(re, crv) && LTB.LidsWellNested(re)
    requires 1 <= l1 <= R.max_lookaround(ast) && 1 <= l2 <= R.max_lookaround(ast) && l1 < l2
    requires LTB.LookEntryOk(crv, l1, la1, b1) && LTB.LookEntryOk(crv, l2, la2, b2)
    ensures QIdsOuter(b1) * LKC.QIdsInt(b2) == {}
  {
    NR.NarrowIsCdn(re);
    hide *;   // the wide premises are this lemma's own: match by name
    DOrdQuantFromTablesCdn(ast, re, crv, l1, la1, b1, l2, la2, b2);
  }

  /** C4e: (Sq-bound) per-row — each body's OUTSIDE-look quant ids land in the
      int image of `re`'s in-look quant ids. Via `LookBodyQuantsIn` (`QuantIds
      (body) <= QuantIdsInLooks(re)`) + `QuantIdsSplit`. */
  lemma SqBoundQuantFromTables(ast: R.regex, re: R.regex, crv: CP.FCompiled,
                               l: int, la: R.lookaround, body: R.regex)
    requires crv == CP.FFullCompilation(ast)
    requires re == R.lazy_prefix(ast)
    requires LookBodiesPlusGateRE(re)   // (G3a) the weak gate (was LooksNoNulledPlusRE)
    requires T.TransWf(re)   // (G3a) for FrameEntryOkFromTables' plus table
    requires PIV.QuantUnique(re) && LTB.LookUnique(re)
    requires LTB.LookTablesOk(re, crv)
    requires 1 <= l <= R.max_lookaround(ast)
    requires LTB.LookEntryOk(crv, l, la, body)
    ensures QIdsOuter(body) <= (set q: nat | q in PIV.QuantIdsInLooks(re) :: q as int)
  {
    var pre := R.Re_quant(R.NonNullable, 0, R.CountedQuant(0, None, false),
                          R.Re_character(R.Dot));
    assert re == R.Re_con(pre, ast);
    assert LTB.LookIds(re) == LTB.LookIds(ast);
    LookEntryOnlyReal(ast, crv, l, la, body);
    var lid := l as nat;
    NI.LookBodyOfTablesTie(re, crv, lid);
    var la0: R.lookaround :| LTB.LookEntryOk(crv, lid as int, la0, NI.LookBodyOfRE(re, lid));
    assert body == NI.LookBodyOfRE(re, lid);
    LookBodyQuantsIn(re, lid);                           // QuantIds(body) <= QuantIdsInLooks(re)
    PIV.QuantIdsSplit(body);                             // QuantIdsOutsideLooks(body) <= QuantIds(body)
    forall k: int | k in QIdsOuter(body)
      ensures k in (set q: nat | q in PIV.QuantIdsInLooks(re) :: q as int)
    {
      var q: nat :| q in PIV.QuantIdsOutsideLooks(body) && (q as int) == k;
      assert q in PIV.QuantIds(body);
      assert q in PIV.QuantIdsInLooks(re);
    }
  }

  /** C4e: nested twin of `MainMatchBodyQuantsInit` — the main pass never stamps
      an inside-look quant, so a genuine-start search returns a winning thread
      whose quant bank agrees with the INITIAL bank OUTSIDE `QIdsOuter(re)`. Via
      the nested outer-quant classifier `QuantBytecodeClassifiedNestedOuter` +
      `CM.FFindMatchQuantFrame`. */
/** (G5a-1 P5b) `MainMatchBodyQuantsInitNested` on the top-level fragment: the same proof, the premise widened and its callees
      on their `…Cdn` forms where the argument is the top regex or a non-look subterm of it. */
  lemma MainMatchBodyQuantsInitCdn(re: R.regex, code: RB.code, str: string,
                                      inits: AI.VmState, cap: AReg.Regs, look: AReg.Regs, quant: AReg.Regs,
                                      ov: LOr.OracleView, cdn: LCdn.cdns, result: Option<AI.Thread>)
    requires NR.NestedFragmentCdnRE(re) && PIV.QuantUnique(re)
    requires code == CP.compile_to_bytecode(re)
    requires |inits.processed.true_set| == RB.size(code) && |inits.processed.false_set| == RB.size(code)
    requires inits.context.nextchar == AI.get_char(str, inits.cp)
    requires 0 <= inits.cp <= |str|
    requires inits.active == [AI.init_thread(cap, look, quant)]
    requires inits.blocked == [] && inits.bestmatch.None?
    requires result == AI.FFindMatch(code, str, inits, ov, LAnc.Forward, cdn).0
    ensures result.Some? ==> CM.RegsAgreeOutside(result.value.quant_regs, quant, QIdsOuter(re))
  {
    QuantBytecodeClassifiedCdnOuter(re);              // QuantWritesInside(code, QIdsOuter(re))
    assert CM.VmQuantsAgree(inits, quant, QIdsOuter(re)) by {
      assert AI.init_thread(cap, look, quant).quant_regs == quant;
      assert CM.RegsAgreeOutside(quant, quant, QIdsOuter(re));
    }
    CM.FFindMatchQuantFrame(code, str, inits, ov, LAnc.Forward, cdn, quant, QIdsOuter(re));
  }

  /** (G5a-1 P5b) The narrow form, as a corollary of `MainMatchBodyQuantsInitCdn`. */
  lemma MainMatchBodyQuantsInitNested(re: R.regex, code: RB.code, str: string,
                                      inits: AI.VmState, cap: AReg.Regs, look: AReg.Regs, quant: AReg.Regs,
                                      ov: LOr.OracleView, cdn: LCdn.cdns, result: Option<AI.Thread>)
    requires NR.NestedFragmentRE(re) && PIV.QuantUnique(re)
    requires code == CP.compile_to_bytecode(re)
    requires |inits.processed.true_set| == RB.size(code) && |inits.processed.false_set| == RB.size(code)
    requires inits.context.nextchar == AI.get_char(str, inits.cp)
    requires 0 <= inits.cp <= |str|
    requires inits.active == [AI.init_thread(cap, look, quant)]
    requires inits.blocked == [] && inits.bestmatch.None?
    requires result == AI.FFindMatch(code, str, inits, ov, LAnc.Forward, cdn).0
    ensures result.Some? ==> CM.RegsAgreeOutside(result.value.quant_regs, quant, QIdsOuter(re))
  {
    NR.NarrowIsCdn(re);
    hide *;   // the wide premises are this lemma's own: match by name
    MainMatchBodyQuantsInitCdn(re, code, str, inits, cap, look, quant, ov, cdn, result);
  }

  /** C4e: a look body's quant ids are disjoint from `re`'s OUTSIDE-look quant
      ids — `QIdsInt(body)` (int image of `QuantIds(body)`) misses `QIdsOuter(re)`.
      Via `LookBodyQuantsIn` (`QuantIds(body) <= QuantIdsInLooks(re)`) +
      `QuantIdsLooksDisjoint`. Feeds the (c'q) discharge in the premise-free
      quant corollary. */
  lemma BodyQIdsIntDisjointOuterRe(ast: R.regex, re: R.regex, crv: CP.FCompiled,
                                   l: int, la: R.lookaround, body: R.regex)
    requires crv == CP.FFullCompilation(ast)
    requires re == R.lazy_prefix(ast)
    requires LookBodiesPlusGateRE(re)   // (G3a) the weak gate (was LooksNoNulledPlusRE)
    requires T.TransWf(re)   // (G3a) for FrameEntryOkFromTables' plus table
    requires PIV.QuantUnique(re) && LTB.LookUnique(re)
    requires LTB.LookTablesOk(re, crv)
    requires 1 <= l <= R.max_lookaround(ast)
    requires LTB.LookEntryOk(crv, l, la, body)
    ensures LKC.QIdsInt(body) * QIdsOuter(re) == {}
  {
    var pre := R.Re_quant(R.NonNullable, 0, R.CountedQuant(0, None, false),
                          R.Re_character(R.Dot));
    assert re == R.Re_con(pre, ast);
    assert LTB.LookIds(re) == LTB.LookIds(ast);
    LookEntryOnlyReal(ast, crv, l, la, body);
    var lid := l as nat;
    NI.LookBodyOfTablesTie(re, crv, lid);
    var la0: R.lookaround :| LTB.LookEntryOk(crv, lid as int, la0, NI.LookBodyOfRE(re, lid));
    assert body == NI.LookBodyOfRE(re, lid);
    LookBodyQuantsIn(re, lid);                           // QuantIds(body) <= QuantIdsInLooks(re)
    PIV.QuantIdsLooksDisjoint(re);                       // outside(re) * inside(re) == {}
    forall k: int | k in LKC.QIdsInt(body) * QIdsOuter(re) ensures false {
      var q1: nat :| q1 in PIV.QuantIds(body) && (q1 as int) == k;
      var q2: nat :| q2 in PIV.QuantIdsOutsideLooks(re) && (q2 as int) == k;
      assert q1 == q2;
      assert q1 in PIV.QuantIdsInLooks(re);
      assert q2 in PIV.QuantIdsOutsideLooks(re) * PIV.QuantIdsInLooks(re);
    }
  }

  /** C4e DELIVERABLE 3: the PREMISE-FREE quant corollary — quant analogue of
      `FLookLoopFullCoversFromTables`, supplying the endpoint's inside-value feed
      (iii) directly. From the whole-regex main-match setup alone, the whole-regex
      `FLookLoop`'s quant bank `res.2`:
      - (recon_outer) writes only inside look bodies: agrees with the main-match
        quant bank OUTSIDE the int image of `QuantIdsInLooks(re)`
        (`FLookLoopQuantFrameNested`);
      - (recon_inner) carries every `qd in QuantIdsInLooks(re)` whose innermost
        owner is a matched positive lookahead, at the owner's fresh-body value
        (`FLookLoopQuantCoversInLooks`).
      `LookRowsFromTablesNested` discharges the shared (a),(b),(e),(f),(g_new),(h)
      + register wf + quant finality; the quant twins (c'q)/(D-ord-q)/(Sq-bound)
      are discharged here from `MainMatchBodyQuantsInitNested`/`DOrdQuantFrom
      Tables`/`SqBoundQuantFromTables`. */
  // ==========================================================================
  // L4 PERF: OPAQUE wrappers for the endpoint's heavy QUANTIFIED facts. Each is
  // ESTABLISHED cheaply inside its producing adapter (`reveal` + the raw fact
  // just proven, a direct match in the adapter's SMALL context) and consumed
  // OPAQUELY (no triggers) at the MainTheoremL4 -> DeepConclude boundary, so the
  // ~5000-obligation context no longer floods every VC with these facts'
  // trigger instantiations. Consumers `reveal` internally to recover the raw
  // fact for their (already-green) bodies.
  // ==========================================================================
  ghost opaque predicate ValueOkO(crv: CP.FCompiled, str: string, res0: AReg.Regs, res1: AReg.Regs,
                                  lid: int, maxlook: int, ov: LOr.OracleView, ncap: int, nlook: int, nquant: int) {
    FLookLoopValueOkFull(crv, str, res0, res1, lid, maxlook, ov, ncap, nlook, nquant)
  }
  ghost opaque predicate QuantValueOkO(crv: CP.FCompiled, str: string, res2: AReg.Regs, res1: AReg.Regs,
                                       lid: int, maxlook: int, ov: LOr.OracleView, ncap: int, nlook: int, nquant: int) {
    FLookLoopQuantValueOkFull(crv, str, res2, res1, lid, maxlook, ov, ncap, nlook, nquant)
  }
  ghost opaque predicate ChildLinkO(crv: CP.FCompiled, str: string, res1: AReg.Regs,
                                    lid: int, maxlook: int, ov: LOr.OracleView, ncap: int, nlook: int, nquant: int) {
    FLookLoopChildLinkOk(crv, str, res1, lid, maxlook, ov, ncap, nlook, nquant)
  }
  ghost opaque predicate LookInvO(res1: AReg.Regs, ov: LOr.OracleView, str: string) {
    CM.LookCpsOracleTrue(res1, ov) && CM.LookCpSetWithClk(res1) && CM.LookCpsLE(res1, |str|)
  }
  ghost opaque predicate TopLookFrameO(re: R.regex, res1: AReg.Regs, look0: AReg.Regs) {
    forall lz: nat :: lz in NI.TopLookIds(re) ==>
                        AI.get_idx(res1.a_clk, lz as int) == AI.get_idx(look0.a_clk, lz as int)
                        && AReg.get_cp(res1, lz as int) == AReg.get_cp(look0, lz as int)
  }
  ghost opaque predicate QuantFrameO(re: R.regex, res2: AReg.Regs, quant0: AReg.Regs) {
    forall q: nat :: q in PIV.QuantIdsOutsideLooks(re) ==>
                       AI.get_idx(res2.a_clk, q as int) == AI.get_idx(quant0.a_clk, q as int)
  }
  ghost opaque predicate CaptureFrameO(re: R.regex, res0: AReg.Regs, cap0: AReg.Regs) {
    forall k: int :: k !in PIV.CaptureRegsSet(PIV.CapIdsInLooks(re)) ==>
                       AI.get_idx(res0.a_cp, k) == AI.get_idx(cap0.a_cp, k)
                       && AI.get_idx(res0.a_clk, k) == AI.get_idx(cap0.a_clk, k)
  }
  ghost opaque predicate Res0LiveO(re: R.regex, res0: AReg.Regs) {
    forall c: nat :: c in PIV.CapIds(re) && AI.get_idx(res0.a_clk, CP.start_reg(c)) < 0
                     ==> AI.get_idx(res0.a_cp, CP.start_reg(c)) < 0
  }
  ghost opaque predicate ThreadLookInvO(look0: AReg.Regs, ov: LOr.OracleView, str: string) {
    CM.LookCpSetWithClk(look0) && CM.LookCpsOracleTrue(look0, ov) && CM.LookCpsLE(look0, |str|)
    && |look0.a_cp| == |look0.a_clk|
  }
  ghost opaque predicate FrameEntryAllO(crv: CP.FCompiled, re: R.regex, ast: R.regex) {
    forall l: int, la: R.lookaround, b: R.regex ::
      1 <= l <= R.max_lookaround(ast) && LTB.LookEntryOk(crv, l, la, b) ==>
        FrameEntryOk(crv, la, b, PIV.CaptureRegsSet(PIV.CapIdsInLooks(re)), LookIdSet(re))
  }
  ghost opaque predicate OracleSufAllO(rer: LW.RegExpRecord, qm: AR.QMap, str: string) {
    forall cp: nat :: cp <= |str| ==> LL.OracleOkSuffix(rer, qm, PIV.InpOfCp(str, cp))
  }
  /** L4 PERF: the (a)-(h) look-table hypotheses that `FreshBodyDirectMember`
      needs, bundled OPAQUE. The (D-ord)/(g_new) SIX-variable quantifiers are the
      dominant Z3 trigger-explosion source; wrapping them lets the owner-forall
      hold the tables atomically (no triggers on its other assertions) and
      `FreshBodyDirectMember` reveal them only in its own body. */
  opaque ghost predicate WinRegsOk(ast: R.regex, re: R.regex, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
                                   th: AI.Thread, ncap: int, nlook: int, nquant: int) {
    CM.ThreadRegsWf(th, ncap, nlook, nquant)
    && (forall k :: AI.get_idx(th.quant_regs.a_cp, k) < 0)
    && (forall k :: AI.get_idx(th.quant_regs.a_clk, k) >= -1)
    && CM.LookCpsLE(th.look_regs, |str|)
    && (forall l: int :: 1 <= l <= R.max_lookaround(ast) && AReg.get_cp(th.look_regs, l).Some? ==>
                           exists la: R.lookaround, body: R.regex :: LTB.LookEntryOk(crv, l, la, body))
    && (forall l: int, la: R.lookaround, body: R.regex ::
          1 <= l <= R.max_lookaround(ast) && LTB.LookEntryOk(crv, l, la, body) ==>
            CM.RegsAgreeInside(th.capture_regs, AReg.init_regs(ncap), PIV.CaptureRegs(body)))
    && (forall l1: int, la1: R.lookaround, b1: R.regex, l2: int ::
          (1 <= l1 <= R.max_lookaround(ast) && LTB.LookEntryOk(crv, l1, la1, b1)
          && 1 <= l2 <= R.max_lookaround(ast) && l2 != l1
          && AReg.get_cp(th.look_regs, l2).Some?) ==> l2 !in LookIdSet(b1))
    && CM.RegsAgreeOutside(th.quant_regs, AReg.init_regs(nquant), QIdsOuter(re))
    && CM.RegsAgreeOutside(th.look_regs, AReg.init_regs(nlook), DirectLidSet(re))
    && CM.LookClkSetWithCp(th.look_regs) && CM.LookCpSetWithClk(th.look_regs)
    && CM.LookCpsOracleTrue(th.look_regs, ov)
    // (gate C, G2) only POSITIVE lids are ever recorded (`CheckOracle` is the only look writer)
    && LB.LookSetIn(th.look_regs, LB.PosLookIds(re))
  }

/** (G5a-1 P5b) `EndpointQuantValueOkRegs` on the top-level fragment: the same proof, the premise widened and its callees
      on their `…Cdn` forms where the argument is the top regex or a non-look subterm of it. */
  lemma EndpointQuantValueOkRegsCdn(
    ast: R.regex, re: R.regex, crv: CP.FCompiled, str: string,
    ov: LOr.OracleView, th: AI.Thread, ncap: int, nlook: int, nquant: int)
    requires crv == CP.FFullCompilation(ast)
    requires re == R.lazy_prefix(ast)
    requires LookBodiesPlusGateRE(re)   // (G3a) the weak gate (was LooksNoNulledPlusRE)
    requires T.TransWf(re)   // (G3a) for FrameEntryOkFromTables' plus table
    requires NR.NestedFragmentCdnRE(re)
    requires PIV.CapUnique(re) && PIV.QuantUnique(re) && LTB.LookUnique(re)
    requires LTB.LookTablesOk(re, crv) && LTB.LidsWellNested(re)
    requires forall x: nat :: x in LTB.LookIds(re) ==> 1 <= x <= R.max_lookaround(ast)
    requires ncap >= 0 && nlook >= 0 && nquant >= 0
    requires WinRegsOk(ast, re, crv, str, ov, th, ncap, nlook, nquant)
    ensures var res := AI.FLookLoop(crv, str, 1, R.max_lookaround(ast),
                                    th.capture_regs, th.look_regs, th.quant_regs, ov);
            |res.2.a_cp| == nquant && |res.2.a_clk| == nquant
            && (forall k :: AI.get_idx(res.2.a_clk, k) >= -1)   // (G3a) clocks only: a look row may stamp positions
            && QuantValueOkO(crv, str, res.2, res.1, 1, R.max_lookaround(ast), ov, ncap, nlook, nquant)
            && QuantFrameO(re, res.2, th.quant_regs)
  {
    reveal QuantValueOkO();
    LookRowsStaticCdn(ast, re, crv);
    RowsAvoidFromTablesCdn(ast, re, crv);   // (G3a) later rows never name a row's outside-look quantifiers
    reveal WinRegsOk();
    {
      var S := PIV.CaptureRegsSet(PIV.CapIdsInLooks(re));
      var Slook := LookIdSet(re);
      var Sq := set qz: nat | qz in PIV.QuantIdsInLooks(re) :: qz as int;
      var c := th.capture_regs;
      var l := th.look_regs;
      var q := th.quant_regs;
      assert CM.ThreadRegsWf(th, ncap, nlook, nquant);
      var maxlook := R.max_lookaround(ast);

      // ---- quant twins of (c'q)/(D-ord-q)/(Sq-bound) — verbatim from FLookLoopQuantCoversFromTables ----
      assert CM.RegsAgreeOutside(q, AReg.init_regs(nquant), QIdsOuter(re));
      PIV.QuantIdsLooksDisjoint(re);
      assert forall lx: int, lax: R.lookaround, body: R.regex ::
          1 <= lx <= maxlook && LTB.LookEntryOk(crv, lx, lax, body) ==>
            CM.RegsAgreeInside(q, AReg.init_regs(nquant), LKC.QIdsInt(body))
      by {
        forall lx: int, lax: R.lookaround, body: R.regex |
          1 <= lx <= maxlook && LTB.LookEntryOk(crv, lx, lax, body)
          ensures CM.RegsAgreeInside(q, AReg.init_regs(nquant), LKC.QIdsInt(body))
        {
          BodyQIdsIntDisjointOuterRe(ast, re, crv, lx, lax, body);
          RegsAgreeOutsideToInside(q, AReg.init_regs(nquant), LKC.QIdsInt(body), QIdsOuter(re));
        }
      }
      assert forall lx1: int, lax1: R.lookaround, b1: R.regex, lx2: int, lax2: R.lookaround, b2: R.regex ::
          1 <= lx1 <= maxlook && 1 <= lx2 <= maxlook && lx1 < lx2
          && LTB.LookEntryOk(crv, lx1, lax1, b1) && LTB.LookEntryOk(crv, lx2, lax2, b2) ==>
            QIdsOuter(b1) * LKC.QIdsInt(b2) == {}
      by {
        forall lx1: int, lax1: R.lookaround, b1: R.regex, lx2: int, lax2: R.lookaround, b2: R.regex |
          1 <= lx1 <= maxlook && 1 <= lx2 <= maxlook && lx1 < lx2
          && LTB.LookEntryOk(crv, lx1, lax1, b1) && LTB.LookEntryOk(crv, lx2, lax2, b2)
          ensures QIdsOuter(b1) * LKC.QIdsInt(b2) == {}
        { DOrdQuantFromTablesCdn(ast, re, crv, lx1, lax1, b1, lx2, lax2, b2); }
      }
      assert forall lx: int, lax: R.lookaround, body: R.regex ::
          1 <= lx <= maxlook && LTB.LookEntryOk(crv, lx, lax, body) ==> QIdsOuter(body) <= Sq
      by {
        forall lx: int, lax: R.lookaround, body: R.regex |
          1 <= lx <= maxlook && LTB.LookEntryOk(crv, lx, lax, body)
          ensures QIdsOuter(body) <= Sq
        { SqBoundQuantFromTables(ast, re, crv, lx, lax, body); }
      }

      FLookLoopQuantValueLiftFull(crv, str, 1, maxlook, c, l, q, ov, S, Slook, Sq, ncap, nlook, nquant);
      // the quant frame (RegsAgreeOutside(res.2, q, Sq)) — same (a)/(Sq-bound) setup
      assert forall lx: int, lax: R.lookaround, body: R.regex ::
          1 <= lx <= maxlook && LTB.LookEntryOk(crv, lx, lax, body) ==>
            FrameEntryOk(crv, lax, body, S, Slook) && QIdsOuter(body) <= Sq;
      FLookLoopQuantFrameNested(crv, str, 1, maxlook, c, l, q, ov, S, Slook, Sq, ncap, nlook, nquant);
      // QuantFrameO: QuantIdsOutsideLooks is disjoint from Sq, so the RegsAgreeOutside
      // just established pins res.2's clock to quant's on those ids.
      var res := AI.FLookLoop(crv, str, 1, maxlook, c, l, q, ov);
      assert QuantFrameO(re, res.2, q) by {
        reveal QuantFrameO();
        forall qz: nat | qz in PIV.QuantIdsOutsideLooks(re)
          ensures AI.get_idx(res.2.a_clk, qz as int) == AI.get_idx(q.a_clk, qz as int)
        {
          assert (qz as int) !in Sq by {
            if (qz as int) in Sq {
              var q2: nat :| q2 in PIV.QuantIdsInLooks(re) && q2 as int == qz as int;
              assert q2 == qz;
              PIV.QuantIdsLooksDisjoint(re);
              assert qz in PIV.QuantIdsOutsideLooks(re) * PIV.QuantIdsInLooks(re);
            }
          }
        }
      }
    }
  }

  /** (G5a-1 P5b) The narrow form, as a corollary of `EndpointQuantValueOkRegsCdn`. */
  lemma EndpointQuantValueOkRegs(
    ast: R.regex, re: R.regex, crv: CP.FCompiled, str: string,
    ov: LOr.OracleView, th: AI.Thread, ncap: int, nlook: int, nquant: int)
    requires crv == CP.FFullCompilation(ast)
    requires re == R.lazy_prefix(ast)
    requires LookBodiesPlusGateRE(re)   // (G3a) the weak gate (was LooksNoNulledPlusRE)
    requires T.TransWf(re)   // (G3a) for FrameEntryOkFromTables' plus table
    requires NR.NestedFragmentRE(re)
    requires PIV.CapUnique(re) && PIV.QuantUnique(re) && LTB.LookUnique(re)
    requires LTB.LookTablesOk(re, crv) && LTB.LidsWellNested(re)
    requires forall x: nat :: x in LTB.LookIds(re) ==> 1 <= x <= R.max_lookaround(ast)
    requires ncap >= 0 && nlook >= 0 && nquant >= 0
    requires WinRegsOk(ast, re, crv, str, ov, th, ncap, nlook, nquant)
    ensures var res := AI.FLookLoop(crv, str, 1, R.max_lookaround(ast),
                                    th.capture_regs, th.look_regs, th.quant_regs, ov);
            |res.2.a_cp| == nquant && |res.2.a_clk| == nquant
            && (forall k :: AI.get_idx(res.2.a_clk, k) >= -1)   // (G3a) clocks only: a look row may stamp positions
            && QuantValueOkO(crv, str, res.2, res.1, 1, R.max_lookaround(ast), ov, ncap, nlook, nquant)
            && QuantFrameO(re, res.2, th.quant_regs)
  {
    NR.NarrowIsCdn(re);
    hide *;   // the wide premises are this lemma's own: match by name
    EndpointQuantValueOkRegsCdn(ast, re, crv, str, ov, th, ncap, nlook, nquant);
  }

  /** (L4 PERF adapter) The whole-bank `FLookLoopValueOkFull` from the STATIC
      package. `FLookLoopValueLiftFull`'s preconditions are ALL directly ensured
      by `LookRowsFromTablesNested` (no quant/look variant needed), so this is a
      thin two-call wrapper — but isolating it keeps the value-lift out of
      MainTheoremL4's ambient context. */
/** (G5a-1 P5b) `EndpointValueOkRegs` on the top-level fragment: the same proof, the premise widened and its callees
      on their `…Cdn` forms where the argument is the top regex or a non-look subterm of it. */
  lemma EndpointValueOkRegsCdn(
    ast: R.regex, re: R.regex, crv: CP.FCompiled, str: string,
    ov: LOr.OracleView, th: AI.Thread, ncap: int, nlook: int, nquant: int)
    requires crv == CP.FFullCompilation(ast)
    requires re == R.lazy_prefix(ast)
    requires LookBodiesPlusGateRE(re)   // (G3a) the weak gate (was LooksNoNulledPlusRE)
    requires T.TransWf(re)   // (G3a) for FrameEntryOkFromTables' plus table
    requires NR.NestedFragmentCdnRE(re)
    requires PIV.CapUnique(re) && PIV.QuantUnique(re) && LTB.LookUnique(re)
    requires LTB.LookTablesOk(re, crv) && LTB.LidsWellNested(re)
    requires forall x: nat :: x in LTB.LookIds(re) ==> 1 <= x <= R.max_lookaround(ast)
    requires ncap >= 0 && nlook >= 0 && nquant >= 0
    requires WinRegsOk(ast, re, crv, str, ov, th, ncap, nlook, nquant)
    ensures var res := AI.FLookLoop(crv, str, 1, R.max_lookaround(ast),
                                    th.capture_regs, th.look_regs, th.quant_regs, ov);
            |res.0.a_cp| == ncap && |res.0.a_clk| == ncap && PIV.CapRegWf(res.0)
            && |res.1.a_cp| == nlook && |res.1.a_clk| == nlook
            && |res.2.a_cp| == nquant && |res.2.a_clk| == nquant
            && ValueOkO(crv, str, res.0, res.1, 1, R.max_lookaround(ast), ov, ncap, nlook, nquant)
            && Res0LiveO(re, res.0) && CaptureFrameO(re, res.0, th.capture_regs)
    ensures FrameEntryAllO(crv, re, ast)
  {
    reveal ValueOkO(), Res0LiveO();
    LookRowsStaticCdn(ast, re, crv);
    RowsAvoidFromTablesCdn(ast, re, crv);   // (G3a) later rows never name a row's outside-look quantifiers
    reveal WinRegsOk();
    assert FrameEntryAllO(crv, re, ast) by { reveal FrameEntryAllO(); }
    {
      var S := PIV.CaptureRegsSet(PIV.CapIdsInLooks(re));
      var Slook := LookIdSet(re);
      var c := th.capture_regs;
      var l := th.look_regs;
      var q := th.quant_regs;
      assert CM.ThreadRegsWf(th, ncap, nlook, nquant);
      // (G3a) (c'q) and (D-ord-q): A4 at a lookahead row reads the quant bank at the body's quantifiers
      assert CM.RegsAgreeOutside(q, AReg.init_regs(nquant), QIdsOuter(re));
      PIV.QuantIdsLooksDisjoint(re);
      assert forall lx: int, lax: R.lookaround, body: R.regex ::
          1 <= lx <= R.max_lookaround(ast) && LTB.LookEntryOk(crv, lx, lax, body) ==>
            CM.RegsAgreeInside(q, AReg.init_regs(nquant), LKC.QIdsInt(body))
      by {
        forall lx: int, lax: R.lookaround, body: R.regex |
          1 <= lx <= R.max_lookaround(ast) && LTB.LookEntryOk(crv, lx, lax, body)
          ensures CM.RegsAgreeInside(q, AReg.init_regs(nquant), LKC.QIdsInt(body))
        {
          BodyQIdsIntDisjointOuterRe(ast, re, crv, lx, lax, body);
          RegsAgreeOutsideToInside(q, AReg.init_regs(nquant), LKC.QIdsInt(body), QIdsOuter(re));
        }
      }
      assert forall lx1: int, lax1: R.lookaround, b1: R.regex, lx2: int, lax2: R.lookaround, b2: R.regex ::
          1 <= lx1 <= R.max_lookaround(ast) && 1 <= lx2 <= R.max_lookaround(ast) && lx1 < lx2
          && LTB.LookEntryOk(crv, lx1, lax1, b1) && LTB.LookEntryOk(crv, lx2, lax2, b2) ==>
            QIdsOuter(b1) * LKC.QIdsInt(b2) == {}
      by {
        forall lx1: int, lax1: R.lookaround, b1: R.regex, lx2: int, lax2: R.lookaround, b2: R.regex |
          1 <= lx1 <= R.max_lookaround(ast) && 1 <= lx2 <= R.max_lookaround(ast) && lx1 < lx2
          && LTB.LookEntryOk(crv, lx1, lax1, b1) && LTB.LookEntryOk(crv, lx2, lax2, b2)
          ensures QIdsOuter(b1) * LKC.QIdsInt(b2) == {}
        { DOrdQuantFromTablesCdn(ast, re, crv, lx1, lax1, b1, lx2, lax2, b2); }
      }
      FLookLoopValueLiftFull(crv, str, 1, R.max_lookaround(ast), c, l, q, ov, S, Slook, ncap, nlook, nquant);
      // Res0LiveO: CapRegWf(res.0) makes cp<0 whenever clk<0 (register invariant)
      var res := AI.FLookLoop(crv, str, 1, R.max_lookaround(ast), c, l, q, ov);
      assert Res0LiveO(re, res.0) by {
        reveal Res0LiveO();
        forall cc: nat | cc in PIV.CapIds(re) && AI.get_idx(res.0.a_clk, CP.start_reg(cc)) < 0
          ensures AI.get_idx(res.0.a_cp, CP.start_reg(cc)) < 0
        {
          assert PIV.CapRegWf(res.0);
        }
      }
      // CaptureFrameO: FLookLoop writes captures only inside look bodies (Sreg).
      FLookLoopCaptureFrameNested(crv, str, 1, R.max_lookaround(ast), c, l, q, ov, S, Slook, ncap, nlook, nquant);
      assert CaptureFrameO(re, res.0, c) by { reveal CaptureFrameO(); }
    }
  }

  /** (G5a-1 P5b) The narrow form, as a corollary of `EndpointValueOkRegsCdn`. */
  lemma EndpointValueOkRegs(
    ast: R.regex, re: R.regex, crv: CP.FCompiled, str: string,
    ov: LOr.OracleView, th: AI.Thread, ncap: int, nlook: int, nquant: int)
    requires crv == CP.FFullCompilation(ast)
    requires re == R.lazy_prefix(ast)
    requires LookBodiesPlusGateRE(re)   // (G3a) the weak gate (was LooksNoNulledPlusRE)
    requires T.TransWf(re)   // (G3a) for FrameEntryOkFromTables' plus table
    requires NR.NestedFragmentRE(re)
    requires PIV.CapUnique(re) && PIV.QuantUnique(re) && LTB.LookUnique(re)
    requires LTB.LookTablesOk(re, crv) && LTB.LidsWellNested(re)
    requires forall x: nat :: x in LTB.LookIds(re) ==> 1 <= x <= R.max_lookaround(ast)
    requires ncap >= 0 && nlook >= 0 && nquant >= 0
    requires WinRegsOk(ast, re, crv, str, ov, th, ncap, nlook, nquant)
    ensures var res := AI.FLookLoop(crv, str, 1, R.max_lookaround(ast),
                                    th.capture_regs, th.look_regs, th.quant_regs, ov);
            |res.0.a_cp| == ncap && |res.0.a_clk| == ncap && PIV.CapRegWf(res.0)
            && |res.1.a_cp| == nlook && |res.1.a_clk| == nlook
            && |res.2.a_cp| == nquant && |res.2.a_clk| == nquant
            && ValueOkO(crv, str, res.0, res.1, 1, R.max_lookaround(ast), ov, ncap, nlook, nquant)
            && Res0LiveO(re, res.0) && CaptureFrameO(re, res.0, th.capture_regs)
    ensures FrameEntryAllO(crv, re, ast)
  {
    NR.NarrowIsCdn(re);
    hide *;   // the wide premises are this lemma's own: match by name
    EndpointValueOkRegsCdn(ast, re, crv, str, ov, th, ncap, nlook, nquant);
  }

  /** (L4 PERF adapter) `FLookLoopChildLinkOk` from the STATIC package. Unlike the
      value/quant lifts, `FLookLoopChildLinkLift` needs the (c'-look) precondition
      (the winning look bank is INITIAL on every look body's direct-child lids),
      which no existing `FromTables` wrapper produces — proving it inline in
      MainTheoremL4 timed out. Here it is built once, in a minimal context: the
      main code gates only DIRECT lids (`DirectLidClassified` -> `LookChecksInside
      (code, DirectLidSet(re))`), so the winning look bank agrees with the initial
      bank OUTSIDE `DirectLidSet(re)` (`CM.FFindMatchLookFrame`); and a look body's
      direct children are disjoint from `re`'s direct lids (`DirectLidsNotInBody`),
      so the bank is initial on each `DirectLidSet(body)`. */
/** (G5a-1 P5b) `EndpointChildLinkOkRegs` on the top-level fragment: the same proof, the premise widened and its callees
      on their `…Cdn` forms where the argument is the top regex or a non-look subterm of it. */
  lemma EndpointChildLinkOkRegsCdn(
    ast: R.regex, re: R.regex, crv: CP.FCompiled, str: string,
    ov: LOr.OracleView, th: AI.Thread, ncap: int, nlook: int, nquant: int)
    requires crv == CP.FFullCompilation(ast)
    requires re == R.lazy_prefix(ast)
    requires LookBodiesPlusGateRE(re)   // (G3a) the weak gate (was LooksNoNulledPlusRE)
    requires T.TransWf(re)   // (G3a) for FrameEntryOkFromTables' plus table
    requires NR.NestedFragmentCdnRE(re)
    requires PIV.CapUnique(re) && PIV.QuantUnique(re) && LTB.LookUnique(re)
    requires LTB.LookTablesOk(re, crv) && LTB.LidsWellNested(re)
    requires forall x: nat :: x in LTB.LookIds(re) ==> 1 <= x <= R.max_lookaround(ast)
    requires ncap >= 0 && nlook >= 0 && nquant >= 0
    requires WinRegsOk(ast, re, crv, str, ov, th, ncap, nlook, nquant)
    ensures var res := AI.FLookLoop(crv, str, 1, R.max_lookaround(ast),
                                    th.capture_regs, th.look_regs, th.quant_regs, ov);
            ChildLinkO(crv, str, res.1, 1, R.max_lookaround(ast), ov, ncap, nlook, nquant)
  {
    reveal ChildLinkO();
    LookRowsStaticCdn(ast, re, crv);
    RowsAvoidFromTablesCdn(ast, re, crv);   // (G3a) later rows never name a row's outside-look quantifiers
    reveal WinRegsOk();
    var maxlook := R.max_lookaround(ast);
    var initlk := AReg.init_regs(nlook);
    var Sd := DirectLidSet(re);


    {
      var S := PIV.CaptureRegsSet(PIV.CapIdsInLooks(re));
      var Slook := LookIdSet(re);
      var c := th.capture_regs;
      var l := th.look_regs;
      var q := th.quant_regs;
      assert CM.ThreadRegsWf(th, ncap, nlook, nquant);
      assert CM.RegsAgreeOutside(l, initlk, Sd);              // WinRegsOk (the run's look frame)

      // (c'-look): the winning look bank is INITIAL on each body's direct children
      assert forall lx: int, lax: R.lookaround, body: R.regex ::
          1 <= lx <= maxlook && LTB.LookEntryOk(crv, lx, lax, body) ==>
            CM.RegsAgreeInside(l, initlk, DirectLidSet(body))
      by {
        forall lx: int, lax: R.lookaround, body: R.regex |
          1 <= lx <= maxlook && LTB.LookEntryOk(crv, lx, lax, body)
          ensures CM.RegsAgreeInside(l, initlk, DirectLidSet(body))
        {
          LookEntryOnlyReal(ast, crv, lx, lax, body);          // (lx as nat) in LookIds(ast) == LookIds(re)
          var pre := R.Re_quant(R.NonNullable, 0, R.CountedQuant(0, None, false), R.Re_character(R.Dot));
          assert re == R.Re_con(pre, ast);
          assert LTB.LookIds(re) == LTB.LookIds(ast);
          NI.LookBodyOfTablesTie(re, crv, lx as nat);
          var la0: R.lookaround :| LTB.LookEntryOk(crv, lx as nat as int, la0, NI.LookBodyOfRE(re, lx as nat));
          assert body == NI.LookBodyOfRE(re, lx as nat);
          DirectLidsNotInBody(re, lx as nat);                  // DirectLookIds(re) * LookIds(body) == {}
          DirectLidsSubLookIds(body);                          // DirectLookIds(body) <= LookIds(body)
          forall k: int | k in DirectLidSet(body) ensures k !in Sd {
            var kn: nat :| kn in DirectLookIds(body) && (kn as int) == k;
            assert kn in LTB.LookIds(body);
            if k in Sd {
              var kr: nat :| kr in DirectLookIds(re) && (kr as int) == k;
              assert kr == kn;
              assert kr in DirectLookIds(re) * LTB.LookIds(body);
            }
          }
          RegsAgreeOutsideToInside(l, initlk, DirectLidSet(body), Sd);
        }
      }

      // (G3a) (c'q) and (D-ord-q): A4 at a lookahead row reads the quant bank at the body's quantifiers
      assert CM.RegsAgreeOutside(q, AReg.init_regs(nquant), QIdsOuter(re));
      PIV.QuantIdsLooksDisjoint(re);
      assert forall lx: int, lax: R.lookaround, body: R.regex ::
          1 <= lx <= maxlook && LTB.LookEntryOk(crv, lx, lax, body) ==>
            CM.RegsAgreeInside(q, AReg.init_regs(nquant), LKC.QIdsInt(body))
      by {
        forall lx: int, lax: R.lookaround, body: R.regex |
          1 <= lx <= maxlook && LTB.LookEntryOk(crv, lx, lax, body)
          ensures CM.RegsAgreeInside(q, AReg.init_regs(nquant), LKC.QIdsInt(body))
        {
          BodyQIdsIntDisjointOuterRe(ast, re, crv, lx, lax, body);
          RegsAgreeOutsideToInside(q, AReg.init_regs(nquant), LKC.QIdsInt(body), QIdsOuter(re));
        }
      }
      assert forall lx1: int, lax1: R.lookaround, b1: R.regex, lx2: int, lax2: R.lookaround, b2: R.regex ::
          1 <= lx1 <= maxlook && 1 <= lx2 <= maxlook && lx1 < lx2
          && LTB.LookEntryOk(crv, lx1, lax1, b1) && LTB.LookEntryOk(crv, lx2, lax2, b2) ==>
            QIdsOuter(b1) * LKC.QIdsInt(b2) == {}
      by {
        forall lx1: int, lax1: R.lookaround, b1: R.regex, lx2: int, lax2: R.lookaround, b2: R.regex |
          1 <= lx1 <= maxlook && 1 <= lx2 <= maxlook && lx1 < lx2
          && LTB.LookEntryOk(crv, lx1, lax1, b1) && LTB.LookEntryOk(crv, lx2, lax2, b2)
          ensures QIdsOuter(b1) * LKC.QIdsInt(b2) == {}
        { DOrdQuantFromTablesCdn(ast, re, crv, lx1, lax1, b1, lx2, lax2, b2); }
      }
      FLookLoopChildLinkLift(crv, str, 1, maxlook, c, l, q, ov, S, Slook, ncap, nlook, nquant);
    }
  }

  /** (G5a-1 P5b) The narrow form, as a corollary of `EndpointChildLinkOkRegsCdn`. */
  lemma EndpointChildLinkOkRegs(
    ast: R.regex, re: R.regex, crv: CP.FCompiled, str: string,
    ov: LOr.OracleView, th: AI.Thread, ncap: int, nlook: int, nquant: int)
    requires crv == CP.FFullCompilation(ast)
    requires re == R.lazy_prefix(ast)
    requires LookBodiesPlusGateRE(re)   // (G3a) the weak gate (was LooksNoNulledPlusRE)
    requires T.TransWf(re)   // (G3a) for FrameEntryOkFromTables' plus table
    requires NR.NestedFragmentRE(re)
    requires PIV.CapUnique(re) && PIV.QuantUnique(re) && LTB.LookUnique(re)
    requires LTB.LookTablesOk(re, crv) && LTB.LidsWellNested(re)
    requires forall x: nat :: x in LTB.LookIds(re) ==> 1 <= x <= R.max_lookaround(ast)
    requires ncap >= 0 && nlook >= 0 && nquant >= 0
    requires WinRegsOk(ast, re, crv, str, ov, th, ncap, nlook, nquant)
    ensures var res := AI.FLookLoop(crv, str, 1, R.max_lookaround(ast),
                                    th.capture_regs, th.look_regs, th.quant_regs, ov);
            ChildLinkO(crv, str, res.1, 1, R.max_lookaround(ast), ov, ncap, nlook, nquant)
  {
    NR.NarrowIsCdn(re);
    hide *;   // the wide premises are this lemma's own: match by name
    EndpointChildLinkOkRegsCdn(ast, re, crv, str, ov, th, ncap, nlook, nquant);
  }

  /** (L4 PERF adapter) The res.1 look-bank invariants `LookCpsOracleTrue`,
      `LookCpSetWithClk`, `LookCpsLE` from the STATIC package — the winning main
      look bank carries the clk/cp/oracle-true shape (`CM.FFindMatchLook*`), and
      `FLookLoopLookOracleTrue`/`FLookLoopLookCpSet` lift it through the fold. */
  opaque ghost predicate LookPosO(lk: AReg.Regs, crv: CP.FCompiled) {
    LB.LookPosTyped(lk, crv)
  }

  /** (gate C, G2) A set record is a matched POSITIVE look. */
  lemma MatchedPosFromBank(crv: CP.FCompiled, lk: AReg.Regs, l: int)
    requires LookPosO(lk, crv)
    requires AReg.get_cp(lk, l).Some?
    ensures MatchedPosLA(crv, lk, l)
  {
    reveal LookPosO();
  }

  /** (gate C, G2) A look body's FRESH replay (init banks, either direction) records
      only positive rows of `crv`, once the body's rows agree with `crv`. The two
      fresh-replay descent sites read this bank, not the endpoint's (W10 probe C). */
  lemma FreshReplayLookPos(host: R.regex, crv: CP.FCompiled, str: string, cp: nat,
                           ov: LOr.OracleView, dir: LAnc.direction, cdn: LCdn.cdns,
                           ncap: int, nlook: int, nquant: int)
    requires LTB.LookTablesOk(host, crv)
    ensures var bc := CP.compile_to_bytecode(if dir.Forward? then host else R.reverse_regex(host));
            var r := AI.FFindMatch(bc, str,
                                   AI.FInitState(bc, cp, AReg.init_regs(ncap), AReg.init_regs(nlook),
                                                 AReg.init_regs(nquant), 0, AI.cp_context(cp, str, dir)),
                                   ov, dir, cdn).0;
            r.Some? ==> LookPosO(r.value.look_regs, crv)
  {
    reveal LookPosO();
    var P := LB.PosLookIds(host);
    var src := if dir.Forward? then host else R.reverse_regex(host);
    LB.ReversePosLookIds(host);
    assert LB.PosLookIds(src) == P;
    var bc := CP.compile_to_bytecode(src);
    LB.CompileToBytecodeChecksIn(src, P);
    var inits := AI.FInitState(bc, cp, AReg.init_regs(ncap), AReg.init_regs(nlook),
                               AReg.init_regs(nquant), 0, AI.cp_context(cp, str, dir));
    LB.InitRegsLookSetIn(nlook, P);
    assert LB.VmLookSetIn(inits, P) by {
      assert inits.active == [AI.init_thread(AReg.init_regs(ncap), AReg.init_regs(nlook), AReg.init_regs(nquant))];
    }
    LB.FFindMatchLookSetIn(bc, str, inits, ov, dir, cdn, P);
    var r := AI.FFindMatch(bc, str, inits, ov, dir, cdn).0;
    if r.Some? {
      LB.PosLookIdsTyped(host, crv);
      LB.LookSetInTyped(r.value.look_regs, P, crv);
    }
  }

  /** (gate C, G2) `lazy_prefix`'s `.*?` head holds no look. */
  lemma PosLookIdsLazyPrefix(ast: R.regex)
    ensures LB.PosLookIds(R.lazy_prefix(ast)) == LB.PosLookIds(ast)
  {
    var pre := R.Re_quant(R.NonNullable, 0, R.CountedQuant(0, None, false), R.Re_character(R.Dot));
    assert R.lazy_prefix(ast) == R.Re_con(pre, ast);
    assert LB.PosLookIds(pre) == {};
  }

  /** (gate C, G2) The endpoint's post-`FLookLoop` bank records only positive rows. */
  lemma LookPosAtEndpoint(
    ast: R.regex, re: R.regex, crv: CP.FCompiled, str: string,
    ov: LOr.OracleView, th: AI.Thread, ncap: int, nlook: int, nquant: int)
    requires crv == CP.FFullCompilation(ast)
    requires re == R.lazy_prefix(ast)
    requires LTB.LookTablesOk(re, crv)
    requires WinRegsOk(ast, re, crv, str, ov, th, ncap, nlook, nquant)
    ensures LookPosO(AI.FLookLoop(crv, str, 1, R.max_lookaround(ast),
                                  th.capture_regs, th.look_regs, th.quant_regs, ov).1, crv)
  {
    hide *;
    reveal WinRegsOk(), LookPosO();
    var P := LB.PosLookIds(re);
    assert LB.LookSetIn(th.look_regs, P);
    PosLookIdsLazyPrefix(ast);
    LB.FFullCompilationChecksPos(ast);
    assert LB.CrvChecksIn(crv, P);
    LB.FLookLoopLookSetIn(crv, str, 1, R.max_lookaround(ast), th.capture_regs, th.look_regs, th.quant_regs, ov, P);
    LB.PosLookIdsTyped(re, crv);
    LB.LookSetInTyped(AI.FLookLoop(crv, str, 1, R.max_lookaround(ast),
                                   th.capture_regs, th.look_regs, th.quant_regs, ov).1, P, crv);
  }

/** (G5a-1 P5b) `EndpointLookInvRegs` on the top-level fragment: the same proof, the premise widened and its callees
      on their `…Cdn` forms where the argument is the top regex or a non-look subterm of it. */
  lemma EndpointLookInvRegsCdn(
    ast: R.regex, re: R.regex, crv: CP.FCompiled, str: string,
    ov: LOr.OracleView, th: AI.Thread, ncap: int, nlook: int, nquant: int)
    requires crv == CP.FFullCompilation(ast)
    requires re == R.lazy_prefix(ast)
    requires LookBodiesPlusGateRE(re)   // (G3a) the weak gate (was LooksNoNulledPlusRE)
    requires T.TransWf(re)   // (G3a) for FrameEntryOkFromTables' plus table
    requires NR.NestedFragmentCdnRE(re)
    requires PIV.CapUnique(re) && PIV.QuantUnique(re) && LTB.LookUnique(re)
    requires LTB.LookTablesOk(re, crv) && LTB.LidsWellNested(re)
    requires forall x: nat :: x in LTB.LookIds(re) ==> 1 <= x <= R.max_lookaround(ast)
    requires ncap >= 0 && nlook >= 0 && nquant >= 0
    requires WinRegsOk(ast, re, crv, str, ov, th, ncap, nlook, nquant)
    ensures var res := AI.FLookLoop(crv, str, 1, R.max_lookaround(ast),
                                    th.capture_regs, th.look_regs, th.quant_regs, ov);
            LookInvO(res.1, ov, str)
            && ThreadLookInvO(th.look_regs, ov, str)
            && LookPosO(res.1, crv)   // (gate C, G2)
  {
    LookPosAtEndpoint(ast, re, crv, str, ov, th, ncap, nlook, nquant);
    reveal LookInvO(), ThreadLookInvO();
    LookRowsStaticCdn(ast, re, crv);
    RowsAvoidFromTablesCdn(ast, re, crv);   // (G3a) later rows never name a row's outside-look quantifiers
    reveal WinRegsOk();
    var maxlook := R.max_lookaround(ast);
    {
      var S := PIV.CaptureRegsSet(PIV.CapIdsInLooks(re));
      var Slook := LookIdSet(re);
      var c := th.capture_regs;
      var l := th.look_regs;
      var q := th.quant_regs;
      assert CM.ThreadRegsWf(th, ncap, nlook, nquant);
      assert CM.LookClkSetWithCp(l);
      assert CM.LookCpSetWithClk(l);
      assert CM.LookCpsOracleTrue(l, ov);
      FLookLoopLookOracleTrue(crv, str, 1, maxlook, c, l, q, ov, S, Slook, ncap, nlook, nquant);
      FLookLoopLookCpSet(crv, str, 1, maxlook, c, l, q, ov, S, Slook, ncap, nlook, nquant);
      assert ThreadLookInvO(l, ov, str) by { reveal ThreadLookInvO(); assert CM.LookCpsLE(l, |str|); }
    }
  }

  /** (G5a-1 P5b) The narrow form, as a corollary of `EndpointLookInvRegsCdn`. */
  lemma EndpointLookInvRegs(
    ast: R.regex, re: R.regex, crv: CP.FCompiled, str: string,
    ov: LOr.OracleView, th: AI.Thread, ncap: int, nlook: int, nquant: int)
    requires crv == CP.FFullCompilation(ast)
    requires re == R.lazy_prefix(ast)
    requires LookBodiesPlusGateRE(re)   // (G3a) the weak gate (was LooksNoNulledPlusRE)
    requires T.TransWf(re)   // (G3a) for FrameEntryOkFromTables' plus table
    requires NR.NestedFragmentRE(re)
    requires PIV.CapUnique(re) && PIV.QuantUnique(re) && LTB.LookUnique(re)
    requires LTB.LookTablesOk(re, crv) && LTB.LidsWellNested(re)
    requires forall x: nat :: x in LTB.LookIds(re) ==> 1 <= x <= R.max_lookaround(ast)
    requires ncap >= 0 && nlook >= 0 && nquant >= 0
    requires WinRegsOk(ast, re, crv, str, ov, th, ncap, nlook, nquant)
    ensures var res := AI.FLookLoop(crv, str, 1, R.max_lookaround(ast),
                                    th.capture_regs, th.look_regs, th.quant_regs, ov);
            LookInvO(res.1, ov, str)
            && ThreadLookInvO(th.look_regs, ov, str)
            && LookPosO(res.1, crv)   // (gate C, G2)
  {
    NR.NarrowIsCdn(re);
    hide *;   // the wide premises are this lemma's own: match by name
    EndpointLookInvRegsCdn(ast, re, crv, str, ov, th, ncap, nlook, nquant);
  }

  /** (L4 PERF adapter) The TOP-look frame: `FLookLoop` leaves every TOP lid's
      look record untouched (the fold replays nested children, never top rows).
      Verbatim from MainTheoremL4's block — per top lid `l`, the (h')@l premise
      (`l !in LookIdSet` of every row's body, via `TopLookNotNested`) feeds
      `FLookLoopTopLook{Clk,Cp}StableFull`. */
/** (G5a-1 P5b) `EndpointTopLookFrameRegs` on the top-level fragment: the same proof, the premise widened and its callees
      on their `…Cdn` forms where the argument is the top regex or a non-look subterm of it. */
  lemma EndpointTopLookFrameRegsCdn(
    ast: R.regex, re: R.regex, crv: CP.FCompiled, str: string,
    ov: LOr.OracleView, th: AI.Thread, ncap: int, nlook: int, nquant: int)
    requires crv == CP.FFullCompilation(ast)
    requires re == R.lazy_prefix(ast)
    requires LookBodiesPlusGateRE(re)   // (G3a) the weak gate (was LooksNoNulledPlusRE)
    requires T.TransWf(re)   // (G3a) for FrameEntryOkFromTables' plus table
    requires NR.NestedFragmentCdnRE(re)
    requires PIV.CapUnique(re) && PIV.QuantUnique(re) && LTB.LookUnique(re)
    requires LTB.LookTablesOk(re, crv) && LTB.LidsWellNested(re)
    requires forall x: nat :: x in LTB.LookIds(re) ==> 1 <= x <= R.max_lookaround(ast)
    requires ncap >= 0 && nlook >= 0 && nquant >= 0
    requires WinRegsOk(ast, re, crv, str, ov, th, ncap, nlook, nquant)
    ensures var res := AI.FLookLoop(crv, str, 1, R.max_lookaround(ast),
                                    th.capture_regs, th.look_regs, th.quant_regs, ov);
            TopLookFrameO(re, res.1, th.look_regs)
  {
    reveal TopLookFrameO();
    LookRowsStaticCdn(ast, re, crv);
    RowsAvoidFromTablesCdn(ast, re, crv);   // (G3a) later rows never name a row's outside-look quantifiers
    reveal WinRegsOk();
    var maxlook := R.max_lookaround(ast);
    {
      var S := PIV.CaptureRegsSet(PIV.CapIdsInLooks(re));
      var Slook := LookIdSet(re);
      var c := th.capture_regs;
      var l := th.look_regs;
      var q := th.quant_regs;
      assert CM.ThreadRegsWf(th, ncap, nlook, nquant);
      NI.TopLookIdsIn(re);
      forall lz: nat | lz in NI.TopLookIds(re)
        ensures AI.get_idx(AI.FLookLoop(crv, str, 1, maxlook, c, l, q, ov).1.a_clk, lz as int)
             == AI.get_idx(l.a_clk, lz as int)
                && AReg.get_cp(AI.FLookLoop(crv, str, 1, maxlook, c, l, q, ov).1, lz as int)
                   == AReg.get_cp(l, lz as int)
      {
        assert forall l1: int, la1: R.lookaround, b1: R.regex ::
            1 <= l1 <= maxlook && LTB.LookEntryOk(crv, l1, la1, b1) ==> (lz as int) !in LookIdSet(b1)
        by {
          forall l1: int, la1: R.lookaround, b1: R.regex |
            1 <= l1 <= maxlook && LTB.LookEntryOk(crv, l1, la1, b1)
            ensures (lz as int) !in LookIdSet(b1)
          {
            LookEntryOnlyReal(ast, crv, l1, la1, b1);
            var pre := R.Re_quant(R.NonNullable, 0, R.CountedQuant(0, None, false), R.Re_character(R.Dot));
            assert re == R.Re_con(pre, ast);
            assert LTB.LookIds(re) == LTB.LookIds(ast);
            NI.LookBodyOfTablesTie(re, crv, l1 as nat);
            var laT: R.lookaround :| LTB.LookEntryOk(crv, l1, laT, NI.LookBodyOfRE(re, l1 as nat));
            assert b1 == NI.LookBodyOfRE(re, l1 as nat);
            NI.TopLookNotNested(re, lz, l1 as nat);
            if (lz as int) in LookIdSet(b1) {
              var x: nat :| x in LTB.LookIds(b1) && (x as int) == lz as int;
              assert x == lz;
            }
          }
        }
        FLookLoopTopLookClkStableFull(crv, str, 1, maxlook, lz as int, c, l, q, ov, S, Slook, ncap, nlook, nquant);
        FLookLoopTopLookCpStableFull(crv, str, 1, maxlook, lz as int, c, l, q, ov, S, Slook, ncap, nlook, nquant);
      }
    }
  }

  /** (G5a-1 P5b) The narrow form, as a corollary of `EndpointTopLookFrameRegsCdn`. */
  lemma EndpointTopLookFrameRegs(
    ast: R.regex, re: R.regex, crv: CP.FCompiled, str: string,
    ov: LOr.OracleView, th: AI.Thread, ncap: int, nlook: int, nquant: int)
    requires crv == CP.FFullCompilation(ast)
    requires re == R.lazy_prefix(ast)
    requires LookBodiesPlusGateRE(re)   // (G3a) the weak gate (was LooksNoNulledPlusRE)
    requires T.TransWf(re)   // (G3a) for FrameEntryOkFromTables' plus table
    requires NR.NestedFragmentRE(re)
    requires PIV.CapUnique(re) && PIV.QuantUnique(re) && LTB.LookUnique(re)
    requires LTB.LookTablesOk(re, crv) && LTB.LidsWellNested(re)
    requires forall x: nat :: x in LTB.LookIds(re) ==> 1 <= x <= R.max_lookaround(ast)
    requires ncap >= 0 && nlook >= 0 && nquant >= 0
    requires WinRegsOk(ast, re, crv, str, ov, th, ncap, nlook, nquant)
    ensures var res := AI.FLookLoop(crv, str, 1, R.max_lookaround(ast),
                                    th.capture_regs, th.look_regs, th.quant_regs, ov);
            TopLookFrameO(re, res.1, th.look_regs)
  {
    NR.NarrowIsCdn(re);
    hide *;   // the wide premises are this lemma's own: match by name
    EndpointTopLookFrameRegsCdn(ast, re, crv, str, ov, th, ncap, nlook, nquant);
  }
}
