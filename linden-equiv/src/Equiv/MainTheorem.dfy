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
  lemma LookBodyLeafOpenSub(rer: LW.RegExpRecord, lk: L.Lookaround, r1: L.Regex, tlk: LT.Tree,
                            gm: LG.GroupMap, inp: LC.Input, sub: seq<LT.Leaf>, S: set<LG.GroupId>)
    requires tlk == FU.ComputeTr(rer, [LS.Areg(r1)], inp, LG.Empty, L.LkDir(lk))
    requires EL.NoLkBrL(r1) && EL.PikeLkRegex(r1)
    requires S == (set g | g in L.DefGroups(r1))
    requires forall g :: g in gm && g in S ==> gm[g].endIdx.Some?   // reused body groups are CLOSED
    requires sub == LT.TreeLeaves(tlk, gm, inp, L.LkDir(lk))
    requires |sub| > 0
    requires L.Positivity(lk)
    requires L.DefGroups(r1) != [] ==> L.LkDir(lk) == WP.Forward
    ensures OpenOf(sub[0].1) <= OpenOf(gm)
    ensures forall g :: g in sub[0].1 ==> g in gm || g in S
    ensures forall g :: g in sub[0].1 && g in S ==> sub[0].1[g].endIdx.Some?   // look closed its captures
  {
    var dir := L.LkDir(lk);
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
      assert L.DefGroups(r1) == [] && S == {};   // contrapositive of the fragment requires
      // GmConfinedLeaves with S == {}: sub[0].1 agrees with gm everywhere.
    }
    forall g | g in sub[0].1 ensures g in gm || g in S {}
    // S groups are never open in sub[0].1 (OpenOf(sub[0].1) <= OpenOf(gm), and gm's S
    // groups are closed), so a present S group is closed.
    forall g | g in sub[0].1 && g in S ensures sub[0].1[g].endIdx.Some? {
      assert g !in OpenOf(gm);
      assert g !in OpenOf(sub[0].1);
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
              assert EL.NoLkBrL(r1) && EL.PikeLkRegex(r1) && (L.DefGroups(r1) != [] ==> dir == WP.Forward) by {
                if L.Positivity(lk) && dir == WP.Forward { NoLkBrImpliesPikeLk(r1); }
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
    // L3a: the checked tree `tstar` is gate-transparent, so it agrees with the
    // capture-folding spec tree `t` only OUTSIDE the inside-look groups `S`. The
    // inside-look groups are reconstructed by `FLookLoop` (§4a frame + value-lift).
    var S := LL.LkBodyGroups(T.Translate(re));
    // CURRENT fragment: lookaround bodies are capture-free, so S == {} and the
    // reframe collapses to full FirstLeaf agreement (L1/L2). The value-lift/P1/P2
    // machinery is staged for when the fragment is widened for capturing lookaheads.
    LkBodyGroupsEmpty(re);
    assert S == {};
    assert LL.LkActsInS([LS.Areg(T.Translate(re))], S) by {
      LL.LkBodyGroupsConfines(T.Translate(re), S);
      assert LL.LkBodiesInS(T.Translate(re), S);
    }
    LL.ComputeTrLkConfined(rer, [LS.Areg(T.Translate(re))], inp, LG.Empty, WP.Forward, S);  // LkConfinedTree(t, S)
    var tstar := ATR.ActionsTreeRepRE(rer, qm, [LS.Areg(T.Translate(re))], code, 0, inp, BS.CannotExit, t, S);
    assert TR.TreeRepRE(qm, tstar, code, 0, inp, false);
    LL.LeavesAgreeAtOutsideEmpty(tstar, t, inp);            // S == {} -> full LeavesAgreeAt
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

  /** L3a §4a — the capture FRAME for the whole FLookLoop pass: the final capture
      bank agrees with the initial one OUTSIDE `S`, where `S` bounds every matched
      body's own capture registers (`CaptureRegs(body) <= S`). Positive lookAHEADs
      may CAPTURE (their writes stay within `CaptureRegs(body) <= S`); every other
      flavour is capture-free and leaves the bank untouched. The look bank is
      unchanged throughout (look-free bodies). Instantiate `S` with the registers of
      `CapIdsInLooks(mainast)`, disjoint by `CaptureRegsDisjoint` from the outside-look
      groups the main filter reads — so the OUTER match is preserved (the inner
      groups carry the reconstruction, whose VALUES are §4b). */
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
        && ((la.Lookbehind? || la.NegLookbehind? || la.NegLookahead?) ==> NR.CaptureFreeRE(body))
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
          && ((la.Lookbehind? || la.NegLookbehind? || la.NegLookahead?) ==> NR.CaptureFreeRE(body));
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
          // la.Lookbehind?, body capture-free -> the replay is the identity
          var inits := AI.FInitState(bytecode, cp, cap, lk, qt, 0, AI.cp_context(cp, str, dir));
          ReplayFrames(bytecode, str, inits, ov, dir, lookcdn, cap, lk, qt, la, body);
          var (res0, ovx) := AI.FFindMatch(bytecode, str, inits, ov, dir, lookcdn);
          assert result.Some? ==> res0.Some?;
          if result.Some? {
            var th := res0.value;
            assert QuantRegsFinal(th);
            FNulledPlusIdentity(lookast, th.capture_regs, th.look_regs, th.quant_regs,
                                crv.f_plus_bc, str, ovx, dir);
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
        && ((la.Lookbehind? || la.NegLookbehind? || la.NegLookahead?) ==> NR.CaptureFreeRE(body))
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
          && ((la.Lookbehind? || la.NegLookbehind? || la.NegLookahead?) ==> NR.CaptureFreeRE(body));
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
          ReplayFrames(bytecode, str, inits, ov, dir, lookcdn, cap, lk, qt, la, body);
          var (res0, ovx) := AI.FFindMatch(bytecode, str, inits, ov, dir, lookcdn);
          assert result.Some? ==> res0.Some?;
          if result.Some? {
            var th := res0.value;
            assert QuantRegsFinal(th);
            FNulledPlusIdentity(lookast, th.capture_regs, th.look_regs, th.quant_regs,
                                crv.f_plus_bc, str, ovx, dir);
            assert nqt == th.quant_regs;
            assert CM.RegsAgreeOutside(nqt, qt, LKC.QIdsInt(body));   // ReplayFrames
            CM.RegsAgreeOutsideWeaken(nqt, qt, LKC.QIdsInt(body), Sq);
          }
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

  /** For the CURRENT (capture-free-lookaround) fragment, the inside-look group set
      is EMPTY: every lookaround body is capture-free, so its translation is
      group-free. So the L3a checked-tree reframe at `S = LkBodyGroups(Translate(re))`
      collapses to `S = {}` -- recovering full `FirstLeaf(tstar) == FirstLeaf(t)`.
      (When the fragment is widened for capturing lookaheads, `S` becomes non-empty
      and the value-lift/P1/P2 machinery takes over.) */
  lemma LkBodyGroupsEmpty(re: R.regex)
    requires T.TransWf(re) && NR.LookBehindFragmentRE(re)
    ensures LL.LkBodyGroups(T.Translate(re)) == {}
    decreases re
  {
    match re
    case Re_alt(r1, r2) => LkBodyGroupsEmpty(r1); LkBodyGroupsEmpty(r2);
    case Re_con(r1, r2) => LkBodyGroupsEmpty(r1); LkBodyGroupsEmpty(r2);
    case Re_quant(_, _, _, r1) => LkBodyGroupsEmpty(r1);
    case Re_capture(_, r1) => LkBodyGroupsEmpty(r1);
    case Re_lookaround(lid, la, r1) =>
      OS.TranslateGroupFree(r1);                    // GroupFreeL(Translate(r1)) (body capture-free + look-free)
      LL.GroupFreeLkBodyEmpty(T.Translate(r1));     // LkBodyGroups(Translate(r1)) == {} && DefGroups == []
    case _ =>
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
    && (if 0 <= l < |crv.f_look_types| then crv.f_look_types[l] else R.Lookahead).Lookahead?
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
    var bc := CP.compile_to_bytecode(body);
    var cdn := if 0 <= l < |crv.f_look_cdns| then crv.f_look_cdns[l] else [];
    AI.FFindMatch(bc, str, AI.FInitState(bc, cp, AReg.init_regs(ncap), AReg.init_regs(nlook),
                  AReg.init_regs(nquant), 0, AI.cp_context(cp, str, LAnc.Forward)), ov, LAnc.Forward, cdn).0
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

  /** The per-lid input-context health `ReplayCapAgreeFresh`/`FreshMatchWf` need. */
  ghost predicate cp_ctx_ok(crv: CP.FCompiled, str: string, lk: AReg.Regs, l: int)
    requires AReg.get_cp(lk, l).Some?
  {
    var cp := AReg.get_cp(lk, l).value;
    0 <= cp <= |str| && AI.cp_context(cp, str, LAnc.Forward).nextchar == AI.get_char(str, cp)
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
        && ((la.Lookbehind? || la.NegLookbehind? || la.NegLookahead?) ==> NR.CaptureFreeRE(body))
    // lookahead-only: every matched CAPTURING lid is a positive forward lookahead
    requires forall l: int :: (lid <= l <= maxlook && AReg.get_cp(lk, l).Some?
        && AI.capture_type(if 0 <= l < |crv.f_look_types| then crv.f_look_types[l] else R.Lookahead)) ==>
      (if 0 <= l < |crv.f_look_types| then crv.f_look_types[l] else R.Lookahead).Lookahead?
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
      |res.0.a_cp| == ncap && |res.0.a_clk| == ncap
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
          && ((la.Lookbehind? || la.NegLookbehind? || la.NegLookahead?) ==> NR.CaptureFreeRE(body));
        assert looktype == la;
        assert la.Lookahead?;                    // lookahead-only requires
        assert body == VBody(crv, lid);
        var bytecode := AI.get_code_v(crv.f_look_capture_bc, lid);
        var dir := AI.capture_direction(looktype);
        var lookcdn := if 0 <= lid < |crv.f_look_cdns| then crv.f_look_cdns[lid] else [];
        var lookast := if 0 <= lid < |crv.f_look_ast| then crv.f_look_ast[lid] else R.Re_empty;
        assert dir == LAnc.Forward && CP.capture_regex(la, body) == body;
        assert bytecode == CP.compile_to_bytecode(body) && lookast == body;
        var (result, ov1) := AI.FFindMatchPlus(bytecode, lookast, crv.f_plus_bc, str, ov, dir,
                                               cp, cap, lk, qt, 0, lookcdn);
        var capN := if result.None? then cap else result.value.capture_regs;
        var lkN := if result.None? then lk else result.value.look_regs;
        var qtN := if result.None? then qt else result.value.quant_regs;
        assert res == AI.FLookLoop(crv, str, next, maxlook, capN, lkN, qtN, ov1);

        NR.PlusIsLookBehindFragmentRE(body);
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
            && ((la2.Lookbehind? || la2.NegLookbehind? || la2.NegLookahead?) ==> NR.CaptureFreeRE(body2))
        by {
          forall l: int | next <= l <= maxlook && AReg.get_cp(lkN, l).Some?
            ensures exists la2: R.lookaround, body2: R.regex ::
              LTB.LookEntryOk(crv, l, la2, body2)
              && NR.LookFreeRE(body2) && NR.PlusFragmentRE(body2)
              && PIV.CapUnique(body2) && PIV.QuantUnique(body2)
              && PIV.CaptureRegs(body2) <= Sp
              && (forall q: nat :: q in PIV.QuantIds(body2) ==> q in PIV.QuantIdsInLooks(mainast))
              && ((la2.Lookbehind? || la2.NegLookbehind? || la2.NegLookahead?) ==> NR.CaptureFreeRE(body2))
          {
            assert AReg.get_cp(lk, l).Some?;
            var la2: R.lookaround, body2: R.regex :|
              LTB.LookEntryOk(crv, l, la2, body2)
              && NR.LookFreeRE(body2) && NR.PlusFragmentRE(body2)
              && PIV.CapUnique(body2) && PIV.QuantUnique(body2)
              && PIV.CaptureRegs(body2) <= S
              && (forall q: nat :: q in PIV.QuantIds(body2) ==> q in PIV.QuantIdsInLooks(mainast))
              && ((la2.Lookbehind? || la2.NegLookbehind? || la2.NegLookahead?) ==> NR.CaptureFreeRE(body2));
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
      }
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

  /** L3a `FBuildCapture` unfold: exposes the RECONSTRUCTED caps directly (no
      `FLookLoopFilterFrame` "unchanged" simplification -- for capturing
      lookaheads the pass DOES move the answer). Purely definitional: the answer
      IS `filter_reset` of the `FLookLoop` result. Feeds the L3a extraction, which
      proves that result's inside-look groups carry the spec `LkResult` values. */
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
    assert LkClosedInGm(LG.Empty, [LS.Areg(T.Translate(re))]);   // Empty has no groups
    SpecRegexOuterLkDisjoint(raw);
    assert T.Translate(re) == LES.SpecRegex(raw);
    assert OuterLkDisjoint([LS.Areg(T.Translate(re))]);
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
