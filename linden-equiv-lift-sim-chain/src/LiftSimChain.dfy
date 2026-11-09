// L3a — THE LIFT: the standalone parallel simulation VM ↔ machine B.
//
// SCAFFOLD (2026-08-02): definitions are REAL and resolve; the lemmas are
// BODILESS — each carries a FILL note naming its template and ingredients.
// Fill order (historical; `TtLkSameTree` was superseded by the quotient
// `ETreeRepLkDeterm` and its dead admitted statement removed 2026-08-25): TtLkSameTree → GateStepValue → LiftInit → LiftAdvanceEpsilon →
// LiftConsume → LiftFindMatch → LiftEndpoint. Verify per-symbol as you go
// (bodiless lemmas verify trivially and warn; the warnings disappear as
// bodies land).
//
// WHAT THIS PROVES, once filled: the VM run induces a valid LK-aware
// PikeTree trace (PikeTreeLk) on the SPEC tree t, whose states pair with the
// VM's — per thread, the B-side group map `gmt` carries the t-side
// accumulated captures, tied OUTSIDE S to GmOfLive(thread regs) and INSIDE S
// to the fresh body replay at the thread's own a_cp[l]. At the end,
// PTL.PikeTreeLkComputesFirstLeaf pins B's best to FirstLeaf(t, inp), so the
// winner's leaf values — inside-look groups INCLUDED — equal the engine's
// reconstruction with no position theorem and no leaf-occurrence reasoning.
//
// WHY NO A-MACHINE / NO PikeSimRE COMPOSITION: B's own correctness layer
// (PtsPreservationLk) already handles priority and memoization soundness on
// the t side, so the lift only has to produce LEGAL B steps mirroring VM
// behavior; the one genuinely shared obligation with the old sim is the
// processed↔seen pairing (SeenRepLk below, mirrored from SeenInclusionRE).
// The existing sim and its files stay UNTOUCHED.
//
// GRANULARITY: the ClockMono frame trio (FAdvanceEpsilon / FConsume /
// FFindMatch parallel induction) — the shape that went first-try five times
// in this campaign (FFindMatchLookCpOk, LookClkSet, LookOracleTrue,
// FFindMatchLookFrame, FFindMatchCapWriteFrame). LiftAdvanceEpsilon's
// per-instruction cases mirror those recursions; the CheckOracle case is the
// only one that STEPS B through a gate, and its value content is
// GateStepValue = the proven keystone LkReplayMatchesSpec at cp = s1.cp.

/** The lift: a per-thread pairing between the RegElk VM and the LK-aware
    PikeTree machine on the SPEC tree, whose group-map tie carries the
    reconstructed inside-look capture values. Scaffold — lemmas are bodiless. */
module LindenElkLiftSimChain {
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
  import L = Regex
  import LS = Semantics
  import BS = BooleanSemantics
  import WP = WarblrePrimitives
  import LW = WarblreRegExpRecord
  import LOr = Oracle
  import LAnc = Anchors
  import LCdn = Cdn
  import PT = PikeTree
  import SS = SeenSets
  import AR = LindenElkActionsRep
  import EL = LindenElkEntryLk
  import WO = LindenElkWalkOk
  import ATR = LindenElkActionsTreeRep
  import PIV = LindenElkPikeInv
  import CM = LindenElkClockMono
  import PTL = LindenElkPikeTreeLk
  import M = LindenElkMain
  import LBK = LindenLookBehindKeystone
  import FG = LindenElkFlipGate
  import FC = LindenElkFlipClosed
  import FST = LindenElkFlipStatics
  import FK = LindenElkFlipKeystone
  import FO = LindenElkFlipOracle
  import FD = LindenElkFlipDisc
  import FM = LindenElkFlipMirror
  import FR = LindenElkFlipRev
  import TRM = LindenTreeResMirror
  import BGM = LindenBackGmMirror
  import LBV = LindenLookBehindValue
  import BV = LindenElkBackValue
  import SD = LindenSpanDuality
  import CD = LindenCloseDisc
  import OS = LindenElkOracleSpec
  import OB = LindenElkOracleBuild
  import OBr = LindenElkOracleBridge
  import ORc = LindenElkOracleReach
  import MIR = LindenElkMirror
  import OBV = LindenElkOracleBridgeV
  import ODV = LindenElkOracleDecompV
  import OAV = LindenElkOracleAcceptV
  import OMV = LindenElkOracleMirrorV
  import T = LindenElkTranslate
  import RC = Charclasses
  import LL = LindenElkLookLeaves
  import LFU = FunctionalUtils
  import FS = FunctionalSemantics
  import SSx = StrictSuffix
  import LN = WarblreNumeric
  import PSM = LindenElkPikeSim
  import RL = LindenElkRegsLaws
  import LKC = LindenElkLookCapture
  import OE = LindenElkOracleEntry
  import LES = LindenElkSpec
  import WOE = LindenElkWalkOkEntry
  import WkE = LindenElkWalkOkEntry
  import TT = LindenElkTreeThread
  import NUL = LindenElkNullable
  import CE = LindenElkCheckErase
  import TREP = LindenElkTreeRep
  import LTB = LindenElkLookTables
  import NI = LindenElkNestInv
  import CW = LindenElkCinWalk
  import opened LindenElkLiftSimCore
  import opened LindenElkLiftSimOracle

  /** `WalkPairLk` rebuilt on `EL.PikeLkActionsRec` (recursive fragment). */
  ghost predicate WalkPairLkRec(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                                tb: LT.Tree, gmt: LG.GroupMap, pc: nat, ea: bool)
    decreases RB.size(code) - pc
  {
    (pc < RB.size(code) && NR.GetPcRE(code, pc) == Some(RB.BeginLoop)
     && WalkPairLkRec(rer, qm, code, inp, tb, gmt, pc + 1, false))
    // (§2.5b F-c) the see-through also crosses the nulled-exit stamp (a plain
    // Reset on the B side); the walk tree is ENGINE-SHAPED (`CW.BoolTreeLkX`)
    || (pc < RB.size(code)
        && exists q: int ::
          (NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(q, false))
           || NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(q, true)))
          && q in qm.quants
          && tb.GroupActionT? && tb.g == LG.Reset(qm.quants[q])
          && WalkPairLkRec(rer, qm, code, inp, tb.t,
                           LG.GMUpdate(tb.g, LC.Idx(inp), gmt), pc + 1, ea))
    || (exists acts: LS.Actions, b: BS.LoopBool ::
          AR.ActionsRepL(rer, qm, acts, code, pc)
          && EL.PikeLkActionsRec(acts)
          && ATR.EaOf(b) == ea
          && CW.BoolTreeLkX(rer, acts, inp, b, tb)
          && GateAheadClear(acts, gmt)
          && WalkDefsOk(acts))
  }

  /** `ThreadRepLkNested` (the `GmtTieInside`-free per-thread tie) on
      `WalkPairLkRec`. */
  ghost predicate ThreadRepLkRec(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code,
                                 inp: LC.Input, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
                                 S: set<LG.GroupId>, tb: LT.Tree, gmt: LG.GroupMap, th: AI.Thread,
                                 ncap: int, nlook: int, nquant: int) {
    th.pc >= 0
    && WalkPairLkRec(rer, qm, code, inp, tb, gmt, th.pc as nat, th.exit_allowed)
    && GmtTieOutside(re, th, gmt, S)
  }

  /** `ThreadRepLkCNested` riding `ThreadRepLkRec`. */
  ghost predicate ThreadRepLkCRec(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code,
                                  inp: LC.Input, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
                                  S: set<LG.GroupId>, tcan: LT.Tree, gmt: LG.GroupMap, th: AI.Thread,
                                  ncap: int, nlook: int, nquant: int) {
    th.pc >= 0
    && TreeRepLkRE(rer, qm, code, inp, tcan, th.pc as nat, th.exit_allowed)
    && exists traw: LT.Tree ::
      CE.ProgErase(traw) == CE.ProgErase(tcan)
      && ThreadRepLkRec(rer, qm, re, code, inp, crv, str, ov, S, traw, gmt, th, ncap, nlook, nquant)
  }

  /** `ActiveRepLkCNested` riding `ThreadRepLkCRec`. */
  ghost predicate ActiveRepLkCRec(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code,
                                  inp: LC.Input, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
                                  S: set<LG.GroupId>, tl: seq<(LT.Tree, LG.GroupMap)>, vl: seq<AI.Thread>,
                                  ncap: int, nlook: int, nquant: int)
    decreases tl
  {
    (|tl| == 0 && |vl| == 0)
    || (|tl| > 0 && |vl| > 0
        && ThreadRepLkCRec(rer, qm, re, code, inp, crv, str, ov, S, tl[0].0, tl[0].1, vl[0],
                           ncap, nlook, nquant)
        && ActiveRepLkCRec(rer, qm, re, code, inp, crv, str, ov, S, tl[1..], vl[1..],
                           ncap, nlook, nquant))
  }

  /** `BlockedRepLkCNested` with its raw erasure witness on `WalkPairLkRec`. */
  ghost predicate BlockedRepLkCRec(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code,
                                   inp: LC.Input, nextinp: LC.Input, crv: CP.FCompiled, str: string,
                                   ov: LOr.OracleView, S: set<LG.GroupId>,
                                   tl: seq<(LT.Tree, LG.GroupMap)>, bl: seq<(AI.Thread, RC.char_expectation)>,
                                   ncap: int, nlook: int, nquant: int)
    decreases tl
  {
    (|tl| == 0 && |bl| == 0)
    || (|tl| > 0 && |bl| > 0
        && bl[0].0.pc >= 0
        && TreeRepLkRE(rer, qm, code, nextinp, tl[0].0, (bl[0].0.pc + 1) as nat, true)
        && (exists traw: LT.Tree ::
              CE.ProgErase(traw) == CE.ProgErase(tl[0].0)
              && WalkPairLkRec(rer, qm, code, nextinp, traw, tl[0].1, (bl[0].0.pc + 1) as nat, true))
        && GmtTieOutside(re, bl[0].0, tl[0].1, S)
        && BlockedRepLkCRec(rer, qm, re, code, inp, nextinp, crv, str, ov, S, tl[1..], bl[1..],
                            ncap, nlook, nquant))
  }

  /** `LiftInvNested` on the `*Rec` pairings (`ActiveRepLkCRec`,
      `BlockedRepLkCRec`, `BestTieLkNested`). (D3) The look-path carriers are the
      TOP-LEVEL-restricted `*Top` variants: at a nested gate only the top-level
      gate lid is stamped, so the inner-lid obligations of the full carriers are
      unsatisfiable at depth >= 2. Confined to the `*Rec` tier (the depth-1/`Nested`
      `LiftInv`/`LiftInvNested` keep the full carriers). */
  ghost predicate LiftInvRec(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code,
                             crv: CP.FCompiled, str: string, ov: LOr.OracleView, S: set<LG.GroupId>,
                             bst: PT.PikeTreeState, vms: AI.VmState,
                             ncap: int, nlook: int, nquant: int) {
    match bst
    case PTS_final(bbest) => BestTieLkNestedTop(rer, re, crv, str, ov, S, bbest, vms.bestmatch, ncap, nlook, nquant)
    case PTS(inp, bactive, bbest, bblocked, bseen) =>
      0 <= vms.cp <= |str|
      && inp == PIV.InpOfCp(str, vms.cp)
      && PIV.ContextOkRE(str, vms.cp, vms.context)
      && ActiveRepLkCRec(rer, qm, re, code, inp, crv, str, ov, S, bactive, vms.active, ncap, nlook, nquant)
      && (forall nextinp :: LC.AdvanceInput(inp, WP.Forward) == Some(nextinp) ==>
                              BlockedRepLkCRec(rer, qm, re, code, inp, nextinp, crv, str, ov, S, bblocked,
                                               PIV.MatchingBlocked(LC.Reverse(vms.blocked), inp), ncap, nlook, nquant))
      && (LC.AdvanceInput(inp, WP.Forward) == None ==> bblocked == [])
      && LookNestRepCTop(re, S, bactive, vms.active)
      && (LC.AdvanceInput(inp, WP.Forward).Some? ==>
            LookNestRepBTop(re, S, bblocked, PIV.MatchingBlocked(LC.Reverse(vms.blocked), inp)))
      && LookNestBackRepCTop(re, crv, str, ov, S, bactive, vms.active, ncap, nlook, nquant)
      && (LC.AdvanceInput(inp, WP.Forward).Some? ==>
            LookNestBackRepBTop(re, crv, str, ov, S, bblocked,
                                PIV.MatchingBlocked(LC.Reverse(vms.blocked), inp), ncap, nlook, nquant))
      // (R2 DEEP CARRIER) the deep-carrier rep predicates, threaded PARALLEL to
      // the direct `LookNestBackRepCTop`/`…BTop` (same shape, `SubFirstLeafAt`
      // landed set), so the best-match tie can carry `LookNestBackTTopDeep`.
      && LookNestBackRepCTopDeep(rer, re, crv, str, ov, S, bactive, vms.active, ncap, nlook, nquant)
      && (LC.AdvanceInput(inp, WP.Forward).Some? ==>
            LookNestBackRepBTopDeep(rer, re, crv, str, ov, S, bblocked,
                                    PIV.MatchingBlocked(LC.Reverse(vms.blocked), inp), ncap, nlook, nquant))
      && BestTieLkNestedTop(rer, re, crv, str, ov, S, bbest, vms.bestmatch, ncap, nlook, nquant)
      && SeenRepLk(rer, qm, code, inp, bseen, vms.processed,
                   PIV.HdTreeOf(bactive), PIV.HeadPcOf(vms.active))
      && IsblockedRepLk(rer, qm, code, inp, bseen, vms.isblocked)
      && LL.OracleOkSuffix(rer, qm, inp)
  }

  /** The star iteration arm's invariants across the unfold: `GateAheadClear`
      by the Reset itself (the fresh body pendings sit inside the reset set;
      the tail's survive the domain shrink), the carrier by `WalkDefsOkUnfold`. */
  lemma StarArmInvariants(acts: LS.Actions, r1: L.Regex, q': L.Regex, chk: LS.Action,
                          gm: LG.GroupMap, gidl: LG.GroupSet)
    requires |acts| > 0 && acts[0].Areg? && acts[0].r.Quantified? && acts[0].r.r1 == r1
    requires q'.Quantified? && q'.r1 == r1
    requires chk.Acheck?
    requires gidl == L.DefGroups(r1)
    requires GateAheadClear(acts, gm)
    requires WalkDefsOk(acts)
    ensures GateAheadClear([LS.Areg(r1), chk, LS.Areg(q')] + acts[1..], LG.GMReset(gidl, gm))
    ensures WalkDefsOk([LS.Areg(r1), chk, LS.Areg(q')] + acts[1..])
  {
    var cont := acts[1..];
    var na := [LS.Areg(r1), chk, LS.Areg(q')] + cont;
    var gm2 := LG.GMReset(gidl, gm);
    WalkDefsOkUnfold(acts, r1, q', [chk]);
    assert [LS.Areg(r1)] + [chk] + [LS.Areg(q')] + cont == na;
    assert GateAheadClear(na, gm2) by {
      forall lk2: L.Lookaround, rr: L.Regex | GatePending(na, lk2, rr)
        ensures forall gg :: gg in L.DefGroups(rr) ==> gg !in gm2
      {
        var j :| 0 <= j < |na| && na[j].Areg? && RegexTopGate(na[j].r, lk2, rr);
        if j == 0 {
          assert na[0] == LS.Areg(r1) && RegexTopGate(r1, lk2, rr);
          RegexTopGateSubDefs(r1, lk2, rr);
          var SRR := set gx | gx in L.DefGroups(rr);
          var SR1 := set gx | gx in L.DefGroups(r1);
          assert SRR <= SR1;
          forall gg | gg in L.DefGroups(rr) ensures gg !in gm2 {
            assert gg in SRR;
            assert gg in SR1;
            assert gg in L.DefGroups(r1);
            assert gm2 == gm - (set gx | gx in gidl);
            assert gg in (set gx | gx in gidl);
          }
        } else if j == 1 {
          assert !na[1].Areg?;
          assert false;
        } else if j == 2 {
          assert na[2] == LS.Areg(q') && !RegexTopGate(q', lk2, rr);
          assert false;
        } else {
          assert na[j] == cont[j - 3];
          assert GatePending(cont, lk2, rr) by {
            assert cont[j - 3].Areg? && RegexTopGate(cont[j - 3].r, lk2, rr);
          }
          GatePendingTail(acts, lk2, rr);
          forall gg | gg in L.DefGroups(rr) ensures gg !in gm2 {
            assert gg !in gm;
          }
        }
      }
    }
  }

  /** THE CARRIER. */
  ghost predicate WalkDefsOk(acts: LS.Actions) {
    M.NoDupSeq(TopLkDefsListActs(acts))                                        // C1
    && (forall i | 0 <= i < |acts| && acts[i].Areg? ::
          M.NoDupSeq(L.DefGroups(acts[i].r)))                                  // C2
    && QuantsClearActs(acts)                                                   // C3
  }

  /** Carrier tail: drop the head. */
  lemma WalkDefsOkTail(acts: LS.Actions)
    requires |acts| > 0 && WalkDefsOk(acts)
    ensures WalkDefsOk(acts[1..])
  {
    NoDupTopLkTail(acts);
    forall i | 0 <= i < |acts[1..]| && acts[1..][i].Areg?
      ensures M.NoDupSeq(L.DefGroups(acts[1..][i].r))
              && QuantsRightClear(acts[1..][i].r, TopLkSetActs(acts[1..][i + 1..]))
    {
      assert acts[1..][i] == acts[i + 1];
      assert acts[1..][i + 1..] == acts[i + 2..];
    }
  }

  /** Carrier across the `Sequence` two-head expand: the TopLk list is the SAME
      sequence, the head's C3 clause unfolds DEFINITIONALLY into the two new
      heads' clauses. */
  lemma WalkDefsOkSeqExpand(acts: LS.Actions, r1: L.Regex, r2: L.Regex)
    requires |acts| > 0 && acts[0] == LS.Areg(L.Sequence(r1, r2))
    requires WalkDefsOk(acts)
    ensures WalkDefsOk([LS.Areg(r1), LS.Areg(r2)] + acts[1..])
  {
    var cont := acts[1..];
    var na := [LS.Areg(r1), LS.Areg(r2)] + cont;
    assert acts == [acts[0]] + cont;
    // C1: same TopLk sequence
    TopLkDefsListActsCons(acts[0], cont);
    TopLkDefsListActsCons(LS.Areg(r1), [LS.Areg(r2)] + cont);
    TopLkDefsListActsCons(LS.Areg(r2), cont);
    assert na == [LS.Areg(r1)] + ([LS.Areg(r2)] + cont);
    assert TopLkDefsList(L.Sequence(r1, r2)) == TopLkDefsList(r1) + TopLkDefsList(r2);
    assert TopLkDefsListActs(na)
        == TopLkDefsList(r1) + (TopLkDefsList(r2) + TopLkDefsListActs(cont));
    assert TopLkDefsList(r1) + (TopLkDefsList(r2) + TopLkDefsListActs(cont))
        == (TopLkDefsList(r1) + TopLkDefsList(r2)) + TopLkDefsListActs(cont);
    assert TopLkDefsListActs(na) == TopLkDefsListActs(acts);
    // C2: split the head's NoDup
    assert M.NoDupSeq(L.DefGroups(L.Sequence(r1, r2)));
    assert L.DefGroups(L.Sequence(r1, r2)) == L.DefGroups(r1) + L.DefGroups(r2);
    M.NoDupConcat(L.DefGroups(r1), L.DefGroups(r2));
    // C3
    assert QuantsRightClear(L.Sequence(r1, r2), TopLkSetActs(cont));
    assert TopLkSetActs([LS.Areg(r2)] + cont)
        == (set g | g in TopLkDefsList(r2)) + TopLkSetActs(cont) by {
      forall g ensures g in TopLkSetActs([LS.Areg(r2)] + cont)
                  <==> g in ((set gx | gx in TopLkDefsList(r2)) + TopLkSetActs(cont)) {
      }
    }
    forall i | 0 <= i < |na| && na[i].Areg?
      ensures M.NoDupSeq(L.DefGroups(na[i].r))
              && QuantsRightClear(na[i].r, TopLkSetActs(na[i + 1..]))
    {
      if i == 0 {
        assert na[0] == LS.Areg(r1) && na[1..] == [LS.Areg(r2)] + cont;
      } else if i == 1 {
        assert na[1] == LS.Areg(r2) && na[2..] == cont;
      } else {
        assert na[i] == cont[i - 2] == acts[i - 1];
        assert na[i + 1..] == cont[i - 1..] == acts[i..];
      }
    }
  }

  /** Carrier across the `Group` expand (`[Areg rb, Aclose gid] + cont`). */
  lemma WalkDefsOkGroupExpand(acts: LS.Actions, gid: LG.GroupId, rb: L.Regex)
    requires |acts| > 0 && acts[0] == LS.Areg(L.Group(gid, rb))
    requires WalkDefsOk(acts)
    ensures WalkDefsOk([LS.Areg(rb), LS.Aclose(gid)] + acts[1..])
  {
    var cont := acts[1..];
    var na := [LS.Areg(rb), LS.Aclose(gid)] + cont;
    assert acts == [acts[0]] + cont;
    // C1: Group is TopLk-transparent, Aclose contributes []
    TopLkDefsListActsCons(acts[0], cont);
    TopLkDefsListActsCons(LS.Areg(rb), [LS.Aclose(gid)] + cont);
    TopLkDefsListActsCons(LS.Aclose(gid), cont);
    assert na == [LS.Areg(rb)] + ([LS.Aclose(gid)] + cont);
    assert TopLkDefsList(L.Group(gid, rb)) == [gid] + TopLkDefsList(rb);
    assert TopLkDefsListActs(acts)
        == ([gid] + TopLkDefsList(rb)) + TopLkDefsListActs(cont);
    assert ([gid] + TopLkDefsList(rb)) + TopLkDefsListActs(cont)
        == [gid] + (TopLkDefsList(rb) + TopLkDefsListActs(cont));
    M.NoDupConcat([gid], TopLkDefsList(rb) + TopLkDefsListActs(cont));
    assert TopLkDefsListActs(na) == TopLkDefsList(rb) + TopLkDefsListActs(cont);
    // C2
    assert M.NoDupSeq(L.DefGroups(L.Group(gid, rb)));
    assert L.DefGroups(L.Group(gid, rb)) == [gid] + L.DefGroups(rb);
    M.NoDupConcat([gid], L.DefGroups(rb));
    // C3
    assert QuantsRightClear(L.Group(gid, rb), TopLkSetActs(cont));
    assert TopLkSetActs([LS.Aclose(gid)] + cont) == TopLkSetActs(cont) by {
      forall g ensures g in TopLkSetActs([LS.Aclose(gid)] + cont) <==> g in TopLkSetActs(cont) {
      }
    }
    forall i | 0 <= i < |na| && na[i].Areg?
      ensures M.NoDupSeq(L.DefGroups(na[i].r))
              && QuantsRightClear(na[i].r, TopLkSetActs(na[i + 1..]))
    {
      if i == 0 {
        assert na[0] == LS.Areg(rb) && na[1..] == [LS.Aclose(gid)] + cont;
      } else if i == 1 {
      } else {
        assert na[i] == cont[i - 2] == acts[i - 1];
        assert na[i + 1..] == cont[i - 1..] == acts[i..];
      }
    }
  }

  /** Carrier at the single-action entry (`[Areg rex]`). */
  lemma WalkDefsOkEntry(rex: L.Regex)
    requires M.NoDupSeq(L.DefGroups(rex))
    ensures WalkDefsOk([LS.Areg(rex)])
  {
    var acts := [LS.Areg(rex)];
    TopLkDefsListActsCons(LS.Areg(rex), []);
    assert TopLkDefsListActs(acts) == TopLkDefsList(rex) + [] == TopLkDefsList(rex);
    TopLkNoDupFromDefGroups(rex);
    assert acts[1..] == [];
    assert TopLkSetActs([]) == {};
    QuantsRightClearFromNoDup(rex, {});
  }

  /** THE UNFOLD: carrier across a quantifier body-copy expansion
      `[Areg(Quantified(.., r1))] + cont  ⟶  [Areg r1] ++ mid ++ [Areg q'] + cont`
      stated for the two shapes the walk produces (`mid` = `[]` for the min>0
      forced copy, `[Acheck(inp0)]` for the star/backfork iteration arm). The
      unfolding node's OWN C3 clause supplies the body-vs-tail freshness; C2
      supplies the body's structural NoDup; the residual `q'` is TopLk-opaque. */
  lemma WalkDefsOkUnfold(acts: LS.Actions, r1: L.Regex, q': L.Regex, mid: LS.Actions)
    requires |acts| > 0 && acts[0].Areg? && acts[0].r.Quantified? && acts[0].r.r1 == r1
    requires q'.Quantified? && q'.r1 == r1
    requires mid == [] || (|mid| == 1 && mid[0].Acheck?)
    requires WalkDefsOk(acts)
    ensures WalkDefsOk([LS.Areg(r1)] + mid + [LS.Areg(q')] + acts[1..])
  {
    var cont := acts[1..];
    var na := [LS.Areg(r1)] + mid + [LS.Areg(q')] + cont;
    assert acts == [acts[0]] + cont;
    // structural facts from the folded head
    assert M.NoDupSeq(L.DefGroups(acts[0].r));
    assert L.DefGroups(acts[0].r) == L.DefGroups(r1);
    assert QuantsRightClear(acts[0].r, TopLkSetActs(cont));
    assert forall g :: g in L.DefGroups(r1) ==> g !in TopLkSetActs(cont);
    // the TopLk view of the unfolded list: TopLk(r1) ++ TopLk(cont)
    var tail1 := mid + [LS.Areg(q')] + cont;
    var tail2 := [LS.Areg(q')] + cont;
    assert na == [LS.Areg(r1)] + tail1;
    TopLkDefsListActsCons(LS.Areg(r1), tail1);
    TopLkDefsListActsCons(LS.Areg(q'), cont);
    assert TopLkDefsList(q') == [];
    assert TopLkDefsListActs(tail2) == TopLkDefsListActs(cont);
    if |mid| == 1 {
      assert tail1 == [mid[0]] + tail2;
      TopLkDefsListActsCons(mid[0], tail2);
      assert TopLkDefsListActs(tail1) == TopLkDefsListActs(tail2);
    } else {
      assert tail1 == tail2;
    }
    assert TopLkDefsListActs(na) == TopLkDefsList(r1) + TopLkDefsListActs(cont);
    // C1: NoDup(TopLk(r1)) structural + disjoint from TopLk(cont) via the C3 clause
    TopLkNoDupFromDefGroups(r1);
    TopLkDefsListSubDefGroups(r1);
    NoDupTopLkTail(acts);
    forall i, j | 0 <= i < |TopLkDefsList(r1)| && 0 <= j < |TopLkDefsListActs(cont)|
      ensures TopLkDefsList(r1)[i] != TopLkDefsListActs(cont)[j]
    {
      if TopLkDefsList(r1)[i] == TopLkDefsListActs(cont)[j] {
        var g := TopLkDefsList(r1)[i];
        assert g in L.DefGroups(r1);
        assert g in TopLkSetActs(cont);
        assert false;
      }
    }
    M.NoDupFromDisjoint(TopLkDefsList(r1), TopLkDefsListActs(cont));
    // C2 + C3 per index
    var koff := |mid| + 2;   // na[koff + k] == cont[k]
    forall i | 0 <= i < |na| && na[i].Areg?
      ensures M.NoDupSeq(L.DefGroups(na[i].r))
              && QuantsRightClear(na[i].r, TopLkSetActs(na[i + 1..]))
    {
      if i == 0 {
        assert na[0] == LS.Areg(r1) && na[1..] == tail1;
        assert TopLkSetActs(tail1) == TopLkSetActs(cont) by {
          forall g ensures g in TopLkSetActs(tail1) <==> g in TopLkSetActs(cont) {}
        }
        QuantsRightClearFromNoDup(r1, TopLkSetActs(cont));
      } else if i < koff - 1 {
        // mid slot (Acheck): not Areg — vacuous
        assert na[i] == mid[i - 1];
      } else if i == koff - 1 {
        assert na[i] == LS.Areg(q') && na[i + 1..] == cont;
        assert L.DefGroups(q') == L.DefGroups(r1);
        forall g | g in L.DefGroups(q') ensures g !in TopLkSetActs(cont) {}
      } else {
        assert na[i] == cont[i - koff] == acts[i - koff + 1];
        assert na[i + 1..] == cont[i - koff + 1..] == acts[i - koff + 2..];
      }
    }
  }

  /** Carrier across a `Disjunction` arm choice: the other arm's TopLk block is
      DROPPED (a sub-concat of the C1 NoDup); C2/C3 select the arm's halves. */
  lemma WalkDefsOkDisjArm(acts: LS.Actions, r1: L.Regex, r2: L.Regex, arm: L.Regex)
    requires |acts| > 0 && acts[0] == LS.Areg(L.Disjunction(r1, r2))
    requires WalkDefsOk(acts)
    requires arm == r1 || arm == r2
    ensures WalkDefsOk([LS.Areg(arm)] + acts[1..])
  {
    var cont := acts[1..];
    var na := [LS.Areg(arm)] + cont;
    assert acts == [acts[0]] + cont;
    TopLkDefsListActsCons(acts[0], cont);
    TopLkDefsListActsCons(LS.Areg(arm), cont);
    var A1 := TopLkDefsList(r1);
    var A2 := TopLkDefsList(r2);
    var C := TopLkDefsListActs(cont);
    assert TopLkDefsList(L.Disjunction(r1, r2)) == A1 + A2;
    assert TopLkDefsListActs(acts) == (A1 + A2) + C;
    assert (A1 + A2) + C == A1 + (A2 + C);
    M.NoDupConcat(A1, A2 + C);
    M.NoDupConcat(A2, C);
    var AA := TopLkDefsList(arm);
    assert TopLkDefsListActs(na) == AA + C;
    // C1: NoDup(AA + C) — AA is one of A1/A2; disjointness from C in both cases
    forall i, j | 0 <= i < |AA| && 0 <= j < |C| ensures AA[i] != C[j] {
      if AA[i] == C[j] {
        var g := AA[i];
        if arm == r1 {
          assert g in A1 && g in (A2 + C);
          assert g in (set gx | gx in A1) * (set gx | gx in A2 + C);
        } else {
          assert g in A2 && g in C;
          assert g in (set gx | gx in A2) * (set gx | gx in C);
        }
      }
    }
    M.NoDupFromDisjoint(AA, C);
    // C2: split the head's DefGroups NoDup
    assert M.NoDupSeq(L.DefGroups(L.Disjunction(r1, r2)));
    assert L.DefGroups(L.Disjunction(r1, r2)) == L.DefGroups(r1) + L.DefGroups(r2);
    M.NoDupConcat(L.DefGroups(r1), L.DefGroups(r2));
    // C3: the head clause's arm conjunct (Disjunction arms share R); shifts
    assert QuantsRightClear(L.Disjunction(r1, r2), TopLkSetActs(cont));
    forall i | 0 <= i < |na| && na[i].Areg?
      ensures M.NoDupSeq(L.DefGroups(na[i].r))
              && QuantsRightClear(na[i].r, TopLkSetActs(na[i + 1..]))
    {
      if i == 0 {
        assert na[0] == LS.Areg(arm) && na[1..] == cont;
      } else {
        assert na[i] == cont[i - 1] == acts[i];
        assert na[i + 1..] == cont[i..] == acts[i + 1..];
      }
    }
  }

  /** Fuel-induction workhorse (LK-aware mirror of `PS.ComputePikeSubtree`):
      running `ComputeTree` on a backref-free action stack yields a
      `PikeSubtreeLk` tree — the only forbidden shape (`ReadBackRef`) comes
      solely from `Backreference`, which `NoBackrefActions` rules out. The
      LK/LKFail cases are now PRODUCED (not contradictions); the lookaround BODY
      is never recursed into (`PikeSubtreeLk` leaves it unconstrained), only the
      continuation. */
  lemma ComputePikeSubtreeLk(rer: LW.RegExpRecord, act: LS.Actions, inp: LC.Input,
                             gm: LG.GroupMap, dir: WP.Direction, fuel: nat, t: LT.Tree)
    requires NoBackrefActions(act)
    requires FS.ComputeTree(rer, act, inp, gm, dir, fuel) == Some(t)
    ensures PTL.PikeSubtreeLk(t)
    decreases fuel
  {
    var f := fuel - 1;
    if |act| == 0 {
    } else {
      var cont := act[1..];
      NoBackrefActionsTail(act);            // NoBackrefActions(cont)
      assert act == [act[0]] + cont;
      NoBackrefActionsCons(act[0], cont);   // NoBackrefAction(act[0])
      match act[0]
      case Acheck(strcheck) =>
        if SSx.IsStrictSuffix(inp, strcheck, dir) {
          var sub := FS.ComputeTree(rer, cont, inp, gm, dir, f);
          if sub.Some? { ComputePikeSubtreeLk(rer, cont, inp, gm, dir, f, sub.value); }
        }
      case Aclose(gid) =>
        var gm' := LG.GMClose(LC.Idx(inp), gid, gm);
        var sub := FS.ComputeTree(rer, cont, inp, gm', dir, f);
        if sub.Some? { ComputePikeSubtreeLk(rer, cont, inp, gm', dir, f, sub.value); }
      case Areg(r) =>
        assert NoBackrefRegex(r);
        match r
        case Epsilon =>
          ComputePikeSubtreeLk(rer, cont, inp, gm, dir, f, t);
        case Character(cd) =>
          match LC.ReadChar(rer, cd, inp, dir) {
            case None =>
            case Some(pair) =>
              var sub := FS.ComputeTree(rer, cont, pair.1, gm, dir, f);
              if sub.Some? { ComputePikeSubtreeLk(rer, cont, pair.1, gm, dir, f, sub.value); }
          }
        case Disjunction(r1, r2) =>
          NoBackrefActionsCons(LS.Areg(r1), cont);
          NoBackrefActionsCons(LS.Areg(r2), cont);
          var s1 := FS.ComputeTree(rer, [LS.Areg(r1)] + cont, inp, gm, dir, f);
          var s2 := FS.ComputeTree(rer, [LS.Areg(r2)] + cont, inp, gm, dir, f);
          if s1.Some? { ComputePikeSubtreeLk(rer, [LS.Areg(r1)] + cont, inp, gm, dir, f, s1.value); }
          if s2.Some? { ComputePikeSubtreeLk(rer, [LS.Areg(r2)] + cont, inp, gm, dir, f, s2.value); }
        case Sequence(r1, r2) =>
          var na := LS.SeqList(r1, r2, dir) + cont;
          assert NoBackrefActions(na) by {
            match dir
            case Forward =>
          assert na == [LS.Areg(r1)] + ([LS.Areg(r2)] + cont);
          NoBackrefActionsCons(LS.Areg(r2), cont);
          NoBackrefActionsCons(LS.Areg(r1), [LS.Areg(r2)] + cont);
            case Backward =>
          assert na == [LS.Areg(r2)] + ([LS.Areg(r1)] + cont);
          NoBackrefActionsCons(LS.Areg(r1), cont);
          NoBackrefActionsCons(LS.Areg(r2), [LS.Areg(r1)] + cont);
          }
          var sub := FS.ComputeTree(rer, na, inp, gm, dir, f);
          if sub.Some? { ComputePikeSubtreeLk(rer, na, inp, gm, dir, f, sub.value); }
        case Quantified(greedy, min, delta, r1) =>
          var gidl := L.DefGroups(r1);
          if min > 0 {
            var quant := L.Quantified(greedy, min - 1, delta, r1);
            var na := [LS.Areg(r1), LS.Areg(quant)] + cont;
            var gm' := LG.GMReset(gidl, gm);
            assert NoBackrefActions(na) by {
              assert na == [LS.Areg(r1)] + ([LS.Areg(quant)] + cont);
              NoBackrefActionsCons(LS.Areg(quant), cont);
              NoBackrefActionsCons(LS.Areg(r1), [LS.Areg(quant)] + cont);
            }
            var sub := FS.ComputeTree(rer, na, inp, gm', dir, f);
            if sub.Some? { ComputePikeSubtreeLk(rer, na, inp, gm', dir, f, sub.value); }
          } else if delta == LN.NN(0) {
            var sub := FS.ComputeTree(rer, cont, inp, gm, dir, f);
            if sub.Some? { ComputePikeSubtreeLk(rer, cont, inp, gm, dir, f, sub.value); }
          } else {
            var quant := L.Quantified(greedy, 0, FS.NoiPred(delta), r1);
            var na := [LS.Areg(r1), LS.Acheck(inp), LS.Areg(quant)] + cont;
            var gm' := LG.GMReset(gidl, gm);
            assert NoBackrefActions(na) by {
              assert na == [LS.Areg(r1)] + ([LS.Acheck(inp)] + ([LS.Areg(quant)] + cont));
              NoBackrefActionsCons(LS.Areg(quant), cont);
              NoBackrefActionsCons(LS.Acheck(inp), [LS.Areg(quant)] + cont);
              NoBackrefActionsCons(LS.Areg(r1), [LS.Acheck(inp)] + ([LS.Areg(quant)] + cont));
            }
            var siter := FS.ComputeTree(rer, na, inp, gm', dir, f);
            var sskip := FS.ComputeTree(rer, cont, inp, gm, dir, f);
            if siter.Some? { ComputePikeSubtreeLk(rer, na, inp, gm', dir, f, siter.value); }
            if sskip.Some? { ComputePikeSubtreeLk(rer, cont, inp, gm, dir, f, sskip.value); }
          }
        case Group(gid, r1) =>
          var na := [LS.Areg(r1), LS.Aclose(gid)] + cont;
          var gm' := LG.GMOpen(LC.Idx(inp), gid, gm);
          assert NoBackrefActions(na) by {
            assert na == [LS.Areg(r1)] + ([LS.Aclose(gid)] + cont);
            NoBackrefActionsCons(LS.Aclose(gid), cont);
            NoBackrefActionsCons(LS.Areg(r1), [LS.Aclose(gid)] + cont);
          }
          var sub := FS.ComputeTree(rer, na, inp, gm', dir, f);
          if sub.Some? { ComputePikeSubtreeLk(rer, na, inp, gm', dir, f, sub.value); }
        case LookaroundR(lk, r1) =>
          // THE LK/LKFail case: the body treelk is NOT recursed into
          // (PikeSubtreeLk leaves it unconstrained); only the continuation.
          var slk := FS.ComputeTree(rer, [LS.Areg(r1)], inp, gm, L.LkDir(lk), f);
          match slk {
            case None =>
            case Some(treelk) =>
              match LS.LkResult(lk, treelk, gm, inp) {
                case Some(gmlk) =>
                  var sc := FS.ComputeTree(rer, cont, inp, gmlk, dir, f);
                  if sc.Some? { ComputePikeSubtreeLk(rer, cont, inp, gmlk, dir, f, sc.value); }
                case None =>   // t == LKFail(lk, treelk); PikeSubtreeLk trivially
              }
          }
        case AnchorR(a) =>
          if LS.AnchorSatisfied(rer, a, inp) {
            var sub := FS.ComputeTree(rer, cont, inp, gm, dir, f);
            if sub.Some? { ComputePikeSubtreeLk(rer, cont, inp, gm, dir, f, sub.value); }
          }
        case Backreference(gid) =>   // NoBackrefRegex(r) is false here — vacuous
    }
  }

  // ==========================================================================
  // ---- (K) THE COMPOSITE SIM (thread-anchored — audit 2026-08-03) ------------
  //
  // ARCHITECTURE (settled by the #5 engine-connection audit): ride the PROVEN
  // machine-A simulation `PSM.PikeInvFullRE` for ALL VM mechanics (queue,
  // priority, seen, blocked, loop/BeginLoop via its `TreeRepRE` `tr_begin`), and
  // carry the LK-machine `ptsB` (`PTL.PikeTreeStepLk`, on the spec tree `t`)
  // ALONGSIDE — its trees paired to the VM THREADS via the standalone
  // `ThreadRepLk`/`ActiveRepLk`, NOT to the tstar trees.
  //
  // WHY THREAD-ANCHORED (not the dead §K tree↔tree route): `ActionsTreeRepFRE`
  // erases the LK head when building tstar, so `ta` (tstar) can NEVER recover
  // `tb` (LK) via `LeavesAgreeAtOutside` — that pairing is dead. BUT both
  // `PIV.ActiveRepRE(ta, vms.active)` (inside `PikeInvFullRE`) and
  // `ActiveRepLk(tb, vms.active)` are INDEX-WISE over the SAME `vms.active`, so
  // the VM thread is the shared anchor: carry PikeInvFullRE(ptsA,vms) AND
  // ThreadRepLk(tb,thread) as independent companions of one VM — no ta↔tb link.
  //
  // KEY STRUCTURAL FACTS:
  //  * `PikeInvFullRE(ptsA, vms)` relates the VM to `ptsA` (gate-transparent
  //    tstar), index-wise `vms.active[i]` ↔ `ptsA.active[i]` via `TreeRepRE`.
  //  * `PTL.PikeTreeStepLk` has the SAME case shape (skip/final/nextchar/active/
  //    match/blocked) as the tstar `PikeTreeStep` — so ptsA and ptsB step in
  //    LOCKSTEP with the same VM worklist. `LiftStepC` mirrors the PROVEN
  //    `PSM.InvariantPreservationRE` (ptsA side) with the per-instruction tb
  //    cores (ptsB side); `L3aCompositeClose` mirrors `PSM.FindMatchSimRE`.
  //  * `GateStepValue` (verified) preserves `GmtTieInside` across a passing gate
  //    (the crux; `ThreadRepLkStepCheckOracle` integrates it). Position tie is
  //    automatic — `ptsA.inp == ptsB.inp == InpOfCp(str, vms.cp)`.
  //  * Endpoint: `PTL.PikeTreeLkComputesFirstLeaf` ⟹ ptsB.best == FirstLeaf(t)
  //    (inside tie via `BestTieLk`); `PIV.BestMatchRE` gives the outside tie.

  // (K-pairing) DELETED `LiftPairC`/`ActivePairC` — the tstar-tree↔LK-tree
  // `LeavesAgreeAtOutside` pairing (the DEAD §K route: `ActionsTreeRepFRE` erases
  // the LK head, so `ta` can't recover `tb`). The composite now uses the THREAD-
  // anchored `ThreadRepLk`/`ActiveRepLk` directly (see `LiftInvC`): each ptsB tree
  // pairs with the VM thread, never with the tstar tree, so no ta↔tb link is
  // needed. Position tie stays automatic — `LiftInvC` pins `ptsA.inp == ptsB.inp
  // == InpOfCp(str, vms.cp)`, so the VM's `a_cp[l] := cp` at `CheckOracle(l)` IS
  // the gate's input position that `GateStepValue` consumes.

  // ---- (c′) the CANONICAL pairing layer (2026-08-07) -----------------------
  //
  // Machine B RUNS the PLANTED canonical tree `tcan` (built at entry by
  // `ActionsTreeRepLkRE`): unique per `(pc, ea)` by `TreeRepLkDetermRE` — the
  // skip-lockstep key — and stutter-discriminating, so `PikeTreeLk`'s
  // exact-tree memo works unchanged. The VALUE layer (all the proven
  // `ThreadRepLkStep*`/`WalkPairLkAt*` cores, on raw `BoolTreeLk` trees)
  // pairs the SAME thread through an ERASURE EXISTENTIAL: a raw witness
  // `traw` with `ProgErase(traw) == ProgErase(tcan)`. The planted guards are
  // leaf- and gm-transparent (`ProgEraseLeavesEq`; `Progress` is a pure
  // stutter in `TreeBfsStepLk`), so the raw walk's value conclusions
  // transport to `tcan` verbatim.
  //
  // WHY the existential (and NOT `WalkPairLk(tcan)` directly): `tcan` is NOT
  // `BoolTreeLk`-representable in general — `BoolTreeLk`'s forced-copy rule
  // (`Quantified min>0`) fixes the guardless continuation
  // `[Areg(r1), Areg(Quantified(min-1,..))]+cont`, so the planted
  // first-arrival `Progress` at a do-while's backward fork (e.g. in `a+`)
  // exists under NO action stack. Erasure is exactly the quotient on which
  // the two layers agree.

  /** (THE FINAL ENDPOINT — both inside-`S` directions supplied by the descent
      wrappers) `L3aEndpointAssemblyNestedFull` with the AllBodyTopFeeds/forward-
      existential/reverse residuals REPLACED by the two facts the completed
      machinery produces: (F) forward membership+VALUE (`ForwardMemberOne`,
      quantified) and (R) reverse membership (`ReverseCDeepFull`). Everything
      else — outside-`S`, frames, the NormGm assembly — is verbatim. */
  lemma L3aEndpointAssemblyNestedFull2(
    ast: R.regex, re: R.regex, crv: CP.FCompiled, code: RB.code, endl: nat,
    str: string, ov: LOr.OracleView, S: set<LG.GroupId>,
    thread: AI.Thread, leaf: LT.Leaf, ncap: int, nlook: int, nquant: int,
    rer: LW.RegExpRecord, qm: AR.QMap, t: LT.Tree, inp: LC.Input)
    requires T.TransWf(re) && NR.NestedFragmentRE(re) && EL.NegBehindLookFreeRE(re)
    requires PIV.CapUnique(re) && PIV.QuantUnique(re) && LTB.LookUnique(re)
    requires S == PIV.CapIdsInLooks(re)
    requires R.max_lookaround(re) == R.max_lookaround(ast)
    requires M.OrderedGm(leaf.1)
    requires LT.FirstLeaf(t, inp) == Some(leaf)
    requires BestTieLkNestedTop(rer, re, crv, str, ov, S, Some(leaf), Some(thread), ncap, nlook, nquant)
    // ---- the recon frames + wf (verbatim (a)) ----
    requires var res := AI.FLookLoop(crv, str, 1, R.max_lookaround(ast),
                                     thread.capture_regs, thread.look_regs, thread.quant_regs, ov);
             (forall k: int :: k !in PIV.CaptureRegsSet(PIV.CapIdsInLooks(re)) ==>
                                 AI.get_idx(AReg.as_arrays(res.0).0, k) == AI.get_idx(AReg.as_arrays(thread.capture_regs).0, k)
                                 && AI.get_idx(AReg.as_arrays(res.0).1, k) == AI.get_idx(AReg.as_arrays(thread.capture_regs).1, k))
             && (forall q: nat :: q in PIV.QuantIdsOutsideLooks(re) ==>
                                    AI.get_idx(AReg.as_arrays(res.2).1, q as int) == AI.get_idx(AReg.as_arrays(thread.quant_regs).1, q as int))
             && CM.ThreadRegsWf(AI.Thread(thread.pc, res.0, res.1, res.2, thread.exit_allowed), ncap, nlook, nquant)
             && M.QuantRegsFinal(AI.Thread(thread.pc, res.0, res.1, res.2, thread.exit_allowed))
    // ---- (F) FORWARD membership + VALUE (per leaf-present g, Norm-form) ----
    requires var res := AI.FLookLoop(crv, str, 1, R.max_lookaround(ast),
                                     thread.capture_regs, thread.look_regs, thread.quant_regs, ov);
             forall g: LG.GroupId :: g in S && g in leaf.1 ==>
                                       g in PIV.GmOfLive(re, res.0, res.1, res.2)
                                       && PIV.NormRange(leaf.1[g]) == PIV.NormRange(PIV.GmOfLive(re, res.0, res.1, res.2)[g])
    // ---- (R) REVERSE membership ----
    requires var res := AI.FLookLoop(crv, str, 1, R.max_lookaround(ast),
                                     thread.capture_regs, thread.look_regs, thread.quant_regs, ov);
             forall g: LG.GroupId :: g in S && g in PIV.GmOfLive(re, res.0, res.1, res.2) ==> g in leaf.1
    ensures var res := AI.FLookLoop(crv, str, 1, R.max_lookaround(ast),
                                    thread.capture_regs, thread.look_regs, thread.quant_regs, ov);
            leaf.1 == PIV.NormGm(PIV.GmOfLive(re, res.0, res.1, res.2))
            && CM.ThreadRegsWf(AI.Thread(thread.pc, res.0, res.1, res.2, thread.exit_allowed), ncap, nlook, nquant)
            && M.QuantRegsFinal(AI.Thread(thread.pc, res.0, res.1, res.2, thread.exit_allowed))
  {
    var res := AI.FLookLoop(crv, str, 1, R.max_lookaround(ast),
                            thread.capture_regs, thread.look_regs, thread.quant_regs, ov);
    var leafgm := leaf.1;
    var synthetic := AI.Thread(thread.pc, res.0, res.1, res.2, thread.exit_allowed);

    // ---- inside-S FORWARD (b): membership + value, NormRange collapses on the
    //      ORDERED leaf value ----
    assert forall g: LG.GroupId :: g in S && g in leafgm ==>
                                     g in PIV.GmOfLive(re, res.0, res.1, res.2)
                                     && leafgm[g] == PIV.NormRange(PIV.GmOfLive(re, res.0, res.1, res.2)[g])
    by {
      forall g: LG.GroupId | g in S && g in leafgm
        ensures g in PIV.GmOfLive(re, res.0, res.1, res.2)
                && leafgm[g] == PIV.NormRange(PIV.GmOfLive(re, res.0, res.1, res.2)[g])
      {
        assert g in PIV.GmOfLive(re, res.0, res.1, res.2)
               && PIV.NormRange(leafgm[g]) == PIV.NormRange(PIV.GmOfLive(re, res.0, res.1, res.2)[g]);
        // OrderedGm: NormRange is the identity on leafgm[g]
        assert leafgm[g].endIdx.Some? ==> leafgm[g].startIdx <= leafgm[g].endIdx.value;
        assert PIV.NormRange(leafgm[g]) == leafgm[g];
      }
    }

    // ---- OUTSIDE S (verbatim from L3aEndpointAssemblyNestedFull) ----
    assert GmtTieOutside(re, thread, leafgm, S);            // from BestTieLkNestedTop
    var gmThread := PIV.GmOfLive(re, thread.capture_regs, thread.look_regs, thread.quant_regs);
    var gmBest := PIV.GmOfLive(re, thread.capture_regs, res.1, thread.quant_regs);
    PIV.GmOfLiveLookIndepNested(re, thread.capture_regs, thread.look_regs, res.1, thread.quant_regs);
    M.LkBodyGroupsEqCapIdsInLooks(re);
    assert forall g: nat :: g !in LL.LkBodyGroups(T.Translate(re)) ==>
                              (g in leafgm <==> g in gmBest) && (g in leafgm ==> leafgm[g] == gmBest[g])
    by {
      forall g: nat | g !in LL.LkBodyGroups(T.Translate(re))
        ensures (g in leafgm <==> g in gmBest) && (g in leafgm ==> leafgm[g] == gmBest[g])
      {
        assert g !in S;
        assert (g in leafgm <==> g in gmThread) && (g in leafgm ==> leafgm[g] == gmThread[g]);
        assert (g in gmThread <==> g in gmBest) && (g in gmThread ==> gmThread[g] == gmBest[g]);
      }
    }
    OutsideLookValueBridgeNested(re, thread.capture_regs, res.0, res.1, thread.quant_regs, res.2,
                                 gmBest, leafgm);
    assert forall g: LG.GroupId :: g !in S ==>
                                     (g in leafgm <==> g in PIV.GmOfLive(re, res.0, res.1, res.2))
                                     && (g in leafgm ==> leafgm[g] == PIV.GmOfLive(re, res.0, res.1, res.2)[g]);

    // ---- assemble ----
    assert synthetic.look_regs == res.1;
    L3aValueBridgeNested(re, synthetic, leafgm, res.0, res.2, S);
    assert leafgm == PIV.NormGm(PIV.GmOfLive(re, res.0, res.1, res.2));
  }

  lemma WalkPairLkAtJmpRec(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                           tb: LT.Tree, gmt: LG.GroupMap, pc: nat, ea: bool, x: int)
    requires WalkPairLkRec(rer, qm, code, inp, tb, gmt, pc, ea)
    requires NR.GetPcRE(code, pc) == Some(RB.Jmp(x))
    ensures x >= 0 && WalkPairLkRec(rer, qm, code, inp, tb, gmt, x as nat, ea)
  {
    var acts: LS.Actions, b: BS.LoopBool :|
      AR.ActionsRepL(rer, qm, acts, code, pc)
      && EL.PikeLkActionsRec(acts)
      && ATR.EaOf(b) == ea
      && CW.BoolTreeLkX(rer, acts, inp, b, tb)
      && GateAheadClear(acts, gmt)
      && WalkDefsOk(acts);
    ActionsRepLThruJmp(rer, qm, acts, code, pc, x);
  }

  lemma WalkPairLkAtConsumeCoreRec(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                                   tb: LT.Tree, gm: LG.GroupMap, pc: nat, b: BS.LoopBool,
                                   acts: LS.Actions, ce: RC.char_expectation)
    requires AR.ActionsRepL(rer, qm, acts, code, pc)
    requires EL.PikeLkActionsRec(acts)
    requires CW.BoolTreeLkX(rer, acts, inp, b, tb)
    requires NR.GetPcRE(code, pc) == Some(RB.Consume(ce))
    requires GateAheadClear(acts, gm)
    requires WalkDefsOk(acts)
    ensures tb.Read? || tb == LT.Mismatch
    ensures tb.Read? ==> exists nextinp ::
                AR.ReadCharE(ce, inp) == Some((tb.c, nextinp))
                && WalkPairLkRec(rer, qm, code, nextinp, tb.t, gm, pc + 1, true)
    ensures tb == LT.Mismatch ==> AR.ReadCharE(ce, inp) == None
    decreases ATR.MsizeA(acts)
  {
    var g := ATR.EaOf(b);
    var pcmid: nat :| AR.ActionRepL(rer, qm, acts[0], code, pc, pcmid) && AR.ActionsRepL(rer, qm, acts[1..], code, pcmid);
    EL.PikeLkActionsRecTail(acts);
    assert acts == [acts[0]] + acts[1..];
    EL.PikeLkActionsRecConsIff(acts[0], acts[1..]);
    var cont := acts[1..];
    match acts[0]
    case Acheck(_) =>   // pins EndLoop / backward Fork — not Consume
    case Aclose(_) =>   // pins SetRegisterToCP — not Consume
    case Areg(r0) =>
      assert EL.PikeLkRegexRec(r0);
      match r0
      case Epsilon =>
        assert pcmid == pc;
        assert CW.BoolTreeLkX(rer, cont, inp, b, tb);
        assert ATR.MsizeA(cont) < ATR.MsizeA(acts);
        GateAheadClearTail(acts, gm);
        WalkDefsOkTail(acts);
        WalkPairLkAtConsumeCoreRec(rer, qm, code, inp, tb, gm, pc, b, cont, ce);
      case Sequence(r1, r2) =>
        assert acts[0] == LS.Areg(L.Sequence(r1, r2));
        assert AR.NfaRepL(rer, qm, L.Sequence(r1, r2), code, pc, pcmid);
        var e1: nat :| AR.NfaRepL(rer, qm, r1, code, pc, e1) && AR.NfaRepL(rer, qm, r2, code, e1, pcmid);
        var na := [LS.Areg(r1), LS.Areg(r2)] + cont;
        assert na == [LS.Areg(r1)] + ([LS.Areg(r2)] + cont);
        AR.ActionsRepLCons(rer, qm, LS.Areg(r2), cont, code, e1, pcmid);
        AR.ActionsRepLCons(rer, qm, LS.Areg(r1), [LS.Areg(r2)] + cont, code, pc, e1);
        assert AR.ActionsRepL(rer, qm, na, code, pc);
        assert EL.PikeLkActionsRec(na) by {
          EL.PikeLkActionsRecConsIff(LS.Areg(r2), cont);
          EL.PikeLkActionsRecConsIff(LS.Areg(r1), [LS.Areg(r2)] + cont);
        }
        assert CW.BoolTreeLkX(rer, na, inp, b, tb);
        assert LS.ActionsRegexSize(acts) == RegSz(r1) + RegSz(r2) + 1 + LS.ActionsRegexSize(cont);
        assert LS.ActionsRegexSize(na) == RegSz(r1) + RegSz(r2) + LS.ActionsRegexSize(cont);
        assert ATR.MsizeA(na) < ATR.MsizeA(acts);
        GateAheadClearSeqExpand(acts, r1, r2, gm);
        WalkDefsOkSeqExpand(acts, r1, r2);
        WalkPairLkAtConsumeCoreRec(rer, qm, code, inp, tb, gm, pc, b, na, ce);
      case Quantified(greedy, min, delta, r1) =>
        if min == 0 && delta == LN.NN(0) {
          assert acts[0] == LS.Areg(L.Quantified(greedy, 0, LN.NN(0), r1));
          assert AR.NfaRepL(rer, qm, L.Quantified(greedy, 0, LN.NN(0), r1), code, pc, pcmid);
          var em: nat :| AR.NfaRepMinL(rer, qm, 0, r1, code, pc, em)
                         && AR.NfaRepOptL(rer, qm, 0, greedy, r1, code, em, pcmid);
          NfaRepMinLHeadPin(rer, qm, 0, r1, code, pc, em);
          NfaRepOptLHeadPin(rer, qm, 0, greedy, r1, code, em, pcmid);
          assert pcmid == pc;
          assert AR.ActionsRepL(rer, qm, cont, code, pc);
          assert CW.BoolTreeLkX(rer, cont, inp, b, tb);
          assert ATR.MsizeA(cont) < ATR.MsizeA(acts);
          GateAheadClearTail(acts, gm);
          WalkDefsOkTail(acts);
          WalkPairLkAtConsumeCoreRec(rer, qm, code, inp, tb, gm, pc, b, cont, ce);
        } else {
          assert acts[0] == LS.Areg(L.Quantified(greedy, min, delta, r1));
          assert AR.NfaRepL(rer, qm, L.Quantified(greedy, min, delta, r1), code, pc, pcmid);
          QuantHeadPinsNonConsume(rer, qm, greedy, min, delta, r1, code, pc, pcmid, ce);
        }
      case Character(cd) =>
        assert acts[0] == LS.Areg(L.Character(cd));
        var ce2 :| NR.GetPcRE(code, pc) == Some(RB.Consume(ce2)) && AR.ExpectationMatches(rer, ce2, cd);
        assert ce2 == ce && pcmid == pc + 1;
        AR.ReadAgree(rer, ce, cd, inp);   // ReadCharE(ce, inp) == ReadChar(rer, cd, inp, Forward)
        match LC.ReadChar(rer, cd, inp, WP.Forward) {
          case None =>
            assert tb == LT.Mismatch;
          case Some(pair) =>
            assert tb.Read? && tb.c == pair.0 && CW.BoolTreeLkX(rer, cont, pair.1, BS.CanExit, tb.t);
            assert AR.ActionsRepL(rer, qm, cont, code, pc + 1);
            GateAheadClearTail(acts, gm);
            WalkDefsOkTail(acts);
            assert WalkPairLkRec(rer, qm, code, pair.1, tb.t, gm, pc + 1, true) by {
              assert ATR.EaOf(BS.CanExit) == true;
              assert EL.PikeLkActionsRec(cont);
            }
            assert AR.ReadCharE(ce, inp) == Some((tb.c, pair.1));
        }
      case Disjunction(_, _) =>   // pins Fork — not Consume
      case Group(_, _) =>   // pins SetRegisterToCP — not Consume
      case LookaroundR(_, _) =>   // pins CheckOracle/NegCheckOracle — not Consume
      case AnchorR(_) =>   // pins AnchorAssertion — not Consume
      case Backreference(_) =>   // NfaRepL false
  }

  lemma WalkPairLkAtConsumeRec(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                               tb: LT.Tree, gm: LG.GroupMap, pc: nat, ea: bool, ce: RC.char_expectation)
    requires WalkPairLkRec(rer, qm, code, inp, tb, gm, pc, ea)
    requires NR.GetPcRE(code, pc) == Some(RB.Consume(ce))
    ensures tb.Read? || tb == LT.Mismatch
    ensures tb.Read? ==> exists nextinp ::
                AR.ReadCharE(ce, inp) == Some((tb.c, nextinp))
                && WalkPairLkRec(rer, qm, code, nextinp, tb.t, gm, pc + 1, true)
    ensures tb == LT.Mismatch ==> AR.ReadCharE(ce, inp) == None
  {
    var acts: LS.Actions, b: BS.LoopBool :|
      AR.ActionsRepL(rer, qm, acts, code, pc)
      && EL.PikeLkActionsRec(acts)
      && ATR.EaOf(b) == ea
      && CW.BoolTreeLkX(rer, acts, inp, b, tb)
      && GateAheadClear(acts, gm)
      && WalkDefsOk(acts);
    WalkPairLkAtConsumeCoreRec(rer, qm, code, inp, tb, gm, pc, b, acts, ce);
  }

  lemma WalkPairLkAtNegCheckOracleCoreRec(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                                          tb: LT.Tree, gm: LG.GroupMap, pc: nat, b: BS.LoopBool,
                                          acts: LS.Actions, lid: int)
    requires AR.ActionsRepL(rer, qm, acts, code, pc)
    requires EL.PikeLkActionsRec(acts)
    requires CW.BoolTreeLkX(rer, acts, inp, b, tb)
    requires NR.GetPcRE(code, pc) == Some(RB.NegCheckOracle(lid))
    requires GateAheadClear(acts, gm)
    requires WalkDefsOk(acts)
    ensures lid in qm.looks
    ensures var (lk, r1) := qm.looks[lid];
            var tlk := LFU.ComputeTr(rer, [LS.Areg(r1)], inp, LG.Empty, L.LkDir(lk));
            !AR.PositiveL(lk)
            && (LS.LkResult(lk, tlk, LG.Empty, inp).Some? ==>
                  tb.LK? && tb.lk == lk && tb.tlk == tlk
                  && WalkPairLkRec(rer, qm, code, inp, tb.t, gm, pc + 1, ATR.EaOf(b)))
            && (LS.LkResult(lk, tlk, LG.Empty, inp).None? ==> tb == LT.LKFail(lk, tlk))
    decreases ATR.MsizeA(acts)
  {
    var g := ATR.EaOf(b);
    var pcmid: nat :| AR.ActionRepL(rer, qm, acts[0], code, pc, pcmid) && AR.ActionsRepL(rer, qm, acts[1..], code, pcmid);
    EL.PikeLkActionsRecTail(acts);
    assert acts == [acts[0]] + acts[1..];
    EL.PikeLkActionsRecConsIff(acts[0], acts[1..]);
    var cont := acts[1..];
    match acts[0]
    case Acheck(_) =>   // pins EndLoop / backward Fork — not NegCheckOracle
    case Aclose(_) =>   // pins SetRegisterToCP — not NegCheckOracle
    case Areg(r0) =>
      assert EL.PikeLkRegexRec(r0);
      match r0
      case Epsilon =>
        assert pcmid == pc;
        assert CW.BoolTreeLkX(rer, cont, inp, b, tb);
        assert ATR.MsizeA(cont) < ATR.MsizeA(acts);
        GateAheadClearTail(acts, gm);
        WalkDefsOkTail(acts);
        WalkPairLkAtNegCheckOracleCoreRec(rer, qm, code, inp, tb, gm, pc, b, cont, lid);
      case Sequence(r1, r2) =>
        assert acts[0] == LS.Areg(L.Sequence(r1, r2));
        assert AR.NfaRepL(rer, qm, L.Sequence(r1, r2), code, pc, pcmid);
        var e1: nat :| AR.NfaRepL(rer, qm, r1, code, pc, e1) && AR.NfaRepL(rer, qm, r2, code, e1, pcmid);
        var na := [LS.Areg(r1), LS.Areg(r2)] + cont;
        assert na == [LS.Areg(r1)] + ([LS.Areg(r2)] + cont);
        AR.ActionsRepLCons(rer, qm, LS.Areg(r2), cont, code, e1, pcmid);
        AR.ActionsRepLCons(rer, qm, LS.Areg(r1), [LS.Areg(r2)] + cont, code, pc, e1);
        assert AR.ActionsRepL(rer, qm, na, code, pc);
        assert EL.PikeLkActionsRec(na) by {
          EL.PikeLkActionsRecConsIff(LS.Areg(r2), cont);
          EL.PikeLkActionsRecConsIff(LS.Areg(r1), [LS.Areg(r2)] + cont);
        }
        assert CW.BoolTreeLkX(rer, na, inp, b, tb);
        assert LS.ActionsRegexSize(acts) == RegSz(r1) + RegSz(r2) + 1 + LS.ActionsRegexSize(cont);
        assert LS.ActionsRegexSize(na) == RegSz(r1) + RegSz(r2) + LS.ActionsRegexSize(cont);
        assert ATR.MsizeA(na) < ATR.MsizeA(acts);
        GateAheadClearSeqExpand(acts, r1, r2, gm);
        M.AllDefsActsCons(acts[0], cont);
        M.AllDefsActsCons(LS.Areg(r1), [LS.Areg(r2)] + cont);
        M.AllDefsActsCons(LS.Areg(r2), cont);
        assert L.DefGroups(L.Sequence(r1, r2)) == L.DefGroups(r1) + L.DefGroups(r2);
        assert L.DefGroups(r1) + (L.DefGroups(r2) + M.AllDefsActs(cont))
            == (L.DefGroups(r1) + L.DefGroups(r2)) + M.AllDefsActs(cont);
        assert M.AllDefsActs(na) == M.AllDefsActs(acts);
        WalkDefsOkSeqExpand(acts, r1, r2);
        WalkPairLkAtNegCheckOracleCoreRec(rer, qm, code, inp, tb, gm, pc, b, na, lid);
      case Quantified(greedy, min, delta, r1) =>
        if min == 0 && delta == LN.NN(0) {
          assert acts[0] == LS.Areg(L.Quantified(greedy, 0, LN.NN(0), r1));
          assert AR.NfaRepL(rer, qm, L.Quantified(greedy, 0, LN.NN(0), r1), code, pc, pcmid);
          var em: nat :| AR.NfaRepMinL(rer, qm, 0, r1, code, pc, em)
                         && AR.NfaRepOptL(rer, qm, 0, greedy, r1, code, em, pcmid);
          NfaRepMinLHeadPin(rer, qm, 0, r1, code, pc, em);
          NfaRepOptLHeadPin(rer, qm, 0, greedy, r1, code, em, pcmid);
          assert pcmid == pc;
          assert AR.ActionsRepL(rer, qm, cont, code, pc);
          assert CW.BoolTreeLkX(rer, cont, inp, b, tb);
          assert ATR.MsizeA(cont) < ATR.MsizeA(acts);
          GateAheadClearTail(acts, gm);
          WalkDefsOkTail(acts);
          WalkPairLkAtNegCheckOracleCoreRec(rer, qm, code, inp, tb, gm, pc, b, cont, lid);
        } else {
          assert acts[0] == LS.Areg(L.Quantified(greedy, min, delta, r1));
          assert AR.NfaRepL(rer, qm, L.Quantified(greedy, min, delta, r1), code, pc, pcmid);
          QuantHeadPinsForkOrSQC(rer, qm, greedy, min, delta, r1, code, pc, pcmid);
        }
      case LookaroundR(lk0, r1) =>
        // ActionRepL's polarity split: a NegCheckOracle pc hosts a NEGATIVE look
        var lid0: int :| NR.GetPcRE(code, pc) == Some(if AR.PositiveL(lk0) then RB.CheckOracle(lid0)
                                                      else RB.NegCheckOracle(lid0))
                         && lid0 in qm.looks && qm.looks[lid0] == (lk0, r1);
        assert !AR.PositiveL(lk0) && lid0 == lid;
        assert pcmid == pc + 1;
        CW.GateNodeAtInpX(rer, acts, inp, b, tb, lk0, r1);   // tb is LK/LKFail with LkGateOk
        var tlk := LFU.ComputeTr(rer, [LS.Areg(r1)], inp, LG.Empty, L.LkDir(lk0));
        if tb.LK? {
          assert tb.tlk == tlk && LS.LkResult(lk0, tlk, LG.Empty, inp).Some?;   // LkGateOk true
          assert CW.BoolTreeLkX(rer, cont, inp, b, tb.t);
          assert AR.ActionsRepL(rer, qm, cont, code, pc + 1);
          // the passing negative merge is the identity ⟹ plain tail bricks
          GateAheadClearTail(acts, gm);
          WalkDefsOkTail(acts);
          assert EL.PikeLkActionsRec(cont);
          assert WalkPairLkRec(rer, qm, code, inp, tb.t, gm, pc + 1, g);
        } else {
          assert tb.LKFail? && tb.tlk == tlk;               // LkGateOk false
          assert LS.LkResult(lk0, tlk, LG.Empty, inp).None?;
          assert tb == LT.LKFail(lk0, tlk);
        }
      case Character(_) =>   // pins Consume — not NegCheckOracle
      case Disjunction(_, _) =>   // pins Fork — not NegCheckOracle
      case Group(_, _) =>   // pins SetRegisterToCP — not NegCheckOracle
      case AnchorR(_) =>   // pins AnchorAssertion — not NegCheckOracle
      case Backreference(_) =>   // NfaRepL false
  }

  lemma WalkPairLkAtNegCheckOracleRec(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                                      tb: LT.Tree, gm: LG.GroupMap, pc: nat, ea: bool, lid: int)
    requires WalkPairLkRec(rer, qm, code, inp, tb, gm, pc, ea)
    requires NR.GetPcRE(code, pc) == Some(RB.NegCheckOracle(lid))
    ensures lid in qm.looks
    ensures var (lk, r1) := qm.looks[lid];
            var tlk := LFU.ComputeTr(rer, [LS.Areg(r1)], inp, LG.Empty, L.LkDir(lk));
            !AR.PositiveL(lk)
            && (LS.LkResult(lk, tlk, LG.Empty, inp).Some? ==>
                  tb.LK? && tb.lk == lk && tb.tlk == tlk
                  && WalkPairLkRec(rer, qm, code, inp, tb.t, gm, pc + 1, ea))
            && (LS.LkResult(lk, tlk, LG.Empty, inp).None? ==> tb == LT.LKFail(lk, tlk))
  {
    var acts: LS.Actions, b: BS.LoopBool :|
      AR.ActionsRepL(rer, qm, acts, code, pc)
      && EL.PikeLkActionsRec(acts)
      && ATR.EaOf(b) == ea
      && CW.BoolTreeLkX(rer, acts, inp, b, tb)
      && GateAheadClear(acts, gm)
      && WalkDefsOk(acts);
    WalkPairLkAtNegCheckOracleCoreRec(rer, qm, code, inp, tb, gm, pc, b, acts, lid);
  }

  lemma WalkPairLkAtEndLoopCoreRec(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                                   tb: LT.Tree, gm: LG.GroupMap, pc: nat, b: BS.LoopBool,
                                   acts: LS.Actions)
    requires AR.ActionsRepL(rer, qm, acts, code, pc)
    requires EL.PikeLkActionsRec(acts)
    requires CW.BoolTreeLkX(rer, acts, inp, b, tb)
    requires NR.GetPcRE(code, pc) == Some(RB.EndLoop)
    requires GateAheadClear(acts, gm)
    requires WalkDefsOk(acts)
    ensures ATR.EaOf(b) ==> tb.Progress? && WalkPairLkRec(rer, qm, code, inp, tb.t, gm, pc + 1, true)
    ensures !ATR.EaOf(b) ==> tb == LT.Mismatch
    decreases ATR.MsizeA(acts)
  {
    var g := ATR.EaOf(b);
    assert !AR.BackForkAt(code, pc);   // GetPcRE(pc)==EndLoop, not Fork
    var pcmid: nat :| AR.ActionRepL(rer, qm, acts[0], code, pc, pcmid) && AR.ActionsRepL(rer, qm, acts[1..], code, pcmid);
    EL.PikeLkActionsRecTail(acts);
    assert acts == [acts[0]] + acts[1..];
    EL.PikeLkActionsRecConsIff(acts[0], acts[1..]);
    var cont := acts[1..];
    match acts[0]
    case Acheck(strcheck) =>
      // ActionRepL(Acheck): EndLoop disjunct (BackFork excluded) ⇒ pcmid == pc+1
      assert pcmid == pc + 1;
      if b == BS.CanExit {
        assert g == true;
        assert tb.Progress? && CW.BoolTreeLkX(rer, cont, inp, BS.CanExit, tb.t);
        assert AR.ActionsRepL(rer, qm, cont, code, pc + 1);
        // gm UNCHANGED across the guard ⟹ tail bricks give the continuation clear.
        GateAheadClearTail(acts, gm);       // GateAheadClear(cont, gm)
        WalkDefsOkTail(acts);             // NoDupSeq(AllDefsActs(cont))
        assert EL.PikeLkActionsRec(cont);
        assert ATR.EaOf(BS.CanExit) == true;
        assert WalkPairLkRec(rer, qm, code, inp, tb.t, gm, pc + 1, true);
      } else {
        assert b == BS.CannotExit && g == false;
        assert tb == LT.Mismatch;
      }
    case Aclose(_) =>   // pins SetRegisterToCP — not EndLoop
    case Areg(r0) =>
      assert EL.PikeLkRegexRec(r0);
      match r0
      case Epsilon =>
        assert pcmid == pc;
        assert CW.BoolTreeLkX(rer, cont, inp, b, tb);
        assert ATR.MsizeA(cont) < ATR.MsizeA(acts);
        GateAheadClearTail(acts, gm);
        WalkDefsOkTail(acts);
        WalkPairLkAtEndLoopCoreRec(rer, qm, code, inp, tb, gm, pc, b, cont);
      case Sequence(r1, r2) =>
        assert acts[0] == LS.Areg(L.Sequence(r1, r2));
        assert AR.NfaRepL(rer, qm, L.Sequence(r1, r2), code, pc, pcmid);
        var e1: nat :| AR.NfaRepL(rer, qm, r1, code, pc, e1) && AR.NfaRepL(rer, qm, r2, code, e1, pcmid);
        var na := [LS.Areg(r1), LS.Areg(r2)] + cont;
        assert na == [LS.Areg(r1)] + ([LS.Areg(r2)] + cont);
        AR.ActionsRepLCons(rer, qm, LS.Areg(r2), cont, code, e1, pcmid);
        AR.ActionsRepLCons(rer, qm, LS.Areg(r1), [LS.Areg(r2)] + cont, code, pc, e1);
        assert AR.ActionsRepL(rer, qm, na, code, pc);
        assert EL.PikeLkActionsRec(na) by {
          EL.PikeLkActionsRecConsIff(LS.Areg(r2), cont);
          EL.PikeLkActionsRecConsIff(LS.Areg(r1), [LS.Areg(r2)] + cont);
        }
        assert CW.BoolTreeLkX(rer, na, inp, b, tb);
        assert LS.ActionsRegexSize(acts) == RegSz(r1) + RegSz(r2) + 1 + LS.ActionsRegexSize(cont);
        assert LS.ActionsRegexSize(na) == RegSz(r1) + RegSz(r2) + LS.ActionsRegexSize(cont);
        assert ATR.MsizeA(na) < ATR.MsizeA(acts);
        GateAheadClearSeqExpand(acts, r1, r2, gm);
        M.AllDefsActsCons(acts[0], cont);
        M.AllDefsActsCons(LS.Areg(r1), [LS.Areg(r2)] + cont);
        M.AllDefsActsCons(LS.Areg(r2), cont);
        assert L.DefGroups(L.Sequence(r1, r2)) == L.DefGroups(r1) + L.DefGroups(r2);
        assert L.DefGroups(r1) + (L.DefGroups(r2) + M.AllDefsActs(cont))
            == (L.DefGroups(r1) + L.DefGroups(r2)) + M.AllDefsActs(cont);
        assert M.AllDefsActs(na) == M.AllDefsActs(acts);
        WalkDefsOkSeqExpand(acts, r1, r2);
        WalkPairLkAtEndLoopCoreRec(rer, qm, code, inp, tb, gm, pc, b, na);
      case Quantified(greedy, min, delta, r1) =>
        if min == 0 && delta == LN.NN(0) {
          assert acts[0] == LS.Areg(L.Quantified(greedy, 0, LN.NN(0), r1));
          assert AR.NfaRepL(rer, qm, L.Quantified(greedy, 0, LN.NN(0), r1), code, pc, pcmid);
          var em: nat :| AR.NfaRepMinL(rer, qm, 0, r1, code, pc, em)
                         && AR.NfaRepOptL(rer, qm, 0, greedy, r1, code, em, pcmid);
          NfaRepMinLHeadPin(rer, qm, 0, r1, code, pc, em);
          NfaRepOptLHeadPin(rer, qm, 0, greedy, r1, code, em, pcmid);
          assert pcmid == pc;
          assert AR.ActionsRepL(rer, qm, cont, code, pc);
          assert CW.BoolTreeLkX(rer, cont, inp, b, tb);
          assert ATR.MsizeA(cont) < ATR.MsizeA(acts);
          GateAheadClearTail(acts, gm);
          WalkDefsOkTail(acts);
          WalkPairLkAtEndLoopCoreRec(rer, qm, code, inp, tb, gm, pc, b, cont);
        } else {
          assert acts[0] == LS.Areg(L.Quantified(greedy, min, delta, r1));
          assert AR.NfaRepL(rer, qm, L.Quantified(greedy, min, delta, r1), code, pc, pcmid);
          QuantHeadPinsForkOrSQC(rer, qm, greedy, min, delta, r1, code, pc, pcmid);
        }
      case Character(_) =>   // pins Consume — not EndLoop
      case Disjunction(_, _) =>   // pins Fork — not EndLoop
      case Group(_, _) =>   // pins SetRegisterToCP — not EndLoop
      case LookaroundR(_, _) =>   // pins CheckOracle/NegCheckOracle — not EndLoop
      case AnchorR(_) =>   // pins AnchorAssertion — not EndLoop
      case Backreference(_) =>   // NfaRepL false
  }

  lemma WalkPairLkAtEndLoopRec(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                               tb: LT.Tree, gm: LG.GroupMap, pc: nat, ea: bool)
    requires WalkPairLkRec(rer, qm, code, inp, tb, gm, pc, ea)
    requires NR.GetPcRE(code, pc) == Some(RB.EndLoop)
    ensures ea ==> tb.Progress? && WalkPairLkRec(rer, qm, code, inp, tb.t, gm, pc + 1, true)
    ensures !ea ==> tb == LT.Mismatch
  {
    var acts: LS.Actions, b: BS.LoopBool :|
      AR.ActionsRepL(rer, qm, acts, code, pc)
      && EL.PikeLkActionsRec(acts)
      && ATR.EaOf(b) == ea
      && CW.BoolTreeLkX(rer, acts, inp, b, tb)
      && GateAheadClear(acts, gm)
      && WalkDefsOk(acts);
    WalkPairLkAtEndLoopCoreRec(rer, qm, code, inp, tb, gm, pc, b, acts);
  }

  lemma WalkPairLkAtBeginLoopRec(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                                 tb: LT.Tree, gmt: LG.GroupMap, pc: nat, ea: bool)
    requires WalkPairLkRec(rer, qm, code, inp, tb, gmt, pc, ea)
    requires NR.GetPcRE(code, pc) == Some(RB.BeginLoop)
    ensures WalkPairLkRec(rer, qm, code, inp, tb, gmt, pc + 1, false)
  {
    forall acts: LS.Actions, b: BS.LoopBool
      ensures !(AR.ActionsRepL(rer, qm, acts, code, pc)
                && EL.PikeLkActionsRec(acts) && ATR.EaOf(b) == ea
                && CW.BoolTreeLkX(rer, acts, inp, b, tb) && GateAheadClear(acts, gmt))
    {
      if AR.ActionsRepL(rer, qm, acts, code, pc) {
        TT.ActionsRepNotAtBeginLoop(rer, qm, acts, code, pc);   // ⇒ false
      }
    }
  }

  lemma WalkPairLkAtSetQuantCoreRec(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                                    tb: LT.Tree, gm: LG.GroupMap, pc: nat, b: BS.LoopBool,
                                    acts: LS.Actions, q: int)
    requires AR.ActionsRepL(rer, qm, acts, code, pc)
    requires EL.PikeLkActionsRec(acts)
    requires CW.BoolTreeLkX(rer, acts, inp, b, tb)
    requires NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(q, false))
    requires GateAheadClear(acts, gm)
    requires WalkDefsOk(acts)
    ensures q in qm.quants
    ensures tb.GroupActionT? && tb.g == LG.Reset(qm.quants[q])
    ensures WalkPairLkRec(rer, qm, code, inp, tb.t,
                          LG.GMUpdate(tb.g, LC.Idx(inp), gm), pc + 1, ATR.EaOf(b))
    decreases ATR.MsizeA(acts)
  {
    var g := ATR.EaOf(b);
    var pcmid: nat :| AR.ActionRepL(rer, qm, acts[0], code, pc, pcmid) && AR.ActionsRepL(rer, qm, acts[1..], code, pcmid);
    EL.PikeLkActionsRecTail(acts);
    assert acts == [acts[0]] + acts[1..];
    EL.PikeLkActionsRecConsIff(acts[0], acts[1..]);
    var cont := acts[1..];
    match acts[0]
    case Acheck(_) =>   // pins EndLoop / backward Fork — not SetQuantToClock
    case Aclose(_) =>   // pins SetRegisterToCP — not SetQuantToClock
    case Areg(r0) =>
      assert EL.PikeLkRegexRec(r0);
      match r0
      case Epsilon =>
        assert pcmid == pc;
        assert CW.BoolTreeLkX(rer, cont, inp, b, tb);
        assert ATR.MsizeA(cont) < ATR.MsizeA(acts);
        GateAheadClearTail(acts, gm);
        WalkDefsOkTail(acts);
        WalkPairLkAtSetQuantCoreRec(rer, qm, code, inp, tb, gm, pc, b, cont, q);
      case Sequence(r1, r2) =>
        assert acts[0] == LS.Areg(L.Sequence(r1, r2));
        assert AR.NfaRepL(rer, qm, L.Sequence(r1, r2), code, pc, pcmid);
        var e1: nat :| AR.NfaRepL(rer, qm, r1, code, pc, e1) && AR.NfaRepL(rer, qm, r2, code, e1, pcmid);
        var na := [LS.Areg(r1), LS.Areg(r2)] + cont;
        assert na == [LS.Areg(r1)] + ([LS.Areg(r2)] + cont);
        AR.ActionsRepLCons(rer, qm, LS.Areg(r2), cont, code, e1, pcmid);
        AR.ActionsRepLCons(rer, qm, LS.Areg(r1), [LS.Areg(r2)] + cont, code, pc, e1);
        assert AR.ActionsRepL(rer, qm, na, code, pc);
        assert EL.PikeLkActionsRec(na) by {
          EL.PikeLkActionsRecConsIff(LS.Areg(r2), cont);
          EL.PikeLkActionsRecConsIff(LS.Areg(r1), [LS.Areg(r2)] + cont);
        }
        assert CW.BoolTreeLkX(rer, na, inp, b, tb);
        assert LS.ActionsRegexSize(acts) == RegSz(r1) + RegSz(r2) + 1 + LS.ActionsRegexSize(cont);
        assert LS.ActionsRegexSize(na) == RegSz(r1) + RegSz(r2) + LS.ActionsRegexSize(cont);
        assert ATR.MsizeA(na) < ATR.MsizeA(acts);
        GateAheadClearSeqExpand(acts, r1, r2, gm);
        WalkDefsOkSeqExpand(acts, r1, r2);
        WalkPairLkAtSetQuantCoreRec(rer, qm, code, inp, tb, gm, pc, b, na, q);
      case Quantified(greedy, min, delta, r1) =>
        assert acts[0] == LS.Areg(L.Quantified(greedy, min, delta, r1));
        assert AR.NfaRepL(rer, qm, L.Quantified(greedy, min, delta, r1), code, pc, pcmid);
        if min > 0 {
          if min == 1 && delta.Inf? && greedy && !NUL.NonNullableL(r1) {
            // §2.5b F-c: the CIN head is the FORK `Fork(em + 1, e1 + 2)` at pc
            var emC, e1C := AR.NfaRepLCinInv(rer, qm, greedy, min, r1, code, pc, pcmid);
            assert emC == pc;
            assert false;
          }
          if min == 1 { CW.NotCinGreedy(greedy, delta, r1); }
          // THE forced-copy real head.
          var quant1 := L.Quantified(greedy, min - 1, delta, r1);
          var contActs := [LS.Areg(r1), LS.Areg(quant1)] + cont;
          var gidl := L.DefGroups(r1);
          assert tb.GroupActionT? && tb.g == LG.Reset(gidl)
                 && CW.BoolTreeLkX(rer, contActs, inp, b, tb.t);
          // the qm.quants binding of THIS instruction's qid
          QuantHeadSQCPin(rer, qm, greedy, min, delta, r1, code, pc, pcmid);
          var qid: int :| NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(qid, false))
                          && qid in qm.quants && qm.quants[qid] == L.DefGroups(r1);
          assert qid == q;
          assert q in qm.quants && qm.quants[q] == gidl;
          QuantForcedContRep(rer, qm, greedy, min, delta, r1, code, pc, pcmid, cont);   // ActionsRepL(contActs, pc+1)
          assert EL.PikeLkRegexRec(r1) && EL.PikeLkRegexRec(quant1);
          assert EL.PikeLkActionsRec(contActs) by {
            EL.PikeLkActionsRecConsIff(LS.Areg(quant1), cont);
            EL.PikeLkActionsRecConsIff(LS.Areg(r1), [LS.Areg(quant1)] + cont);
          }
          // gm moves by the Reset
          var gm2 := LG.GMUpdate(LG.Reset(gidl), LC.Idx(inp), gm);
          assert gm2 == LG.GMReset(gidl, gm);
          // GateAheadClear(contActs, gm2): fresh r1-pendings ⊆ the reset set;
          // cont's pendings carry (absent in gm, and Reset only removes keys)
          assert GateAheadClear(contActs, gm2) by {
            forall lk2: L.Lookaround, rr: L.Regex | GatePending(contActs, lk2, rr)
              ensures forall gg :: gg in L.DefGroups(rr) ==> gg !in gm2
            {
              var j :| 0 <= j < |contActs| && contActs[j].Areg? && RegexTopGate(contActs[j].r, lk2, rr);
              if j == 0 {
                assert contActs[0] == LS.Areg(r1) && RegexTopGate(r1, lk2, rr);
                RegexTopGateSubDefs(r1, lk2, rr);
                var SRR := set gx | gx in L.DefGroups(rr);
                var SR1 := set gx | gx in L.DefGroups(r1);
                assert SRR <= SR1;
                forall gg | gg in L.DefGroups(rr) ensures gg !in gm2 {
                  assert gg in SRR;
                  assert gg in SR1;
                  assert gg in L.DefGroups(r1);
                  assert gm2 == gm - (set gx | gx in gidl);
                  assert gg in (set gx | gx in gidl);
                }
              } else if j == 1 {
                assert !RegexTopGate(quant1, lk2, rr);   // Quantified: never pending
                assert false;
              } else {
                assert contActs[j] == cont[j - 2];
                assert GatePending(cont, lk2, rr) by {
                  assert cont[j - 2].Areg? && RegexTopGate(cont[j - 2].r, lk2, rr);
                }
                GatePendingTail(acts, lk2, rr);
                forall gg | gg in L.DefGroups(rr) ensures gg !in gm2 {
                  assert gg !in gm;   // GateAheadClear(acts, gm)
                }
              }
            }
          }
          // WalkDefsOk(contActs): the unfold brick (mid = [])
          WalkDefsOkUnfold(acts, r1, quant1, []);
          assert [LS.Areg(r1)] + [] + [LS.Areg(quant1)] + cont == contActs;
          // pack the existential at pc+1
          assert AR.ActionsRepL(rer, qm, contActs, code, pc + 1)
                 && EL.PikeLkActionsRec(contActs)
                 && ATR.EaOf(b) == g
                 && CW.BoolTreeLkX(rer, contActs, inp, b, tb.t)
                 && GateAheadClear(contActs, gm2)
                 && WalkDefsOk(contActs);
          assert WalkPairLkRec(rer, qm, code, inp, tb.t, gm2, pc + 1, g);
        } else if delta == LN.NN(0) {
          var em: nat :| AR.NfaRepMinL(rer, qm, 0, r1, code, pc, em)
                         && AR.NfaRepOptL(rer, qm, 0, greedy, r1, code, em, pcmid);
          NfaRepMinLHeadPin(rer, qm, 0, r1, code, pc, em);
          NfaRepOptLHeadPin(rer, qm, 0, greedy, r1, code, em, pcmid);
          assert pcmid == pc;
          assert AR.ActionsRepL(rer, qm, cont, code, pc);
          assert CW.BoolTreeLkX(rer, cont, inp, b, tb);
          assert ATR.MsizeA(cont) < ATR.MsizeA(acts);
          GateAheadClearTail(acts, gm);
          WalkDefsOkTail(acts);
          WalkPairLkAtSetQuantCoreRec(rer, qm, code, inp, tb, gm, pc, b, cont, q);
        } else {
          // min==0 with Inf or NN(kx>0): pins a Fork at pc, not SetQuantToClock.
          match delta
          case Inf =>
            if exists e1: nat ::
                NR.GetPcRE(code, pc) == Some(if greedy then RB.Fork(pc + 1, e1 + 2) else RB.Fork(e1 + 2, pc + 1))
                && (exists qid: int :: NR.GetPcRE(code, pc + 1) == Some(RB.SetQuantToClock(qid, false))
                                       && qid in qm.quants && qm.quants[qid] == L.DefGroups(r1))
                && NR.GetPcRE(code, pc + 2) == Some(RB.BeginLoop)
                && AR.NfaRepL(rer, qm, r1, code, pc + 3, e1)
                && NR.GetPcRE(code, e1) == Some(RB.EndLoop)
                && NR.GetPcRE(code, e1 + 1) == Some(RB.Jmp(pc))
                && pcmid == e1 + 2 {
              var e1: nat :| NR.GetPcRE(code, pc) == Some(if greedy then RB.Fork(pc + 1, e1 + 2) else RB.Fork(e1 + 2, pc + 1));
            } else {
              AR.NfaRepLStarLoopViews(rer, qm, greedy, r1, code, pc, pcmid);
              if NUL.NonNullableL(r1) {
                var em: nat :| NR.GetPcRE(code, pc) == Some(if greedy then RB.Fork(em, pc + 1) else RB.Fork(pc + 1, em));
              } else {
                var emC, e1C := AR.NfaRepLStarCinInv(rer, qm, r1, code, pc, pcmid);
              }
            }
          case NN(kx) =>
            var em: nat :| AR.NfaRepMinL(rer, qm, 0, r1, code, pc, em)
                           && AR.NfaRepOptL(rer, qm, kx, greedy, r1, code, em, pcmid);
            NfaRepMinLHeadPin(rer, qm, 0, r1, code, pc, em);
            NfaRepOptLHeadPin(rer, qm, kx, greedy, r1, code, em, pcmid);   // kx>0 ⇒ Fork at pc
        }
      case Character(_) =>   // pins Consume — not SetQuantToClock
      case Disjunction(_, _) =>   // pins Fork — not SetQuantToClock
      case Group(_, _) =>   // pins SetRegisterToCP — not SetQuantToClock
      case LookaroundR(_, _) =>   // pins CheckOracle/NegCheckOracle — not SetQuantToClock
      case AnchorR(_) =>   // pins AnchorAssertion — not SetQuantToClock
      case Backreference(_) =>   // NfaRepL false
  }

  lemma WalkPairLkAtSetQuantRec(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                                tb: LT.Tree, gm: LG.GroupMap, pc: nat, ea: bool, q: int, bq: bool)
    requires WalkPairLkRec(rer, qm, code, inp, tb, gm, pc, ea)
    requires NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(q, bq))
    ensures q in qm.quants
    ensures tb.GroupActionT? && tb.g == LG.Reset(qm.quants[q])
    ensures WalkPairLkRec(rer, qm, code, inp, tb.t,
                          LG.GMUpdate(tb.g, LC.Idx(inp), gm), pc + 1, ea)
  {
    if (exists acts: LS.Actions, b: BS.LoopBool ::
          AR.ActionsRepL(rer, qm, acts, code, pc)
          && EL.PikeLkActionsRec(acts)
          && ATR.EaOf(b) == ea
          && CW.BoolTreeLkX(rer, acts, inp, b, tb)
          && GateAheadClear(acts, gm)
          && WalkDefsOk(acts)) {
      var acts: LS.Actions, b: BS.LoopBool :|
        AR.ActionsRepL(rer, qm, acts, code, pc)
        && EL.PikeLkActionsRec(acts)
        && ATR.EaOf(b) == ea
        && CW.BoolTreeLkX(rer, acts, inp, b, tb)
        && GateAheadClear(acts, gm)
        && WalkDefsOk(acts);
      if bq { ActionsRepNotAtTrueStamp(rer, qm, acts, code, pc, q); }   // (§2.5b F-c) no stack sits at the stamp
      WalkPairLkAtSetQuantCoreRec(rer, qm, code, inp, tb, gm, pc, b, acts, q);
    } else {
      // the SQC see-through disjunct is the live one
      var q0: int :| (NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(q0, false))
                      || NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(q0, true)))
                     && q0 in qm.quants
                     && tb.GroupActionT? && tb.g == LG.Reset(qm.quants[q0])
                     && WalkPairLkRec(rer, qm, code, inp, tb.t, LG.GMUpdate(tb.g, LC.Idx(inp), gm), pc + 1, ea);
      assert q0 == q;
    }
  }

  lemma {:isolate_assertions} WalkPairLkAtForkCoreRec(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                                tb: LT.Tree, gm: LG.GroupMap, pc: nat, b: BS.LoopBool,
                                acts: LS.Actions, x: int, y: int)
    requires AR.ActionsRepL(rer, qm, acts, code, pc)
    requires EL.PikeLkActionsRec(acts)
    requires CW.BoolTreeLkX(rer, acts, inp, b, tb)
    requires NR.GetPcRE(code, pc) == Some(RB.Fork(x, y))
    requires GateAheadClear(acts, gm)
    requires WalkDefsOk(acts)
    ensures x >= 0 && y >= 0
    // ERASURE-SHAPED (raw `Progress` guard wrappers can nest at a backfork):
    // dead, or the erased tree is a Choice whose arms have walking witnesses
    // at x/y — always at the OUTER flag (every Acheck peel preserves CanExit).
    ensures CE.ProgErase(tb) == LT.Mismatch
            || exists ta1: LT.Tree, ta2: LT.Tree ::
              CE.ProgErase(tb) == LT.Choice(CE.ProgErase(ta1), CE.ProgErase(ta2))
              && WalkPairLkRec(rer, qm, code, inp, ta1, gm, x as nat, ATR.EaOf(b))
              && WalkPairLkRec(rer, qm, code, inp, ta2, gm, y as nat, ATR.EaOf(b))
    decreases ATR.MsizeA(acts)
  {
    // (§2.5b/z3 4.14) recursive nullability predicates + the CIN disjunct's
    // triggered existential storm the solver; all uses here are opaque.
    hide NUL.NonNullableL, NUL.CINullableL, NUL.NoNulledPlusL, AR.NfaRepCinL;
    var g := ATR.EaOf(b);
    var pcmid: nat :| AR.ActionRepL(rer, qm, acts[0], code, pc, pcmid) && AR.ActionsRepL(rer, qm, acts[1..], code, pcmid);
    EL.PikeLkActionsRecTail(acts);
    assert acts == [acts[0]] + acts[1..];
    EL.PikeLkActionsRecConsIff(acts[0], acts[1..]);
    var cont := acts[1..];
    match acts[0]
    case Acheck(strcheck) =>
      // EndLoop != Fork ⟹ the BackForkAt disjunct: pcmid == pc.
      assert AR.BackForkAt(code, pc);
      assert x >= 0 && y >= 0;
      if b == BS.CanExit {
        assert tb.Progress? && CW.BoolTreeLkX(rer, cont, inp, BS.CanExit, tb.t);
        assert AR.ActionsRepL(rer, qm, cont, code, pc);
        GateAheadClearTail(acts, gm);
        WalkDefsOkTail(acts);
        assert ATR.MsizeA(cont) < ATR.MsizeA(acts);
        WalkPairLkAtForkCoreRec(rer, qm, code, inp, tb.t, gm, pc, BS.CanExit, cont, x, y);
        // the erased result lifts through the Progress wrapper verbatim
        assert CE.ProgErase(tb) == CE.ProgErase(tb.t);
        assert ATR.EaOf(BS.CanExit) == ATR.EaOf(b);
      } else {
        assert tb == LT.Mismatch;
      }
    case Aclose(_) =>   // pins SetRegisterToCP — not Fork
    case Areg(r0) =>
      assert EL.PikeLkRegexRec(r0);
      match r0
      case Epsilon =>
        assert pcmid == pc;
        assert CW.BoolTreeLkX(rer, cont, inp, b, tb);
        assert ATR.MsizeA(cont) < ATR.MsizeA(acts);
        GateAheadClearTail(acts, gm);
        WalkDefsOkTail(acts);
        WalkPairLkAtForkCoreRec(rer, qm, code, inp, tb, gm, pc, b, cont, x, y);
      case Sequence(r1, r2) =>
        assert acts[0] == LS.Areg(L.Sequence(r1, r2));
        assert AR.NfaRepL(rer, qm, L.Sequence(r1, r2), code, pc, pcmid);
        var e1: nat :| AR.NfaRepL(rer, qm, r1, code, pc, e1) && AR.NfaRepL(rer, qm, r2, code, e1, pcmid);
        var na := [LS.Areg(r1), LS.Areg(r2)] + cont;
        assert na == [LS.Areg(r1)] + ([LS.Areg(r2)] + cont);
        AR.ActionsRepLCons(rer, qm, LS.Areg(r2), cont, code, e1, pcmid);
        AR.ActionsRepLCons(rer, qm, LS.Areg(r1), [LS.Areg(r2)] + cont, code, pc, e1);
        assert AR.ActionsRepL(rer, qm, na, code, pc);
        assert EL.PikeLkActionsRec(na) by {
          EL.PikeLkActionsRecConsIff(LS.Areg(r2), cont);
          EL.PikeLkActionsRecConsIff(LS.Areg(r1), [LS.Areg(r2)] + cont);
        }
        assert CW.BoolTreeLkX(rer, na, inp, b, tb);
        assert LS.ActionsRegexSize(acts) == RegSz(r1) + RegSz(r2) + 1 + LS.ActionsRegexSize(cont);
        assert LS.ActionsRegexSize(na) == RegSz(r1) + RegSz(r2) + LS.ActionsRegexSize(cont);
        assert ATR.MsizeA(na) < ATR.MsizeA(acts);
        GateAheadClearSeqExpand(acts, r1, r2, gm);
        WalkDefsOkSeqExpand(acts, r1, r2);
        WalkPairLkAtForkCoreRec(rer, qm, code, inp, tb, gm, pc, b, na, x, y);
      case Disjunction(r1, r2) =>
        var e1: nat :| NR.GetPcRE(code, pc) == Some(RB.Fork(pc + 1, e1 + 1))
                       && AR.NfaRepL(rer, qm, r1, code, pc + 1, e1)
                       && NR.GetPcRE(code, e1) == Some(RB.Jmp(pcmid))
                       && AR.NfaRepL(rer, qm, r2, code, e1 + 1, pcmid);
        assert x == pc + 1 && y == e1 + 1;
        assert tb.Choice?
               && CW.BoolTreeLkX(rer, [LS.Areg(r1)] + cont, inp, b, tb.t1)
               && CW.BoolTreeLkX(rer, [LS.Areg(r2)] + cont, inp, b, tb.t2);
        // arm reps: r1's tail rides the mid Jmp; r2's is direct
        assert AR.ActionsRepL(rer, qm, cont, code, e1);   // jump_bc via Jmp(pcmid)
        AR.ActionsRepLCons(rer, qm, LS.Areg(r1), cont, code, pc + 1, e1);
        AR.ActionsRepLCons(rer, qm, LS.Areg(r2), cont, code, e1 + 1, pcmid);
        assert EL.PikeLkActionsRec([LS.Areg(r1)] + cont) && EL.PikeLkActionsRec([LS.Areg(r2)] + cont) by {
          EL.PikeLkActionsRecConsIff(LS.Areg(r1), cont);
          EL.PikeLkActionsRecConsIff(LS.Areg(r2), cont);
        }
        GateAheadClearDisjArm(acts, r1, r2, r1, gm);
        GateAheadClearDisjArm(acts, r1, r2, r2, gm);
        WalkDefsOkDisjArm(acts, r1, r2, r1);
        WalkDefsOkDisjArm(acts, r1, r2, r2);
        assert WalkPairLkRec(rer, qm, code, inp, tb.t1, gm, x as nat, g)
               && WalkPairLkRec(rer, qm, code, inp, tb.t2, gm, y as nat, g);
        assert CE.ProgErase(tb) == LT.Choice(CE.ProgErase(tb.t1), CE.ProgErase(tb.t2));
        assert exists ta1: LT.Tree, ta2: LT.Tree ::
            CE.ProgErase(tb) == LT.Choice(CE.ProgErase(ta1), CE.ProgErase(ta2))
            && WalkPairLkRec(rer, qm, code, inp, ta1, gm, x as nat, ATR.EaOf(b))
            && WalkPairLkRec(rer, qm, code, inp, ta2, gm, y as nat, ATR.EaOf(b)) by {
          assert WalkPairLkRec(rer, qm, code, inp, tb.t1, gm, x as nat, ATR.EaOf(b));
          assert WalkPairLkRec(rer, qm, code, inp, tb.t2, gm, y as nat, ATR.EaOf(b));
        }
      case Quantified(greedy, min, delta, r1) =>
        assert acts[0] == LS.Areg(L.Quantified(greedy, min, delta, r1));
        assert AR.NfaRepL(rer, qm, L.Quantified(greedy, min, delta, r1), code, pc, pcmid);
        if min == 0 && delta == LN.NN(0) {
          var em: nat :| AR.NfaRepMinL(rer, qm, 0, r1, code, pc, em)
                         && AR.NfaRepOptL(rer, qm, 0, greedy, r1, code, em, pcmid);
          NfaRepMinLHeadPin(rer, qm, 0, r1, code, pc, em);
          NfaRepOptLHeadPin(rer, qm, 0, greedy, r1, code, em, pcmid);
          assert pcmid == pc;
          assert AR.ActionsRepL(rer, qm, cont, code, pc);
          assert CW.BoolTreeLkX(rer, cont, inp, b, tb);
          assert ATR.MsizeA(cont) < ATR.MsizeA(acts);
          GateAheadClearTail(acts, gm);
          WalkDefsOkTail(acts);
          WalkPairLkAtForkCoreRec(rer, qm, code, inp, tb, gm, pc, b, cont, x, y);
        } else if min == 1 && delta.Inf? && greedy && !NUL.NonNullableL(r1) {
          // §2.5b F-c: THE CIN HEAD FORK (its own lemma)
          WalkPairLkCinHeadArmsRec(rer, qm, code, inp, tb, gm, pc, b, acts, cont, pcmid, r1, x, y);
        } else if min > 0 {
          // §2.5a: needs the STRONG head fact to refute the `Fork` we sit at;
          // `QuantHeadPinsForkOrSQC`'s `Fork? || SetQuantToClock?` is too weak.
          QuantHeadMinPosPinsSQC(rer, qm, greedy, min, delta, r1, code, pc, pcmid);
          assert false;   // min>0 head pins SetQuantToClock, not Fork
        } else {
          // min == 0 with Inf or NN(kx>0): the star fork — tb is the Choice.
          var gidl := L.DefGroups(r1);
          var q' := L.Quantified(greedy, 0, FS.NoiPred(delta), r1);
          var itert := if greedy then tb.t1 else tb.t2;
          var skipt := if greedy then tb.t2 else tb.t1;
          assert tb.Choice?
                 && itert.GroupActionT? && itert.g == LG.Reset(gidl)
                 && CW.BoolTreeLkX(rer, [LS.Areg(r1), LS.Acheck(inp), LS.Areg(q')] + cont,
                                  inp, BS.CannotExit, itert.t)
                 && CW.BoolTreeLkX(rer, cont, inp, b, skipt);
          var armlist := [LS.Areg(r1), LS.Acheck(inp), LS.Areg(q')] + cont;
          assert EL.PikeLkActionsRec(armlist) by {
            assert EL.PikeLkRegexRec(r1) && EL.PikeLkRegexRec(q');
            EL.PikeLkActionsRecConsIff(LS.Areg(q'), cont);
            EL.PikeLkActionsRecConsIff(LS.Acheck(inp), [LS.Areg(q')] + cont);
            EL.PikeLkActionsRecConsIff(LS.Areg(r1), [LS.Acheck(inp)] + ([LS.Areg(q')] + cont));
            assert [LS.Areg(r1)] + ([LS.Acheck(inp)] + ([LS.Areg(q')] + cont)) == armlist;
          }
          StarArmInvariants(acts, r1, q', LS.Acheck(inp), gm, gidl);
          // skip arm invariants
          GateAheadClearTail(acts, gm);
          WalkDefsOkTail(acts);
          match delta
          case Inf =>
            assert q' == L.Quantified(greedy, 0, LN.Inf, r1);
            if exists e1: nat ::
                NR.GetPcRE(code, pc) == Some(if greedy then RB.Fork(pc + 1, e1 + 2) else RB.Fork(e1 + 2, pc + 1))
                && (exists qid: int :: NR.GetPcRE(code, pc + 1) == Some(RB.SetQuantToClock(qid, false))
                                       && qid in qm.quants && qm.quants[qid] == L.DefGroups(r1))
                && NR.GetPcRE(code, pc + 2) == Some(RB.BeginLoop)
                && AR.NfaRepL(rer, qm, r1, code, pc + 3, e1)
                && NR.GetPcRE(code, e1) == Some(RB.EndLoop)
                && NR.GetPcRE(code, e1 + 1) == Some(RB.Jmp(pc))
                && pcmid == e1 + 2 {
              // ---- the LOOP BLOCK: SQC at pc+1, BeginLoop at pc+2 ----------
              var e1: nat :|
                NR.GetPcRE(code, pc) == Some(if greedy then RB.Fork(pc + 1, e1 + 2) else RB.Fork(e1 + 2, pc + 1))
                && (exists qid: int :: NR.GetPcRE(code, pc + 1) == Some(RB.SetQuantToClock(qid, false))
                                       && qid in qm.quants && qm.quants[qid] == L.DefGroups(r1))
                && NR.GetPcRE(code, pc + 2) == Some(RB.BeginLoop)
                && AR.NfaRepL(rer, qm, r1, code, pc + 3, e1)
                && NR.GetPcRE(code, e1) == Some(RB.EndLoop)
                && NR.GetPcRE(code, e1 + 1) == Some(RB.Jmp(pc))
                && pcmid == e1 + 2;
              var qid: int :| NR.GetPcRE(code, pc + 1) == Some(RB.SetQuantToClock(qid, false))
                              && qid in qm.quants && qm.quants[qid] == L.DefGroups(r1);
              // armlist rep at pc+3: r1; Acheck at EndLoop; q'+cont via the back-jump
              assert AR.ActionsRepL(rer, qm, [LS.Areg(q')] + cont, code, pc) by {
                AR.ActionsRepLCons(rer, qm, LS.Areg(q'), cont, code, pc, pcmid);
              }
              assert AR.ActionsRepL(rer, qm, [LS.Areg(q')] + cont, code, e1 + 1);   // jump_bc
              assert AR.ActionRepL(rer, qm, LS.Acheck(inp), code, e1, e1 + 1);      // EndLoop
              AR.ActionsRepLCons(rer, qm, LS.Acheck(inp), [LS.Areg(q')] + cont, code, e1, e1 + 1);
              AR.ActionsRepLCons(rer, qm, LS.Areg(r1), [LS.Acheck(inp)] + ([LS.Areg(q')] + cont),
                                 code, pc + 3, e1);
              assert [LS.Areg(r1)] + ([LS.Acheck(inp)] + ([LS.Areg(q')] + cont)) == armlist;
              assert AR.ActionsRepL(rer, qm, armlist, code, pc + 3);
              StarIterArmWalkBLRec(rer, qm, code, inp, gm, pc + 1, g, qid, r1, itert.t, armlist);
              assert WalkPairLkRec(rer, qm, code, inp, itert, gm, pc + 1, g);
              // skip arm at pcmid == e1+2
              assert WalkPairLkRec(rer, qm, code, inp, skipt, gm, pcmid, g);
              if greedy {
                assert x == pc + 1 && y == e1 + 2;
              } else {
                assert x == e1 + 2 && y == pc + 1;
              }
              assert WalkPairLkRec(rer, qm, code, inp, tb.t1, gm, x as nat, g)
                     && WalkPairLkRec(rer, qm, code, inp, tb.t2, gm, y as nat, g);
              assert CE.ProgErase(tb) == LT.Choice(CE.ProgErase(tb.t1), CE.ProgErase(tb.t2));
              assert exists ta1: LT.Tree, ta2: LT.Tree ::
                  CE.ProgErase(tb) == LT.Choice(CE.ProgErase(ta1), CE.ProgErase(ta2))
                  && WalkPairLkRec(rer, qm, code, inp, ta1, gm, x as nat, ATR.EaOf(b))
                  && WalkPairLkRec(rer, qm, code, inp, ta2, gm, y as nat, ATR.EaOf(b)) by {
                assert WalkPairLkRec(rer, qm, code, inp, tb.t1, gm, x as nat, ATR.EaOf(b));
                assert WalkPairLkRec(rer, qm, code, inp, tb.t2, gm, y as nat, ATR.EaOf(b));
              }

            } else {
              // ---- the LOOP VIEW: SQC at em (backward), body directly after
              AR.NfaRepLStarLoopViews(rer, qm, greedy, r1, code, pc, pcmid);
              if !NUL.NonNullableL(r1) {
                // §2.5b F-c: the CIN loop view (its own lemma)
                WalkPairLkCinLoopViewArmsRec(rer, qm, code, inp, tb, gm, pc, b, acts, cont, pcmid, r1, x, y);
                return;
              }
              assert NUL.NonNullableL(r1);
              var em: nat :| NR.GetPcRE(code, pc) == Some(if greedy then RB.Fork(em, pc + 1) else RB.Fork(pc + 1, em))
                             && em <= pc
                             && (exists qid: int :: NR.GetPcRE(code, em) == Some(RB.SetQuantToClock(qid, false))
                                                    && qid in qm.quants && qm.quants[qid] == L.DefGroups(r1))
                             && AR.NfaRepL(rer, qm, r1, code, em + 1, pc)
                             && pcmid == pc + 1;
              var qid: int :| NR.GetPcRE(code, em) == Some(RB.SetQuantToClock(qid, false))
                              && qid in qm.quants && qm.quants[qid] == L.DefGroups(r1);
              // armlist rep at em+1: r1 to pc; Acheck dissolves at the back fork; q'+cont at pc
              assert AR.ActionsRepL(rer, qm, [LS.Areg(q')] + cont, code, pc) by {
                AR.ActionsRepLCons(rer, qm, LS.Areg(q'), cont, code, pc, pcmid);
              }
              assert AR.BackForkAt(code, pc);
              assert AR.ActionRepL(rer, qm, LS.Acheck(inp), code, pc, pc);
              AR.ActionsRepLCons(rer, qm, LS.Acheck(inp), [LS.Areg(q')] + cont, code, pc, pc);
              AR.ActionsRepLCons(rer, qm, LS.Areg(r1), [LS.Acheck(inp)] + ([LS.Areg(q')] + cont),
                                 code, em + 1, pc);
              assert [LS.Areg(r1)] + ([LS.Acheck(inp)] + ([LS.Areg(q')] + cont)) == armlist;
              assert AR.ActionsRepL(rer, qm, armlist, code, em + 1);
              assert armlist == [LS.Areg(r1)] + ([LS.Acheck(inp), LS.Areg(q')] + cont);
              StarIterArmWalkLVRec(rer, qm, code, inp, gm, em, g, qid, r1, itert.t,
                                   [LS.Acheck(inp), LS.Areg(q')] + cont);
              assert WalkPairLkRec(rer, qm, code, inp, itert, gm, em, g);
              assert WalkPairLkRec(rer, qm, code, inp, skipt, gm, pc + 1, g);
              if greedy {
                assert x == em && y == pc + 1;
              } else {
                assert x == pc + 1 && y == em;
              }
              assert WalkPairLkRec(rer, qm, code, inp, tb.t1, gm, x as nat, g)
                     && WalkPairLkRec(rer, qm, code, inp, tb.t2, gm, y as nat, g);
              assert CE.ProgErase(tb) == LT.Choice(CE.ProgErase(tb.t1), CE.ProgErase(tb.t2));
              assert exists ta1: LT.Tree, ta2: LT.Tree ::
                  CE.ProgErase(tb) == LT.Choice(CE.ProgErase(ta1), CE.ProgErase(ta2))
                  && WalkPairLkRec(rer, qm, code, inp, ta1, gm, x as nat, ATR.EaOf(b))
                  && WalkPairLkRec(rer, qm, code, inp, ta2, gm, y as nat, ATR.EaOf(b)) by {
                assert WalkPairLkRec(rer, qm, code, inp, tb.t1, gm, x as nat, ATR.EaOf(b));
                assert WalkPairLkRec(rer, qm, code, inp, tb.t2, gm, y as nat, ATR.EaOf(b));
              }

            }
          case NN(kx) =>
            assert kx > 0;
            assert q' == L.Quantified(greedy, 0, LN.NN(kx - 1), r1);
            var em0: nat :| AR.NfaRepMinL(rer, qm, 0, r1, code, pc, em0)
                            && AR.NfaRepOptL(rer, qm, kx, greedy, r1, code, em0, pcmid);
            NfaRepMinLHeadPin(rer, qm, 0, r1, code, pc, em0);
            assert em0 == pc;
            var e1x: nat :| NR.GetPcRE(code, pc) == Some(if greedy then RB.Fork(pc + 1, pcmid) else RB.Fork(pcmid, pc + 1))
                            && (exists qid: int :: NR.GetPcRE(code, pc + 1) == Some(RB.SetQuantToClock(qid, false))
                                                   && qid in qm.quants && qm.quants[qid] == L.DefGroups(r1))
                            && NR.GetPcRE(code, pc + 2) == Some(RB.BeginLoop)
                            && AR.NfaRepL(rer, qm, r1, code, pc + 3, e1x)
                            && NR.GetPcRE(code, e1x) == Some(RB.EndLoop)
                            && AR.NfaRepOptL(rer, qm, kx - 1, greedy, r1, code, e1x + 1, pcmid);
            var qid: int :| NR.GetPcRE(code, pc + 1) == Some(RB.SetQuantToClock(qid, false))
                            && qid in qm.quants && qm.quants[qid] == L.DefGroups(r1);
            // q' at e1x+1: zero forced copies + the kx-1 optional layers
            assert AR.NfaRepL(rer, qm, q', code, e1x + 1, pcmid) by {
              assert AR.NfaRepMinL(rer, qm, 0, r1, code, e1x + 1, e1x + 1);
            }
            AR.ActionsRepLCons(rer, qm, LS.Areg(q'), cont, code, e1x + 1, pcmid);
            assert AR.ActionRepL(rer, qm, LS.Acheck(inp), code, e1x, e1x + 1);   // EndLoop
            AR.ActionsRepLCons(rer, qm, LS.Acheck(inp), [LS.Areg(q')] + cont, code, e1x, e1x + 1);
            AR.ActionsRepLCons(rer, qm, LS.Areg(r1), [LS.Acheck(inp)] + ([LS.Areg(q')] + cont),
                               code, pc + 3, e1x);
            assert [LS.Areg(r1)] + ([LS.Acheck(inp)] + ([LS.Areg(q')] + cont)) == armlist;
            assert AR.ActionsRepL(rer, qm, armlist, code, pc + 3);
            StarIterArmWalkBLRec(rer, qm, code, inp, gm, pc + 1, g, qid, r1, itert.t, armlist);
            assert WalkPairLkRec(rer, qm, code, inp, itert, gm, pc + 1, g);
            assert WalkPairLkRec(rer, qm, code, inp, skipt, gm, pcmid, g);
            if greedy {
              assert x == pc + 1 && y == pcmid;
            } else {
              assert x == pcmid && y == pc + 1;
            }
            assert WalkPairLkRec(rer, qm, code, inp, tb.t1, gm, x as nat, g)
                   && WalkPairLkRec(rer, qm, code, inp, tb.t2, gm, y as nat, g);
            assert CE.ProgErase(tb) == LT.Choice(CE.ProgErase(tb.t1), CE.ProgErase(tb.t2));
            assert exists ta1: LT.Tree, ta2: LT.Tree ::
                CE.ProgErase(tb) == LT.Choice(CE.ProgErase(ta1), CE.ProgErase(ta2))
                && WalkPairLkRec(rer, qm, code, inp, ta1, gm, x as nat, ATR.EaOf(b))
                && WalkPairLkRec(rer, qm, code, inp, ta2, gm, y as nat, ATR.EaOf(b)) by {
              assert WalkPairLkRec(rer, qm, code, inp, tb.t1, gm, x as nat, ATR.EaOf(b));
              assert WalkPairLkRec(rer, qm, code, inp, tb.t2, gm, y as nat, ATR.EaOf(b));
            }

        }
      case Character(_) =>   // pins Consume — not Fork
      case Group(_, _) =>   // pins SetRegisterToCP — not Fork
      case LookaroundR(_, _) =>   // pins CheckOracle/NegCheckOracle — not Fork
      case AnchorR(_) =>   // pins AnchorAssertion — not Fork
      case Backreference(_) =>   // NfaRepL false
  }

  lemma WalkPairLkAtForkArmsRec(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                                tb: LT.Tree, gm: LG.GroupMap, pc: nat, ea: bool, x: int, y: int)
    requires WalkPairLkRec(rer, qm, code, inp, tb, gm, pc, ea)
    requires NR.GetPcRE(code, pc) == Some(RB.Fork(x, y))
    ensures x >= 0 && y >= 0
    ensures CE.ProgErase(tb) == LT.Mismatch
            || exists ta1: LT.Tree, ta2: LT.Tree ::
              CE.ProgErase(tb) == LT.Choice(CE.ProgErase(ta1), CE.ProgErase(ta2))
              && WalkPairLkRec(rer, qm, code, inp, ta1, gm, x as nat, ea)
              && WalkPairLkRec(rer, qm, code, inp, ta2, gm, y as nat, ea)
  {
    var acts: LS.Actions, b: BS.LoopBool :|
      AR.ActionsRepL(rer, qm, acts, code, pc)
      && EL.PikeLkActionsRec(acts)
      && ATR.EaOf(b) == ea
      && CW.BoolTreeLkX(rer, acts, inp, b, tb)
      && GateAheadClear(acts, gm)
      && WalkDefsOk(acts);
    WalkPairLkAtForkCoreRec(rer, qm, code, inp, tb, gm, pc, b, acts, x, y);
  }

  lemma WalkPairLkAtCheckOracleCoreRec(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                                       tb: LT.Tree, gm: LG.GroupMap, pc: nat, b: BS.LoopBool,
                                       acts: LS.Actions, lid: int)
    requires AR.ActionsRepL(rer, qm, acts, code, pc)
    requires EL.PikeLkActionsRec(acts)
    requires CW.BoolTreeLkX(rer, acts, inp, b, tb)
    requires NR.GetPcRE(code, pc) == Some(RB.CheckOracle(lid))
    requires LL.OracleOkAt(rer, qm, inp)
    requires GateAheadClear(acts, gm)
    requires WalkDefsOk(acts)
    ensures lid in qm.looks
    ensures var (lk, r1) := qm.looks[lid];
            (LOr.view_get_oracle(qm.ov, TR_CpOf(inp), lid) ==>
               tb.LK? && tb.lk == lk
               && EL.LkGateOk(rer, lk, r1, inp, tb.tlk, true)
               && LS.LkResult(lk, tb.tlk, gm, inp).Some?
               && WalkPairLkRec(rer, qm, code, inp, tb.t, LS.LkResult(lk, tb.tlk, gm, inp).value,
                                pc + 1, ATR.EaOf(b)))
            && (!LOr.view_get_oracle(qm.ov, TR_CpOf(inp), lid) ==>
                  tb.LKFail? && tb.lk == lk
                  && EL.LkGateOk(rer, lk, r1, inp, tb.tlk, false))
    // the gate's OWN GateAheadClear instance: it is pending at the real head,
    // so its body groups are absent from the accumulated map (discharges
    // `ThreadRepLkStepCheckOracle`'s absence hypothesis)
    ensures forall gg :: gg in L.DefGroups(qm.looks[lid].1) ==> gg !in gm
    decreases ATR.MsizeA(acts)
  {
    var g := ATR.EaOf(b);
    var pcmid: nat :| AR.ActionRepL(rer, qm, acts[0], code, pc, pcmid) && AR.ActionsRepL(rer, qm, acts[1..], code, pcmid);
    assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
    EL.PikeLkActionsRecTail(acts);
    assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
    assert acts == [acts[0]] + acts[1..];
    assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
    EL.PikeLkActionsRecConsIff(acts[0], acts[1..]);
    var cont := acts[1..];
    match acts[0]
    case Acheck(_) =>   // pins EndLoop / backward Fork — not CheckOracle
    case Aclose(_) =>   // pins SetRegisterToCP — not CheckOracle
    case Areg(r0) =>
      assert EL.PikeLkRegexRec(r0);
      match r0
      case Epsilon =>
        assert pcmid == pc;
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert CW.BoolTreeLkX(rer, cont, inp, b, tb);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert ATR.MsizeA(cont) < ATR.MsizeA(acts);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        GateAheadClearTail(acts, gm);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        WalkDefsOkTail(acts);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        WalkPairLkAtCheckOracleCoreRec(rer, qm, code, inp, tb, gm, pc, b, cont, lid);
      case Sequence(r1, r2) =>
        assert acts[0] == LS.Areg(L.Sequence(r1, r2));
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert AR.NfaRepL(rer, qm, L.Sequence(r1, r2), code, pc, pcmid);
        var e1: nat :| AR.NfaRepL(rer, qm, r1, code, pc, e1) && AR.NfaRepL(rer, qm, r2, code, e1, pcmid);
        var na := [LS.Areg(r1), LS.Areg(r2)] + cont;
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert na == [LS.Areg(r1)] + ([LS.Areg(r2)] + cont);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        AR.ActionsRepLCons(rer, qm, LS.Areg(r2), cont, code, e1, pcmid);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        AR.ActionsRepLCons(rer, qm, LS.Areg(r1), [LS.Areg(r2)] + cont, code, pc, e1);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert AR.ActionsRepL(rer, qm, na, code, pc);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert EL.PikeLkActionsRec(na) by {
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          EL.PikeLkActionsRecConsIff(LS.Areg(r2), cont);
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          EL.PikeLkActionsRecConsIff(LS.Areg(r1), [LS.Areg(r2)] + cont);
        }
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert CW.BoolTreeLkX(rer, na, inp, b, tb);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert LS.ActionsRegexSize(acts) == RegSz(r1) + RegSz(r2) + 1 + LS.ActionsRegexSize(cont);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert LS.ActionsRegexSize(na) == RegSz(r1) + RegSz(r2) + LS.ActionsRegexSize(cont);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert ATR.MsizeA(na) < ATR.MsizeA(acts);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        GateAheadClearSeqExpand(acts, r1, r2, gm);
        // NoDupSeq(AllDefsActs(na)) == NoDupSeq(AllDefsActs(acts)) (same sequence).
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        M.AllDefsActsCons(acts[0], cont);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        M.AllDefsActsCons(LS.Areg(r1), [LS.Areg(r2)] + cont);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        M.AllDefsActsCons(LS.Areg(r2), cont);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert L.DefGroups(L.Sequence(r1, r2)) == L.DefGroups(r1) + L.DefGroups(r2);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert L.DefGroups(r1) + (L.DefGroups(r2) + M.AllDefsActs(cont))
            == (L.DefGroups(r1) + L.DefGroups(r2)) + M.AllDefsActs(cont);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert M.AllDefsActs(na) == M.AllDefsActs(acts);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        WalkDefsOkSeqExpand(acts, r1, r2);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        WalkPairLkAtCheckOracleCoreRec(rer, qm, code, inp, tb, gm, pc, b, na, lid);
      case Quantified(greedy, min, delta, r1) =>
        if min == 0 && delta == LN.NN(0) {
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          assert acts[0] == LS.Areg(L.Quantified(greedy, 0, LN.NN(0), r1));
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          assert AR.NfaRepL(rer, qm, L.Quantified(greedy, 0, LN.NN(0), r1), code, pc, pcmid);
          var em: nat :| AR.NfaRepMinL(rer, qm, 0, r1, code, pc, em)
                         && AR.NfaRepOptL(rer, qm, 0, greedy, r1, code, em, pcmid);
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          NfaRepMinLHeadPin(rer, qm, 0, r1, code, pc, em);
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          NfaRepOptLHeadPin(rer, qm, 0, greedy, r1, code, em, pcmid);
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          assert pcmid == pc;
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          assert AR.ActionsRepL(rer, qm, cont, code, pc);
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          assert CW.BoolTreeLkX(rer, cont, inp, b, tb);
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          assert ATR.MsizeA(cont) < ATR.MsizeA(acts);
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          GateAheadClearTail(acts, gm);
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          WalkDefsOkTail(acts);
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          WalkPairLkAtCheckOracleCoreRec(rer, qm, code, inp, tb, gm, pc, b, cont, lid);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        } else {
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          assert acts[0] == LS.Areg(L.Quantified(greedy, min, delta, r1));
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          assert AR.NfaRepL(rer, qm, L.Quantified(greedy, min, delta, r1), code, pc, pcmid);
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          QuantHeadPinsForkOrSQC(rer, qm, greedy, min, delta, r1, code, pc, pcmid);
        }
      case LookaroundR(lk0, r1) =>
        var lid0: int :| NR.GetPcRE(code, pc) == Some(if AR.PositiveL(lk0) then RB.CheckOracle(lid0)
                                                                           else RB.NegCheckOracle(lid0))
                         && lid0 in qm.looks && qm.looks[lid0] == (lk0, r1) && pcmid == pc + 1;
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert AR.PositiveL(lk0) && lid0 == lid;
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert L.Positivity(lk0);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert lid in qm.looks && qm.looks[lid] == (lk0, r1);
        // the gate is pending at index 0 ⟹ its body groups are clear NOW
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert RegexTopGate(L.LookaroundR(lk0, r1), lk0, r1);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert GatePending(acts, lk0, r1) by {
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          assert acts[0].Areg? && RegexTopGate(acts[0].r, lk0, r1);
        }
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert forall gg :: gg in L.DefGroups(r1) ==> gg !in gm;
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        CW.GateNodeAtInpX(rer, acts, inp, b, tb, lk0, r1);   // tb is LK/LKFail with LkGateOk
        var bit := LOr.view_get_oracle(qm.ov, TR_CpOf(inp), lid);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        if tb.LK? {
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          assert EL.LkGateOk(rer, lk0, r1, inp, tb.tlk, true);
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          assert CW.BoolTreeLkX(rer, cont, inp, b, tb.t);
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          assert AR.ActionsRepL(rer, qm, cont, code, pc + 1);
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          assert bit;
          // ---- gate-frame facts for LkResultAgreeOutsideNested ----
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          assert r0 == L.LookaroundR(lk0, r1);
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          assert EL.PikeLkRegexRec(r1);                                     // NoLkBrL(r1)
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          assert LS.LkResult(lk0, tb.tlk, LG.Empty, inp).Some?;       // LkGateOk true
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          EL.LkResultGmIndep(lk0, tb.tlk, gm, inp);
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          assert LS.LkResult(lk0, tb.tlk, gm, inp).Some?;
          var gm2 := LS.LkResult(lk0, tb.tlk, gm, inp).value;
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          assert tb.tlk == LFU.ComputeTr(rer, [LS.Areg(r1)], inp, LG.Empty, L.LkDir(lk0));   // LkGateOk
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          LkResultAgreeOutsideNested(rer, lk0, r1, inp, tb.tlk, gm);        // GmAgreeOutside(gm2, gm, Sr1)
          var Sr1 := set gx | gx in L.DefGroups(r1);
          // AfterMerge req (2): gm2 keys ⊆ gm ∪ DefGroups(r1).
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          assert forall gg :: gg in gm2 ==> gg in gm || gg in L.DefGroups(r1) by {
            assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
            forall gg | gg in gm2 ensures gg in gm || gg in L.DefGroups(r1) {
              if gg !in Sr1 { assert gg in gm2 <==> gg in gm; assert gg in gm; }
              else { assert gg in L.DefGroups(r1); }
            }
          }
          // AfterMerge req (3): pending-in-cont ⟹ pending-in-acts.
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          assert forall lk2: L.Lookaround, r2: L.Regex :: GatePending(cont, lk2, r2) ==> GatePending(acts, lk2, r2) by {
            assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
            forall lk2: L.Lookaround, r2: L.Regex | GatePending(cont, lk2, r2)
              ensures GatePending(acts, lk2, r2)
            { GatePendingTail(acts, lk2, r2); }
          }
          // AfterMerge req (4): every other pending gate's body disjoint from
          // DefGroups(r1) — from C1 (TopLk NoDup): the head gate contributes
          // DefGroups(r1) as a block, pending bodies in cont sit inside
          // TopLkDefsListActs(cont) (RegexTopGateSubTopLk).
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          TopLkDefsListActsCons(acts[0], cont);
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          assert TopLkDefsList(L.LookaroundR(lk0, r1)) == L.DefGroups(r1);
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          assert TopLkDefsListActs(acts) == L.DefGroups(r1) + TopLkDefsListActs(cont);
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          M.NoDupConcat(L.DefGroups(r1), TopLkDefsListActs(cont));
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          assert forall lk2: L.Lookaround, r2: L.Regex :: GatePending(cont, lk2, r2) ==>
                                                            (forall gg :: gg in L.DefGroups(r2) ==> gg !in L.DefGroups(r1)) by {
            assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
            forall lk2: L.Lookaround, r2: L.Regex | GatePending(cont, lk2, r2)
              ensures forall gg :: gg in L.DefGroups(r2) ==> gg !in L.DefGroups(r1)
            {
              var j :| 0 <= j < |cont| && cont[j].Areg? && RegexTopGate(cont[j].r, lk2, r2);
              RegexTopGateSubTopLk(cont[j].r, lk2, r2);     // set(DefGroups r2) ⊆ set(TopLk cont[j].r)
              TopLkDefsListMemberSub(cont, j);              // set(TopLk cont[j].r) ⊆ set(TopLkActs cont)
              var SR2 := set gx | gx in L.DefGroups(r2);
              var SCJ := set gx | gx in TopLkDefsList(cont[j].r);
              var SAC := set gx | gx in TopLkDefsListActs(cont);
              var SR1 := set gx | gx in L.DefGroups(r1);
              assert SR2 <= SCJ && SCJ <= SAC;              // the two lemma subsets (named-set form)
              assert SR1 * SAC == {};                       // NoDupConcat disjointness
              forall gg | gg in L.DefGroups(r2) ensures gg !in L.DefGroups(r1) {
                assert gg in SR2;
                assert gg in SAC;                           // via SR2 ⊆ SCJ ⊆ SAC
                if gg in L.DefGroups(r1) {                   // contradiction: SR1 ∩ SAC == {}
                  assert gg in SR1 && gg in SAC;
                  assert gg in SR1 * SAC;
                  assert false;
                }
              }
            }
          }
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          GateAheadClearAfterMerge(acts, cont, gm, gm2, lk0, r1);   // GateAheadClear(cont, gm2)
          // Assemble WalkPairLkRec(tb.t, gm2, pc+1, g) via the existential disjunct.
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          assert EL.PikeLkActionsRec(cont);
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          WalkDefsOkTail(acts);
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          assert AR.ActionsRepL(rer, qm, cont, code, pc + 1)
                 && EL.PikeLkActionsRec(cont)
                 && ATR.EaOf(b) == g
                 && CW.BoolTreeLkX(rer, cont, inp, b, tb.t)
                 && GateAheadClear(cont, gm2)
                 && WalkDefsOk(cont);
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          assert WalkPairLkRec(rer, qm, code, inp, tb.t, gm2, pc + 1, g);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        } else {
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          assert tb.LKFail?;   // GateNodeAtInp: only LK or LKFail
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          assert !bit;
        }
      case Character(_) =>   // pins Consume — not CheckOracle
      case Disjunction(_, _) =>   // pins Fork — not CheckOracle
      case Group(_, _) =>   // pins SetRegisterToCP — not CheckOracle
      case AnchorR(_) =>   // pins AnchorAssertion — not CheckOracle
      case Backreference(_) =>   // NfaRepL false
  }

  lemma WalkPairLkAtCheckOracleRec(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                                   tb: LT.Tree, gm: LG.GroupMap, pc: nat, ea: bool, lid: int)
    requires WalkPairLkRec(rer, qm, code, inp, tb, gm, pc, ea)
    requires NR.GetPcRE(code, pc) == Some(RB.CheckOracle(lid))
    requires LL.OracleOkAt(rer, qm, inp)
    ensures lid in qm.looks
    ensures var (lk, r1) := qm.looks[lid];
            (LOr.view_get_oracle(qm.ov, TR_CpOf(inp), lid) ==>
               tb.LK? && tb.lk == lk
               && EL.LkGateOk(rer, lk, r1, inp, tb.tlk, true)
               && LS.LkResult(lk, tb.tlk, gm, inp).Some?
               && WalkPairLkRec(rer, qm, code, inp, tb.t, LS.LkResult(lk, tb.tlk, gm, inp).value, pc + 1, ea))
            && (!LOr.view_get_oracle(qm.ov, TR_CpOf(inp), lid) ==>
                  tb.LKFail? && tb.lk == lk
                  && EL.LkGateOk(rer, lk, r1, inp, tb.tlk, false))
    ensures forall gg :: gg in L.DefGroups(qm.looks[lid].1) ==> gg !in gm
  {
    // GetPcRE==CheckOracle ≠ BeginLoop kills the stutter disjunct; extract the walk.
    var acts: LS.Actions, b: BS.LoopBool :|
      AR.ActionsRepL(rer, qm, acts, code, pc)
      && EL.PikeLkActionsRec(acts)
      && ATR.EaOf(b) == ea
      && CW.BoolTreeLkX(rer, acts, inp, b, tb)
      && GateAheadClear(acts, gm)
      && WalkDefsOk(acts);
    WalkPairLkAtCheckOracleCoreRec(rer, qm, code, inp, tb, gm, pc, b, acts, lid);
  }

  lemma WalkPairLkAtAnchorCoreRec(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                                  tb: LT.Tree, gm: LG.GroupMap, pc: nat, b: BS.LoopBool,
                                  acts: LS.Actions, a: R.anchor)
    requires AR.ActionsRepL(rer, qm, acts, code, pc)
    requires EL.PikeLkActionsRec(acts)
    requires CW.BoolTreeLkX(rer, acts, inp, b, tb)
    requires NR.GetPcRE(code, pc) == Some(RB.AnchorAssertion(a))
    requires GateAheadClear(acts, gm)
    requires WalkDefsOk(acts)
    ensures tb.AnchorPass? || tb == LT.Mismatch
    ensures tb.AnchorPass? ==> WalkPairLkRec(rer, qm, code, inp, tb.t, gm, pc + 1, ATR.EaOf(b))
    decreases ATR.MsizeA(acts)
  {
    var g := ATR.EaOf(b);
    var pcmid: nat :| AR.ActionRepL(rer, qm, acts[0], code, pc, pcmid) && AR.ActionsRepL(rer, qm, acts[1..], code, pcmid);
    EL.PikeLkActionsRecTail(acts);
    assert acts == [acts[0]] + acts[1..];
    EL.PikeLkActionsRecConsIff(acts[0], acts[1..]);
    var cont := acts[1..];
    match acts[0]
    case Acheck(_) =>   // pins EndLoop / backward Fork — not AnchorAssertion
    case Aclose(_) =>   // pins SetRegisterToCP — not AnchorAssertion
    case Areg(r0) =>
      assert EL.PikeLkRegexRec(r0);
      match r0
      case Epsilon =>
        assert pcmid == pc;
        assert CW.BoolTreeLkX(rer, cont, inp, b, tb);
        assert ATR.MsizeA(cont) < ATR.MsizeA(acts);
        GateAheadClearTail(acts, gm);
        WalkDefsOkTail(acts);
        WalkPairLkAtAnchorCoreRec(rer, qm, code, inp, tb, gm, pc, b, cont, a);
      case Sequence(r1, r2) =>
        assert acts[0] == LS.Areg(L.Sequence(r1, r2));
        assert AR.NfaRepL(rer, qm, L.Sequence(r1, r2), code, pc, pcmid);
        var e1: nat :| AR.NfaRepL(rer, qm, r1, code, pc, e1) && AR.NfaRepL(rer, qm, r2, code, e1, pcmid);
        var na := [LS.Areg(r1), LS.Areg(r2)] + cont;
        assert na == [LS.Areg(r1)] + ([LS.Areg(r2)] + cont);
        AR.ActionsRepLCons(rer, qm, LS.Areg(r2), cont, code, e1, pcmid);
        AR.ActionsRepLCons(rer, qm, LS.Areg(r1), [LS.Areg(r2)] + cont, code, pc, e1);
        assert AR.ActionsRepL(rer, qm, na, code, pc);
        assert EL.PikeLkActionsRec(na) by {
          EL.PikeLkActionsRecConsIff(LS.Areg(r2), cont);
          EL.PikeLkActionsRecConsIff(LS.Areg(r1), [LS.Areg(r2)] + cont);
        }
        assert CW.BoolTreeLkX(rer, na, inp, b, tb);
        assert LS.ActionsRegexSize(acts) == RegSz(r1) + RegSz(r2) + 1 + LS.ActionsRegexSize(cont);
        assert LS.ActionsRegexSize(na) == RegSz(r1) + RegSz(r2) + LS.ActionsRegexSize(cont);
        assert ATR.MsizeA(na) < ATR.MsizeA(acts);
        GateAheadClearSeqExpand(acts, r1, r2, gm);
        M.AllDefsActsCons(acts[0], cont);
        M.AllDefsActsCons(LS.Areg(r1), [LS.Areg(r2)] + cont);
        M.AllDefsActsCons(LS.Areg(r2), cont);
        assert L.DefGroups(L.Sequence(r1, r2)) == L.DefGroups(r1) + L.DefGroups(r2);
        assert L.DefGroups(r1) + (L.DefGroups(r2) + M.AllDefsActs(cont))
            == (L.DefGroups(r1) + L.DefGroups(r2)) + M.AllDefsActs(cont);
        assert M.AllDefsActs(na) == M.AllDefsActs(acts);
        WalkDefsOkSeqExpand(acts, r1, r2);
        WalkPairLkAtAnchorCoreRec(rer, qm, code, inp, tb, gm, pc, b, na, a);
      case Quantified(greedy, min, delta, r1) =>
        if min == 0 && delta == LN.NN(0) {
          assert acts[0] == LS.Areg(L.Quantified(greedy, 0, LN.NN(0), r1));
          assert AR.NfaRepL(rer, qm, L.Quantified(greedy, 0, LN.NN(0), r1), code, pc, pcmid);
          var em: nat :| AR.NfaRepMinL(rer, qm, 0, r1, code, pc, em)
                         && AR.NfaRepOptL(rer, qm, 0, greedy, r1, code, em, pcmid);
          NfaRepMinLHeadPin(rer, qm, 0, r1, code, pc, em);
          NfaRepOptLHeadPin(rer, qm, 0, greedy, r1, code, em, pcmid);
          assert pcmid == pc;
          assert AR.ActionsRepL(rer, qm, cont, code, pc);
          assert CW.BoolTreeLkX(rer, cont, inp, b, tb);
          assert ATR.MsizeA(cont) < ATR.MsizeA(acts);
          GateAheadClearTail(acts, gm);
          WalkDefsOkTail(acts);
          WalkPairLkAtAnchorCoreRec(rer, qm, code, inp, tb, gm, pc, b, cont, a);
        } else {
          assert acts[0] == LS.Areg(L.Quantified(greedy, min, delta, r1));
          assert AR.NfaRepL(rer, qm, L.Quantified(greedy, min, delta, r1), code, pc, pcmid);
          QuantHeadPinsForkOrSQC(rer, qm, greedy, min, delta, r1, code, pc, pcmid);
        }
      case AnchorR(la) =>
        var a2: R.anchor :| NR.GetPcRE(code, pc) == Some(RB.AnchorAssertion(a2)) && T.TrAnchor(a2) == la;
        assert pcmid == pc + 1;
        if LS.AnchorSatisfied(rer, la, inp) {
          assert tb.AnchorPass? && CW.BoolTreeLkX(rer, cont, inp, b, tb.t);
          assert AR.ActionsRepL(rer, qm, cont, code, pc + 1);
          // gm UNCHANGED across AnchorPass ⟹ tail bricks give the continuation clear.
          GateAheadClearTail(acts, gm);       // GateAheadClear(cont, gm)
          WalkDefsOkTail(acts);             // NoDupSeq(AllDefsActs(cont))
          assert EL.PikeLkActionsRec(cont);
          assert WalkPairLkRec(rer, qm, code, inp, tb.t, gm, pc + 1, g);
        } else {
          assert tb == LT.Mismatch;
        }
      case Character(_) =>   // pins Consume — not AnchorAssertion
      case Disjunction(_, _) =>   // pins Fork — not AnchorAssertion
      case Group(_, _) =>   // pins SetRegisterToCP — not AnchorAssertion
      case LookaroundR(_, _) =>   // pins CheckOracle/NegCheckOracle — not AnchorAssertion
      case Backreference(_) =>   // NfaRepL false
  }

  lemma WalkPairLkAtAnchorRec(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                              tb: LT.Tree, gm: LG.GroupMap, pc: nat, ea: bool, a: R.anchor)
    requires WalkPairLkRec(rer, qm, code, inp, tb, gm, pc, ea)
    requires NR.GetPcRE(code, pc) == Some(RB.AnchorAssertion(a))
    ensures tb.AnchorPass? || tb == LT.Mismatch
    ensures tb.AnchorPass? ==> WalkPairLkRec(rer, qm, code, inp, tb.t, gm, pc + 1, ea)
  {
    var acts: LS.Actions, b: BS.LoopBool :|
      AR.ActionsRepL(rer, qm, acts, code, pc)
      && EL.PikeLkActionsRec(acts)
      && ATR.EaOf(b) == ea
      && CW.BoolTreeLkX(rer, acts, inp, b, tb)
      && GateAheadClear(acts, gm)
      && WalkDefsOk(acts);
    WalkPairLkAtAnchorCoreRec(rer, qm, code, inp, tb, gm, pc, b, acts, a);
  }

  lemma WalkPairLkAtSetRegCoreRec(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                                  tb: LT.Tree, gm: LG.GroupMap, pc: nat, b: BS.LoopBool,
                                  acts: LS.Actions, r: int)
    requires AR.ActionsRepL(rer, qm, acts, code, pc)
    requires EL.PikeLkActionsRec(acts)
    requires CW.BoolTreeLkX(rer, acts, inp, b, tb)
    requires NR.GetPcRE(code, pc) == Some(RB.SetRegisterToCP(r))
    requires GateAheadClear(acts, gm)
    requires WalkDefsOk(acts)
    ensures tb.GroupActionT?
    ensures (tb.g.Open? && r == CP.start_reg(tb.g.g as int))
            || (tb.g.Close? && r == CP.end_reg(tb.g.g as int))
    ensures WalkPairLkRec(rer, qm, code, inp, tb.t, LG.GMUpdate(tb.g, LC.Idx(inp), gm), pc + 1, ATR.EaOf(b))
    decreases ATR.MsizeA(acts)
  {
    var g := ATR.EaOf(b);
    var pcmid: nat :| AR.ActionRepL(rer, qm, acts[0], code, pc, pcmid) && AR.ActionsRepL(rer, qm, acts[1..], code, pcmid);
    assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
    EL.PikeLkActionsRecTail(acts);
    assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
    assert acts == [acts[0]] + acts[1..];
    assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
    EL.PikeLkActionsRecConsIff(acts[0], acts[1..]);
    var cont := acts[1..];
    match acts[0]
    case Acheck(_) =>   // pins EndLoop / backward Fork — not SetRegisterToCP
    case Aclose(gid) =>
      assert pcmid == pc + 1 && r == CP.end_reg(gid as int);
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert tb.GroupActionT? && tb.g == LG.Close(gid) && CW.BoolTreeLkX(rer, cont, inp, b, tb.t);
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert AR.ActionsRepL(rer, qm, cont, code, pc + 1);
      var gm2 := LG.GMUpdate(LG.Close(gid), LC.Idx(inp), gm);
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert gm2 == LG.GMClose(LC.Idx(inp), gid, gm);
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      GateAheadClearTail(acts, gm);
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      GateAheadClearMono(cont, gm, gm2);   // GMClose keeps the domain
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      WalkDefsOkTail(acts);
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert EL.PikeLkActionsRec(cont);
      assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
      assert WalkPairLkRec(rer, qm, code, inp, tb.t, gm2, pc + 1, g);
    case Areg(r0) =>
      assert EL.PikeLkRegexRec(r0);
      match r0
      case Epsilon =>
        assert pcmid == pc;
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert CW.BoolTreeLkX(rer, cont, inp, b, tb);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert ATR.MsizeA(cont) < ATR.MsizeA(acts);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        GateAheadClearTail(acts, gm);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        WalkDefsOkTail(acts);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        WalkPairLkAtSetRegCoreRec(rer, qm, code, inp, tb, gm, pc, b, cont, r);
      case Sequence(r1, r2) =>
        assert acts[0] == LS.Areg(L.Sequence(r1, r2));
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert AR.NfaRepL(rer, qm, L.Sequence(r1, r2), code, pc, pcmid);
        var e1: nat :| AR.NfaRepL(rer, qm, r1, code, pc, e1) && AR.NfaRepL(rer, qm, r2, code, e1, pcmid);
        var na := [LS.Areg(r1), LS.Areg(r2)] + cont;
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert na == [LS.Areg(r1)] + ([LS.Areg(r2)] + cont);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        AR.ActionsRepLCons(rer, qm, LS.Areg(r2), cont, code, e1, pcmid);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        AR.ActionsRepLCons(rer, qm, LS.Areg(r1), [LS.Areg(r2)] + cont, code, pc, e1);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert AR.ActionsRepL(rer, qm, na, code, pc);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert EL.PikeLkActionsRec(na) by {
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          EL.PikeLkActionsRecConsIff(LS.Areg(r2), cont);
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          EL.PikeLkActionsRecConsIff(LS.Areg(r1), [LS.Areg(r2)] + cont);
        }
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert CW.BoolTreeLkX(rer, na, inp, b, tb);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert LS.ActionsRegexSize(acts) == RegSz(r1) + RegSz(r2) + 1 + LS.ActionsRegexSize(cont);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert LS.ActionsRegexSize(na) == RegSz(r1) + RegSz(r2) + LS.ActionsRegexSize(cont);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert ATR.MsizeA(na) < ATR.MsizeA(acts);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        GateAheadClearSeqExpand(acts, r1, r2, gm);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        M.AllDefsActsCons(acts[0], cont);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        M.AllDefsActsCons(LS.Areg(r1), [LS.Areg(r2)] + cont);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        M.AllDefsActsCons(LS.Areg(r2), cont);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert L.DefGroups(L.Sequence(r1, r2)) == L.DefGroups(r1) + L.DefGroups(r2);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert L.DefGroups(r1) + (L.DefGroups(r2) + M.AllDefsActs(cont))
            == (L.DefGroups(r1) + L.DefGroups(r2)) + M.AllDefsActs(cont);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert M.AllDefsActs(na) == M.AllDefsActs(acts);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        WalkDefsOkSeqExpand(acts, r1, r2);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        WalkPairLkAtSetRegCoreRec(rer, qm, code, inp, tb, gm, pc, b, na, r);
      case Group(gid, r1) =>
        var e1: nat :| NR.GetPcRE(code, pc) == Some(RB.SetRegisterToCP(CP.start_reg(gid as int)))
                       && AR.NfaRepL(rer, qm, r1, code, pc + 1, e1)
                       && NR.GetPcRE(code, e1) == Some(RB.SetRegisterToCP(CP.end_reg(gid as int)))
                       && pcmid == e1 + 1;
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert r == CP.start_reg(gid as int);
        var ga := [LS.Areg(r1), LS.Aclose(gid)] + cont;
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert ga == [LS.Areg(r1)] + ([LS.Aclose(gid)] + cont);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        AR.ActionsRepLCons(rer, qm, LS.Aclose(gid), cont, code, e1, pcmid);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        AR.ActionsRepLCons(rer, qm, LS.Areg(r1), [LS.Aclose(gid)] + cont, code, pc + 1, e1);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert AR.ActionsRepL(rer, qm, ga, code, pc + 1);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert tb.GroupActionT? && tb.g == LG.Open(gid) && CW.BoolTreeLkX(rer, ga, inp, b, tb.t);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert EL.PikeLkActionsRec(ga) by {
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          EL.PikeLkActionsRecConsIff(LS.Aclose(gid), cont);
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          EL.PikeLkActionsRecConsIff(LS.Areg(r1), [LS.Aclose(gid)] + cont);
        }
        var gm2 := LG.GMUpdate(LG.Open(gid), LC.Idx(inp), gm);
        // carrier across the Group expand; C1 pins gid ∉ TopLk of both parts
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        WalkDefsOkGroupExpand(acts, gid, r1);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        TopLkDefsListActsCons(acts[0], cont);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        TopLkDefsListActsCons(LS.Areg(r1), [LS.Aclose(gid)] + cont);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        TopLkDefsListActsCons(LS.Aclose(gid), cont);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert TopLkDefsList(L.Group(gid, r1)) == [gid] + TopLkDefsList(r1);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert TopLkDefsListActs(acts)
            == ([gid] + TopLkDefsList(r1)) + TopLkDefsListActs(cont);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert ([gid] + TopLkDefsList(r1)) + TopLkDefsListActs(cont)
            == [gid] + (TopLkDefsList(r1) + TopLkDefsListActs(cont));
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        M.NoDupConcat([gid], TopLkDefsList(r1) + TopLkDefsListActs(cont));
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert TopLkDefsListActs(ga) == TopLkDefsList(r1) + TopLkDefsListActs(cont);
        // GateAheadClear(ga, gm): pending-in-ga ⟹ pending-in-acts.
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert forall lk2: L.Lookaround, rr: L.Regex :: GatePending(ga, lk2, rr) ==> GatePending(acts, lk2, rr) by {
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          forall lk2: L.Lookaround, rr: L.Regex | GatePending(ga, lk2, rr) ensures GatePending(acts, lk2, rr) {
            assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
            GatePendingGroupBack(acts, gid, r1, lk2, rr);
          }
        }
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert GateAheadClear(ga, gm) by {
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          forall lk2: L.Lookaround, rr: L.Regex | GatePending(ga, lk2, rr)
            ensures forall gg :: gg in L.DefGroups(rr) ==> gg !in gm
          { GatePendingGroupBack(acts, gid, r1, lk2, rr); }
        }
        // gid ∉ every pending body of ga (via C1: gid ∉ TopLkDefsListActs(ga) ⊇ DefGroups(rr)).
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert forall lk2: L.Lookaround, rr: L.Regex :: GatePending(ga, lk2, rr) ==> gid !in L.DefGroups(rr) by {
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          forall lk2: L.Lookaround, rr: L.Regex | GatePending(ga, lk2, rr) ensures gid !in L.DefGroups(rr) {
            var j :| 0 <= j < |ga| && ga[j].Areg? && RegexTopGate(ga[j].r, lk2, rr);
            assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
            RegexTopGateSubTopLk(ga[j].r, lk2, rr);
            assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
            TopLkDefsListMemberSub(ga, j);
            var SRR := set gx | gx in L.DefGroups(rr);
            var SGJ := set gx | gx in TopLkDefsList(ga[j].r);
            var SAG := set gx | gx in TopLkDefsListActs(ga);
            assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
            assert SRR <= SGJ && SGJ <= SAG;   // the two lemma subsets (named-set form)
            assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
            assert (set gx | gx in [gid]) * SAG == {};   // NoDupConcat disjointness
            assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
            if gid in L.DefGroups(rr) {
              assert gid in SRR && gid in SAG;           // via SRR ⊆ SGJ ⊆ SAG
              assert gid in (set gx | gx in [gid]);
              assert gid in (set gx | gx in [gid]) * SAG;   // contradicts disjoint
            }
          }
        }
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        GateAheadClearAfterOpen(ga, gm, gid, LC.Idx(inp));   // GateAheadClear(ga, gm2)
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        assert WalkPairLkRec(rer, qm, code, inp, tb.t, gm2, pc + 1, g);
      case Quantified(greedy, min, delta, r1) =>
        if min == 0 && delta == LN.NN(0) {
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          assert acts[0] == LS.Areg(L.Quantified(greedy, 0, LN.NN(0), r1));
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          assert AR.NfaRepL(rer, qm, L.Quantified(greedy, 0, LN.NN(0), r1), code, pc, pcmid);
          var em: nat :| AR.NfaRepMinL(rer, qm, 0, r1, code, pc, em)
                         && AR.NfaRepOptL(rer, qm, 0, greedy, r1, code, em, pcmid);
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          NfaRepMinLHeadPin(rer, qm, 0, r1, code, pc, em);
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          NfaRepOptLHeadPin(rer, qm, 0, greedy, r1, code, em, pcmid);
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          assert pcmid == pc;
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          assert AR.ActionsRepL(rer, qm, cont, code, pc);
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          assert CW.BoolTreeLkX(rer, cont, inp, b, tb);
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          assert ATR.MsizeA(cont) < ATR.MsizeA(acts);
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          GateAheadClearTail(acts, gm);
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          WalkDefsOkTail(acts);
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          WalkPairLkAtSetRegCoreRec(rer, qm, code, inp, tb, gm, pc, b, cont, r);
        assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
        } else {
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          assert acts[0] == LS.Areg(L.Quantified(greedy, min, delta, r1));
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          assert AR.NfaRepL(rer, qm, L.Quantified(greedy, min, delta, r1), code, pc, pcmid);
          assert {:split_here} true;   // (2026-09-06) per-step batch under z3 4.14
          QuantHeadPinsForkOrSQC(rer, qm, greedy, min, delta, r1, code, pc, pcmid);
        }
      case Character(_) =>   // pins Consume — not SetRegisterToCP
      case Disjunction(_, _) =>   // pins Fork — not SetRegisterToCP
      case LookaroundR(_, _) =>   // pins CheckOracle/NegCheckOracle — not SetRegisterToCP
      case AnchorR(_) =>   // pins AnchorAssertion — not SetRegisterToCP
      case Backreference(_) =>   // NfaRepL false
  }

  lemma WalkPairLkAtSetRegRec(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                              tb: LT.Tree, gm: LG.GroupMap, pc: nat, ea: bool, r: int)
    requires WalkPairLkRec(rer, qm, code, inp, tb, gm, pc, ea)
    requires NR.GetPcRE(code, pc) == Some(RB.SetRegisterToCP(r))
    ensures tb.GroupActionT?
    ensures (tb.g.Open? && r == CP.start_reg(tb.g.g as int))
            || (tb.g.Close? && r == CP.end_reg(tb.g.g as int))
    ensures WalkPairLkRec(rer, qm, code, inp, tb.t, LG.GMUpdate(tb.g, LC.Idx(inp), gm), pc + 1, ea)
  {
    var acts: LS.Actions, b: BS.LoopBool :|
      AR.ActionsRepL(rer, qm, acts, code, pc)
      && EL.PikeLkActionsRec(acts)
      && ATR.EaOf(b) == ea
      && CW.BoolTreeLkX(rer, acts, inp, b, tb)
      && GateAheadClear(acts, gm)
      && WalkDefsOk(acts);
    WalkPairLkAtSetRegCoreRec(rer, qm, code, inp, tb, gm, pc, b, acts, r);
  }

  /** A `Reset` only removes keys: pending gates stay clear. */
  lemma GateAheadClearReset(acts: LS.Actions, gidl: LG.GroupSet, gm: LG.GroupMap)
    requires GateAheadClear(acts, gm)
    ensures GateAheadClear(acts, LG.GMReset(gidl, gm))
  {
    forall lk: L.Lookaround, rr: L.Regex | GatePending(acts, lk, rr)
      ensures forall gg :: gg in L.DefGroups(rr) ==> gg !in LG.GMReset(gidl, gm)
    {
      forall gg | gg in L.DefGroups(rr) ensures gg !in LG.GMReset(gidl, gm) {
        assert gg !in gm;
        assert LG.GMReset(gidl, gm) == gm - (set gx | gx in gidl);
      }
    }
  }

  /** (§2.5b F-c) THE CIN HEAD FORK `Fork(em + 1, e1 + 2)` under the walk: the
      engine-shaped tree's loop arm walks through the clock-mark and the
      BeginLoop into the iteration list at `em + 3`; its stamp arm walks through
      the stamp's Reset (the new see-through) into the continuation at `e1 + 3`. */
  lemma WalkPairLkCinHeadArmsRec(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                                 tb: LT.Tree, gm: LG.GroupMap, pc: nat, b: BS.LoopBool,
                                 acts: LS.Actions, cont: LS.Actions, pcmid: nat, r1: L.Regex, x: int, y: int)
    requires |acts| > 0 && cont == acts[1..]
    requires acts[0] == LS.Areg(L.Quantified(true, 1, LN.Inf, r1)) && !NUL.NonNullableL(r1)
    requires AR.ActionRepL(rer, qm, acts[0], code, pc, pcmid) && AR.ActionsRepL(rer, qm, cont, code, pcmid)
    requires EL.PikeLkActionsRec(acts) && EL.PikeLkActionsRec(cont)
    requires CW.BoolTreeLkX(rer, acts, inp, b, tb)
    requires NR.GetPcRE(code, pc) == Some(RB.Fork(x, y))
    requires GateAheadClear(acts, gm) && WalkDefsOk(acts)
    ensures x >= 0 && y >= 0
    ensures exists ta1: LT.Tree, ta2: LT.Tree ::
              CE.ProgErase(tb) == LT.Choice(CE.ProgErase(ta1), CE.ProgErase(ta2))
              && WalkPairLkRec(rer, qm, code, inp, ta1, gm, x as nat, ATR.EaOf(b))
              && WalkPairLkRec(rer, qm, code, inp, ta2, gm, y as nat, ATR.EaOf(b))
  {
    hide NUL.NonNullableL, NUL.CINullableL, NUL.NoNulledPlusL, AR.NfaRepCinL, AR.NfaRepStarCinL;
    var g := ATR.EaOf(b);
    var gidl := L.DefGroups(r1);
    assert AR.NfaRepL(rer, qm, L.Quantified(true, 1, LN.Inf, r1), code, pc, pcmid);
    var em, e1x := AR.NfaRepLCinInv(rer, qm, true, 1, r1, code, pc, pcmid);
    var qidC: int :| NR.GetPcRE(code, em + 1) == Some(RB.SetQuantToClock(qidC, false))
                     && NR.GetPcRE(code, e1x + 2) == Some(RB.SetQuantToClock(qidC, true))
                     && qidC in qm.quants && qm.quants[qidC] == gidl
                     && AR.StampBodyOk(qm, qidC, r1);
    assert em == pc;
    AR.NfaRepIncrL(rer, qm, r1, code, em + 3, e1x);
    assert x == pc + 1 && y == e1x + 2;
    CW.CinGreedyIntro(r1);
    var q0 := L.Quantified(true, 0, LN.Inf, r1);
    var ia := [LS.Areg(r1), LS.Acheck(inp), LS.Areg(q0)] + cont;
    assert ia == [LS.Areg(r1)] + ([LS.Acheck(inp)] + ([LS.Areg(q0)] + cont));
    match tb {
      case Choice(ta, tbb) =>
        match ta {
          case GroupActionT(g1, ti) =>
            match tbb {
              case GroupActionT(h1, tc) =>
                assert g1 == LG.Reset(gidl) && h1 == LG.Reset(gidl);
                assert CW.BoolTreeLkX(rer, ia, inp, BS.CannotExit, ti);
                assert CW.BoolTreeLkX(rer, cont, inp, b, tc);
                assert EL.PikeLkActionRec(acts[0]);
                assert EL.PikeLkRegexRec(r1) && EL.PikeLkRegexRec(q0);
                EL.PikeLkActionsRecConsIff(LS.Areg(q0), cont);
                EL.PikeLkActionsRecConsIff(LS.Acheck(inp), [LS.Areg(q0)] + cont);
                EL.PikeLkActionsRecConsIff(LS.Areg(r1), [LS.Acheck(inp)] + ([LS.Areg(q0)] + cont));
                assert EL.PikeLkActionsRec(ia);
                assert {:split_here} true;   // (E3) section: the iteration list's representation
                // the iteration list at em + 3 (EndLoop at e1x, the CIN loop view at e1x + 1)
                // (§2.5b pack) with packed deps this section grew past 19 GB (3:22 with
                // source deps), even one ActionsRepLCons call per batch: the list's
                // rep is built in a cut context, only the head reps unfold
                assert AR.ActionsRepL(rer, qm, ia, code, em + 3) by {
                  hide *; reveal AR.ActionRepL;
                  AR.NfaRepLStarCinIntro(rer, qm, r1, code, em, e1x, qidC);
                  assert AR.ActionRepL(rer, qm, LS.Areg(q0), code, e1x + 1, pcmid);
                  AR.ActionsRepLCons(rer, qm, LS.Areg(q0), cont, code, e1x + 1, pcmid);
                  assert AR.ActionRepL(rer, qm, LS.Acheck(inp), code, e1x, e1x + 1);
                  AR.ActionsRepLCons(rer, qm, LS.Acheck(inp), [LS.Areg(q0)] + cont, code, e1x, e1x + 1);
                  assert AR.ActionRepL(rer, qm, LS.Areg(r1), code, em + 3, e1x);
                  AR.ActionsRepLCons(rer, qm, LS.Areg(r1), [LS.Acheck(inp)] + ([LS.Areg(q0)] + cont), code, em + 3, e1x);
                }
                assert {:split_here} true;   // (E3) section: walk invariants + the loop arm
                assert {:split_here} true;   // (E3) section: walk invariants + the arms
            StarArmInvariants(acts, r1, q0, LS.Acheck(inp), gm, gidl);
                GateAheadClearTail(acts, gm);
                WalkDefsOkTail(acts);
                // loop arm at x == em + 1
                StarIterArmWalkBLRec(rer, qm, code, inp, gm, em + 1, g, qidC, r1, ti, ia);
                assert WalkPairLkRec(rer, qm, code, inp, ta, gm, x as nat, g);
                assert {:split_here} true;   // (E3) section: the stamp arm
                // stamp arm at y == e1x + 2: the see-through over the stamp's Reset
                var gm2 := LG.GMUpdate(LG.Reset(gidl), LC.Idx(inp), gm);
                assert gm2 == LG.GMReset(gidl, gm);
                GateAheadClearReset(cont, gidl, gm);
                WalkDefsOkTail(acts);
                // the continuation's walk at pcmid: the explicit (acts, b) witness
                assert AR.ActionsRepL(rer, qm, cont, code, pcmid) && EL.PikeLkActionsRec(cont)
                       && ATR.EaOf(b) == g && CW.BoolTreeLkX(rer, cont, inp, b, tc)
                       && GateAheadClear(cont, gm2) && WalkDefsOk(cont);
                assert WalkPairLkRec(rer, qm, code, inp, tc, gm2, pcmid, g);
                assert e1x + 2 < RB.size(code);
                // the stamp see-through at y: the explicit qid witness
                assert tbb.t == tc && LG.GMUpdate(tbb.g, LC.Idx(inp), gm) == gm2 && pcmid == (e1x + 2) + 1;
                assert (NR.GetPcRE(code, e1x + 2) == Some(RB.SetQuantToClock(qidC, false))
                        || NR.GetPcRE(code, e1x + 2) == Some(RB.SetQuantToClock(qidC, true)))
                       && qidC in qm.quants
                       && tbb.GroupActionT? && tbb.g == LG.Reset(qm.quants[qidC])
                       && WalkPairLkRec(rer, qm, code, inp, tbb.t, LG.GMUpdate(tbb.g, LC.Idx(inp), gm), (e1x + 2) + 1, g);
                assert WalkPairLkRec(rer, qm, code, inp, tbb, gm, y as nat, g);
                assert CE.ProgErase(tb) == LT.Choice(CE.ProgErase(ta), CE.ProgErase(tbb));
              case _ =>
            }
          case _ =>
        }
      case _ =>
    }
  }

  /** (§2.5b F-c) THE CIN LOOP VIEW under the walk, at the end fork
      `Fork(em + 1, e1 + 3)`: the iteration re-enters through the clock-mark and
      the BeginLoop, the exit arm is the continuation at `e1 + 3`. */
  lemma WalkPairLkCinLoopViewArmsRec(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                                     tb: LT.Tree, gm: LG.GroupMap, pc: nat, b: BS.LoopBool,
                                     acts: LS.Actions, cont: LS.Actions, pcmid: nat, r1: L.Regex, x: int, y: int)
    requires |acts| > 0 && cont == acts[1..]
    requires acts[0] == LS.Areg(L.Quantified(true, 0, LN.Inf, r1))
    requires AR.NfaRepStarCinL(rer, qm, r1, code, pc, pcmid)
    requires AR.ActionRepL(rer, qm, acts[0], code, pc, pcmid) && AR.ActionsRepL(rer, qm, cont, code, pcmid)
    requires EL.PikeLkActionsRec(acts) && EL.PikeLkActionsRec(cont)
    requires CW.BoolTreeLkX(rer, acts, inp, b, tb)
    requires NR.GetPcRE(code, pc) == Some(RB.Fork(x, y))
    requires GateAheadClear(acts, gm) && WalkDefsOk(acts)
    ensures x >= 0 && y >= 0
    ensures exists ta1: LT.Tree, ta2: LT.Tree ::
              CE.ProgErase(tb) == LT.Choice(CE.ProgErase(ta1), CE.ProgErase(ta2))
              && WalkPairLkRec(rer, qm, code, inp, ta1, gm, x as nat, ATR.EaOf(b))
              && WalkPairLkRec(rer, qm, code, inp, ta2, gm, y as nat, ATR.EaOf(b))
  {
    hide NUL.NonNullableL, NUL.CINullableL, NUL.NoNulledPlusL, AR.NfaRepCinL, AR.NfaRepStarCinL;
    var g := ATR.EaOf(b);
    var gidl := L.DefGroups(r1);
    var em, e1 := AR.NfaRepLStarCinInv(rer, qm, r1, code, pc, pcmid);
    var qidC: int :| NR.GetPcRE(code, em + 1) == Some(RB.SetQuantToClock(qidC, false))
                     && NR.GetPcRE(code, e1 + 2) == Some(RB.SetQuantToClock(qidC, true))
                     && qidC in qm.quants && qm.quants[qidC] == gidl
                     && AR.StampBodyOk(qm, qidC, r1);
    assert x == em + 1 && y == e1 + 3 && pc == e1 + 1 && pcmid == e1 + 3;
    var q0 := L.Quantified(true, 0, LN.Inf, r1);
    assert FS.NoiPred(LN.Inf) == LN.Inf;
    var ia := [LS.Areg(r1), LS.Acheck(inp), LS.Areg(q0)] + cont;
    assert ia == [LS.Areg(r1)] + ([LS.Acheck(inp)] + ([LS.Areg(q0)] + cont));
    match tb {
      case Choice(ta, skipt) =>
        match ta {
          case GroupActionT(g1, ti) =>
            assert g1 == LG.Reset(gidl);
            assert CW.BoolTreeLkX(rer, ia, inp, BS.CannotExit, ti);
            assert CW.BoolTreeLkX(rer, cont, inp, b, skipt);
            assert EL.PikeLkActionRec(acts[0]);
            assert EL.PikeLkRegexRec(r1) && EL.PikeLkRegexRec(q0);
            EL.PikeLkActionsRecConsIff(LS.Areg(q0), cont);
            EL.PikeLkActionsRecConsIff(LS.Acheck(inp), [LS.Areg(q0)] + cont);
            EL.PikeLkActionsRecConsIff(LS.Areg(r1), [LS.Acheck(inp)] + ([LS.Areg(q0)] + cont));
            assert EL.PikeLkActionsRec(ia);
            assert {:split_here} true;   // (E3) section: the iteration list's representation
            // the iteration list at em + 3: r1 to e1, the EndLoop check, the star at pc
            AR.ActionsRepLCons(rer, qm, LS.Areg(q0), cont, code, pc, pcmid);
            assert AR.ActionRepL(rer, qm, LS.Acheck(inp), code, e1, e1 + 1);
            AR.ActionsRepLCons(rer, qm, LS.Acheck(inp), [LS.Areg(q0)] + cont, code, e1, e1 + 1);
            AR.ActionsRepLCons(rer, qm, LS.Areg(r1), [LS.Acheck(inp)] + ([LS.Areg(q0)] + cont), code, em + 3, e1);
            assert AR.ActionsRepL(rer, qm, ia, code, em + 3);
            assert {:split_here} true;   // (E3) section: walk invariants + the arms
            StarArmInvariants(acts, r1, q0, LS.Acheck(inp), gm, gidl);
            GateAheadClearTail(acts, gm);
            WalkDefsOkTail(acts);
            StarIterArmWalkBLRec(rer, qm, code, inp, gm, em + 1, g, qidC, r1, ti, ia);
            assert WalkPairLkRec(rer, qm, code, inp, ta, gm, x as nat, g);
            assert WalkPairLkRec(rer, qm, code, inp, skipt, gm, y as nat, g);
            assert CE.ProgErase(tb) == LT.Choice(CE.ProgErase(ta), CE.ProgErase(skipt));
          case _ =>
        }
      case _ =>
    }
  }

  lemma StarIterArmWalkBLRec(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                             gm: LG.GroupMap, sqcpc: nat, ea: bool, qid: int,
                             r1: L.Regex, ti: LT.Tree, armlist: LS.Actions)
    requires NR.GetPcRE(code, sqcpc) == Some(RB.SetQuantToClock(qid, false))
    requires qid in qm.quants && qm.quants[qid] == L.DefGroups(r1)
    requires NR.GetPcRE(code, sqcpc + 1) == Some(RB.BeginLoop)
    requires AR.ActionsRepL(rer, qm, armlist, code, sqcpc + 2)
    requires EL.PikeLkActionsRec(armlist)
    requires CW.BoolTreeLkX(rer, armlist, inp, BS.CannotExit, ti)
    requires GateAheadClear(armlist, LG.GMReset(L.DefGroups(r1), gm))
    requires WalkDefsOk(armlist)
    ensures WalkPairLkRec(rer, qm, code, inp, LT.GroupActionT(LG.Reset(L.DefGroups(r1)), ti),
                          gm, sqcpc, ea)
  {
    var gidl := L.DefGroups(r1);
    var gm2 := LG.GMUpdate(LG.Reset(gidl), LC.Idx(inp), gm);
    assert gm2 == LG.GMReset(gidl, gm);
    assert sqcpc + 1 < RB.size(code);
    assert ATR.EaOf(BS.CannotExit) == false;
    assert WalkPairLkRec(rer, qm, code, inp, ti, gm2, sqcpc + 2, false);
    assert WalkPairLkRec(rer, qm, code, inp, ti, gm2, sqcpc + 1, ea);   // BeginLoop absorbs any flag
    assert sqcpc < RB.size(code);
  }

  lemma StarIterArmWalkLVRec(rer: LW.RegExpRecord, qm: AR.QMap, code: RB.code, inp: LC.Input,
                             gm: LG.GroupMap, sqcpc: nat, ea: bool, qid: int,
                             r1: L.Regex, ti: LT.Tree, rest: LS.Actions)
    requires NR.GetPcRE(code, sqcpc) == Some(RB.SetQuantToClock(qid, false))
    requires qid in qm.quants && qm.quants[qid] == L.DefGroups(r1)
    requires NUL.NonNullableL(r1)
    requires AR.ActionsRepL(rer, qm, [LS.Areg(r1)] + rest, code, sqcpc + 1)
    requires EL.PikeLkActionsRec([LS.Areg(r1)] + rest)
    requires CW.BoolTreeLkX(rer, [LS.Areg(r1)] + rest, inp, BS.CannotExit, ti)
    requires GateAheadClear([LS.Areg(r1)] + rest, LG.GMReset(L.DefGroups(r1), gm))
    requires WalkDefsOk([LS.Areg(r1)] + rest)
    ensures WalkPairLkRec(rer, qm, code, inp, LT.GroupActionT(LG.Reset(L.DefGroups(r1)), ti),
                          gm, sqcpc, ea)
  {
    var gidl := L.DefGroups(r1);
    var gm2 := LG.GMUpdate(LG.Reset(gidl), LC.Idx(inp), gm);
    assert gm2 == LG.GMReset(gidl, gm);
    var b2 := if ea then BS.CanExit else BS.CannotExit;
    if ea { BoolTreeLkGuardShieldRec(rer, r1, rest, inp, ti); }
    assert CW.BoolTreeLkX(rer, [LS.Areg(r1)] + rest, inp, b2, ti) && ATR.EaOf(b2) == ea;
    assert WalkPairLkRec(rer, qm, code, inp, ti, gm2, sqcpc + 1, ea);
    assert sqcpc < RB.size(code);
  }

  lemma BlockedRepLkCSnocRec(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code,
                             inp: LC.Input, nextinp: LC.Input, crv: CP.FCompiled, str: string,
                             ov: LOr.OracleView, S: set<LG.GroupId>,
                             tl: seq<(LT.Tree, LG.GroupMap)>, bl: seq<(AI.Thread, RC.char_expectation)>,
                             tp: (LT.Tree, LG.GroupMap), p: (AI.Thread, RC.char_expectation),
                             ncap: int, nlook: int, nquant: int)
    requires BlockedRepLkCRec(rer, qm, re, code, inp, nextinp, crv, str, ov, S, tl, bl, ncap, nlook, nquant)
    requires p.0.pc >= 0
    requires TreeRepLkRE(rer, qm, code, nextinp, tp.0, (p.0.pc + 1) as nat, true)
    requires exists traw: LT.Tree ::
               CE.ProgErase(traw) == CE.ProgErase(tp.0)
               && WalkPairLkRec(rer, qm, code, nextinp, traw, tp.1, (p.0.pc + 1) as nat, true)
    requires GmtTieOutside(re, p.0, tp.1, S)
    ensures BlockedRepLkCRec(rer, qm, re, code, inp, nextinp, crv, str, ov, S, tl + [tp], bl + [p],
                             ncap, nlook, nquant)
    decreases tl
  {
    if |tl| == 0 {
      assert |bl| == 0;
      assert tl + [tp] == [tp] && bl + [p] == [p];
      assert ([tp])[0] == tp && ([tp])[1..] == [] && ([p])[0] == p && ([p])[1..] == [];
    } else {
      assert |bl| > 0;
      assert (tl + [tp])[0] == tl[0] && (bl + [p])[0] == bl[0];
      assert (tl + [tp])[1..] == tl[1..] + [tp] && (bl + [p])[1..] == bl[1..] + [p];
      BlockedRepLkCSnocRec(rer, qm, re, code, inp, nextinp, crv, str, ov, S, tl[1..], bl[1..],
                           tp, p, ncap, nlook, nquant);
    }
  }

  lemma ThreadRepLkStepAnchorRec(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code,
                                 inp: LC.Input, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
                                 S: set<LG.GroupId>, tb: LT.Tree, gm: LG.GroupMap, t: AI.Thread,
                                 ncap: int, nlook: int, nquant: int, a: R.anchor)
    requires ThreadRepLkRec(rer, qm, re, code, inp, crv, str, ov, S, tb, gm, t, ncap, nlook, nquant)
    requires NR.GetPcRE(code, t.pc as nat) == Some(RB.AnchorAssertion(a))
    requires tb.AnchorPass?     // the anchor is satisfied (else the VM drops the thread)
    ensures ThreadRepLkRec(rer, qm, re, code, inp, crv, str, ov, S, tb.t, gm,
                           t.(pc := t.pc + 1), ncap, nlook, nquant)
  {
    WalkPairLkAtAnchorRec(rer, qm, code, inp, tb, gm, t.pc as nat, t.exit_allowed, a);
    assert (t.pc + 1) as nat == (t.pc as nat) + 1;
    // GmtTieOutside/GmtTieInside read only the capture/look/quant regs, unchanged
    // by the pc update, so they transfer verbatim from ThreadRepLkRec(tb, gm, t).
  }

  lemma ThreadRepLkStepCheckOracleRec(
    rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, crv: CP.FCompiled,
    str: string, ov: LOr.OracleView, S: set<LG.GroupId>, lk: L.Lookaround, r1: L.Regex,
    tlk: LT.Tree, tc: LT.Tree, gm: LG.GroupMap, t: AI.Thread, l: int, cp: nat, clk: int,
    body: R.regex, la: R.lookaround, bodycode: RB.code, endl: nat, ngroups: nat,
    qt: AReg.Regs, ncap: int, nlook: int, nquant: int)
    requires qm.ov == ov && !rer.ignoreCase && !rer.multiline
    requires cp <= |str| && t.pc >= 0
    requires l in qm.looks && qm.looks[l] == (lk, r1)
    requires L.Positivity(lk) && L.LkDir(lk) == WP.Forward
    requires LS.LkResult(lk, tlk, gm, PIV.InpOfCp(str, cp)).Some?
    requires EL.LkGateOk(rer, lk, r1, PIV.InpOfCp(str, cp), tlk, true)
    // the paired B-subtree at t.pc is the LK gate node (from TtLkAtCheckOracleRec):
    requires ThreadRepLkRec(rer, qm, re, code, PIV.InpOfCp(str, cp), crv, str, ov, S,
                            LT.LK(lk, tlk, tc), gm, t, ncap, nlook, nquant)
    requires forall g :: g in L.DefGroups(r1) ==> g !in gm        // GateAheadClear at this gate
    // (L4 NESTED) the body may itself contain looks: the depth-1 LookFreeRE(body)
    // is replaced by the positive-nesting sub-fragment (feeds PikeLkRegexRec(r1)
    // for the recursive outside-tie); the GateStepValue body-package requires
    // (StaticOkRE(body)/bodycode/qt/f_look_* rows) are DROPPED with the call.
    requires T.TransWf(body) && NR.NestedFragmentRE(body) && EL.NegBehindLookFreeRE(body) && la.Lookahead?
    requires NR.NoNulledPlusRE(body)   // §2.5b interim: all stamps false
    requires r1 == T.Translate(body) && lk == T.TrLookaround(la)
    requires LL.OracleOkSuffix(rer, qm, PIV.InpOfCp(str, cp))
    requires 0 <= l < nlook && l < RL.ASize(t.look_regs)
    // gate position + outside-frame well-formedness (caller supplies); the
    // continuation walk and outside frame are now DERIVED in the body.
    requires NR.GetPcRE(code, t.pc as nat) == Some(RB.CheckOracle(l))
    requires T.TransWf(re) && NR.NestedFragmentRE(re)
    requires S == LL.LkBodyGroups(T.Translate(re))
    requires (set g | g in L.DefGroups(r1)) <= S
    ensures var t' := t.(pc := t.pc + 1, look_regs := AReg.set_reg(t.look_regs, l, Some(cp as int), clk));
            var gm2 := LS.LkResult(lk, tlk, gm, PIV.InpOfCp(str, cp)).value;
            ThreadRepLkRec(rer, qm, re, code, PIV.InpOfCp(str, cp), crv, str, ov, S, tc, gm2, t',
                           ncap, nlook, nquant)
  {
    var inp := PIV.InpOfCp(str, cp);
    var t' := t.(pc := t.pc + 1, look_regs := AReg.set_reg(t.look_regs, l, Some(cp as int), clk));
    var gm2 := LS.LkResult(lk, tlk, gm, inp).value;
    // (1) INSIDE tie DROPPED (GmtTieInside is not part of ThreadRepLkRec).
    assert t' == t.(pc := t.pc + 1, look_regs := AReg.set_reg(t.look_regs, l, Some(cp as int), clk));
    // (2) CONTINUATION walk: from the incoming ThreadRepLk's WalkPairLkRec on the LK head.
    assert LL.OracleOkAt(rer, qm, inp);   // OracleOkSuffix instantiated at inp
    assert WalkPairLkRec(rer, qm, code, inp, LT.LK(lk, tlk, tc), gm, t.pc as nat, t.exit_allowed);
    WalkPairLkAtCheckOracleRec(rer, qm, code, inp, LT.LK(lk, tlk, tc), gm, t.pc as nat, t.exit_allowed, l);
    assert LT.LK(lk, tlk, tc).LK?;        // ⟹ bit true (wrapper: !bit ==> LKFail?)
    assert (t.pc + 1) as nat == (t.pc as nat) + 1 && t'.exit_allowed == t.exit_allowed;
    assert WalkPairLkRec(rer, qm, code, inp, tc, gm2, (t.pc + 1) as nat, t.exit_allowed);
    // (3) OUTSIDE frame: recursive-body confinement (PikeLkRegexRec(r1)).
    assert GmtTieOutside(re, t, gm, S);   // from the incoming ThreadRepLkRec(LK, gm, t)
    EL.TranslateFragmentPikeLkRec(body);  // PikeLkRegexRec(Translate(body)) == PikeLkRegexRec(r1)
    GmtTieOutsideAfterGateNested(rer, re, str, lk, r1, tlk, gm, t, l, cp, clk, S);   // GmtTieOutside(t',gm2,S)
  }

  /** (L5 F6c) The LOOKBEHIND twin of `ThreadRepLkStepCheckOracleRec`: the same
      gate step for a POSITIVE LOOKBEHIND gate (`L.LkDir(lk) == WP.Backward`,
      `la.Lookbehind?`). Every ingredient is direction-generic
      (`WalkPairLkAtCheckOracleRec` is oracle-bit based; `GmtTieOutsideAfterGateNested`
      takes the direction from `L.LkDir(lk)`), so the proof body is verbatim; only
      the direction pin differs. Fills the (BRICK D5) dead arm of
      `LiftPreserveGatePassLkRec` once `NoPosLookbehindRE` is lifted (F7). */
  lemma ThreadRepLkStepCheckOracleRecLB(
    rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code, crv: CP.FCompiled,
    str: string, ov: LOr.OracleView, S: set<LG.GroupId>, lk: L.Lookaround, r1: L.Regex,
    tlk: LT.Tree, tc: LT.Tree, gm: LG.GroupMap, t: AI.Thread, l: int, cp: nat, clk: int,
    body: R.regex, la: R.lookaround, bodycode: RB.code, endl: nat, ngroups: nat,
    qt: AReg.Regs, ncap: int, nlook: int, nquant: int)
    requires qm.ov == ov && !rer.ignoreCase && !rer.multiline
    requires cp <= |str| && t.pc >= 0
    requires l in qm.looks && qm.looks[l] == (lk, r1)
    requires L.Positivity(lk) && L.LkDir(lk) == WP.Backward
    requires LS.LkResult(lk, tlk, gm, PIV.InpOfCp(str, cp)).Some?
    requires EL.LkGateOk(rer, lk, r1, PIV.InpOfCp(str, cp), tlk, true)
    // the paired B-subtree at t.pc is the LK gate node (from TtLkAtCheckOracleRec):
    requires ThreadRepLkRec(rer, qm, re, code, PIV.InpOfCp(str, cp), crv, str, ov, S,
                            LT.LK(lk, tlk, tc), gm, t, ncap, nlook, nquant)
    requires forall g :: g in L.DefGroups(r1) ==> g !in gm        // GateAheadClear at this gate
    // (L4 NESTED) the body may itself contain looks: the depth-1 LookFreeRE(body)
    // is replaced by the positive-nesting sub-fragment (feeds PikeLkRegexRec(r1)
    // for the recursive outside-tie); the GateStepValue body-package requires
    // (StaticOkRE(body)/bodycode/qt/f_look_* rows) are DROPPED with the call.
    requires T.TransWf(body) && NR.NestedFragmentRE(body) && EL.NegBehindLookFreeRE(body) && la.Lookbehind?
    requires NR.NoNulledPlusRE(body)   // §2.5b interim: all stamps false
    requires r1 == T.Translate(body) && lk == T.TrLookaround(la)
    requires LL.OracleOkSuffix(rer, qm, PIV.InpOfCp(str, cp))
    requires 0 <= l < nlook && l < RL.ASize(t.look_regs)
    // gate position + outside-frame well-formedness (caller supplies); the
    // continuation walk and outside frame are now DERIVED in the body.
    requires NR.GetPcRE(code, t.pc as nat) == Some(RB.CheckOracle(l))
    requires T.TransWf(re) && NR.NestedFragmentRE(re)
    requires S == LL.LkBodyGroups(T.Translate(re))
    requires (set g | g in L.DefGroups(r1)) <= S
    ensures var t' := t.(pc := t.pc + 1, look_regs := AReg.set_reg(t.look_regs, l, Some(cp as int), clk));
            var gm2 := LS.LkResult(lk, tlk, gm, PIV.InpOfCp(str, cp)).value;
            ThreadRepLkRec(rer, qm, re, code, PIV.InpOfCp(str, cp), crv, str, ov, S, tc, gm2, t',
                           ncap, nlook, nquant)
  {
    var inp := PIV.InpOfCp(str, cp);
    var t' := t.(pc := t.pc + 1, look_regs := AReg.set_reg(t.look_regs, l, Some(cp as int), clk));
    var gm2 := LS.LkResult(lk, tlk, gm, inp).value;
    // (1) INSIDE tie DROPPED (GmtTieInside is not part of ThreadRepLkRec).
    assert t' == t.(pc := t.pc + 1, look_regs := AReg.set_reg(t.look_regs, l, Some(cp as int), clk));
    // (2) CONTINUATION walk: from the incoming ThreadRepLk's WalkPairLkRec on the LK head.
    assert LL.OracleOkAt(rer, qm, inp);   // OracleOkSuffix instantiated at inp
    assert WalkPairLkRec(rer, qm, code, inp, LT.LK(lk, tlk, tc), gm, t.pc as nat, t.exit_allowed);
    WalkPairLkAtCheckOracleRec(rer, qm, code, inp, LT.LK(lk, tlk, tc), gm, t.pc as nat, t.exit_allowed, l);
    assert LT.LK(lk, tlk, tc).LK?;        // ⟹ bit true (wrapper: !bit ==> LKFail?)
    assert (t.pc + 1) as nat == (t.pc as nat) + 1 && t'.exit_allowed == t.exit_allowed;
    assert WalkPairLkRec(rer, qm, code, inp, tc, gm2, (t.pc + 1) as nat, t.exit_allowed);
    // (3) OUTSIDE frame: recursive-body confinement (PikeLkRegexRec(r1)).
    assert GmtTieOutside(re, t, gm, S);   // from the incoming ThreadRepLkRec(LK, gm, t)
    EL.TranslateFragmentPikeLkRec(body);  // PikeLkRegexRec(Translate(body)) == PikeLkRegexRec(r1)
    GmtTieOutsideAfterGateNested(rer, re, str, lk, r1, tlk, gm, t, l, cp, clk, S);   // GmtTieOutside(t',gm2,S)
  }

  /** (R2 DEEP CARRIER — the gate-pass rep step, EXTRACTED from
      `LiftPreserveGatePassLkRec`) The deep-carrier converse across a positive
      lookAHEAD gate crossing, packaged as a standalone (non-isolate-assertions)
      lemma so the giant gate-pass preserver's VC count does not balloon. Composes
      `DeepGateReqFromCrossing` (the crossing lands l's whole sub-first-leaf into
      `gm2`) with `LookNestBackTGatePassTopDeep` (every other top lid transports by
      congruence), then rebuilds the deep active rep for the stepped head + tail.
      MIRRORS the DIRECT gate-pass rep threading verbatim, `SubFirstLeafAt` landed
      set in place of `GmOfLive(body, FreshBodyMatch)`. */
  lemma GatePassDeepRepStep(
    rer: LW.RegExpRecord, re: R.regex, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
    S: set<LG.GroupId>, ta: seq<(LT.Tree, LG.GroupMap)>, sactive: seq<AI.Thread>,
    tt: LT.Tree, gm: LG.GroupMap, gm2: LG.GroupMap, th: AI.Thread, th': AI.Thread,
    l: int, lk: L.Lookaround, r1: L.Regex, tlk: LT.Tree, body: R.regex, cp: nat,
    ncap: int, nlook: int, nquant: int)
    requires |ta| > 0 && |sactive| == |ta|
    requires sactive[0] == th && ta[0].1 == gm
    requires PIV.CapUnique(re) && LTB.LookUnique(re)
    requires LookNestBackRepCTopDeep(rer, re, crv, str, ov, S, ta, sactive, ncap, nlook, nquant)
    // frame: gate touches only look_regs at l
    requires th'.quant_regs == th.quant_regs
    requires forall j: int :: j != l ==>
                                AI.get_idx(th'.look_regs.a_clk, j) == AI.get_idx(th.look_regs.a_clk, j)
                                && AI.get_idx(th'.look_regs.a_cp, j) == AI.get_idx(th.look_regs.a_cp, j)
    // the crossing seam (feeds `DeepGateReqFromCrossing`)
    requires cp <= |str|
    requires l >= 0 && (l as nat) in LTB.LookIds(re) && (l as nat) in NI.TopLookIds(re)
    requires T.TransWf(body)
    requires L.Positivity(lk) && L.LkDir(lk) == LidDir(crv, l)   // (L5 F7a) direction-generic
    requires EL.PikeLkRegexRec(r1)
    requires r1 == T.Translate(body)
    requires body == M.VBody(crv, l) && NI.LookBodyOfRE(re, l as nat) == body
    requires tlk == LFU.ComputeTr(rer, [LS.Areg(r1)], PIV.InpOfCp(str, cp), LG.Empty, L.LkDir(lk))
    requires LS.LkResult(lk, tlk, gm, PIV.InpOfCp(str, cp)).Some?
    requires gm2 == LS.LkResult(lk, tlk, gm, PIV.InpOfCp(str, cp)).value
    requires M.GmAgreeOn(gm, LG.Empty, set g | g in L.DefGroups(r1))
    requires AReg.get_cp(th'.look_regs, l) == Some(cp as int)
    ensures LookNestBackRepCTopDeep(rer, re, crv, str, ov, S, [(tt, gm2)] + ta[1..],
                                    [th'] + sactive[1..], ncap, nlook, nquant)
  {
    assert LookNestBackTTopDeep(rer, re, crv, str, ov, S, gm, th, ncap, nlook, nquant);  // rep element 0
    DeepGateReqFromCrossing(rer, re, crv, str, ov, S, gm, gm2, lk, r1, tlk, th', l, cp, body,
                            ncap, nlook, nquant);
    // the off-body region frame from the crossing's confinement
    assert LL.GmAgreeOutside(gm2, gm, PIV.CapIds(NI.LookBodyOfRE(re, l as nat)));
    assert forall g: LG.GroupId ::
        g in S && !(l >= 0 && (l as nat) in LTB.LookIds(re) && g in PIV.CapIds(NI.LookBodyOfRE(re, l as nat)))
        ==> ((g in gm <==> g in gm2) && (g in gm ==> gm2[g] == gm[g]));
    LookNestBackTGatePassTopDeep(rer, re, crv, str, ov, S, gm, gm2, th, th', l, ncap, nlook, nquant);
    forall i | 0 <= i < |[(tt, gm2)] + ta[1..]|
      ensures LookNestBackTTopDeep(rer, re, crv, str, ov, S, ([(tt, gm2)] + ta[1..])[i].1,
                                   ([th'] + sactive[1..])[i], ncap, nlook, nquant)
    {
      if i == 0 {
      } else {
        assert ([(tt, gm2)] + ta[1..])[i] == ta[i];
        assert ([th'] + sactive[1..])[i] == sactive[i];
      }
    }
  }

  lemma BlockedToActiveLkCRec(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, code: RB.code,
                              inp: LC.Input, nextinp: LC.Input, crv: CP.FCompiled, str: string,
                              ov: LOr.OracleView, S: set<LG.GroupId>,
                              tl: seq<(LT.Tree, LG.GroupMap)>, bl: seq<(AI.Thread, RC.char_expectation)>,
                              ncap: int, nlook: int, nquant: int)
    requires BlockedRepLkCRec(rer, qm, re, code, inp, nextinp, crv, str, ov, S, tl, bl, ncap, nlook, nquant)
    ensures ActiveRepLkCRec(rer, qm, re, code, nextinp, crv, str, ov, S, tl, PSM.ResumeAll(bl),
                            ncap, nlook, nquant)
    decreases tl
  {
    if |tl| == 0 {
      assert |bl| == 0;
    } else {
      assert |bl| > 0;
      var th := bl[0].0;
      var rth := th.(exit_allowed := true, pc := th.pc + 1);
      assert PSM.ResumeAll(bl) == [rth] + PSM.ResumeAll(bl[1..]);
      assert rth.pc >= 0 && (rth.pc as nat) == (th.pc + 1) as nat;
      assert TreeRepLkRE(rer, qm, code, nextinp, tl[0].0, rth.pc as nat, rth.exit_allowed);
      var traw: LT.Tree :| CE.ProgErase(traw) == CE.ProgErase(tl[0].0)
                           && WalkPairLkRec(rer, qm, code, nextinp, traw, tl[0].1, (th.pc + 1) as nat, true);
      assert rth.capture_regs == th.capture_regs && rth.look_regs == th.look_regs
             && rth.quant_regs == th.quant_regs;
      assert GmtTieOutside(re, rth, tl[0].1, S)
        ;
      assert ThreadRepLkRec(rer, qm, re, code, nextinp, crv, str, ov, S, traw, tl[0].1, rth,
                            ncap, nlook, nquant);
      assert ThreadRepLkCRec(rer, qm, re, code, nextinp, crv, str, ov, S, tl[0].0, tl[0].1, rth,
                             ncap, nlook, nquant);
      BlockedToActiveLkCRec(rer, qm, re, code, inp, nextinp, crv, str, ov, S, tl[1..], bl[1..],
                            ncap, nlook, nquant);
      assert ([rth] + PSM.ResumeAll(bl[1..]))[0] == rth
             && ([rth] + PSM.ResumeAll(bl[1..]))[1..] == PSM.ResumeAll(bl[1..]);
    }
  }

  /** (§2.3/§2.4) An inside-look capture present in the top readout is present in
      its innermost owner's FRESH body match. The presence path on the reconstructed
      banks descends to the owner (`LookPathDecomposeNested`) and the FLookLoop value
      lifts move it onto the fresh banks, quantifier clocks included: the path itself
      is the dominance, so no capture-under-quantifier hypothesis is needed. */
  lemma OwnerPkgFromPresence(
    qm: AR.QMap, crv: CP.FCompiled, str: string, ast: R.regex, re: R.regex, ov: LOr.OracleView,
    res0: AReg.Regs, res1: AReg.Regs, res2: AReg.Regs, g: LG.GroupId, ncap: int, nlook: int, nquant: int)
    returns (owner: nat)
    requires NR.NestedFragmentRE(re) && NR.L5ScopeRE(re)
    requires PIV.CapUnique(re) && PIV.QuantUnique(re) && LTB.LookUnique(re)
    requires LTB.LookTablesOk(re, crv)
    requires forall x: nat :: x in LTB.LookIds(re) ==> 1 <= x <= R.max_lookaround(ast)
    requires forall x: nat :: x in LTB.LookIds(re) ==> (x as int) in qm.looks
    requires GateStaticsOkNested(qm, re, crv, ncap, nlook, nquant)
    requires |res1.a_cp| == nlook && |res1.a_clk| == nlook
    requires M.LookInvO(res1, ov, str) && M.Res0LiveO(re, res0)
    requires M.ValueOkO(crv, str, res0, res1, 1, R.max_lookaround(ast), ov, ncap, nlook, nquant)
    requires M.QuantValueOkO(crv, str, res2, res1, 1, R.max_lookaround(ast), ov, ncap, nlook, nquant)
    requires g in PIV.CapIdsInLooks(re) && g in PIV.GmOfLive(re, res0, res1, res2)
    ensures OwnerPkg(crv, str, re, ov, res1, g, owner, ncap, nlook, nquant)
  {
    hide NUL.NonNullableL, NUL.CINullableL, NUL.NoNulledPlusL, AR.NfaRepCinL;
    reveal M.LookInvO(), M.Res0LiveO();
    PIV.CapIdsSplit(re);
    NI.GmOfLivePresenceExtractLkNested(re, res0, res1, res2, g);
    assert AReg.as_arrays(res1).1 == res1.a_clk && AReg.as_arrays(res2).1 == res2.a_clk;
    assert PIV.PathPresentLk(re, res0.a_clk, res1.a_clk, res2.a_clk, -1, g);
    owner := NI.InnermostOwnerDirect(re, g);
    var body := NI.LookBodyOfRE(re, owner);
    NI.LookPathDecomposeNested(re, body, res0.a_clk, res1.a_clk, res2.a_clk, -1, owner, g);
    M.LookBodyFactsL5(re, crv, owner);
    assert NR.NestedFragmentRE(body) && PIV.CapUnique(body);
    assert {:split_here} true;
    // the owner matched: the record is set and the look is positive
    assert AI.get_idx(res1.a_cp, owner as int) >= 0;
    assert AReg.get_cp(res1, owner as int).Some? by { RL.AAsArraysLaws(res1); }
    assert 1 <= owner <= R.max_lookaround(ast) && (owner as int) in qm.looks;
    MatchedPosFromHub(qm, re, crv, res1, owner, g, ncap, nlook, nquant);
    assert M.MatchedPosLA(crv, res1, owner as int);
    assert body == M.VBody(crv, owner as int) by {
      NI.LookBodyOfTablesTie(re, crv, owner);
      var laT: R.lookaround :| LTB.LookEntryOk(crv, owner as int, laT, body);
    }
    assert {:split_here} true;
    // the value lifts at the owner
    var rf := M.FreshBodyMatch(crv, str, owner as int, res1, ov, ncap, nlook, nquant);
    PIV.CapIdsSplit(body);
    assert g in PIV.CapIdsOutsideLooks(body);
    assert CP.start_reg(g as int) in PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(body));
    assert rf.Some? by {
      if rf.None? {
        assert CM.RegsAgreeInside(res0, AReg.init_regs(ncap), PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(body))) by {
          reveal M.ValueOkO();
          assert 1 <= owner as int <= R.max_lookaround(ast);
        }
        RL.AInitLaws(ncap);
        assert AI.get_idx(res0.a_clk, CP.start_reg(g as int)) == AI.get_idx(AReg.init_regs(ncap).a_clk, CP.start_reg(g as int));
        if 0 <= CP.start_reg(g as int) < ncap { }
        assert false;
      }
    }
    assert CM.RegsAgreeInside(res0, rf.value.capture_regs, PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(body))) by {
      reveal M.ValueOkO();
      assert 1 <= owner as int <= R.max_lookaround(ast);
    }
    assert CM.RegsAgreeInside(res2, rf.value.quant_regs, M.QIdsOuter(body)) by {
      reveal M.QuantValueOkO();
      assert 1 <= owner as int <= R.max_lookaround(ast);
    }
    assert {:split_here} true;
    var rfc := rf.value.capture_regs;
    var rfl := rf.value.look_regs;
    var rfq := rf.value.quant_regs;
    forall c: nat | c in PIV.CapIdsOutsideLooks(body)
      ensures AI.get_idx(rfc.a_clk, CP.start_reg(c)) == AI.get_idx(res0.a_clk, CP.start_reg(c))
    {
      assert CP.start_reg(c) in PIV.CaptureRegsSet(PIV.CapIdsOutsideLooks(body));
    }
    forall q: nat | q in PIV.QuantIdsOutsideLooks(body)
      ensures AI.get_idx(rfq.a_clk, q as int) == AI.get_idx(res2.a_clk, q as int)
    {
      assert (q as int) in M.QIdsOuter(body);
    }
    PathPresentLkDirectAgreeQ(body, rfc.a_clk, rfl.a_clk, rfq.a_clk,
                              res0.a_clk, res1.a_clk, res2.a_clk, -1, g);
    assert AReg.as_arrays(rfc).1 == rfc.a_clk && AReg.as_arrays(rfc).0 == rfc.a_cp;
    assert AReg.as_arrays(rfl).1 == rfl.a_clk && AReg.as_arrays(rfq).1 == rfq.a_clk;
    NI.GmOfLiveKeepsPresentLkNested(body, rfc, rfl, rfq, g);
  }

  /** (§2.3/§2.4) The owner-package forall on the reconstructed banks: successor of
      the gated, no-quant `ProduceOwnerForall`. */
  lemma ProduceOwnerForallRes(
    qm: AR.QMap, crv: CP.FCompiled, str: string, ast: R.regex, re: R.regex, ov: LOr.OracleView,
    res0: AReg.Regs, res1: AReg.Regs, res2: AReg.Regs, S: set<LG.GroupId>, ncap: int, nlook: int, nquant: int)
    requires NR.NestedFragmentRE(re) && NR.L5ScopeRE(re)
    requires PIV.CapUnique(re) && PIV.QuantUnique(re) && LTB.LookUnique(re)
    requires LTB.LookTablesOk(re, crv)
    requires forall x: nat :: x in LTB.LookIds(re) ==> 1 <= x <= R.max_lookaround(ast)
    requires forall x: nat :: x in LTB.LookIds(re) ==> (x as int) in qm.looks
    requires GateStaticsOkNested(qm, re, crv, ncap, nlook, nquant)
    requires |res1.a_cp| == nlook && |res1.a_clk| == nlook
    requires M.LookInvO(res1, ov, str) && M.Res0LiveO(re, res0)
    requires M.ValueOkO(crv, str, res0, res1, 1, R.max_lookaround(ast), ov, ncap, nlook, nquant)
    requires M.QuantValueOkO(crv, str, res2, res1, 1, R.max_lookaround(ast), ov, ncap, nlook, nquant)
    requires S == PIV.CapIdsInLooks(re)
    ensures OwnerForallO(crv, str, re, ov, res0, res1, res2, S, ncap, nlook, nquant)
  {
    forall g: LG.GroupId | g in S && g in PIV.GmOfLive(re, res0, res1, res2)
      ensures exists owner: nat :: OwnerPkg(crv, str, re, ov, res1, g, owner, ncap, nlook, nquant)
    {
      var owner := OwnerPkgFromPresence(qm, crv, str, ast, re, ov, res0, res1, res2, g, ncap, nlook, nquant);
    }
    assert OwnerForallO(crv, str, re, ov, res0, res1, res2, S, ncap, nlook, nquant) by {
      reveal OwnerForallO();
    }
  }

}
